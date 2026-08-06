#include <cstdint>
#include <cstring>
#include <cstdio>
#include <cerrno>

#ifdef _WIN32
  #include <winsock2.h>
  #pragma comment(lib, "ws2_32.lib")
  typedef int socklen_t;
#else
  #include <sys/socket.h>
  #include <netinet/in.h>
  #include <arpa/inet.h>
  #include <unistd.h>
  #include <fcntl.h>
  #include <sys/select.h>
#endif

// ─── Internal helpers ─────────────────────────────────────────────────────────

static int make_tcp_socket_ms(const char* ip, int port, int timeout_ms) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    // Non-blocking connect
#ifndef _WIN32
    fcntl(fd, F_SETFL, O_NONBLOCK);
#endif

    struct sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons((uint16_t)port);
    inet_pton(AF_INET, ip, &addr.sin_addr);

    int rc = connect(fd, (struct sockaddr*)&addr, sizeof(addr));
    if (rc < 0 && errno != EINPROGRESS) {
#ifndef _WIN32
        close(fd);
#endif
        return -1;
    }

    // Wait for connect with select()
    fd_set wset;
    FD_ZERO(&wset);
    FD_SET(fd, &wset);
    struct timeval tv{ timeout_ms / 1000, (timeout_ms % 1000) * 1000 };
    if (select(fd + 1, nullptr, &wset, nullptr, &tv) <= 0) {
#ifndef _WIN32
        close(fd);
#endif
        return -1;
    }

    // Restore blocking mode
#ifndef _WIN32
    int flags = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, flags & ~O_NONBLOCK);
#endif
    return fd;
}

static int make_udp_socket() {
    return socket(AF_INET, SOCK_DGRAM, 0);
}

// ─── Exported API (C linkage) ─────────────────────────────────────────────────

extern "C" {

/// Send a raw payload to ip:port over TCP.
/// Returns bytes sent on success, -1 on error.
int eiv_raw_send(const char* ip, int port, const uint8_t* payload, int len) {
    int fd = make_tcp_socket_ms(ip, port, 2000);
    if (fd < 0) return -1;
    int sent = (int)send(fd, payload, (size_t)len, 0);
#ifndef _WIN32
    close(fd);
#endif
    return sent;
}

/// Modbus TCP: send a Read Holding Registers (FC=03) PDU to unit_id.
/// Fills result[0..N] with the raw response.
/// Returns number of bytes received, 0 if no device, -1 on error.
int eiv_modbus_probe(const char* ip, int unit_id, uint8_t* result) {
    int fd = make_tcp_socket_ms(ip, 502, 2000);
    if (fd < 0) return 0;   // port closed — not an error

    // Modbus TCP Application Data Unit (MBAP + PDU)
    // Transaction ID=0x0001, Protocol=0x0000, Length=0x0006
    // Unit ID, FC=0x03 (Read Holding Registers), Addr=0x0000, Count=0x000A
    uint8_t pdu[] = {
        0x00, 0x01,  // transaction id
        0x00, 0x00,  // protocol id (Modbus TCP = 0)
        0x00, 0x06,  // remaining length
        (uint8_t)unit_id,
        0x03,        // function code: read holding registers
        0x00, 0x00,  // start address
        0x00, 0x0A,  // quantity: 10 registers
    };

    send(fd, pdu, sizeof(pdu), 0);

    // Receive response (max 256 bytes)
    uint8_t buf[256] = {};
    struct timeval tv{ 1, 500000 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        rc = (int)recv(fd, buf, sizeof(buf), 0);
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && result) {
        int copy = rc < 256 ? rc : 255;
        memcpy(result, buf, (size_t)copy);
        // Return number of data bytes (registers) — byte_count is buf[8]
        return (rc >= 9) ? buf[8] : rc;
    }
    return rc > 0 ? rc : 0;
}

/// BACnet/IP: send a WHO-IS request and wait for I-AM.
/// Returns 1 if a BACnet device responded, 0 otherwise.
int eiv_bacnet_probe(const char* ip, uint8_t* result) {
    int fd = make_udp_socket();
    if (fd < 0) return 0;

    // BACnet/IP BVLL WHO-IS (broadcast)
    // BVLC Type=0x81, Function=0x0a (Original-Broadcast), Length=0x000c
    // NPDU: 0x01 0x20 (data expecting reply, dest broadcast)
    // APDU: UnconfirmedServiceRequest (0x10), WHO-IS (0x08)
    uint8_t pkt[] = {
        0x81, 0x0b, 0x00, 0x0c,   // BVLC header (Original-Unicast)
        0x01, 0x04,                // NPDU
        0x10, 0x08,                // APDU: WHO-IS
    };

    struct sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons(47808);  // BAC0
    inet_pton(AF_INET, ip, &addr.sin_addr);

    sendto(fd, pkt, sizeof(pkt), 0, (struct sockaddr*)&addr, sizeof(addr));

    uint8_t buf[256] = {};
    struct timeval tv{ 1, 0 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        socklen_t slen = sizeof(addr);
        rc = (int)recvfrom(fd, buf, sizeof(buf), 0, (struct sockaddr*)&addr, &slen);
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 4 && result) memcpy(result, buf, (size_t)(rc < 256 ? rc : 255));
    // I-AM response starts with 0x81 0x0b and APDU 0x10 0x00
    return (rc > 4 && buf[0] == 0x81) ? 1 : 0;
}

/// Profinet DCP: send an Identify.req and check for Identify.res.
/// Returns 1 if a Profinet device responded, 0 otherwise.
int eiv_profinet_probe(const char* ip, uint8_t* result) {
    // Profinet DCP runs over Ethernet (raw frames), not IP.
    // Over TCP/IP networks we probe port 34964 (Profinet RT).
    int fd = make_udp_socket();
    if (fd < 0) return 0;

    // Minimal DCP Identify request payload
    uint8_t pkt[] = { 0xfe, 0xfe, 0x05, 0x00, 0x00, 0x01, 0x00, 0x00 };

    struct sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons(34964);
    inet_pton(AF_INET, ip, &addr.sin_addr);

    sendto(fd, pkt, sizeof(pkt), 0, (struct sockaddr*)&addr, sizeof(addr));

    uint8_t buf[256] = {};
    struct timeval tv{ 1, 0 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        socklen_t slen = sizeof(addr);
        rc = (int)recvfrom(fd, buf, sizeof(buf), 0, (struct sockaddr*)&addr, &slen);
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && result) memcpy(result, buf, (size_t)(rc < 256 ? rc : 255));
    return rc > 0 ? 1 : 0;
}

/// EtherNet/IP: send a ListIdentity request (CIP port 44818).
/// Returns number of items listed, 0 if no device.
int eiv_ethernetip_probe(const char* ip, uint8_t* result) {
    int fd = make_tcp_socket_ms(ip, 44818, 2000);
    if (fd < 0) return 0;

    // EtherNet/IP Encapsulation Header: ListIdentity (cmd=0x0063)
    uint8_t pkt[] = {
        0x63, 0x00,  // command: ListIdentity
        0x00, 0x00,  // length: 0 (no data)
        0x00, 0x00, 0x00, 0x00,  // session handle
        0x00, 0x00, 0x00, 0x00,  // status
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // sender context
        0x00, 0x00, 0x00, 0x00,  // options
    };

    send(fd, pkt, sizeof(pkt), 0);

    uint8_t buf[512] = {};
    struct timeval tv{ 1, 500000 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        rc = (int)recv(fd, buf, sizeof(buf), 0);
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && result) memcpy(result, buf, (size_t)(rc < 512 ? rc : 511));
    return rc > 24 ? 1 : 0;
}

/// UPnP M-SEARCH: broadcast SSDP discovery to port 1900.
/// Returns 1 if any UPnP device responded, 0 otherwise.
int eiv_upnp_probe(const char* ip, uint8_t* result) {
    int fd = make_udp_socket();
    if (fd < 0) return 0;

    // SSDP M-SEARCH message
    const char* ssdp =
        "M-SEARCH * HTTP/1.1\r\n"
        "HOST: 239.255.255.250:1900\r\n"
        "MAN: \"ssdp:discover\"\r\n"
        "MX: 1\r\n"
        "ST: ssdp:all\r\n"
        "\r\n";

    // Send to target IP (unicast discovery)
    struct sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons(1900);
    inet_pton(AF_INET, ip, &addr.sin_addr);

    sendto(fd, ssdp, strlen(ssdp), 0, (struct sockaddr*)&addr, sizeof(addr));

    uint8_t buf[1024] = {};
    struct timeval tv{ 1, 500000 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        socklen_t slen = sizeof(addr);
        rc = (int)recvfrom(fd, buf, sizeof(buf) - 1, 0, (struct sockaddr*)&addr, &slen);
        buf[rc > 0 ? rc : 0] = 0;
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && result) memcpy(result, buf, (size_t)(rc < 1024 ? rc : 1023));
    // Check for HTTP/1.1 200 OK (SSDP response) or NOTIFY
    return (rc > 0 && (memcmp(buf, "HTTP/1.1 200", 12) == 0 || memcmp(buf, "NOTIFY", 6) == 0)) ? 1 : 0;
}

/// mDNS: query _services._dns-sd._udp.local to fingerprint the device.
/// Returns 1 if an mDNS response was received, 0 otherwise.
int eiv_mdns_probe(const char* ip, uint8_t* result) {
    int fd = make_udp_socket();
    if (fd < 0) return 0;

    // Minimal mDNS PTR query for service discovery
    uint8_t mdns_query[] = {
        0x00, 0x00,  // transaction id (0 for mDNS)
        0x00, 0x00,  // flags: standard query
        0x00, 0x01,  // QDCOUNT: 1
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ANCOUNT, NSCOUNT, ARCOUNT
        // QNAME: _services._dns-sd._udp.local
        0x09, '_','s','e','r','v','i','c','e','s',
        0x07, '_','d','n','s','-','s','d',
        0x04, '_','u','d','p',
        0x05, 'l','o','c','a','l',
        0x00,        // root label
        0x00, 0x0c,  // QTYPE: PTR
        0x80, 0x01,  // QCLASS: IN (unicast response requested)
    };

    struct sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons(5353);
    inet_pton(AF_INET, ip, &addr.sin_addr);

    sendto(fd, mdns_query, sizeof(mdns_query), 0, (struct sockaddr*)&addr, sizeof(addr));

    uint8_t buf[1024] = {};
    struct timeval tv{ 1, 0 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;
    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        socklen_t slen = sizeof(addr);
        rc = (int)recvfrom(fd, buf, sizeof(buf), 0, (struct sockaddr*)&addr, &slen);
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && result) memcpy(result, buf, (size_t)(rc < 1024 ? rc : 1023));
    return rc > 12 ? 1 : 0;
}

/// TCP banner grab: connect to ip:port, read the banner.
/// timeout_ms: connect + read timeout in milliseconds.
/// Returns number of banner bytes read into out[], 0 if no banner.
int eiv_banner_grab(const char* ip, int port, uint8_t* out, int timeout_ms) {
    int fd = make_tcp_socket_ms(ip, port, timeout_ms);
    if (fd < 0) return 0;

    // For protocols that send first (FTP, SMTP, SSH, Telnet), just read.
    // For HTTP, send a minimal GET.
    uint8_t buf[1024] = {};
    struct timeval tv{ timeout_ms / 1000, (timeout_ms % 1000) * 1000 };
    fd_set rset;
    FD_ZERO(&rset);
    FD_SET(fd, &rset);
    int rc = 0;

    if (select(fd + 1, &rset, nullptr, nullptr, &tv) > 0) {
        rc = (int)recv(fd, buf, sizeof(buf) - 1, 0);
    }
    if (rc <= 0 && (port == 80 || port == 8080 || port == 8443)) {
        // HTTP — send a HEAD request
        const char* head = "HEAD / HTTP/1.0\r\nHost: target\r\n\r\n";
        send(fd, head, strlen(head), 0);
        fd_set rset2; FD_ZERO(&rset2); FD_SET(fd, &rset2);
        struct timeval tv2{ 1, 0 };
        if (select(fd + 1, &rset2, nullptr, nullptr, &tv2) > 0) {
            rc = (int)recv(fd, buf, sizeof(buf) - 1, 0);
        }
    }
#ifndef _WIN32
    close(fd);
#endif
    if (rc > 0 && out) {
        int copy = rc < 1024 ? rc : 1023;
        memcpy(out, buf, (size_t)copy);
        out[copy] = 0;
    }
    return rc > 0 ? rc : 0;
}

} // extern "C"
