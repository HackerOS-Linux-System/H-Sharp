#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#define PCRE2_CODE_UNIT_WIDTH 8
#include <pcre2.h>

typedef const char* hsh_string;

int64_t hsh_regex_match(hsh_string pattern, hsh_string text) {
    if (!pattern || !text) return 0;
    int errcode; PCRE2_SIZE erroffset;
    pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
        0, &errcode, &erroffset, NULL);
    if (!re) return 0;
    pcre2_match_data* md = pcre2_match_data_create(1, NULL);
    int rc = pcre2_match(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0, 0, md, NULL);
    pcre2_match_data_free(md);
    pcre2_code_free(re);
    return rc >= 0 ? 1 : 0;
}

hsh_string hsh_regex_find(hsh_string pattern, hsh_string text) {
    if (!pattern || !text) return "";
    int errcode; PCRE2_SIZE erroffset;
    pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
        0, &errcode, &erroffset, NULL);
    if (!re) return "";
    pcre2_match_data* md = pcre2_match_data_create(1, NULL);
    int rc = pcre2_match(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0, 0, md, NULL);
    hsh_string result = "";
    if (rc >= 0) {
        PCRE2_SIZE* ov = pcre2_get_ovector_pointer(md);
        size_t len = ov[1] - ov[0];
        char* out = (char*)malloc(len + 1);
        if (out) { memcpy(out, text + ov[0], len); out[len] = '\0'; result = out; }
    }
    pcre2_match_data_free(md);
    pcre2_code_free(re);
    return result;
}

hsh_string hsh_regex_replace(hsh_string pattern, hsh_string replacement, hsh_string text) {
    if (!pattern || !text || !replacement) return text ? text : "";
    int errcode; PCRE2_SIZE erroffset;
    pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
        0, &errcode, &erroffset, NULL);
    if (!re) return text;
    PCRE2_SIZE outlen = strlen(text) * 2 + strlen(replacement) + 64;
    PCRE2_UCHAR* out = (PCRE2_UCHAR*)malloc(outlen);
    if (!out) { pcre2_code_free(re); return text; }
    int rc = pcre2_substitute(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0,
        PCRE2_SUBSTITUTE_GLOBAL | PCRE2_SUBSTITUTE_EXTENDED, NULL, NULL,
        (PCRE2_SPTR)replacement, PCRE2_ZERO_TERMINATED, out, &outlen);
    pcre2_code_free(re);
    if (rc < 0) { free(out); return text; }
    return (hsh_string)out;
}

/* Extract all matches — returns newline-separated list */
hsh_string hsh_regex_find_all(hsh_string pattern, hsh_string text) {
    if (!pattern || !text) return "";
    int errcode; PCRE2_SIZE erroffset;
    pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
        0, &errcode, &erroffset, NULL);
    if (!re) return "";
    pcre2_match_data* md = pcre2_match_data_create(4, NULL);
    char* buf = NULL; size_t total = 0, cap = 0;
    PCRE2_SIZE offset = 0;
    size_t tlen = strlen(text);
    while (offset <= tlen) {
        int rc = pcre2_match(re, (PCRE2_SPTR)text, tlen, offset, 0, md, NULL);
        if (rc < 0) break;
        PCRE2_SIZE* ov = pcre2_get_ovector_pointer(md);
        size_t mlen = ov[1] - ov[0];
        if (total + mlen + 2 > cap) {
            cap = (cap + mlen + 2) * 2;
            char* nb = (char*)realloc(buf, cap);
            if (!nb) break;
            buf = nb;
        }
        memcpy(buf + total, text + ov[0], mlen); total += mlen;
        buf[total++] = '\n';
        offset = ov[1] == offset ? offset + 1 : ov[1];
    }
    pcre2_match_data_free(md);
    pcre2_code_free(re);
    if (!buf) return "";
    buf[total] = '\0';
    return buf;
}
