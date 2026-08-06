use std::collections::HashMap;

// ─── Vulnerability codes (matches H# web3_vuln_name) ─────────────────────────

const VULN_REENTRANCY:          u8 = 1;
const VULN_INTEGER_OVERFLOW:    u8 = 2;
const VULN_ACCESS_CONTROL:      u8 = 3;
const VULN_UNPROTECTED_SELFDESTRUCT: u8 = 4;
const VULN_TX_ORIGIN_AUTH:      u8 = 5;
const VULN_UNHANDLED_RETURN:    u8 = 6;
const VULN_DELEGATECALL_INJECT: u8 = 7;
const VULN_FRONT_RUNNING:       u8 = 8;

// ─── EVM opcodes we care about ────────────────────────────────────────────────

const OP_CALL:         u8 = 0xf1;
const OP_CALLCODE:     u8 = 0xf2;
const OP_DELEGATECALL: u8 = 0xf4;
const OP_STATICCALL:   u8 = 0xfa;
const OP_SELFDESTRUCT: u8 = 0xff;
const OP_SSTORE:       u8 = 0x55;
const OP_SLOAD:        u8 = 0x54;
const OP_ADD:          u8 = 0x01;
const OP_MUL:          u8 = 0x02;
const OP_SUB:          u8 = 0x03;
const OP_ORIGIN:       u8 = 0x32;
const OP_CALLER:       u8 = 0x33;
const OP_EQ:           u8 = 0x14;
const OP_JUMPI:        u8 = 0x57;
const OP_JUMP:         u8 = 0x56;
const OP_RETURN:       u8 = 0xf3;

// ─── Finding struct ───────────────────────────────────────────────────────────

#[repr(C)]
pub struct Finding {
    pub code:   u8,    // vulnerability code (VULN_*)
    pub offset: u32,   // bytecode offset
}

// ─── Pattern matchers ─────────────────────────────────────────────────────────

/// Check for reentrancy: CALL before SSTORE in same basic block.
/// Simplified: look for CALL followed by SSTORE within a window.
fn check_reentrancy(bytecode: &[u8]) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut i = 0usize;
    while i < bytecode.len() {
        if bytecode[i] == OP_CALL {
            // Scan next 64 opcodes for SSTORE
            let window = &bytecode[i+1 .. (i + 64).min(bytecode.len())];
            for (j, &op) in window.iter().enumerate() {
                if op == OP_SSTORE {
                    findings.push(Finding { code: VULN_REENTRANCY, offset: i as u32 });
                    break;
                }
                // Stop at another CALL or RETURN — different basic block
                if op == OP_CALL || op == OP_RETURN { break; }
                let _ = j;
            }
        }
        i += skip_push(bytecode, i);
    }
    findings
}

/// Check for unprotected SELFDESTRUCT: no JUMPI guard within 32 ops before it.
fn check_unprotected_selfdestruct(bytecode: &[u8]) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut i = 0usize;
    while i < bytecode.len() {
        if bytecode[i] == OP_SELFDESTRUCT {
            // Look back 32 bytes for a JUMPI (access guard)
            let look_back = if i > 32 { i - 32 } else { 0 };
            let guarded = bytecode[look_back..i].contains(&OP_JUMPI);
            if !guarded {
                findings.push(Finding { code: VULN_UNPROTECTED_SELFDESTRUCT, offset: i as u32 });
            }
        }
        i += skip_push(bytecode, i);
    }
    findings
}

/// Check for DELEGATECALL with a non-constant target (potential injection).
fn check_delegatecall(bytecode: &[u8]) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut i = 0usize;
    while i < bytecode.len() {
        if bytecode[i] == OP_DELEGATECALL {
            // If the previous opcode was not a PUSH (constant target) — flag it
            let prev = if i > 0 { bytecode[i - 1] } else { 0 };
            let is_constant_target = (0x60..=0x7f).contains(&prev); // PUSH1..PUSH32
            if !is_constant_target {
                findings.push(Finding { code: VULN_DELEGATECALL_INJECT, offset: i as u32 });
            }
        }
        i += skip_push(bytecode, i);
    }
    findings
}

/// Check for ORIGIN used in authorization (tx.origin == msg.sender anti-pattern).
fn check_tx_origin(bytecode: &[u8]) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut i = 0usize;
    while i + 2 < bytecode.len() {
        if bytecode[i] == OP_ORIGIN {
            // ORIGIN followed by EQ and JUMPI = tx.origin auth
            let window = &bytecode[i+1 .. (i + 8).min(bytecode.len())];
            let has_eq   = window.contains(&OP_EQ);
            let has_jumpi = window.contains(&OP_JUMPI);
            if has_eq && has_jumpi {
                findings.push(Finding { code: VULN_TX_ORIGIN_AUTH, offset: i as u32 });
            }
        }
        i += skip_push(bytecode, i);
    }
    findings
}

/// Check for unchecked arithmetic: ADD/MUL/SUB not followed by SafeMath pattern.
/// Heuristic: in pre-0.8 ABI (no built-in overflow check), these are risky.
fn check_integer_overflow(bytecode: &[u8]) -> Vec<Finding> {
    let mut findings = Vec::new();
    // Simple heuristic: if ADD or MUL appears more than 3 times without
    // accompanying JUMPI guards, flag as potential unchecked arithmetic.
    let arithmetic_count = bytecode.iter()
        .filter(|&&b| b == OP_ADD || b == OP_MUL || b == OP_SUB)
        .count();
    let jumpi_count = bytecode.iter().filter(|&&b| b == **&OP_JUMPI).count();

    // If there are more arithmetic ops than guards, likely no SafeMath
    if arithmetic_count > 3 && arithmetic_count > jumpi_count * 2 {
        // Find the first ADD/MUL offset
        for (i, &b) in bytecode.iter().enumerate() {
            if b == OP_ADD || b == OP_MUL {
                findings.push(Finding { code: VULN_INTEGER_OVERFLOW, offset: i as u32 });
                break;
            }
        }
    }
    findings
}

/// Skip PUSH instructions and their data bytes.
fn skip_push(bytecode: &[u8], i: usize) -> usize {
    let op = bytecode[i];
    if (0x60..=0x7f).contains(&op) {
        // PUSH1 = 0x60 (1 byte data), PUSH32 = 0x7f (32 bytes data)
        let data_bytes = (op - 0x5f) as usize;
        1 + data_bytes
    } else {
        1
    }
}

// ─── Exported C API ───────────────────────────────────────────────────────────

/// Analyze EVM bytecode for vulnerability patterns.
///
/// # Parameters
/// - `bytecode`: pointer to EVM bytecode bytes
/// - `len`:      number of bytes
/// - `report`:   output buffer — filled with packed `[code:u8, offset:u32le]` tuples
///
/// # Returns
/// Number of vulnerabilities found (0 = clean, -1 = error).
#[no_mangle]
pub extern "C" fn eiv_web3_analyze(
    bytecode: *const u8,
    len:      i32,
    report:   *mut u8,
) -> i32 {
    if bytecode.is_null() || len <= 0 { return -1; }
    let data = unsafe { std::slice::from_raw_parts(bytecode, len as usize) };

    let mut all_findings: Vec<Finding> = Vec::new();
    all_findings.extend(check_reentrancy(data));
    all_findings.extend(check_unprotected_selfdestruct(data));
    all_findings.extend(check_delegatecall(data));
    all_findings.extend(check_tx_origin(data));
    all_findings.extend(check_integer_overflow(data));

    // Pack findings into report buffer: [code:u8, offset:u32le] per finding
    if !report.is_null() {
        let report_buf = unsafe { std::slice::from_raw_parts_mut(report, all_findings.len() * 5) };
        for (i, f) in all_findings.iter().enumerate() {
            let base = i * 5;
            if base + 4 < report_buf.len() {
                report_buf[base]     = f.code;
                report_buf[base + 1] = (f.offset & 0xff) as u8;
                report_buf[base + 2] = ((f.offset >> 8)  & 0xff) as u8;
                report_buf[base + 3] = ((f.offset >> 16) & 0xff) as u8;
                report_buf[base + 4] = ((f.offset >> 24) & 0xff) as u8;
            }
        }
    }

    all_findings.len() as i32
}

/// Calculate the Shannon entropy of `len` bytes at `data`.
///
/// Returns a value in [0.0, 8.0]. Values above 7.5 suggest encryption
/// or obfuscation; values below 1.0 suggest mostly zero-padding.
#[no_mangle]
pub extern "C" fn eiv_entropy_score(data: *const u8, len: i32) -> f64 {
    if data.is_null() || len <= 0 { return 0.0; }
    let slice = unsafe { std::slice::from_raw_parts(data, len as usize) };

    let mut freq = [0u32; 256];
    for &byte in slice { freq[byte as usize] += 1; }

    let n = len as f64;
    let mut entropy = 0.0f64;
    for &count in &freq {
        if count > 0 {
            let p = count as f64 / n;
            entropy -= p * p.log2();
        }
    }
    entropy
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reentrancy_detected() {
        // CALL (0xf1) followed immediately by SSTORE (0x55)
        let bytecode = vec![0x60, 0x00, 0xf1, 0x55]; // PUSH1 0x00 CALL SSTORE
        let findings = check_reentrancy(&bytecode);
        assert!(!findings.is_empty());
        assert_eq!(findings[0].code, VULN_REENTRANCY);
    }

    #[test]
    fn selfdestruct_unguarded() {
        // SELFDESTRUCT with no JUMPI in the preceding 32 bytes
        let bytecode = vec![0xff];
        let findings = check_unprotected_selfdestruct(&bytecode);
        assert!(!findings.is_empty());
        assert_eq!(findings[0].code, VULN_UNPROTECTED_SELFDESTRUCT);
    }

    #[test]
    fn selfdestruct_guarded() {
        // JUMPI then SELFDESTRUCT — should NOT flag
        let mut bytecode = vec![0x57u8]; // JUMPI
        bytecode.extend(vec![0x00u8; 10]); // padding
        bytecode.push(0xff); // SELFDESTRUCT
        let findings = check_unprotected_selfdestruct(&bytecode);
        assert!(findings.is_empty());
    }

    #[test]
    fn entropy_zero_buffer() {
        let buf = vec![0u8; 64];
        let e = eiv_entropy_score(buf.as_ptr(), buf.len() as i32);
        assert_eq!(e, 0.0);
    }

    #[test]
    fn entropy_random_like() {
        // All 256 byte values — maximum entropy
        let buf: Vec<u8> = (0..=255u8).collect();
        let e = eiv_entropy_score(buf.as_ptr(), buf.len() as i32);
        // Should be very close to 8.0
        assert!(e > 7.9);
    }
}
