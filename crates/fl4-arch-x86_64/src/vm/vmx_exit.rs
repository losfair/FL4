//! Defined VM-exit metadata from a VMCS shared by successive VCPUs.
//!
//! Intel SDM vol. 3C §§28.2.2–28.2.5: invalid fields, and undefined bits
//! within otherwise valid fields, can retain the preceding VCPU's values.
use fl4_core::vcpu::vmx::*;

const VALID: u64 = 1 << 31;
const ERROR: u64 = 1 << 11;

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct Metadata {
    pub interrupt: u64,
    pub interrupt_error: u64,
    pub vector: u64,
    pub vector_error: u64,
    pub length: u64,
    pub instruction: u64,
}

fn event(info: u64) -> u64 {
    if info & VALID != 0 {
        info & (VALID | 0xfff)
    } else {
        0
    }
}

fn software_event(info: u64) -> bool {
    info & VALID != 0 && matches!((info >> 8) & 7, 4..=6)
}

fn has_length(reason: u64, qualification: u64, interrupt: u64, vector: u64) -> bool {
    match reason {
        // #BP/INTO/INT1 exits, or faults during software-event delivery.
        0 => software_event(interrupt) || software_event(vector),
        // CALL/IRET/JMP task switches; IDT task gates only for software events.
        9 => qualification >> 30 & 3 != 3 || software_event(vector),
        // Trap-like CR8 and x2APIC WRMSR exits cannot occur: FL4 does not
        // enable TPR shadowing or virtualize x2APIC mode.
        10..=32 | 36 | 39 | 40 | 46 | 47 | 50 | 51 | 53..=55 | 57..=61 | 63 | 64 | 67 | 68 => true,
        // APIC access: only linear accesses during software-event delivery.
        44 => qualification >> 12 & 15 == 3 && software_event(vector),
        // EPT violation, PML full, SPP: only during software-event delivery.
        // EPT misconfiguration does not define an instruction length.
        48 | 62 | 66 => software_event(vector),
        _ => false,
    }
}

fn instruction_info(
    reason: u64,
    qualification: u64,
    basic: u64,
    read: &mut impl FnMut(u64) -> u64,
) -> u64 {
    if reason == 30 {
        // Only INS/OUTS define this field, and only with VMX_BASIC[54].
        if qualification & (1 << 4) == 0 || basic & (1 << 54) == 0 {
            return 0;
        }
        let mask = (7 << 7)
            | if qualification & (1 << 3) == 0 {
                7 << 15
            } else {
                0
            };
        return read(DATA_EXIT_INSTRUCTION_INFO) & mask;
    }
    if matches!(reason, 57 | 61 | 67 | 68) {
        return read(DATA_EXIT_INSTRUCTION_INFO) & ((15 << 3) | (3 << 11));
    }
    if !matches!(
        reason,
        19 | 21..=23 | 25 | 27 | 46 | 47 | 50 | 53 | 58 | 63 | 64
    ) {
        return 0;
    }
    let info = read(DATA_EXIT_INSTRUCTION_INFO);
    let mut mask = match reason {
        23 | 25 | 50 | 53 | 58 => 15 << 28, // Second register operand.
        46 | 47 => 3 << 28,                 // Descriptor instruction identity.
        _ => 0,
    };
    if matches!(reason, 23 | 25 | 47) {
        mask |= 1 << 10; // Register versus memory operand.
        if info & (1 << 10) != 0 {
            return info & (mask | (15 << 3));
        }
    }
    // Memory operands: address size, segment, index/base invalid bits.
    mask |= (7 << 7) | (7 << 15) | (1 << 22) | (1 << 27);
    if info & (1 << 22) == 0 {
        mask |= 3 | (15 << 18); // Scaling and index, only with a valid index.
    }
    if info & (1 << 27) == 0 {
        mask |= 15 << 23;
    }
    if reason == 46 && read(GUEST_CS_ACCESS_RIGHTS) & (1 << 13) == 0 {
        mask |= 1 << 11; // Operand size is undefined in 64-bit mode.
    }
    info & mask
}

pub(super) fn read(
    valid: bool,
    reason: u64,
    qualification: u64,
    basic: u64,
    mut read: impl FnMut(u64) -> u64,
) -> Metadata {
    let mut result = Metadata::default();
    if !valid {
        return result;
    }
    result.vector = event(read(DATA_IDT_VECTOR_INFO));
    if result.vector & ERROR != 0 {
        result.vector_error = read(DATA_IDT_VECTOR_ERROR);
    }
    if reason == 0 {
        let raw = read(DATA_EXIT_INTERRUPT_INFO);
        result.interrupt = event(raw);
        if result.interrupt & ERROR != 0 {
            result.interrupt_error = read(DATA_EXIT_INTERRUPT_ERROR);
        }
        // NMI-unblocking is undefined with a valid vector or a double fault.
        if result.interrupt != 0 && result.vector == 0 && result.interrupt & 255 != 8 {
            result.interrupt |= raw & (1 << 12);
        }
    }
    if has_length(reason, qualification, result.interrupt, result.vector) {
        result.length = read(DATA_EXIT_INSTRUCTION_LENGTH);
    }
    result.instruction = instruction_info(reason, qualification, basic, &mut read);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_entries_never_read_exit_metadata() {
        for reason in [0xffff_ffff, 33, 34, 41] {
            assert_eq!(
                read(false, reason, 0, 0, |_| panic!("stale VMCS read")),
                Metadata::default()
            );
        }
    }

    #[test]
    fn shared_vmcs_does_not_disclose_a_previous_vcpus_vector_or_error() {
        // A's EPT exit interrupted #PF delivery. B then exits on CPUID;
        // hardware clears only the vector's valid bit, retaining its payload.
        let mut vector = VALID | ERROR | (3 << 8) | 14;
        let snapshot = || {
            read(true, 48, 0, 0, |field| match field {
                DATA_IDT_VECTOR_INFO => vector,
                DATA_IDT_VECTOR_ERROR => 0x1234,
                _ => panic!("undefined field {field:x}"),
            })
        };
        assert_eq!(snapshot().vector_error, 0x1234);
        vector &= !VALID;
        let b = read(true, 10, 0, 0, |field| match field {
            DATA_IDT_VECTOR_INFO => vector,
            DATA_EXIT_INSTRUCTION_LENGTH => 2,
            _ => panic!("B read A's undefined field {field:x}"),
        });
        assert_eq!(
            b,
            Metadata {
                length: 2,
                ..Metadata::default()
            }
        );
    }

    #[test]
    fn software_event_faults_keep_the_length_and_valid_error_codes() {
        let info = read(true, 0, 0, 0, |field| match field {
            DATA_IDT_VECTOR_INFO => VALID | (4 << 8) | 0x80 | (1 << 12),
            DATA_EXIT_INTERRUPT_INFO => VALID | ERROR | (3 << 8) | 13 | (1 << 12),
            DATA_EXIT_INTERRUPT_ERROR => 0x42,
            DATA_EXIT_INSTRUCTION_LENGTH => 2,
            _ => panic!("undefined field {field:x}"),
        });
        assert_eq!(info.vector, VALID | (4 << 8) | 0x80);
        assert_eq!(info.vector_error, 0);
        assert_eq!(info.interrupt, VALID | ERROR | (3 << 8) | 13);
        assert_eq!(info.interrupt_error, 0x42);
        assert_eq!(info.length, 2);
    }

    #[test]
    fn lengths_are_defined_by_the_event_type_not_just_the_exit_reason() {
        for (reason, qualification, interrupt, vector, expected) in [
            (0, 0, VALID | (3 << 8) | 6, 0, false), // UD2 is a hardware exception.
            (0, 0, VALID | (6 << 8) | 3, 0, true),  // INT3.
            (0, 0, VALID | (5 << 8) | 1, 0, true),  // INT1.
            (0, 0, VALID | (3 << 8) | 1, 0, false), // Hardware #DB.
            (48, 0, 0, VALID | (3 << 8) | 14, false),
            (48, 0, 0, VALID | (4 << 8) | 0x80, true),
            (49, 0, 0, VALID | (4 << 8) | 0x80, false),
            (9, 0, 0, 0, true),
            (9, 3 << 30, 0, VALID | 0x20, false),
            (9, 3 << 30, 0, VALID | (4 << 8) | 0x80, true),
            (44, 3 << 12, 0, VALID | (4 << 8) | 0x80, true),
            (44, 10 << 12, 0, VALID | (4 << 8) | 0x80, false),
            (1, 0, 0, VALID | (4 << 8) | 0x80, false),
            (37, 0, 0, 0, false), // MTF, after an instruction retires.
            (56, 0, 0, 0, false), // APIC write, also trap-like.
            (75, 0, 0, 0, false), // Unknown/notification exit.
        ] {
            let info = read(true, reason, qualification, 0, |field| match field {
                DATA_IDT_VECTOR_INFO => vector,
                DATA_EXIT_INTERRUPT_INFO => interrupt,
                DATA_EXIT_INSTRUCTION_LENGTH if expected => 3,
                _ => panic!("undefined field {field:x} for exit {reason}"),
            });
            assert_eq!(info.length, if expected { 3 } else { 0 });
        }
    }

    #[test]
    fn io_and_wbinvd_do_not_read_undefined_instruction_information() {
        for (reason, qualification, basic) in [(30, 0, 1 << 54), (30, 1 << 4, 0), (54, 0, 0)] {
            assert_eq!(
                instruction_info(reason, qualification, basic, &mut |_| panic!(
                    "undefined read"
                )),
                0
            );
        }
        // INS has no defined segment field; OUTS does.
        assert_eq!(
            instruction_info(30, (1 << 4) | (1 << 3), 1 << 54, &mut |_| u64::MAX),
            7 << 7
        );
        assert_eq!(
            instruction_info(30, 1 << 4, 1 << 54, &mut |_| u64::MAX),
            (7 << 7) | (7 << 15)
        );
    }

    #[test]
    fn instruction_information_masks_undefined_operand_bits() {
        // RDRAND: only the register and operand size are meaningful.
        assert_eq!(
            instruction_info(57, 0, 0, &mut |_| u64::MAX),
            (15 << 3) | (3 << 11)
        );
        // Register VMREAD: no memory-address fields are meaningful.
        assert_eq!(
            instruction_info(23, 0, 0, &mut |_| u64::MAX),
            (15 << 28) | (1 << 10) | (15 << 3)
        );
        // VMCLEAR without index/base: their stale numbers and scaling vanish.
        assert_eq!(
            instruction_info(19, 0, 0, &mut |_| u64::MAX),
            (7 << 7) | (7 << 15) | (1 << 22) | (1 << 27)
        );
        for long_mode in [false, true] {
            let info = instruction_info(46, 0, 0, &mut |field| match field {
                DATA_EXIT_INSTRUCTION_INFO => u64::MAX,
                GUEST_CS_ACCESS_RIGHTS => {
                    if long_mode {
                        1 << 13
                    } else {
                        0
                    }
                }
                _ => panic!("unexpected field"),
            });
            assert_eq!(info & (1 << 11) != 0, !long_mode);
        }
    }
}
