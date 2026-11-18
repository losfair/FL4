//! Scalar MOV and MOVZX forms for SNP MMIO faults in 64-bit userspace. The caller
//! fetches instruction bytes from executable private mappings and validates
//! the resulting memory operand against its user page tables.
#[derive(Debug, PartialEq, Eq)]
pub struct Access {
    pub address: u64,
    pub bytes: u64,
    pub length: u64,
    pub op: Operation,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operation {
    Read {
        register: usize,
        shift: u8,
        dest_bytes: u64,
    },
    Write(u64),
}

struct Instruction<F> {
    fetch: F,
    length: u64,
}

impl<F: FnMut(u64) -> Option<u8>> Instruction<F> {
    fn byte(&mut self) -> Option<u8> {
        if self.length == 15 {
            return None;
        }
        let result = (self.fetch)(self.length)?;
        self.length += 1;
        Some(result)
    }

    fn immediate(&mut self, bytes: u64) -> Option<u64> {
        let mut value = 0;
        for i in 0..bytes {
            value |= u64::from(self.byte()?) << (8 * i);
        }
        Some(value)
    }
}

pub fn decode(
    rip: u64,
    registers: &[u64; 16],
    fetch: impl FnMut(u64) -> Option<u8>,
) -> Option<Access> {
    let mut i = Instruction { fetch, length: 0 };
    let mut opcode = i.byte()?;
    let word = opcode == 0x66;
    if word {
        opcode = i.byte()?;
    }
    let rex = if (0x40..=0x4f).contains(&opcode) {
        let rex = opcode;
        opcode = i.byte()?;
        rex
    } else {
        0
    };
    let operand_bytes = if rex & 8 != 0 {
        8
    } else if word {
        2
    } else {
        4
    };
    let movzx = opcode == 0x0f;
    if movzx {
        opcode = i.byte()?;
    }
    let bytes = match (movzx, opcode) {
        (true, 0xb6) | (false, 0x88 | 0x8a | 0xc6) => 1,
        (true, 0xb7) => 2,
        (false, 0x89 | 0x8b | 0xc7) => operand_bytes,
        _ => return None,
    };
    let dest_bytes = if movzx { operand_bytes } else { bytes };
    let modrm = i.byte()?;
    let mode = modrm >> 6;
    if mode == 3 {
        return None;
    }
    let reg = (modrm >> 3 & 7) as usize;
    let rm = modrm & 7;
    let mut rip_relative = false;
    let mut disp32 = mode == 2;
    let mut address = if rm == 4 {
        let sib = i.byte()?;
        let index = ((sib >> 3 & 7) | ((rex & 2) << 2)) as usize;
        let scaled = if index == 4 {
            0
        } else {
            registers[index] << (sib >> 6)
        };
        let base = sib & 7;
        if mode == 0 && base == 5 {
            disp32 = true;
            scaled
        } else {
            scaled.wrapping_add(registers[(base | ((rex & 1) << 3)) as usize])
        }
    } else if mode == 0 && rm == 5 {
        rip_relative = true;
        disp32 = true;
        0
    } else {
        registers[(rm | ((rex & 1) << 3)) as usize]
    };
    if disp32 {
        address = address.wrapping_add(i.immediate(4)? as i32 as i64 as u64);
    } else if mode == 1 {
        address = address.wrapping_add(i.byte()? as i8 as i64 as u64);
    }
    let (register, shift) = if !movzx && rex == 0 && bytes == 1 && reg >= 4 {
        (reg - 4, 8)
    } else {
        (reg | ((rex & 4) << 1) as usize, 0)
    };
    let op = match opcode {
        0x8a | 0x8b | 0xb6 | 0xb7 => Operation::Read {
            register,
            shift,
            dest_bytes,
        },
        0x88 | 0x89 => Operation::Write(registers[register] >> shift),
        _ if reg != 0 => return None,
        _ if bytes == 8 => Operation::Write(i.immediate(4)? as i32 as i64 as u64),
        _ => Operation::Write(i.immediate(bytes)?),
    };
    if rip_relative {
        address = address.wrapping_add(rip).wrapping_add(i.length);
    }
    Some(Access {
        address,
        bytes,
        length: i.length,
        op,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_nvme_register_loads_and_stores() {
        let mut regs = [0; 16];
        regs[0] = 3;
        regs[3] = 0x1234_5678_9abc_def0;
        let mov = |b: &[u8]| decode(0x401000, &regs, |i| b.get(i as usize).copied());
        assert_eq!(
            mov(&[0x8b, 0x04, 0x25, 0x1c, 0, 0, 0x20]),
            Some(Access {
                address: 0x2000001c,
                bytes: 4,
                length: 7,
                op: Operation::Read {
                    register: 0,
                    shift: 0,
                    dest_bytes: 4,
                },
            })
        );
        assert_eq!(
            mov(&[0x48, 0x89, 0x1c, 0x25, 0x28, 0, 0, 0x20]),
            Some(Access {
                address: 0x20000028,
                bytes: 8,
                length: 8,
                op: Operation::Write(regs[3]),
            })
        );
        assert_eq!(
            mov(&[0xc7, 0x04, 0x85, 0, 0, 0, 0x20, 1, 0, 0, 0]),
            Some(Access {
                address: 0x2000000c,
                bytes: 4,
                length: 11,
                op: Operation::Write(1),
            })
        );
    }

    #[test]
    fn decodes_movzx_destination_width_and_register() {
        let mut regs = [0; 16];
        regs[0] = 0x1000;
        let decode = |b: &[u8]| decode(0, &regs, |i| b.get(i as usize).copied()).unwrap();
        let byte = decode(&[0x0f, 0xb6, 0x20]); // movzbl (%rax), %esp
        assert_eq!(byte.bytes, 1);
        assert_eq!(
            byte.op,
            Operation::Read {
                register: 4,
                shift: 0,
                dest_bytes: 4
            }
        );
        let word = decode(&[0x4c, 0x0f, 0xb7, 0x00]); // movzwq (%rax), %r8
        assert_eq!(word.bytes, 2);
        assert_eq!(
            word.op,
            Operation::Read {
                register: 8,
                shift: 0,
                dest_bytes: 8
            }
        );
    }

    #[test]
    fn includes_full_instruction_length_in_rip_relative_address() {
        let b = [
            0x48, 0xc7, 0x05, 0xfc, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        ];
        let mov = |b: &[u8]| decode(0x4000, &[0; 16], |i| b.get(i as usize).copied());
        assert_eq!(
            mov(&b),
            Some(Access {
                address: 0x4007,
                bytes: 8,
                length: 11,
                op: Operation::Write(u64::MAX),
            })
        );
        assert!(mov(&b[..9]).is_none());
        assert!(mov(&[0x89, 0xc0]).is_none());
        assert!(mov(&[0xf0, 0x89, 0]).is_none());
    }
}
