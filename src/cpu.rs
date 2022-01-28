use std::collections::HashMap;
use crate::opcodes;
use crate::bus::Bus;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///

    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

pub enum Direction {
    Left,
    Right
}

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub stack_pointer: u8,
    pub bus: Bus
}

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data)
    }
    fn mem_read_u16(&self, pos: u16) -> u16 {
        self.bus.mem_read_u16(pos)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        self.bus.mem_write_u16(pos, data)
    }
}

impl CPU {
    pub fn new(bus: Bus) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::from_bits_truncate(0b100100),
            stack_pointer: STACK_RESET,
            program_counter: 0,
            bus: bus
        }
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.program_counter = 0x0600;
        self.run();
    }

    pub fn load(&mut self, program: Vec<u8>) {
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0600 + i, program[i as usize]);
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.stack_pointer = STACK_RESET;
        self.status = CpuFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes.get(&code).expect(&format!("OpCode {:x} is not recognized", code));

            match code {
                /* LDA */
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }

                /* LDX */
                0xa2 | 0xae | 0xbe | 0xa6 | 0xb6 => {
                    self.ldx(&opcode.mode);
                }

                /* LDY */
                0xa0 | 0xac | 0xbc | 0xa4 | 0xb4 => {
                    self.ldy(&opcode.mode);
                }

                /* STA */
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                /* STX */
                0x8e | 0x86 | 0x96 => {
                    self.stx(&opcode.mode);
                }

                /* STY */
                0x8c | 0x84 | 0x94 => {
                    self.sty(&opcode.mode);
                }

                0xaa => self.tax(),
                0xa8 => self.tay(),
                0x8a => self.txa(),
                0x98 => self.tya(),

                0x48 => self.stack_push(self.register_a),
                0x08 => self.stack_push(self.status.bits()),
                0x68 => self.pla(),
                0x28 => self.plp(),

                /* ASL */
                0x0a => self.asl_accumulator(),
                0x0e | 0x1e | 0x06 | 0x16 => self.asl_mem(&opcode.mode),

                /* LSR */
                0x4a => self.lsr_accumulator(),
                0x4e | 0x5e | 0x46 | 0x56 => self.lsr_mem(&opcode.mode),

                /* ROL */
                0x2a => self.rol_accumulator(),
                0x2e | 0x3e | 0x26 | 0x36 => self.rol_mem(&opcode.mode),

                /* ROR */
                0x6a => self.ror_accumulator(),
                0x6e | 0x7e | 0x66 | 0x76 => self.ror_mem(&opcode.mode),

                /* AND */
                0x29 | 0x2d | 0x3d | 0x39 | 0x25 | 0x35 | 0x21 | 0x31 => self.and(&opcode.mode),

                /* EOR */
                0x49 | 0x4d | 0x5d | 0x59 | 0x45 | 0x55 | 0x41 | 0x51 => self.eor(&opcode.mode),

                /* ORA */
                0x09 | 0x0d | 0x1d | 0x19 | 0x05 | 0x15 | 0x01 | 0x11 => self.ora(&opcode.mode),

                /* BIT */
                0x2c | 0x24 => self.bit(&opcode.mode),

                /* ADC */
                0x69 | 0x6d | 0x7d | 0x79 | 0x65 | 0x75 | 0x61 | 0x71 => self.adc(&opcode.mode),

                /* SBC */
                0xe9 | 0xed | 0xfd | 0xf9 | 0xe5 | 0xf5 | 0xe1 | 0xf1 => self.sbc(&opcode.mode),

                /* CMP */
                0xc9 | 0xcd | 0xdd | 0xd9 | 0xc5 | 0xd5 | 0xc1 | 0xd1 => self.compare(&opcode.mode, self.register_a),

                /* CPX */
                0xe0 | 0xec | 0xe4 => self.compare(&opcode.mode, self.register_x),

                /* CPY */
                0xc0 | 0xcc | 0xc4 => self.compare(&opcode.mode, self.register_y),

                /* DEC */
                0xce | 0xde | 0xc6 | 0xd6 => self.dec(&opcode.mode),

                /* DEX */
                0xca => self.dex(),

                /* DEY */
                0x88 => self.dey(),

                /* INC */
                0xee | 0xfe | 0xe6 | 0xf6 => self.inc(&opcode.mode),

                /* INX */
                0xe8 => self.inx(),

                /* INY */
                0xc8 => self.iny(),

                /* CLC */
                0x18 => self.status.remove(CpuFlags::CARRY),

                /* CLI */
                0x58 => self.status.remove(CpuFlags::INTERRUPT_DISABLE),

                /* CLV */
                0xb8 => self.status.remove(CpuFlags::OVERFLOW),

                /* SEC */
                0x38 => self.status.insert(CpuFlags::CARRY),

                /* SEI */
                0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE),

                /* JMP Absolute */
                0x4c => self.jmp_absolute(),

                /* JMP Indirect */
                0x6c => self.jmp_indirect(),

                /* BCC */
                0x90 => self.bcc(),

                /* BCS */
                0xb0 => self.bcs(),

                /* BEQ */
                0xf0 => self.beq(),

                /* BMI */
                0x30 => self.bmi(),

                /* BNE */
                0xd0 => self.bne(),

                /* BPL */
                0x10 => self.bpl(),

                /* BVC */
                0x50 => self.bvc(),

                /* BVS */
                0x70 => self.bvs(),

                0x00 => return,
                _ => todo!()
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result >> 7 == 1 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }

    fn update_carry_flag(&mut self, result: bool) {
        match result {
            true => self.status.insert(CpuFlags::CARRY),
            false => self.status.remove(CpuFlags::CARRY),
        }
    }

    fn update_overflow_flag(&mut self, result: bool) {
        match result {
            true => self.status.insert(CpuFlags::OVERFLOW),
            false => self.status.remove(CpuFlags::OVERFLOW)
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                pos.wrapping_add(self.register_x) as u16
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                pos.wrapping_add(self.register_y) as u16
            }
            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                base.wrapping_add(self.register_x as u16)
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                base.wrapping_add(self.register_y as u16)
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                deref_base.wrapping_add(self.register_y as u16)
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.set_register_a(value & self.register_a);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.set_register_a(value ^ self.register_a);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.set_register_a(value | self.register_a);
    }

    fn asl_mem(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = self.asl(value);
        self.mem_write(addr, new_value);
    }

    fn asl_accumulator(&mut self) {
        let value = self.register_a;
        let new_value = self.asl(value);

        self.register_a = new_value;
    }

    fn asl(&mut self, value: u8) -> u8 {
        let carry: bool = value & 0b1000_0000 == 0b1000_0000;
        self.update_carry_flag(carry);

        let new_value: u8 = value << 1;
        self.update_zero_and_negative_flags(new_value);
        new_value
    }


    fn lsr_mem(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = self.lsr(value);
        self.mem_write(addr, new_value);
    }

    fn lsr_accumulator(&mut self) {
        let value = self.register_a;
        let new_value = self.lsr(value);

        self.register_a = new_value;
    }

    fn lsr(&mut self, value: u8) -> u8 {
        let carry: bool = value & 0b0000_0001 == 0b0000_0001;
        self.update_carry_flag(carry);

        let new_value: u8 = value >> 1;
        self.update_zero_and_negative_flags(new_value);
        new_value
    }

    fn rol_accumulator(&mut self) {
        let value = self.register_a;
        let new_value = self.rotate(value, &Direction::Left);

        self.register_a = new_value;
    }

    fn rol_mem(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = self.rotate(value, &Direction::Left);
        self.mem_write(addr, new_value);
    }

    fn ror_accumulator(&mut self) {
        let value = self.register_a;
        let new_value = self.rotate(value, &Direction::Right);

        self.register_a = new_value;
    }

    fn ror_mem(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = self.rotate(value, &Direction::Right);
        self.mem_write(addr, new_value);
    }

    fn rotate(&mut self, value: u8, direction: &Direction) -> u8 {
        let carry: bool;
        let new_value: u8;

        match direction {
            Direction::Left => {
                carry = value & 0b1000_0000 == 0b1000_0000;
                new_value = value.rotate_left(1);
            }

            Direction::Right => {
                carry = value & 0b0000_0001 == 0b0000_0001;
                new_value = value.rotate_right(1);
            }
        }

        self.update_carry_flag(carry);
        self.update_zero_and_negative_flags(new_value);
        new_value
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = value & self.register_a;

        self.update_zero_and_negative_flags(new_value);
        self.update_overflow_flag(new_value & 0b0100_0000 == 0b0100_0000);
    }

    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (if self.status.contains(CpuFlags::CARRY) {
            1
        } else {
            0
        }) as u16;

        self.update_carry_flag(sum > 0xff);

        let result = sum as u8;

        if (data ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW);
        }

        self.set_register_a(result);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.add_to_register_a(value);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.add_to_register_a(((value as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn compare(&mut self, mode: &AddressingMode, comparator: u8) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        if value <= comparator {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(comparator.wrapping_sub(value));
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = value.wrapping_sub(1);

        self.mem_write(addr, new_value);
        self.update_zero_and_negative_flags(new_value);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        let new_value = value.wrapping_add(1);

        self.mem_write(addr, new_value);
        self.update_zero_and_negative_flags(new_value);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);
        self.set_register_a(value);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn pla(&mut self) {
        let data = self.stack_pop();
        self.set_register_a(data);
    }

    fn plp(&mut self) {
        self.status.bits = self.stack_pop();
        self.status.remove(CpuFlags::BREAK);
        self.status.insert(CpuFlags::BREAK2);
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write((STACK as u16) + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_pointer as u16)
    }

    fn bcc(&mut self) {
        if !self.status.contains(CpuFlags::CARRY) {
            self.jmp_absolute();
        }
    }

    fn bcs(&mut self) {
        if self.status.contains(CpuFlags::CARRY) {
            self.jmp_absolute();
        }
    }

    fn beq(&mut self) {
        if self.status.contains(CpuFlags::ZERO) {
            self.jmp_absolute();
        }
    }

    fn bmi(&mut self) {
        if self.status.contains(CpuFlags::NEGATIV) {
            self.jmp_absolute();
        }
    }

    fn bne(&mut self) {
        if !self.status.contains(CpuFlags::ZERO) {
            self.jmp_absolute();
        }
    }

    fn bpl(&mut self) {
        if !self.status.contains(CpuFlags::NEGATIV) {
            self.jmp_absolute();
        }
    }

    fn bvc(&mut self) {
        if !self.status.contains(CpuFlags::OVERFLOW) {
            self.jmp_absolute();
        }
    }

    fn bvs(&mut self) {
        if self.status.contains(CpuFlags::OVERFLOW) {
            self.jmp_absolute();
        }
    }

    fn jmp_absolute(&mut self) {
        let addr = self.mem_read_u16(self.program_counter);
        self.program_counter = addr;
    }

    fn jmp_indirect(&mut self) {
        let addr = self.mem_read_u16(self.program_counter);
        // let indirect_ref = self.mem_read_u16(mem_address);
        //6502 bug mode with with page boundary:
        //  if address $3000 contains $40, $30FF contains $80, and $3100 contains $50,
        // the result of JMP ($30FF) will be a transfer of control to $4080 rather than $5080 as you intended
        // i.e. the 6502 took the low byte of the address from $30FF and the high byte from $3000

        let indirect_ref = if addr & 0x00FF == 0x00FF {
            let lo = self.mem_read(addr);
            let hi = self.mem_read(addr & 0xFF00);
            (hi as u16) << 8 | (lo as u16)
        } else {
            self.mem_read_u16(addr)
        };

        self.program_counter = indirect_ref;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cartridge::test;

    #[test]
    fn test_0xa9_lda_immediate_load_data() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);

        assert_eq!(cpu.register_a, 5);
        assert_eq!(cpu.status.bits() & 0b0000_0010, 0b00);
        assert_eq!(cpu.status.bits() & 0b1000_0000, 0);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert_eq!(cpu.status.bits() & 0b0000_0010, 0b10);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x0A, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10);
    }

    #[test]
    fn test_0xa8_tay_move_a_to_y() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0x0A, 0xa8, 0x00]);

        assert_eq!(cpu.register_y, 10);
    }

    #[test]
    fn test_0x8a_txa_move_x_to_a() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa2, 0x0a, 0x8a, 0x00]);

        assert_eq!(cpu.register_a, 10)
    }

    #[test]
    fn test_0x98_tya_move_y_to_a() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa0, 0x0a, 0x98, 0x00]);

        assert_eq!(cpu.register_a, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_ldx_from_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa6, 0x10, 0x00]);

        assert_eq!(cpu.register_x, 0x55);
    }

    #[test]
    fn test_ldy_from_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa4, 0x10, 0x00]);

        assert_eq!(cpu.register_y, 0x55);
    }

    #[test]
    fn test_sta_to_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0x55;

        /* Skip load and run */
        cpu.load(vec![0x85, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x55);
    }

    #[test]
    fn test_stx_to_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_x = 0x55;

        /* Skip load and run */
        cpu.load(vec![0x86, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x55);
    }

    #[test]
    fn test_sty_to_memory() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_y = 0x55;

        /* Skip load and run */
        cpu.load(vec![0x84, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x55);
    }

    #[test]
    fn test_pha_push_a_to_stack() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0x55;
        cpu.stack_pointer = STACK_RESET;

        /* Skip load and run */
        cpu.load(vec![0x48, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(((STACK as u16) + (cpu.stack_pointer as u16)) + 1), 0x55);
    }

    #[test]
    fn test_php_push_status_to_stack() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0x55;
        cpu.stack_pointer = STACK_RESET;

        /* Skip load and run */
        cpu.load(vec![0x08, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(((STACK as u16) + (cpu.stack_pointer as u16)) + 1), cpu.status.bits());
    }

    #[test]
    fn test_pla_pop_stack_to_a() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0x55;
        cpu.stack_pointer = STACK_RESET;

        /* Skip load and run */
        cpu.load(vec![0x48, 0xa9, 0x00, 0x68, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_plp_pop_stack_to_status() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1100101;
        cpu.stack_pointer = STACK_RESET;

        /* Skip load and run */
        cpu.load(vec![0x48, 0x28, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.bits(), 0b1100101);
    }

    #[test]
    fn test_asl_accumulator_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x0a, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b0011_0010);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_asl_mem_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0b1001_1001);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x0e, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0b0011_0010);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_lsr_accumulator_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x4a, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b0100_1100);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_lsr_mem_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0b1001_1001);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x4e, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0b0100_1100);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_rol_accumulator_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x2a, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b0011_0011);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_rol_mem_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0b1001_1001);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x2e, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0b0011_0011);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_ror_accumulator_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x6a, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b1100_1100);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_ror_mem_with_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0b1001_1001);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x6e, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0b1100_1100);
        assert_eq!(cpu.status.bits() & 0b0000_0001, 0b0000_0001); // Carry flag should be set
    }

    #[test]
    fn test_and_immediate() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x29, 0b1100_1100, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b1000_1000);
    }

    #[test]
    fn test_eor_immediate() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x49, 0b1100_1100, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b0101_0101);
    }

    #[test]
    fn test_ora_immediate() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.register_a = 0b1001_1001;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x09, 0b1100_1100, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 0b1101_1101);
    }

    #[test]
    fn test_bit() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0b1100_0000);
        cpu.register_a = 0b1111_1111;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x2c, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.bits() & 0b1100_0001, 0b1100_0000);
    }

    #[test]
    fn test_adc_without_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_a = 0x50;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x69, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 96);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }

    #[test]
    fn test_sbc_without_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_a = 0x1e;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x38, 0xe9, 0x0a, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_a, 20);
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }

    #[test]
    fn test_cmp_equal_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_a = 0x1e;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xc9, 0x1e, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::ZERO), true);
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
    }

    #[test]
    fn test_cmp_negative() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_a = 0x1e;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xc9, 0x1f, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::NEGATIV), true);
    }

    #[test]
    fn test_dec() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.mem_write_u16(0x10, 0x1f);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xc6, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x1e);
    }

    #[test]
    fn test_dex() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_x = 0x1f;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xca, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_x, 0x1e);
    }

    #[test]
    fn text_dey() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.register_y = 0x1f;
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x88, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.register_y, 0x1e);
    }

    #[test]
    fn test_inc() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.mem_write_u16(0x10, 0x1e);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xe6, 0x10, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x1f);
    }

    #[test]
    fn test_clear_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.status.insert(CpuFlags::CARRY);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x18, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), false);
    }

    #[test]
    fn test_set_carry() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.status.remove(CpuFlags::CARRY);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x38, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::CARRY), true);
    }

    #[test]
    fn test_clear_interrupt_disable() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.status.insert(CpuFlags::INTERRUPT_DISABLE);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x58, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::INTERRUPT_DISABLE), false);
    }

    #[test]
    fn test_set_interrupt_disable() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.status.remove(CpuFlags::INTERRUPT_DISABLE);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0x78, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::INTERRUPT_DISABLE), true);
    }

    #[test]
    fn test_clear_overflow() {
        let bus = Bus::new(test::test_rom());
        let mut cpu = CPU::new(bus);

        cpu.status.insert(CpuFlags::OVERFLOW);
        cpu.stack_pointer = STACK_RESET;

        cpu.load(vec![0xb8, 0x00]);
        cpu.program_counter = 0x0600;

        cpu.run();
        assert_eq!(cpu.status.contains(CpuFlags::OVERFLOW), false);
    }
}