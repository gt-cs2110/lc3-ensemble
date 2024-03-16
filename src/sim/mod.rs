use crate::ast::sim::SimInstr;
use crate::ast::Reg;

struct Simulator {
    mem: [Word; 2usize.pow(16)],
    reg_file: [Word; 8],
    pc: u16,
    cc: u8,

    /// The number of subroutines or trap calls we've entered.
    /// 
    /// This is incremented when JSR/JSRR/TRAP is called,
    /// and decremented when RET/JMP R7/RTI is called.
    /// 
    /// If this is 0, this is considered the global state,
    /// and as such, decrementing should have no effect.
    /// 
    /// I am hoping this is large enough that it doesn't overflow :)
    sr_entered: u64
}
struct Word {
    data: u16,
    init: bool 
}

impl Simulator {
    fn new() -> Self {
        Self {
            mem: std::array::from_fn(|_| Word::new()),
            reg_file: std::array::from_fn(|_| Word::new()),
            pc: 0x3000,
            cc: 0b010,
            sr_entered: 0
        }
    }

    fn access_mem(&mut self, addr: u16) -> &mut Word {
        &mut self.mem[addr as usize]
    }
    fn access_reg(&mut self, reg: Reg) -> &mut Word {
        &mut self.reg_file[reg.0 as usize]
    }
    
    fn set_cc(&mut self, result: u16) {
        match (result as i16).cmp(&0) {
            std::cmp::Ordering::Less    => self.cc = 0b100,
            std::cmp::Ordering::Equal   => self.cc = 0b010,
            std::cmp::Ordering::Greater => self.cc = 0b001,
        }
    }
    fn start(&mut self) {
        loop {
            self.step_in();
        }
    }
    fn step_in(&mut self) {
        let word = self.access_mem(self.pc).get_unsigned();
        let instr = SimInstr::decode(word);
        self.pc += 1;

        match instr {
            SimInstr::BR(cc, off)  => {
                if cc & self.cc != 0 {
                    self.pc = self.pc.wrapping_add_signed(off.get());
                }
            },
            SimInstr::ADD(dr, sr1, sr2) => {
                let val1 = self.access_reg(sr1).get_unsigned();
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get(),
                    crate::ast::ImmOrReg::Reg(r2) => self.access_reg(r2).get_signed(),
                };

                let result = val1.wrapping_add_signed(val2);
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LD(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = self.access_mem(ea).get_unsigned();
                self.access_reg(dr).set(val);
                self.set_cc(val);
            },
            SimInstr::ST(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = self.access_reg(sr).get_unsigned();
                self.access_mem(ea).set(val);
            },
            SimInstr::JSR(op) => {
                let off = match op {
                    crate::ast::ImmOrReg::Imm(off) => off.get(),
                    crate::ast::ImmOrReg::Reg(br)  => self.access_reg(br).get_signed(),
                };

                self.reg_file[0b111].set(self.pc);
                self.pc = self.pc.wrapping_add_signed(off);
                self.sr_entered += 1;
            },
            SimInstr::AND(dr, sr1, sr2) => {
                let val1 = self.access_reg(sr1).get_unsigned();
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get() as u16,
                    crate::ast::ImmOrReg::Reg(r2) => self.access_reg(r2).get_unsigned(),
                };

                let result = val1 & val2;
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LDR(dr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());

                let val = self.access_mem(ea).get_unsigned();
                self.access_reg(dr).set(val);
                self.set_cc(val);
            },
            SimInstr::STR(sr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());
                
                let val = self.access_reg(sr).get_unsigned();
                self.access_mem(ea).set(val);
            },
            SimInstr::RTI => todo!("rti not yet implemented"),
            SimInstr::NOT(dr, sr) => {
                let val1 = self.access_reg(sr).get_unsigned();
                
                let result = !val1;
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LDI(dr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = self.access_mem(ea).get_unsigned();
                self.access_reg(dr).set(val);
                self.set_cc(val);
            },
            SimInstr::STI(sr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = self.access_reg(sr).get_unsigned();
                self.access_mem(ea).set(val);
            },
            SimInstr::JMP(br) => {
                let off = self.access_reg(br).get_signed();
                self.pc = self.pc.wrapping_add_signed(off);

                // check for RET
                if br.0 == 7 {
                    self.sr_entered = self.sr_entered.saturating_sub(1);
                }
            },
            SimInstr::LEA(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                self.access_reg(dr).set(ea);
            },
            SimInstr::TRAP(vect) => {
                self.pc = self.access_mem(vect.get()).get_unsigned();
                self.sr_entered += 1;
            },
        }
    }
    fn step_over(&mut self) {
        let curr_frame = self.sr_entered;
        self.step_in();
        // step until we have landed back in the same frame
        while curr_frame < self.sr_entered {
            self.step_in();
        }
    }
    fn step_out(&mut self) {
        let curr_frame = self.sr_entered;
        self.step_in();
        // step until we get out of this frame
        while curr_frame != 0 && curr_frame <= self.sr_entered {
            self.step_in();
        }
    }
}
impl Word {
    fn new() -> Self {
        Self {
            data: 0,
            init: false,
        }
    }

    fn get_unsigned(&self) -> u16 {
        self.data
    }
    fn get_signed(&self) -> i16 {
        self.data as i16
    }
    fn set(&mut self, word: u16) {
        self.data = word;
        self.init = true;
    }
}