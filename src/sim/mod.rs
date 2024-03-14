use crate::ast::sim::SimInstr;

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
        let word = &self.mem[self.pc as usize];
        let instr = SimInstr::decode(word.data);
        self.pc += 1;

        match instr {
            SimInstr::Br(cc, off)  => {
                if cc & self.cc != 0 {
                    self.pc = self.pc.wrapping_add_signed(off.get());
                }
            },
            SimInstr::Add(dr, sr1, sr2) => {
                let val1 = self.reg_file[sr1.0 as usize].data;
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get(),
                    crate::ast::ImmOrReg::Reg(r2) => self.reg_file[r2.0 as usize].data as i16,
                };

                let result = val1.wrapping_add_signed(val2);
                self.reg_file[dr.0 as usize].set(result);
                self.set_cc(result);
            },
            SimInstr::Ld(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = self.mem[ea as usize].data;
                self.reg_file[dr.0 as usize].set(val);
                self.set_cc(val);
            },
            SimInstr::St(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = self.reg_file[sr.0 as usize].data;
                self.mem[ea as usize].set(val);
            },
            SimInstr::Jsr(op) => {
                let off = match op {
                    crate::ast::ImmOrReg::Imm(off) => off.get(),
                    crate::ast::ImmOrReg::Reg(br)  => self.reg_file[br.0 as usize].data as i16,
                };

                self.reg_file[0b111].set(self.pc);
                self.pc = self.pc.wrapping_add_signed(off);
                self.sr_entered += 1;
            },
            SimInstr::And(dr, sr1, sr2) => {
                let val1 = self.reg_file[sr1.0 as usize].data;
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get() as u16,
                    crate::ast::ImmOrReg::Reg(r2) => self.reg_file[r2.0 as usize].data,
                };

                let result = val1 & val2;
                self.reg_file[dr.0 as usize].set(result);
                self.set_cc(result);
            },
            SimInstr::Ldr(dr, br, off) => {
                let ea = self.reg_file[br.0 as usize].data.wrapping_add_signed(off.get());

                let val = self.mem[ea as usize].data;
                self.reg_file[dr.0 as usize].set(val);
                self.set_cc(val);
            },
            SimInstr::Str(sr, br, off) => {
                let ea = self.reg_file[br.0 as usize].data.wrapping_add_signed(off.get());
                
                let val = self.reg_file[sr.0 as usize].data;
                self.mem[ea as usize].set(val);
            },
            SimInstr::Rti => todo!("rti not yet implemented"),
            SimInstr::Not(dr, sr) => {
                let val1 = self.reg_file[sr.0 as usize].data;
                
                let result = !val1;
                self.reg_file[dr.0 as usize].set(result);
                self.set_cc(result);
            },
            SimInstr::Ldi(dr, off) => {
                let ea = self.mem[self.pc.wrapping_add_signed(off.get()) as usize].data;

                let val = self.mem[ea as usize].data;
                self.reg_file[dr.0 as usize].set(val);
                self.set_cc(val);
            },
            SimInstr::Sti(sr, off) => {
                let ea = self.mem[self.pc.wrapping_add_signed(off.get()) as usize].data;

                let val = self.reg_file[sr.0 as usize].data;
                self.mem[ea as usize].set(val);
            },
            SimInstr::Jmp(br) => {
                let off = self.reg_file[br.0 as usize].data as i16;
                self.pc = self.pc.wrapping_add_signed(off);

                // check for RET
                if br.0 == 7 {
                    self.sr_entered = self.sr_entered.saturating_sub(1);
                }
            },
            SimInstr::Lea(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                self.reg_file[dr.0 as usize].set(ea);
            },
            SimInstr::Trap(vect) => {
                self.pc = self.mem[vect.get() as usize].data;
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

    fn set(&mut self, word: u16) {
        self.data = word;
        self.init = true;
    }
}