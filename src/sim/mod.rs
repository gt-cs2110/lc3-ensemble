struct Simulator {
    blocks: [Word; 2usize.pow(16)],
    pc: u16
}
struct Word {
    data: u16,
    init: bool 
}

impl Simulator {
    fn new() -> Self {
        Self {
            blocks: std::array::from_fn(|_| Word::new()),
            pc: 0x3000
        }
    }

    fn start(&mut self) {
        loop {
            let instr = &self.blocks[self.pc as usize];
            let opcode = instr.data >> 12;
            match opcode {
                i => println!("invalid opcode {i:04b}")
            }
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
}