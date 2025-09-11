#[derive(Clone, Debug)]
pub enum Instr {
    Halt,
    Push(u16),
    Load(u8),
    Store(u8),
    Loadp,
    Storep,
    Cmp,
    Jmp(i8),
    Jlt(i8),
    Jgt(i8),
    Jeq(i8),
    Call(u16),
    Ret,
    Add,
    Sub,
    Mul,
    Div,
    Neg,

    Not,

    And,
    Or,
    Xor,
    Shft,

    Mov(u8, u8),
    Pushr(u8),
    Popr(u8),

    Print,
    MvCur(i8),

    // label pseudo instructions
    Lbl(String),
    CallLbl(String),
    JmpLbl(String),
    JltLbl(String),
    JgtLbl(String),
    JeqLbl(String),
}

impl Instr {
    pub fn byte_len(&self) -> usize {
        match self {
            Instr::Push(_) => 3,
            Instr::Load(_) => 2,
            Instr::Store(_) => 2,
            Instr::Jmp(_) => 2,
            Instr::Jlt(_) => 2,
            Instr::Jgt(_) => 2,
            Instr::Jeq(_) => 2,
            Instr::Mov(_, _) => 2,
            Instr::Pushr(_) => 2,
            Instr::Popr(_) => 2,
            Instr::Add
            | Instr::Sub
            | Instr::Mul
            | Instr::Div
            | Instr::Neg
            | Instr::Not
            | Instr::Cmp
            | Instr::Halt => 1,
            Instr::Lbl(_) => 0,
            Instr::JmpLbl(_) => 2,
            Instr::JltLbl(_) => 2,
            Instr::JgtLbl(_) => 2,
            Instr::JeqLbl(_) => 2,
            Instr::CallLbl(_) => 3,
            Instr::And => 1,
            Instr::Or => 1,
            Instr::Shft => 1,
            Instr::Xor => 1,
            Instr::Loadp => 1,
            Instr::Storep => 1,
            Instr::Print => 1,
            Instr::MvCur(_) => 1,
            Instr::Call(_) => 3,
            Instr::Ret => 1,
        }
    }
}
