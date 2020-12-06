//! Intcode disassembly.

use crate::{Int, Intcode};
use std::fmt;

/// A disassembled instruction, identified by its opcode and parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    /// `hlt` - Halts execution of the program.
    Hlt,

    /// `add a b c` - Adds two values and stores the result.
    Add(Src, Src, Dst),

    /// `mul a b c` - Multiplies two values and stores the result.
    Mul(Src, Src, Dst),

    /// `in a` - Reads a value from input and stores it.
    In(Dst),

    /// `out a` - Writes a value to output.
    Out(Src),

    /// `jt a b` - Branches to `b` if `a` is non-zero.
    Jt(Src, Src),

    /// `jf a b` - Branches to `b` if `a` is zero.
    Jf(Src, Src),

    /// `lt a b c` - Stores `1` in `c` if `a < b`, and `0` otherwise.
    Lt(Src, Src, Dst),

    /// `eq a b c` - Stores `1` in `c` if `a == b`, and `0` otherwise.
    Eq(Src, Src, Dst),

    /// `rbo a` - Adds `a` to the current relative base.
    Rbo(Src),
}

impl Instruction {
    pub fn disasm(code: &Intcode, addr: Int) -> Result<Self, DisasmError> {
        let opcode = code[addr] % 100;
        match opcode {
            1 => Ok(Self::Add(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
                Dst::disasm(code, addr, 3)?,
            )),
            2 => Ok(Self::Mul(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
                Dst::disasm(code, addr, 3)?,
            )),
            3 => Ok(Self::In(Dst::disasm(code, addr, 1)?)),
            4 => Ok(Self::Out(Src::disasm(code, addr, 1)?)),
            5 => Ok(Self::Jt(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
            )),
            6 => Ok(Self::Jf(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
            )),
            7 => Ok(Self::Lt(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
                Dst::disasm(code, addr, 3)?,
            )),
            8 => Ok(Self::Eq(
                Src::disasm(code, addr, 1)?,
                Src::disasm(code, addr, 2)?,
                Dst::disasm(code, addr, 3)?,
            )),
            9 => Ok(Self::Rbo(Src::disasm(code, addr, 1)?)),
            99 => Ok(Self::Hlt),
            _ => Err(DisasmError::BadOpcode { addr, opcode }),
        }
    }

    pub fn len(&self) -> Int {
        match self {
            Self::Hlt => 1,
            Self::In(..) | Self::Out(..) | Self::Rbo(..) => 2,
            Self::Jt(..) | Self::Jf(..) => 3,
            Self::Add(..) | Self::Mul(..) | Self::Lt(..) | Self::Eq(..) => 4,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Hlt => write!(f, "hlt"),
            Self::Add(a, b, c) => write!(f, "add {} {} {}", a, b, c),
            Self::Mul(a, b, c) => write!(f, "mul {} {} {}", a, b, c),
            Self::In(a) => write!(f, "in {}", a),
            Self::Out(a) => write!(f, "out {}", a),
            Self::Jt(a, b) => write!(f, "jt {} {}", a, b),
            Self::Jf(a, b) => write!(f, "jf {} {}", a, b),
            Self::Lt(a, b, c) => write!(f, "lt {} {} {}", a, b, c),
            Self::Eq(a, b, c) => write!(f, "eq {} {} {}", a, b, c),
            Self::Rbo(a) => write!(f, "rbo {}", a),
        }
    }
}

/// Macros that can be easily picked out from a list of instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Macro {
    /// `@cpy a b` - equivalent to `add 0 a b` or `mul 1 a b`.
    Cpy(Src, Dst),

    /// `@jmp a` - equivalent to `jt 1 a` or `jf 0 a`.
    Jmp(Src),

    /// `@call a` - equivalent to `@cpy <addr + 7> ~0; @jmp a`.
    Call(Src),
}

impl Macro {
    /// Attempts to disassemble a macro at the given position. If no macro matches the instructions
    /// disassembled, then `None` is returned instead.
    pub fn disasm(intcode: &Intcode, addr: Int) -> Result<Option<Self>, DisasmError> {
        match Instruction::disasm(intcode, addr)? {
            Instruction::Add(Src::Imm(0), a, b)
            | Instruction::Add(a, Src::Imm(0), b)
            | Instruction::Mul(Src::Imm(1), a, b)
            | Instruction::Mul(a, Src::Imm(1), b) => {
                //TODO confirm relative position
                if a == Src::Imm(addr + 7) && b == Dst::Rel(0) {
                    match Macro::disasm(intcode, addr + 4)? {
                        Some(Macro::Jmp(c)) => {
                            return Ok(Some(Macro::Call(c)));
                        }
                        _ => {}
                    }
                }
                Ok(Some(Macro::Cpy(a, b)))
            }
            Instruction::Jt(Src::Imm(x), a) if x != 0 => Ok(Some(Macro::Jmp(a))),
            Instruction::Jf(Src::Imm(0), a) => Ok(Some(Macro::Jmp(a))),
            _ => Ok(None),
        }
    }

    pub fn len(&self) -> Int {
        match self {
            Self::Cpy(..) => 4,
            Self::Jmp(..) => 6,
            Self::Call(..) => 7,
        }
    }
}

impl fmt::Display for Macro {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Cpy(a, b) => write!(f, "@cpy {} {}", a, b),
            Self::Jmp(a) => write!(f, "@jmp {}", a),
            Self::Call(a) => write!(f, "@call {}", a),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacroInstruction {
    Macro(Macro),
    Instruction(Instruction),
}

impl MacroInstruction {
    pub fn disasm(intcode: &Intcode, addr: Int) -> Result<MacroInstruction, DisasmError> {
        match Macro::disasm(intcode, addr)? {
            Some(mac) => Ok(Self::Macro(mac)),
            None => Ok(Self::Instruction(Instruction::disasm(intcode, addr)?)),
        }
    }

    pub fn len(&self) -> Int {
        match self {
            Self::Macro(mac) => mac.len(),
            Self::Instruction(instr) => instr.len(),
        }
    }
}

impl From<Macro> for MacroInstruction {
    fn from(mac: Macro) -> Self {
        Self::Macro(mac)
    }
}

impl From<Instruction> for MacroInstruction {
    fn from(instr: Instruction) -> Self {
        Self::Instruction(instr)
    }
}

impl fmt::Display for MacroInstruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Macro(mac) => write!(f, "{}", mac),
            Self::Instruction(instr) => write!(f, "{}", instr),
        }
    }
}

/// Parameter modes in source position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Src {
    /// Immediate mode. `x`
    Imm(Int),

    /// Position mode. `*x`
    Pos(Int),

    /// Relative mode. `~x` or `*(rbo + x)`
    Rel(Int),
}

impl Src {
    fn disasm(code: &Intcode, addr: Int, index: u32) -> Result<Self, DisasmError> {
        let mode = (code[addr] / 10i64.pow(index + 1)) % 10;
        let value = code[addr + index as Int];
        match mode {
            0 => Ok(Self::Pos(value)),
            1 => Ok(Self::Imm(value)),
            2 => Ok(Self::Rel(value)),
            _ => Err(DisasmError::BadSrcMode { addr, mode }),
        }
    }
}

impl fmt::Display for Src {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Imm(x) => write!(f, "{}", x),
            Self::Pos(x) => write!(f, "*{}", x),
            Self::Rel(x) => write!(f, "~{}", x),
        }
    }
}

/// Parameter modes in destination position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dst {
    /// Position mode. `*x`
    Pos(Int),

    /// Relative mode. `~x` or `*(rbo + x)`
    Rel(Int),
}

impl Dst {
    fn disasm(code: &Intcode, addr: Int, index: u32) -> Result<Self, DisasmError> {
        let mode = (code[addr] / 10i64.pow(index + 1)) % 10;
        let value = code[addr + index as Int];
        match mode {
            0 => Ok(Self::Pos(value)),
            2 => Ok(Self::Rel(value)),
            _ => Err(DisasmError::BadDstMode { addr, mode }),
        }
    }
}

impl fmt::Display for Dst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Pos(x) => write!(f, "*{}", x),
            Self::Rel(x) => write!(f, "~{}", x),
        }
    }
}

#[derive(Debug)]
pub enum DisasmError {
    BadOpcode { addr: Int, opcode: Int },
    BadSrcMode { addr: Int, mode: Int },
    BadDstMode { addr: Int, mode: Int },
}

impl fmt::Display for DisasmError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::BadOpcode { addr, opcode } => write!(f, "bad opcode {} at addr {}", opcode, addr),
            Self::BadSrcMode { addr, mode } => {
                write!(f, "bad source parameter mode {} at addr {}", mode, addr)
            }
            Self::BadDstMode { addr, mode } => {
                write!(f, "bad dest parameter mode {} at addr {}", mode, addr)
            }
        }
    }
}

impl std::error::Error for DisasmError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disasm_example_1() {
        // Example from 2019 day 5.
        // Note that this code is self-modifying,
        // which cannot be detected by the disassembler.
        let intcode: Intcode = "3,3,1108,-1,8,3,4,3,99".parse().unwrap();

        let mut pos = 0;
        let mut instructions = Vec::new();
        while pos < intcode.len() {
            let instr = Instruction::disasm(&intcode, pos).unwrap();
            pos += instr.len();
            instructions.push(instr);
        }

        let expected: Vec<Instruction> = vec![
            Instruction::In(Dst::Pos(3)),
            Instruction::Eq(Src::Imm(-1), Src::Imm(8), Dst::Pos(3)),
            Instruction::Out(Src::Pos(3)),
            Instruction::Hlt,
        ];

        assert_eq!(instructions, expected);
    }

    #[test]
    fn disasm_example_2() {
        // Example taken from my 2019 day 21 input, demonstrating some of the macros used by the
        // compiled puzzle inputs. The corresponding assembly code:
        //
        // rbo 2050
        //
        // @cpy 966 ~1
        // @call 1378

        let intcode: Intcode = "109,2050,21102,1,966,1,21101,0,13,0,1105,1,1378"
            .parse()
            .unwrap();

        let mut pos = 0;
        let mut instructions = Vec::new();
        while pos < intcode.len() {
            let instr = MacroInstruction::disasm(&intcode, pos).unwrap();
            pos += instr.len();
            instructions.push(instr);
        }

        let expected: Vec<MacroInstruction> = vec![
            Instruction::Rbo(Src::Imm(2050)).into(),
            Macro::Cpy(Src::Imm(966), Dst::Rel(1)).into(),
            Macro::Call(Src::Imm(1378)).into(),
        ];

        assert_eq!(instructions, expected);
    }
}
