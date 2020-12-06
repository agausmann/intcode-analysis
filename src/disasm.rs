//! Low-level Intcode disassembly.

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
    pub fn disasm(code: &Intcode, addr: Int) -> Result<Instruction, DisasmError> {
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

#[cfg(test)]
mod tests {
    use super::*;

    const INTCODE_EXAMPLE: &str = "3,3,1108,-1,8,3,4,3,99";

    #[test]
    fn disasm_in() {
        let intcode: Intcode = INTCODE_EXAMPLE.parse().unwrap();
        let instr = Instruction::disasm(&intcode, 0).unwrap();
        assert_eq!(instr, Instruction::In(Dst::Pos(3)));
    }

    #[test]
    fn disasm_eq() {
        let intcode: Intcode = INTCODE_EXAMPLE.parse().unwrap();
        let instr = Instruction::disasm(&intcode, 2).unwrap();
        assert_eq!(
            instr,
            Instruction::Eq(Src::Imm(-1), Src::Imm(8), Dst::Pos(3))
        );
    }

    #[test]
    fn disasm_out() {
        let intcode: Intcode = INTCODE_EXAMPLE.parse().unwrap();
        let instr = Instruction::disasm(&intcode, 6).unwrap();
        assert_eq!(instr, Instruction::Out(Src::Pos(3)));
    }

    #[test]
    fn disasm_hlt() {
        let intcode: Intcode = INTCODE_EXAMPLE.parse().unwrap();
        let instr = Instruction::disasm(&intcode, 8).unwrap();
        assert_eq!(instr, Instruction::Hlt);
    }
}
