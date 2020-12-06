pub mod disasm;

use std::convert::{TryFrom, TryInto};
use std::num::ParseIntError;
use std::str::FromStr;
use std::{fmt, ops};

pub type Int = i64;

/// A buffer containing Intcode code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Intcode(Vec<Int>);

impl Intcode {
    pub fn new(ints: Vec<Int>) -> Intcode {
        Self(ints)
    }

    pub fn get(&self, addr: Int) -> Option<&Int> {
        usize::try_from(addr)
            .ok()
            .and_then(|addr_usize| self.0.get(addr_usize))
    }

    pub fn len(&self) -> Int {
        self.0.len().try_into().expect("len is too big")
    }
}

impl ops::Index<Int> for Intcode {
    type Output = Int;

    fn index(&self, addr: Int) -> &Self::Output {
        self.get(addr).expect("address out of bounds")
    }
}

impl fmt::Display for Intcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(first) = self.0.first() {
            write!(f, "{}", first)?;
        }
        if let Some(tail) = self.0.get(1..) {
            for int in tail {
                write!(f, ",{}", int)?;
            }
        }
        Ok(())
    }
}

impl FromStr for Intcode {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.is_empty() {
            Ok(Self(vec![]))
        } else {
            s.split(',')
                .map(str::parse::<Int>)
                .collect::<Result<Vec<Int>, ParseIntError>>()
                .map(Self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_intcode() {
        let intcode: Intcode = "23,45,6".parse().unwrap();
        assert_eq!(intcode, Intcode::new(vec![23, 45, 6]));
    }

    #[test]
    fn fmt_intcode() {
        let intcode = Intcode::new(vec![23, 45, 6]);
        assert_eq!(intcode.to_string(), "23,45,6");
    }
}
