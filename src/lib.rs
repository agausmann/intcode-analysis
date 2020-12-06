pub mod disasm;

use std::convert::{TryFrom, TryInto};
use std::num::ParseIntError;
use std::str::FromStr;
use std::{fmt, ops};

/// A buffer containing Intcode code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Intcode(Vec<i64>);

impl Intcode {
    pub fn new(ints: Vec<i64>) -> Intcode {
        Self(ints)
    }

    pub fn get(&self, addr: i64) -> Option<&i64> {
        usize::try_from(addr)
            .ok()
            .and_then(|addr_usize| self.0.get(addr_usize))
    }

    pub fn len(&self) -> i64 {
        self.0.len().try_into().expect("len is too big")
    }
}

impl ops::Index<i64> for Intcode {
    type Output = i64;

    fn index(&self, addr: i64) -> &Self::Output {
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
                .map(str::parse::<i64>)
                .collect::<Result<Vec<i64>, ParseIntError>>()
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
