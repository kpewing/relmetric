use std::fmt;

// use core::slice;
// use std::ops::{Index};
use byteorder::{BigEndian, WriteBytesExt};

/// Represents a column in a Relation
///
/// The default [`Column`] is empty, with `row_count` == 0 and empty `bit_field`.
///
/// # Examples
///
/// ```
/// use relmetric::Column;
///
/// let c0: Column = Column::new();
/// assert_eq!(c0.row_count, 0, "The row_count should be 0, not {}", c0.row_count);
/// assert!(c0.bit_field.is_empty(), "The bit_field should be empty");
/// assert!(c0.is_empty());
/// ```
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Column {
    pub row_count: usize,
    pub bit_field: Vec<u8>,
}

impl Column {
    pub fn new() -> Column {
        //! `new()` takes no arguments and returns an empty Column
        Default::default()
    }
    pub fn len(&self) -> usize {
        //! `len()` returns the number of `u8` integers representing the Column
        self.bit_field.len()
    }
    pub fn is_empty(&self) -> bool {
        //! `is_empty` returns `true` iff the `row_count` == 0 or the `bit_field` is empty
        self.row_count == 0 || self.bit_field.is_empty()
    }
    pub fn to_hex(&self) -> String {
        //! `to_hex` returns a string with hexadecimal representation of the Column's `u8` bytes
        let mut s = String::new();
        s.push_str("{ ");
        for elem in &self.bit_field {
            s.push_str(&format!("{:02x}", elem));
            s.push_str(" ");
        }
        s.push_str("}");
        return s
    }
    pub fn get_bit(&self, n:usize) -> bool {
        //! `get_bit` returns the bool value of the n'th bit
        assert!(!self.is_empty(), "Can't get_bit from empty Column");
        assert!(n < self.row_count, "Index {n} outside range: 0..{}", self.row_count);
        const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        return self.bit_field[the_int] & ROW_MASK[the_bit] > 0;
    }
    pub fn set_bit(&mut self, n:usize, v: bool) {
        //! `set_bit` set the n'th bit to the given bool value
        assert!(!self.is_empty(), "Can't get_bit from empty Column");
        assert!(n < self.row_count, "Index {n} outside range: 0..{}", self.row_count);
        const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        if v == true {
            self.bit_field[the_int] = self.bit_field[the_int] | ROW_MASK[the_bit];
        } else {
            self.bit_field[the_int] = self.bit_field[the_int] & ROW_MASK[the_bit];
        }
    }

    pub fn is_disjoint(&self, other: &Column) -> bool {
        //! `is_disjoint` checks whether two columns are disjoint by rows
        let mut res = true;
        if self.is_empty() & other.is_empty() {
            res = true
        } else if !self.is_empty() & !other.is_empty() {
            assert_eq!(self.row_count, other.row_count, "Column::disjoint requires non-empty Columns to have equal row_count but {} != {}", self.row_count, other.row_count);
            assert_eq!(self.bit_field.len(), other.bit_field.len(), "Column::disjoint requires non-empty Columns to have equal lengths but {} != {}", self.bit_field.len(), other.bit_field.len());
            for (i, elem) in self.bit_field.iter().enumerate() {
                if elem & other.bit_field[i] > 0 {
                    res = false
                }
            }
        } else {
            res = true
        };
        return res
    }
}

// # Traits
//
// ## From
//
impl From<Vec<u8>> for Column {
    //! Since single bytes, endianness is irrelevant: included for completeness
    fn from(bits: Vec<u8>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u8(elem).unwrap();
        }
        Column { row_count: new_bits.len() * 8, bit_field: new_bits }
    }
}

impl From<Vec<u16>> for Column {
    fn from(bits: Vec<u16>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u16::<BigEndian>(elem).unwrap();
        }
        Column { row_count: new_bits.len() * 8, bit_field: new_bits }
    }
}

impl From<Vec<u32>> for Column {
    fn from(bits: Vec<u32>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u32::<BigEndian>(elem).unwrap();
        }
        Column { row_count: new_bits.len() * 8, bit_field: new_bits }
    }
}

impl From<Vec<u64>> for Column {
    fn from(bits: Vec<u64>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u64::<BigEndian>(elem).unwrap();
        }
        Column { row_count: new_bits.len() * 8, bit_field: new_bits }
    }
}

// ## Index, IndexMut
//
// impl Index<usize> for Column {
//     type Output = u8;

//     fn index(&self, n: usize) -> &Self::Output {
//         assert!(!self.is_empty(), "Can't index empty Column");
//         assert!(n <= self.row_count, "Index {n} outside range: 0..{}", self.row_count);
//         const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
//         let the_int = n / u8::BITS as usize;
//         let the_bit = n % u8::BITS as usize;
//         let res = self.bit_field[the_int] & ROW_MASK[the_bit];
//         return &res
//     }
// }

// impl IndexMut<usize> for Column {
//     fn index_mut(&mut self, n: usize) -> &mut Self::Output {
//         assert!(!self.is_empty(), "Can't index empty Column");
//         assert!(n <= self.row_count, "Index {n} outside range: 0..{}", self.row_count);
//         const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
//         let the_int = n / u8::BITS as usize;
//         let the_bit = n % u8::BITS as usize;
//         let mut res = self.bit_field[the_int] & ROW_MASK[the_bit];
//         return &mut res
//     }
// }

// ## Display
//
impl fmt::Display for Column {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for r in 0..self.row_count {
            // s.push_str(&format!("{}\n", 4))
            if self.get_bit(r) {
                s.push_str("1\n")
            } else {
                s.push_str("0\n")
            }
        }
        write!(f, "{s}")
    }
}

pub struct Relation {

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_col_is_empty() {
        let c: Column = Column::new();
        assert!(c.is_empty());
    }

    #[test]
    fn prints_hex() {
        let c = Column::from(vec![0x3000 as u16, 0x000f as u16]);
        let hex_c = c.to_hex();
        let want = "{ 30 00 00 0f }";
        assert_eq!(hex_c, want, "{} doesn't equal {}", hex_c, want);
    }

    #[test]
    fn sets_and_gets_bit() {
        let mut c = Column::from(vec![0b00000001u8]);
        let mut res = c.get_bit(7);
        let want = true;
        assert_eq!(res, want, "Gotten bit {} doesn't match {}", res, want);
        c.set_bit(6, true);
        res = c.get_bit(6);
        assert_eq!(res, want, "Set bit {} doesn't match {}", res, want);
    }

    #[test]
    fn displays_column() {
        let c = Column::from(vec![0b10000000u8, 0b00000001u8]);
        let res = format!("{}", c);
        let want = "1\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n1\n";
        assert_eq!(res, want, "{} doesn't equal {}", res, want);
    }

    #[test]
    fn is_disjoint_works() {
        let c1 = Column::from(vec![0b10000000u8, 0b00000001u8]);
        let c2 = Column::from(vec![0b00000001u8,0b10000000u8]);
        let c3 = Column::from(vec![0b10000001u8,0b10000000u8]);
        assert!(c1.is_disjoint(&c2), "Fails to see that {} is disjoint from {}", c1.to_hex(), c2.to_hex());
        assert!(!c2.is_disjoint(&c3), "Fails to see that {} is NOT disjoint from {}", c2.to_hex(), c3.to_hex());
    }
}
