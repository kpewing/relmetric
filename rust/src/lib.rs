//! # A Library for Calculations with Binary Relations
//!
//! The `relmetric` library creates an abstraction of a (binary) relation---a 2x2 matrix of zero's and one's representing whether objects in one set *X* relate to those in another *Y*. It offers core types [`Relation`], [`Column`], [`Matches`], and [`XGrouping`], and methods like [`Relation::new()`] and [`Relation::set_col`] to manipulate them. Among many other methods, the crate also provides [`Relation::weight()`] and [`Relation::distance()`] to calculate the *weight* of a [`Matches`] function between two [`Relation`]s and the *distance* between two [`Relation`]s, as defined in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^1] Because calculating *distance* exactly requires a combinatorial search all possible [`Matches`], the method [`Relation::rel_dist_bound`] calculates a tight upper bound with *O*(*m* &times; *n*) complexity. See [*id.* at p. 33](https://arxiv.org/abs/2105.01690).[^2]
//!
//! # Overview
//!
//! As a quick overview, we reproduce the calculations of Examples 1 and 2 in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^3]
//!
//! ## Example 1
//!
//! ```
//! use relmetric::*;
//!
//! let r1 = Relation::from(vec![Column::from(vec![1u8])]);
//! let r2 = Relation::new();
//! assert!(r2.is_empty());
//! assert_eq!(r1.min_weight(&r2), 1);
//! assert_eq!(r1.distance(&r2), 1);
//! ```
//! ## Example 2
//!
//! ```
//! use relmetric::*;
//!
//! let mut r1 = Relation::from(vec![
//!     Column::from(vec![0b1100u8]),
//!     Column::from(vec![0b1010u8]),
//!     Column::from(vec![0b1011u8]),
//!     Column::from(vec![0b0011u8]),
//! ]);
//! let mut r2 = Relation::from(vec![
//!     Column::from(vec![0b1100u8]),
//!     Column::from(vec![0b1011u8]),
//!     Column::from(vec![0b0101u8]),
//! ]);
//! assert_eq!(r1.distance(&r2), 2);
//! assert_eq!(r2.distance(&r1), 2);
//! r1.trim_row_count();
//! let pretty_r1 = "\
//! 1110
//! 1000
//! 0111
//! 0011
//! ";
//! assert_eq!(format!("{}", r1), pretty_r1);
//! r2.trim_row_count();
//! let pretty_r2 = "\
//! 110
//! 101
//! 010
//! 011
//! ";
//! assert_eq!(format!("{}", r2), pretty_r2);
//! ```
//!
//! ## Other Cool Stuff
//!
//! - Calculate the [*kappa* bound](Relation::kappa()) defined in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
//! - Iterate over all *n*^(*k*) (combinatorial) variations of *k* choices from a set of *n* numbers, with replacement using the [`Matches`] [`Iterator`](std::iter::Iterator).
//! - Pretty-print both a [`Relation`] and an [`XGrouping`] with the standard format [`Display`](std::fmt::Display).
//! - Show easily human-readable binary and hexadecimal forms of both [`Column`]s and [`Relation`]s using the standard formats [`Binary`](std::fmt::Binary), [`LowerHex`](std::fmt::LowerHex), and [`UpperHex`](std::fmt::UpperHex).
//! - Total lexical ordering of [`Column`]s and [`Relation`]s.
//! - Binary arithmetic for both [`Column`]s and [`Relation`]s using the standard [`& (BitAnd)`](std::ops::BitAnd), [`| (BitOr)`](std::ops::BitOr), and [`^ (BitXor)`](std::ops::BitXor) operations.
//!
//! [^1]: Definitions 1 and 2, [Kenneth P. Ewing & Michael Robinson, "Metric Comparison of Relations," p. 7](https://arxiv.org/abs/2105.01690).
//!
//! [^2]: Theorem 2, [*id*, p. 33](https://arxiv.org/abs/2105.01690).
//!
//! [^3]: Examples 1 and 2, [*id*, pp. 10-11](https://arxiv.org/abs/2105.01690).

use std::{
    fmt::{self},
    iter::zip,
    ops::{BitAnd, BitOr, BitXor, Index, Sub, Not},
};
use byteorder::{BigEndian, WriteBytesExt};

/// Represents the relations one item in one set has with all items of the other set in a [`Relation`].
///
/// Each is represented by a list of [`u8`] integers in big-endian order.
/// Lists end on word boundaries; so the modulus resides in the low end of last integer in the list for each column.
///
/// The default `Column` is empty, with `row_count` == 0 and empty `bit_field`.
///
/// A zero `Column` has a positive `row_count` and 0s in the `bit_field`, so is *not* empty.
///
/// Two [`Column`]s are [*disjoint*](Column::is_disjoint()) if they do not share `true` bit in any row. Thus [empty](Column::is_empty()) and [zero](Column::is_zero()) [`Column`]s are all *not* disjoint from each other, since they share no `true` bit in any row.
///
/// # Examples
///
/// ```
/// use relmetric::Column;
///
/// let c0 = Column::new();
/// assert_eq!(c0, Column { row_count: 0, bit_field: vec![] });
/// assert!(c0.bit_field.is_empty());
/// assert!(c0.is_empty());
///
/// let zero16 = Column::zero(16);
/// assert_eq!(zero16, Column { row_count: 16, bit_field: vec![0; 2] });
/// assert!(zero16.is_zero());
/// assert!(!zero16.is_empty());
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Column {
    /// The number of rows of this [`Column`].
    pub row_count: usize,
    /// Represents a sequence of rows as bits in a big-endian vector of `u8` integers.
    ///
    /// NB: Modulus of rows resides in low end of last integer.
    pub bit_field: Vec<u8>,
}

impl Column {
    /// Returns a new empty [`Column`] equal to the [`Default`] with `row_count` 0 and `bit_field` empty.
    pub fn new() -> Column {
        Default::default()
    }

    /// Returns a new empty [`Column`] with requested `row_count`.
    pub fn zero(row_count: usize) -> Column {
        let mut int_count = row_count / (u8::BITS as usize);
        if row_count % (u8::BITS as usize) > 0 {
            int_count += 1
        }
        Column {
            row_count,
            bit_field: vec![0u8; int_count],
        }
    }

    /// Returns the `row_count`.
    pub fn get_row_count(&self) -> usize {
        self.row_count
    }

    /// Sets and returns the `row_count`.
    ///
    /// Panics if the requested `row_count` exceeds capacity of [`bit_fied`.
    pub fn set_row_count(&mut self, v: usize) -> usize {
        let cap = self.bit_field.len() * u8::BITS as usize;
        assert!(
            v <= cap,
            "Column::set_row_count requires new value in range 0..{}",
            cap
        );
        self.row_count = v;
        self.row_count
    }

    /// Returns the `bool` value of the `n`th bit.
    ///
    /// Panics if `row_count` == 0 or the index `n` is out of bounds.
    pub fn get_bit(&self, n: usize) -> bool {
        assert!(self.row_count > 0, "Column::get_bit requires row_count > 0");
        assert!(
            n < self.row_count,
            "Column::get_bit index {n} outside range: 0..{}",
            self.row_count
        );
        const ROW_MASK: [u8; 8] = [
            0b10000000u8,
            0b01000000u8,
            0b00100000u8,
            0b00010000u8,
            0b00001000u8,
            0b00000100u8,
            0b00000010u8,
            0b00000001u8,
        ];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        let the_offset =
            (self.bit_field.len() * u8::BITS as usize - self.row_count) % u8::BITS as usize;

        if self.bit_field.len() == 0 {
            return false;
        } else if the_int < self.bit_field.len() - 1 {
            return self.bit_field[the_int] & ROW_MASK[the_bit] > 0;
        } else {
            return self.bit_field[the_int] & ROW_MASK[the_offset + the_bit] > 0;
        }
    }

    /// Sets the `n`th bit to the given `bool` value.
    ///
    /// Panics if `row_count` == 0 or the index `n` is out of bounds.
    pub fn set_bit(&mut self, n: usize, v: bool) {
        //! Panics if row_count == 0 or bit index outside range 0..row_count
        assert!(self.row_count > 0, "Column::set_bit requires row_count > 0");
        assert!(
            n < self.row_count,
            "Column::set_bit index {n} outside range: 0..{}",
            self.row_count
        );
        const ROW_MASK: [u8; 8] = [
            0b10000000u8,
            0b01000000u8,
            0b00100000u8,
            0b00010000u8,
            0b00001000u8,
            0b00000100u8,
            0b00000010u8,
            0b00000001u8,
        ];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        let the_offset =
            (self.bit_field.len() * u8::BITS as usize - self.row_count) % u8::BITS as usize;

        if the_int < self.bit_field.len() - 1 {
            if v == true {
                self.bit_field[the_int] = self.bit_field[the_int] | ROW_MASK[the_bit];
            } else {
                self.bit_field[the_int] = self.bit_field[the_int] & !ROW_MASK[the_bit];
            }
        } else {
            if v == true {
                self.bit_field[the_int] = self.bit_field[the_int] | ROW_MASK[the_offset + the_bit];
            } else {
                self.bit_field[the_int] = self.bit_field[the_int] & !ROW_MASK[the_offset + the_bit];
            }
        }
    }

    /// Returns 1 + the highest row index with a `true` bit.
    ///
    /// **BEWARE: Ignores leading `false` bits; so can be "too short" if the high-order rows happen to be `false` for this [`Column`].**
    pub fn max_true_bit(&self) -> usize {
        let n = self.bit_field.len();
        let mut res = n * u8::BITS as usize;
        for i in 0..n {
            let int = self.bit_field[n - i - 1];
            let zeros = int.leading_zeros();
            if zeros == u8::BITS {
                res -= u8::BITS as usize
            } else {
                res -= zeros as usize;
                break;
            }
        }
        return res;
    }

    /// Sets and returns the `row_count` to match the `max_true_bit()`.
    ///
    /// **BEWARE: Ignores leading `false` bits; so can be "too short" if the high-order rows happen to be `false` for this [`Column`].**
    pub fn trim_row_count(&mut self) -> usize {
        self.set_row_count(self.max_true_bit())
    }

    /// Returns `true` iff `row_count` == 0 or `bit_field` is empty.
    pub fn is_empty(&self) -> bool {
        self.row_count == 0 || self.bit_field.is_empty()
    }

    /// Returns `true` iff `row_count` > 0 and `bit_field` is all `0u8`.
    pub fn is_zero(&self) -> bool {
        self.row_count > 0 && self.bit_field.iter().all(|&x| x == 0)
    }

    /// Returns whether two [`Column`]s are disjoint by rows.
    ///
    /// `true` unless `self` and `other` share a `true` bit in some row.
    ///
    /// NB: Unlike the `lua` version, [`empty`](Column::is_empty()) and [`zero`](Column::is_zero()) [`Column`]s are *not* disjoint from each other and *are* disjoint from non-[`empty`](Column::is_empty()) and non-[`zero`](Column::is_zero()) ones. Finding empties disjoint from everything doesn't make sense.
    pub fn is_disjoint(&self, other: &Column) -> bool {
        if self.is_empty() || self.is_zero() {
            if other.is_empty() || other.is_zero() {
                return false;
            } else {
                return true;
            }
        } else if other.is_empty() || other.is_zero() {
            return true;
        } else {
            let mut res = true;
            assert_eq!(
                self.row_count, other.row_count,
                "Column::disjoint requires non-empty Columns to have equal row_count but {} != {}",
                self.row_count, other.row_count
            );
            assert_eq!(
                self.bit_field.len(),
                other.bit_field.len(),
                "Column::disjoint requires non-empty Columns to have equal lengths but {} != {}",
                self.bit_field.len(),
                other.bit_field.len()
            );
            for (i, elem) in self.bit_field.iter().enumerate() {
                if elem & other.bit_field[i] > 0 {
                    res = false
                }
            }
            return res;
        }
    }

}

// Since single bytes, endian-ness is irrelevant: included for completeness
impl From<Vec<u8>> for Column {
    fn from(bits: Vec<u8>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u8(elem).unwrap();
        }
        Column {
            row_count: new_bits.len() * 8,
            bit_field: new_bits,
        }
    }
}

impl From<Vec<u16>> for Column {
    fn from(bits: Vec<u16>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u16::<BigEndian>(elem).unwrap();
        }
        Column {
            row_count: new_bits.len() * 8,
            bit_field: new_bits,
        }
    }
}

impl From<Vec<u32>> for Column {
    fn from(bits: Vec<u32>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u32::<BigEndian>(elem).unwrap();
        }
        Column {
            row_count: new_bits.len() * 8,
            bit_field: new_bits,
        }
    }
}

impl From<Vec<u64>> for Column {
    fn from(bits: Vec<u64>) -> Self {
        let mut new_bits: Vec<u8> = Vec::new();
        for elem in bits {
            new_bits.write_u64::<BigEndian>(elem).unwrap();
        }
        Column {
            row_count: new_bits.len() * 8,
            bit_field: new_bits,
        }
    }
}

impl fmt::Display for Column {
    /// Display as a binary column of rows from top to bottom.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for r in 0..self.row_count {
            if self.get_bit(r) {
                s.push_str("1\n")
            } else {
                s.push_str("0\n")
            }
        }
        write!(f, "{s}")
    }
}

impl fmt::Binary for Column {
    /// Show a big-endian binary representation of the [`Column`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.row_count / u8::BITS as usize;
        let rest_bits = self.row_count % u8::BITS as usize;
        const REST_MASK: [u8; 8] = [
            0b00000000u8,
            0b00000001u8,
            0b00000011u8,
            0b00000111u8,
            0b00001111u8,
            0b00011111u8,
            0b00111111u8,
            0b01111111u8,
        ];

        let mut s = String::from("[");
        s.push_str(
            &self
                .bit_field
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:08b}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                s.push_str(&format!(
                    "{:b}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            } else {
                s.push_str(&format!(
                    ", {:b}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            }
        }
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl fmt::LowerHex for Column {
    /// Show a big-endian lower hexadecimal representation of the [`Column`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.row_count / u8::BITS as usize;
        let rest_bits = self.row_count % u8::BITS as usize;
        const REST_MASK: [u8; 8] = [
            0b00000000u8,
            0b00000001u8,
            0b00000011u8,
            0b00000111u8,
            0b00001111u8,
            0b00011111u8,
            0b00111111u8,
            0b01111111u8,
        ];
        let mut s = String::from("[");
        s.push_str(
            &self
                .bit_field
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:02x}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                s.push_str(&format!(
                    "{:x}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            } else {
                s.push_str(&format!(
                    ", {:x}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            }
        }
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl fmt::UpperHex for Column {
    /// Show a big-endian upper hexadecimal representation of the [`Column`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.row_count / u8::BITS as usize;
        let rest_bits = self.row_count % u8::BITS as usize;
        const REST_MASK: [u8; 8] = [
            0b00000000u8,
            0b00000001u8,
            0b00000011u8,
            0b00000111u8,
            0b00001111u8,
            0b00011111u8,
            0b00111111u8,
            0b01111111u8,
        ];
        let mut s = String::from("[");
        s.push_str(
            &self
                .bit_field
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:02X}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                s.push_str(&format!(
                    "{:X}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            } else {
                s.push_str(&format!(
                    ", {:X}",
                    self.bit_field[whole_ints] & REST_MASK[rest_bits]
                ));
            }
        }
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl Not for Column {
    type Output = Self;

    /// Performs the unary [`!`](std::ops::Not) operation for a [`Column`].
    fn not(self) -> Self::Output {
        Column {
            row_count: self.row_count,
            bit_field: self.bit_field.iter().map(|x|!x).collect(),
        }
    }
}

impl BitAnd for Column {
    type Output = Self;

    /// Performs the [`&`](std::ops::BitAnd::bitand) operation for two [`Column`]s of same `row_count`.
    ///
    /// Panics if the two [`Column`]s don't have the same `row_count`.
    fn bitand(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone();
        } else if rhs.is_empty() {
            return self.clone();
        } else {
            assert!(
                self.row_count == rhs.row_count,
                "Column::bitand requires non-empty Columns to have equal row_count but: {} != {}",
                self.row_count,
                rhs.row_count
            );
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitand requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            return Column::from(
                zip(self.bit_field.clone(), rhs.bit_field.clone())
                    .map(|(s, r)| s & r)
                    .collect::<Vec<u8>>(),
            );
        }
    }
}

impl BitOr for Column {
    type Output = Self;

    /// Performs the [`|`](std::ops::BitOr::bitor) operation for two [`Column`]s of same `row_count`.
    ///
    /// Panics if the two [`Column`]s don't have the same `row_count`.
    fn bitor(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone();
        } else if rhs.is_empty() {
            return self.clone();
        } else {
            assert!(
                self.row_count == rhs.row_count,
                "Column::bitor requires non-empty Columns to have equal row_count but: {} != {}",
                self.row_count,
                rhs.row_count
            );
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitor requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            return Column::from(
                zip(self.bit_field.clone(), rhs.bit_field.clone())
                    .map(|(s, r)| s | r)
                    .collect::<Vec<u8>>(),
            );
        }
    }
}

impl BitXor for Column {
    type Output = Self;

    /// Performs the [`^`](std::ops::BitXor::bitxor) operation for two [`Column`]s of same `row_count`.
    ///
    /// Panics if the two [`Column`]s don't have the same `row_count`.
    fn bitxor(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone();
        } else if rhs.is_empty() {
            return self.clone();
        } else {
            assert!(
                self.row_count == rhs.row_count,
                "Column::bitxor requires non-empty Columns to have equal row_count but: {} != {}",
                self.row_count,
                rhs.row_count
            );
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitxor requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            return Column::from(
                zip(self.bit_field.clone(), rhs.bit_field.clone())
                    .map(|(s, r)| s ^ r)
                    .collect::<Vec<u8>>(),
            );
        }
    }
}

/// Represents a *binary relation* between two arbitrary sets *X* and *Y* as a collection of [`Column`]s of bits.
///
/// A `true` bit in any row *x* &in; *X* of [`Column`] *y* &in; *Y* indicates a "relation" between *x* and *y*.
///
/// The default Relation is [`empty`](Column::is_empty()), with `row_count` == 0 and an empty collection of [`Column`]s.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Relation {
    /// The number of rows of all [`Column`]s of this [`Relation`].
    pub row_count: usize,
    /// Collection of the [`Column`]s in this [`Relation`].
    pub columns: Vec<Column>,
}

impl Relation {
    /// Returns a new empty [`Relation`] with `row_count` set to default 0, no [`Column`]s.
    pub fn new() -> Relation {
        Default::default()
    }

    /// Returns a zero [`Relation`] with given `row_count` and given number of zero [`Column`]s.
    pub fn zero(row_count: usize, col_count: usize) -> Relation {
        Relation {
            row_count,
            columns: vec![Column::zero(row_count); col_count],
        }
    }

    /// Returns the `row_count`.
    pub fn get_row_count(&self) -> usize {
        self.row_count
    }

    /// Returns the number of Columns in the [`Relation`].
    pub fn len(&self) -> usize {
        self.columns.len()
    }

    /// Returns whether the [`Relation`] is empty.
    pub fn is_empty(&self) -> bool {
        self.columns.len() == 0 || self.columns.iter().fold(true, |acc, x| acc & x.is_empty())
    }

    /// Returns the `n`'th Column in the Relation
    pub fn get_col(&self, n: usize) -> &Column {
        &self.columns[n]
    }

    /// Replaces the [`Relation`]'s `n`'th [`Column`] with `v`, pushing any needed [zero Columns](`Column::zero()`).
    ///
    /// Can be used to extend the [`Relation`] with [`zero`](Column::is_zero()) [`Column`]s.
    ///
    /// Panics if non-empty `self` and `v` have different `row_count`s.
    pub fn set_col(&mut self, n: usize, v: Column) {
        let self_empty = self.is_empty();
        let v_empty = v.is_empty();
        if self_empty && v_empty {
            println!("both empty");
            // no-op
        } else {
            let need_cols = n.checked_sub(self.columns.len()).unwrap_or(0);
            let mut new_col = v;
            if self_empty {
                println!("set_col self_empty");
                self.row_count = new_col.row_count;
                self.columns.clear();
                self.columns = vec![Column::zero(new_col.row_count)];
            } else if v_empty {
                println!("set_col v_empty");
                new_col = Column::zero(self.row_count);
            } else {
                println!("set_col neither empty");
                assert!(
                    self.row_count == new_col.row_count,
                    "Relation::set_col requires same row_count but {} != {}",
                    self.row_count,
                    new_col.row_count
                );
            }
            for _ in 0..need_cols {
                self.columns.push(Column::zero(self.row_count));
            }
            self.columns[n] = new_col;
        }
    }

    /// Returns the index of the highest `true` bit of its [`Column`]s.
    ///
    /// **BEWARE: Ignores leading `false` bits; so can be "too short" if the high-order rows happen to be `false` for all [`Column`]s.**
    pub fn max_true_bit(&self) -> usize {
        self.columns
            .iter()
            .fold(0, |acc, x| acc.max(x.max_true_bit()))
    }

    /// Sets and returns the `row_count` to match the `max_true_bit()`.
    ///
    /// **BEWARE: Ignores leading `false` bits; so can be "too short" if the high-order rows happen to be `false` for all [`Column`]s.**
    pub fn trim_row_count(&mut self) -> usize {
        let max_true_bit = self.max_true_bit();
        for c in &mut self.columns {
            c.set_row_count(max_true_bit);
        }
        self.row_count = max_true_bit;
        max_true_bit
    }

    /// Returns the [`XGrouping`] partition of the [`Relation`].
    ///
    /// NB: The [`XGrouping`] of an [`empty`](Relation::is_empty()) [`Relation`] is, in itself "empty", i.e., has no [`XGroup`]s in it.
    pub fn xgroup(&self) -> XGrouping {
        // Checks all columns v. all groups:
        // - for each `columns[i]` first check overlap with all groups `res[j]`
        // -- if overlaps a `res[j]`, then expand it and check remaining groups `res[j+1..]`
        // -- if no overlaps, then create a new group `res[_]
        // - repeat checking for remaining `columns[i+1..]`
        if self.is_empty() {
            return XGrouping {
                relation: &self,
                partition: vec![],
            };
        } else {
            let mut res: Vec<XGroup> = vec![XGroup {
                max: self.columns[0].clone(),
                col_indices: vec![0],
            }];
            for i in 1..self.columns.len() {
                let col = &self.columns[i];
                let mut new_group = true;
                let mut expanded: Option<usize> = None;
                for j in 0..res.len() {
                    match expanded {
                        // -- haven't yet found an overlapping group res[j] to expand: this one?
                        None => {
                            let isdisjnt = res[j].max.is_disjoint(&col);
                            if !isdisjnt {
                                // expand res[j] and save the index
                                res[j].col_indices.push(i);
                                res[j].max = res[j].max.clone() | (*col).clone();
                                expanded = Some(j);
                                new_group = false;
                            }
                        }
                        // -- have expanded group res[idx]: combine it with any other groups?
                        Some(idx) => {
                            let isdisjnt = res[idx].max.is_disjoint(&res[j].max);
                            if !isdisjnt {
                                // drain this res[j]'s col_indices
                                let mut resj_indices: Vec<usize> =
                                    res[j].col_indices.drain(..).collect();
                                // add them to res[idx]'s col_indices
                                res[idx].col_indices.append(&mut resj_indices);
                                // update res[idx].max
                                res[idx].max = res[idx].max.clone() | res[j].max.clone();
                            }
                        }
                    }
                }
                // -- disjoint from all groups: create a new group for col
                if new_group {
                    res.push(XGroup {
                        max: col.clone(),
                        col_indices: vec![i],
                    });
                }
            }
            res.sort_unstable_by(|a, b| a.col_indices.len().cmp(&b.col_indices.len()));
            return XGrouping {
                relation: &self,
                partition: res,
            }
        }
    }

    /// Returns the "kappa" value for a [`Relation`].
    ///
    /// See Kenneth P. Ewing "Bounds for the Distance Between Relations," arXiv:2105.01690.
    pub fn kappa(&self, max_count: Option<usize>) -> usize {
        // NB: `Rust` vectors are base 0 rather than `lua`'s base 1.
        if self.is_empty() {
            return 0;
        } else {
            let xgs = self.xgroup().partition;
            let mut blockcounts: Vec<usize> = xgs.iter().map(|x| x.col_indices.len()).collect();
            blockcounts.sort();
            let mut bc_sum = 0;
            let blocksums: Vec<usize> = blockcounts
                .iter()
                .map(|x| {
                    bc_sum = bc_sum + x;
                    bc_sum
                })
                .collect();
            let cap = match max_count {
                None => self.columns.len(),
                Some(n) => self.columns.len().min(n),
            };
            let mut m = 0;

            if blocksums[0] <= cap {
                while m < blocksums.len() && blocksums[m] <= cap {
                    m = m + 1
                }
            }
            if blocksums.len() == 1 {
                return 0;
            } else if cap >= self.columns.len() {
                return blocksums[m - 2];
            } else if blocksums[m - 1] + blockcounts[m - 1] > cap {
                return blocksums[m - 2];
            } else {
                return blocksums[m - 1];
            }
        }
    }

    /// Returns the bound on the "Relation metric" for "distance" between two [`Relation`]s.
    ///
    /// See Kenneth P. Ewing "Bounds for the Distance Between Relations," arXiv:2105.01690.
    pub fn rel_dist_bound(&self, other: &Relation) -> usize {
        // NB: `Rust` vectors are base 0 rather than `lua`'s base 1.

        println!("rel1:\n{}\n", self);
        println!("rel2:\n{}\n", other);

        let rel1_count = self.columns.len();
        let rel2_count = other.columns.len();
        let delta12 = self.clone() - (*other).clone();
        let delta21 = other.clone() - (*self).clone();

        println!("delta12:\n{}\n", delta12);
        println!("delta21:\n{}\n", delta21);

        let delta12_count = delta12.len();
        let delta21_count = delta21.len();
        let kappa12 = delta12.kappa(Some(delta21_count));
        let kappa21 = delta21.kappa(Some(delta12_count));

        println!(
            "rel_dist_bound = max({}, {}) - min({} - {} + {}, {} - {} + {})",
            rel1_count,
            rel2_count,
            rel1_count,
            delta12_count,
            kappa12,
            rel2_count,
            delta12_count,
            kappa21
        );

        return rel1_count.max(rel2_count)
            - (rel1_count - delta12_count + kappa12).min(rel2_count - delta21_count + kappa21);
    }

    /// Returns a new [`Relation`] resulting from applying `col_matches` between `self` and `other`.
    ///
    /// Panics if both `self` and `other` are non-[`empty`](Relation::is_empty()) but don't have same `row_count`, or if `col_matches` is out of range for either `self` or `other`.
    pub fn match_columns(&self, other: &Relation, col_matches: &Vec<usize>) -> Relation {
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        if self_empty & other_empty {
            println!("match_columns both empty");
            return self.clone();
        } else if self_empty {
            println!("match_columns self_empty");
            return Relation::zero(other.row_count, other.columns.len())
                .match_columns(&other, col_matches);
        } else if other_empty {
            println!("match_columns other_empty");
            return self.match_columns(
                &Relation::zero(self.row_count, self.columns.len()),
                col_matches,
            );
        } else {
            assert_eq!(self.row_count, other.row_count, "Relation::match_columns() requires non-empty Relations to have same row_count but {} != {}", self.row_count, other.row_count);
            println!("match_columns neither empty");
            assert!(col_matches.len() <= self.columns.len(), "Relation::match_columns() Invalid col_match: col_match.len() {} > self.columns.len() {}", col_matches.len(), self.columns.len());
            assert!(other.columns.len() >= *col_matches.iter().max().unwrap(), "Relation::match_columns() Invalid col_match: max col_matches[..] > self.columns.len() {}", other.columns.len());

            let mut res = self.clone();
            for i in 0..col_matches.len() {
                res.set_col(i, other.get_col(col_matches[i]).clone())
            }
            return res;
        }
    }

    /// Returns the "weight" of a [`Column`] function from `self` to `other` (represented as `col_matches`).
    ///
    /// Panics if non-empty [`Relation`]s don't have same `row_count`s or `col_matches` exceeds Column counts of `self` and `other`.
    ///
    /// Given a function *f* that matches each [`Column`] in one [`Relation`] *r1* to a some [`Column`] in the other [`Relation`] *r2*, the *weight* of *f* is the largest count of differences seen in any row after matching with *f*, plus the number of any [`Column`]s in *r2* that were not matched.
    ///
    /// So the weight of any function between empty [`Relation`]s is 0, that of any function to an empty [`Relation`] returns the highest row-count of ones in `self`, and similarly for any function from an empty [`Relation`] to any `other`.
    ///
    /// See Kenneth P. Ewing "Bounds for the Distance Between Relations," arXiv:2105.01690.
    pub fn weight(&self, other: &Relation, col_matches: &Vec<usize>) -> u32 {
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        if self_empty & other_empty {
            println!("weight both empty");
            return 0;
        } else if self_empty {
            println!("weight self_empty");
            return *other
                .columns
                .iter()
                .fold(vec![0_u32; other.row_count], |mut acc, c| {
                    for r in 0..other.row_count {
                        if c.get_bit(r) {
                            acc[r] += 1
                        }
                    }
                    acc
                })
                .iter()
                .max()
                .unwrap();
        } else if other_empty {
            println!("weight other_empty");
            return *self
                .columns
                .iter()
                .fold(vec![0_u32; self.row_count], |mut acc, c| {
                    for r in 0..self.row_count {
                        if c.get_bit(r) {
                            acc[r] += 1
                        }
                    }
                    acc
                })
                .iter()
                .max()
                .unwrap();
        } else {
            let used_count = col_matches
                .iter()
                .fold(vec![0u32; other.columns.len()], |mut acc, m| {
                    acc[*m] = acc[*m] | 1;
                    acc
                })
                .iter()
                .sum::<u32>();
            let penalty = other.columns.len() as u32 - used_count;
            let image = self.match_columns(other, col_matches);
            let bitxor_image = image.clone().bitxor(self.clone());
            let max_row_diff = *bitxor_image
                .columns
                .iter()
                .fold(vec![0_u32; self.row_count], |mut acc, c| {
                    for r in 0..self.row_count {
                        if c.get_bit(r) {
                            acc[r] += 1
                        }
                    }
                    acc
                })
                .iter()
                .max()
                .unwrap();
            println!(
                "weight neither empty, penalty:{} max_row_diff:{}\nimage:{:b}\nbitxor_image:{:b}",
                penalty, max_row_diff, image, bitxor_image
            );
            return penalty + max_row_diff;
        }
    }

    /// Returns the minimum [`Relation::weight()`] of all possible [`Column`] functions from `self` to `other`.
    ///
    /// Panics if non-empty [`Relation`]s don't have same `row_count`.
    ///
    /// See Kenneth P. Ewing "Bounds for the Distance Between Relations," arXiv:2105.01690.
    pub fn min_weight(&self, other: &Relation) -> u32 {
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        let from_col_count = self.columns.len();
        let to_col_count = other.columns.len();

        if self_empty || other_empty {
            // weight() will ignore matches
            return self.weight(&other, &vec![0])
        } else {
            // initialize worst case
            let mut res = to_col_count as u32 * other.get_row_count() as u32;

            // check all matches
            for m in Matches::new(from_col_count, to_col_count) {
                let w = self.weight(&other, &m);
                println!("min_weight:{} with weight:{} for match:{:?}", res, w, m);
                if w < res { res = w; }
            }
            return res
        }
    }

    /// Returns the "distance" between two [`Relation`]s.
    ///
    /// Panics if non-empty [`Relation`]s don't have the same `row_count`.
    ///
    /// The *distance* is defined as the maximum of the minimum *weight* between the [`Relation`]s in each direction. This is achieved in the direction toward the [`Relation`] with the larger number of [`Column`]s, in essence, because no one-for-one column-matching function can cover the all of the [`Column`]s in the destination (not [*surjective*](https://en.wikipedia.org/wiki/Surjective_function)), guaranteeing a minimum penalty.
    ///
    /// See Kenneth P. Ewing "Bounds for the Distance Between Relations," arXiv:2105.01690.
    ///
    /// # Example
    ///
    pub fn distance(&self, other: &Relation) -> u32 {
        let from_col_count = if self.is_empty() {0} else {self.columns.len()};
        let to_col_count = if other.is_empty() {0} else {other.columns.len()};

        if from_col_count <= to_col_count {
            return self.min_weight(other)
        } else {
            return other.min_weight(self)
        }
    }
}

impl From<Vec<Column>> for Relation {
    /// Converts a [`Vec<Column>`] into a [`Relation`] if everything has the same `row_count`.
    ///
    /// Panics if they don't have the same `row_count`.
    fn from(columns: Vec<Column>) -> Self {
        let row_count = columns[0].row_count;
        assert!(
            columns
                .iter()
                .fold(true, |acc, x| acc && (x.row_count == row_count)),
            "From<Vec<Column>> for Relation requires all Columns to have same row_count"
        );
        Relation {
            row_count,
            columns,
        }
    }
}

impl From<Vec<Vec<u8>>> for Relation {
    /// Converts a [`Vec<Vec<u8>>`] into a [`Relation`] if all [`Column`]s created from the inner `Vec<u8>` have the same `row_count`.
    ///
    /// Panics if the created [`Column`]s don't have the `row_count`.
    fn from(cols: Vec<Vec<u8>>) -> Self {
        let columns: Vec<Column> = cols.into_iter().map(|x| Column::from(x)).collect();
        let row_count = columns[0].row_count;
        assert!(
            columns
                .iter()
                .fold(true, |acc, x| acc && (x.row_count == row_count)),
            "From<Vec<Vec<u8>> for Relation requires the inner Vec<u8> to have same length"
        );
        Relation {
            row_count,
            columns,
        }
    }
}

impl fmt::Display for Relation {
    /// Display as a binary matrix of rows from top to bottom and columns from left to right.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for r in 0..self.row_count {
            for c in 0..self.columns.len() {
                if self.columns[c].get_bit(r) {
                    s.push_str("1")
                } else {
                    s.push_str("0")
                };
            }
            s.push_str("\n");
        }
        write!(f, "{s}")
    }
}

impl fmt::Binary for Relation {
    /// Show the a big-endian binary representation of all [`Column`]s in the [`Relation`], one per line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // let s = self.columns.iter().enumerate().map(|x| format!("[{}]: {:08b}", x.0, x.1)).collect::<Vec<String>>().join("\n");
        let mut s = String::from("[");
        s.push_str(
            &self
                .columns
                .iter()
                .map(|x| format!("{:b}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl fmt::LowerHex for Relation {
    /// Show the a big-endian lower-hexadecimal representation of all [`Column`]s in the [`Relation`], one per line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // let s = self.columns.iter().enumerate().map(|x| format!("[{}]: {:08b}", x.0, x.1)).collect::<Vec<String>>().join("\n");
        let mut s = String::from("[");
        s.push_str(
            &self
                .columns
                .iter()
                .map(|x| format!("{:x}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl fmt::UpperHex for Relation {
    /// Show the a big-endian upper-hexadecimal representation of all [`Column`]s in the [`Relation`], one per line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // let s = self.columns.iter().enumerate().map(|x| format!("[{}]: {:08b}", x.0, x.1)).collect::<Vec<String>>().join("\n");
        let mut s = String::from("[");
        s.push_str(
            &self
                .columns
                .iter()
                .map(|x| format!("{:X}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        s.push_str("]");
        write!(f, "{s}")
    }
}

impl Not for Relation {
    type Output = Self;

    /// Performs the unary [`!`](std::ops::Not) operation for a [`Relation`].
    fn not(self) -> Self::Output {
        Relation {
            row_count: self.row_count,
            columns: self.columns.iter().map(|x|!x.clone()).collect(),
        }
    }
}

impl BitAnd for Relation {
    type Output = Self;

    /// Performs the [`^`](std::ops::BitAnd::bitand) operation for two [`Relation`]s of same `row_count` and number of `columns`.
    ///
    /// Panics if the two [`Relation`]s don't have the same `row_count` and number of `columns`.
    fn bitand(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return self.clone();
        } else if rhs.is_empty() {
            return rhs.clone();
        } else {
            assert!(self.row_count == rhs.row_count, "Relation::bitxor requires non-empty Relations to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.columns.len() == rhs.columns.len(), "Relation::bitxor requires non-empty Relations to have equal numbers of columns but: {} != {}", self.columns.len(), rhs.columns.len());
            return Relation {
                row_count: self.row_count,
                columns: zip(self.columns.clone(), rhs.columns.clone())
                    .map(|(s, r)| s & r)
                    .collect::<Vec<Column>>(),
                };
        }
    }
}

impl BitOr for Relation {
    type Output = Self;

    /// Performs the [`^`](std::ops::BitOr::bitor) operation for two [`Relation`]s of same `row_count` and number of `columns`.
    ///
    /// Panics if the two [`Relation`]s don't have the same `row_count` and number of `columns`.
    fn bitor(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone();
        } else if rhs.is_empty() {
            return self.clone();
        } else {
            assert!(self.row_count == rhs.row_count, "Relation::bitxor requires non-empty Relations to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.columns.len() == rhs.columns.len(), "Relation::bitxor requires non-empty Relations to have equal numbers of columns but: {} != {}", self.columns.len(), rhs.columns.len());
            return Relation {
                row_count: self.row_count,
                columns: zip(self.columns.clone(), rhs.columns.clone())
                    .map(|(s, r)| s | r)
                    .collect::<Vec<Column>>(),
            };
        }
    }
}

impl BitXor for Relation {
    type Output = Self;

    /// Performs the [`^`](std::ops::BitXor::bitxor) operation for two [`Relation`]s of same `row_count` and number of `columns`.
    ///
    /// Panics if the two [`Relation`]s don't have the same `row_count` and number of `columns`.
    fn bitxor(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone();
        } else if rhs.is_empty() {
            return self.clone();
        } else {
            assert!(self.row_count == rhs.row_count, "Relation::bitxor requires non-empty Relations to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.columns.len() == rhs.columns.len(), "Relation::bitxor requires non-empty Relations to have equal numbers of columns but: {} != {}", self.columns.len(), rhs.columns.len());
            return Relation {
                row_count: self.row_count,
                columns: zip(self.columns.clone(), rhs.columns.clone())
                    .map(|(s, r)| s ^ r)
                    .collect::<Vec<Column>>(),
            };
        }
    }
}

impl Sub for Relation {
    type Output = Self;

    /// Multiset difference: one-for-one remove from `self` each [`Column`] that is found in `other`
    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(
            self.row_count, other.row_count,
            "Relation::sub requires non-empty Relations to have equal row_counts but {} != {}",
            self.row_count, other.row_count
        );
        let mut new_cols = vec![];
        let mut cut_sc = vec![false; self.columns.len()];
        let mut used_oc = vec![false; other.columns.len()];
        for (i, sc) in self.columns.iter().enumerate() {
            for (j, oc) in other.columns.iter().enumerate() {
                if !cut_sc[i] && !used_oc[j] && *sc == *oc {
                    cut_sc[i] = true;
                    used_oc[j] = true;
                    print!("cut{}{} ", i, j);
                    break;
                }
            }
        }
        for i in 0..self.columns.len() {
            if !cut_sc[i] {
                new_cols.push(self.columns[i].clone())
            }
        }
        return Relation {
            row_count: self.row_count,
            columns: new_cols,
        };
    }
}

/// Represents the partition of a [`Relation`] into [`XGroup`]s.
///
/// A [`Relation`]'s [`Column`]s can be partitioned into a collection of [`XGroup`]s of Columns, each collecting [`Column`]s that are *each* not [`disjoint`](Column::is_disjoint()) (i.e., share a `true` bit) with *some* other member of the [`XGroup`] but *all* are [`disjoint`](Column::is_disjoint()) with *all* other [`Column`]s *not* in that [`XGroup`].
///
/// NB: Because a partition makes no sense away from its [`Relation`], the [`XGrouping`] inherits the [lifetime](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) of its [`Relation`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XGrouping<'a> {
    relation: &'a Relation,
    pub partition: Vec<XGroup>,
}

impl XGrouping<'_> {
    /// Returns an [`XGrouping`] for the given [`Relation`] or `None` if the [`Relation`] is [`empty`](Relation::is_empty()).
    pub fn new<'a>(rel: &'a Relation) -> XGrouping<'a> {
        rel.xgroup()
    }
}

impl fmt::Display for XGrouping<'_> {
    /// Display the partitioned [`Relation`] as a binary matrix of [`XGroup`]'ed [`Column`]s separated by a column of `' '`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rel = self.relation;
        let xgs = &self.partition;
        let mut s = String::new();

        if self.partition.len() > 0 {
            for r in 0..rel.row_count {
                for c in 0..xgs[0].col_indices.len() {
                    if rel.columns[xgs[0].col_indices[c]].get_bit(r) {
                        s.push_str("1")
                    } else {
                        s.push_str("0")
                    };
                }
                for g in 1..xgs.len() {
                    if rel.columns[xgs[g].col_indices[0]].get_bit(r) {
                        s.push_str(" 1")
                    } else {
                        s.push_str(" 0")
                    };
                    for c in 1..xgs[g].col_indices.len() {
                        if rel.columns[xgs[g].col_indices[c]].get_bit(r) {
                            s.push_str("1")
                        } else {
                            s.push_str("0")
                        };
                    }
                }
                s.push_str("\n");
            }
        };
        write!(f, "{s}")
    }
}

/// Represents an *x-group* of [`Column`]s that are [`disjoint`](Column::is_disjoint()) with all other [`Column`]s in the [`Relation`].
///
/// Each [`XGroup`] collects the [`Column`]s that share a relation (`true`) for some row with at least one other member of the [`XGroup`].
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XGroup {
    pub max: Column,
    pub col_indices: Vec<usize>,
}

/// Returns a new empty [`XGroup`].
impl XGroup {
    pub fn new() -> XGroup {
        Default::default()
    }
}

impl Index<usize> for XGroup {
    type Output = usize;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.col_indices[idx]
    }
}

/// Represents a *function* between [`Relation`]s as an [`Iterator`] of matches between [`Column`]s.
///
/// Each call to `next()` returns a new [`Vec`] of length `cols1` selected from `0..cols2`, with repetition possible. The iterator terminates after `cols2.pow(cols1)` variations.
///
/// Example
/// ```
/// use relmetric::Matches;
///
/// let mut m = Matches::new(2,2);
/// assert_eq!(m.next(), Some(vec![0,0]));
/// assert_eq!(m.next(), Some(vec![1,0]));
/// assert_eq!(m.next(), Some(vec![0,1]));
/// assert_eq!(m.next(), Some(vec![1,1]));
/// assert_eq!(m.next(), None);
/// ```
#[derive(Debug)]
pub struct Matches {
    matches: Vec<usize>,
    cols1: usize,
    cols2: usize,
    col: usize,
}

impl Matches {
    pub fn new(cols1: usize, cols2: usize) -> Matches {
        Matches {
            matches: vec![],
            cols1,
            cols2,
            col: 0,
        }
    }
}

impl Iterator for Matches {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        println!("{:?}", self);
        if self.matches.len() == 0 {
            self.matches = vec![0; self.cols1];
            self.col = 0;
            return Some(self.matches.clone())
        } else if self.matches[self.col] + 1 < self.cols2 {
            self.matches[self.col] += 1;
            return Some(self.matches.clone());
        } else {
            self.col += 1;
            while self.col < self.cols1
                && self.matches[self.col] + 1 == self.cols2 {
                self.col += 1
            }
            if self.col == self.cols1 {
                return None;
            } else {
                self.matches[self.col] += 1;
                for i in 0..self.col {
                    self.matches[i] = 0
                }
                self.matches[0] = 0;
                self.col = 0;
                return Some(self.matches.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn col_new_works() {
        let res: Column = Column::new();
        let want = Column {
            row_count: 0,
            bit_field: vec![],
        };
        assert_eq!(res, want)
    }

    #[test]
    fn col_zero_works() {
        let res = Column::zero(32);
        let want = Column {
            row_count: 32,
            bit_field: vec![0u8; 4],
        };
        assert_eq!(res, want);
    }

    #[test]
    fn col_is_empty_works() {
        let c0 = Column::new();
        let c1 = Column {
            row_count: 32,
            bit_field: vec![0x30u8, 0x00u8, 0x00u8, 0x0fu8],
        };
        assert!(c0.is_empty(), "{:?} should be empty", c0);
        assert!(!c1.is_empty(), "{:?} should not be empty", c1);
    }

    #[test]
    fn col_is_zero_works() {
        let c0 = Column::new();
        let c1 = Column {
            row_count: 32,
            bit_field: vec![0u8, 0u8, 0u8, 0u8],
        };
        assert!(!c0.is_zero(), "{:?} should not be zero", c0);
        assert!(c1.is_zero(), "{:?} should be zero", c1);
    }

    #[test]
    fn col_from_vec_works() {
        let c1a = Column::from(vec![0x3000u16, 0x000fu16]);
        let c1b = Column {
            row_count: 32,
            bit_field: vec![0x30u8, 0x00u8, 0x00u8, 0x0fu8],
        };
        assert_eq!(c1a, c1b, "{:?} should == {:?}", c1a, c1b)
    }

    #[test]
    #[should_panic]
    fn col_get_bit_empty_panics() {
        Column::new().get_bit(5);
    }

    #[test]
    fn col_get_bit_works() {
        // let c0 = Column::new();
        let mut c1 = Column::from(vec![0x30u8, 0x00u8, 0x00u8, 0x0fu8]);
        assert_eq!(
            c1.get_bit(1),
            false,
            "\nColumn::get_bit({}) fails for\n{:b}",
            2,
            c1
        );
        assert_eq!(
            c1.get_bit(2),
            true,
            "\nColumn::get_bit({}) fails for\n{:b}",
            2,
            c1
        );
        assert_eq!(
            c1.get_bit(5),
            false,
            "\nColumn::get_bit({}) fails for\n{:b}",
            5,
            c1
        );
        assert_eq!(
            c1.get_bit(27),
            false,
            "\nColumn::get_bit({}) fails for\n{:b}",
            27,
            c1
        );
        assert_eq!(
            c1.get_bit(28),
            true,
            "\nColumn::get_bit({}) fails for\n{:b}",
            28,
            c1
        );
        assert_eq!(
            c1.get_bit(31),
            true,
            "\nColumn::get_bit({}) fails for\n{:b}",
            31,
            c1
        );
        let trim = c1.trim_row_count();
        assert_eq!(
            c1.get_bit(1),
            false,
            "\nColumn::get_bit({}) fails for trimmed to 0..{}\n{:b}",
            2,
            trim,
            c1
        );
        assert_eq!(
            c1.get_bit(2),
            true,
            "\nColumn::get_bit({}) fails for trimmed to 0..{}\n{:b}",
            2,
            trim,
            c1
        );
        assert_eq!(
            c1.get_bit(5),
            false,
            "\nColumn::get_bit({}) fails for trimmed to 0..{}\n{:b}",
            5,
            trim,
            c1
        );
        assert_eq!(
            c1.get_bit(23),
            false,
            "\nColumn::get_bit({}) fails for trimmed to 0..{}\n{:b}",
            23,
            trim,
            c1
        );
        assert_eq!(
            c1.get_bit(27),
            true,
            "\nColumn::get_bit({}) fails for trimmed to 0..{}\n{:b}",
            27,
            trim,
            c1
        );
    }

    #[test]
    #[should_panic]
    fn col_set_bit_empty_panics() {
        let mut c0 = Column::new();
        c0.set_bit(12, true);
    }

    #[test]
    fn col_set_bit_works() {
        let mut c1 = Column::from(vec![0x30u8, 0x00u8, 0x00u8, 0x0fu8]);
        c1.set_bit(0, true);
        assert_eq!(
            c1.get_bit(0),
            true,
            "\nColumn::set_bit({}) {} fails, got\n{:b}",
            0,
            true,
            c1
        );
        c1.set_bit(2, false);
        assert_eq!(
            c1.get_bit(2),
            false,
            "\nColumn::set_bit({}) {} fails, got\n{:b}",
            2,
            false,
            c1
        );
        c1.set_bit(12, false);
        assert_eq!(
            c1.get_bit(12),
            false,
            "\nColumn::set_bit({}) {} fails, got\n{:b}",
            2,
            false,
            c1
        );

        let trim = c1.trim_row_count();
        c1.set_bit(23, true);
        assert_eq!(
            c1.get_bit(23),
            true,
            "Column::set_bit({}) {} fails for trimmed 0..{}\n{:b}",
            0,
            false,
            trim,
            c1
        );
        c1.set_bit(2, true);
        assert_eq!(
            c1.get_bit(2),
            true,
            "Column::set_bit({}) {} fails for trimmed 0..{}\n{:b}",
            2,
            true,
            trim,
            c1
        );
        c1.set_bit(5, false);
        assert_eq!(
            c1.get_bit(5),
            false,
            "Column::set_bit({}) {} fails for trimmed 0..{}\n{:b}",
            5,
            false,
            trim,
            c1
        );
        c1.set_bit(27, true);
        assert_eq!(
            c1.get_bit(27),
            true,
            "Column::set_bit({}) {} fails for trimmed 0..{}\n{:b}",
            27,
            true,
            trim,
            c1
        );
    }

    #[test]
    fn col_display() {
        let c = Column::from(vec![0b10000000u8, 0b00000001u8]);
        let mut res = format!("{}", c);
        let mut want = "1\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n1\n";
        assert_eq!(res, want, "fmt::Display fails for {:b}", c);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        res = format!("{}", c1);
        want = "0\n0\n1\n1\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n0\n1\n1\n1\n1\n";
        assert_eq!(res, want, "fmt::Display fails for {:b}", c1);
    }

    #[test]
    fn col_binary() {
        let c0 = Column::new();
        let mut res = format!("{:b}", c0);
        let mut want = "[]";
        assert_eq!(res, want, "fmt::Binary failed for {:?}", c0);
        let mut c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        res = format!("{:b}", c1);
        want = "[00110000, 00000000, 00000000, 00001111]";
        assert_eq!(res, want, "fmt::Binary failed for {:?}", c1);
        c1.trim_row_count();
        res = format!("{:b}", c1);
        want = "[00110000, 00000000, 00000000, 1111]";
        assert_eq!(res, want, "fmt::Binary failed for {:?}", c1);
    }

    #[test]
    fn col_lower_hex() {
        let c0 = Column::new();
        let mut res = format!("{:x}", c0);
        let mut want = "[]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c0);
        let mut c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        res = format!("{:x}", c1);
        want = "[30, 00, 00, 0f]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c1);
        c1.trim_row_count();
        res = format!("{:x}", c1);
        want = "[30, 00, 00, f]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c1);
    }

    #[test]
    fn col_upper_hex() {
        let c0 = Column::new();
        let mut res = format!("{:X}", c0);
        let mut want = "[]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c0);
        let mut c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        res = format!("{:X}", c1);
        want = "[30, 00, 00, 0F]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c1);
        c1.trim_row_count();
        res = format!("{:X}", c1);
        want = "[30, 00, 00, F]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", c1);
    }

    #[test]
    fn col_not_works() {
        let empty = Column::new();
        let c0 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        assert_eq!(!empty.clone(), empty, "Column::not() failed to leave empty unchanged");
        assert_eq!(!c0, Column::from(vec![!0x0000u16, !0x0000u16]));
        assert_eq!(!c1, Column::from(vec![!0x3000u16, !0x000fu16]));
    }

    #[test]
    fn col_bitand_works() {
        let empty = Column::new();
        let c0 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let c3 = Column::from(vec![0x1000u16, 0x000fu16]);
        assert_eq!(
            c0.clone().bitand(empty.clone()),
            c0,
            "\nColumn::BitAnd fails for\n{:b}\n{:b}",
            c0,
            empty
        );
        assert_eq!(
            c0.clone().bitand(c1.clone()),
            c0,
            "\nColumn::BitAnd fails for\n{:b}\n{:b}",
            c0,
            c1
        );
        assert_eq!(
            c1.clone().bitand(c2.clone()),
            c3,
            "\nColumn::BitAnd fails for\n{:b}\n{:b}",
            c1,
            c2
        );
    }

    #[test]
    fn col_bitor_works() {
        let empty = Column::new();
        let c0 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let c3 = Column::from(vec![0x300fu16, 0x0f3fu16]);
        assert_eq!(
            c0.clone().bitor(empty.clone()),
            c0,
            "\nColumn::BitOr fails for\n{:b}\n{:b}",
            c0,
            empty
        );
        assert_eq!(
            c0.clone().bitor(c1.clone()),
            c1,
            "\nColumn::BitOr fails for\n{:b}\n{:b}",
            c0,
            c1
        );
        assert_eq!(
            c1.clone().bitor(c2.clone()),
            c3,
            "\nColumn::BitOr fails for\n{:b}\n{:b}",
            c1,
            c2
        );
    }

    #[test]
    fn col_bitxor_works() {
        let empty = Column::new();
        let c0 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let c3 = Column::from(vec![0x200fu16, 0x0f30u16]);
        assert_eq!(
            c0.clone().bitxor(empty.clone()),
            c0,
            "\nColumn::BitXor fails for\n{:b}\n{:b}",
            c0,
            empty
        );
        assert_eq!(
            c0.clone().bitxor(c1.clone()),
            c1,
            "\nColumn::BitXor fails for\n{:b}\n{:b}",
            c0,
            c1
        );
        assert_eq!(
            c1.clone().bitxor(c2.clone()),
            c3,
            "\nColumn::BitXor fails for\n{:b}\n{:b}",
            c1,
            c2
        );
    }

    #[test]
    fn col_is_disjoint_works() {
        let empty = Column::new();
        let zero = Column::zero(16);
        let c1 = Column::from(vec![0b10000000u8, 0b00000001u8]);
        let c2 = Column::from(vec![0b00000001u8, 0b10000000u8]);
        let c3 = Column::from(vec![0b10000001u8, 0b10000000u8]);
        assert!(
            !empty.is_disjoint(&empty),
            "Fails to see that empties are NOT disjoint:\n left: {:?}\nright: {:?}",
            empty,
            empty
        );
        assert!(
            !zero.is_disjoint(&zero),
            "Fails to see that zeros are NOT disjoint:\n left: {:?}\nright: {:?}",
            zero,
            zero
        );
        assert!(
            !empty.is_disjoint(&zero),
            "Fails to see that empty and zero are NOT disjoint:\n left: {:?}\nright: {:?}",
            empty,
            zero
        );
        assert!(
            !zero.is_disjoint(&empty),
            "Fails to see that zero and empty are NOT disjoint:\n left: {:?}\nright: {:?}",
            zero,
            empty
        );
        assert!(
            c1.is_disjoint(&empty),
            "Fails to see that {:?} is disjoint from empty {:?}",
            c1,
            empty
        );
        assert!(
            c1.is_disjoint(&zero),
            "Fails to see that {:?} is disjoint from zero {:?}",
            c1,
            zero
        );
        assert!(
            c1.is_disjoint(&c2),
            "Fails to see that {:?} is disjoint from {:?} for c1 {:?} and c2 {:?}",
            c1,
            c2,
            c1,
            c2
        );
        assert!(
            !c2.is_disjoint(&c3),
            "Fails to see that {:?} is NOT disjoint from {:?} for c1 {:?} and c2 {:?}",
            c2,
            c3,
            c1,
            c2
        );
    }

    #[test]
    fn new_rel_works() {
        let res = Relation::new();
        let want = Relation {
            row_count: 0,
            columns: vec![],
        };
        assert_eq!(res, want)
    }

    #[test]
    fn rel_is_empty_works() {
        let r0 = Relation::new();
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let r1 = Relation {
            row_count: 32,
            columns: vec![c1, c2],
        };
        assert!(r0.is_empty(), "{:?} should not be empty", r0);
        assert!(!r1.is_empty(), "{:?} should be empty", r1);
    }

    #[test]
    fn rel_from_col_vec_works() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let r1a = Relation::from(vec![c1.clone(), c2.clone()]);
        let r1b = Relation {
            row_count: 32,
            columns: vec![c1, c2],
        };
        assert_eq!(r1a, r1b, "{:?} should == {:?}", r1a, r1b)
    }

    #[test]
    fn rel_display() {
        let r1 = Relation::from(vec![
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x0000u16, 0x0000u16]),
        ]);
        let res = format!("{}", r1);
        let want = String::from("00\n00\n10\n10\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n10\n10\n10\n10\n");
        assert_eq!(res, want, "\nfmt::Display failed for r1 {:b}", r1);
    }

    #[test]
    fn rel_lower_hex() {
        let r0 = Relation::new();
        let mut r1 = Relation::from(vec![
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x0000u16, 0x0000u16]),
        ]);
        let mut res = format!("{:x}", r0);
        let mut want = "[]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", r0);
        res = format!("{:x}", r1);
        want = "[[30, 00, 00, 0f], [00, 00, 00, 00]]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", r1);
        r1.trim_row_count();
        res = format!("{:x}", r1);
        want = "[[30, 00, 00, f], [00, 00, 00, 0]]";
        assert_eq!(res, want, "fmt::LowerHex failed for {:?}", r1);
    }

    #[test]
    fn sets_and_gets_col() {
        let c0 = Column::new();
        let zero32 = Column {row_count: 32, bit_field: vec![0;4]};
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let mut r1 = Relation::from(vec![c1.clone(), c2.clone()]);

        assert_eq!(r1.get_col(0), &c1, "\nFails to get_col[{}] from:{:?}", 0, r1);
        assert_eq!(r1.get_col(1), &c2, "\nFails to get_col[{}] from:{:?}", 1, r1);

        r1.set_col(0, c0.clone());
        assert_eq!(r1.get_col(0), &zero32, "\nFails to set_col[{}] to empty of proper length, got:\n {:?}", 0, r1);

        r1.set_col(0, c2.clone());
        assert_eq!(r1.get_col(0), &c2, "\nFails to set_col[{}] to non-empty {:?}, got:\n {:?}", 0, &c2, r1);

        r1.set_col(1, c1.clone());
        assert_eq!(r1.get_col(1), &c1, "\nFails to set_col[{}] to non-empty {:?}, got:\n {:?}", 1, &c1, r1);
    }

    #[test]
    fn col_max_true_bit_works() {
        let mut c = Column::new();
        assert_eq!(c.max_true_bit(), 0, " for {:?}", c);
        c = Column::from(vec![0b11111111u8]);
        assert_eq!(c.max_true_bit(), 8, " for {:?}", c);
        c = Column::from(vec![0b1111u8, 0b111u8]);
        assert_eq!(c.max_true_bit(), 11, " for {:?}", c);
        c = Column::from(vec![0b1111u32, 0b1111u32]);
        assert_eq!(c.max_true_bit(), 60, " for {:?}", c);
    }

    #[test]
    fn col_trim_row_count_works() {
        let mut c = Column::from(vec![0b1111u32, 0b1111u32]);
        assert_eq!(c.row_count, 64);
        assert_eq!(c.trim_row_count(), 60);
        assert_eq!(c.row_count, 60);
    }

    #[test]
    fn rel_not_works() {
        let empty = Relation::new();
        let r1 = Relation::from(vec![
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
        ]);
        let r1n = Relation::from(vec![
            Column::from(vec![!0x0000u16, !0x0000u16]),
            Column::from(vec![!0x3000u16, !0x000fu16]),
        ]);
        assert_eq!(!empty.clone(), empty, "\nRelation::not() failed to leave empty unchanged");
        assert_eq!(!r1.clone(), r1n, "\nRelation::not() failed for\n {:?}", r1);
    }

    #[test]
    fn rel_bitand_works() {
        let empty = Relation::new();
        let r1 = Relation::from(vec![
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0x100fu16, 0x0f3fu16]),
            Column::from(vec![0x1000u16, 0x0001u16]),
            ]);
        let r3 = Relation::from(vec![
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x1000u16, 0x0001u16]),
            ]);
        assert_eq!(empty.clone().bitand(empty.clone()), empty, "\nRelation::bitand() failed for:\n {:?}\n {:?}",empty, empty);
        assert_eq!(empty.clone().bitand(r1.clone()), empty, "\nRelation::bitand() failed for:\n {:?}\n {:?}",empty, r1);
        assert_eq!(r1.clone().bitand(r2.clone()), r3, "\nRelation::bitand() failed for:\n {:?}\n {:?}",r1, r2);
        assert_eq!(r2.clone().bitand(r1.clone()), r3, "\nRelation::bitand() failed for:\n {:?}\n {:?}",r2, r1);
    }

    #[test]
    fn rel_bitor_works() {
        let empty = Relation::new();
        let r1 = Relation::from(vec![
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0x100fu16, 0x0f3fu16]),
            Column::from(vec![0x1000u16, 0x0001u16]),
            ]);
        let r3 = Relation::from(vec![
            Column::from(vec![0x100fu16, 0x0f3fu16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
            ]);
        assert_eq!(empty.clone().bitor(empty.clone()), empty, "\nRelation::bitor() failed for:\n {:?}\n {:?}", empty, empty);
        assert_eq!(empty.clone().bitor(r1.clone()), r1, "\nRelation::bitor() failed for:\n {:?}\n {:?}", empty, r1);
        assert_eq!(r1.clone().bitor(r2.clone()), r3, "\nRelation::bitor() failed for:\n {:?}\n {:?}", r1, r2);
        assert_eq!(r2.clone().bitor(r1.clone()), r3, "\nRelation::bitor() failed for:\n {:?}\n {:?}", r2, r1);
    }

    #[test]
    fn rel_bitxor_works() {
        let empty = Relation::new();
        let r1 = Relation::from(vec![
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0x100fu16, 0x0f3fu16]),
            Column::from(vec![0x1000u16, 0x0001u16]),
            ]);
        let r3 = Relation::from(vec![
            Column::from(vec![0x100fu16, 0x0f3fu16]),
            Column::from(vec![0x2000u16, 0x000eu16]),
            ]);
        assert_eq!(empty.clone().bitxor(empty.clone()), empty, "\nRelation::bitxor() failed for:\n {:?}\n {:?}", empty, empty);
        assert_eq!(empty.clone().bitxor(r1.clone()), r1, "\nRelation::bitxor() failed for:\n {:?}\n {:?}", empty, r1);
        assert_eq!(r1.clone().bitxor(r2.clone()), r3, "\nRelation::bitxor() failed for:\n {:?}\n {:?}", r1, r2);
        assert_eq!(r2.clone().bitxor(r1.clone()), r3, "\nRelation::bitxor() failed for:\n {:?}\n {:?}", r2, r1);
    }

    #[test]
    fn rel_max_true_bit_works() {
        let r0 = Relation::from(vec![Column::new()]);
        assert_eq!(r0.max_true_bit(), 0, " for {:?}", r0);
        let r1 = Relation::from(vec![Column::from(vec![0b11111111u8])]);
        assert_eq!(r1.max_true_bit(), 8, " for {:?}", r1);
        let r2 = Relation::from(vec![Column::from(vec![0b1111u8, 0b111u8])]);
        assert_eq!(r2.max_true_bit(), 11, " for {:?}", r2);
        let r3 = Relation::from(vec![Column::from(vec![0b1111u32, 0b1111u32])]);
        assert_eq!(r3.max_true_bit(), 60, " for {:?}", r3);
    }

    #[test]
    fn rel_trim_row_count_works() {
        let mut r = Relation::from(vec![Column::from(vec![0b1111u32, 0b1111u32])]);
        assert_eq!(r.row_count, 64);
        assert_eq!(r.trim_row_count(), 60);
        assert_eq!(r.row_count, 60);
    }

    #[test]
    fn rel_sub_works() {
        let r1 = Relation::from(vec![
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x0000u16, 0x0000u16]),
            Column::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x0000u16, 0x0000u16]),
        ]);
        let r3 = Relation::from(vec![
            Column::from(vec![0x3000u16, 0x000fu16]),
            Column::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let mut res = r1.clone() - r2.clone();
        assert_eq!(
            res, r3,
            "\nRelation::sub fails for\n lhs:{:b}\n rhs:{:b}\nshould be {:b}\ngot       {:b}",
            r1, r2, r3, res
        );
        res = res - r3.clone();
        assert!(
            res.is_empty(),
            "\nRelation::sub fails for\n lhs:{:b}\n rhs:{:b}\nshould be {:b}\ngot       {:b}",
            res,
            r3,
            Relation::new(),
            res
        );
    }

    #[test]
    fn xgroup_works() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c3 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let mut r1 = Relation::from(vec![c1.clone(), c1, c2.clone(), c3.clone()]);
        let mut res = r1.xgroup().partition.len();
        let mut want = 2;
        assert_eq!(
            res, want,
            "\n\nNumber of XGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.set_col(2, c2.clone());
        res = r1.xgroup().partition.len();
        assert_eq!(
            res, want,
            "\n\nNumber of XGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.set_col(2, c3.clone());
        res = r1.xgroup().partition.len();
        want = 1;
        assert_eq!(
            res, want,
            "\n\nNumber of XGroups {} != {} for\n{:?}",
            res, want, r1
        );
    }

    #[test]
    fn xgrouping_display() {
        let r = Relation::from(vec![
            Column::from(vec![0b0000u8]),
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b0010u8]),
            Column::from(vec![0b0010u8]),
            Column::from(vec![0b0001u8]),
            Column::from(vec![0b0001u8]),
            Column::from(vec![0b0001u8]),
            Column::from(vec![0b0001u8]),
        ]);
        let xgs = r.xgroup();
        let x_grouping = XGrouping::new(&r);
        let res = format!("{}", x_grouping);
        let want = r#"0 00 000 0000
0 00 000 0000
0 00 000 0000
0 00 000 0000
0 00 111 0000
0 00 011 0000
0 11 000 0000
0 00 000 1111
"#;
        assert_eq!(
            res, want,
            "r:\n{}\nx_grouping:\n{}\nxgs:\n{:?}\n",
            r, x_grouping, xgs
        )
    }

    #[test]
    fn kappa_works() {
        // "R" of Example 10 in "Metric Comparisons".
        let ex10_r = Relation::from(vec![
            Column::from(vec![0x0u8]),
            Column::from(vec![0x08u8]),
            Column::from(vec![0x0cu8]),
            Column::from(vec![0x0cu8]),
            Column::from(vec![0x02u8]),
            Column::from(vec![0x02u8]),
            Column::from(vec![0x01u8]),
            Column::from(vec![0x01u8]),
            Column::from(vec![0x01u8]),
            Column::from(vec![0x01u8]),
        ]);
        // "R3" of Example 12 in "Metric Comparisons".
        let ex12_r3 = Relation::from(vec![
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1100u8]),
        ]);
        // "R4" of Example 13 in "Metric Comparisons".
        let ex13_r4 = Relation::from(vec![
            Column::from(vec![0b0000u8]),
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1100u8]),
        ]);
        assert_eq!(
            ex12_r3.kappa(Some(5)),
            0,
            "Fails Example 12: kappa(R3, N=5) => 0"
        );
        assert_eq!(
            ex13_r4.kappa(Some(5)),
            1,
            "Fails Example 13: kappa(R4, N=5) => 1"
        );
        assert_eq!(
            ex10_r.kappa(Some(4)),
            1,
            "Fails Example 14: kappa(R, N=4) => 1"
        );
        assert_eq!(
            ex10_r.kappa(Some(5)),
            3,
            "Fails Example 15: kappa(R, N=5) => 3"
        );
    }

    #[test]
    fn rel_dist_bound_works() {
        // "R1" of Example 18 in "Metric Comparisons".
        let ex18_r1 = Relation::from(vec![
            Column::from(vec![0b10111u8]),
            Column::from(vec![0b01111u8]),
            Column::from(vec![0b10111u8]),
            Column::from(vec![0b11001u8]),
            Column::from(vec![0b00111u8]),
            Column::from(vec![0b00000u8]),
            Column::from(vec![0b10001u8]),
            Column::from(vec![0b11001u8]),
            Column::from(vec![0b01001u8]),
            Column::from(vec![0b11101u8]),
        ]);
        // "R2" of Example 18 in "Metric Comparisons".
        let ex18_r2 = Relation::from(vec![
            Column::from(vec![0b00100u8]),
            Column::from(vec![0b00010u8]),
            Column::from(vec![0b11100u8]),
            Column::from(vec![0b11110u8]),
            Column::from(vec![0b01000u8]),
            Column::from(vec![0b11101u8]),
            Column::from(vec![0b10100u8]),
            Column::from(vec![0b11010u8]),
            Column::from(vec![0b01111u8]),
            Column::from(vec![0b10101u8]),
        ]);
        // "R1" of Example 19 in "Metric Comparisons".
        let ex19_r1 = Relation::from(vec![
            Column::from(vec![0b00000u8]),
            Column::from(vec![0b00101u8]),
            Column::from(vec![0b11000u8]),
            Column::from(vec![0b00100u8]),
            Column::from(vec![0b01000u8]),
            Column::from(vec![0b10000u8]),
            Column::from(vec![0b00101u8]),
            Column::from(vec![0b00000u8]),
            Column::from(vec![0b00100u8]),
            Column::from(vec![0b11000u8]),
        ]);
        // "R2" of Example 19 in "Metric Comparisons".
        let ex19_r2 = Relation::from(vec![
            Column::from(vec![0b00000u8]),
            Column::from(vec![0b00101u8]),
            Column::from(vec![0b11000u8]),
            Column::from(vec![0b01100u8]),
            Column::from(vec![0b01000u8]),
            Column::from(vec![0b10000u8]),
            Column::from(vec![0b00001u8]),
            Column::from(vec![0b00001u8]),
            Column::from(vec![0b00100u8]),
            Column::from(vec![0b10010u8]),
        ]);
        assert_eq!(
            ex18_r1.rel_dist_bound(&ex18_r2),
            8,
            "Fails Example 18 (corrected): rel_dist_bound(R1,R2) => 8"
        );
        assert_eq!(
            ex19_r1.rel_dist_bound(&ex19_r2),
            2,
            "Fails Example 19:  rel_dist_bound(R1,R2) => 2"
        );
    }

    #[test]
    fn rel_match_columns_works() {
        let r1 = Relation::from(vec![
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b1001u8]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0b0000u8]),
            Column::from(vec![0b1000u8]),
        ]);
        let col_matches = vec![1usize, 0usize];
        let res = r1.match_columns(&r2, &col_matches);
        let want = Relation::from(vec![
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b0000u8]),
        ]);
        assert_eq!(res, want, "\nRelation::match_columns fails with col_matches[{:?}] for \n{:x} \n{:x}\nwanted {:x}\ngot    {:x}\n", col_matches, r1, r2, want, res);

        let ex1_r1 = Relation {
            row_count: 1,
            columns: vec![Column {
                row_count: 1,
                bit_field: vec![0b1u8],
            }],
        };
        let ex1_r2 = Relation::new();
        let ex1_matches = vec![0];
        let ex1_res = ex1_r1.match_columns(&ex1_r2, &ex1_matches);
        let ex1_want = Relation::zero(1, 1);
        assert_eq!(res, want, "\nRelation::match_columns fails Ex 1 with col_matches[{:?}] for\n{:x}\n{:x}\nwanted {:x}\ngot    {:x}\n", ex1_matches, ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1010u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0011u8]),
        ]);
        // ex2_r1.trim_row_count();
        let ex2_r2 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0101u8]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_matches12 = vec![0, 1, 1, 2];
        let ex2_matches21 = vec![1, 2, 0];
        let ex2_res12 = ex2_r1.match_columns(&ex2_r2, &ex2_matches12);
        let ex2_want12 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0101u8]),
        ]);
        assert_eq!(ex2_res12, ex2_want12, "\nRelation::match_columns fails Ex 2 with col_matches[{:?}] for\n{:x}\n{:x}\nwanted {:x}\ngot    {:x}\n", ex2_matches12, ex2_r1, ex2_r2, ex2_want12, ex2_res12);

        let ex2_res21 = ex2_r2.match_columns(&ex2_r1, &ex2_matches21);
        let ex2_want21 = Relation::from(vec![
            Column::from(vec![0b1010u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b1100u8]),
        ]);
        assert_eq!(ex2_res21, ex2_want21, "\nRelation::match_columns fails Ex 2 with col_matches[{:?}] for\n{:x}\n{:x}\nwanted {:x}\ngot    {:x}\n", ex2_matches21, ex2_r2, ex2_r1, ex2_want21, ex2_res21);
    }

    #[test]
    fn rel_weight_works() {
        let ex1_r1 = Relation {
            row_count: 1,
            columns: vec![Column {
                row_count: 1,
                bit_field: vec![0b1u8],
            }],
        };
        let ex1_r2 = Relation::new();
        let ex1_matches = vec![0];
        let ex1_res = ex1_r1.weight(&ex1_r2, &ex1_matches);
        let ex1_want = 1;
        assert_eq!(ex1_res, ex1_want, "\nRelation::weight fails Ex 1 with col_matches[{:?}] for\n {:b}\n {:b}\nwanted:{} got:{}", ex1_matches, ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1010u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0011u8]),
        ]);
        // ex2_r1.trim_row_count();
        let ex2_r2 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0101u8]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_matches12 = vec![0, 1, 1, 2];
        let ex2_res12 = ex2_r1.weight(&ex2_r2, &ex2_matches12);
        let ex2_want12 = 1;
        assert_eq!(ex2_res12, ex2_want12, "\nRelation::weight fails Ex 2 r1->r2 with col_matches[{:?}] for\n {:b}\n {:b}\nwanted:{} got:{}", ex2_matches12, ex2_r1, ex2_r2, ex2_want12, ex2_res12);

        let ex2_matches21 = vec![1, 2, 0];
        let ex2_res21 = ex2_r2.weight(&ex2_r1, &ex2_matches21);
        let ex2_want21 = 2;
        assert_eq!(ex2_res21, ex2_want21, "\nRelation::weight fails Ex 2 r2->r1 with col_matches[{:?}] for\n {:b}\n {:b}\nwanted:{} got:{}", ex2_matches21, ex2_r2, ex2_r1, ex2_want21, ex2_res21);
    }

    #[test]
    fn match_iterator_works() {
        let mut m = Matches::new(2,3);
        assert_eq!(m.next(), Some(vec![0,0]));
        assert_eq!(m.next(), Some(vec![1,0]));
        assert_eq!(m.next(), Some(vec![2,0]));
        assert_eq!(m.next(), Some(vec![0,1]));
        assert_eq!(m.next(), Some(vec![1,1]));
        assert_eq!(m.next(), Some(vec![2,1]));
        assert_eq!(m.next(), Some(vec![0,2]));
        assert_eq!(m.next(), Some(vec![1,2]));
        assert_eq!(m.next(), Some(vec![2,2]));
        assert_eq!(m.next(), None);
    }

    #[test]
    fn rel_min_weight_works() {
        let ex1_r1 = Relation {
            row_count: 1,
            columns: vec![Column {
                row_count: 1,
                bit_field: vec![0b1u8],
            }],
        };
        let ex1_r2 = Relation::new();
        let ex1_res = ex1_r1.min_weight(&ex1_r2);
        let ex1_want = 1;
        assert_eq!(ex1_res, ex1_want, "\nRelation::min_weight fails Ex 1 for\n {:b}\n {:b}\nwanted:{} got:{}", ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1010u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0011u8]),
        ]);
        // ex2_r1.trim_row_count();
        let ex2_r2 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0101u8]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_res12 = ex2_r1.min_weight(&ex2_r2);
        let ex2_want12 = 1;
        assert_eq!(ex2_res12, ex2_want12, "\nRelation::min_weight fails Ex 2 r1->r2 for\n {:b}\n {:b}\nwanted:{} got:{}", ex2_r1, ex2_r2, ex2_want12, ex2_res12);

        let ex2_res21 = ex2_r2.min_weight(&ex2_r1);
        let ex2_want21 = 2;
        assert_eq!(ex2_res21, ex2_want21, "\nRelation::min_weight fails Ex 2 r2->r1 for\n {:b}\n {:b}\nwanted:{} got:{}", ex2_r2, ex2_r1, ex2_want21, ex2_res21);
    }

    #[test]
    fn rel_metric_works() {
        let ex1_r1 = Relation {
            row_count: 1,
            columns: vec![Column {
                row_count: 1,
                bit_field: vec![0b1u8],
            }],
        };
        let ex1_r2 = Relation::new();
        let ex1_res = ex1_r1.distance(&ex1_r2);
        let ex1_want = 1;
        assert_eq!(ex1_res, ex1_want, "\nRelation::metric fails Ex 1 for\n {:b}\n {:b}\nwanted:{} got:{}", ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1010u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0011u8]),
        ]);
        // ex2_r1.trim_row_count();
        let ex2_r2 = Relation::from(vec![
            Column::from(vec![0b1100u8]),
            Column::from(vec![0b1011u8]),
            Column::from(vec![0b0101u8]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_res = ex2_r2.distance(&ex2_r1);
        let ex2_want = 2;
        assert_eq!(ex2_res, ex2_want, "\nRelation::metric fails Ex 2 r2->r1 for\n {:b}\n {:b}\nwanted:{} got:{}", ex2_r2, ex2_r1, ex2_want, ex2_res);
    }

}
