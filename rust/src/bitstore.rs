/*! Bit Stores

This module creates the [`BitStore`] `trait` for efficiently representing expandable vectors of `bool` values.
 */

use core::fmt;
use core::ops::{Bound, Range, RangeBounds};
use core::iter::zip;
use core::hash::Hash;
use std::fmt::{Write, Debug};
use std::ops::{Not, BitAnd, BitOr, BitXor, Index};

use serde::{Serialize, Deserialize};

/// A `trait` for a *bit store*.
pub trait BitStore {
    /// Create a new, empty *bit store*.
    fn new() -> Self;

    /// Create a *bit store* of given `bit_length` with bits all `false` (*i.e.*, a "zero" *bit store*).
    fn zero(bit_length: usize) -> Self
    where
        Self: Sized
    {
        let mut res = Self::new();
        res.set_capacity(bit_length).unwrap();
        res.set_bit_length(bit_length).unwrap();
        res.set_bits(0..bit_length, vec![false; bit_length]).unwrap();
        res
    }

    /// Create a *bit store* with `true` bits at given indices.
    fn from_indices(bits: Vec<usize>) -> Self
    where
        Self: Sized
    {
        match bits.iter().max() {
            None => Self::new(),
            Some(&n) => {
                let mut res = Self::zero(n + 1);
                for bit in bits {
                    res.set_bit(bit, true).unwrap();
                };
                res
            }
        }
    }

    /// Return `true` if the *bit store* is empty, *i.e.*, the `bit_length` == 0.
    fn is_empty(&self) -> bool {
        self.get_bit_length() == 0
    }

    /// Return `true` if the *bit store* is zero, *i.e.*, the `bit_length` > 0 and all `bits` are `false`.
    fn is_zero(&self) -> bool {
        self.get_bit_length() > 0 && self.count_ones() == 0
    }

    /// Return the number of bits actually represented by the *bit store*.
    ///
    /// **NB**: This may be less than the `capacity`.
    fn get_bit_length(&self) -> usize;

    /// Return the *bit store* with the given `bit_length` or an "out of bounds" `Err`.
    ///
    /// The `bit_length` **must not** exceed the `capacity`. To avoid possible `Err`, first use [`set_capacity()](BitStore::set_capacity()).
    fn set_bit_length(&mut self, value: usize) -> Result<&mut Self, &'static str>;

    /// Return the *capacity* of the *bit store* in bits, which is the number of bits that *can* be represented.
    fn get_capacity(&self) -> usize;

    /// Return the *bit store* with the given `capacity`, growing it if needed without increasing the [`bit_length`](BitStore::get_bit_length()), or an "out of bounds" `Err`.
    ///
    ///  This **must** equal or exceed the [`bit_length`](BitStore::get_bit_length()). To avoid possible `Err`, before increasing the `bit_length`, first use [`set_capacity()](BitStore::set_capacity()).
    fn set_capacity(&mut self, value: usize) -> Result<&mut Self, &'static str>;

    /// Return the contents of the *bit store* as a raw `Vec<u8>`.
    fn get_raw_bits(&self) -> Vec<u8>;

    /// Return the *bit store* after setting its contents to the given raw `Vec<u8>`.
    fn set_raw_bits(&mut self, bits: Vec<u8>) -> &mut Self;

    /// Return a validated [`Range`] into the *bit store* or an "out of bounds" `Err`.
    fn valid_range<T: RangeBounds<usize>>(&self, range: T) -> Result<Range<usize>, &'static str> {
        let start = match range.start_bound() {
            Bound::Excluded(&value) => value + 1,
            Bound::Included(&value) => value,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Excluded(&value) => value,
            Bound::Included(&value) => value + 1,
            Bound::Unbounded => self.get_bit_length(),
        };
        if start <= end && start <= self.get_bit_length() && end <= self.get_bit_length() {
            Ok(Range { start, end })
        } else {
            Err("out of bounds for BitStore")
        }
    }

    /// Return a `Vec` of `bool` values of the given range of bits, or an "out of bounds" `Err`.
    fn get_bits(&self, range: Range<usize>) -> Result<Vec<bool>, &'static str>;

    /// Return the `bool` value of the given bit, or an "out of bounds" `Err`.
    fn get_bit(&self, idx: usize) -> Result<bool, &'static str> {
        self.get_bits(idx..(idx + 1)).map(|x| x[0])
    }

    // Return the *bit store* with the given range of bits set to the given `bool` values, or an "out of bounds" `Err`.
    fn set_bits<T: RangeBounds<usize>>(&mut self, range: T, values: Vec<bool>) -> Result<&mut Self, &'static str>;

    // Return the *bit store* with the given bit set to the given `bool` value, or an "out of bounds" `Err`.
    fn set_bit(&mut self, idx: usize, value: bool) -> Result<&mut Self, &'static str> {
        self.set_bits(idx..(idx + 1), vec![value])
    }

    /// Return the count of `true` bits in the *bit store*.
    fn count_ones(&self) -> usize {
        self.get_bits(0..self.get_bit_length())
            .unwrap()
            .iter()
            .filter(|&&x| x)
            .count()
    }

    /// Return the given `Vec` of *bit store*s *normalized* to have the same `bit_length` and `capacity()`.
    fn normalize(bitstores: &[Self]) -> Vec<Self>
    where
        Self: Sized + Clone
    {
        let mut res = vec![];
        res.extend_from_slice(bitstores);
        if res.len() > 1 {
            let max_bit_length = bitstores.iter()
                .max_by(
                    |&a, &b|
                    a.get_bit_length().cmp(&b.get_bit_length()))
                .unwrap()
                .get_bit_length();
            for bs in &mut res {
                if bs.get_bit_length() < max_bit_length {
                    bs.set_capacity(max_bit_length).unwrap();
                    bs.set_bit_length(max_bit_length).unwrap();
                }
            }
        }
        res
    }

}

// Some private macros to help implement [`BitStore`]
//
// A macro to generate the [`From<Vec<_>.`] implementations for a [`BitStore`] for all the integer types.
// #[macro_export]
macro_rules! impl_bitstore_from_vec_int {
    ( $name:ident, $( u8 )? ) => {
        impl From<Vec<u8>> for $name {
            fn from(ints: Vec<u8>) -> Self {
                $name {
                    bit_length: ints.len() * u8::BITS as usize,
                    bits: ints,
                }
            }
        }
    };
    ( $name:ident, $( $x:ty ),+ ) => {
        $(
            impl From<Vec<$x>> for $name {
                fn from(ints: Vec<$x>) -> Self {
                    $name {
                        bit_length: ints.len() * <$x>::BITS as usize,
                        bits: ints
                            .iter()
                            .fold(vec![], |mut acc, x| {
                                acc.push(x.to_be_bytes().to_vec());
                                acc
                            })
                            .concat(),
                    }
                }
            }

        )*
    };
}

// A macro to generate the four logical / bit operations for [`BitStore`]s.
// #[macro_export]
macro_rules! impl_bitstore_bit_logic {
    ( $name:ident, Not $(, $func:tt, $op:tt)? ) => {
        impl Not for $name {
            type Output = Self;

            /// Performs the unary [`!!`](std::ops::Not) operations for a [`$name`].
            fn not(self) -> Self::Output {
                $name {
                    bit_length: self.bit_length,
                    bits: self.bits.iter().map(|x| !x).collect(),
                }
            }
        }
    };
    ( $name:ident, $trait:tt, $func:tt, $op:tt ) => {
        impl $trait for $name {
            type Output = Self;

            /// Performs the [`&`](std::ops::$trait::$func) operation for two [`$name`]s of same `bit_length`.
            ///
            /// Panics if the two [`$name`]s don't have the same `bit_length`.
            fn $func(self, rhs: Self) -> Self::Output {
                if self.is_empty() {
                    rhs
                } else if rhs.is_empty() {
                    self
                } else {
                    assert!(
                        self.bit_length == rhs.bit_length,
                        "$name::$func requires non-empty $names to have equal bit_length but: {} != {}",
                        self.bit_length,
                        rhs.bit_length
                    );
                    assert!(self.bits.len() == rhs.bits.len(), "$name::$func requires non-empty $names to have equal length bit fields but: {} != {}", self.bits.len(), rhs.bits.len());
                    $name {
                        bit_length: self.bit_length,
                        bits: zip(self.bits, rhs.bits)
                            .map(|(s, r)| s $op r)
                            .collect::<Vec<u8>>(),
                    }
                }
            }
        }
    }
}

/// A [`macro_rule`](https://doc.rust-lang.org/reference/macros-by-example.html) to define `struct`s that implement [`BitStore`].
// #[macro_export]
macro_rules! impl_bitstore {
    ( $name:tt, $title:literal ) => {
        /// $title
        ///
        /// Stores *bits* as [`bool`]s in a [`Vec`] of [`u8`] in little endian order, while enforcing a maximum `bit_length` for the whole store. Wraps getters and setters in a [`Result<_, &'static str>`] to manage out-of-bounds errors.
        #[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        pub struct $name {
            /// Count of bits represented.
            bit_length: usize,
            /// Container for bit being represented.
            bits: Vec<u8>
        }

        impl $name {
            pub fn new() -> Self {
                Default::default()
            }
        }

        impl BitStore for $name {
            fn new() -> Self {
                Self::new()
            }

            fn zero(bit_length: usize) -> Self {
                if bit_length == 0 {
                    $name {
                        bit_length,
                        bits: vec![]
                    }
                } else if bit_length % u8::BITS as usize > 0 {
                    $name {
                        bit_length,
                        bits: vec![0u8; 1 + bit_length / u8::BITS as usize]
                    }
                } else {
                    $name {
                        bit_length,
                        bits: vec![0u8; bit_length / u8::BITS as usize]
                    }
                }
            }

            fn get_bit_length(&self) -> usize {
                self.bit_length
            }

            fn set_bit_length(&mut self, value: usize) -> Result<&mut Self, &'static str> {
                if value == self.bit_length {
                    Ok(self)
                } else if value > self.bit_length && value <= self.get_capacity() {
                    self.bit_length = value;
                    Ok(self)
                } else {
                    Err("out of bounds for BitStore")
                }
            }

            fn get_capacity(&self) -> usize {
                self.bits.len() * u8::BITS as usize
            }

            fn set_capacity(&mut self, value: usize) -> Result<&mut Self, &'static str> {
                let cap = self.get_capacity();
                if value < self.bit_length {
                    Err("can't reduce BitStore capacity below bit_length")
                } else if value > cap {
                    let n = (value - cap) / u8::BITS as usize + if (value - cap) % u8::BITS as usize > 0 { 1 } else { 0 };
                    self.bits.extend(vec![0u8; n]);
                    Ok(self)
                } else if value < cap {
                    let n = value / u8::BITS as usize + if value % u8::BITS as usize > 0 { 1 } else { 0 };
                    self.bits = self.bits[0..n].to_vec();
                    Ok(self)
                } else {
                    Ok(self)
                }
            }

            fn get_raw_bits(&self) -> Vec<u8> {
                self.bits.clone()
            }

            fn set_raw_bits(&mut self, bits: Vec<u8>) -> &mut Self {
                self.bits = bits;
                self
            }

            fn get_bits(&self, range: std::ops::Range<usize>) -> Result<Vec<bool>, &'static str> {
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
                let f = |x| {
                    let the_int = x / u8::BITS as usize;
                    let the_bit = x % u8::BITS as usize;
                    if self.bits.is_empty() {
                        false
                    } else {
                        self.bits[the_int] & ROW_MASK[the_bit] > 0
                    }
                };
                Ok(self.valid_range(range)?.map(f).collect())
            }

            fn set_bits<T: std::ops::RangeBounds<usize>>(&mut self, range: T, values: Vec<bool>) -> Result<&mut Self, &'static str> {
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
                for (idx, &val) in zip(self.valid_range(range)?, values.iter()) {
                    let the_int = idx / u8::BITS as usize;
                    let the_bit = idx % u8::BITS as usize;
                    if val {
                        self.bits[the_int] |= ROW_MASK[the_bit];
                    } else {
                        self.bits[the_int] &= ! (ROW_MASK[the_bit] as u8);
                    }
                }
                Ok(self)
            }
        }

        impl Index<usize> for $name {
            type Output = bool;

            fn index(&self, index: usize) -> &Self::Output {
                match self.get_bit(index).unwrap() {
                    true => &true,
                    false => &false
                }
            }
        }

        impl From<Vec<bool>> for $name {
            fn from(bools: Vec<bool>) -> Self {
                let mut res = $name::new();
                res.set_capacity(bools.len()).unwrap();
                res.set_bit_length(bools.len()).unwrap();
                res.set_bits(0..bools.len(), bools).unwrap();
                res
            }
        }

        impl_bitstore_from_vec_int!($name, u8, u16, u32, u64, u128, usize);

        impl_bitstore_bit_logic!($name, Not, not, !);
        impl_bitstore_bit_logic!($name, BitAnd, bitand, &);
        impl_bitstore_bit_logic!($name, BitOr, bitor, |);
        impl_bitstore_bit_logic!($name, BitXor, bitxor, ^);

        impl fmt::Display for $name {
            /// Show a big-endian representation on one line.
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                std::fmt::Binary::fmt(self, f)
            }
        }

        impl fmt::Binary for $name {
            /// Show a big-endian binary representation on one line.
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let whole_ints = self.get_bit_length() / u8::BITS as usize;
                let rest_bits = self.get_bit_length() % u8::BITS as usize;
                const REST_MASK: [u8; 8] = [
                    0b10000000u8,
                    0b11000000u8,
                    0b11100000u8,
                    0b11110000u8,
                    0b11111000u8,
                    0b11111100u8,
                    0b11111110u8,
                    0b11111111u8,
                ];

                let mut s = String::from("[");
                s.push_str(
                    &self
                    .bits
                    .iter()
                    .take(whole_ints)
                    .map(|x| format!("{:08b}", x))
                    .collect::<Vec<String>>()
                    .join(", "),
                );
                if rest_bits > 0 {
                    if whole_ints > 0 {
                        s.push_str(", ")
                    };
                    // let width = rest_bits;
                    // let the_int = (self.bits[whole_ints] & REST_MASK[rest_bits - 1]) >> (u8::BITS as usize - rest_bits);
                    write!(
                        s,
                        "{:0width$b}",
                        (self.bits[whole_ints] & REST_MASK[rest_bits - 1]) >> (u8::BITS as usize - rest_bits),
                        width = rest_bits
                    )
                    .unwrap();
                }
                s.push(']');
                write!(f, "{s}")
            }
        }
    };
}
impl_bitstore!(BStore, "A `struct` to store bit as a [`BitStore`].");

// Unit Tests
mod tests {
    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use itertools::sorted;

    #[test]
    fn bitstore_new_works() {
        assert_eq!(BStore::new(), BStore { bit_length: 0, bits: vec![] });
    }

    #[test]
    fn bitstore_zero_works() {
        assert_eq!(BStore::zero(9), BStore { bit_length: 9, bits: vec![0u8; 2]});
    }

    #[test]
    fn bitstore_from_bits_works() {
        assert_eq!(BStore::from_indices(vec![2, 4, 8]), BStore::from(vec![false, false, true, false, true, false, false, false, true]));
    }

    #[test]
    fn bitstore_is_empty_works() {
        assert!(BStore::new().is_empty());
        assert!(!BStore::zero(9).is_empty());
        assert!(!BStore { bit_length: 9, bits: vec![0u8, 1u8] }.is_empty());
    }

    #[test]
    fn bitstore_is_zero_works() {
        assert!(BStore::zero(9).is_zero());
        assert!(!BStore::new().is_zero());
        assert_eq!(!BStore { bit_length: 6, bits: vec![0b00010000u8] }.is_zero(), true, "{:b}", BStore { bit_length: 6, bits: vec![0b00010000u8] });
    }

    #[test]
    fn bitstore_from_vecbool_works() {
        assert_eq!(BStore::from(vec![false, false, false, false, false, false, false, true, true]), BStore { bit_length: 9, bits: vec![0b00000001u8, 0b10000000u8]});
    }

    #[test]
    fn bitstore_from_vecint_works() {
        assert_eq!(
            BStore::from(vec![0xff_usize]),
            BStore { bit_length: 64, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BStore::from(vec![0x0_u8, 0xff]),
            BStore { bit_length: 16, bits: vec![0u8, 255] }
        );
        assert_eq!(
            BStore::from(vec![0x0_u16, 0xff]),
            BStore { bit_length: 32, bits: vec![0u8, 0, 0, 255] }
        );
        assert_eq!(
            BStore::from(vec![0x0_u32, 0xff]),
            BStore { bit_length: 64, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BStore::from(vec![0x0_u64, 0xff]),
            BStore { bit_length: 128, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BStore::from(vec![0x0_u128, 0xff]),
            BStore { bit_length: 256, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255] }
        );
    }

    #[test]
    fn bitstore_getrs_setrs_work() {
        let mut bs = BStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        assert_eq!(bs.get_bit_length(), 14);
        assert_eq!(bs.get_capacity(), 16);
        assert!(bs.set_bit_length(15).is_ok());
        assert!(bs.set_bit_length(30).is_err());
        assert_eq!(bs.get_bit_length(), 15);
        assert!(bs.set_capacity(4).is_err());
        assert!(bs.set_bit_length(20).is_err());
        assert!(bs.set_capacity(20).is_ok());
        assert_eq!(bs.get_capacity(), 24);
        assert_eq!(bs.get_bit_length(), 15);

        assert_eq!(BStore::from(vec![0b01010101u8]).get_bits(0..8), Ok(vec![false, true, false, true, false, true, false, true]));
        assert_eq!(bs.get_bits(0..15), Ok(vec![false, false, true, true, false, false, false, true, false, false, true, false, false, true, false]), "for {:?}", bs);
        assert_eq!(bs.get_bit(2), Ok(true));
        assert_eq!(bs.get_bits(2..4), Ok(vec![true, true]));
        assert_eq!(bs.get_bits(6..10), Ok(vec![false, true, false, false]));
        assert!(bs.set_bits(6..10, vec![false, true, true, false]).is_ok());
        assert_eq!(bs.get_bits(6..10), Ok(vec![false, true, true, false]));
        assert!(bs.set_bit(3, false).is_ok());
        assert_eq!(bs.get_bit(3), Ok(false));
        assert!(bs.get_bit(20).is_err());
        assert!(bs.get_bits(10..20).is_err());
    }

    #[test]
    fn bitstore_index_works() {
        let bs = BStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        assert_eq!(bs[0], false);
        assert_eq!(bs[2], true);
        assert_eq!(bs[10], true);
    }

    #[test]
    fn bitstore_count_ones_works() {
        let bs = BStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        assert_eq!(bs.count_ones(), 5);
        assert_eq!(BStore::from(vec![0b01010101u8]).count_ones(), 4, "count_ones for {:?}", BStore::from(vec![0b01010101u8]));
    }

    #[test]
    fn bitstore_normalize_works() {
        let bs1 = BStore::from(vec![0b00110001u8]);
        let bs2 = BStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        let bs_slice = &vec![bs1.clone(), bs2.clone()][..];
        assert_eq!(BStore::normalize(bs_slice), vec![BStore {bit_length: 14, bits: vec![0b00110001u8, 0]}, bs2]);
    }

    #[test]
    fn bitstore_bitnot_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        assert_eq!(!BStore::from(v1.clone()), BStore::from(not_v1.clone()));
        assert_eq!(!BStore { bit_length: 10, bits: v1 }, BStore { bit_length: 10, bits: not_v1 });
    }

    #[test]
    fn bitstore_bitand_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        let bs1 = BStore::from(v1.clone());
        let bs2 = BStore::from(not_v1.clone());
        assert_eq!(bs1.clone() & bs2.clone(), BStore::zero(16));
        assert_eq!(BStore { bit_length: 10, bits: v1} & BStore { bit_length: 10, bits: not_v1}, BStore { bit_length: 10, bits: vec![0u8;2]});
    }

    #[test]
    fn bitstore_bitor_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        let bs1 = BStore::from(v1.clone());
        let bs2 = BStore::from(not_v1.clone());
        assert_eq!(bs1.clone() | bs2.clone(), ! BStore::zero(16));
        assert_eq!(BStore { bit_length: 10, bits: v1} | BStore { bit_length: 10, bits: not_v1}, BStore { bit_length: 10, bits: vec![! 0u8; 2]});
    }

    #[test]
    fn bitstore_bitxor_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let v2 = vec![0b01010101u8, 0b00110001u8];
        let v3 = vec![0b01100100u8, 0b01100100u8];
        let bs1 = BStore::from(v1.clone());
        let bs2 = BStore::from(v2.clone());
        let bs3 = BStore::from(v3.clone());
        assert_eq!(bs1.clone() ^ bs2.clone(), bs3.clone() );
        assert_eq!(BStore { bit_length: 10, bits: v1} ^ BStore { bit_length: 10, bits: v2}, BStore { bit_length: 10, bits: v3});
    }

    #[test]
    fn bitstore_binary_works() {
        assert_eq!(format!("{:b}", BStore::from(vec![0b01010101u8, 0b00110001])), "[01010101, 00110001]".to_string());
        assert_eq!(format!("{:b}", BStore::from(vec![false, true, false, true, false])), "[01010]".to_string());
    }

    #[test]
    fn bitstore_display_works() {
        assert_eq!(format!("{}", BStore::from(vec![0b01010101u8, 0b00110001])), "[01010101, 00110001]".to_string());
        assert_eq!(format!("{}", BStore::from(vec![false, true, false, true, false])), "[01010]".to_string());
    }

}
