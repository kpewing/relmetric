/*! # A Module Representing Dowker Complexes

This module creates an abstraction of the [`Dowker Complex`] and various supporting types and traits, including the [`Abstract Simplicial Complex`], the [`Face`], and the underlying [`BitStore`] trait and default [`BitStore`] struct.
*/

use core::fmt;
use core::ops::{Bound, Range, RangeBounds};
use core::iter::zip;
use std::fmt::Write;

use itertools::Itertools;
// use bit_field::BitField;

// /// A *Dowker Complex* on a [`Relation`].
// ///
// /// For more on *Dowker Complexes*, *see, e.g.*, [Michael Robinson, "Cosheaf representations of relations and Dowker complexes", J Appl. and Comput. Topology 6, 27–63 (2022)](https://doi.org/10.1007/s41468-021-00078-y).
// pub struct MyDowker<'a, R, A> where
//     R: RelationTrait,
//     A: AbstractSimplicialComplex<bool>
// {
//     relation: &'a R,
//     asc: A,
// }

// // /// A generic trait a *Dowker Complex*.
// // ///
// // pub trait Dowker<T> where
// //     T: Face<U>
// // {
// //     type R: RelationTrait;
// //     type A: AbstractSimplicialComplex<T>;
// //     fn new() -> Self;
// //     fn is_empty(&self) -> bool;
// //     fn diff_weight(&self, face: T) -> usize;
// //     fn tot_weight(&self, face: T) -> usize;
// // }


// /// A generic trait for a *Relation*.
// ///
// pub trait RelationTrait {
//     type C;
//     type R;
//     fn new() -> Self;
//     fn is_empty(&self) -> bool;
//     fn zero(row_count: usize, col_count: usize) -> Self;
//     fn get_row_count(&self) -> usize;
//     fn get_col_count(&self) -> usize;
//     fn get_row(&self, idx: usize) -> Self::R;
//     fn get_col(&self, idx: usize) -> Self::C;
//     fn set_row(&mut self, idx: usize, row: Self::R);
//     fn set_col(&mut self, idx: usize, col: Self::C);
//     fn transpose(&self) -> Self;
// }

// /// A generic trait for an *abstract simplicial complex* of generically defined [`Face`]s.
// ///
// /// An [*abstract simplicial complex* (*asc*)](https://en.wikipedia.org/wiki/Abstract_simplicial_complex) is a family of sets called [`Face`]s that is closed under taking subsets; *i.e*, every subset of a [`Face`] in the family is also in the family. Each [`Face`] is a set of *vertices*. The *vertex set* of an [*asc*](AbstractSimplicialComplex) is the union of all the [`Face`]s, *i.e.*, all the *vertices* `T` used in the [*asc*](AbstractSimplicialComplex). The [`size`](AbstractSimplicialComplex::size()) of the [`AbstractSimplicialComplex`] is the largest [`size`](Face::size()) of any [`Face`] in the complex.
// ///
// /// **NB**: We extend the common definition to permit an [*asc*](AbstractSimplicialComplex) to be [`empty`](AbstractSimplicialComplex::is_empty()).
// pub trait AbstractSimplicialComplex where
//     T: Clone + Hash + Eq
// {
//     type F: Face;

//     /// Create a new, empty [`AbstractSimplicialComplex`]
//     fn new() -> Self;

//     /// Create a new [`AbstractSimplicialComplex`] from a [`Vec`] of [`Face`]s of *vertices* `T`, without duplication.
//     ///
//     /// Implementation *required*.
//     fn from(faces: Vec<Self::F>) -> Self;

//     /// Return a [`Vec`] of all the [`Face`]s in this [`AbstractSimplicialComplex`].
//     ///
//     /// Implementation *required*.
//     fn faces(&self) -> Vec<Self::F>;

//     /// Return a [`Vec`] of the *vertices* `T` actually used in this [`AbstractSimplicialComplex`], *i.e.*, its *vertex set*.
//     ///
//     /// **NB**: The *vertex set* might not itself be present in the [`AbstractSimplicialComplex`].
//     ///
//     /// *Optional* implementation: Default is union of vertices in generators().
//     fn vertices(&self) -> Vec<T> {
//         self.generators()
//             .iter()
//             .flat_map(|x| x.vertices())
//             .unique()
//             .collect_vec()
//     }

//     /// Return `true` if this [`AbstractSimplicialComplex`] contains the given [`Face`].
//     ///
//     /// *Optional* implementation. Default: find the given [`Face`] in the [`faces()`].
//     fn contains(&self, face: Self::F) -> bool {
//         match self.faces()
//             .into_iter()
//             .find(|&x| x.eq(face)) {
//                 Some(_) => true,
//                 None => false
//             }
//     }

//     /// Insert the given [`Face`] and return the resulting [`AbstractSimplicialComplex`].
//     ///
//     /// *Optional* implementation. Default: extend this [`AbstractSimplicialComplex`]'s [`Face`]s with the given one without duplication.
//     fn insert(&mut self, face: &Self::F) -> Self {
//         let mut new = self.faces().push(face);
//         new = new.iter().unique().collect_vec();
//         AbstractSimplicialComplex::from()
//     }

//     /// Remove the given [`Face`] and return the resulting [`AbstractSimplicialComplex`].
//     ///
//     /// *Optional* implementation. Default: create a new [`AbstractSimplicialComplex`] without the given [`Face`].
//     fn remove(&mut self, face: Self::F) -> Self {
//         AbstractSimplicialComplex::from(self.faces().filter(|x| x != face))
//     }

//     /// Return the [`size`](Face::size()) of a [`maximal Face`](AbstractSimplicialComplex::is_maximal()) in this [`AbstractSimplicialComplex`].
//     ///
//     /// **NB**: This will *not* equal the count of items in the [*vertex set*](AbstractSimplicialComplex::vertices()) whenever there a multiple [`maximal Faces`](AbstractSimplicialComplex::is_maximal()), since they by definition have different *vertices* from each other.
//     ///
//     /// *Optional* implementation. Default: size of the first generator.
//     fn size(&self) -> usize {
//         self.generators().take(1).size()
//     }

//     /// Return whether the [`AbstractSimplicialComplex`] is empty.
//     ///
//     /// *Optional* implementation. Default: size == 0.
//     fn is_empty(&self) -> bool {
//         self.size() == 0
//     }

//     /// Return `true` if there is no other larger [`Face`] in this [`AbstractSimplicialComplex`].
//     ///
//     /// *Optional* implementation. Default: find it in generators()
//     fn is_maximal(&self, face: Self::F) -> bool {
//         self.generators().find(|x| x == face)
//     }

//     /// Return a [`Vec`] of the [`maximal Faces`](AbstractSimplicialComplex::is_maximal()), the union of whose [`descendants`](Face::descendants()) *generates* this [`AbstractSimplicialComplex`].
//     ///
//     /// *Optional* implementation. Default: use itertools::max_set_by() on size().
//     fn generators(&self) -> Vec<Self::F> {
//         self.max_set_by(|a, b| a.size().cmp(b.size()))
//     }

// }

/// A generic trait for *face*s of an [`AbstractSimplicialComplex`] of *vertices* of the associated type [`Vertex`](Face::Vertex).
///
/// Each *face* has a [`size`](Face::size()) equal to the count of *vertices* in it. This is equal to the more commonly defined *simplex dimension* + 1. **NB**: We thus extend the more common definition to permit a [`Face`] to be [`empty`](Face::is_empty()).
///
pub trait Face {
    type Vertex;

    /// Create a new, empty [`Face`].
    // fn new() -> Self;

    /// Create a new [`Face`] from a [`Vec`] of [`Vertex`](Face::Vertex)s, without duplication.
    fn from_vertices(vertices: Vec<Self::Vertex>) -> Self;

    /// Return a [`Vec`] of the [`Vertex`](Face::Vertex)s actually in use in this [`Face`].
    fn vertices(&self) -> Vec<Self::Vertex>;

    /// Insert the given [`Vertex`](Face::Vertex) and return the resulting [`Face`].
    fn insert(&mut self, vertex: Self::Vertex) -> &mut Self;

    /// Remove the given [`Vertex`](Face::Vertex) and return the resulting [`Face`], without truncating the [`bit_length`](Face::bit_length()) or changing the [`capacity`](Face::capacity()).
    ///
    /// *Optional* implementation. Default: set the bit to `false` if it's in bounds or just return self.
    fn remove(&mut self, vertex: &Self::Vertex) -> &mut Self;

    /// Return `true` if this [`Face`] contains the given [`Vertex`](Face::Vertex).
    ///
    /// *Optional* implementation. Default: `true` if [`vertices()`](Face::vertices()) contains the given *vertex*.
    fn contains(&self, vertex: &Self::Vertex) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.vertices()[..].contains(vertex)
    }

    /// Return the number of *vertices* `T: Into<usize>`in this [`Face`], *i.e.*, its (*simplex*) *dimension* + 1.
    ///
    /// *Optional* implementation. Default: count the vertices.
    fn size(&self) -> usize {
        self.vertices().len()
    }

    /// Return `true` if this [`Face`] is empty, *i.e.*, has [`Face::size()`] == 0.
    ///
    /// *Optional* implementation. Default: size == 0.
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Return `true` if this [`Face`] is [`size`] 1 larger than the given [`Face`] and contains all of the given one's *vertices*.
    ///
    /// *Optional* implementation. Default: this [`Face`] is one larger than the given [`Face`] and an [`ancestor`](is_ancestor-of()) of the given [`Face`].
    fn is_parent_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.size() == face.size() + 1 && self.is_ancestor_of(face)
    }

    /// Return `true` if this [`Face`] is [`size`] 1 smaller than the given [`Face`] and all its *vertices* `usize` are contained by the given one.
    ///
    /// *Optional* implementation. Default flip is_parent_of().
    fn is_child_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        face.is_parent_of(self)
    }

    /// Return a [`Vec`] of all sub-[`Face`]s within this [`Face`] with [`size`](Face::size()) exactly one less than this [`Face`]'s.
    /// Return an [`Iterator`](std::iter::Iterator) of all sub-[`Face`]s within this [`Face`] with [`size`](Face::size()) exactly one less than this [`Face`]'s.
    ///
    /// *Optional* implementation. Default: generate by removing each vertex in this [`Face`] in turn.
    fn children(&self) -> Vec<Self>
    where
        Self: Sized,
        Self::Vertex: Clone,
    {
        let mut res = vec![];
        for vs in self.vertices().into_iter().combinations(self.size() - 1) {
            res.push(Self::from_vertices(vs))
        }
        res
    }

    /// Return `true` if this [`Face`] is smaller than the given one and all its *vertices* `usize` are contained by the given one.
    ///
    /// *Optional* implementation. Default: find the face in descendants.
    fn is_ancestor_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.size() > face.size() && face.vertices().iter().all(|x| self.contains(x))
    }

    /// Return `true` if this [`Face`] contains all the *vertices* `usize` in the given [`Face`].
    ///
    /// *Optional* implementation. Default: flip is_ancestor_of().
    fn is_descendant_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        face.is_ancestor_of(self)
    }

    /// Return a [`Vec`] of all possible subsets of this [`Face`], including the empty [`Face`].
    /// Return an [`Iterator`](std::iter::Iterator) of all possible subsets of this [`Face`], including the empty [`Face`].
    ///
    /// *Optional* implementation. Default: use Itertools::powerset().
    fn descendants(&self) -> Vec<Self>
    where
        Self: Sized,
        Self::Vertex: Clone
    {
        let mut res = vec![];
        for vs in self.vertices().into_iter().powerset() {
            if vs.len() != self.vertices().len() {
                res.push(Self::from_vertices(vs))
            }
        }
        res
    }

}

/// A type for storing bits in a variable-length [`Vec`] of [`bit_field::BitField`]s.
///
/// Maps [`bit_field::BitField`] over a [`Vec`] of [`u8`] in little endian order, while enforcing a maximum `bit_length` for the whole store. Wraps getters and setters in a [`Result<_, &'static str>`] to avoid out-of-bounds panics.
//
// [ ] - TODO: consider implementing [`SliceIndex`](https://doc.rust-lang.org/std/slice/trait.SliceIndex.html)
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitStore {
    /// Count of bits represented.
    bit_length: usize,
    /// Container for the bits being represented.
    bits: Vec<u8>,
}

impl BitStore {

    /// Creates a new, default [`BitStore`], which is [`empty`](is_empty()).
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns a validated [`Range`] into the [`BitStore`] or an "out of bounds" `Err`.
    pub fn valid_range<T: RangeBounds<usize>>(&self, range: T) -> Result<Range<usize>, &'static str> {
        let start = match range.start_bound() {
            Bound::Excluded(&value) => value + 1,
            Bound::Included(&value) => value,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Excluded(&value) => value,
            Bound::Included(&value) => value + 1,
            Bound::Unbounded => self.bit_length,
        };
        println!("valid_range({}..{})", start, end);
        if start <= end && start <= self.bit_length && end <= self.bit_length {
            println!("valid_range => Ok(Range {}, {})", start, end);
            Ok(Range { start, end })
        } else {
            println!("valid_range => Err with start:{} end:{} bit_length:{}", start, end, self.bit_length);
            Err("out of bounds for BitStore")
        }
    }

    /// Returns the [`bit_length`](BitStore::bit_length).
    pub fn get_bit_length(&self) -> usize {
        self.bit_length
    }

    /// Returns the `Ok(<[BitStore](dowker::BitStore)>)` with the given [`bit_length`](BitStore::bit_length) or an "out of bounds" `Err`.
    pub fn set_bit_length(&mut self, value: usize) -> Result<&mut Self, &'static str> {
        print!("set_bit_length {} to {} => ", self.bit_length, value);
        if value == self.bit_length {
            println!("{}", self.bit_length);
            Ok(self)
        } else if value > self.bit_length  && value < self.get_capacity() {
            self.bit_length = value;
            println!("{}", self.bit_length);
            Ok(self)
        } else {
            Err("out of bounds for BitStore")
        }
    }

    /// Returns the `capacity` of the [`BitStore`] in bits, which is the length of [`BitStore.bits`] * 8 (the size of a `u8`).
    pub fn get_capacity(&self) -> usize {
        self.bits.len() * u8::BITS as usize
    }

    /// Returns `Ok(<[BitStore](dowker::BitStore)>)` with the given `capacity`, growing it if needed without increasing the [`bit_length`], or an "out of bounds" `Err`.
    pub fn set_capacity(&mut self, value: usize) -> Result<&mut Self, &'static str> {
        let cap = self.get_capacity();
        print!("set_capacity {} to {}", cap, value);
        if value < self.bit_length {
            Err("can't reduce BitStore capacity below bit_length")
        } else if value > cap {
            self.bits.extend(vec![0u8; 1 + (value - cap) / u8::BITS as usize]);
            println!(" by {} bytes => {}", 1 + (value - cap) / u8::BITS as usize, self.get_capacity());
            Ok(self)
        } else if value < cap {
            println!(" within => {}", self.get_capacity());
            self.bits = self.bits[0..(value / u8::BITS as usize)].to_vec();
            Ok(self)
        } else {
            Ok(self)
        }
    }

    /// Returns the `Ok<bool>` value of the given bit or an "out of bounds" `Err`.
    pub fn get_bit(&self, idx: usize) -> Result<bool, &'static str> {
        self.get_bits(idx..(idx + 1)).map(|x| x[0])
    }

    /// Returns a `Ok<Vec<bool>>` of the given range of bits or an "out of bounds" `Err`.
    pub fn get_bits(&self, range: Range<usize>) -> Result<Vec<bool>, &'static str> {
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
        let the_offset = (self.get_capacity() - self.bit_length) % u8::BITS as usize;
        let f = |x| {
            let the_int = x / u8::BITS as usize;
            let the_bit = x % u8::BITS as usize;
            if self.bits.is_empty() {
                false
            } else if the_int < self.get_bit_length() / u8::BITS as usize {
                self.bits[the_int] & ROW_MASK[the_bit] > 0
            } else {
                self.bits[the_int] & ROW_MASK[the_offset + the_bit] > 0
            }
        };
        Ok(self.valid_range(range)?.map(f).collect())
    }

    // Return `Ok<Self>` with the given bit set to the given `bool` value.
    pub fn set_bit(&mut self, idx: usize, value: bool) -> Result<&mut Self, &'static str> {
        self.set_bits(idx..(idx + 1), vec![value])
    }

    // Return `Ok<Self>` with the given range of bits set to the given `bool` values or an "out of bounds" `Err`.
    pub fn set_bits<T: RangeBounds<usize>>(&mut self, range: T, values: Vec<bool>) -> Result<&mut Self, &'static str> {
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
        let the_offset = self.get_capacity().saturating_sub(self.bit_length) % u8::BITS as usize;
        for (idx, &val) in zip(self.valid_range(range)?, values.iter()) {
            let the_int = idx / u8::BITS as usize;
            let the_bit = idx % u8::BITS as usize;
            if the_int < self.get_bit_length() / u8::BITS as usize {
                if val {
                    self.bits[the_int] |= ROW_MASK[the_bit];
                } else {
                    self.bits[the_int] &= ! (ROW_MASK[the_bit] as u8);
                }
            } else if val {
                self.bits[the_int] |= ROW_MASK[the_offset + the_bit];
            } else {
                self.bits[the_int] &= ! (ROW_MASK[the_offset + the_bit] as u8);
            }
        }
        Ok(self)
    }

    /// Return the count of `true` bits in the [`BitStore`].
    pub fn count_ones(&self) -> usize {
        self.get_bits(0..self.get_bit_length()).unwrap()
            .iter().filter(|&x| *x).count()
    }

}

// [ ] - TODO: use a macro to generate for the various numbers
impl From<Vec<u8>> for BitStore {
    fn from(ints: Vec<u8>) -> Self {
        BitStore {
            bit_length: ints.len() * u8::BITS as usize,
            bits: ints,
        }
    }
}

impl From<Vec<u16>> for BitStore {
    fn from(ints: Vec<u16>) -> Self {
        BitStore {
            bit_length: ints.len() * u16::BITS as usize,
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

impl From<Vec<u32>> for BitStore {
    fn from(ints: Vec<u32>) -> Self {
        BitStore {
            bit_length: ints.len() * u32::BITS as usize,
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

impl From<Vec<u64>> for BitStore {
    fn from(ints: Vec<u64>) -> Self {
        BitStore {
            bit_length: ints.len() * u64::BITS as usize,
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

impl From<Vec<u128>> for BitStore {
    fn from(ints: Vec<u128>) -> Self {
        BitStore {
            bit_length: ints.len() * u128::BITS as usize,
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

impl From<Vec<usize>> for BitStore {
    fn from(ints: Vec<usize>) -> Self {
        BitStore {
            bit_length: ints.len() * usize::BITS as usize,
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

impl fmt::Binary for BitStore {
    /// Show a big-endian binary representation of the [`BitStore`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.bit_length / u8::BITS as usize;
        let rest_bits = self.bit_length % u8::BITS as usize;
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
                .bits
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:08b}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                write!(s, "{:b}", self.bits[whole_ints] & REST_MASK[rest_bits]).unwrap();
            } else {
                write!(
                    s,
                    ", {:b}",
                    self.bits[whole_ints] & REST_MASK[rest_bits]
                )
                .unwrap();
            }
        }
        s.push(']');
        write!(f, "{s}")
    }
}

impl fmt::LowerHex for BitStore {
    /// Show a big-endian lower hexadecimal representation of the [`BitStore`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.bit_length / u8::BITS as usize;
        let rest_bits = self.bit_length % u8::BITS as usize;
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
                .bits
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:02x}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                write!(s, "{:x}", self.bits[whole_ints] & REST_MASK[rest_bits]).unwrap();
            } else {
                write!(
                    s,
                    ", {:x}",
                    self.bits[whole_ints] & REST_MASK[rest_bits]
                )
                .unwrap();
            }
        }
        s.push(']');
        write!(f, "{s}")
    }
}

impl fmt::UpperHex for BitStore {
    /// Show a big-endian upper hexadecimal representation of the [`BitStore`] on one line.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let whole_ints = self.bit_length / u8::BITS as usize;
        let rest_bits = self.bit_length % u8::BITS as usize;
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
                .bits
                .iter()
                .take(whole_ints)
                .map(|x| format!("{:02X}", x))
                .collect::<Vec<String>>()
                .join(", "),
        );
        if rest_bits > 0 {
            if whole_ints == 0 {
                write!(s, "{:X}", self.bits[whole_ints] & REST_MASK[rest_bits]).unwrap();
            } else {
                write!(
                    s,
                    ", {:X}",
                    self.bits[whole_ints] & REST_MASK[rest_bits]
                )
                .unwrap();
            }
        }
        s.push(']');
        write!(f, "{s}")
    }
}


impl Face for BitStore {
    type Vertex = usize;

    // fn new() -> Self {
    //     Default::default()
    // }

    fn from_vertices(vertices: Vec<Self::Vertex>) -> Self {
        println!("from_vertices vertices: {:?}", vertices);
        let max = match vertices.iter().max() {
            None => return Self::new(),
            Some(n) => n
        };
        let mut res = Self::new();
        res.bit_length = *max + 1;
        println!("from_vertices res.bit_length:{}", res.bit_length);
        res.bits = vec![0u8; 1 + *max / u8::BITS as usize];
        println!("from_vertices initial res.bits:{:?}", res.bits);
        for v in vertices {
            res.set_bit(v, true).unwrap();
        }
        println!("from_vertices final res.bits:{:?}", res.bits);
        res
    }

    fn vertices(&self) -> Vec<Self::Vertex> {
        println!("vertices for {:?}", self);
        self.get_bits(0..self.bit_length).unwrap()
            .iter()
            .enumerate()
            .filter_map(|(idx, bit)| if *bit {Some(idx)} else {None})
            .collect::<Vec<Self::Vertex>>()
    }

    fn contains(&self, vertex: &Self::Vertex) -> bool {
        self.get_bit(*vertex).unwrap_or(false)
    }

    fn insert(&mut self, vertex: Self::Vertex) -> &mut Self {
        println!("insert({})", vertex);
        if vertex < self.get_bit_length() {
            // SAFETY: vertex < bit_length => set_bit() can't fail.
            self.set_bit(vertex, true).unwrap()
        } else {
            // SAFETY: vertex > bit_length => set_capacity() can't fail.
            // The set_capacity() call => set_bit_length() can't fail.
            // The set_bit_length() call => set_bit() can't fail.
            if vertex >= self.get_capacity() {
                self.set_capacity(vertex + 1).unwrap();
            }
            println!("insert({}) capacity:{}", vertex, self.get_capacity());
            self.set_bit_length(vertex + 1).unwrap();
            println!("insert({}) capacity:{} bit_length:{}", vertex, self.get_capacity(), self.get_bit_length());
            self.set_bit(vertex, true).unwrap()
        }
    }

    fn remove(&mut self, &vertex: &Self::Vertex) -> &mut Self {
        if vertex < self.get_bit_length() {
            // SAFETY: vertex < bit_length => set_bit() can't fail.
            self.set_bit(vertex, false).unwrap()
        } else {
            self
        }
    }

    // fn is_parent_of(&self, face: &Self) -> bool {
    //     self.size() == face.size() + 1 && self.is_ancestor_of(face)
    // }

    // fn is_child_of(&self, face: &Self) -> bool {
    //     face.is_parent_of(self)
    // }

    // fn children(&self) -> dyn Iterator<Item = Self> {
    //     self.vertices().map(|x| self.clone().remove(x)).collect::<Vec<Self>>()
    // }

}

// Unit Tests
mod tests {
    use super::*;

    #[test]
    fn bitstore_new_works() {
        assert_eq!(BitStore::new(), BitStore { bit_length: 0, bits: vec![] });
    }

    #[test]
    fn bitstore_from_works() {
        assert_eq!(
            BitStore::from(vec![0xff_usize]),
            BitStore { bit_length: 64, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BitStore::from(vec![0x0_u8, 0xff]),
            BitStore { bit_length: 16, bits: vec![0u8, 255] }
        );
        assert_eq!(
            BitStore::from(vec![0x0_u16, 0xff]),
            BitStore { bit_length: 32, bits: vec![0u8, 0, 0, 255] }
        );
        assert_eq!(
            BitStore::from(vec![0x0_u32, 0xff]),
            BitStore { bit_length: 64, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BitStore::from(vec![0x0_u64, 0xff]),
            BitStore { bit_length: 128, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255] }
        );
        assert_eq!(
            BitStore::from(vec![0x0_u128, 0xff]),
            BitStore { bit_length: 256, bits: vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255] }
        );
    }

    #[test]
    fn bitstore_getrs_setrs_work() {
        let mut bs = BitStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
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

        assert_eq!(bs.get_bits(0..15), Ok(vec![false, false, true, true, false, false, false, true, false, true, false, false, true, false, true]), "for {:?}", bs);
        assert_eq!(bs.get_bit(2), Ok(true));
        assert_eq!(bs.get_bits(2..4), Ok(vec![true, true]));
        assert_eq!(bs.get_bits(6..10), Ok(vec![false, true, false, true]));
        assert!(bs.set_bits(6..10, vec![false, true, true, false]).is_ok());
        assert_eq!(bs.get_bits(6..10), Ok(vec![false, true, true, false]));
        assert!(bs.set_bit(3, false).is_ok());
        assert_eq!(bs.get_bit(3), Ok(false));
        assert!(bs.get_bit(20).is_err());
        assert!(bs.get_bits(10..20).is_err());
    }

    #[test]
    fn bitstore_count_ones_works() {
        let bs = BitStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        assert_eq!(bs.count_ones(), 6);
    }

    #[test]
    fn face_bitstore_from_vertices_works() {
        assert_eq!(BitStore::from_vertices(vec![2, 4, 8]), BitStore {bit_length: 9, bits: vec![0b00101000, 0b00000001u8]});
        assert_eq!(BitStore::from_vertices(vec![]), BitStore {bit_length: 0, bits: vec![]});
    }

    #[test]
    fn face_bitstore_vertices_works() {
        assert_eq!(BitStore::from_vertices(vec![2, 4, 8]).vertices(), vec![2, 4, 8]);
        assert_eq!(BitStore::from_vertices(vec![]).vertices(), vec![]);
    }

    #[test]
    fn face_bitstore_contains_works() {
        let bs = BitStore::from_vertices(vec![2, 4, 8]);
        assert!(bs.contains(&4));
        assert!(!bs.contains(&1));
        assert!(!bs.contains(&12));
        assert!(!bs.contains(&30));
    }

    #[test]
    fn face_bitstore_insert_works() {
        let mut bs = BitStore::from_vertices(vec![2, 4, 8]);
        assert!(bs.insert(1).contains(&1));
        assert!(bs.insert(10).contains(&10));
    }

    #[test]
    fn face_bitstore_remove_works() {
        let mut bs = BitStore::from_vertices(vec![2, 4, 8]);
        assert!(!bs.remove(&1).contains(&1));
        assert!(!bs.remove(&2).contains(&2));
        assert!(!bs.remove(&10).contains(&10));
    }

    #[test]
    fn face_bitstore_size_works() {
        assert_eq!(BitStore::new().size(), 0);
        assert_eq!(BitStore::from_vertices(vec![2, 4, 8]).size(), 3);
    }

    #[test]
    fn face_bitstore_is_empty_works() {
        assert!(BitStore::new().is_empty());
        assert!(!BitStore::from_vertices(vec![2, 4, 8]).is_empty());
    }

    #[test]
    fn face_bitstore_is_parent_of_works() {
        let bs0 = BitStore::new();
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![4]);
        assert!(!bs1.is_parent_of(&bs1));
        assert!(!bs2.is_parent_of(&bs1));
        assert!(bs1.is_parent_of(&bs2));
        assert!(!bs0.is_parent_of(&bs1));
        assert!(bs3.is_parent_of(&bs0));
    }

    #[test]
    fn face_bitstore_is_child_of_works() {
        let bs0 = BitStore::new();
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![4]);
        assert!(!bs1.is_child_of(&bs1));
        assert!(bs2.is_child_of(&bs1));
        assert!(!bs1.is_child_of(&bs2));
        assert!(!bs0.is_child_of(&bs1));
        assert!(bs0.is_child_of(&bs3));
    }

    #[test]
    fn face_bitstore_children_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let res = bs1.children();
        assert_eq!(res.len(), 3);
        assert_eq!(res[0].size(), 2);
        for x in bs1.children() {
            assert!(x.is_child_of(&bs1))
        }
    }

    #[test]
    fn face_bitstore_is_ancestor_of_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        assert!(bs1.is_ancestor_of(&bs2));
        assert!(!bs2.is_ancestor_of(&bs1));
    }

    #[test]
    fn face_bitstore_is_descendant_of_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        assert!(!bs1.is_descendant_of(&bs2));
        assert!(bs2.is_descendant_of(&bs1));
    }

    #[test]
    fn face_bitstore_descendants_works() {
        let bs0 = BitStore::from_vertices(vec![]);
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let bs4 = BitStore::from_vertices(vec![2, 4]);
        let bs5 = BitStore::from_vertices(vec![2]);
        let bs6 = BitStore::from_vertices(vec![4]);
        let bs7 = BitStore::from_vertices(vec![8]);
        let mut res = bs1.descendants();
        res.sort();
        let mut want = [bs0, bs2, bs3, bs4, bs5, bs6, bs7];
        want.sort();
        assert_eq!(res, want);
    }

}
