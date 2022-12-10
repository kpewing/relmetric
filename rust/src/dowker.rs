/*! # A Module Representing Dowker Complexes

This module creates an abstraction of the [`Dowker Complex`] and various supporting types and traits, including the [`Abstract Simplicial Complex`](AbstractSimplicialComplex), the [`Face`], and the underlying [`BitStore`] trait and default [`BitStore`] struct.
*/

use core::fmt;
use core::ops::{Bound, Range, RangeBounds};
use core::iter::zip;
use core::hash::Hash;
use std::collections::BTreeMap;
use std::fmt::{Write, Debug};
use std::ops::{Not, BitAnd, BitOr, BitXor};

use itertools::Itertools;


/// A `struct` to implement *Dowker Complexes*.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct MyDowker {
    /// The *Dowker Complex*'s generators.
    generators: ASC,
    /// The [*differential weights*](MyDowker::diff_weight()) of [`Face`]s in the *Dowker Complex*.
    weights: BTreeMap<BitStore, usize>,
}

impl MyDowker {
    /// Create a new, empty [`MyDowker`].
    pub fn new() -> Self {
        Default::default()
    }
}

/// Create a [`MyDowker`] from a [`BRel`].
impl From<&BRel> for MyDowker
where
    BRel: RelationTrait,
{
    fn from(relation: &BRel) -> Self {
        let mut res = MyDowker::new();
        for f in &relation.contents {
            println!("MyDowker::from<BRel> f:{:b} = {:b}", f, f);
            res.generators.insert_face(f.clone());
            res.weights.entry(f.clone())
                .and_modify(|diff_weight| *diff_weight += 1)
                .or_insert(1);
        }
        res
    }
}

impl Dowker for MyDowker {
    type A = ASC;
    type F = BitStore;

    fn is_empty(&self) -> bool {
        self.generators.is_empty()
    }

    fn diff_weight(&self, face: &Self::F) -> usize {
        *self.weights.get(face).unwrap_or(&0)
    }

    fn tot_weight(&self, face: &Self::F) -> usize {
        Face::closure(&vec![face.clone()][..]).iter().fold(
            0,
            |mut acc, x| {
                acc += self.weights.get(x).unwrap_or(&0);
                acc
            }
        )
    }

}

/// A `trait` for a *Dowker Complex*.
///
/// A *Dowker Complex* represents the rows or columns of a *binary relation* as [`Face`]s of an [*abstract simplicial complex*](AbstractSimplicialComplex) and assigns a [*differential weight*](Dowker::diff_weight()) and a [*total weight*](Dowker::tot_weight()) to each such [`Face`].
///
/// For more on *Dowker Complexes*, *see, e.g.*, [Michael Robinson, "Cosheaf representations of relations and Dowker complexes", J Appl. and Comput. Topology 6, 27–63 (2022)](https://doi.org/10.1007/s41468-021-00078-y).
pub trait Dowker {
    type A: AbstractSimplicialComplex;
    type F: Face;

    /// Returns `true` if this [`Dowker`] is empty, *i.e.*, has no [`Face`]s in it.
    fn is_empty(&self) -> bool;

    /// Returns the *differential weight* of the given [`Face`] within the [`MyDowker`], *i.e.*, the number of times that [`Face`] appears within the *Dowker Complex*'s *relation*.
    fn diff_weight(&self, face: &Self::F) -> usize;

    /// Returns the *total weight* of the given [`Face`] within the [`MyDowker`], *i.e.*, the sum of [`diff_weight()`](Dowker::diff_weight())s of all [`Face`]s within the given [`Face`] that appear within the *Dowker Complex*'s *relation*.
    fn tot_weight(&self, face: &Self::F) -> usize;
}

/// An `enum` of the two axes of a *binary relation*.
#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub enum Axis {
    Column,
    #[default] Row,
}

/// A `struct` to implement *binary relation*s as a bit field.
#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct BRel {
    /// The [`Axis`] of the *binary relation* whose elements are stored consecutively (default: [`Row`](Axis::Row)).
    major_axis: Axis,
    /// The bit field.
    contents: Vec<BitStore>
}

/// A `trait` for *binary relation*s.
impl BRel {
    /// Create a new, empty [`BRel`] with default [`major_axis`](BRel)
    pub fn new() -> Self {
        Default::default()
    }

    /// Return the `major_axis`.
    pub fn get_major_axis(&self) -> Axis {
        self.major_axis
    }

    /// Set the `major_axis` to the given [`Axis`].
    pub fn set_major_axis(&mut self, &axis: &Axis) -> &mut Self {
        self.major_axis = axis;
        self
    }

    /// Return the `contents`.
    pub fn get_contents(&self) -> Vec<BitStore> {
        self.contents.clone()
    }

    /// Set the `major_axis` to the given [`Axis`].
    pub fn set_contents(&mut self, contents: &Vec<BitStore>) -> &mut Self {
        self.contents = contents.clone();
        self
    }

}

impl RelationTrait for BRel {
    type MajorAxis = Axis;

    fn new() -> Self {
        Self::new()
    }

    fn is_empty(&self) -> bool {
        self.contents.iter().all(|x| x.count_ones() == 0)
    }

    fn zero(row_count: usize, col_count: usize, major_axis: Axis) -> Self {
        let (vec_length, bit_length) = match major_axis {
            Axis::Row => (row_count, col_count),
            Axis::Column => (col_count, row_count),
        };
        BRel {
            major_axis,
            contents: vec![BitStore::zero(bit_length); vec_length],
        }
    }

    fn get_row_count(&self) -> usize {
        match self.major_axis {
            Axis::Row => self.contents.len(),
            Axis::Column =>
                if self.contents.is_empty() {
                    0
                } else {
                    self.contents[0].get_bit_length()
                },
        }
    }

    fn get_col_count(&self) -> usize {
        match self.major_axis {
            Axis::Column => self.contents.len(),
            Axis::Row =>
                if self.contents.is_empty() {
                    0
                } else {
                    self.contents[0].get_bit_length()
                },
        }
    }

    fn get_row(&self, idx: usize) -> Result<Vec<bool>, &'static str> {
        match self.major_axis {
            Axis::Column => {
                let mut bits = vec![];
                for c in self.contents[..].iter() {
                        bits.push(c.get_bit(idx)?)
                    }
                Ok(bits)
                },
            Axis::Row => Ok(self.contents[idx].get_bits(0..self.contents[idx].get_bit_length())?),
        }
    }

    fn get_col(&self, idx: usize) -> Result<Vec<bool>, &'static str> {
        match self.major_axis {
            Axis::Column => Ok(self.contents[idx].get_bits(0..self.contents[idx].get_bit_length())?),
            Axis::Row => {
                let mut bits = vec![];
                for c in self.contents[..].iter() {
                        bits.push(c.get_bit(idx)?)
                    }
                Ok(bits)
                },
        }
    }

    fn set_row(&mut self, idx: usize, row: Vec<bool>) -> Result<&mut Self, &'static str> {
        match self.major_axis {
            Axis::Column => {
                for (i, &v) in row.iter().enumerate() {
                    self.contents[i].set_bit(idx, v)?;
                }
                Ok(self)
            },
            Axis::Row => {
                self.contents[idx] = BitStore::from(row);
                BitStore::normalize(&self.contents);
                Ok(self)
            },
        }
    }

    fn set_col(&mut self, idx: usize, col: Vec<bool>) -> Result<&mut Self, &'static str> {
        match self.major_axis {
            Axis::Column => {
                self.contents[idx] = BitStore::from(col);
                BitStore::normalize(&self.contents);
                Ok(self)
            },
            Axis::Row => {
                for (i, &v) in col.iter().enumerate() {
                    self.contents[i].set_bit(idx, v)?;
                }
                Ok(self)
            },
        }
    }

    // DOESN'T WORK
    // fn transpose(&mut self) -> Result<&mut Self, &'static str> {
    //     println!("\ntranspose self:\n{:b}\n", self);
    //     let mut new = Self::zero(self.get_col_count(), self.get_row_count(), self.major_axis);
    //     match self.major_axis {
    //         Axis::Row => for r in 0..self.get_row_count() {
    //             new.set_col(r, self.get_row(self.get_row_count() - r - 1)?)?;
    //         }
    //         Axis::Column => for c in 0..self.get_col_count() {
    //             new.set_row(c, self.get_col(self.get_col_count() - c - 1)?)?;
    //         }
    //     };
    //     *self = new;
    //     println!("\n ->\n{:b}\n", self);
    //     Ok(self)
    // }
}

impl From<Vec<BitStore>> for BRel {
    fn from(bitstores: Vec<BitStore>) -> Self {
        BRel {
            major_axis: BRel::default().major_axis,
            contents: BitStore::normalize(&bitstores) }
    }
}

impl fmt::Binary for BRel {
    /// Display the [`BRel`] line-by-line, as big-endian binary of the `major_axis`, *i.e.* row-by-row for [column-major-axis](Axis::Column) and column-by-column for [column-major-axis](Axis::Column).
    ///
    /// **NB**: For [column-major-axis](Axis::Column), the result appears rotated by 90&deg; compared to the standard binary representation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::from("[");
        if !self.is_empty() {
            match self.major_axis {
                Axis::Column => {
                    write!(s, "{:b}", BitStore::from(self.get_col(0).unwrap())).unwrap();
                    for c in 1..self.get_col_count() {
                        write!(s, "\n {:b}", BitStore::from(self.get_col(c).unwrap())).unwrap();
                    }
                },
                Axis::Row => {
                    write!(s, "{:b}", self.contents[0]).unwrap();
                    for r in 1..self.get_row_count() {
                        write!(s, "\n {:b}", self.contents[r]).unwrap();
                    }
                }
            };
        }
        s.push(']');
        write!(f, "{s}")
    }
}

/// A trait for a *binary relation*.
pub trait RelationTrait {
    type MajorAxis;
    fn new() -> Self;
    fn is_empty(&self) -> bool;
    fn zero(row_count: usize, col_count: usize, major_axis: Axis) -> Self;
    fn get_row_count(&self) -> usize;
    fn get_col_count(&self) -> usize;
    fn get_row(&self, idx: usize) -> Result<Vec<bool>, &'static str>;
    fn set_row(&mut self, idx: usize, row: Vec<bool>) -> Result<&mut Self, &'static str>;
    fn get_col(&self, idx: usize) -> Result<Vec<bool>, &'static str>;
    fn set_col(&mut self, idx: usize, col: Vec<bool>) -> Result<&mut Self, &'static str>;
}

/// A `struct` to implement an [*abstract simplicial complex*](AbstractSimplicialComplex) on a *vertex set* of `usize`s.
///
/// Just wraps the [*generators*](AbstractSimplicialComplex::generators()).
#[derive(Default, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ASC(Vec<BitStore>);

impl ASC {
    pub fn new() -> Self
    {
        Default::default()
    }
}

impl AbstractSimplicialComplex for ASC {
    type Face = BitStore;

    fn generators(&self) -> Vec<Self::Face> {
        self.0.to_vec()
    }

    fn insert_face (&mut self, face: Self::Face) -> &mut Self {
        // println!("insert_face self:{:?} face:{:b} contains:{}", self, face, self.contains(&face));
        if self.contains(&face) {
            self
        } else {
            self.0.push(face);
            self.0 = BitStore::normalize(&self.0);
            self
        }
    }

    fn remove_face (&mut self, face: Self::Face) -> &mut Self {
        for idx in 0..self.0.len() {
            if self.0[idx].is_ancestor_of(&face) {
                for v in self.0[idx].vertices() {
                    self.0[idx].set_bit(v, false).unwrap();
                }
            }
        }
        self
    }
}

impl From<Vec<BitStore>> for ASC {
    fn from(faces: Vec<BitStore>) -> Self {
        ASC(Face::maximals(&BitStore::normalize(&faces)))
    }
}

/// A generic trait for an *abstract simplicial complex* of its associated type [`Face`](AbstractSimplicialComplex::Face)s.
///
/// An [*abstract simplicial complex* (*asc*)](https://en.wikipedia.org/wiki/Abstract_simplicial_complex) is a collection of sets called [`Face`]s that is closed under taking subsets; *i.e*, every subset of a [`Face`] in the collection is also in the collection. Each [`Face`] is a set of *vertices*. The *vertex set* of an [*asc*](AbstractSimplicialComplex) is the union of all the [`Face`]s, *i.e.*, all the *vertices* used in the [*asc*](AbstractSimplicialComplex). The [`size`](AbstractSimplicialComplex::size()) of an [`AbstractSimplicialComplex`] is the largest [`size`](Face::size()) of any [`Face`] in the complex. The [`generators`](AbstractSimplicialComplex::generators()) of an [`AbstractSimplicialComplex`] are a collection of [`maximal`](AbstractSimplicialComplex::is_maximal()) [`Face`]s within the complex, the union of the [`closure`s](Face::closure()) of which equals the [`AbstractSimplicialComplex`], *i.e.*, one can "generate" the complex by collecting the [`generators`](AbstractSimplicialComplex::generators()) and all of their [`descendants`](Face::descendants()), without duplication.
///
/// **NB**: The common definition is extended to permit an [*asc*](AbstractSimplicialComplex) to be [`empty`].(AbstractSimplicialComplex::is_empty()).
pub trait AbstractSimplicialComplex {
    type Face;

    // /// Create a new, empty [`AbstractSimplicialComplex`].
    // fn new() -> Self where Self: Sized;

    /// Return a [`Vec`] of [`maximal Faces`](AbstractSimplicialComplex::is_maximal()), the union of whose [`descendants`](Face::descendants()) *generates* this [`AbstractSimplicialComplex`].
    fn generators(&self) -> Vec<Self::Face>;

    /// Insert the given [`Face`](AbstractSimplicialComplex::Face) and return the resulting [`AbstractSimplicialComplex`].
    fn insert_face(&mut self, face: Self::Face) -> &mut Self;

    /// Remove the given [`Face`] and return the resulting [`AbstractSimplicialComplex`].
    fn remove_face(&mut self, face: Self::Face) -> &mut Self;

    /// Return a [`Vec`] of all the [`Face`](AbstractSimplicialComplex::Face) s in this [`AbstractSimplicialComplex`].
    ///
    /// # Default Implementation
    /// - Take the [`closure()`](Face::closure()) of the [`generators()`](AbstractSimplicialComplex::generators()).
    /// - Requires the associated type `Face` to have traits `Face + Clone + Hash + Eq` and its associated type `Face::Vertex` to have trait `Clone`.
    fn faces(&self) -> Vec<<Self as AbstractSimplicialComplex>::Face>
    where
        Self::Face: Face + Clone + Hash + Eq,
        <<Self as AbstractSimplicialComplex>::Face as Face>::Vertex: Clone,
    {
        Face::closure(&self.generators())
    }

    /// Return a [`Vec`] of the [`Vertex`](Face::Vertex)s actually used in this [`AbstractSimplicialComplex`], *i.e.*, its *vertex set*.
    ///
    /// **NB**: The *vertex set* might not itself be present in the [`AbstractSimplicialComplex`].
    ///
    /// # Default Implementation
    /// - Collects the unique [`Vertex`](Face::Vertex)s of the [`generators()`](AbstractSimplicialComplex::generators()`].
    /// - Requires the associated type `Face` to have trait `Face` and its associated type `Face::Vertex` to have traits `Hash + Eq + Clone`.
    fn vertices(&self) -> Vec<<<Self as AbstractSimplicialComplex>::Face as Face>::Vertex>
    where
        Self::Face: Face,
        <<Self as AbstractSimplicialComplex>::Face as Face>::Vertex: Hash + Eq + Clone,
    {
        self.generators()
            .iter()
            .flat_map(
                |x|
                x.vertices())
            .unique()
            .collect_vec()
    }

    /// Return `true` if this [`AbstractSimplicialComplex`] contains the given [`Face`].
    ///
    /// # Default Implementation
    /// - Find the given [`Face`](AbstractSimplicialComplex::Face) in the [`faces()`](AbstractSimplicialComplex::faces()).
    /// - Requires the associated types `Face` to have trait `Face + Clone + Hash + Eq` and `Face::Vertex` to have traits `Clone + PartialEq`.
    fn contains(&self, face: &Self::Face) -> bool
    where
        Self::Face: Face + Clone + Hash + Eq,
        <Self::Face as Face>::Vertex: Clone + PartialEq,
    {
        self.generators().iter().any(|x| {
            x == face || x.is_ancestor_of(face)
        })
    }

    /// Return the [`size`](Face::size()) of a [`maximal Face`](AbstractSimplicialComplex::is_maximal()) in this [`AbstractSimplicialComplex`].
    ///
    /// **NB**: This will *not* equal the count of items in the [*vertex set*](AbstractSimplicialComplex::vertices()) whenever there are multiple [`maximal Faces`](AbstractSimplicialComplex::is_maximal()), since they by definition have different [`Vertex`](Face::Vertex)s from each other.
    ///
    /// # Default Implementation
    /// - Return the [`size()`](Face::size()) of the first [`generator`](AbstractSimplicialComplex::generators()).
    /// - Requires the associated type `Face` to have trait `Face`.
    fn size(&self) -> usize
    where
        Self::Face: Face
    {
        self.generators().iter().map(|x| x.size()).max().unwrap_or(0)
    }

    /// Return whether the [`AbstractSimplicialComplex`] is empty.
    ///
    /// # Default Implementation
    /// - Whether `self.size() == 0`.
    /// - Requires the associated type `Face` to have trait `Face`.
    fn is_empty(&self) -> bool
    where
        // <Self as AbstractSimplicialComplex>::Face: Face
        Self::Face: Face
    {
        self.size() == 0
    }

    /// Return `true` if there is no other larger [`Face`] in this [`AbstractSimplicialComplex`].
    ///
    /// # Default Implementation
    /// - Find it in `generators()`.
    /// - Requires the associated type `Face` to have traits `Face + PartialEq`.
    fn is_maximal(&self, face: &Self::Face) -> bool
    where
        Self::Face: Face + PartialEq,
    {
        self.generators().iter().any(|x| x == face)
    }

}

/// A generic trait for *face*s of an [`AbstractSimplicialComplex`] of *vertices* of the associated type [`Vertex`](Face::Vertex).
///
/// Each *face* has a [`size`](Face::size()) equal to the count of *vertices* in it. This is equal to the more commonly defined *simplex dimension* + 1. **NB**: The more common definition is extended to permit a [`Face`] to be [`empty`](Face::is_empty()).
///
pub trait Face {
    type Vertex;

    /// Create a new, empty [`Face`].
    fn new() -> Self;

    /// Create a new [`Face`] from a [`Vec`] of [`Vertex`](Face::Vertex)s, without duplication.
    fn from_vertices(vertices: Vec<Self::Vertex>) -> Self;

    /// Return a [`Vec`] of the [`Vertex`](Face::Vertex)s actually in use in this [`Face`].
    fn vertices(&self) -> Vec<Self::Vertex>;

    /// Insert the given [`Vertex`](Face::Vertex) and return the resulting [`Face`].
    fn insert(&mut self, vertex: Self::Vertex) -> &mut Self;

    /// Remove the given [`Vertex`](Face::Vertex) and return the resulting [`Face`].
    fn remove(&mut self, vertex: &Self::Vertex) -> &mut Self;

    /// Return `true` if this [`Face`] contains the given [`Vertex`](Face::Vertex).
    ///
    /// # Default Implementation
    /// - Whether [`vertices()`](Face::vertices()) contains the given *vertex*.
    /// - Requires `Self::Vertex` to have trait `PartialEq`.
    fn contains(&self, vertex: &Self::Vertex) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.vertices()[..].contains(vertex)
    }

    /// Return the number of *vertices* in this [`Face`], *i.e.*, its *simplex dimension* + 1.
    ///
    /// # Default Implementation
    /// - Count the vertices.
    fn size(&self) -> usize {
        self.vertices().len()
    }

    /// Return `true` if this [`Face`] is empty, *i.e.*, has [`Face::size()`] == 0.
    ///
    /// # Default Implementation
    /// - Whether the size is 0.
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Return `true` unless this and the given [`Face`] share a *vertex*.
    ///
    /// **NB**: Unlike the `lua` version, [`empty`](Face::is_empty()) and [`zero`](Face::is_zero()) [`Face`]s are *not* disjoint from each other and *are* disjoint from non-[`empty`](Face::is_empty()) and non-[`zero`](Face::is_zero()) ones. Finding empties disjoint from everything doesn't make sense.
    ///
    /// # Default Implementation
    /// - Whether both are `is_empty()` or the given [`Face`] `contains()` any *vertex* of this one.
    /// - Requires associated type `Vertex` to have trait `PartialEq`.
    fn is_disjoint(&self, other: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        if self.is_empty() && other.is_empty() {
            false
        } else if self.is_empty() || other.is_empty() {
            true
        } else {
            ! self.vertices().iter().any(|x| other.contains(x))
        }
    }

    /// Return `true` if this [`Face`] has [`size()`](Face::size()) 1 larger than the given [`Face`] and contains all of the given one's *vertices*.
    ///
    /// # Default Implementation
    /// - Whether this [`Face`] is one larger than the given [`Face`] and an [`ancestor`](is_ancestor-of()) of the given [`Face`].
    /// - Requires associated type `Vertex` to have trait `PartialEq`.
    fn is_parent_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.size() == face.size() + 1 && self.is_ancestor_of(face)
    }

    /// Return `true` if this [`Face`] is [`size`] 1 smaller than the given [`Face`] and all its *vertices* are contained in the given one.
    ///
    /// # Default Implementation
    /// - Flip [`is_parent_of()`](Face::is_parent_of()).
    /// - Requires associated type `Vertex` to have trait `PartialEq`.
    fn is_child_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        face.is_parent_of(self)
    }

    /// Return a [`Vec`] of all sub-[`Face`]s within this [`Face`] with [`size`](Face::size()) exactly one less than this [`Face`]'s.
    ///
    /// # Default Implementation
    /// - Use [itertools::Itertools::combinations()].
    /// - Requires `Self` to have trait `Sized` and associated type `Vertex` to have trait `Clone`.
    /// - Panics if the capacity of the new [`Vec`] would exceed `isize::MAX` bytes.
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

    /// Return `true` if this [`Face`] is smaller than the given one and all its *vertices* are contained by the given one.
    ///
    /// # Default Implementation
    /// - Requires associated type `Vertex` to have trait `PartialEq`.
    fn is_ancestor_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.size() > face.size() && face.vertices().iter().all(|x| self.contains(x))
    }

    /// Return `true` if this [`Face`] contains all the *vertices* in the given [`Face`].
    ///
    /// # Default Implementation
    /// - Flip [`is_ancestor_of()`](Face::is_ancestor_of()).
    /// - Requires associated type `Vertex` to have trait `PartialEq`.
    fn is_descendant_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        face.is_ancestor_of(self)
    }

    /// Return a [`Vec`] of all possible subsets of this [`Face`], including the empty [`Face`].
    ///
    /// # Default Implementation
    /// - Use [`itertools::Itertools::powerset()`].
    /// - Requires `Self` to have trait `Sized` and associated type `Vertex` to have trait `Clone`.
    /// - Panics if the capacity of the new [`Vec`] would exceed `isize::MAX` bytes.
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

    /// Return the subset of the given [`Vec`] of [`Face`]s that are not descendants of any other [`Face`]s in the given [`Vec`] of [`Face`]s.
    ///
    /// # Default Implementation
    /// - Requires `Self` to have traits `Sized + Clone` and associated type `Vertex` to have trait `PartialEq`.
    /// - Panics if the capacity of the new [`Vec`] would exceed `isize::MAX` bytes.
    fn maximals(faces: &[Self]) -> Vec<Self>
    where
        Self: Sized + Clone,
        Self::Vertex: PartialEq,
    {
        let mut res = vec![];
        let mut input = faces.to_vec();
        input.sort_by_key(|a| a.size());
        for f in input.iter().rev() {
            if !res.iter().any(|g| (*f).is_descendant_of(g)) {
                res.push((*f).clone())
            }
        }
        res
    }

    /// Return the given [`Face`]s and all their [`descendant`](Face::descendants())s.
    ///
    /// Compare [*closure*](https://en.wikipedia.org/wiki/Simplicial_complex#Closure,_star,_and_link).
    ///
    /// # Default Implementation
    /// - Apply [`unique()`](itertools::Itertools::unique()) to all[`descendants()`](Face::descendants()).
    /// - Requires `Self` to have trait `Sized + Clone + Hash + Eq` and associated type `Vertex` to have trait `Clone`.
    fn closure(faces: &[Self]) -> Vec<Self>
    where
        Self: Sized + Clone + Hash + Eq,
        Self::Vertex: Clone,
    {
        let mut res = vec![];
        res.extend_from_slice(faces);
        for f in faces.iter() {
            res.append(f.descendants().as_mut())
        }
        res.into_iter().unique().collect()
    }

}

/// A type for storing bits in a variable-length [`Vec`] of [`u8`]s.
///
/// Maps [`bit_field::BitField`] over a [`Vec`] of [`u8`] in little endian order, while enforcing a maximum `bit_length` for the whole store. Wraps getters and setters in a [`Result<_, &'static str>`] to manage out-of-bounds errors.
//
// [ ] - TODO: consider implementing [`SliceIndex`](https://doc.rust-lang.org/std/slice/trait.SliceIndex.html) to access bits
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitStore {
    /// Count of bits represented.
    bit_length: usize,
    /// Container for the bits being represented.
    bits: Vec<u8>,
}

impl BitStore {

    /// Create a new, default [`BitStore`], which is [`empty`](is_empty()).
    pub fn new() -> Self {
        Default::default()
    }

    /// Create a [`BitStore`] of given `bit_length` with bits all `false` (*i.e.*, "zero").
    pub fn zero(bit_length: usize) -> Self {
        if bit_length == 0 {
            BitStore {
                bit_length,
                bits: vec![]
            }
        } else if bit_length % u8::BITS as usize > 0 {
            BitStore {
                bit_length,
                bits: vec![0u8; 1 + bit_length / u8::BITS as usize]
            }
        } else {
            BitStore {
                bit_length,
                bits: vec![0u8; bit_length / u8::BITS as usize]
            }
        }
    }

    /// Return `true` if the [`BitStore`] is empty, *i.e.*, the `bit_length` == 0.
    pub fn is_empty(&self) -> bool {
        self.bit_length == 0
    }

    /// Return `true` if the [`BitStore`] is zero, *i.e.*, the `bit_length` > 0 and all `bits` are `false`.
    pub fn is_zero(&self) -> bool {
        self.bit_length > 0 && self.count_ones() == 0
    }

    /// Return a validated [`Range`] into the [`BitStore`] or an "out of bounds" `Err`.
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
        if start <= end && start <= self.bit_length && end <= self.bit_length {
            Ok(Range { start, end })
        } else {
            Err("out of bounds for BitStore")
        }
    }

    /// Return the [`bit_length`](BitStore::bit_length).
    ///
    /// This is the number of bits that *are* represented by the `BitStore`, which may be less than its [`capacity()`](BitStore::capacity()).
    pub fn get_bit_length(&self) -> usize {
        self.bit_length
    }

    /// Return the [`BitStore`] with the given [`bit_length`](BitStore::bit_length) or an "out of bounds" `Err`.
    ///
    /// The `bit_length` **must not** exceed the [`capacity`](BitStore::get_capacity()). To avoid possible `Err`, first use [`set_capacity()](BitStore::set_capacity()).
    ///
    /// # Example
    ///
    /// use relmetric::*;
    ///
    /// let mut bs = BitStore { bit_length: 5, bits: vec![0u8]};
    /// assert!(bs.set_bit_length(10).is_err());
    /// bs.set_capacity(10);
    /// assert!(bs.set_bit_length(10).is_ok());
    ///
    pub fn set_bit_length(&mut self, value: usize) -> Result<&mut Self, &'static str> {
        if value == self.bit_length {
            Ok(self)
        } else if value > self.bit_length && value <= self.get_capacity() {
            self.bit_length = value;
            Ok(self)
        } else {
            Err("out of bounds for BitStore")
        }
    }

    /// Return the *capacity* of the [`BitStore`] in bits, which is the number of bits that *can* be represented.
    pub fn get_capacity(&self) -> usize {
        self.bits.len() * u8::BITS as usize
    }

    /// Return the `BitStore` with the given `capacity`, growing it if needed without increasing the [`bit_length`](BitStore::get_bit_length()), or an "out of bounds" `Err`.
    ///
    ///  This **must** equal or exceed the [`bit_length`](BitStore::get_bit_length()). To avoid possible `Err`, before increasing the `bit_length`, first use [`set_capacity()](BitStore::set_capacity()).
    ///
    ///  See *Example* at [`set_bit_length()`](BitStore::set_bit_length()).
    pub fn set_capacity(&mut self, value: usize) -> Result<&mut Self, &'static str> {
        let cap = self.get_capacity();
        if value < self.bit_length {
            Err("can't reduce BitStore capacity below bit_length")
        } else if value > cap {
            self.bits.extend(vec![0u8; 1 + (value - cap) / u8::BITS as usize]);
            Ok(self)
        } else if value < cap {
            self.bits = self.bits[0..(1 + value / u8::BITS as usize)].to_vec();
            Ok(self)
        } else {
            Ok(self)
        }
    }

    /// Return the `bool` value of the given bit, or an "out of bounds" `Err`.
    pub fn get_bit(&self, idx: usize) -> Result<bool, &'static str> {
        self.get_bits(idx..(idx + 1)).map(|x| x[0])
    }

    /// Return a `Vec` of `bool` values of the given range of bits, or an "out of bounds" `Err`.
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

    // Return the `BitStore` with the given bit set to the given `bool` value, or an "out of bounds" `Err`.
    pub fn set_bit(&mut self, idx: usize, value: bool) -> Result<&mut Self, &'static str> {
        self.set_bits(idx..(idx + 1), vec![value])
    }

    // Return the `BitStore` with the given range of bits set to the given `bool` values, or an "out of bounds" `Err`.
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
        for (idx, &val) in zip(self.valid_range(range)?, values.iter()) {
            let the_int = idx / u8::BITS as usize;
            let the_bit = idx % u8::BITS as usize;
            print!("set_bits cap:{} bit_len:{} int:{} bit:{} self:{:b}", self.get_capacity(), self.get_bit_length(), the_int, the_bit, self);
            if val {
                self.bits[the_int] |= ROW_MASK[the_bit];
            } else {
                self.bits[the_int] &= ! (ROW_MASK[the_bit] as u8);
            }
            println!("->{:b}", self);
        }
        Ok(self)
    }

    /// Return the count of `true` bits in the `BitStore`.
    pub fn count_ones(&self) -> usize {
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
        if self.bit_length > 0 {
            let last_int = (self.get_bit_length() - 1) / u8::BITS as usize;
            // let last_count = (self.bits[last_int] & REST_MASK[(self.get_capacity() - self.bit_length) % u8::BITS as usize]).count_ones() as usize;
            let last_count = (self.bits[last_int] & REST_MASK[self.get_bit_length() - last_int * u8::BITS as usize - 1]).count_ones() as usize;
            self.bits[..last_int].iter().fold(last_count, |acc, x| acc + x.count_ones() as usize)
        } else {
            0
        }
    }

    /// Return the given `Vec` of `BitStore`s *normalized* to have the same `bit_length` and `capacity()`.
    pub fn normalize(faces: &[Self]) -> Vec<Self> {
        let mut res = vec![];
        res.extend_from_slice(faces);
        if res.len() > 1 {
            let max_bit_length = faces.iter()
                .max_by(
                    |&a, &b|
                    a.get_bit_length().cmp(&b.bit_length))
                .unwrap()
                .get_bit_length();
            for idx in 0..res.len() {
                if res[idx].bit_length < max_bit_length {
                    res[idx].set_capacity(max_bit_length).unwrap();
                    res[idx].set_bit_length(max_bit_length).unwrap();
                }
            }
        }
        res
    }

}

impl From<Vec<bool>> for BitStore {
    fn from(bools: Vec<bool>) -> Self {
        let mut res = BitStore::new();
        res.set_capacity(bools.len()).unwrap();
        res.set_bit_length(bools.len()).unwrap();
        res.set_bits(0..bools.len(), bools).unwrap();
        res
    }
}

macro_rules! impl_bitstore_from_vec_int {
    ( $( u8 )? ) => {
        impl From<Vec<u8>> for BitStore {
            fn from(ints: Vec<u8>) -> Self {
                BitStore {
                    bit_length: ints.len() * u8::BITS as usize,
                    bits: ints,
                }
            }
        }
    };
    ( $( $x:ty ),+ ) => {
        $(
            impl From<Vec<$x>> for BitStore {
                fn from(ints: Vec<$x>) -> Self {
                    BitStore {
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
impl_bitstore_from_vec_int!(u8, u16, u32, u64, u128, usize);

macro_rules! impl_bitstore_display {
    ( $fmt:tt, $whole:tt, $part:tt, $rest:tt ) => {
        impl fmt::$fmt for BitStore {
            /// Show a big-endian binary representation of the [`BitStore`] on one line.
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let whole_ints = self.bit_length / u8::BITS as usize;
                let rest_bits = self.bit_length % u8::BITS as usize;
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
                        .map(|x| format!($whole, x))
                        .collect::<Vec<String>>()
                        .join(", "),
                );
                if rest_bits > 0 {
                    if whole_ints == 0 {
                        write!(s, $rest, self.bits[whole_ints] & REST_MASK[rest_bits]).unwrap();
                    } else {
                        write!(
                            s,
                            $part,
                            // self.bits[whole_ints] & REST_MASK[rest_bits - 1]
                            (self.bits[whole_ints] & REST_MASK[rest_bits - 1]) >> (u8::BITS as usize - rest_bits)
                        )
                        .unwrap();
                    }
                }
                s.push(']');
                write!(f, "{s}")
            }
        }
    };
}
impl_bitstore_display!(Binary, "{:08b}", ", {:b}", "{:b}");
impl_bitstore_display!(LowerHex, "{:02x}", ", {:x}", "{:x}");
impl_bitstore_display!(UpperHex, "{:02X}", ", {:X}", "{:X}");

impl Not for BitStore {
    type Output = Self;

    /// Performs the unary [`!!`](std::ops::Not) operations for a [`Face`].
    fn not(self) -> Self::Output {
        BitStore {
            bit_length: self.bit_length,
            bits: self.bits.iter().map(|x| !x).collect(),
        }
    }
}

macro_rules! impl_bitstore_bit_logic {
    ( $trait:tt, $func:tt, $op:tt ) => {
        impl $trait for BitStore {
            type Output = Self;

            /// Performs the [`&`](std::ops::$trait::$func) operation for two [`BitStore`]s of same `bit_length`.
            ///
            /// Panics if the two [`BitStore`]s don't have the same `bit_length`.
            fn $func(self, rhs: Self) -> Self::Output {
                if self.is_empty() {
                    rhs
                } else if rhs.is_empty() {
                    self
                } else {
                    assert!(
                        self.bit_length == rhs.bit_length,
                        "BitStore::$func requires non-empty BitStores to have equal bit_length but: {} != {}",
                        self.bit_length,
                        rhs.bit_length
                    );
                    assert!(self.bits.len() == rhs.bits.len(), "BitStore::$func requires non-empty BitStores to have equal length bit fields but: {} != {}", self.bits.len(), rhs.bits.len());
                    BitStore {
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
impl_bitstore_bit_logic!(BitAnd, bitand, &);
impl_bitstore_bit_logic!(BitOr, bitor, |);
impl_bitstore_bit_logic!(BitXor, bitxor, ^);

impl Face for BitStore {
    type Vertex = usize;

    fn new() -> Self {
        Self::new()
    }

    fn from_vertices(vertices: Vec<Self::Vertex>) -> Self {
        let &max = match vertices.iter().max() {
            None => return Self::new(),
            Some(n) => n
        };
        let mut res = Self::new();
        // res.bit_length = *max + 1;
        // res.bits = vec![0u8; 1 + *max / u8::BITS as usize];
        res.set_capacity(max).unwrap();
        res.set_bit_length(max).unwrap();
        for v in vertices {
            // res.set_bit(v, true).unwrap();
            res.insert(v);
        }
        res
    }

    fn vertices(&self) -> Vec<Self::Vertex> {
        self.get_bits(0..self.bit_length).unwrap()
            .iter()
            .enumerate()
            .filter_map(|(idx, bit)| if *bit {Some(idx)} else {None})
            .collect::<Vec<Self::Vertex>>()
    }

    fn contains(&self, vertex: &Self::Vertex) -> bool {
        self.get_bit(*vertex).unwrap_or(false)
    }

    fn size(&self) -> usize {
        self.count_ones()
    }

    fn insert(&mut self, vertex: Self::Vertex) -> &mut Self {
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
            self.set_bit_length(vertex + 1).unwrap();
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

    // /// Return `true` unless this and the given [`BitStore`] share a `true` bit at some position or an error if they don't have equal `bit_length`s.
    // ///
    // /// **NB**: Unlike the `lua` version, [`empty`](BitStore::is_empty()) and [`zero`](BitStore::is_zero()) [`BitStore`]s are *not* disjoint from each other and *are* disjoint from non-[`empty`](BitStore::is_empty()) and non-[`zero`](BitStore::is_zero()) ones. Finding empties disjoint from everything doesn't make sense.
    // fn is_disjoint(&self, other: &Self) -> Result<bool, &str> {
    //     if self.is_empty() || self.is_zero() {
    //         Ok(!(other.is_empty() || other.is_zero()))
    //     } else if other.is_empty() || other.is_zero() {
    //         Ok(true)
    //     } else if self.bit_length != other.bit_length {
    //         Err("requires non-empty BitStores to have equal bit_length")
    //     } else {
    //         Ok(zip(&self.bits, &other.bits).any(|(&a, &b)| a & b > 0))
    //         // let mut res = true;
    //         // for (i, elem) in self.bits.iter().enumerate() {
    //         //     if elem & other.bits[i] > 0 {
    //         //         res = false
    //         //     }
    //         // }
    //         // Ok(res)
    //     }
    // }

}

// Unit Tests
mod tests {
    // use std::ptr::eq;

    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use itertools::sorted;

    #[test]
    fn bitstore_new_works() {
        assert_eq!(BitStore::new(), BitStore { bit_length: 0, bits: vec![] });
    }

    #[test]
    fn bitstore_zero_works() {
        assert_eq!(BitStore::zero(9), BitStore { bit_length: 9, bits: vec![0u8; 2]});
    }

    #[test]
    fn bitstore_is_empty_works() {
        assert!(BitStore::new().is_empty());
        assert!(!BitStore::zero(9).is_empty());
        assert!(!BitStore { bit_length: 9, bits: vec![0u8, 1u8] }.is_empty());
    }

    #[test]
    fn bitstore_is_zero_works() {
        assert!(BitStore::zero(9).is_zero());
        assert!(!BitStore::new().is_zero());
        assert_eq!(!BitStore { bit_length: 6, bits: vec![0b00010000u8] }.is_zero(), true, "{:b}", BitStore { bit_length: 6, bits: vec![0b00010000u8] });
    }

    #[test]
    fn bitstore_from_vecbool_works() {
        assert_eq!(BitStore::from(vec![false, false, false, false, false, false, false, true, true]), BitStore { bit_length: 9, bits: vec![0b00000001u8, 0b10000000u8]});
    }

    #[test]
    fn bitstore_from_vecint_works() {
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

        assert_eq!(BitStore::from(vec![0b01010101u8]).get_bits(0..8), Ok(vec![false, true, false, true, false, true, false, true]));
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
    fn bitstore_count_ones_works() {
        let bs = BitStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        assert_eq!(bs.count_ones(), 5);
        assert_eq!(BitStore::from(vec![0b01010101u8]).count_ones(), 4, "count_ones for {:?}", BitStore::from(vec![0b01010101u8]));
    }

    #[test]
    fn bitstore_normalize_works() {
        let bs1 = BitStore::from(vec![0b00110001u8]);
        let bs2 = BitStore {bit_length: 14, bits: vec![0b00110001u8, 0b00100101u8]};
        let bs_slice = &vec![bs1.clone(), bs2.clone()][..];
        assert_eq!(BitStore::normalize(bs_slice), vec![BitStore {bit_length: 14, bits: vec![0b00110001u8, 0]}, bs2]);
    }

    #[test]
    fn bitstore_not_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        assert_eq!(!BitStore::from(v1.clone()), BitStore::from(not_v1.clone()));
        assert_eq!(!BitStore { bit_length: 10, bits: v1 }, BitStore { bit_length: 10, bits: not_v1 });
    }

    #[test]
    fn bitstore_bitand_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        let bs1 = BitStore::from(v1.clone());
        let bs2 = BitStore::from(not_v1.clone());
        assert_eq!(bs1.clone() & bs2.clone(), BitStore::zero(16));
        assert_eq!(BitStore { bit_length: 10, bits: v1} & BitStore { bit_length: 10, bits: not_v1}, BitStore { bit_length: 10, bits: vec![0u8;2]});
    }

    #[test]
    fn bitstore_bitor_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let not_v1 = vec![!0b00110001u8, !0b01010101u8];
        let bs1 = BitStore::from(v1.clone());
        let bs2 = BitStore::from(not_v1.clone());
        assert_eq!(bs1.clone() | bs2.clone(), ! BitStore::zero(16));
        assert_eq!(BitStore { bit_length: 10, bits: v1} | BitStore { bit_length: 10, bits: not_v1}, BitStore { bit_length: 10, bits: vec![! 0u8; 2]});
    }

    #[test]
    fn bitstore_bitxor_works() {
        let v1 = vec![0b00110001u8, 0b01010101u8];
        let v2 = vec![0b01010101u8, 0b00110001u8];
        let v3 = vec![0b01100100u8, 0b01100100u8];
        let bs1 = BitStore::from(v1.clone());
        let bs2 = BitStore::from(v2.clone());
        let bs3 = BitStore::from(v3.clone());
        assert_eq!(bs1.clone() ^ bs2.clone(), bs3.clone() );
        assert_eq!(BitStore { bit_length: 10, bits: v1} ^ BitStore { bit_length: 10, bits: v2}, BitStore { bit_length: 10, bits: v3});
    }

    #[test]
    fn bitstore_binary_works() {
        assert_eq!(format!("{:b}", BitStore::from(vec![0b01010101u8])), "[01010101]".to_string());
        assert_eq!(format!("{:b}", BitStore::from_vertices(vec![2, 4, 8, 9, 12])), "[00101000, 11001]".to_string());
    }

    #[test]
    fn face_bitstore_from_vertices_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        // let bs2 = BitStore {bit_length: 9, bits: vec![0b00101000, 0b00000001u8]};
        let bs2 = BitStore {bit_length: 9, bits: vec![0b00101000, 0b10000000u8]};
        assert_eq!(bs1, bs2, "\n\nbs1:{:?}={:b} bs2:{:?}={:b}", bs1, bs1, bs2, bs2);
        assert_eq!(BitStore::from_vertices(vec![2, 4]), BitStore {bit_length: 5, bits: vec![0b00101000]});
        assert_eq!(BitStore::from_vertices(vec![]), BitStore {bit_length: 0, bits: vec![]});
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        assert_eq!(bs3, BitStore {bit_length: 9, bits: vec![0b00100000, 0b10000000u8]});
        let bs5 = BitStore::from_vertices(vec![5, 7]);
        assert_eq!(bs5, BitStore {bit_length: 8, bits: vec![0b00000101]});
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
    fn face_bitstore_is_disjoint_works() {
        assert!(!BitStore::new().is_disjoint(&BitStore::new()));
        assert!(BitStore::from(vec![0b00000101u8]).is_disjoint(&BitStore::new()));
        assert!(BitStore::from(vec![0b00000101u8]).is_disjoint(&BitStore::from(vec![0b00101000u8])));
        assert!(!BitStore::from(vec![0b00000101u8]).is_disjoint(&BitStore::from(vec![0b0000100u8])));
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
        let bs3 = BitStore::from_vertices(vec![2, 4]);
        assert!(bs1.is_ancestor_of(&bs2));
        assert!(bs1.is_ancestor_of(&bs3));
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

    #[test]
    fn face_bitstore_maximals_works() {
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs5 = BitStore::from_vertices(vec![2]);
        let bs6 = BitStore::from_vertices(vec![4]);
        let bs7 = BitStore::from_vertices(vec![8]);
        let v1 = vec![bs2.clone(), bs5.clone(), bs6.clone(), bs7.clone()];
        let want = vec![bs2.clone(), bs5.clone()];
        assert_eq!(Face::maximals(&v1), want);
    }

    #[test]
    fn face_bitstore_closure_works() {
        let bs0 = BitStore::new();
        // let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        // let bs4 = BitStore::from_vertices(vec![2, 4]);
        let bs5 = BitStore::from_vertices(vec![2]);
        let bs6 = BitStore::from_vertices(vec![4]);
        let bs7 = BitStore::from_vertices(vec![8]);
        let v1 = vec![bs2.clone(), bs3.clone()];
        let res = sorted(Face::closure(&v1)).collect::<Vec<BitStore>>();
        let want = sorted(vec![bs0.clone(), bs2.clone(), bs3.clone(), bs5.clone(), bs6.clone(), bs7.clone()]).collect::<Vec<BitStore>>();
        assert_eq!(res, want);
    }

    #[test]
    fn asc_from_and_faces_work() {
        let bs0 = BitStore::new();
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let bs4 = BitStore::from_vertices(vec![2, 4]);
        let bs5 = BitStore::from_vertices(vec![2]);
        let bs6 = BitStore::from_vertices(vec![4]);
        let bs7 = BitStore::from_vertices(vec![8]);
        let asc1 = ASC::from(vec![bs2.clone(), bs1.clone(), bs3.clone()]);
        // asc1.sort();
        let mut asc_vec = vec![bs3, bs2, bs4, bs1, bs5, bs6, bs7];
        assert_eq!(asc1.0, Face::maximals(&asc_vec), "\nasc1.sort() != maximals(asc_vec.sort()");
        let mut res = asc1.faces();
        res.sort();
        asc_vec.insert(0, bs0);
        asc_vec.sort();
        assert_eq!(res, asc_vec, "\nasc1.sort().faces() != asc_vec.sort()");
    }

    #[test]
    fn asc_vertices_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert_eq!(asc1.vertices(), vec![2, 4, 8]);
    }

    #[test]
    fn asc_contains_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let bs4 = BitStore::from_vertices(vec![2, 4]);
        let bs5 = BitStore::from_vertices(vec![5, 7]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(asc1.contains(&bs1));
        assert!(asc1.contains(&bs2));
        assert!(asc1.contains(&bs3));
        assert!(asc1.contains(&bs4));
        assert!(!asc1.contains(&bs5));
    }

    #[test]
    fn asc_insert_face_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let bs4 = BitStore::from_vertices(vec![2, 4]);
        let mut asc1 = ASC::from(vec![bs1.clone(), bs2.clone()]);
        asc1.insert_face(bs3.clone());
        assert!(asc1.contains(&bs3));
        asc1.insert_face(bs4.clone());
        assert!(asc1.contains(&bs4));
    }

    #[test]
    fn asc_remove_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        asc1.remove_face(bs3.clone());
        assert!(!asc1.contains(&bs3));
    }

    #[test]
    fn asc_size_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert_eq!(asc1.size(), 3)
    }

    #[test]
    fn asc_is_empty_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(!asc1.is_empty());
        assert!(ASC::from(vec![]).is_empty());
    }

    #[test]
    fn asc_is_maximal_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(!asc1.is_maximal(&bs3), "not is_maximal({:b}) fails with generators {:?}", bs3, asc1.generators());
        assert!(asc1.is_maximal(&bs1), "is_maximal({:b}) fails with generators {:?}", bs1, asc1.generators());
    }

    #[test]
    fn asc_generators_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let asc1 = ASC::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        let res = asc1.generators().sort();
        let want = vec![bs1.clone(), bs2.clone(), bs3.clone()].sort();
        assert_eq!(res, want);
        assert_eq!(ASC::from(vec![]).generators(), vec![]);
    }

    #[test]
    fn brel_new_works() {
        let br = BRel::new();
        assert_eq!(br, BRel { major_axis: Axis::Row, contents: vec![]});
        assert_eq!(br.get_major_axis(), BRel::default().get_major_axis());
        assert_eq!(br.get_contents(), BRel::default().get_contents());
    }

    #[test]
    fn brel_binary_works() {
        assert_eq!(format!("{:b}", BRel::from(vec![BitStore::from(vec![0b01010101u8])])), "[[01010101]]".to_string());
    }

    #[test]
    fn reltrait_brel_new_and_is_empty_work() {
        let r1 = BRel::new();
        assert_eq!(r1, BRel { major_axis: Axis::Row, contents: vec![]});
        assert!(r1.is_empty());
    }

    #[test]
    fn reltrait_brel_from_bitstores_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let bsvec = vec![bs1, bs2, bs3];
        let r1 = BRel::from(bsvec.clone());
        assert_eq!(r1, BRel { major_axis: Axis::Row, contents: bsvec});
    }

    #[test]
    fn reltrait_brel_zero_works() {
        assert_eq!(BRel::zero(2, 9, Axis::Column), BRel { major_axis: Axis::Column, contents: vec![BitStore::zero(2); 9]});
    }

    #[test]
    fn reltrait_brel_get_major_axis_works() {
        assert_eq!(BRel::new().major_axis, BRel::default().major_axis);
    }

    #[test]
    fn reltrait_brel_set_major_axis_works() {
        let mut r1 = BRel::new();
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_major_axis(), Axis::Column);
    }

    #[test]
    fn reltrait_brel_get_row_count_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let r1 = BRel::from(vec![bs2, bs1, bs3]);
        assert_eq!(r1.get_row_count(), 3);
        assert_eq!(BRel::new().get_row_count(), 0);
    }

    #[test]
    fn reltrait_brel_get_col_count_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1, bs3]);
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_col_count(), 3);
        assert_eq!(BRel::new().get_col_count(), 0);
    }

    #[test]
    fn reltrait_brel_get_row_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.get_row(1), bs1.get_bits(0..bs1.get_bit_length()));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_row(0), Ok(vec![false, false, false]));
    }

    #[test]
    fn reltrait_brel_set_row_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.set_row(2, bs1.get_bits(0..bs1.get_bit_length()).unwrap()).unwrap().get_row(2), bs1.get_bits(0..bs1.get_bit_length()));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.set_row(0, vec![true, true, true]).unwrap().get_row(0), Ok(vec![true, true, true]));
    }

    #[test]
    fn reltrait_brel_get_col_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.get_col(0), Ok(vec![false, false, false]));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_col(1), bs1.get_bits(0..bs1.get_bit_length()));
    }

    #[test]
    fn reltrait_brel_set_col_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let bs3 = BitStore::from_vertices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.set_col(0, vec![true, true, true]).unwrap().get_col(0), Ok(vec![true, true, true]));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.set_col(2, bs1.get_bits(0..bs1.get_bit_length()).unwrap()).unwrap().get_col(2), bs1.get_bits(0..bs1.get_bit_length()));
    }

    // #[test]
    // fn reltrait_brel_transpose_works() {
    //     let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
    //     let bs2 = BitStore::from_vertices(vec![4, 8]);
    //     let bs3 = BitStore::from_vertices(vec![2, 8]);
    //     let mut r1 = BRel::from(vec![bs1, bs2, bs3]);
    //     let bs1_t = BitStore::from_vertices(vec![]);
    //     let bs2_t = BitStore::from_vertices(vec![]);
    //     let bs3_t = BitStore::from_vertices(vec![0, 2]);
    //     let bs4_t = BitStore::from_vertices(vec![]);
    //     let bs5_t = BitStore::from_vertices(vec![0, 1]);
    //     let bs6_t = BitStore::from_vertices(vec![]);
    //     let bs7_t = BitStore::from_vertices(vec![]);
    //     let bs8_t = BitStore::from_vertices(vec![]);
    //     let bs9_t = BitStore::from_vertices(vec![0, 1, 2]);
    //     let mut r1_t = BRel::from(vec![bs1_t, bs2_t, bs3_t, bs4_t, bs5_t, bs6_t, bs7_t, bs8_t, bs9_t]);
    //     let res = r1.transpose().unwrap();
    //     assert_eq!((res.get_row_count(), res.get_col_count(), res.get_major_axis()), (9,3,Axis::Row), "res:{:b}", res);
    //     assert_eq!(res, &mut r1_t);

    //     res.set_major_axis(&Axis::Column);
    //     r1_t.set_major_axis(&Axis::Column);
    //     assert_eq!(res, &r1_t);
    // }

    #[test]
    fn mydowker_new_works() {
        assert_eq!(MyDowker::new(), MyDowker { generators: ASC::new(), weights: BTreeMap::new() });
    }

    #[test]
    fn mydowker_from_brel_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![2, 4]);
        let bs2_normalized = &BitStore::normalize(&[bs1.clone(), bs2.clone()])[1];
        let br = BRel::from(vec![bs1.clone(), bs2.clone()]);
        let mut bt: BTreeMap<BitStore, usize> = BTreeMap::new();
        bt.insert(bs1.clone(), 1);
        bt.insert(bs2_normalized.clone(), 1);
        assert_eq!(MyDowker::from(&br), MyDowker { generators: ASC(vec![bs1.clone()]), weights: bt}, "\n\nbs1:{:?}={:b} bs2:{:?}={:b}\nbr[0]:{:?}={:b} br[1]:{:?}={:b}\n", bs1, bs1, bs2, bs2, br.get_contents()[0], br.get_contents()[0], br.get_contents()[1], br.get_contents()[1]);
    }

    #[test]
    fn mydowker_is_empty_works() {
        assert!(MyDowker::new().is_empty())
    }

    #[test]
    fn mydowker_diff_weight_works() {
        let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BitStore::from_vertices(vec![4, 8]);
        let br = BRel::from(vec![bs1.clone(), bs2.clone()]);
        let dk = MyDowker::from(&br);
        assert_eq!(dk.diff_weight(&bs1), 1);
        assert_eq!(dk.diff_weight(&bs2), 1);
    }

    #[test]
    fn mydowker_tot_weight_works() {

    }

}
