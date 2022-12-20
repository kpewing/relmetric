/*! Abstract Simplicial Complexes

This modules creates the [`AbstractSimplicialComplex`] `trait` and an implementing `struct` [`AbSiCo`] representing an *abstract simplicial complex*, along with supporting `trait`s and implementing `struct`s.
 */

use core::hash::Hash;
use std::{fmt::{Debug}};

use itertools::Itertools;
use serde::{Serialize, Deserialize};

use crate::bitstore::*;

/// A generic trait for an *abstract simplicial complex* of its associated type [`Face`](AbstractSimplicialComplex::Face)s.
///
/// An [*abstract simplicial complex* (*asc*)](https://en.wikipedia.org/wiki/Abstract_simplicial_complex) is a collection of sets called [`Face`]s that is closed under taking subsets; *i.e*, every subset of a [`Face`] in the collection is also in the collection. Each [`Face`] is a set of *vertices*. The *vertex set* of an [*asc*](AbstractSimplicialComplex) is the union of all the [`Face`]s, *i.e.*, all the *vertices* used in the [*asc*](AbstractSimplicialComplex). The [`size`](AbstractSimplicialComplex::size()) of an [`AbstractSimplicialComplex`] is the largest [`size`](Face::size()) of any [`Face`] in the complex. The [`generators`](AbstractSimplicialComplex::generators()) of an [`AbstractSimplicialComplex`] are a collection of [`maximal`](AbstractSimplicialComplex::is_maximal()) [`Face`]s within the complex, the union of the [`closure`s](Face::closure()) of which equals the [`AbstractSimplicialComplex`], *i.e.*, one can "generate" the complex by collecting the [`generators`](AbstractSimplicialComplex::generators()) and all of their [`descendants`](Face::descendants()), without duplication.
///
/// **NB**: The common definition is extended to permit an [*asc*](AbstractSimplicialComplex) to be empty.
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
    /// - Collects the unique [`Vertices`](Face::Vertex) of the [`generators()`](AbstractSimplicialComplex::generators()`).
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
    fn is_maximal(&self, face: &Self::Face) -> bool
    where
        Self::Face: Face + PartialEq,
    {
        self.generators().iter().any(|x| x == face)
    }

}

/// A generic trait for *faces* of an [`AbstractSimplicialComplex`] of *vertices* of the associated type [`Vertex`](Face::Vertex).
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
    /// **NB**: [`empty`](Face::is_empty()) are *not* disjoint from each other and *are* disjoint from non-[`empty`](Face::is_empty()) ones. Finding empties disjoint from everything doesn't make sense.
    ///
    /// # Default Implementation
    /// - Whether both are [`empty`](Face::is_empty()) or the given [`Face`] [`contains`](Face::contains()) any *vertex* of this one.
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
    fn is_parent_of(&self, face: &Self) -> bool
    where
        Self::Vertex: PartialEq
    {
        self.size() == face.size() + 1 && self.is_ancestor_of(face)
    }

    /// Return `true` if this [`Face`] is [`size`](Face::size()) 1 smaller than the given [`Face`] and all its *vertices* are contained in the given one.
    ///
    /// # Default Implementation
    /// - Flip [`is_parent_of()`](Face::is_parent_of()).
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

    /// Return the size-sorted subset of the given [`Vec`] of [`Face`]s that are not descendants of any other [`Face`]s in the given [`Vec`] of [`Face`]s.
    ///
    /// # Default Implementation
    /// - Panics if the capacity of the new [`Vec`] would exceed `isize::MAX` bytes.
    fn maximals(faces: &[Self]) -> Vec<Self>
    where
        Self: Sized + Clone + Ord,
        Self::Vertex: PartialEq,
    {
        let mut res = vec![];
        let mut input = faces.to_vec();
        input.sort_by_key(|a| a.size());
        for f in input.iter().rev() {
            if !res.iter().any(|g| (*f).is_descendant_of(g)) {
                res.push((*f).clone())
            }
        };
        res.sort();
        res
    }

    /// Return the given [`Face`]s and all their [`descendant`](Face::descendants())s.
    ///
    /// Compare [*closure*](https://en.wikipedia.org/wiki/Simplicial_complex#Closure,_star,_and_link).
    ///
    /// # Default Implementation
    /// - Apply [`unique()`](itertools::Itertools::unique()) to all [`descendants()`](Face::descendants()).
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

impl Face for BStore {
    type Vertex = usize;

    fn new() -> Self {
        Self::new()
    }

    fn from_vertices(vertices: Vec<Self::Vertex>) -> Self {
        BStore::from_indices(vertices)
    }

    fn vertices(&self) -> Vec<Self::Vertex> {
        self.get_bits(0..self.get_bit_length()).unwrap()
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

}

/// A `struct` to implement an [*abstract simplicial complex*](AbstractSimplicialComplex) on a *vertex set* of `usize`s.
///
/// Just wraps the [*generators*](AbstractSimplicialComplex::generators()).
#[derive(Default, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct AbSiCo(Vec<BStore>);

impl AbSiCo {
    pub fn new() -> Self
    {
        Default::default()
    }
}

impl AbstractSimplicialComplex for AbSiCo {
    type Face = BStore;

    fn generators(&self) -> Vec<Self::Face> {
        // self.0.to_vec()
        Face::maximals(&self.0.to_vec())
    }

    fn insert_face (&mut self, face: Self::Face) -> &mut Self {
        // println!("insert_face self:{:?} face:{:b} contains:{}", self, face, self.contains(&face));
        if self.contains(&face) {
            self
        } else {
            self.0.push(face);
            self.0 = BStore::normalize(&self.0);
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

impl From<Vec<BStore>> for AbSiCo {
    fn from(faces: Vec<BStore>) -> Self {
        AbSiCo(Face::maximals(&BStore::normalize(&faces)))
    }
}

// Unit Tests
mod tests {
    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use itertools::sorted;

    #[test]
    fn face_bitstore_from_vertices_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        // let bs2 = BitStore {bit_length: 9, bits: vec![0b00101000, 0b00000001u8]};
        let bs2 = BStore::from(vec![false, false, true, false, true, false, false, false, true]);
        assert_eq!(bs1, bs2, "\n\nbs1:{:?}={:b} bs2:{:?}={:b}", bs1, bs1, bs2, bs2);
        assert_eq!(BStore::from_vertices(vec![2, 4]), BStore::from(vec![false, false, true, false, true]));
        assert_eq!(BStore::from_vertices(vec![]), BStore::new());
        let bs3 = BStore::from_vertices(vec![2, 8]);
        assert_eq!(bs3, BStore::from(vec![false, false, true, false, false, false, false, false, true]));
        let bs5 = BStore::from_vertices(vec![5, 7]);
        assert_eq!(bs5, BStore::from(vec![false, false, false, false, false, true, false, true]));
    }

    #[test]
    fn face_bitstore_vertices_works() {
        assert_eq!(BStore::from_vertices(vec![2, 4, 8]).vertices(), vec![2, 4, 8]);
        assert_eq!(BStore::from_vertices(vec![]).vertices(), vec![]);
    }

    #[test]
    fn face_bitstore_contains_works() {
        let bs = BStore::from_vertices(vec![2, 4, 8]);
        assert!(bs.contains(&4));
        assert!(!bs.contains(&1));
        assert!(!bs.contains(&12));
        assert!(!bs.contains(&30));
    }

    #[test]
    fn face_bitstore_is_disjoint_works() {
        assert!(!BStore::new().is_disjoint(&BStore::new()));
        assert!(BStore::from(vec![0b00000101u8]).is_disjoint(&BStore::new()));
        assert!(BStore::from(vec![0b00000101u8]).is_disjoint(&BStore::from(vec![0b00101000u8])));
        assert!(!BStore::from(vec![0b00000101u8]).is_disjoint(&BStore::from(vec![0b0000100u8])));
    }

    #[test]
    fn face_bitstore_insert_works() {
        let mut bs = BStore::from_vertices(vec![2, 4, 8]);
        assert!(bs.insert(1).contains(&1));
        assert!(bs.insert(10).contains(&10));
    }

    #[test]
    fn face_bitstore_remove_works() {
        let mut bs = BStore::from_vertices(vec![2, 4, 8]);
        assert!(!bs.remove(&1).contains(&1));
        assert!(!bs.remove(&2).contains(&2));
        assert!(!bs.remove(&10).contains(&10));
    }

    #[test]
    fn face_bitstore_size_works() {
        assert_eq!(BStore::new().size(), 0);
        assert_eq!(BStore::from_vertices(vec![2, 4, 8]).size(), 3);
    }

    #[test]
    fn face_bitstore_is_empty_works() {
        // assert!(BitStore::new().is_empty());
        assert!(Face::is_empty(&BStore::new()));
        assert!(!Face::is_empty(&BStore::from_vertices(vec![2, 4, 8])));
    }

    #[test]
    fn face_bitstore_is_parent_of_works() {
        let bs0 = BStore::new();
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![4]);
        assert!(!bs1.is_parent_of(&bs1));
        assert!(!bs2.is_parent_of(&bs1));
        assert!(bs1.is_parent_of(&bs2));
        assert!(!bs0.is_parent_of(&bs1));
        assert!(bs3.is_parent_of(&bs0));
    }

    #[test]
    fn face_bitstore_is_child_of_works() {
        let bs0 = BStore::new();
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![4]);
        assert!(!bs1.is_child_of(&bs1));
        assert!(bs2.is_child_of(&bs1));
        assert!(!bs1.is_child_of(&bs2));
        assert!(!bs0.is_child_of(&bs1));
        assert!(bs0.is_child_of(&bs3));
    }

    #[test]
    fn face_bitstore_children_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let res = bs1.children();
        assert_eq!(res.len(), 3);
        assert_eq!(res[0].size(), 2);
        for x in bs1.children() {
            assert!(x.is_child_of(&bs1))
        }
    }

    #[test]
    fn face_bitstore_is_ancestor_of_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 4]);
        assert!(bs1.is_ancestor_of(&bs2));
        assert!(bs1.is_ancestor_of(&bs3));
        assert!(!bs2.is_ancestor_of(&bs1));
    }

    #[test]
    fn face_bitstore_is_descendant_of_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        assert!(!bs1.is_descendant_of(&bs2));
        assert!(bs2.is_descendant_of(&bs1));
    }

    #[test]
    fn face_bitstore_descendants_works() {
        let bs0 = BStore::from_vertices(vec![]);
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let bs4 = BStore::from_vertices(vec![2, 4]);
        let bs5 = BStore::from_vertices(vec![2]);
        let bs6 = BStore::from_vertices(vec![4]);
        let bs7 = BStore::from_vertices(vec![8]);
        let mut res = bs1.descendants();
        res.sort();
        let mut want = [bs0, bs2, bs3, bs4, bs5, bs6, bs7];
        want.sort();
        assert_eq!(res, want);
    }

    #[test]
    fn face_bitstore_maximals_works() {
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs5 = BStore::from_vertices(vec![2]);
        let bs6 = BStore::from_vertices(vec![4]);
        let bs7 = BStore::from_vertices(vec![8]);
        let v1 = vec![bs2.clone(), bs5.clone(), bs6.clone(), bs7.clone()];
        let want = vec![bs2.clone(), bs5.clone()];
        assert_eq!(Face::maximals(&v1), want);
    }

    #[test]
    fn face_bitstore_closure_works() {
        let bs0 = BStore::new();
        // let bs1 = BitStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        // let bs4 = BitStore::from_vertices(vec![2, 4]);
        let bs5 = BStore::from_vertices(vec![2]);
        let bs6 = BStore::from_vertices(vec![4]);
        let bs7 = BStore::from_vertices(vec![8]);
        let v1 = vec![bs2.clone(), bs3.clone()];
        let res = sorted(Face::closure(&v1)).collect::<Vec<BStore>>();
        let want = sorted(vec![bs0.clone(), bs2.clone(), bs3.clone(), bs5.clone(), bs6.clone(), bs7.clone()]).collect::<Vec<BStore>>();
        assert_eq!(res, want);
    }

    #[test]
    fn asc_from_and_faces_work() {
        let bs0 = BStore::new();
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let bs4 = BStore::from_vertices(vec![2, 4]);
        let bs5 = BStore::from_vertices(vec![2]);
        let bs6 = BStore::from_vertices(vec![4]);
        let bs7 = BStore::from_vertices(vec![8]);
        let asc1 = AbSiCo::from(vec![bs2.clone(), bs1.clone(), bs3.clone()]);
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
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert_eq!(asc1.vertices(), vec![2, 4, 8]);
    }

    #[test]
    fn asc_contains_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let bs4 = BStore::from_vertices(vec![2, 4]);
        let bs5 = BStore::from_vertices(vec![5, 7]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(asc1.contains(&bs1));
        assert!(asc1.contains(&bs2));
        assert!(asc1.contains(&bs3));
        assert!(asc1.contains(&bs4));
        assert!(!asc1.contains(&bs5));
    }

    #[test]
    fn asc_insert_face_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let bs4 = BStore::from_vertices(vec![2, 4]);
        let mut asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone()]);
        asc1.insert_face(bs3.clone());
        assert!(asc1.contains(&bs3));
        asc1.insert_face(bs4.clone());
        assert!(asc1.contains(&bs4));
    }

    #[test]
    fn asc_remove_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let mut asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        asc1.remove_face(bs3.clone());
        assert!(!asc1.contains(&bs3));
    }

    #[test]
    fn asc_size_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert_eq!(asc1.size(), 3)
    }

    #[test]
    fn asc_is_empty_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(!asc1.is_empty());
        assert!(AbSiCo::from(vec![]).is_empty());
    }

    #[test]
    fn asc_is_maximal_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert!(!asc1.is_maximal(&bs3), "not is_maximal({:b}) fails with generators {:?}", bs3, asc1.generators());
        assert!(asc1.is_maximal(&bs1), "is_maximal({:b}) fails with generators {:?}", bs1, asc1.generators());
    }

    #[test]
    fn asc_generators_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let bs3 = BStore::from_vertices(vec![2, 8]);
        let asc1 = AbSiCo::from(vec![bs1.clone(), bs2.clone(), bs3.clone()]);
        assert_eq!(asc1.generators(), vec![bs1.clone()]);
        assert_eq!(AbSiCo::from(vec![]).generators(), vec![]);
    }

}
