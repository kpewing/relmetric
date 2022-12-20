/*! # Dowker Complexes

This module creates the [`Dowker`] to represent a *Dowker complex*, along with various supporting types and traits, including the [`Abstract Simplicial Complex`](AbstractSimplicialComplex), the [`Face`], and the underlying [`BitStore`] trait and default [`BitStore`] struct.

For more about *abstract simplicial complexes* and the *Dowker complex*, see [Definitions 4 and 5, *Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^1]

[^1]: [Kenneth P. Ewing & Michael Robinson, "Metric Comparison of Relations," p. 7](https://arxiv.org/abs/2105.01690).
*/

use std::collections::BTreeMap;
use std::fmt::Debug;

use serde::{Serialize, Deserialize};

use crate::bitstore::BStore;
use crate::relation::*;
use crate::absico::*;

/// A `trait` for a *Dowker Complex*.
///
/// A *Dowker Complex* represents the rows or columns of a *binary relation* as [`Face`]s of an [*abstract simplicial complex*](AbstractSimplicialComplex) and assigns a [*differential weight*](Dowker::diff_weight()) and a [*total weight*](Dowker::tot_weight()) to each such [`Face`].
///
/// For more on *Dowker Complexes*, *see, e.g.*, [Michael Robinson, "Cosheaf representations of relations and Dowker complexes", J Appl. and Comput. Topology 6, 27–63 (2022)](https://doi.org/10.1007/s41468-021-00078-y).
pub trait DowkerComplex {
    type A: AbstractSimplicialComplex;
    type F: Face;

    /// Return `true` if this [`Dowker`] is empty, *i.e.*, has no [`Face`]s in it.
    fn is_empty(&self) -> bool;

    /// Return the *differential weight* of the given [`Face`] within the [`Dowker`], *i.e.*, the number of times that [`Face`] appears within the *Dowker Complex*'s *binary relation*.
    fn diff_weight(&self, face: &Self::F) -> usize;

    /// Return the *total weight* of the given [`Face`] within the [`Dowker`], *i.e.*, the sum of [`diff_weight()`](Dowker::diff_weight())s of all [`Face`]s within the given [`Face`] that appear within the *Dowker Complex*'s *binary relation*.
    fn tot_weight(&self, face: &Self::F) -> usize;
}

/// A `struct` to implement *Dowker Complexes*.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Dowker {
    /// The *Dowker Complex*'s generators.
    generators: AbSiCo,
    /// The [*differential weights*](Dowker::diff_weight()) of [`Face`]s in the *Dowker Complex*.
    weights: BTreeMap<BStore, usize>,
}

impl Dowker {
    /// Create a new, empty [`Dowker`].
    pub fn new() -> Self {
        Default::default()
    }
}

/// Create a [`Dowker`] from a [`BRel`].
impl From<&BRel> for Dowker
where
    BRel: Relation,
{
    fn from(relation: &BRel) -> Self {
        let mut res = Dowker::new();
        for f in &relation.get_contents() {
            // println!("Dowker::from<BRel> f:{:b} = {:b}", f, f);
            res.generators.insert_face(f.clone());
            res.weights.entry(f.clone())
                .and_modify(|diff_weight| *diff_weight += 1)
                .or_insert(1);
        }
        res
    }
}

impl DowkerComplex for Dowker {
    type A = AbSiCo;
    type F = BStore;

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

// Unit Tests
mod tests {
    // use crate::bitstore::BitStore;

    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use itertools::sorted;

    #[test]
    fn dowker_new_works() {
        assert_eq!(Dowker::new(), Dowker { generators: AbSiCo::new(), weights: BTreeMap::new() });
    }

    #[test]
    fn dowker_from_brel_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![2, 4]);
        let bs2_normalized = &BStore::normalize(&[bs1.clone(), bs2.clone()])[1];
        let br = BRel::from(vec![bs1.clone(), bs2.clone()]);
        let mut bt: BTreeMap<BStore, usize> = BTreeMap::new();
        bt.insert(bs1.clone(), 1);
        bt.insert(bs2_normalized.clone(), 1);
        assert_eq!(Dowker::from(&br), Dowker { generators: AbSiCo::from(vec![bs1.clone()]), weights: bt}, "\n\nbs1:{:?}={:b} bs2:{:?}={:b}\nbr[0]:{:?}={:b} br[1]:{:?}={:b}\n", bs1, bs1, bs2, bs2, br.get_contents()[0], br.get_contents()[0], br.get_contents()[1], br.get_contents()[1]);
    }

    #[test]
    fn dowker_is_empty_works() {
        assert!(Dowker::new().is_empty())
    }

    #[test]
    fn dowker_diff_weight_works() {
        let bs1 = BStore::from_vertices(vec![2, 4, 8]);
        let bs2 = BStore::from_vertices(vec![4, 8]);
        let br = BRel::from(vec![bs1.clone(), bs2.clone()]);
        let dk = Dowker::from(&br);
        assert_eq!(dk.diff_weight(&bs1), 1);
        assert_eq!(dk.diff_weight(&bs2), 1);
    }

    #[test]
    fn dowker_tot_weight_works() {

    }
}
