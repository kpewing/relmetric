/*! Relations

This module creates the [`Relation`] `trait` to represent a *binary relation* and relevant calculations on and with them, including the following:
- [`transpose()`](Relation::transpose()) to convert between [`Column`](Axis::Column)-major and [`Row`](Axis::Row)-major orientations,
- various logical (bit) operations, like [`BitAnd (&)`], and multiset operations [`Add`] and [`Sub`],
- [`Matches`] to specify functions between two *binary relations*, and
- [`weight()`](Relation::weight()), [`min_weight()`](Relation::min_weight()), and [`distance()`](Relation::distance()) between *binary relations*.
It also provides the `struct` [`BRel`] as default implementation, which can be formed from `Vec`s of [`Column`]s or [`Row`]s and printed as a binary matrix.
 */

use core::fmt;
// use core::ops::{Bound, Range, RangeBounds};
use core::iter::zip;
// use core::hash::Hash;
// use std::collections::BTreeMap;
use std::fmt::{Write, Debug};
use std::ops::{Not, BitAnd, BitOr, BitXor, Sub, Add, Index, IndexMut};
// use itertools::Itertools;

use itertools::Itertools;

pub use crate::bitstore::*;
use crate::impl_bitstore;

/// A `trait` for a *binary relation*.
pub trait Relation {

    /// Create a new, empty *binary relation*.
    fn new() -> Self;

    /// Return `true` if the *binary relation* is empty, *i.e.*, an array representation would be zero-length in both [`Axis::Row`] and [`Axis::Column`] dimensions.
    fn is_empty(&self) -> bool;

    /// Return `true` if the *binary relation* is not [`empty`](Relation::is_empty()) but there are no relations, *i.e.*, an array representation would be non-empty but have only `false` in it.
    fn is_zero(&self) -> bool;

    /// Return a new *binary relation* is not [`empty`](Relation::is_empty()), *i.e.*, an array representation would have non-zero-length [`Axis::Row`] and [`Axis::Column`] dimensions, but nothing is related to anything else, *i.e.*, all bits in the array are `false`.
    fn zero(row_count: usize, col_count: usize, major_axis: Axis) -> Self;

    /// Return the length of the [`Axis::Row`] dimension of the *binary relation*.
    fn get_row_count(&self) -> usize;

    /// Return the length of the [`Axis::Column`] dimension of the *binary relation*.
    fn get_col_count(&self) -> usize;

    /// Return the [`Axis::Row`] identified by the given `idx`.
    fn get_row(&self, idx: usize) -> Result<Vec<bool>, &'static str>;

    /// Set the [`Axis::Row`] identified by the given `idx` to the given `Vec<bool>` of bits.
    fn set_row(&mut self, idx: usize, row: Vec<bool>) -> Result<&mut Self, &'static str>;

    /// Return the [`Axis::Column`] identified by the given `idx`.
    fn get_col(&self, idx: usize) -> Result<Vec<bool>, &'static str>;

    /// Set the [`Axis::Column`] identified by the given `idx` to the given `Vec<bool>` of bits.
    fn set_col(&mut self, idx: usize, col: Vec<bool>) -> Result<&mut Self, &'static str>;

    /// Get the `bool` value at the given `row` and `col`.
    fn get_cell(&self, row: usize, col: usize) -> Result<bool, &'static str>;

    /// Get the `bool` value at the given `row` and `col`.
    fn set_cell(&mut self, row: usize, col: usize, val: bool) -> Result<&mut Self, &'static str>;

    /// Return the transposed *binary relation* with the same `major_axis`.
    fn transpose(&self) -> Self;

    /// Return the [`DJGrouping`] partition of the *binary relation* by its [`Axis`].
    ///
    /// **NB**: The [`DJGrouping`] of an [`empty`](Relation::is_empty()) *binary relation* is, itself "empty", i.e., has no [`DJGroup`]s in it.
    fn djgroup(&self) -> DJGrouping;

    /// Return the [`DJGrouping`] partition of the *binary relation* by the given [`Axis`], using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// **NB**: The [`DJGrouping`] of an [`empty`](Relation::is_empty()) *binary relation* is, itself "empty", i.e., has no [`DJGroup`]s in it.
    fn djgroup_by(&self, axis: &Axis) -> DJGrouping;

    /// Return the "kappa" value for a *binary relation*.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn kappa(&self, max_count: Option<usize>) -> usize;

    /// Return the "kappa" value for a *binary relation* by the given [`Axis`], using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn kappa_by(&self, max_count: Option<usize>, axis: &Axis) -> usize;

    /// Return an upper bound on the "distance" between two *binary relations*.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn rel_dist_bound(&self, other: &Self) -> usize;

    /// Return an upper bound on the "distance" between two *binary relations* by the given [`Axis`], using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn rel_dist_bound_by(&self, other: &Self, axis: &Axis) -> usize;

    /// Return a new *binary relation* resulting from applying `matches` between `self` and `other`.
    ///
    /// # Panics
    /// - If `matches` is out of range for either `self` or `other`.
    fn match_indices(&self, other: &Self, matches: &[usize]) -> Self;

    /// Return a new *binary relation* resulting from applying `matches` between `self` and `other` by the given [`Axis`], using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// # Panics
    /// - If `matches` is out of range for either `self` or `other`.
    fn match_indices_by(&self, other: &Self, matches: &[usize], axis: &Axis) -> Self;

    /// Return the "weight" of a function from `self` to `other` (represented as `matches`).
    ///
    /// Given a function *f* that matches each [`Column`] in one *binary relation* *r1* to a some [`Column`] in the other *binary relation* *r2*, the *weight* of *f* is the largest count of differences seen in any row after matching with *f*, plus the number of any [`Column`]s in *r2* that were not matched.
    ///
    /// So the weight of any function between empty *binary relations* is 0, that of any function to an empty *binary relation* returns the highest row-count of ones in `self`, and similarly for any function from an empty *binary relation* to any `other`.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    ///
    /// # Panics
    /// - If `matches` is out of range for either `self` and `other`.
    fn weight(&self, other: &Self, matches: &[usize]) -> u32;

    /// Return the "weight" of a [`Column`] function from `self` to `other` (represented as `matches`), using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// Given a function *f* that matches each [`Column`] in one *binary relation* *r1* to a some [`Column`] in the other *binary relation* *r2*, the *weight* of *f* is the largest count of differences seen in any row after matching with *f*, plus the number of any [`Column`]s in *r2* that were not matched.
    ///
    /// So the weight of any function between empty *binary relations* is 0, that of any function to an empty *binary relation* returns the highest row-count of ones in `self`, and similarly for any function from an empty *binary relation* to any `other`.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    ///
    /// # Panics
    /// - If `matches` is out of range for either `self` and `other`.
    fn weight_by(&self, other: &Self, matches: &[usize], axis: &Axis) -> u32;

    /// Return the minimum [`Relation::weight()`] of all possible [`Column`] functions from `self` to `other`.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn min_weight(&self, other: &Self) -> u32;

    /// Return the minimum [`Relation::weight()`] of all possible [`Column`] functions from `self` to `other`, using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    fn min_weight_by(&self, other: &Self, axis: &Axis) -> u32;

    /// Return the "distance" between two *binary relations*, using possibly costly [`transpose()`](Relation::transpose()) to convert the *binary relation*'s [`Axis`] if needed.
    ///
    /// The *distance* is defined as the maximum of the minimum *weight* between the *binary relations* in each direction. This is achieved in the direction toward the *binary relation* with the larger number of [`Column`]s, in essence, because no one-for-one column-matching function can cover the all of the [`Column`]s in the destination (not [*surjective*](https://en.wikipedia.org/wiki/Surjective_function)), guaranteeing a minimum penalty.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    ///
    /// # Example
    ///
    fn distance_by(&self, other: &Self, axis: &Axis) -> u32;

    /// Return the "distance" between two *binary relations*.
    ///
    /// The *distance* is defined as the maximum of the minimum *weight* between the *binary relations* in each direction. This is achieved in the direction toward the *binary relation* with the larger number of [`Column`]s, in essence, because no one-for-one column-matching function can cover the all of the [`Column`]s in the destination (not [*surjective*](https://en.wikipedia.org/wiki/Surjective_function)), guaranteeing a minimum penalty.
    ///
    /// See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
    ///
    /// # Example
    ///
    fn distance(&self, other: &Self) -> u32;
}

/// A `struct` that implements [`Relation`] as a [`Vec`] of [`BStore`] bit fields oriented along a `major_axis`.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct BRel {
    /// The [`Axis`] of the *binary relation* whose elements are stored consecutively (default: [`Row`](Axis::Row)).
    major_axis: Axis,
    /// The bit field.
    contents: Vec<BStore>
}

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
    pub fn get_contents(&self) -> Vec<BStore> {
        self.contents.clone()
    }

    /// Set the `major_axis` to the given [`Axis`].
    pub fn set_contents(&mut self, contents: &[BStore]) -> &mut Self {
        self.contents = contents.to_owned();
        self
    }

    /// Sort the [`BStore`]s in `contents` lexicographically by `major_axis` and `bits`.
    pub fn sort(&mut self) -> &mut Self {
        self.contents[..].sort();
        self
    }

}

/// An `enum` of the two axes of a *binary relation*.
#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Axis {
    Column,
    #[default] Row,
}

impl fmt::Display for Axis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            Axis::Column => "Column",
            Axis::Row => "Row"
        })
    }
}

impl Relation for BRel {
    fn new() -> Self {
        Self::new()
    }

    fn is_empty(&self) -> bool {
        // self.contents.iter().all(|x| x.count_ones() == 0)
        self.get_contents().len() == 0
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

    fn is_zero(&self) -> bool {
        !self.is_empty() && self.contents.iter().all(|x| x.count_ones() == 0)
    }

    fn get_row_count(&self) -> usize {
        match self.major_axis {
            Axis::Row => self.contents.len(),
            Axis::Column =>
                if self.contents.is_empty() {
                    0
                } else {
                    self.contents[0].get_bit_length()
                }
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
                };
                Ok(bits)
            },
            Axis::Row =>
                if idx < self.get_row_count() {
                    Ok(self.contents[idx].get_bits(0..self.contents[idx].get_bit_length())?)
                } else {
                    Err("out of bounds for BRel")
                }
        }
    }

    fn get_col(&self, idx: usize) -> Result<Vec<bool>, &'static str> {
        match self.major_axis {
            Axis::Column =>
                if idx < self.get_col_count() {
                    Ok(self.contents[idx].get_bits(0..self.contents[idx].get_bit_length())?)
                } else {
                    Err("out of bounds for BRel")
                },
            Axis::Row => {
                let mut bits = vec![];
                for c in self.contents[..].iter() {
                        bits.push(c.get_bit(idx)?)
                    };
                Ok(bits)
            }
        }
    }

    fn set_row(&mut self, idx: usize, row: Vec<bool>) -> Result<&mut Self, &'static str> {
        match self.major_axis {
            Axis::Column => {
                for (i, &v) in row.iter().enumerate() {
                    self.contents[i].set_bit(idx, v)?;
                };
                Ok(self)
            },
            Axis::Row =>
                if idx < self.get_row_count() {
                    self.contents[idx] = BStore::from(row);
                    BStore::normalize(&self.contents);
                    Ok(self)
                } else {
                    Err("out of bounds for BRel")
                }
        }
    }

    fn set_col(&mut self, idx: usize, col: Vec<bool>) -> Result<&mut Self, &'static str> {
        match self.major_axis {
            Axis::Column =>
                if idx < self.get_col_count() {
                    self.contents[idx] = BStore::from(col);
                    BStore::normalize(&self.contents);
                    Ok(self)
                } else {
                    Err("out of bounds for BRel")
                },
            Axis::Row => {
                    for (i, &v) in col.iter().enumerate() {
                        self.contents[i].set_bit(idx, v)?;
                    }
                    Ok(self)
            }
        }
    }

    fn get_cell(&self, row: usize, col: usize) -> Result<bool, &'static str> {
        match self.major_axis {
            Axis::Column =>
                if row < self.get_row_count() {
                    Ok(self.get_col(col)?[row])
                } else {
                    Err("out of bounds for BStore")
                },
            Axis::Row =>
                if col < self.get_col_count() {
                    Ok(self.get_row(row)?[col])
                } else {
                    Err("out of bounds for BStore")
                }
        }
    }

    fn set_cell(&mut self, row: usize, col: usize, value: bool) -> Result<&mut Self, &'static str> {
        match self.major_axis {
            Axis::Column => if col < self.get_col_count() {
                self.contents[col].set_bit(row, value)?;
                Ok(self)
            } else {
                Err("out of bounds for BRel")
            },
            Axis::Row => if row < self.get_row_count() {
                self.contents[row].set_bit(col, value)?;
                Ok(self)
            } else {
                Err("out of bounds for BRel")
            }
        }
    }

    fn djgroup_by(&self, axis: &Axis) -> DJGrouping {
        if *axis == self.major_axis {
            self.djgroup()
        } else {
            DJGrouping {
                relation: self,
                partition: self.transpose().djgroup().partition
            }
        }
    }

    fn djgroup(&self) -> DJGrouping {
        // Checks all [`BStore`]s in `contents` v. all groups:
        // - for each `contents[i]` first check overlap with all groups `res[j]`
        // -- if overlaps a `res[j]`, then expand it and check remaining groups `res[j+1..]`
        // -- if no overlaps, then create a new group `res[_]
        // - repeat checking for remaining `contents[i+1..]`
        if self.is_empty() {
            DJGrouping {
                relation: self,
                partition: vec![],
            }
        } else {
            let mut res: Vec<DJGroup> = vec![DJGroup {
                max: self.contents[0].clone(),
                indices: vec![0],
            }];
            for i in 1..self.contents.len() {
                let bs = &self.contents[i];
                let mut new_group = true;
                let mut expanded: Option<usize> = None;
                for j in 0..res.len() {
                    match expanded {
                        // -- haven't yet found an overlapping group res[j] to expand: this one?
                        None => {
                            let isdisjnt = (res[j].max.clone() & bs.clone()).count_ones() == 0;
                            if !isdisjnt {
                                // expand res[j] and save the index
                                res[j].indices.push(i);
                                res[j].max = res[j].max.clone() | (*bs).clone();
                                expanded = Some(j);
                                new_group = false;
                            }
                        }
                        // -- have expanded group res[idx]: combine it with any other groups?
                        Some(idx) => {
                            let isdisjnt = (res[idx].max.clone() & res[j].max.clone()).count_ones() == 0;

                            if !isdisjnt {
                                // drain this res[j]'s indices
                                let mut resj_indices: Vec<usize> =
                                    res[j].indices.drain(..).collect();
                                // add them to res[idx]'s indices
                                res[idx].indices.append(&mut resj_indices);
                                // update res[idx].max
                                res[idx].max = res[idx].max.clone() | res[j].max.clone();
                            }
                        }
                    }
                }
                // -- disjoint from all groups: create a new group for bs
                if new_group {
                    res.push(DJGroup {
                        max: bs.clone(),
                        indices: vec![i],
                    });
                }
            }
            res.sort_unstable_by(|a, b| a.indices.len().cmp(&b.indices.len()));
            DJGrouping {
                relation: self,
                partition: res,
            }
        }
    }

    fn kappa_by(&self, max_count: Option<usize>, axis: &Axis) -> usize {
        if axis == &self.major_axis {
            self.kappa(max_count)
        } else {
            self.transpose().kappa(max_count)
        }
    }

    fn kappa(&self, max_count: Option<usize>) -> usize {
        // NB: `Rust` vectors are base 0 rather than `lua`'s base 1.
        if self.is_empty() {
            0
        } else {
            let xgs = self.djgroup().partition;
            let mut blockcounts: Vec<usize> = xgs.iter().map(|x| x.indices.len()).collect();
            blockcounts.sort();
            let mut bc_sum = 0;
            let blocksums: Vec<usize> = blockcounts
                .iter()
                .map(|x| {
                    bc_sum += x;
                    bc_sum
                })
                .collect();
            let cap = match max_count {
                None => self.contents.len(),
                Some(n) => self.contents.len().min(n),
            };
            let mut m = 0;

            if blocksums[0] <= cap {
                while m < blocksums.len() && blocksums[m] <= cap {
                    m += 1
                }
            }
            if blocksums.len() == 1 {
                0
            } else if cap >= self.contents.len() || blocksums[m - 1] + blockcounts[m - 1] > cap {
                blocksums[m - 2]
            } else {
                blocksums[m - 1]
            }
        }
    }

    fn rel_dist_bound_by(&self, other: &Self, axis: &Axis) -> usize {
        if axis == &self.major_axis {
            self.rel_dist_bound(other)
        } else {
            self.transpose().rel_dist_bound(other)
        }
    }

    fn rel_dist_bound(&self, other: &Self) -> usize {
        // NB: `Rust` vectors are base 0 rather than `lua`'s base 1.
        println!("rel1:\n{:b}\n", self);
        println!("rel2:\n{:b}\n", other);

        let rel1_count = self.contents.len();
        let rel2_count = other.contents.len();
        let delta12 = self.clone() - (*other).clone();
        let delta21 = other.clone() - (*self).clone();

        println!("delta12:\n{:b}\n", delta12);
        println!("delta21:\n{:b}\n", delta21);

        let delta12_count = delta12.contents.len();
        let delta21_count = delta21.contents.len();
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

        rel1_count.max(rel2_count)
            - (rel1_count - delta12_count + kappa12).min(rel2_count - delta21_count + kappa21)
    }

    fn match_indices_by(&self, other: &Self, matches: &[usize], axis: &Axis) -> Self {
        if axis == &self.major_axis {
            self.match_indices(other, matches)
        } else {
            self.transpose().match_indices(other, matches)
        }
    }

    fn match_indices(&self, other: &Self, matches: &[usize]) -> Self {
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        if self_empty & other_empty {
            println!("match_indices both empty");
            self.clone()
        } else if self_empty {
            println!("match_indices self_empty");
            BRel::zero(other.get_row_count(), other.get_col_count(), other.get_major_axis()).match_indices(other, matches)
        } else if other_empty {
            println!("match_indices other_empty");
            self.match_indices(&BRel::zero(self.get_row_count(), self.get_col_count(), self.get_major_axis()), matches)
        } else {
            println!("match_indices neither empty");
            assert!(matches.len() <= self.contents.len(), "BRel::match_indices() Invalid match: match.len() {} > self.contents.len() {}", matches.len(), self.contents.len());
            assert!(other.contents.len() >= *matches.iter().max().unwrap(), "BRel::match_indices() Invalid match: max matches[..] > self.contents.len() {}", other.contents.len());

            let mut res = self.clone();
            for (i, _) in matches.iter().enumerate() {
                res.contents[i] = other.contents[matches[i]].clone()
            }
            res
        }
    }

    fn weight_by(&self, other: &Self, matches: &[usize], axis: &Axis) -> u32 {
        if axis == &self.major_axis {
            self.weight(other, matches)
        } else {
            self.transpose().weight(other, matches)
        }
    }

    fn weight(&self, other: &Self, matches: &[usize]) -> u32 {
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        if self_empty & other_empty {
            println!("weight both empty\n");
            0
        } else if self_empty {
            let other_len = other.contents.len();
            println!("weight self_empty\n");
            *other
                .contents
                .iter()
                .fold(vec![0_u32; other_len], |mut counts, bs| {
                    for (i, count) in counts.iter_mut().enumerate().take(other_len) {
                        // SAFETY: counts.len() = bs.len() => i can't go out of bounds.
                        if bs.get_bit(i).unwrap() {
                            *count += 1
                        }
                    }
                    counts
                })
                .iter()
                .max()
                .unwrap()
        } else if other_empty {
            println!("weight other_empty\n");
            let self_len = self.contents.len();
            *self
                .contents
                .iter()
                .fold(vec![0_u32; self_len], |mut counts, bs| {
                    for (i, count) in counts.iter_mut().enumerate().take(self_len) {
                        // SAFETY: counts.len() = bs.len() => i can't go out of bounds.
                        if bs.get_bit(i).unwrap() {
                            *count += 1
                        }
                    }
                    counts
                })
                .iter()
                .max()
                .unwrap()
        } else {
            println!("weight neither empty");
            let self_len = self.contents.len();
            let used_count = matches
            .iter()
            .fold(vec![0u32; other.contents.len()], |mut acc, m| {
                acc[*m] |= 1;
                acc
            })
            .iter()
            .sum::<u32>();
            let penalty = other.contents.len() as u32 - used_count;
            let image = self.match_indices(other, matches);
            let bitxor_image = image.clone().bitxor(self.clone());
            let max_diff = *bitxor_image
                .contents
                .iter()
                .fold(vec![0_u32; self_len], |mut counts, bs| {
                    for (i, count) in counts.iter_mut().enumerate().take(self_len) {
                        // SAFETY: counts.len() = bs.len() => i can't go out of bounds.
                        if bs.get_bit(i).unwrap() {
                            *count += 1
                        }
                    }
                    counts
                })
                .iter()
                .max()
                .unwrap();
            println!(
                "matches:{:?}\nimage:\n{:b}\nbitxor_image:\n{:b}\npenalty:{} max_diff:{} weight:{}\n",
                matches, image, bitxor_image, penalty, max_diff, penalty + max_diff
            );
            penalty + max_diff
        }
    }

    fn min_weight_by(&self, other: &Self, axis: &Axis) -> u32 {
        if axis == &self.major_axis {
            self.min_weight(other)
        } else {
            self.transpose().min_weight(other)
        }
    }

    fn min_weight(&self, other: &Self) -> u32 {
        let self_len = self.contents.len();
        let other_len = other.contents.len();

        if self.is_empty() || other.is_empty() {
            // weight() will ignore matches
            self.weight(other, &[0])
        } else {
            // initialize worst case
            let mut res = other_len as u32 * other.get_row_count() as u32;

            // check all matches
            for m in Matches::new(self_len, other_len) {
                let w = self.weight(other, &m);
                println!("min_weight:{} with weight:{} for match:{:?}", res, w, m);
                if w < res {
                    res = w;
                }
            }
            res
        }
    }

    fn distance_by(&self, other: &Self, axis: &Axis) -> u32 {
        if axis == &self.major_axis {
            self.distance(other)
        } else {
            self.transpose().distance(other)
        }
    }

    fn distance(&self, other: &Self) -> u32 {
        let from_len = if self.is_empty() {
            0
        } else {
            self.contents.len()
        };
        let to_len = if other.is_empty() {
            0
        } else {
            other.contents.len()
        };

        if from_len <= to_len {
            self.min_weight(other)
        } else {
            other.min_weight(self)
        }
    }

    fn transpose(&self) -> Self {
        let new_row_count = self.get_col_count();
        let new_col_count = self.get_row_count();
        let mut new = Self::zero(new_row_count, new_col_count, self.major_axis);
        for r in 0..new_row_count {
            for c in 0..new_col_count {
                new.set_cell(r, c, self.get_cell(c, r).unwrap()).unwrap();
            }
        }
        BRel { major_axis: self.major_axis, contents: new.contents }
    }
}

impl From<Vec<BStore>> for BRel {
    fn from(bitstores: Vec<BStore>) -> Self {
        BRel {
            major_axis: BRel::default().major_axis,
            contents: BStore::normalize(&bitstores) }
    }
}

impl Index<usize> for BRel {
    type Output = BStore;

    fn index(&self, index: usize) -> &Self::Output {
        &self.contents[index]
    }
}

impl IndexMut<usize> for BRel {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.contents[index]
    }
}

impl fmt::Binary for BRel {
    /// Display the [`BRel`] line-by-line, as big-endian binary of the `major_axis`, *i.e.* row-by-row for [column-major-axis](Axis::Column) and column-by-column for [column-major-axis](Axis::Column).
    ///
    /// **NB**: For [column-major-axis](Axis::Column), the result appears rotated by 90&deg; compared to the standard binary representation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::from("[");
        // if !self.is_empty() {
        if !self.get_contents().len() > 0 {
            match self.major_axis {
                Axis::Column => {
                    let mut rows = (0..self.get_row_count())
                        .map(|x| Row::from(self.get_row(x).unwrap()))
                        .collect_vec();
                    rows = BitStore::normalize(&rows);
                    write!(s, "{:b}", rows[0]).unwrap();
                    for r in rows.iter().skip(1) {
                        write!(s, "\n {:b}", r).unwrap();
                    }
                },
                Axis::Row => {
                    write!(s, "{:b}", self[0]).unwrap();
                    for r in 1..self.get_row_count() {
                        write!(s, "\n {:b}", self[r]).unwrap();
                    }
                }
            };
        }
        s.push(']');
        write!(f, "{s}")
    }
}

// Use a macro to generate the four logical / bit operations on [`BRel`]s.
macro_rules! impl_brel_bitops {
    ( Not $( , $func:tt, $op:tt )? ) => {
        impl Not for BRel {
            type Output = Self;
            fn not(self) -> Self::Output {
                BRel {
                    major_axis: self.major_axis,
                    contents: self.contents.iter().map(|x| !x.clone()).collect(),
                }
            }
        }
    };
    ( $trait:tt, $func:tt, $op:tt ) => {
        impl $trait for BRel {
            type Output = Self;
            fn $func(self, rhs: Self) -> Self::Output {
                if self.is_empty() {
                    self
                } else if rhs.is_empty() {
                    rhs
                } else {
                    assert!(self.major_axis == rhs.major_axis, "BRel::$func requires non-empty `BRel`s to have same major_axis but: {} != {}", self.major_axis, rhs.major_axis);
                    BRel {
                        major_axis: self.major_axis,
                        contents: zip(self.contents, rhs.contents)
                            .map(|(s, r)| s $op r)
                            .collect::<Vec<BStore>>(),
                    }
                }
            }
        }
    };
}
impl_brel_bitops!(Not, not, !);
impl_brel_bitops!(BitAnd, bitand, &);
impl_brel_bitops!(BitOr, bitor, |);
impl_brel_bitops!(BitXor, bitxor, ^);

impl Add for BRel {
    type Output = Self;

    /// Multiset sum: disjoint union, *i.e.*, combine all [`BStore`]s in both [`BRel`]s.
    ///
    /// For more on multiset operations, see <https://en.wikipedia.org/wiki/Multiset#Basic_properties_and_operations>.
    ///
    /// # Panics
    /// - if the two [`BRel`]s don't have the same `major_axis`.
    fn add(self, other: Self) -> Self::Output {
        assert_eq!(
            self.major_axis, other.major_axis,
            "BRel::add() requires non-empty `BRel`s to have same `major_axis` but {} != {}",
            self.major_axis, other.major_axis
        );
        let mut new = self.contents.clone();
        new.extend_from_slice(&other.contents[..]);
        BRel {
            major_axis: self.major_axis,
            contents: new,
        }
    }
}

impl Sub for BRel {
    type Output = Self;

    /// Multiset difference: one-for-one remove from `self` each [`BStore`] that is found in `other`.
    ///
    /// For more on multiset operations, see <https://en.wikipedia.org/wiki/Multiset#Basic_properties_and_operations>.
    ///
    /// # Panics
    /// - if the two [`BRel`]s don't have the same `major_axis`.
    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(
            self.major_axis, other.major_axis,
            "BRel::sub() requires non-empty `BRel`s to have same `major_axis` but {} != {}",
            self.major_axis, other.major_axis
        );
        let mut new = vec![];
        let mut cut_self = vec![false; self.contents.len()];
        let mut used_other = vec![false; other.contents.len()];
        for (i, sc) in self.contents.iter().enumerate() {
            for (j, oc) in other.contents.iter().enumerate() {
                if !cut_self[i] && !used_other[j] && *sc == *oc {
                    cut_self[i] = true;
                    used_other[j] = true;
                    print!("cut{}{} ", i, j);
                    break;
                }
            }
        }
        for (i, col) in self.contents.iter().enumerate() {
            if !cut_self[i] {
                new.push(col.clone())
            }
        }
        BRel {
            major_axis: self.major_axis,
            contents: new,
        }
    }
}

impl_bitstore!(Column, "A `struct` to represent a *column* in a *binary relation* as a [`BitStore`].");

impl From<Column> for BStore {
    fn from(col: Column) -> Self {
        let mut res = BStore::new();
        let len = col.get_bit_length();
        res.set_capacity(len).unwrap();
        res.set_bit_length(len).unwrap();
        res.set_raw_bits(col.get_raw_bits());
        res
    }
}

impl From<BStore> for Column {
    fn from(bs: BStore) -> Self {
        let mut res = Column::new();
        let len = bs.get_bit_length();
        res.set_capacity(len).unwrap();
        res.set_bit_length(len).unwrap();
        res.set_raw_bits(bs.get_raw_bits());
        res
    }
}

impl From<Vec<Column>> for BRel {
    fn from(columns: Vec<Column>) -> Self {
        BRel {
            major_axis: Axis::Column,
            contents: columns.into_iter().map(BStore::from).collect_vec() }
    }
}

impl_bitstore!(Row, "A `struct` to represent a *row* in a *binary relation* as a [`BitStore`].");

impl From<Row> for BStore {
    fn from(col: Row) -> Self {
        let mut res = BStore::new();
        let len = col.get_bit_length();
        res.set_capacity(len).unwrap();
        res.set_bit_length(len).unwrap();
        res.set_raw_bits(col.get_raw_bits());
        res
    }
}

impl From<BStore> for Row {
    fn from(bs: BStore) -> Self {
        let mut res = Row::new();
        let len = bs.get_bit_length();
        res.set_capacity(len).unwrap();
        res.set_bit_length(len).unwrap();
        res.set_raw_bits(bs.get_raw_bits());
        res
    }
}

impl From<Vec<Row>> for BRel {
    fn from(columns: Vec<Row>) -> Self {
        BRel {
            major_axis: Axis::Row,
            contents: columns.into_iter().map(BStore::from).collect_vec() }
    }
}

impl IntoIterator for BRel {
    type Item = BStore;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.contents.into_iter()
    }
}

impl FromIterator<BStore> for BRel {
    fn from_iter<T: IntoIterator<Item = BStore>>(iter: T) -> Self {
        let mut res = BRel::new();
        res.set_contents(&iter.into_iter().collect::<Vec<BStore>>());
        res
    }
}

/// Represents the partition of a *binary relation* [`BRel`] into [`DJGroup`]s.
///
/// A [`BRel`]'s [`BStore`]s can be partitioned into a collection of [`DJGroup`]s, each collecting [`BStore`]s that are *each* not disjoint (*i.e.*, share `true` at some bit) with *some* other member of the [`DJGroup`], but *all* are disjoint from *all* other [`BStore`]s *not* in that [`DJGroup`]. The partition can be with respect to either [`Row`](Axis::Row) or [`Column`](Axis::Column).
///
/// NB: Because a partition makes no sense away from its [`BRel`], the [`DJGrouping`] inherits the [lifetime](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) of its [`BRel`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DJGrouping<'a> {
    relation: &'a BRel,
    pub partition: Vec<DJGroup>,
}

impl DJGrouping<'_> {
    /// Return a [`DJGrouping`] for the given *binary relation*.
    pub fn new(rel: &BRel) -> DJGrouping {
        rel.djgroup()
    }
}

impl fmt::Display for DJGrouping<'_> {
    /// Display the partitioned *binary relation* as a binary matrix of [`DJGroup`]s separated by a lines. The [`DJGroup`]s (and spacer lines) will be horizontal if the `major_axis` is [`Row`](Axis::Row) and vertical if it is [`Column`](Axis::Column).
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rel = self.relation;
        let xgs = &self.partition;
        let mut s = String::new();

        if !self.partition.is_empty() {
            match rel.get_major_axis() {
                Axis::Column =>
                    for r in 0..rel.get_row_count() {
                        for c in 0..xgs[0].indices.len() {
                            if rel[xgs[0].indices[c]][r] {
                                s.push('1')
                            } else {
                                s.push('0')
                            };
                        };
                        for xg in xgs.iter().skip(1) {
                            s.push_str(" | ");
                            for c in 0..xg.indices.len() {
                                if rel[xg.indices[c]][r] {
                                    s.push('1')
                                } else {
                                    s.push('0')
                                };
                            }
                        };
                        s.push('\n')
                    },
                Axis::Row => {
                    for r in 0..xgs[0].indices.len() {
                        for c in 0..rel.get_col_count() {
                            if rel[xgs[0].indices[r]][c] {
                                s.push('1')
                            } else {
                                s.push('0')
                            };
                        };
                        s.push('\n');
                    };
                    for xg in xgs.iter().skip(1) {
                        s.push_str(&"-".repeat(rel.get_col_count()));
                        s.push('\n');
                        for r in 0..xg.indices.len() {
                            for c in 0..rel.get_col_count() {
                                if rel[xg.indices[r]][c] {
                                    s.push('1')
                                } else {
                                    s.push('0')
                                };
                            };
                            s.push('\n');
                        };
                    };
                }
            }
        };
        write!(f, "{s}")
    }
}

/// Represents a *disjoint-group* of [`BStore`]s that are disjoint (*i.e.*, share `true` at some bit) with all other [`BStore`]s in the *binary relation*.
///
/// Each [`DJGroup`] collects indices in the *binary relation's* to [`BStore`]s that share a relation (`true`) with at least one other member of the [`DJGroup`].
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DJGroup {
    max: BStore,
    indices: Vec<usize>,
}

/// Return a new empty [`DJGroup`].
impl DJGroup {
    pub fn new() -> DJGroup {
        Default::default()
    }
}

impl Index<usize> for DJGroup {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.indices[index]
    }
}

impl IndexMut<usize> for DJGroup {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.indices[index]
    }
}

/// Represents a *function* between *binary relations* as an [`Iterator`] of matches between indices into one their dimensions, *i.e*, into their [`Column`](Axis::Column)s or [`Row`](Axis::Row)s.
///
/// Each call to [`next()`](Iterator::next()) returns a new [`Vec`] of length `count1` selected from `0..count2`, with repetition possible. The iterator terminates after `count2.pow(count1)` variations.
///
/// Example
/// ```
/// use relmetric::relation::Matches;
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
    /// Pairs source indices with target indices.
    matches: Vec<usize>,
    /// Count of indices in source.
    count1: usize,
    /// Count of indices in target.
    count2: usize,
    /// Iterator's current index.
    current: usize,
}

impl Matches {
    pub fn new(count1: usize, count2: usize) -> Matches {
        Matches {
            matches: vec![],
            count1,
            count2,
            current: 0,
        }
    }
}

impl Iterator for Matches {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        println!("{:?}", self);
        if self.matches.is_empty() {
            self.matches = vec![0; self.count1];
            self.current = 0;
            Some(self.matches.clone())
        } else if self.matches[self.current] + 1 < self.count2 {
            self.matches[self.current] += 1;
            Some(self.matches.clone())
        } else {
            self.current += 1;
            while self.current < self.count1 && self.matches[self.current] + 1 == self.count2 {
                self.current += 1
            }
            if self.current == self.count1 {
                None
            } else {
                self.matches[self.current] += 1;
                for i in 0..self.current {
                    self.matches[i] = 0
                }
                self.matches[0] = 0;
                self.current = 0;
                Some(self.matches.clone())
            }
        }
    }
}

// Unit Tests
mod tests {
    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use crate::bitstore::BStore;
    // #[allow(unused_imports)]
    // use itertools::sorted;

    #[test]
    fn brel_new_works() {
        let br = BRel::new();
        assert_eq!(br, BRel { major_axis: Axis::Row, contents: vec![]});
        assert_eq!(br.get_major_axis(), BRel::default().get_major_axis());
        assert_eq!(br.get_contents(), BRel::default().get_contents());
    }

    #[test]
    fn brel_index_works() {
        let br = BRel::from(vec![BStore::from(vec![0b01010101u8]), BStore::from(vec![0b01010101u8])]);
        assert_eq!(br[0], BStore::from(vec![0b01010101u8]));
        assert_eq!(br[0][0], false);
        assert_eq!(br[1][1], true);
    }

    #[test]
    fn brel_binary_works() {
        assert_eq!(format!("{:b}", BRel::from(vec![BStore::from(vec![0b01010101u8])])), "[[01010101]]".to_string());
    }

    #[test]
    fn brel_bitnot_works() {
        let bs1 = BStore::from(vec![0b00010101u8, 0b10100000u8]);
        let bs2 = BStore::from(vec![0b10110000u8, 0b00000101u8]);
        let br = BRel { major_axis: Axis::Row, contents: vec![bs1.clone(), bs2.clone()] };
        let not_br = BRel { major_axis: Axis::Row, contents: vec![!bs1.clone(), !bs2.clone()]};
        assert_eq!(!br.clone(), not_br, "br:{:b} not_br:{:b}", br, not_br);
    }

    #[test]
    fn brel_bitand_works() {
        let bs1 = BStore::from(vec![0b00010101u8, 0b10100000u8]);
        let bs2 = BStore::from(vec![0b10110000u8, 0b00000101u8]);
        let br1 = BRel { major_axis: Axis::Row, contents: vec![bs1.clone(), bs2.clone()] };
        let br2 = BRel { major_axis: Axis::Row, contents: vec![bs2.clone(), bs1.clone()] };
        let want = BRel { major_axis: Axis::Row, contents: vec![bs1.clone() & bs2.clone(), bs2.clone() & bs1.clone()]};
        assert_eq!(br1.clone() & br2.clone(), want, "br1:{:b} br2:{:b} want:{:b}", br1, br2, want);
    }

    #[test]
    fn brel_bitor_works() {
        let bs1 = BStore::from(vec![0b00010101u8, 0b10100000u8]);
        let bs2 = BStore::from(vec![0b10110000u8, 0b00000101u8]);
        let br1 = BRel { major_axis: Axis::Row, contents: vec![bs1.clone(), bs2.clone()] };
        let br2 = BRel { major_axis: Axis::Row, contents: vec![bs2.clone(), bs1.clone()] };
        let want = BRel { major_axis: Axis::Row, contents: vec![bs1.clone() | bs2.clone(), bs2.clone() | bs1.clone()]};
        assert_eq!(br1.clone() | br2.clone(), want, "br1:{:b} br2:{:b} want:{:b}", br1, br2, want);
    }

    #[test]
    fn brel_bitxor_works() {
        let bs1 = BStore::from(vec![0b00010101u8, 0b10100000u8]);
        let bs2 = BStore::from(vec![0b10110000u8, 0b00000101u8]);
        let br1 = BRel { major_axis: Axis::Row, contents: vec![bs1.clone(), bs2.clone()] };
        let br2 = BRel { major_axis: Axis::Row, contents: vec![bs2.clone(), bs1.clone()] };
        let want = BRel { major_axis: Axis::Row, contents: vec![bs1.clone() | bs2.clone(), bs2.clone() | bs1.clone()]};
        assert_eq!(br1.clone() | br2.clone(), want, "br1:{:b} br2:{:b} want:{:b}", br1, br2, want);
    }

    #[test]
    fn brel_sub_works() {
        let r1 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x0000u16, 0x0000u16]),
            BStore::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let r2 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x0000u16, 0x0000u16]),
        ]);
        let r3 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let mut res = r1.clone() - r2.clone();
        assert_eq!(
            res, r3,
            "\nBRel::sub() fails for\n lhs:{:b}\n rhs:{:b}\nshould be {:b}\ngot       {:b}",
            r1, r2, r3, res
        );
        res = res - r3.clone();
        assert!(
            res.is_empty(),
            "\nBRel::sub() fails for\n lhs:{:b}\n rhs:{:b}\nshould be {:b}\ngot       {:b}",
            res,
            r3,
            BRel::new(),
            res
        );
    }

    #[test]
    fn brel_add_works() {
        let mut r1 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x0000u16, 0x0000u16]),
            BStore::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let r2 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x0000u16, 0x0000u16]),
        ]);
        let r3 = BRel::from(vec![
            BStore::from(vec![0x3000u16, 0x000fu16]),
            BStore::from(vec![0x100fu16, 0x0f3fu16]),
        ]);
        let mut res = r2.clone() + r3.clone();
        res.sort();
        r1.sort();
        assert_eq!(
            res, r1,
            "\nBRel::add() fails for\n lhs:\n{:b}\n rhs:\n{:b}\nshould be\n{:b}\ngot\n{:b}",
            r2, r3, r1, res
        );
    }

    #[test]
    fn column_new_works() {
        assert_eq!(Column::new(), Column::from(BStore::new()));
    }

    #[test]
    fn column_from_to_work() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        assert_eq!(Column::from(bs1.clone()), Column::from(bs1.clone()));
        assert_eq!(BStore::from(Column::from(bs1.clone())), bs1.clone());
    }

    #[test]
    fn brel_from_columns_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let br = BRel::from(vec![Column::from(bs1.clone())]);
        assert_eq!(br, BRel { major_axis: Axis::Column, contents: vec![bs1] });
    }

    #[test]
    fn row_new_works() {
        let r = Row::new();
        let bs = BStore::new();
        assert_eq!((r.get_bit_length(), r.get_bits(0..r.get_bit_length())), (bs.get_bit_length(), bs.get_bits(0..bs.get_bit_length())));
    }

    #[test]
    fn row_from_to_work() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        assert_eq!(Row::from(bs1.clone()), Row::from(bs1.clone()));
        assert_eq!(BStore::from(Row::from(bs1.clone())), bs1.clone());
    }

    #[test]
    fn brel_from_rows_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let br = BRel::from(vec![Row::from(bs1.clone())]);
        assert_eq!(br, BRel { major_axis: Axis::Row, contents: vec![bs1] });
    }

    #[test]
    fn reltrait_brel_new_and_is_empty_work() {
        let r1 = BRel::new();
        assert_eq!(r1, BRel { major_axis: Axis::Row, contents: vec![]});
        assert!(r1.is_empty());
    }

    #[test]
    fn reltrait_brel_from_bitstores_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let bsvec = vec![bs1, bs2, bs3];
        let r1 = BRel::from(bsvec.clone());
        assert_eq!(r1, BRel { major_axis: Axis::Row, contents: bsvec});
    }

    #[test]
    fn reltrait_brel_zero_works() {
        assert_eq!(BRel::zero(2, 9, Axis::Column), BRel { major_axis: Axis::Column, contents: vec![BStore::zero(2); 9]});
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
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let r1 = BRel::from(vec![bs2, bs1, bs3]);
        assert_eq!(r1.get_row_count(), 3);
        assert_eq!(BRel::new().get_row_count(), 0);
    }

    #[test]
    fn reltrait_brel_get_col_count_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1, bs3]);
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_col_count(), 3);
        assert_eq!(BRel::new().get_col_count(), 0);
    }

    #[test]
    fn reltrait_brel_get_row_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.get_row(1), bs1.get_bits(0..bs1.get_bit_length()));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_row(0), Ok(vec![false, false, false]));
    }

    #[test]
    fn reltrait_brel_set_row_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.set_row(2, bs1.get_bits(0..bs1.get_bit_length()).unwrap()).unwrap().get_row(2), bs1.get_bits(0..bs1.get_bit_length()));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.set_row(0, vec![true, true, true]).unwrap().get_row(0), Ok(vec![true, true, true]));
    }

    #[test]
    fn reltrait_brel_get_col_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        assert_eq!(r1.get_col(0), Ok(vec![false, false, false]));
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.get_col(1), bs1.get_bits(0..bs1.get_bit_length()));
    }

    #[test]
    fn reltrait_brel_set_col_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let mut r1 = BRel::from(vec![bs2, bs1.clone(), bs3]);
        let r2 = r1.clone();
        assert_eq!(r1.set_col(0, vec![true, true, true]).unwrap().get_col(0), Ok(vec![true, true, true]), "\nset_col({}, {:?}) fails for\n{:b}", 0, vec![true, true, true], r2);
        r1.set_major_axis(&Axis::Column);
        assert_eq!(r1.set_col(2, bs1.get_bits(0..bs1.get_bit_length()).unwrap()).unwrap().get_col(2), bs1.get_bits(0..bs1.get_bit_length()));
    }

    #[test]
    fn reltrait_brel_get_cell_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let r1 = BRel::from(vec![bs1, bs2]);
        assert_eq!(r1.get_cell(0, 2), Ok(true), "\nget_cell({}, {})={} fails for: {:b}", 0, 2, true, r1);
        assert_eq!(r1.get_cell(0, 0), Ok(false), "\nget_cell({}, {})={} fails for: {:b}", 0, 0, false, r1);
        assert!(r1.get_cell(2, 0).is_err());
    }

    #[test]
    fn reltrait_brel_set_cell_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let mut r1 = BRel::from(vec![bs1, bs2]);
        assert_eq!(r1.set_cell(0, 0, true).unwrap().get_cell(0, 0), Ok(true), "\nset_cell({}, {}, {})={} fails for: {:b}", 0, 0, true, true, r1);
        assert_eq!(r1.set_cell(1, 4, false).unwrap().get_cell(1, 4), Ok(false), "\nset_cell({}, {}, {})={} fails for: {:b}", 0, 0, false, false, r1);
        assert!(r1.set_cell(2, 0, true).is_err());
        assert!(r1.set_cell(0, 30, true).is_err());
    }

    #[test]
    fn djgrouping_display_works() {
        let row_br = BRel::from(vec![
            BStore::from(vec![0b0000u8]),
            BStore::from(vec![0b1000u8]),
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b0010u8]),
            BStore::from(vec![0b0010u8]),
            BStore::from(vec![0b0001u8]),
            BStore::from(vec![0b0001u8]),
            BStore::from(vec![0b0001u8]),
            BStore::from(vec![0b0001u8]),
        ]);
        let mut col_br = row_br.clone();
        col_br.set_major_axis(&Axis::Column);
        let row_dgs = row_br.djgroup();
        let row_djgrouping = DJGrouping::new(&row_br);
        let mut res = format!("{}", row_djgrouping);
        let mut want = r#"00000000
--------
00000010
00000010
--------
00001000
00001100
00001100
--------
00000001
00000001
00000001
00000001
"#;
        assert_eq!(
            res, want,
            "r:\n{:b}\nrow_djgrouping:\n{}\nrow_dgs:\n{:?}\n",
            row_br, row_djgrouping, row_dgs
        );
        let col_dgs = col_br.djgroup();
        let col_djgrouping = DJGrouping::new(&col_br);
        res = format!("{}", col_djgrouping);
        want = r#"0 | 00 | 000 | 0000
0 | 00 | 000 | 0000
0 | 00 | 000 | 0000
0 | 00 | 000 | 0000
0 | 00 | 111 | 0000
0 | 00 | 011 | 0000
0 | 11 | 000 | 0000
0 | 00 | 000 | 1111
"#;
        assert_eq!(
            res, want,
            "r:\n{:b}\ncol_djgrouping:\n{}\ncol_dgs:\n{:?}\n",
            col_br, col_djgrouping, col_dgs
        );
}


    #[test]
    fn reltrait_brel_djgroup_works() {
        let c1 = BStore::from(vec![0x3000u16, 0x000fu16]);
        let c2 = BStore::from(vec![0x0000u16, 0x0000u16]);
        let c3 = BStore::from(vec![0x100fu16, 0x0f3fu16]);
        let mut r1 = BRel::from(vec![c1.clone(), c1, c2.clone(), c3.clone()]);
        let mut res = r1.djgroup().partition.len();
        let mut want = 2;
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.contents[2] = c2.clone();
        res = r1.djgroup().partition.len();
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.contents[2] = c3.clone();
        res = r1.djgroup().partition.len();
        want = 1;
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
    }

    #[test]
    fn reltrait_brel_djgroupby_works() {
        let c1 = BStore::from(vec![0x3000u16, 0x000fu16]);
        let c2 = BStore::from(vec![0x0000u16, 0x0000u16]);
        let c3 = BStore::from(vec![0x100fu16, 0x0f3fu16]);
        let mut r1 = BRel::from(vec![c1.clone(), c1, c2.clone(), c3.clone()]);
        r1.set_major_axis(&Axis::Column);
        let mut res = r1.djgroup_by(&Axis::Column).partition.len();
        let mut want = 2;
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.contents[2] = c2.clone();
        res = r1.djgroup().partition.len();
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
        r1.contents[2] = c3.clone();
        res = r1.djgroup().partition.len();
        want = 1;
        assert_eq!(
            res, want,
            "\n\nNumber of DJGroups {} != {} for\n{:?}",
            res, want, r1
        );
    }

    #[test]
    fn reltrait_brel_kappa_works() {
        // "R" of Example 10 in "Metric Comparisons".
        let ex10_r = BRel::from(vec![
            BStore::from(vec![0x0u8]),
            BStore::from(vec![0x08u8]),
            BStore::from(vec![0x0cu8]),
            BStore::from(vec![0x0cu8]),
            BStore::from(vec![0x02u8]),
            BStore::from(vec![0x02u8]),
            BStore::from(vec![0x01u8]),
            BStore::from(vec![0x01u8]),
            BStore::from(vec![0x01u8]),
            BStore::from(vec![0x01u8]),
        ]);
        // "R3" of Example 12 in "Metric Comparisons".
        let ex12_r3 = BRel::from(vec![
            BStore::from(vec![0b1000u8]),
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1100u8]),
        ]);
        // "R4" of Example 13 in "Metric Comparisons".
        let ex13_r4 = BRel::from(vec![
            BStore::from(vec![0b0000u8]),
            BStore::from(vec![0b1000u8]),
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1100u8]),
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
    fn reltrait_brel_rel_dist_bound_works() {
        // "R1" of Example 18 in "Metric Comparisons".
        let ex18_r1 = BRel::from(vec![
            BStore::from(vec![0b10111u8]),
            BStore::from(vec![0b01111u8]),
            BStore::from(vec![0b10111u8]),
            BStore::from(vec![0b11001u8]),
            BStore::from(vec![0b00111u8]),
            BStore::from(vec![0b00000u8]),
            BStore::from(vec![0b10001u8]),
            BStore::from(vec![0b11001u8]),
            BStore::from(vec![0b01001u8]),
            BStore::from(vec![0b11101u8]),
        ]);
        // "R2" of Example 18 in "Metric Comparisons".
        let ex18_r2 = BRel::from(vec![
            BStore::from(vec![0b00100u8]),
            BStore::from(vec![0b00010u8]),
            BStore::from(vec![0b11100u8]),
            BStore::from(vec![0b11110u8]),
            BStore::from(vec![0b01000u8]),
            BStore::from(vec![0b11101u8]),
            BStore::from(vec![0b10100u8]),
            BStore::from(vec![0b11010u8]),
            BStore::from(vec![0b01111u8]),
            BStore::from(vec![0b10101u8]),
        ]);
        // "R1" of Example 19 in "Metric Comparisons".
        let ex19_r1 = BRel::from(vec![
            BStore::from(vec![0b00000u8]),
            BStore::from(vec![0b00101u8]),
            BStore::from(vec![0b11000u8]),
            BStore::from(vec![0b00100u8]),
            BStore::from(vec![0b01000u8]),
            BStore::from(vec![0b10000u8]),
            BStore::from(vec![0b00101u8]),
            BStore::from(vec![0b00000u8]),
            BStore::from(vec![0b00100u8]),
            BStore::from(vec![0b11000u8]),
        ]);
        // "R2" of Example 19 in "Metric Comparisons".
        let ex19_r2 = BRel::from(vec![
            BStore::from(vec![0b00000u8]),
            BStore::from(vec![0b00101u8]),
            BStore::from(vec![0b11000u8]),
            BStore::from(vec![0b01100u8]),
            BStore::from(vec![0b01000u8]),
            BStore::from(vec![0b10000u8]),
            BStore::from(vec![0b00001u8]),
            BStore::from(vec![0b00001u8]),
            BStore::from(vec![0b00100u8]),
            BStore::from(vec![0b10010u8]),
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
    fn reltrait_brel_match_indices_works() {
        let r1 = BRel::from(vec![
            BStore::from(vec![0b1000u8]),
            BStore::from(vec![0b1001u8]),
        ]);
        let r2 = BRel::from(vec![
            BStore::from(vec![0b0000u8]),
            BStore::from(vec![0b1000u8]),
        ]);
        let matches = vec![1usize, 0usize];
        let res = r1.match_indices(&r2, &matches);
        let want = BRel::from(vec![
            BStore::from(vec![0b1000u8]),
            BStore::from(vec![0b0000u8]),
        ]);
        assert_eq!(res, want, "\nRelation::match_indices fails with matches[{:?}] for \n{:b} \n{:b}\nwanted {:b}\ngot    {:b}\n", matches, r1, r2, want, res);

        let ex1_r1 = BRel { major_axis: Axis::Column, contents: vec![BStore::from_indices(vec![1])] };
        let ex1_r2 = BRel::new();
        let ex1_matches = vec![0];
        let ex1_res = ex1_r1.match_indices(&ex1_r2, &ex1_matches);
        let ex1_want = BRel::zero(1, 1, Axis::Column);
        assert_eq!(res, want, "\nRelation::match_indices fails Ex 1 with matches[{:?}] for\n{:b}\n{:b}\nwanted {:b}\ngot    {:b}\n", ex1_matches, ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = BRel::from(vec![
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1010u8]),
            BStore::from(vec![0b1011u8]),
            BStore::from(vec![0b0011u8]),
        ]);
        let ex2_r2 = BRel::from(vec![
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1011u8]),
            BStore::from(vec![0b0101u8]),
        ]);
        let ex2_matches12 = vec![0, 1, 1, 2];
        let ex2_matches21 = vec![1, 2, 0];
        let ex2_res12 = ex2_r1.match_indices(&ex2_r2, &ex2_matches12);
        let ex2_want12 = BRel::from(vec![
            BStore::from(vec![0b1100u8]),
            BStore::from(vec![0b1011u8]),
            BStore::from(vec![0b1011u8]),
            BStore::from(vec![0b0101u8]),
        ]);
        assert_eq!(ex2_res12, ex2_want12, "\nRelation::match_indices fails Ex 2 with matches[{:?}] for\n{:b}\n{:b}\nwanted {:b}\ngot    {:b}\n", ex2_matches12, ex2_r1, ex2_r2, ex2_want12, ex2_res12);

        let ex2_res21 = ex2_r2.match_indices(&ex2_r1, &ex2_matches21);
        let ex2_want21 = BRel::from(vec![
            BStore::from(vec![0b1010u8]),
            BStore::from(vec![0b1011u8]),
            BStore::from(vec![0b1100u8]),
        ]);
        assert_eq!(ex2_res21, ex2_want21, "\nRelation::match_indices fails Ex 2 with matches[{:?}] for\n{:b}\n{:b}\nwanted {:b}\ngot    {:b}\n", ex2_matches21, ex2_r2, ex2_r1, ex2_want21, ex2_res21);
    }

    #[test]
    fn reltrait_brel_weight_works() {
        let ex1_r1 = BRel {
            major_axis: Axis::Row,
            contents: vec![BStore::from_indices(vec![0])]
        };
        let ex1_r2 = BRel::new();
        let ex1_matches = vec![0];
        let ex1_res = ex1_r1.weight(&ex1_r2, &ex1_matches);
        let ex1_want = 1;
        assert_eq!(ex1_res, ex1_want, "\nBRel::weight fails Ex 1 with matches[{:?}] for\n {:b}\n {:b}\nwanted:{} got:{}", ex1_matches, ex1_r1, ex1_r2, ex1_want, ex1_res);

        let ex2_r1 = BRel::from(vec![
            BStore::from(vec![0b11000000u8]),
            BStore::from(vec![0b10100000u8]),
            BStore::from(vec![0b10110000u8]),
            BStore::from(vec![0b00110000u8]),
        ]);
        let ex2_r2 = BRel::from(vec![
            BStore::from(vec![0b11000000u8]),
            BStore::from(vec![0b10110000u8]),
            BStore::from(vec![0b01010000u8]),
        ]);
        let ex2_matches12 = vec![0, 1, 1, 2];
        let ex2_res12 = ex2_r1.weight(&ex2_r2, &ex2_matches12);
        let ex2_want12 = 1;
        assert_eq!(ex2_res12, ex2_want12, "\nBRel::weight fails Ex 2 r1->r2 with matches[{:?}] for\nsource:\n{:b}\ntarget:\n{:b}\nwanted:{} got:{}", ex2_matches12, ex2_r1, ex2_r2, ex2_want12, ex2_res12);

        let ex2_matches21 = vec![1, 2, 0];
        let ex2_res21 = ex2_r2.weight(&ex2_r1, &ex2_matches21);
        let ex2_want21 = 2;
        assert_eq!(ex2_res21, ex2_want21, "\nBRel::weight fails Ex 2 r2->r1 with matches[{:?}] for\nsource:\n{:b}\ntarget:\n{:b}\nwanted:{} got:{}", ex2_matches21, ex2_r2, ex2_r1, ex2_want21, ex2_res21);
    }

    #[test]
    fn match_iterator_works() {
        let mut m = Matches::new(2, 3);
        assert_eq!(m.next(), Some(vec![0, 0]));
        assert_eq!(m.next(), Some(vec![1, 0]));
        assert_eq!(m.next(), Some(vec![2, 0]));
        assert_eq!(m.next(), Some(vec![0, 1]));
        assert_eq!(m.next(), Some(vec![1, 1]));
        assert_eq!(m.next(), Some(vec![2, 1]));
        assert_eq!(m.next(), Some(vec![0, 2]));
        assert_eq!(m.next(), Some(vec![1, 2]));
        assert_eq!(m.next(), Some(vec![2, 2]));
        assert_eq!(m.next(), None);
    }

    #[test]
    fn reltrait_brel_min_weight_works() {
        let ex1_r1 = BRel {
            major_axis: Axis::Row,
            contents: vec![BStore::from_indices(vec![0])],
        };
        let ex1_r2 = BRel::new();
        let ex1_res = ex1_r1.min_weight(&ex1_r2);
        let ex1_want = 1;
        assert_eq!(
            ex1_res, ex1_want,
            "\nRelation::min_weight fails Ex 1 for source:\n{:b}\ntarget\n{:b}\nwanted:{} got:{}",
            ex1_r1, ex1_r2, ex1_want, ex1_res
        );

        let ex2_r1 = BRel::from(vec![
            BStore::from(vec![true, true, false, false]),
            BStore::from(vec![true, false, true, false]),
            BStore::from(vec![true, false, true, true]),
            BStore::from(vec![false, false, true, true,]),
            ]);
            // ex2_r1.trim_row_count();
            let ex2_r2 = BRel::from(vec![
            BStore::from(vec![true, true, false, false]),
            BStore::from(vec![true, false, true, true]),
            BStore::from(vec![false, true, false, true]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_res12 = ex2_r1.min_weight(&ex2_r2);
        let ex2_want12 = 1;
        assert_eq!(
            ex2_res12, ex2_want12,
            "\nRelation::min_weight fails Ex 2 r1->r2 for source:\n{:b}\ntarget\n{:b}\nwanted:{} got:{}",
            ex2_r1, ex2_r2, ex2_want12, ex2_res12
        );

        let ex2_res21 = ex2_r2.min_weight(&ex2_r1);
        let ex2_want21 = 2;
        assert_eq!(
            ex2_res21, ex2_want21,
            "\nRelation::min_weight fails Ex 2 r2->r1 for source:\n{:b}\ntarget\n{:b}\nwanted:{} got:{}",
            ex2_r2, ex2_r1, ex2_want21, ex2_res21
        );
    }

    #[test]
    fn reltrait_brel_distance_works() {
        let ex1_r1 = BRel {
            major_axis: Axis::Row,
            contents: vec![BStore::from_indices(vec![0])],
        };
        let ex1_r2 = BRel::new();
        let ex1_res = ex1_r1.distance(&ex1_r2);
        let ex1_want = 1;
        assert_eq!(
            ex1_res, ex1_want,
            "\nRelation::distance fails Ex 1 for source:\n{:b}\ntarget:\n{:b}\nwanted:{} got:{}",
            ex1_r1, ex1_r2, ex1_want, ex1_res
        );

        let ex2_r1 = BRel::from(vec![
            BStore::from(vec![true, true, false, false]),
            BStore::from(vec![true, false, true, false]),
            BStore::from(vec![true, false, true, true]),
            BStore::from(vec![false, false, true, true]),
            ]);
        // ex2_r1.trim_row_count();
        let ex2_r2 = BRel::from(vec![
            BStore::from(vec![true, true, false, false]),
            BStore::from(vec![true, false, true, true]),
            BStore::from(vec![false, true, false, true]),
        ]);
        // ex2_r2.trim_row_count();
        let ex2_res = ex2_r2.distance(&ex2_r1);
        let ex2_want = 2;
        assert_eq!(
            ex2_res, ex2_want,
            "\nRelation::distance fails Ex 2 r2->r1 for source:\n{:b}\ntarget:\n{:b}\nwanted:{} got:{}",
            ex2_r2, ex2_r1, ex2_want, ex2_res
        );
    }

    #[test]
    fn reltrait_brel_transpose_works() {
        let bs1 = BStore::from_indices(vec![2, 4, 8]);
        let bs2 = BStore::from_indices(vec![4, 8]);
        let bs3 = BStore::from_indices(vec![2, 8]);
        let r1 = BRel::from(vec![bs1, bs2, bs3]);
        let bs1_t = BStore::from_indices(vec![]);
        let bs2_t = BStore::from_indices(vec![]);
        let bs3_t = BStore::from_indices(vec![0, 2]);
        let bs4_t = BStore::from_indices(vec![]);
        let bs5_t = BStore::from_indices(vec![0, 1]);
        let bs6_t = BStore::from_indices(vec![]);
        let bs7_t = BStore::from_indices(vec![]);
        let bs8_t = BStore::from_indices(vec![]);
        let bs9_t = BStore::from_indices(vec![0, 1, 2]);
        let r1_t = BRel::from(vec![bs1_t, bs2_t, bs3_t, bs4_t, bs5_t, bs6_t, bs7_t, bs8_t, bs9_t]);
        let res = r1.transpose();
        assert_eq!((res.get_row_count(), res.get_col_count(), res.get_major_axis()), (9, 3, Axis::Row), "\nfrom:\n{:b}\nres:\n{:b}", r1, res);
        assert_eq!(res, r1_t);
    }

    #[test]
    fn example2() {
        let r1 = BRel::from(vec![
            Column::from(vec![true, true, false, false]),
            Column::from(vec![true, false, true, false]),
            Column::from(vec![true, false, true, true]),
            Column::from(vec![false, false, true, true]),
        ]);
        assert_eq!(format!("{:b}", r1),"\
[[1110]
 [1000]
 [0111]
 [0011]]\
");
        let r2 = BRel::from(vec![
            Column::from(vec![true, true, false, false]),
            Column::from(vec![true, false, true, true]),
            Column::from(vec![false, true, false, true]),
        ]);
        assert_eq!(format!("{:b}", r2),"\
[[110]
 [101]
 [010]
 [011]]\
");
        assert_eq!(r1.distance(&r2), 2);
        assert_eq!(r2.distance(&r1), 2);
    }
}

// Column::from_indices(vec![0, 1]),
// Column::from_indices(vec![0, 2, 3]),
// Column::from_indices(vec![1, 3]),
