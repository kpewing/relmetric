/*! # A Library for Calculations with Binary Relations

The `relmetric` library creates an abstraction of a *binary relation*---a dynamically sized, 2-dimensional matrix representing whether objects in one set *X* relate to those in another *Y*. It offers core types [`Relation`](relation::Relation), [`Column`](relation::Column), [`Matches`](relation::Matches), and [`DJGrouping`](relation::DJGrouping), and methods like [`Relation::new()`](relation::Relation::new()) and [`Relation::set_col`](relation::Relation::set_col) and overloaded logical operations like [`BitAnd (&)`](std::ops::BitAnd) and multiset operations [`Add` (+)](std::ops::Add) and [`Sub (-)`](std::ops::Sub) to manipulate them.

Reflecting results of ongoing research, the library provides [`Relation::weight()`](relation::Relation::weight()) and [`Relation::distance()`](relation::Relation::distance()) to calculate the *weight* of a [`Matches`](relation::Matches) function between two [`Relation`](relation::Relation)s and the *distance* between two [`Relation`](relation::Relation)s, defined as the minimum *weight* of all functions in either direction between two *binary relations*. See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^1] Because calculating *distance* exactly requires a combinatorial search all possible [`Matches`](relation::Matches), the method [`Relation::rel_dist_bound()`](relation::Relation::rel_dist_bound()) calculates a tight upper bound with *O*(*m* &times; *n*) complexity. See [*id.* at p. 33](https://arxiv.org/abs/2105.01690).[^2]

Building on these core types, the library also provides an abstraction of

# Overview

As a quick overview, we reproduce the calculations of Examples 1 and 2 in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^3]

## Example 1
use relmetric::*;
let r1 = Relation::from(vec![Column::from(vec![1u8])]);
let r2 = Relation::new();
assert!(r2.is_empty());
assert_eq!(r1.min_weight(&r2), 1);
assert_eq!(r1.distance(&r2), 1);

## Example 2
use relmetric::*;
let mut r1 = Relation::from(vec![
    Column::from(vec![0b1100u8]),
    Column::from(vec![0b1010u8]),
    Column::from(vec![0b1011u8]),
    Column::from(vec![0b0011u8]),
]);
let mut r2 = Relation::from(vec![
    Column::from(vec![0b1100u8]),
    Column::from(vec![0b1011u8]),
    Column::from(vec![0b0101u8]),
]);
assert_eq!(r1.distance(&r2), 2);
assert_eq!(r2.distance(&r1), 2);
r1.trim_row_count();
let pretty_r1 = "\
1110
1000
0111
0011
";
assert_eq!(format!("{}", r1), pretty_r1);
r2.trim_row_count();
let pretty_r2 = "\
110
101
010
011
";
assert_eq!(format!("{}", r2), pretty_r2);

## Other Cool Stuff

- Calculate the [*kappa* bound](relation::Relation::kappa()) defined in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
- Iterate over all *n*^(*k*) (combinatorial) variations of *k* choices from a set of *n* numbers, with replacement using the [`Matches`](relation::Matches) [`Iterator`](std::iter::Iterator).
- Pretty-print both a [`Relation`](relation::Relation) and an [`DJGrouping`](relation::DJGrouping) with the standard format [`Display`](std::fmt::Display).
- Show easily human-readable binary and hexadecimal forms of both [`Column`](relation::Column)s and [`Relation`](relation::Relation)s using the standard formats [`Binary`](std::fmt::Binary), [`LowerHex`](std::fmt::LowerHex), and [`UpperHex`](std::fmt::UpperHex).
- Total lexical ordering of [`Column`](relation::Column)s and [`Relation`](relation::Relation)s.
- Binary arithmetic for both [`Column`](relation::Column)s and [`Relation`](relation::Relation)s using the standard [`& (BitAnd)`](std::ops::BitAnd), [`| (BitOr)`](std::ops::BitOr), and [`^ (BitXor)`](std::ops::BitXor) operations.

[^1]: Definitions 1 and 2, [Kenneth P. Ewing & Michael Robinson, "Metric Comparison of Relations," p. 7](https://arxiv.org/abs/2105.01690).

[^2]: Theorem 2, [*id*, p. 33](https://arxiv.org/abs/2105.01690).

[^3]: Examples 1 and 2, [*id*, pp. 10-11](https://arxiv.org/abs/2105.01690).
*/

pub mod bitstore;
pub mod relation;
pub mod absico;
pub mod dowker;
