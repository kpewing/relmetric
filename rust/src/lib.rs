/*! # A Library for Calculations with Binary Relations

The `relmetric` library creates an abstraction of a dynamically sized *binary relation*---a 2-dimensional binary matrix representing whether objects in one set *X* relate to those in another *Y*. It offers core types [`Relation`](relation::Relation), [`Row`](relation::Row), and [`Column`](relation::Column), as well as [`Matches`](relation::Matches) to transform one *binary relation* into another, partitions of *binary relations* into a disjoint [`DJGrouping`](relation::DJGrouping)s of *rows* or *columns*, overloaded logical operations like [`BitAnd (&)`](std::ops::BitAnd) and multiset [`Add` (+)](std::ops::Add) and [`Sub (-)`](std::ops::Sub), and human-readable [`Display`](std::fmt::Display) and [`Binary`](std::fmt::Binary) printing.

Reflecting results of ongoing research, the users can calculate the [`weight()`](relation::Relation::weight()) of a transformation from one [`Relation`](relation::Relation) to another and the [`distance()`](relation::Relation::distance()) between two [`Relation`](relation::Relation)s, defined as the minimum *weight* of all transformation in either direction between two *binary relations*. See [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).[^1] Because calculating *distance* exactly requires a combinatorial search of all possible transformation, the method [`rel_dist_bound()`](relation::Relation::rel_dist_bound()) calculates a tight upper bound with *O*(*m* &times; *n*) complexity. See [*id.* at p. 33](https://arxiv.org/abs/2105.01690).[^2]

The library also creates an abstraction of the *Dowker complex*, [`DowkerComplex`](dowker::DowkerComplex) of a *binary relation*. For more on these, see [*Robinson*, Cosheaf][^3].

# Overview

As a quick overview, we reproduce the calculations of Examples 1 and 2 in [*Ewing & Robinson*][^4].

## Example 1

First, let's use the [`BRel`](relation::BRel) for the *binary relations*, creating one using a [`Column`](relation::Column)s created from a (zero-based) `vec` of indices. For the other *binary relation*, which is [`is_empty()`](relation::Relation::is_empty()), we can use [`new()`](relation::Relation::new()). We calculate the [`min_weight()`](relation::Relation::min_weight()) and [`distance()`](relation::Relation::distance()) between them.

```
use relmetric::relation::*;
let r1 = BRel::from(vec![Column::from_indices(vec![0])]);
let r2 = BRel::new();
assert!(r2.is_empty());
assert_eq!(r1.min_weight(&r2), 1);
assert_eq!(r1.distance(&r2), 1);
```

## Example 2

For this example, we can create the [`BRel`](relation::BRel)s with [`Column`](relation::Column)s created from `vec`s of `bool`s and show the default [`Display`](std::fmt::Display) and [`Binary`](std::fmt::Binary).

```
use relmetric::relation::*;
// Create `Column`s from vectors of `true`/`false` values.
let mut r1 = BRel::from(vec![
    Column::from(vec![true, true, false, false]),
    Column::from(vec![true, false, true, false]),
    Column::from(vec![true, false, true, true]),
    Column::from(vec![false, false, true, true]),
]);
assert_eq!(format!("{}", r1),"\
[[1110]
 [1000]
 [0111]
 [0011]]\
");
let mut r2 = BRel::from(vec![
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
```

## Other Cool Stuff

- Calculate the [*kappa* bound](relation::Relation::kappa()) defined in [*Ewing & Robinson*](https://arxiv.org/abs/2105.01690).
- Iterate over all *n*^(*k*) (combinatorial) variations of *k* choices from a set of *n* numbers, with replacement using the [`Matches`](relation::Matches) [`Iterator`](std::iter::Iterator).

[^1]: Definitions 1 and 2, [Kenneth P. Ewing & Michael Robinson, "Metric Comparison of Relations," p. 7](https://arxiv.org/abs/2105.01690).

[^2]: Theorem 2, [*id*, p. 33](https://arxiv.org/abs/2105.01690).

[^3]: [Michael Robinson, "Cosheaf representations of relations and Dowker complexes", J Appl. and Comput. Topology 6, 27–63 (2022)](https://doi.org/10.1007/s41468-021-00078-y).

[^4]: Examples 1 and 2, [*Ewing & Robinson*, pp. 10-11](https://arxiv.org/abs/2105.01690).

*/

pub mod bitstore;
pub mod relation;
pub mod absico;
pub mod dowker;
