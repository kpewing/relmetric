use std::{fmt, iter::zip, ops::{Sub, BitAnd, BitOr, Index}};

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
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Column {
    pub row_count: usize,
    pub bit_field: Vec<u8>,
}

impl Column {
    pub fn new() -> Column {
        //! `new()` takes no arguments and returns an empty Column
        Default::default()
    }
    pub fn zero(row_count: usize) -> Column {
        let mut int_count = row_count / (u8::BITS as usize);
        if row_count % (u8::BITS as usize) > 0 {
            int_count += 1
        }
        Column {
            row_count,
            bit_field: vec![0u8; int_count]
        }
    }
    pub fn len(&self) -> usize {
        //! `len()` returns the number of `u8` integers representing the Column
        self.bit_field.len()
    }
    pub fn is_empty(&self) -> bool {
        //! `is_empty` returns `true` iff the `row_count` == 0 or the `bit_field` is empty
        self.row_count == 0 || self.bit_field.is_empty() || self.bit_field.iter().all(|&x|x == 0)
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
        assert!(self.row_count > 0, "Column::get_bit requires row_count > 0");
        assert!(n < self.row_count, "Column::get_bit index {n} outside range: 0..{}", self.row_count);
        const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        if self.bit_field.len() == 0 {
            return false
        } else {
            return self.bit_field[the_int] & ROW_MASK[the_bit] > 0;
        }
    }

    pub fn set_bit(&mut self, n:usize, v: bool) {
        //! `set_bit` set the n'th bit to the given bool value, pushing any needed zeros onto bit_field
        assert!(self.row_count > 0, "Column::set_bit requires row_count > 0");
        assert!(n < self.row_count, "Column::set_bit index {n} outside range: 0..{}", self.row_count);
        const ROW_MASK: [u8; 8] = [0b10000000u8, 0b01000000u8, 0b00100000u8, 0b00010000u8, 0b00001000u8, 0b00000100u8, 0b00000010u8, 0b00000001u8];
        let the_int = n / u8::BITS as usize;
        let the_bit = n % u8::BITS as usize;
        let need_ints = the_int.checked_sub(self.bit_field.len()).unwrap_or(0);
        for _ in 0..need_ints {
            self.bit_field.push(0u8);
        };
        if v == true {
            self.bit_field[the_int] = self.bit_field[the_int] | ROW_MASK[the_bit];
        } else {
            self.bit_field[the_int] = self.bit_field[the_int] & ROW_MASK[the_bit];
        }
    }

    pub fn is_disjoint(&self, other: &Column) -> bool {
        //! `is_disjoint` checks whether two columns are disjoint by rows
        //! True unless self and other share a true bit in some row
        //! NB: Unlike the `lua` version, empties / zeros are not disjoint from each other and are disjoint from non-empties / non-zeros. Finding empties disjoint from everything doesn't make sense.
        if self.is_empty() {
            if other.is_empty() {
                return false
            } else {
                return true
            }
        } else if other.is_empty() {
            return true
        } else {
            let mut res = true;
            assert_eq!(self.row_count, other.row_count, "Column::disjoint requires non-empty Columns to have equal row_count but {} != {}", self.row_count, other.row_count);
            assert_eq!(self.bit_field.len(), other.bit_field.len(), "Column::disjoint requires non-empty Columns to have equal lengths but {} != {}", self.bit_field.len(), other.bit_field.len());
            for (i, elem) in self.bit_field.iter().enumerate() {
                if elem & other.bit_field[i] > 0 {
                    res = false
                }
            }
            return res
        }
    }

    pub fn column_diff(&self, other: &Column) -> u32 {
        //! `column_diff` counts the differences of two Columns
        //! Panics if non-empty Columns have different `row_count`s or `bit_field` lengths.
        const REST_MASK: [u8; 8] = [0b00000000u8, 0b10000000u8, 0b11000000u8, 0b11100000u8, 0b11110000u8, 0b11111000u8, 0b11111100u8, 0b11111110u8];
        let mut res;
        let mut whole_ints = self.row_count / u8::BITS as usize;
        let mut rest_bits = self.row_count % u8::BITS as usize;
        let self_empty = self.is_empty();
        let other_empty = other.is_empty();
        if self_empty && other_empty {
            println!("both _empty");
            res = 0
        } else if self_empty {
            println!("self_empty");
            whole_ints = other.row_count / u8::BITS as usize;
            rest_bits = other.row_count % u8::BITS as usize;
            res = other.bit_field.iter().take(whole_ints).fold(0, |acc, x| acc + x.count_ones());
            if rest_bits > 0 {
                res = res + (other.bit_field[whole_ints] & REST_MASK[rest_bits]).count_ones();
            }
        } else if other_empty {
            println!("other_empty");
            res = self.bit_field.iter().take(whole_ints).fold(0, |acc, x| acc + x.count_ones());
            if rest_bits > 0 {
                res = res + (self.bit_field[whole_ints] & REST_MASK[rest_bits]).count_ones();
            }
        } else {
            println!("both not empty");
            assert_eq!(self.row_count, other.row_count, "Column::column_diff requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, other.row_count);
            assert_eq!(self.bit_field.len(), other.bit_field.len(), "Column::column_diff requires non-empty Columns to have equal bit_field lengths but: {} != {}", self.bit_field.len(), other.bit_field.len());
            res = zip(&self.bit_field, &other.bit_field).take(whole_ints).fold(0, |acc, x| acc + (x.0 ^ x.1).count_ones());
            if rest_bits > 0 {
                res = res + (self.bit_field[whole_ints] ^ other.bit_field[whole_ints] & REST_MASK[rest_bits]).count_ones()
            };
        }
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

// ## BitAnd, BitOr
impl BitAnd for Column {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone()
        } else if rhs.is_empty() {
            return self.clone()
        } else {
            assert!(self.row_count == rhs.row_count, "Column::bitand requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitand requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            return Column::from(zip(self.bit_field.clone(), rhs.bit_field.clone()).map(|(s,r)|s & r).collect::<Vec<u8>>())
        }
    }
}

impl BitOr for Column {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        if self.is_empty() {
            return rhs.clone()
        } else if rhs.is_empty() {
            return self.clone()
        } else {
            assert!(self.row_count == rhs.row_count, "Column::bitor requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitor requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            return Column::from(zip(self.bit_field.clone(), rhs.bit_field.clone()).map(|(s,r)|s | r).collect::<Vec<u8>>());
        }
    }
}


// Represents a Relation
//
// A Relation is a collection of Columns with the same row_count that can be partitioned by whether columns share bits row-by-row (aka `x_group`).
//
// The default Relation is empty, with `row_count` == 0 and empty collection of Columns.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Relation<'a> {
    pub row_count: usize,
    pub columns: Vec<Column>,
    x_groups: Option<XGrouping<'a>>,
}

impl<'a> Relation<'a> {
    pub fn new() -> Relation<'a> {
        //! `new()` takes no arguments and returns an empty Relation
        Default::default()
    }

    pub fn len(&self) -> usize {
        //! `len()` returns the number of Columns in the Relation
        self.columns.len()
    }

    pub fn is_empty(&self) -> bool {
        //! `is_empty()` returns whether the Relation is empty
        self.columns.len() == 0 || self.columns.iter().fold(true, |acc, x|acc & x.is_empty())
    }

    pub fn to_hex(&self) -> String {
        //! `to_hex()` returns a String representation of the Relation
        self.columns.iter().enumerate().map(|x| format!("Col {}: {}", x.0, x.1.to_hex())).collect::<Vec<String>>().join("\n")
    }

    pub fn get_col(&self, n:usize) -> &Column {
        //! `get_col()` takes an index n and returns the n'th Column in the Relation
        &self.columns[n]
    }

    pub fn set_col(&mut self, n:usize, v:Column) {
        //! `set_col()` replaces the Relation's n'th Column with v, pushing any needed zero columns, and resets the `x_groups` to None
        assert!(self.row_count == v.row_count, "Relation::set_col requires same row_count but {} != {}", self.row_count, v.row_count);
        let need_cols = n.checked_sub(self.columns.len()).unwrap_or(0);
        for _ in 0..need_cols {
            self.columns.push(Column::zero(self.row_count));
        };
        self.columns[n] = v;
        self.x_groups = None;   // force recalculation next time
    }

    pub fn match_columns(&self, other: &Relation, col1: usize, col2: usize) -> u32 {
        //! `match_columns(self, other)` compares two specified Columns between Relations
        self.columns[col1].column_diff(&other.columns[col2])
    }

    pub fn xgroup(&self) -> Option<Vec<XGroup>> {
        //! `xgroup()` optionally returns a partition of the Relation's Columns as a vector of `XGroup`s
        // Checks all columns v. all groups:
        // - for each `columns[i]` first check overlap with all groups `res[j]`
        // -- if overlaps a `res[j]`, then expand it and check remaining groups `res[j+1..]`
        // -- if no overlaps, then create a new group `res[_]
        // - repeat checking for remaining `columns[i+1..]`
        if self.is_empty() {
            return None
        } else {
            let mut res: Vec<XGroup> = vec![XGroup { max: self.columns[0].clone(), col_indices: vec![0]}];
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
                                let mut resj_indices: Vec<usize> = res[j].col_indices.drain(..).collect();
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
                    res.push(XGroup { max: col.clone(), col_indices: vec![i] });
                }
            }
            res.sort_unstable_by(|a,b|a.col_indices.len().cmp(&b.col_indices.len()));
            return Some(res)
        }
    }

    pub fn kappa(&self, max_count: Option<usize>) -> usize {
        //! `kappa()` returns the `kappa` value for a Relation according to the algorithm in
        //! Kenneth P. Ewing ``Bounds for the Distance Between Relations'', arXiv:2105.01690
        //!
        //! NB: `Rust` vectors are base 0 rather than `lua`'s base 1.
        if self.is_empty() {
            return 0
        } else {
            let xgs = match self.xgroup() {
                None => panic!("Relation::kappa() requires XGrouping but xgroup() generated None"),
                Some(x) => x
            };
            let mut blockcounts: Vec<usize> = xgs.iter().map(|x|x.col_indices.len()).collect();
            blockcounts.sort();
            let mut bc_sum = 0;
            let blocksums: Vec<usize> = blockcounts.iter().map(|x|{ bc_sum = bc_sum + x; bc_sum }).collect();
            let cap = match max_count {
                None => self.columns.len(),
                Some(n) => self.columns.len().min(n)
            };
            let mut m = 0;

            if blocksums[0] <= cap {
                while m < blocksums.len() && blocksums[m] <= cap {
                    m = m + 1
                }
            }
            if blocksums.len() == 1 {
                return 0
            } else if cap >= self.columns.len() {
                return blocksums[m - 2]
            } else if blocksums[m - 1] + blockcounts[m - 1] > cap {
                return blocksums[m - 2]
            } else {
                return blocksums[m - 1]
            }
        }
    }

    pub fn rel_dist_bound(&self, other: &Relation) -> usize {
        //! `rel_dist_bound()` returns the bound on the Relation metric in
        //! Kenneth P. Ewing ``Bounds for the Distance Between Relations'', arXiv:2105.01690
        //! NB: `Rust` vectors are base 0 rather than `lua`'s base 1.

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

        println!("rel_dist_bound = max({}, {}) - min({} - {} + {}, {} - {} + {})", rel1_count, rel2_count, rel1_count, delta12_count, kappa12, rel2_count, delta12_count, kappa21);

        return rel1_count.max(rel2_count) - (rel1_count - delta12_count + kappa12).min(rel2_count - delta21_count + kappa21)
    }
}

// # Traits
//
// ## From
impl From<Vec<Column>> for Relation<'_> {
    fn from(columns: Vec<Column>) -> Self {
        let row_count = columns[0].row_count;
        assert!(columns.iter().fold(true, |acc, x| acc && (x.row_count == row_count)), "From<Vec<Column>> for Relation requires all Columns to have same row_count");
        Relation {
            row_count,
            columns,
            x_groups: Default::default(),
        }
    }
}

impl From<Vec<Vec<u8>>> for Relation<'_> {
    fn from(cols: Vec<Vec<u8>>) -> Self {
        let columns: Vec<Column> = cols.into_iter().map(|x| Column::from(x)).collect();
        let row_count = columns[0].row_count;
        assert!(columns.iter().fold(true, |acc, x| acc && (x.row_count == row_count)), "From<Vec<Column>> for Relation requires all Columns to have same row_count");
        Relation {
            row_count,
            columns,
            x_groups: Default::default(),
        }
    }
}

// ## Display
impl fmt::Display for Relation<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        for j in 0..self.row_count {
            for c in 0..self.columns.len() {
                // s.push_str(&format!("{}\n", 4))
                if self.columns[c].get_bit(j) {
                    s.push_str("1")
                } else {
                    s.push_str("0")
                };
                // s.push_str(" ");
            }
            s.push_str("\n");
        }
        write!(f, "{s}")
    }
}

// ## Sub
impl Sub for Relation<'_> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut new_rel = self.clone();
        for oc in other.columns {
            for i in 0..new_rel.columns.len() {
                if oc == new_rel.columns[i] {
                    new_rel.columns.remove(i);
                    break;
                }
            }
        };
        new_rel
    }
}

// Represents an XGrouping
//
// The `XGrouping` of a `Relation` represents the partition of the Relation's Columns by row-overlap. The field `relation` refers to the `Relation`, whose lifetime it shares. The field `partition` collects the individual partitions as `XGroup`s.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XGrouping<'a> {
    relation: &'a Relation<'a>,
    pub partition: Vec<XGroup>,
}

impl XGrouping<'_> {
    pub fn new<'a>(rel: &'a Relation) -> Option<XGrouping<'a>> {
        //! `new(rel)` takes a reference to Relation and optionally returns its `Xgrouping` calculated by [`Relation::xgroup()`]
        match rel.xgroup() {
            None => None,
            Some(xgs) =>
                Some(XGrouping { relation: &rel, partition: xgs })
        }
    }
}

// impl Index<usize> for XGrouping<'_> {
//     type Output = &XGroup;

//     fn index(&self, idx: usize) -> Self::Output {
//         &self.partition[idx]
//     }
// }

impl fmt::Display for XGrouping<'_> {
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
                };
                s.push_str("\n");
            }
        };
        write!(f, "{s}")
    }
}

// Represents an XGroup
//
// Each partition is an `XGroup` collecting Columns sharing a relation (`true`) for some row with at least one other member. , but not with any other Columns in the Relation.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XGroup {
    pub max: Column,
    pub col_indices: Vec<usize>,
}

impl XGroup {
    pub fn new() -> XGroup {
        //! `new()` creates an empty XGroup
        Default::default()
    }
}

impl Index<usize> for XGroup {
    type Output = usize;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.col_indices[idx]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_col_works() {
        let res: Column = Column::new();
        let want = Column {
            row_count: 0,
            bit_field: vec![],
        };
        assert_eq!(res, want)
    }

    #[test]
    fn zero_col_works() {
        let res = Column::zero(32);
        let want = Column {
            row_count: 32,
            bit_field: vec![0u8; 4]
        };
        assert_eq!(res, want);
    }

    #[test]
    fn col_is_empty_works() {
        let c0 = Column::new();
        let c1 = Column {
            row_count: 32,
            bit_field: vec![0x30 as u8, 0x00 as u8, 0x00 as u8, 0x0f as u8],
        };
        assert!(c0.is_empty(), "{:?} should be empty", c0);
        assert!(!c1.is_empty(), "{:?} should not be empty", c1);
    }

    #[test]
    fn col_from_vec_works() {
        let c1a = Column::from(vec![0x3000 as u16, 0x000f as u16]);
        let c1b = Column {
            row_count: 32,
            bit_field: vec![0x30 as u8, 0x00 as u8, 0x00 as u8, 0x0f as u8]
        };
        assert_eq!(c1a, c1b, "{:?} should == {:?}", c1a, c1b)
    }

    #[test]
    fn prints_col_to_hex() {
        let c1 = Column::from(vec![0x3000 as u16, 0x000f as u16]);
        let res = c1.to_hex();
        let want = "{ 30 00 00 0f }";
        assert_eq!(res, want, "{} doesn't equal {}", res, want);
    }

    #[test]
    fn sets_and_gets_bit_in_col() {
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
    fn col_is_disjoint_works() {
        let empty = Column::new();
        let zero = Column::zero(16);
        let c1 = Column::from(vec![0b10000000u8,0b00000001u8]);
        let c2 = Column::from(vec![0b00000001u8,0b10000000u8]);
        let c3 = Column::from(vec![0b10000001u8,0b10000000u8]);
        assert!(!empty.is_disjoint(&empty), "Fails to see that empties are NOT disjoint:\n left: {:?}\nright: {:?}", empty, empty);
        assert!(!zero.is_disjoint(&zero), "Fails to see that zeros are NOT disjoint:\n left: {:?}\nright: {:?}", zero, zero);
        assert!(!empty.is_disjoint(&zero), "Fails to see that empty are zero are NOT disjoint:\n left: {:?}\nright: {:?}", empty, zero);
        assert!(!zero.is_disjoint(&empty), "Fails to see that empty are zero are NOT disjoint:\n left: {:?}\nright: {:?}", zero, empty);
        assert!(c1.is_disjoint(&empty), "Fails to see that {} is disjoint from empty {}", c1.to_hex(), empty.to_hex());
        assert!(c1.is_disjoint(&zero), "Fails to see that {} is disjoint from zero {}", c1.to_hex(), zero.to_hex());
        assert!(c1.is_disjoint(&c2), "Fails to see that {} is disjoint from {} for c1 {:?} and c2 {:?}", c1.to_hex(), c2.to_hex(), c1, c2);
        assert!(!c2.is_disjoint(&c3), "Fails to see that {} is NOT disjoint from {} for c1 {:?} and c2 {:?}", c2.to_hex(), c3.to_hex(), c1, c2);
    }

    #[test]
    fn column_diff_works() {
        let c0 = Column::new();
        let zero23 = Column::zero(23);
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let want = 0x3000u16.count_ones() + 0x000fu16.count_ones();
        let mut res = c0.column_diff(&c0);
        assert_eq!(res, 0, "\nempty.column_diff(empty) expected 0 but got {} for c0 {:?}", res, c0);
        res = zero23.column_diff(&c0);
        assert_eq!(res, 0, "\nzero.column_diff(empty) expected 0 but got {} for zero23 {:?}", res, zero23);
        res = c1.column_diff(&c0);
        assert_eq!(res, want, "\nc1.column_diff(empty) expected {} but got {} for c1 {:?}", want, res, c1);
        res = c0.column_diff(&c1);
        assert_eq!(res, want, "\nempty.column_diff(c1) expected {} but got {} for c1 {:?}", want, res, c1);

        let r1_0 = Column::from(vec![0b1000u8]);
        let r1_1 = Column::from(vec![0b1001u8]);
        let r2_0 = Column::from(vec![0b0000u8]);
        let r2_1 = Column::from(vec![0b1000u8]);
        assert_eq!(r1_0.column_diff(&r2_0), 1, "\nr1_0 {} v. r2_0 {} expected {}", r1_0, r2_0, 1);
        assert_eq!(r1_0.column_diff(&r2_1), 0, "\nr1_0 {} v. r2_1 {} expected {}", r1_0, r2_0, 0);
        assert_eq!(r1_1.column_diff(&r2_0), 2, "\nr1_1 {} v. r2_0 {} expected {}", r1_0, r2_0, 2);
        assert_eq!(r1_1.column_diff(&r2_1), 1, "\nr1_1 {} v. r2_1 {} expected {}", r1_0, r2_0, 1);
    }

    #[test]
    fn new_rel_works() {
        let res = Relation::new();
        let want = Relation {
            row_count: 0,
            columns: vec![],
            x_groups: None,
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
            x_groups: None
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
            x_groups: Default::default()
        };
        assert_eq!(r1a, r1b, "{:?} should == {:?}", r1a, r1b)
    }

    #[test]
    fn prints_rel_to_hex() {
        let r0 = Relation::new();
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let r1 = Relation {
            row_count: 32,
            columns: vec![c1.clone(), c2.clone()],
            x_groups: None
        };
        let mut res = r0.to_hex();
        let mut want = String::new();
        assert_eq!(res, want, "{} doesn't equal {}", res, want);
        res = r1.to_hex();
        want = format!("Col 0: {}\nCol 1: {}", &c1.to_hex(), &c2.to_hex());
        assert_eq!(res, want, "{} doesn't equal {}", res, want);
    }

    #[test]
    fn displays_relation() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let r1 = Relation::from(vec![c1.clone(), c2.clone()]);
        let res = format!("{}", r1);
        let want = String::from("00\n00\n10\n10\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n00\n10\n10\n10\n10\n");
        assert_eq!(res, want, "{} should == {} for r1 {:?}", res, want, r1)
    }

    #[test]
    fn sets_and_gets_col() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let mut r1 = Relation::from(vec![c1.clone(), c2.clone()]);
        assert_eq!(r1.get_col(0), &c1, "Fails to get column {}", 1);
        r1.set_col(0, c2);
        assert!(r1.get_col(0).is_empty(), "Fails to set column {} to zero", 1);
    }

    #[test]
    fn rel_sub_works() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c3 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let r1 = Relation::from(vec![c1.clone(), c1.clone(), c2.clone(), c3.clone()]);
        let r2 = Relation::from(vec![c1.clone(), c2.clone()]);
        let res = r1.clone() - r2.clone();
        let want = Relation::from(vec![c1.clone(), c3.clone()]);
        assert_eq!(res, want, "\nDetail:\n {:?}\n - {:?}\n should be {:?}\n but is    {:?}", r1, r2, want, res)
    }

    #[test]
    fn xgroup_works() {
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let c2 = Column::from(vec![0x0000u16, 0x0000u16]);
        let c3 = Column::from(vec![0x100fu16, 0x0f3fu16]);
        let mut r1 = Relation::from(vec![c1.clone(), c1, c2.clone(), c3.clone()]);
        let mut res = match r1.xgroup() {
            None => 0,
            Some(xgs) => xgs.len(),
        };
        let mut want = 2;
        assert_eq!(res, want, "\n\nLength of x_groups {} != {} for\n{:?}", res, want, r1);
        r1.set_col(2, c2.clone());
        res = match r1.xgroup() {
            None => 0,
            Some(xgs) => xgs.len(),
        };
        assert_eq!(res, want, "\n\nLength of x_groups {} != {} for\n{:?}", res, want, r1);
        r1.set_col(2, c3.clone());
        res = match r1.xgroup() {
            None => 0,
            Some(xgs) => xgs.len(),
        };
        want = 1;
        assert_eq!(res, want, "\n\nLength of x_groups {} != {} for\n{:?}", res, want, r1);
    }

    #[test]
    fn displays_xgrouping() {
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
        let xgs = r.xgroup().unwrap();
        let x_grouping = XGrouping::new(&r).unwrap();
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
        assert_eq!(res, want, "r:\n{}\nx_grouping:\n{}\nxgs:\n{:?}\n", r, x_grouping, xgs)
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
        assert_eq!(ex12_r3.kappa(Some(5)), 0, "Fails Example 12: kappa(R3, N=5) => 0");
        assert_eq!(ex13_r4.kappa(Some(5)), 1, "Fails Example 13: kappa(R4, N=5) => 1");
        assert_eq!(ex10_r.kappa(Some(4)), 1, "Fails Example 14: kappa(R, N=4) => 1");
        assert_eq!(ex10_r.kappa(Some(5)), 3, "Fails Example 15: kappa(R, N=5) => 3");
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
        assert_eq!(ex18_r1.rel_dist_bound(&ex18_r2), 8, "Fails Example 18 (corrected): rel_dist_bound(R1,R2) => 8");
        assert_eq!(ex19_r1.rel_dist_bound(&ex19_r2), 2, "Fails Example 19:  rel_dist_bound(R1,R2) => 2");
    }

    #[test]
    fn match_columns_works() {
        let r1 = Relation::from(vec![
            Column::from(vec![0b1000u8]),
            Column::from(vec![0b1001u8]),
        ]);
        let r2 = Relation::from(vec![
            Column::from(vec![0b0000u8]),
            Column::from(vec![0b1000u8]),
        ]);
        assert_eq!(r1.match_columns(&r2, 0, 0), 1, "\nmatch\n Col: {} of {:?},\n Col: {} or {:?}\nexpected: 1", 0, r1, 0, r2);
        assert_eq!(r1.match_columns(&r2, 0, 1), 0, "\nmatch\n Col: {} of {:?},\n Col: {} or {:?}\nexpected: 0", 0, r1, 1, r2);
        assert_eq!(r1.match_columns(&r2, 1, 0), 2, "\nmatch\n Col: {} of {:?},\n Col: {} or {:?}\nexpected: 2", 1, r1, 0, r2);
    }

    #[test]
    fn weight_works() {

    }

    #[test]
    fn matches_works() {

    }

    #[test]
    fn min_weight_works() {

    }

    #[test]
    fn relmetric_works() {

    }

}
