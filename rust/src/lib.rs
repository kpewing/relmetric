use std::{fmt, iter::{zip}, ops::{Sub, BitAnd, BitOr}};

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
        if !self.is_empty() & !other.is_empty() {
            let mut res = true;
            assert_eq!(self.row_count, other.row_count, "Column::disjoint requires non-empty Columns to have equal row_count but {} != {}", self.row_count, other.row_count);
            assert_eq!(self.bit_field.len(), other.bit_field.len(), "Column::disjoint requires non-empty Columns to have equal lengths but {} != {}", self.bit_field.len(), other.bit_field.len());
            for (i, elem) in self.bit_field.iter().enumerate() {
                if elem & other.bit_field[i] > 0 {
                    res = false
                }
            }
            return res
        } else {
            return false
        }
    }

    pub fn column_diff(&self, other: &Column) -> u32 {
        //! `column_diff` counts the differences of two Columns
        //! Panics if the Columns have different row_count or bit_field lengths.
        let mut res;
        if self.is_empty() {
            res = other.bit_field.iter().fold(0, |acc, x| acc + x.count_ones());
        } else if other.is_empty() {
            res = self.bit_field.iter().fold(0, |acc, x| acc + x.count_ones());
        } else {
            assert_eq!(self.row_count, other.row_count, "Column::column_diff requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, other.row_count);
            assert_eq!(self.bit_field.len(), other.bit_field.len(), "Column::column_diff requires non-empty Columns to have equal bit_field lengths but: {} != {}", self.bit_field.len(), other.bit_field.len());
            let whole_ints = &self.row_count / u8::BITS as usize;
            let rest_bits = &self.row_count % u8::BITS as usize;
            const REST_MASK: [u8; 8] = [0b10000000u8, 0b11000000u8, 0b11100000u8, 0b11110000u8, 0b11111000u8, 0b11111100u8, 0b11111110u8, 0b11111111u8];
            let zipped = zip(&self.bit_field, &other.bit_field);
            res = zipped.take(whole_ints).fold(0, |acc, x| acc + (x.0 & x.1).count_ones());
            if rest_bits > 0 {
                res = res + (self.bit_field[whole_ints + 1] & other.bit_field[whole_ints + 1] & REST_MASK[rest_bits]).count_ones()
            };
            // res = zipped.enumerate().fold(0, |acc, x| if x.0 < whole_ints {acc + (x.1.0 & x.1.1).count_ones()} else {if x.0 == whole_ints && rest_bits > 0 {acc + (x.1.0 & x.1.1 & REST_MASK[rest_bits]).count_ones()} else {acc}});
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
        let mut res;
        if self.is_empty() {
            res = rhs.clone()
        } else if rhs.is_empty() {
            res = self.clone()
        } else {
            assert!(self.row_count == rhs.row_count, "Column::bitand requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitand requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            res = Column::from(zip(self.bit_field.clone(), rhs.bit_field.clone()).map(|(s,r)|s & r).collect::<Vec<u8>>());
        }
        return res
    }
}

impl BitOr for Column {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut res;
        if self.is_empty() {
            res = rhs.clone()
        } else if rhs.is_empty() {
            res = self.clone()
        } else {
            assert!(self.row_count == rhs.row_count, "Column::bitor requires non-empty Columns to have equal row_count but: {} != {}", self.row_count, rhs.row_count);
            assert!(self.bit_field.len() == rhs.bit_field.len(), "Column::bitor requires non-empty Columns to have equal length bit fields but: {} != {}", self.bit_field.len(), rhs.bit_field.len());
            res = Column::from(zip(self.bit_field.clone(), rhs.bit_field.clone()).map(|(s,r)|s | r).collect::<Vec<u8>>());
        }
        return res
    }
}


// Represents a Relation
//
// A Relation is a collection of Columns with the same row_count that can be partitioned by whether columns share bits row-by-row (aka `x_group`).
//
// The default Relation is empty, with `row_count` == 0 and empty collection of Columns.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Relation {
    pub row_count: usize,
    pub columns: Vec<Column>,
    x_groups: Option<Vec<XGroup>>,
}

// Represents indices of the Columns in a Relation that overlap by rows
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XGroup {
    pub max: Column,
    pub col_indices: Vec<usize>,
}

impl XGroup {
    pub fn new() -> XGroup {
        //! `new()` takes no arguments and returns an empty XGroup
        Default::default()
    }
}

impl Relation {
    pub fn new() -> Relation {
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
    // pub fn get_col_mut(&self, n:usize) -> &mut Column {
    //     //! `get_col_mut()` takes an index n and returns a mutable to the n'th Column in the Relation
    //     &self.columns[n]
    // }
    pub fn set_col(&mut self, n:usize, v:Column) {
        //! `set_col()` takes an index n and Column v and replaces the n'th Column in the Relation with v
    }
    pub fn xgroup(&mut self) -> &Option<Vec<XGroup>> {
        //! `xgroup()` sets the Relation's `x_groups` field to represent its partition into `XGroup`s
        if self.is_empty() {
            self.x_groups = None
        } else {
            let mut zero_grp = XGroup {
                max: Column::zero(self.row_count),
                col_indices: vec![]
            };
            let mut res = vec![zero_grp];
            for i in 0..self.columns.len() {
                let mut col = &self.columns[i];
                let mut isdisjnt = false;
                // -- check col v. all groups
                for j in 0..res.len() {
                    let mut expanded: Option<usize> = None;
                    match expanded {
                        // -- haven't yet found an overlapping res[j] to expand: this one?
                        None => {
                            isdisjnt = res[j].max.is_disjoint(&col);
                            if !isdisjnt {
                                // expand res[j] and save the index
                                res[j].col_indices.push(i);
                                res[j].max = res[j].max.clone() | (*col).clone();
                                expanded = Some(j);
                                break
                            }
                        }
                        // -- expanded res[idx]: combine with any others?
                        Some(idx) => {
                            isdisjnt = res[idx].max.is_disjoint(&res[j].max);
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
                    // -- disjoint from all groups: create a new group for col
                    if isdisjnt {
                        res.push(XGroup { max: col.clone(), col_indices: vec![i] })
                    }
                }
            }
            self.x_groups = Some(res)
        }
        return &self.x_groups
    }
}

// # Traits
//
// ## From
impl From<Vec<Column>> for Relation {
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

impl From<Vec<Vec<u8>>> for Relation {
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
impl fmt::Display for Relation {
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
            }
            s.push_str("\n");
        }
        write!(f, "{s}")
    }
}

// ## Sub
impl Sub for Relation {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut new_rel = self.clone();
        for oc in other.columns {
            // for (i, nc) in new_rel.columns.iter().enumerate() {
            for i in 0..new_rel.columns.len() {
                if oc == new_rel.columns[i] {
                    new_rel.columns.remove(i);
                    break;
                }
            }
        };
        new_rel.x_groups = match self.x_groups {
                None => None,
                Some(_) => {
                    new_rel.xgroup();
                    new_rel.x_groups
                }
            };
        new_rel
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
        let c1 = Column::from(vec![0b10000000u8, 0b00000001u8]);
        let c2 = Column::from(vec![0b00000001u8,0b10000000u8]);
        let c3 = Column::from(vec![0b10000001u8,0b10000000u8]);
        assert!(!empty.is_disjoint(&empty), "Fails to see that empties are NOT disjoint:\n left: {:?}\nright: {:?}", empty, empty);
        assert!(!zero.is_disjoint(&zero), "Fails to see that zeros are NOT disjoint:\n left: {:?}\nright: {:?}", zero, zero);
        assert!(!empty.is_disjoint(&zero), "Fails to see that empty are zero are NOT disjoint:\n left: {:?}\nright: {:?}", empty, zero);
        assert!(!zero.is_disjoint(&empty), "Fails to see that empty are zero are NOT disjoint:\n left: {:?}\nright: {:?}", zero, empty);
        assert!(!c1.is_disjoint(&empty), "Fails to see that {} is NOT disjoint from empty {}", c1.to_hex(), empty.to_hex());
        assert!(!c1.is_disjoint(&zero), "Fails to see that {} is NOT disjoint from zero {}", c1.to_hex(), zero.to_hex());
        assert!(c1.is_disjoint(&c2), "Fails to see that {} is disjoint from {} for c1 {:?} and c2 {:?}", c1.to_hex(), c2.to_hex(), c1, c2);
        assert!(!c2.is_disjoint(&c3), "Fails to see that {} is NOT disjoint from {} for c1 {:?} and c2 {:?}", c2.to_hex(), c3.to_hex(), c1, c2);
    }

    #[test]
    fn column_diff_works() {
        let c0 = Column::new();
        let c1 = Column::from(vec![0x3000u16, 0x000fu16]);
        let mut res = c1.column_diff(&c0);
        let want = 0x3000u16.count_ones() + 0x000fu16.count_ones();
        assert_eq!(res, want, "Column::column_diff of c1 and empty is {} not {} for c1 {:?}", res, want, c1);
        res = c0.column_diff(&c1);
        assert_eq!(res, want, "Column::column_diff of empty and c1 is {} not {} for c1 {:?}", res, want, c1);
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
        let mut r = Relation::from(vec!(vec![0b00000001u8]));
        let mut res = r.get_col(0).get_bit(7);
        let want = true;
        assert_eq!(res, want, "Gotten bit {} doesn't match {}", res, want);
        r.columns[0].set_bit(6, true);
        res = r.columns[0].get_bit(6);
        assert_eq!(res, want, "Set bit {} doesn't match {}", res, want);
    }

    #[test]
    fn sub_works_for_relation() {
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
        let mut r1 = Relation::from(vec![c1.clone(), c1, c2, c3]);
        let res = match r1.xgroup() {
            None => 0,
            Some(xgs) => xgs.len(),
        };
        let want = 2;
        assert_eq!(res, want, "\n\nLength of x_groups {} != {} for {:?}", res, want, r1);
    }
}
