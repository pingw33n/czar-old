use enum_map::Enum;
use std::marker::PhantomData;
use std::ops::RangeBounds;

pub fn enum_iter<T: Enum<()> + Copy, R: RangeBounds<T>>(r: R) -> EnumIter<T> {
    use std::ops::Bound;
    let i = match r.start_bound() {
        Bound::Included(b) => b.to_usize(),
        Bound::Excluded(_) => unreachable!(),
        Bound::Unbounded => 0,
    };
    let end = match r.end_bound() {
        Bound::Included(b) => b.to_usize().checked_add(1).unwrap(),
        Bound::Excluded(b) => b.to_usize(),
        Bound::Unbounded => T::POSSIBLE_VALUES,
    };
    if i > end {
        panic!("slice index starts at ordinal {} but ends at ordinal {}", i, end);
    } else if end > T::POSSIBLE_VALUES {
        panic!("ordinal {} out of range for enum of length {}", i, T::POSSIBLE_VALUES);
    }
    EnumIter::new(i, end)
}

pub trait EnumExt: Enum<()> + Copy {
    fn len() -> usize {
        Self::POSSIBLE_VALUES
    }

    fn iter() -> EnumIter<Self> {
        enum_iter(..)
    }

    fn from_ordinal(v: usize) -> Self {
        Enum::from_usize(v)
    }

    fn try_from_ordinal(v: usize) -> Option<Self> {
        if v < Self::len() {
            Some(Self::from_ordinal(v))
        } else {
            None
        }
    }

    fn ordinal(self) -> usize {
        Enum::to_usize(self)
    }
}

impl<T: Enum<()> + Copy> EnumExt for T {}

pub struct EnumIter<T> {
    i: usize,
    end: usize,
    _t: PhantomData<T>,
}

impl<T: Enum<()>> EnumIter<T> {
    fn new(i: usize, end: usize) -> Self {
        Self {
            i,
            end,
            _t: PhantomData,
        }
    }

    fn empty() -> Self {
        Self::new(0, 0)
    }
}

impl<T: Enum<()>> Iterator for EnumIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.end {
            return None;
        }
        let r = T::from_usize(self.i);
        self.i += 1;
        Some(r)
    }
}