use crate::{BinaryGroupBy, BinaryGroupByMut};

pub struct BinaryGroupByKey<'a, T: 'a>(BinaryGroupBy<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> BinaryGroupByKey<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        BinaryGroupByKey(BinaryGroupBy::new(slice, predicate))
    }
}

impl<'a, T: 'a> BinaryGroupByKey<'a, T> {
    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn remainder(&self) -> &[T] {
        self.0.remainder()
    }
}

group_by_wrapped!{ struct BinaryGroupByKey, &'a [T] }

pub struct BinaryGroupByKeyMut<'a, T: 'a>(BinaryGroupByMut<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> BinaryGroupByKeyMut<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a mut [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        BinaryGroupByKeyMut(BinaryGroupByMut::new(slice, predicate))
    }
}

group_by_wrapped!{ struct BinaryGroupByKeyMut, &'a mut [T] }
