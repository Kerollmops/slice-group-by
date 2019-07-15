use crate::{LinearGroupBy, LinearGroupByMut};

pub struct LinearGroupByKey<'a, T: 'a>(LinearGroupBy<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> LinearGroupByKey<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        LinearGroupByKey(LinearGroupBy::new(slice, predicate))
    }
}

impl<'a, T: 'a> LinearGroupByKey<'a, T> {
    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn remainder(&self) -> &[T] {
        self.0.remainder()
    }
}

group_by_partial_eq!{ struct LinearGroupByKey, &'a [T] }

pub struct LinearGroupByKeyMut<'a, T: 'a>(LinearGroupByMut<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> LinearGroupByKeyMut<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a mut [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        LinearGroupByKeyMut(LinearGroupByMut::new(slice, predicate))
    }
}

group_by_partial_eq!{ struct LinearGroupByKeyMut, &'a mut [T] }
