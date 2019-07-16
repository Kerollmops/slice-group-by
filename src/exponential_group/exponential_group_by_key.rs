use crate::{ExponentialGroupBy, ExponentialGroupByMut};

pub struct ExponentialGroupByKey<'a, T: 'a>(ExponentialGroupBy<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> ExponentialGroupByKey<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        ExponentialGroupByKey(ExponentialGroupBy::new(slice, predicate))
    }
}

impl<'a, T: 'a> ExponentialGroupByKey<'a, T> {
    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn remainder(&self) -> &[T] {
        self.0.remainder()
    }
}

group_by_wrapped!{ struct ExponentialGroupByKey, &'a [T] }

pub struct ExponentialGroupByKeyMut<'a, T: 'a>(ExponentialGroupByMut<'a, T, Box<dyn FnMut(&T, &T) -> bool + 'a>>);

impl<'a, T> ExponentialGroupByKeyMut<'a, T> {
    pub fn new<F: 'a, K>(slice: &'a mut [T], mut f: F) -> Self
    where F: FnMut(&T) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: &T, b: &T| f(a) == f(b));
        ExponentialGroupByKeyMut(ExponentialGroupByMut::new(slice, predicate))
    }
}

group_by_wrapped!{ struct ExponentialGroupByKeyMut, &'a mut [T] }
