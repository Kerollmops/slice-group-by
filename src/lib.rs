#![cfg_attr(feature = "nightly", feature(ptr_offset_from))]
#![cfg_attr(feature = "nightly", feature(test))]

mod linear_group_by;
mod binary_group_by;
mod exponential_group_by;

pub use self::linear_group_by::{LinearGroupBy, LinearGroupByMut};
pub use self::binary_group_by::{BinaryGroupBy, BinaryGroupByMut};
pub use self::exponential_group_by::{ExponentialGroupBy, ExponentialGroupByMut};

#[cfg(feature = "nightly")]
#[inline]
unsafe fn offset_from<T>(to: *const T, from: *const T) -> usize {
    to.offset_from(from) as usize
}

#[cfg(not(feature = "nightly"))]
#[inline]
unsafe fn offset_from<T>(to: *const T, from: *const T) -> usize {
    use std::mem;
    (to as usize - from as usize) / mem::size_of::<T>()
}

pub trait GroupBy<T, P> {
    fn linear_group_by(&self, predicate: P) -> LinearGroupBy<T, P>;
    fn binary_group_by(&self, predicate: P) -> BinaryGroupBy<T, P>;
    fn exponential_group_by(&self, predicate: P) -> ExponentialGroupBy<T, P>;
}

pub trait GroupByMut<T, P> {
    fn linear_group_by_mut(&mut self, predicate: P) -> LinearGroupByMut<T, P>;
    fn binary_group_by_mut(&mut self, predicate: P) -> BinaryGroupByMut<T, P>;
    fn exponential_group_by_mut(&mut self, predicate: P) -> ExponentialGroupByMut<T, P>;
}

impl<T, P, S> GroupBy<T, P> for S
where S: AsRef<[T]>,
      P: FnMut(&T, &T) -> bool,
{
    fn linear_group_by(&self, predicate: P) -> LinearGroupBy<T, P> {
        LinearGroupBy::new(self.as_ref(), predicate)
    }

    fn binary_group_by(&self, predicate: P) -> BinaryGroupBy<T, P> {
        BinaryGroupBy::new(self.as_ref(), predicate)
    }

    fn exponential_group_by(&self, predicate: P) -> ExponentialGroupBy<T, P> {
        ExponentialGroupBy::new(self.as_ref(), predicate)
    }
}

impl<T, P, S> GroupByMut<T, P> for S
where S: AsMut<[T]>,
      P: FnMut(&T, &T) -> bool,
{
    fn linear_group_by_mut(&mut self, predicate: P) -> LinearGroupByMut<T, P> {
        LinearGroupByMut::new(self.as_mut(), predicate)
    }

    fn binary_group_by_mut(&mut self, predicate: P) -> BinaryGroupByMut<T, P> {
        BinaryGroupByMut::new(self.as_mut(), predicate)
    }

    fn exponential_group_by_mut(&mut self, predicate: P) -> ExponentialGroupByMut<T, P> {
        ExponentialGroupByMut::new(self.as_mut(), predicate)
    }
}
