//! Crate `slice-group-by` is a library for efficiently iterating on a slice by groups defined by
//! a function that specifies if two elements are in the same group.
//!
//! # Example: Linear Searched Immutable Groups
//!
//! You will only need to define a function that returns `true` if two elements are in the same group.
//!
//! The `LinearGroupBy` iterator will always gives contiguous elements to the predicate function.
//!
//! ```rust
//! use slice_group_by::GroupBy;
//!
//! let slice = &[1, 1, 1, 3, 3, 2, 2, 2];
//!
//! let mut iter = slice.linear_group_by(|a, b| a == b);
//!
//! assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
//! assert_eq!(iter.next(), Some(&[3, 3][..]));
//! assert_eq!(iter.next(), Some(&[2, 2, 2][..]));
//! assert_eq!(iter.next(), None);
//! ```
//!
//! # Example: Binary Searched Mutable Groups
//!
//! It is also possible to get mutable non overlapping groups of a slice.
//!
//! The `BinaryGroupBy/Mut` and `ExponentialGroupBy/Mut` iterators will not necessarily
//! gives contiguous elements to the predicate function. The predicate function should implement
//! an order consistent with the sort order of the slice.
//!
//! ```rust
//! use slice_group_by::GroupByMut;
//!
//! let slice = &mut [1, 1, 1, 2, 2, 2, 3, 3];
//!
//! let mut iter = slice.binary_group_by_mut(|a, b| a == b);
//!
//! assert_eq!(iter.next(), Some(&mut [1, 1, 1][..]));
//! assert_eq!(iter.next(), Some(&mut [2, 2, 2][..]));
//! assert_eq!(iter.next(), Some(&mut [3, 3][..]));
//! assert_eq!(iter.next(), None);
//! ```
//!
//! # Example: Exponential Searched Mutable Groups starting from the End
//!
//! It is also possible to get mutable non overlapping groups of a slice even starting from the end of the slice.
//!
//! ```rust
//! use slice_group_by::GroupByMut;
//!
//! let slice = &mut [1, 1, 1, 2, 2, 2, 3, 3];
//!
//! let mut iter = slice.exponential_group_by_mut(|a, b| a == b).rev();
//!
//! assert_eq!(iter.next(), Some(&mut [3, 3][..]));
//! assert_eq!(iter.next(), Some(&mut [2, 2, 2][..]));
//! assert_eq!(iter.next(), Some(&mut [1, 1, 1][..]));
//! assert_eq!(iter.next(), None);
//! ```
//!

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

/// A convenient trait to construct an iterator returning non-overlapping groups
/// defined by a predicate.
pub trait GroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool
{
    /// Returns an iterator on slice groups using the *linear search* method.
    fn linear_group_by(self, predicate: P) -> LinearGroupBy<'a, T, P>;

    /// Returns an iterator on slice groups using the *binary search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn binary_group_by(self, predicate: P) -> BinaryGroupBy<'a, T, P>;

    /// Returns an iterator on slice groups using the *exponential search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn exponential_group_by(self, predicate: P) -> ExponentialGroupBy<'a, T, P>;
}

/// A convenient trait to construct an iterator returning non-overlapping mutable
/// groups defined by a predicate.
pub trait GroupByMut<'a, T: 'a, P>
where P: FnMut(&T, &T) -> bool
{
    /// Returns an iterator on slice groups using the *linear search* method.
    fn linear_group_by_mut(self, predicate: P) -> LinearGroupByMut<'a, T, P>;

    /// Returns an iterator on slice groups using the *binary search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn binary_group_by_mut(self, predicate: P) -> BinaryGroupByMut<'a, T, P>;

    /// Returns an iterator on slice groups using the *exponential search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn exponential_group_by_mut(self, predicate: P) -> ExponentialGroupByMut<'a, T, P>;
}

impl<'a, T, P> GroupBy<'a, T, P> for &'a [T]
where P: FnMut(&T, &T) -> bool
{
    fn linear_group_by(self, predicate: P) -> LinearGroupBy<'a, T, P> {
        LinearGroupBy::new(self, predicate)
    }

    fn binary_group_by(self, predicate: P) -> BinaryGroupBy<'a, T, P> {
        BinaryGroupBy::new(self, predicate)
    }

    fn exponential_group_by(self, predicate: P) -> ExponentialGroupBy<'a, T, P> {
        ExponentialGroupBy::new(self, predicate)
    }
}

impl<'a, T: 'a, P> GroupByMut<'a, T, P> for &'a mut [T]
where P: FnMut(&T, &T) -> bool
{
    fn linear_group_by_mut(self, predicate: P) -> LinearGroupByMut<'a, T, P> {
        LinearGroupByMut::new(self, predicate)
    }

    fn binary_group_by_mut(self, predicate: P) -> BinaryGroupByMut<'a, T, P> {
        BinaryGroupByMut::new(self, predicate)
    }

    fn exponential_group_by_mut(self, predicate: P) -> ExponentialGroupByMut<'a, T, P> {
        ExponentialGroupByMut::new(self, predicate)
    }
}
