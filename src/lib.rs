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
//! It is also possible to get mutable non overlapping groups of a slice even starting from the end of it.
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

#![cfg_attr(all(not(test), not(feature = "std")), no_std)]
#[cfg(all(not(test), not(feature = "std")))]
extern crate core as std;

mod linear_group_by;
mod binary_group_by;
mod exponential_group_by;

use std::cmp::{self, Ordering};

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

/// Exponential searches this sorted slice for a given element.
///
/// If the value is found then `Ok` is returned, containing the index of the matching element;
/// if the value is not found then `Err` is returned, containing the index where a matching element
/// could be inserted while maintaining sorted order.
///
/// # Examples
///
/// Looks up a series of four elements. The first is found, with a
/// uniquely determined position; the second and third are not
/// found; the fourth could match any position in `[1, 4]`.
///
/// ```
/// use slice_group_by::exponential_search;
///
/// let s = &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
///
/// assert_eq!(exponential_search(s, &13),  Ok(9));
/// assert_eq!(exponential_search(s, &4),   Err(7));
/// assert_eq!(exponential_search(s, &100), Err(13));
/// let r = exponential_search(s, &1);
/// assert!(match r { Ok(1..=4) => true, _ => false, });
/// ```
#[inline]
pub fn exponential_search<T>(slice: &[T], elem: &T) -> Result<usize, usize>
where T: Ord
{
    exponential_search_by(slice, |x| x.cmp(elem))
}

/// Binary searches this sorted slice with a comparator function.
///
/// The comparator function should implement an order consistent with the sort order of
/// the underlying slice, returning an order code that indicates whether its argument
/// is `Less`, `Equal` or `Greater` the desired target.
///
/// If the value is found then `Ok` is returned, containing the index of the matching element;
/// if the value is not found then `Err` is returned, containing the index where a matching element
/// could be inserted while maintaining sorted order.
///
/// # Examples
///
/// Looks up a series of four elements. The first is found, with a
/// uniquely determined position; the second and third are not
/// found; the fourth could match any position in `[1, 4]`.
///
/// ```
/// use slice_group_by::exponential_search_by;
///
/// let s = &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
///
/// let seek = 13;
/// assert_eq!(exponential_search_by(s, |probe| probe.cmp(&seek)), Ok(9));
/// let seek = 4;
/// assert_eq!(exponential_search_by(s, |probe| probe.cmp(&seek)), Err(7));
/// let seek = 100;
/// assert_eq!(exponential_search_by(s, |probe| probe.cmp(&seek)), Err(13));
/// let seek = 1;
/// let r = exponential_search_by(s, |probe| probe.cmp(&seek));
/// assert!(match r { Ok(1..=4) => true, _ => false, });
/// ```
#[inline]
pub fn exponential_search_by<T, F>(slice: &[T], mut f: F) -> Result<usize, usize>
where F: FnMut(&T) -> Ordering,
{
    let mut index = 1;
    while index < slice.len() && f(&slice[index]) == Ordering::Less {
        index *= 2;
    }

    let half_bound = index / 2;
    let bound = cmp::min(index + 1, slice.len());

    match slice[half_bound..bound].binary_search_by(f) {
        Ok(pos) => Ok(half_bound + pos),
        Err(pos) => Err(half_bound + pos),
    }
}

/// Binary searches this sorted slice with a key extraction function.
///
/// Assumes that the slice is sorted by the key.
///
/// If the value is found then `Ok` is returned, containing the index of the matching element;
/// if the value is not found then `Err` is returned, containing the index where a matching element
/// could be inserted while maintaining sorted order.
///
/// # Examples
///
/// Looks up a series of four elements. The first is found, with a
/// uniquely determined position; the second and third are not
/// found; the fourth could match any position in `[1, 4]`.
///
/// ```
/// use slice_group_by::exponential_search_by_key;
///
/// let s = &[(0, 0), (2, 1), (4, 1), (5, 1), (3, 1),
///           (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
///           (1, 21), (2, 34), (4, 55)];
///
/// assert_eq!(exponential_search_by_key(s, &13, |&(a,b)| b),  Ok(9));
/// assert_eq!(exponential_search_by_key(s, &4, |&(a,b)| b),   Err(7));
/// assert_eq!(exponential_search_by_key(s, &100, |&(a,b)| b), Err(13));
/// let r = exponential_search_by_key(s, &1, |&(a,b)| b);
/// assert!(match r { Ok(1..=4) => true, _ => false, });
/// ```
#[inline]
pub fn exponential_search_by_key<T, B, F>(slice: &[T], b: &B, mut f: F) -> Result<usize, usize>
where F: FnMut(&T) -> B,
      B: Ord
{
    exponential_search_by(slice, |k| f(k).cmp(b))
}

/// A convenient trait to construct an iterator returning non-overlapping groups
/// defined by a predicate.
pub trait GroupBy<T, P>
where P: FnMut(&T, &T) -> bool
{
    /// Returns an iterator on slice groups using the *linear search* method.
    fn linear_group_by(&self, predicate: P) -> LinearGroupBy<T, P>;

    /// Returns an iterator on slice groups using the *binary search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn binary_group_by(&self, predicate: P) -> BinaryGroupBy<T, P>;

    /// Returns an iterator on slice groups using the *exponential search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn exponential_group_by(&self, predicate: P) -> ExponentialGroupBy<T, P>;
}

/// A convenient trait to construct an iterator returning non-overlapping mutable
/// groups defined by a predicate.
pub trait GroupByMut<T, P>
where P: FnMut(&T, &T) -> bool
{
    /// Returns an iterator on slice groups using the *linear search* method.
    fn linear_group_by_mut(&mut self, predicate: P) -> LinearGroupByMut<T, P>;

    /// Returns an iterator on slice groups using the *binary search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn binary_group_by_mut(&mut self, predicate: P) -> BinaryGroupByMut<T, P>;

    /// Returns an iterator on slice groups using the *exponential search* method.
    ///
    /// The predicate function should implement an order consistent with
    /// the sort order of the slice.
    fn exponential_group_by_mut(&mut self, predicate: P) -> ExponentialGroupByMut<T, P>;
}

impl<T, P> GroupBy<T, P> for [T]
where P: FnMut(&T, &T) -> bool
{
    fn linear_group_by(&self, predicate: P) -> LinearGroupBy<T, P> {
        LinearGroupBy::new(self, predicate)
    }

    fn binary_group_by(&self, predicate: P) -> BinaryGroupBy<T, P> {
        BinaryGroupBy::new(self, predicate)
    }

    fn exponential_group_by(&self, predicate: P) -> ExponentialGroupBy<T, P> {
        ExponentialGroupBy::new(self, predicate)
    }
}

impl<T, P> GroupByMut<T, P> for [T]
where P: FnMut(&T, &T) -> bool
{
    fn linear_group_by_mut(&mut self, predicate: P) -> LinearGroupByMut<T, P> {
        LinearGroupByMut::new(self, predicate)
    }

    fn binary_group_by_mut(&mut self, predicate: P) -> BinaryGroupByMut<T, P> {
        BinaryGroupByMut::new(self, predicate)
    }

    fn exponential_group_by_mut(&mut self, predicate: P) -> ExponentialGroupByMut<T, P> {
        ExponentialGroupByMut::new(self, predicate)
    }
}
