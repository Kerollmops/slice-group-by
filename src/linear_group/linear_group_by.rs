use std::slice::{from_raw_parts, from_raw_parts_mut};
use std::{fmt, marker};

use crate::offset_from;

macro_rules! group_by {
    (struct $name:ident, $elem:ty, $mkslice:ident) => {
        impl<'a, T: 'a, P> $name<'a, T, P> {
            #[inline]
            pub fn is_empty(&self) -> bool {
                self.ptr == self.end
            }

            #[inline]
            pub fn remainder_len(&self) -> usize {
                unsafe { offset_from(self.end, self.ptr) }
            }
        }

        impl<'a, T: 'a, P> std::iter::Iterator for $name<'a, T, P>
        where P: FnMut(&T, &T) -> bool,
        {
            type Item = $elem;

            fn next(&mut self) -> Option<Self::Item> {
                if self.is_empty() { return None }

                let mut i = 0;
                let mut ptr = self.ptr;

                // we use an unsafe block to avoid bounds checking here.
                // this is safe because the only thing we do here is to get
                // two elements at `ptr` and `ptr + 1`, bounds checking is done by hand.

                // we need to get *two* contiguous elements so we check that:
                //  - the first element is at the `end - 1` position because
                //  - the second one will be read from `ptr + 1` that must
                //    be lower or equal to `end`
                unsafe {
                    while ptr != self.end.sub(1) {
                        let a = &*ptr;
                        ptr = ptr.add(1);
                        let b = &*ptr;

                        i += 1;

                        if !(self.predicate)(a, b) {
                            let slice = $mkslice(self.ptr, i);
                            self.ptr = ptr;
                            return Some(slice)
                        }
                    }
                }

                // `i` is either `0` or the `slice length - 1` because either:
                //  - we have not entered the loop and so `i` is equal to `0`
                //    the slice length is necessarily `1` because we ensure it is not empty
                //  - we have entered the loop and we have not early returned
                //    so `i` is equal to the slice `length - 1`
                let slice = unsafe { $mkslice(self.ptr, i + 1) };
                self.ptr = self.end;
                Some(slice)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                if self.is_empty() { return (0, Some(0)) }

                let len = self.remainder_len();
                (1, Some(len))
            }

            fn last(mut self) -> Option<Self::Item> {
                self.next_back()
            }
        }

        impl<'a, T: 'a, P> std::iter::DoubleEndedIterator for $name<'a, T, P>
        where P: FnMut(&T, &T) -> bool,
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                // during the loop we retrieve two elements at `ptr` and `ptr - 1`.
                if self.is_empty() { return None }

                let mut i = 0;

                unsafe {
                    // we ensure that the first element that will be read
                    // is not under `end` because `end` is out of bound.
                    let mut ptr = self.end.sub(1);

                    while ptr != self.ptr {
                        // we first get `a` that is at the left of `ptr`
                        // then `b` that is under the `ptr` position.
                        let a = &*ptr.sub(1);
                        let b = &*ptr;

                        i += 1;

                        if !(self.predicate)(a, b) {
                            // the slice to return starts at the `ptr` position
                            // and `i` is the length of it.
                            let slice = $mkslice(ptr, i);

                            // because `end` is always an invalid bound
                            // we use `ptr` as `end` for the future call to `next`.
                            self.end = ptr;
                            return Some(slice)
                        }

                        ptr = ptr.sub(1);
                    }
                }

                let slice = unsafe { $mkslice(self.ptr, i + 1) };
                self.ptr = self.end;
                Some(slice)
            }
        }

        impl<'a, T: 'a, P> std::iter::FusedIterator for $name<'a, T, P>
        where P: FnMut(&T, &T) -> bool,
        { }
    }
}

/// An iterator that will return non-overlapping groups in the slice
/// using *linear/sequential search*.
///
/// It will gives two contiguous elements to the predicate function therefore the slice
/// must not be necessarily sorted.
pub struct LinearGroupBy<'a, T: 'a, P> {
    ptr: *const T,
    end: *const T,
    predicate: P,
    _phantom: marker::PhantomData<&'a T>,
}

impl<'a, T: 'a, P> LinearGroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    pub fn new(slice: &'a [T], predicate: P) -> Self {
        Self {
            ptr: slice.as_ptr(),
            end: unsafe { slice.as_ptr().add(slice.len()) },
            predicate,
            _phantom: marker::PhantomData,
        }
    }
}

impl<'a, T: 'a, P> LinearGroupBy<'a, T, P> {
    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn remainder(&self) -> &[T] {
        let len = self.remainder_len();
        unsafe { from_raw_parts(self.ptr, len) }
    }
}

impl<'a, T: 'a + fmt::Debug, P> fmt::Debug for LinearGroupBy<'a, T, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("LinearGroupBy")
            .field("remainder", &self.remainder())
            .finish()
    }
}

group_by!{ struct LinearGroupBy, &'a [T], from_raw_parts }

/// An iterator that will return non-overlapping *mutable* groups in the slice
/// using *linear/sequential search*.
///
/// It will gives two contiguous elements to the predicate function therefore the slice
/// must not be necessarily sorted.
pub struct LinearGroupByMut<'a, T: 'a, P> {
    ptr: *mut T,
    end: *mut T,
    predicate: P,
    _phantom: marker::PhantomData<&'a T>,
}

impl<'a, T: 'a, P> LinearGroupByMut<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    pub fn new(slice: &'a mut [T], predicate: P) -> Self {
        Self {
            ptr: slice.as_mut_ptr(),
            end: unsafe { slice.as_mut_ptr().add(slice.len()) },
            predicate,
            _phantom: marker::PhantomData,
        }
    }
}

impl<'a, T: 'a, P> LinearGroupByMut<'a, T, P> {
    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn into_remainder(self) -> &'a mut [T] {
        let len = self.remainder_len();
        unsafe { from_raw_parts_mut(self.ptr, len) }
    }
}

impl<'a, T: 'a + fmt::Debug, P> fmt::Debug for LinearGroupByMut<'a, T, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let len = self.remainder_len();
        let remainder = unsafe { from_raw_parts(self.ptr, len) };

        f.debug_struct("LinearGroupByMut")
            .field("remainder", &remainder)
            .finish()
    }
}

group_by!{ struct LinearGroupByMut, &'a mut [T], from_raw_parts_mut }
