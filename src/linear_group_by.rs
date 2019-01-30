use std::slice::{from_raw_parts, from_raw_parts_mut};
use std::iter::FusedIterator;
use std::{fmt, marker};

use crate::offset_from;

macro_rules! group_by {
    (struct $name:ident, $elem:ty, $mkslice:ident) => {
        impl<'a, T: 'a, P> $name<'a, T, P> {
            #[inline]
            fn is_empty(&self) -> bool {
                self.ptr == self.end
            }

            #[inline]
            fn remainder_len(&self) -> usize {
                unsafe { offset_from(self.end, self.ptr) }
            }
        }

        impl<'a, T: 'a, P> Iterator for $name<'a, T, P>
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

        impl<'a, T: 'a, P> DoubleEndedIterator for $name<'a, T, P>
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

        impl<'a, T: 'a, P> FusedIterator for $name<'a, T, P>
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
            predicate: predicate,
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


/// An iterator that will return non-overlapping groups in the slice
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
            predicate: predicate,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Eq)]
    enum Guard {
        Valid(i32),
        Invalid(i32),
    }

    impl PartialEq for Guard {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Guard::Valid(_), Guard::Valid(_)) => true,
                (a, b) => panic!("denied read on Guard::Invalid variant ({:?}, {:?})", a, b),
            }
        }
    }

    #[test]
    fn one_big_group() {
        let slice = &[1, 1, 1, 1];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_equal_groups() {
        let slice = &[1, 1, 1, 1, 2, 2, 2, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_little_equal_groups() {
        let slice = &[1, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[3, 3][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_little_groups() {
        let slice = &[1, 3, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn overflow() {
        let slice = &[Guard::Invalid(0), Guard::Valid(1), Guard::Valid(2), Guard::Invalid(3)];

        let mut iter = LinearGroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.next(), Some(&[Guard::Valid(1), Guard::Valid(2)][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn last_three_little_groups() {
        let slice = &[1, 3, 2];

        let iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.last(), Some(&[2][..]));
    }

    #[test]
    fn last_three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.last(), Some(&[2, 2, 2][..]));
    }

    #[test]
    fn last_overflow() {
        let slice = &[Guard::Invalid(0), Guard::Valid(1), Guard::Valid(2), Guard::Invalid(3)];

        println!("{:?}", (&slice[1..3]).as_ptr());

        let iter = LinearGroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.last(), Some(&[Guard::Valid(1), Guard::Valid(2)][..]));
    }

    #[test]
    fn back_empty_slice() {
        let slice: &[i32] = &[];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn back_one_little_group() {
        let slice = &[1];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[1][..]));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back_three_little_groups() {
        let slice = &[1, 3, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[2][..]));
        assert_eq!(iter.next_back(), Some(&[3][..]));
        assert_eq!(iter.next_back(), Some(&[1][..]));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn back_three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next_back(), Some(&[3, 3][..]));
        assert_eq!(iter.next_back(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn double_ended_dont_cross() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next_back(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next(), Some(&[3, 3][..]));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn fused_iterator() {
        let slice = &[1, 2, 3];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back_fused_iterator() {
        let slice = &[1, 2, 3];

        let mut iter = LinearGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[3][..]));
        assert_eq!(iter.next_back(), Some(&[2][..]));
        assert_eq!(iter.next_back(), Some(&[1][..]));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);
    }

    fn panic_param_ord(a: &i32, b: &i32) -> bool {
        if a < b { true }
        else { panic!("params are not in the right order") }
    }

    #[test]
    fn predicate_call_param_order() {
        let slice = &[1, 2, 3, 4, 5];

        let mut iter = LinearGroupBy::new(slice, panic_param_ord);

        assert_eq!(iter.next(), Some(&[1, 2, 3, 4, 5][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn rev_predicate_call_param_order() {
        let slice = &[1, 2, 3, 4, 5];

        let mut iter = LinearGroupBy::new(slice, panic_param_ord);

        assert_eq!(iter.next_back(), Some(&[1, 2, 3, 4, 5][..]));
        assert_eq!(iter.next_back(), None);
    }
}

#[cfg(all(feature = "nightly", test))]
mod bench {
    extern crate test;
    extern crate rand;

    use super::*;
    use self::rand::{Rng, SeedableRng};
    use self::rand::rngs::StdRng;
    use self::rand::distributions::Alphanumeric;

    #[bench]
    fn vector_16_000(b: &mut test::Bencher) {
        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn vector_16_000_sorted(b: &mut test::Bencher) {
        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        vec.sort_unstable();

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn vector_little_sorted(b: &mut test::Bencher) {
        let mut rng = StdRng::from_seed([42; 32]);

        let len = 30;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        vec.sort_unstable();

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn vector_16_000_one_group(b: &mut test::Bencher) {
        let vec = vec![1; 16_000];

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn rev_vector_16_000(b: &mut test::Bencher) {
        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.rev().count())
        })
    }

    #[bench]
    fn rev_vector_16_000_one_group(b: &mut test::Bencher) {
        let vec = vec![1; 16_000];

        b.iter(|| {
            let group_by = LinearGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.rev().count())
        })
    }
}
