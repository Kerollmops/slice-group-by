use std::slice::{from_raw_parts, from_raw_parts_mut};
use std::cmp::Ordering::{Less, Greater};
use std::iter::FusedIterator;
use std::marker;

use crate::offset_from;

macro_rules! binary_group_by {
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

                let first = unsafe { &*self.ptr };

                let len = self.remainder_len();
                let tail = unsafe { $mkslice(self.ptr.add(1), len - 1) };

                let predicate = |probe: &T| if (self.predicate)(first, probe) { Less } else { Greater };
                let index = tail.binary_search_by(predicate).unwrap_err();

                let left = unsafe { $mkslice(self.ptr, index + 1) };
                self.ptr = unsafe { self.ptr.add(index + 1) };

                Some(left)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                if self.is_empty() { return (0, Some(0)) }

                let len = self.remainder_len();
                (1, Some(len))
            }
        }

        impl<'a, T: 'a, P> FusedIterator for $name<'a, T, P>
        where P: FnMut(&T, &T) -> bool,
        { }
    }
}

pub struct BinaryGroupBy<'a, T, P> {
    ptr: *const T,
    end: *const T,
    predicate: P,
    _phantom: marker::PhantomData<&'a T>,
}

impl<'a, T, P> BinaryGroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    pub fn new(slice: &'a [T], predicate: P) -> Self {
        BinaryGroupBy {
            ptr: slice.as_ptr(),
            end: unsafe { slice.as_ptr().add(slice.len()) },
            predicate: predicate,
            _phantom: marker::PhantomData,
        }
    }

    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn remainder(&self) -> &[T] {
        let len = self.remainder_len();
        unsafe { from_raw_parts(self.ptr, len) }
    }
}

binary_group_by!{ struct BinaryGroupBy, &'a [T], from_raw_parts }

pub struct BinaryGroupByMut<'a, T, P> {
    ptr: *mut T,
    end: *mut T,
    predicate: P,
    _phantom: marker::PhantomData<&'a T>,
}

impl<'a, T, P> BinaryGroupByMut<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    pub fn new(slice: &'a mut [T], predicate: P) -> Self {
        BinaryGroupByMut {
            ptr: slice.as_mut_ptr(),
            end: unsafe { slice.as_mut_ptr().add(slice.len()) },
            predicate: predicate,
            _phantom: marker::PhantomData,
        }
    }

    /// Returns the remainder of the original slice that is going to be
    /// returned by the iterator.
    pub fn into_remainder(self) -> &'a mut [T] {
        let len = self.remainder_len();
        unsafe { from_raw_parts_mut(self.ptr, len) }
    }
}

binary_group_by!{ struct BinaryGroupByMut, &'a mut [T], from_raw_parts_mut }

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
    fn empty_slice() {
        let slice: &[i32] = &[];

        let mut iter = BinaryGroupBy::new(slice, PartialEq::eq);

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn one_little_group() {
        let slice = &[1];

        let mut iter = BinaryGroupBy::new(slice, PartialEq::eq);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn one_big_group() {
        let slice = &[1, 1, 1, 1];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_equal_groups() {
        let slice = &[1, 1, 1, 1, 2, 2, 2, 2];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_little_equal_groups() {
        let slice = &[1, 2];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[3, 3][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_little_groups() {
        let slice = &[1, 3, 2];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn overflow() {
        let slice = &[Guard::Invalid(0), Guard::Valid(1), Guard::Valid(2), Guard::Invalid(3)];

        let mut iter = BinaryGroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.next(), Some(&[Guard::Valid(1), Guard::Valid(2)][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn fused_iterator() {
        let slice = &[1, 2, 3];

        let mut iter = BinaryGroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    fn panic_param_ord(a: &i32, b: &i32) -> bool {
        if a < b { true }
        else { panic!("params are not in the right order") }
    }

    #[test]
    fn predicate_call_param_order() {
        let slice = &[1, 2, 3, 4, 5];

        let mut iter = BinaryGroupBy::new(slice, panic_param_ord);

        assert_eq!(iter.next(), Some(&[1, 2, 3, 4, 5][..]));
        assert_eq!(iter.next(), None);
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
    fn vector_16_000_sorted(b: &mut test::Bencher) {
        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        vec.sort_unstable();

        b.iter(|| {
            let group_by = BinaryGroupBy::new(vec.as_slice(), |a, b| a == b);
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
            let group_by = BinaryGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn vector_16_000_one_group(b: &mut test::Bencher) {
        let vec = vec![1; 16_000];

        b.iter(|| {
            let group_by = BinaryGroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }
}
