#![feature(test)]
extern crate test;

use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::mem::size_of;
use std::slice::from_raw_parts;

// Thank you Yorick !
pub fn group_by_equality<T: Eq>(slice: &[T]) -> impl Iterator<Item=&[T]> {
    GroupBy::new(slice, PartialEq::eq)
}

pub struct GroupBy<'a, T: 'a, P> {
    ptr: *const T,
    end: *const T,
    predicate: P,
    _phantom: PhantomData<&'a T>,
}

impl<'a, T: 'a, P> GroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    pub fn new(slice: &'a [T], predicate: P) -> Self {
        Self {
            ptr: slice.as_ptr(),
            end: unsafe { slice.as_ptr().add(slice.len()) },
            predicate: predicate,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T: 'a, P> Iterator for GroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{
    type Item = &'a [T];

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.ptr == self.end { return None }

            let mut i = 0;
            let mut ptr = self.ptr;

            while ptr != self.end.sub(1) {
                let a = &*ptr;
                ptr = ptr.add(1);
                let b = &*ptr;

                i += 1;

                if !(self.predicate)(a, b) {
                    let slice = from_raw_parts(self.ptr, i);
                    self.ptr = ptr;
                    return Some(slice)
                }
            }

            let slice = from_raw_parts(self.ptr, i + 1);
            self.ptr = self.end;
            Some(slice)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let lower = if self.ptr == self.end { 0 } else { 1 };
        let upper = (self.end as usize - self.ptr as usize) / size_of::<T>();
        (lower, Some(upper))
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, T: 'a, P> DoubleEndedIterator for GroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{

    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.ptr == self.end { return None }

            let mut i = 0;
            let mut ptr = self.end.sub(1);

            while ptr != self.ptr {
                let a = &*ptr;
                let b = &*ptr.sub(1);

                i += 1;

                // swap a and b to call the predicate correctly
                if !(self.predicate)(b, a) {
                    let slice = from_raw_parts(ptr, i);
                    self.end = ptr;
                    return Some(slice)
                }

                ptr = ptr.sub(1);
            }

            let slice = from_raw_parts(self.ptr, i + 1);
            self.ptr = self.end;
            Some(slice)
        }
    }
}

impl<'a, T: 'a, P> FusedIterator for GroupBy<'a, T, P>
where P: FnMut(&T, &T) -> bool,
{ }

#[cfg(test)]
mod tests {
    extern crate rand;
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

        let mut iter = group_by_equality(slice);

        assert_eq!(iter.next(), None);
    }

    #[test]
    fn one_little_group() {
        let slice = &[1];

        let mut iter = group_by_equality(slice);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn one_big_group() {
        let slice = &[1, 1, 1, 1];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_equal_groups() {
        let slice = &[1, 1, 1, 1, 2, 2, 2, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn two_little_equal_groups() {
        let slice = &[1, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next(), Some(&[3, 3][..]));
        assert_eq!(iter.next(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn three_little_groups() {
        let slice = &[1, 3, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn overflow() {
        let slice = &[Guard::Invalid(0), Guard::Valid(1), Guard::Valid(2), Guard::Invalid(3)];

        let mut iter = GroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.next(), Some(&[Guard::Valid(1), Guard::Valid(2)][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn last_three_little_groups() {
        let slice = &[1, 3, 2];

        let iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.last(), Some(&[2][..]));
    }

    #[test]
    fn last_three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.last(), Some(&[2, 2, 2][..]));
    }

    #[test]
    fn last_overflow() {
        let slice = &[Guard::Invalid(0), Guard::Valid(1), Guard::Valid(2), Guard::Invalid(3)];

        println!("{:?}", (&slice[1..3]).as_ptr());

        let iter = GroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.last(), Some(&[Guard::Valid(1), Guard::Valid(2)][..]));
    }

    #[test]
    fn back_empty_slice() {
        let slice: &[i32] = &[];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn back_one_little_group() {
        let slice = &[1];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[1][..]));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back_three_little_groups() {
        let slice = &[1, 3, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[2][..]));
        assert_eq!(iter.next_back(), Some(&[3][..]));
        assert_eq!(iter.next_back(), Some(&[1][..]));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn back_three_groups() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next_back(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next_back(), Some(&[3, 3][..]));
        assert_eq!(iter.next_back(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn double_ended_dont_cross() {
        let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
        assert_eq!(iter.next_back(), Some(&[2, 2, 2][..]));
        assert_eq!(iter.next(), Some(&[3, 3][..]));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn fused_iterator() {
        let slice = &[1, 2, 3];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

        assert_eq!(iter.next(), Some(&[1][..]));
        assert_eq!(iter.next(), Some(&[2][..]));
        assert_eq!(iter.next(), Some(&[3][..]));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn back_fused_iterator() {
        let slice = &[1, 2, 3];

        let mut iter = GroupBy::new(slice, |a, b| a == b);

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

        let mut iter = GroupBy::new(slice, panic_param_ord);

        assert_eq!(iter.next(), Some(&[1, 2, 3, 4, 5][..]));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn rev_predicate_call_param_order() {
        let slice = &[1, 2, 3, 4, 5];

        let mut iter = GroupBy::new(slice, panic_param_ord);

        assert_eq!(iter.next_back(), Some(&[1, 2, 3, 4, 5][..]));
        assert_eq!(iter.next_back(), None);
    }

    #[bench]
    fn vector_16_000(b: &mut test::Bencher) {
        use self::rand::{Rng, SeedableRng};
        use self::rand::rngs::StdRng;
        use self::rand::distributions::Alphanumeric;

        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        b.iter(|| {
            let group_by = GroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn vector_16_000_one_group(b: &mut test::Bencher) {
        let vec = vec![1; 16_000];

        b.iter(|| {
            let group_by = GroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.count())
        })
    }

    #[bench]
    fn rev_vector_16_000(b: &mut test::Bencher) {
        use self::rand::{Rng, SeedableRng};
        use self::rand::rngs::StdRng;
        use self::rand::distributions::Alphanumeric;

        let mut rng = StdRng::from_seed([42; 32]);

        let len = 16_000;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(rng.sample(Alphanumeric));
        }

        b.iter(|| {
            let group_by = GroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.rev().count())
        })
    }

    #[bench]
    fn rev_vector_16_000_one_group(b: &mut test::Bencher) {
        let vec = vec![1; 16_000];

        b.iter(|| {
            let group_by = GroupBy::new(vec.as_slice(), |a, b| a == b);
            test::black_box(group_by.rev().count())
        })
    }
}
