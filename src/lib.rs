#![feature(test)]
extern crate test;

use std::marker::PhantomData;
use std::{mem, iter};
use std::slice::from_raw_parts;

macro_rules! slice_offset {
    ($ptr:expr, $by:expr) => {{
        let ptr = $ptr;
        if size_from_ptr(ptr) == 0 {
            (ptr as *mut i8).wrapping_offset($by) as _
        } else {
            ptr.offset($by)
        }
    }};
}

#[inline]
fn size_from_ptr<T>(_: *const T) -> usize {
    mem::size_of::<T>()
}

trait PointerExt : Copy {
    unsafe fn slice_offset(self, i: isize) -> Self;

    /// Increments `self` by 1, but returns the old value.
    #[inline(always)]
    unsafe fn post_inc(&mut self) -> Self {
        let current = *self;
        *self = self.slice_offset(1);
        current
    }

    /// Decrements `self` by 1, and returns the new value.
    #[inline(always)]
    unsafe fn pre_dec(&mut self) -> Self {
        *self = self.slice_offset(-1);
        *self
    }
}

impl<T> PointerExt for *const T {
    #[inline(always)]
    unsafe fn slice_offset(self, i: isize) -> Self {
        slice_offset!(self, i)
    }
}

impl<T> PointerExt for *mut T {
    #[inline(always)]
    unsafe fn slice_offset(self, i: isize) -> Self {
        slice_offset!(self, i)
    }
}

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

            let end = self.end as usize - mem::size_of::<T>();
            while ptr as usize != end {

                let a = &*ptr;
                ptr = ptr.offset(1);
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

    fn last(mut self) -> Option<Self::Item> {
        unsafe {
            if self.len == 0 { return None }

            for i in (0..self.len - 1).rev() {
                let a = &*self.ptr.add(i);
                let b = &*self.ptr.add(i + 1);

                if !(self.predicate)(a, b) {
                    let len = self.len - (i + 1);
                    let slice = from_raw_parts(self.ptr.add(i + 1), len);
                    return Some(slice)
                }
            }

            let slice = from_raw_parts(self.ptr, self.len);
            Some(slice)
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use super::*;

    #[derive(Debug, Eq)]
    enum Guard {
        Valid,
        Invalid,
    }

    impl PartialEq for Guard {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Guard::Valid, Guard::Valid) => true,
                _ => panic!("denied read on Guard::Invalid variant")
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
        let slice = &[Guard::Valid, Guard::Valid, Guard::Invalid];

        let mut iter = GroupBy::new(&slice[0..2], |a, b| a == b);

        assert_eq!(iter.next(), Some(&[Guard::Valid, Guard::Valid][..]));
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
        let slice = &[Guard::Invalid, Guard::Valid, Guard::Valid, Guard::Invalid];

        let iter = GroupBy::new(&slice[1..3], |a, b| a == b);

        assert_eq!(iter.last(), Some(&[Guard::Valid, Guard::Valid][..]));
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
            test::black_box(group_by.for_each(drop))
        })
    }

}
