use crate::{LinearStrGroupBy, LinearStrGroupByMut};

pub struct LinearStrGroupByKey<'a>(LinearStrGroupBy<'a, Box<dyn FnMut(char, char) -> bool + 'a>>);

impl<'a> LinearStrGroupByKey<'a> {
    pub fn new<F: 'a, K>(slice: &'a str, mut f: F) -> Self
    where F: FnMut(char) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: char, b: char| f(a) == f(b));
        LinearStrGroupByKey(LinearStrGroupBy::new(slice, predicate))
    }
}

str_group_by_wrapped!{ struct LinearStrGroupByKey, &'a str }

pub struct LinearStrGroupByKeyMut<'a>(LinearStrGroupByMut<'a, Box<dyn FnMut(char, char) -> bool + 'a>>);

impl<'a> LinearStrGroupByKeyMut<'a> {
    pub fn new<F: 'a, K>(slice: &'a mut str, mut f: F) -> Self
    where F: FnMut(char) -> K + Copy,
          K: PartialEq,
    {
        let predicate = Box::new(move |a: char, b: char| f(a) == f(b));
        LinearStrGroupByKeyMut(LinearStrGroupByMut::new(slice, predicate))
    }
}

str_group_by_wrapped!{ struct LinearStrGroupByKeyMut, &'a mut str }
