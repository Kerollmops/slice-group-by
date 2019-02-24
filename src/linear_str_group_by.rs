use std::iter::FusedIterator;

/// An iterator that will return non-overlapping groups in the `str`
/// using *linear/sequential search*.
///
/// It will gives two contiguous `char` to the predicate function.
pub struct LinearStrGroupBy<'a, P> {
    inner: &'a str,
    predicate: P,
}

impl<'a, P> LinearStrGroupBy<'a, P> {
    pub fn new(string: &'a str, predicate: P) -> Self {
        Self {
            inner: string,
            predicate: predicate,
        }
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        self.inner
    }
}

impl<'a, P> Iterator for LinearStrGroupBy<'a, P>
where P: FnMut(char, char) -> bool,
{
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.inner.is_empty() { return None }

        let mut iter = self.inner.char_indices().peekable();
        while let (Some((_, ac)), Some((bi, bc))) = (iter.next(), iter.peek().cloned())
        {
            if !(self.predicate)(ac, bc) {
                let (left, right) = self.inner.split_at(bi);
                self.inner = right;
                return Some(left);
            }
        }

        let output = self.inner;
        self.inner = "";
        return Some(output);
    }
}

impl<'a, P> DoubleEndedIterator for LinearStrGroupBy<'a, P>
where P: FnMut(char, char) -> bool,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.inner.is_empty() { return None }

        let mut iter = self.inner.char_indices().rev().peekable();
        while let (Some((ai, ac)), Some((_, bc))) = (iter.next(), iter.peek().cloned())
        {
            if !(self.predicate)(ac, bc) {
                let (left, right) = self.inner.split_at(ai);
                self.inner = left;
                return Some(right);
            }
        }

        let output = self.inner;
        self.inner = "";
        return Some(output);
    }
}

impl<'a, P> FusedIterator for LinearStrGroupBy<'a, P>
where P: FnMut(char, char) -> bool,
{ }

/// An iterator that will return non-overlapping groups of equal `char`
/// in the str using *linear/sequential search*.
///
/// It will use the `char` [`PartialEq::eq`] function.
///
/// [`PartialEq::eq`]: https://doc.rust-lang.org/std/primitive.char.html#impl-PartialEq%3Cchar%3E
pub struct LinearStrGroup<'a>(LinearStrGroupBy<'a, fn(char, char) -> bool>);

impl<'a> LinearStrGroup<'a> {
    pub fn new(string: &'a str) -> Self {
        LinearStrGroup(LinearStrGroupBy::new(string, |a, b| a == b))
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl<'a> Iterator for LinearStrGroup<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<'a> DoubleEndedIterator for LinearStrGroup<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<'a> FusedIterator for LinearStrGroup<'a>
{ }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn str_easy() {
        let string = "aaaabbbbbaacccc";

        let mut iter = LinearStrGroup::new(string);

        assert_eq!(iter.next(), Some("aaaa"));
        assert_eq!(iter.next(), Some("bbbbb"));
        assert_eq!(iter.next(), Some("aa"));
        assert_eq!(iter.next(), Some("cccc"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn str_kanji() {
        let string = "包包饰饰与与钥钥匙匙扣扣";

        let mut iter = LinearStrGroup::new(string);

        assert_eq!(iter.next(), Some("包包"));
        assert_eq!(iter.next(), Some("饰饰"));
        assert_eq!(iter.next(), Some("与与"));
        assert_eq!(iter.next(), Some("钥钥"));
        assert_eq!(iter.next(), Some("匙匙"));
        assert_eq!(iter.next(), Some("扣扣"));
        assert_eq!(iter.next(), None);
    }

    fn is_cjk(c: char) -> bool {
        (c >= '\u{2e80}' && c <= '\u{2eff}') ||
        (c >= '\u{2f00}' && c <= '\u{2fdf}') ||
        (c >= '\u{3040}' && c <= '\u{309f}') ||
        (c >= '\u{30a0}' && c <= '\u{30ff}') ||
        (c >= '\u{3100}' && c <= '\u{312f}') ||
        (c >= '\u{3200}' && c <= '\u{32ff}') ||
        (c >= '\u{3400}' && c <= '\u{4dbf}') ||
        (c >= '\u{4e00}' && c <= '\u{9fff}') ||
        (c >= '\u{f900}' && c <= '\u{faff}')
    }

    #[test]
    fn str_ascii_cjk() {
        let string = "abc包包bbccdd饰饰";

        let mut iter = LinearStrGroupBy::new(string, |a, b| is_cjk(a) == is_cjk(b));

        assert_eq!(iter.next(), Some("abc"));
        assert_eq!(iter.next(), Some("包包"));
        assert_eq!(iter.next(), Some("bbccdd"));
        assert_eq!(iter.next(), Some("饰饰"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn str_rev_easy() {
        let string = "aaaabbbbbaacccc";

        let mut iter = LinearStrGroup::new(string).rev();

        assert_eq!(iter.next(), Some("cccc"));
        assert_eq!(iter.next(), Some("aa"));
        assert_eq!(iter.next(), Some("bbbbb"));
        assert_eq!(iter.next(), Some("aaaa"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn str_rev_ascii_cjk() {
        let string = "abc包包bbccdd饰饰";

        let mut iter = LinearStrGroupBy::new(string, |a, b| is_cjk(a) == is_cjk(b)).rev();

        assert_eq!(iter.next(), Some("饰饰"));
        assert_eq!(iter.next(), Some("bbccdd"));
        assert_eq!(iter.next(), Some("包包"));
        assert_eq!(iter.next(), Some("abc"));
        assert_eq!(iter.next(), None);
    }
}
