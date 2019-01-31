# slice-group-by

An implementation of the `group_by` Haskell function for slices only.

It provides tools for efficiently iterating over a slice by groups defined by a function that specifies if two elements are in the same group.

## Examples

### Linear Searched Immutable Groups

You will only need to define a function that returns `true` if two elements are in the same group.

The `LinearGroupBy` iterator will always gives contiguous elements to the predicate function.

```rust
use slice_group_by::GroupBy;

let slice = &[1, 1, 1, 3, 3, 2, 2, 2];

let mut iter = slice.linear_group_by(|a, b| a == b);

assert_eq!(iter.next(), Some(&[1, 1, 1][..]));
assert_eq!(iter.next(), Some(&[3, 3][..]));
assert_eq!(iter.next(), Some(&[2, 2, 2][..]));
assert_eq!(iter.next(), None);
```

### Binary Searched Mutable Groups

It is also possible to get mutable non overlapping groups of a slice.

The `BinaryGroupBy/Mut` and `ExponentialGroupBy/Mut` iterators will not necessarily
gives contiguous elements to the predicate function. The predicate function should implement
an order consistent with the sort order of the slice.

```rust
use slice_group_by::GroupByMut;

let slice = &mut [1, 1, 1, 2, 2, 2, 3, 3];

let mut iter = slice.binary_group_by_mut(|a, b| a == b);

assert_eq!(iter.next(), Some(&mut [1, 1, 1][..]));
assert_eq!(iter.next(), Some(&mut [2, 2, 2][..]));
assert_eq!(iter.next(), Some(&mut [3, 3][..]));
assert_eq!(iter.next(), None);
```

### Exponential Searched Mutable Groups starting from the End

It is also possible to get mutable non overlapping groups of a slice even starting from end of it.

```rust
use slice_group_by::GroupByMut;

let slice = &mut [1, 1, 1, 2, 2, 2, 3, 3];

let mut iter = slice.exponential_group_by_mut(|a, b| a == b).rev();

assert_eq!(iter.next(), Some(&mut [3, 3][..]));
assert_eq!(iter.next(), Some(&mut [2, 2, 2][..]));
assert_eq!(iter.next(), Some(&mut [1, 1, 1][..]));
assert_eq!(iter.next(), None);
```
