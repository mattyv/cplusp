//! The translator: lists, decision 0121. The summary of the proofs is in `model`.

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------ lists, decision 0121

/// A list of items, in their order. Every list of the model is one, decision 0121.
#[derive(PartialEq, Eq, Debug)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

/// The value of the first pair with the key `k`.
pub open spec fn spec_get<V>(l: List<(u32, V)>, k: u32) -> Option<V>
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if n == k {
            Some(v)
        } else {
            spec_get(*rest, k)
        },
    }
}

pub fn get<V: Copy>(l: &List<(u32, V)>, k: u32) -> (r: Option<V>)
    ensures
        r == spec_get(*l, k),
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if *n == k {
            Some(*v)
        } else {
            get(rest, k)
        },
    }
}

/// The value of the first pair with the key `k`, by reference.
pub fn get_ref<V>(l: &List<(u32, V)>, k: u32) -> (r: Option<&V>)
    ensures
        match r {
            Some(v) => spec_get(*l, k) == Some(*v),
            None => spec_get(*l, k) is None,
        },
    decreases l,
{
    match l {
        List::Nil => None,
        List::Cons((n, v), rest) => if *n == k {
            Some(v)
        } else {
            get_ref(rest, k)
        },
    }
}

/// `k` is in the list.
pub open spec fn spec_has(l: List<u32>, k: u32) -> bool
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(n, rest) => n == k || spec_has(*rest, k),
    }
}

pub fn has(l: &List<u32>, k: u32) -> (r: bool)
    ensures
        r == spec_has(*l, k),
    decreases l,
{
    match l {
        List::Nil => false,
        List::Cons(n, rest) => *n == k || has(rest, k),
    }
}

/// The keys of a list of pairs, in their order.
pub open spec fn spec_keys<V>(l: List<(u32, V)>) -> List<u32>
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons((n, _), rest) => List::Cons(n, Box::new(spec_keys(*rest))),
    }
}

pub fn keys<V>(l: &List<(u32, V)>) -> (r: List<u32>)
    ensures
        r == spec_keys(*l),
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons((n, _), rest) => List::Cons(*n, Box::new(keys(rest))),
    }
}

/// The items of `a`, then the items of `b`.
pub open spec fn spec_append<T>(a: List<T>, b: List<T>) -> List<T>
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(x, rest) => List::Cons(x, Box::new(spec_append(*rest, b))),
    }
}

pub fn append<T>(a: List<T>, b: List<T>) -> (r: List<T>)
    ensures
        r == spec_append(a, b),
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(x, rest) => List::Cons(x, Box::new(append(*rest, b))),
    }
}

/// A copy of a list of plain items.
pub fn copy<T: Copy>(l: &List<T>) -> (r: List<T>)
    ensures
        r == *l,
    decreases l,
{
    match l {
        List::Nil => List::Nil,
        List::Cons(x, rest) => List::Cons(*x, Box::new(copy(rest))),
    }
}

} // verus!
