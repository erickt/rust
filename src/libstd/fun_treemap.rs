// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! An ordered map and set implemented as self-balancing binary search
//! trees. The only requirement for the types is that the key implements
//! `Ord`, and that the `lt` method provides a total ordering.

#[forbid(deprecated_mode)];

use prelude::*;

// This is implemented as an AA tree, which is a simplified variation of
// a red-black tree where where red (horizontal) nodes can only be added
// as a right child. The time complexity is the same, and re-balancing
// operations are more frequent but also cheaper.

// Future improvements:

// range search - O(log n) retrieval of an iterator from some key

// (possibly) implement the overloads Python does for sets:
//   * intersection: &
//   * difference: -
//   * symmetric difference: ^
//   * union: |
// These would be convenient since the methods work like `each`

pub enum TreeMap<K, V> {
    priv Empty,
    priv Node(@TreeNode<K, V>),
}

impl <K: Eq Ord, V: Eq> TreeMap<K, V>: Eq {
    pure fn eq(&self, other: &TreeMap<K, V>) -> bool {
        if self.len() != other.len() {
            false
        } else {
            let mut x = self.iter();
            let mut y = other.iter();
            for self.len().times {
                unsafe { // unsafe as a purity workaround
                    x = x.next();
                    y = y.next();
                    // FIXME: #4492 (ICE), x.get() == y.get()
                    let (x1, x2) = x.get().unwrap();
                    let (y1, y2) = y.get().unwrap();

                    if x1 != y1 || x2 != y2 {
                        return false
                    }
                }
            }
            true
        }
    }
    pure fn ne(&self, other: &TreeMap<K, V>) -> bool { !self.eq(other) }
}

// Lexicographical comparison
pure fn lt<K: Ord, V>(a: &TreeMap<K, V>, b: &TreeMap<K, V>) -> bool {
    let mut x = a.iter();
    let mut y = b.iter();

    let (a_len, b_len) = (a.len(), b.len());
    for uint::min(a_len, b_len).times {
        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let (key_a,_) = x.get().unwrap();
            let (key_b,_) = y.get().unwrap();
            if *key_a < *key_b { return true; }
            if *key_a > *key_b { return false; }
        }
    };

    return a_len < b_len;
}

impl <K: Ord, V> TreeMap<K, V>: Ord {
    #[inline(always)]
    pure fn lt(&self, other: &TreeMap<K, V>) -> bool {
        lt(self, other)
    }
    #[inline(always)]
    pure fn le(&self, other: &TreeMap<K, V>) -> bool {
        !lt(other, self)
    }
    #[inline(always)]
    pure fn ge(&self, other: &TreeMap<K, V>) -> bool {
        !lt(self, other)
    }
    #[inline(always)]
    pure fn gt(&self, other: &TreeMap<K, V>) -> bool {
        lt(other, self)
    }
}

impl <K: Ord, V> TreeMap<K, V>: Container {
    /// Return the number of elements in the map
    pure fn len(&self) -> uint {
        let mut count = 0;
        for self.each |_, _| { count += 1; }
        count
    }

    /// Return true if the map contains no elements
    pure fn is_empty(&self) -> bool {
        match *self {
            Empty => true,
            _ => false,
        }
    }
}

impl <K: Ord, V> TreeMap<K, V>: Map<K, V> {
    /// Return true if the map contains a value for the specified key
    pure fn contains_key(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// Visit all key-value pairs in order
    pure fn each(&self, f: fn(&K, &V) -> bool) {
        match *self {
            Node(ref n) => {
                n.left.each(f);
                if f(&*n.key, &*n.value) { n.right.each(f); }
            }
            Empty => (),
        }
    }

    /// Visit all keys in order
    pure fn each_key(&self, f: fn(&K) -> bool) { self.each(|k, _| f(k)) }

    /// Visit all values in order
    pure fn each_value(&self, f: fn(&V) -> bool) { self.each(|_, v| f(v)) }

    /// Return the value corresponding to the key in the map
    pure fn find(&self, key: &K) -> Option<&self/V> {
        let mut current: &self/TreeMap<K, V> = self;
        loop {
            match *current {
                Node(ref n) => {
                    let n: &self/@TreeNode<K, V> = n; // FIXME: #3148
                    if *key < *n.key {
                        current = &n.left;
                    } else if *key > *n.key {
                        current = &n.right;
                    } else {
                        return Some(&*n.value);
                    }
                }
                Empty => return None
            }
        }
    }
}

impl <K: Ord, V> TreeMap<K, V>: ImmutableMap<K, V> {
    /// Insert a key-value pair into the map. An existing value for a
    /// key is replaced by the value.
    pure fn insert(&self, key: K, value: V) -> TreeMap<K, V> {
        match *self {
            Empty => Node(@TreeNode::new(@key, @value)),
            Node(ref n) => {
                if key < *n.key {
                    Node(split(skew(@TreeNode {
                        level: n.level,
                        key: n.key,
                        value: n.value,
                        left: n.left.insert(key, value),
                        right: n.right,
                    })))
                } else if key > *n.key {
                    Node(split(skew(@TreeNode {
                        level: n.level,
                        key: n.key,
                        value: n.value,
                        left: n.left,
                        right: n.right.insert(key, value),
                    })))
                } else {
                    Node(@TreeNode {
                        level: n.level,
                        key: @key,
                        value: @value,
                        left: n.left,
                        right: n.right,
                    })
                }
            }
        }
    }

    /// Remove a key-value pair from the map.
    pure fn remove(&self, _key: &K) -> TreeMap<K, V> {
        fail
        /*
        match *self {
            Node(ref n) => {
                if key < *n.key {
                    Node(@TreeNode {
                        key: n.key,
                        value: n.value,
                        left: n.left.remove(key),
                        right: n.right,
                    })
                } else if key > *n.key {
                    Node(@TreeNode {
                        key: n.key,
                        value: n.value,
                        left: n.left,
                        right: n.right.remove(key),
                    })
                } else {
                    match (n.left, n.right) {
                        (Node(ref left), Node(ref right)) => {
                            match (left.

                            Node(@TreeNode {
                                key: left.key,
                                value: left.value,
                                left: ,
                                right: ,
                            })
                        }
                        (Empty, Node(ref right)) => n.right,
                        (Node(ref left), Empty) => n.left,
                        (Empty, Empty) => Empty,
                    }
                    fail
                    / *
                    Node(@TreeNode {
                        key: @key,
                        value: @value,
                        left: n.left,
                        right: n.right,
                    })
                    * /
                }
            }
            Emtpy => Empty,
        }
        */
    }
}

impl <K: Ord, V> TreeMap<K, V> {
    /// Create an empty TreeMap
    static pure fn new() -> TreeMap<K, V> { Empty }

    /// Visit all key-value pairs in reverse order
    pure fn each_reverse(&self, f: fn(&K, &V) -> bool) {
        match *self {
            Node(ref n) => {
                n.right.each_reverse(f);
                if f(&*n.key, &*n.value) { n.left.each_reverse(f) }
            }
            Empty => (),
        }
    }

    /// Visit all keys in reverse order
    pure fn each_key_reverse(&self, f: fn(&K) -> bool) {
        self.each_reverse(|k, _| f(k))
    }

    /// Visit all values in reverse order
    pure fn each_value_reverse(&self, f: fn(&V) -> bool) {
        self.each_reverse(|_, v| f(v))
    }

    /// Get a lazy iterator over the key-value pairs in the map.
    /// Requires that it be frozen (immutable).
    pure fn iter(&self) -> TreeMapIterator/&self<K, V> {
        TreeMapIterator { stack: ~[], node: self, current: None }
    }
}

/// Lazy forward iterator over a map
pub struct TreeMapIterator<K, V> {
    priv stack: ~[&@TreeNode<K, V>],
    priv node: &TreeMap<K, V>,
    priv current: Option<&@TreeNode<K, V>>,
}

impl <K: Ord, V> TreeMapIterator<K, V> {
    // Returns the current node, or None if this iterator is at the end.
    fn get(&const self) -> Option<(&self/K, &self/V)> {
        match self.current {
            Some(res) => Some((&*res.key, &*res.value)),
            None => None
        }
    }

    /// Advance the iterator to the next node (in order). If this iterator
    /// is finished, does nothing.
    fn next(self) -> TreeMapIterator/&self<K, V> {
        let mut this = self;
        while !this.stack.is_empty() || !this.node.is_empty() {
            match *this.node {
                Node(ref x) => {
                    this.stack.push(x);
                    this.node = &x.left;
                }
                Empty => {
                    let res = this.stack.pop();
                    this.node = &res.right;
                    this.current = Some(res);
                    return this;
                }
            }
        }
        this.current = None;
        this
    }
}

pub struct TreeSet<T> {
    priv map: TreeMap<T, ()>,
}

impl <T: Ord> TreeSet<T>: iter::BaseIter<T> {
    /// Visit all values in order
    pure fn each(&self, f: fn(&T) -> bool) { self.map.each_key(f) }
    pure fn size_hint(&self) -> Option<uint> { Some(self.len()) }
}

impl <T: Eq Ord> TreeSet<T>: Eq {
    pure fn eq(&self, other: &TreeSet<T>) -> bool { self.map == other.map }
    pure fn ne(&self, other: &TreeSet<T>) -> bool { self.map != other.map }
}

impl <T: Ord> TreeSet<T>: Ord {
    #[inline(always)]
    pure fn lt(&self, other: &TreeSet<T>) -> bool { self.map < other.map }
    #[inline(always)]
    pure fn le(&self, other: &TreeSet<T>) -> bool { self.map <= other.map }
    #[inline(always)]
    pure fn ge(&self, other: &TreeSet<T>) -> bool { self.map >= other.map }
    #[inline(always)]
    pure fn gt(&self, other: &TreeSet<T>) -> bool { self.map > other.map }
}

impl <T: Ord> TreeSet<T>: Container {
    /// Return the number of elements in the set
    pure fn len(&self) -> uint { self.map.len() }

    /// Return true if the set contains no elements
    pure fn is_empty(&self) -> bool { self.map.is_empty() }
}

impl <T: Ord> TreeSet<T>: Set<T> {
    /// Return true if the set contains a value
    pure fn contains(&self, value: &T) -> bool {
        self.map.contains_key(value)
    }

    /// Return true if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    pure fn is_disjoint(&self, other: &TreeSet<T>) -> bool {
        let mut x = self.iter();
        let mut y = other.iter();
        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();
            while a.is_some() && b.is_some() {
                let a1 = a.unwrap();
                let b1 = b.unwrap();
                if a1 < b1 {
                    x = x.next();
                    a = x.get();
                } else if b1 < a1 {
                    y = y.next();
                    b = y.get();
                } else {
                    return false;
                }
            }
        }
        true
    }

    /// Return true if the set is a subset of another
    pure fn is_subset(&self, other: &TreeSet<T>) -> bool {
        other.is_superset(self)
    }

    /// Return true if the set is a superset of another
    pure fn is_superset(&self, other: &TreeSet<T>) -> bool {
        let mut x = self.iter();
        let mut y = other.iter();
        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();
            while b.is_some() {
                if a.is_none() {
                    return false
                }

                let a1 = a.unwrap();
                let b1 = b.unwrap();

                if b1 < a1 {
                    return false
                }

                if !(a1 < b1) {
                    y = y.next();
                    b = y.get();
                }
                x = x.next();
                a = x.get();
            }
        }
        true
    }

    /// Visit the values (in-order) representing the difference
    pure fn difference(&self, other: &TreeSet<T>, f: fn(&T) -> bool) {
        let mut x = self.iter();
        let mut y = other.iter();

        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();

            while a.is_some() {
                if b.is_none() {
                    return do a.while_some() |a1| {
                        if f(a1) { x = x.next(); x.get() } else { None }
                    }
                }

                let a1 = a.unwrap();
                let b1 = b.unwrap();

                if a1 < b1 {
                    if !f(a1) { return }
                    x = x.next();
                    a = x.get();
                } else {
                    if !(b1 < a1) { x = x.next(); a = x.get() }
                    y = y.next();
                    b = y.get();
                }
            }
        }
    }

    /// Visit the values (in-order) representing the symmetric difference
    pure fn symmetric_difference(&self, other: &TreeSet<T>,
                                 f: fn(&T) -> bool) {
        let mut x = self.iter();
        let mut y = other.iter();

        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();

            while a.is_some() {
                if b.is_none() {
                    return do a.while_some() |a1| {
                        if f(a1) { x.next(); x.get() } else { None }
                    }
                }

                let a1 = a.unwrap();
                let b1 = b.unwrap();

                if a1 < b1 {
                    if !f(a1) { return }
                    x = x.next();
                    a = x.get();
                } else {
                    if b1 < a1 {
                        if !f(b1) { return }
                    } else {
                        x = x.next();
                        a = x.get();
                    }
                    y = y.next();
                    b = y.get();
                }
            }
            do b.while_some |b1| {
                if f(b1) { y = y.next(); y.get() } else { None }
            }
        }
    }

    /// Visit the values (in-order) representing the intersection
    pure fn intersection(&self, other: &TreeSet<T>, f: fn(&T) -> bool) {
        let mut x = self.iter();
        let mut y = other.iter();

        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();

            while a.is_some() && b.is_some() {
                let a1 = a.unwrap();
                let b1 = b.unwrap();
                if a1 < b1 {
                    x = x.next();
                    a = x.get();
                } else {
                    if !(b1 < a1) {
                        if !f(a1) { return }
                    }
                    y = y.next();
                    b = y.get();
                }
            }
        }
    }

    /// Visit the values (in-order) representing the union
    pure fn union(&self, other: &TreeSet<T>, f: fn(&T) -> bool) {
        let mut x = self.iter();
        let mut y = other.iter();

        unsafe { // purity workaround
            x = x.next();
            y = y.next();
            let mut a = x.get();
            let mut b = y.get();

            while a.is_some() {
                if b.is_none() {
                    return do a.while_some() |a1| {
                        if f(a1) { x = x.next(); x.get() } else { None }
                    }
                }

                let a1 = a.unwrap();
                let b1 = b.unwrap();

                if b1 < a1 {
                    if !f(b1) { return }
                    y = y.next();
                    b = y.get();
                } else {
                    if !f(a1) { return }
                    if !(a1 < b1) {
                        y = y.next();
                        b = y.get()
                    }
                    x = x.next();
                    a = x.get();
                }
            }
        }
    }
}

impl <T: Ord> TreeSet<T>: ImmutableSet<T> {
    /// Insert a value into the set.
    pure fn insert(&self, value: T) -> TreeSet<T> {
        TreeSet { map: self.map.insert(value, ()) }
    }

    /// Remove a value from the set.
    pure fn remove(&self, value: &T) -> TreeSet<T> {
        TreeSet { map: self.map.remove(value) }
    }
}

impl <T: Ord> TreeSet<T> {
    /// Create an empty TreeSet
    static pure fn new() -> TreeSet<T> {
        TreeSet { map: TreeMap::new::<T, ()>() }
    }

    /// Visit all values in reverse order
    pure fn each_reverse(&self, f: fn(&T) -> bool) {
        self.map.each_key_reverse(f)
    }

    /// Get a lazy iterator over the values in the set.
    /// Requires that it be frozen (immutable).
    pure fn iter(&self) -> TreeSetIterator/&self<T> {
        TreeSetIterator { iter: self.map.iter() }
    }
}

/// Lazy forward iterator over a set
pub struct TreeSetIterator<T> {
    priv iter: TreeMapIterator<T, ()>
}

impl <T: Ord> TreeSetIterator<T> {
    /// Returns the current node, or None if this iterator is at the end.
    fn get(&const self) -> Option<&self/T> {
        match self.iter.get() {
            None => None,
            Some((k, _)) => Some(k)
        }
    }

    /// Advance the iterator to the next node (in order). If this iterator is
    /// finished, does nothing.
    fn next(self) -> TreeSetIterator/&self<T> {
        TreeSetIterator { iter: self.iter.next() }
    }
}

// Nodes keep track of their level in the tree, starting at 1 in the
// leaves and with a red child sharing the level of the parent.
struct TreeNode<K, V> {
    level: uint,
    key: @K,
    value: @V,
    left: TreeMap<K, V>,
    right: TreeMap<K, V>,
}

impl <K: Ord, V> TreeNode<K, V> {
    #[inline(always)]
    static pure fn new(key: @K, value: @V) -> TreeNode<K, V> {
        TreeNode {
            level: 1,
            key: key,
            value: value,
            left: Empty,
            right: Empty,
        }
    }
}

// Remove left horizontal link by rotating right
pure fn skew<K: Ord, V>(node: @TreeNode<K, V>) -> @TreeNode<K, V> {
    match node.left {
        Node(ref left) if node.level == left.level => {
            @TreeNode {
                level: left.level,
                key: left.key,
                value: left.value,
                left: left.left,
                right: Node(@TreeNode {
                    level: node.level,
                    key: node.key,
                    value: node.value,
                    left: left.right,
                    right: node.right,
                })
            }
        }
        _ => node,
    }
}

// Remove dual horizontal link by rotating left and increasing level of
// the parent
pure fn split<K: Ord, V>(node: @TreeNode<K, V>) -> @TreeNode<K, V> {
    match node.right {
        Node(ref r) => {
            match r.right {
                Node(rr) if r.level == rr.level => {
                    @TreeNode {
                        level: r.level + 1,
                        key: r.key,
                        value: r.value,
                        left: Node(@TreeNode {
                            level: node.level,
                            key: node.key,
                            value: node.value,
                            left: node.left,
                            right: r.left,
                        }),
                        right: r.right,
                    }
                }
                _ => node,
            }
        }
        _ => node,
    }
}

#[cfg(test)]
mod test_treemap {
    use super::*;
    use core::str;

    #[test]
    fn find_empty() {
        let m = TreeMap::new::<int, int>();
        assert m.find(&5) == None;
    }

    #[test]
    fn find_not_found() {
        let mut m = TreeMap::new();
        m = m.insert(1, 2);
        m = m.insert(5, 3);
        m = m.insert(9, 3);
        assert m.find(&2) == None;
    }

    #[test]
    fn insert_replace() {
        let mut m = TreeMap::new();
        m = m.insert(5, 2);
        m = m.insert(2, 9);
        m = m.insert(2, 11);
        assert m.find(&2).unwrap() == &11;
    }

    #[test]
    fn u8_map() {
        let mut m = TreeMap::new();

        let k1 = str::to_bytes(~"foo");
        let k2 = str::to_bytes(~"bar");
        let v1 = str::to_bytes(~"baz");
        let v2 = str::to_bytes(~"foobar");

        m = m.insert(k1, v1);
        m = m.insert(k2, v2);

        assert m.find(&k2) == Some(&v2);
        assert m.find(&k1) == Some(&v1);
    }

    fn check_equal<K: Eq Ord, V: Eq>(ctrl: &[(K, V)], map: &TreeMap<K, V>) {
        assert ctrl.is_empty() == map.is_empty();
        for ctrl.each |x| {
            let &(k, v) = x;
            assert map.find(&k).unwrap() == &v
        }
        for map.each |map_k, map_v| {
            let mut found = false;
            for ctrl.each |x| {
                let &(ctrl_k, ctrl_v) = x;
                if *map_k == ctrl_k {
                    assert *map_v == ctrl_v;
                    found = true;
                    break;
                }
            }
            assert found;
        }
    }

    fn check_left<K: Ord, V>(
        node: &TreeMap<K, V>,
        parent: &@TreeNode<K, V>
    ) {
        match *node {
          Node(ref r) => {
            assert r.key < parent.key;
            assert r.level == parent.level - 1; // left is black
            check_left(&r.left, r);
            check_right(&r.right, r, false);
          }
          Empty => assert parent.level == 1 // parent is leaf
        }
    }

    fn check_right<K: Ord, V>(
        node: &TreeMap<K, V>,
        parent: &@TreeNode<K, V>,
        parent_red: bool
    ) {
        match *node {
          Node(ref r) => {
            assert r.key > parent.key;
            let red = r.level == parent.level;
            if parent_red { assert !red } // no dual horizontal links
            assert red || r.level == parent.level - 1; // right red or black
            check_left(&r.left, r);
            check_right(&r.right, r, red);
          }
          Empty => assert parent.level == 1 // parent is leaf
        }
    }

    fn check_structure<K: Ord, V>(map: &TreeMap<K, V>) {
        match *map {
          Node(ref r) => {
            check_left(&r.left, r);
            check_right(&r.right, r, false);
          }
          Empty => ()
        }
    }

    #[test]
    fn test_rand_int() {
        let mut map = TreeMap::new::<int, int>();
        let mut ctrl = ~[];

        check_equal(ctrl, &map);
        assert map.find(&5).is_none();

        let rng = rand::seeded_rng(&~[42]);

        for 3.times {
            for 90.times {
                let k = rng.gen_int();
                let v = rng.gen_int();
                if !ctrl.contains(&(k, v)) {
                    map = map.insert(k, v);
                    ctrl.push((k, v));
                    check_structure(&map);
                    check_equal(ctrl, &map);
                }
            }

            for 30.times {
                let r = rng.gen_uint_range(0, ctrl.len());
                let (key, _) = vec::remove(&mut ctrl, r);
                map = map.remove(&key);
                check_structure(&map);
                check_equal(ctrl, &map);
            }
        }
    }

    #[test]
    fn test_len() {
        let mut m = TreeMap::new();
        m = m.insert(3, 6);
        assert m.len() == 1;
        m = m.insert(0, 0);
        assert m.len() == 2;
        m = m.insert(4, 8);
        assert m.len() == 3;
        m = m.remove(&3);
        assert m.len() == 2;
        m = m.remove(&5);
        assert m.len() == 2;
        m = m.insert(2, 4);
        assert m.len() == 3;
        m = m.insert(1, 2);
        assert m.len() == 4;
    }

    #[test]
    fn test_each() {
        let mut m = TreeMap::new();

        m = m.insert(3, 6);
        m = m.insert(0, 0);
        m = m.insert(4, 8);
        m = m.insert(2, 4);
        m = m.insert(1, 2);

        let mut n = 0;
        for m.each |k, v| {
            assert *k == n;
            assert *v == n * 2;
            n += 1;
        }
    }

    #[test]
    fn test_each_reverse() {
        let mut m = TreeMap::new();

        m = m.insert(3, 6);
        m = m.insert(0, 0);
        m = m.insert(4, 8);
        m = m.insert(2, 4);
        m = m.insert(1, 2);

        let mut n = 4;
        for m.each_reverse |k, v| {
            assert *k == n;
            assert *v == n * 2;
            n -= 1;
        }
    }

    #[test]
    fn test_eq() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert a == b;
        a = a.insert(0, 5);
        assert a != b;
        b = b.insert(0, 4);
        assert a != b;
        a = a.insert(5, 19);
        assert a != b;
        b = b.insert(0, 5);
        assert a != b;
        b = b.insert(5, 19);
        assert a == b;
    }

    #[test]
    fn test_lt() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert !(a < b) && !(b < a);
        b = b.insert(0, 5);
        assert a < b;
        a = a.insert(0, 7);
        assert !(a < b) && !(b < a);
        b = b.insert(-2, 0);
        assert b < a;
        a = a.insert(-5, 2);
        assert a < b;
        a = a.insert(6, 2);
        assert a < b && !(b < a);
    }

    #[test]
    fn test_ord() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert a <= b && a >= b;
        a = a.insert(1, 1);
        assert a > b && a >= b;
        assert b < a && b <= a;
        b = b.insert(2, 2);
        assert b > a && b >= a;
        assert a < b && a <= b;
    }

    #[test]
    fn test_lazy_iterator() {
        let mut m = TreeMap::new();
        let (x1, y1) = (2, 5);
        let (x2, y2) = (9, 12);
        let (x3, y3) = (20, -3);
        let (x4, y4) = (29, 5);
        let (x5, y5) = (103, 3);

        m = m.insert(x1, y1);
        m = m.insert(x2, y2);
        m = m.insert(x3, y3);
        m = m.insert(x4, y4);
        m = m.insert(x5, y5);

        let m = m;
        let mut iter = m.iter();

        // FIXME: #4492 (ICE): iter.next() == Some((&x1, &y1))

        iter = iter.next();
        assert iter.get().unwrap() == (&x1, &y1);
        iter = iter.next();
        assert iter.get().unwrap() == (&x2, &y2);
        iter = iter.next();
        assert iter.get().unwrap() == (&x3, &y3);
        iter = iter.next();
        assert iter.get().unwrap() == (&x4, &y4);
        iter = iter.next();
        assert iter.get().unwrap() == (&x5, &y5);

        iter = iter.next();
        assert iter.get().is_none();
    }
}

#[cfg(test)]
mod test_set {
    use super::*;

    #[test]
    fn test_disjoint() {
        let mut xs = TreeSet::new();
        let mut ys = TreeSet::new();
        assert xs.is_disjoint(&ys);
        assert ys.is_disjoint(&xs);
        xs = xs.insert(5);
        ys = ys.insert(11);
        assert xs.is_disjoint(&ys);
        assert ys.is_disjoint(&xs);
        xs = xs.insert(7);
        xs = xs.insert(19);
        xs = xs.insert(4);
        ys = ys.insert(2);
        ys = ys.insert(-11);
        assert xs.is_disjoint(&ys);
        assert ys.is_disjoint(&xs);
        ys = ys.insert(7);
        assert !xs.is_disjoint(&ys);
        assert !ys.is_disjoint(&xs);
    }

    #[test]
    fn test_subset_and_superset() {
        let mut a = TreeSet::new();
        a = a.insert(0);
        a = a.insert(5);
        a = a.insert(11);
        a = a.insert(7);

        let mut b = TreeSet::new();
        b = b.insert(0);
        b = b.insert(7);
        b = b.insert(19);
        b = b.insert(250);
        b = b.insert(11);
        b = b.insert(200);

        assert !a.is_subset(&b);
        assert !a.is_superset(&b);
        assert !b.is_subset(&a);
        assert !b.is_superset(&a);

        b = b.insert(5);

        assert a.is_subset(&b);
        assert !a.is_superset(&b);
        assert !b.is_subset(&a);
        assert b.is_superset(&a);
    }

    #[test]
    fn test_each() {
        let mut m = TreeSet::new();

        m = m.insert(3);
        m = m.insert(0);
        m = m.insert(4);
        m = m.insert(2);
        m = m.insert(1);

        let mut n = 0;
        for m.each |x| {
            assert *x == n;
            n += 1
        }
    }

    #[test]
    fn test_each_reverse() {
        let mut m = TreeSet::new();

        m = m.insert(3);
        m = m.insert(0);
        m = m.insert(4);
        m = m.insert(2);
        m = m.insert(1);

        let mut n = 4;
        for m.each_reverse |x| {
            assert *x == n;
            n -= 1
        }
    }

    #[test]
    fn test_intersection() {
        let mut a = TreeSet::new();
        let mut b = TreeSet::new();

        a = a.insert(11);
        a = a.insert(1);
        a = a.insert(3);
        a = a.insert(77);
        a = a.insert(103);
        a = a.insert(5);
        a = a.insert(-5);

        b = b.insert(2);
        b = b.insert(11);
        b = b.insert(77);
        b = b.insert(-9);
        b = b.insert(-42);
        b = b.insert(5);
        b = b.insert(3);

        let mut i = 0;
        let expected = [3, 5, 11, 77];
        for a.intersection(&b) |x| {
            assert *x == expected[i];
            i += 1
        }
        assert i == expected.len();
    }

    #[test]
    fn test_difference() {
        let mut a = TreeSet::new();
        let mut b = TreeSet::new();

        a = a.insert(1);
        a = a.insert(3);
        a = a.insert(5);
        a = a.insert(9);
        a = a.insert(11);

        b = b.insert(3);
        b = b.insert(9);

        let mut i = 0;
        let expected = [1, 5, 11];
        for a.difference(&b) |x| {
            assert *x == expected[i];
            i += 1
        }
        assert i == expected.len();
    }

    #[test]
    fn test_symmetric_difference() {
        let mut a = TreeSet::new();
        let mut b = TreeSet::new();

        a = a.insert(1);
        a = a.insert(3);
        a = a.insert(5);
        a = a.insert(9);
        a = a.insert(11);

        b = b.insert(-2);
        b = b.insert(3);
        b = b.insert(9);
        b = b.insert(14);
        b = b.insert(22);

        let mut i = 0;
        let expected = [-2, 1, 5, 11, 14, 22];
        for a.symmetric_difference(&b) |x| {
            assert *x == expected[i];
            i += 1
        }
        assert i == expected.len();
    }

    #[test]
    fn test_union() {
        let mut a = TreeSet::new();
        let mut b = TreeSet::new();

        a = a.insert(1);
        a = a.insert(3);
        a = a.insert(5);
        a = a.insert(9);
        a = a.insert(11);
        a = a.insert(16);
        a = a.insert(19);
        a = a.insert(24);

        b = b.insert(-2);
        b = b.insert(1);
        b = b.insert(5);
        b = b.insert(9);
        b = b.insert(13);
        b = b.insert(19);

        let mut i = 0;
        let expected = [-2, 1, 3, 5, 9, 11, 13, 16, 19, 24];
        for a.union(&b) |x| {
            assert *x == expected[i];
            i += 1
        }
        assert i == expected.len();
    }
}
