// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Abstract hashing support.
 *
 * This module represents a generic way to support hashing of values. It
 * contains an abstract supertrait, `Hasher`, and a subtrait `StreamHasher`
 * that describe a type that can compute a hash of a value. `Hasher` is the
 * root trait that can hash a value, but does not provide any assistance in
 * actually hashing the value.  `StreamHasher`, along with the related trait
 * `StreamState`, provide a way to stream in the bytes of a value into a
 * hasher.
 *
 * Hashing functions are difficult to write, so it's not recommended for most
 * users to implement the `Hasher` trait. Instead it is recommended that they
 * use the `std::hash2::sip::SipHasher` hasher, which provides both a good
 * speed and strong _keyed_ hashing.
 */

use cast;
use container::Container;
use iter::Iterator;
use mem;
use option::{Option, Some, None};
use rc::Rc;
use str::{StrSlice};
use vec::ImmutableVector;

/// Reexport the `sip::hash` function as our default hasher.
pub use hash = self::sip::hash;

/// Reexport the `sip::hash_with_keys` function as our default hasher.
pub use hash_with_keys = self::sip::hash_with_keys;

pub mod sip;

/// A trait that represents a type that can be hashed by an abstract hasher.
pub trait Hash<S = sip::SipState> {
    /// Compute a hash of the value.
    fn hash(&self, state: S) -> u64;
}

/// A trait that computes a hash for a value.
pub trait Hasher<S> {
    /// Return a hash state that will be used to compute the hash.
    fn state(&self) -> S;

    /// Compute a hash of the value.
    #[inline]
    fn hash<T: Hash<S>>(&self, value: &T) -> u64 {
        value.hash(self.state())
    }
}

/// A trait that represents a type that computes a hash from a stream of
/// bytes. This should be used with `Hash` and `Hasher`.
pub trait StreamState {
    /// Input `&[u8]` into the hash.
    fn input_bytes(&mut self, bytes: &[u8]);

    /// Input `()` into the hash.
    #[inline]
    fn input_nil(&mut self) { }

    /// Input `u8` into the hash.
    #[inline]
    fn input_u8(&mut self, v: u8) {
        self.input_bytes([v])
    }

    /// Input `u16` into the hash.
    #[inline]
    fn input_u16(&mut self, v: u16) {
        // huonw did some benchmarking in #11863 and compared the performance
        // of manually extracting out the bytes of an integer with `[(x >> 8)
        // as u8, x as u8]` with using a cast. It turns that while at an
        // --opt-level=1, they are about the same, at --opt-level=2 and higher,
        // casting is about 40% faster for u64, 10% faster for u32, and about
        // the same for u16 and u8.

        unsafe {
            let value = mem::to_le16(v as i16);
            let bytes: [u8, .. 2] = cast::transmute(value);
            self.input_bytes(bytes)
        }
    }

    /// Input `u32` into the hash.
    #[inline]
    fn input_u32(&mut self, v: u32) {
        // See justification for using transmute in `.input_u16`.

        unsafe {
            let value = mem::to_le32(v as i32);
            let bytes: [u8, .. 4] = cast::transmute(value);
            self.input_bytes(bytes)
        }
    }

    /// Input `u64` into the hash.
    #[inline]
    fn input_u64(&mut self, v: u64) {
        // See justification for using transmute in `.input_u16`.

        unsafe {
            let value = mem::to_le64(v as i64);
            let bytes: [u8, .. 8] = cast::transmute(value);
            self.input_bytes(bytes)
        }
    }

    /// Input `uint` into the hash.
    #[inline]
    #[cfg(target_word_size = "32")]
    fn input_uint(&mut self, v: uint) {
        self.input_u32(v as u32)
    }

    /// Input `uint` into the hash.
    #[inline]
    #[cfg(target_word_size = "64")]
    fn input_uint(&mut self, v: uint) {
        self.input_u64(v as u64)
    }

    /// Input `i8` into the hash.
    #[inline]
    fn input_i8(&mut self, v: i8) {
        self.input_u8(v as u8)
    }

    /// Input `i16` into the hash.
    #[inline]
    fn input_i16(&mut self, v: i16) {
        self.input_u16(v as u16)
    }

    /// Input `i32` into the hash.
    #[inline]
    fn input_i32(&mut self, v: i32) {
        self.input_u32(v as u32)
    }

    /// Input `i64` into the hash.
    #[inline]
    fn input_i64(&mut self, v: i64) {
        self.input_u64(v as u64)
    }

    /// Input `int` into the hash.
    #[inline]
    fn input_int(&mut self, v: int) {
        self.input_uint(v as uint)
    }

    /// Input `f32` into the hash.
    #[inline]
    fn input_f32(&mut self, v: f32) {
        unsafe {
            // 0.0 == -0.0 so they should also have the same hashcode
            let v: u32 = cast::transmute(if v == -0.0 { 0.0 } else { v });
            self.input_u32(v)
        }
    }

    /// Input `f64` into the hash.
    #[inline]
    fn input_f64(&mut self, v: f64) {
        unsafe {
            // 0.0 == -0.0 so they should also have the same hashcode
            let v: u64 = cast::transmute(if v == -0.0 { 0.0 } else { v });
            self.input_u64(v)
        }
    }

    /// Input `bool` into the hash.
    #[inline]
    fn input_bool(&mut self, v: bool) {
        self.input_u8(v as u8)
    }

    /// Input `char` into the hash.
    #[inline]
    fn input_char(&mut self, v: char) {
        self.input_u32(v as u32)
    }

    /// Input `&str` into the hash.
    #[inline]
    fn input_str(&mut self, v: &str) {
        self.input_bytes(v.as_bytes());
        self.input_u8(0xff);
    }

    /// Input `&[T]` into the hash.
    #[inline]
    fn input_slice<T: StreamHash<Self>>(&mut self, v: &[T]) {
        self.input_uint(v.len());
        for elt in v.iter() {
            elt.input(self)
        }
    }

    /// Input `*T` into the hash.
    #[inline]
    fn input_ptr<T>(&mut self, v: *T) {
        // NB: raw-pointer `Hash` does _not_ dereference
        // to the target; it just gives you the pointer-bytes.
        self.input_uint(v as uint)
    }

    /// Input `*mut T` into the hash.
    #[inline]
    fn input_mut_ptr<T>(&mut self, v: *mut T) {
        // NB: raw-pointer `Hash` does _not_ dereference
        // to the target; it just gives you the pointer-bytes.
        self.input_uint(v as uint)
    }

    /// Return the computed hash from the state.
    fn result(&self) -> u64;
}

/// A helper trait that inputs the hash into the hash state.
pub trait StreamHash<S: StreamState = sip::SipState>: Hash<S> {
    /// Input the hash into the hash state.
    fn input(&self, state: &mut S);
}

//////////////////////////////////////////////////////////////////////////////

macro_rules! impl_hash(
    ($ty:ty => $e:expr) => (
        impl<'a, S: StreamState> Hash<S> for $ty {
            #[inline]
            fn hash(&self, mut state: S) -> u64 {
                self.input(&mut state);
                state.result()
            }
        }

        impl<'a, S: StreamState> StreamHash<S> for $ty {
            #[inline]
            fn input(&self, state: &mut S) {
                $e
            }
        }
    )
)

impl_hash!(u8 => state.input_u8(*self))
impl_hash!(u16 => state.input_u16(*self))
impl_hash!(u32 => state.input_u32(*self))
impl_hash!(u64 => state.input_u64(*self))
impl_hash!(uint => state.input_uint(*self))
impl_hash!(i8 => state.input_i8(*self))
impl_hash!(i16 => state.input_i16(*self))
impl_hash!(i32 => state.input_i32(*self))
impl_hash!(i64 => state.input_i64(*self))
impl_hash!(int => state.input_int(*self))
impl_hash!(f32 => state.input_f32(*self))
impl_hash!(f64 => state.input_f64(*self))
impl_hash!(bool => state.input_bool(*self))
impl_hash!(char => state.input_char(*self))
impl_hash!(&'a str => state.input_str(*self))
impl_hash!(~str => state.input_str(*self))

macro_rules! impl_input_tuple(
    () => (
        impl<S: StreamState> Hash<S> for () {
            #[inline]
            fn hash(&self, mut state: S) -> u64 {
                self.input(&mut state);
                state.result()
            }
        }

        impl<S: StreamState> StreamHash<S> for () {
            #[inline]
            fn input(&self, state: &mut S) {
                state.input_nil();
            }
        }
    );

    ($A:ident $($B:ident)*) => (
        impl<
            S: StreamState,
            $A: StreamHash<S> $(, $B: StreamHash<S>)*
        > Hash<S> for ($A, $($B),*) {
            #[inline]
            fn hash(&self, mut state: S) -> u64 {
                self.input(&mut state);
                state.result()
            }
        }

        impl<
            S: StreamState,
            $A: StreamHash<S> $(, $B: StreamHash<S>)*
        > StreamHash<S> for ($A, $($B),*) {
            #[inline]
            fn input(&self, state: &mut S) {
                match *self {
                    (ref $A, $(ref $B),*) => {
                        $A.input(state);
                        $(
                            $B.input(state);
                        )*
                    }
                }
            }
        }
    );
)

impl_input_tuple!()
impl_input_tuple!(A0)
impl_input_tuple!(A0 A1)
impl_input_tuple!(A0 A1 A2)
impl_input_tuple!(A0 A1 A2 A3)
impl_input_tuple!(A0 A1 A2 A3 A4)
impl_input_tuple!(A0 A1 A2 A3 A4 A5)
impl_input_tuple!(A0 A1 A2 A3 A4 A5 A6)
impl_input_tuple!(A0 A1 A2 A3 A4 A5 A6 A7)

macro_rules! impl_input_compound(
    ($ty:ty => $e:expr) => (
        impl<'a, S: StreamState, T: StreamHash<S>> Hash<S> for $ty {
            #[inline]
            fn hash(&self, mut state: S) -> u64 {
                self.input(&mut state);
                state.result()
            }
        }

        impl<'a, S: StreamState, T: StreamHash<S>> StreamHash<S> for $ty {
            #[inline]
            fn input(&self, state: &mut S) {
                $e
            }
        }
    )
)

impl_input_compound!(&'a [T] => state.input_slice(*self))
impl_input_compound!(&'a mut [T] => state.input_slice(*self))
impl_input_compound!(~[T] => state.input_slice(*self))
impl_input_compound!(&'a T => (**self).input(state))
impl_input_compound!(&'a mut T => (**self).input(state))
impl_input_compound!(~T => (*self).input(state))
impl_input_compound!(@T => (*self).input(state))
impl_input_compound!(Rc<T> => self.borrow().input(state))

impl<S: StreamState, T: StreamHash<S>> Hash<S> for Option<T> {
    #[inline]
    fn hash(&self, mut state: S) -> u64 {
        self.input(&mut state);
        state.result()
    }
}

impl<S: StreamState, T: StreamHash<S>> StreamHash<S> for Option<T> {
    #[inline]
    fn input(&self, state: &mut S) {
        match *self {
            Some(ref x) => {
                0u8.input(state);
                x.input(state);
            }
            None => {
                0u8.input(state);
            }
        }
    }
}

impl<S: StreamState, T> Hash<S> for *T {
    #[inline]
    fn hash(&self, mut state: S) -> u64 {
        self.input(&mut state);
        state.result()
    }
}

impl<S: StreamState, T> StreamHash<S> for *T {
    #[inline]
    fn input(&self, state: &mut S) {
        state.input_ptr(*self)
    }
}

impl<S: StreamState, T> Hash<S> for *mut T {
    #[inline]
    fn hash(&self, mut state: S) -> u64 {
        self.input(&mut state);
        state.result()
    }
}

impl<S: StreamState, T> StreamHash<S> for *mut T {
    #[inline]
    fn input(&self, state: &mut S) {
        state.input_mut_ptr(*self)
    }
}

//////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use cast;
    use iter::{Iterator};
    use option::{Some, None};
    use vec::ImmutableVector;

    use super::{Hash, StreamState, Hasher};

    struct MyStreamHasher;

    impl Hasher<MyStreamState> for MyStreamHasher {
        fn state(&self) -> MyStreamState {
            MyStreamState { hash: 0 }
        }
    }

    struct MyStreamState {
        hash: u64,
    }

    impl StreamState for MyStreamState {
        // Most things we'll just add up the bytes.
        fn input_bytes(&mut self, buf: &[u8]) {
            for byte in buf.iter() {
                self.hash += *byte as u64;
            }
        }

        // But we want to do something interesting with u16.
        fn input_u16(&mut self, x: u16) {
            self.hash += (x as u64 * 7) % 100;
        }

        fn result(&self) -> u64 {
            self.hash
        }
    }

    #[test]
    fn test_stream_hasher() {
        let hasher = MyStreamHasher;

        assert_eq!(hasher.hash(&()), 0);

        assert_eq!(hasher.hash(&5u8), 5);
        assert_eq!(hasher.hash(&5u16), 35);
        assert_eq!(hasher.hash(&5u32), 5);
        assert_eq!(hasher.hash(&5u64), 5);
        assert_eq!(hasher.hash(&5u), 5);

        assert_eq!(hasher.hash(&5i8), 5);
        assert_eq!(hasher.hash(&5i16), 35);
        assert_eq!(hasher.hash(&5i32), 5);
        assert_eq!(hasher.hash(&5i64), 5);
        assert_eq!(hasher.hash(&5i), 5);

        assert_eq!(hasher.hash(&5f32), 224);
        assert_eq!(hasher.hash(&5f64), 84);

        assert_eq!(hasher.hash(&false), 0);
        assert_eq!(hasher.hash(&true), 1);

        assert_eq!(hasher.hash(&'a'), 97);

        assert_eq!(hasher.hash(& &"a"), 97 + 0xFF);
        assert_eq!(hasher.hash(& &[1u8, 2u8, 3u8]), 9);

        unsafe {
            let ptr: *int = cast::transmute(5);
            assert_eq!(hasher.hash(&ptr), 5);
        }

    }

    struct Custom {
        hash: u64
    }

    impl Hash<()> for Custom {
        fn hash(&self, _hasher: ()) -> u64 {
            self.hash
        }
    }

    #[test]
    fn test_custom_hasher() {
        let custom = Custom { hash: 5 };
        assert_eq!(custom.hash(()), 5);
    }
}
