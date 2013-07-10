// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use cast;
use iterator::{Iterator, IteratorUtil};
use libc;
use ops::Drop;
use option::{Option, Some, None};
use ptr::IsNullPtr;
use ptr;
use str::StrSlice;
use vec::ImmutableVector;

/**
 * The representation of a C String.
 *
 * This structure wraps a `*libc::c_char`, and will automatically free the
 * memory it is pointing to when it goes out of scope.
 */
pub struct CStr {
    priv buf: *libc::c_char,
    priv owns_buffer: bool,
}

impl<'self> CStr {
    /**
     */
    pub fn new(buf: *libc::c_char) -> CStr {
        if buf.is_null() {
            fail!("Passed a null pointer!");
        }
        CStr { buf: buf, owns_buffer: false }
    }

    /**
     */
    pub fn new_with_ownership(buf: *libc::c_char) -> CStr {
        if buf.is_null() {
            fail!("Passed a null pointer!");
        }
        CStr { buf: buf, owns_buffer: true }
    }

    /**
     * Return the length of the c string.
     *
     * This performs O(n) steps to count the number of bytes in the string.
     */
    pub fn len(&self) -> uint {
        self.iter().count(|ch| ch != 0)
    }

    /**
     * Returns true if the CStr does not wrap a `*libc::c_char`.
     */
    #[inline]
    pub fn is_null(&self) -> bool {
        self.buf.is_null()
    }

    /**
     * Returns true if the CStr wraps a `*libc::c_char`.
     */
    #[inline]
    pub fn is_not_null(&self) -> bool {
        self.buf.is_not_null()
    }

    /**
     * Calls a closure with a reference to the underlying `*libc::c_char`.
     */
    #[inline]
    pub fn as_ptr(&self) -> &'self libc::c_char {
        unsafe { cast::transmute(self.buf) }
    }

    /**
     * Calls a closure with a mutable reference to the underlying `*libc::c_char`.
     */
    #[inline]
    pub fn as_mut_ptr(&mut self) -> &'self libc::c_char {
        unsafe { cast::transmute(self.buf) }
    }

    /**
     * Converts the CStr into a `&[u8]` without copying.
     */
    #[inline]
    pub fn as_bytes(&self) -> &'self [u8] {
        unsafe { cast::transmute((self.buf, self.len() + 1)) }
    }

    /**
     * Return a CStr iterator.
     */
    fn iter(&self) -> CStrIterator<'self> {
        CStrIterator { ptr: self.as_ptr() }
    }
}

impl Drop for CStr {
    fn drop(&self) {
        if self.owns_buffer && self.buf.is_not_null() {
            unsafe {
                libc::free(self.buf as *libc::c_void);
            }
        }
    }
}

/**
 * A generic trait for converting a value to a CStr.
 */
pub trait ToCStr {
    /**
     * Create a C String.
     */
    fn to_c_str(&self) -> CStr;
}

impl<'self> ToCStr for &'self str {
    /**
     * Create a C String from a `&str`.
     */
    #[inline]
    fn to_c_str(&self) -> CStr {
        self.as_bytes().to_c_str()
    }
}

impl<'self> ToCStr for &'self [u8] {
    /**
     * Create a C String from a `&[u8]`.
     */
    fn to_c_str(&self) -> CStr {
        do self.as_imm_buf |self_buf, self_len| {
            unsafe {
                let buf = libc::malloc(self_len as u64 + 1) as *mut u8;
                if buf.is_null() {
                    fail!("failed to allocate memory!");
                }

                ptr::copy_memory(buf, self_buf, self_len);
                *ptr::mut_offset(buf, self_len) = 0;

                CStr::new_with_ownership(buf as *libc::c_char)
            }
        }
    }
}

/**
 * External iterator for a CStr's bytes.
 *
 * Use with the `std::iterator` module.
 */
pub struct CStrIterator<'self> {
    priv ptr: &'self libc::c_char,
}

impl<'self> Iterator<libc::c_char> for CStrIterator<'self> {
    /**
     * Advance the iterator.
     */
    fn next(&mut self) -> Option<libc::c_char> {
        let ch = *self.ptr;

        if ch == 0 {
            None
        } else {
            self.ptr = unsafe { cast::transmute(ptr::offset(self.ptr, 1)) };
            Some(ch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libc;
    use ptr;

    #[test]
    fn test_len() {
        assert_eq!("".to_c_str().len(), 0);
        assert_eq!("hello".to_c_str().len(), 5);
    }

    #[test]
    fn test_as_ptr() {
        let c_str = "".to_c_str();
        unsafe {
            assert_eq!(*ptr::offset(c_str.as_ptr(), 0), 0);
        }

        let c_str = "hello".to_c_str();
        let ptr = c_str.as_ptr();
        unsafe {
            assert_eq!(*ptr::offset(ptr, 0), 'h' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 1), 'e' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 2), 'l' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 3), 'l' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 4), 'o' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 5), 0);
        }
    }

    #[test]
    fn test_as_mut_ptr() {
        let mut c_str = "".to_c_str();
        unsafe {
            assert_eq!(*ptr::offset(c_str.as_mut_ptr(), 0), 0);
        }

        let mut c_str = "hello".to_c_str();
        let ptr = c_str.as_mut_ptr();
        unsafe {
            assert_eq!(*ptr::offset(ptr, 0), 'h' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 1), 'e' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 2), 'l' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 3), 'l' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 4), 'o' as libc::c_char);
            assert_eq!(*ptr::offset(ptr, 5), 0);
        }
    }
}
