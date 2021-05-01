use crate::StackVec;
#[cfg(feature = "std")]
use std::borrow::Cow;
use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::{Add, AddAssign, Deref, DerefMut};
use std::str::{FromStr, Utf8Error};
use std::{fmt, ptr, str};

/// A possible error value when converting a `StackStr` from a UTF-8 byte vector.
///
/// This type is the error type for the [`from_utf8`] method on [`StackStr`]. It
/// is designed in such a way to carefully avoid reallocations: the
/// [`into_bytes`] method will give back the byte vector that was used in the
/// conversion attempt.
///
/// [`from_utf8`]: StackStr::from_utf8
/// [`into_bytes`]: FromUtf8Error::into_bytes
///
/// # Examples
///
/// ```
/// use stack_buf::{StackStr, stack_vec};
///
/// // some invalid bytes, in a vector
/// let bytes = stack_vec![0, 159];
///
/// let value = StackStr::<2>::from_utf8(bytes);
///
/// assert!(value.is_err());
/// assert_eq!(stack_vec![0, 159], value.unwrap_err().into_bytes());
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "str")))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FromUtf8Error<const N: usize> {
    bytes: StackVec<u8, N>,
    error: Utf8Error,
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> std::error::Error for FromUtf8Error<N> {}

impl<const N: usize> fmt::Display for FromUtf8Error<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<const N: usize> FromUtf8Error<N> {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackStr, stack_vec};
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = stack_vec![0, 159];
    ///
    /// let value = StackStr::<2>::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{stack_vec, StackStr};
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = stack_vec![0, 159];
    ///
    /// let value = StackStr::<2>::from_utf8(bytes);
    ///
    /// assert_eq!(stack_vec![0, 159], value.unwrap_err().into_bytes());
    /// ```
    #[inline]
    pub fn into_bytes(self) -> StackVec<u8, N> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackStr, stack_vec};
    ///
    /// // some invalid bytes, in a vector
    /// let bytes = stack_vec![0, 159];
    ///
    /// let error = StackStr::<2>::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    #[inline]
    pub const fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

/// A string with a fixed capacity and stored on the stack.
///
/// The `StackStr` is a string backed by a fixed size `StackVec`. It keeps track
/// of its length, and is parameterized by `N` for the maximum capacity.
///
/// `N` is of type `usize` but is range limited to `u32::MAX`; attempting to create
/// string with larger size will panic.
#[cfg_attr(docsrs, doc(cfg(feature = "str")))]
pub struct StackStr<const N: usize> {
    vec: StackVec<u8, N>,
}

impl<const N: usize> StackStr<N> {
    /// Creates a new empty `StackStr`.
    ///
    /// The maximum capacity is given by the generic parameter `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s: StackStr<3> = StackStr::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        StackStr {
            vec: StackVec::new(),
        }
    }

    /// Converts a vector of bytes to a `StackStr`.
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why the
    /// provided bytes are not UTF-8. The vector you moved in is also included.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackStr, stack_vec};
    ///
    /// // some bytes, in a vector
    /// let sparkle_heart = stack_vec![240, 159, 146, 150];
    ///
    /// // We know these bytes are valid, so we'll use `unwrap()`.
    /// let sparkle_heart = StackStr::from_utf8(sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// use stack_buf::{StackStr, stack_vec};
    ///
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = stack_vec![0, 159, 146, 150];
    ///
    /// assert!(StackStr::from_utf8(sparkle_heart).is_err());
    /// ```
    ///
    /// See the docs for [`FromUtf8Error`] for more details on what you can do
    /// with this error.
    ///
    /// [`from_utf8_unchecked`]: StackStr::from_utf8_unchecked
    /// [`into_bytes`]: StackStr::into_bytes
    #[inline]
    pub fn from_utf8(vec: StackVec<u8, N>) -> Result<Self, FromUtf8Error<N>> {
        match str::from_utf8(&vec) {
            Ok(..) => Ok(StackStr { vec }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    /// Converts a vector of bytes to a `StackStr` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more details.
    ///
    /// [`from_utf8`]: StackStr::from_utf8
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `StackStr`, as the rest of
    /// the library assumes that `StackStr`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackStr, stack_vec};
    ///
    /// // some bytes, in a vector
    /// let sparkle_heart = stack_vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     StackStr::from_utf8_unchecked(sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    pub const unsafe fn from_utf8_unchecked(bytes: StackVec<u8, N>) -> Self {
        StackStr { vec: bytes }
    }

    /// Converts a `StackStr` into a byte vector.
    ///
    /// This consumes the `StackStr`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s = StackStr::<5>::from("hello");
    /// let bytes = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> StackVec<u8, N> {
        self.vec
    }

    /// Returns the length of this `StackStr`, in bytes, not [`char`]s or
    /// graphemes. In other words, it may not be what a human considers the
    /// length of the string.
    #[inline]
    pub const fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns whether the string is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the `StackStr` is completely filled to its capacity, false otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<1>::new();
    /// assert!(!s.is_full());
    /// s.push('a');
    /// assert!(s.is_full());
    /// ```
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Returns this `StackStr`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s = StackStr::<10>::new();
    ///
    /// assert_eq!(s.capacity(), 10);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Returns the capacity left in the `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<3>::from("123");
    /// s.pop();
    /// assert_eq!(s.remaining_capacity(), 1);
    /// ```
    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Sets the `StackStr`’s length without dropping or moving out elements
    ///
    /// # Safety
    /// This method is `unsafe` because it changes the notion of the
    /// number of “valid” elements in the vector.
    ///
    /// This method uses *debug assertions* to check that `length` is
    /// not greater than the capacity.
    #[inline]
    pub unsafe fn set_len(&mut self, length: usize) {
        self.vec.set_len(length);
    }

    /// Extracts a string slice containing the entire `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s = StackStr::<5>::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        self
    }

    /// Converts a `StackStr` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<10>::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Returns a raw pointer to the `StackStr`'s buffer.
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const u8 {
        self.vec.as_ptr() as _
    }

    /// Returns a raw mutable pointer to the `StackStr`'s buffer.
    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.vec.as_mut_ptr() as _
    }

    /// Returns a byte slice of this `StackStr`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: StackStr::from_utf8
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s = StackStr::<5>::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Returns a mutable reference to the contents of this `StackStr`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `StackStr`, as the rest of
    /// the standard library assumes that `StackStr`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<5>::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut StackVec<u8, N> {
        &mut self.vec
    }

    /// Appends a given string slice onto the end of this `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<10>::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    pub fn push_str(&mut self, string: &str) {
        self.vec.copy_from_slice(string.as_bytes())
    }

    /// Appends the given [`char`] to the end of this `StackStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<6>::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.vec.push(ch as u8),
            _ => self
                .vec
                .copy_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `StackStr` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<3>::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let new_len = self.len() - ch.len_utf8();
        unsafe {
            self.vec.set_len(new_len);
        }
        Some(ch)
    }

    /// Shortens this `StackStr` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<5>::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            unsafe { self.set_len(new_len) }
        }
    }

    /// Truncates this `StackStr`, removing all contents.
    ///
    /// While this means the `StackStr` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<3>::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        unsafe {
            self.set_len(0);
        }
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place, visiting each character exactly once in the
    /// original order, and preserves the order of the retained characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<10>::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, "foobar");
    /// ```
    ///
    /// The exact order may be useful for tracking external state, like an index.
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<5>::from("abcde");
    /// let keep = [false, true, true, false, true];
    /// let mut i = 0;
    /// s.retain(|_| (keep[i], i += 1).0);
    /// assert_eq!(s, "bce");
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        unsafe {
            self.vec.set_len(0);
        }

        while idx < len {
            let ch = unsafe { self.get_unchecked(idx..len).chars().next().unwrap() };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    ptr::copy(
                        self.vec.as_ptr().add(idx),
                        self.vec.as_mut_ptr().add(idx - del_bytes),
                        ch_len,
                    );
                }
            }

            // Point idx to the next char
            idx += ch_len;
        }

        unsafe {
            self.vec.set_len(len - del_bytes);
        }
    }

    /// Inserts a character into this `StackStr` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `StackStr`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<3>::new();
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        let mut bits = [0; 4];
        let bits = ch.encode_utf8(&mut bits).as_bytes();

        unsafe {
            self.insert_bytes(idx, bits);
        }
    }

    unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
        let len = self.len();
        let amt = bytes.len();
        assert!(self.vec.remaining_capacity() >= amt);

        ptr::copy(
            self.vec.as_ptr().add(idx),
            self.vec.as_mut_ptr().add(idx + amt),
            len - idx,
        );
        ptr::copy(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
        self.vec.set_len(len + amt);
    }

    /// Inserts a string slice into this `StackStr` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `StackStr`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<6>::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));

        unsafe {
            self.insert_bytes(idx, string.as_bytes());
        }
    }

    /// Removes a [`char`] from this `StackStr` at a byte position and returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `StackStr`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let mut s = StackStr::<3>::from("foo");
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a StackStr"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(next),
                self.vec.as_mut_ptr().add(idx),
                len - next,
            );
            self.vec.set_len(len - (next - idx));
        }
        ch
    }
}

impl<const N: usize> Clone for StackStr<N> {
    #[inline]
    fn clone(&self) -> Self {
        let mut vec = StackVec::new();
        vec.copy_from_slice(&self.vec);
        StackStr { vec }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.clear();
        self.vec.copy_from_slice(&source.vec);
    }
}

impl<const N: usize> Deref for StackStr<N> {
    type Target = str;

    #[inline(always)]
    fn deref(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.vec.as_slice()) }
    }
}

impl<const N: usize> DerefMut for StackStr<N> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut str {
        unsafe { std::str::from_utf8_unchecked_mut(self.vec.as_mut_slice()) }
    }
}

impl<const N: usize> AsRef<str> for StackStr<N> {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<const N: usize> AsMut<str> for StackStr<N> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> AsRef<[u8]> for StackStr<N> {
    #[inline(always)]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> Borrow<str> for StackStr<N> {
    #[inline(always)]
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> BorrowMut<str> for StackStr<N> {
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut str {
        self
    }
}

impl<const N: usize> Borrow<[u8]> for StackStr<N> {
    #[inline(always)]
    fn borrow(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> Default for StackStr<N> {
    /// Creates an empty `StackStr<N>`.
    #[inline(always)]
    fn default() -> StackStr<N> {
        StackStr::new()
    }
}

impl<const N: usize> fmt::Debug for StackStr<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<const N: usize> fmt::Display for StackStr<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<const N: usize> fmt::Write for StackStr<N> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }
}

impl<const N1: usize, const N2: usize> PartialEq<StackStr<N2>> for StackStr<N1> {
    #[inline]
    fn eq(&self, other: &StackStr<N2>) -> bool {
        **self == **other
    }
}

impl<const N: usize> PartialEq<str> for StackStr<N> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        &**self == other
    }
}

impl<const N: usize> PartialEq<StackStr<N>> for str {
    #[inline]
    fn eq(&self, other: &StackStr<N>) -> bool {
        self == &**other
    }
}

impl<const N: usize> PartialEq<&str> for StackStr<N> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        &**self == *other
    }
}

impl<const N: usize> PartialEq<StackStr<N>> for &str {
    #[inline]
    fn eq(&self, other: &StackStr<N>) -> bool {
        *self == &**other
    }
}

impl<const N: usize> Eq for StackStr<N> {}

impl<const N1: usize, const N2: usize> PartialOrd<StackStr<N2>> for StackStr<N1> {
    #[inline]
    fn partial_cmp(&self, other: &StackStr<N2>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<const N: usize> PartialOrd<str> for StackStr<N> {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        (**self).partial_cmp(other)
    }
}

impl<const N: usize> PartialOrd<StackStr<N>> for str {
    #[inline]
    fn partial_cmp(&self, other: &StackStr<N>) -> Option<Ordering> {
        self.partial_cmp(&**other)
    }
}

impl<const N: usize> PartialOrd<&str> for StackStr<N> {
    #[inline]
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        (**self).partial_cmp(*other)
    }
}

impl<const N: usize> PartialOrd<StackStr<N>> for &str {
    #[inline]
    fn partial_cmp(&self, other: &StackStr<N>) -> Option<Ordering> {
        (*self).partial_cmp(&**other)
    }
}

impl<const N: usize> Ord for StackStr<N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<const N: usize> Extend<char> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        iterator.for_each(move |c| self.push(c));
    }
}

impl<'a, const N: usize> Extend<&'a char> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

impl<'a, const N: usize> Extend<&'a str> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(s));
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> Extend<Box<str>> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = Box<str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> Extend<String> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = String>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<'a, const N: usize> Extend<Cow<'a, str>> for StackStr<N> {
    #[inline]
    fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_str(&s));
    }
}

impl<const N: usize> FromIterator<char> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

impl<'a, const N: usize> FromIterator<&'a char> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

impl<'a, const N: usize> FromIterator<&'a str> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> FromIterator<String> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = String>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> FromIterator<Box<str>> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = Box<str>>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<'a, const N: usize> FromIterator<Cow<'a, str>> for StackStr<N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = Cow<'a, str>>>(iter: I) -> Self {
        let mut buf = StackStr::new();
        buf.extend(iter);
        buf
    }
}

impl<const N: usize> From<&str> for StackStr<N> {
    #[inline]
    fn from(s: &str) -> Self {
        let mut buf = StackStr::new();
        buf.push_str(s);
        buf
    }
}

impl<const N: usize> From<&mut str> for StackStr<N> {
    #[inline]
    fn from(s: &mut str) -> Self {
        let mut buf = StackStr::new();
        buf.push_str(s);
        buf
    }
}

impl<const N1: usize, const N2: usize> From<&StackStr<N2>> for StackStr<N1> {
    #[inline]
    fn from(s: &StackStr<N2>) -> Self {
        let mut buf = StackStr::new();
        buf.push_str(&s);
        buf
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> From<Box<str>> for StackStr<N> {
    /// Converts the given boxed `str` slice to a `StrackStr`.
    /// It is notable that the `str` slice is owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackStr;
    ///
    /// let s1 = String::from("hello world");
    /// let s2 = s1.into_boxed_str();
    /// let s3 = StackStr::<16>::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    #[inline]
    fn from(s: Box<str>) -> Self {
        let mut buf = StackStr::new();
        buf.push_str(&s);
        buf
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "str"))))]
impl<const N: usize> From<Cow<'_, str>> for StackStr<N> {
    #[inline]
    fn from(s: Cow<'_, str>) -> Self {
        let mut buf = StackStr::new();
        buf.push_str(&s);
        buf
    }
}

impl<const N: usize> Hash for StackStr<N> {
    #[inline]
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `StackStr` on the left-hand side and re-uses its buffer.
/// This is done to avoid allocating a new `StackStr` and copying the entire contents on
/// every operation, which would lead to *O*(*n*^2) running time when building an *n*-byte string by
/// repeated concatenation.
///
/// The string on the right-hand side is only borrowed; its contents are copied into the returned
/// `StackStr`.
///
/// # Examples
///
/// Concatenating two `StackStr`s takes the first by value and borrows the second:
///
/// ```
/// use stack_buf::StackStr;
///
/// let a = StackStr::<16>::from("hello");
/// let b = StackStr::<6>::from(" world");
/// let c = a + &b;
/// // `a` is moved and can no longer be used here.
///
/// assert_eq!(c, "hello world");
/// ```
///
/// If you want to keep using the first `StackStr`, you can clone it and append to the clone instead:
///
/// ```
/// use stack_buf::StackStr;
///
/// let a = StackStr::<16>::from("hello");
/// let b = StackStr::<6>::from(" world");
/// let c = a.clone() + &b;
/// // `a` is still valid here.
///
/// assert_eq!(c, "hello world");
/// ```
impl<const N: usize> Add<&str> for StackStr<N> {
    type Output = StackStr<N>;

    #[inline]
    fn add(mut self, other: &str) -> Self {
        self.push_str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `StackStr`.
///
/// This has the same behavior as the [`push_str`][StackStr::push_str] method.
impl<const N: usize> AddAssign<&str> for StackStr<N> {
    #[inline]
    fn add_assign(&mut self, other: &str) {
        self.push_str(other);
    }
}

impl<const N: usize> FromStr for StackStr<N> {
    type Err = std::convert::Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(StackStr::from(s))
    }
}

impl<const N: usize> From<StackStr<N>> for StackVec<u8, N> {
    #[inline]
    fn from(s: StackStr<N>) -> Self {
        s.into_bytes()
    }
}

#[cfg(feature = "serde")]
mod impl_serde {
    use super::*;
    use serde::de::{Error, Unexpected, Visitor};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::marker::PhantomData;

    #[cfg_attr(docsrs, doc(cfg(all(feature = "str", feature = "serde"))))]
    impl<const N: usize> Serialize for StackStr<N> {
        #[inline]
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.serialize_str(self)
        }
    }

    #[cfg_attr(docsrs, doc(cfg(all(feature = "str", feature = "serde"))))]
    impl<'de, const N: usize> Deserialize<'de> for StackStr<N> {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct StackStrVisitor<const N: usize>(PhantomData<([u8; N])>);

            impl<'de, const N: usize> Visitor<'de> for StackStrVisitor<N> {
                type Value = StackStr<N>;

                #[inline]
                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    write!(formatter, "a string with no more than {} bytes", N)
                }

                #[inline]
                fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    Ok(StackStr::from(v))
                }

                #[inline]
                fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
                where
                    E: Error,
                {
                    let s = str::from_utf8(v)
                        .map_err(|_| E::invalid_value(Unexpected::Bytes(v), &self))?;
                    Ok(StackStr::from(s))
                }
            }

            deserializer.deserialize_str(StackStrVisitor::<N>(PhantomData))
        }
    }
}
