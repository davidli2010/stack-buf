use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{
    Bound, Deref, DerefMut, Index, IndexMut, Range, RangeBounds, RangeFrom, RangeFull,
    RangeInclusive, RangeTo, RangeToInclusive,
};
use std::ptr::NonNull;
use std::{fmt, ptr, slice};

type Size = u32;

macro_rules! assert_capacity {
    ($cap: expr) => {
        if std::mem::size_of::<usize>() > std::mem::size_of::<Size>() {
            // largest supported capacity is Size::MAX
            if $cap > Size::MAX as usize {
                [][$cap]
            }
        }
    };
}

/// Set the length of the vec when the `SetLenOnDrop` value goes out of scope.
///
/// Copied from https://github.com/rust-lang/rust/pull/36355
struct SetLenOnDrop<'a> {
    len: &'a mut Size,
    local_len: Size,
}

impl<'a> SetLenOnDrop<'a> {
    #[inline]
    fn new(len: &'a mut Size) -> Self {
        SetLenOnDrop {
            local_len: *len,
            len,
        }
    }

    #[inline(always)]
    fn increment_len(&mut self, increment: Size) {
        self.local_len += increment;
    }
}

impl<'a> Drop for SetLenOnDrop<'a> {
    #[inline]
    fn drop(&mut self) {
        *self.len = self.local_len;
    }
}

/// A draining iterator for `StackVec<T, N>`.
///
/// This `struct` is created by [`StackVec::drain()`].
pub struct Drain<'a, T: 'a, const N: usize> {
    /// Index of tail to preserve
    tail_start: usize,
    /// Length of tail
    tail_len: usize,
    /// Current remaining range to remove
    iter: slice::Iter<'a, T>,
    vec: NonNull<StackVec<T, N>>,
}

unsafe impl<'a, T: Sync, const N: usize> Sync for Drain<'a, T, N> {}
unsafe impl<'a, T: Send, const N: usize> Send for Drain<'a, T, N> {}

impl<'a, T: 'a, const N: usize> Iterator for Drain<'a, T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|elt| unsafe { ptr::read(elt as *const _) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T: 'a, const N: usize> DoubleEndedIterator for Drain<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|elt| unsafe { ptr::read(elt as *const _) })
    }
}

impl<'a, T: 'a, const N: usize> ExactSizeIterator for Drain<'a, T, N> {}

impl<'a, T: 'a, const N: usize> Drop for Drain<'a, T, N> {
    fn drop(&mut self) {
        // len is currently 0 so panicking while dropping will not cause a double drop.

        // exhaust self first
        while let Some(_) = self.next() {}

        if self.tail_len > 0 {
            unsafe {
                let source_vec = self.vec.as_mut();
                // memmove back untouched tail, update to new length
                let start = source_vec.len();
                let tail = self.tail_start;
                let src = source_vec.as_ptr().add(tail);
                let dst = source_vec.as_mut_ptr().add(start);
                ptr::copy(src, dst, self.tail_len);
                source_vec.set_len(start + self.tail_len);
            }
        }
    }
}

/// A `Vec`-like container that stores elements on the stack.
///
/// The `StackVec` is a vector backed by a fixed size array. It keeps track of
/// the number of initialized elements. The `StackVec<T, N>` is parameterized
/// by `T` for the element type and `N` for the maximum capacity.
///
/// `N` is of type `usize` but is range limited to `u32::MAX`; attempting to create larger
/// `StackVec` with larger capacity will panic.
///
/// The vector is a contiguous value (storing the elements inline) that you can store directly on
/// the stack.
///
/// It offers a simple API but also dereferences to a slice, so that the full slice API is
/// available.
pub struct StackVec<T, const N: usize> {
    vec: [MaybeUninit<T>; N],
    len: Size,
}

impl<T, const N: usize> StackVec<T, N> {
    const VALUE: MaybeUninit<T> = MaybeUninit::uninit();
    const VEC: [MaybeUninit<T>; N] = [Self::VALUE; N];

    /// Creates a new empty `StackVec`.
    ///
    /// The maximum capacity is given by the generic parameter `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::<_, 16>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(&vec[..], &[1, 2]);
    /// assert_eq!(vec.capacity(), 16);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        assert_capacity!(N);
        StackVec {
            vec: Self::VEC,
            len: 0,
        }
    }

    /// Returns the number of elements stored in the `StackVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3]);
    /// vec.pop();
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns `true` if the `StackVec` is empty, false otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1]);
    /// vec.pop();
    /// assert_eq!(vec.is_empty(), true);
    /// ```
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the `StackVec` is completely filled to its capacity, false otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::<_, 1>::new();
    /// assert!(!vec.is_full());
    /// vec.push(1);
    /// assert!(vec.is_full());
    /// ```
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Returns the capacity of the `StackVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let vec = StackVec::from([1, 2, 3]);
    /// assert_eq!(vec.capacity(), 3);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns the capacity left in the `StackVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3]);
    /// vec.pop();
    /// assert_eq!(vec.remaining_capacity(), 1);
    /// ```
    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Returns a raw pointer to the `StackVec`'s buffer.
    #[inline(always)]
    pub const fn as_ptr(&self) -> *const T {
        self.vec.as_ptr() as _
    }

    /// Returns a raw mutable pointer to the `StackVec`'s buffer.
    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.vec.as_mut_ptr() as _
    }

    /// Returns a slice containing all elements of the `StackVec`.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns a mutable slice containing all elements of the `StackVec`.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Sets the `StackVec`???s length without dropping or moving out elements
    ///
    /// # Safety
    /// This method is `unsafe` because it changes the notion of the
    /// number of ???valid??? elements in the vector.
    ///
    /// This method uses *debug assertions* to check that `length` is
    /// not greater than the capacity.
    #[inline]
    pub unsafe fn set_len(&mut self, length: usize) {
        debug_assert!(length <= self.capacity());
        self.len = length as Size;
    }

    /// Appends an `value` to the end of the `StackVec`.
    ///
    /// # Panics
    ///
    /// This function will panic if the `StackVec` is already full.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::<_, 2>::new();
    ///
    /// vec.push(1);
    /// vec.push(2);
    ///
    /// assert_eq!(&vec[..], &[1, 2]);
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) {
        self.vec[self.len()] = MaybeUninit::new(value);
        self.len += 1;
    }

    /// Removes the last element of the vector and return it, or None if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::<_, 2>::new();
    ///
    /// vec.push(1);
    ///
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        unsafe {
            self.len -= 1;
            Some(ptr::read(self.as_ptr().add(self.len())))
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector???s current length this has no
    /// effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3, 4, 5]);
    /// vec.truncate(3);
    /// assert_eq!(&vec[..], &[1, 2, 3]);
    /// vec.truncate(4);
    /// assert_eq!(&vec[..], &[1, 2, 3]);
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }

        unsafe {
            let remaining_len = self.len() - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.set_len(len);
            ptr::drop_in_place(s);
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3]);
    ///
    /// vec.clear();
    ///
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len` or the vector is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackVec, stack_vec};
    ///
    /// let mut vec = stack_vec![5#1, 2, 3];
    /// vec.insert(1, 4);
    /// assert_eq!(&vec[..], [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(&vec[..], [1, 4, 2, 3, 5]);
    /// ```
    #[inline]
    pub fn insert(&mut self, index: usize, element: T) {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        let len = self.len();
        if index > len {
            assert_failed(index, len);
        }
        assert!(len < self.capacity());
        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            ptr::copy(ptr, ptr.offset(1), len - index);
            ptr::write(ptr, element);
            self.set_len(len + 1);
        }
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3]);
    /// assert_eq!(vec.remove(1), 2);
    /// assert_eq!(&vec[..], [1, 3]);
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("removal index (is {}) should be < len (is {})", index, len);
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }
        unsafe {
            let ret;
            {
                let ptr = self.as_mut_ptr().add(index);
                ret = ptr::read(ptr);
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut v = StackVec::from(["foo", "bar", "baz", "qux"]);
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(&v[..], ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(&v[..], ["baz", "qux"]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!(
                "swap_remove index (is {}) should be < len (is {})",
                index, len
            );
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }
        unsafe {
            // We replace self[index] with the last element. Note that if the
            // bounds check above succeeds there must be a last element (which
            // can be self[index] itself).
            let last = ptr::read(self.as_ptr().add(len - 1));
            let hole = self.as_mut_ptr().add(index);
            self.set_len(len - 1);
            ptr::replace(hole, last)
        }
    }

    /// Create a draining iterator that removes the specified range in the vector
    /// and yields the removed items from start to end. The element range is
    /// removed even if the iterator is not consumed until the end.
    ///
    /// Note: It is unspecified how many elements are removed from the vector,
    /// if the `Drain` value is leaked.
    ///
    /// # Panics
    /// If the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut v1 = StackVec::from([1, 2, 3]);
    /// let v2: StackVec<_, 3> = v1.drain(0..2).collect();
    /// assert_eq!(&v1[..], &[3]);
    /// assert_eq!(&v2[..], &[1, 2]);
    /// ```
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<T, N>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // When the Drain is first created, it shortens the length of
        // the source vector to make sure no uninitialized or moved-from elements
        // are accessible at all if the Drain's destructor never gets to run.
        //
        // Drain will ptr::read out the values to remove.
        // When finished, remaining tail of the vec is copied back to cover
        // the hole, and the vector length is restored to the new length.
        //
        let len = self.len();
        let start = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i.saturating_add(1),
        };
        let end = match range.end_bound() {
            Bound::Excluded(&j) => j,
            Bound::Included(&j) => j.saturating_add(1),
            Bound::Unbounded => len,
        };

        // bounds check happens here (before length is changed!)
        let range_slice: *const _ = &self[start..end];

        // Calling `set_len` creates a fresh and thus unique mutable references, making all
        // older aliases we created invalid. So we cannot call that function.
        self.len = start as Size;

        unsafe {
            Drain {
                tail_start: end,
                tail_len: len - end,
                iter: (*range_slice).iter(),
                vec: NonNull::new_unchecked(self as *mut _),
            }
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns `false`.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut vec = StackVec::from([1, 2, 3, 4]);
    /// vec.retain(|x| *x & 1 != 0 );
    /// assert_eq!(&vec[..], &[1, 3]);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut del = 0;
        let len = self.len();
        for i in 0..len {
            if !f(&mut self[i]) {
                del += 1;
            } else if del > 0 {
                self.swap(i - del, i);
            }
        }
        self.truncate(len - del);
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the vector and
    /// must determine if the elements compare equal. The elements are passed in opposite order
    /// from their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::stack_vec;
    ///
    /// let mut vec = stack_vec!["foo", "bar", "Bar", "baz", "bar"];
    ///
    /// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(&vec[..], ["foo", "bar", "baz", "bar"]);
    /// ```
    pub fn dedup_by<F>(&mut self, mut same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        // See the implementation of Vec::dedup_by in the
        // standard library for an explanation of this algorithm.
        let len = self.len();
        if len <= 1 {
            return;
        }

        let ptr = self.as_mut_ptr();
        let mut w: usize = 1;

        unsafe {
            for r in 1..len {
                let p_r = ptr.add(r);
                let p_wm1 = ptr.add(w - 1);
                if !same_bucket(&mut *p_r, &mut *p_wm1) {
                    if r != w {
                        let p_w = p_wm1.add(1);
                        std::mem::swap(&mut *p_r, &mut *p_w);
                    }
                    w += 1;
                }
            }
        }

        self.truncate(w);
    }

    /// Removes all but the first of consecutive elements in the vector that resolve to the same
    /// key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::stack_vec;
    ///
    /// let mut vec = stack_vec![10, 20, 21, 30, 20];
    ///
    /// vec.dedup_by_key(|i| *i / 10);
    ///
    /// assert_eq!(&vec[..], [10, 20, 30, 20]);
    /// ```
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b))
    }
}

impl<T: Clone, const N: usize> StackVec<T, N> {
    /// Creates a `StackVec` with `n` copies of `elem`.
    ///
    /// # Panics
    ///
    /// This function will panic if the `n > N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let vec = StackVec::<char, 128>::from_elem('d', 2);
    /// assert_eq!(&vec[..], ['d', 'd']);
    /// ```
    #[inline]
    pub fn from_elem(elem: T, n: usize) -> Self {
        let mut vec = StackVec::<T, N>::new();
        vec.push_elem(elem, n);
        vec
    }

    /// Appends `n` copies of `elem` to the `StackVec`.
    ///
    /// # Panics
    ///
    /// This function will panic if the `self.remaining_capacity() < n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let mut  vec = StackVec::<char, 10>::new();
    /// vec.push('a');
    /// vec.push_elem('d', 2);
    /// assert_eq!(&vec[..], ['a', 'd', 'd']);
    /// ```
    #[inline]
    pub fn push_elem(&mut self, elem: T, n: usize) {
        assert!(self.remaining_capacity() >= n);
        unsafe {
            let ptr = self.as_mut_ptr();
            let mut local_len = SetLenOnDrop::new(&mut self.len);
            for _ in 0..n {
                ptr::write(ptr.offset(local_len.local_len as isize), elem.clone());
                local_len.increment_len(1);
            }
        }
    }

    /// Clones and appends all elements in a slice to the `StackVec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `StackVec`. The `other` vector is traversed in-order.
    ///
    /// # Panics
    ///
    /// This function will panic if `self.remaining_capacity() < other.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackVec, stack_vec};
    /// let mut vec = stack_vec![10#1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(&vec[..], [1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T]) {
        assert!(self.remaining_capacity() >= other.len());
        unsafe {
            let ptr = self.as_mut_ptr();
            let mut local_len = SetLenOnDrop::new(&mut self.len);
            for elem in other {
                ptr::write(ptr.offset(local_len.local_len as isize), elem.clone());
                local_len.increment_len(1);
            }
        }
    }

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// This method requires `T` to implement [`Clone`],
    /// in order to be able to clone the passed value.
    ///
    /// # Panics
    ///
    /// This function will be panic if `new_len > self.capacity()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use stack_buf::{StackVec, stack_vec};
    ///
    /// let mut vec = stack_vec![5#"hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(&vec[..], ["hello", "world", "world"]);
    ///
    /// let mut vec = stack_vec![1, 2, 3, 4];
    /// vec.resize(2, 0);
    /// assert_eq!(&vec[..], [1, 2]);
    /// ```
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T) {
        assert!(new_len <= self.capacity());
        let len = self.len();

        if new_len > len {
            self.push_elem(value, new_len - len);
        } else {
            self.truncate(new_len);
        }
    }
}

impl<T: Copy, const N: usize> StackVec<T, N> {
    /// Copies all elements from `src` into `self`, using a memcpy.
    ///
    /// The length of `src` must be less than or equals `self`'s remaining capacity.
    ///
    /// If `T` does not implement `Copy`, use [`StackVec::extend_from_slice()`].
    ///
    /// # Panics
    ///
    /// This function will panic if the length of `self.remaining_capacity() < src.len()`.
    ///
    /// # Examples
    ///
    /// Copying two elements from a slice into a `StackVec`:
    ///
    /// ```
    /// use stack_buf::StackVec;
    ///
    /// let src = [1, 2, 3, 4];
    /// let mut dst = StackVec::<_, 8>::new();
    ///
    /// dst.copy_from_slice(&src[2..]);
    ///
    /// assert_eq!(src, [1, 2, 3, 4]);
    /// assert_eq!(&dst[..], [3, 4]);
    /// ```
    #[inline]
    pub fn copy_from_slice(&mut self, src: &[T]) {
        assert!(self.remaining_capacity() >= src.len());

        unsafe {
            let dest = self.as_mut_ptr().add(self.len());
            ptr::copy_nonoverlapping(src.as_ptr(), dest, src.len());
            self.set_len(self.len() + src.len());
        }
    }
}

impl<T, const N: usize> Drop for StackVec<T, N> {
    #[inline]
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len())) }
    }
}

/// Creates a `StackVec` from an array.
///
/// # Examples
///
/// ```
/// use stack_buf::StackVec;
///
/// let mut vec = StackVec::from([1, 2, 3]);
/// assert_eq!(vec.len(), 3);
/// assert_eq!(vec.capacity(), 3);
/// ```
impl<T, const N: usize> From<[T; N]> for StackVec<T, N> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        let array = ManuallyDrop::new(array);
        let mut vec = StackVec::<T, N>::new();
        unsafe {
            (&*array as *const [T; N] as *const [MaybeUninit<T>; N])
                .copy_to_nonoverlapping(&mut vec.vec as *mut [MaybeUninit<T>; N], 1);
            vec.set_len(N);
        }
        vec
    }
}

impl<T, const N: usize> Clone for StackVec<T, N>
where
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.clear();
        self.extend_from_slice(source);
    }
}

impl<T, const N: usize> Deref for StackVec<T, N> {
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for StackVec<T, N> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> AsRef<[T]> for StackVec<T, N> {
    #[inline(always)]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> AsMut<[T]> for StackVec<T, N> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> Borrow<[T]> for StackVec<T, N> {
    #[inline(always)]
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> BorrowMut<[T]> for StackVec<T, N> {
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> Default for StackVec<T, N> {
    /// Creates an empty `StackVec<T, N>`.
    #[inline(always)]
    fn default() -> StackVec<T, N> {
        StackVec::new()
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for StackVec<T, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T, const N: usize> Hash for StackVec<T, N>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<T, const N1: usize, const N2: usize> PartialEq<StackVec<T, N2>> for StackVec<T, N1>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &StackVec<T, N2>) -> bool {
        **self == **other
    }
}

impl<T, const N: usize> PartialEq<[T]> for StackVec<T, N>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        **self == *other
    }
}

impl<T, const N: usize> Eq for StackVec<T, N> where T: Eq {}

impl<T: PartialOrd, const N1: usize, const N2: usize> PartialOrd<StackVec<T, N2>>
    for StackVec<T, N1>
{
    #[inline]
    fn partial_cmp(&self, other: &StackVec<T, N2>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Ord, const N: usize> Ord for StackVec<T, N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<const N: usize> std::io::Write for StackVec<u8, N> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.copy_from_slice(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl<const N: usize> fmt::Write for StackVec<u8, N> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.copy_from_slice(s.as_bytes());
        Ok(())
    }
}

impl<T, const N: usize> Index<usize> for StackVec<T, N> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<T, const N: usize> IndexMut<usize> for StackVec<T, N> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.as_mut_slice()[index]
    }
}

impl<T, const N: usize> Index<RangeFull> for StackVec<T, N> {
    type Output = [T];

    #[inline]
    fn index(&self, _index: RangeFull) -> &Self::Output {
        self.as_slice()
    }
}

impl<T, const N: usize> IndexMut<RangeFull> for StackVec<T, N> {
    #[inline]
    fn index_mut(&mut self, _index: RangeFull) -> &mut Self::Output {
        self.as_mut_slice()
    }
}

macro_rules! impl_range_index {
    ($idx_ty: ty) => {
        impl<T, const N: usize> Index<$idx_ty> for StackVec<T, N> {
            type Output = [T];

            #[inline]
            fn index(&self, index: $idx_ty) -> &Self::Output {
                &self.as_slice()[index]
            }
        }

        impl<T, const N: usize> IndexMut<$idx_ty> for StackVec<T, N> {
            #[inline]
            fn index_mut(&mut self, index: $idx_ty) -> &mut Self::Output {
                &mut self.as_mut_slice()[index]
            }
        }
    };
    ($($idx_ty: ty),+ $(,)?) => {
        $(impl_range_index!($idx_ty);)+
    }
}

impl_range_index!(
    Range<usize>,
    RangeFrom<usize>,
    RangeInclusive<usize>,
    RangeTo<usize>,
    RangeToInclusive<usize>,
);

impl<T, const N: usize> Extend<T> for StackVec<T, N> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for elem in iter.into_iter() {
            self.push(elem);
        }
    }
}

impl<T, const N: usize> FromIterator<T> for StackVec<T, N> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vec = StackVec::new();
        vec.extend(iter);
        vec
    }
}

/// Iterate the `StackVec` with references to each element.
///
/// ```
/// use stack_buf::StackVec;
///
/// let vec = StackVec::from([1, 2, 3]);
///
/// for ele in &vec {
///     // ...
/// }
/// ```
impl<'a, T, const N: usize> IntoIterator for &'a StackVec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterate the `StackVec` with mutable references to each element.
///
/// ```
/// use stack_buf::StackVec;
///
/// let mut vec = StackVec::from([1, 2, 3]);
///
/// for ele in &mut vec {
///     // ...
/// }
/// ```
impl<'a, T, const N: usize> IntoIterator for &'a mut StackVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Iterate the `StackVec` with each element by value.
///
/// The vector is consumed by this operation.
///
/// ```
/// use stack_buf::StackVec;
///
/// for ele in StackVec::from([1, 2, 3]) {
///     // ...
/// }
/// ```
impl<T, const N: usize> IntoIterator for StackVec<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            vec: self,
            index: 0,
        }
    }
}

/// An iterator that consumes a `StackVec` and yields its items by value.
///
/// Returned from [`StackVec::into_iter()`].
pub struct IntoIter<T, const N: usize> {
    vec: StackVec<T, N>,
    index: usize,
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.vec.len() {
            None
        } else {
            unsafe {
                let index = self.index;
                self.index = index + 1;
                Some(ptr::read(self.vec.as_mut_ptr().add(index)))
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.vec.len() - self.index;
        (len, Some(len))
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index == self.vec.len() {
            None
        } else {
            unsafe {
                let new_len = self.vec.len() - 1;
                self.vec.set_len(new_len);
                Some(ptr::read(self.vec.as_mut_ptr().add(new_len)))
            }
        }
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    #[inline]
    fn drop(&mut self) {
        let index = self.index;
        let len = self.vec.len();
        unsafe {
            self.vec.set_len(0);
            let elements = slice::from_raw_parts_mut(self.vec.as_mut_ptr().add(index), len - index);
            ptr::drop_in_place(elements);
        }
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for IntoIter<T, N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(&self.vec[self.index..]).finish()
    }
}

#[cfg(feature = "serde")]
mod impl_serde {
    use super::*;
    use serde::de::{Error, SeqAccess, Visitor};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::marker::PhantomData;

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<T: Serialize, const N: usize> Serialize for StackVec<T, N> {
        #[inline]
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.collect_seq(self.as_slice())
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<'de, T: Deserialize<'de>, const N: usize> Deserialize<'de> for StackVec<T, N> {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct StackVecVisitor<'de, T: Deserialize<'de>, const N: usize>(
                PhantomData<(&'de (), [T; N])>,
            );

            impl<'de, T: Deserialize<'de>, const N: usize> Visitor<'de> for StackVecVisitor<'de, T, N> {
                type Value = StackVec<T, N>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    write!(formatter, "an array with no more than {} items", N)
                }

                #[inline]
                fn visit_seq<SA>(self, mut seq: SA) -> Result<Self::Value, SA::Error>
                where
                    SA: SeqAccess<'de>,
                {
                    let mut values = StackVec::<T, N>::new();

                    while let Some(value) = seq.next_element()? {
                        if values.is_full() {
                            return Err(SA::Error::invalid_length(N + 1, &self));
                        }

                        values.push(value);
                    }

                    Ok(values)
                }
            }

            deserializer.deserialize_seq(StackVecVisitor::<T, N>(PhantomData))
        }
    }
}

/// Creates a [`StackVec`] containing the arguments.
///
/// `stack_vec!` allows `StackVec`s to be defined with the same syntax as array expressions.
/// There are two forms of this macro:
///
/// - Creates a empty [`StackVec`]:
///
/// ```
/// use stack_buf::{StackVec, stack_vec};
///
/// let vec: StackVec<i32, 8> = stack_vec![];
/// assert!(vec.is_empty());
/// assert_eq!(vec.capacity(), 8);
///
/// let vec = stack_vec![i32; 16];
/// assert!(vec.is_empty());
/// assert_eq!(vec.capacity(), 16);
/// ```
///
/// - Creates a [`StackVec`] containing a given list of elements:
///
/// ```
/// use stack_buf::{StackVec, stack_vec};
///
/// let vec = stack_vec![128#1, 2, 3];
/// assert_eq!(vec.capacity(), 128);
/// assert_eq!(vec[0], 1);
/// assert_eq!(vec[1], 2);
/// assert_eq!(vec[2], 3);
///
/// let vec = stack_vec![1, 2, 3];
/// assert_eq!(vec.capacity(), 3);
///
/// ```
///
/// - Creates a [`StackVec`] from a given element and size:
///
/// ```
/// use stack_buf::{StackVec, stack_vec};
///
/// let v = stack_vec![0x8000#1; 3];
/// assert_eq!(v.as_slice(), [1, 1, 1]);
/// assert_eq!(v.capacity(), 0x8000);
///
/// let v = stack_vec![1; 3];
/// assert_eq!(v.capacity(), 3);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements
/// which implement [`Clone`] and the number of elements doesn't have to be
/// a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful
/// using this with types having a nonstandard `Clone` implementation. For
/// example, `stack_vec![Rc::new(1); 5]` will create a vector of five references
/// to the same boxed integer value, not five references pointing to independently
/// boxed integers.
#[macro_export]
macro_rules! stack_vec {
    () => ($crate::StackVec::new());
    ($ty: ty; $cap: literal) => ($crate::StackVec::<$ty, $cap>::new());
    ($elem:expr; $n:expr) => ({
        $crate::StackVec::<_, $n>::from_elem($elem, $n)
    });
    ($cap:literal# $elem:expr; $n:expr) => ({
        $crate::StackVec::<_, $cap>::from_elem($elem, $n)
    });
    ($($x:expr),+ $(,)?) => ({
        $crate::StackVec::from([$($x),+])
    });
    ($cap:literal# $($x:expr),+ $(,)?) => ({
        let mut vec = $crate::StackVec::<_, $cap>::new();
        $(vec.push($x);)+
        vec
    });
}
