use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
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
/// the stack if needed.
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

    /// Sets the `StackVec`’s length without dropping or moving out elements
    ///
    /// # Safety
    /// This method is `unsafe` because it changes the notion of the
    /// number of “valid” elements in the vector.
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
    /// If `len` is greater than the vector’s current length this has no
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
    /// assert_eq!(vec.as_slice(), ['d', 'd']);
    /// ```
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
    /// assert_eq!(vec.as_slice(), ['a', 'd', 'd']);
    /// ```
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
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
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
    /// assert_eq!(dst.as_slice(), [3, 4]);
    /// ```
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

impl<T, const N: usize> PartialEq for StackVec<T, N>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T, const N: usize> Eq for StackVec<T, N> where T: Eq {}

impl<T: PartialOrd, const N: usize> PartialOrd for StackVec<T, N> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Ord, const N: usize> Ord for StackVec<T, N> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

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
