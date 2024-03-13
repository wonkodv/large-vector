use core::slice;
use std::ops;
use std::slice::SliceIndex;

///! Large vector, backed by mmap anonymous pages, with real `O(1)` pushing and indexing.
///!
///! # Example:
///!
///! ```
///! let mut v = LVec::<u32>::new();
///! v.push(1);
///! v.push(1);
///! for i in 2..10000 {
///!     v.push(v[i-1].wrappinging_add(v[i-2]));
///! }
///! ```
// TODO: Cool specialization to initialize for free since the OS zeroes memory
// TODO: Not all pages are 4096 bytes large, don't base tests on this
use libc::c_void;

/// A contiguous growable array for large amounts of data, written as `LVec<T>`, short for 'large vector'.
///
/// The API should match [`alloc::vec::Vec`], most of the documentation and some code was copied from Vec
///
/// # Examples
///
/// ```
/// # use large_vector::LVec;
/// let mut vec = LVec::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
/// ```
///
/// Use a `LVec<T>` as an efficient stack:
///
/// ```
/// # use large_vector::LVec;
/// let mut stack = LVec::new();
///
/// stack.push(1);
/// stack.push(2);
/// stack.push(3);
///
/// while let Some(top) = stack.pop() {
///     // Prints 3, 2, 1
///     println!("{top}");
/// }
/// ```
///
/// # Indexing
///
/// The `LVec` type allows access to values by index:
///
/// ```
/// # use large_vector::LVec;
/// let v = LVec::from([0, 2, 4, 6]);
/// assert_eq!(v[1], 2);
/// ```
///
/// However be careful: if you try to access an index which isn't in the `LVec`,
/// your software will panic! You cannot do this:
///
/// ```should_panic
/// # use large_vector::LVec;
/// let v = LVec::from([0, 2, 4, 6]);
/// println!("{}", v[4]); // it will panic!
/// ```
///
/// Use [`get`] and [`get_mut`] if you want to check whether the index is in
/// the `LVec`.
///
/// # Slicing
///
/// A `LVec` can be mutable. On the other hand, slices are read-only objects.
/// To get a [slice][prim@slice], use [`&`]. Example:
///
/// ```
/// # use large_vector::LVec;
/// fn read_slice(slice: &[usize]) {
///     // ...
/// }
///
/// let v = LVec::from([0, 1]);
/// read_slice(&v);
///
/// // ... and that's all!
/// // you can also do it like this:
/// let u: &[usize] = &v;
/// // or like this:
/// let u: &[_] = &v;
/// ```
///
/// # Memory
///
/// the pointer ([`LVec::as_ptr`] and [`LVec::as_mut_ptr`]) always points at one or more memory
/// pages, allocated with an anonymous mmap.
/// The pages are not shared, so even if you store only 1 byte, the Vector allocates a full page
/// which is 4KiB large on many OSs.
///
/// When the vector grows, additional pages are requested form the OS (with `mremap`).
/// If the OS chooses to do so, the virtual address of the mapping stays the same, or it changes.
/// In both cases, the physical address remains the same, so no data are copied.
///
/// In that allocation, only the first [`len`] elemensts at `pointer` are initialized.
///
/// [`push`] and [`insert`] will never (re)allocate if the reported capacity is
/// sufficient. [`push`] and [`insert`] *will* (re)allocate if
/// <code>[len] == [capacity]</code>. That is, the reported capacity is completely
/// accurate, and can be relied on.
///
/// Whenever capacity changes, exactly enough pages to contain `capacity` elements are
/// requested from the OS.
///
///
/// See also:
/// -   [`mmap](https://man.archlinux.org/man/core/man-pages/mmap.2)
/// -   [`mremap`](https://man.archlinux.org/man/core/man-pages/mremap.2)
/// -   [`munmap`](https://man.archlinux.org/man/core/man-pages/munmap.2)
///
pub struct LVec<T> {
    buffer: *mut T,
    size_in_bytes: usize,
    len: usize,
}

/// API
impl<T> LVec<T> {
    /// Construct a new empty `LVec<T>`.
    ///
    /// The vector immediately allocates space for at least 1 `T` and at least 1 page (usually
    /// 4KiB)
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec: LVec<i32> = LVec::new();
    /// assert_eq!(vec.capacity(), 1024); // fails if your pages aren't 4kb
    /// ```
    pub fn new() -> Self {
        Self::with_capacity(1)
    }

    /// Constructs a new, empty `LVec<T>` with at least the specified capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is 0, the vector will allocate for 1 `T~.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    /// Panics if `T` has higher alignment than a single page.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec = LVec::<u32>::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    /// ```
    ///
    pub fn with_capacity(capacity: usize) -> Self {
        if std::mem::align_of::<T>() > page_size() {
            panic!(
                "T can not have higher alignment ({})  than a single page ({})",
                std::mem::align_of::<T>(),
                page_size()
            );
        }

        let len = 0;
        let size_in_bytes = Self::size_for_len(capacity);

        const PROT: libc::c_int = libc::PROT_READ | libc::PROT_WRITE;
        const FLAGS: libc::c_int = libc::MAP_PRIVATE | libc::MAP_ANON; // TODO: libc::MAP_UNINITIALIZED or implement something cool that uses the zeros
        const FD: libc::c_int = -1;
        const OFFSET: libc::off_t = 0;
        const ADDR: *mut c_void = 0 as *mut c_void;

        //  SAFETY:
        //  -   Calling `mmap` with addr `0` has no bad effects on existing memory.
        //  -   The call either returns `MAP_FAILED` or the address of `size_in_bytes` usable bytes
        //  -   The allocated area is initialized before increasing `len`
        let buffer: *mut c_void =
            unsafe { libc::mmap(ADDR, size_in_bytes, PROT, FLAGS, FD, OFFSET) };

        if buffer == libc::MAP_FAILED {
            let error = errno();
            panic!("mmap({ADDR:?}, {size_in_bytes}, {PROT}, {FLAGS}, {FD}, {OFFSET}) failed: {error:?}");
        }

        let buffer = buffer as *mut T;

        Self {
            buffer,
            size_in_bytes,
            len,
        }
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec: LVec<i32> = LVec::with_capacity(10);
    /// vec.push(42);
    /// assert!(vec.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.size_in_bytes / std::mem::size_of::<T>()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `LVec<T>`. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec = LVec::from([1]);
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let new_size = Self::size_for_len(self.len + additional);
        if new_size > self.size_in_bytes {
            // SAFETY: growing is safe
            unsafe { self.remap_to_size(new_size) };
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// Due to page size, capacity may still be much larger than len
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec:LVec<u8> = LVec::with_capacity(5000);
    /// vec.extend([1, 2, 3]);
    /// assert_eq!(vec.capacity(), 8192);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 4096);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let new_size = Self::size_for_len(self.len);
        if new_size < self.size_in_bytes {
            // SAFETY: shrinking is safe if new size fits at least len elements
            unsafe { self.remap_to_size(new_size) };
        }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// use std::io::{self, Write};
    /// let buffer = LVec::from([1, 2, 3, 5, 8]);
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: all elements were initialized before incrementing len
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// use std::io::{self, Read};
    /// let mut buffer = LVec::from([0; 3]);
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: all elements were initialized before incrementing len
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }

    /// Returns a raw pointer to the vector's buffer.
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let x = LVec::from([1, 2, 4]);
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// TODO: vec talks about aliasing guarantees
    pub fn as_ptr(&self) -> *const T {
        self.buffer
    }

    /// Returns a mutable pointer to the vector's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// // Allocate vector big enough for 1000 elements.
    /// let size = 1000;
    /// let mut x: LVec<i32> = LVec::with_capacity(size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as i32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&x[997..=999], &[997,998,999]);
    /// ```
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buffer
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This can be used with `as_mut_ptr` or the fact, that the OS will usually zero the
    /// page before mapping for security reasons
    ///
    /// # Example
    /// ```
    /// # use large_vector::LVec;
    /// let mut v:LVec<i32> = LVec::with_capacity(1000);
    /// unsafe{v.set_len(1000)};
    /// assert_eq!(v[999], 0);
    /// ```
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.len = new_len;
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec = LVec::from([1, 2]);
    /// vec.push(3);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    pub fn push(&mut self, value: T) {
        self.reserve(1);
        // SAFETY: `len` is never greater than capacity, so add always returns a pointer into
        // the same allocation
        let pointer = unsafe { self.as_mut_ptr().add(self.len) };
        // SAFETY: pointer is previously unused, aligned and allocated, so writing (moving) value
        // is safe
        unsafe { std::ptr::write(pointer, value) };
        self.len += 1;
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// If you'd like to pop the first element, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec = LVec::from([1, 2, 3]);
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            // SAFETY: `len` is never greater than capacity, so add always returns a pointer into
            // the same allocation
            let pointer = unsafe { self.as_ptr().add(self.len()) };
            // SAFETY: all elemens below `len` were initialized before incrementing len
            let value = unsafe { std::ptr::read(pointer) };
            Some(value)
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut vec = LVec::from([1, 2, 3]);
    /// let mut vec2 = LVec::from([4, 5, 6]);
    /// vec.append(&mut vec2);
    /// assert_eq!(&vec.as_slice(), &[1, 2, 3, 4, 5, 6]);
    /// assert_eq!(&vec2.as_slice(), &[]);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        unsafe {
            self.append_elements(other.as_slice() as _);
            other.set_len(0);
        }
    }

    /// Appends elements to `self` from other buffer.
    ///
    /// # SAFETY
    /// The elements at `other` must not be used later
    unsafe fn append_elements(&mut self, other: *const [T]) {
        let count = unsafe { (*other).len() };
        self.reserve(count);
        let len = self.len();
        unsafe {
            std::ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(len), count)
        };
        self.len += count;
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let mut v = LVec::from([1, 2, 3]);
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        let elems: *mut [T] = self.as_mut_slice();

        // SAFETY:
        // - `elems` comes directly from `as_mut_slice` and is therefore valid.
        // - Setting `self.len` before calling `drop_in_place` means that,
        //   if an element's `Drop` impl panics, the vector's `Drop` impl will
        //   do nothing (leaking the rest of the elements) instead of dropping
        //   some twice.
        unsafe {
            self.len = 0;
            std::ptr::drop_in_place(elems);
        }
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use large_vector::LVec;
    /// let a = LVec::from([1, 2, 3]);
    /// assert_eq!(a.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T: Clone> From<&[T]> for LVec<T> {
    fn from(source: &[T]) -> LVec<T> {
        let mut copy = Self::with_capacity(source.len());
        for e in source {
            copy.push(e.clone());
        }
        // TODO: something better with slice::clone_from_slice that has better performance?
        copy
    }
}

impl<T: Clone, const N: usize> From<[T; N]> for LVec<T> {
    fn from(s: [T; N]) -> LVec<T> {
        Self::from(s.as_slice())
    }
}

/// Details
impl<T> LVec<T> {
    /// resize the mapping
    ///
    /// SAFETY:
    /// -   if this shrinks the mapping, all objects in the unmapped area must be dropped and len
    ///     adjusted before calling
    unsafe fn remap_to_size(&mut self, new_size_in_bytes: usize) {
        self.buffer = {
            let addr = self.buffer as *mut c_void;
            let old_capacity_in_bytes = self.size_in_bytes;
            //  SAFETY:
            //  -   Growing:    Newly mapped memory is initialized before `len` is incremented and
            //                  unaccessible before
            //  -   Shrinking:  Caller droped elemnents in shrunk area and adjusted len.
            let addr = unsafe {
                libc::mremap(
                    addr,
                    old_capacity_in_bytes,
                    new_size_in_bytes,
                    libc::MREMAP_MAYMOVE,
                )
            };
            if addr == libc::MAP_FAILED {
                panic!("mremap failed, errno = {:?}", errno());
            }
            addr
        } as *mut T;
        self.size_in_bytes = new_size_in_bytes;
    }

    // size for `len` elements, rounded up to the next full page.
    // even if len is 0 one page is allocated
    fn size_for_len(len: usize) -> usize {
        let size = round_up(len * std::mem::size_of::<T>(), page_size());
        if size > isize::MAX as usize {
            // (*const T)::add does not support offsets > isize::MAX
            panic!("don't reserve more than isize::MAX bytes");
        }
        size
    }
}

impl<T> Drop for LVec<T> {
    fn drop(&mut self) {
        self.clear();
        let addr = self.buffer as *mut c_void;
        let size = self.size_in_bytes;
        // SAFETY: the area has been cleared, it is safe to unmap
        let r: i32 = unsafe { libc::munmap(addr, size) };
        if r != 0 {
            let error = errno();
            panic!("munmap({addr:?}, {size}) failed: {error:?}");
        }
    }
}

#[cfg(unix)]
fn page_size() -> usize {
    // SAFETY: sysconf is safe to call
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

// Round up `from` to be divisible by `to`
fn round_up(from: usize, to: usize) -> usize {
    let r = if from % to == 0 {
        from
    } else {
        from + to - (from % to)
    };
    if r == 0 {
        to
    } else {
        r
    }
}

// Implement nice Traits

impl<T> ops::Deref for LVec<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }
}

impl<T> ops::DerefMut for LVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }
}

impl<T: Clone> Clone for LVec<T> {
    fn clone(&self) -> Self {
        Self::from(self.as_slice())
    }
}

impl<T, I: SliceIndex<[T]>> ops::Index<I> for LVec<T> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<T, I: SliceIndex<[T]>> ops::IndexMut<I> for LVec<T> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.as_mut_slice()[index]
    }
}

impl<T> Extend<T> for LVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        let (lower, _upper) = iter.size_hint();
        self.reserve(lower);
        for e in iter {
            self.push(e);
        }
    }
}

struct Error(i32);
impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            libc::EACCES => write!(f, "EACCES"),
            libc::EBADF => write!(f, "EBADF"),
            libc::EINVAL => write!(f, "EINVAL"),
            libc::ENODEV => write!(f, "ENODEV"),
            libc::ENOMEM => write!(f, "ENOMEM"),
            code => write!(f, "Error {}", code),
        }
    }
}
fn errno() -> Error {
    Error(std::io::Error::last_os_error().raw_os_error().unwrap_or(-1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_round_up() {
        assert_eq!(round_up(5, 10), 10);
        assert_eq!(round_up(0, 10), 10);
        assert_eq!(round_up(9, 10), 10);
        assert_eq!(round_up(10, 10), 10);
        assert_eq!(round_up(11, 10), 20);
    }

    #[test]
    fn test_page_size() {
        assert_eq!(page_size(), 4096); // TODO: what about non 4kb pages?
    }

    struct Large {
        #[allow(dead_code)]
        data: [u8; 997],
    }

    impl Large {
        fn new() -> Self {
            Self { data: [0u8; 997] }
        }
    }

    #[test]
    fn test_basic_empty() {
        let v = LVec::<Large>::new();
        assert_eq!(v.capacity(), 4, "four large should fit 1 page"); // TODO: what about non 4kb pages?
        assert!(v.is_empty());
        std::mem::drop(v);
    }

    #[test]
    fn test_push_in_capa() {
        let mut v = LVec::<Large>::new();
        assert_eq!(v.capacity(), 4, "four large should fit 1 page"); // TODO: what about non 4kb pages?
        v.push(Large::new());
        assert_eq!(v.len(), 1, "after adding 1, size is 1");
        assert_eq!(v.capacity(), 4, "1 fits without resize");
    }

    #[test]
    fn test_push_grow() {
        let mut v = LVec::<Large>::new();
        assert_eq!(v.capacity(), 4); // TODO: what about non 4kb pages?
        v.push(Large::new());
        v.push(Large::new());
        v.push(Large::new());
        v.push(Large::new());
        assert_eq!(v.len(), 4);
        assert_eq!(v.capacity(), 4);
        v.push(Large::new());
        assert_eq!(v.len(), 5);
        assert_eq!(v.capacity(), 8);
    }

    #[test]
    fn test_use() {
        let mut v = LVec::<Large>::new();
        v.push(Large::new());
        v.as_mut_slice()[0].data[0] = 42;

        assert_eq!(
            unsafe { std::ptr::read_volatile(v.as_ptr() as *const u8) },
            42
        );
    }

    /// Grow LVec exponentially until its address changes
    /// see that values are the same
    #[test]
    fn test_ptr_changes_on_large_grow() {
        let mut v = LVec::<u8>::new();
        v.extend("Test String".bytes());
        let p = v.buffer;
        for i in 0..64 {
            v.reserve(1 << i);
            if p != v.buffer {
                break;
            }
        }
        assert!(p != v.buffer);
        assert_eq!(std::str::from_utf8(v.as_slice()).unwrap(), "Test String");
    }

    /// Test that Acceptable alignment passes, and, in the doctest, that too large alignment
    /// panics.
    ///
    /// ```
    /// #[repr(align(8192))]
    /// struct OverAligned(u8);
    /// let _ = LVec::<OverAligned>::new();
    /// ```
    #[test]
    pub fn test_alignment_check() {
        #[repr(align(4096))]
        struct Aligned(u8);
        let _ = LVec::<Aligned>::new();
    }
}

/// Tests that should panic, as doctests, on a doc-hidden type.
///
/// ```should_panic
/// # use large_vector::LVec;
/// #[repr(align(8192))]
/// struct OverAligned(u8);
/// let _ = LVec::<OverAligned>::new();
/// ```
#[doc(hidden)]
pub struct ShouldPanicDocTestHolder;
