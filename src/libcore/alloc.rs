// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![unstable(feature = "allocator_api",
            reason = "the precise API and guarantees it provides may be tweaked \
                      slightly, especially to possibly take into account the \
                      types being stored to make room for a future \
                      tracing garbage collector",
            issue = "32838")]

use cmp;
use fmt;
use mem;
use usize;
use ptr::{self, NonNull};
use num::NonZeroUsize;

extern {
    /// An opaque, unsized type. Used for pointers to allocated memory.
    ///
    /// This type can only be used behind a pointer like `*mut Opaque` or `ptr::NonNull<Opaque>`.
    /// Such pointers are similar to C’s `void*` type.
    pub type Opaque;
}

impl Opaque {
    /// Similar to `std::ptr::null`, which requires `T: Sized`.
    pub fn null() -> *const Self {
        0 as _
    }

    /// Similar to `std::ptr::null_mut`, which requires `T: Sized`.
    pub fn null_mut() -> *mut Self {
        0 as _
    }
}

fn size_align<T>() -> (usize, usize) {
    (mem::size_of::<T>(), mem::align_of::<T>())
}

/// Layout of a block of memory.
///
/// An instance of `Layout` describes a particular layout of memory.
/// You build a `Layout` up as an input to give to an allocator.
///
/// All layouts have an associated positive non-zero size and
/// a (non-zero) power-of-two alignment.
///
/// When these preconditions are not met functions manipulating
/// `Layout` return a `LayoutErr` instead.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    // size of the requested block of memory, measured in bytes.
    size: NonZeroUsize,

    // alignment of the requested block of memory, measured in bytes.
    align: NonZeroUsize,
}

impl Layout {

    /// Checks that the `size` and `alignment` satisfy `Layout`'s preconditions.
    #[inline]
    fn valid_size_align(size: usize, align: usize) -> bool {
        if size == 0 {
            return false;
        }

        if !align.is_power_of_two() {
            return false;
        }

        // (power-of-two implies align != 0.)

        // Rounded up size is:
        //   size_rounded_up = (size + align - 1) & !(align - 1);
        //
        // We know from above that align != 0. If adding (align - 1)
        // does not overflow, then rounding up will be fine.
        //
        // Conversely, &-masking with !(align - 1) will subtract off
        // only low-order-bits. Thus if overflow occurs with the sum,
        // the &-mask cannot subtract enough to undo that overflow.
        //
        // Above implies that checking for summation overflow is both
        // necessary and sufficient.
        if size > usize::MAX.wrapping_sub(align.wrapping_sub(1)) {
            return false;
        }

        true
    }

    /// Constructs a `Layout` from a given `size` and `align`,
    /// or returns `LayoutErr` if either of the following conditions
    /// are not met:
    ///
    /// * `size` must be greater than zero,
    ///
    /// * `align` must be a power of two,
    ///
    /// * `size`, when rounded up to the nearest multiple of `align`,
    ///    must not overflow (i.e. the rounded value must be less than
    ///    `usize::MAX`).
    #[inline]
    pub fn from_size_align(size: usize, align: usize) -> Result<Self, LayoutErr> {
        if !Self::valid_size_align(size, align) {
            return Err(LayoutErr { private: () });
        }
        unsafe {
            Ok(Layout::from_size_align_unchecked(size, align))
        }
    }

    /// Creates a layout, bypassing all checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe as it does not verify the
    /// `Layout::from_size_align` preconditions.
    ///
    /// **FIXME**: link to `from_size_align` here.
    #[inline]
    pub unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Self {
        debug_assert!(Self::valid_size_align(size, align));
        Layout { size: NonZeroUsize::new_unchecked(size), align: NonZeroUsize::new_unchecked(align) }
    }

    /// The minimum size in bytes for a memory block of this layout.
    #[inline]
    pub fn size(&self) -> usize { self.size.get() }

    /// The minimum byte alignment for a memory block of this layout.
    #[inline]
    pub fn align(&self) -> usize { self.align.get() }

    /// Constructs a `Layout` suitable for holding a value of type `T`.
    #[inline]
    pub fn new<T>() -> Result<Self, LayoutErr> {
        let (size, align) = size_align::<T>();
        Layout::from_size_align(size, align)
    }

    /// Produces layout describing a record that could be used to
    /// allocate backing structure for `T` (which could be a trait
    /// or other unsized type like a slice).
    #[inline]
    pub fn for_value<T: ?Sized>(t: &T) -> Result<Self, LayoutErr> {
        let (size, align) = (mem::size_of_val(t), mem::align_of_val(t));
        Layout::from_size_align(size, align)
    }

    /// Creates a layout describing the record that can hold a value
    /// of the same layout as `self`, but that also is aligned to
    /// alignment `align` (measured in bytes).
    ///
    /// If `self` already meets the prescribed alignment, then returns
    /// `self`.
    ///
    /// Note that this method does not add any padding to the overall
    /// size, regardless of whether the returned layout has a different
    /// alignment. In other words, if `K` has size 16, `K.align_to(32)`
    /// will *still* have size 16.
    #[inline]
    pub fn align_to(&self, align: usize) -> Result<Self, LayoutErr> {
        Layout::from_size_align(self.size(), cmp::max(self.align(), align))
    }

    /// Returns the amount of padding we must insert after `self`
    /// to ensure that the following address will satisfy `align`
    /// (measured in bytes).
    ///
    /// E.g. if `self.size()` is 9, then `self.padding_needed_for(4)`
    /// returns 3, because that is the minimum number of bytes of
    /// padding required to get a 4-aligned address (assuming that the
    /// corresponding memory block starts at a 4-aligned address).
    ///
    /// The return value of this function has no meaning if `align` is
    /// not a power-of-two.
    ///
    /// Note that the utility of the returned value requires `align`
    /// to be less than or equal to the alignment of the starting
    /// address for the whole allocated block of memory. One way to
    /// satisfy this constraint is to ensure `align <= self.align()`.
    #[inline]
    pub fn padding_needed_for(&self, align: usize) -> usize {
        let len = self.size();

        // Rounded up value is:
        //   len_rounded_up = (len + align - 1) & !(align - 1);
        // and then we return the padding difference: `len_rounded_up - len`.
        //
        // We use modular arithmetic throughout:
        //
        // 1. align is guaranteed to be > 0, so align - 1 is always
        //    valid.
        //
        // 2. `len + align - 1` can overflow by at most `align - 1`,
        //    so the &-mask wth `!(align - 1)` will ensure that in the
        //    case of overflow, `len_rounded_up` will itself be 0.
        //    Thus the returned padding, when added to `len`, yields 0,
        //    which trivially satisfies the alignment `align`.
        //
        // (Of course, attempts to allocate blocks of memory whose
        // size and padding overflow in the above manner should cause
        // the allocator to yield an error anyway.)

        let len_rounded_up = len.wrapping_add(align).wrapping_sub(1)
            & !align.wrapping_sub(1);
        return len_rounded_up.wrapping_sub(len);
    }

    /// Creates a layout describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each to
    /// ensure that each instance is given its requested size and
    /// alignment. On success, returns `(k, offs)` where `k` is the
    /// layout of the array and `offs` is the distance, in bytes, between
    /// the start of each element in the array.
    #[inline]
    pub fn repeat(&self, n: usize) -> Result<(Self, usize), LayoutErr> {
        let padded_size = self.size().checked_add(self.padding_needed_for(self.align()))
            .ok_or(LayoutErr { private: () })?;
        let alloc_size = padded_size.checked_mul(n)
            .ok_or(LayoutErr { private: () })?;
        Ok((Layout::from_size_align(alloc_size, self.align())?, padded_size))
    }

    /// Creates a layout describing the record for `self` followed by
    /// `next`, including any necessary padding to ensure that `next`
    /// will be properly aligned. Note that the result layout will
    /// satisfy the alignment properties of both `self` and `next`.
    ///
    /// Returns `Some((k, offset))`, where `k` is layout of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded within the concatenated record
    /// (assuming that the record itself starts at offset 0).
    pub fn extend(&self, next: Self) -> Result<(Self, usize), LayoutErr> {
        let new_align = cmp::max(self.align(), next.align());
        let realigned = Layout::from_size_align(self.size(), new_align)?;

        let pad = realigned.padding_needed_for(next.align());

        let offset = self.size().checked_add(pad)
            .ok_or(LayoutErr { private: () })?;
        let new_size = offset.checked_add(next.size())
            .ok_or(LayoutErr { private: () })?;

        let layout = Layout::from_size_align(new_size, new_align)?;
        Ok((layout, offset))
    }

    /// Creates a layout describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// Note that, unlike `repeat`, `repeat_packed` does not guarantee
    /// that the repeated instances of `self` will be properly
    /// aligned, even if a given instance of `self` is properly
    /// aligned. In other words, if the layout returned by
    /// `repeat_packed` is used to allocate an array, it is not
    /// guaranteed that all elements in the array will be properly
    /// aligned.
    pub fn repeat_packed(&self, n: usize) -> Result<Self, LayoutErr> {
        let size = self.size().checked_mul(n).ok_or(LayoutErr { private: () })?;
        Layout::from_size_align(size, self.align())
    }

    /// Creates a layout describing the record for `self` followed by
    /// `next` with no additional padding between the two. Since no
    /// padding is inserted, the alignment of `next` is irrelevant,
    /// and is not incorporated *at all* into the resulting layout.
    ///
    /// Returns `(k, offset)`, where `k` is layout of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded within the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// (The `offset` is always the same as `self.size()`; we use this
    ///  signature out of convenience in matching the signature of
    ///  `extend`.)
    pub fn extend_packed(&self, next: Self) -> Result<(Self, usize), LayoutErr> {
        let new_size = self.size().checked_add(next.size())
            .ok_or(LayoutErr { private: () })?;
        let layout = Layout::from_size_align(new_size, self.align())?;
        Ok((layout, self.size()))
    }

    /// Creates a layout describing the record for a `[T; n]`.
    #[inline]
    pub fn array<T>(n: usize) -> Result<Self, LayoutErr> {
        let l = Layout::new::<T>().map(|l| {
            l.repeat(n)
            .map(|(k, offs)| {
                debug_assert!(offs == mem::size_of::<T>());
                k
            })
        });
        match l {
            Ok(l) => match l {
                Ok(l) => Ok(l),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
}

// (we need this for downstream impl of Display for AllocErr)
impl fmt::Display for Layout {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "size: {}, align: {}", self.size(), self.align())
    }
}

/// The `Layout` constraints could not be satisfied:
///
/// * `size` must be greater than zero,
///
/// * `align` must be a power of two,
///
/// * `size`, when rounded up to the nearest multiple of `align`,
///    must not overflow (i.e. the rounded value must be less than
///    `usize::MAX`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutErr {
    private: ()
}

// (we need this for downstream impl of trait Error)
impl fmt::Display for LayoutErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid parameters to Layout::from_size_align")
    }
}

/// Represents a memory allocation with a non-null starting address and a
/// `Layout`.
#[derive(Debug)]
pub struct Allocation(NonNull<Opaque>, Layout);

impl Allocation {
    /// Instantiates a memory allocation from a pointer and a size.
    ///
    /// # Safety
    ///
    /// The pointer and layout must be provided by an allocator. Depending on
    /// the concrete allocator, it might accept reallocating or deallocating
    /// allocations build using a different `layout`.
    #[inline]
    pub unsafe fn from_ptr(ptr: *mut Opaque, layout: Layout) -> Result<Self, AllocErr> {
        if ptr.is_null() || (ptr as *mut u8).align_offset(layout.align()) != 0 {
            Err(AllocErr(layout))
        } else {
            Ok(Allocation(NonNull::new_unchecked(ptr), layout))
        }
    }

    #[inline]
    pub unsafe fn new(ptr: NonNull<Opaque>, layout: Layout) -> Result<Self, AllocErr> {
        if ptr.as_ptr().is_null() || (ptr.as_ptr() as *const u8).align_offset(layout.align()) != 0 {
            Err(AllocErr(layout))
        } else {
            Ok(Allocation(ptr, layout))
        }
    }

    #[inline]
    pub unsafe fn from_ptr_unchecked(ptr: *mut Opaque, layout: Layout) -> Self {
        debug_assert!(Allocation::from_ptr(ptr, layout).is_ok(), "invalid unchecked allocation");
        Allocation(NonNull::new_unchecked(ptr), layout)
    }

    #[inline]
    pub unsafe fn new_unchecked(ptr: NonNull<Opaque>, layout: Layout) -> Self {
        debug_assert!(Allocation::new(ptr, layout).is_ok(), "invalid unchecked allocation");
        Allocation(ptr, layout)
    }

    /// Returns the pointer to the starting address of the memory allocation.
    #[inline]
    pub fn ptr(&self) -> *mut Opaque {
        self.0.as_ptr()
    }

    /// Returns the pointer to the starting address of the memory allocation.
    #[inline]
    pub fn non_null(&self) -> NonNull<Opaque> {
        self.0
    }

    /// Returns the layout of the allocation.
    #[inline]
    pub fn layout(&self) -> Layout {
        self.1
    }
}


/// The `AllocErr` error specifies that an allocation failed.
///
/// This can happen either due to resource exhaustion or because the allocator
/// does not support the requested `Layout`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AllocErr(Layout);

impl AllocErr {
    /// Instantiates a new `AllocErr` from a `layout`.
    pub fn new(layout: Layout) -> Self {
        AllocErr(layout)
    }
    /// Layout that produced the allocation to fail.
    pub fn layout(&self) -> Layout {
        self.0
    }
}

// (we need this for downstream impl of trait Error)
impl fmt::Display for AllocErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "memory allocation failed with layout: {}", self.0)
    }
}

/// Reallocation error.
///
/// This can happen either due to resource exhaustion, because the allocator
/// does not support the provided `Layout`, if the `Allocation` was allocated
/// with a differen allocator, etc.
///
/// It contains the `AllocErr` containing the provided `Layout` and the
/// `Allocation` that failed to reallocate.
#[derive(Debug)]
pub struct ReallocErr(AllocErr, Allocation);

impl ReallocErr {
    pub fn new(alloc_err: AllocErr, allocation: Allocation) -> Self {
        ReallocErr(alloc_err, allocation)
    }
}

// (we need this for downstream impl of trait Error)
impl fmt::Display for ReallocErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "memory reallocation of layout \"{}\" to layout \"{}\" failed",
               self.0.layout(), self.1.layout())
    }
}

/// The `ReallocInPlaceErr` error is used when `realloc_in_place` was unable to
/// reuse the given memory block for a requested layout range.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReallocInPlaceErr((Layout, Layout));

impl ReallocInPlaceErr {
    pub fn new(range: (Layout, Layout)) -> Self {
        ReallocInPlaceErr(range)
    }
}


// (we need this for downstream impl of trait Error)
impl fmt::Display for ReallocInPlaceErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"cannot reallocate allocator's memory in place to fit in layout range [{}, {}]",
               (self.0).0, (self.0).1)
    }
}

/// Augments `AllocErr` with a CapacityOverflow variant.
#[derive(Clone, PartialEq, Eq, Debug)]
#[unstable(feature = "try_reserve", reason = "new API", issue="48043")]
pub enum CollectionAllocErr {
    /// Error due to the computed capacity exceeding the collection's maximum
    /// (usually `isize::MAX` bytes).
    CapacityOverflow,
    /// Error due to the allocator (see the `AllocErr` type's docs).
    AllocErr(AllocErr),
}

#[unstable(feature = "try_reserve", reason = "new API", issue="48043")]
impl From<AllocErr> for CollectionAllocErr {
    #[inline]
    fn from(x: AllocErr) -> Self {
        CollectionAllocErr::AllocErr(x)
    }
}

/// A memory allocator that can be registered to be the one backing
/// `std::alloc::Global` though the `#[global_allocator]` attributes.
///
/// # Definitions
///
/// * An allocation is "currently allocated by this allocator" if:
///
///   * The allocation pointer was obtained from a previous call to one of the
///   memory allocation methods returned by this allocator.
///
///   * An `Allocation` built using this pointer has not been previously
///   deallocated.
///
/// * An allocation's layout "fits the memory block of the allocation" if:
///
///   * The size and alignment of the allocation layout are in range of the
///   layout requested when performing the allocation, the layout returned
///   by the memory allocator, and the alignment is a power of two.
///
/// # Unsafety
///
/// Implementors of the `GlobalAlloc` trait must ensure that:
///
/// * Pointers of returned `Allocation`s point to valid memory and retain their
///   validity until they are passed to an allocation functions that invalidates
///   them (like deallocation or reallocation functions).
///
/// * None of the trait method implementations unwind the stack, that is, they
///   do not `panic!`.
///
/// # Error handling
///
/// All methods of the `GlobalAlloc` trait are infallible, that is, they are not
/// allowed to `abort` or `unwind` on error, but must return an `Err` instead.
///
/// Clients wishing to abort computation in response to an allocation
/// error are encouraged to call the allocator's `oom` method, rather than
/// directly invoking `panic!` or similar.
pub unsafe trait GlobalAlloc {
    /// Requests an uninitialized memory block able to fit `layout`.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    fn alloc(&self, layout: Layout) -> Result<Allocation, AllocErr>;

    /// Deallocates the `allocation`.
    ///
    /// That is, the allocation is not allocated by this memory allocator anymore.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `allocation` is currently allocated by
    /// this allocator and its layout fits its memory block.
    unsafe fn dealloc(&self, allocation: Allocation);

    /// Requests a zeroed memory block able to fit `layout`.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<Allocation, AllocErr> {
        let size = layout.size();
        self.alloc(layout).map(|a| {
            unsafe { ptr::write_bytes(a.ptr() as *mut u8, 0, size) };
            a
        })
    }

    /// Requests shrinking or growing a memory `allocation` to fit `new_layout`.
    ///
    /// On success, same effects as `dealloc(allocation)`: the `allocation` is
    /// not allocated by this memory allocator anymore.
    ///
    /// On error, the unaltered `allocation` is returned as part of `ReallocErr`
    /// and is still valid.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `allocation` is currently allocated by
    /// this allocator and its layout fits its memory block.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `new_layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    #[inline]
    unsafe fn realloc(&self, allocation: Allocation,
                      new_layout: Layout) -> Result<Allocation, ReallocErr> {
        match self.alloc(new_layout) {
            Ok(new_allocation) => {
                ptr::copy_nonoverlapping(
                    allocation.ptr() as *const u8,
                    new_allocation.ptr() as *mut u8,
                    cmp::min(allocation.layout().size(), new_allocation.layout().size()),
                );
                self.dealloc(allocation);
                Ok(new_allocation)
            },
            Err(alloc_err) => Err(ReallocErr(alloc_err, allocation)),
        } 
    }
}


/// Memory allocation API.
///
/// > Note that this list may get tweaked over time as clarifications are made in
/// > the future. Additionally global allocators may gain unique requirements for
/// > how to safely implement one in the future as well.
///
/// # Definitions
///
/// * An allocation is "currently allocated by this allocator" if:
///
///   * The allocation pointer was obtained from a previous call to one of the
///   memory allocation methods returned by this allocator.
///
///   * An `Allocation` built using this pointer has not been previously
///   deallocated.
///
/// * An allocation's layout "fits the memory block of the allocation" if:
///
///   * The size and alignment of the allocation layout are in range of the
///   layout requested when performing the allocation, the layout returned
///   by the memory allocator, and the alignment is a power of two.
///
/// # Unsafety
///
/// Implementors of the `GlobalAlloc` trait must ensure that:
///
/// * Pointers of returned `Allocation`s point to valid memory and retain their
///   validity until they are passed to an allocation functions that invalidates
///   them (like deallocation or reallocation functions).
///
/// * None of the trait method implementations unwind the stack, that is, they
///   do not `panic!`.
///
/// # Unsafety
///
/// The `Alloc` trait is an `unsafe` trait for a number of reasons, and
/// implementors must ensure that they adhere to these contracts:
///
/// * Pointers returned from allocation functions must point to valid memory and
///   retain their validity until at least the instance of `Alloc` is dropped
///   itself.
///
/// # Error handling
///
/// All methods of the `Alloc` trait are infallible, that is, they are not
/// allowed to `abort` or `unwind` on error, but must return an `Err` instead.
///
/// Clients wishing to abort computation in response to an allocation
/// error are encouraged to call the allocator's `oom` method, rather than
/// directly invoking `panic!` or similar.
pub unsafe trait Alloc {
    /// Requests an uninitialized memory block able to fit `layout`.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    fn alloc(&mut self, layout: Layout) -> Result<Allocation, AllocErr>;

    /// Deallocates the `allocation.
    ///
    /// That is, the allocation is not allocated by this memory allocator anymore.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `allocation` is currently allocated by
    /// this allocator and its layout fits its memory block.
    unsafe fn dealloc(&mut self, allocation: Allocation);

    /// Requests a zeroed memory block able to fit `layout`.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    fn alloc_zeroed(&mut self, layout: Layout) -> Result<Allocation, AllocErr> {
        let size = layout.size();
        self.alloc(layout).map(|a| {
            unsafe { ptr::write_bytes(a.ptr() as *mut u8, 0, size) };
            a
        })
    }

    /// Requests shrinking or growing a memory `allocation` to fit `new_layout`.
    ///
    /// On success, same effects as `dealloc(allocation)`: the `allocation` is
    /// not allocated by this memory allocator anymore.
    ///
    /// On error, the unaltered `allocation` is returned as part of `ReallocErr`
    /// and is still valid.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `allocation` is currently allocated by
    /// this allocator and its layout fits its memory block.
    ///
    /// # Errors
    ///
    /// This method might fail due to resource exhaustion or because the
    /// allocator does not support the requested `new_layout`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    unsafe fn realloc(&mut self,
               allocation: Allocation,
               new_layout: Layout) -> Result<Allocation, ReallocErr> {
        match self.alloc(new_layout) {
            Ok(new_allocation) => {
                ptr::copy_nonoverlapping(
                    allocation.ptr() as *const u8,
                    new_allocation.ptr() as *mut u8,
                    cmp::min(allocation.layout().size(), new_allocation.layout().size()),
                );
                self.dealloc(allocation);
                Ok(new_allocation)
            },
            Err(alloc_err) => Err(ReallocErr(alloc_err, allocation)),
        }
    }

    /// Requests reallocating a memory `allocation` to fit a layout in range
    /// `[range.0, range.1]` in place.
    ///
    /// On success the layout of `allocation` is in range `[range.0, range.1]`.
    ///
    /// If the new layout is smaller than the original layout, the contents of
    /// the memory block within the new allocation layout are unaltered, and the
    /// memory between the original and new allocation is effectively
    /// deallocated.
    ///
    /// If the new layout is larger than the original layout, the contents of
    /// the memory block within the original allocation are unaltered, and the
    /// memory between the original and new allocation is uninitialized.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `allocation` is currently allocated by
    /// this allocator and its layout fits its memory block.
    ///
    /// # Error
    ///
    /// If the allocation cannot be made to fit a layout in `range` it errors with
    /// `CannotReallocInPlace`.
    ///
    /// Implementations are required to return `Err` on error, it is illegal for
    /// an implementation `abort` or `unwind`.
    unsafe fn realloc_in_place(&mut self,
                               allocation: &mut Allocation,
                               range: (Layout, Layout)) -> Result<(), ReallocInPlaceErr> {
        if range.1.size() < range.0.size() {
            return Err(ReallocInPlaceErr(range));
        }

        let original = allocation.layout();

        if range.0.size() >= original.size() {
            // grow the allocation
            let (_, u) = self.usable_layout(&allocation);
            if u.size() >= range.0.size() {
                *allocation = Allocation::from_ptr_unchecked(allocation.ptr(), range.1);
                return Ok(());
            }
        } else {
            // shrink the allocation
            let (l, _) = self.usable_layout(&allocation);
            if l.size() >= range.0.size() && l.size() <= range.1.size() {
                *allocation = Allocation::from_ptr_unchecked(allocation.ptr(), l);
                return Ok(());
            }
        }

        Err(ReallocInPlaceErr(range))
    }

    /// Returns bounds on the layout of a successful
    /// `allocation` that are accepted by the allocation functions.
    ///
    /// This method can be used to determine if an allocation's layout fits the
    /// memory block of a succesfull allocation.
    ///
    /// In particular, if one has a memory block allocated via a given
    /// allocator `a` and layout `k` where `a.usable_layout(k)` returns
    /// `(l, u)`, then one can pass that block to `a.dealloc()` with a
    /// layout in the range `[l, u]`.
    ///
    /// Both the lower- and upper-bounds (`l` and `u` respectively)
    /// are provided, because an allocator based on size classes could
    /// misbehave if one attempts to deallocate a block without
    /// providing a correct value for its size (i.e., one within the
    /// range `[l, u]`).
    #[inline]
    fn usable_layout(&self, allocation: &Allocation) -> (Layout, Layout) {
        (allocation.layout(), allocation.layout())
    }
}
