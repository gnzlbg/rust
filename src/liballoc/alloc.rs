// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
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

use core::intrinsics::{min_align_of_val, size_of_val};
use core::ptr::{Unique};
use core::usize;

#[doc(inline)]
pub use core::alloc::*;

extern "Rust" {
    #[allocator]
    #[rustc_allocator_nounwind]
    fn __rust_alloc(size: usize, align: usize) -> *mut u8;
    #[rustc_allocator_nounwind]
    fn __rust_dealloc(ptr: *mut u8, size: usize, align: usize);
    #[rustc_allocator_nounwind]
    fn __rust_realloc(ptr: *mut u8,
                      old_size: usize,
                      align: usize,
                      new_size: usize) -> *mut u8;
    #[rustc_allocator_nounwind]
    fn __rust_alloc_zeroed(size: usize, align: usize) -> *mut u8;
}

#[derive(Copy, Clone, Default, Debug)]
pub struct Global;

#[unstable(feature = "allocator_api", issue = "32838")]
#[rustc_deprecated(since = "1.27.0", reason = "type renamed to `Global`")]
pub type Heap = Global;

#[unstable(feature = "allocator_api", issue = "32838")]
#[rustc_deprecated(since = "1.27.0", reason = "type renamed to `Global`")]
#[allow(non_upper_case_globals)]
pub const Heap: Global = Global;

unsafe impl GlobalAlloc for Global {
    #[inline]
    fn alloc(&self, layout: Layout) -> Result<Allocation, AllocErr> {
        unsafe {
            let ptr = __rust_alloc(layout.size(), layout.align());
            Allocation::from_ptr(ptr as *mut Opaque, layout)
        }
    }

    #[inline]
    unsafe fn dealloc(&self, allocation: Allocation) {
        __rust_dealloc(
            allocation.ptr() as *mut u8,
            allocation.layout().size(), allocation.layout().align()
        )
    }

    #[inline]
    unsafe fn realloc(&self, allocation: Allocation, new_layout: Layout)
                      -> Result<Allocation, ReallocErr> {
        if (allocation.ptr() as *mut u8).align_offset(new_layout.align()) != 0 {
            return Err(ReallocErr::new(AllocErr::new(new_layout), allocation));
        }
        let ptr = __rust_realloc(
            allocation.ptr() as *mut u8,
            allocation.layout().size(),
            allocation.layout().align(),
            new_layout.size()
        );
        Allocation::from_ptr(ptr as *mut Opaque, new_layout)
            .map_err(|e| ReallocErr::new(e, allocation))
    }

    #[inline]
    fn alloc_zeroed(&self, layout: Layout) -> Result<Allocation, AllocErr> {
        let ptr = __rust_alloc_zeroed(
            layout.size(), layout.align()
        );
        Allocation::from_ptr(ptr as *mut Opaque, layout)
    }
}

unsafe impl Alloc for Global {
    #[inline]
    fn alloc(&mut self, layout: Layout) -> Result<Allocation, AllocErr> {
        GlobalAlloc::alloc(self, layout)
    }

    #[inline]
    unsafe fn dealloc(&mut self, allocation: Allocation) {
        GlobalAlloc::dealloc(self, allocation)
    }

    #[inline]
    unsafe fn realloc(&mut self,
                      allocation: Allocation,
                      new_layout: Layout) -> Result<Allocation, ReallocErr>
    {
        GlobalAlloc::realloc(self, allocation, new_layout)
    }

    #[inline]
    fn alloc_zeroed(&mut self, layout: Layout) -> Result<Allocation, AllocErr> {
        GlobalAlloc::alloc_zeroed(self, layout)
    }
}

/// The allocator for unique pointers.
// This function must not unwind. If it does, MIR codegen will fail.
#[cfg(not(test))]
#[lang = "exchange_malloc"]
#[inline]
unsafe fn exchange_malloc(size: usize, align: usize) -> *mut u8 {
    if let Ok(layout) = Layout::from_size_align(size, align) {
        if let Ok(alloc) = Global.alloc(layout) {
            return alloc.ptr() as *mut u8;
        }
        oom()
    } else {
        align as *mut u8
    }
}

#[cfg_attr(not(test), lang = "box_free")]
#[inline]
pub(crate) unsafe fn box_free<T: ?Sized>(ptr: Unique<T>) {
    let ptr = ptr.as_ptr();
    let size = size_of_val(&*ptr);
    let align = min_align_of_val(&*ptr);
    if let Ok(layout) = Layout::from_size_align(size, align) {
        let alloc = Allocation::from_ptr(ptr as *mut Opaque, layout);
        if let Ok(alloc) = alloc  {
            Global.dealloc(alloc);
        } else {
            debug_assert!(ptr.is_null(), "trying to deallocate null pointer with non-zero layout");
            debug_assert!(false, "trying to deallocate pointer with non-fitting layout");
        }
    }
    // We do not allocate for Box<T> when T is ZST, so deallocation is also not
    // necessary.
    debug_assert!(ptr as *const u8 == align as *const u8,
                  "incorrect pointer value for Unique<T> where T: ZST");
}

pub fn oom() -> ! {
    extern {
        #[lang = "oom"]
        fn oom_impl() -> !;
    }
    unsafe { oom_impl() }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use self::test::Bencher;
    use boxed::Box;
    use alloc::{Global, Alloc, Layout, oom};

    #[test]
    fn allocate_zeroed() {
        unsafe {
            let layout = Layout::from_size_align(1024, 1).unwrap();
            let ptr = Global.alloc_zeroed(layout.clone())
                .unwrap_or_else(|_| oom());

            let mut i = ptr.cast::<u8>().as_ptr();
            let end = i.offset(layout.size() as isize);
            while i < end {
                assert_eq!(*i, 0);
                i = i.offset(1);
            }
            Global.dealloc(ptr, layout);
        }
    }

    #[bench]
    fn alloc_owned_small(b: &mut Bencher) {
        b.iter(|| {
            let _: Box<_> = box 10;
        })
    }
}
