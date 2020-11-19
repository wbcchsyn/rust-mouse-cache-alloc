// Copyright 2020 Shin Yoshida
//
// "LGPL-3.0-or-later OR Apache-2.0"
//
// This is part of mouse-cache-alloc
//
//  mouse-cache-alloc is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  mouse-cache-alloc is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with mouse-cache-alloc.  If not, see <http://www.gnu.org/licenses/>.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![deny(missing_docs)]

//! # mouse-cache-alloc

use core::alloc::{GlobalAlloc, Layout};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::os::raw::c_void;

/// Same to `std::alloc::alloc` except for this method is for cache memory.
pub unsafe fn alloc(layout: Layout) -> *mut u8 {
    SIZE_ALLOC.alloc(layout)
}

/// Same to `std::alloc::alloc_zeroed` except for this method is for cache memory.
pub unsafe fn alloc_zeroed(layout: Layout) -> *mut u8 {
    SIZE_ALLOC.alloc_zeroed(layout)
}

/// Same to `std::alloc::realloc` except for this method is for cache memory.
pub unsafe fn realloc(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    SIZE_ALLOC.realloc(ptr, layout, new_size)
}

/// Same to `std::alloc::dealloc` except for this method is for cache memory.
pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    SIZE_ALLOC.dealloc(ptr, layout);
}

/// Returns how many bytes memory is allocated for cache.
pub fn cache_size() -> usize {
    SIZE_ALLOC.allocating_size()
}

/// Increases caching memory size by `bytes` and returns the new size.
pub fn increase_cache_size(bytes: usize) -> usize {
    SIZE_ALLOC.increase_size(bytes)
}

/// Decreases caching memory size by `bytes` and returns the new size.
pub fn decrease_cache_size(bytes: usize) -> usize {
    SIZE_ALLOC.decrease_size(bytes)
}

/// Implementation for `GlobalAlloc` to allocate/deallocate memory for cache.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Alloc;

unsafe impl GlobalAlloc for Alloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        alloc(layout)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        alloc_zeroed(layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        realloc(ptr, layout, new_size)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        dealloc(ptr, layout);
    }
}

static SIZE_ALLOC: SizeAllocator = SizeAllocator::new();

/// Implementation for `GlobalAlloc` to store allocating memory size.
struct SizeAllocator {
    size: AtomicUsize,
}

impl SizeAllocator {
    /// Creates a new instance with no allocating memory.
    pub const fn new() -> Self {
        Self {
            size: AtomicUsize::new(0),
        }
    }

    /// Returns the total byte size of allocating memory.
    pub fn allocating_size(&self) -> usize {
        self.size.load(Ordering::Relaxed)
    }

    /// Increase the allocating memory size by `bytes` and returns the new byte size.
    pub fn increase_size(&self, bytes: usize) -> usize {
        self.size.fetch_add(bytes, Ordering::Acquire) + bytes
    }

    /// Decrease the allocating memory size by `bytes` and returns the new byte size.
    pub fn decrease_size(&self, bytes: usize) -> usize {
        self.size.fetch_sub(bytes, Ordering::Acquire) - bytes
    }
}

unsafe impl GlobalAlloc for SizeAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = std::alloc::alloc(layout);

        if !ptr.is_null() {
            let size = allocating_size(ptr);
            self.size.fetch_add(size, Ordering::Acquire);
        }

        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = std::alloc::alloc_zeroed(layout);

        if !ptr.is_null() {
            let size = allocating_size(ptr);
            self.size.fetch_add(size, Ordering::Acquire);
        }

        ptr
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let old_size = allocating_size(ptr);
        let ptr_ = std::alloc::realloc(ptr, layout, new_size);

        if (ptr_ != ptr) && !ptr_.is_null() {
            let new_size = allocating_size(ptr_);

            if old_size < new_size {
                self.size.fetch_add(new_size - old_size, Ordering::SeqCst);
            } else {
                self.size.fetch_sub(old_size - new_size, Ordering::SeqCst);
            }
        }

        ptr_
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        debug_assert!(!ptr.is_null());

        let size = allocating_size(ptr);
        self.size.fetch_sub(size, Ordering::Release);

        std::alloc::dealloc(ptr, layout);
    }
}

/// Returns size of memory allocated from heap.
///
/// Argument `ptr` must fulfill the followings
///
/// - It must be what `std::alloc::alloc` returned.
/// - It must not be null.
/// - It must not have been deallocated yet.
///
/// # Safety
///
/// The behavior is undefined if `ptr` doesn't satisfy the
/// requirements.
///
/// # Warnings
///
/// This function works under both Linux `dmalloc` and `jemalloc` ,
/// however, it is based on `malloc_usable_size`, which is not defined
/// in POSIX.
#[cfg(unix)]
pub unsafe fn allocating_size<T>(ptr: *const T) -> usize {
    debug_assert_eq!(false, ptr.is_null());

    malloc_usable_size(ptr as *const c_void)
}

extern "C" {
    /// Returns size of memory allocated from heap.
    ///
    /// Argument `ptr` must be what `std::alloc::alloc` returned, and
    /// must not be deallocated yet.
    /// If `ptr` is null pointer, always returns 0.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `ptr` doesn't satisfy the
    /// requirements.
    ///
    /// # Warnings
    ///
    /// Both Linux `dmalloc` and `jemalloc`  implemnets this function,
    /// however, it is not defined in POSIX.
    /// For example, `tcmalloc` names `tc_malloc_size` the same function.
    #[cfg(unix)]
    fn malloc_usable_size(ptr: *const c_void) -> usize;
}
