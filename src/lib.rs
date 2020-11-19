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

use core::sync::atomic::AtomicUsize;
use std::os::raw::c_void;

/// Implementation for `GlobalAlloc` to store allocating memory size.
struct SizeAllocator {
    size: AtomicUsize,
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
