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

use core::alloc::{GlobalAlloc, Layout};
use core::mem::size_of;
use core::sync::atomic::AtomicUsize;

/// Bucket of `Crc` to allocate/deallocate memory for reference count and valu at once.
///
/// Property `Bucket::size` is same to `Bucket<T>` when `T` is `Sized` .
/// The align of `Bucket` is same to that of `usize` .
#[repr(C)]
struct Bucket<T: ?Sized> {
    size: usize,
    count: AtomicUsize,
    val: T,
}

impl<T> From<T> for Bucket<T> {
    fn from(val: T) -> Self {
        Self {
            size: size_of::<Self>(),
            count: AtomicUsize::new(1),
            val,
        }
    }
}

/// `CrcInner` is for `Crc` .
///
/// It behaves like `std::sync::Arc` except for the followings.
///
/// - `CrcInner` supports only strong pointer, but not weak pointer.
/// - `CrcInner` takes allocator as template parameter to allocate/deallocate heap memory.
///
/// # Warnings
///
/// Heap is allocated when created first via the property `alloc` , and the memory will be shared
/// among cloned instance. It will be deallocated when the last cloned instance is dropped using
/// the `alloc` . i.e. The allocator is not always the very same to allocate and to deallocate the
/// pointer.
struct CrcInner<T: ?Sized, A>
where
    A: GlobalAlloc,
{
    ptr: *mut T,
    alloc: A,
}

impl<T: ?Sized, A> CrcInner<T, A>
where
    A: GlobalAlloc,
{
    /// Returns a reference to the reference counter.
    pub fn counter(&self) -> &AtomicUsize {
        unsafe {
            let ptr: *const AtomicUsize = self.ptr.cast();
            let ptr = ptr.sub(1);
            &*ptr
        }
    }

    /// Returns a layout to have allocated the heap.
    fn layout(&self) -> Layout {
        unsafe {
            let ptr: *const AtomicUsize = self.ptr.cast();
            let ptr = ptr.sub(1);

            let ptr: *const usize = ptr.cast();
            let ptr = ptr.sub(1);
            let size = *ptr;

            Layout::from_size_align_unchecked(size, core::mem::align_of::<usize>())
        }
    }

    /// Returns a pointer to the bucket to be allocated.
    fn bucket_ptr(&mut self) -> *mut u8 {
        unsafe {
            let ptr: *mut AtomicUsize = self.ptr.cast();
            let ptr = ptr.sub(1);

            let ptr: *mut usize = ptr.cast();
            let ptr = ptr.sub(1);

            ptr.cast()
        }
    }
}
