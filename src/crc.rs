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

use crate::Alloc;
use core::alloc::{GlobalAlloc, Layout};
use core::any::Any;
use core::mem::{forget, size_of, MaybeUninit};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::handle_alloc_error;

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

impl<T: ?Sized, A> Drop for CrcInner<T, A>
where
    A: GlobalAlloc,
{
    fn drop(&mut self) {
        // Decrement the reference count.
        let count = self.counter().fetch_sub(1, Ordering::Release) - 1;

        // Do nothing if another instance is left.
        if count != 0 {
            return;
        }

        // Drop and deallocate.
        let layout = self.layout();
        let ptr = self.bucket_ptr();

        unsafe {
            self.ptr.drop_in_place();
            self.alloc.dealloc(ptr, layout);
        };
    }
}

impl<T, A> CrcInner<T, A>
where
    A: GlobalAlloc,
{
    /// Creates a new instance.
    pub fn new(val: T, alloc: A) -> Self {
        // Allocate memory for Bucket.
        let layout = Layout::new::<Bucket<T>>();
        let ptr = unsafe {
            let ptr = alloc.alloc(layout) as *mut Bucket<T>;
            if ptr.is_null() {
                handle_alloc_error(layout);
            }

            ptr
        };

        // Build bucket
        let bucket = unsafe {
            ptr.write(Bucket::from(val));
            &mut *ptr
        };

        let ptr: *mut T = &mut bucket.val;
        let ret = Self { ptr, alloc };
        debug_assert_eq!(layout, ret.layout());
        ret
    }

    /// Consumes `self` and convert type parameter `T` into `dyn Any` .
    pub fn into_any(self) -> CrcInner<dyn Any, A>
    where
        T: 'static,
    {
        let alloc = unsafe {
            let org: *const A = &self.alloc;
            let mut alloc = MaybeUninit::<A>::uninit();
            alloc.as_mut_ptr().copy_from_nonoverlapping(org, 1);
            alloc.assume_init()
        };

        let ptr: *mut dyn Any = self.ptr;

        forget(self);
        CrcInner::<dyn Any, A> { ptr, alloc }
    }
}

impl<T: ?Sized, A> Clone for CrcInner<T, A>
where
    A: GlobalAlloc + Clone,
{
    fn clone(&self) -> Self {
        self.counter().fetch_add(1, Ordering::Acquire);
        Self {
            ptr: self.ptr,
            alloc: self.alloc.clone(),
        }
    }
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

#[cfg(test)]
mod crcinner_tests {
    extern crate gharial;

    use super::*;
    use gharial::{TestAlloc, TestBox};
    use std::alloc::System;

    #[test]
    fn constructor() {
        let alloc = TestAlloc::<System>::default();

        let val = TestBox::new(1, &alloc);
        let crc_inner = CrcInner::new(val, alloc.clone());

        assert_eq!(1, crc_inner.counter().load(Ordering::Relaxed));
    }

    #[test]
    fn into_any() {
        let val = 1;
        let alloc = TestAlloc::<System>::default();

        let crc_inner = CrcInner::new(val, alloc.clone());
        assert_eq!(1, crc_inner.counter().load(Ordering::Relaxed));

        let crc_inner = CrcInner::into_any(crc_inner);
        assert_eq!(1, crc_inner.counter().load(Ordering::Relaxed));
    }

    #[test]
    fn clone() {
        let val = 0;
        let alloc = TestAlloc::<System>::default();

        let inner0 = CrcInner::new(val, alloc);
        assert_eq!(1, inner0.counter().load(Ordering::Relaxed));

        let inner1 = inner0.clone();
        assert_eq!(2, inner0.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner1.counter().load(Ordering::Relaxed));

        let inner2 = CrcInner::into_any(inner0);
        assert_eq!(2, inner1.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner2.counter().load(Ordering::Relaxed));

        let inner3 = inner2.clone();
        assert_eq!(3, inner1.counter().load(Ordering::Relaxed));
        assert_eq!(3, inner2.counter().load(Ordering::Relaxed));
        assert_eq!(3, inner3.counter().load(Ordering::Relaxed));
    }
}

/// `Crc` is a reference-counting pointer to allocate and to deallocate via `crate::Alloc` .
/// `Crc` stands for 'Cache Reference Counted'.
///
/// It behaves like `std::sync::Arc` except for the followings.
///
/// - `Crc` supports only strong pointer, but not weak pointer.
/// - `Crc` uses `crate::Alloc` to allocate and to deallocate heap memory.
pub struct Crc<T: ?Sized>(CrcInner<T, Alloc>);

impl<T> From<T> for Crc<T> {
    fn from(val: T) -> Self {
        Self(CrcInner::new(val, Alloc))
    }
}

#[cfg(test)]
mod crc_tests {
    extern crate gharial;

    use super::*;
    use gharial::{TestAlloc, TestBox};
    use std::alloc::System;

    #[test]
    fn from() {
        let alloc = TestAlloc::<System>::default();
        let val = TestBox::new(3, &alloc);
        let _crc = Crc::from(val);
    }
}
