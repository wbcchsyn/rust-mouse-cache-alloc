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
use core::hash::{Hash, Hasher};
use core::mem::{forget, size_of, MaybeUninit};
use core::ops::Deref;
use core::ptr::NonNull;
use core::result::Result;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::handle_alloc_error;
use std::borrow::Borrow;
use std::fmt;
use std::panic::{RefUnwindSafe, UnwindSafe};

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
    ptr: NonNull<T>,
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
            self.ptr.as_ptr().drop_in_place();
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

        let ptr = unsafe { NonNull::new_unchecked(&mut bucket.val) };
        let ret = Self { ptr, alloc };
        debug_assert_eq!(layout, ret.layout());
        ret
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
    /// Consumes `self` and returns a pair of a wrapped pointer and the allocator.
    ///
    /// # Safety
    ///
    /// To avoid memory leak, the returned pointer must be converted back to `CrcInner` using
    /// `CrcInner::from_raw` .
    pub unsafe fn into_raw(self) -> (*const T, A) {
        let ptr = self.ptr.as_ptr();

        let alloc = {
            let mut alloc = MaybeUninit::uninit();
            let ptr: *const A = &self.alloc;
            core::ptr::copy_nonoverlapping(ptr, alloc.as_mut_ptr(), 1);
            alloc.assume_init()
        };

        forget(self);
        (ptr, alloc)
    }

    /// Constructs an `Crc` from raw pointer and allocator.
    ///
    /// `ptr` and `alloc` must have been previously returned by a call to `CrcInner<U>::into_raw`
    /// where `U` must have the same size and alignment as `T` .
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `ptr` and `alloc` does not satisfy the requirement.
    pub unsafe fn from_raw(ptr: *const T, alloc: A) -> Self {
        let r = &*ptr;
        let ptr = NonNull::from(r);
        Self { ptr, alloc }
    }

    /// Returns a reference to the reference counter.
    pub fn counter(&self) -> &AtomicUsize {
        unsafe {
            let ptr: *const AtomicUsize = self.ptr.as_ptr().cast();
            let ptr = ptr.sub(1);
            &*ptr
        }
    }

    /// Returns a layout to have allocated the heap.
    fn layout(&self) -> Layout {
        unsafe {
            let ptr: *const AtomicUsize = self.ptr.as_ptr().cast();
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
            let ptr: *mut AtomicUsize = self.ptr.as_ptr().cast();
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
    fn clone() {
        let alloc = TestAlloc::<System>::default();
        let val = TestAlloc::<System>::default();

        let inner0 = CrcInner::new(val, alloc.clone());
        assert_eq!(1, inner0.counter().load(Ordering::Relaxed));

        let inner1 = inner0.clone();
        assert_eq!(2, inner0.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner1.counter().load(Ordering::Relaxed));

        let inner2 = inner1.clone();
        assert_eq!(3, inner0.counter().load(Ordering::Relaxed));
        assert_eq!(3, inner1.counter().load(Ordering::Relaxed));
        assert_eq!(3, inner2.counter().load(Ordering::Relaxed));

        drop(inner0);
        assert_eq!(2, inner1.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner2.counter().load(Ordering::Relaxed));

        drop(inner2);
        assert_eq!(1, inner1.counter().load(Ordering::Relaxed));
    }

    #[test]
    fn into_from_raw() {
        let alloc = TestAlloc::<System>::default();
        let val = TestBox::new(32, &alloc);

        let inner0 = CrcInner::new(val, alloc.clone());
        assert_eq!(1, inner0.counter().load(Ordering::Relaxed));

        let inner1 = inner0.clone();
        assert_eq!(2, inner0.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner1.counter().load(Ordering::Relaxed));

        let (ptr, alloc) = unsafe { CrcInner::into_raw(inner1) };
        let ptr: *const dyn AsRef<i32> = ptr;
        assert_eq!(2, inner0.counter().load(Ordering::Relaxed));

        let inner2 = unsafe { CrcInner::from_raw(ptr, alloc) };
        assert_eq!(2, inner0.counter().load(Ordering::Relaxed));
        assert_eq!(2, inner2.counter().load(Ordering::Relaxed));
    }
}

/// `Crc` is a reference-counting pointer to allocate and to deallocate via `crate::Alloc` .
/// `Crc` stands for 'Cache Reference Counted'.
///
/// It behaves like `std::sync::Arc` except for the followings.
///
/// - `Crc` supports only strong pointer, but not weak pointer.
/// - `Crc` uses `crate::Alloc` to allocate and to deallocate heap memory.
#[derive(Clone)]
pub struct Crc<T: ?Sized>(CrcInner<T, Alloc>);

impl<T> From<T> for Crc<T> {
    fn from(val: T) -> Self {
        Self(CrcInner::new(val, Alloc))
    }
}

impl<T: ?Sized> Deref for Crc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.ptr.as_ref() }
    }
}

impl<T: ?Sized> AsRef<T> for Crc<T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<T: ?Sized> Borrow<T> for Crc<T> {
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T: ?Sized> fmt::Pointer for Crc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0.ptr.fmt(f)
    }
}

impl<T: ?Sized> fmt::Debug for Crc<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Crc")
            .field("pointer", &&*self)
            .field("strong_count", &self.strong_count())
            .finish()
    }
}

impl<T: ?Sized, U: ?Sized> PartialEq<Crc<U>> for Crc<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &Crc<U>) -> bool {
        self.as_ref().eq(other.as_ref())
    }
}

impl<T: ?Sized> Eq for Crc<T> where T: Eq {}

impl<T: ?Sized, U: ?Sized> PartialOrd<Crc<U>> for Crc<T>
where
    T: PartialOrd<U>,
{
    fn partial_cmp(&self, other: &Crc<U>) -> Option<core::cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<T: ?Sized> Ord for Crc<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl<T: ?Sized> Hash for Crc<T>
where
    T: Hash,
{
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        self.as_ref().hash(hasher)
    }
}

unsafe impl<T: ?Sized> Send for Crc<T> where T: Send + Sync {}
unsafe impl<T: ?Sized> Sync for Crc<T> where T: Send + Sync {}

impl<T: ?Sized> UnwindSafe for Crc<T> where T: RefUnwindSafe {}

impl<T: ?Sized> Crc<T> {
    /// Consumes `self` and returns a wrapped pointer.
    ///
    /// # Safety
    ///
    /// To avoid memory leak, the returned pointer must be converted back to `CrcInner` using
    /// `CrcInner::from_raw` .
    pub unsafe fn into_raw(self) -> *const T {
        CrcInner::into_raw(self.0).0
    }

    /// Constructs an `Crc` from a raw pointer.
    ///
    /// `ptr` must have been previously returned by a call to `Crc<U>::into_raw` where `U` must
    /// have the same size and alignment as `T` .
    ///
    /// # Safety
    ///
    /// The behavior is undefined if `ptr` does not satisfy the requirement.
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        Self(CrcInner::from_raw(ptr, Alloc))
    }

    /// Provides a raw pointer to the data.
    pub fn as_ptr(&self) -> *const T {
        self.0.ptr.as_ptr()
    }

    /// Returns the number of strong pointers to this allocation.
    pub fn strong_count(&self) -> usize {
        self.0.counter().load(Ordering::Relaxed)
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

    #[test]
    fn deref() {
        let val = -1892;
        let crc = Crc::from(val);
        assert_eq!(val, *crc);
    }

    #[test]
    fn eq() {
        let val = 45;
        let crc0 = Crc::from(val);
        let crc1 = Crc::from(val);
        assert_eq!(crc0, crc1);

        let val = 13;
        let crc2 = Crc::from(val);
        assert_ne!(crc0, crc2);
    }

    #[test]
    fn cmp() {
        let crc0 = Crc::from(-1);
        let crc1 = Crc::from(0);
        let crc2 = Crc::from(1);
        let crc3 = Crc::from(2);

        assert!(crc0 < crc1);
        assert!(crc1 < crc2);
        assert!(crc2 < crc3);
    }
}
