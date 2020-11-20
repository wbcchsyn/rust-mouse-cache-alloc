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

use crate::decrease_cache_size;

/// A wrapper of `std::vec::Vec` to use `crate::Alloc` .
///
/// This struct will not be used after [`allocator_api`] and the [`integration`]
/// will be merged into rust stable toolchain.
///
/// [`allocator_api`]: https://github.com/rust-lang/rust/issues/32838
/// [`integration`]: https://github.com/rust-lang/rust/pull/42313
pub struct Vec<T> {
    inner: std::vec::Vec<T>,
    size: usize,
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        decrease_cache_size(self.size);
    }
}

/// Delegate methods without allocation.
impl<T> Vec<T> {
    /// Creates an empty instance.
    pub const fn new() -> Self {
        Self {
            inner: std::vec::Vec::<T>::new(),
            size: 0,
        }
    }

    /// Returns the number of elements `self` can hold without allocation.
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::capacity` for detail.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Enshortens `self` , keeping the first `len` elements and drop the rest.
    ///
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::truncate` for detail.
    pub fn truncate(&mut self, len: usize) {
        let _old_ptr = self.as_ptr();
        self.inner.truncate(len);
        debug_assert_eq!(_old_ptr, self.as_ptr());
    }

    /// Extracts a slice containing the entire elements in `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::as_slice` for detail.
    pub fn as_slice(&self) -> &[T] {
        self.inner.as_slice()
    }

    /// Extracts a mutable slice containing the entire elements in `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::as_mut_slice` for detail.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.inner.as_mut_slice()
    }

    /// Returns a raw pointer to the buffer of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::as_ptr` for detail.
    pub fn as_ptr(&self) -> *const T {
        self.inner.as_ptr()
    }

    /// Returns a mutable raw pointer to the buffer of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::as_mut_ptr` for detail.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_mut_ptr()
    }

    /// Force to update the `len` to `new_len` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::set_len` for detail.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.inner.set_len(new_len)
    }

    /// Removes the element at `index` and returns it.
    ///
    /// This method does not preserve the ordering, but is O(1).
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::swap_remove` for detail.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> T {
        let _old_ptr = self.as_ptr();
        let ret = self.inner.swap_remove(index);
        debug_assert_eq!(_old_ptr, self.as_ptr());

        ret
    }

    /// Removes the element at `index` and returns it.
    ///
    /// All the elements after `index` are shifted to left.
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::remove` for detail.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn remove(&mut self, index: usize) -> T {
        let _old_ptr = self.as_ptr();
        let ret = self.inner.remove(index);
        debug_assert_eq!(_old_ptr, self.as_ptr());

        ret
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, removes all the elements `f(&e)` returns false.
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::retain` for detail.
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let _old_ptr = self.as_ptr();
        self.inner.retain(f);
        debug_assert_eq!(_old_ptr, self.as_ptr());
    }

    /// Removes all but the first of consecutive elements that resolve to the same key.
    ///
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::dedup_by_key` for detail.
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq<K>,
    {
        let _old_ptr = self.as_ptr();
        self.inner.dedup_by_key(key);
        debug_assert_eq!(_old_ptr, self.as_ptr());
    }

    /// Removes all but the first of consecutive elements satisfying a given equality relation.
    ///
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::dedup_by` for detail.
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let _old_ptr = self.as_ptr();
        self.inner.dedup_by(same_bucket);
        debug_assert_eq!(_old_ptr, self.as_ptr());
    }

    /// Returns None if empty; otherwise, removes the last element of `self` and returns it.
    ///
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::pop` for detail.
    pub fn pop(&mut self) -> Option<T> {
        let _old_ptr = self.as_ptr();
        let ret = self.inner.pop();
        debug_assert_eq!(_old_ptr, self.as_ptr());

        ret
    }

    /// Creates a draining iterator that removes specified range in `self` and yields the removed items.
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::drain` for detail.
    pub fn drain<R>(&mut self, range: R) -> std::vec::Drain<'_, T>
    where
        R: core::ops::RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    /// Removes all the elements.
    ///
    /// Note that this method has no effect on the allocated capacity of `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::clear` for detail.
    pub fn clear(&mut self) {
        let _old_ptr = self.as_ptr();
        self.inner.clear();
        debug_assert_eq!(_old_ptr, self.as_ptr());
    }

    /// Returns the number of elements in `self` .
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::len` for detail.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if `self` has no element, or false.
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::is_empty` for detail.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Removes all but the first consecutive repeated elements according to the `PartialEq` trait implementation.
    ///
    /// This method just delegates to the inner `std::vec::Vec` .
    /// See `std::vec::Vec::dedup` for detail.
    pub fn dedup(&mut self)
    where
        T: PartialEq<T>,
    {
        let _old_ptr = self.as_ptr();
        self.inner.dedup();
        debug_assert_eq!(_old_ptr, self.as_ptr())
    }
}
