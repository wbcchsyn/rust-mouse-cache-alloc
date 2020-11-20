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

use crate::{allocating_size, decrease_cache_size, increase_cache_size};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::{Extend, FromIterator};
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::slice::{Iter, IterMut, SliceIndex};
use std::borrow::{Borrow, BorrowMut, Cow};
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::ffi::CString;
use std::io::{Result, Write};

/// A wrapper of `std::vec::Vec` to use `crate::Alloc` .
///
/// This struct will not be used after [`allocator_api`] and the [`integration`]
/// will be merged into rust stable toolchain.
///
/// [`allocator_api`]: https://github.com/rust-lang/rust/issues/32838
/// [`integration`]: https://github.com/rust-lang/rust/pull/42313
#[derive(Debug)]
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

/// Delegate methods which can allocate or deallocate heap memory.
///
/// Note that the capacity must not be shrinked; i.e. method `shrink_to_fit` must not be
/// implemented.
/// (This is because `std::vec::Vec` could place the buffer on stack for optimization.
/// This package cannot distinguish whether the buffer is on heap or not, and the behavior
/// is undefined if it is on stack.)
impl<T> Vec<T> {
    /// Creates an empty instance with specified `capacity` .
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::with_capacity` for details.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut ret = Self::new();
        ret.reserve_exact(capacity);
        ret
    }

    /// Reserves capacity for at least `additional` more elements to hold.
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::reserve` for details.
    pub fn reserve(&mut self, additional: usize) {
        let old_ptr = self.as_ptr();
        self.inner.reserve(additional);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Reserves the minimum capacity for at least `additional` more elements to hold.
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::reserve_exact` for details.
    pub fn reserve_exact(&mut self, additional: usize) {
        let old_ptr = self.as_ptr();
        self.inner.reserve_exact(additional);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Inserts `element` at position `index` .
    ///
    /// The all elements after `index` will be shifted to the right.
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::insert` for details.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than `self.len` .
    pub fn insert(&mut self, index: usize, element: T) {
        let old_ptr = self.as_ptr();
        self.inner.insert(index, element);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Appends `element` at the end of `self` .
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::push` for details.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than `self.len` .
    pub fn push(&mut self, element: T) {
        let old_ptr = self.as_ptr();
        self.inner.push(element);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing elements in the range [at, len).
    /// After the call, `self` will be left containing elements [0, at).
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::split_off` for details.
    ///
    /// # Panics
    ///
    /// Panics if `at` is greater than `self.len` .
    pub fn split_off(&mut self, at: usize) -> Self {
        let _old_ptr = self.as_ptr();
        let inner = self.inner.split_off(at);
        debug_assert_eq!(_old_ptr, self.as_ptr());

        let size = unsafe { allocating_size(inner.as_ptr()) };
        Self { inner, size }
    }

    /// Resize `self` in place so that `self.len` will equal to `new_len` .
    ///
    /// If `new_len` is less than `self.len` , `self` will be simply truncated; otherwise,
    /// pushes elements till `self.len` is `new_len` . Element is created by calling `f` on
    /// evely push.
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::resize_with` for details.
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        let old_ptr = self.as_ptr();
        let ret = self.inner.resize_with(new_len, f);
        unsafe { self.update_cache_size(old_ptr) };

        ret
    }

    /// Resize `self` in place so that `self.len` will equal to `new_len` .
    ///
    /// If `new_len` is less than `self.len` , `self` will be simply truncated; otherwise,
    /// clones `value` and pushes till `self.len` is `new_len` .
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::resize` for details.
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        let old_ptr = self.as_ptr();
        self.inner.resize(new_len, value);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Clones and appends all the elements in `other` .
    ///
    /// This method delegates to the inner `std::vec::Vec` except for updating
    /// cache memory size to allocate.
    /// See `std::vec::Vec::extend_from_slice` for details.
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        let old_ptr = self.as_ptr();
        self.inner.extend_from_slice(other);
        unsafe { self.update_cache_size(old_ptr) };
    }

    /// Checks the buffer is newly allocated or not, and updates the cache using memory size.
    ///
    /// # Safety
    ///
    /// The behavior is undefined if the buffer is currently on stack and if old_ptr is on heap.
    unsafe fn update_cache_size(&mut self, old_ptr: *const T) {
        let new_ptr = self.as_ptr();

        if old_ptr != new_ptr {
            let new_size = allocating_size(new_ptr);
            debug_assert!(self.size < new_size);
            increase_cache_size(new_size - self.size);
            self.size = new_size;
        }
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

impl<T> AsMut<[T]> for Vec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.as_mut()
    }
}

impl<T> AsRef<[T]> for Vec<T> {
    fn as_ref(&self) -> &[T] {
        self.inner.as_ref()
    }
}

impl<T> Borrow<[T]> for Vec<T> {
    fn borrow(&self) -> &[T] {
        self.inner.borrow()
    }
}

impl<T> BorrowMut<[T]> for Vec<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.inner.borrow_mut()
    }
}

impl<T> Clone for Vec<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut ret = Self::new();
        ret.extend_from_slice(self.as_ref());
        ret
    }
}

impl<T> Default for Vec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.deref_mut()
    }
}

impl<T> Eq for Vec<T> where T: Eq {}

impl<'a, T> Extend<&'a T> for Vec<T>
where
    T: 'a + Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        let old_ptr = self.as_ptr();
        self.inner.extend(iter);
        unsafe { self.update_cache_size(old_ptr) };
    }
}

impl<T> Extend<T> for Vec<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        let old_ptr = self.as_ptr();
        self.inner.extend(iter);
        unsafe { self.update_cache_size(old_ptr) };
    }
}

impl<T> From<std::vec::Vec<T>> for Vec<T> {
    fn from(inner: std::vec::Vec<T>) -> Self {
        let mut ret = Self::new();
        let old_ptr = ret.as_ptr();
        ret.inner = inner;
        unsafe { ret.update_cache_size(old_ptr) };
        ret
    }
}

impl<T> From<&'_ [T]> for Vec<T>
where
    T: Clone,
{
    fn from(s: &[T]) -> Self {
        let inner = std::vec::Vec::<T>::from(s);
        Self::from(inner)
    }
}

impl<T> From<&'_ mut [T]> for Vec<T>
where
    T: Clone,
{
    fn from(s: &mut [T]) -> Self {
        let inner = std::vec::Vec::<T>::from(s);
        Self::from(inner)
    }
}

impl From<&'_ str> for Vec<u8> {
    fn from(s: &str) -> Self {
        Self::from(s.as_bytes())
    }
}

impl<T> From<BinaryHeap<T>> for Vec<T> {
    fn from(bh: BinaryHeap<T>) -> Self {
        let inner = std::vec::Vec::<T>::from(bh);
        Self::from(inner)
    }
}

impl<T> From<Box<[T]>> for Vec<T> {
    fn from(b: Box<[T]>) -> Self {
        let inner = std::vec::Vec::<T>::from(b);
        Self::from(inner)
    }
}

impl From<CString> for Vec<u8> {
    fn from(s: CString) -> Self {
        let inner = std::vec::Vec::<u8>::from(s);
        Self::from(inner)
    }
}

impl From<String> for Vec<u8> {
    fn from(s: String) -> Self {
        let inner = std::vec::Vec::<u8>::from(s);
        Self::from(inner)
    }
}

impl<T> From<VecDeque<T>> for Vec<T> {
    fn from(q: VecDeque<T>) -> Self {
        let inner = std::vec::Vec::<T>::from(q);
        Self::from(inner)
    }
}

impl<T> FromIterator<T> for Vec<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let inner = std::vec::Vec::<T>::from_iter(iter);
        Self::from(inner)
    }
}

impl<T> Hash for Vec<T>
where
    T: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        self.inner.hash(state);
    }
}

impl<T, I> Index<I> for Vec<T>
where
    I: SliceIndex<[T]>,
{
    type Output = <I as SliceIndex<[T]>>::Output;
    fn index(&self, index: I) -> &Self::Output {
        self.inner.index(index)
    }
}

impl<T, I> IndexMut<I> for Vec<T>
where
    I: SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.inner.index_mut(index)
    }
}

impl<'a, T> IntoIterator for &'a mut Vec<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        (&mut self.inner).into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Vec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.inner).into_iter()
    }
}

impl<T> Ord for Vec<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<A, B> PartialEq<&'_ [B]> for Vec<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B]) -> bool {
        self.inner.eq(other)
    }
}

impl<A, B> PartialEq<&'_ mut [B]> for Vec<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut [B]) -> bool {
        self.inner.eq(other)
    }
}

impl<A, B> PartialEq<Vec<B>> for VecDeque<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.eq(&other.inner)
    }
}

impl<A, B> PartialEq<Vec<B>> for &'_ [A]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.eq(&other.inner)
    }
}

impl<A, B> PartialEq<Vec<B>> for &'_ mut [A]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.eq(&other.inner)
    }
}

impl<A, B> PartialEq<Vec<B>> for Cow<'_, [A]>
where
    A: PartialEq<B> + Clone,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.eq(&other.inner)
    }
}

impl<A, B> PartialEq<Vec<B>> for Vec<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<A, B> PartialEq<Vec<B>> for std::vec::Vec<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B>) -> bool {
        self.eq(&other.inner)
    }
}

impl<A, B> PartialEq<std::vec::Vec<B>> for Vec<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &std::vec::Vec<B>) -> bool {
        self.inner.eq(other)
    }
}

impl<T> PartialOrd<Vec<T>> for Vec<T>
where
    T: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<T> PartialOrd<Vec<T>> for std::vec::Vec<T>
where
    T: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &Vec<T>) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
}

impl<T> PartialOrd<std::vec::Vec<T>> for Vec<T>
where
    T: PartialOrd<T>,
{
    fn partial_cmp(&self, other: &std::vec::Vec<T>) -> Option<Ordering> {
        self.inner.partial_cmp(other)
    }
}

impl Write for Vec<u8> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let old_ptr = self.as_ptr();
        let ret = self.inner.write(buf);
        unsafe { self.update_cache_size(old_ptr) };
        ret
    }

    fn flush(&mut self) -> Result<()> {
        let old_ptr = self.as_ptr();
        let ret = self.inner.flush();
        unsafe { self.update_cache_size(old_ptr) };
        ret
    }
}
