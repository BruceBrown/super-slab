#![deny(warnings, missing_docs, missing_debug_implementations)]
#![cfg_attr(test, deny(warnings, unreachable_pub))]

//! Why multiply, when you can divide.
//! I'd like to acknowledge the wonderful work done by the developers of Slab.
//! Much of this is a direct derivative of their work.
//!
//! Build on top of Slab, SuperSlab uses an extent model, where a primary capacity
//! is allocated. When full, a new slab of a secondary size is added to the
//! SuperSlab. The primary advantage is that allocation doesn't reallocate the
//! Slab.
//!
//! Nearly all of the Slab methods are present here as well. The notable exceptions
//! being:
//! * reserve()
//! * reserve_exact()
//! * shrink_to_fit()
//! * compact()
//! * key_of
//! * various flavors of DoubleEndedIterator
//!
//! # Examples
//!
//! Basic storing and retrieval.
//!
//! ```
//! # use super_slab::*;
//! let mut slab = SuperSlab::new();
//!
//! let hello = slab.insert("hello");
//! let world = slab.insert("world");
//!
//! assert_eq!(slab[hello], "hello");
//! assert_eq!(slab[world], "world");
//!
//! slab[world] = "earth";
//! assert_eq!(slab[world], "earth");
//! ```
//!
//! Sometimes it is useful to be able to associate the key with the value being
//! inserted in the slab. This can be done with the `vacant_entry` API as such:
//!
//! ```
//! # use super_slab::*;
//! let mut slab = SuperSlab::new();
//!
//! let hello = {
//!     let entry = slab.vacant_entry();
//!     let key = entry.key();
//!
//!     entry.insert((key, "hello"));
//!     key
//! };
//!
//! assert_eq!(hello, slab[hello].0);
//! assert_eq!("hello", slab[hello].1);
//! ```
//!
//! It is generally a good idea to specify the desired capacity of a slab at
//! creation time. Note that `SuperSlab` will add a new slab when attempting
//! to insert a new value once the existing capacity has been reached.
//!
//! ```
//! # use super_slab::*;
//! let mut slab = SuperSlab::with_capacity(1024);
//!
//! // ... use the slab
//!
//!
//! slab.insert("the slab is not at capacity yet");
//! ```
//!
//! For complete constroll, you can specify the primary capacity, the secondary
//! capacity and the capacity of the slab vec.
//!
//! ```
//! # use super_slab::*;
//!
//! // allocate a primary capacity of 5000, once that fills, a new slab
//! // with capacity 1000 will be allocated. Once 8 have been allocated,
//! // the slab vec will need to be reallocated.
//!
//! let mut slab = SuperSlab::with_capacity_and_extents(5000, 1000, 8);
//!
//!
//! // ... use the slab
//!
//!
//! slab.insert("the slab is not at capacity yet");
//! ```

use std::fmt;
use std::iter::IntoIterator;
use std::ops;

use slab::Slab;

/// A SuperSlab is a collection of Slabs, viewed as single Slab.
#[derive(Clone)]
pub struct SuperSlab<T> {
    primary_capacity: usize,
    secondary_capacity: usize,
    slabs: Vec<Slab<T>>,
}

impl<T> Default for SuperSlab<T> {
    fn default() -> Self { Self::new() }
}

/// A handle to a vacant entry in a `Slab`.
///
/// `VacantEntry` allows constructing values with the key that they will be
/// assigned to.
///
/// # Examples
///
/// ```
/// # use super_slab::*;
/// let mut slab = SuperSlab::new();
///
/// let hello = {
///     let entry = slab.vacant_entry();
///     let key = entry.key();
///
///     entry.insert((key, "hello"));
///     key
/// };
///
/// assert_eq!(hello, slab[hello].0);
/// assert_eq!("hello", slab[hello].1);
/// ```
#[derive(Debug)]
pub struct VacantEntry<'a, T: 'a> {
    key_offset: usize,
    vacant_entry: slab::VacantEntry<'a, T>,
}

/// An iterator over the `Slabs`
pub struct Iter<'a, T: 'a> {
    slabs: std::slice::Iter<'a, Slab<T>>,
    slab_iter: slab::Iter<'a, T>,
    primary_capacity: usize,
    secondary_capacity: usize,
    key_offset: usize,
}

/// A mutable iterator over the `Slabs`
pub struct IterMut<'a, T: 'a> {
    slabs: std::slice::IterMut<'a, Slab<T>>,
    slab_iter: slab::IterMut<'a, T>,
    primary_capacity: usize,
    secondary_capacity: usize,
    key_offset: usize,
}

/// A draining iterator for `Slabs`
pub struct Drain<'a, T: 'a> {
    iter: std::slice::IterMut<'a, Slab<T>>,
    draining: slab::Drain<'a, T>,
}

impl<T> SuperSlab<T> {
    /// Construct a new, empty `SuperSlab`.
    /// The function allocates 4 extents with each `Slab` having a capacity of 4.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let slab: SuperSlab<i32> = SuperSlab::new();
    /// assert_eq!(slab.capacity(), 16);
    /// ```
    pub fn new() -> Self { Self::with_capacity(16) }

    /// Construct a new, empty `SuperSlab` with the specified capacity.
    ///
    /// The returned slab will be able to store exactly `capacity` without
    /// allocating an extent. If `capacity` is 0, a panic will occur.
    ///
    /// It is important to note that this function does not specify the *length*
    /// of the returned slab, but only the capacity. For an explanation of the
    /// difference between length and capacity, see [Capacity and
    /// reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    ///
    /// // allocate with a capacity of 10, reserve 4 extents, each with a capacity of 2
    /// // this produces two allocation, one for the extents (4 slots) and one for
    /// // the primary (10 entries).
    ///
    /// let mut slab = SuperSlab::with_capacity_and_extents(10, 2, 4);
    ///
    /// // The slab contains no values, even though it has capacity for more
    /// assert_eq!(slab.len(), 0);
    /// assert_eq!(slab.capacity(), 10);
    ///
    /// // These are all done without extending...
    /// for i in 0..10 {
    ///     slab.insert(i);
    /// }
    ///
    /// // ...but this will make the super slab add an extent
    /// slab.insert(11);
    /// assert_eq!(slab.capacity(), 12);
    /// ```
    pub fn with_capacity_and_extents(capacity: usize, secondary: usize, extents: usize) -> Self {
        if capacity == 0 {
            panic!("capacity must not be zero")
        }
        if secondary == 0 {
            panic!("secondary must not be zero")
        }
        if extents == 0 {
            panic!("extents must not be zero")
        }

        let mut slabs: Vec<Slab<T>> = Vec::with_capacity(extents);
        slabs.push(Slab::<T>::with_capacity(capacity));
        Self {
            primary_capacity: capacity,
            secondary_capacity: secondary,
            slabs,
        }
    }

    /// Simpler instantiation of a slab. This will extents will be 1/4 of capacity or capacity if capacity
    /// is less than or equal to 100.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    ///
    /// // allocate with a capacity of 10, reserve 4 extents, each with a capacity of 10
    /// // this produces two allocation, one for the extents (4 slots) and one for
    /// // the primary (10 entries).
    ///
    /// let mut slab = SuperSlab::with_capacity(10);
    ///
    /// // The slab contains no values, even though it has capacity for more
    /// assert_eq!(slab.len(), 0);
    /// assert_eq!(slab.capacity(), 10);
    ///
    /// // These are all done without extending...
    /// for i in 0..10 {
    ///     slab.insert(i);
    /// }
    ///
    /// // ...but this will make the super slab add an extent
    /// slab.insert(11);
    /// assert_eq!(slab.capacity(), 20);
    /// ```

    pub fn with_capacity(capacity: usize) -> Self {
        let secondary = if capacity >= 100 { capacity >> 2 } else { capacity };
        Self::with_capacity_and_extents(capacity, secondary, 4)
    }

    /// Return the number of values the slab can store without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let slab: SuperSlab<i32> = SuperSlab::with_capacity(10);
    /// assert_eq!(slab.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize { self.primary_capacity + ((self.slabs.len() - 1) * self.secondary_capacity) }

    /// reserve is not supported. It seems to have limited value in a SuperSlab.
    /// reserve_exact is not supported. It seems to have limited value in a SuperSlab.
    /// shrink_to_fit is not supported. It seems to have limited value in a SuperSlab.
    /// compact is not supported. It may be supported in the future

    /// Clear the slabs of all values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// for i in 0..slab.capacity() {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.clear();
    /// assert!(slab.is_empty());
    /// ```
    pub fn clear(&mut self) { self.slabs.iter_mut().for_each(|s| s.clear()); }

    /// Return the number of stored values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// for i in 0..6 {
    ///     slab.insert(i);
    /// }
    ///
    /// assert_eq!(6, slab.len());
    /// ```
    pub fn len(&self) -> usize {
        let mut len: usize = 0;
        self.slabs.iter().for_each(|s| len += s.len());
        len
    }

    /// Return `true` if there are no values stored in the slab.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// assert!(slab.is_empty());
    ///
    /// slab.insert(1);
    /// assert!(!slab.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.slabs.iter().all(|s| s.is_empty()) }

    /// Return an iterator over the slabs.
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vacant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::with_capacity(2);
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// let mut iterator = slab.iter();
    /// assert_eq!(iterator.next(), Some((0, &0)));
    /// assert_eq!(iterator.next(), Some((1, &1)));
    /// assert_eq!(iterator.next(), Some((2, &2)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        let mut slabs = self.slabs.iter();
        let slab_iter = slabs.next().unwrap().iter();
        Iter {
            slabs,
            slab_iter,
            primary_capacity: self.primary_capacity,
            secondary_capacity: self.secondary_capacity,
            key_offset: 0,
        }
    }

    /// Return an iterator that allows modifying each value.
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vacant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::with_capacity(2);
    ///
    /// let key1 = slab.insert(0);
    /// let key2 = slab.insert(1);
    ///
    /// for (key, val) in slab.iter_mut() {
    ///     if key == key1 {
    ///         *val += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 1);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let mut slabs = self.slabs.iter_mut();
        let slab_iter = slabs.next().unwrap().iter_mut();
        IterMut {
            slabs,
            slab_iter,
            primary_capacity: self.primary_capacity,
            secondary_capacity: self.secondary_capacity,
            key_offset: 0,
        }
    }

    /// Return a reference to the value associated with the given key.
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// let key = slab.insert("hello");
    ///
    /// assert_eq!(slab.get(key), Some(&"hello"));
    /// assert_eq!(slab.get(123), None);
    /// ```
    pub fn get(&self, key: usize) -> Option<&T> {
        let (sub_key, slab) = self.conv_from_key(key);
        if slab >= self.slabs.len() {
            return None;
        }
        self.slabs[slab].get(sub_key)
    }

    /// Return a mutable reference to the value associated with the given key.
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// let key = slab.insert("hello");
    ///
    /// *slab.get_mut(key).unwrap() = "world";
    ///
    /// assert_eq!(slab[key], "world");
    /// assert_eq!(slab.get_mut(123), None);
    /// ```
    pub fn get_mut(&mut self, key: usize) -> Option<&mut T> {
        let (sub_key, slab) = self.conv_from_key(key);
        if slab >= self.slabs.len() {
            return None;
        }
        self.slabs[slab].get_mut(sub_key)
    }

    /// Return a reference to the value associated with the given key without
    /// performing bounds checking.
    ///
    /// # Safety
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// let key = slab.insert(2);
    ///
    /// unsafe {
    ///     assert_eq!(slab.get_unchecked(key), &2);
    /// }
    /// ```
    pub unsafe fn get_unchecked(&self, key: usize) -> &T {
        let (sub_key, slab) = self.conv_from_key(key);
        self.slabs[slab].get_unchecked(sub_key)
    }

    /// Return a mutable reference to the value associated with the given key
    /// without performing bounds checking.
    ///
    /// # Safety
    /// This function should be used with care.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// let key = slab.insert(2);
    ///
    /// unsafe {
    ///     let val = slab.get_unchecked_mut(key);
    ///     *val = 13;
    /// }
    ///
    /// assert_eq!(slab[key], 13);
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, key: usize) -> &mut T {
        let (sub_key, slab) = self.conv_from_key(key);
        self.slabs[slab].get_unchecked_mut(sub_key)
    }

    /// key_of is not supported. It may be supported in the future.

    /// Insert a value in the slab, returning key assigned to the value.
    ///
    /// The returned key can later be used to retrieve or remove the value using indexed
    /// lookup and `remove`. Additional capacity is allocated if needed. See
    /// [Capacity and reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the vector overflows a `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    /// let key = slab.insert("hello");
    /// assert_eq!(slab[key], "hello");
    /// ```
    pub fn insert(&mut self, val: T) -> usize {
        let primary_capacity = self.primary_capacity;
        let secondary_capacity = self.secondary_capacity;
        // find a slab that is not at capacity and insert into it
        match self.slabs.iter_mut().enumerate().find(|val| val.1.len() != val.1.capacity()) {
            Some((idx, slab)) => {
                let k = slab.insert(val);
                if idx == 0 {
                    k
                } else {
                    k + primary_capacity + ((idx - 1) * secondary_capacity)
                }
            },
            None => {
                let mut slab = Slab::with_capacity(self.secondary_capacity);
                let res = self.conv_into_key(slab.insert(val), self.slabs.len());
                self.slabs.push(slab);
                res
            },
        }
    }

    // convert internal key/slab index to external key
    #[inline]
    fn conv_into_key(&self, key: usize, idx: usize) -> usize {
        let res = if idx == 0 {
            key
        } else {
            key + self.primary_capacity + ((idx - 1) * self.secondary_capacity)
        };
        res
    }

    // convert exteneral key to internal key/slab index
    #[inline]
    const fn conv_from_key(&self, key: usize) -> (usize, usize) {
        if key < self.primary_capacity {
            (key, 0)
        } else {
            let k = key - self.primary_capacity;
            (k % self.secondary_capacity, (k / self.secondary_capacity) + 1)
        }
    }

    /// Return a handle to a vacant entry allowing for further manipulation.
    ///
    /// This function is useful when creating values that must contain their
    /// slab key. The returned `VacantEntry` reserves a slot in the slab and is
    /// able to query the associated key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn vacant_entry(&mut self) -> VacantEntry<T> {
        let idx = self.find_or_create_available_slab();
        VacantEntry {
            key_offset: self.conv_into_key(0, idx),
            vacant_entry: self.slabs[idx].vacant_entry(),
        }
    }

    fn find_or_create_available_slab(&mut self) -> usize {
        for (idx, slab) in self.slabs.iter_mut().enumerate() {
            if slab.len() != slab.capacity() {
                return idx;
            }
        }
        // need to add an extent
        let slab = Slab::with_capacity(self.secondary_capacity);
        self.slabs.push(slab);
        self.slabs.len() - 1
    }

    /// Remove and return the value associated with the given key.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not associated with a value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// let hello = slab.insert("hello");
    ///
    /// assert_eq!(slab.remove(hello), "hello");
    /// assert!(!slab.contains(hello));
    /// ```
    pub fn remove(&mut self, key: usize) -> T {
        let (sub_key, slab) = self.conv_from_key(key);
        self.slabs[slab].remove(sub_key)
    }

    /// Return `true` if a value is associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// let hello = slab.insert("hello");
    /// assert!(slab.contains(hello));
    ///
    /// slab.remove(hello);
    ///
    /// assert!(!slab.contains(hello));
    /// ```
    pub fn contains(&self, key: usize) -> bool {
        let (sub_key, slab) = self.conv_from_key(key);
        self.slabs[slab].contains(sub_key)
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(usize, &mut e)`
    /// returns false. This method operates in place and preserves the key
    /// associated with the retained values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::with_capacity(2);
    ///
    /// let k1 = slab.insert(0);
    /// let k2 = slab.insert(1);
    /// let k3 = slab.insert(2);
    ///
    /// slab.retain(|key, val| key == k1 || *val == 1);
    ///
    /// assert!(slab.contains(k1));
    /// assert!(slab.contains(k2));
    /// assert!(!slab.contains(k3));
    ///
    /// assert_eq!(2, slab.len());
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize, &mut T) -> bool,
    {
        use std::sync::atomic::{AtomicUsize, Ordering};
        // wrap the enclosure to deal with keys
        let offset = AtomicUsize::new(0);
        let mut wrapper = |key: usize, val: &mut T| -> bool { f(key + offset.load(Ordering::SeqCst), val) };
        for slab in self.slabs.iter_mut() {
            slab.retain(&mut wrapper);
            let capacity = if offset.load(Ordering::SeqCst) == 0 {
                self.primary_capacity
            } else {
                self.secondary_capacity
            };
            offset.fetch_add(capacity, Ordering::SeqCst);
        }
    }

    /// Return a draining iterator that removes all elements from the slab and
    /// yields the removed items.
    ///
    /// Note: Elements are removed even if the iterator is only partially
    /// consumed or not consumed at all.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// let _ = slab.insert(0);
    /// let _ = slab.insert(1);
    /// let _ = slab.insert(2);
    ///
    /// {
    ///     let mut drain = slab.drain();
    ///
    ///     assert_eq!(Some(0), drain.next());
    ///     assert_eq!(Some(1), drain.next());
    ///     assert_eq!(Some(2), drain.next());
    ///     assert_eq!(None, drain.next());
    /// }
    ///
    /// assert!(slab.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<T> {
        let mut iter = self.slabs.iter_mut();
        let draining = iter.next().unwrap().drain();
        Drain { iter, draining }
    }
}

impl<T> ops::Index<usize> for SuperSlab<T> {
    type Output = T;

    fn index(&self, key: usize) -> &T {
        let (sub_key, slab) = self.conv_from_key(key);
        if slab >= self.slabs.len() {
            panic!("invalid key")
        }
        self.slabs[slab].index(sub_key)
    }
}

impl<T> ops::IndexMut<usize> for SuperSlab<T> {
    fn index_mut(&mut self, key: usize) -> &mut T {
        let (sub_key, slab) = self.conv_from_key(key);
        if slab >= self.slabs.len() {
            panic!("invalid key")
        }
        self.slabs[slab].index_mut(sub_key)
    }
}

impl<'a, T> IntoIterator for &'a SuperSlab<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> { self.iter() }
}

impl<'a, T> IntoIterator for &'a mut SuperSlab<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> { self.iter_mut() }
}

impl<T> fmt::Debug for SuperSlab<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("SuperSlab")
            .field("len", &self.len())
            .field("cap", &self.capacity())
            .field("ext", &self.slabs.len())
            .finish()
    }
}

impl<'a, T: 'a> fmt::Debug for Iter<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Iter")
            .field("slabs", &self.slabs)
            .field("cap", &self.primary_capacity)
            .finish()
    }
}

impl<'a, T: 'a> fmt::Debug for IterMut<'a, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("IterMut")
            .field("slabs", &self.slabs)
            .field("cap", &self.primary_capacity)
            .finish()
    }
}

impl<'a, T: 'a> fmt::Debug for Drain<'a, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { fmt.debug_struct("Drain").finish() }
}

// ===== VacantEntry =====

impl<'a, T> VacantEntry<'a, T> {
    /// Insert a value in the entry, returning a mutable reference to the value.
    ///
    /// To get the key associated with the value, use `key` prior to calling
    /// `insert`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use super_slab::*;
    /// let mut slab = SuperSlab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn insert(self, val: T) -> &'a mut T { self.vacant_entry.insert(val) }

    /// Return the key associated with this entry.
    ///
    /// A value stored in this entry will be associated with this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn key(&self) -> usize { self.vacant_entry.key() + self.key_offset }
}

// ===== Iter =====

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<(usize, &'a T)> {
        // try advancing within the current slab
        if let Some((key, val)) = self.slab_iter.next() {
            return Some((key + self.key_offset, val));
        }
        // advance to the next slab that has entries
        while let Some(slab) = self.slabs.next() {
            self.key_offset += if self.key_offset == 0 {
                self.primary_capacity
            } else {
                self.secondary_capacity
            };
            if slab.is_empty() {
                continue;
            }
            self.slab_iter = slab.iter();
            if let Some((key, val)) = self.slab_iter.next() {
                return Some((key + self.key_offset, val));
            }
        }
        None
    }
}

/// DoubleEndedIterator for Iter isn't supported.

// ===== IterMut =====

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    fn next(&mut self) -> Option<(usize, &'a mut T)> {
        // try advancing within the current slab
        if let Some((key, val)) = self.slab_iter.next() {
            return Some((key + self.key_offset, val));
        }
        // advance to the next slab that has entries
        while let Some(slab) = self.slabs.next() {
            self.key_offset += if self.key_offset == 0 {
                self.primary_capacity
            } else {
                self.secondary_capacity
            };
            if slab.is_empty() {
                continue;
            }
            self.slab_iter = slab.iter_mut();
            if let Some((key, val)) = self.slab_iter.next() {
                return Some((key + self.key_offset, val));
            }
        }
        None
    }
}

/// DoubleEndedIterator for IterMut isn't supported.

// ===== Drain =====

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        loop {
            match self.draining.next() {
                Some(v) => break Some(v),
                None => match self.iter.next() {
                    Some(slab) => self.draining = slab.drain(),
                    None => break None,
                },
            }
        }
    }
}

/// DoubleEndedIterator for Drain isn't supported.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iter() {
        let mut super_slab = SuperSlab::with_capacity(2);
        for i in 0 .. 6 {
            super_slab.insert(i);
        }
        assert_eq!(super_slab.get(4), Some(&4));
        // remove all from 2nd extend and remove last from 3rd
        super_slab.remove(2);
        super_slab.remove(3);
        super_slab.remove(5);
        let mut iterator = super_slab.iter();
        assert_eq!(iterator.next(), Some((0, &0)));
        assert_eq!(iterator.next(), Some((1, &1)));
        assert_eq!(iterator.next(), Some((4, &4)));
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.next(), None);
    }
}
