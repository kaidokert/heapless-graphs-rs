// SPDX-License-Identifier: Apache-2.0

//! [SetTrait] that abstracts hash sets

pub mod staticset;

/// Basic abstraction for a set type.
pub trait SetTrait<K> {
    /// Creates an empty set.
    fn new() -> Self
    where
        Self: Sized;

    /// Inserts a key into the set.
    ///
    /// # Returns
    ///
    /// `true` if the key was not present in the set and was inserted successfully.
    /// `false` if the key was already present.
    fn insert(&mut self, key: K) -> bool;

    /// Removes a key from the set.
    ///
    /// # Returns
    ///
    /// `true` if the key was present in the set and was removed.
    /// `false` if the key was not found.
    fn remove(&mut self, key: &K) -> bool;

    /// Checks if the set contains the specified key.
    ///
    /// # Returns
    ///
    /// `true` if the key is present in the set.
    /// `false` otherwise.
    fn contains(&self, key: &K) -> bool;

    /// Returns the number of elements in the set.
    fn len(&self) -> usize;

    /// Returns `true` if the set contains no elements.
    fn is_empty(&self) -> bool;

    /// Returns `true` if the set has reached its capacity.
    ///
    /// By default, sets are not bounded, so this returns `false`.
    /// Implementations that have a fixed capacity can override this method.
    fn is_full(&self) -> bool {
        false
    }
    /// Clears the set
    fn clear(&mut self);
}

#[cfg(feature = "std")]
impl<K> SetTrait<K> for std::collections::HashSet<K>
where
    K: std::cmp::Eq + std::hash::Hash,
{
    fn new() -> Self {
        Self::new()
    }

    fn insert(&mut self, key: K) -> bool {
        self.insert(key)
    }
    fn remove(&mut self, key: &K) -> bool {
        self.remove(key)
    }
    fn contains(&self, key: &K) -> bool {
        self.contains(key)
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn clear(&mut self) {
        self.clear();
    }
}

#[cfg(feature = "heapless")]
impl<K, const N: usize> SetTrait<K> for heapless::FnvIndexSet<K, N>
where
    K: core::cmp::Eq + core::hash::Hash,
{
    fn new() -> Self
    where
        Self: Sized,
    {
        Self::new()
    }

    fn insert(&mut self, key: K) -> bool {
        self.insert(key).unwrap_or(false)
    }

    fn remove(&mut self, key: &K) -> bool {
        self.remove(key)
    }

    fn contains(&self, key: &K) -> bool {
        self.contains(key)
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn clear(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "heapless")]
    use heapless::FnvIndexSet;

    use super::{staticset, SetTrait};

    #[cfg(feature = "heapless")]
    #[test]
    fn test_construct() {
        fn test<K, T: SetTrait<K>>() {
            let _ = T::new();
        }
        test::<_, FnvIndexSet<usize, 4>>();
        test::<_, staticset::Set<usize, 4>>();
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>();
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test_insert() {
        fn test<K, T: SetTrait<K>>(key: K) {
            let mut set = T::new();
            assert_eq!(set.insert(key), true);
        }
        test::<_, FnvIndexSet<usize, 4>>(2);
        test::<_, staticset::Set<usize, 4>>(2);
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>(2);
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test_remove() {
        fn test<K, T: SetTrait<K>>(key1: K, key2: K, key3: K) {
            let mut set = T::new();
            assert_eq!(set.remove(&key1), false);
            assert_eq!(set.insert(key2), true);
            assert_eq!(set.remove(&key3), true);
        }
        test::<_, FnvIndexSet<usize, 4>>(1, 2, 2);
        test::<_, staticset::Set<usize, 4>>(1, 2, 2);
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>(1, 2, 2);
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test_contains() {
        fn test<K, T: SetTrait<K>>(key1: K, key2: K, key3: K) {
            let mut set = T::new();
            assert_eq!(set.contains(&key1), false);
            assert_eq!(set.insert(key2), true);
            assert_eq!(set.contains(&key3), true);
        }
        test::<_, FnvIndexSet<usize, 4>>(1, 2, 2);
        test::<_, staticset::Set<usize, 4>>(1, 2, 2);
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>(1, 2, 2);
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test_len() {
        fn test<K, T: SetTrait<K>>(key1: K, key2: K, key3: K) {
            let mut set = T::new();
            assert_eq!(set.len(), 0);
            assert_eq!(set.insert(key1), true);
            assert_eq!(set.len(), 1);
            assert_eq!(set.insert(key2), true);
            assert_eq!(set.len(), 2);
            assert_eq!(set.remove(&key3), true);
            assert_eq!(set.len(), 1);
        }
        test::<_, FnvIndexSet<usize, 4>>(1, 2, 2);
        test::<_, staticset::Set<usize, 4>>(1, 2, 2);
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>(1, 2, 2);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_is_empty() {
        fn test<K, T: SetTrait<K>>(key1: K, key2: K, key3: K, key4: K) {
            let mut set = T::new();
            assert_eq!(set.is_empty(), true);
            assert_eq!(set.insert(key1), true);
            assert_eq!(set.is_empty(), false);
            assert_eq!(set.insert(key2), true);
            assert_eq!(set.is_empty(), false);
            assert_eq!(set.remove(&key3), true);
            assert_eq!(set.is_empty(), false);
            assert_eq!(set.remove(&key4), true);
            assert_eq!(set.is_empty(), true);
        }
        test::<_, FnvIndexSet<usize, 4>>(1, 2, 1, 2);
        test::<_, staticset::Set<usize, 4>>(1, 2, 1, 2);
        #[cfg(feature = "std")]
        test::<_, std::collections::HashSet<usize>>(1, 2, 1, 2);
    }
}
