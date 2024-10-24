// SPDX-License-Identifier: Apache-2.0

//! [Deque] that abstracts double endedd queues

mod circularqueue;

pub use circularqueue::CircularQueue;

/// Basic abstraction for double-ended queues.
pub trait Deque<T: Sized> {
    /// Provides a reference to the back element, or None if the deque is empty.
    fn back(&self) -> Option<&T>;
    /// Returns the number of elements the deque can hold.
    fn capacity(&self) -> usize;
    /// Clears the deque, removing all values.
    fn clear(&mut self);
    /// Provides a reference to the front element, or None if the deque is empty.
    fn front(&self) -> Option<&T>;
    /// Returns true if the deque is empty.
    fn is_empty(&self) -> bool;
    /// Returns true if the deque is full.
    fn is_full(&self) -> bool {
        false
    }
    /// Returns the number of elements in the deque.
    fn len(&self) -> usize;
    /// Removes the last element from the deque and returns it, or None if it is empty.
    fn pop_back(&mut self) -> Option<T>;
    /// Removes the first element and returns it, or None if the deque is empty.
    fn pop_front(&mut self) -> Option<T>;
    /// Appends an element to the back of the deque.
    fn push_back(&mut self, value: T);
    /// Prepends an element to the deque.
    fn push_front(&mut self, value: T);
}

#[cfg(feature = "std")]
impl<T> Deque<T> for std::collections::VecDeque<T> {
    fn push_front(&mut self, value: T) {
        self.push_front(value);
    }
    fn pop_front(&mut self) -> Option<T> {
        self.pop_front()
    }
    fn push_back(&mut self, value: T) {
        self.push_back(value);
    }
    fn pop_back(&mut self) -> Option<T> {
        self.pop_back()
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn clear(&mut self) {
        self.clear();
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
    fn back(&self) -> Option<&T> {
        self.back()
    }
    fn front(&self) -> Option<&T> {
        self.front()
    }
}

#[cfg(feature = "heapless")]
impl<T, const N: usize> Deque<T> for heapless::Deque<T, N> {
    fn push_front(&mut self, value: T) {
        self.push_front(value).ok();
    }
    fn pop_front(&mut self) -> Option<T> {
        self.pop_front()
    }
    fn push_back(&mut self, value: T) {
        self.push_back(value).ok();
    }
    fn pop_back(&mut self) -> Option<T> {
        self.pop_back()
    }
    fn is_empty(&self) -> bool {
        self.is_empty()
    }
    fn is_full(&self) -> bool {
        self.is_full()
    }
    fn len(&self) -> usize {
        self.len()
    }
    fn clear(&mut self) {
        self.clear();
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
    fn back(&self) -> Option<&T> {
        self.back()
    }
    fn front(&self) -> Option<&T> {
        self.front()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_queue<T: Deque<u32>>(que: &mut T) {
        assert_eq!(true, que.is_empty());
        que.push_front(1);
        que.push_front(2);
        assert_eq!(que.pop_back(), Some(1));
        assert_eq!(que.pop_back(), Some(2));
        assert_eq!(true, que.is_empty());
        que.push_front(2);
        assert_eq!(false, que.is_empty());
        que.clear();
        assert_eq!(true, que.is_empty());
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_std_queue() {
        let mut que = std::collections::VecDeque::new();
        test_queue(&mut que);
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test_heapless_queue() {
        let mut que = heapless::Deque::<_, 4>::new();
        test_queue(&mut que);
    }

    #[test]
    fn test_circular_queue() {
        let mut que = circularqueue::CircularQueue::<u32, 4>::new();
        test_queue(&mut que);
    }
}
