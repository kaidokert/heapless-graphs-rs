// SPDX-License-Identifier: Apache-2.0

use super::Deque;

/// A minimal circular queue with a fixed capacity.
///
/// Uses `Option<T>` internally to avoid requiring `Default` on the stored type.
/// The queue maintains head and tail pointers and tracks the current size.
pub struct CircularQueue<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize,
    tail: usize,
    size: usize,
}

impl<T, const N: usize> Default for CircularQueue<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> CircularQueue<T, N> {
    pub fn new() -> Self {
        Self {
            buffer: core::array::from_fn(|_| None),
            head: 0,
            tail: 0,
            size: 0,
        }
    }
}

impl<T, const N: usize> Deque<T> for CircularQueue<T, N> {
    fn push_front(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            Err(value)
        } else {
            self.head = (self.head + N - 1) % N;
            self.buffer[self.head] = Some(value);
            self.size += 1;
            Ok(())
        }
    }
    fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let value = self.buffer[self.head].take();
        self.head = (self.head + 1) % N;
        self.size -= 1;
        value
    }
    fn push_back(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            Err(value)
        } else {
            self.buffer[self.tail] = Some(value);
            self.tail = (self.tail + 1) % N;
            self.size += 1;
            Ok(())
        }
    }
    fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        self.tail = (self.tail + N - 1) % N;
        let value = self.buffer[self.tail].take();
        self.size -= 1;
        value
    }

    fn is_empty(&self) -> bool {
        self.size == 0
    }

    fn len(&self) -> usize {
        self.size
    }

    fn clear(&mut self) {
        self.head = 0;
        self.tail = 0;
        self.size = 0;
    }

    fn capacity(&self) -> usize {
        N
    }

    fn back(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        let index = (self.tail + N - 1) % N;
        self.buffer[index].as_ref()
    }

    fn front(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        self.buffer[self.head].as_ref()
    }
    fn is_full(&self) -> bool {
        self.size >= N
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_queue_is_empty() {
        let queue: CircularQueue<i32, 5> = CircularQueue::new();
        assert!(queue.is_empty());
        assert!(!queue.is_full());
        assert_eq!(queue.len(), 0);
        assert_eq!(queue.capacity(), 5);
        assert_eq!(queue.front(), None);
        assert_eq!(queue.back(), None);
    }

    #[test]
    fn test_push_back_and_pop_front() {
        let mut queue: CircularQueue<i32, 3> = CircularQueue::new();

        // Test push_back
        assert_eq!(queue.push_back(1), Ok(()));
        assert_eq!(queue.len(), 1);
        assert!(!queue.is_empty());
        assert_eq!(queue.front(), Some(&1));
        assert_eq!(queue.back(), Some(&1));

        assert_eq!(queue.push_back(2), Ok(()));
        assert_eq!(queue.len(), 2);
        assert_eq!(queue.front(), Some(&1));
        assert_eq!(queue.back(), Some(&2));

        assert_eq!(queue.push_back(3), Ok(()));
        assert_eq!(queue.len(), 3);
        assert!(queue.is_full());
        assert_eq!(queue.front(), Some(&1));
        assert_eq!(queue.back(), Some(&3));

        // Test overflow
        assert_eq!(queue.push_back(4), Err(4));
        assert_eq!(queue.len(), 3);

        // Test pop_front
        assert_eq!(queue.pop_front(), Some(1));
        assert_eq!(queue.len(), 2);
        assert!(!queue.is_full());
        assert_eq!(queue.front(), Some(&2));
        assert_eq!(queue.back(), Some(&3));

        assert_eq!(queue.pop_front(), Some(2));
        assert_eq!(queue.len(), 1);
        assert_eq!(queue.front(), Some(&3));
        assert_eq!(queue.back(), Some(&3));

        assert_eq!(queue.pop_front(), Some(3));
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
        assert_eq!(queue.front(), None);
        assert_eq!(queue.back(), None);

        // Test underflow
        assert_eq!(queue.pop_front(), None);
    }

    #[test]
    fn test_push_front_and_pop_back() {
        let mut queue: CircularQueue<i32, 3> = CircularQueue::new();

        // Test push_front
        assert_eq!(queue.push_front(1), Ok(()));
        assert_eq!(queue.len(), 1);
        assert_eq!(queue.front(), Some(&1));
        assert_eq!(queue.back(), Some(&1));

        assert_eq!(queue.push_front(2), Ok(()));
        assert_eq!(queue.len(), 2);
        assert_eq!(queue.front(), Some(&2));
        assert_eq!(queue.back(), Some(&1));

        assert_eq!(queue.push_front(3), Ok(()));
        assert_eq!(queue.len(), 3);
        assert!(queue.is_full());
        assert_eq!(queue.front(), Some(&3));
        assert_eq!(queue.back(), Some(&1));

        // Test overflow
        assert_eq!(queue.push_front(4), Err(4));

        // Test pop_back
        assert_eq!(queue.pop_back(), Some(1));
        assert_eq!(queue.len(), 2);
        assert_eq!(queue.front(), Some(&3));
        assert_eq!(queue.back(), Some(&2));

        assert_eq!(queue.pop_back(), Some(2));
        assert_eq!(queue.len(), 1);
        assert_eq!(queue.front(), Some(&3));
        assert_eq!(queue.back(), Some(&3));

        assert_eq!(queue.pop_back(), Some(3));
        assert!(queue.is_empty());
    }

    #[test]
    fn test_mixed_operations() {
        let mut queue: CircularQueue<i32, 4> = CircularQueue::new();

        // Mix push_back and push_front
        assert_eq!(queue.push_back(1), Ok(()));
        assert_eq!(queue.push_front(2), Ok(()));
        assert_eq!(queue.push_back(3), Ok(()));
        assert_eq!(queue.push_front(4), Ok(()));

        assert!(queue.is_full());
        assert_eq!(queue.len(), 4);

        // Queue should now be: [4, 2, 1, 3] (front to back)
        assert_eq!(queue.front(), Some(&4));
        assert_eq!(queue.back(), Some(&3));

        // Mix pop operations
        assert_eq!(queue.pop_front(), Some(4)); // [2, 1, 3]
        assert_eq!(queue.pop_back(), Some(3)); // [2, 1]
        assert_eq!(queue.pop_front(), Some(2)); // [1]
        assert_eq!(queue.pop_back(), Some(1)); // []

        assert!(queue.is_empty());
    }

    #[test]
    fn test_wraparound() {
        let mut queue: CircularQueue<i32, 3> = CircularQueue::new();

        // Fill the queue
        queue.push_back(1).unwrap();
        queue.push_back(2).unwrap();
        queue.push_back(3).unwrap();

        // Pop and push to cause wraparound
        assert_eq!(queue.pop_front(), Some(1));
        assert_eq!(queue.push_back(4), Ok(()));

        assert_eq!(queue.pop_front(), Some(2));
        assert_eq!(queue.push_back(5), Ok(()));

        // Queue should now be [3, 4, 5]
        assert_eq!(queue.front(), Some(&3));
        assert_eq!(queue.back(), Some(&5));
        assert_eq!(queue.len(), 3);

        // Verify all elements
        assert_eq!(queue.pop_front(), Some(3));
        assert_eq!(queue.pop_front(), Some(4));
        assert_eq!(queue.pop_front(), Some(5));
        assert!(queue.is_empty());
    }

    #[test]
    fn test_clear() {
        let mut queue: CircularQueue<i32, 3> = CircularQueue::new();

        queue.push_back(1).unwrap();
        queue.push_back(2).unwrap();
        queue.push_back(3).unwrap();

        assert_eq!(queue.len(), 3);
        assert!(!queue.is_empty());

        queue.clear();

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
        assert!(!queue.is_full());
        assert_eq!(queue.front(), None);
        assert_eq!(queue.back(), None);

        // Should be able to use normally after clear
        assert_eq!(queue.push_back(10), Ok(()));
        assert_eq!(queue.front(), Some(&10));
    }

    #[test]
    fn test_default() {
        let queue: CircularQueue<i32, 5> = CircularQueue::default();
        assert!(queue.is_empty());
        assert_eq!(queue.capacity(), 5);
    }

    #[test]
    fn test_single_element_queue() {
        let mut queue: CircularQueue<i32, 1> = CircularQueue::new();

        assert_eq!(queue.push_back(42), Ok(()));
        assert!(queue.is_full());
        assert_eq!(queue.front(), Some(&42));
        assert_eq!(queue.back(), Some(&42));

        // Should not be able to add another
        assert_eq!(queue.push_back(43), Err(43));
        assert_eq!(queue.push_front(44), Err(44));

        assert_eq!(queue.pop_front(), Some(42));
        assert!(queue.is_empty());
    }

    #[test]
    fn test_zero_capacity_queue() {
        let mut queue: CircularQueue<i32, 0> = CircularQueue::new();

        assert!(queue.is_empty());
        assert!(queue.is_full()); // Zero capacity means always full
        assert_eq!(queue.capacity(), 0);

        // Should not be able to add anything
        assert_eq!(queue.push_back(1), Err(1));
        assert_eq!(queue.push_front(2), Err(2));

        // Should not be able to pop anything
        assert_eq!(queue.pop_front(), None);
        assert_eq!(queue.pop_back(), None);
    }

    #[test]
    fn test_non_copy_type() {
        // Test that the queue works with non-Copy types (like String)
        let mut queue: CircularQueue<String, 3> = CircularQueue::new();

        let s1 = String::from("hello");
        let s2 = String::from("world");

        assert_eq!(queue.push_back(s1), Ok(()));
        assert_eq!(queue.push_back(s2), Ok(()));

        assert_eq!(queue.front(), Some(&String::from("hello")));
        assert_eq!(queue.back(), Some(&String::from("world")));

        assert_eq!(queue.pop_front(), Some(String::from("hello")));
        assert_eq!(queue.pop_front(), Some(String::from("world")));
        assert!(queue.is_empty());
    }

    #[test]
    fn test_non_default_type() {
        // Test with a type that doesn't implement Default
        #[derive(Debug, PartialEq)]
        struct NoDefault(i32);

        let mut queue: CircularQueue<NoDefault, 2> = CircularQueue::new();

        assert_eq!(queue.push_back(NoDefault(1)), Ok(()));
        assert_eq!(queue.push_back(NoDefault(2)), Ok(()));

        assert_eq!(queue.front(), Some(&NoDefault(1)));
        assert_eq!(queue.back(), Some(&NoDefault(2)));

        assert_eq!(queue.pop_front(), Some(NoDefault(1)));
        assert_eq!(queue.pop_back(), Some(NoDefault(2)));
        assert!(queue.is_empty());
    }

    #[test]
    fn test_queue_with_references() {
        let mut queue: CircularQueue<&str, 3> = CircularQueue::new();

        let s1 = String::from("hello");
        let s2 = String::from("world");

        assert_eq!(queue.push_back(&s1), Ok(()));
        assert_eq!(queue.push_back(&s2), Ok(()));
    }
}
