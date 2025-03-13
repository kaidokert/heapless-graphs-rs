// SPDX-License-Identifier: Apache-2.0

use super::Deque;

/// A minimal circular queue with a fixed capacity.
pub struct CircularQueue<T, const N: usize> {
    buffer: [T; N],
    head: usize,
    tail: usize,
    size: usize,
}

impl<T: Default + Copy, const N: usize> Default for CircularQueue<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Default + Copy, const N: usize> CircularQueue<T, N> {
    pub fn new() -> Self {
        Self {
            buffer: [T::default(); N],
            head: 0,
            tail: 0,
            size: 0,
        }
    }
}

impl<T: Default + Copy, const N: usize> Deque<T> for CircularQueue<T, N> {
    fn push_front(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            Err(value)
        } else {
            self.head = (self.head + N - 1) % N;
            self.buffer[self.head] = value;
            self.size += 1;
            Ok(())
        }
    }
    fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let value = self.buffer[self.head];
        self.head = (self.head + 1) % N;
        self.size -= 1;
        Some(value)
    }
    fn push_back(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            Err(value)
        } else {
            self.buffer[self.tail] = value;
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
        let value = self.buffer[self.tail];
        self.size -= 1;
        Some(value)
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
        Some(&self.buffer[index])
    }

    fn front(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        Some(&self.buffer[self.head])
    }
    fn is_full(&self) -> bool {
        self.size >= N
    }
}
