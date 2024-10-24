// SPDX-License-Identifier: Apache-2.0

//! Defines a visited tracker trait
//!
//! Provides an abstraction of various ways of tracking
//! visited nodes in graph traversal algorithms.

use core::slice::SliceIndex;

use crate::containers::{maps::MapTrait, sets::SetTrait};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    /// Node not visited, default
    Unvisited,
    /// Node is in the visiting path
    Visiting,
    /// Node has been visited
    Visited,
}

/// Abstraction for visiting nodes in a graph
///
/// Implementations: a simple array of booleans for very small
/// graphs where node indices are within array
/// bounds, or more typically a set
pub trait VisitedTracker<NI> {
    /// Reset tracker state
    fn reset(&mut self);
    /// Mark node as visited.
    fn mark_visited(&mut self, node: &NI);
    /// Return true if node is visited.
    fn is_visited(&self, node: &NI) -> bool;
    /// Return true if node is unvisited.
    fn is_unvisited(&self, node: &NI) -> bool;
}

/// Visited tracker with 3-rd state: visiting
///
/// This is similar to VisitedTracker, but also allows
/// tracking whether node is currently on visiting stack
pub trait TriStateVisitedTracker<NI>: VisitedTracker<NI> {
    // Mark node as visiting
    fn mark_visiting(&mut self, node: &NI);
    /// Return true if node is visiting.
    fn is_visiting(&self, node: &NI) -> bool;
}

/// VisitedTracker implementation for a slice of booleans
///
/// Only suitable for very compact graphs with small node indices.
impl<NI> VisitedTracker<NI> for [bool]
where
    NI: SliceIndex<[bool], Output = bool> + Copy,
{
    fn reset(&mut self) {
        self.fill(false);
    }
    fn mark_visited(&mut self, node: &NI) {
        self[*node] = true;
    }

    fn is_visited(&self, node: &NI) -> bool {
        self[*node]
    }

    fn is_unvisited(&self, node: &NI) -> bool {
        !self[*node]
    }
}

/// VisitedTracker implementation for a slice of NodeStates
///
/// Only suitable for very compact graphs with small node indices.
impl<NI> VisitedTracker<NI> for [NodeState]
where
    NI: SliceIndex<[NodeState], Output = NodeState> + Copy,
{
    fn reset(&mut self) {
        self.fill(NodeState::Unvisited)
    }
    fn mark_visited(&mut self, node: &NI) {
        self[*node] = NodeState::Visited;
    }

    fn is_visited(&self, node: &NI) -> bool {
        self[*node] == NodeState::Visited
    }

    fn is_unvisited(&self, node: &NI) -> bool {
        self[*node] == NodeState::Unvisited
    }
}
impl<NI> TriStateVisitedTracker<NI> for [NodeState]
where
    NI: SliceIndex<[NodeState], Output = NodeState> + Copy,
{
    fn mark_visiting(&mut self, node: &NI) {
        self[*node] = NodeState::Visiting;
    }

    fn is_visiting(&self, node: &NI) -> bool {
        self[*node] == NodeState::Visiting
    }
}

pub struct SetWrapper<T>(pub T);
pub struct MapWrapper<T>(pub T);

impl<K, T> VisitedTracker<K> for SetWrapper<T>
where
    T: SetTrait<K>,
    K: Eq + core::hash::Hash + Copy,
    NodeState: Clone,
{
    fn reset(&mut self) {}
    fn mark_visited(&mut self, node: &K) {
        self.0.insert(*node);
    }

    fn is_visited(&self, node: &K) -> bool {
        self.0.contains(node)
    }

    fn is_unvisited(&self, node: &K) -> bool {
        !self.is_visited(node)
    }
}

// Blanket implementation of VisitedTracker for any MapTrait<K, NodeState>
impl<K, T> VisitedTracker<K> for MapWrapper<T>
where
    T: MapTrait<K, NodeState>,
    K: Eq + core::hash::Hash + Copy,
    NodeState: Clone,
{
    fn reset(&mut self) {}
    fn mark_visited(&mut self, node: &K) {
        if let Some(k) = self.0.get_mut(node) {
            *k = NodeState::Visited;
        } else {
            self.0.insert(*node, NodeState::Visited);
        }
    }

    fn is_visited(&self, node: &K) -> bool {
        self.0.get(node).unwrap_or(&NodeState::Unvisited) == &NodeState::Visited
    }

    fn is_unvisited(&self, node: &K) -> bool {
        self.0.get(node).unwrap_or(&NodeState::Unvisited) == &NodeState::Unvisited
    }
}

impl<K, T> TriStateVisitedTracker<K> for MapWrapper<T>
where
    T: MapTrait<K, NodeState>,
    K: Eq + core::hash::Hash + Copy,
    NodeState: Clone,
{
    fn mark_visiting(&mut self, node: &K) {
        if let Some(k) = self.0.get_mut(node) {
            *k = NodeState::Visiting;
        } else {
            self.0.insert(*node, NodeState::Visiting);
        }
    }

    fn is_visiting(&self, node: &K) -> bool {
        self.0.get(node).unwrap_or(&NodeState::Unvisited) == &NodeState::Visiting
    }
}

#[cfg(test)]

mod test {
    use crate::containers::{
        maps::staticdict::Dictionary,
        sets::{staticset::Set, SetTrait},
    };

    use super::*;

    fn test_visited<NI, T: VisitedTracker<NI> + ?Sized>(track: &mut T, n: NI) {
        assert_eq!(track.is_visited(&n), false);
        assert_eq!(track.is_unvisited(&n), true);
        track.mark_visited(&n);
    }
    #[test]
    fn test_bool_array() {
        let mut visited = [false; 8];
        test_visited(visited.as_mut_slice(), 2_usize);
    }
    #[test]
    fn test_state_array() {
        let mut visited = [NodeState::Unvisited; 8];
        test_visited(visited.as_mut_slice(), 2_usize);
    }
    #[test]
    fn test_set() {
        let mut visited = SetWrapper(Set::<usize, 13>::new());
        test_visited(&mut visited, 2_usize);
    }
    #[test]
    fn test_dict() {
        let mut visited = MapWrapper(Dictionary::<usize, NodeState, 37>::new());
        test_visited(&mut visited, 2_usize);
    }
}
