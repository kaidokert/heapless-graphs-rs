// SPDX-License-Identifier: Apache-2.0

//! Defines a visited tracker trait
//!
//! Provides an abstraction of various ways of tracking
//! visited nodes in graph traversal algorithms.

use core::slice::SliceIndex;

// TODO: These traits need to propagate errors from the underlying containers.
// .insert() can return a capacity error, which should be propagated to the caller.

use crate::containers::{maps::MapTrait, sets::SetTrait};

/// Represents the visitation state of a node during graph traversal
///
/// This enum is used by tri-state visited trackers to track whether a node
/// has been unvisited, is currently being visited, or has been fully visited.
/// This is particularly useful for cycle detection algorithms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    /// Node not visited, default
    Unvisited,
    /// Node is in the visiting path
    Visiting,
    /// Node has been visited
    Visited,
}

/// Trait for tracking visited nodes during graph traversal
///
/// This trait provides a common interface for different strategies of tracking
/// which nodes have been visited during graph algorithms like DFS or BFS.
///
/// Implementations include:
/// - Simple array of booleans for compact graphs with small node indices
/// - Set-based tracking for sparse graphs with arbitrary node types
pub trait VisitedTracker<NI> {
    /// Reset tracker state
    fn reset(&mut self);
    /// Mark node as visited.
    fn mark_visited(&mut self, node: &NI) -> Result<(), NI>;
    /// Return true if node is visited.
    fn is_visited(&self, node: &NI) -> bool;
    /// Return true if node is unvisited.
    fn is_unvisited(&self, node: &NI) -> bool;
}

/// Extension of [`VisitedTracker`] that supports three states: unvisited, visiting, and visited
///
/// This trait is particularly useful for algorithms that need to detect cycles,
/// such as topological sorting or strongly connected component detection.
/// The "visiting" state indicates a node is currently on the traversal stack.
pub trait TriStateVisitedTracker<NI>: VisitedTracker<NI> {
    // Mark node as visiting
    fn mark_visiting(&mut self, node: &NI) -> Result<(), NI>;
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
    fn mark_visited(&mut self, node: &NI) -> Result<(), NI> {
        self[*node] = true;
        Ok(())
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
    fn mark_visited(&mut self, node: &NI) -> Result<(), NI> {
        self[*node] = NodeState::Visited;
        Ok(())
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
    fn mark_visiting(&mut self, node: &NI) -> Result<(), NI> {
        self[*node] = NodeState::Visiting;
        Ok(())
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
    fn mark_visited(&mut self, node: &K) -> Result<(), K> {
        self.0.insert(*node).map_or_else(|_| Err(*node), |_| Ok(()))
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
    fn mark_visited(&mut self, node: &K) -> Result<(), K> {
        if let Some(k) = self.0.get_mut(node) {
            *k = NodeState::Visited;
            Ok(())
        } else {
            self.0
                .insert(*node, NodeState::Visited)
                .map_or_else(|_| Err(*node), |_| Ok(()))
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
    fn mark_visiting(&mut self, node: &K) -> Result<(), K> {
        if let Some(k) = self.0.get_mut(node) {
            *k = NodeState::Visiting;
            Ok(())
        } else {
            self.0
                .insert(*node, NodeState::Visiting)
                .map_or_else(|_| Err(*node), |_| Ok(()))
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

    fn test_visited<NI: core::fmt::Debug, T: VisitedTracker<NI> + ?Sized>(track: &mut T, n: NI) {
        assert_eq!(track.is_visited(&n), false);
        assert_eq!(track.is_unvisited(&n), true);
        track.mark_visited(&n).unwrap();
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
