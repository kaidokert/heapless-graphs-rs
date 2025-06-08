// SPDX-License-Identifier: Apache-2.0

//! Provides some common graph algorithms
//!
//! Sample implementations of frequently used graph algorithms.
//!
//! Note: These are not necessarily efficient implementations,
//! nor thoroughly tested.

pub mod bellman_ford;
pub mod dijkstra;
pub mod greedy_coloring;
pub mod kahns;
pub mod kruskals;
pub mod topological_sort;
pub mod traversal;

use crate::edgelist::edge_list::EdgeListError;
use crate::graph::{GraphError, NodeIndexTrait};

/// Errors that can occur during graph algorithm execution
///
/// This enum represents various error conditions that may arise when running
/// graph algorithms, including capacity limitations and graph-related errors.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AlgorithmError<NI: NodeIndexTrait> {
    /// Queue capacity exceeded during breadth-first operations
    QueueCapacityExceeded,
    /// Stack capacity exceeded during depth-first operations
    StackCapacityExceeded,
    /// Buffer for edges too small
    EdgeCapacityExceeded,
    /// Cycle detected in algorithm that requires acyclic graph
    CycleDetected,
    /// Output buffer too small
    ResultCapacityExceeded,
    /// Graph operation error
    GraphError(GraphError<NI>),
}

impl<NI: NodeIndexTrait> From<GraphError<NI>> for AlgorithmError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        AlgorithmError::GraphError(e)
    }
}

impl<NI: NodeIndexTrait> From<EdgeListError<NI>> for AlgorithmError<NI> {
    fn from(e: EdgeListError<NI>) -> Self {
        match e {
            EdgeListError::GraphError(ge) => AlgorithmError::GraphError(ge),
            EdgeListError::EdgeNodeError(_) => AlgorithmError::GraphError(GraphError::NodeNotFound),
        }
    }
}
