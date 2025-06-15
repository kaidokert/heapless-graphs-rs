// SPDX-License-Identifier: Apache-2.0

//! Provides some common graph algorithms
//!
//! Sample implementations of frequently used graph algorithms.
//!
//! Note: These are not necessarily efficient implementations,
//! nor thoroughly tested.

mod bellman_ford;
mod connected_components;
mod dijkstra;
mod greedy_coloring;
mod kahns;
mod kruskals;
mod tarjan_scc;
mod topological_sort;
mod traversal;

pub use bellman_ford::bellman_ford;
pub use connected_components::{connected_components, count_connected_components};
pub use dijkstra::dijkstra;
pub use greedy_coloring::greedy_color;
pub use kahns::kahns;
pub use kruskals::kruskals;
pub use tarjan_scc::{count_tarjan_scc, tarjan_scc};
pub use topological_sort::topological_sort_dfs;
pub use traversal::{bfs, bfs_unchecked, dfs_iterative, dfs_recursive, dfs_recursive_unchecked};

use crate::edgelist::edge_list::EdgeListError;
use crate::edges::EdgeNodeError;
use crate::graph::{GraphError, NodeIndex};

/// Errors that can occur during graph algorithm execution
///
/// This enum represents various error conditions that may arise when running
/// graph algorithms, including capacity limitations and graph-related errors.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AlgorithmError<NI: NodeIndex> {
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
    /// Invalid algorithm state (e.g., empty stack when expecting nodes)
    InvalidState,
    /// Graph operation error
    GraphError(GraphError<NI>),
    /// Edge node error
    EdgeNodeError(EdgeNodeError),
}

impl<NI: NodeIndex> From<GraphError<NI>> for AlgorithmError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        AlgorithmError::GraphError(e)
    }
}

// Helper to easily cast container capacity errors to algorithm errors
pub trait ContainerResultExt<T, NI: NodeIndex> {
    fn capacity_error(self) -> Result<T, AlgorithmError<NI>>;
}

impl<T, V, NI: NodeIndex> ContainerResultExt<T, NI> for Result<T, V> {
    fn capacity_error(self) -> Result<T, AlgorithmError<NI>> {
        self.map_err(|_| AlgorithmError::ResultCapacityExceeded)
    }
}

impl<NI: NodeIndex> From<EdgeListError<NI>> for AlgorithmError<NI> {
    fn from(e: EdgeListError<NI>) -> Self {
        match e {
            EdgeListError::GraphError(ge) => AlgorithmError::GraphError(ge),
            EdgeListError::EdgeNodeError(ene) => AlgorithmError::EdgeNodeError(ene),
        }
    }
}
