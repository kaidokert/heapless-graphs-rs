// SPDX-License-Identifier: Apache-2.0

//! Provides some common graph algorithms
//!
//! Sample implementations of frequently used graph algorithms.
//!
//! Note: These are not necessarily efficient implementations,
//! nor thoroughly tested.

#[cfg(feature = "num-traits")]
mod bellman_ford;
#[cfg(feature = "num-traits")]
mod dijkstra;
mod kruskals;
mod topological_sort;
mod traversal;

#[cfg(feature = "num-traits")]
pub use bellman_ford::bellman_ford;
#[cfg(feature = "num-traits")]
pub use dijkstra::dijkstra;
pub use kruskals::kruskals;
pub use topological_sort::topological_sort;
pub use traversal::{bfs, bfs_unchecked, dfs_iterative, dfs_recursive, dfs_recursive_unchecked};

use crate::graph::GraphError;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum AlgorithmError<NI: PartialEq> {
    /// Edge list iteration issue, capacity etc.
    GraphError(GraphError<NI>),
    /// Unexpected error in accessing dictionary items
    DictionaryError,
    /// Buffer for edges too small
    EdgeCapacityExceeded { max_edges: usize },
    /// Output buffer too small
    OutputCapacityExceeded,
    /// Indicates a cycle was detected at a specific node,
    /// along with the two edges that formed the cycle.
    CycleDetected {
        incoming_edge: NI,
        outgoing_edge: NI,
    },
    /// A negative cycle was detected in the graph
    NegativeCycle {
        incoming_edge: NI,
        outgoing_edge: NI,
    },
    /// Edge weight is missing, cannot continue
    MissingEdgeWeight {
        incoming_edge: NI,
        outgoing_edge: NI,
    },
}
impl<NI: PartialEq> From<GraphError<NI>> for AlgorithmError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        AlgorithmError::GraphError(e)
    }
}

// Helper to easily cast unlikely missing dict values to errors
trait OptionResultExt<T, NI: PartialEq> {
    fn dict_error(self) -> Result<T, AlgorithmError<NI>>;
}

impl<T, NI: PartialEq> OptionResultExt<T, NI> for Option<T> {
    fn dict_error(self) -> Result<T, AlgorithmError<NI>> {
        self.ok_or(AlgorithmError::DictionaryError)
    }
}
