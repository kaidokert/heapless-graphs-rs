// SPDX-License-Identifier: Apache-2.0

//! Graph conversion traits and utilities
//!
//! This module provides traits and functions for converting between different graph representations.

use crate::graph::{Graph, NodeIndex};

/// Trait for graph types that can be constructed from other graph types
///
/// This trait provides a standardized way to convert from any source graph
/// to the implementing graph type. It handles the common pattern of copying
/// nodes and edges from a source graph while managing capacity constraints
/// and error handling.
///
/// # Type Parameters
/// * `NI` - The node index type for the target graph
/// * `E` - The error type returned by the conversion
///
/// # Implementation Guidelines
///
/// Implementations should:
/// 1. Iterate over all nodes in the source graph and copy them
/// 2. Iterate over all edges in the source graph and copy them
/// 3. Handle capacity constraints appropriately for the target graph type
/// 4. Convert source graph errors to the target error type
/// 5. Support empty graphs (graphs with no nodes/edges)
///
/// # Examples
///
/// ```
/// use heapless_graphs::conversions::FromGraph;
/// use heapless_graphs::matrix::simple_matrix::Matrix;
/// use heapless_graphs::adjacency_list::map_adjacency_list::MapAdjacencyList;
/// // ... (setup source graph)
/// // let target_matrix = Matrix::from_graph2(&source_graph)?;
/// ```
pub trait FromGraph<NI, E>
where
    NI: NodeIndex,
{
    /// Creates a new graph by copying data from the source graph
    ///
    /// This function converts any graph that implements the `Graph` trait
    /// into the target graph type. The conversion process typically involves:
    ///
    /// 1. **Node collection**: Gathering all nodes from the source graph
    /// 2. **Edge collection**: Gathering all edges from the source graph
    /// 3. **Capacity validation**: Ensuring the target graph can hold all data
    /// 4. **Data population**: Creating the target graph with the copied data
    ///
    /// # Arguments
    /// * `source_graph` - The graph to convert from
    ///
    /// # Returns
    /// * `Ok(Self)` - Successfully created target graph
    /// * `Err(E)` - Conversion failed (capacity, invalid data, etc.)
    ///
    /// # Errors
    ///
    /// Common error conditions include:
    /// * **Capacity exceeded**: Target graph cannot hold all nodes/edges
    /// * **Invalid node indices**: Source nodes outside target's valid range
    /// * **Source iteration failure**: Problems reading from source graph
    /// * **Memory allocation**: Target graph construction failed
    fn from_graph<G>(source_graph: &G) -> Result<Self, E>
    where
        G: Graph<NI>,
        E: From<G::Error>,
        Self: Sized;
}
