// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`Graph`] trait and related error values
//! and sub-traits.

/// Trait for types that can be used as node indices in graphs
///
/// Node indices must support equality, ordering comparisons, and copying.
/// This is typically implemented for numeric types like `usize`, `u32`, etc.
///
/// The trait is automatically implemented for any type that satisfies the bounds,
/// making it easy to use custom index types while ensuring they have the required
/// operations for graph algorithms.
pub trait NodeIndex: PartialEq + PartialOrd + Copy {}
impl<T> NodeIndex for T where T: PartialEq + PartialOrd + Copy {}

/// Errors that can occur during graph operations
///
/// This enum represents various error conditions that may arise when working
/// with graph structures, such as accessing non-existent nodes or edges.
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum GraphError<NI: NodeIndex> {
    /// Edge is referring to a node not present in graph
    EdgeHasInvalidNode(NI),
    /// Given node wasn't found in the graph
    NodeNotFound(NI),
    /// Index is out of bounds
    IndexOutOfBounds(usize, NI),
    /// Unexpected condition occurred
    Unexpected,
}

/// Core graph trait for immutable graph access
///
/// This trait provides read-only access to graph structure through owned values.
/// It forms the foundation for all graph representations in this library, with
/// concrete implementations like [`EdgeNodeList`](crate::edgelist::edge_node_list::EdgeNodeList)
/// and adjacency list representations.
///
/// All methods return owned values rather than references for better ergonomics,
/// though this may require cloning for some implementations.
pub trait Graph<NI: NodeIndex> {
    type Error: From<GraphError<NI>>;

    /// Return an iterator over all nodes in the graph
    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error>;
    /// Return an iterator over all edges in the graph
    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error>;

    /// Return an iterator over all outgoing edges for a node
    ///
    /// Default implementation filters all edges, which is inefficient.
    /// Implementers should override this method when they can provide
    /// direct access to outgoing edges (e.g., adjacency lists, matrices).
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self
            .iter_edges()?
            .filter(move |(src, _dst)| *src == node)
            .map(|(_src, dst)| dst))
    }

    /// Return an iterator over all incoming edges for a node
    ///
    /// Default implementation filters all edges, which is inefficient.
    /// Implementers should override this method when they can provide
    /// direct access to incoming edges (e.g., adjacency matrices).
    fn incoming_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self
            .iter_edges()?
            .filter(move |(_src, dst)| *dst == node)
            .map(|(src, _dst)| src))
    }

    /// Check if a node is present in the graph
    ///
    /// **Performance Warning**: Default implementation iterates all nodes, which is O(n).
    /// Implementers should override this method when they can provide
    /// faster lookup (e.g., hash-based storage for O(1) or tree-based storage for O(log n)).
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.iter_nodes()?.any(|x| x == node))
    }
}

/// Extension of [`Graph`] that provides access to node values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `NV` with each node in the graph. Node values are optional,
/// allowing for sparse assignment of data to nodes.
///
/// Useful for algorithms that need to store additional data with nodes,
/// such as distances in shortest path algorithms, colors in graph coloring,
/// or any domain-specific node attributes.
pub trait GraphWithNodeValues<NI, NV>: Graph<NI>
where
    NI: NodeIndex,
{
    /// Get the value associated with a node
    fn node_value(&self, node: NI) -> Result<Option<&NV>, Self::Error>;
    /// Return an iterator over all node values in the graph
    fn iter_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a NV>)>, Self::Error>
    where
        NV: 'a;
}

/// Extension of [`Graph`] that provides access to edge values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `EV` with each edge in the graph. Edge values are optional,
/// allowing for sparse assignment of data to edges.
///
/// Commonly used for weighted graphs where edges have costs, capacities,
/// distances, or other numeric values. Also useful for storing metadata
/// about relationships between nodes.
pub trait GraphWithEdgeValues<NI, EV>: Graph<NI>
where
    NI: NodeIndex,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a;

    /// Return outgoing edges with values for a specific node
    ///
    /// **Performance Warning**: Default implementation filters all edges, which is O(E).
    /// Implementers should override this method when they can provide
    /// direct access to outgoing edges (e.g., adjacency lists).
    fn outgoing_edge_values<'a>(
        &'a self,
        node: NI,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a,
    {
        Ok(self
            .iter_edge_values()?
            .filter(move |(src, _dst, _weight)| *src == node)
            .map(|(_src, dst, weight)| (dst, weight)))
    }

    /// Return incoming edges with values for a specific node
    ///
    /// **Performance Warning**: Default implementation filters all edges, which is O(E).
    /// Implementers should override this method when they can provide
    /// direct access to incoming edges (e.g., adjacency matrices).
    fn incoming_edge_values<'a>(
        &'a self,
        node: NI,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a,
    {
        Ok(self
            .iter_edge_values()?
            .filter(move |(_src, dst, _weight)| *dst == node)
            .map(|(src, _dst, weight)| (src, weight)))
    }
}

/// Integrity check for graphs - validates that all edges reference valid nodes
///
/// This function checks that every edge in the graph references nodes that actually
/// exist in the graph's node set. This is used during graph construction to ensure
/// data integrity and prevent invalid graph states.
pub(crate) fn integrity_check<NI, G>(graph: &G) -> Result<(), G::Error>
where
    NI: NodeIndex,
    G: Graph<NI>,
{
    for (src, dst) in graph.iter_edges()? {
        if !graph.contains_node(src)? {
            return Err(GraphError::EdgeHasInvalidNode(src).into());
        }
        if !graph.contains_node(dst)? {
            return Err(GraphError::EdgeHasInvalidNode(dst).into());
        }
    }

    // TODO: Perhaps check for duplicate nodes
    Ok(())
}
