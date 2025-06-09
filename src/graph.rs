// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`GraphRef`] and [`GraphVal`] traits and related error values
//! and sub-traits.

/// Trait for types that can be used as node indices in graphs
///
/// Node indices must support equality and ordering comparisons.
/// This is typically implemented for numeric types like `usize`, `u32`, etc.
pub trait NodeIndexTrait: PartialEq + PartialOrd {}
impl<T> NodeIndexTrait for T where T: PartialEq + PartialOrd {}

/// Errors that can occur during graph operations
///
/// This enum represents various error conditions that may arise when working
/// with graph structures, such as accessing non-existent nodes or edges.
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum GraphError<NI: NodeIndexTrait> {
    NodeNotFound(NI),
    EdgeHasInvalidNode,
}

/// Reference-based graph trait for immutable graph access
///
/// This trait provides read-only access to graph structure through borrowed references.
/// It's designed for cases where you need to examine graph structure without taking
/// ownership of the data.
///
/// The underlying storage is defined by concrete implementations like
/// [`EdgeList`](crate::edgelist::edge_list::EdgeList) or
/// [`MapAdjacencyList`](crate::adjacency_list::map_adjacency_list::MapAdjacencyList).
pub trait GraphRef<NodeIndex: NodeIndexTrait> {
    type Error: From<GraphError<NodeIndex>>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NodeIndex>, Self::Error>
    where
        NodeIndex: 'a;
    fn iter_edges<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (&'a NodeIndex, &'a NodeIndex)>, Self::Error>
    where
        NodeIndex: 'a;

    fn outgoing_edges<'a>(
        &'a self,
        node: &'a NodeIndex,
    ) -> Result<impl Iterator<Item = &'a NodeIndex>, Self::Error>
    where
        NodeIndex: 'a,
    {
        Ok(self
            .iter_edges()?
            .filter(move |(src, _dst)| *src == node)
            .map(|(_src, dst)| dst))
    }

    /// Check if a node is present in the graph
    fn contains_node(&self, node: &NodeIndex) -> Result<bool, Self::Error> {
        Ok(self.iter_nodes()?.any(|x| x == node))
    }
}

/// Value-based graph trait for immutable graph access
///
/// This trait provides read-only access to graph structure through owned values.
/// It's designed for cases where you can efficiently copy node indices and prefer
/// to work with owned data rather than borrowed references.
///
/// Requires `NodeIndex: Copy` since iterators return owned values rather than references.
pub trait GraphVal<NodeIndex: NodeIndexTrait + Copy> {
    type Error: From<GraphError<NodeIndex>>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NodeIndex>, Self::Error>;
    fn iter_edges(&self) -> Result<impl Iterator<Item = (NodeIndex, NodeIndex)>, Self::Error>;

    /// Get outgoing edges from a node
    fn outgoing_edges(
        &self,
        node: NodeIndex,
    ) -> Result<impl Iterator<Item = NodeIndex>, Self::Error> {
        Ok(self
            .iter_edges()?
            .filter(move |(src, _dst)| *src == node)
            .map(|(_src, dst)| dst))
    }

    /// Check if a node is present in the graph
    fn contains_node(&self, node: NodeIndex) -> Result<bool, Self::Error> {
        Ok(self.iter_nodes()?.any(|x| x == node))
    }
}

/// Extension of [`GraphRef`] that provides access to node values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `NV` with each node in the graph. Node values are optional,
/// allowing for sparse assignment of data to nodes.
pub trait GraphRefWithNodeValues<NI, NV>: GraphRef<NI>
where
    NI: NodeIndexTrait,
{
    fn iter_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a NV>)>, Self::Error>
    where
        NV: 'a,
        NI: 'a;
    fn node_value(&self, node: &NI) -> Result<Option<&NV>, Self::Error>;
}

/// Extension of [`GraphVal`] that provides access to node values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `NV` with each node in the graph. Node values are optional,
/// allowing for sparse assignment of data to nodes.
pub trait GraphValWithNodeValues<NI, NV>: GraphVal<NI>
where
    NI: NodeIndexTrait + Copy,
{
    fn node_value(&self, node: NI) -> Result<Option<&NV>, Self::Error>;
    fn iter_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a NV>)>, Self::Error>
    where
        NV: 'a;
}

/// Extension of [`GraphRef`] that provides access to edge values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `EV` with each edge in the graph. Edge values are optional,
/// allowing for sparse assignment of data to edges.
pub trait GraphRefWithEdgeValues<NI, EV>: GraphRef<NI>
where
    NI: NodeIndexTrait,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (&'a NI, &'a NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a,
        NI: 'a;
}
/// Extension of [`GraphVal`] that provides access to edge values
///
/// This trait extends basic graph functionality with the ability to associate
/// values of type `EV` with each edge in the graph. Edge values are optional,
/// allowing for sparse assignment of data to edges.
pub trait GraphValWithEdgeValues<NI, EV>: GraphVal<NI>
where
    NI: NodeIndexTrait + Copy,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a;

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
}

/// Integrity check for graphs - validates that all edges reference valid nodes
///
/// This function checks that every edge in the graph references nodes that actually
/// exist in the graph's node set. This is used during graph construction to ensure
/// data integrity and prevent invalid graph states.
pub(crate) fn integrity_check<NI, G>(graph: &G) -> Result<(), G::Error>
where
    NI: NodeIndexTrait,
    G: GraphRef<NI>,
{
    for (src, dst) in graph.iter_edges()? {
        if !graph.contains_node(src)? {
            return Err(GraphError::EdgeHasInvalidNode.into());
        }
        if !graph.contains_node(dst)? {
            return Err(GraphError::EdgeHasInvalidNode.into());
        }
    }
    Ok(())
}
