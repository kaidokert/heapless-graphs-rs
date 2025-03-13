// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`Graph`] trait and related error values
//! and sub-traits.

use crate::edges::EdgeNodeError;

#[derive(PartialEq, Debug, Clone, Copy)]
/// Errors for Graph
pub enum GraphError<NI> {
    /// Edge is referring to a node not present in graph
    EdgeHasInvalidNode,
    /// Contains an `EdgeNodeError`
    EdgeNodeError(EdgeNodeError),
    /// Given node wasn't found in the graph
    NodeNotFound,
    // Arbitrary error that owns NI, not currently used.
    SomeError(NI),
}

impl<NI> From<EdgeNodeError> for GraphError<NI>
where
    NI: PartialEq,
{
    fn from(err: EdgeNodeError) -> Self {
        GraphError::EdgeNodeError(err)
    }
}

/// Represents a graph
///
/// Holds edge values, and may hold node values.
/// The underlying storage is defined by concrete implementations
/// like [EdgeNodeList](crate::edge_list::EdgeNodeList) or
/// [SliceAdjacencyList](`crate::adjacency_list::SliceAdjacencyList`)
pub trait Graph {
    type NodeIndex: PartialEq;
    type Error: From<GraphError<Self::NodeIndex>>;

    /// Return an iterator over all edges in the graph
    fn get_edges<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (&'a Self::NodeIndex, &'a Self::NodeIndex)>, Self::Error>
    where
        Self::NodeIndex: 'a;
    /// Return an iterator over all nodes in the graph
    fn get_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a Self::NodeIndex>, Self::Error>
    where
        Self::NodeIndex: 'a;

    /// Check if a node is present in the graph
    fn contains_node(&self, node: &Self::NodeIndex) -> Result<bool, Self::Error> {
        Ok(self.get_nodes()?.any(|x| x == node))
    }

    /// Return an iterator over all outgoing edges for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a Self::NodeIndex,
    ) -> Result<impl Iterator<Item = &'a Self::NodeIndex>, Self::Error> {
        Ok(self
            .get_edges()?
            .filter(move |(src, _)| *src == node)
            .map(|(_, next)| next)) // Keep only the next node
    }

    /// Return an iterator over all incoming edges for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn incoming_edges_for_node<'a>(
        &'a self,
        node: &'a Self::NodeIndex,
    ) -> Result<impl Iterator<Item = &'a Self::NodeIndex>, Self::Error> {
        Ok(self
            .get_edges()?
            .filter(move |(_, dst)| *dst == node)
            .map(|(src, _)| src)) // Keep only the next node
    }

    /// Return an iterator over all neighboring nodes for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn neighboring_nodes<'a>(
        &'a self,
        node: &'a Self::NodeIndex,
    ) -> Result<impl Iterator<Item = &'a Self::NodeIndex>, Self::Error> {
        Ok(self
            .get_edges()?
            .filter(move |(src, dst)| *src == node || *dst == node)
            .map(move |(src, dst)| if src == node { dst } else { src }))
    }
}

/// Check if all edges refer to valid nodes in the graph
pub(crate) fn integrity_check<G: Graph>(graph: &G) -> Result<(), G::Error> {
    for edge in graph.get_edges()? {
        if !graph.contains_node(edge.0)? {
            return Err(GraphError::EdgeHasInvalidNode.into());
        }
        if !graph.contains_node(edge.1)? {
            return Err(GraphError::EdgeHasInvalidNode.into());
        }
    }
    Ok(())
}

/// Graph where nodes can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableNodes: Graph {
    // TODO: What if there's a duplicate node?
    fn add_node_unchecked(&mut self, n: Self::NodeIndex) -> Option<usize>;
    // TODO: what happens if the node is referred to? IntegrityError ?
    fn remove_node_unchecked(&mut self, n: Self::NodeIndex) -> Option<usize>;
}

/// Trait for graphs that store node values
///
/// Warning: Work in progress
pub trait GraphWithNodeValues<V>: Graph {
    /// Return an iterator over all nodes with values in the graph
    fn get_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (&'a Self::NodeIndex, Option<&'a V>)>, Self::Error>
    where
        V: 'a;
    /// Return a value for a node
    fn get_node_value(&self, node: &Self::NodeIndex) -> Result<Option<&V>, Self::Error>;

    /// Return neighboring nodes with values
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a Self::NodeIndex,
    ) -> Result<impl Iterator<Item = (&'a Self::NodeIndex, Option<&'a V>)>, Self::Error>
    where
        V: 'a;
}

/// Graph where edges can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableEdges: Graph {
    // TODO: should be simple, actually implement this
    fn add_edge(&mut self, src: Self::NodeIndex, dst: Self::NodeIndex) -> Option<usize>;
    // TODO: What happens with duplicates ?
    fn remove_edge(&mut self, src: Self::NodeIndex, dst: Self::NodeIndex) -> Option<usize>;
}

/// Trait for graphs that store edge values or weights
pub trait GraphWithEdgeValues<V>: Graph {
    /// Return an iterator over all edges with values in the graph
    #[allow(clippy::type_complexity)]
    fn get_edge_values<'a>(
        &'a self,
    ) -> Result<
        impl Iterator<Item = (&'a Self::NodeIndex, &'a Self::NodeIndex, Option<&'a V>)>,
        Self::Error,
    >
    where
        V: 'a;

    /// Return all neighbors for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a Self::NodeIndex,
    ) -> Result<impl Iterator<Item = (&'a Self::NodeIndex, Option<&'a V>)>, Self::Error>
    where
        V: 'a,
    {
        Ok(self
            .get_edge_values()?
            .filter(move |(src, dst, _)| *src == node || *dst == node)
            .map(move |(src, dst, v)| if src == node { (dst, v) } else { (src, v) }))
    }
}
