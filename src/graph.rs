// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`Graph`] trait and related error values
//! and sub-traits.

use crate::edges::EdgeNodeError;

#[derive(PartialEq, Debug, Clone, Copy)]
/// Errors for Graph
pub enum GraphError<NI>
where
    NI: PartialEq,
{
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
pub trait Graph<NI>
where
    NI: PartialEq,
    Self: Sized,
{
    type Edges<'a>: DoubleEndedIterator<Item = (&'a NI, &'a NI)>
    where
        Self: 'a,
        NI: 'a;
    type Nodes<'a>: Iterator<Item = &'a NI>
    where
        Self: 'a,
        NI: 'a;

    /// Return an iterator over all edges in the graph
    fn get_edges(&self) -> Result<Self::Edges<'_>, GraphError<NI>>;
    /// Return an iterator over all nodes in the graph
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, GraphError<NI>>;

    /// Check if a node is present in the graph
    fn contains_node(&self, node: &NI) -> Result<bool, GraphError<NI>> {
        Ok(self.get_nodes()?.any(|x| x == node))
    }

    /// Return an iterator over all outgoing edges for a node
    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl DoubleEndedIterator<Item = &'a NI>, GraphError<NI>> {
        Ok(self
            .get_edges()?
            .filter(move |(src, _)| *src == node)
            .map(|(_, next)| next)) // Keep only the next node
    }

    /// Check if all edges refer to valid nodes in the graph
    fn integrity_check(&self) -> Result<(), GraphError<NI>> {
        for edge in self.get_edges()? {
            if !self.contains_node(edge.0)? {
                return Err(GraphError::EdgeHasInvalidNode);
            }
            if !self.contains_node(edge.1)? {
                return Err(GraphError::EdgeHasInvalidNode);
            }
        }
        Ok(())
    }
}

/// Graph where nodes can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableNodes<NI: PartialEq>: Graph<NI> {
    // TODO: What if there's a duplicate node?
    fn add_node_unchecked(&mut self, n: NI) -> Option<usize>;
    // TODO: what happens if the node is referred to? IntegrityError ?
    fn remove_node_unchecked(&mut self, n: NI) -> Option<usize>;
}

/// Trait for graphs that store node values
///
/// Warning: Work in progress
pub trait GraphWithNodeValues<NI: PartialEq, V>: Graph<NI> {
    type NodeValues<'a>: Iterator<Item = (&'a NI, Option<&'a V>)>
    where
        Self: 'a,
        V: 'a,
        NI: 'a;
    /// Return an iterator over all nodes with values in the graph
    fn get_node_values<'a>(&'a self) -> Result<Self::NodeValues<'_>, GraphError<NI>>
    where
        V: 'a;
    /// Return a value for a node
    fn get_node_value(&self, node: &NI) -> Result<Option<&V>, GraphError<NI>>;
}

/// Graph where edges can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableEdges<NI: PartialEq>: Graph<NI> {
    // TODO: should be simple, actually implement this
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize>;
    // TODO: What happens with duplicates ?
    fn remove_edge(&mut self, src: NI, dst: NI) -> Option<usize>;
}

/// Trait for graphs that store edge values or weights
pub trait GraphWithEdgeValues<NI: PartialEq, V>: Graph<NI> {
    type EdgeValues<'a>: DoubleEndedIterator<Item = (&'a NI, &'a NI, Option<&'a V>)>
    where
        Self: 'a,
        V: 'a,
        NI: 'a;
    // TODO: lifetime 'a here shouldn't be needed
    /// Return an iterator over all edges with values in the graph
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'_>, GraphError<NI>>
    where
        V: 'a;

    /// Return all neighbors for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn neighbors_for_node_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl DoubleEndedIterator<Item = (&'a NI, Option<&'a V>)>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self
            .get_edge_values()?
            .filter(move |(src, dst, _)| *src == node || *dst == node)
            .map(move |(src, dst, v)| if src == node { (dst, v) } else { (src, v) }))
    }
}
