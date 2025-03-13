// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`Graph`] trait and related error values
//! and sub-traits.

pub trait NodeIndex: PartialEq {}
impl<T> NodeIndex for T where T: PartialEq {}

#[derive(PartialEq, Debug, Clone, Copy)]
/// Errors for Graph
pub enum GraphError<NI>
where
    NI: NodeIndex,
{
    /// Edge is referring to a node not present in graph
    EdgeHasInvalidNode,
    /// Given node wasn't found in the graph
    NodeNotFound,
    // Arbitrary error that owns NI, not currently used.
    SomeError(NI),
}

// Why is NI a parameter here, rather than associated type ?

/// Represents a graph
///
/// Holds edge values, and may hold node values.
/// The underlying storage is defined by concrete implementations
/// like [EdgeNodeList](crate::edge_list::EdgeNodeList) or
/// [SliceAdjacencyList](`crate::adjacency_list::SliceAdjacencyList`)
pub trait Graph<NI>
where
    NI: NodeIndex,
    Self: Sized,
{
    type Error: From<GraphError<NI>>;

    // todo: Should this be DoubleEnded or not ?
    type Edges<'a>: Iterator<Item = (&'a NI, &'a NI)>
    where
        Self: 'a,
        NI: 'a;
    type Nodes<'a>: Iterator<Item = &'a NI>
    where
        Self: 'a,
        NI: 'a;

    /// Return an iterator over all edges in the graph
    fn get_edges(&self) -> Result<Self::Edges<'_>, Self::Error>;
    /// Return an iterator over all nodes in the graph
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, Self::Error>;

    /// Check if a node is present in the graph
    fn contains_node(&self, node: &NI) -> Result<bool, Self::Error> {
        Ok(self.get_nodes()?.any(|x| x == node))
    }

    /// Return an iterator over all outgoing edges for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error> {
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
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error> {
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
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error> {
        Ok(self
            .get_edges()?
            .filter(move |(src, dst)| *src == node || *dst == node)
            .map(move |(src, dst)| if src == node { dst } else { src }))
    }

    /// Check if all edges refer to valid nodes in the graph
    fn integrity_check(&self) -> Result<(), Self::Error> {
        for edge in self.get_edges()? {
            if !self.contains_node(edge.0)? {
                return Err(GraphError::EdgeHasInvalidNode.into());
            }
            if !self.contains_node(edge.1)? {
                return Err(GraphError::EdgeHasInvalidNode.into());
            }
        }
        Ok(())
    }
}

/// Graph where nodes can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableNodes<NI: NodeIndex>: Graph<NI> {
    // TODO: What if there's a duplicate node?
    fn add_node_unchecked(&mut self, n: NI) -> Option<usize>;
    // TODO: what happens if the node is referred to? IntegrityError ?
    fn remove_node_unchecked(&mut self, n: NI) -> Option<usize>;
}

/// Trait for graphs that store node values
///
/// Warning: Work in progress
pub trait GraphWithNodeValues<NI: NodeIndex, V>: Graph<NI> {
    type NodeValues<'a>: Iterator<Item = (&'a NI, Option<&'a V>)>
    where
        Self: 'a,
        V: 'a,
        NI: 'a;
    /// Return an iterator over all nodes with values in the graph
    fn get_node_values<'a>(&'a self) -> Result<Self::NodeValues<'a>, GraphError<NI>>
    where
        V: 'a;
    /// Return a value for a node
    fn get_node_value(&self, node: &NI) -> Result<Option<&V>, GraphError<NI>>;

    /// Return neighboring nodes with values
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a V>)>, Self::Error>
    where
        NI: 'a,
        V: 'a;
}

/// Graph where edges can be added and removed
///
/// Warning: Work in progress
pub trait GraphWithMutableEdges<NI: NodeIndex>: Graph<NI> {
    // TODO: should be simple, actually implement this
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize>;
    // TODO: What happens with duplicates ?
    fn remove_edge(&mut self, src: NI, dst: NI) -> Option<usize>;
}

/// Trait for graphs that store edge values or weights
pub trait GraphWithEdgeValues<NI: NodeIndex, V>: Graph<NI> {
    type EdgeValues<'a>: Iterator<Item = (&'a NI, &'a NI, Option<&'a V>)>
    where
        Self: 'a,
        V: 'a,
        NI: 'a;
    // TODO: lifetime 'a here shouldn't be needed
    /// Return an iterator over all edges with values in the graph
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'a>, GraphError<NI>>
    where
        V: 'a;

    /// Return all neighbors for a node
    ///
    /// Warning: This is very inefficient default implementation that loops over all
    /// edges in the graph.
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a V>)>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self
            .get_edge_values()?
            .filter(move |(src, dst, _)| *src == node || *dst == node)
            .map(move |(src, dst, v)| if src == node { (dst, v) } else { (src, v) }))
    }
}
