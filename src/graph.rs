// SPDX-License-Identifier: Apache-2.0

//! Core graph traits
//!
//! Defines the [`GraphRef`] and [`GraphVal`] traits and related error values
//! and sub-traits.

pub trait NodeIndexTrait: PartialEq + PartialOrd {}
impl<T> NodeIndexTrait for T where T: PartialEq + PartialOrd {}

#[derive(PartialEq, Debug, Clone, Copy)]
/// Errors for Graph
pub enum GraphError<NI: NodeIndexTrait> {
    NodeNotFound,
    EdgeNotFound,
    EdgeHasInvalidNode,
    PlaceHolder(NI),
}

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
pub trait GraphValWithEdgeValues<NI, EV>: GraphVal<NI>
where
    NI: NodeIndexTrait + Copy,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a EV>)>, Self::Error>
    where
        EV: 'a;
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
