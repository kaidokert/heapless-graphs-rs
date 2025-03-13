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
            .map(|(src, _dst)| src))
    }
}

pub trait GraphVal<NodeIndex: NodeIndexTrait + Copy> {
    type Error: From<GraphError<NodeIndex>>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NodeIndex>, Self::Error>;
    fn iter_edges(&self) -> Result<impl Iterator<Item = (NodeIndex, NodeIndex)>, Self::Error>;
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
