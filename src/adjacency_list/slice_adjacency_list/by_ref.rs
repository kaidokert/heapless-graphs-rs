use crate::graph::{GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, SliceAdjacencyList};

impl<NI, E, C, T> GraphRef<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.nodes_contrainer.as_ref().iter().map(|(n, _)| n))
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self
            .nodes_contrainer
            .as_ref()
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (n, m))))
    }
}
