use crate::graph::{GraphError, GraphVal, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, SliceAdjacencyList};

impl<NI, E, C, T> GraphVal<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait + Copy,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes_contrainer.as_ref().iter().map(|(n, _)| *n))
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes_contrainer
            .as_ref()
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(n) contains_node for slice adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self
            .nodes_contrainer
            .as_ref()
            .iter()
            .any(|(n, _)| *n == node))
    }

    /// Optimized O(n + out-degree) outgoing_edges for slice adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Same pattern: use Option to unify iterator types, then flatten
        let edges_option = self
            .nodes_contrainer
            .as_ref()
            .iter()
            .find(|(n, _)| *n == node)
            .map(|(_, node_data)| node_data.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}
