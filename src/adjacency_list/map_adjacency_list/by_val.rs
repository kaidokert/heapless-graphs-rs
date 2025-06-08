use crate::containers::maps::MapTrait;
use crate::graph::{GraphError, GraphVal, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, MapAdjacencyList};

impl<M, NI, E, C> GraphVal<NI> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: NodeIndexTrait + Eq + core::hash::Hash + Copy,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.keys().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(1) contains_node for map adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.nodes.contains_key(&node))
    }

    /// Optimized O(out-degree) outgoing_edges for map adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // The key insight: use Option to unify the iterator types, then flatten
        let edges_option = self.nodes.get(&node).map(|edges| edges.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}
