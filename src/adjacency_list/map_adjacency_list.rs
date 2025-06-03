use crate::containers::maps::MapTrait;
use crate::{graph::NodeIndexTrait, nodes::NodesIterable};

use super::outgoing_nodes::AsOutgoingNodes;

mod by_ref;
mod by_val;

pub struct MapAdjacencyList<M, NI, E, C>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    nodes: M,
    _phantom: core::marker::PhantomData<(E, C)>,
}

impl<M, NI, E, C> MapAdjacencyList<M, NI, E, C>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    pub fn new_unchecked(nodes: M) -> Self {
        Self {
            nodes,
            _phantom: core::marker::PhantomData,
        }
    }
}
