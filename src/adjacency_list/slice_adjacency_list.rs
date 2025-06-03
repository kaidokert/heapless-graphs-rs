use crate::{graph::NodeIndexTrait, nodes::NodesIterable};

use super::outgoing_nodes::AsOutgoingNodes;

mod by_ref;
mod by_val;

pub struct SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    nodes_contrainer: T,
    _phantom: core::marker::PhantomData<(E, C)>,
}
