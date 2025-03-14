use crate::graph::NodeIndexTrait;
use crate::nodes::NodesIterable;

/// A list of outgoing edges from a node, in an adjacency list.
pub trait AsOutgoingNodes<NI, E>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>: DoubleEndedIterator<Item = &'a NI>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a;
}
