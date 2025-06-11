use crate::graph::NodeIndex;
use crate::nodes::NodesIterable;

/// A list of outgoing nodes from a node, in an adjacency list.
pub trait AsOutgoingNodes<NI, E>
where
    NI: NodeIndex,
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

impl<E, NI> AsOutgoingNodes<NI, E> for E
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>
        = E::Iter<'a>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a,
    {
        self.iter_nodes()
    }
}
