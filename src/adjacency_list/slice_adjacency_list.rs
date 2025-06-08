use crate::graph::{integrity_check, GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

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

impl<NI, E, C, T> SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    /// Create new slice adjacency list with validation
    ///
    /// This function validates that all edge destinations exist in the node set.
    /// Returns an error if any edge references a non-existent node.
    pub fn new(nodes_contrainer: T) -> Result<Self, GraphError<NI>>
    where
        Self: GraphRef<NI, Error = GraphError<NI>>,
    {
        let result = Self::new_unchecked(nodes_contrainer);
        integrity_check::<NI, _>(&result)?;
        Ok(result)
    }

    pub fn new_unchecked(nodes_contrainer: T) -> Self {
        Self {
            nodes_contrainer,
            _phantom: core::marker::PhantomData,
        }
    }
}
