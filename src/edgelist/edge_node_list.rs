mod by_ref;
mod by_val;

use crate::graph::{GraphError, GraphRef, NodeIndexTrait};

pub struct EdgeNodeList<E, N, NI> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
}

/// Integrity check for graphs - validates that all edges reference valid nodes
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

impl<E, N, NI> EdgeNodeList<E, N, NI> {
    pub fn new(edges: E, nodes: N) -> Result<Self, GraphError<NI>>
    where
        Self: GraphRef<NI, Error = GraphError<NI>>,
        NI: NodeIndexTrait,
    {
        let result = Self::new_unchecked(edges, nodes);
        integrity_check::<NI, _>(&result)?;
        Ok(result)
    }

    pub fn new_unchecked(edges: E, nodes: N) -> Self {
        Self {
            edges,
            nodes,
            _phantom: core::marker::PhantomData,
        }
    }
}
