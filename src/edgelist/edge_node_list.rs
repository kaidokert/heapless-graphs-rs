mod by_ref;
mod by_val;

use crate::graph::{integrity_check, GraphError, GraphRef, NodeIndexTrait};

/// Edge list graph that stores both edges and nodes.
///
/// This struct represents a graph that stores both edges and nodes explicitly.
/// It requires more memory than a graph that only stores edges like [EdgeList],
/// but iterating over nodes is much more efficient. Additionally, it allows
/// storing values associated with each node.
///
/// # Type Parameters
///
/// - `E`: The type of the container or collection that stores the edges. It is
///   expected to implement the [EdgesIterable] trait, which defines the
///   behavior for iterating over edges.
/// - `N`: The type of the container or collection that stores the nodes. It is
///   expected to implement the [NodesIterable] trait, which defines the
///   behavior for iterating over nodes.
/// - `NI`: The type that represents the node indices in the graph. This could be
///   a simple type like `usize` or a more complex index type. It is expected
///   to implement [`PartialEq`] to allow node comparison.
///
pub struct EdgeNodeList<E, N, NI> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
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
