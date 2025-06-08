use crate::edges::EdgeNodeError;

use crate::graph::{GraphError, NodeIndexTrait};

mod by_ref;
mod by_val;

#[derive(Debug)]
pub enum EdgeListError<NI: NodeIndexTrait> {
    EdgeNodeError(EdgeNodeError),
    GraphError(GraphError<NI>),
}

impl<NI: NodeIndexTrait> From<EdgeNodeError> for EdgeListError<NI> {
    fn from(e: EdgeNodeError) -> Self {
        EdgeListError::EdgeNodeError(e)
    }
}
impl<NI: NodeIndexTrait> From<GraphError<NI>> for EdgeListError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        EdgeListError::GraphError(e)
    }
}

/// Edge list graph that stores only edges
///
/// This struct represents a graph using an edge list. It is optimized for
/// compact edge representation, but iterating over nodes may be expensive.
/// Edges can also have values.
///
/// See [EdgesToNodesIterator] for the expensive node iteration used.
///
/// # Type Parameters
///
/// - `N`: The max number of nodes in the graph. This is a constant size parameter
///   that represents the total capacity for nodes. The storage is only allocated
///   on stack temporarily when nodes are iterated over.
/// - `E`: The type of the container or collection that stores the edges. It is expected to
///   implement the [`EdgesIterable`] trait, which defines the behavior for
///   iterating over edges.
/// - `NI`: The type that represents the node indices in the graph. This could be
///   a simple integer type like `usize` or a more complex index type.
///
pub struct EdgeList<const N: usize, E, NI> {
    edges: E,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, E, NI> EdgeList<N, E, NI> {
    pub fn new(edges: E) -> Self {
        Self {
            edges,
            _phantom: Default::default(),
        }
    }
}
