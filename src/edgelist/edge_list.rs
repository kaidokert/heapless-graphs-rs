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
