mod by_ref;
mod by_val;

pub struct EdgeNodeList<E, N, NI> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
}

impl<E, N, NI> EdgeNodeList<E, N, NI> {
    pub fn new(edges: E, nodes: N) -> Self {
        Self {
            edges,
            nodes,
            _phantom: core::marker::PhantomData,
        }
    }
}
