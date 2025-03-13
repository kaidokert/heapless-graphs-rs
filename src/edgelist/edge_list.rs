use crate::edges::EdgesIterable;

use crate::edges::{EdgeNodeError, EdgesToNodesIterator};

use crate::graph::{GraphError, GraphRef, GraphVal, NodeIndexTrait};

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

impl<const N: usize, E, NI> GraphRef<NI> for EdgeList<N, E, NI>
where
    E: EdgesIterable<Node = NI>,
    NI: NodeIndexTrait + Ord,
{
    type Error = EdgeListError<NI>;

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.edges.iter_edges())
    }
    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        // Note: N here limits the capacity of yielded nodes
        Ok(EdgesToNodesIterator::<N, NI>::new(&self.edges)?)
    }
}

impl<const N: usize, E, NI> GraphVal<NI> for EdgeList<N, E, NI>
where
    E: EdgesIterable<Node = NI>,
    NI: NodeIndexTrait + Ord + Copy,
{
    type Error = EdgeListError<NI>;

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }
    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(EdgesToNodesIterator::<N, NI>::new(&self.edges)?.copied())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_edge_list() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        // graph.iter_nodes().unwrap().for_each(|x| println!("{}", x));
        //GraphRef::iter_nodes(&graph).unwrap().for_each(|x| println!("{}", x));
        GraphVal::iter_nodes(&graph)
            .unwrap()
            .for_each(|x| println!("{}", x));
    }
}
