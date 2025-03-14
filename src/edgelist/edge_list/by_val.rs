use crate::{
    edges::{EdgesIterable, EdgesToNodesIterator},
    graph::{GraphVal, NodeIndexTrait},
};

use super::{EdgeList, EdgeListError};

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
        graph.iter_nodes().unwrap().for_each(|x| println!("{}", x));
    }
}
