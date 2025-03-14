use crate::{
    edges::{EdgesIterable, EdgesToNodesIterator},
    graph::{GraphRef, NodeIndexTrait},
};

use super::{EdgeList, EdgeListError};

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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_edge_list() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        graph.iter_nodes().unwrap().for_each(|x| println!("{}", x));
    }

    #[test]
    fn test_iter_edges() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        let edges = graph.iter_edges().unwrap();
        assert_eq!(
            edges.collect::<Vec<_>>(),
            vec![(&0, &1), (&0, &2), (&1, &2)]
        );
    }

    #[test]
    fn test_outgoing_edges() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        let edges = graph.outgoing_edges(&0).unwrap();
        assert_eq!(edges.collect::<Vec<_>>(), vec![&1, &2]);
    }
}
