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
    use crate::tests::array_collect;

    #[test]
    fn test_edge_list() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        // Test iteration without println for no_std compatibility
        let _: () = graph.iter_nodes().unwrap().for_each(|_x| {});
    }

    #[test]
    fn test_iter_edges() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        let edges = graph.iter_edges().unwrap();
        let mut edge_list = [(&0usize, &0usize); 8];
        let len = array_collect(edges, &mut edge_list);
        assert_eq!(len, 3);
        assert_eq!(&edge_list[..len], &[(&0, &1), (&0, &2), (&1, &2)]);
    }

    #[test]
    fn test_outgoing_edges() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        let edges = graph.outgoing_edges(&0).unwrap();
        let mut edge_nodes = [&0usize; 8];
        let len = array_collect(edges, &mut edge_nodes);
        assert_eq!(len, 2);
        assert_eq!(&edge_nodes[..len], &[&1, &2]);
    }
}
