use crate::{
    edges::{EdgeValuesIterable, EdgesIterable, EdgesToNodesIterator},
    graph::{GraphVal, GraphValWithEdgeValues, NodeIndexTrait},
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

impl<const N: usize, E, NI, V> GraphValWithEdgeValues<NI, V> for EdgeList<N, E, NI>
where
    E: EdgeValuesIterable<V, Node = NI>,
    NI: NodeIndexTrait + Ord + Copy,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a V>)>, Self::Error>
    where
        V: 'a,
    {
        Ok(self.edges.iter_edges_values().map(|(a, b, v)| (*a, *b, v)))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::edges::EdgeValueStruct;
    use crate::tests::collect;

    #[test]
    fn test_edge_list() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        // Test iteration without println for no_std compatibility
        let _: () = graph.iter_nodes().unwrap().for_each(|_x| {});
    }

    #[test]
    fn test_edge_list_with_values() {
        // Create a graph with edge weights using EdgeValueStruct
        let edge_data = EdgeValueStruct([(0usize, 1usize, 5i32), (1, 2, 3), (0, 2, 8)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        // Test that GraphValWithEdgeValues is implemented
        let edge_values = graph.iter_edge_values().unwrap();
        let mut edges_with_values = [(0usize, 0usize, 0i32); 8];
        let mut len = 0;

        for (src, dst, weight_opt) in edge_values {
            if let Some(weight) = weight_opt {
                edges_with_values[len] = (src, dst, *weight);
                len += 1;
            }
        }

        assert_eq!(len, 3);
        assert_eq!(
            &edges_with_values[..len],
            &[(0, 1, 5), (1, 2, 3), (0, 2, 8)]
        );
    }

    #[test]
    fn test_edge_list_nodes_with_values() {
        // Test that basic GraphVal methods still work with weighted edges
        let edge_data = EdgeValueStruct([(0usize, 1usize, 10i32), (2, 3, 20)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let nodes = graph.iter_nodes().unwrap();
        let mut node_list = [0usize; 8];
        let node_slice = collect(nodes, &mut node_list);
        assert_eq!(node_slice, &[0, 1, 2, 3]);
    }
}
