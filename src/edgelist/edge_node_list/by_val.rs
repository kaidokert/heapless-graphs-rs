use crate::{
    edges::EdgesIterable,
    graph::{GraphError, GraphVal, GraphValWithEdgeValues, GraphValWithNodeValues, NodeIndexTrait},
    nodes::{NodesIterable, NodesValuesIterable},
};

use super::EdgeNodeList;

impl<E, N, NI> GraphVal<NI> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait + Copy,
    N: NodesIterable<Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.iter_nodes().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }
}

impl<E, N, NI, V> GraphValWithNodeValues<NI, V> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait + Copy,
    N: NodesValuesIterable<V, Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    fn node_value(&self, node: NI) -> Result<Option<&V>, Self::Error> {
        self.nodes
            .iter_nodes_values()
            .find(|(n, _)| **n == node)
            .map(|(_, value)| value)
            .ok_or(GraphError::NodeNotFound(node))
    }

    fn iter_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a V>)>, Self::Error>
    where
        V: 'a,
    {
        Ok(self.nodes.iter_nodes_values().map(|(n, v)| (*n, v)))
    }
}

impl<E, N, NI, V> GraphValWithEdgeValues<NI, V> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait + Copy,
    N: NodesIterable<Node = NI>,
    E: EdgesIterable<Node = NI> + crate::edges::EdgeValuesIterable<V, Node = NI>,
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

    #[test]
    fn test_edge_node_list() {
        let graph = EdgeNodeList::new([(0usize, 1usize), (0, 2), (1, 2)], [0, 1, 2]).unwrap();
        // Test iteration without println for no_std compatibility
        let _: () = graph.iter_nodes().unwrap().for_each(|_x| {});
    }

    #[test]
    fn test_edge_node_list_with_values() {
        // Create a graph with edge weights using EdgeValueStruct
        let edge_data = EdgeValueStruct([(0usize, 1usize, 5i32), (1, 2, 3), (0, 2, 8)]);
        let graph = EdgeNodeList::new(edge_data, [0, 1, 2]).unwrap();

        // Test that GraphValWithEdgeValues is implemented
        let mut edges_with_values = [(0usize, 0usize, 0i32); 8];
        let mut len = 0;

        for (src, dst, weight_opt) in graph.iter_edge_values().unwrap() {
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

        // Test outgoing edge values from node 0
        let mut outgoing = [(0usize, 0i32); 8];
        let mut len = 0;
        for (dst, weight_opt) in graph.outgoing_edge_values(0).unwrap() {
            if let Some(weight) = weight_opt {
                outgoing[len] = (dst, *weight);
                len += 1;
            }
        }
        assert_eq!(len, 2);
        assert!(outgoing[..len].contains(&(1, 5)));
        assert!(outgoing[..len].contains(&(2, 8)));
    }
}
