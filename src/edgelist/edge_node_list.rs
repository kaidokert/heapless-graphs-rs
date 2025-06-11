use crate::graph::{integrity_check, Graph, GraphError, NodeIndex};

/// Edge list graph that stores both edges and nodes.
///
/// This struct represents a graph that stores both edges and nodes explicitly.
/// It requires more memory than a graph that only stores edges like [`crate::edgelist::edge_list::EdgeList`],
/// but iterating over nodes is much more efficient. Additionally, it allows
/// storing values associated with each node.
///
/// # Type Parameters
///
/// - `NI`: The type that represents the node indices in the graph. This could be
///   a simple type like `usize` or a more complex index type. It is expected
///   to implement [`PartialEq`] to allow node comparison.
/// - `E`: The type of the container or collection that stores the edges. It is
///   expected to implement the [`crate::edges::EdgesIterable`] trait, which defines the
///   behavior for iterating over edges.
/// - `N`: The type of the container or collection that stores the nodes. It is
///   expected to implement the [`crate::nodes::NodesIterable`] trait, which defines the
///   behavior for iterating over nodes.
///
pub struct EdgeNodeList<NI, E, N> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
}

impl<NI, E, N> EdgeNodeList<NI, E, N> {
    pub fn new(edges: E, nodes: N) -> Result<Self, GraphError<NI>>
    where
        Self: Graph<NI, Error = GraphError<NI>>,
        NI: NodeIndex,
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

impl<NI, E, N> Graph<NI> for EdgeNodeList<NI, E, N>
where
    NI: NodeIndex,
    N: crate::nodes::NodesIterable<Node = NI>,
    E: crate::edges::EdgesIterable<Node = NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.iter_nodes().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }
}

impl<NI, E, N, V> crate::graph::GraphWithNodeValues<NI, V> for EdgeNodeList<NI, E, N>
where
    NI: NodeIndex,
    N: crate::nodes::NodesValuesIterable<V, Node = NI>,
    E: crate::edges::EdgesIterable<Node = NI>,
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

impl<NI, E, N, V> crate::graph::GraphWithEdgeValues<NI, V> for EdgeNodeList<NI, E, N>
where
    NI: NodeIndex,
    N: crate::nodes::NodesIterable<Node = NI>,
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::EdgeValuesIterable<V, Node = NI>,
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
    use crate::graph::{GraphError, GraphWithEdgeValues, GraphWithNodeValues};
    use crate::nodes::{NodeValueStructOption, NodesValuesIterable};
    use crate::tests::collect;

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

        // Test that GraphWithEdgeValues is implemented
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

    #[test]
    fn test_iter_nodes_values() {
        // Test that iter_nodes_values() and node_value() work correctly with mixed values including None
        let node_data = NodeValueStructOption([
            Some((0, Some("value_0"))), // Node 0 exists with a value
            Some((1, Some("value_1"))), // Node 1 exists with a value
            Some((2, None)),            // Node 2 exists but has None value
            None,                       // Index 3 has no node
            Some((3, Some("value_3"))), // Node 3 exists with a value
        ]);

        // Test the iterator behavior
        let mut nodes_and_values = [(0usize, None); 5];
        let nodes_values_slice = collect(
            node_data.iter_nodes_values().map(|(n, v)| (*n, v)),
            &mut nodes_and_values,
        );

        // Should yield all 4 existing nodes in order: 0, 1, 2, 3
        assert_eq!(
            nodes_values_slice,
            &[
                (0, Some(&Some("value_0"))),
                (1, Some(&Some("value_1"))),
                (2, Some(&None)), // Node exists but has None value
                (3, Some(&Some("value_3")))
            ]
        );

        // Test with EdgeNodeList
        let edges = [(0usize, 1usize), (1, 2), (2, 3)];
        let graph = EdgeNodeList::new(edges, node_data).unwrap();

        // Test node_value() for each node
        assert_eq!(graph.node_value(0).unwrap(), Some(&Some("value_0")));
        assert_eq!(graph.node_value(1).unwrap(), Some(&Some("value_1")));
        assert_eq!(graph.node_value(2).unwrap(), Some(&None)); // Node exists with None value
        assert_eq!(graph.node_value(3).unwrap(), Some(&Some("value_3")));

        // Non-existent node should return error
        assert!(graph.node_value(99).is_err());
        assert!(matches!(
            graph.node_value(99).unwrap_err(),
            GraphError::NodeNotFound(99)
        ));
    }
}
