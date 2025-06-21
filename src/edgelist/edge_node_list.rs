use crate::graph::{integrity_check, Graph, GraphError, GraphWithMutableNodes, NodeIndex};
use crate::nodes::MutableNodes;

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

impl<NI, E, N> EdgeNodeList<NI, E, N>
where
    NI: NodeIndex + Copy + Default,
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::MutableEdges<NI> + Default,
    N: crate::nodes::NodesIterable<Node = NI> + crate::nodes::MutableNodes<NI> + Default,
{
    /// Creates an EdgeNodeList from any graph by copying all nodes and edges
    ///
    /// This function iterates over all nodes and edges in the source graph and creates
    /// an EdgeNodeList representation. Both nodes and edges are stored explicitly.
    ///
    /// # Arguments
    /// * `source_graph` - The graph to copy nodes and edges from
    ///
    /// # Returns
    /// * `Ok(EdgeNodeList)` if successful
    /// * `Err(GraphError)` if iteration fails or capacity is exceeded
    ///
    /// # Constraints
    /// * Node index type must implement Copy
    /// * Edge container E must implement Default and MutableEdges
    /// * Node container N must implement Default and MutableNodes
    /// * Requires sufficient capacity in both E and N for all edges and nodes
    ///
    /// # Example
    /// ```
    /// use heapless_graphs::edgelist::edge_node_list::EdgeNodeList;
    /// use heapless_graphs::adjacency_list::map_adjacency_list::MapAdjacencyList;
    /// use heapless_graphs::containers::maps::staticdict::Dictionary;
    /// use heapless_graphs::containers::maps::MapTrait;
    /// use heapless_graphs::edges::EdgeStructOption;
    /// use heapless_graphs::nodes::NodeStructOption;
    ///
    /// // Create a source graph (adjacency list)
    /// let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
    /// dict.insert(0, [1, 2]).unwrap();
    /// dict.insert(1, [2, 0]).unwrap();
    /// dict.insert(2, [0, 1]).unwrap();
    /// let source = MapAdjacencyList::new_unchecked(dict);
    ///
    /// // Convert to EdgeNodeList with capacity for nodes and edges
    /// let edge_node_graph: EdgeNodeList<usize, EdgeStructOption<8, usize>, NodeStructOption<4, usize>> =
    ///     EdgeNodeList::from_graph(&source).unwrap();
    /// ```
    pub fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<NI>>
    where
        G: Graph<NI>,
        GraphError<NI>: From<G::Error>,
    {
        // Create default containers for edges and nodes
        let mut edges = E::default();
        let mut nodes = N::default();

        // Add all nodes to the node container
        for node in source_graph.iter_nodes()? {
            if nodes.add(node).is_none() {
                return Err(GraphError::OutOfCapacity);
            }
        }

        // Add all edges to the edge container
        for (source, destination) in source_graph.iter_edges()? {
            if edges.add_edge((source, destination)).is_none() {
                return Err(GraphError::OutOfCapacity);
            }
        }

        Ok(Self::new_unchecked(edges, nodes))
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

impl<NI, E, N> GraphWithMutableNodes<NI> for EdgeNodeList<NI, E, N>
where
    NI: NodeIndex + PartialEq,
    N: crate::nodes::NodesIterable<Node = NI> + MutableNodes<NI>,
    E: crate::edges::EdgesIterable<Node = NI>,
{
    fn add_node(&mut self, node: NI) -> Result<(), Self::Error> {
        if self.contains_node(node)? {
            return Err(GraphError::DuplicateNode(node));
        }
        self.nodes.add(node).ok_or(GraphError::OutOfCapacity)?;
        Ok(())
    }

    fn remove_node(&mut self, node: NI) -> Result<(), Self::Error> {
        // Check if node exists
        if !self.contains_node(node)? {
            return Err(GraphError::NodeNotFound(node));
        }

        // Check if node has incoming edges
        if self.incoming_edges(node)?.next().is_some() {
            return Err(GraphError::NodeHasIncomingEdges(node));
        }

        // Remove the node from the nodes container
        self.nodes
            .remove(node)
            .ok_or(GraphError::NodeNotFound(node))?;
        Ok(())
    }
}

impl<NI, E, N> crate::graph::GraphWithMutableEdges<NI> for EdgeNodeList<NI, E, N>
where
    NI: NodeIndex + PartialEq,
    N: crate::nodes::NodesIterable<Node = NI>,
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::MutableEdges<NI>,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Validate that both nodes exist in the graph
        if !self.contains_node(source)? {
            return Err(GraphError::EdgeHasInvalidNode(source));
        }
        if !self.contains_node(destination)? {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Add the edge to the edge container
        self.edges
            .add_edge((source, destination))
            .ok_or(GraphError::OutOfCapacity)?;

        Ok(())
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Remove the edge from the edge container
        // If nodes don't exist, the edge won't be found anyway
        self.edges
            .remove_edge((source, destination))
            .ok_or(GraphError::EdgeNotFound(source, destination))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::edges::EdgeValueStruct;
    use crate::graph::{GraphError, GraphWithEdgeValues, GraphWithNodeValues};
    use crate::nodes::{NodeValueStructOption, NodesValuesIterable};
    use crate::tests::{collect, collect_sorted};

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
        let edges_slice = collect(
            graph
                .iter_edge_values()
                .unwrap()
                .filter_map(|(src, dst, weight_opt)| weight_opt.map(|w| (src, dst, *w))),
            &mut edges_with_values,
        );
        assert_eq!(edges_slice, &[(0, 1, 5), (1, 2, 3), (0, 2, 8)]);

        // Test outgoing edge values from node 0
        let mut outgoing = [(0usize, 0i32); 8];
        let outgoing_slice = collect_sorted(
            graph
                .outgoing_edge_values(0)
                .unwrap()
                .filter_map(|(dst, weight_opt)| weight_opt.map(|w| (dst, *w))),
            &mut outgoing,
        );
        assert_eq!(outgoing_slice, &[(1, 5), (2, 8)]);
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
        assert!(matches!(
            graph.node_value(99),
            Err(GraphError::NodeNotFound(99))
        ));
    }

    #[test]
    fn test_add_node_to_empty_graph() {
        use crate::nodes::NodeStructOption;

        let edges: [(usize, usize); 0] = [];
        let nodes = NodeStructOption([None, None, None]); // Capacity for 3 nodes
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add a node to empty graph
        graph.add_node(42).unwrap();

        // Verify the node was added
        assert!(graph.contains_node(42).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 1);
        assert_eq!(graph.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_to_existing_graph() {
        use crate::nodes::NodeStructOption;

        let edges = [(0usize, 1usize), (1, 2)];
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), None, None]); // Room to add more
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add a new node
        graph.add_node(3).unwrap();

        // Verify all nodes exist
        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert!(graph.contains_node(3).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 4);

        // Verify new node has no outgoing edges
        assert_eq!(graph.outgoing_edges(3).unwrap().count(), 0);

        // Verify existing edges are preserved
        let mut edges = [0usize; 2];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1]);

        let mut edges = [0usize; 2];
        let edges_slice = collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2]);
    }

    #[test]
    fn test_add_node_capacity_exceeded() {
        use crate::nodes::NodeStructOption;

        // Create a NodeStructOption that's already at full capacity
        let edges = [(0usize, 1usize)];
        let nodes = NodeStructOption([Some(0), Some(1)]); // Full capacity, no None slots
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Try to add a third node (should exceed capacity)
        let result = graph.add_node(2);

        // Should return capacity error
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));

        // Original graph should be unchanged
        assert_eq!(graph.iter_nodes().unwrap().count(), 2);
    }

    #[test]
    fn test_add_multiple_nodes() {
        use crate::nodes::NodeStructOption;

        let edges: [(usize, usize); 0] = [];
        let nodes = NodeStructOption([None, None, None, None, None]); // Capacity for 5 nodes
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add multiple nodes
        graph.add_node(10).unwrap();
        graph.add_node(20).unwrap();
        graph.add_node(30).unwrap();

        // Verify all nodes were added
        assert!(graph.contains_node(10).unwrap());
        assert!(graph.contains_node(20).unwrap());
        assert!(graph.contains_node(30).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);

        // Verify no edges exist between nodes (since we started with empty edges)
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Verify each node has no outgoing edges
        assert_eq!(graph.outgoing_edges(10).unwrap().count(), 0);
        assert_eq!(graph.outgoing_edges(20).unwrap().count(), 0);
        assert_eq!(graph.outgoing_edges(30).unwrap().count(), 0);
    }

    #[test]
    fn test_add_duplicate_node() {
        use crate::nodes::NodeStructOption;

        let edges = [(0usize, 1usize)];
        let nodes = NodeStructOption([Some(0), Some(1), None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Try to add a duplicate node
        let result = graph.add_node(0);

        // Should return error
        assert!(matches!(result, Err(GraphError::DuplicateNode(0))));

        // Original graph should be unchanged
        assert_eq!(graph.iter_nodes().unwrap().count(), 2);
    }

    #[test]
    fn test_add_node_with_option_container() {
        use crate::nodes::NodeStructOption;

        let edges = [(0usize, 1usize)];
        let nodes = NodeStructOption([Some(0), Some(1), None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add a new node to the empty slot
        graph.add_node(2).unwrap();

        // Verify all nodes exist
        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);

        // Verify new node has no outgoing edges
        assert_eq!(graph.outgoing_edges(2).unwrap().count(), 0);

        // Try to add another node when container is full
        let result = graph.add_node(3);
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_add_edge_success() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([None, None, None, None, None]); // Capacity for 5 edges
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), None, None]); // 3 nodes
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add edges between existing nodes
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert!(graph.add_edge(0, 2).is_ok());

        // Verify edges were added by checking edge iteration
        let edge_count = graph.iter_edges().unwrap().count();
        assert_eq!(edge_count, 3);

        // Verify specific edges exist
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2)]);
    }

    #[test]
    fn test_add_edge_invalid_nodes() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([None, None, None, None, None]);
        let nodes = NodeStructOption([Some(0), Some(1), None, None, None]); // Only nodes 0, 1
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Try to add edge with non-existent source node
        let result = graph.add_edge(2, 1);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(2))));

        // Try to add edge with non-existent destination node
        let result = graph.add_edge(0, 3);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Try to add edge with both nodes non-existent
        let result = graph.add_edge(5, 6);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(5))));
    }

    #[test]
    fn test_add_edge_capacity_exceeded() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([None, None]); // Capacity for only 2 edges
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), None, None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Add edges up to capacity
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());

        // Try to add one more edge (should exceed capacity)
        let result = graph.add_edge(0, 2);
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_remove_edge_success() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), Some((0, 2)), None, None]);
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), None, None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Verify initial edge count
        assert_eq!(graph.iter_edges().unwrap().count(), 3);

        // Remove an edge
        assert!(graph.remove_edge(1, 2).is_ok());

        // Verify edge was removed
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2)]);
    }

    #[test]
    fn test_remove_edge_not_found() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), None, None, None]);
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), None, None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Try to remove edge that doesn't exist
        let result = graph.remove_edge(0, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 2))));

        // Verify original edges are still there
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
    }

    #[test]
    fn test_remove_edge_with_nonexistent_nodes() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([Some((0, 1)), None, None, None, None]);
        let nodes = NodeStructOption([Some(0), Some(1), None, None, None]); // Only nodes 0, 1
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Try to remove edge involving non-existent nodes
        // This should fail with EdgeNotFound (not EdgeHasInvalidNode)
        // because we don't validate node existence in remove_edge
        let result = graph.remove_edge(2, 3);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(2, 3))));

        // Verify original edge is still there
        assert_eq!(graph.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_add_remove_edge_comprehensive() {
        use crate::edges::EdgeStructOption;
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let edges = EdgeStructOption([None, None, None, None, None]);
        let nodes = NodeStructOption([Some(0), Some(1), Some(2), Some(3), None]);
        let mut graph = EdgeNodeList::new(edges, nodes).unwrap();

        // Start with empty graph
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Add several edges
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert!(graph.add_edge(2, 3).is_ok());
        assert!(graph.add_edge(0, 3).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);

        // Remove some edges
        assert!(graph.remove_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 3);

        // Try to remove the same edge again (should fail)
        let result = graph.remove_edge(1, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(1, 2))));

        // Add the edge back
        assert!(graph.add_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);

        // Verify final edge set
        let mut edges = [(0usize, 0usize); 8];
        let sorted_edges = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(sorted_edges, &[(0, 1), (0, 3), (1, 2), (2, 3)]);
    }

    #[test]
    fn test_edge_node_list_from_graph() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create a source graph (map adjacency list with nodes 0, 1, 2)
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // 0 -> 1, 2
        dict.insert(1, [2, 0]).unwrap(); // 1 -> 2, 0
        dict.insert(2, [0, 1]).unwrap(); // 2 -> 0, 1
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeNodeList with capacity for nodes and edges
        let edge_node_graph: EdgeNodeList<
            usize,
            EdgeStructOption<8, usize>,
            NodeStructOption<4, usize>,
        > = EdgeNodeList::from_graph(&source).unwrap();

        // Verify nodes were copied correctly
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(edge_node_graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice.len(), 3); // Should have 3 nodes
        assert!(nodes_slice.contains(&0));
        assert!(nodes_slice.contains(&1));
        assert!(nodes_slice.contains(&2));

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(edge_node_graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 6); // Should have 6 edges total

        // Check that all expected edges are present
        assert!(edges_slice.contains(&(0, 1)));
        assert!(edges_slice.contains(&(0, 2)));
        assert!(edges_slice.contains(&(1, 2)));
        assert!(edges_slice.contains(&(1, 0)));
        assert!(edges_slice.contains(&(2, 0)));
        assert!(edges_slice.contains(&(2, 1)));
    }

    #[test]
    fn test_edge_node_list_from_graph_empty() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create an empty source graph
        let dict = Dictionary::<usize, [usize; 2], 8>::default();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeNodeList
        let edge_node_graph: EdgeNodeList<
            usize,
            EdgeStructOption<8, usize>,
            NodeStructOption<4, usize>,
        > = EdgeNodeList::from_graph(&source).unwrap();

        // Verify no nodes or edges
        assert_eq!(edge_node_graph.iter_nodes().unwrap().count(), 0);
        assert_eq!(edge_node_graph.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_edge_node_list_from_graph_node_capacity_exceeded() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create a source graph with 4 nodes but target has capacity for only 2
        let mut dict = Dictionary::<usize, [usize; 1], 8>::new();
        dict.insert(0, [1]).unwrap();
        dict.insert(1, [2]).unwrap();
        dict.insert(2, [3]).unwrap();
        dict.insert(3, [0]).unwrap();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Try to convert to EdgeNodeList with capacity for only 2 nodes
        let result: Result<
            EdgeNodeList<usize, EdgeStructOption<8, usize>, NodeStructOption<2, usize>>,
            _,
        > = EdgeNodeList::from_graph(&source);

        // Should fail because source has 4 nodes but target has capacity for only 2
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_edge_node_list_from_graph_edge_capacity_exceeded() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create a source graph with 6 edges but target has capacity for only 4
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // 0 -> 1, 2 (2 edges)
        dict.insert(1, [2, 0]).unwrap(); // 1 -> 2, 0 (2 edges)
        dict.insert(2, [0, 1]).unwrap(); // 2 -> 0, 1 (2 edges)
        let source = MapAdjacencyList::new_unchecked(dict);

        // Try to convert to EdgeNodeList with capacity for only 4 edges
        let result: Result<
            EdgeNodeList<usize, EdgeStructOption<4, usize>, NodeStructOption<4, usize>>,
            _,
        > = EdgeNodeList::from_graph(&source);

        // Should fail because source has 6 edges but target has capacity for only 4
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_edge_node_list_from_graph_single_node() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create a source graph with a single node and self-loop
        let mut dict = Dictionary::<usize, [usize; 1], 8>::new();
        dict.insert(42, [42]).unwrap(); // Node 42 -> 42 (self-loop)
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeNodeList
        let edge_node_graph: EdgeNodeList<
            usize,
            EdgeStructOption<8, usize>,
            NodeStructOption<4, usize>,
        > = EdgeNodeList::from_graph(&source).unwrap();

        // Verify single node
        let mut nodes = [0usize; 4];
        let nodes_slice = collect(edge_node_graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);

        // Verify self-loop edge
        let mut edges = [(0usize, 0usize); 4];
        let edges_slice = collect(edge_node_graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(42, 42)]);
    }

    #[test]
    fn test_edge_node_list_from_graph_chain() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Create a source graph forming a partial chain: 0 -> 1 -> 2
        // Node 3 will have a self-loop
        let mut dict = Dictionary::<usize, [usize; 1], 8>::new();
        dict.insert(0, [1]).unwrap(); // 0 -> 1
        dict.insert(1, [2]).unwrap(); // 1 -> 2
        dict.insert(2, [0]).unwrap(); // 2 -> 0 (cycle back)
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeNodeList
        let edge_node_graph: EdgeNodeList<
            usize,
            EdgeStructOption<8, usize>,
            NodeStructOption<8, usize>,
        > = EdgeNodeList::from_graph(&source).unwrap();

        // Verify all nodes
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(edge_node_graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);

        // Verify edges
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(edge_node_graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (1, 2), (2, 0)]);

        // Verify outgoing edges for each node
        let mut outgoing = [0usize; 2];
        let outgoing_slice = collect(edge_node_graph.outgoing_edges(0).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[1]);

        let outgoing_slice = collect(edge_node_graph.outgoing_edges(1).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[2]);

        let outgoing_slice = collect(edge_node_graph.outgoing_edges(2).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[0]);
    }
}
