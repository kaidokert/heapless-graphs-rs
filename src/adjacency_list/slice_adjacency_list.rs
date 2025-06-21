use crate::graph::{integrity_check, Graph, GraphError, GraphWithMutableEdges, NodeIndex};
use crate::nodes::{MutableNodes, NodesIterable};

pub struct SliceAdjacencyList<NI, E, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    T: AsRef<[(NI, E)]>,
{
    nodes_container: T,
    _phantom: core::marker::PhantomData<E>,
}

impl<NI, E, T> SliceAdjacencyList<NI, E, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    T: AsRef<[(NI, E)]>,
{
    /// Create new slice adjacency list with validation
    ///
    /// This function validates that all edge destinations exist in the node set.
    /// Returns an error if any edge references a non-existent node.
    pub fn new(nodes_container: T) -> Result<Self, GraphError<NI>>
    where
        NI: Copy,
        Self: Graph<NI, Error = GraphError<NI>>,
    {
        let result = Self::new_unchecked(nodes_container);
        integrity_check::<NI, _>(&result)?;
        Ok(result)
    }

    pub fn new_unchecked(nodes_container: T) -> Self {
        Self {
            nodes_container,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<NI, E, T> Graph<NI> for SliceAdjacencyList<NI, E, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    T: AsRef<[(NI, E)]>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes_container.as_ref().iter().map(|(n, _)| *n))
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes_container
            .as_ref()
            .iter()
            .flat_map(|(n, e_container)| e_container.iter_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(n) contains_node for slice adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self
            .nodes_container
            .as_ref()
            .iter()
            .any(|(n, _)| *n == node))
    }

    /// Optimized O(n + out-degree) outgoing_edges for slice adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Same pattern: use Option to unify iterator types, then flatten
        let edges_option = self
            .nodes_container
            .as_ref()
            .iter()
            .find(|(n, _)| *n == node)
            .map(|(_, node_data)| node_data.iter_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}

impl<NI, E, T> GraphWithMutableEdges<NI> for SliceAdjacencyList<NI, E, T>
where
    NI: NodeIndex + PartialEq,
    E: NodesIterable<Node = NI> + MutableNodes<NI>,
    T: AsRef<[(NI, E)]> + AsMut<[(NI, E)]>,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // First, validate that both nodes exist in the graph
        if !self.contains_node(source)? {
            return Err(GraphError::EdgeHasInvalidNode(source));
        }
        if !self.contains_node(destination)? {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Find the source node's edge container and add the destination
        let nodes = self.nodes_container.as_mut();
        for (node_id, edge_container) in nodes.iter_mut() {
            if *node_id == source {
                return edge_container
                    .add(destination)
                    .map(|_| ())
                    .ok_or(GraphError::OutOfCapacity);
            }
        }

        // This should never happen since we validated the source node exists
        Err(GraphError::EdgeHasInvalidNode(source))
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Find the source node's edge container and remove the destination
        let nodes = self.nodes_container.as_mut();
        for (node_id, edge_container) in nodes.iter_mut() {
            if *node_id == source {
                return edge_container
                    .remove(destination)
                    .map(|_| ())
                    .ok_or(GraphError::EdgeNotFound(source, destination));
            }
        }

        // Source node doesn't exist, so edge can't exist either
        Err(GraphError::EdgeNotFound(source, destination))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::collect;

    #[test]
    fn test_slice_adjacency_list_new() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_slice_adjacency_list_new_unchecked() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_slice_adjacency_list_with_empty_graph() {
        let adj_list_data: [(usize, [usize; 0]); 0] = [];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        assert_eq!(graph.iter_nodes().unwrap().count(), 0);
    }

    #[test]
    fn test_slice_adjacency_list_single_node() {
        let adj_list_data = [(42, [])];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        let mut nodes = [0usize; 2];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);
    }

    #[test]
    fn test_graphval_iter_nodes() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_graphval_iter_edges() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 6);
        assert_eq!(
            edges_slice,
            &[(0, 1), (0, 2), (1, 2), (1, 0), (2, 0), (2, 0)]
        );
    }

    #[test]
    fn test_graphval_contains_node() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert!(!graph.contains_node(3).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graphval_outgoing_edges() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test node 0 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1, 2]);

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2, 0]);

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 0]);

        // Test non-existent node
        assert_eq!(graph.outgoing_edges(99).unwrap().count(), 0);
    }

    #[test]
    fn test_graphval_empty_graph() {
        let adj_list_data: [(usize, [usize; 0]); 0] = [];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test empty node iteration
        assert_eq!(graph.iter_nodes().unwrap().count(), 0);

        // Test empty edge iteration
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test contains_node on empty graph
        assert!(!graph.contains_node(0).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graphval_self_loops() {
        let adj_list_data = [(0, [0, 1]), (1, [1, 1])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test self-loop edges
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 0), (0, 1), (1, 1), (1, 1)]);

        // Test outgoing edges with self-loops
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 1]);
    }

    #[test]
    fn test_graphval_single_node_no_edges() {
        let adj_list_data = [(42, [])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test single node
        let mut nodes = [0usize; 2];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);

        // Test contains_node
        assert!(graph.contains_node(42).unwrap());
        assert!(!graph.contains_node(0).unwrap());

        // Test no edges
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test no outgoing edges
        assert_eq!(graph.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_graphval_multiple_nodes_same_target() {
        let adj_list_data = [(0, [1, 0]), (2, [1, 0]), (1, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test multiple edges pointing to same target
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(0, 1), (0, 0), (2, 1), (2, 0), (1, 0), (1, 0)]
        );

        // Test contains_node for all nodes
        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
    }

    #[test]
    fn test_slice_adjacency_list_with_node_struct_option() {
        use crate::nodes::NodeStructOption;

        // Create adjacency list with NodeStructOption as edge containers
        let adj_list_data = [
            (0, NodeStructOption([Some(1), Some(2), None])), // Node 0 -> [1, 2]
            (1, NodeStructOption([Some(2), None, None])),    // Node 1 -> [2]
            (2, NodeStructOption([Some(0), None, None])),    // Node 2 -> [0]
        ];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test nodes iteration
        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);

        // Test edges iteration
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2), (2, 0)]);

        // Test outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1, 2]);

        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2]);

        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0]);
    }

    #[test]
    fn test_slice_adjacency_list_option_based_edges() {
        use crate::edges::EdgeStructOption;
        use crate::nodes::NodeStructOption;

        // Test if SliceAdjacencyList can work with Option-based edge structures
        // This explores current capabilities before implementing GraphWithMutableEdges
        let _edge_data =
            EdgeStructOption([Some((0, 1)), Some((0, 2)), Some((1, 2)), Some((2, 0)), None]);

        // Try to create adjacency list representation from edge data
        // Note: This is conceptually different from our design - edges are stored as a list,
        // not as adjacency lists per node. This test explores the boundary of current capabilities.

        // Since SliceAdjacencyList expects [(NI, E)] where E: NodesIterable, we can't directly
        // use EdgeStructOption as the container type. We need per-node edge lists.

        // Instead, let's test a mixed approach with some nodes having Option-based edge lists
        let adj_list_data = [
            (0, NodeStructOption([Some(1), Some(2), None, None])), // Node 0 -> [1, 2]
            (1, NodeStructOption([Some(2), None, None, None])),    // Node 1 -> [2]
            (2, NodeStructOption([Some(0), None, None, None])),    // Node 2 -> [0]
        ];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Verify this works with expanded capacity for future edge additions
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2), (2, 0)]);

        // This test demonstrates that SliceAdjacencyList already supports Option-based
        // edge containers through NodeStructOption, providing a foundation for future
        // mutable edge operations within fixed capacity constraints.
    }

    #[test]
    fn test_mutable_edges_add_edge_success() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([Some(1), None, None, None])), // Node 0 -> [1], capacity for 3 more
            (1, NodeStructOption([None, None, None, None])),    // Node 1 -> [], capacity for 4
            (2, NodeStructOption([Some(0), None, None, None])), // Node 2 -> [0], capacity for 3 more
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Add new edges
        assert!(graph.add_edge(0, 2).is_ok()); // 0 -> [1, 2]
        assert!(graph.add_edge(1, 0).is_ok()); // 1 -> [0]
        assert!(graph.add_edge(1, 2).is_ok()); // 1 -> [0, 2]

        // Verify edges were added
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 5);
        assert!(edges_slice.contains(&(0, 1))); // Original
        assert!(edges_slice.contains(&(2, 0))); // Original
        assert!(edges_slice.contains(&(0, 2))); // Added
        assert!(edges_slice.contains(&(1, 0))); // Added
        assert!(edges_slice.contains(&(1, 2))); // Added
    }

    #[test]
    fn test_mutable_edges_add_edge_invalid_nodes() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([Some(1), None, None])),
            (1, NodeStructOption([None, None, None])),
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Try to add edge with non-existent source
        let result = graph.add_edge(99, 1);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(99))));

        // Try to add edge with non-existent destination
        let result = graph.add_edge(0, 99);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(99))));

        // Try to add edge with both nodes non-existent
        let result = graph.add_edge(98, 99);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(98))));
    }

    #[test]
    fn test_mutable_edges_add_edge_capacity_exceeded() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([Some(1), Some(2)])), // Node 0 at full capacity
            (1, NodeStructOption([None, None])),
            (2, NodeStructOption([None, None])),
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Try to add edge when source node's edge container is full
        let result = graph.add_edge(0, 1); // 0 already has [1, 2] - no capacity
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));

        // Should still be able to add edge from node with capacity
        assert!(graph.add_edge(1, 0).is_ok());
    }

    #[test]
    fn test_mutable_edges_remove_edge_success() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([Some(1), Some(2), None])), // Node 0 -> [1, 2]
            (1, NodeStructOption([Some(2), Some(0), None])), // Node 1 -> [2, 0]
            (2, NodeStructOption([Some(0), None, None])),    // Node 2 -> [0]
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Initial edge count
        assert_eq!(graph.iter_edges().unwrap().count(), 5);

        // Remove edges
        assert!(graph.remove_edge(0, 1).is_ok()); // 0 -> [2]
        assert!(graph.remove_edge(1, 0).is_ok()); // 1 -> [2]

        // Verify edges were removed
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 3);
        assert!(edges_slice.contains(&(0, 2))); // Remaining
        assert!(edges_slice.contains(&(1, 2))); // Remaining
        assert!(edges_slice.contains(&(2, 0))); // Remaining
        assert!(!edges_slice.contains(&(0, 1))); // Removed
        assert!(!edges_slice.contains(&(1, 0))); // Removed
    }

    #[test]
    fn test_mutable_edges_remove_edge_not_found() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([Some(1), None, None])), // Node 0 -> [1]
            (1, NodeStructOption([Some(2), None, None])), // Node 1 -> [2]
            (2, NodeStructOption([None, None, None])),    // Node 2 -> []
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Try to remove edge that doesn't exist
        let result = graph.remove_edge(0, 2);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 2))));

        // Try to remove edge from node with no outgoing edges
        let result = graph.remove_edge(2, 0);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeNotFound(2, 0))));

        // Try to remove edge with non-existent source node
        let result = graph.remove_edge(99, 1);
        assert!(result.is_err());
        assert!(matches!(result, Err(GraphError::EdgeNotFound(99, 1))));
    }

    #[test]
    fn test_mutable_edges_add_remove_comprehensive() {
        use crate::graph::GraphWithMutableEdges;
        use crate::nodes::NodeStructOption;

        let adj_list_data = [
            (0, NodeStructOption([None, None, None, None])), // Empty with capacity
            (1, NodeStructOption([None, None, None, None])), // Empty with capacity
            (2, NodeStructOption([None, None, None, None])), // Empty with capacity
        ];
        let mut graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Start with empty graph
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Add edges
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(0, 2).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert!(graph.add_edge(2, 0).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);

        // Remove some edges
        assert!(graph.remove_edge(0, 1).is_ok());
        assert!(graph.remove_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 2);

        // Add them back
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);

        // Verify final state
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert!(edges_slice.contains(&(0, 2)));
        assert!(edges_slice.contains(&(2, 0)));
        assert!(edges_slice.contains(&(0, 1))); // Re-added
        assert!(edges_slice.contains(&(1, 2))); // Re-added
    }
}
