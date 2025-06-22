use crate::containers::maps::MapTrait;
use crate::conversions::FromGraph;
use crate::graph::{
    integrity_check, Graph, GraphError, GraphWithMutableEdges, GraphWithMutableNodes, NodeIndex,
};
use crate::nodes::{MutableNodes, NodesIterable};

pub struct MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    M: MapTrait<NI, E>,
{
    nodes: M,
    _phantom: core::marker::PhantomData<E>,
}

impl<NI, E, M> MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    M: MapTrait<NI, E>,
{
    /// Create new map adjacency list with validation
    ///
    /// This function validates that all edge destinations exist in the node set.
    /// Returns an error if any edge references a non-existent node.
    pub fn new(nodes: M) -> Result<Self, GraphError<NI>>
    where
        NI: Copy,
        Self: Graph<NI, Error = GraphError<NI>>,
    {
        let result = Self::new_unchecked(nodes);
        integrity_check::<NI, _>(&result)?;
        Ok(result)
    }

    pub fn new_unchecked(nodes: M) -> Self {
        Self {
            nodes,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<NI, E, M> FromGraph<NI, GraphError<NI>> for MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI> + MutableNodes<NI> + Default,
    M: MapTrait<NI, E> + Default,
{
    fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<NI>>
    where
        G: Graph<NI>,
        GraphError<NI>: From<G::Error>,
    {
        let mut nodes = M::new();
        for node in source_graph.iter_nodes()? {
            let mut outbound = E::default();
            for edge in source_graph.outgoing_edges(node)? {
                outbound.add(edge);
            }
            nodes
                .insert(node, outbound)
                .map_err(|_| GraphError::OutOfCapacity)?;
        }
        Ok(Self {
            nodes,
            _phantom: Default::default(),
        })
    }
}

impl<NI, E, M> MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI> + MutableNodes<NI> + Default,
    M: MapTrait<NI, E>,
{
}

impl<NI, E, M> Graph<NI> for MapAdjacencyList<NI, E, M>
where
    M: MapTrait<NI, E>,
    NI: NodeIndex + Eq + core::hash::Hash + Copy,
    E: NodesIterable<Node = NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.keys().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes
            .iter()
            .flat_map(|(n, e_container)| e_container.iter_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(1) contains_node for map adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.nodes.contains_key(&node))
    }

    /// Optimized O(out-degree) outgoing_edges for map adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // The key insight: use Option to unify the iterator types, then flatten
        let edges_option = self.nodes.get(&node).map(|edges| edges.iter_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}

impl<NI, E, M> GraphWithMutableNodes<NI> for MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex + Eq + core::hash::Hash + Copy,
    E: NodesIterable<Node = NI> + Default,
    M: MapTrait<NI, E>,
{
    fn add_node(&mut self, node: NI) -> Result<(), Self::Error> {
        if self.nodes.contains_key(&node) {
            return Err(GraphError::DuplicateNode(node));
        }
        let outbound = E::default();
        self.nodes
            .insert(node, outbound)
            .map_err(|_| GraphError::OutOfCapacity)?;
        Ok(())
    }

    fn remove_node(&mut self, node: NI) -> Result<(), Self::Error> {
        // Check if node exists
        if !self.nodes.contains_key(&node) {
            return Err(GraphError::NodeNotFound(node));
        }

        // Check if node has incoming edges
        if self.incoming_edges(node)?.next().is_some() {
            return Err(GraphError::NodeHasIncomingEdges(node));
        }

        // Remove the node (this automatically removes all its outgoing edges)
        self.nodes.remove(&node);
        Ok(())
    }
}

impl<NI, E, M> GraphWithMutableEdges<NI> for MapAdjacencyList<NI, E, M>
where
    NI: NodeIndex + Eq + core::hash::Hash + Copy + PartialEq,
    E: NodesIterable<Node = NI> + MutableNodes<NI>,
    M: MapTrait<NI, E>,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Validate both nodes exist with minimal lookups:
        // 1. Use get() for destination (read-only)
        // 2. Use get_mut() for source (gets mutable ref + validates existence)

        // Check destination exists first to preserve error precedence when both are invalid
        if self.nodes.get(&destination).is_none() {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Get mutable reference to source node's adjacency list (validates source exists)
        let source_edges = self
            .nodes
            .get_mut(&source)
            .ok_or(GraphError::EdgeHasInvalidNode(source))?;

        // Add the destination to the source's adjacency list
        source_edges
            .add(destination)
            .ok_or(GraphError::OutOfCapacity)?;

        Ok(())
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Get mutable reference to source node's adjacency list
        let source_edges = self
            .nodes
            .get_mut(&source)
            .ok_or(GraphError::EdgeNotFound(source, destination))?;

        // Remove the destination from the source's adjacency list
        source_edges
            .remove(destination)
            .ok_or(GraphError::EdgeNotFound(source, destination))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::graph::GraphWithMutableEdges;
    use crate::nodes::NodeStructOption;
    use crate::tests::{collect, collect_sorted};

    #[test]
    fn test_map_adjacency_list_new() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_sorted(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_map_adjacency_list_new_unchecked() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_sorted(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_map_adjacency_list_empty() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new(dict).unwrap();

        assert_eq!(graph.iter_nodes().unwrap().count(), 0);
    }

    #[test]
    fn test_map_adjacency_list_single_node() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []).unwrap();

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 2];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);
    }

    #[test]
    fn test_graph_iter_nodes() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[2, 0, 1]);
    }

    #[test]
    fn test_graph_iter_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 6);
        assert_eq!(
            edges_slice,
            &[(2, 0), (2, 0), (0, 1), (0, 2), (1, 2), (1, 0)]
        );
    }

    #[test]
    fn test_graph_contains_node() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert!(!graph.contains_node(3).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graph_outgoing_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

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
        assert_eq!(edges_slice, &[0, 0]); // Both edges go to node 0

        // Test non-existent node
        assert_eq!(graph.outgoing_edges(99).unwrap().count(), 0);
    }

    #[test]
    fn test_graph_empty_graph() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test empty node iteration
        assert_eq!(graph.iter_nodes().unwrap().count(), 0);

        // Test empty edge iteration
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test contains_node on empty graph
        assert!(!graph.contains_node(0).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graph_single_node_no_edges() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

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
    fn test_graph_self_loops() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [0, 1]).unwrap();
        dict.insert(1, [1, 1]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test self-loop edges
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 0), (0, 1), (1, 1), (1, 1)]);

        // Test outgoing edges with self-loops
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 1]);
    }

    #[test]
    fn test_graph_multiple_nodes_same_target() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 1]).unwrap();
        dict.insert(2, [1, 0]).unwrap();
        dict.insert(1, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test multiple edges pointing to same target
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(0, 1), (0, 1), (1, 0), (1, 0), (2, 0), (2, 1)]
        );
    }

    #[test]
    fn test_map_adjacency_list_not_all_edges() {
        let mut dict = Dictionary::<_, NodeStructOption<3, _>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1), Some(2), None]))
            .unwrap();
        dict.insert(1, NodeStructOption([Some(2), Some(0), None]))
            .unwrap();
        dict.insert(2, NodeStructOption([Some(0), None, None]))
            .unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(2, 0), (0, 1), (0, 2), (1, 2), (1, 0)]);
    }

    #[test]
    fn test_map_adjacency_list_from_graph() {
        let src_graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);
        let adjlist =
            MapAdjacencyList::<_, _, Dictionary<_, NodeStructOption<5, _>, 5>>::from_graph(
                &src_graph,
            )
            .unwrap();

        let mut nodes = [0usize; 8];
        let node_slice = collect_sorted(adjlist.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(node_slice, &[0usize, 1, 2, 3]);

        let mut edges = [(0usize, 0usize); 8];
        let edge_slice = collect_sorted(adjlist.iter_edges().unwrap(), &mut edges);
        assert_eq!(edge_slice, &[(0, 1), (0, 2), (1, 3), (2, 3)]);

        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(0).unwrap(), &mut nodes),
            &[1, 2]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(1).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(2).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(3).unwrap(), &mut nodes),
            &[]
        );
    }

    #[test]
    fn test_add_node_to_empty_graph() {
        let dict = Dictionary::<usize, NodeStructOption<2, usize>, 5>::new();
        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Add a node to empty graph
        graph.add_node(42).unwrap();

        // Verify the node was added
        assert!(graph.contains_node(42).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 1);
        assert_eq!(graph.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_to_existing_graph() {
        let mut dict = Dictionary::<usize, NodeStructOption<2, usize>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1), None])).unwrap();
        dict.insert(1, NodeStructOption([None, None])).unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Add a new node
        graph.add_node(2).unwrap();

        // Verify all nodes exist
        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);

        // Verify new node has no outgoing edges
        assert_eq!(graph.outgoing_edges(2).unwrap().count(), 0);

        // Verify existing edges are preserved
        let mut edges = [0usize; 2];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1]);
    }

    #[test]
    fn test_add_duplicate_node() {
        let mut dict = Dictionary::<usize, NodeStructOption<1, usize>, 5>::new();
        dict.insert(0, NodeStructOption([None])).unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Try to add duplicate node
        let result = graph.add_node(0);

        // Should return error
        assert!(matches!(result, Err(GraphError::DuplicateNode(0))));

        // Original graph should be unchanged
        assert_eq!(graph.iter_nodes().unwrap().count(), 1);
    }

    #[test]
    fn test_add_node_capacity_exceeded() {
        // Create a dictionary with capacity for only 2 nodes
        let mut dict = Dictionary::<usize, NodeStructOption<1, usize>, 2>::new();
        dict.insert(0, NodeStructOption([None])).unwrap();
        dict.insert(1, NodeStructOption([None])).unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Try to add a third node (should exceed capacity)
        let result = graph.add_node(2);

        // Should return capacity error
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));

        // Original graph should be unchanged
        assert_eq!(graph.iter_nodes().unwrap().count(), 2);
    }

    #[test]
    fn test_add_multiple_nodes() {
        let dict = Dictionary::<usize, NodeStructOption<3, usize>, 10>::new();
        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Add multiple nodes
        graph.add_node(10).unwrap();
        graph.add_node(20).unwrap();
        graph.add_node(30).unwrap();

        // Verify all nodes were added
        assert!(graph.contains_node(10).unwrap());
        assert!(graph.contains_node(20).unwrap());
        assert!(graph.contains_node(30).unwrap());
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);

        // Verify no edges exist between nodes
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Verify each node has no outgoing edges
        assert_eq!(graph.outgoing_edges(10).unwrap().count(), 0);
        assert_eq!(graph.outgoing_edges(20).unwrap().count(), 0);
        assert_eq!(graph.outgoing_edges(30).unwrap().count(), 0);
    }

    #[test]
    fn test_add_edge_success() {
        let mut dict = Dictionary::<usize, NodeStructOption<3, usize>, 5>::new();
        dict.insert(0, NodeStructOption([None, None, None]))
            .unwrap(); // Empty adjacency list
        dict.insert(1, NodeStructOption([None, None, None]))
            .unwrap();
        dict.insert(2, NodeStructOption([None, None, None]))
            .unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

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
        let mut dict = Dictionary::<usize, NodeStructOption<2, usize>, 5>::new();
        dict.insert(0, NodeStructOption([None, None])).unwrap();
        dict.insert(1, NodeStructOption([None, None])).unwrap(); // Only nodes 0, 1

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Try to add edge with non-existent source node
        let result = graph.add_edge(2, 1);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(2))));

        // Try to add edge with non-existent destination node
        let result = graph.add_edge(0, 3);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Try to add edge with both nodes non-existent
        let result = graph.add_edge(5, 6);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(6)))); // Destination checked first in optimized version
    }

    #[test]
    fn test_add_edge_capacity_exceeded() {
        let mut dict = Dictionary::<usize, NodeStructOption<2, usize>, 5>::new();
        dict.insert(0, NodeStructOption([None, None])).unwrap(); // Capacity for only 2 edges
        dict.insert(1, NodeStructOption([None, None])).unwrap();
        dict.insert(2, NodeStructOption([None, None])).unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Add edges up to capacity for node 0
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(0, 2).is_ok());

        // Try to add one more edge from node 0 (should exceed capacity)
        let result = graph.add_edge(0, 1); // Try to add duplicate or different edge
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_remove_edge_success() {
        let mut dict = Dictionary::<usize, NodeStructOption<3, usize>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1), Some(2), None]))
            .unwrap();
        dict.insert(1, NodeStructOption([Some(2), None, None]))
            .unwrap();
        dict.insert(2, NodeStructOption([None, None, None]))
            .unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Verify initial edge count
        assert_eq!(graph.iter_edges().unwrap().count(), 3);

        // Remove an edge
        assert!(graph.remove_edge(0, 1).is_ok());

        // Verify edge was removed
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 2), (1, 2)]);
    }

    #[test]
    fn test_remove_edge_not_found() {
        let mut dict = Dictionary::<usize, NodeStructOption<2, usize>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1), None])).unwrap();
        dict.insert(1, NodeStructOption([None, None])).unwrap();
        dict.insert(2, NodeStructOption([None, None])).unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Try to remove edge that doesn't exist
        let result = graph.remove_edge(0, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 2))));

        // Verify original edges are still there
        assert_eq!(graph.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_remove_edge_with_nonexistent_nodes() {
        let mut dict = Dictionary::<usize, NodeStructOption<1, usize>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1)])).unwrap();
        dict.insert(1, NodeStructOption([None])).unwrap(); // Only nodes 0, 1

        let mut graph = MapAdjacencyList::new(dict).unwrap();

        // Try to remove edge involving non-existent source node
        let result = graph.remove_edge(2, 3);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(2, 3))));

        // Verify original edge is still there
        assert_eq!(graph.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_map_adjacency_list_from_graph_trait() {
        let src_graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);
        let adjlist =
            MapAdjacencyList::<_, _, Dictionary<_, NodeStructOption<5, _>, 5>>::from_graph(
                &src_graph,
            )
            .unwrap();

        let mut nodes = [0usize; 8];
        let node_slice = collect_sorted(adjlist.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(node_slice, &[0usize, 1, 2, 3]);

        let mut edges = [(0usize, 0usize); 8];
        let edge_slice = collect_sorted(adjlist.iter_edges().unwrap(), &mut edges);
        assert_eq!(edge_slice, &[(0, 1), (0, 2), (1, 3), (2, 3)]);

        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(0).unwrap(), &mut nodes),
            &[1, 2]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(1).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(2).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(3).unwrap(), &mut nodes),
            &[]
        );
    }

    #[test]
    fn test_add_remove_edge_comprehensive() {
        let mut dict = Dictionary::<usize, NodeStructOption<5, usize>, 5>::new();
        dict.insert(0, NodeStructOption([None, None, None, None, None]))
            .unwrap();
        dict.insert(1, NodeStructOption([None, None, None, None, None]))
            .unwrap();
        dict.insert(2, NodeStructOption([None, None, None, None, None]))
            .unwrap();
        dict.insert(3, NodeStructOption([None, None, None, None, None]))
            .unwrap();

        let mut graph = MapAdjacencyList::new(dict).unwrap();

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
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 3), (1, 2), (2, 3)]);
    }
}
