use crate::graph::{integrity_check, Graph, GraphError, NodeIndex};
use crate::nodes::NodesIterable;

use super::outgoing_nodes::AsOutgoingNodes;

pub struct SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    nodes_container: T,
    _phantom: core::marker::PhantomData<(E, C)>,
}

impl<NI, E, C, T> SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
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

impl<NI, E, C, T> Graph<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
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
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
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
            .map(|(_, node_data)| node_data.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten().copied())
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
}
