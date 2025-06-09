use crate::containers::maps::MapTrait;
use crate::graph::{GraphError, GraphVal, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, MapAdjacencyList};

impl<M, NI, E, C> GraphVal<NI> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: NodeIndexTrait + Eq + core::hash::Hash + Copy,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.keys().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(1) contains_node for map adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.nodes.contains_key(&node))
    }

    /// Optimized O(out-degree) outgoing_edges for map adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // The key insight: use Option to unify the iterator types, then flatten
        let edges_option = self.nodes.get(&node).map(|edges| edges.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::tests::array_collect;

    #[test]
    fn test_graphval_iter_nodes() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let len = array_collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(len, 3);
        // Note: order may vary with map implementation
        assert!(nodes[..len].contains(&0));
        assert!(nodes[..len].contains(&1));
        assert!(nodes[..len].contains(&2));
    }

    #[test]
    fn test_graphval_iter_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(0usize, 0usize); 8];
        let len = array_collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(len, 6);

        // Check that all expected edges are present (order may vary)
        assert!(edges[..len].contains(&(0, 1)));
        assert!(edges[..len].contains(&(0, 2)));
        assert!(edges[..len].contains(&(1, 2)));
        assert!(edges[..len].contains(&(1, 0)));
        assert!(edges[..len].contains(&(2, 0)));
    }

    #[test]
    fn test_graphval_contains_node() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert!(!graph.contains_node(3).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graphval_outgoing_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test node 0 outgoing edges
        let mut edges = [0usize; 4];
        let len = array_collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert!(edges[..len].contains(&1));
        assert!(edges[..len].contains(&2));

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let len = array_collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert!(edges[..len].contains(&2));
        assert!(edges[..len].contains(&0));

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let len = array_collect(graph.outgoing_edges(2).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert_eq!(&edges[..len], &[0, 0]); // Both edges go to node 0

        // Test non-existent node
        assert_eq!(graph.outgoing_edges(99).unwrap().count(), 0);
    }

    #[test]
    fn test_graphval_empty_graph() {
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
    fn test_graphval_single_node_no_edges() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []);

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test single node
        let mut nodes = [0usize; 2];
        let len = array_collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(len, 1);
        assert_eq!(&nodes[..len], &[42]);

        // Test contains_node
        assert!(graph.contains_node(42).unwrap());
        assert!(!graph.contains_node(0).unwrap());

        // Test no edges
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test no outgoing edges
        assert_eq!(graph.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_graphval_self_loops() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [0, 1]);
        dict.insert(1, [1, 1]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test self-loop edges
        let mut edges = [(0usize, 0usize); 8];
        let len = array_collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(len, 4);

        // Check that all expected edges are present (order may vary)
        assert!(edges[..len].contains(&(0, 0)));
        assert!(edges[..len].contains(&(0, 1)));
        assert!(edges[..len].contains(&(1, 1)));
        // Should have two (1,1) edges
        assert_eq!(edges[..len].iter().filter(|&&e| e == (1, 1)).count(), 2);

        // Test outgoing edges with self-loops
        let mut edges = [0usize; 4];
        let len = array_collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert!(edges[..len].contains(&0));
        assert!(edges[..len].contains(&1));
    }

    #[test]
    fn test_graphval_multiple_nodes_same_target() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 1]);
        dict.insert(2, [1, 0]);
        dict.insert(1, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test multiple edges pointing to same target
        let mut edges = [(0usize, 0usize); 8];
        let len = array_collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(len, 6);

        // Check that all expected edges are present
        assert!(edges[..len].contains(&(0, 1)));
        assert!(edges[..len].contains(&(2, 1)));
        assert!(edges[..len].contains(&(2, 0)));
        assert!(edges[..len].contains(&(1, 0)));
        // Should have two edges from 0->1 and two from 1->0
        assert_eq!(edges[..len].iter().filter(|&&e| e == (0, 1)).count(), 2);
        assert_eq!(edges[..len].iter().filter(|&&e| e == (1, 0)).count(), 2);
    }
}
