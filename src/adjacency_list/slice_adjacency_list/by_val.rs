use crate::graph::{GraphError, GraphVal, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, SliceAdjacencyList};

impl<NI, E, C, T> GraphVal<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait + Copy,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes_contrainer.as_ref().iter().map(|(n, _)| *n))
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes_contrainer
            .as_ref()
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(n) contains_node for slice adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self
            .nodes_contrainer
            .as_ref()
            .iter()
            .any(|(n, _)| *n == node))
    }

    /// Optimized O(n + out-degree) outgoing_edges for slice adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Same pattern: use Option to unify iterator types, then flatten
        let edges_option = self
            .nodes_contrainer
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
    use crate::adjacency_list::slice_adjacency_list::SliceAdjacencyList;
    use crate::tests::array_collect;

    #[test]
    fn test_graphval_iter_nodes() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let len = array_collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(len, 3);
        assert_eq!(&nodes[..len], &[0, 1, 2]);
    }

    #[test]
    fn test_graphval_iter_edges() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut edges = [(0usize, 0usize); 8];
        let mut len = 0;
        for edge in graph.iter_edges().unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 6);
        assert_eq!(edges[0], (0, 1));
        assert_eq!(edges[1], (0, 2));
        assert_eq!(edges[2], (1, 2));
        assert_eq!(edges[3], (1, 0));
        assert_eq!(edges[4], (2, 0));
        assert_eq!(edges[5], (2, 0));
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
        let len = array_collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert_eq!(&edges[..len], &[1, 2]);

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let len = array_collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(len, 2);
        assert_eq!(&edges[..len], &[2, 0]);

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let len = array_collect(
            crate::graph::GraphVal::outgoing_edges(&graph, 2).unwrap(),
            &mut edges,
        );
        assert_eq!(len, 2);
        assert_eq!(&edges[..len], &[0, 0]);

        // Test non-existent node
        assert_eq!(
            crate::graph::GraphVal::outgoing_edges(&graph, 99)
                .unwrap()
                .count(),
            0
        );
    }

    #[test]
    fn test_graphval_empty_graph() {
        let adj_list_data: [(usize, [usize; 0]); 0] = [];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test empty node iteration
        assert_eq!(
            crate::graph::GraphVal::iter_nodes(&graph).unwrap().count(),
            0
        );

        // Test empty edge iteration
        assert_eq!(
            crate::graph::GraphVal::iter_edges(&graph).unwrap().count(),
            0
        );

        // Test contains_node on empty graph
        assert!(!crate::graph::GraphVal::contains_node(&graph, 0).unwrap());
        assert!(!crate::graph::GraphVal::contains_node(&graph, 42).unwrap());
    }

    #[test]
    fn test_graphval_self_loops() {
        let adj_list_data = [(0, [0, 1]), (1, [1, 1])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test self-loop edges
        let mut edges = [(0usize, 0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphVal::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 4);
        assert_eq!(edges[0], (0, 0));
        assert_eq!(edges[1], (0, 1));
        assert_eq!(edges[2], (1, 1));
        assert_eq!(edges[3], (1, 1));

        // Test outgoing edges with self-loops
        let mut edges = [0usize; 4];
        let len = array_collect(
            crate::graph::GraphVal::outgoing_edges(&graph, 0).unwrap(),
            &mut edges,
        );
        assert_eq!(len, 2);
        assert_eq!(&edges[..len], &[0, 1]);
    }

    #[test]
    fn test_graphval_single_node_no_edges() {
        let adj_list_data = [(42, [])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test single node
        let mut nodes = [0usize; 2];
        let len = array_collect(
            crate::graph::GraphVal::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(len, 1);
        assert_eq!(&nodes[..len], &[42]);

        // Test contains_node
        assert!(crate::graph::GraphVal::contains_node(&graph, 42).unwrap());
        assert!(!crate::graph::GraphVal::contains_node(&graph, 0).unwrap());

        // Test no edges
        assert_eq!(
            crate::graph::GraphVal::iter_edges(&graph).unwrap().count(),
            0
        );

        // Test no outgoing edges
        assert_eq!(
            crate::graph::GraphVal::outgoing_edges(&graph, 42)
                .unwrap()
                .count(),
            0
        );
    }

    #[test]
    fn test_graphval_multiple_nodes_same_target() {
        let adj_list_data = [(0, [1, 0]), (2, [1, 0]), (1, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test multiple edges pointing to same target
        let mut edges = [(0usize, 0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphVal::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 6);
        assert_eq!(edges[0], (0, 1));
        assert_eq!(edges[1], (0, 0));
        assert_eq!(edges[2], (2, 1));
        assert_eq!(edges[3], (2, 0));
        assert_eq!(edges[4], (1, 0));
        assert_eq!(edges[5], (1, 0));

        // Test contains_node for all nodes
        assert!(crate::graph::GraphVal::contains_node(&graph, 0).unwrap());
        assert!(crate::graph::GraphVal::contains_node(&graph, 1).unwrap());
        assert!(crate::graph::GraphVal::contains_node(&graph, 2).unwrap());
    }
}
