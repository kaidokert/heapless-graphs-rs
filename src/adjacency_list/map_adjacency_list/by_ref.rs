use crate::containers::maps::MapTrait;
use crate::graph::{GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, MapAdjacencyList};

impl<NI, E, C, M> GraphRef<NI> for MapAdjacencyList<NI, E, C, M>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.nodes.keys())
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self
            .nodes
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (n, m))))
    }

    fn outgoing_edges<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        let edges_option = self.nodes.get(node).map(|edges| edges.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::tests::collect_ref;

    #[test]
    fn test_graphref_iter_nodes() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        // Note: order may vary with map implementation
        nodes_slice.sort_unstable();
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_graphref_iter_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphRef::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 6);

        // Convert to a more testable format
        let mut edge_pairs = [(0usize, 0usize); 8];
        for i in 0..len {
            edge_pairs[i] = (*edges[i].0, *edges[i].1);
        }
        edge_pairs[..len].sort_unstable();
        assert_eq!(
            &edge_pairs[..len],
            &[(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 0)]
        );
    }

    #[test]
    fn test_graphref_empty_graph() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new_unchecked(dict);

        assert_eq!(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap().count(),
            0
        );
        assert_eq!(
            crate::graph::GraphRef::iter_edges(&graph).unwrap().count(),
            0
        );
    }

    #[test]
    fn test_graphref_single_node_no_edges() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 2];
        let nodes_slice = collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(nodes_slice, &[42]);

        assert_eq!(
            crate::graph::GraphRef::iter_edges(&graph).unwrap().count(),
            0
        );
    }

    #[test]
    fn test_graphref_self_loops() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [0, 1]);
        dict.insert(1, [1, 1]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphRef::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 4);

        // Convert to testable format
        let mut edge_pairs = [(0usize, 0usize); 8];
        for i in 0..len {
            edge_pairs[i] = (*edges[i].0, *edges[i].1);
        }
        edge_pairs[..len].sort_unstable();
        assert_eq!(&edge_pairs[..len], &[(0, 0), (0, 1), (1, 1), (1, 1)]);
    }

    #[test]
    fn test_graphref_multiple_nodes_same_target() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 1]);
        dict.insert(2, [1, 0]);
        dict.insert(1, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphRef::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 6);

        // Convert to testable format
        let mut edge_pairs = [(0usize, 0usize); 8];
        for i in 0..len {
            edge_pairs[i] = (*edges[i].0, *edges[i].1);
        }
        edge_pairs[..len].sort_unstable();
        assert_eq!(
            &edge_pairs[..len],
            &[(0, 1), (0, 1), (1, 0), (1, 0), (2, 0), (2, 1)]
        );
    }

    #[test]
    fn test_graphref_outgoing_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test node 0 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(
            crate::graph::GraphRef::outgoing_edges(&graph, &0).unwrap(),
            &mut edges,
        );
        assert_eq!(edges_slice, &[1, 2]);

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(
            crate::graph::GraphRef::outgoing_edges(&graph, &1).unwrap(),
            &mut edges,
        );
        assert_eq!(edges_slice, &[2, 0]);

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(
            crate::graph::GraphRef::outgoing_edges(&graph, &2).unwrap(),
            &mut edges,
        );
        assert_eq!(edges_slice, &[0, 0]); // Both edges go to node 0

        // Test non-existent node
        assert_eq!(
            crate::graph::GraphRef::outgoing_edges(&graph, &99)
                .unwrap()
                .count(),
            0
        );
    }
}
