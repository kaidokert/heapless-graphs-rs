use crate::containers::maps::MapTrait;
use crate::graph::{GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, MapAdjacencyList};

impl<M, NI, E, C> GraphRef<NI> for MapAdjacencyList<M, NI, E, C>
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::tests::array_collect_ref;

    #[test]
    fn test_graphref_iter_nodes() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let len = array_collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(len, 3);
        // Note: order may vary with map implementation
        assert!(nodes[..len].contains(&0));
        assert!(nodes[..len].contains(&1));
        assert!(nodes[..len].contains(&2));
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

        // Check that all expected edges are present (order may vary)
        assert!(edge_pairs[..len].contains(&(0, 1)));
        assert!(edge_pairs[..len].contains(&(0, 2)));
        assert!(edge_pairs[..len].contains(&(1, 2)));
        assert!(edge_pairs[..len].contains(&(1, 0)));
        assert!(edge_pairs[..len].contains(&(2, 0)));
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
        let len = array_collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(len, 1);
        assert_eq!(&nodes[..len], &[42]);

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

        // Check that all expected edges are present (order may vary)
        assert!(edge_pairs[..len].contains(&(0, 0)));
        assert!(edge_pairs[..len].contains(&(0, 1)));
        assert!(edge_pairs[..len].contains(&(1, 1)));
        // Should have two (1,1) edges
        assert_eq!(
            edge_pairs[..len].iter().filter(|&&e| e == (1, 1)).count(),
            2
        );
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

        // Check that all expected edges are present
        assert!(edge_pairs[..len].contains(&(0, 1)));
        assert!(edge_pairs[..len].contains(&(2, 1)));
        assert!(edge_pairs[..len].contains(&(2, 0)));
        assert!(edge_pairs[..len].contains(&(1, 0)));
        // Should have two edges from 0->1 and two from 1->0
        assert_eq!(
            edge_pairs[..len].iter().filter(|&&e| e == (0, 1)).count(),
            2
        );
        assert_eq!(
            edge_pairs[..len].iter().filter(|&&e| e == (1, 0)).count(),
            2
        );
    }
}
