use crate::graph::{GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::{super::outgoing_nodes::AsOutgoingNodes, SliceAdjacencyList};

impl<NI, E, C, T> GraphRef<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.nodes_container.as_ref().iter().map(|(n, _)| n))
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self
            .nodes_container
            .as_ref()
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
        let edges_option = self
            .nodes_container
            .as_ref()
            .iter()
            .find(|(n, _)| *n == *node)
            .map(|(_, node_data)| node_data.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::slice_adjacency_list::SliceAdjacencyList;
    use crate::tests::collect_ref;

    #[test]
    fn test_graphref_iter_nodes() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_ref(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_graphref_iter_edges() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in graph.iter_edges().unwrap() {
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
            &[(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 0)]
        );
    }

    #[test]
    fn test_graphref_empty_graph() {
        let adj_list_data: [(usize, [usize; 0]); 0] = [];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        assert_eq!(graph.iter_nodes().unwrap().count(), 0);
        assert_eq!(graph.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_graphref_single_node_no_edges() {
        let adj_list_data = [(42, [])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 2];
        let nodes_slice = collect_ref(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);

        assert_eq!(graph.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_graphref_self_loops() {
        let adj_list_data = [(0, [0, 1]), (1, [1, 1])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in graph.iter_edges().unwrap() {
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
    fn test_graphref_outgoing_edges() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        // Test node 0 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(graph.outgoing_edges(&0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1, 2]);

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(graph.outgoing_edges(&1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2, 0]);

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_ref(graph.outgoing_edges(&2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 0]);

        // Test non-existent node
        assert_eq!(graph.outgoing_edges(&99).unwrap().count(), 0);
    }
}
