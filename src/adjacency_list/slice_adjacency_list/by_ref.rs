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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::slice_adjacency_list::SliceAdjacencyList;

    #[test]
    fn test_graphref_iter_nodes() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let mut len = 0;
        for node in graph.iter_nodes().unwrap() {
            nodes[len] = *node;
            len += 1;
        }
        assert_eq!(len, 3);
        assert_eq!(&nodes[..len], &[0, 1, 2]);
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
        assert_eq!(edges[0], (&0, &1));
        assert_eq!(edges[1], (&0, &2));
        assert_eq!(edges[2], (&1, &2));
        assert_eq!(edges[3], (&1, &0));
        assert_eq!(edges[4], (&2, &0));
        assert_eq!(edges[5], (&2, &0));
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
        let mut len = 0;
        for node in graph.iter_nodes().unwrap() {
            nodes[len] = *node;
            len += 1;
        }
        assert_eq!(len, 1);
        assert_eq!(&nodes[..len], &[42]);

        assert_eq!(graph.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_graphref_self_loops() {
        let adj_list_data = [(0, [0, 1]), (1, [1, 1])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut edges = [(&0usize, &0usize); 8];
        let mut len = 0;
        for edge in crate::graph::GraphRef::iter_edges(&graph).unwrap() {
            edges[len] = edge;
            len += 1;
        }
        assert_eq!(len, 4);
        assert_eq!(edges[0], (&0, &0));
        assert_eq!(edges[1], (&0, &1));
        assert_eq!(edges[2], (&1, &1));
        assert_eq!(edges[3], (&1, &1));
    }
}
