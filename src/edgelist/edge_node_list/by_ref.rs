use crate::{
    edges::EdgesIterable,
    graph::{GraphError, GraphRef, NodeIndexTrait},
    nodes::NodesIterable,
};

use super::EdgeNodeList;

impl<E, N, NI> GraphRef<NI> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait,
    N: NodesIterable<Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.nodes.iter_nodes())
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.edges.iter_edges())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_edge_node_list() {
        let graph = EdgeNodeList::new([(0usize, 1usize), (0, 2), (1, 2)], [0, 1, 2]).unwrap();
        graph.iter_nodes().unwrap().for_each(|x| println!("{}", x));
    }

    #[test]
    fn test_edge_node_list_validation() {
        // Test with valid edges - should succeed
        let valid_graph = EdgeNodeList::new([(0usize, 1usize), (1, 2)], [0, 1, 2]);
        assert!(valid_graph.is_ok());

        // Test with invalid edge - edge references node 99 which doesn't exist in [0, 1, 2]
        let invalid_graph = EdgeNodeList::new([(0usize, 1usize), (1, 99)], [0, 1, 2]);
        assert!(invalid_graph.is_err());
        if let Err(err) = invalid_graph {
            assert_eq!(err, GraphError::EdgeHasInvalidNode);
        }

        // Test with another invalid edge - edge references node 100 as source
        let invalid_graph2 = EdgeNodeList::new([(100usize, 1usize), (1, 2)], [0, 1, 2]);
        assert!(invalid_graph2.is_err());
        if let Err(err) = invalid_graph2 {
            assert_eq!(err, GraphError::EdgeHasInvalidNode);
        }
    }
}
