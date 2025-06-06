use crate::{
    edges::EdgesIterable,
    graph::{GraphError, GraphVal, GraphValWithNodeValues, NodeIndexTrait},
    nodes::{NodesIterable, NodesValuesIterable},
};

use super::EdgeNodeList;

impl<E, N, NI> GraphVal<NI> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait + Copy,
    N: NodesIterable<Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.iter_nodes().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }
}

impl<E, N, NI, V> GraphValWithNodeValues<NI, V> for EdgeNodeList<E, N, NI>
where
    NI: NodeIndexTrait + Copy,
    N: NodesValuesIterable<V, Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    fn node_value(&self, node: NI) -> Result<Option<&V>, Self::Error> {
        self.nodes
            .iter_nodes_values()
            .find(|(n, _)| **n == node)
            .map(|(_, value)| value)
            .ok_or(GraphError::NodeNotFound)
    }

    fn iter_node_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, Option<&'a V>)>, Self::Error>
    where
        V: 'a,
    {
        Ok(self.nodes.iter_nodes_values().map(|(n, v)| (*n, v)))
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
}
