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
        let graph = EdgeNodeList::new([(0usize, 1usize), (0, 2), (1, 2)], [0, 1, 2]);
        graph.iter_nodes().unwrap().for_each(|x| println!("{}", x));
    }
}
