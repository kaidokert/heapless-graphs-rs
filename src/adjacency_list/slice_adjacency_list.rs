use crate::graph::{integrity_check, GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::outgoing_nodes::AsOutgoingNodes;

mod by_ref;
mod by_val;

pub struct SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    nodes_container: T,
    _phantom: core::marker::PhantomData<(E, C)>,
}

impl<NI, E, C, T> SliceAdjacencyList<NI, E, C, T>
where
    NI: NodeIndexTrait,
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
        Self: GraphRef<NI, Error = GraphError<NI>>,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::collect_ref;

    #[test]
    fn test_slice_adjacency_list_new() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_slice_adjacency_list_new_unchecked() {
        let adj_list_data = [(0, [1, 2]), (1, [2, 0]), (2, [0, 0])];
        let graph = SliceAdjacencyList::new_unchecked(adj_list_data);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_slice_adjacency_list_with_empty_graph() {
        let adj_list_data: [(usize, [usize; 0]); 0] = [];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        assert_eq!(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap().count(),
            0
        );
    }

    #[test]
    fn test_slice_adjacency_list_single_node() {
        let adj_list_data = [(42, [])];
        let graph = SliceAdjacencyList::new(adj_list_data).unwrap();

        let mut nodes = [0usize; 2];
        let nodes_slice = collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(nodes_slice, &[42]);
    }
}
