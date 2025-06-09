use crate::containers::maps::MapTrait;
use crate::graph::{integrity_check, GraphError, GraphRef, NodeIndexTrait};
use crate::nodes::NodesIterable;

use super::outgoing_nodes::AsOutgoingNodes;

mod by_ref;
mod by_val;

pub struct MapAdjacencyList<M, NI, E, C>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    nodes: M,
    _phantom: core::marker::PhantomData<(E, C)>,
}

impl<M, NI, E, C> MapAdjacencyList<M, NI, E, C>
where
    NI: NodeIndexTrait,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    /// Create new map adjacency list with validation
    ///
    /// This function validates that all edge destinations exist in the node set.
    /// Returns an error if any edge references a non-existent node.
    pub fn new(nodes: M) -> Result<Self, GraphError<NI>>
    where
        Self: GraphRef<NI, Error = GraphError<NI>>,
    {
        let result = Self::new_unchecked(nodes);
        integrity_check::<NI, _>(&result)?;
        Ok(result)
    }

    pub fn new_unchecked(nodes: M) -> Self {
        Self {
            nodes,
            _phantom: core::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::graph::GraphRef;
    use crate::tests::array_collect_ref;

    #[test]
    fn test_map_adjacency_list_new() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]);
        dict.insert(1, [2, 0]);
        dict.insert(2, [0, 0]);

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 4];
        let len = array_collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(len, 3);
        assert!(nodes[..len].contains(&0));
        assert!(nodes[..len].contains(&1));
        assert!(nodes[..len].contains(&2));
    }

    #[test]
    fn test_map_adjacency_list_new_unchecked() {
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
        assert!(nodes[..len].contains(&0));
        assert!(nodes[..len].contains(&1));
        assert!(nodes[..len].contains(&2));
    }

    #[test]
    fn test_map_adjacency_list_empty() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new(dict).unwrap();

        assert_eq!(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap().count(),
            0
        );
    }

    #[test]
    fn test_map_adjacency_list_single_node() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []);

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 2];
        let len = array_collect_ref(
            crate::graph::GraphRef::iter_nodes(&graph).unwrap(),
            &mut nodes,
        );
        assert_eq!(len, 1);
        assert_eq!(&nodes[..len], &[42]);
    }
}
