use crate::containers::maps::MapTrait;
use crate::graph::{integrity_check, Graph, GraphError, NodeIndex};
use crate::nodes::{AddNode, NodesIterable};

use super::outgoing_nodes::AsOutgoingNodes;

pub struct MapAdjacencyList<NI, E, C, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    M: MapTrait<NI, C>,
{
    nodes: M,
    _phantom: core::marker::PhantomData<(E, C)>,
}

impl<NI, E, C, M> MapAdjacencyList<NI, E, C, M>
where
    NI: NodeIndex,
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
        NI: Copy,
        Self: Graph<NI, Error = GraphError<NI>>,
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

impl<NI, E, C, M> MapAdjacencyList<NI, E, C, M>
where
    NI: NodeIndex,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E> + AddNode<NI> + Default,
    M: MapTrait<NI, C>,
{
    pub fn from_graph<G: Graph<NI>>(source_graph: &G) -> Result<Self, G::Error>
    where
        G::Error: core::fmt::Debug,
    {
        let mut nodes = M::new();
        for node in source_graph.iter_nodes()? {
            let mut outbound = C::default();
            for edge in source_graph.outgoing_edges(node)? {
                outbound.add(edge);
            }
            nodes
                .insert(node, outbound)
                .map_err(|_| GraphError::OutOfCapacity)?;
        }
        Ok(Self {
            nodes,
            _phantom: Default::default(),
        })
    }
}

impl<NI, E, C, M> Graph<NI> for MapAdjacencyList<NI, E, C, M>
where
    M: MapTrait<NI, C>,
    NI: NodeIndex + Eq + core::hash::Hash + Copy,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.nodes.keys().copied())
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .nodes
            .iter()
            .flat_map(|(n, c)| c.as_outgoing_nodes().map(move |m| (*n, *m))))
    }

    /// Optimized O(1) contains_node for map adjacency list
    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.nodes.contains_key(&node))
    }

    /// Optimized O(out-degree) outgoing_edges for map adjacency list
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // The key insight: use Option to unify the iterator types, then flatten
        let edges_option = self.nodes.get(&node).map(|edges| edges.as_outgoing_nodes());
        Ok(edges_option.into_iter().flatten().copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::nodes::NodeStructOption;
    use crate::tests::{collect, collect_sorted};

    #[test]
    fn test_map_adjacency_list_new() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_sorted(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_map_adjacency_list_new_unchecked() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect_sorted(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_map_adjacency_list_empty() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new(dict).unwrap();

        assert_eq!(graph.iter_nodes().unwrap().count(), 0);
    }

    #[test]
    fn test_map_adjacency_list_single_node() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []).unwrap();

        let graph = MapAdjacencyList::new(dict).unwrap();

        let mut nodes = [0usize; 2];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);
    }

    #[test]
    fn test_graph_iter_nodes() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut nodes = [0usize; 4];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[2, 0, 1]);
    }

    #[test]
    fn test_graph_iter_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 6);
        assert_eq!(
            edges_slice,
            &[(2, 0), (2, 0), (0, 1), (0, 2), (1, 2), (1, 0)]
        );
    }

    #[test]
    fn test_graph_contains_node() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        assert!(graph.contains_node(0).unwrap());
        assert!(graph.contains_node(1).unwrap());
        assert!(graph.contains_node(2).unwrap());
        assert!(!graph.contains_node(3).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graph_outgoing_edges() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        dict.insert(2, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test node 0 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1, 2]);

        // Test node 1 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2, 0]);

        // Test node 2 outgoing edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 0]); // Both edges go to node 0

        // Test non-existent node
        assert_eq!(graph.outgoing_edges(99).unwrap().count(), 0);
    }

    #[test]
    fn test_graph_empty_graph() {
        let dict = Dictionary::<usize, [usize; 0], 5>::new();
        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test empty node iteration
        assert_eq!(graph.iter_nodes().unwrap().count(), 0);

        // Test empty edge iteration
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test contains_node on empty graph
        assert!(!graph.contains_node(0).unwrap());
        assert!(!graph.contains_node(42).unwrap());
    }

    #[test]
    fn test_graph_single_node_no_edges() {
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test single node
        let mut nodes = [0usize; 2];
        let nodes_slice = collect(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);

        // Test contains_node
        assert!(graph.contains_node(42).unwrap());
        assert!(!graph.contains_node(0).unwrap());

        // Test no edges
        assert_eq!(graph.iter_edges().unwrap().count(), 0);

        // Test no outgoing edges
        assert_eq!(graph.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_graph_self_loops() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [0, 1]).unwrap();
        dict.insert(1, [1, 1]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test self-loop edges
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 0), (0, 1), (1, 1), (1, 1)]);

        // Test outgoing edges with self-loops
        let mut edges = [0usize; 4];
        let edges_slice = collect(graph.outgoing_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 1]);
    }

    #[test]
    fn test_graph_multiple_nodes_same_target() {
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 1]).unwrap();
        dict.insert(2, [1, 0]).unwrap();
        dict.insert(1, [0, 0]).unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);

        // Test multiple edges pointing to same target
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(0, 1), (0, 1), (1, 0), (1, 0), (2, 0), (2, 1)]
        );
    }

    fn test_nodes_iterable<NI, T: NodesIterable<Node = NI>>(iter: T) {}

    fn test_nodes_iterable_with_ni<NI, T: NodesIterable<Node = NI>>(iter: T, ni: NI) {}

    #[test]
    fn test_map_adjaceny_list_not_all_edges() {
        let mut dict = Dictionary::<_, NodeStructOption<3, _>, 5>::new();
        dict.insert(0, NodeStructOption([Some(1), Some(2), None]))
            .unwrap();
        dict.insert(1, NodeStructOption([Some(2), Some(0), None]))
            .unwrap();
        dict.insert(2, NodeStructOption([Some(0), None, None]))
            .unwrap();

        let graph = MapAdjacencyList::new_unchecked(dict);
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(2, 0), (0, 1), (0, 2), (1, 2), (1, 0)]);
    }

    #[test]
    fn test_map_adjacency_list_from_graph() {
        let src_graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);
        let adjlist =
            MapAdjacencyList::<_, _, _, Dictionary<_, NodeStructOption<5, _>, 5>>::from_graph(
                &src_graph,
            )
            .unwrap();

        let mut nodes = [0usize; 8];
        let node_slice = collect_sorted(adjlist.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(node_slice, &[0usize, 1, 2, 3]);

        let mut edges = [(0usize, 0usize); 8];
        let edge_slice = collect_sorted(adjlist.iter_edges().unwrap(), &mut edges);
        assert_eq!(edge_slice, &[(0, 1), (0, 2), (1, 3), (2, 3)]);

        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(0).unwrap(), &mut nodes),
            &[1, 2]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(1).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(2).unwrap(), &mut nodes),
            &[3]
        );
        assert_eq!(
            collect_sorted(adjlist.outgoing_edges(3).unwrap(), &mut nodes),
            &[]
        );
    }
}
