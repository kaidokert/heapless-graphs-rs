use crate::conversions::FromGraph;
use crate::edges::EdgeNodeError;
use crate::graph::{Graph, GraphError, GraphWithMutableEdges, NodeIndex};

#[derive(Debug)]
pub enum EdgeListError<NI: NodeIndex> {
    EdgeNodeError(EdgeNodeError),
    GraphError(GraphError<NI>),
}

impl<NI: NodeIndex> From<EdgeNodeError> for EdgeListError<NI> {
    fn from(e: EdgeNodeError) -> Self {
        EdgeListError::EdgeNodeError(e)
    }
}
impl<NI: NodeIndex> From<GraphError<NI>> for EdgeListError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        EdgeListError::GraphError(e)
    }
}

impl<NI: NodeIndex> From<EdgeListError<NI>> for GraphError<NI> {
    fn from(e: EdgeListError<NI>) -> Self {
        match e {
            EdgeListError::EdgeNodeError(_) => GraphError::OutOfCapacity,
            EdgeListError::GraphError(ge) => ge,
        }
    }
}

/// Edge list graph that stores only edges
///
/// This struct represents a graph using an edge list. It is optimized for
/// compact edge representation, but iterating over nodes is expensive.
/// Edges can also have values.
///
/// See [`crate::edges::EdgesToNodesIterator`] for the expensive node iteration used.
///
/// # Type Parameters
///
/// - `N`: The max number of nodes in the graph. This is a constant size parameter
///   that represents the total capacity for nodes. The storage is only allocated
///   on stack temporarily when nodes are iterated over.
/// - `E`: The type of the container or collection that stores the edges. It is expected to
///   implement the [`crate::edges::EdgesIterable`] trait, which defines the behavior for
///   iterating over edges.
/// - `NI`: The type that represents the node indices in the graph. This could be
///   a simple integer type like `usize` or a more complex index type.
///
pub struct EdgeList<const N: usize, NI, E> {
    edges: E,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, E> EdgeList<N, NI, E> {
    pub fn new(edges: E) -> Self {
        Self {
            edges,
            _phantom: Default::default(),
        }
    }
}

impl<const N: usize, NI, E> FromGraph<NI, EdgeListError<NI>> for EdgeList<N, NI, E>
where
    NI: NodeIndex + Ord + PartialEq,
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::MutableEdges<NI> + Default,
{
    fn from_graph<G>(source_graph: &G) -> Result<Self, EdgeListError<NI>>
    where
        G: Graph<NI>,
        EdgeListError<NI>: From<G::Error>,
    {
        let mut edges = E::default();

        for (source, destination) in source_graph.iter_edges()? {
            if edges.add_edge((source, destination)).is_none() {
                // Edge container is full, return capacity error
                return Err(EdgeListError::GraphError(GraphError::OutOfCapacity));
            }
        }

        Ok(Self {
            edges,
            _phantom: Default::default(),
        })
    }
}

impl<const N: usize, NI, E> EdgeList<N, NI, E>
where
    NI: NodeIndex + Ord + PartialEq,
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::MutableEdges<NI> + Default,
{
}

impl<const N: usize, NI, E> Graph<NI> for EdgeList<N, NI, E>
where
    E: crate::edges::EdgesIterable<Node = NI>,
    NI: NodeIndex + Ord,
{
    type Error = EdgeListError<NI>;

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }
    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(crate::edges::EdgesToNodesIterator::<N, NI>::new(&self.edges)?.copied())
    }
}

impl<const N: usize, NI, E, V> crate::graph::GraphWithEdgeValues<NI, V> for EdgeList<N, NI, E>
where
    E: crate::edges::EdgeValuesIterable<V, Node = NI>,
    NI: NodeIndex + Ord,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a V>)>, Self::Error>
    where
        V: 'a,
    {
        Ok(self.edges.iter_edges_values().map(|(a, b, v)| (*a, *b, v)))
    }
}

impl<const N: usize, NI, E> GraphWithMutableEdges<NI> for EdgeList<N, NI, E>
where
    E: crate::edges::EdgesIterable<Node = NI> + crate::edges::MutableEdges<NI>,
    NI: NodeIndex + Ord + PartialEq,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // No node validation needed - nodes are implicitly created by adding edges
        // EdgeList derives nodes from edges, so any edge automatically makes both nodes exist
        self.edges
            .add_edge((source, destination))
            .ok_or(GraphError::OutOfCapacity)?;
        Ok(())
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Remove the edge from the edge container
        self.edges
            .remove_edge((source, destination))
            .ok_or(GraphError::EdgeNotFound(source, destination))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::containers::maps::MapTrait;
    use crate::edges::EdgeNodeError;
    use crate::edges::EdgeStructOption;
    use crate::graph::{GraphError, GraphWithEdgeValues, GraphWithMutableEdges};
    use crate::tests::{collect, collect_sorted};

    #[test]
    fn test_edge_list_new() {
        let edges = [(0, 1), (1, 2), (2, 0)];
        let edge_list = EdgeList::<10, usize, _>::new(edges);

        // Test that we can create the edge list
        assert_eq!(
            core::mem::size_of_val(&edge_list.edges),
            core::mem::size_of_val(&edges)
        );
    }

    #[test]
    fn test_edge_list_new_empty() {
        let edges: [(usize, usize); 0] = [];
        let edge_list = EdgeList::<10, usize, _>::new(edges);

        // Test that we can create an empty edge list
        assert_eq!(core::mem::size_of_val(&edge_list.edges), 0);
    }

    #[test]
    fn test_edge_list_new_single_edge() {
        let edges = [(42, 99)];
        let edge_list = EdgeList::<10, usize, _>::new(edges);

        // Test that we can create an edge list with a single edge
        assert_eq!(
            core::mem::size_of_val(&edge_list.edges),
            core::mem::size_of_val(&edges)
        );
    }

    #[test]
    fn test_edge_list_with_different_node_types() {
        // Test with different node index types
        let edges_u32 = [(0u32, 1u32), (1u32, 2u32)];
        let _edge_list_u32 = EdgeList::<10, u32, _>::new(edges_u32);

        let edges_i32 = [(0i32, 1i32), (1i32, 2i32)];
        let _edge_list_i32 = EdgeList::<10, i32, _>::new(edges_i32);

        let edges_u8 = [(0u8, 1u8), (1u8, 2u8)];
        let _edge_list_u8 = EdgeList::<10, u8, _>::new(edges_u8);
    }

    #[test]
    fn test_edge_list_error_from_edge_node_error() {
        let edge_node_error = EdgeNodeError::NotEnoughCapacity;
        let edge_list_error = EdgeListError::<usize>::from(edge_node_error);

        assert!(matches!(
            edge_list_error,
            EdgeListError::EdgeNodeError(EdgeNodeError::NotEnoughCapacity)
        ));
    }

    #[test]
    fn test_edge_list_error_from_graph_error() {
        let graph_error = GraphError::<usize>::NodeNotFound(0);
        let edge_list_error = EdgeListError::<usize>::from(graph_error);

        assert!(matches!(
            edge_list_error,
            EdgeListError::GraphError(GraphError::NodeNotFound(0))
        ));
    }

    #[test]
    fn test_graph_error_from_edge_list_error() {
        // Test EdgeNodeError variant
        let edge_node_error =
            EdgeListError::<usize>::EdgeNodeError(EdgeNodeError::NotEnoughCapacity);
        let graph_error = GraphError::<usize>::from(edge_node_error);
        assert!(matches!(graph_error, GraphError::OutOfCapacity));

        // Test GraphError variant
        let original_graph_error = GraphError::<usize>::NodeNotFound(42);
        let edge_list_error = EdgeListError::<usize>::GraphError(original_graph_error);
        let converted_graph_error = GraphError::<usize>::from(edge_list_error);
        assert!(matches!(
            converted_graph_error,
            GraphError::NodeNotFound(42)
        ));
    }

    #[test]
    fn test_edge_list_error_types() {
        // Test EmptyEdges variant
        let edge_node_error = EdgeListError::<usize>::EdgeNodeError(EdgeNodeError::EmptyEdges);
        assert!(matches!(
            edge_node_error,
            EdgeListError::EdgeNodeError(EdgeNodeError::EmptyEdges)
        ));

        // Test NotEnoughCapacity variant
        let capacity_error =
            EdgeListError::<usize>::EdgeNodeError(EdgeNodeError::NotEnoughCapacity);
        assert!(matches!(
            capacity_error,
            EdgeListError::EdgeNodeError(EdgeNodeError::NotEnoughCapacity)
        ));

        let graph_error = EdgeListError::<usize>::GraphError(GraphError::NodeNotFound(0));
        assert!(matches!(
            graph_error,
            EdgeListError::GraphError(GraphError::NodeNotFound(0))
        ));
    }

    #[test]
    fn test_edge_list_with_vec_like_edges() {
        // Test with array slice
        let edge_array = [(0, 1), (1, 2), (2, 0)];
        let _edge_list = EdgeList::<10, usize, _>::new(&edge_array[..]);

        // Test with different edge container types that might implement EdgesIterable
        let edge_slice: &[(usize, usize)] = &[(0, 1), (1, 2)];
        let _edge_list_slice = EdgeList::<10, usize, _>::new(edge_slice);
    }

    #[test]
    fn test_edge_list_different_capacities() {
        let edges = [(0, 1), (1, 2)];

        // Test different capacity parameters
        let _edge_list_small = EdgeList::<3, usize, _>::new(edges);
        let _edge_list_medium = EdgeList::<100, usize, _>::new(edges);
        let _edge_list_large = EdgeList::<1000, usize, _>::new(edges);
    }

    #[test]
    fn test_edge_list_graphval_functionality() {
        let edges = [(0, 1), (1, 2), (2, 0)];
        let edge_list = EdgeList::<10, usize, _>::new(edges);

        // Test that Graph trait is implemented
        let edges_iter = edge_list.iter_edges().unwrap();
        assert_eq!(edges_iter.count(), 3);

        // Test node iteration (this uses EdgesToNodesIterator internally)
        let nodes_iter = edge_list.iter_nodes().unwrap();
        let mut nodes = [0usize; 10];
        let nodes_slice = collect_sorted(nodes_iter, &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }

    #[test]
    fn test_edge_list() {
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2)]);
        // Test iteration without println for no_std compatibility
        let _: () = graph.iter_nodes().unwrap().for_each(|_x| {});
    }

    #[test]
    fn test_edge_list_with_values() {
        // Create a graph with edge weights using EdgeValueStruct
        let edge_data =
            crate::edges::EdgeValueStruct([(0usize, 1usize, 5i32), (1, 2, 3), (0, 2, 8)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        // Test that GraphWithEdgeValues is implemented
        let edge_values = graph.iter_edge_values().unwrap();
        let mut edges_with_values = [(0usize, 0usize, 0i32); 8];
        let edges_slice = collect(
            edge_values.filter_map(|(src, dst, weight_opt)| weight_opt.map(|w| (src, dst, *w))),
            &mut edges_with_values,
        );
        assert_eq!(edges_slice, &[(0, 1, 5), (1, 2, 3), (0, 2, 8)]);
    }

    #[test]
    fn test_edge_list_nodes_with_values() {
        // Test that basic Graph methods still work with weighted edges
        let edge_data = crate::edges::EdgeValueStruct([(0usize, 1usize, 10i32), (2, 3, 20)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let nodes = graph.iter_nodes().unwrap();
        let mut node_list = [0usize; 8];
        let node_slice = collect(nodes, &mut node_list);
        assert_eq!(node_slice, &[0, 1, 2, 3]);
    }

    #[test]
    fn test_edge_list_incoming_edge_values() {
        // Create a graph with edge weights using EdgeValueStruct
        let edge_data = crate::edges::EdgeValueStruct([
            (0usize, 1usize, 5i32), // 0 -> 1 with weight 5
            (1, 2, 3),              // 1 -> 2 with weight 3
            (0, 2, 8),              // 0 -> 2 with weight 8
            (3, 1, 7),              // 3 -> 1 with weight 7
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        // Test incoming edge values for node 1
        let mut incoming = [(0usize, 0i32); 8];
        let incoming_slice = collect(
            graph
                .incoming_edge_values(1)
                .unwrap()
                .filter_map(|(src, weight)| weight.map(|w| (src, *w))),
            &mut incoming,
        );
        assert_eq!(incoming_slice, &[(0, 5), (3, 7)]);

        // Test incoming edge values for node 2
        let mut incoming = [(0usize, 0i32); 8];
        let incoming_slice = collect(
            graph
                .incoming_edge_values(2)
                .unwrap()
                .filter_map(|(src, weight)| weight.map(|w| (src, *w))),
            &mut incoming,
        );
        assert_eq!(incoming_slice, &[(1, 3), (0, 8)]);

        // Test incoming edge values for node 0 (no incoming edges)
        let mut incoming = [(0usize, 0i32); 8];
        let incoming_slice = collect(
            graph
                .incoming_edge_values(0)
                .unwrap()
                .filter_map(|(src, weight)| weight.map(|w| (src, *w))),
            &mut incoming,
        );
        assert_eq!(incoming_slice, &[]);

        // Test incoming edge values for non-existent node
        assert_eq!(graph.incoming_edge_values(99).unwrap().count(), 0);
    }

    #[test]
    fn test_edge_list_add_edge_success() {
        let edges = EdgeStructOption([None, None, None, None, None]); // Capacity for 5 edges
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Start with empty graph
        assert_eq!(graph.iter_edges().unwrap().count(), 0);
        // Note: iter_nodes() on empty EdgeList returns EmptyEdges error
        assert!(graph.iter_nodes().is_err());

        // Add edges - nodes are implicitly created
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert!(graph.add_edge(0, 2).is_ok());

        // Verify edges were added
        let edge_count = graph.iter_edges().unwrap().count();
        assert_eq!(edge_count, 3);

        // Verify nodes were implicitly created
        let node_count = graph.iter_nodes().unwrap().count();
        assert_eq!(node_count, 3); // nodes 0, 1, 2

        // Verify specific edges exist
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2)]);
    }

    #[test]
    fn test_edge_list_add_edge_capacity_exceeded() {
        let edges = EdgeStructOption([None, None]); // Capacity for only 2 edges
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Add edges up to capacity
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());

        // Try to add one more edge (should exceed capacity)
        let result = graph.add_edge(0, 2);
        assert!(matches!(
            result,
            Err(EdgeListError::GraphError(GraphError::OutOfCapacity))
        ));
    }

    #[test]
    fn test_edge_list_remove_edge_success() {
        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), Some((0, 2)), None, None]);
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Verify initial state
        assert_eq!(graph.iter_edges().unwrap().count(), 3);
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);

        // Remove an edge
        assert!(graph.remove_edge(1, 2).is_ok());

        // Verify edge was removed
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2)]);

        // Verify nodes still exist (other edges reference them)
        assert_eq!(graph.iter_nodes().unwrap().count(), 3);
    }

    #[test]
    fn test_edge_list_remove_edge_isolates_node() {
        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), None, None, None]);
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Remove edge that will isolate node 2
        assert!(graph.remove_edge(1, 2).is_ok());

        // Verify edge was removed
        assert_eq!(graph.iter_edges().unwrap().count(), 1);

        // Verify node 2 no longer exists (not referenced by any edge)
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(graph.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1]); // Node 2 is gone
    }

    #[test]
    fn test_edge_list_remove_edge_not_found() {
        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), None, None, None]);
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Try to remove edge that doesn't exist
        let result = graph.remove_edge(0, 2);
        assert!(matches!(
            result,
            Err(EdgeListError::GraphError(GraphError::EdgeNotFound(0, 2)))
        ));

        // Verify original edges are still there
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
    }

    #[test]
    fn test_edge_list_add_remove_edge_comprehensive() {
        let edges = EdgeStructOption([None, None, None, None, None]);
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Start with empty graph
        assert_eq!(graph.iter_edges().unwrap().count(), 0);
        // Note: iter_nodes() on empty EdgeList returns EmptyEdges error
        assert!(graph.iter_nodes().is_err());

        // Add several edges
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 2).is_ok());
        assert!(graph.add_edge(2, 3).is_ok());
        assert!(graph.add_edge(0, 3).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);
        assert_eq!(graph.iter_nodes().unwrap().count(), 4);

        // Remove some edges
        assert!(graph.remove_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 3);

        // Try to remove the same edge again (should fail)
        let result = graph.remove_edge(1, 2);
        assert!(matches!(
            result,
            Err(EdgeListError::GraphError(GraphError::EdgeNotFound(1, 2)))
        ));

        // Add the edge back
        assert!(graph.add_edge(1, 2).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 4);

        // Verify final edge set
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 3), (1, 2), (2, 3)]);
    }

    #[test]
    fn test_edge_list_self_loops() {
        let edges = EdgeStructOption([None, None, None, None, None]);
        let mut graph = EdgeList::<10, usize, _>::new(edges);

        // Add self-loops and regular edges
        assert!(graph.add_edge(0, 0).is_ok()); // Self-loop
        assert!(graph.add_edge(0, 1).is_ok());
        assert!(graph.add_edge(1, 1).is_ok()); // Self-loop

        assert_eq!(graph.iter_edges().unwrap().count(), 3);
        assert_eq!(graph.iter_nodes().unwrap().count(), 2); // nodes 0, 1

        // Remove self-loop
        assert!(graph.remove_edge(0, 0).is_ok());
        assert_eq!(graph.iter_edges().unwrap().count(), 2);
        assert_eq!(graph.iter_nodes().unwrap().count(), 2); // Still nodes 0, 1
    }

    #[test]
    fn test_edge_list_from_graph() {
        // Create a source graph (adjacency list)
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap();
        dict.insert(1, [2, 0]).unwrap();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeList
        let edge_list: EdgeList<8, usize, EdgeStructOption<16, usize>> =
            EdgeList::from_graph(&source).unwrap();

        // Verify edges were copied correctly - use collect to slice
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(edge_list.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2), (1, 0)]);
    }

    #[test]
    fn test_edge_list_from_empty_graph() {
        // Create an empty source graph
        let dict = Dictionary::<usize, [usize; 2], 8>::new();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to EdgeList
        let edge_list: EdgeList<8, usize, EdgeStructOption<16, usize>> =
            EdgeList::from_graph(&source).unwrap();

        // Verify no edges
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(edge_list.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice.len(), 0);
    }

    #[test]
    fn test_edge_list_from_graph_trait() {
        // Create a source graph (adjacency list)
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // 0 -> 1, 2
        dict.insert(1, [2, 0]).unwrap(); // 1 -> 2, 0
        let source = MapAdjacencyList::new_unchecked(dict);

        // Use the trait method instead of the direct method
        let edge_list: EdgeList<8, usize, EdgeStructOption<16, usize>> =
            EdgeList::from_graph(&source).unwrap();

        // Verify it works the same as from_graph
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(edge_list.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2), (1, 0)]);
    }
}
