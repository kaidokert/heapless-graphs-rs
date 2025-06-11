use crate::edges::EdgeNodeError;

use crate::graph::{GraphError, NodeIndexTrait};

mod by_val;

#[derive(Debug)]
pub enum EdgeListError<NI: NodeIndexTrait> {
    EdgeNodeError(EdgeNodeError),
    GraphError(GraphError<NI>),
}

impl<NI: NodeIndexTrait> From<EdgeNodeError> for EdgeListError<NI> {
    fn from(e: EdgeNodeError) -> Self {
        EdgeListError::EdgeNodeError(e)
    }
}
impl<NI: NodeIndexTrait> From<GraphError<NI>> for EdgeListError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        EdgeListError::GraphError(e)
    }
}

/// Edge list graph that stores only edges
///
/// This struct represents a graph using an edge list. It is optimized for
/// compact edge representation, but iterating over nodes may be expensive.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edges::EdgeNodeError;
    use crate::graph::GraphError;
    use crate::tests::collect;

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

        // Test that GraphVal trait is implemented
        let edges_iter = crate::graph::GraphVal::iter_edges(&edge_list).unwrap();
        assert_eq!(edges_iter.count(), 3);

        // Test node iteration (this uses EdgesToNodesIterator internally)
        let nodes_iter = crate::graph::GraphVal::iter_nodes(&edge_list).unwrap();
        let mut nodes = [0usize; 10];
        let nodes_slice = collect(nodes_iter, &mut nodes);
        nodes_slice.sort_unstable();
        assert_eq!(nodes_slice, &[0, 1, 2]);
    }
}
