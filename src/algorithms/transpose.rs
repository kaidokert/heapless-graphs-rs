// SPDX-License-Identifier: Apache-2.0

//! Graph transposition algorithm
//!
//! Creates the transpose (reverse) of a directed graph by reversing all edges.
//! This is useful for algorithms that need to traverse edges in the opposite direction,
//! such as finding strongly connected components or reverse reachability analysis.

use super::AlgorithmError;
use crate::graph::{Graph, GraphWithMutableEdges, NodeIndex};

/// Creates the transpose of a graph by reversing all edges
///
/// The transpose of a directed graph G = (V, E) is a graph Gᵀ = (V, Eᵀ) where
/// Eᵀ = {(v, u) : (u, v) ∈ E}. In other words, every edge (u, v) in the original
/// graph becomes an edge (v, u) in the transpose.
///
/// # Arguments
/// * `source_graph` - The graph to transpose
/// * `target_graph` - The graph to store the result (must be empty)
///
/// # Returns
/// * `Ok(())` if successful
/// * `Err(AlgorithmError)` if the operation fails
///
/// # Example
/// ```
/// use heapless_graphs::algorithms::transpose_graph;
/// use heapless_graphs::edgelist::edge_list::EdgeList;
/// use heapless_graphs::graph::{Graph, GraphWithMutableEdges};
///
/// // Create a simple directed graph: 0 -> 1 -> 2
/// let source = EdgeList::<8, usize, _>::new([(0, 1), (1, 2)]);
/// let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);
///
/// transpose_graph(&source, &mut target).unwrap();
///
/// // Result should be: 1 -> 0, 2 -> 1
/// let edges: Vec<_> = target.iter_edges().unwrap().collect();
/// assert!(edges.contains(&(1, 0)));
/// assert!(edges.contains(&(2, 1)));
/// ```
pub fn transpose_graph<NI, G1, G2>(
    source_graph: &G1,
    target_graph: &mut G2,
) -> Result<(), AlgorithmError<NI>>
where
    NI: NodeIndex,
    G1: Graph<NI>,
    G2: GraphWithMutableEdges<NI>,
    AlgorithmError<NI>: From<G1::Error>,
    AlgorithmError<NI>: From<G2::Error>,
{
    // Iterate through all edges in the source graph and add them in reverse to the target
    for (source, destination) in source_graph.iter_edges()? {
        // Add the reversed edge: destination -> source
        target_graph.add_edge(destination, source)?;
    }

    Ok(())
}

/// In-place graph transposition for graphs that support both iteration and mutation
///
/// This function creates a temporary copy of all edges, clears the graph,
/// and then adds all edges back in reverse order.
///
/// # Arguments
/// * `graph` - The graph to transpose in-place
/// * `edge_buffer` - Temporary buffer to store edges during transposition
///
/// # Returns
/// * `Ok(())` if successful
/// * `Err(AlgorithmError)` if the operation fails or buffer is too small
///
/// # Example
/// ```
/// use heapless_graphs::algorithms::transpose_graph_inplace;
/// use heapless_graphs::edgelist::edge_list::EdgeList;
/// use heapless_graphs::graph::{Graph, GraphWithMutableEdges};
///
/// let mut graph = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([
///     Some((0, 1)), Some((1, 2)), Some((0, 2)), None, None, None, None, None
/// ]);
/// let mut buffer = [(0usize, 0usize); 8];
///
/// transpose_graph_inplace(&mut graph, &mut buffer).unwrap();
///
/// // Edges are now reversed
/// let edges: Vec<_> = graph.iter_edges().unwrap().collect();
/// assert!(edges.contains(&(1, 0)));
/// assert!(edges.contains(&(2, 1)));
/// assert!(edges.contains(&(2, 0)));
/// ```
pub fn transpose_graph_inplace<NI, G>(
    graph: &mut G,
    edge_buffer: &mut [(NI, NI)],
) -> Result<(), AlgorithmError<NI>>
where
    NI: NodeIndex + Copy,
    G: Graph<NI> + GraphWithMutableEdges<NI>,
    AlgorithmError<NI>: From<G::Error>,
{
    // Collect all current edges into the buffer
    let mut edge_count = 0;
    for edge in graph.iter_edges()? {
        if edge_count >= edge_buffer.len() {
            return Err(AlgorithmError::ResultCapacityExceeded);
        }
        edge_buffer[edge_count] = edge;
        edge_count += 1;
    }

    // Remove all existing edges
    for &(source, destination) in edge_buffer.iter().take(edge_count) {
        graph.remove_edge(source, destination)?;
    }

    // Add all edges back in reverse
    for &(source, destination) in edge_buffer.iter().take(edge_count) {
        graph.add_edge(destination, source)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edgelist::edge_list::EdgeList;
    use crate::tests::collect_sorted;

    #[test]
    fn test_transpose_graph_simple() {
        // Create source graph: 0 -> 1 -> 2
        let source = EdgeList::<8, usize, _>::new([(0, 1), (1, 2)]);
        let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

        transpose_graph(&source, &mut target).unwrap();

        // Target should be: 1 -> 0, 2 -> 1
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(target.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(1, 0), (2, 1)]);
    }

    #[test]
    fn test_transpose_graph_with_self_loops() {
        // Create source graph with self-loops: 0 -> 0, 0 -> 1, 1 -> 1
        let source = EdgeList::<8, usize, _>::new([(0, 0), (0, 1), (1, 1)]);
        let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

        transpose_graph(&source, &mut target).unwrap();

        // Target should be: 0 -> 0, 1 -> 0, 1 -> 1 (self-loops unchanged)
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(target.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 0), (1, 0), (1, 1)]);
    }

    #[test]
    fn test_transpose_graph_empty() {
        let source = EdgeList::<8, usize, [(usize, usize); 0]>::new([]);
        let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 0]>::new([]);

        transpose_graph(&source, &mut target).unwrap();

        assert_eq!(target.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_transpose_graph_complete() {
        // Create a complete graph on 3 nodes: 0->1, 0->2, 1->0, 1->2, 2->0, 2->1
        let source = EdgeList::<8, usize, _>::new([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]);
        let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

        transpose_graph(&source, &mut target).unwrap();

        // Complete graph should be its own transpose
        let mut source_edges = [(0usize, 0usize); 8];
        let source_slice = collect_sorted(source.iter_edges().unwrap(), &mut source_edges);

        let mut target_edges = [(0usize, 0usize); 8];
        let target_slice = collect_sorted(target.iter_edges().unwrap(), &mut target_edges);

        assert_eq!(source_slice, target_slice);
    }

    #[test]
    fn test_transpose_graph_inplace_simple() {
        let mut graph = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([
            Some((0, 1)),
            Some((1, 2)),
            Some((0, 2)),
            None,
            None,
            None,
            None,
            None,
        ]);
        let mut buffer = [(0usize, 0usize); 8];

        transpose_graph_inplace(&mut graph, &mut buffer).unwrap();

        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(graph.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(1, 0), (2, 0), (2, 1)]);
    }

    #[test]
    fn test_transpose_graph_inplace_buffer_too_small() {
        let mut graph = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([
            Some((0, 1)),
            Some((1, 2)),
            Some((0, 2)),
            None,
            None,
            None,
            None,
            None,
        ]);
        let mut buffer = [(0usize, 0usize); 2]; // Too small for 3 edges

        let result = transpose_graph_inplace(&mut graph, &mut buffer);
        assert!(matches!(
            result,
            Err(AlgorithmError::ResultCapacityExceeded)
        ));
    }

    #[test]
    fn test_transpose_preserves_node_count() {
        let source = EdgeList::<8, usize, _>::new([(0, 1), (1, 2), (2, 3), (3, 1)]);
        let mut target = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

        transpose_graph(&source, &mut target).unwrap();

        // Both graphs should have the same nodes
        assert_eq!(
            source.iter_nodes().unwrap().count(),
            target.iter_nodes().unwrap().count()
        );

        // Verify specific nodes exist
        let mut source_nodes = [0usize; 8];
        let source_nodes_slice = collect_sorted(source.iter_nodes().unwrap(), &mut source_nodes);

        let mut target_nodes = [0usize; 8];
        let target_nodes_slice = collect_sorted(target.iter_nodes().unwrap(), &mut target_nodes);

        assert_eq!(source_nodes_slice, target_nodes_slice);
    }

    #[test]
    fn test_double_transpose_identity() {
        // Transpose of transpose should equal original
        let original = EdgeList::<8, usize, _>::new([(0, 1), (1, 2), (0, 3)]);
        let mut first_transpose = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);
        let mut second_transpose =
            EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

        transpose_graph(&original, &mut first_transpose).unwrap();
        transpose_graph(&first_transpose, &mut second_transpose).unwrap();

        // Second transpose should equal original
        let mut original_edges = [(0usize, 0usize); 8];
        let original_slice = collect_sorted(original.iter_edges().unwrap(), &mut original_edges);

        let mut final_edges = [(0usize, 0usize); 8];
        let final_slice = collect_sorted(second_transpose.iter_edges().unwrap(), &mut final_edges);

        assert_eq!(original_slice, final_slice);
    }
}
