// SPDX-License-Identifier: Apache-2.0

//! Topological sorting algorithms for directed acyclic graphs (DAGs)

use super::AlgorithmError;
use crate::graph::{GraphVal, NodeIndexTrait};
use crate::visited::TriStateVisitedTracker;

fn topological_sort_dfs_visit<G, NI, VT>(
    graph: &G,
    node: NI,
    visited: &mut VT,
    sorted_nodes: &mut [NI],
    sort_index: &mut usize,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    if visited.is_visiting(&node) {
        return Err(AlgorithmError::CycleDetected);
    }
    if visited.is_visited(&node) {
        return Ok(());
    }

    visited.mark_visiting(&node);

    for next_node in graph.outgoing_edges(node)? {
        topological_sort_dfs_visit(graph, next_node, visited, sorted_nodes, sort_index)?;
    }

    visited.mark_visited(&node);

    // Add to front of result (DFS post-order gives reverse topological order)
    if *sort_index >= sorted_nodes.len() {
        return Err(AlgorithmError::ResultCapacityExceeded);
    }
    sorted_nodes[*sort_index] = node;
    *sort_index += 1;

    Ok(())
}

/// DFS-based topological sort algorithm
///
/// Performs a topological sort on a directed graph using depth-first search.
/// The algorithm detects cycles and returns an error if the graph is not a DAG.
///
/// # Arguments
/// * `graph` - The graph to sort topologically (must implement GraphVal)
/// * `visited` - Tri-state visited tracker (unvisited/visiting/visited)
/// * `sorted_nodes` - Buffer to store the topologically sorted nodes
///
/// # Returns
/// * `Ok(&[NI])` slice of sorted nodes if successful
/// * `Err(AlgorithmError::CycleDetected)` if a cycle is found
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if result buffer is full
///
/// # Time Complexity
/// O(V + E) where V is the number of vertices and E is the number of edges
pub fn topological_sort_dfs<'a, G, NI, VT>(
    graph: &G,
    visited: &mut VT,
    sorted_nodes: &'a mut [NI],
) -> Result<&'a [NI], AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    visited.reset();
    let mut sort_index = 0;

    // Visit all nodes in the graph
    for node in graph.iter_nodes()? {
        if visited.is_unvisited(&node) {
            topological_sort_dfs_visit(graph, node, visited, sorted_nodes, &mut sort_index)?;
        }
    }

    // Reverse the result since DFS post-order gives reverse topological order
    let result_slice = &mut sorted_nodes[..sort_index];
    result_slice.reverse();

    Ok(result_slice)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edgelist::edge_list::EdgeList;
    use crate::visited::NodeState;
    use test_log::test;

    #[test]
    fn test_topological_sort_simple() {
        // Create a simple DAG: 0 -> 1 -> 2
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut sorted_nodes = [0usize; 8];

        let result =
            topological_sort_dfs(&graph, visited.as_mut_slice(), &mut sorted_nodes).unwrap();

        assert_eq!(result, &[0, 1, 2]);
    }

    #[test]
    fn test_topological_sort_complex() {
        // Create a more complex DAG: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut sorted_nodes = [0usize; 8];

        let result =
            topological_sort_dfs(&graph, visited.as_mut_slice(), &mut sorted_nodes).unwrap();

        assert_eq!(result.len(), 4);

        // Valid topological orderings: [0, 1, 2, 3] or [0, 2, 1, 3]
        // Both should have 0 first and 3 last
        assert_eq!(result[0], 0);
        assert_eq!(result[result.len() - 1], 3);

        // Check that all nodes are present
        assert!(result.contains(&1));
        assert!(result.contains(&2));
    }

    #[test]
    fn test_topological_sort_cycle_detection() {
        // Create a graph with a cycle: 0 -> 1 -> 2 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2), (2, 0)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut sorted_nodes = [0usize; 8];

        let error = topological_sort_dfs(&graph, visited.as_mut_slice(), &mut sorted_nodes);

        assert!(matches!(error, Err(AlgorithmError::CycleDetected)));
    }

    #[test]
    fn test_topological_sort_disconnected() {
        // Create a disconnected graph: 0 -> 1, 2 -> 3 (no connection between pairs)
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (2, 3)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut sorted_nodes = [0usize; 8];

        let result =
            topological_sort_dfs(&graph, visited.as_mut_slice(), &mut sorted_nodes).unwrap();

        assert_eq!(result.len(), 4);

        // Check relative ordering within connected components
        let pos_0 = result.iter().position(|&x| x == 0).unwrap();
        let pos_1 = result.iter().position(|&x| x == 1).unwrap();
        let pos_2 = result.iter().position(|&x| x == 2).unwrap();
        let pos_3 = result.iter().position(|&x| x == 3).unwrap();

        assert!(pos_0 < pos_1); // 0 should come before 1
        assert!(pos_2 < pos_3); // 2 should come before 3
    }
}
