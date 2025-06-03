// SPDX-License-Identifier: Apache-2.0

//! Topological sorting algorithms for directed acyclic graphs (DAGs)

use super::AlgorithmError;
use crate::containers::queues::Deque;
use crate::graph::{GraphVal, NodeIndexTrait};
use crate::visited::TriStateVisitedTracker;

fn topological_sort_dfs_visit<G, NI, VT, R>(
    graph: &G,
    node: NI,
    visited: &mut VT,
    result: &mut R,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    R: Deque<NI>,
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
        topological_sort_dfs_visit(graph, next_node, visited, result)?;
    }

    visited.mark_visited(&node);
    result
        .push_front(node)
        .map_err(|_| AlgorithmError::ResultCapacityExceeded)?;

    Ok(())
}

/// DFS-based topological sort algorithm
///
/// Performs a topological sort on a directed graph using depth-first search.
/// The algorithm detects cycles and returns an error if the graph is not a DAG.
///
/// # Arguments
/// * `graph` - The graph to sort topologically (must implement GraphVal)
/// * `nodes` - Iterator over all nodes to consider for sorting
/// * `visited` - Tri-state visited tracker (unvisited/visiting/visited)
/// * `result` - Container to store the topologically sorted nodes
///
/// # Returns
/// * `Ok(())` if successful
/// * `Err(AlgorithmError::CycleDetected)` if a cycle is found
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if result container is full
///
/// # Time Complexity
/// O(V + E) where V is the number of vertices and E is the number of edges
pub fn topological_sort_dfs<G, NI, VT, R>(
    graph: &G,
    nodes: impl Iterator<Item = NI>,
    visited: &mut VT,
    result: &mut R,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    R: Deque<NI>,
    AlgorithmError<NI>: From<G::Error>,
{
    result.clear();
    visited.reset();

    for node in nodes {
        if !graph.contains_node(node)? {
            continue;
        }
        if visited.is_unvisited(&node) {
            topological_sort_dfs_visit(graph, node, visited, result)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::queues::CircularQueue;
    use crate::edgelist::edge_list::EdgeList;
    use crate::visited::NodeState;
    use test_log::test;

    #[test]
    fn test_topological_sort_simple() {
        // Create a simple DAG: 0 -> 1 -> 2
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2];
        topological_sort_dfs(
            &graph,
            nodes.iter().copied(),
            visited.as_mut_slice(),
            &mut result,
        )
        .unwrap();

        let mut sorted = [0usize; 8];
        let mut len = 0;
        while let Some(node) = result.pop_front() {
            sorted[len] = node;
            len += 1;
        }
        assert_eq!(len, 3);
        assert_eq!(&sorted[..len], &[0, 1, 2]);
    }

    #[test]
    fn test_topological_sort_complex() {
        // Create a more complex DAG: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2, 3];
        topological_sort_dfs(
            &graph,
            nodes.iter().copied(),
            visited.as_mut_slice(),
            &mut result,
        )
        .unwrap();

        let mut sorted = [0usize; 8];
        let mut len = 0;
        while let Some(node) = result.pop_front() {
            sorted[len] = node;
            len += 1;
        }
        assert_eq!(len, 4);

        // Valid topological orderings: [0, 1, 2, 3] or [0, 2, 1, 3]
        // Both should have 0 first and 3 last
        assert_eq!(sorted[0], 0);
        assert_eq!(sorted[len - 1], 3);

        // Check that all nodes are present
        let sorted_slice = &sorted[..len];
        assert!(sorted_slice.contains(&1));
        assert!(sorted_slice.contains(&2));
    }

    #[test]
    fn test_topological_sort_cycle_detection() {
        // Create a graph with a cycle: 0 -> 1 -> 2 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2), (2, 0)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2];
        let error = topological_sort_dfs(
            &graph,
            nodes.iter().copied(),
            visited.as_mut_slice(),
            &mut result,
        );

        assert_eq!(error, Err(AlgorithmError::CycleDetected));
    }

    #[test]
    fn test_topological_sort_disconnected() {
        // Create a disconnected graph: 0 -> 1, 2 -> 3 (no connection between pairs)
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (2, 3)]);
        let mut visited = [NodeState::Unvisited; 8];
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2, 3];
        topological_sort_dfs(
            &graph,
            nodes.iter().copied(),
            visited.as_mut_slice(),
            &mut result,
        )
        .unwrap();

        let mut sorted = [0usize; 8];
        let mut len = 0;
        while let Some(node) = result.pop_front() {
            sorted[len] = node;
            len += 1;
        }
        assert_eq!(len, 4);

        // Check relative ordering within connected components
        let sorted_slice = &sorted[..len];
        let pos_0 = sorted_slice.iter().position(|&x| x == 0).unwrap();
        let pos_1 = sorted_slice.iter().position(|&x| x == 1).unwrap();
        let pos_2 = sorted_slice.iter().position(|&x| x == 2).unwrap();
        let pos_3 = sorted_slice.iter().position(|&x| x == 3).unwrap();

        assert!(pos_0 < pos_1); // 0 should come before 1
        assert!(pos_2 < pos_3); // 2 should come before 3
    }
}
