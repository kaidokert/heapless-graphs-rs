// SPDX-License-Identifier: Apache-2.0

//! Kahn's algorithm for topological sorting of directed acyclic graphs (DAGs)

use super::AlgorithmError;
use crate::containers::{maps::MapTrait, queues::Deque};
use crate::graph::{Graph, NodeIndex};

/// Kahn's algorithm for topological sorting
///
/// Performs a topological sort on a directed graph using Kahn's algorithm (BFS-based).
/// This algorithm tracks in-degrees of nodes and processes nodes with zero in-degree.
/// It detects cycles and returns an error if the graph is not a DAG.
///
/// # Arguments
/// * `graph` - The graph to sort topologically (must implement Graph)
/// * `queue` - Queue for BFS processing (nodes with zero in-degree)
/// * `in_degree_map` - Map to track in-degree count for each node
/// * `sorted_nodes` - Buffer to store the topologically sorted nodes
///
/// # Returns
/// * `Ok(&[NI])` slice of sorted nodes if successful
/// * `Err(AlgorithmError::CycleDetected)` if a cycle is found
/// * `Err(AlgorithmError::QueueCapacityExceeded)` if queue capacity exceeded
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if result buffer is full
///
/// # Time Complexity
/// O(V + E) where V is the number of vertices and E is the number of edges.
/// For matrix-based graphs with optimized incoming_edges, the in-degree
/// calculation is O(V) instead of O(V + E).
pub fn kahns<'a, G, NI, D, M>(
    graph: &G,
    mut queue: D,
    mut in_degree_map: M,
    sorted_nodes: &'a mut [NI],
) -> Result<&'a [NI], AlgorithmError<NI>>
where
    G: Graph<NI>,
    NI: NodeIndex,
    D: Deque<NI>,
    M: MapTrait<NI, isize>,
    AlgorithmError<NI>: From<G::Error>,
{
    queue.clear();

    let mut sort_index = 0;
    let mut append_to_list = |node: NI| -> Result<(), AlgorithmError<NI>> {
        if sort_index >= sorted_nodes.len() {
            return Err(AlgorithmError::ResultCapacityExceeded);
        }
        sorted_nodes[sort_index] = node;
        sort_index += 1;
        Ok(())
    };

    // Calculate in-degrees by directly counting incoming edges for each node
    for node in graph.iter_nodes()? {
        let in_degree = graph.incoming_edges(node)?.count() as isize;
        in_degree_map.insert(node, in_degree);
    }

    // Find all nodes with zero in-degree and add to queue
    for (node, &degree) in in_degree_map.iter() {
        if degree == 0 {
            queue
                .push_back(*node)
                .map_err(|_| AlgorithmError::QueueCapacityExceeded)?;
        }
    }

    // Process nodes in topological order
    while let Some(node) = queue.pop_front() {
        append_to_list(node)?;

        // Reduce in-degree of all neighbors
        for target in graph.outgoing_edges(node)? {
            if let Some(degree) = in_degree_map.get_mut(&target) {
                *degree -= 1;
                if *degree == 0 {
                    queue
                        .push_back(target)
                        .map_err(|_| AlgorithmError::QueueCapacityExceeded)?;
                }
            }
        }
    }

    // Check for cycles - if any node still has positive in-degree, there's a cycle
    for (_, &degree) in in_degree_map.iter() {
        if degree > 0 {
            return Err(AlgorithmError::CycleDetected);
        }
    }

    Ok(&sorted_nodes[..sort_index])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::{maps::staticdict::Dictionary, queues::CircularQueue};
    use crate::edgelist::edge_list::EdgeList;
    use test_log::test;

    #[test]
    fn test_kahns_simple() {
        // Create a simple DAG: 0 -> 1 -> 2
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut sorted_nodes = [0usize; 8];

        let result = kahns(&graph, queue, in_degree_map, &mut sorted_nodes).unwrap();

        assert_eq!(result, &[0, 1, 2]);
    }

    #[test]
    fn test_kahns_complex() {
        // Create a more complex DAG: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut sorted_nodes = [0usize; 8];

        let result = kahns(&graph, queue, in_degree_map, &mut sorted_nodes).unwrap();

        assert_eq!(result.len(), 4);

        // Kahn's algorithm should produce: [0, 1, 2, 3] or [0, 2, 1, 3]
        // 0 should be first (no incoming edges)
        // 3 should be last (no outgoing edges)
        assert_eq!(result[0], 0);
        assert_eq!(result[result.len() - 1], 3);

        // Check that all nodes are present
        assert!(result.contains(&1));
        assert!(result.contains(&2));
    }

    #[test]
    fn test_kahns_cycle_detection() {
        // Create a graph with a cycle: 0 -> 1 -> 2 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2), (2, 0)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut sorted_nodes = [0usize; 8];

        let error = kahns(&graph, queue, in_degree_map, &mut sorted_nodes);

        assert_eq!(error, Err(AlgorithmError::CycleDetected));
    }

    #[test]
    fn test_kahns_disconnected() {
        // Create a disconnected graph: 0 -> 1, 2 -> 3 (no connection between pairs)
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (2, 3)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut sorted_nodes = [0usize; 8];

        let result = kahns(&graph, queue, in_degree_map, &mut sorted_nodes).unwrap();

        assert_eq!(result.len(), 4);

        // Check relative ordering within connected components
        let pos_0 = result.iter().position(|&x| x == 0).unwrap();
        let pos_1 = result.iter().position(|&x| x == 1).unwrap();
        let pos_2 = result.iter().position(|&x| x == 2).unwrap();
        let pos_3 = result.iter().position(|&x| x == 3).unwrap();

        assert!(pos_0 < pos_1); // 0 should come before 1
        assert!(pos_2 < pos_3); // 2 should come before 3
    }

    #[test]
    fn test_kahns_self_loop() {
        // Create a graph with a self-loop: 0 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 0usize)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut sorted_nodes = [0usize; 8];

        let error = kahns(&graph, queue, in_degree_map, &mut sorted_nodes);

        assert_eq!(error, Err(AlgorithmError::CycleDetected));
    }
}
