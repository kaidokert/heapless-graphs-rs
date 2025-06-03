// SPDX-License-Identifier: Apache-2.0

//! Kahn's algorithm for topological sorting of directed acyclic graphs (DAGs)

use super::AlgorithmError;
use crate::containers::{maps::MapTrait, queues::Deque};
use crate::graph::{GraphVal, NodeIndexTrait};

/// Kahn's algorithm for topological sorting
///
/// Performs a topological sort on a directed graph using Kahn's algorithm (BFS-based).
/// This algorithm tracks in-degrees of nodes and processes nodes with zero in-degree.
/// It detects cycles and returns an error if the graph is not a DAG.
///
/// # Arguments
/// * `graph` - The graph to sort topologically (must implement GraphVal)
/// * `nodes` - Iterator over all nodes to consider for sorting
/// * `queue` - Queue for BFS processing (nodes with zero in-degree)
/// * `in_degree_map` - Map to track in-degree count for each node
/// * `result` - Container to store the topologically sorted nodes
///
/// # Returns
/// * `Ok(())` if successful
/// * `Err(AlgorithmError::CycleDetected)` if a cycle is found
/// * `Err(AlgorithmError::QueueCapacityExceeded)` if queue capacity exceeded
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if result container is full
///
/// # Time Complexity
/// O(V + E) where V is the number of vertices and E is the number of edges
pub fn kahns<G, NI, Q, M, R>(
    graph: &G,
    nodes: impl Iterator<Item = NI> + Clone,
    mut queue: Q,
    mut in_degree_map: M,
    result: &mut R,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    Q: Deque<NI>,
    M: MapTrait<NI, isize>,
    R: Deque<NI>,
    AlgorithmError<NI>: From<G::Error>,
{
    result.clear();
    queue.clear();

    // Initialize in-degree map with all nodes having 0 in-degree
    for node in nodes.clone() {
        if graph.contains_node(node)? {
            in_degree_map.insert(node, 0);
        }
    }

    // Calculate in-degrees by examining all edges
    for node in nodes.clone() {
        if graph.contains_node(node)? {
            for target in graph.outgoing_edges(node)? {
                if let Some(degree) = in_degree_map.get_mut(&target) {
                    *degree += 1;
                } else {
                    in_degree_map.insert(target, 1);
                }
            }
        }
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
        result
            .push_back(node)
            .map_err(|_| AlgorithmError::ResultCapacityExceeded)?;

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

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::{
        maps::staticdict::Dictionary,
        queues::{CircularQueue, Deque},
    };
    use crate::edgelist::edge_list::EdgeList;
    use test_log::test;

    #[test]
    fn test_kahns_simple() {
        // Create a simple DAG: 0 -> 1 -> 2
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2];
        kahns(
            &graph,
            nodes.iter().copied(),
            queue,
            in_degree_map,
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
    fn test_kahns_complex() {
        // Create a more complex DAG: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2, 3];
        kahns(
            &graph,
            nodes.iter().copied(),
            queue,
            in_degree_map,
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

        // Kahn's algorithm should produce: [0, 1, 2, 3] or [0, 2, 1, 3]
        // 0 should be first (no incoming edges)
        // 3 should be last (no outgoing edges)
        assert_eq!(sorted[0], 0);
        assert_eq!(sorted[len - 1], 3);

        // Check that all nodes are present
        let sorted_slice = &sorted[..len];
        assert!(sorted_slice.contains(&1));
        assert!(sorted_slice.contains(&2));
    }

    #[test]
    fn test_kahns_cycle_detection() {
        // Create a graph with a cycle: 0 -> 1 -> 2 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2), (2, 0)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2];
        let error = kahns(
            &graph,
            nodes.iter().copied(),
            queue,
            in_degree_map,
            &mut result,
        );

        assert_eq!(error, Err(AlgorithmError::CycleDetected));
    }

    #[test]
    fn test_kahns_disconnected() {
        // Create a disconnected graph: 0 -> 1, 2 -> 3 (no connection between pairs)
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (2, 3)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0, 1, 2, 3];
        kahns(
            &graph,
            nodes.iter().copied(),
            queue,
            in_degree_map,
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

    #[test]
    fn test_kahns_self_loop() {
        // Create a graph with a self-loop: 0 -> 0
        let graph = EdgeList::<8, _, _>::new([(0usize, 0usize)]);
        let queue = CircularQueue::<usize, 8>::new();
        let in_degree_map = Dictionary::<usize, isize, 8>::new();
        let mut result = CircularQueue::<usize, 8>::new();

        let nodes = [0];
        let error = kahns(
            &graph,
            nodes.iter().copied(),
            queue,
            in_degree_map,
            &mut result,
        );

        assert_eq!(error, Err(AlgorithmError::CycleDetected));
    }
}
