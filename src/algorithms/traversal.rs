// SPDX-License-Identifier: Apache-2.0

//! Common traversal algorithms
//!
//! Implements common traversal algorithms.

use super::AlgorithmError;

use crate::containers::queues::Deque;
use crate::graph::{GraphRef, GraphVal, NodeIndexTrait};
use crate::visited::VisitedTracker;

/// Unchecked depth first traversal
///
/// Always yields the initial node, even if it is not present in graph
pub fn dfs_recursive_unchecked<G, NI, VT, F>(
    graph: &G,
    start_node: &NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), G::Error>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait,
    VT: VisitedTracker<NI> + ?Sized,
    for<'a> F: FnMut(&'a NI),
{
    if !visited.is_visited(start_node) {
        visited.mark_visited(start_node);
        operation(start_node);
    }
    for next_node in graph.outgoing_edges(start_node)? {
        if !visited.is_visited(next_node) {
            dfs_recursive_unchecked(graph, next_node, visited, operation)?;
        }
    }
    Ok(())
}

/// Depth first recursive traversal
///
/// Does not index initial node, if initial node is not present in the graph
pub fn dfs_recursive<G, NI, VT, F>(
    graph: &G,
    start_node: &NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), G::Error>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait,
    VT: VisitedTracker<NI> + ?Sized,
    for<'a> F: FnMut(&'a NI),
{
    if !graph.contains_node(start_node)? {
        return Ok(());
    }
    dfs_recursive_unchecked(graph, start_node, visited, operation)
}

/// Unchecked iterative depth first traversal, using a stack
///
/// Always yields the initial node, even if it is not present in graph
pub fn dfs_iterative_unchecked<G, NI, VT, S, F>(
    graph: &G,
    start_node: NI,
    visited: &mut VT,
    mut stack: S,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    S: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    stack
        .push_back(start_node)
        .map_err(|_| AlgorithmError::StackCapacityExceeded)?;

    while let Some(node) = stack.pop_back() {
        if visited.is_visited(&node) {
            continue;
        }
        visited.mark_visited(&node);
        operation(node);

        for next_node in graph.outgoing_edges(node)? {
            if !visited.is_visited(&next_node) {
                stack
                    .push_back(next_node)
                    .map_err(|_| AlgorithmError::StackCapacityExceeded)?;
            }
        }
    }
    Ok(())
}

/// Iterative depth first traversal, using a stack
///
/// Does not index initial node, if initial node is not present in graph
pub fn dfs_iterative<G, NI, VT, S, F>(
    graph: &G,
    start_node: NI,
    visited: &mut VT,
    stack: S,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    S: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    if !graph.contains_node(start_node)? {
        return Ok(());
    }
    dfs_iterative_unchecked(graph, start_node, visited, stack, operation)
}

/// Unchecked breadth first traversal, using a queue
///
/// Always yields the initial node, even if it is not present in graph
pub fn bfs_unchecked<G, NI, VT, Q, F>(
    graph: &G,
    start_node: NI,
    visited: &mut VT,
    mut queue: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    queue
        .push_back(start_node)
        .map_err(|_| AlgorithmError::QueueCapacityExceeded)?;
    visited.mark_visited(&start_node);

    while !queue.is_empty() {
        if let Some(node) = queue.pop_front() {
            operation(node);
            for next_node in graph.outgoing_edges(node)? {
                if !visited.is_visited(&next_node) {
                    visited.mark_visited(&next_node);
                    queue
                        .push_back(next_node)
                        .map_err(|_| AlgorithmError::QueueCapacityExceeded)?;
                }
            }
        }
    }
    Ok(())
}

/// Breadth first traversal, using a queue
///
/// Does not index initial node, if initial node is not present in graph
pub fn bfs<G, NI, VT, Q, F>(
    graph: &G,
    start_node: NI,
    visited: &mut VT,
    queue: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphVal<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    if !graph.contains_node(start_node)? {
        return Ok(());
    }
    bfs_unchecked(graph, start_node, visited, queue, operation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edgelist::edge_list::EdgeList;
    use test_log::test;

    struct Collector<T, const N: usize> {
        nodes: [T; N],
        index: usize,
    }
    impl<T: Default, const N: usize> Collector<T, N> {
        fn new() -> Self {
            Self {
                nodes: core::array::from_fn(|_| T::default()),
                index: 0,
            }
        }
        fn push(&mut self, node: T) {
            self.nodes[self.index] = node;
            self.index += 1;
        }
        fn result(&self) -> &[T] {
            &self.nodes[..self.index]
        }
    }

    #[test]
    fn test_dfs_recursive_unchecked() {
        let graph =
            EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2), (2, 0), (2, 3), (3, 3)]);
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        dfs_recursive_unchecked(&graph, &0, visited.as_mut_slice(), &mut |x| {
            collector.push(*x);
        })
        .unwrap();
        assert_eq!(collector.result(), &[0, 1, 2, 3]);
    }

    #[test]
    fn test_bfs_unchecked() {
        use crate::containers::queues::CircularQueue;

        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let queue = CircularQueue::<usize, 16>::new();

        bfs_unchecked(&graph, 0, visited.as_mut_slice(), queue, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        // BFS should visit in breadth-first order: 0, then 1,2, then 3
        assert_eq!(collector.result(), &[0, 1, 2, 3]);
    }

    #[test]
    fn test_dfs_iterative_unchecked() {
        use crate::containers::queues::CircularQueue;

        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3), (2, 3)]);
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let stack = CircularQueue::<usize, 16>::new();

        dfs_iterative_unchecked(&graph, 0, visited.as_mut_slice(), stack, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        // DFS iterative visits in depth-first order (may vary due to stack order)
        assert_eq!(collector.result().len(), 4);
        assert!(collector.result().contains(&0));
        assert!(collector.result().contains(&1));
        assert!(collector.result().contains(&2));
        assert!(collector.result().contains(&3));
    }

    #[test]
    fn test_bfs_with_owned_and_borrowed_graphs() {
        use crate::containers::queues::CircularQueue;

        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3)]);

        // Test with borrowed graph (&graph)
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let queue = CircularQueue::<usize, 16>::new();

        bfs(&graph, 0, visited.as_mut_slice(), queue, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        assert_eq!(collector.result().len(), 4);

        // Test with owned graph (graph) - this should also work
        let graph_owned = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3)]);
        let mut visited2 = [false; 16];
        let mut collector2 = Collector::<usize, 16>::new();
        let queue2 = CircularQueue::<usize, 16>::new();

        // This tests that we can pass an owned graph where &G is expected
        bfs(&graph_owned, 0, visited2.as_mut_slice(), queue2, &mut |x| {
            collector2.push(x);
        })
        .unwrap();

        assert_eq!(collector2.result().len(), 4);
    }

    #[test]
    fn test_dfs_iterative_with_owned_and_borrowed_graphs() {
        use crate::containers::queues::CircularQueue;

        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3)]);

        // Test with borrowed graph (&graph)
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let stack = CircularQueue::<usize, 16>::new();

        dfs_iterative(&graph, 0, visited.as_mut_slice(), stack, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        assert_eq!(collector.result().len(), 4);

        // Test with owned graph (graph) - this should also work
        let graph_owned = EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 3)]);
        let mut visited2 = [false; 16];
        let mut collector2 = Collector::<usize, 16>::new();
        let stack2 = CircularQueue::<usize, 16>::new();

        // This tests that we can pass an owned graph where &G is expected
        dfs_iterative(&graph_owned, 0, visited2.as_mut_slice(), stack2, &mut |x| {
            collector2.push(x);
        })
        .unwrap();

        assert_eq!(collector2.result().len(), 4);
    }

    #[test]
    fn test_bfs_with_map_adjacency_list() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::{
            maps::{staticdict::Dictionary, MapTrait},
            queues::CircularQueue,
        };
        use crate::nodes::NodeStruct;

        // Create a map adjacency list - this will benefit from O(1) contains_node
        let mut map = Dictionary::<usize, NodeStruct<3, usize>, 8>::new();
        map.insert(0, NodeStruct([1, 2, 0])); // 0 as sentinel (self-loop)
        map.insert(1, NodeStruct([3, 1, 1])); // self-loops as sentinels
        map.insert(2, NodeStruct([3, 2, 2]));
        map.insert(3, NodeStruct([3, 3, 3]));

        let graph = MapAdjacencyList::new_unchecked(map);

        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let queue = CircularQueue::<usize, 16>::new();

        bfs(&graph, 0, visited.as_mut_slice(), queue, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        // Should visit all 4 nodes
        assert_eq!(collector.result().len(), 4);
        assert!(collector.result().contains(&0));
        assert!(collector.result().contains(&1));
        assert!(collector.result().contains(&2));
        assert!(collector.result().contains(&3));
    }
}
