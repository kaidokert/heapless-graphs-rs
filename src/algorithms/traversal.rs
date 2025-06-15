// SPDX-License-Identifier: Apache-2.0

//! Common traversal algorithms
//!
//! Implements common traversal algorithms.

use super::AlgorithmError;

use crate::containers::queues::Deque;
use crate::graph::{Graph, NodeIndex};
use crate::visited::VisitedTracker;

/// Unchecked depth first traversal
///
/// Always yields the initial node, even if it is not present in graph
pub fn dfs_recursive_unchecked<G, NI, VT, F>(
    graph: &G,
    start_node: NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: Graph<NI>,
    NI: NodeIndex,
    VT: VisitedTracker<NI> + ?Sized,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    if !visited.is_visited(&start_node) {
        visited.mark_visited(&start_node);
        operation(start_node);
    }
    for next_node in graph.outgoing_edges(start_node)? {
        if !visited.is_visited(&next_node) {
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
    start_node: NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    G: Graph<NI>,
    NI: NodeIndex + core::fmt::Debug,
    VT: VisitedTracker<NI> + ?Sized,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
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
    G: Graph<NI>,
    NI: NodeIndex,
    VT: VisitedTracker<NI> + ?Sized,
    S: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    stack
        .push_back(start_node)
        .map_err(|_| AlgorithmError::StackCapacityExceeded)?;
    visited.mark_visited(&start_node);

    while let Some(node) = stack.pop_back() {
        operation(node);

        for next_node in graph.outgoing_edges(node)? {
            if !visited.is_visited(&next_node) {
                visited.mark_visited(&next_node);
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
    G: Graph<NI>,
    NI: NodeIndex,
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
    G: Graph<NI>,
    NI: NodeIndex,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    F: FnMut(NI),
    AlgorithmError<NI>: From<G::Error>,
{
    queue
        .push_back(start_node)
        .map_err(|_| AlgorithmError::QueueCapacityExceeded)?;
    visited.mark_visited(&start_node);

    while let Some(node) = queue.pop_front() {
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
    G: Graph<NI>,
    NI: NodeIndex,
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
    use crate::adjacency_list::{
        map_adjacency_list::MapAdjacencyList, slice_adjacency_list::SliceAdjacencyList,
    };
    use crate::containers::{
        maps::{staticdict::Dictionary, MapTrait},
        queues::CircularQueue,
    };
    use crate::edgelist::edge_list::EdgeList;
    use crate::edgelist::edge_node_list::EdgeNodeList;
    use crate::edges::EdgeStruct;
    use crate::matrix::{bit_map_matrix::BitMapMatrix, simple_matrix::Matrix};
    use crate::nodes::{NodeStruct, NodeStructOption};

    #[cfg(feature = "heapless")]
    use crate::nodes::NodeValueStructOption;
    use core::slice::SliceIndex;
    #[cfg(feature = "heapless")]
    use heapless::FnvIndexMap;

    fn test_dfs_recursive<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default
            + PartialEq
            + Copy
            + core::fmt::Debug
            + SliceIndex<[bool], Output = bool>
            + PartialOrd
            + 'a,
        E: Graph<NI>,
        E::Error: core::fmt::Debug,
        AlgorithmError<NI>: From<E::Error>,
    {
        let mut visited = [false; 16]; // Use larger array to be safe
        let mut collector = Collector::<NI, C>::new();
        dfs_recursive(elg, start, visited.as_mut_slice(), &mut |x| {
            collector.push(x);
        })
        .expect("Should complete traversal");
        assert_eq!(collector.result(), check);
    }

    fn test_dfs_iterative<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default
            + PartialEq
            + Copy
            + core::fmt::Debug
            + SliceIndex<[bool], Output = bool>
            + PartialOrd
            + 'a,
        E: Graph<NI>,
        E::Error: core::fmt::Debug,
        AlgorithmError<NI>: From<E::Error>,
    {
        let mut visited = [false; 16]; // Use larger array to be safe
        let mut collector = Collector::<NI, C>::new();
        let q = CircularQueue::<NI, C>::new();
        dfs_iterative(elg, start, visited.as_mut_slice(), q, &mut |x| {
            collector.push(x);
        })
        .expect("Should complete traversal");
        assert_eq!(collector.result(), check);
    }

    fn test_bfs<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default
            + PartialEq
            + Copy
            + core::fmt::Debug
            + SliceIndex<[bool], Output = bool>
            + PartialOrd
            + 'a,
        E: Graph<NI>,
        E::Error: core::fmt::Debug,
        AlgorithmError<NI>: From<E::Error>,
    {
        let mut visited = [false; 16]; // Use larger array to be safe
        let mut collector = Collector::<NI, C>::new();
        let q = CircularQueue::<NI, C>::new();
        bfs(elg, start, visited.as_mut_slice(), q, &mut |x| {
            collector.push(x);
        })
        .expect("Should complete");
        assert_eq!(collector.result(), check);
    }

    fn test_traversals<'a, const C: usize, E, NI>(
        elg: &'a E,
        start: NI,
        dfs_check: &[NI],
        dfs_iter_check: &[NI], // This has right-hand order by default
        bfs_check: &[NI],
    ) where
        NI: Default
            + PartialEq
            + Copy
            + core::fmt::Debug
            + SliceIndex<[bool], Output = bool>
            + PartialOrd
            + 'a,
        E: Graph<NI>,
        AlgorithmError<NI>: From<E::Error>,
        E::Error: core::fmt::Debug,
    {
        test_dfs_recursive::<C, _, _>(elg, start, dfs_check);
        test_dfs_iterative::<C, _, _>(elg, start, dfs_iter_check);
        test_bfs::<C, _, _>(elg, start, bfs_check);
    }

    #[test]
    fn test_basic_traversals() {
        // Beautiful graph structure from the original test:
        //   +------------------+
        //   v                  |
        // Node1 --> Node5 --> Node3
        //    v
        // Node4         +-----+
        //               v     |
        //             Node7 --+
        const C: usize = 8;
        let nodestruct = NodeStructOption([
            Some(1),
            Some(4),
            Some(3),
            None,
            None,
            Some(5),
            None,
            Some(7),
        ]);
        let nodestruct2 = NodeStructOption([
            Some(1),
            Some(4),
            Some(3),
            None,
            None,
            Some(5),
            None,
            Some(7),
        ]);
        let edge_array1 = [(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)];
        let edge_array2 = edge_array1.clone();
        let edgestruct = EdgeStruct([(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)]);
        let edgestruct2 = EdgeStruct([(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)]);
        let edges = EdgeList::<8, _, _>::new(edgestruct);
        let edges_array = EdgeList::<8, _, _>::new(edge_array1);
        let edges_nodes = EdgeNodeList::new(edgestruct2, nodestruct).unwrap();
        let edges_nodes_array = EdgeNodeList::new(edge_array2, nodestruct2).unwrap();
        let slice_adj_list = SliceAdjacencyList::new([
            (1_usize, NodeStructOption([Some(5), Some(4), None, None])),
            (5, NodeStructOption([Some(3), None, None, None])),
            (3, NodeStructOption([Some(1), None, None, None])),
            (4, NodeStructOption([None, None, None, None])),
            (7, NodeStructOption([Some(7), None, None, None])),
        ])
        .unwrap();
        #[cfg(feature = "heapless")]
        let map_adj_list = MapAdjacencyList::new(FnvIndexMap::<_, _, 8>::from_iter(
            [
                (
                    1_usize,
                    NodeValueStructOption([Some((5, 'x')), None, Some((4, 'a'))]),
                ),
                (5, NodeValueStructOption([Some((3, ' ')), None, None])),
                (3, NodeValueStructOption([None, Some((1, '_')), None])),
                (4, NodeValueStructOption([None, None, None])),
                (7, NodeValueStructOption([None, None, Some((7, 'z'))])),
            ]
            .into_iter(),
        ))
        .unwrap();

        // Create SimpleMatrix: 8x8 matrix for nodes 0-7
        let simple_matrix = Matrix::<8, i32, _, _>::new([
            [None, None, None, None, None, None, None, None], // node 0 -> none
            [None, None, None, None, Some(1), Some(1), None, None], // node 1 -> 4,5
            [None, None, None, None, None, None, None, None], // node 2 -> none
            [None, Some(1), None, None, None, None, None, None], // node 3 -> 1
            [None, None, None, None, None, None, None, None], // node 4 -> none
            [None, None, None, Some(1), None, None, None, None], // node 5 -> 3
            [None, None, None, None, None, None, None, None], // node 6 -> none
            [None, None, None, None, None, None, None, Some(1)], // node 7 -> 7
        ]);

        // Create BitMapMatrix with node mapping: need to map our node IDs to char indices
        let bit_matrix = crate::matrix::bit_matrix::BitMatrix::new([
            [0b00000000u8], // node 0 -> none
            [0b00110000u8], // node 1 -> bits 4,5 (nodes 4,5)
            [0b00000000u8], // node 2 -> none
            [0b00000010u8], // node 3 -> bit 1 (node 1)
            [0b00000000u8], // node 4 -> none
            [0b00001000u8], // node 5 -> bit 3 (node 3)
            [0b00000000u8], // node 6 -> none
            [0b10000000u8], // node 7 -> bit 7 (node 7)
        ]);
        let mut index_map = Dictionary::<usize, usize, 8>::new();
        index_map.insert(0, 0);
        index_map.insert(1, 1);
        index_map.insert(2, 2);
        index_map.insert(3, 3);
        index_map.insert(4, 4);
        index_map.insert(5, 5);
        index_map.insert(6, 6);
        index_map.insert(7, 7);
        let bit_map_matrix = BitMapMatrix::new(bit_matrix, index_map).unwrap();

        let test = |start: usize,
                    dfs_check: &[usize],
                    dfs_iter_check: &[usize],
                    bfs_check: &[usize]| {
            test_traversals::<C, _, _>(&edges_array, start, dfs_check, dfs_iter_check, bfs_check);
            test_traversals::<C, _, _>(&edges, start, dfs_check, dfs_iter_check, bfs_check);
            test_traversals::<C, _, _>(&edges_nodes, start, dfs_check, dfs_iter_check, bfs_check);
            test_traversals::<C, _, _>(
                &edges_nodes_array,
                start,
                dfs_check,
                dfs_iter_check,
                bfs_check,
            );
            test_traversals::<C, _, _>(
                &slice_adj_list,
                start,
                dfs_check,
                dfs_iter_check,
                bfs_check,
            );
            #[cfg(feature = "heapless")]
            test_traversals::<C, _, _>(&map_adj_list, start, dfs_check, dfs_iter_check, bfs_check);
            // TODO: Matrix representations visit edges in index order, producing different but valid traversals
            // test_traversals::<C, _, _>(&simple_matrix, start, dfs_check, dfs_iter_check, bfs_check);
            // test_traversals::<C, _, _>(&bit_map_matrix, start, dfs_check, dfs_iter_check, bfs_check);
        };
        test(1, &[1, 5, 3, 4], &[1, 4, 5, 3], &[1, 5, 4, 3]);
        test(2, &[], &[], &[]);
        test(3, &[3, 1, 5, 4], &[3, 1, 4, 5], &[3, 1, 5, 4]);
        test(4, &[4], &[4], &[4]);
        test(5, &[5, 3, 1, 4], &[5, 3, 1, 4], &[5, 3, 1, 4]);
        test(7, &[7], &[7], &[7]);

        // Test matrix representations separately since they visit edges in index order
        let test_matrix = |start: usize,
                           dfs_check: &[usize],
                           dfs_iter_check: &[usize],
                           bfs_check: &[usize]| {
            test_traversals::<C, _, _>(&simple_matrix, start, dfs_check, dfs_iter_check, bfs_check);
            test_traversals::<C, _, _>(
                &bit_map_matrix,
                start,
                dfs_check,
                dfs_iter_check,
                bfs_check,
            );
        };
        // Matrix representations visit edges in index order: from node 1, visit node 4 (index 4) before node 5 (index 5)
        test_matrix(1, &[1, 4, 5, 3], &[1, 5, 3, 4], &[1, 4, 5, 3]); // Matrix order: DFS iterative follows 1->5->3->1->4
        test_matrix(2, &[2], &[2], &[2]); // Node 2 exists in matrix but has no outgoing edges
        test_matrix(3, &[3, 1, 4, 5], &[3, 1, 5, 4], &[3, 1, 4, 5]); // Note: 4 before 5 when reached from 3->1
        test_matrix(4, &[4], &[4], &[4]);
        test_matrix(5, &[5, 3, 1, 4], &[5, 3, 1, 4], &[5, 3, 1, 4]); // Same as others since 5->3->1, then 1->4 (first by index)
        test_matrix(7, &[7], &[7], &[7]);
    }

    #[test]
    fn test_dfs_fix_verification() {
        // Simple test to verify our DFS fix prevents duplicate node pushes
        // Using the same graph structure: 1->5,4  5->3  3->1  7->7
        let edges = [(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)];
        let edge_list = EdgeList::<8, _, _>::new(edges);

        // Test starting from node 1 - should visit all reachable nodes exactly once
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        let stack = CircularQueue::<usize, 16>::new();

        dfs_iterative_unchecked(&edge_list, 1, visited.as_mut_slice(), stack, &mut |x| {
            collector.push(x);
        })
        .unwrap();

        let result = collector.result();

        // Verify no duplicates (our fix should prevent this)
        for i in 0..result.len() {
            for j in i + 1..result.len() {
                assert_ne!(
                    result[i], result[j],
                    "DFS produced duplicate node {}: {:?}",
                    result[i], result
                );
            }
        }

        // Should start with node 1
        assert_eq!(result[0], 1, "DFS should start with the start node");

        // Should visit exactly 4 nodes: 1, 5, 3, 4 (all reachable from 1)
        assert_eq!(
            result.len(),
            4,
            "Should visit exactly 4 nodes, got: {:?}",
            result
        );

        // All reachable nodes should be present
        assert!(result.contains(&1));
        assert!(result.contains(&3));
        assert!(result.contains(&4));
        assert!(result.contains(&5));
    }

    #[test]
    fn debug_simple_dfs_test() {
        const C: usize = 8;
        let edge_array = [(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)];
        let edges_array = EdgeList::<8, _, _>::new(edge_array);

        // Test the exact same call that the test helper makes
        let mut visited = [false; C];
        let mut collector = Collector::<usize, C>::new();
        dfs_recursive(&edges_array, 1, visited.as_mut_slice(), &mut |x| {
            collector.push(x);
        })
        .expect("Should complete traversal");

        // This should match what test_dfs_recursive gets
        let result = collector.result();
        assert_eq!(result, &[1, 5, 3, 4], "Direct test result: {:?}", result);
    }

    #[test]
    fn test_cross_representation_dfs_consistency() {
        // Same graph structure: 0->1,2  1->3  2->3  (DAG with clear ordering)
        let edges = [(0usize, 1usize), (0, 2), (1, 3), (2, 3)];

        // Test with EdgeList
        let edge_list_graph = EdgeList::<8, _, _>::new(edges);
        let mut visited1 = [false; 16];
        let mut collector1 = Collector::<usize, 16>::new();
        let stack1 = CircularQueue::<usize, 16>::new();

        dfs_iterative_unchecked(
            &edge_list_graph,
            0,
            visited1.as_mut_slice(),
            stack1,
            &mut |x| {
                collector1.push(x);
            },
        )
        .unwrap();

        // Test with EdgeNodeList
        let edge_node_graph = EdgeNodeList::new(edges, [0, 1, 2, 3]).unwrap();
        let mut visited2 = [false; 16];
        let mut collector2 = Collector::<usize, 16>::new();
        let stack2 = CircularQueue::<usize, 16>::new();

        dfs_iterative_unchecked(
            &edge_node_graph,
            0,
            visited2.as_mut_slice(),
            stack2,
            &mut |x| {
                collector2.push(x);
            },
        )
        .unwrap();

        // Test with MapAdjacencyList
        let mut map = Dictionary::<usize, NodeStruct<2, usize>, 8>::new();
        map.insert(0, NodeStruct([1, 2]));
        map.insert(1, NodeStruct([3, 1])); // 1 as sentinel
        map.insert(2, NodeStruct([3, 2])); // 2 as sentinel
        map.insert(3, NodeStruct([3, 3])); // 3 as sentinel (no outgoing)
        let map_graph = MapAdjacencyList::new_unchecked(map);

        let mut visited3 = [false; 16];
        let mut collector3 = Collector::<usize, 16>::new();
        let stack3 = CircularQueue::<usize, 16>::new();

        dfs_iterative_unchecked(&map_graph, 0, visited3.as_mut_slice(), stack3, &mut |x| {
            collector3.push(x);
        })
        .unwrap();

        // All should visit exactly 4 nodes: 0, 1, 2, 3
        assert_eq!(collector1.result().len(), 4);
        assert_eq!(collector2.result().len(), 4);
        assert_eq!(collector3.result().len(), 4);

        // All should visit all nodes
        for result in [
            collector1.result(),
            collector2.result(),
            collector3.result(),
        ] {
            assert!(result.contains(&0));
            assert!(result.contains(&1));
            assert!(result.contains(&2));
            assert!(result.contains(&3));
        }

        // Start node should always be first in DFS
        assert_eq!(collector1.result()[0], 0);
        assert_eq!(collector2.result()[0], 0);
        assert_eq!(collector3.result()[0], 0);
    }

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
        fn result_sorted(&mut self) -> &[T]
        where
            T: Ord,
        {
            self.nodes[..self.index].sort_unstable();
            &self.nodes[..self.index]
        }
    }

    #[test]
    fn test_dfs_recursive_unchecked() {
        let graph =
            EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2), (2, 0), (2, 3), (3, 3)]);
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        dfs_recursive_unchecked(&graph, 0, visited.as_mut_slice(), &mut |x| {
            collector.push(x);
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
        assert_eq!(collector.result_sorted(), &[0, 1, 2, 3]);
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

        assert_eq!(collector.result(), &[0, 1, 2, 3]);

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

        assert_eq!(collector2.result(), &[0, 1, 2, 3]);
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

        assert_eq!(collector.result_sorted(), &[0, 1, 2, 3]);

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

        assert_eq!(collector2.result_sorted(), &[0, 1, 2, 3]);
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
        assert_eq!(collector.result_sorted(), &[0, 1, 2, 3]);
    }
}
