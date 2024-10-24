// SPDX-License-Identifier: Apache-2.0

//! Common traversal algorithms
//!
//! Implements common traversal algorithms.

use crate::containers::queues::Deque;
use crate::graph::Graph;
use crate::VisitedTracker;

use super::AlgorithmError;

/// Unchecked depth first traversal
///
/// Always yields the initial node, even if it is not present in graph
pub fn dfs_recursive_unchecked<T, NI, VT, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    for<'b> F: FnMut(&'b NI),
{
    if !visited.is_visited(&node) {
        visited.mark_visited(&node);
        operation(&node);
    }
    for next_node in graph.outgoing_edges_for_node(&node)? {
        if !visited.is_visited(next_node) {
            dfs_recursive_unchecked(graph, *next_node, visited, operation)?;
        }
    }
    Ok(())
}

/// Depth first recursive traversal
///
/// Does not index initial node, if initial node is not present in the graph
pub fn dfs_recursive<T, NI, VT, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    for<'b> F: FnMut(&'b NI),
{
    // Check if first node exists
    if !graph.contains_node(&node)? {
        return Ok(());
    }
    dfs_recursive_unchecked(graph, node, visited, operation)
}

/// Unchecked iterative depth first traversal, using a stack
///
/// Always yields the initial node, even if it is not present in graph
pub fn dfs_iterative_unchecked<T, NI, VT, Q, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    mut stack: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    for<'b> F: FnMut(&'b NI),
{
    stack.push_back(node);
    while let Some(node) = stack.pop_back() {
        if visited.is_visited(&node) {
            continue;
        }
        visited.mark_visited(&node);
        operation(&node);
        for next_node in graph.outgoing_edges_for_node(&node)?.rev() {
            if !visited.is_visited(next_node) {
                stack.push_back(*next_node);
            }
        }
    }
    Ok(())
}

/// Iterative depth first traversal, using a stack
///
/// Does not index initial node, if initial node is not present in graph
pub fn dfs_iterative<T, NI, VT, Q, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    stack: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    for<'b> F: FnMut(&'b NI),
{
    // Check if first node exists
    if !graph.contains_node(&node)? {
        return Ok(());
    }
    dfs_iterative_unchecked(graph, node, visited, stack, operation)
}

/// Unchecked breadth first traversal, using a queue
///
/// Always yields the initial node, even if it is not present in graph
pub fn bfs_unchecked<T, NI, VT, Q, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    mut queue: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    for<'b> F: FnMut(&'b NI),
{
    queue.push_back(node);
    visited.mark_visited(&node);
    while !queue.is_empty() {
        if let Some(node) = queue.pop_back() {
            operation(&node);

            for next_node in graph.outgoing_edges_for_node(&node)? {
                if !visited.is_visited(next_node) {
                    visited.mark_visited(next_node);
                    queue.push_front(*next_node);
                }
            }
        }
    }
    Ok(())
}

/// Breadth first traversal, using a queue
///
/// Does not index initial node, if initial node is not present in graph
pub fn bfs<T, NI, VT, Q, F>(
    graph: &T,
    node: NI,
    visited: &mut VT,
    queue: Q,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    T: Graph<NI>,
    VT: VisitedTracker<NI> + ?Sized,
    Q: Deque<NI>,
    for<'b> F: FnMut(&'b NI),
{
    // Check if start_node exists in the edges list
    if !graph.contains_node(&node)? {
        return Ok(());
    }
    bfs_unchecked(graph, node, visited, queue, operation)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "heapless")]
    use crate::adjacency_list::MapAdjacencyList;
    use crate::adjacency_list::{EdgesOnly, SliceAdjacencyList};
    use crate::containers::queues::CircularQueue;
    use crate::edge_list::{EdgeList, EdgeNodeList};
    use crate::edges::EdgeStruct;
    use crate::nodes::{NodeStructOption, NodeValueStructOption};
    use core::slice::SliceIndex;

    fn test_dfs_recursive<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default + PartialEq + Copy + core::fmt::Debug + SliceIndex<[bool], Output = bool> + 'a,
        E: Graph<NI>,
    {
        let mut visited = [false; C];
        let mut collect: [NI; C] = core::array::from_fn(|_| NI::default());
        let mut iter = collect.iter_mut();
        dfs_recursive(elg, start, visited.as_mut_slice(), &mut |x| {
            if let Some(val) = iter.next() {
                *val = *x;
            }
        })
        .expect("Should complete traversal");
        let collected_len = C - iter.len();
        assert_eq!(&collect[..collected_len], check);
    }
    fn test_dfs_iterative<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default + PartialEq + Copy + core::fmt::Debug + SliceIndex<[bool], Output = bool> + 'a,
        E: Graph<NI>,
    {
        let mut visited = [false; C];
        let mut collect: [NI; C] = core::array::from_fn(|_| NI::default());
        let mut iter = collect.iter_mut();
        let q = CircularQueue::<NI, C>::new();
        dfs_iterative(elg, start, visited.as_mut_slice(), q, &mut |x| {
            if let Some(val) = iter.next() {
                *val = *x;
            }
        })
        .expect("Should complete traversal");
        let collected_len = C - iter.len();
        assert_eq!(&collect[..collected_len], check);
    }

    fn test_bfs<'a, const C: usize, E, NI>(elg: &'a E, start: NI, check: &[NI])
    where
        NI: Default + PartialEq + Copy + core::fmt::Debug + SliceIndex<[bool], Output = bool> + 'a,
        E: Graph<NI>,
    {
        let mut visited = [false; C];
        let mut collect: [NI; C] = core::array::from_fn(|_| NI::default());
        let mut iter = collect.iter_mut();
        let q = CircularQueue::<NI, C>::new();
        bfs(elg, start, visited.as_mut_slice(), q, &mut |x| {
            if let Some(val) = iter.next() {
                *val = *x;
            }
        })
        .expect("Should complete");
        let collected_len = C - iter.len();
        assert_eq!(&collect[..collected_len], check);
    }
    fn test_traversals<'a, const C: usize, E, NI>(
        elg: &'a E,
        start: NI,
        dfs_check: &[NI],
        bfs_check: &[NI],
    ) where
        NI: Default + PartialEq + Copy + core::fmt::Debug + SliceIndex<[bool], Output = bool> + 'a,
        E: Graph<NI>,
    {
        test_dfs_recursive::<C, _, _>(elg, start, dfs_check);
        test_dfs_iterative::<C, _, _>(elg, start, dfs_check);
        test_bfs::<C, _, _>(elg, start, bfs_check);
    }

    #[test]
    fn test_basic_traversals() {
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
        let edges = EdgeList::<8, _, _>::new(edgestruct).unwrap();
        let edges_array = EdgeList::<8, _, _>::new(edge_array1).unwrap();
        let edges_nodes = EdgeNodeList::new(edgestruct2, nodestruct).unwrap();
        let edges_nodes_array = EdgeNodeList::new(edge_array2, nodestruct2).unwrap();
        let slice_adj_list = SliceAdjacencyList::new([
            (
                1_usize,
                EdgesOnly(NodeStructOption([Some(5), None, Some(4), None])),
            ),
            (5, EdgesOnly(NodeStructOption([Some(3), None, None, None]))),
            (3, EdgesOnly(NodeStructOption([None, Some(1), None, None]))),
            (4, EdgesOnly(NodeStructOption([None, None, None, None]))),
            (7, EdgesOnly(NodeStructOption([None, None, None, Some(7)]))),
        ])
        .unwrap();
        #[cfg(feature = "heapless")]
        let map_adj_list = MapAdjacencyList::new(heapless::FnvIndexMap::<_, _, 8>::from_iter(
            [
                (
                    1_usize,
                    (
                        "node 1",
                        NodeValueStructOption([Some((5, 'x')), None, Some((4, 'a'))]),
                    ),
                ),
                (
                    5,
                    ("five!", NodeValueStructOption([Some((3, ' ')), None, None])),
                ),
                (
                    3,
                    ("three", NodeValueStructOption([None, Some((1, '_')), None])),
                ),
                (4, (" ", NodeValueStructOption([None, None, None]))),
                (
                    7,
                    ("seven", NodeValueStructOption([None, None, Some((7, 'z'))])),
                ),
            ]
            .into_iter(),
        ))
        .unwrap();
        let test = |start: usize, dfs_check: &[usize], bfs_check: &[usize]| {
            test_traversals::<C, _, _>(&edges_array, start, dfs_check, bfs_check);
            test_traversals::<C, _, _>(&edges, start, dfs_check, bfs_check);
            test_traversals::<C, _, _>(&edges_nodes, start, dfs_check, bfs_check);
            test_traversals::<C, _, _>(&edges_nodes_array, start, dfs_check, bfs_check);
            test_traversals::<C, _, _>(&slice_adj_list, start, dfs_check, bfs_check);
            #[cfg(feature = "heapless")]
            test_traversals::<C, _, _>(&map_adj_list, start, dfs_check, bfs_check);
        };
        test(1, &[1, 5, 3, 4], &[1, 5, 4, 3]);
        test(2, &[], &[]);
        test(3, &[3, 1, 5, 4], &[3, 1, 5, 4]);
        test(4, &[4], &[4]);
        test(5, &[5, 3, 1, 4], &[5, 3, 1, 4]);
        test(7, &[7], &[7]);
    }
}
