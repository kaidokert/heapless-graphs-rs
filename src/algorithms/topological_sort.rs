// SPDX-License-Identifier: Apache-2.0

use crate::{visited::TriStateVisitedTracker, Graph};

use super::AlgorithmError;

/// Depth-first post-order traversal, with nodes enumerated in reverse order
///
/// Detects cycles
fn dfs_recursive_postorder<G, NI, VT, F>(
    graph: &G,
    node: NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), AlgorithmError<NI>>
where
    NI: PartialEq + Copy + core::fmt::Debug,
    G: Graph<NodeIndex = NI>,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    F: FnMut(&NI),
    AlgorithmError<NI>: From<G::Error>,
{
    if visited.is_visited(&node) {
        return Ok(());
    }
    visited.mark_visiting(&node);
    for next_node in graph.outgoing_edges_for_node(&node)? {
        if visited.is_visiting(next_node) {
            return Err(AlgorithmError::CycleDetected {
                outgoing_edge: *next_node,
                incoming_edge: node,
            });
        }
        if !visited.is_visited(next_node) {
            dfs_recursive_postorder(graph, *next_node, visited, operation)?;
        }
    }
    visited.mark_visited(&node);
    operation(&node);
    Ok(())
}

/// Topological sort of a directed graph
///
/// Returns an error if a cycle is found
pub fn topological_sort<'a, G, NI, VT>(
    graph: &G,
    visited: &mut VT,
    sorted_nodes: &'a mut [NI],
) -> Result<&'a [NI], AlgorithmError<NI>>
where
    NI: PartialEq + Copy + core::fmt::Debug,
    G: Graph<NodeIndex = NI>,
    VT: TriStateVisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    let mut sort_index = 0;
    let mut append_to_list = |node: &NI| {
        sorted_nodes[sort_index] = *node;
        sort_index += 1;
    };
    for node in graph.get_nodes()? {
        if visited.is_unvisited(node) {
            dfs_recursive_postorder(graph, *node, visited, &mut append_to_list)?;
        }
    }
    // Catch isolated nodes
    for node in graph.get_nodes()? {
        if visited.is_unvisited(node) {
            append_to_list(node);
        }
    }
    let sorted_slice = &mut sorted_nodes[..sort_index];
    sorted_slice.reverse();
    Ok(sorted_slice)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edge_list::{EdgeList, EdgeNodeList};
    use crate::edges::EdgeStruct;
    use crate::nodes::{NodeStruct, NodeValueTwoArray};
    use crate::NodeState;
    use core::slice::SliceIndex;

    fn test_topological<'a, const C: usize, E, NI>(elg: &'a E, order_check: &[NI])
    where
        NI: Default
            + PartialEq
            + Copy
            + core::fmt::Debug
            + SliceIndex<[NodeState], Output = NodeState>
            + 'a,
        E: Graph<NodeIndex = NI>,
        AlgorithmError<NI>: From<E::Error>,
    {
        let mut storage: [NI; C] = core::array::from_fn(|_| NI::default());
        let mut visited = [NodeState::Unvisited; 8];
        let sort_slice =
            topological_sort(elg, visited.as_mut_slice(), storage.as_mut_slice()).unwrap();
        assert_eq!(sort_slice, order_check);
    }

    #[test]
    fn test_topological_sort() {
        // Node1 --> Node5 --> Node3
        //   v          Node0    Node6
        // Node4   Node2 --> Node7
        let edge_struct = EdgeStruct([(5, 3), (1_usize, 5), (2, 7), (1, 4)]);
        let edge_struct2 = EdgeStruct([(5, 3), (1_usize, 5), (2, 7), (1, 4)]);
        let edges = EdgeList::<8, _, _>::new(edge_struct).unwrap();
        test_topological::<8, _, _>(&edges, &[2, 7, 1, 4, 5, 3]);
        let node_struct = NodeValueTwoArray(
            [1, 4, 3, 6, 0, 5, 2, 7],
            ['b', 'c', 'd', 'a', 'e', 'f', 'g', 'h'],
        );
        let edges_with_nodes = EdgeNodeList::new(edge_struct2, node_struct).unwrap();
        test_topological::<8, _, _>(&edges_with_nodes, &[2, 7, 0, 6, 1, 4, 5, 3]);
    }
    #[test]
    fn test_empty_topolocical() {
        let empty_edges_with_nodes =
            EdgeNodeList::new(EdgeStruct::<0, usize>([]), NodeStruct([])).unwrap();
        test_topological::<0, _, _>(&empty_edges_with_nodes, &[]);
    }
    #[test]
    fn test_one_topolocical() {
        let single_node = EdgeStruct([]); // no edges
        let single_node_with_value = NodeValueTwoArray([0], ['a']);
        let edges_with_single_node =
            EdgeNodeList::new(single_node, single_node_with_value).unwrap();
        test_topological::<1, _, _>(&edges_with_single_node, &[0]);
    }
    #[test]
    fn test_cycles_topological() {
        let cyclic_edges = EdgeStruct([(1, 2), (2, 3), (3, 1)]);
        let edges = EdgeList::<5, _, _>::new(cyclic_edges).unwrap();
        let mut visited = [NodeState::Unvisited; 8];
        let mut storage = [0; 5];
        assert_eq!(
            topological_sort(&edges, visited.as_mut_slice(), &mut storage),
            Err(AlgorithmError::CycleDetected {
                incoming_edge: 3,
                outgoing_edge: 1
            })
        );
    }
    #[test]
    fn test_duplicate_edges_topological() {
        let edges = EdgeStruct([(0, 1), (0, 1)]);
        let duplicate_edges = EdgeList::<8, _, _>::new(edges).unwrap();
        test_topological::<3, _, _>(&duplicate_edges, &[0, 1]);
    }
    #[test]
    fn test_fully_connected_dag_topological() {
        let fully_connected_dag = EdgeStruct([(1, 2), (0, 1), (0, 2)]);
        let edges = EdgeList::<8, _, _>::new(fully_connected_dag).unwrap();
        test_topological::<3, _, _>(&edges, &[0, 1, 2]);
    }
}
