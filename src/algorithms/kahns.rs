// SPDX-License-Identifier: Apache-2.0

use crate::{
    containers::{maps::MapTrait, queues::Deque},
    Graph,
};

use super::{AlgorithmError, OptionResultExt};

/// Kahn's algorithm for topologically sorting a graph
///
/// Does not need a starting node, works with disconnected
/// graphs and detects cycles.
pub fn kahns<'a, NI, G, Q, M>(
    graph: &G,
    mut queue: Q,
    mut in_degree_map: M,
    sorted_nodes: &'a mut [NI],
) -> Result<&'a [NI], AlgorithmError<NI>>
where
    NI: PartialEq + Copy + core::fmt::Debug,
    G: Graph<NodeIndex = NI>,
    Q: Deque<NI>,
    M: MapTrait<NI, isize>,
    AlgorithmError<NI>: From<G::Error>,
{
    let mut sort_index = 0;
    let mut append_to_list = |node: &NI| -> Result<(), AlgorithmError<NI>> {
        if sort_index >= sorted_nodes.len() {
            return Err(AlgorithmError::OutputCapacityExceeded);
        }
        sorted_nodes[sort_index] = *node;
        sort_index += 1;
        Ok(())
    };
    for node in graph.get_nodes()? {
        in_degree_map.insert(*node, 0);
    }
    // Count incoming connections for all nodes
    for (_, dst) in graph.get_edges()? {
        let mut in_degree = *in_degree_map.get(dst).dict_error()?;
        in_degree += 1;
        in_degree_map.insert(*dst, in_degree);
    }
    // Get nodes with no incoming connections
    for (node, &deg) in in_degree_map.iter() {
        if deg == 0 {
            queue
                .push_back(*node)
                .map_err(|_| AlgorithmError::StackCapacityExceeded)?;
        }
    }
    while let Some(node) = queue.pop_back() {
        append_to_list(&node)?;
        for &neighbor in graph.neighboring_nodes(&node)? {
            let mut in_degree = *in_degree_map.get(&neighbor).dict_error()?;
            in_degree -= 1;
            in_degree_map.insert(neighbor, in_degree);
            if in_degree == 0 {
                queue
                    .push_back(neighbor)
                    .map_err(|_| AlgorithmError::StackCapacityExceeded)?;
            }
        }
    }
    // Cycle detection
    if sort_index != in_degree_map.len() {
        return Err(AlgorithmError::CycleDetectedInConsistencyCheck);
    }
    let sorted_slice = &mut sorted_nodes[..sort_index];
    Ok(sorted_slice)
}

#[cfg(test)]
mod test {
    use crate::{
        containers::{maps::staticdict::Dictionary, queues::CircularQueue},
        edge_list::{EdgeList, EdgeNodeList},
    };

    use super::*;

    #[test]
    fn test_basic() {
        // Node1 --> Node5 --> Node3
        //    v
        // Node4
        let mut sorted_nodes = [0; 5];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let edges = [(5, 3), (1, 4), (1_usize, 5)];
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, [1, 5, 3, 4]);
    }

    #[test]
    fn test_cycle_detection() {
        // Node1 --> Node2 --> Node3
        //    ^              |
        //    +--------------+
        let mut sorted_nodes = [0; 3];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let edges = [(1_usize, 2), (2, 3), (3, 1)];
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert!(result.is_err());
    }

    #[test]
    fn test_disconnected_graph() {
        // Node1 --> Node2
        // Node3 --> Node4
        let mut sorted_nodes = [0; 4];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new([(1_usize, 2), (3, 4)]).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, [1, 2, 3, 4]);
    }

    #[test]
    fn test_single_node() {
        // Node1 with no edges
        let mut sorted_nodes = [0; 1];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let edges: [(usize, usize); 0] = [];
        let graph = EdgeNodeList::new(edges, [1_usize]).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, [1]);
    }

    #[test]
    fn test_empty_graph() {
        let edges: [(usize, usize); 0] = [];
        let mut sorted_nodes = [0; 0];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeNodeList::new(edges, []).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, []);
    }

    #[test]
    fn test_queue_capacity_error() {
        let mut sorted_nodes = [0; 4];
        let queue = CircularQueue::<usize, 2>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new([(1_usize, 2), (3, 4), (5, 6)]).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert_eq!(result, Err(AlgorithmError::StackCapacityExceeded));
    }

    #[test]
    fn test_dict_capacity_error() {
        // Test with a small dictionary that cannot hold all necessary nodes
        // Graph: Node1 --> Node2 --> Node3 --> Node4
        let edges = [(1_usize, 2), (2, 3), (3, 4)];
        let mut sorted_nodes = [0; 4];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 2>::new();
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert_eq!(result, Err(AlgorithmError::DictionaryError));
    }

    #[test]
    fn test_queue_and_dict_exact_capacity() {
        // Test with queue and dictionary having exactly the required capacity
        // Graph: Node1 --> Node2
        // Node3 --> Node4
        let edges = [(1_usize, 2), (3, 4)];
        let mut sorted_nodes = [0; 4];
        let queue = CircularQueue::<usize, 2>::new(); // Exact capacity
        let dict = Dictionary::<_, _, 4>::new(); // Exact capacity
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, [1, 2, 3, 4]);
    }

    #[test]
    fn test_output_capacity_exceeded() {
        // Graph: Node1 --> Node2 --> Node3
        let mut sorted_nodes = [0; 2]; // Insufficient capacity
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new([(1_usize, 2), (2, 3)]).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert_eq!(result, Err(AlgorithmError::OutputCapacityExceeded));
    }

    #[test]
    fn test_self_loop_detection() {
        // Graph: Node1 --> Node1 (self-loop)
        let edges = [(1_usize, 1)];
        let mut sorted_nodes = [0; 1];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert!(matches!(
            result,
            Err(AlgorithmError::CycleDetectedInConsistencyCheck)
        ));
    }

    #[test]
    fn test_parallel_edges() {
        // Graph: Node1 --> Node2 (two parallel edges)
        let edges = [(1_usize, 2), (1, 2)];
        let mut sorted_nodes = [0; 2];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, [1, 2]);
    }

    #[test]
    fn test_complex_cycle_detection() {
        // Graph with interlinked cycles
        // Node1 --> Node2 --> Node3 --> Node1
        //             |
        //             v
        //           Node4 --> Node5 --> Node2
        let edges = [(1_usize, 2), (2, 3), (3, 1), (2, 4), (4, 5), (5, 2)];
        let mut sorted_nodes = [0; 5];
        let queue = CircularQueue::<usize, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<10, _, _>::new(edges).unwrap();
        let result = kahns(&graph, queue, dict, &mut sorted_nodes);
        assert!(matches!(
            result,
            Err(AlgorithmError::CycleDetectedInConsistencyCheck)
        ));
    }

    #[test]
    fn test_non_integer_node_identifiers() {
        // Use &str as node identifiers
        let edges = [("Node1", "Node2"), ("Node2", "Node3")];
        let mut sorted_nodes = [""; 3];
        let queue = CircularQueue::<&str, 10>::new();
        let dict = Dictionary::<_, _, 10>::new();
        let graph = EdgeList::<8, _, _>::new(edges).unwrap();
        let sorted = kahns(&graph, queue, dict, &mut sorted_nodes).unwrap();
        assert_eq!(sorted, ["Node1", "Node2", "Node3"]);
    }
}
