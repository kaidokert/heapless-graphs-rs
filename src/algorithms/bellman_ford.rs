use crate::containers::maps::MapTrait;
use crate::graph::{GraphValWithEdgeValues, NodeIndexTrait};

use super::AlgorithmError;

/// Bellman-Ford algorithm for finding shortest paths from a source node
///
/// This algorithm can handle graphs with negative edge weights and will detect
/// negative cycles. It requires edge weights through GraphValWithEdgeValues.
///
/// # Arguments
/// * `graph` - Graph implementing GraphValWithEdgeValues
/// * `source` - Source node to find shortest paths from
/// * `distance_map` - Map to store distances, must be pre-initialized with Default values
/// * `has_distance` - Map to track which nodes have finite distance
/// * `max_iterations` - Maximum number of iterations (typically |V|-1)
///
/// # Returns
/// * `Ok(())` if shortest paths computed successfully
/// * `Err(AlgorithmError::CycleDetected)` if negative cycle detected
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
pub fn bellman_ford<G, NI, V, M, S>(
    graph: &G,
    source: NI,
    distance_map: &mut M,
    has_distance: &mut S,
    max_iterations: usize,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphValWithEdgeValues<NI, V>,
    NI: NodeIndexTrait + Copy,
    M: MapTrait<NI, V>,
    S: MapTrait<NI, bool>,
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize: source has distance 0, others have infinite distance
    distance_map.insert(source, V::default());
    has_distance.insert(source, true);

    for node in graph.iter_nodes()? {
        if node != source {
            distance_map.insert(node, V::default());
            has_distance.insert(node, false);
        }
    }

    // Relax edges repeatedly
    for _ in 0..max_iterations {
        let mut changed = false;

        for (src, dst, weight_opt) in graph.iter_edge_values()? {
            if let Some(weight) = weight_opt {
                if let (Some(src_has_dist), Some(src_dist)) =
                    (has_distance.get(&src), distance_map.get(&src))
                {
                    if *src_has_dist {
                        let new_distance = *src_dist + *weight;

                        if let (Some(dst_has_dist), Some(dst_dist)) =
                            (has_distance.get(&dst), distance_map.get(&dst))
                        {
                            if !*dst_has_dist || new_distance < *dst_dist {
                                distance_map.insert(dst, new_distance);
                                has_distance.insert(dst, true);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        if !changed {
            break;
        }
    }

    // Check for negative cycles
    for (src, dst, weight_opt) in graph.iter_edge_values()? {
        if let Some(weight) = weight_opt {
            if let (Some(src_has_dist), Some(src_dist)) =
                (has_distance.get(&src), distance_map.get(&src))
            {
                if *src_has_dist {
                    if let (Some(dst_has_dist), Some(dst_dist)) =
                        (has_distance.get(&dst), distance_map.get(&dst))
                    {
                        if *dst_has_dist {
                            let new_distance = *src_dist + *weight;
                            if new_distance < *dst_dist {
                                return Err(AlgorithmError::CycleDetected);
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::edges::EdgeValueStruct;

    #[test]
    fn test_bellman_ford_simple() {
        // Create a simple weighted graph: 0 -> 1 (weight 5), 1 -> 2 (weight 3)
        let edge_data = EdgeValueStruct([(0usize, 1usize, 5i32), (1, 2, 3)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut distance_map = Dictionary::<usize, i32, 16>::new();
        let mut has_distance = Dictionary::<usize, bool, 16>::new();

        bellman_ford(&graph, 0, &mut distance_map, &mut has_distance, 2).unwrap();

        assert_eq!(distance_map.get(&0), Some(&0));
        assert_eq!(distance_map.get(&1), Some(&5));
        assert_eq!(distance_map.get(&2), Some(&8));

        // Check that all nodes have finite distance
        assert_eq!(has_distance.get(&0), Some(&true));
        assert_eq!(has_distance.get(&1), Some(&true));
        assert_eq!(has_distance.get(&2), Some(&true));
    }

    #[test]
    fn test_bellman_ford_negative_cycle() {
        // Create graph with negative cycle: 0 -> 1 (weight -1), 1 -> 0 (weight -1)
        let edge_data = EdgeValueStruct([(0usize, 1usize, -1i32), (1, 0, -1)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut distance_map = Dictionary::<usize, i32, 16>::new();
        let mut has_distance = Dictionary::<usize, bool, 16>::new();

        let result = bellman_ford(&graph, 0, &mut distance_map, &mut has_distance, 1);
        assert_eq!(result, Err(AlgorithmError::CycleDetected));
    }

    #[test]
    fn test_bellman_ford_disconnected() {
        // Create disconnected graph: 0 -> 1 (weight 2), 2 isolated
        let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut distance_map = Dictionary::<usize, i32, 16>::new();
        let mut has_distance = Dictionary::<usize, bool, 16>::new();

        bellman_ford(&graph, 0, &mut distance_map, &mut has_distance, 2).unwrap();

        // Check distances - node 2 should be unreachable
        assert_eq!(distance_map.get(&0), Some(&0));
        assert_eq!(distance_map.get(&1), Some(&2));
        assert_eq!(has_distance.get(&0), Some(&true));
        assert_eq!(has_distance.get(&1), Some(&true));
        // Note: node 2 doesn't exist in this graph, so we can't check has_distance for it
    }

    #[test]
    fn test_bellman_ford_placeholder() {
        // Basic test to ensure the function compiles correctly
        let mut distance_map = Dictionary::<usize, i32, 16>::new();
        let mut has_distance = Dictionary::<usize, bool, 16>::new();

        // Insert some test values to ensure maps work
        distance_map.insert(0, 42);
        has_distance.insert(0, true);

        assert_eq!(distance_map.get(&0), Some(&42));
        assert_eq!(has_distance.get(&0), Some(&true));
    }
}
