use crate::containers::maps::MapTrait;
use crate::graph::{GraphValWithEdgeValues, NodeIndexTrait};

use super::AlgorithmError;

/// Bellman-Ford algorithm for finding shortest paths from a source node
///
/// This algorithm can handle graphs with negative edge weights and will detect
/// negative cycles. It requires edge weights through GraphValWithEdgeValues.
/// Uses the standard |V|-1 iterations automatically.
///
/// # Arguments
/// * `graph` - Graph implementing GraphValWithEdgeValues
/// * `source` - Source node to find shortest paths from
/// * `distance_map` - Map to store distances (None = infinite/unreachable, Some(v) = distance v)
///
/// # Returns
/// * `Ok(M)` populated distance map if shortest paths computed successfully
/// * `Err(AlgorithmError::CycleDetected)` if negative cycle detected
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
pub fn bellman_ford<G, NI, V, M>(
    graph: &G,
    source: NI,
    distance_map: M,
) -> Result<M, AlgorithmError<NI>>
where
    G: GraphValWithEdgeValues<NI, V>,
    NI: NodeIndexTrait + Copy,
    M: MapTrait<NI, Option<V>>,
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Auto-compute |V|-1 iterations
    let node_count = graph.iter_nodes()?.count();
    let max_iterations = if node_count > 0 { node_count - 1 } else { 0 };
    bellman_ford_bounded(graph, source, distance_map, max_iterations)
}

/// Bellman-Ford algorithm with custom iteration limit
///
/// This algorithm can handle graphs with negative edge weights and will detect
/// negative cycles. It requires edge weights through GraphValWithEdgeValues.
/// Allows custom control over the maximum number of iterations.
///
/// # Arguments
/// * `graph` - Graph implementing GraphValWithEdgeValues
/// * `source` - Source node to find shortest paths from
/// * `distance_map` - Map to store distances (None = infinite/unreachable, Some(v) = distance v)
/// * `max_iterations` - Maximum number of iterations (typically |V|-1)
///
/// # Returns
/// * `Ok(M)` populated distance map if shortest paths computed successfully
/// * `Err(AlgorithmError::CycleDetected)` if negative cycle detected
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
pub fn bellman_ford_bounded<G, NI, V, M>(
    graph: &G,
    source: NI,
    mut distance_map: M,
    max_iterations: usize,
) -> Result<M, AlgorithmError<NI>>
where
    G: GraphValWithEdgeValues<NI, V>,
    NI: NodeIndexTrait + Copy,
    M: MapTrait<NI, Option<V>>,
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize: source has distance 0, others are None (infinite/unreachable)
    distance_map.insert(source, Some(V::default()));

    for node in graph.iter_nodes()? {
        if node != source {
            distance_map.insert(node, None);
        }
    }

    // Relax edges repeatedly
    for _ in 0..max_iterations {
        let mut changed = false;

        for (src, dst, weight_opt) in graph.iter_edge_values()? {
            if let Some(weight) = weight_opt {
                if let Some(Some(src_dist)) = distance_map.get(&src) {
                    let new_distance = *src_dist + *weight;

                    if let Some(dst_dist_opt) = distance_map.get(&dst) {
                        if dst_dist_opt.is_none() || new_distance < dst_dist_opt.unwrap() {
                            distance_map.insert(dst, Some(new_distance));
                            changed = true;
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
            if let Some(Some(src_dist)) = distance_map.get(&src) {
                if let Some(Some(dst_dist)) = distance_map.get(&dst) {
                    let new_distance = *src_dist + *weight;
                    if new_distance < *dst_dist {
                        return Err(AlgorithmError::CycleDetected);
                    }
                }
            }
        }
    }

    Ok(distance_map)
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

        let distance_map = Dictionary::<usize, Option<i32>, 16>::new();

        let result = bellman_ford(&graph, 0, distance_map).unwrap();

        assert_eq!(result.get(&0), Some(&Some(0)));
        assert_eq!(result.get(&1), Some(&Some(5)));
        assert_eq!(result.get(&2), Some(&Some(8)));
    }

    #[test]
    fn test_bellman_ford_negative_cycle() {
        // Create graph with negative cycle: 0 -> 1 (weight -1), 1 -> 0 (weight -1)
        let edge_data = EdgeValueStruct([(0usize, 1usize, -1i32), (1, 0, -1)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let distance_map = Dictionary::<usize, Option<i32>, 16>::new();

        let result = bellman_ford_bounded(&graph, 0, distance_map, 1);
        assert!(matches!(result, Err(AlgorithmError::CycleDetected)));
    }

    #[test]
    fn test_bellman_ford_disconnected() {
        // Create disconnected graph: 0 -> 1 (weight 2), 2 isolated
        let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let distance_map = Dictionary::<usize, Option<i32>, 16>::new();

        let result = bellman_ford(&graph, 0, distance_map).unwrap();

        // Check distances - node 1 should be reachable
        assert_eq!(result.get(&0), Some(&Some(0)));
        assert_eq!(result.get(&1), Some(&Some(2)));
        // Note: node 2 doesn't exist in this graph, so we can't check has_distance for it
    }
}
