use crate::containers::maps::MapTrait;
use crate::graph::{GraphValWithEdgeValues, NodeIndexTrait};

use super::AlgorithmError;

/// Dijkstra algorithm to find shortest path between nodes
///
/// Calculates the shortest path from a start node to all other nodes in the graph,
/// does not handle negative edge weights.
///
/// # Arguments
/// * `graph` - Graph implementing GraphValWithEdgeValues
/// * `source` - Source node to find shortest paths from
/// * `distance_map` - Map to store distances, must be pre-initialized with Default values
/// * `has_distance` - Map to track which nodes have finite distance
/// * `visited` - Map to track which nodes have been processed
///
/// # Returns
/// * `Ok(())` if shortest paths computed successfully
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
pub fn dijkstra<G, NI, V, M, S, VIS>(
    graph: &G,
    source: NI,
    distance_map: &mut M,
    has_distance: &mut S,
    visited: &mut VIS,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphValWithEdgeValues<NI, V>,
    NI: NodeIndexTrait + Copy,
    M: MapTrait<NI, V>,
    S: MapTrait<NI, bool>,
    VIS: MapTrait<NI, bool>,
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize distances: source is 0, others are "infinity" (marked as unreachable)
    distance_map.insert(source, V::default());
    has_distance.insert(source, true);

    // Initialize all other nodes as unreachable
    for node in graph.iter_nodes()? {
        if node != source {
            distance_map.insert(node, V::default()); // This will be overwritten when found
            has_distance.insert(node, false);
        }
    }

    // Initialize visited tracking
    for node in graph.iter_nodes()? {
        visited.insert(node, false);
    }

    let node_count = graph.iter_nodes()?.count();

    // Main Dijkstra loop
    for _ in 0..node_count {
        // Find unvisited node with minimum distance
        let mut min_distance = None;
        let mut min_node = None;

        for node in graph.iter_nodes()? {
            if let (Some(is_visited), Some(has_dist), Some(dist)) = (
                visited.get(&node),
                has_distance.get(&node),
                distance_map.get(&node),
            ) {
                if !*is_visited && *has_dist {
                    if let Some(current_min) = min_distance {
                        if *dist < current_min {
                            min_distance = Some(*dist);
                            min_node = Some(node);
                        }
                    } else {
                        min_distance = Some(*dist);
                        min_node = Some(node);
                    }
                }
            }
        }

        // If no unvisited node found, we're done
        let u = match min_node {
            Some(node) => node,
            None => break,
        };

        // Mark current node as visited
        visited.insert(u, true);

        // Update distances to neighbors
        for (src, dst, weight_opt) in graph.iter_edge_values()? {
            if src == u {
                if let Some(weight) = weight_opt {
                    if let (Some(u_dist), Some(dst_visited)) =
                        (distance_map.get(&u), visited.get(&dst))
                    {
                        if !*dst_visited {
                            let new_distance = *u_dist + *weight;

                            if let (Some(dst_has_dist), Some(dst_dist)) =
                                (has_distance.get(&dst), distance_map.get(&dst))
                            {
                                if !*dst_has_dist || new_distance < *dst_dist {
                                    distance_map.insert(dst, new_distance);
                                    has_distance.insert(dst, true);
                                }
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
    fn test_dijkstra_simple() {
        //    (1)        (2)
        //A ------ B -------- C
        // \       |          |
        //  \      |(5)       |(1)
        //   \     |          |
        //    \    D ---------
        //     \              |
        //      \_____________|
        //          (4)

        // Create the graph with positive edge weights
        let edge_data = EdgeValueStruct([
            ('A', 'B', 1),
            ('A', 'C', 4),
            ('B', 'C', 2),
            ('B', 'D', 5),
            ('C', 'D', 1),
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut distance_map = Dictionary::<char, i32, 16>::new();
        let mut has_distance = Dictionary::<char, bool, 16>::new();
        let mut visited = Dictionary::<char, bool, 16>::new();

        dijkstra(
            &graph,
            'A',
            &mut distance_map,
            &mut has_distance,
            &mut visited,
        )
        .unwrap();

        // Check the expected distances
        assert_eq!(distance_map.get(&'A'), Some(&0));
        assert_eq!(distance_map.get(&'B'), Some(&1));
        assert_eq!(distance_map.get(&'C'), Some(&3)); // 1 (A->B) + 2 (B->C)
        assert_eq!(distance_map.get(&'D'), Some(&4)); // 3 (A->B->C) + 1 (C->D)

        // Check that all nodes have finite distance
        assert_eq!(has_distance.get(&'A'), Some(&true));
        assert_eq!(has_distance.get(&'B'), Some(&true));
        assert_eq!(has_distance.get(&'C'), Some(&true));
        assert_eq!(has_distance.get(&'D'), Some(&true));
    }

    #[test]
    fn test_dijkstra_disconnected() {
        // Create disconnected graph: 0 -> 1 (weight 2), 2 isolated
        let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut distance_map = Dictionary::<usize, i32, 16>::new();
        let mut has_distance = Dictionary::<usize, bool, 16>::new();
        let mut visited = Dictionary::<usize, bool, 16>::new();

        dijkstra(
            &graph,
            0,
            &mut distance_map,
            &mut has_distance,
            &mut visited,
        )
        .unwrap();

        // Check distances - node 1 should be reachable
        assert_eq!(distance_map.get(&0), Some(&0));
        assert_eq!(distance_map.get(&1), Some(&2));
        assert_eq!(has_distance.get(&0), Some(&true));
        assert_eq!(has_distance.get(&1), Some(&true));
    }
}
