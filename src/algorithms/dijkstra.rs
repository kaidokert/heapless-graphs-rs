// SPDX-License-Identifier: Apache-2.0

//! Dijkstra algorithm for finding shortest paths

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
/// * `visited` - Map to track which nodes have been processed
/// * `distance_map` - Map to store distances (None = infinite/unreachable, Some(v) = distance v)
///
/// # Returns
/// * `Ok(M)` populated distance map if shortest paths computed successfully
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
pub fn dijkstra<G, NI, V, VIS, M>(
    graph: &G,
    source: NI,
    mut visited: VIS,
    mut distance_map: M,
) -> Result<M, AlgorithmError<NI>>
where
    G: GraphValWithEdgeValues<NI, V>,
    NI: NodeIndexTrait + Copy,
    VIS: MapTrait<NI, bool>,
    M: MapTrait<NI, Option<V>>,
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize distances: source is 0, others are None (infinite/unreachable)
    distance_map.insert(source, Some(V::default()));

    // Initialize all other nodes as unreachable
    for node in graph.iter_nodes()? {
        if node != source {
            distance_map.insert(node, None);
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
            if let (Some(is_visited), Some(dist_opt)) =
                (visited.get(&node), distance_map.get(&node))
            {
                if !*is_visited {
                    if let Some(dist) = dist_opt {
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
                    if let (Some(u_dist_opt), Some(dst_visited)) =
                        (distance_map.get(&u), visited.get(&dst))
                    {
                        if !*dst_visited {
                            if let Some(u_dist) = u_dist_opt {
                                let new_distance = *u_dist + *weight;

                                if let Some(dst_dist_opt) = distance_map.get(&dst) {
                                    if dst_dist_opt.is_none()
                                        || new_distance < dst_dist_opt.unwrap()
                                    {
                                        distance_map.insert(dst, Some(new_distance));
                                    }
                                }
                            }
                        }
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

        let distance_map = Dictionary::<char, Option<i32>, 16>::new();
        let visited = Dictionary::<char, bool, 16>::new();

        let result = dijkstra(&graph, 'A', visited, distance_map).unwrap();

        // Check the expected distances
        assert_eq!(result.get(&'A'), Some(&Some(0)));
        assert_eq!(result.get(&'B'), Some(&Some(1)));
        assert_eq!(result.get(&'C'), Some(&Some(3))); // 1 (A->B) + 2 (B->C)
        assert_eq!(result.get(&'D'), Some(&Some(4))); // 3 (A->B->C) + 1 (C->D)
    }

    #[test]
    fn test_dijkstra_disconnected() {
        // Create disconnected graph: 0 -> 1 (weight 2), 2 isolated
        let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let distance_map = Dictionary::<usize, Option<i32>, 16>::new();
        let visited = Dictionary::<usize, bool, 16>::new();

        let result = dijkstra(&graph, 0, visited, distance_map).unwrap();

        // Check distances - node 1 should be reachable
        assert_eq!(result.get(&0), Some(&Some(0)));
        assert_eq!(result.get(&1), Some(&Some(2)));
    }
}
