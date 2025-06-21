// SPDX-License-Identifier: Apache-2.0
//! A* pathfinding algorithm
//!
//! A* is an extension of Dijkstra's algorithm that uses a heuristic function
//! to guide the search toward the goal node, making it more efficient for
//! single-target pathfinding problems.

use super::ContainerResultExt;

use crate::containers::maps::MapTrait;
use crate::graph::{GraphWithEdgeValues, NodeIndex};

use super::AlgorithmError;

/// Configuration structure for A* algorithm to avoid too many function parameters
pub struct AStarConfig<OS, CF, GS> {
    /// Map to track nodes in the open set with their f-scores
    pub open_set: OS,
    /// Map to track the path (parent of each node)
    pub came_from: CF,
    /// Map to store actual cost from start to each node
    pub g_score: GS,
}

/// A* pathfinding algorithm to find shortest path between two specific nodes
///
/// Finds the shortest path from a start node to a goal node using a heuristic
/// function to guide the search. The heuristic must be admissible (never overestimate
/// the actual cost) for A* to guarantee optimal results.
///
/// # Arguments
/// * `graph` - Graph implementing GraphWithEdgeValues
/// * `start` - Starting node
/// * `goal` - Goal node to find path to
/// * `heuristic` - Heuristic function estimating cost from any node to goal
/// * `open_set` - Map to track nodes in the open set with their f-scores
/// * `came_from` - Map to track the path (parent of each node)
/// * `g_score` - Map to store actual cost from start to each node
/// * `path_buffer` - Buffer to store the reconstructed path
///
/// # Returns
/// * `Ok(Some(path_slice))` if path found, containing the path from start to goal
/// * `Ok(None)` if no path exists
/// * `Err(AlgorithmError)` if the operation fails
///
/// # Heuristic Function
/// The heuristic function should estimate the cost from a node to the goal.
/// For optimal results, it must be admissible (never overestimate) and
/// consistent (satisfy triangle inequality).
///
/// # Example
/// ```
/// use heapless_graphs::algorithms::astar;
/// use heapless_graphs::containers::maps::{staticdict::Dictionary, MapTrait};
/// use heapless_graphs::edgelist::edge_list::EdgeList;
/// use heapless_graphs::edges::EdgeValueStruct;
///
/// // Create a simple graph: 0 --(2)--> 1 --(3)--> 2
/// let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32), (1, 2, 3)]);
/// let graph = EdgeList::<8, _, _>::new(edge_data);
///
/// // Simple heuristic that returns 0 (converts A* to Dijkstra)
/// let heuristic = |_node: usize, _goal: usize| 0i32;
///
/// let open_set = Dictionary::<usize, i32, 16>::new();
/// let came_from = Dictionary::<usize, usize, 16>::new();
/// let g_score = Dictionary::<usize, Option<i32>, 16>::new();
/// let mut path_buffer = [0usize; 16];
///
/// let result = astar(&graph, 0, 2, heuristic, open_set, came_from, g_score, &mut path_buffer).unwrap();
///
/// assert!(result.is_some());
/// let path = result.unwrap();
/// assert_eq!(path, &[0, 1, 2]);
/// ```
#[allow(clippy::too_many_arguments)]
pub fn astar<'a, G, NI, V, OS, CF, GS, H>(
    graph: &G,
    start: NI,
    goal: NI,
    heuristic: H,
    mut open_set: OS,
    mut came_from: CF,
    mut g_score: GS,
    path_buffer: &'a mut [NI],
) -> Result<Option<&'a [NI]>, AlgorithmError<NI>>
where
    G: GraphWithEdgeValues<NI, V>,
    NI: NodeIndex,
    OS: MapTrait<NI, V>,         // Maps node to f-score (g + h)
    CF: MapTrait<NI, NI>,        // Maps node to its parent in the path
    GS: MapTrait<NI, Option<V>>, // Maps node to g-score (actual cost from start)
    H: Fn(NI, NI) -> V,          // Heuristic function (node, goal) -> estimated cost
    V: PartialOrd + Copy + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize g-score for all nodes (None means infinite)
    for node in graph.iter_nodes()? {
        g_score.insert(node, None).capacity_error()?;
    }

    // Initialize start node
    let start_g_score = V::default(); // 0
    let start_f_score = start_g_score + heuristic(start, goal);

    g_score
        .insert(start, Some(start_g_score))
        .capacity_error()?;
    open_set.insert(start, start_f_score).capacity_error()?;

    while !open_set.is_empty() {
        // Find node in open_set with lowest f-score
        let mut current = None;
        let mut lowest_f_score = None;

        for (&node, &f_score) in open_set.iter() {
            if let Some(current_lowest) = lowest_f_score {
                if f_score < current_lowest {
                    lowest_f_score = Some(f_score);
                    current = Some(node);
                }
            } else {
                lowest_f_score = Some(f_score);
                current = Some(node);
            }
        }

        // If no current node found, something is wrong with the open_set state
        let current = match current {
            Some(node) => node,
            None => return Err(AlgorithmError::InvalidState),
        };

        // If we reached the goal, reconstruct path
        if current == goal {
            return Ok(Some(reconstruct_path(&came_from, current, path_buffer)?));
        }

        // Remove current from open set
        open_set.remove(&current);

        // Check all neighbors
        for (neighbor, edge_weight_opt) in graph.outgoing_edge_values(current)? {
            if let Some(edge_weight) = edge_weight_opt {
                // Calculate tentative g-score
                let current_g_score = match g_score.get(&current).and_then(|opt| *opt) {
                    Some(score) => score,
                    None => return Err(AlgorithmError::InvalidState), // current should have g_score
                };

                let tentative_g_score = current_g_score + *edge_weight;

                // Check if this path to neighbor is better
                let neighbor_g_score = g_score.get(&neighbor).and_then(|opt| *opt);

                if neighbor_g_score.is_none_or(|existing| tentative_g_score < existing) {
                    // This path is better, record it
                    came_from.insert(neighbor, current).capacity_error()?;
                    g_score
                        .insert(neighbor, Some(tentative_g_score))
                        .capacity_error()?;

                    let f_score = tentative_g_score + heuristic(neighbor, goal);

                    // Add neighbor to open set if not already there with better score
                    if let Some(&existing_f) = open_set.get(&neighbor) {
                        if f_score < existing_f {
                            open_set.insert(neighbor, f_score).capacity_error()?;
                        }
                    } else {
                        open_set.insert(neighbor, f_score).capacity_error()?;
                    }
                }
            }
        }
    }

    // No path found
    Ok(None)
}

/// Reconstructs the path from start to goal using the came_from map
fn reconstruct_path<'a, NI, CF>(
    came_from: &CF,
    mut current: NI,
    path_buffer: &'a mut [NI],
) -> Result<&'a [NI], AlgorithmError<NI>>
where
    NI: NodeIndex,
    CF: MapTrait<NI, NI>,
{
    let mut path_len = 0;

    // Build path backwards
    let mut temp_path = [current; 32]; // Temporary fixed-size buffer for reversal
    let mut temp_len = 0;

    temp_path[temp_len] = current;
    temp_len += 1;

    while let Some(&parent) = came_from.get(&current) {
        if temp_len >= temp_path.len() {
            return Err(AlgorithmError::ResultCapacityExceeded);
        }
        temp_path[temp_len] = parent;
        temp_len += 1;
        current = parent;
    }

    // Reverse the path into the output buffer
    if temp_len > path_buffer.len() {
        return Err(AlgorithmError::ResultCapacityExceeded);
    }

    for i in 0..temp_len {
        path_buffer[i] = temp_path[temp_len - 1 - i];
        path_len += 1;
    }

    Ok(&path_buffer[..path_len])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::edges::EdgeValueStruct;

    #[test]
    fn test_astar_simple_path() {
        // Create a linear graph: 0 --(2)--> 1 --(3)--> 2
        let edge_data = EdgeValueStruct([(0usize, 1usize, 2i32), (1, 2, 3)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        // Zero heuristic (makes A* behave like Dijkstra)
        let heuristic = |_node: usize, _goal: usize| 0i32;

        let open_set = Dictionary::<usize, i32, 16>::new();
        let came_from = Dictionary::<usize, usize, 16>::new();
        let g_score = Dictionary::<usize, Option<i32>, 16>::new();
        let mut path_buffer = [0usize; 16];

        let result = astar(
            &graph,
            0,
            2,
            heuristic,
            open_set,
            came_from,
            g_score,
            &mut path_buffer,
        )
        .unwrap();

        assert!(result.is_some());
        let path = result.unwrap();
        assert_eq!(path, &[0, 1, 2]);
    }

    #[test]
    fn test_astar_with_heuristic() {
        // Create a diamond graph:
        //     1
        //   /   \
        //  0     3
        //   \   /
        //     2
        let edge_data = EdgeValueStruct([
            (0usize, 1usize, 1i32), // 0 -> 1 (cost 1)
            (0, 2, 4),              // 0 -> 2 (cost 4) - longer path
            (1, 3, 1),              // 1 -> 3 (cost 1)
            (2, 3, 1),              // 2 -> 3 (cost 1)
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        // Heuristic that guides toward node 3 (goal)
        let heuristic = |node: usize, goal: usize| {
            if node == goal {
                0
            } else {
                1
            }
        };

        let open_set = Dictionary::<usize, i32, 16>::new();
        let came_from = Dictionary::<usize, usize, 16>::new();
        let g_score = Dictionary::<usize, Option<i32>, 16>::new();
        let mut path_buffer = [0usize; 16];

        let result = astar(
            &graph,
            0,
            3,
            heuristic,
            open_set,
            came_from,
            g_score,
            &mut path_buffer,
        )
        .unwrap();

        assert!(result.is_some());
        let path = result.unwrap();
        // Should take the shorter path: 0 -> 1 -> 3 (cost 2) instead of 0 -> 2 -> 3 (cost 5)
        assert_eq!(path, &[0, 1, 3]);
    }

    #[test]
    fn test_astar_no_path() {
        // Create disconnected graph: 0 -> 1, 2 isolated
        let edge_data = EdgeValueStruct([(0usize, 1usize, 1i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let heuristic = |_node: usize, _goal: usize| 0i32;

        let open_set = Dictionary::<usize, i32, 16>::new();
        let came_from = Dictionary::<usize, usize, 16>::new();
        let g_score = Dictionary::<usize, Option<i32>, 16>::new();
        let mut path_buffer = [0usize; 16];

        let result = astar(
            &graph,
            0,
            2,
            heuristic,
            open_set,
            came_from,
            g_score,
            &mut path_buffer,
        )
        .unwrap();

        assert!(result.is_none()); // No path from 0 to 2
    }

    #[test]
    fn test_astar_same_start_goal() {
        // Test when start == goal
        let edge_data = EdgeValueStruct([(0usize, 1usize, 1i32)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let heuristic = |_node: usize, _goal: usize| 0i32;

        let open_set = Dictionary::<usize, i32, 16>::new();
        let came_from = Dictionary::<usize, usize, 16>::new();
        let g_score = Dictionary::<usize, Option<i32>, 16>::new();
        let mut path_buffer = [0usize; 16];

        let result = astar(
            &graph,
            0,
            0,
            heuristic,
            open_set,
            came_from,
            g_score,
            &mut path_buffer,
        )
        .unwrap();

        assert!(result.is_some());
        let path = result.unwrap();
        assert_eq!(path, &[0]); // Path should just be the start node
    }

    #[test]
    fn test_astar_complex_graph() {
        // Create a more complex graph to test A* optimization
        //   1 --3-- 4
        //  /|      /|
        // 0 |     / |
        //  \|    /  |
        //   2 --5-- 3 --1-- 6
        let edge_data = EdgeValueStruct([
            (0usize, 1usize, 1i32),
            (0, 2, 1),
            (1, 2, 1),
            (1, 4, 3),
            (2, 3, 5),
            (4, 3, 1),
            (4, 6, 1),
            (3, 6, 1),
        ]);
        let graph = EdgeList::<16, _, _>::new(edge_data);

        // Heuristic based on "distance" to goal (node 6)
        let heuristic = |node: usize, goal: usize| {
            match (node, goal) {
                (6, 6) => 0,
                (3, 6) | (4, 6) => 1,
                (1, 6) | (2, 6) => 2,
                (0, 6) => 3,
                _ => 10, // Unknown nodes get high cost
            }
        };

        let open_set = Dictionary::<usize, i32, 32>::new();
        let came_from = Dictionary::<usize, usize, 32>::new();
        let g_score = Dictionary::<usize, Option<i32>, 32>::new();
        let mut path_buffer = [0usize; 16];

        let result = astar(
            &graph,
            0,
            6,
            heuristic,
            open_set,
            came_from,
            g_score,
            &mut path_buffer,
        )
        .unwrap();

        assert!(result.is_some());
        let path = result.unwrap();

        // Verify we got a valid path from 0 to 6
        assert_eq!(path[0], 0);
        assert_eq!(path[path.len() - 1], 6);

        // The optimal path should be 0 -> 1 -> 4 -> 6 (cost: 1 + 3 + 1 = 5)
        // or 0 -> 1 -> 4 -> 3 -> 6 (cost: 1 + 3 + 1 + 1 = 6)
        assert!(path.len() >= 3 && path.len() <= 5);
    }
}
