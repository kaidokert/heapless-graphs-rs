// SPDX-License-Identifier: Apache-2.0

//! Greedy graph coloring algorithm

use super::AlgorithmError;
use crate::containers::{maps::MapTrait, sets::SetTrait};
use crate::graph::{Graph, NodeIndex};

/// Greedy graph coloring algorithm
///
/// This algorithm assigns colors to vertices of a graph such that no two adjacent
/// vertices share the same color. It uses a greedy approach that processes nodes
/// in order and assigns the smallest available color to each node.
///
/// For simplicity, this version does not support pre-colored nodes from the graph.
/// All nodes start uncolored and are colored by the algorithm.
///
/// # Arguments
/// * `graph` - Graph implementing Graph
/// * `color_assignment` - Map to store node-to-color assignments (None = uncolored)
/// * `neighbor_colors` - Set for tracking neighbor colors during execution
/// * `default` - Starting color value (typically 1)
/// * `increment` - Increment value for generating next color (typically 1)
///
/// # Returns
/// * `Ok(M)` populated color assignment map if successful
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if containers are too small
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
///
/// # Time Complexity
/// O(V × D) where V is the number of vertices and D is the maximum degree
pub fn greedy_color<NI, G, V, M, S>(
    graph: &G,
    mut color_assignment: M,
    mut neighbor_colors: S,
    default: V,
    increment: V,
) -> Result<M, AlgorithmError<NI>>
where
    NI: NodeIndex,
    G: Graph<NI>,
    M: MapTrait<NI, Option<V>>,
    S: SetTrait<Option<V>>,
    V: Copy + Ord + core::ops::Add<Output = V>,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize all nodes as uncolored
    for node in graph.iter_nodes()? {
        color_assignment.insert(node, None);
    }

    // Color each node
    for node in graph.iter_nodes()? {
        // Collect colors of all colored neighbors
        neighbor_colors.clear();

        // For undirected graphs represented as directed edges, we need to check
        // both outgoing and incoming edges to find all neighbors
        for neighbor in graph.outgoing_edges(node)? {
            if let Some(neighbor_color) = color_assignment.get(&neighbor) {
                neighbor_colors.insert(*neighbor_color);
            }
        }
        for neighbor in graph.incoming_edges(node)? {
            // Skip if we've already processed this neighbor's color
            if let Some(neighbor_color) = color_assignment.get(&neighbor) {
                if !neighbor_colors.contains(neighbor_color) {
                    neighbor_colors.insert(*neighbor_color);
                }
            }
        }

        // Find the smallest available color
        let mut candidate_color = default;
        while neighbor_colors.contains(&Some(candidate_color)) {
            candidate_color = candidate_color + increment;
        }

        // Assign the color to this node
        color_assignment.insert(node, Some(candidate_color));
    }

    Ok(color_assignment)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::{
        maps::{staticdict::Dictionary, MapTrait},
        sets::{staticset::Set, SetTrait},
    };
    use crate::edgelist::edge_list::EdgeList;

    #[test]
    fn test_greedy_coloring_simple() {
        // Create a simple triangle graph: 0-1, 1-2, 2-0
        // This requires 3 colors (chromatic number = 3)
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (1, 2), (2, 0)]);

        let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
        let neighbor_colors = Set::<Option<i32>, 16>::new();

        let result = greedy_color(&graph, color_assignment, neighbor_colors, 1i32, 1i32).unwrap();

        // Check that all nodes are colored
        assert_eq!(result.get(&0), Some(&Some(1))); // First node gets color 1
        assert!(result.get(&1).unwrap().is_some()); // Second node gets some color
        assert!(result.get(&2).unwrap().is_some()); // Third node gets some color

        // Check that no adjacent nodes have the same color
        let color_0 = result.get(&0).unwrap().unwrap();
        let color_1 = result.get(&1).unwrap().unwrap();
        let color_2 = result.get(&2).unwrap().unwrap();

        assert_ne!(color_0, color_1); // 0-1 are adjacent
        assert_ne!(color_1, color_2); // 1-2 are adjacent
        assert_ne!(color_2, color_0); // 2-0 are adjacent

        // For a triangle, we should use exactly 3 colors
        let mut colors = [color_0, color_1, color_2];
        colors.sort();
        assert_eq!(colors, [1, 2, 3]); // Should be colors 1, 2, 3
    }

    #[test]
    fn test_greedy_coloring_bipartite() {
        // Create a bipartite graph K_2,2: 0-2, 0-3, 1-2, 1-3
        // This should require only 2 colors
        let graph = EdgeList::<8, _, _>::new([(0usize, 2usize), (0, 3), (1, 2), (1, 3)]);

        let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
        let neighbor_colors = Set::<Option<i32>, 16>::new();

        let result = greedy_color(&graph, color_assignment, neighbor_colors, 0i32, 1i32).unwrap();

        // Extract colors
        let color_0 = result.get(&0).unwrap().unwrap();
        let color_1 = result.get(&1).unwrap().unwrap();
        let color_2 = result.get(&2).unwrap().unwrap();
        let color_3 = result.get(&3).unwrap().unwrap();

        // Check proper coloring (no adjacent nodes have same color)
        assert_ne!(color_0, color_2); // 0-2 adjacent
        assert_ne!(color_0, color_3); // 0-3 adjacent
        assert_ne!(color_1, color_2); // 1-2 adjacent
        assert_ne!(color_1, color_3); // 1-3 adjacent

        // In a bipartite graph, greedy should use exactly 2 colors
        // Nodes 0,1 should have one color, nodes 2,3 should have another
        assert_eq!(color_0, color_1); // Same partition
        assert_eq!(color_2, color_3); // Same partition
        assert_ne!(color_0, color_2); // Different partitions
    }

    #[test]
    fn test_greedy_coloring_disconnected() {
        // Test with disconnected components: 0-1 and 2-3
        let graph = EdgeList::<8, _, _>::new([(0usize, 1usize), (2, 3)]);

        let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
        let neighbor_colors = Set::<Option<i32>, 16>::new();

        let result = greedy_color(&graph, color_assignment, neighbor_colors, 10i32, 5i32).unwrap();

        // Extract colors
        let color_0 = result.get(&0).unwrap().unwrap();
        let color_1 = result.get(&1).unwrap().unwrap();
        let color_2 = result.get(&2).unwrap().unwrap();
        let color_3 = result.get(&3).unwrap().unwrap();

        // Check proper coloring within components
        assert_ne!(color_0, color_1); // 0-1 adjacent
        assert_ne!(color_2, color_3); // 2-3 adjacent

        // First nodes of each component should get the default color
        assert_eq!(color_0, 10); // First node gets default
        assert_eq!(color_2, 10); // First node of second component also gets default
    }

    #[test]
    fn test_greedy_coloring_isolated_nodes() {
        // Test with isolated nodes using self-loops that we'll ignore
        // Each node connects to itself, creating isolated components
        let graph = EdgeList::<8, _, _>::new([
            (10usize, 10usize), // Self-loop (will be ignored by many algorithms)
            (20, 20),           // Another self-loop
        ]);

        let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
        let neighbor_colors = Set::<Option<i32>, 16>::new();

        let result = greedy_color(&graph, color_assignment, neighbor_colors, 42i32, 1i32).unwrap();

        // Both nodes should be colored
        // Since they don't connect to each other, they can have the same color
        assert_eq!(result.get(&10), Some(&Some(42))); // Gets default color
        assert_eq!(result.get(&20), Some(&Some(42))); // Gets default color too
        assert_eq!(result.len(), 2); // Should have exactly 2 nodes
    }

    #[test]
    fn test_greedy_coloring_single_edge() {
        // Test with just a single edge
        let graph = EdgeList::<8, _, _>::new([(5usize, 7usize)]);

        let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
        let neighbor_colors = Set::<Option<i32>, 16>::new();

        let result =
            greedy_color(&graph, color_assignment, neighbor_colors, 100i32, 10i32).unwrap();

        // Should have exactly 2 nodes with different colors
        let color_5 = result.get(&5).unwrap().unwrap();
        let color_7 = result.get(&7).unwrap().unwrap();

        assert_ne!(color_5, color_7); // Adjacent nodes must have different colors
        assert_eq!(result.len(), 2); // Should have exactly 2 nodes
    }
}
