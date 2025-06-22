// SPDX-License-Identifier: Apache-2.0

//! A* pathfinding demonstration
//!
//! This example demonstrates how to use the A* pathfinding algorithm
//! to find optimal paths in weighted graphs using heuristic functions.

use heapless_graphs::{
    algorithms::astar,
    containers::maps::{staticdict::Dictionary, MapTrait},
    edgelist::edge_list::EdgeList,
    edges::EdgeValueStruct,
};

fn main() {
    println!("A* Pathfinding Demo");
    println!("===================");

    // Example 1: Grid-like pathfinding (game/robotics scenario)
    println!("\n1. Grid-based Pathfinding");
    println!("Grid layout (distances are Manhattan-like):");
    println!("  0 --1-- 1 --1-- 2");
    println!("  |       |       |");
    println!("  2       1       1");
    println!("  |       |       |");
    println!("  3 --1-- 4 --2-- 5");

    // Create graph representing a 2x3 grid with costs
    let grid_edges = EdgeValueStruct([
        (0usize, 1usize, 1i32), // Top row
        (1, 2, 1),
        (0, 3, 2), // Left column
        (1, 4, 1), // Middle column
        (2, 5, 1), // Right column
        (3, 4, 1), // Bottom row
        (4, 5, 2),
    ]);
    let grid_graph = EdgeList::<16, _, _>::new(grid_edges);

    // Manhattan distance heuristic for 2x3 grid
    let grid_heuristic = |node: usize, goal: usize| {
        let coords = |n| (n / 3, n % 3); // Convert node to (row, col)
        let (r1, c1) = coords(node);
        let (r2, c2) = coords(goal);
        ((r2 as i32 - r1 as i32).abs() + (c2 as i32 - c1 as i32).abs()) as i32
    };

    let open_set = Dictionary::<usize, i32, 16>::new();
    let came_from = Dictionary::<usize, usize, 16>::new();
    let g_score = Dictionary::<usize, Option<i32>, 16>::new();
    let mut path_buffer = [0usize; 16];

    match astar(
        &grid_graph,
        0,
        5,
        grid_heuristic,
        open_set,
        came_from,
        g_score,
        &mut path_buffer,
    ) {
        Ok(Some(path)) => {
            println!("Path from top-left (0) to bottom-right (5): {:?}", path);
            let total_cost: i32 = path
                .windows(2)
                .map(|w| {
                    // Calculate cost between consecutive nodes in path
                    match (w[0], w[1]) {
                        (0, 1) | (1, 2) | (3, 4) => 1,
                        (0, 3) | (4, 5) => 2,
                        (1, 4) | (2, 5) => 1,
                        _ => 0,
                    }
                })
                .sum();
            println!("Total path cost: {}", total_cost);
        }
        Ok(None) => println!("No path found"),
        Err(e) => println!("Error: {:?}", e),
    }

    // Example 2: Comparing A* vs Dijkstra-like behavior
    println!("\n2. A* vs Dijkstra-like Comparison");
    println!("Graph with alternative routes:");
    println!("     2");
    println!("  1 --- 3");
    println!(" /|     |\\");
    println!("0 |     | 5");
    println!(" \\|     |/");
    println!("  2 --- 4");
    println!("     3");

    let comparison_edges = EdgeValueStruct([
        (0usize, 1usize, 1i32),
        (0, 2, 1),
        (1, 3, 2),
        (2, 4, 3),
        (3, 5, 1),
        (4, 5, 1),
        (1, 2, 1), // Additional connection
    ]);
    let comparison_graph = EdgeList::<16, _, _>::new(comparison_edges);

    // Test with zero heuristic (Dijkstra-like)
    println!("\nUsing zero heuristic (like Dijkstra):");
    let zero_heuristic = |_node: usize, _goal: usize| 0i32;

    let open_set = Dictionary::<usize, i32, 16>::new();
    let came_from = Dictionary::<usize, usize, 16>::new();
    let g_score = Dictionary::<usize, Option<i32>, 16>::new();
    let mut path_buffer = [0usize; 16];

    match astar(
        &comparison_graph,
        0,
        5,
        zero_heuristic,
        open_set,
        came_from,
        g_score,
        &mut path_buffer,
    ) {
        Ok(Some(path)) => println!("Path: {:?}", path),
        Ok(None) => println!("No path found"),
        Err(e) => println!("Error: {:?}", e),
    }

    // Test with goal-directed heuristic
    println!("\nUsing goal-directed heuristic:");
    let directed_heuristic = |node: usize, goal: usize| {
        if node == goal {
            0
        } else {
            1
        } // Simple distance estimation
    };

    let open_set = Dictionary::<usize, i32, 16>::new();
    let came_from = Dictionary::<usize, usize, 16>::new();
    let g_score = Dictionary::<usize, Option<i32>, 16>::new();
    let mut path_buffer = [0usize; 16];

    match astar(
        &comparison_graph,
        0,
        5,
        directed_heuristic,
        open_set,
        came_from,
        g_score,
        &mut path_buffer,
    ) {
        Ok(Some(path)) => println!("Path: {:?}", path),
        Ok(None) => println!("No path found"),
        Err(e) => println!("Error: {:?}", e),
    }

    // Example 3: Navigation with obstacles
    println!("\n3. Navigation with Obstacles");
    println!("Route planning around expensive areas:");
    println!("S --1-- o --1-- o --1-- G");
    println!("|       |       |       |");
    println!("1      10      10       1");
    println!("|       |       |       |");
    println!("o --1-- X --9-- X --1-- o");
    // S = start, G = goal, X = expensive area, o = normal area

    let navigation_edges = EdgeValueStruct([
        (0usize, 1usize, 1i32), // S -> o
        (1, 2, 1),              // o -> o
        (2, 3, 1),              // o -> G
        (0, 4, 1),              // S down
        (1, 5, 10),             // o down (expensive)
        (2, 6, 10),             // o down (expensive)
        (3, 7, 1),              // G down
        (4, 5, 1),              // Bottom row
        (5, 6, 9),              // Expensive area
        (6, 7, 1),              // Bottom row
    ]);
    let nav_graph = EdgeList::<16, _, _>::new(navigation_edges);

    // Heuristic that estimates distance to goal (node 3)
    let nav_heuristic = |node: usize, goal: usize| {
        if node == goal {
            0
        } else {
            // Simple grid distance estimation
            let goal_pos = (goal / 4, goal % 4);
            let node_pos = (node / 4, node % 4);
            ((goal_pos.0 as i32 - node_pos.0 as i32).abs()
                + (goal_pos.1 as i32 - node_pos.1 as i32).abs()) as i32
        }
    };

    let open_set = Dictionary::<usize, i32, 16>::new();
    let came_from = Dictionary::<usize, usize, 16>::new();
    let g_score = Dictionary::<usize, Option<i32>, 16>::new();
    let mut path_buffer = [0usize; 16];

    match astar(
        &nav_graph,
        0,
        3,
        nav_heuristic,
        open_set,
        came_from,
        g_score,
        &mut path_buffer,
    ) {
        Ok(Some(path)) => {
            println!("Optimal path avoiding expensive areas: {:?}", path);
            println!("This should prefer the top route (0->1->2->3) over expensive bottom areas");
        }
        Ok(None) => println!("No path found"),
        Err(e) => println!("Error: {:?}", e),
    }

    println!("\nA* is particularly useful for:");
    println!("- Game AI pathfinding");
    println!("- Robot navigation");
    println!("- GPS route planning");
    println!("- Puzzle solving");
    println!("- Any scenario where you have a good distance/cost heuristic");
}
