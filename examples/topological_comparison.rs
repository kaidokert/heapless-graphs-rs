// SPDX-License-Identifier: Apache-2.0

//! Example comparing DFS-based and Kahn's topological sort algorithms

use heapless_graphs::{
    algorithms::{kahns::kahns, topological_sort::topological_sort_dfs},
    containers::{
        maps::{staticdict::Dictionary, MapTrait},
        queues::CircularQueue,
    },
    edgelist::edge_list::EdgeList,
    visited::NodeState,
};

fn main() {
    // Create a more complex DAG representing task dependencies:
    // 0: "setup" -> 1: "compile", 2: "test_setup"
    // 1: "compile" -> 3: "link"
    // 2: "test_setup" -> 4: "run_tests"
    // 3: "link" -> 4: "run_tests"
    // 4: "run_tests" -> 5: "deploy"
    let graph = EdgeList::<16, _, _>::new([
        (0_usize, 1), // setup -> compile
        (0, 2),       // setup -> test_setup
        (1, 3),       // compile -> link
        (2, 4),       // test_setup -> run_tests
        (3, 4),       // link -> run_tests
        (4, 5),       // run_tests -> deploy
    ]);

    let tasks = [
        "setup",
        "compile",
        "test_setup",
        "link",
        "run_tests",
        "deploy",
    ];

    println!("Graph edges:");
    for (src, dst) in [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4), (4, 5)] {
        println!("  {} -> {}", tasks[src], tasks[dst]);
    }
    println!();

    // Test DFS-based topological sort
    println!("=== DFS-based Topological Sort ===");
    let mut visited = [NodeState::Unvisited; 8];
    let mut sorted_nodes = [0usize; 8];

    match topological_sort_dfs(
        &graph,
        visited.as_mut_slice(),
        &mut sorted_nodes,
    ) {
        Ok(result) => {
            print!("DFS order: ");
            for (i, &node) in result.iter().enumerate() {
                if i > 0 {
                    print!(" -> ");
                }
                print!("{}", tasks[node]);
            }
            println!();
        }
        Err(e) => {
            println!("DFS failed: {:?}", e);
        }
    }

    // Test Kahn's algorithm
    println!("\n=== Kahn's Algorithm (BFS-based) ===");
    let queue = CircularQueue::<usize, 8>::new();
    let in_degree_map = Dictionary::<usize, isize, 8>::new();
    let mut sorted_nodes = [0usize; 8];

    match kahns(
        &graph,
        queue,
        in_degree_map,
        &mut sorted_nodes,
    ) {
        Ok(result) => {
            print!("Kahn order: ");
            for (i, &node) in result.iter().enumerate() {
                if i > 0 {
                    print!(" -> ");
                }
                print!("{}", tasks[node]);
            }
            println!();
        }
        Err(e) => {
            println!("Kahn's failed: {:?}", e);
        }
    }

    println!("\nBoth algorithms should produce valid topological orderings!");
    println!("Note: The exact order may differ between algorithms but both are correct.");
}
