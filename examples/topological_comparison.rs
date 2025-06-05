// SPDX-License-Identifier: Apache-2.0

//! Example comparing DFS-based and Kahn's topological sort algorithms

use heapless_graphs::{
    algorithms::{kahns::kahns, topological_sort::topological_sort_dfs},
    containers::{
        maps::{staticdict::Dictionary, MapTrait},
        queues::{CircularQueue, Deque},
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

    let nodes = [0, 1, 2, 3, 4, 5];
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
    let mut dfs_result = CircularQueue::<usize, 8>::new();

    match topological_sort_dfs(
        &graph,
        nodes.iter().copied(),
        visited.as_mut_slice(),
        &mut dfs_result,
    ) {
        Ok(()) => {
            print!("DFS order: ");
            let mut sorted = [0usize; 8];
            let mut len = 0;
            while let Some(node) = dfs_result.pop_front() {
                sorted[len] = node;
                len += 1;
            }

            for (i, &node) in sorted[..len].iter().enumerate() {
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
    let mut kahn_result = CircularQueue::<usize, 8>::new();

    match kahns(
        &graph,
        queue,
        in_degree_map,
        &mut kahn_result,
    ) {
        Ok(()) => {
            print!("Kahn order: ");
            let mut sorted = [0usize; 8];
            let mut len = 0;
            while let Some(node) = kahn_result.pop_front() {
                sorted[len] = node;
                len += 1;
            }

            for (i, &node) in sorted[..len].iter().enumerate() {
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
