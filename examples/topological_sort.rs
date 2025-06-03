// SPDX-License-Identifier: Apache-2.0

//! Example demonstrating topological sort on a directed acyclic graph (DAG)

use heapless_graphs::{
    algorithms::topological_sort::topological_sort_dfs,
    containers::queues::{CircularQueue, Deque},
    edgelist::edge_list::EdgeList,
    visited::NodeState,
};

fn main() {
    // Create a DAG representing a simple build dependency graph:
    // compile_lib -> link_lib -> run_tests
    // compile_main -> link_main -> run_tests
    let graph = EdgeList::<8, _, _>::new([
        (0_usize, 1), // compile_lib -> link_lib
        (1, 3),       // link_lib -> run_tests
        (2, 4),       // compile_main -> link_main
        (4, 3),       // link_main -> run_tests
    ]);

    // Set up tracking structures
    let mut visited = [NodeState::Unvisited; 8];
    let mut result = CircularQueue::<usize, 8>::new();

    // All nodes to consider for sorting
    let nodes = [0, 1, 2, 3, 4];

    // Perform topological sort
    match topological_sort_dfs(
        &graph,
        nodes.iter().copied(),
        visited.as_mut_slice(),
        &mut result,
    ) {
        Ok(()) => {
            println!("Topological sort successful!");
            print!("Build order: ");

            let mut sorted = [0usize; 8];
            let mut len = 0;
            while let Some(node) = result.pop_front() {
                sorted[len] = node;
                len += 1;
            }

            let tasks = [
                "compile_lib",
                "link_lib",
                "compile_main",
                "run_tests",
                "link_main",
            ];
            for (i, &node) in sorted[..len].iter().enumerate() {
                if i > 0 {
                    print!(" -> ");
                }
                print!("{}", tasks[node]);
            }
            println!();
        }
        Err(e) => {
            println!("Topological sort failed: {:?}", e);
        }
    }
}
