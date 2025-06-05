// SPDX-License-Identifier: Apache-2.0

//! Example demonstrating topological sort on a directed acyclic graph (DAG)

use heapless_graphs::{
    algorithms::topological_sort::topological_sort_dfs,
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
    let mut sorted_nodes = [0usize; 8];

    // Perform topological sort
    match topological_sort_dfs(
        &graph,
        visited.as_mut_slice(),
        &mut sorted_nodes,
    ) {
        Ok(result) => {
            println!("Topological sort successful!");
            print!("Build order: ");

            let tasks = [
                "compile_lib",
                "link_lib",
                "compile_main",
                "run_tests",
                "link_main",
            ];
            for (i, &node) in result.iter().enumerate() {
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
