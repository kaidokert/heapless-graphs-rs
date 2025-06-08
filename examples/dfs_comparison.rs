// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{
    algorithms::traversal::{dfs_iterative, dfs_recursive},
    containers::queues::CircularQueue,
    edgelist::edge_list::EdgeList,
};

fn main() {
    // Create a simple graph: 0->1, 0->2, 1->3, 2->3
    let graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);

    println!("DFS Recursive traversal starting from node 0:");
    let mut visited = [false; 10];
    dfs_recursive(&graph, &0, visited.as_mut_slice(), &mut |x| {
        println!("visited: {}", x)
    })
    .unwrap();

    println!("\nDFS Iterative traversal starting from node 0:");
    let mut visited = [false; 10];
    let stack = CircularQueue::<usize, 16>::new();
    dfs_iterative(&graph, 0, visited.as_mut_slice(), stack, &mut |x| {
        println!("visited: {}", x)
    })
    .unwrap();
}
