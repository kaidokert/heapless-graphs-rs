// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{
    algorithms::traversal::dfs_iterative, containers::queues::CircularQueue,
    edgelist::edge_list::EdgeList,
};

fn main() {
    // Create a simple graph: 0->1, 0->2, 1->3, 2->3
    let graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);
    let mut visited = [false; 10];
    let stack = CircularQueue::<usize, 16>::new();

    println!("DFS iterative traversal starting from node 0:");
    dfs_iterative(&graph, 0, visited.as_mut_slice(), stack, &mut |x| {
        println!("visited: {}", x)
    })
    .unwrap();
}
