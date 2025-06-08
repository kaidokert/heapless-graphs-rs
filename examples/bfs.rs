// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{
    algorithms::traversal::bfs, containers::queues::CircularQueue, edgelist::edge_list::EdgeList,
};

fn main() {
    // Create a simple graph: 0->1, 0->2, 1->3, 2->3
    let graph = EdgeList::<8, _, _>::new([(0, 1), (0, 2), (1, 3), (2, 3)]);
    let mut visited = [false; 10];
    let queue = CircularQueue::<usize, 16>::new();

    println!("BFS traversal starting from node 0:");
    bfs(&graph, 0, visited.as_mut_slice(), queue, &mut |x| {
        println!("visited: {}", x)
    })
    .unwrap();
}
