// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{algorithms::dfs_recursive, edgelist::edge_list::EdgeList};

fn main() {
    // Do DFS traversal, starting from node 5
    let graph = EdgeList::<8, _, _>::new([(1, 5), (5, 3), (7, 7)]);
    let mut visited = [false; 10];
    dfs_recursive(&graph, 5, visited.as_mut_slice(), &mut |x| {
        println!("node: {}", x)
    })
    .unwrap();
}
