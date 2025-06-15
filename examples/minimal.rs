// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{algorithms::dfs_recursive, edgelist::edge_node_list::EdgeNodeList};

fn main() {
    // Make a graph from edges and nodes
    let graph = EdgeNodeList::new([(1_usize, 5), (5, 3), (7, 7)], [7, 4, 3, 1, 5]).unwrap();
    // Visited array tracker
    let mut visited = [false; 10];
    // Do a depth-first traversal, starting from node 5
    dfs_recursive(&graph, 5, visited.as_mut_slice(), &mut |x| {
        println!("node: {}", x)
    })
    .unwrap();
}
