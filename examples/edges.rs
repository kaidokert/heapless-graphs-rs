// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{algorithms::dfs_recursive_unchecked, edge_list::EdgeList};

fn main() {
    // Do DFS traversal, starting from node 5
    dfs_recursive_unchecked(
        &EdgeList::<3, _, _>::new([(1, 5), (5, 3), (7, 7)]).unwrap(),
        5,
        [false; 10].as_mut_slice(),
        &mut |x| println!("node: {}", x),
    )
    .unwrap();
}
