// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::containers::sets::SetTrait;
use heapless_graphs::{
    algorithms::dfs_recursive_unchecked, containers::sets::staticset::Set, edge_list::EdgeList,
    visited::SetWrapper,
};

fn main() {
    // Do DFS traversal, starting from node 5
    let mut visited = SetWrapper(Set::<_, 13>::new());
    dfs_recursive_unchecked(
        &EdgeList::<3, _, _>::new([
            ("one", "five"),
            ("five", "three"),
            ("seven", "seven"),
            ("three", "five"),
        ])
        .unwrap(),
        "five",
        &mut visited,
        &mut |x| println!("node: {}", x),
    )
    .unwrap();
}
