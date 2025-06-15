// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::containers::sets::staticset::Set;
use heapless_graphs::containers::sets::SetTrait;
use heapless_graphs::{
    algorithms::dfs_recursive, edgelist::edge_list::EdgeList, visited::SetWrapper,
};

fn main() {
    // Do DFS traversal, starting from node "five"
    let mut visited = SetWrapper(Set::<_, 13>::new());
    dfs_recursive(
        &EdgeList::<8, _, _>::new([
            ("one", "five"),
            ("five", "three"),
            ("seven", "seven"),
            ("three", "five"),
        ]),
        "five",
        &mut visited,
        &mut |x| println!("node: {}", x),
    )
    .unwrap();
}
