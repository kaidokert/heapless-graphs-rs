// SPDX-License-Identifier: Apache-2.0

use heapless_graphs::{algorithms::dfs_recursive, edge_list::EdgeNodeList, nodes::NodeRef};
use hybrid_array::{typenum::U4, Array, ArraySize};

pub struct NodeStructArray<NI, U: ArraySize<NI>>(pub Array<NI, U>);
impl<NI, U: ArraySize<NI>> NodeRef for NodeStructArray<NI, U> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        Some(&self.0[index])
    }
    fn capacity(&self) -> usize {
        U::to_usize()
    }
}

#[test]
fn test_hybrid_array_nodes() {
    let edges = [(1_usize, 2), (3, 4)];
    let nodes = NodeStructArray(Array::<_, U4>([1_usize, 2, 3, 4]));
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    let mut visited = [false; 8];
    dfs_recursive(&graph, 4, visited.as_mut_slice(), &mut |node| {
        println!("Visited node: {}", node);
    })
    .expect("DFS failed");
}
