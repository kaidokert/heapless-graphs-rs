// TODO: Remove this
#![allow(unused)]

use heapless::sorted_linked_list::Node;

use crate::{
    containers::{maps::MapTrait, sets::SetTrait},
    graph::GraphWithNodeValues,
};

use super::{AlgorithmError, OptionResultExt};

pub fn greedy_color<NI, G, V, M, S>(
    graph: &G,
    mut color_assignment: M,
    mut neighbor_colors: S,
    default: V,
    increment: V,
) -> Result<M, AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    G: GraphWithNodeValues<V, NodeIndex = NI>,
    M: MapTrait<NI, Option<V>>,
    S: SetTrait<Option<V>>,
    V: Copy + Ord + core::ops::Add<Output = V> + Default,
    AlgorithmError<NI>: From<G::Error>,
{
    color_assignment.clear();
    for (node, val) in graph.get_node_values()? {
        if let Some(color) = val {
            color_assignment.insert(*node, Some(*color));
        }
    }
    for (node, val) in graph.get_node_values()? {
        neighbor_colors.clear();
        for (index, neighbor) in graph.neighboring_nodes_with_values(node)? {
            if let Some(neighbor_color) = *color_assignment.get(index).dict_error()? {
                neighbor_colors.insert(Some(neighbor_color));
            }
        }
        let mut color = default;
        while neighbor_colors.contains(&Some(color)) {
            color = color + increment;
        }
        color_assignment.insert(*node, Some(color));
    }
    Ok(color_assignment)
}

#[cfg(test)]
mod tests {
    use crate::{
        containers::{maps::staticdict::Dictionary, sets::staticset::Set},
        edge_list::EdgeNodeList,
        nodes::NodeValueStruct,
    };

    use super::*;

    // TODO: WIP
    #[test]
    fn test_greedy_color_basic() {
        let graph = EdgeNodeList::new(
            [(1_usize, 2), (2, 3), (3, 4)],
            NodeValueStruct([(1, 200i32), (2, 201), (3, 203), (4, 204)]),
        )
        .unwrap();
        let color_assignment = Dictionary::<usize, Option<i32>, 37>::new();
        let neighbor_set = Set::<Option<i32>, 37>::new();
        let res = greedy_color(&graph, color_assignment, neighbor_set, 200, 1).unwrap();
        assert_eq!(res.get(&1).unwrap(), &Some(200));
        assert_eq!(res.get(&2).unwrap(), &Some(201));
        assert_eq!(res.get(&3).unwrap(), &Some(200));
    }

    #[test]
    fn test_greedy_color() {
        /*
            (1) A
            /   \
        (2)B -- (3)C
            |      |
            (1)D -- (2)E
            |
            (2)F
         */
        let graph = EdgeNodeList::new(
            [
                ('a', 'b'),
                ('a', 'c'),
                ('b', 'c'),
                ('b', 'd'),
                ('c', 'e'),
                ('d', 'e'),
                ('d', 'f'),
            ],
            NodeValueStruct([('a', 0), ('b', 0), ('c', 0), ('d', 0), ('e', 0), ('f', 0)]),
        )
        .unwrap();
        let color_assignment = Dictionary::<char, Option<i32>, 37>::new();
        let neighbor_color = Set::<Option<i32>, 37>::new();
        let res = greedy_color(&graph, color_assignment, neighbor_color, 1, 1).unwrap();
        assert_eq!(res.get(&'a').unwrap(), &Some(1));
        assert_eq!(res.get(&'b').unwrap(), &Some(2));
        assert_eq!(res.get(&'c').unwrap(), &Some(3));
        assert_eq!(res.get(&'d').unwrap(), &Some(1));
        assert_eq!(res.get(&'e').unwrap(), &Some(2));
        assert_eq!(res.get(&'f').unwrap(), &Some(2));
    }
}
