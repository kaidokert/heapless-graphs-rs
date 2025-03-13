// SPDX-License-Identifier: Apache-2.0

use crate::containers::maps::MapTrait;

use crate::graph::GraphWithEdgeValues;

use super::{AlgorithmError, OptionResultExt};

/// Bellman-Ford algorithm for shortest path between nodes
///
/// Calculates the shortest path from a start node to all other nodes in the graph,
/// able to handle negative edge weights.
#[cfg(feature = "num-traits")]
pub fn bellman_ford<NI, G, V, M>(
    graph: &G,
    start: NI,
    mut distance: M,
) -> Result<M, AlgorithmError<NI>>
where
    G: GraphWithEdgeValues<NI, V>,
    NI: PartialEq + Copy + core::fmt::Debug,
    M: MapTrait<NI, V>,
    V: num_traits::Bounded + num_traits::Zero + PartialOrd + Copy + core::fmt::Debug,
    AlgorithmError<NI>: From<G::Error>,
{
    distance.clear();
    for &node in graph.get_nodes()? {
        if node == start {
            distance.insert(node, V::zero());
        } else {
            distance.insert(node, V::max_value());
        }
    }
    let mut node_peek = graph.get_nodes()?.peekable();
    while let Some(_) = node_peek.next() {
        if node_peek.peek().is_none() {
            break;
        }
        for (src, dst, weight) in graph.get_edge_values()? {
            let old_distance = *distance.get(src).dict_error()?;
            let real_weight = *weight.dict_error()?;
            let new_distance = old_distance + real_weight;
            if new_distance < *distance.get(dst).dict_error()? {
                let mut_ref = distance.get_mut(dst).unwrap();
                *mut_ref = new_distance;
            }
        }
    }

    for (src, dst, weight) in graph.get_edge_values()? {
        let old_distance = *distance.get(src).dict_error()?;
        let real_weight = *weight.dict_error()?;
        let new_distance = old_distance + real_weight;
        if new_distance < *distance.get(dst).dict_error()? {
            return Err(AlgorithmError::NegativeCycle {
                incoming_edge: *src,
                outgoing_edge: *dst,
            });
        }
    }
    Ok(distance)
}

#[cfg(test)]
#[cfg(feature = "num-traits")]
mod tests {
    use super::*;
    #[cfg(feature = "heapless")]
    use crate::adjacency_list::MapAdjacencyList;
    use crate::adjacency_list::{EdgesOnly, SliceAdjacencyList};
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edge_list::EdgeList;
    use crate::edges::EdgeValueStruct;
    use crate::edges::EdgeValueStructOption;
    use crate::nodes::NodeValueStructOption;

    #[test]
    fn test_bellman_ford_edge_list() {
        let graph = EdgeList::<3, _, _>::new(EdgeValueStruct([
            ('a', 'b', 1),
            ('b', 'c', -3),
            ('c', 'a', 1),
        ]))
        .unwrap();
        let dict = Dictionary::<_, _, 16>::new();
        let result = bellman_ford(&graph, 'a', dict);
        assert_eq!(
            result.err(),
            Some(AlgorithmError::NegativeCycle {
                incoming_edge: 'a',
                outgoing_edge: 'b'
            })
        );

        let graph = EdgeList::<3, _, _>::new(EdgeValueStruct([
            ('a', 'b', 1),
            ('a', 'c', 4),
            ('b', 'c', 2),
        ]))
        .unwrap();
        let dict = Dictionary::<_, _, 16>::new();
        let result = bellman_ford(&graph, 'a', dict).unwrap();
        assert_eq!(result.get(&'a'), Some(&0));
        assert_eq!(result.get(&'b'), Some(&1));
        assert_eq!(result.get(&'c'), Some(&3));

        let graph = EdgeList::<10, _, _>::new(EdgeValueStructOption([
            Some(('a', 'b', 1)),
            None,
            None,
            Some(('a', 'c', 4)),
            Some(('b', 'c', 2)),
            None,
            None,
        ]))
        .unwrap();
        let dict = Dictionary::<_, _, 16>::new();
        let result = bellman_ford(&graph, 'a', dict).unwrap();
        assert_eq!(result.get(&'a'), Some(&0));
        assert_eq!(result.get(&'b'), Some(&1));
        assert_eq!(result.get(&'c'), Some(&3));
    }

    #[test]
    fn test_bellman_ford_adj_list() {
        let graph = SliceAdjacencyList::new([
            (
                'a',
                EdgesOnly(NodeValueStructOption([
                    Some(('b', 1)),
                    None,
                    Some(('c', 4)),
                    None,
                ])),
            ),
            (
                'b',
                EdgesOnly(NodeValueStructOption([None, None, Some(('c', 2)), None])),
            ),
            (
                'c',
                EdgesOnly(NodeValueStructOption([None, None, None, None])),
            ),
        ])
        .unwrap();
        let dict = Dictionary::<_, _, 16>::new();
        let result = bellman_ford(&graph, 'a', dict).unwrap();
        assert_eq!(result.get(&'a'), Some(&0));
        assert_eq!(result.get(&'b'), Some(&1));
        assert_eq!(result.get(&'c'), Some(&3));

        #[cfg(feature = "heapless")]
        {
            let graph = MapAdjacencyList::new(heapless::FnvIndexMap::<_, _, 8>::from_iter([
                (
                    'a',
                    EdgesOnly(NodeValueStructOption([
                        Some(('b', 1)),
                        None,
                        Some(('c', 4)),
                        None,
                    ])),
                ),
                (
                    'b',
                    EdgesOnly(NodeValueStructOption([None, None, Some(('c', 2)), None])),
                ),
                (
                    'c',
                    EdgesOnly(NodeValueStructOption([None, None, None, None])),
                ),
            ]))
            .unwrap();
            let dict = Dictionary::<_, _, 16>::new();
            let result = bellman_ford(&graph, 'a', dict).unwrap();
            assert_eq!(result.get(&'a'), Some(&0));
            assert_eq!(result.get(&'b'), Some(&1));
            assert_eq!(result.get(&'c'), Some(&3));
        }
    }
}
