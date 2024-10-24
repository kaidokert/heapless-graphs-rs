// SPDX-License-Identifier: Apache-2.0

use crate::{containers::maps::MapTrait, graph::GraphWithEdgeValues, VisitedTracker};

use super::{AlgorithmError, OptionResultExt};

/// Dijkstra algorithm to find shortest path between nodes
///
/// Calculates the shortest path from a start node to all other nodes in the graph,
/// does not handle negative edge weights.
#[cfg(feature = "num-traits")]
pub fn dijkstra<NI, V, VT, M, G: GraphWithEdgeValues<NI, V>>(
    graph: &G,
    source: NI,
    visited: &mut VT,
) -> Result<M, AlgorithmError<NI>>
where
    NI: PartialEq + Copy,
    VT: VisitedTracker<NI>,
    M: MapTrait<NI, V>,
    V: num_traits::Bounded + num_traits::Zero + PartialOrd + Copy,
{
    let mut distance = M::new();
    distance.clear();
    for &node in graph.get_nodes()? {
        if node == source {
            distance.insert(node, V::zero());
        } else {
            distance.insert(node, V::max_value());
        }
    }
    for _ in graph.get_nodes()? {
        let mut min_distance = V::max_value();
        let mut min_node = None;
        for v in graph.get_nodes()? {
            let dist = distance.get(v).dict_error()?;
            if !visited.is_visited(v) && dist < &min_distance {
                min_distance = *dist;
                min_node = Some(v);
            }
        }
        if min_node.is_none() {
            break;
        }
        let u = min_node.unwrap();
        visited.mark_visited(u);
        for (v, value) in graph.neighbors_for_node_with_values(u)? {
            if visited.is_unvisited(v) {
                let u_dist = *distance.get(u).dict_error()?;
                let v_dist = *distance.get(v).dict_error()?;
                if let Some(&weight) = value {
                    let new_distance = u_dist + weight;
                    if new_distance < v_dist {
                        distance.insert(*v, new_distance);
                    }
                } else {
                    return Err(AlgorithmError::MissingEdgeWeight {
                        incoming_edge: *u,
                        outgoing_edge: *v,
                    });
                }
            }
        }
    }
    Ok(distance)
}

#[cfg(test)]
#[cfg(feature = "num-traits")]
mod tests {
    use super::*;
    #[test]
    fn test_djikstra() {
        use crate::containers::maps::{staticdict::Dictionary, MapTrait};
        use crate::{edge_list::EdgeList, edges::EdgeValueStruct};
        use crate::{visited::MapWrapper, NodeState};
        //    (1)        (2)
        //A ------ B -------- C
        // \       |          |
        //  \      |(5)       |(1)
        //   \     |          |
        //    \    D ---------
        //     \              |
        //      \_____________|
        //          (4)

        // Create the graph with positive edge weights
        let graph = EdgeList::<5, _, _>::new(EdgeValueStruct([
            ('A', 'B', 1),
            ('A', 'C', 4),
            ('B', 'C', 2),
            ('B', 'D', 5),
            ('C', 'D', 1),
        ]))
        .unwrap();

        let mut visited = MapWrapper(Dictionary::<char, NodeState, 37>::new());
        let res = dijkstra::<_, _, _, Dictionary<_, _, 16>, _>(&graph, 'A', &mut visited)
            .expect("this worked?");
        // Check the expected distances
        assert_eq!(res.get(&'A'), Some(&0));
        assert_eq!(res.get(&'B'), Some(&1));
        assert_eq!(res.get(&'C'), Some(&3)); // 1 (A->B) + 2 (B->C)
        assert_eq!(res.get(&'D'), Some(&4)); // 3 (A->B->C) + 1 (C->D)
    }
}
