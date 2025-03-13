// SPDX-License-Identifier: Apache-2.0

use crate::{containers::maps::MapTrait, graph::GraphWithEdgeValues};

use super::{AlgorithmError, OptionResultExt};

/// Kruskal's algorithm for minimum spanning tree
///
/// Finds the minimum spanning tree of a graph
pub fn kruskals<'a, NI, G, V, M>(
    graph: &G,
    edge_storage: &mut [(NI, NI, V)],
    mut parent: M,
    mst: &'a mut [(NI, NI, V)],
) -> Result<&'a [(NI, NI, V)], AlgorithmError<NI>>
where
    G: GraphWithEdgeValues<NI, V>,
    M: MapTrait<NI, NI>,
    NI: Eq + Copy + Default + Ord + Sized,
    V: Copy + Default + Ord + Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    parent.clear();
    for &node in graph.get_nodes()? {
        parent.insert(node, node);
    }
    fn find<NI, M>(node: NI, parent: &mut M) -> Result<NI, AlgorithmError<NI>>
    where
        NI: PartialEq + Eq + Copy,
        M: MapTrait<NI, NI>,
    {
        let mut cur_node = node;
        loop {
            let parent_node = *parent.get(&cur_node).dict_error()?;
            if parent_node == cur_node {
                break;
            }
            let grandparent = *parent.get(&parent_node).dict_error()?;
            *parent.get_mut(&cur_node).dict_error()? = grandparent;
            cur_node = grandparent;
        }
        Ok(cur_node)
    }
    fn union<NI, M>(u: NI, v: NI, parent: &mut M) -> Result<bool, AlgorithmError<NI>>
    where
        NI: PartialEq + Eq + Copy,
        M: MapTrait<NI, NI>,
    {
        let root_u = find(u, parent)?;
        let root_v = find(v, parent)?;
        if root_u == root_v {
            return Ok(false);
        }
        *parent.get_mut(&root_v).dict_error()? = root_u;
        Ok(true)
    }
    let sorted_edges = edge_storage;
    let mut count = 0;
    for edge in graph.get_edge_values()? {
        if count >= sorted_edges.len() {
            return Err(AlgorithmError::EdgeCapacityExceeded {
                max_edges: sorted_edges.len(),
            });
        }
        if let Some(weight) = edge.2 {
            sorted_edges[count] = (*edge.0, *edge.1, *weight);
            count += 1;
        } else {
            return Err(AlgorithmError::MissingEdgeWeight {
                incoming_edge: *edge.0,
                outgoing_edge: *edge.1,
            });
        }
    }
    let sortable_slice = &mut sorted_edges[..count];
    sortable_slice.sort_unstable_by(|a, b| a.2.cmp(&b.2));
    count = 0;
    for &(u, v, w) in sortable_slice.iter() {
        if u == v {
            continue; // Skip self-loops
        }
        if union(u, v, &mut parent)? {
            if count >= mst.len() {
                return Err(AlgorithmError::OutputCapacityExceeded);
            }
            mst[count] = (u, v, w);
            count += 1;
        }
    }
    let ret_range = &mut mst[..count];
    Ok(ret_range)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "heapless")]
    use crate::adjacency_list::MapAdjacencyList;
    use crate::{
        adjacency_list::{EdgesOnly, SliceAdjacencyList},
        containers::maps::staticdict::Dictionary,
    };

    #[test]
    fn test_kruskals() {
        use crate::nodes::NodeValueStructOption;
        use crate::{edge_list::EdgeList, edges::EdgeValueStruct};

        let graph = EdgeList::<8, _, _>::new(EdgeValueStruct([
            ('a', 'b', 1),
            ('a', 'c', 3),
            ('b', 'c', 2),
            ('b', 'd', 2),
            ('c', 'd', 4),
        ]))
        .unwrap();
        let mut mst = [('0', '0', 0); 3];
        let mut edge_storage = [('0', '0', 0); 5];
        let res = kruskals(
            &graph,
            edge_storage.as_mut_slice(),
            Dictionary::<_, _, 16>::new(),
            &mut mst,
        )
        .unwrap();
        assert_eq!(res, &[('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 2)]);

        let graph = SliceAdjacencyList::new([
            (
                'a',
                EdgesOnly(NodeValueStructOption([Some(('b', 1)), Some(('c', 3))])),
            ),
            (
                'b',
                EdgesOnly(NodeValueStructOption([Some(('c', 2)), Some(('d', 2))])),
            ),
            (
                'c',
                EdgesOnly(NodeValueStructOption([Some(('d', 4)), None])),
            ),
            ('d', EdgesOnly(NodeValueStructOption([None, None]))),
        ])
        .unwrap();
        let mut mst2 = [('0', '0', 0); 3];
        let mut edge_storage2 = [('0', '0', 0); 5];
        let res = kruskals(
            &graph,
            edge_storage2.as_mut_slice(),
            Dictionary::<_, _, 16>::new(),
            &mut mst2,
        )
        .unwrap();
        assert_eq!(res, &[('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 2)]);

        #[cfg(feature = "heapless")]
        {
            let graph = MapAdjacencyList::new(heapless::FnvIndexMap::<_, _, 8>::from_iter([
                (
                    'a',
                    EdgesOnly(NodeValueStructOption([
                        Some(('b', 1)),
                        None,
                        Some(('c', 3)),
                        None,
                    ])),
                ),
                (
                    'b',
                    EdgesOnly(NodeValueStructOption([
                        None,
                        None,
                        Some(('c', 2)),
                        Some(('d', 2)),
                    ])),
                ),
                (
                    'c',
                    EdgesOnly(NodeValueStructOption([None, None, Some(('d', 4)), None])),
                ),
                (
                    'd',
                    EdgesOnly(NodeValueStructOption([None, None, None, None])),
                ),
            ]))
            .unwrap();
            let mut mst3 = [('0', '0', 0); 3];
            let mut edge_storage3 = [('0', '0', 0); 5];
            let res = kruskals(
                &graph,
                edge_storage3.as_mut_slice(),
                Dictionary::<_, _, 16>::new(),
                &mut mst3,
            )
            .unwrap();
            assert_eq!(res, &[('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 2)]);
        }
    }
}
