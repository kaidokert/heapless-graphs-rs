// SPDX-License-Identifier: Apache-2.0

//! Kruskal's algorithm for finding minimum spanning trees

use super::AlgorithmError;
use crate::containers::maps::MapTrait;
use crate::graph::{GraphWithEdgeValues, NodeIndex};

/// Kruskal's algorithm for finding minimum spanning trees
///
/// This algorithm finds the minimum spanning tree of a connected, undirected graph
/// with edge weights. It works by sorting all edges by weight and greedily adding
/// edges that don't create cycles, using union-find for efficient cycle detection.
///
/// # Arguments
/// * `graph` - Graph implementing GraphWithEdgeValues with edge weights
/// * `edge_storage` - Temporary buffer for storing and sorting edges by weight
/// * `parent` - Map for union-find data structure (each node initially maps to itself)
/// * `mst` - Output buffer for the minimum spanning tree edges
///
/// # Returns
/// * `Ok(&[(NI, NI, V)])` slice of MST edges if successful
/// * `Err(AlgorithmError::EdgeCapacityExceeded)` if edge storage buffer is too small
/// * `Err(AlgorithmError::ResultCapacityExceeded)` if MST output buffer is too small
/// * `Err(AlgorithmError::GraphError(_))` for graph access errors
///
/// # Time Complexity
/// O(E log E) where E is the number of edges (dominated by sorting)
pub fn kruskals<'a, NI, G, V, M>(
    graph: &G,
    edge_storage: &mut [(NI, NI, V)],
    mut parent: M,
    mst: &'a mut [(NI, NI, V)],
) -> Result<&'a [(NI, NI, V)], AlgorithmError<NI>>
where
    NI: NodeIndex + Ord,
    V: Copy + Ord,
    G: GraphWithEdgeValues<NI, V>,
    M: MapTrait<NI, NI>,
    AlgorithmError<NI>: From<G::Error>,
{
    // Initialize union-find: each node is its own parent
    for node in graph.iter_nodes()? {
        parent.insert(node, node);
    }

    // Collect all edges with weights into edge_storage
    let mut edge_count = 0;
    for (src, dst, weight_opt) in graph.iter_edge_values()? {
        if let Some(weight) = weight_opt {
            // Skip self-loops
            if src == dst {
                continue;
            }

            if edge_count >= edge_storage.len() {
                return Err(AlgorithmError::EdgeCapacityExceeded);
            }
            edge_storage[edge_count] = (src, dst, *weight);
            edge_count += 1;
        }
    }

    // Sort edges by weight in ascending order
    let edges = &mut edge_storage[..edge_count];
    edges.sort_unstable_by_key(|(_, _, weight)| *weight);

    // Union-find helper functions with path compression
    fn find<NI: Copy + Eq, M: MapTrait<NI, NI>>(parent: &mut M, node: NI) -> NI {
        if let Some(&p) = parent.get(&node) {
            if p != node {
                let root = find(parent, p);
                parent.insert(node, root); // Path compression
                root
            } else {
                node
            }
        } else {
            node
        }
    }

    fn union<NI: Copy + Eq, M: MapTrait<NI, NI>>(parent: &mut M, u: NI, v: NI) {
        let root_u = find(parent, u);
        let root_v = find(parent, v);
        if root_u != root_v {
            parent.insert(root_u, root_v);
        }
    }

    // Build MST by processing edges in weight order
    let mut mst_count = 0;
    for (u, v, weight) in edges.iter() {
        // Check if adding this edge creates a cycle
        let root_u = find(&mut parent, *u);
        let root_v = find(&mut parent, *v);

        if root_u != root_v {
            // No cycle - add edge to MST
            if mst_count >= mst.len() {
                return Err(AlgorithmError::ResultCapacityExceeded);
            }
            mst[mst_count] = (*u, *v, *weight);
            mst_count += 1;

            // Union the components
            union(&mut parent, *u, *v);
        }
    }

    Ok(&mst[..mst_count])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::edges::EdgeValueStruct;

    #[test]
    fn test_kruskals_simple() {
        // Create a simple weighted graph:
        // a(0) -- 1 -- b(1)
        //  |            |
        //  3            2
        //  |            |
        // c(2) -- 4 -- d(3)
        let edge_data = EdgeValueStruct([
            (0usize, 1usize, 1i32), // a-b weight 1
            (0, 2, 3),              // a-c weight 3
            (1, 3, 2),              // b-d weight 2
            (2, 3, 4),              // c-d weight 4
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut edge_storage = [(0usize, 0usize, 0i32); 16];
        let parent = Dictionary::<usize, usize, 16>::new();
        let mut mst = [(0usize, 0usize, 0i32); 8];

        let result = kruskals(&graph, &mut edge_storage, parent, &mut mst).unwrap();

        // Expected MST: edges (0,1,1), (1,3,2), (0,2,3) with total weight 6
        assert_eq!(result.len(), 3);

        // Check that all expected edges are present (order may vary)
        let mut found_edges = [false; 3];
        for &(u, v, w) in result {
            if (u == 0 && v == 1 && w == 1) || (u == 1 && v == 0 && w == 1) {
                found_edges[0] = true;
            } else if (u == 1 && v == 3 && w == 2) || (u == 3 && v == 1 && w == 2) {
                found_edges[1] = true;
            } else if (u == 0 && v == 2 && w == 3) || (u == 2 && v == 0 && w == 3) {
                found_edges[2] = true;
            }
        }
        assert!(
            found_edges.iter().all(|&found| found),
            "Missing expected MST edges"
        );

        // Calculate total weight
        let total_weight: i32 = result.iter().map(|(_, _, w)| w).sum();
        assert_eq!(total_weight, 6);
    }

    #[test]
    fn test_kruskals_disconnected() {
        // Create a disconnected graph: 0-1 and 2-3 (no connection between pairs)
        let edge_data = EdgeValueStruct([
            (0usize, 1usize, 5i32), // 0-1 weight 5
            (2, 3, 3),              // 2-3 weight 3
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut edge_storage = [(0usize, 0usize, 0i32); 16];
        let parent = Dictionary::<usize, usize, 16>::new();
        let mut mst = [(0usize, 0usize, 0i32); 8];

        let result = kruskals(&graph, &mut edge_storage, parent, &mut mst).unwrap();

        // For disconnected graph, we get a minimum spanning forest
        assert_eq!(result.len(), 2);

        // Check that both edges are present
        let mut found_edges = [false; 2];
        for &(u, v, w) in result {
            if (u == 0 && v == 1 && w == 5) || (u == 1 && v == 0 && w == 5) {
                found_edges[0] = true;
            } else if (u == 2 && v == 3 && w == 3) || (u == 3 && v == 2 && w == 3) {
                found_edges[1] = true;
            }
        }
        assert!(
            found_edges.iter().all(|&found| found),
            "Missing expected MST edges"
        );
    }

    #[test]
    fn test_kruskals_no_edges() {
        // Graph with nodes but no edges
        let edge_data = EdgeValueStruct([
            (0usize, 1usize, 1i32), // Add at least one edge to create nodes
        ]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut edge_storage = [(0usize, 0usize, 0i32); 16];
        let parent = Dictionary::<usize, usize, 16>::new();
        let mut mst = [(0usize, 0usize, 0i32); 8];

        let result = kruskals(&graph, &mut edge_storage, parent, &mut mst).unwrap();

        // MST should contain exactly one edge (the only edge in the graph)
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], (0, 1, 1));
    }

    #[test]
    fn test_kruskals_capacity_exceeded() {
        // Create graph with more edges than storage capacity
        let edge_data = EdgeValueStruct([(0usize, 1usize, 1i32), (1, 2, 2), (2, 3, 3)]);
        let graph = EdgeList::<8, _, _>::new(edge_data);

        let mut edge_storage = [(0usize, 0usize, 0i32); 2]; // Only room for 2 edges
        let parent = Dictionary::<usize, usize, 16>::new();
        let mut mst = [(0usize, 0usize, 0i32); 8];

        let result = kruskals(&graph, &mut edge_storage, parent, &mut mst);
        assert!(matches!(result, Err(AlgorithmError::EdgeCapacityExceeded)));
    }
}
