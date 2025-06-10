// SPDX-License-Identifier: Apache-2.0

//! Connected Components Algorithm
//!
//! Finds all connected components in an undirected graph using depth-first search.
//! A connected component is a maximal set of vertices such that there is a path
//! between every pair of vertices.

use super::AlgorithmError;

use crate::graph::{GraphRef, NodeIndexTrait};
use crate::visited::VisitedTracker;

/// Find all connected components in an undirected graph
///
/// This function identifies all connected components in the graph by performing
/// DFS from each unvisited node. Each connected component is collected into
/// the provided buffer.
///
/// # Arguments
/// * `graph` - The graph to analyze
/// * `visited` - Tracker for visited nodes
/// * `components` - Buffer to store the connected components as (slice, size) tuples
/// * `node_buffer` - Temporary buffer for collecting nodes in each component
///
/// # Returns
/// The number of connected components found, or an error if buffers are too small
///
/// # Example
/// ```ignore
/// let mut visited = [false; 10];
/// let mut components = [(&[0usize][..], 0usize); 5]; // Up to 5 components with sizes
/// let mut node_buffer = [0usize; 10];
///
/// let component_count = connected_components(
///     &graph,
///     visited.as_mut_slice(),
///     &mut components,
///     &mut node_buffer
/// )?;
/// ```
pub fn connected_components<'a, G, NI, VT>(
    graph: &G,
    visited: &mut VT,
    components: &mut [(&'a [NI], usize)],
    node_buffer: &'a mut [NI],
) -> Result<usize, AlgorithmError<NI>>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    let mut component_count = 0;
    let mut buffer_offset = 0;

    // First pass: collect all components and store sizes
    for node in graph.iter_nodes()? {
        if !visited.is_visited(node) {
            if component_count >= components.len() {
                return Err(AlgorithmError::ResultCapacityExceeded);
            }

            // Collect all nodes in this connected component
            let remaining_buffer = &mut node_buffer[buffer_offset..];
            let component_size = dfs_component_collection(graph, node, visited, remaining_buffer)?;

            if buffer_offset + component_size > node_buffer.len() {
                return Err(AlgorithmError::ResultCapacityExceeded);
            }

            // Store size temporarily (slice will be filled in second pass)
            components[component_count] = (&[], component_size);
            buffer_offset += component_size;
            component_count += 1;
        }
    }

    // Second pass: populate component slices
    let mut current_offset = 0;
    for component in components.iter_mut().take(component_count) {
        let component_size = component.1;
        let component_slice = &node_buffer[current_offset..current_offset + component_size];
        *component = (component_slice, component_size);
        current_offset += component_size;
    }

    Ok(component_count)
}

/// Helper function to collect all nodes in a connected component using DFS
///
/// Performs depth-first search starting from the given node and collects
/// all reachable nodes into the provided buffer.
fn dfs_component_collection<G, NI, VT>(
    graph: &G,
    start_node: &NI,
    visited: &mut VT,
    buffer: &mut [NI],
) -> Result<usize, AlgorithmError<NI>>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    let mut count = 0;

    // Use a simple recursive DFS to collect nodes
    dfs_collect_recursive(graph, start_node, visited, buffer, &mut count)?;

    Ok(count)
}

/// Recursive helper for DFS node collection
fn dfs_collect_recursive<G, NI, VT>(
    graph: &G,
    node: &NI,
    visited: &mut VT,
    buffer: &mut [NI],
    count: &mut usize,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait + Copy,
    VT: VisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    if visited.is_visited(node) {
        return Ok(());
    }

    // Mark as visited and add to buffer
    visited.mark_visited(node);

    if *count >= buffer.len() {
        return Err(AlgorithmError::ResultCapacityExceeded);
    }

    buffer[*count] = *node;
    *count += 1;

    // Recursively visit all unvisited neighbors
    for neighbor in graph.outgoing_edges(node)? {
        if !visited.is_visited(neighbor) {
            dfs_collect_recursive(graph, neighbor, visited, buffer, count)?;
        }
    }

    Ok(())
}

/// Count the number of connected components without collecting the actual components
///
/// This is a more memory-efficient version that only counts components
/// without storing them.
pub fn count_connected_components<G, NI, VT>(
    graph: &G,
    visited: &mut VT,
) -> Result<usize, AlgorithmError<NI>>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait,
    VT: VisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    let mut component_count = 0;

    for node in graph.iter_nodes()? {
        if !visited.is_visited(node) {
            // Start DFS from this unvisited node
            dfs_mark_component(graph, node, visited)?;
            component_count += 1;
        }
    }

    Ok(component_count)
}

/// Helper function to mark all nodes in a connected component as visited
fn dfs_mark_component<G, NI, VT>(
    graph: &G,
    start_node: &NI,
    visited: &mut VT,
) -> Result<(), AlgorithmError<NI>>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait,
    VT: VisitedTracker<NI> + ?Sized,
    AlgorithmError<NI>: From<G::Error>,
{
    if visited.is_visited(start_node) {
        return Ok(());
    }

    visited.mark_visited(start_node);

    for neighbor in graph.outgoing_edges(start_node)? {
        if !visited.is_visited(neighbor) {
            dfs_mark_component(graph, neighbor, visited)?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::{staticdict::Dictionary, MapTrait};
    use crate::edgelist::edge_list::EdgeList;
    use crate::edgelist::edge_node_list::EdgeNodeList;

    #[test]
    fn test_connected_components_edge_list() {
        // Create a graph with 3 connected components:
        // Component 1: 0-1-2
        // Component 2: 3-4
        // Component 3: 5 (isolated)
        let edges = [(0, 1), (1, 2), (3, 4)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut visited = [false; 10];
        let mut components: [(&[usize], usize); 5] = [(&[], 0); 5];
        let mut node_buffer = [0usize; 10];

        let component_count = connected_components(
            &graph,
            visited.as_mut_slice(),
            &mut components,
            &mut node_buffer,
        )
        .unwrap();

        // Should find 2 components
        assert_eq!(component_count, 2);

        // Check component sizes
        assert_eq!(components[0].0.len(), 3); // 0-1-2
        assert_eq!(components[1].0.len(), 2); // 3-4

        // Verify all nodes are accounted for
        let mut all_nodes = [0usize; 10];
        let mut total_nodes = 0;
        for i in 0..component_count {
            for &node in components[i].0 {
                all_nodes[total_nodes] = node;
                total_nodes += 1;
            }
        }
        all_nodes[..total_nodes].sort();
        assert_eq!(&all_nodes[..total_nodes], &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_count_connected_components() {
        let edges = [(0, 1), (1, 2), (3, 4)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut visited = [false; 10];
        let count = count_connected_components(&graph, visited.as_mut_slice()).unwrap();

        assert_eq!(count, 2); // Two components: {0,1,2}, {3,4}
    }

    #[test]
    fn test_connected_components_single_component() {
        // All nodes connected: 0-1-2-3
        let edges = [(0, 1), (1, 2), (2, 3)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut visited = [false; 10];
        let count = count_connected_components(&graph, visited.as_mut_slice()).unwrap();

        assert_eq!(count, 1); // One component containing all nodes
    }

    #[test]
    fn test_connected_components_map_adjacency_list() {
        // Test with different graph type
        let mut dict = Dictionary::<usize, [usize; 2], 5>::new();
        dict.insert(0, [1, 2]); // 0 connects to 1, 2
        dict.insert(1, [0, 2]); // 1 connects to 0, 2
        dict.insert(2, [0, 1]); // 2 connects to 0, 1
        dict.insert(3, [3, 3]); // 3 is isolated (self-loop)

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut visited = [false; 10];
        let count = count_connected_components(&graph, visited.as_mut_slice()).unwrap();

        assert_eq!(count, 2); // Two components: {0,1,2} and {3}
    }

    #[test]
    fn test_connected_components_empty_graph() {
        let edges: [(usize, usize); 0] = [];
        let graph = EdgeList::<5, usize, _>::new(edges);

        let mut visited = [false; 5];

        // Empty EdgeList will return an error when trying to iterate nodes
        // because EdgesToNodesIterator requires at least one edge
        let result = count_connected_components(&graph, visited.as_mut_slice());
        assert!(result.is_err()); // Should error on empty graph
    }

    #[test]
    fn test_connected_components_edge_node_list_with_isolated() {
        // EdgeNodeList allows us to define isolated nodes explicitly
        // Create a graph with 3 connected components:
        // Component 1: 0-1-2
        // Component 2: 3-4
        // Component 3: 5 (isolated)
        let edges = [(0, 1), (1, 2), (3, 4)];
        let nodes = [0, 1, 2, 3, 4, 5]; // Node 5 is isolated
        let graph = EdgeNodeList::<usize, _, _>::new(edges, nodes).unwrap();

        let mut visited = [false; 10];
        let mut components: [(&[usize], usize); 5] = [(&[], 0); 5];
        let mut node_buffer = [0usize; 10];

        let component_count = connected_components(
            &graph,
            visited.as_mut_slice(),
            &mut components,
            &mut node_buffer,
        )
        .unwrap();

        // Should find 3 components including the isolated node
        assert_eq!(component_count, 3);

        // Check component sizes
        let mut sizes = [0; 3];
        for i in 0..component_count {
            sizes[i] = components[i].0.len();
        }
        sizes.sort(); // Sort to make assertion order-independent
        assert_eq!(sizes, [1, 2, 3]); // One isolated (1), one pair (2), one triple (3)

        // Verify all nodes are accounted for
        let mut all_nodes = [0usize; 10];
        let mut total_nodes = 0;
        for i in 0..component_count {
            for &node in components[i].0 {
                all_nodes[total_nodes] = node;
                total_nodes += 1;
            }
        }
        all_nodes[..total_nodes].sort();
        assert_eq!(&all_nodes[..total_nodes], &[0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_connected_components_all_isolated() {
        // Graph with nodes but no edges - each node is its own component
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(0, []);
        dict.insert(1, []);
        dict.insert(2, []);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut visited = [false; 10];
        let count = count_connected_components(&graph, visited.as_mut_slice()).unwrap();

        assert_eq!(count, 3); // Three isolated nodes = three components
    }
}
