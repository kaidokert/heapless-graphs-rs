// SPDX-License-Identifier: Apache-2.0

//! Tarjan's Strongly Connected Components Algorithm
//!
//! Finds all strongly connected components (SCCs) in a directed graph using
//! Tarjan's algorithm. A strongly connected component is a maximal set of vertices
//! such that there is a path from each vertex to every other vertex in the component.
//!
//! This implementation uses a single DFS pass with a stack to identify SCCs.

use super::AlgorithmError;

use crate::containers::queues::Deque;
use crate::graph::GraphRef;

/// Result of Tarjan's SCC algorithm
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TarjanState {
    /// DFS discovery time
    pub index: usize,
    /// Low-link value (lowest index reachable)
    pub lowlink: usize,
    /// Whether node is currently on the stack
    pub on_stack: bool,
}

impl Default for TarjanState {
    fn default() -> Self {
        Self {
            index: usize::MAX, // Use MAX as "unvisited" marker
            lowlink: usize::MAX,
            on_stack: false,
        }
    }
}

/// Find all strongly connected components using Tarjan's algorithm
///
/// This function performs a single DFS traversal to identify all SCCs in the graph.
/// Each SCC is collected into the provided buffer.
///
/// # Arguments
/// * `graph` - The directed graph to analyze
/// * `state` - Array to track DFS state for each node (indexed by node value for integer nodes)
/// * `stack` - Stack for tracking the current DFS path
/// * `components` - Buffer to store the strongly connected components
/// * `node_buffer` - Temporary buffer for collecting nodes in each component
///
/// # Returns
/// The number of SCCs found, or an error if buffers are too small
///
/// # Note
/// This implementation assumes nodes are integers that can be used as array indices.
/// For non-integer nodes, consider using a map-based approach.
pub fn tarjan_scc<'a, G, S>(
    graph: &G,
    state: &mut [TarjanState],
    mut stack: S,
    components: &mut [&'a [usize]],
    node_buffer: &'a mut [usize],
) -> Result<usize, AlgorithmError<usize>>
where
    G: GraphRef<usize>,
    S: Deque<usize>,
    AlgorithmError<usize>: From<G::Error>,
{
    let mut index_counter = 0;
    let mut component_count = 0;
    let mut buffer_offset = 0;
    let mut component_sizes = [0usize; 32]; // Max 32 components

    // Run DFS from each unvisited node
    for node in graph.iter_nodes()? {
        if state[*node].index == usize::MAX {
            let (_new_index, new_components, new_buffer_offset) = tarjan_dfs(
                graph,
                *node,
                state,
                &mut stack,
                &mut index_counter,
                &mut node_buffer[buffer_offset..],
                &mut component_sizes[component_count..],
            )?;
            component_count += new_components;
            buffer_offset += new_buffer_offset;

            if component_count >= components.len() {
                return Err(AlgorithmError::ResultCapacityExceeded);
            }
        }
    }

    // Populate component slices
    let mut current_offset = 0;
    for i in 0..component_count {
        let component_size = component_sizes[i];
        components[i] = &node_buffer[current_offset..current_offset + component_size];
        current_offset += component_size;
    }

    Ok(component_count)
}

/// Recursive DFS helper for Tarjan's algorithm
fn tarjan_dfs<G, S>(
    graph: &G,
    node: usize,
    state: &mut [TarjanState],
    stack: &mut S,
    index_counter: &mut usize,
    node_buffer: &mut [usize],
    component_sizes: &mut [usize],
) -> Result<(usize, usize, usize), AlgorithmError<usize>>
where
    G: GraphRef<usize>,
    S: Deque<usize>,
    AlgorithmError<usize>: From<G::Error>,
{
    // Initialize this node
    state[node].index = *index_counter;
    state[node].lowlink = *index_counter;
    state[node].on_stack = true;
    *index_counter += 1;

    stack
        .push_back(node)
        .map_err(|_| AlgorithmError::StackCapacityExceeded)?;

    let mut component_count = 0;
    let mut buffer_offset = 0;

    // Explore neighbors
    for neighbor in graph.outgoing_edges(&node)? {
        let neighbor_idx = *neighbor;

        if state[neighbor_idx].index == usize::MAX {
            // Neighbor not visited, recurse
            let (_new_index, new_components, new_buffer_offset) = tarjan_dfs(
                graph,
                neighbor_idx,
                state,
                stack,
                index_counter,
                &mut node_buffer[buffer_offset..],
                &mut component_sizes[component_count..],
            )?;

            component_count += new_components;
            buffer_offset += new_buffer_offset;

            // Update lowlink
            state[node].lowlink = state[node].lowlink.min(state[neighbor_idx].lowlink);
        } else if state[neighbor_idx].on_stack {
            // Neighbor is on stack, update lowlink
            state[node].lowlink = state[node].lowlink.min(state[neighbor_idx].index);
        }
    }

    // If node is a root node, pop the stack and create an SCC
    if state[node].lowlink == state[node].index {
        let mut component_size = 0;

        loop {
            let Some(stack_node) = stack.pop_back() else {
                return Err(AlgorithmError::StackCapacityExceeded);
            };

            state[stack_node].on_stack = false;

            if buffer_offset + component_size >= node_buffer.len() {
                return Err(AlgorithmError::ResultCapacityExceeded);
            }

            node_buffer[buffer_offset + component_size] = stack_node;
            component_size += 1;

            if stack_node == node {
                break;
            }
        }

        component_sizes[component_count] = component_size;
        component_count += 1;
        buffer_offset += component_size;
    }

    Ok((*index_counter, component_count, buffer_offset))
}

/// Count the number of strongly connected components without collecting them
///
/// More memory-efficient version that only counts SCCs.
pub fn count_tarjan_scc<G, S>(
    graph: &G,
    state: &mut [TarjanState],
    mut stack: S,
) -> Result<usize, AlgorithmError<usize>>
where
    G: GraphRef<usize>,
    S: Deque<usize>,
    AlgorithmError<usize>: From<G::Error>,
{
    let mut index_counter = 0;
    let mut component_count = 0;

    // Run DFS from each unvisited node
    for node in graph.iter_nodes()? {
        if state[*node].index == usize::MAX {
            component_count +=
                tarjan_count_dfs(graph, *node, state, &mut stack, &mut index_counter)?;
        }
    }

    Ok(component_count)
}

/// DFS helper for counting SCCs
fn tarjan_count_dfs<G, S>(
    graph: &G,
    node: usize,
    state: &mut [TarjanState],
    stack: &mut S,
    index_counter: &mut usize,
) -> Result<usize, AlgorithmError<usize>>
where
    G: GraphRef<usize>,
    S: Deque<usize>,
    AlgorithmError<usize>: From<G::Error>,
{
    // Initialize this node
    state[node].index = *index_counter;
    state[node].lowlink = *index_counter;
    state[node].on_stack = true;
    *index_counter += 1;

    stack
        .push_back(node)
        .map_err(|_| AlgorithmError::StackCapacityExceeded)?;

    let mut component_count = 0;

    // Explore neighbors
    for neighbor in graph.outgoing_edges(&node)? {
        let neighbor_idx = *neighbor;

        if state[neighbor_idx].index == usize::MAX {
            // Neighbor not visited, recurse
            component_count += tarjan_count_dfs(graph, neighbor_idx, state, stack, index_counter)?;

            // Update lowlink
            state[node].lowlink = state[node].lowlink.min(state[neighbor_idx].lowlink);
        } else if state[neighbor_idx].on_stack {
            // Neighbor is on stack, update lowlink
            state[node].lowlink = state[node].lowlink.min(state[neighbor_idx].index);
        }
    }

    // If node is a root node, pop the stack and count an SCC
    if state[node].lowlink == state[node].index {
        component_count += 1;

        // Pop nodes until we reach the root
        loop {
            let Some(stack_node) = stack.pop_back() else {
                return Err(AlgorithmError::StackCapacityExceeded);
            };

            state[stack_node].on_stack = false;

            if stack_node == node {
                break;
            }
        }
    }

    Ok(component_count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::{
        maps::{staticdict::Dictionary, MapTrait},
        queues::CircularQueue,
    };
    use crate::edgelist::edge_list::EdgeList;

    #[test]
    fn test_tarjan_scc_simple_cycle() {
        // Simple cycle: 0 -> 1 -> 2 -> 0
        let edges = [(0, 1), (1, 2), (2, 0)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut state = [TarjanState::default(); 10];
        let stack = CircularQueue::<usize, 10>::new();
        let mut components: [&[usize]; 5] = [&[]; 5];
        let mut node_buffer = [0usize; 10];

        let component_count =
            tarjan_scc(&graph, &mut state, stack, &mut components, &mut node_buffer).unwrap();

        // Should find 1 SCC containing all 3 nodes
        assert_eq!(component_count, 1);
        assert_eq!(components[0].len(), 3);

        // Verify all nodes are in the component
        let mut nodes_in_component = [0; 3];
        for (i, &node) in components[0].iter().enumerate() {
            nodes_in_component[i] = node;
        }
        nodes_in_component.sort();
        assert_eq!(nodes_in_component, [0, 1, 2]);
    }

    #[test]
    fn test_tarjan_scc_disconnected_components() {
        // Two separate cycles: 0->1->0 and 2->3->2
        let edges = [(0, 1), (1, 0), (2, 3), (3, 2)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut state = [TarjanState::default(); 10];
        let stack = CircularQueue::<usize, 10>::new();
        let count = count_tarjan_scc(&graph, &mut state, stack).unwrap();

        // Should find 2 SCCs
        assert_eq!(count, 2);
    }

    #[test]
    fn test_tarjan_scc_dag() {
        // Directed acyclic graph: 0->1, 0->2, 1->3, 2->3
        let edges = [(0, 1), (0, 2), (1, 3), (2, 3)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut state = [TarjanState::default(); 10];
        let stack = CircularQueue::<usize, 10>::new();
        let count = count_tarjan_scc(&graph, &mut state, stack).unwrap();

        // DAG should have 4 SCCs (each node is its own SCC)
        assert_eq!(count, 4);
    }

    #[test]
    fn test_tarjan_scc_complex() {
        // More complex graph with multiple SCCs
        // SCC 1: {0, 1, 2} - strongly connected
        // SCC 2: {3} - single node
        // SCC 3: {4, 5} - cycle
        let mut dict = Dictionary::<usize, [usize; 3], 10>::new();
        dict.insert(0, [1, 3, 0]); // 0 -> 1, 3 (self-loop as padding)
        dict.insert(1, [2, 1, 1]); // 1 -> 2 (padding)
        dict.insert(2, [0, 2, 2]); // 2 -> 0 (padding)
        dict.insert(3, [4, 3, 3]); // 3 -> 4 (padding)
        dict.insert(4, [5, 4, 4]); // 4 -> 5 (padding)
        dict.insert(5, [4, 5, 5]); // 5 -> 4 (padding)

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut state = [TarjanState::default(); 10];
        let stack = CircularQueue::<usize, 20>::new();
        let mut components: [&[usize]; 5] = [&[]; 5];
        let mut node_buffer = [0usize; 10];

        let component_count =
            tarjan_scc(&graph, &mut state, stack, &mut components, &mut node_buffer).unwrap();

        // Should find 3 SCCs
        assert_eq!(component_count, 3);

        // Check component sizes
        let mut sizes = [0; 3];
        for i in 0..component_count {
            sizes[i] = components[i].len();
        }
        sizes.sort();
        assert_eq!(sizes, [1, 2, 3]); // One single node, one pair, one triple
    }

    #[test]
    fn test_tarjan_scc_self_loops() {
        // Graph with self-loops: 0->0, 1->1, 0->1
        let edges = [(0, 0), (1, 1), (0, 1)];
        let graph = EdgeList::<10, usize, _>::new(edges);

        let mut state = [TarjanState::default(); 10];
        let stack = CircularQueue::<usize, 10>::new();
        let count = count_tarjan_scc(&graph, &mut state, stack).unwrap();

        // Each node with a self-loop is its own SCC
        assert_eq!(count, 2);
    }

    #[test]
    fn test_tarjan_scc_single_node() {
        // Single node with no edges
        let mut dict = Dictionary::<usize, [usize; 0], 5>::new();
        dict.insert(42, []);

        let graph = MapAdjacencyList::new_unchecked(dict);

        let mut state = [TarjanState::default(); 50];
        let stack = CircularQueue::<usize, 10>::new();
        let count = count_tarjan_scc(&graph, &mut state, stack).unwrap();

        // Single isolated node is one SCC
        assert_eq!(count, 1);
    }
}
