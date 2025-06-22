// SPDX-License-Identifier: Apache-2.0

//! Graph conversion demonstration
//!
//! This example demonstrates how to convert between different graph types
//! using the `from_graph` functionality.

use heapless_graphs::{
    adjacency_list::map_adjacency_list::MapAdjacencyList,
    containers::maps::{staticdict::Dictionary, MapTrait},
    edgelist::edge_list::EdgeList,
    edges::EdgeStructOption,
    graph::Graph,
};

fn main() {
    println!("Graph Conversion Demo");
    println!("====================");

    // Example 1: Convert MapAdjacencyList to EdgeList
    println!("\n1. Converting Adjacency List to Edge List");

    // Create a MapAdjacencyList representing a small social network
    // 0 (Alice) -> [1 (Bob), 2 (Charlie)]
    // 1 (Bob) -> [2 (Charlie), 3 (David)]
    // 2 (Charlie) -> [3 (David)]
    let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
    dict.insert(0, [1, 2]).unwrap(); // Alice knows Bob and Charlie
    dict.insert(1, [2, 3]).unwrap(); // Bob knows Charlie and David
    dict.insert(2, [3, 0]).unwrap(); // Charlie knows David and Alice (back-reference)
    dict.insert(3, [0, 1]).unwrap(); // David knows Alice and Bob

    let adjacency_graph = MapAdjacencyList::new_unchecked(dict);

    println!("Original adjacency list graph:");
    print_graph_info(&adjacency_graph);

    // Convert to EdgeList
    let edge_list_graph: EdgeList<8, usize, EdgeStructOption<16, usize>> =
        EdgeList::from_graph(&adjacency_graph).unwrap();

    println!("\nConverted to edge list:");
    print_graph_info(&edge_list_graph);

    // Example 2: Working with the converted graph
    println!("\n2. Working with the Converted Graph");

    // Both graphs should have the same edges and nodes
    let mut adj_edges = [(0usize, 0usize); 16];
    let mut edge_edges = [(0usize, 0usize); 16];

    let adj_edge_slice = collect(adjacency_graph.iter_edges().unwrap(), &mut adj_edges);
    let edge_edge_slice = collect(edge_list_graph.iter_edges().unwrap(), &mut edge_edges);

    println!("Edge count comparison:");
    println!("  Adjacency list: {} edges", adj_edge_slice.len());
    println!("  Edge list: {} edges", edge_edge_slice.len());
    assert_eq!(adj_edge_slice.len(), edge_edge_slice.len());

    let mut adj_nodes = [0usize; 8];
    let mut edge_nodes = [0usize; 8];

    let adj_node_slice = collect(adjacency_graph.iter_nodes().unwrap(), &mut adj_nodes);
    let edge_node_slice = collect(edge_list_graph.iter_nodes().unwrap(), &mut edge_nodes);

    println!("Node count comparison:");
    println!("  Adjacency list: {} nodes", adj_node_slice.len());
    println!("  Edge list: {} nodes", edge_node_slice.len());
    assert_eq!(adj_node_slice.len(), edge_node_slice.len());

    // Example 3: Converting a simple chain graph
    println!("\n3. Converting a Chain Graph");

    let mut chain_dict = Dictionary::<usize, [usize; 1], 8>::new();
    chain_dict.insert(0, [1]).unwrap(); // 0 -> 1
    chain_dict.insert(1, [2]).unwrap(); // 1 -> 2
    chain_dict.insert(2, [3]).unwrap(); // 2 -> 3
    chain_dict.insert(3, [4]).unwrap(); // 3 -> 4

    let chain_adjacency = MapAdjacencyList::new_unchecked(chain_dict);

    println!("Chain graph (adjacency list):");
    print_graph_info(&chain_adjacency);

    let chain_edge_list: EdgeList<8, usize, EdgeStructOption<8, usize>> =
        EdgeList::from_graph(&chain_adjacency).unwrap();

    println!("Chain graph (edge list):");
    print_graph_info(&chain_edge_list);

    // Example 4: Converting an empty graph
    println!("\n4. Converting an Empty Graph");

    let empty_dict = Dictionary::<usize, [usize; 2], 8>::new();
    let empty_adjacency = MapAdjacencyList::new_unchecked(empty_dict);

    let empty_edge_list: EdgeList<8, usize, EdgeStructOption<8, usize>> =
        EdgeList::from_graph(&empty_adjacency).unwrap();

    println!("Empty graph conversions:");
    println!(
        "  Adjacency list - nodes: {}, edges: {}",
        empty_adjacency.iter_nodes().unwrap().count(),
        empty_adjacency.iter_edges().unwrap().count()
    );

    // EdgeList may fail on iter_nodes for empty graphs, so handle gracefully
    let edge_list_node_count = match empty_edge_list.iter_nodes() {
        Ok(iter) => iter.count(),
        Err(_) => 0, // Empty edge list has no nodes
    };
    println!(
        "  Edge list - nodes: {}, edges: {}",
        edge_list_node_count,
        empty_edge_list.iter_edges().unwrap().count()
    );

    println!("\nGraph conversion is useful for:");
    println!("- Converting between different graph representations");
    println!("- Optimizing for different use cases (space vs. query speed)");
    println!("- Interfacing between different parts of an application");
    println!("- Testing graph algorithms with different backing stores");
}

/// Helper function to print basic graph information
fn print_graph_info<G: Graph<usize>>(graph: &G)
where
    G::Error: core::fmt::Debug,
{
    let node_count = graph.iter_nodes().unwrap().count();
    let edge_count = graph.iter_edges().unwrap().count();

    println!("  Nodes: {}, Edges: {}", node_count, edge_count);

    if edge_count <= 8 {
        // Only print edges for small graphs
        print!("  Edges: ");
        for (i, (from, to)) in graph.iter_edges().unwrap().enumerate() {
            if i > 0 {
                print!(", ");
            }
            print!("{}→{}", from, to);
        }
        println!();
    }
}

/// Helper function to collect iterator into slice (copied from tests)
fn collect<T: Copy, I: Iterator<Item = T>>(iter: I, dest: &mut [T]) -> &mut [T] {
    let slice_len = iter
        .zip(dest.iter_mut())
        .map(|(item, slot)| *slot = item)
        .count();
    &mut dest[..slice_len]
}
