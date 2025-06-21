// SPDX-License-Identifier: Apache-2.0

//! Graph transposition demonstration
//!
//! This example demonstrates how to use the graph transposition algorithm
//! to reverse the direction of all edges in a directed graph.

use heapless_graphs::{
    algorithms::{transpose_graph, transpose_graph_inplace},
    edgelist::edge_list::EdgeList,
    graph::Graph,
};

fn main() {
    println!("Graph Transposition Demo");
    println!("========================");

    // Example 1: Dependency Analysis
    println!("\n1. Software Dependency Analysis");
    println!("Original dependencies: A->B, B->C, A->C");

    // Create a dependency graph: A depends on B, B depends on C, A depends on C
    let dependencies = EdgeList::<8, usize, _>::new([(0, 1), (1, 2), (0, 2)]); // A=0, B=1, C=2
    let mut reverse_deps = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

    transpose_graph(&dependencies, &mut reverse_deps).unwrap();

    println!("Reverse dependencies (who depends on whom):");
    for (from, to) in reverse_deps.iter_edges().unwrap() {
        let from_name = match from {
            0 => "A",
            1 => "B",
            2 => "C",
            _ => "?",
        };
        let to_name = match to {
            0 => "A",
            1 => "B",
            2 => "C",
            _ => "?",
        };
        println!("  {} is depended on by {}", from_name, to_name);
    }

    // Example 2: Social Network
    println!("\n2. Social Network Analysis");
    println!("Original follows: Alice->Bob, Bob->Charlie, Alice->Charlie");

    let follows = EdgeList::<8, usize, _>::new([(0, 1), (1, 2), (0, 2)]); // Alice=0, Bob=1, Charlie=2
    let mut followers = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([None; 8]);

    transpose_graph(&follows, &mut followers).unwrap();

    println!("Follower relationships:");
    for (followed, follower) in followers.iter_edges().unwrap() {
        let followed_name = match followed {
            0 => "Alice",
            1 => "Bob",
            2 => "Charlie",
            _ => "?",
        };
        let follower_name = match follower {
            0 => "Alice",
            1 => "Bob",
            2 => "Charlie",
            _ => "?",
        };
        println!("  {} is followed by {}", followed_name, follower_name);
    }

    // Example 3: In-place transposition
    println!("\n3. In-place Transposition");
    let mut graph = EdgeList::<8, usize, [Option<(usize, usize)>; 8]>::new([
        Some((0, 1)),
        Some((1, 2)),
        Some((2, 0)),
        None,
        None,
        None,
        None,
        None,
    ]);
    let mut buffer = [(0usize, 0usize); 8];

    println!("Before transpose:");
    for (from, to) in graph.iter_edges().unwrap() {
        println!("  {} -> {}", from, to);
    }

    transpose_graph_inplace(&mut graph, &mut buffer).unwrap();

    println!("After transpose:");
    for (from, to) in graph.iter_edges().unwrap() {
        println!("  {} -> {}", from, to);
    }
}
