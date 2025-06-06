// SPDX-License-Identifier: Apache-2.0

//! Example demonstrating Dijkstra's shortest path algorithm
//!
//! This example shows how to use Dijkstra's algorithm to find shortest paths
//! from a source node to all other nodes in a weighted graph.

use heapless_graphs::algorithms::dijkstra::dijkstra;
use heapless_graphs::containers::maps::staticdict::Dictionary;
use heapless_graphs::containers::maps::MapTrait;
use heapless_graphs::edgelist::edge_list::EdgeList;
use heapless_graphs::edges::EdgeValueStruct;

fn main() {
    println!("Dijkstra's Algorithm Example");
    println!("============================");

    // Create a weighted graph representing a simple network
    //
    //     A ----5---- B
    //     |           |
    //     2           1
    //     |           |
    //     C ----3---- D ----4---- E
    //     |           |           |
    //     6           2           1
    //     |           |           |
    //     F ----1---- G ----3---- H

    let edges = EdgeValueStruct([
        ('A', 'B', 5),
        ('A', 'C', 2),
        ('B', 'D', 1),
        ('C', 'D', 3),
        ('C', 'F', 6),
        ('D', 'E', 4),
        ('D', 'G', 2),
        ('E', 'H', 1),
        ('F', 'G', 1),
        ('G', 'H', 3),
    ]);

    let graph = EdgeList::<16, _, _>::new(edges);

    let distance_map = Dictionary::<char, Option<i32>, 16>::new();
    let visited = Dictionary::<char, bool, 16>::new();

    println!("\nFinding shortest paths from node 'A'...");

    match dijkstra(&graph, 'A', visited, distance_map) {
        Ok(result) => {
            println!("\nShortest distances from A:");
            let nodes = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'];

            for node in nodes.iter() {
                if let Some(dist_opt) = result.get(node) {
                    match dist_opt {
                        Some(dist) => println!("  A -> {}: {}", node, dist),
                        None => println!("  A -> {}: unreachable", node),
                    }
                }
            }

            println!("\nShortest path analysis:");
            println!(
                "  A -> B: direct (cost 5) vs A -> C -> D -> B (cost 2+3+1=6), so direct is better"
            );
            println!("  A -> D: A -> C -> D (cost 2+3=5) vs A -> B -> D (cost 5+1=6), so via C is better");
            println!("  A -> H: A -> C -> F -> G -> H (cost 2+6+1+3=12) vs A -> C -> D -> G -> H (cost 2+3+2+3=10)");
        }
        Err(e) => {
            println!("Error running Dijkstra: {:?}", e);
        }
    }

    // Example with a disconnected graph
    println!("\n\nExample with disconnected components:");
    println!("=====================================");

    let disconnected_edges = EdgeValueStruct([
        (1, 2, 10),
        (2, 3, 5),
        (4, 5, 3), // Disconnected component
    ]);

    let disconnected_graph = EdgeList::<8, _, _>::new(disconnected_edges);

    let distance_map2 = Dictionary::<i32, Option<i32>, 16>::new();
    let visited2 = Dictionary::<i32, bool, 16>::new();

    println!("Finding shortest paths from node 1...");

    match dijkstra(&disconnected_graph, 1, visited2, distance_map2) {
        Ok(result) => {
            println!("\nDistances from node 1:");
            for node in [1, 2, 3, 4, 5].iter() {
                if let Some(dist_opt) = result.get(node) {
                    match dist_opt {
                        Some(dist) => println!("  1 -> {}: {}", node, dist),
                        None => println!("  1 -> {}: unreachable", node),
                    }
                }
            }
        }
        Err(e) => {
            println!("Error running Dijkstra: {:?}", e);
        }
    }
}
