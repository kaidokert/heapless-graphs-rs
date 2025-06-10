// SPDX-License-Identifier: Apache-2.0

//! Example demonstrating Kruskal's algorithm for finding minimum spanning trees

use heapless_graphs::{
    algorithms::kruskals,
    containers::maps::{staticdict::Dictionary, MapTrait},
    edgelist::edge_list::EdgeList,
    edges::EdgeValueStruct,
};

fn main() {
    println!("Kruskal's Algorithm - Minimum Spanning Tree");
    println!("==========================================");

    // Create a weighted graph representing a network of cities:
    //
    //     A(0) ---- 4 ---- B(1)
    //      |               |
    //      2               1
    //      |               |
    //     C(2) ---- 5 ---- D(3)
    //      |               |
    //      3               6
    //      |               |
    //     E(4) ---- 7 ---- F(5)
    //
    let edge_data = EdgeValueStruct([
        (0usize, 1usize, 4i32), // A-B weight 4
        (0, 2, 2),              // A-C weight 2
        (1, 3, 1),              // B-D weight 1
        (2, 3, 5),              // C-D weight 5
        (2, 4, 3),              // C-E weight 3
        (3, 5, 6),              // D-F weight 6
        (4, 5, 7),              // E-F weight 7
    ]);
    let graph = EdgeList::<16, _, _>::new(edge_data);

    // Set up data structures for Kruskal's algorithm
    let mut edge_storage = [(0usize, 0usize, 0i32); 32]; // Buffer for sorting edges
    let parent = Dictionary::<usize, usize, 16>::new(); // Union-find parent map
    let mut mst = [(0usize, 0usize, 0i32); 16]; // Output buffer for MST

    println!("Original graph edges:");
    println!("  A(0) - B(1): weight 4");
    println!("  A(0) - C(2): weight 2");
    println!("  B(1) - D(3): weight 1");
    println!("  C(2) - D(3): weight 5");
    println!("  C(2) - E(4): weight 3");
    println!("  D(3) - F(5): weight 6");
    println!("  E(4) - F(5): weight 7");
    println!();

    // Run Kruskal's algorithm
    match kruskals(&graph, &mut edge_storage, parent, &mut mst) {
        Ok(result) => {
            println!("Minimum Spanning Tree found!");
            println!("MST edges (in order found):");

            let city_names = ["A", "B", "C", "D", "E", "F"];
            let mut total_weight = 0;

            for (i, &(u, v, weight)) in result.iter().enumerate() {
                println!(
                    "  {}: {} - {} (weight: {})",
                    i + 1,
                    city_names[u],
                    city_names[v],
                    weight
                );
                total_weight += weight;
            }

            println!();
            println!("Total MST weight: {}", total_weight);
            println!("Number of edges in MST: {}", result.len());

            // Verify MST properties
            let num_nodes = 6;
            if result.len() == num_nodes - 1 {
                println!(
                    "✓ MST has correct number of edges (n-1 = {})",
                    num_nodes - 1
                );
            } else {
                println!("✗ MST has incorrect number of edges");
            }

            println!();
            println!("Visual representation of MST:");
            println!("     A(0) ---- 4 ---- B(1)");
            println!("      |               |");
            println!("      2               1");
            println!("      |               |");
            println!("     C(2)             D(3)");
            println!("      |");
            println!("      3");
            println!("      |");
            println!("     E(4)             F(5)");
            println!();
            println!("(F(5) is connected via D(3) with edge D-F weight 6)");
        }
        Err(e) => {
            println!("Kruskal's algorithm failed: {:?}", e);
        }
    }

    println!();
    println!("=== Testing with Disconnected Graph ===");

    // Test with a disconnected graph (two separate components)
    let disconnected_data = EdgeValueStruct([
        (0usize, 1usize, 10i32), // Component 1: A-B
        (1, 2, 15),              // Component 1: B-C
        (3, 4, 20),              // Component 2: D-E
        (4, 5, 25),              // Component 2: E-F
    ]);
    let disconnected_graph = EdgeList::<16, _, _>::new(disconnected_data);

    let mut edge_storage2 = [(0usize, 0usize, 0i32); 32];
    let parent2 = Dictionary::<usize, usize, 16>::new();
    let mut mst2 = [(0usize, 0usize, 0i32); 16];

    match kruskals(&disconnected_graph, &mut edge_storage2, parent2, &mut mst2) {
        Ok(result) => {
            println!("Minimum Spanning Forest found (disconnected graph):");
            let city_names = ["A", "B", "C", "D", "E", "F"];
            let mut total_weight = 0;

            for &(u, v, weight) in result {
                println!(
                    "  {} - {} (weight: {})",
                    city_names[u], city_names[v], weight
                );
                total_weight += weight;
            }

            println!("Total forest weight: {}", total_weight);
            println!(
                "Note: For disconnected graphs, Kruskal's produces a minimum spanning forest."
            );
        }
        Err(e) => {
            println!("Algorithm failed on disconnected graph: {:?}", e);
        }
    }
}
