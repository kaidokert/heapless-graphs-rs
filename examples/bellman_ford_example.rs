// Example usage of Bellman-Ford algorithm with edge weights

use heapless_graphs::algorithms::bellman_ford::bellman_ford;
use heapless_graphs::containers::maps::staticdict::Dictionary;
use heapless_graphs::containers::maps::MapTrait;
use heapless_graphs::edgelist::edge_list::EdgeList;
use heapless_graphs::edges::EdgeValueStruct;

fn main() {
    println!("Bellman-Ford Algorithm Example");
    println!("==============================");

    // Create a weighted graph: 0 -> 1 (weight 5), 1 -> 2 (weight 3), 2 -> 0 (weight -2)
    let edge_data = EdgeValueStruct([
        (0usize, 1usize, 5i32), // Edge from 0 to 1 with weight 5
        (1, 2, 3),              // Edge from 1 to 2 with weight 3
        (2, 0, -2),             // Edge from 2 to 0 with weight -2
    ]);
    let graph = EdgeList::<8, _, _>::new(edge_data);

    // Initialize distance map (using larger size to avoid hash collisions)
    let distance_map = Dictionary::<usize, Option<i32>, 16>::new();

    println!("Running Bellman-Ford from source node 0...");

    // Run Bellman-Ford algorithm from source node 0
    match bellman_ford(&graph, 0, distance_map) {
        Ok(result) => {
            println!("Algorithm completed successfully!");
            println!("\nShortest distances from node 0:");

            // Print shortest distances
            for node in 0..3 {
                if let Some(dist_opt) = result.get(&node) {
                    match dist_opt {
                        Some(dist) => println!("  Node {}: distance = {}", node, dist),
                        None => println!("  Node {}: unreachable", node),
                    }
                }
            }
        }
        Err(e) => {
            println!("Algorithm failed: {:?}", e);
        }
    }

    println!("\n--- Testing Negative Cycle Detection ---");

    // Test negative cycle detection
    let negative_cycle_data = EdgeValueStruct([
        (0usize, 1usize, -1i32), // Edge creating negative cycle
        (1, 0, -1),              // Edge completing negative cycle
    ]);
    let neg_graph = EdgeList::<8, _, _>::new(negative_cycle_data);

    let distance_map2 = Dictionary::<usize, Option<i32>, 16>::new();

    match bellman_ford(&neg_graph, 0, distance_map2) {
        Ok(_) => println!("No negative cycle detected"),
        Err(e) => println!("Negative cycle detected: {:?}", e),
    }
}
