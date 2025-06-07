// SPDX-License-Identifier: Apache-2.0

//! Example demonstrating greedy graph coloring algorithm

use heapless_graphs::{
    algorithms::greedy_coloring::greedy_color,
    containers::{
        maps::{staticdict::Dictionary, MapTrait},
        sets::{staticset::Set, SetTrait},
    },
    edgelist::edge_list::EdgeList,
};

fn main() {
    println!("Greedy Graph Coloring Algorithm");
    println!("===============================");

    // Create a graph representing conflicts between activities
    // If two activities are connected, they cannot have the same time slot (color)
    //
    // Activities:
    // 0: "Meeting A"
    // 1: "Meeting B"
    // 2: "Training Session"
    // 3: "Team Lunch"
    // 4: "Project Review"
    // 5: "Client Call"
    //
    // Conflicts (edges):
    // Meeting A conflicts with Meeting B, Training, and Client Call
    // Meeting B conflicts with Meeting A, Team Lunch, and Project Review
    // Training conflicts with Meeting A and Team Lunch
    // Team Lunch conflicts with Meeting B and Training
    // Project Review conflicts with Meeting B and Client Call
    // Client Call conflicts with Meeting A and Project Review

    let graph = EdgeList::<16, _, _>::new([
        (0usize, 1usize), // Meeting A - Meeting B
        (0, 2),           // Meeting A - Training Session
        (0, 5),           // Meeting A - Client Call
        (1, 3),           // Meeting B - Team Lunch
        (1, 4),           // Meeting B - Project Review
        (2, 3),           // Training Session - Team Lunch
        (4, 5),           // Project Review - Client Call
    ]);

    // Set up data structures for greedy coloring
    let color_assignment = Dictionary::<usize, Option<i32>, 16>::new();
    let neighbor_colors = Set::<Option<i32>, 16>::new();

    println!("Activity conflicts:");
    println!("  Meeting A conflicts with: Meeting B, Training Session, Client Call");
    println!("  Meeting B conflicts with: Meeting A, Team Lunch, Project Review");
    println!("  Training Session conflicts with: Meeting A, Team Lunch");
    println!("  Team Lunch conflicts with: Meeting B, Training Session");
    println!("  Project Review conflicts with: Meeting B, Client Call");
    println!("  Client Call conflicts with: Meeting A, Project Review");
    println!();

    // Run greedy coloring algorithm
    match greedy_color(&graph, color_assignment, neighbor_colors, 1i32, 1i32) {
        Ok(result) => {
            println!("Greedy coloring completed successfully!");
            println!("Time slot assignments:");

            let activities = [
                "Meeting A",
                "Meeting B",
                "Training Session",
                "Team Lunch",
                "Project Review",
                "Client Call",
            ];

            let time_slots = [
                "9:00 AM", "10:00 AM", "11:00 AM", "1:00 PM", "2:00 PM", "3:00 PM",
            ];

            // Print the color assignment
            for activity_id in 0..6 {
                if let Some(color_opt) = result.get(&activity_id) {
                    if let Some(color) = color_opt {
                        let time_slot_index = (*color - 1) as usize; // Convert to 0-based index
                        if time_slot_index < time_slots.len() {
                            println!(
                                "  {}: {} (Color {})",
                                activities[activity_id], time_slots[time_slot_index], color
                            );
                        }
                    }
                }
            }

            // Verify the coloring is valid
            println!();
            println!("Verification:");
            let mut valid = true;
            let conflict_pairs = [(0, 1), (0, 2), (0, 5), (1, 3), (1, 4), (2, 3), (4, 5)];

            for &(a, b) in &conflict_pairs {
                let color_a = result.get(&a).unwrap().unwrap();
                let color_b = result.get(&b).unwrap().unwrap();
                if color_a == color_b {
                    println!(
                        "  ✗ Conflict: {} and {} have same color {}",
                        activities[a], activities[b], color_a
                    );
                    valid = false;
                } else {
                    println!(
                        "  ✓ {} (Color {}) and {} (Color {}) have different colors",
                        activities[a], color_a, activities[b], color_b
                    );
                }
            }

            if valid {
                println!("\n🎉 All conflicts resolved! The coloring is valid.");

                // Count unique colors used
                let mut colors_used = Set::<i32, 16>::new();
                for activity_id in 0..6 {
                    if let Some(Some(color)) = result.get(&activity_id) {
                        colors_used.insert(*color);
                    }
                }
                println!("Total time slots needed: {}", colors_used.len());
            } else {
                println!("\n❌ Invalid coloring found!");
            }
        }
        Err(e) => {
            println!("Greedy coloring failed: {:?}", e);
        }
    }

    println!();
    println!("=== Testing Different Graph Types ===");

    // Test with a complete graph (clique) - should need n colors
    println!("\nTesting complete graph K4 (everyone conflicts with everyone):");
    let clique_graph = EdgeList::<16, _, _>::new([
        (0usize, 1usize),
        (0, 2),
        (0, 3), // Node 0 connects to all others
        (1, 2),
        (1, 3), // Node 1 connects to remaining
        (2, 3), // Node 2 connects to 3
    ]);

    let clique_colors = Dictionary::<usize, Option<i32>, 16>::new();
    let clique_neighbor_colors = Set::<Option<i32>, 16>::new();

    match greedy_color(
        &clique_graph,
        clique_colors,
        clique_neighbor_colors,
        1i32,
        1i32,
    ) {
        Ok(result) => {
            println!("Complete graph coloring:");
            for node in 0..4 {
                if let Some(Some(color)) = result.get(&node) {
                    println!("  Node {}: Color {}", node, color);
                }
            }

            let mut unique_colors = Set::<i32, 16>::new();
            for node in 0..4 {
                if let Some(Some(color)) = result.get(&node) {
                    unique_colors.insert(*color);
                }
            }
            println!(
                "Colors needed for K4: {} (should be 4)",
                unique_colors.len()
            );
        }
        Err(e) => {
            println!("Failed to color complete graph: {:?}", e);
        }
    }

    // Test with a bipartite graph - should need only 2 colors
    println!("\nTesting bipartite graph K2,2:");
    let bipartite_graph = EdgeList::<16, _, _>::new([
        (0usize, 2usize),
        (0, 3), // Left partition {0,1} connects to right partition {2,3}
        (1, 2),
        (1, 3),
    ]);

    let bipartite_colors = Dictionary::<usize, Option<i32>, 16>::new();
    let bipartite_neighbor_colors = Set::<Option<i32>, 16>::new();

    match greedy_color(
        &bipartite_graph,
        bipartite_colors,
        bipartite_neighbor_colors,
        1i32,
        1i32,
    ) {
        Ok(result) => {
            println!("Bipartite graph coloring:");
            for node in 0..4 {
                if let Some(Some(color)) = result.get(&node) {
                    println!("  Node {}: Color {}", node, color);
                }
            }

            let mut unique_colors = Set::<i32, 16>::new();
            for node in 0..4 {
                if let Some(Some(color)) = result.get(&node) {
                    unique_colors.insert(*color);
                }
            }
            println!(
                "Colors needed for K2,2: {} (should be 2)",
                unique_colors.len()
            );
        }
        Err(e) => {
            println!("Failed to color bipartite graph: {:?}", e);
        }
    }
}
