#![cfg_attr(not(feature = "std"), no_std)]
// SPDX-License-Identifier: Apache-2.0

//! stack-friendly graph structures that do not require dynamic memory allocation.
//!
//! This crate provides composable building blocks for graph structures, all with
//! statically sized memory allocation.
//!
//! Minimal example:
//! ```
//!   # use heapless_graphs::VisitedTracker;
//!   # use heapless_graphs::algorithms::traversal::dfs_recursive;
//!   # use heapless_graphs::edgelist::edge_node_list::EdgeNodeList;
//!   // Create edges and nodes
//!   let graph = EdgeNodeList::new(
//!     [(1_usize, 5), (5, 3), (7, 7)],
//!     [7, 4, 3, 1, 5]).unwrap();
//!   let mut visited = [false; 10];
//!   dfs_recursive(&graph, &5, visited.as_mut_slice(), &mut |x| {
//!     println!("node: {}",x)
//!   });
//! ```
//!
//! The memory layout of the graphs is flexible: both edges and nodes can
//! be provided with and without associated values, edges can be pairs of
//! arrays or arrays of pairs, adding and removing is possible by storing
//! array elements as [`Option`], and/or using a backing store like
//! [`heapless::Vec`]
//!
//! The core abstractions are the [`GraphRef`] and [`GraphVal`] traits, which are automatically
//! implemented for edge list and adjacency list representations.
//!
//! [`GraphRef`]: graph::GraphRef
//! [`GraphVal`]: graph::GraphVal
//!
pub mod adjacency_list;
pub mod algorithms;
pub mod containers;
pub mod edgelist;
pub mod edges;
pub mod graph;
pub mod matrix;
pub mod nodes;
pub mod visited;

pub use algorithms::AlgorithmError;
pub use visited::VisitedTracker;
