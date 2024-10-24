#![cfg_attr(not(feature = "std"), no_std)]
// SPDX-License-Identifier: Apache-2.0

//! `static` friendly graph structures that do not require dynamic memory allocation.
//!
//! This crate provides composable building blocks for graph structures, all with
//! statically sized memory allocation.
//!
//! Minimal example:
//! ```
//!   # use heapless_graphs::VisitedTracker;
//!   # use heapless_graphs::algorithms::dfs_recursive;
//!   # use heapless_graphs::edge_list::EdgeNodeList;
//!   // Create edges and nodes
//!   let graph = EdgeNodeList::new(
//!     [(1_usize, 5), (5, 3), (7, 7)],
//!     [7, 4, 3, 1, 5]).unwrap();
//!   let mut visited = [false; 10];
//!   dfs_recursive(&graph, 5, visited.as_mut_slice(), &mut |x| {
//!     println!("node: {}",x)
//!   });
//! ```
//!
//! More complex example:, with node values provided
//! ```
//!   # use heapless_graphs::{edges::EdgeStruct,nodes::NodeValueTwoArray,VisitedTracker};
//!   # use heapless_graphs::edge_list::EdgeNodeList;
//!   # use heapless_graphs::algorithms::dfs_recursive;
//!   // Create edges of `usize` and nodes with values of `char`
//!   let edges = [(1_usize, 5), (5, 3), (7, 7)];
//!   let nodes = NodeValueTwoArray( [7, 4, 3, 1, 5], ['b', 'z', 'c', 'x', 'a']);
//!   // Create the graph and check for consistency
//!   let graph = EdgeNodeList::new(edges, nodes).unwrap();
//!   // Provide a visited tracker
//!   let mut visited = [false; 10];
//!   // Do a DFS traversal, starting from node 5
//!   dfs_recursive(&graph, 5, visited.as_mut_slice(), &mut |x| {
//!     println!("node: {}",x)
//!   });
//! ```
//!
//! You can also create graphs only from edges, in a very compact ( but
//! very slow !) representation.
//! ```
//!   # use heapless_graphs::{edges::EdgeValueStruct,NodeState};
//!   # use heapless_graphs::edge_list::EdgeList;
//!   # use heapless_graphs::containers::maps::{staticdict::Dictionary,MapTrait};
//!   # use heapless_graphs::algorithms::topological_sort;
//!   # use heapless_graphs::visited::MapWrapper;
//!   // Edges of `usize` with values of `char`
//!   let edges = [(1_usize, 20, 'x'), (0, 1, 'a'), (3, 2, 'c')];
//!   // Create graph from edges, specifying max number of nodes
//!   let graph = EdgeList::<16,_,_>::new(edges).unwrap();
//!   // Use a static dictionary to track visited nodes
//!   let mut visited = MapWrapper(Dictionary::<usize,NodeState,37>::new());
//!   // Backing store for the returned slice
//!   let mut storage = [0_usize;16];
//!   let sorted = topological_sort(&graph, &mut visited,&mut storage);
//!   println!("Topologically sorted nodes: {:?}", sorted );
//!   assert_eq!(sorted.unwrap(),&[3,2,0,1,20])
//! ```
//!
//! The memory layout of the graphs is flexible: both edges and nodes can
//! be provided with and without associated values, edges can be pairs of
//! arrays or arrays of pairs, adding and removing is possible by storing
//! array elements as [`Option`], and/or using a backing store like
//! [`heapless::Vec`]
//!
//! The core abstraction is the [`Graph`] trait, which is automatically
//! for edge list and adjacency list representations.
//!
pub mod adjacency_list;
pub mod algorithms;
pub mod containers;
pub mod edge_list;
pub mod edges;
pub mod graph;
pub mod nodes;
pub mod visited;
pub use visited::{NodeState, VisitedTracker};

pub use graph::{Graph, GraphWithEdgeValues};
