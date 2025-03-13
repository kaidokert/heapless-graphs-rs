#![feature(type_alias_impl_trait)]
#![feature(impl_trait_in_assoc_type)]
// #![cfg_attr(not(feature = "std"), no_std)]
// SPDX-License-Identifier: Apache-2.0

//! `static` friendly graph structures that do not require dynamic memory allocation.
//!
//! This crate provides composable building blocks for graph structures, all with
//! statically sized memory allocation.
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
pub mod edgelist;
pub mod edges;
pub mod graph;
pub mod matrix;
pub mod nodes;
pub mod visited;
