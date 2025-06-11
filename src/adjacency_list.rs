// SPDX-License-Identifier: Apache-2.0

//! Adjacency list graphs
//!
//! This module provides adjacency list graph structures that
//! implement the [`GraphVal`] trait.
//!
//! [`GraphVal`]: crate::graph::GraphVal

pub mod map_adjacency_list;
pub mod outgoing_nodes;
pub mod slice_adjacency_list;
