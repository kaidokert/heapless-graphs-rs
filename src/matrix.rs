// SPDX-License-Identifier: Apache-2.0

//! Adjacency matrix graphs
//!
//! This module provides adjacency matrix graph structures that
//! implement the [`GraphRef`] and [`GraphVal`] traits.
//!
//! [`GraphRef`]: crate::graph::GraphRef
//! [`GraphVal`]: crate::graph::GraphVal

pub mod bit_map_matrix;
pub mod bit_matrix;
pub mod map_matrix;
pub mod simple_matrix;
