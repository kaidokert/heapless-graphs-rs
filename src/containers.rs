// SPDX-License-Identifier: Apache-2.0

//! Provides limited traits to abstract container types
//!
//! Provides subset abstractions for containers that are used
//! in graph traversal algorithms.
//!
//! Note: None of those are required in the graph implementations,
//! only in the algorithms.

mod djb2hash;
pub mod maps;
pub mod queues;
pub mod sets;
