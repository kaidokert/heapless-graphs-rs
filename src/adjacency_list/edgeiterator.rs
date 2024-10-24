// SPDX-License-Identifier: Apache-2.0

use core::marker::PhantomData;

use super::{AsOutgoingNodes, AsOutgoingNodesWithValues};
use crate::nodes::{NodesIterable, NodesValuesIterable};

/// Trait to convert iterator items into `(&'a NI, &'a C)`
pub trait IntoEdge<'a, NI, C> {
    fn into_edge(self) -> (&'a NI, &'a C);
}

// Implement `IntoEdge` for iterators yielding `(&'a NI, &'a C)`
impl<'a, NI, C> IntoEdge<'a, NI, C> for (&'a NI, &'a C) {
    fn into_edge(self) -> (&'a NI, &'a C) {
        self
    }
}

// Implement `IntoEdge` for iterators yielding `&(NI, C)`
impl<'a, NI, C> IntoEdge<'a, NI, C> for &'a (NI, C) {
    fn into_edge(self) -> (&'a NI, &'a C) {
        (&self.0, &self.1)
    }
}

/// Iterator that that yields all edges from adjaceny list nodes
pub struct EdgeIterator<'a, NI, E, C, I, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E> + 'a,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
{
    nodes: I,
    current_node: Option<&'a NI>,
    outgoing: Option<C::Iter<'a>>,
    _marker: PhantomData<(NI, E, C)>,
}

impl<'a, NI, E, C, I, T> EdgeIterator<'a, NI, E, C, I, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
{
    /// Creates a new `EdgeIterator` from the given iterator
    pub fn new(iter: I) -> Self {
        Self {
            nodes: iter,
            current_node: None,
            outgoing: None,
            _marker: PhantomData,
        }
    }
}

impl<'a, NI, E, C, I, T> Iterator for EdgeIterator<'a, NI, E, C, I, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
{
    type Item = (&'a NI, &'a NI);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If there are outgoing nodes to process, yield the next one
            if let Some(ref mut outgoing) = self.outgoing {
                if let Some(out_node) = outgoing.next() {
                    if let Some(current) = self.current_node {
                        return Some((current, out_node));
                    }
                }
            }

            // Move to the next node in the iterator
            match self.nodes.next() {
                Some(item) => {
                    let (n, c) = item.into_edge();
                    self.current_node = Some(n);
                    self.outgoing = Some(c.as_outgoing_nodes());
                }
                None => return None, // No more nodes to process
            }
        }
    }
}

impl<'a, NI, E, C, I, T> DoubleEndedIterator for EdgeIterator<'a, NI, E, C, I, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!("This is not quite possible if underlying iterator isn't DE as well")
    }
}

pub struct EdgeValueIterator<'a, NI, E, C, I, T, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V> + 'a,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
    V: 'a,
{
    nodes: I,
    current_node: Option<&'a NI>,
    outgoing: Option<C::IterValues<'a>>,
    _marker: PhantomData<(NI, E, C, V)>,
}

impl<'a, NI, E, C, I, T, V> EdgeValueIterator<'a, NI, E, C, I, T, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V> + 'a,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
    V: 'a,
{
    pub fn new(iter: I) -> Self {
        Self {
            nodes: iter,
            current_node: None,
            outgoing: None,
            _marker: PhantomData,
        }
    }
}

impl<'a, NI, E, C, I, T, V> Iterator for EdgeValueIterator<'a, NI, E, C, I, T, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V> + 'a,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
    V: 'a,
{
    type Item = (&'a NI, &'a NI, Option<&'a V>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut outgoing) = self.outgoing {
                if let Some(out_node) = outgoing.next() {
                    if let Some(current) = self.current_node {
                        return Some((current, out_node.0, out_node.1));
                    }
                }
            }
            match self.nodes.next() {
                Some(item) => {
                    let (n, c) = item.into_edge();
                    self.current_node = Some(n);
                    self.outgoing = Some(c.as_outgoing_nodes_values());
                }
                None => return None,
            }
        }
    }
}

impl<'a, NI, E, C, I, T, V> DoubleEndedIterator for EdgeValueIterator<'a, NI, E, C, I, T, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V> + 'a,
    I: Iterator<Item = T>,
    T: IntoEdge<'a, NI, C>,
    V: 'a,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!("This is not quite possible if underlying iterator isn't DE as well")
    }
}
