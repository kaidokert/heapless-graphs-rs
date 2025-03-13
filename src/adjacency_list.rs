// SPDX-License-Identifier: Apache-2.0

//! Adjacency list graphs
//!
//! This module provides adjacency list graph structures that
//! implement the [`Graph`] trait.

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use crate::containers::maps::MapTrait;
use crate::graph::{
    Graph, GraphError, GraphWithEdgeValues, GraphWithMutableEdges, GraphWithNodeValues,
};
use crate::nodes::{AddNode, NodesIterable, NodesValuesIterable};

use core::iter::Map;

mod edgeiterator;
pub use edgeiterator::{EdgeIterator, EdgeValueIterator};

/// A list of outgoing edges from a node, in an adjacency list.
pub trait AsOutgoingNodes<NI, E>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>: DoubleEndedIterator<Item = &'a NI>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a;
}

/// [AsOutgoingNodes] that also allows creating new nodes
pub trait AsOutgoingNodesFromEdges<NI, E>: AsOutgoingNodes<NI, E>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    fn from_edges(edges: E) -> Self;
}

/// A list of outgoing edges along with values from a node in an
/// adjacency list.
pub trait AsOutgoingNodesWithValues<NI, E, V>: AsOutgoingNodes<NI, E>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
{
    type IterValues<'a>: DoubleEndedIterator<Item = (&'a NI, Option<&'a V>)>
    where
        NI: 'a,
        Self: 'a,
        V: 'a;
    fn as_outgoing_nodes_values<'a>(&'a self) -> Self::IterValues<'a>
    where
        NI: 'a;
    fn value(&self) -> Option<&V>;
}

/// [AsOutgoingNodesWithValues] that also allows creating new nodes
pub trait AsOutgoingNodesWithValuesFromEdges<NI, E, V>:
    AsOutgoingNodesWithValues<NI, E, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
{
    fn from_edges(edges: E) -> Self;
}

/// A list of outgoing edges from a node, in an adjacency list.
#[derive(Debug)]
pub struct EdgesOnly<E>(pub E);
/// A list of outgoing edges from a node, in an adjacency list, along with node values
pub struct EdgesWithNodeValues<E, V>(pub (V, E));

impl<E> Deref for EdgesOnly<E> {
    type Target = E;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E> DerefMut for EdgesOnly<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<E, NI> AsOutgoingNodes<NI, E> for E
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>
        = E::Iter<'a>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a,
    {
        self.iter_nodes()
    }
}
impl<E, NI> AsOutgoingNodesFromEdges<NI, E> for E
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    fn from_edges(edges: E) -> Self {
        edges
    }
}

impl<NI, E> AsOutgoingNodes<NI, E> for EdgesOnly<E>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>
        = E::Iter<'a>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a,
    {
        (**self).iter_nodes()
    }
}
impl<NI, E> AsOutgoingNodesFromEdges<NI, E> for EdgesOnly<E>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    fn from_edges(edges: E) -> Self {
        EdgesOnly(edges)
    }
}

impl<NI, E, V> AsOutgoingNodesWithValues<NI, E, V> for EdgesOnly<E>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
{
    type IterValues<'a>
        = <E as NodesValuesIterable<V>>::IterValues<'a>
    where
        NI: 'a,
        Self: 'a,
        V: 'a;
    fn as_outgoing_nodes_values<'a>(&'a self) -> Self::IterValues<'a>
    where
        NI: 'a,
    {
        self.0.iter_nodes_values()
    }
    fn value(&self) -> Option<&V> {
        None
    }
}

impl<E, V> Deref for EdgesWithNodeValues<E, V> {
    type Target = E;
    fn deref(&self) -> &Self::Target {
        &self.0 .1
    }
}
impl<E, V> DerefMut for EdgesWithNodeValues<E, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0 .1
    }
}

impl<E, NI, V> AsOutgoingNodes<NI, E> for (V, E)
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>
        = E::Iter<'a>
    where
        NI: 'a,
        Self: 'a;

    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a,
    {
        self.1.iter_nodes()
    }
}
impl<E, NI, V> AsOutgoingNodesFromEdges<NI, E> for (V, E)
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    V: Default,
{
    fn from_edges(edges: E) -> Self {
        (Default::default(), edges)
    }
}

impl<NI, E, V> AsOutgoingNodes<NI, E> for EdgesWithNodeValues<E, V>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
{
    type Iter<'a>
        = E::Iter<'a>
    where
        NI: 'a,
        Self: 'a;
    fn as_outgoing_nodes<'a>(&'a self) -> Self::Iter<'a>
    where
        NI: 'a,
    {
        (**self).as_outgoing_nodes()
    }
}
impl<NI, E, V> AsOutgoingNodesFromEdges<NI, E> for EdgesWithNodeValues<E, V>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    V: Default,
{
    fn from_edges(edges: E) -> Self {
        EdgesWithNodeValues((Default::default(), edges))
    }
}
impl<NI, E, V> AsOutgoingNodesWithValues<NI, E, V> for EdgesWithNodeValues<E, V>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
{
    type IterValues<'a>
        = <E as NodesValuesIterable<V>>::IterValues<'a>
    where
        NI: 'a,
        Self: 'a,
        V: 'a;
    fn as_outgoing_nodes_values<'a>(&'a self) -> Self::IterValues<'a>
    where
        NI: 'a,
    {
        self.0 .1.iter_nodes_values()
    }
    fn value(&self) -> Option<&V> {
        Some(&self.0 .0)
    }
}

/// Adjacency list graph based on a slice of tuples.
///
/// The slice is a tuple of a node index and a container of edges.
///
/// # Type Parameters
/// - `NI`: The type that represents the node indices in the graph. For core
///        functionality, it is only expected to implement [`PartialEq`]
/// - `E`: The type of the container or collection that stores the edges. Node
///        structures like [`NodeStruct`](crate::nodes::NodeStruct) can be used.
/// - `C`: Wrapper structure that holds outgoing edges with node values, either
///        [EdgesOnly] or [EdgesWithNodeValues]
/// - `T`: The type of the container or collection that stores the nodes and edges,
///        either an array, slice or vector types that can be viewed as slice.
pub struct SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    nodes_container: T,
    _phantom: PhantomData<(E, C)>,
}

impl<NI, E, C, T> SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
    Self: Graph<NI>,
{
    /// Create new adjacency list and check for integrity
    pub fn new(value: T) -> Result<Self, <Self as Graph<NI>>::Error> {
        let result = Self::new_unchecked(value);
        result.integrity_check()?;
        Ok(result)
    }

    /// Create new adjacency list, do not check consistency
    pub fn new_unchecked(value: T) -> Self {
        Self {
            nodes_container: value,
            _phantom: Default::default(),
        }
    }
}

impl<NI, E, C, T> Graph<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    T: AsRef<[(NI, C)]>,
{
    type Error = GraphError<NI>;
    type Edges<'a>
        = EdgeIterator<'a, NI, E, C, core::slice::Iter<'a, (NI, C)>, &'a (NI, C)>
    where
        Self: 'a;
    type Nodes<'a>
        = Map<core::slice::Iter<'a, (NI, C)>, fn(&(NI, C)) -> &NI>
    where
        Self: 'a;

    fn get_edges(&self) -> Result<Self::Edges<'_>, GraphError<NI>> {
        Ok(EdgeIterator::new(self.nodes_container.as_ref().iter()))
    }
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, GraphError<NI>> {
        Ok(self.nodes_container.as_ref().iter().map(|(n, _)| n))
    }
    /// Slow scan O(n)
    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, GraphError<NI>> {
        if let Some((_ni, node_data)) = self
            .nodes_container
            .as_ref()
            .iter()
            .find(|(n, _)| n == node)
        {
            Ok(node_data.as_outgoing_nodes())
        } else {
            Err(GraphError::NodeNotFound)
        }
    }
}

impl<NI, E, C, T, V> GraphWithEdgeValues<NI, V> for SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V>,
    T: AsRef<[(NI, C)]>,
{
    type EdgeValues<'a>
        = EdgeValueIterator<'a, NI, E, C, core::slice::Iter<'a, (NI, C)>, &'a (NI, C), V>
    where
        Self: 'a,
        V: 'a;
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'a>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(EdgeValueIterator::new(self.nodes_container.as_ref().iter()))
    }
}
impl<NI, E, C, T, V> GraphWithNodeValues<NI, V> for SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V>,
    T: AsRef<[(NI, C)]>,
{
    type NodeValues<'a>
        = Map<core::slice::Iter<'a, (NI, C)>, fn(&(NI, C)) -> (&NI, Option<&V>)>
    where
        Self: 'a,
        V: 'a;
    fn get_node_values<'a>(&'a self) -> Result<Self::NodeValues<'a>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self
            .nodes_container
            .as_ref()
            .iter()
            .map(|(n, c)| (n, c.value())))
    }

    fn get_node_value(&self, node: &NI) -> Result<Option<&V>, GraphError<NI>> {
        self.nodes_container
            .as_ref()
            .iter()
            .find(|(n, _)| n == node)
            .map(|(_, c)| c.value())
            .ok_or(GraphError::NodeNotFound)
    }
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a V>)>, GraphError<NI>>
    where
        NI: 'a,
        V: 'a,
    {
        self.neighboring_nodes(node)
            .map(move |iter| iter.map(move |n| (n, self.get_node_value(n).ok().flatten())))
    }
}

impl<NI, E, C, T> GraphWithMutableEdges<NI> for SliceAdjacencyList<NI, E, C, T>
where
    NI: PartialEq,
    E: NodesIterable<Node = NI> + AddNode<NI> + Default,
    C: AsOutgoingNodes<NI, E> + DerefMut<Target = E>,
    T: AsRef<[(NI, C)]> + AsMut<[(NI, C)]>,
{
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize> {
        let maybe = self
            .nodes_container
            .as_mut()
            .iter_mut()
            .find(|(n, _)| n == &src)
            .map(|(_, c)| c);
        if let Some(edges) = maybe {
            edges.deref_mut().add(dst)
        } else {
            todo!(
                "Can't add new nodes to slice adjacency list - yet, \
                 this could be implemented for Option<(NI, C)>"
            )
        }
    }

    fn remove_edge(&mut self, _src: NI, _dst: NI) -> Option<usize> {
        todo!()
    }
}

/// Adjacency list graph based on a map that implements [MapTrait].
///
/// The map keys are nodes and values are containers of edges.
///
/// # Type Parameters
/// - `NI`: The type that represents the node indices in the graph. For core
///        functionality, it is only expected to implement [`PartialEq`]
/// - `M`: The type of the map that stores the nodes and edges.
/// - `E`: The type of the container or collection that stores the edges. Node
///        structures like [`NodeStruct`](crate::nodes::NodeStruct) can be used.
/// - `C`: Wrapper structure that holds outgoing edges with node values, either
///        [EdgesOnly] or [EdgesWithNodeValues], or a [NodesIterable]
#[derive(Debug)]
pub struct MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
{
    nodes: M,
    _phantom: PhantomData<(E, C)>,
}

impl<M, NI, E, C> MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: PartialEq,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
    Self: Graph<NI>,
{
    /// Create new adjacency list and check for integrity
    pub fn new(value: M) -> Result<Self, <Self as Graph<NI>>::Error> {
        let res = Self::new_unchecked(value);
        res.integrity_check()?;
        Ok(res)
    }

    /// Create new adjacency list, do not check consistency
    pub fn new_unchecked(value: M) -> Self {
        Self {
            nodes: value,
            _phantom: Default::default(),
        }
    }
}

impl<M, E, NI, C> Graph<NI> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: Eq + core::hash::Hash,
    E: NodesIterable<Node = NI>,
    C: AsOutgoingNodes<NI, E>,
{
    type Error = GraphError<NI>;
    type Edges<'a>
        = EdgeIterator<'a, NI, E, C, M::Iter<'a>, (&'a NI, &'a C)>
    where
        Self: 'a;
    type Nodes<'a>
        = M::Keys<'a>
    where
        Self: 'a;

    fn contains_node(&self, node: &NI) -> Result<bool, GraphError<NI>> {
        Ok(self.nodes.contains_key(node))
    }
    /// Fast access O(1)
    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, GraphError<NI>> {
        if let Some(edges) = self.nodes.get(node) {
            Ok(edges.as_outgoing_nodes())
        } else {
            Err(GraphError::NodeNotFound)
        }
    }
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, GraphError<NI>> {
        Ok(self.nodes.keys())
    }
    fn get_edges(&self) -> Result<Self::Edges<'_>, GraphError<NI>> {
        Ok(EdgeIterator::new(self.nodes.iter()))
    }
}

impl<M, NI, E, C, V> GraphWithEdgeValues<NI, V> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: Eq + core::hash::Hash,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V>,
{
    type EdgeValues<'a>
        = EdgeValueIterator<'a, NI, E, C, M::Iter<'a>, (&'a NI, &'a C), V>
    where
        Self: 'a,
        V: 'a;
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'a>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(EdgeValueIterator::new(self.nodes.iter()))
    }
}

impl<M, NI, E, C, V> GraphWithNodeValues<NI, V> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: Eq + core::hash::Hash,
    E: NodesValuesIterable<V, Node = NI>,
    C: AsOutgoingNodesWithValues<NI, E, V>,
{
    type NodeValues<'a>
        = Map<M::Iter<'a>, fn((&'a NI, &'a C)) -> (&'a NI, Option<&'a V>)>
    where
        V: 'a,
        Self: 'a;
    fn get_node_values<'a>(&'a self) -> Result<Self::NodeValues<'a>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self.nodes.iter().map(|(n, c)| (n, c.value())))
    }

    fn get_node_value(&self, node: &NI) -> Result<Option<&V>, GraphError<NI>> {
        self.nodes
            .get(node)
            .map(|c| c.value())
            .ok_or(GraphError::NodeNotFound)
    }
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a V>)>, GraphError<NI>>
    where
        NI: 'a,
        V: 'a,
    {
        self.neighboring_nodes(node)
            .map(move |iter| iter.map(move |n| (n, self.get_node_value(n).ok().flatten())))
    }
}

impl<M, NI, E, C> GraphWithMutableEdges<NI> for MapAdjacencyList<M, NI, E, C>
where
    M: MapTrait<NI, C>,
    NI: Eq + core::hash::Hash,
    E: NodesIterable<Node = NI> + AddNode<NI> + Default,
    C: AsOutgoingNodesFromEdges<NI, E> + DerefMut<Target = E>,
{
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize> {
        if let Some(edges) = self.nodes.get_mut(&src) {
            edges.deref_mut().add(dst)
        } else {
            let mut new_edges = E::default();
            new_edges.add(dst)?;
            if self.nodes.insert(src, C::from_edges(new_edges)).is_none() {
                Some(1)
            } else {
                None
            }
        }
    }

    fn remove_edge(&mut self, _src: NI, _dst: NI) -> Option<usize> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::{EdgesOnly, EdgesWithNodeValues};
    use crate::containers::maps::staticdict::Dictionary;
    use crate::nodes::{NodeStruct, NodeStructOption, NodeValueStruct, NodeValueStructOption};
    use core::fmt::Debug;

    fn test_adjacency_list<'a, T, NI>(
        graph: &'a T,
        nodes: &[NI],
        edges: &[(NI, NI)],
    ) -> Result<(), GraphError<NI>>
    where
        T: Graph<NI>,
        NI: PartialEq + Default + Copy + core::fmt::Debug + 'a,
        GraphError<NI>: From<T::Error>,
    {
        let mut collect = [NI::default(); 32];
        let mut count = 0;
        for n in graph.get_nodes()?.zip(collect.iter_mut()) {
            *n.1 = *n.0;
            count += 1;
        }
        assert_eq!(&collect[..count], nodes);
        let mut coll2 = [(NI::default(), NI::default()); 32];
        let mut count = 0;
        for e in graph.get_edges()?.zip(coll2.iter_mut()) {
            *e.1 = (*e.0 .0, *e.0 .1);
            count += 1;
        }
        assert_eq!(&coll2[..count], edges);
        Ok(())
    }
    fn test_outgoing_edges<'a, T: Graph<NI>, NI>(
        graph: &'a T,
        node: NI,
        edges: &[NI],
    ) -> Result<(), GraphError<NI>>
    where
        NI: PartialEq + Default + Copy + core::fmt::Debug + 'a,
        GraphError<NI>: From<T::Error>,
    {
        let mut collect = [NI::default(); 10];
        graph
            .outgoing_edges_for_node(&node)?
            .zip(collect.iter_mut())
            .for_each(|(n, c)| {
                *c = *n;
            });
        assert_eq!(&collect[..edges.len()], edges);
        Ok(())
    }

    #[test]
    fn test_node_array_list() {
        let gen = SliceAdjacencyList::new_unchecked([
            (1, EdgesOnly(NodeStructOption([Some(1), None, Some(3)]))),
            (2, EdgesOnly(NodeStructOption([None, Some(2), None]))),
            (3, EdgesOnly(NodeStructOption([None, None, Some(3)]))),
        ]);
        let graph = &gen;
        test_adjacency_list(graph, &[1, 2, 3], &[(1, 1), (1, 3), (2, 2), (3, 3)]).unwrap();
        test_outgoing_edges(graph, 1, &[1, 3, 0]).unwrap();
        test_outgoing_edges(graph, 2, &[2, 0, 0]).unwrap();
        test_outgoing_edges(graph, 3, &[3, 0, 0]).unwrap();
    }

    #[test]
    fn test_node_array_list_unnested() {
        let gen = SliceAdjacencyList::new_unchecked([
            (1, NodeStructOption([Some(1), None, Some(3)])),
            (2, NodeStructOption([None, Some(2), None])),
            (3, NodeStructOption([None, None, Some(3)])),
        ]);
        let graph = &gen;
        test_adjacency_list(graph, &[1, 2, 3], &[(1, 1), (1, 3), (2, 2), (3, 3)]).unwrap();
        test_outgoing_edges(graph, 1, &[1, 3, 0]).unwrap();
        test_outgoing_edges(graph, 2, &[2, 0, 0]).unwrap();
        test_outgoing_edges(graph, 3, &[3, 0, 0]).unwrap();
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_vector_list() {
        let mut vec = heapless::Vec::<_, 3>::new();
        vec.extend([
            (1, EdgesWithNodeValues((Some('b'), NodeStruct([1, 2, 3])))),
            (2, EdgesWithNodeValues((Some('x'), NodeStruct([2, 2, 3])))),
            (3, EdgesWithNodeValues((Some('z'), NodeStruct([3, 3, 3])))),
        ]);
        let gen = SliceAdjacencyList::new_unchecked(vec);
        let graph = &gen;
        test_outgoing_edges(graph, 1, &[1, 2, 3]).unwrap();
        test_outgoing_edges(graph, 2, &[2, 2, 3]).unwrap();
        test_outgoing_edges(graph, 3, &[3, 3, 3]).unwrap();
    }

    #[test]
    fn test_dictionary() {
        let mut dict = Dictionary::<_, _, 8>::new();
        dict.insert(
            'a',
            EdgesOnly(NodeStructOption([Some('b'), Some('c'), None])),
        );
        dict.insert('b', EdgesOnly(NodeStructOption([None, None, Some('c')])));
        dict.insert('c', EdgesOnly(NodeStructOption([None, None, None])));
        let graph = MapAdjacencyList::new_unchecked(dict);
        test_adjacency_list(
            &graph,
            &['c', 'a', 'b'], // Order is not guaranteed with Dictionary
            &[('a', 'b'), ('a', 'c'), ('b', 'c')],
        )
        .expect("worked");
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_map_list() {
        let mut im0 = heapless::FnvIndexMap::<_, _, 8>::new();
        im0.insert(1, EdgesOnly(NodeStruct([1, 2, 3]))).ok();
        let mut im1 = heapless::FnvIndexMap::<_, _, 8>::new();
        im1.insert(2, ('c', NodeStruct([1, 2, 3]))).ok();
        let mut im2 = heapless::FnvIndexMap::<_, _, 8>::new();
        im2.insert(3, EdgesWithNodeValues((Some('c'), NodeStruct([1, 2, 3]))))
            .ok();
        let el0 = MapAdjacencyList::new_unchecked(im0);
        let el1 = MapAdjacencyList::new_unchecked(im1);
        let el2 = MapAdjacencyList::new_unchecked(im2);
        test_adjacency_list(&el0, &[1], &[(1, 1), (1, 2), (1, 3)]).expect("worked");
        test_adjacency_list(&el1, &[2], &[(2, 1), (2, 2), (2, 3)]).expect("worked");
        test_adjacency_list(&el2, &[3], &[(3, 1), (3, 2), (3, 3)]).expect("worked");
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_fnv() {
        let adjl = MapAdjacencyList::new_unchecked(heapless::FnvIndexMap::<_, _, 8>::from_iter(
            [
                (1, EdgesOnly(NodeStruct([1, 2, 3]))),
                (2, EdgesOnly(NodeStruct([1, 2, 3]))),
            ]
            .into_iter(),
        ));
        test_adjacency_list(
            &adjl,
            &[1, 2],
            &[(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)],
        )
        .expect("worked");
    }

    fn test_with_values<NI, V, G: GraphWithEdgeValues<NI, V>>(
        graph: &G,
        expect: &[(NI, NI, V)],
    ) -> Result<(), GraphError<NI>>
    where
        NI: PartialEq + Default + Copy + Debug,
        V: Default + Copy + PartialEq + core::fmt::Debug,
    {
        let mut collect = [(NI::default(), NI::default(), V::default()); 32];
        let mut len = 0;
        for (src, dst) in graph.get_edge_values()?.zip(collect.iter_mut()) {
            *dst = (*src.0, *src.1, *src.2.unwrap());
            len += 1;
        }
        assert_eq!(&collect[..len], expect);
        Ok(())
    }

    #[test]
    fn test_adjlist_values_0() {
        let graph = SliceAdjacencyList::new([
            ('a', EdgesOnly(NodeValueStruct([('b', 1), ('c', 4)]))),
            ('b', EdgesOnly(NodeValueStruct([('c', 2), ('c', 1)]))),
            ('c', EdgesOnly(NodeValueStruct([('c', 3), ('c', 4)]))),
        ])
        .unwrap();
        test_with_values(
            &graph,
            &[
                ('a', 'b', 1),
                ('a', 'c', 4),
                ('b', 'c', 2),
                ('b', 'c', 1),
                ('c', 'c', 3),
                ('c', 'c', 4),
            ],
        )
        .expect("worked");
    }
    #[test]
    fn test_adjlist_values_1() {
        let graph = SliceAdjacencyList::new_unchecked([
            (
                'a',
                EdgesOnly(NodeValueStructOption([
                    Some(('b', 1)),
                    None,
                    Some(('c', 4)),
                    None,
                ])),
            ),
            (
                'b',
                EdgesOnly(NodeValueStructOption([None, None, Some(('c', 2)), None])),
            ),
            (
                'c',
                EdgesOnly(NodeValueStructOption([None, None, None, None])),
            ),
        ]);
        test_with_values(&graph, &[('a', 'b', 1), ('a', 'c', 4), ('b', 'c', 2)]).expect("worked");
    }

    fn add_test<NI, G: GraphWithMutableEdges<NI>>(
        graph: &mut G,
        ok: bool,
        edge: (NI, NI),
        expect_nodes: &[NI],
        expect_edges: &[(NI, NI)],
    ) where
        NI: PartialEq + Default + Debug + Copy,
        GraphError<NI>: From<G::Error>,
    {
        let res = graph.add_edge(edge.0, edge.1);
        assert_eq!(res.is_some(), ok);
        test_adjacency_list(graph, expect_nodes, expect_edges).expect("okay");
    }
    fn outer_add_test<G: GraphWithMutableEdges<char>>(graph: &mut G, try_adding_new_nodes: bool)
    where
        GraphError<char>: From<G::Error>,
    {
        // Check it's as expected
        test_adjacency_list(
            graph,
            &['a', 'b'], // Order is not guaranteed with Dictionary
            &[('a', 'a'), ('a', 'b')],
        )
        .expect("okay");
        // Add b-a backwards edge
        add_test(
            graph,
            true,
            ('b', 'a'),
            &['a', 'b'],
            &[('a', 'a'), ('a', 'b'), ('b', 'a')],
        );
        if !try_adding_new_nodes {
            return;
        }
        // Add c-a edge, inserting a new node
        add_test(
            graph,
            true,
            ('c', 'a'),
            &['c', 'a', 'b'],
            &[('c', 'a'), ('a', 'a'), ('a', 'b'), ('b', 'a')],
        );
        // Add a-c edge, taking up the last outgoing slot from A
        add_test(
            graph,
            true,
            ('a', 'c'),
            &['c', 'a', 'b'],
            &[('c', 'a'), ('a', 'a'), ('a', 'b'), ('a', 'c'), ('b', 'a')],
        );
        // Try to add one more edge to a, should fail, we are out of slots
        add_test(
            graph,
            false,
            ('a', 'f'),
            &['c', 'a', 'b'],
            &[('c', 'a'), ('a', 'a'), ('a', 'b'), ('a', 'c'), ('b', 'a')],
        );
    }

    #[test]
    fn test_add_edges_with_map() {
        // Set up dict with two nodes, one edge
        let mut dict = Dictionary::<_, _, 8>::new();
        dict.insert(
            'a',
            EdgesOnly(NodeStructOption([Some('a'), Some('b'), None])),
        );
        dict.insert('b', EdgesOnly(NodeStructOption([None, None, None])));
        let mut graph = MapAdjacencyList::new(dict).unwrap();
        outer_add_test(&mut graph, true);
    }
    #[test]
    fn test_add_edges_with_list() {
        let mut graph = SliceAdjacencyList::new([
            (
                'a',
                EdgesOnly(NodeStructOption([Some('a'), Some('b'), None])),
            ),
            ('b', EdgesOnly(NodeStructOption([None, None, None]))),
        ])
        .unwrap();
        outer_add_test(&mut graph, false);
    }
}
