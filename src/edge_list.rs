// SPDX-License-Identifier: Apache-2.0

//! Edge list graphs
//!
//! This module provides edge list graph structures that
//! implement the [`Graph`] trait.

use crate::nodes::{AddNode, NodeRef, NodesIterable, NodesValuesIterable, RemoveNode};

use crate::edges::{AddEdge, EdgeRef, EdgeValuesIterable, EdgesIterable, EdgesToNodesIterator};
use crate::graph::{
    Graph, GraphError, GraphWithEdgeValues, GraphWithMutableEdges, GraphWithMutableNodes,
    GraphWithNodeValues,
};

/// Edge list graph that stores only edges
///
/// This struct represents a graph using an edge list. It is optimized for
/// compact edge representation, but iterating over nodes may be expensive.
/// Edges can also have values.
///
/// See [EdgesToNodesIterator] for the expensive node iteration used.
///
/// # Type Parameters
///
/// - `N`: The max number of nodes in the graph. This is a constant size parameter
///        that represents the total capacity for nodes. The storage is only allocated
///        on stack temporarily when nodes are iterated over.
/// - `E`: The type of the container or collection that stores the edges. It is expected to
///        implement the [`EdgesIterable`] trait, which defines the behavior for
///        iterating over edges.
/// - `NI`: The type that represents the node indices in the graph. This could be
///         a simple integer type like `usize` or a more complex index type.
///
/// Example usage:
/// ```
///   # use heapless_graphs::{Graph,edge_list::EdgeList,edges::EdgeStruct};
///   const MAX_NODES: usize = 10;
///   let graph = EdgeList::<MAX_NODES,_,_>::new(
///     EdgeStruct([('a', 'b'), ('b', 'x')])
///   ).unwrap();
///   assert_eq!(graph.contains_node(&'x'), Ok(true));
/// ```
pub struct EdgeList<const N: usize, E, NI> {
    edges: E,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, E, NI> EdgeList<N, E, NI>
where
    NI: PartialEq,
{
    pub fn new(edges: E) -> Result<Self, GraphError<NI>> {
        let res = Self {
            edges,
            _phantom: Default::default(),
        };
        Ok(res)
    }
}

/// Implementation borrows data for nodes
impl<const N: usize, E, NI> Graph<NI> for EdgeList<N, E, NI>
where
    E: EdgesIterable<Node = NI>,
    NI: PartialEq + Ord,
{
    type Error = GraphError<NI>;
    type Edges<'b>
        = E::Iter<'b>
    where
        Self: 'b;
    // Note: N here limits the capacity of yielded nodes
    type Nodes<'b>
        = EdgesToNodesIterator<'b, N, NI>
    where
        Self: 'b;
    fn get_edges(&self) -> Result<Self::Edges<'_>, GraphError<NI>> {
        Ok(self.edges.iter_edges())
    }
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, GraphError<NI>> {
        Ok(EdgesToNodesIterator::new(&self.edges)?)
    }
}

/// Edge list graph that stores both edges and nodes.
///
/// This struct represents a graph that stores both edges and nodes explicitly.
/// It requires more memory than a graph that only stores edges like [EdgeList],
/// but iterating over nodes is much more efficient. Additionally, it allows
/// storing values associated with each node.
///
/// # Type Parameters
///
/// - `E`: The type of the container or collection that stores the edges. It is
///        expected to implement the [EdgesIterable] trait, which defines the
///        behavior for iterating over edges.
/// - `N`: The type of the container or collection that stores the nodes. It is
///        expected to implement the [NodesIterable] trait, which defines the
///        behavior for iterating over nodes.
/// - `NI`: The type that represents the node indices in the graph. This could be
///         a simple type like `usize` or a more complex index type. It is expected
///         to implement [`PartialEq`] to allow node comparison.
///
/// Example usage:
/// ```
///  # use heapless_graphs::{Graph,edge_list::EdgeNodeList,edges::EdgeStruct,nodes::NodeStruct};
///  let graph = EdgeNodeList::new(
///     EdgeStruct([(1, 3), (3, 1)]),
///     NodeStruct([1, 2, 3])
///  ).unwrap();
///  assert_eq!(graph.contains_node(&2), Ok(true));
/// ```
pub struct EdgeNodeList<E, N, NI> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
}

impl<E, N, NI> EdgeNodeList<E, N, NI>
where
    Self: Graph<NI>,
    NI: PartialEq,
{
    /// Creates a new EdgeNodeList instance and checks
    /// for invalid node references.
    pub fn new(edges: E, nodes: N) -> Result<Self, <Self as Graph<NI>>::Error> {
        let res = Self {
            edges,
            nodes,
            _phantom: core::marker::PhantomData,
        };
        res.integrity_check()?;
        Ok(res)
    }
}

impl<E, N, NI> Graph<NI> for EdgeNodeList<E, N, NI>
where
    E: EdgesIterable<Node = NI>,
    N: NodesIterable<Node = NI>,
    NI: PartialEq,
{
    type Error = GraphError<NI>;
    type Edges<'b>
        = E::Iter<'b>
    where
        Self: 'b;
    type Nodes<'b>
        = N::Iter<'b>
    where
        Self: 'b;

    fn get_edges(&self) -> Result<Self::Edges<'_>, GraphError<NI>> {
        Ok(self.edges.iter_edges())
    }
    fn get_nodes(&self) -> Result<Self::Nodes<'_>, GraphError<NI>> {
        Ok(self.nodes.iter_nodes())
    }
}

impl<E, N, NI: PartialEq> GraphWithMutableNodes<NI> for EdgeNodeList<E, N, NI>
where
    Self: Graph<NI>,
    N: AddNode<NI> + RemoveNode<NI>,
{
    fn add_node_unchecked(&mut self, n: NI) -> Option<usize> {
        self.nodes.add(n)
    }
    fn remove_node_unchecked(&mut self, n: NI) -> Option<usize> {
        self.nodes.remove(n)
    }
}

/// Implementation for graphs that store node values
impl<E, N, NI, V> GraphWithNodeValues<NI, V> for EdgeNodeList<E, N, NI>
where
    NI: PartialEq,
    Self: Graph<NI>,
    N: NodesValuesIterable<V, Node = NI>,
{
    type NodeValues<'a>
        = N::IterValues<'a>
    where
        Self: 'a,
        V: 'a;

    fn get_node_value(&self, n: &NI) -> Result<Option<&V>, GraphError<NI>> {
        self.get_node_values()?
            .find(|(node, _)| *node == n)
            .map(|(_, v)| v)
            .ok_or(GraphError::NodeNotFound)
    }

    fn get_node_values<'a>(&'a self) -> Result<Self::NodeValues<'_>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self.nodes.iter_nodes_values())
    }
    fn neighboring_nodes_with_values<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = (&'a NI, Option<&'a V>)>, Self::Error>
    where
        NI: 'a,
        V: 'a,
    {
        Ok(self
            .get_edges()?
            .filter(move |(src, dst)| *src == node || *dst == node)
            .map(move |(src, dst)| {
                if src == node {
                    (dst, self.get_node_value(dst).ok().unwrap())
                } else {
                    (src, self.get_node_value(src).ok().unwrap())
                }
            }))
    }
}

impl<const N: usize, E, NI, V> GraphWithEdgeValues<NI, V> for EdgeList<N, E, NI>
where
    NI: PartialEq,
    Self: Graph<NI>,
    E: EdgeValuesIterable<V, Node = NI>,
{
    type EdgeValues<'a>
        = E::IterValues<'a>
    where
        Self: 'a,
        V: 'a;
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'_>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self.edges.iter_edges_values())
    }
}

impl<E, N, NI, V> GraphWithEdgeValues<NI, V> for EdgeNodeList<E, N, NI>
where
    NI: PartialEq,
    Self: Graph<NI>,
    E: EdgeValuesIterable<V, Node = NI>,
{
    type EdgeValues<'a>
        = <E as EdgeValuesIterable<V>>::IterValues<'a>
    where
        Self: 'a,
        V: 'a;
    fn get_edge_values<'a>(&'a self) -> Result<Self::EdgeValues<'_>, GraphError<NI>>
    where
        V: 'a,
    {
        Ok(self.edges.iter_edges_values())
    }
}

impl<E, N, NI> GraphWithMutableEdges<NI> for EdgeNodeList<E, N, NI>
where
    NI: PartialEq,
    Self: Graph<NI>,
    E: AddEdge<Edge = (NI, NI)>,
{
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize> {
        self.edges.add_edge((src, dst))
    }
    fn remove_edge(&mut self, _src: NI, _dst: NI) -> Option<usize> {
        todo!()
    }
}

impl<const N: usize, E, NI> GraphWithMutableEdges<NI> for EdgeList<N, E, NI>
where
    NI: PartialEq,
    Self: Graph<NI>,
    E: AddEdge<Edge = (NI, NI)>,
{
    fn add_edge(&mut self, src: NI, dst: NI) -> Option<usize> {
        self.edges.add_edge((src, dst))
    }
    fn remove_edge(&mut self, _src: NI, _dst: NI) -> Option<usize> {
        todo!()
    }
}

impl<const NSZ: usize, N, NI, E> TryFrom<EdgeList<NSZ, E, NI>> for EdgeNodeList<E, N, NI>
where
    NI: PartialEq,
    E: EdgeRef<NodeIndex = NI>,
    N: NodeRef<NodeIndex = NI> + Default,
{
    type Error = GraphError<NI>;

    fn try_from(_value: EdgeList<NSZ, E, NI>) -> Result<Self, Self::Error> {
        todo!("Implement TryFrom for EdgeList to EdgeNodeList");
        /*
        Self::new(
            value.edges,
            // Todo: Maybe can do without a default with a ::from_nodes( ) call
        N::default()
        )
         */
    }
}

impl<const NSZ: usize, N, NI, E> TryFrom<EdgeNodeList<E, N, NI>> for EdgeList<NSZ, E, NI>
where
    NI: PartialEq,
    E: EdgeRef<NodeIndex = NI>,
    N: NodeRef<NodeIndex = NI>,
{
    type Error = GraphError<NI>;

    fn try_from(value: EdgeNodeList<E, N, NI>) -> Result<Self, Self::Error> {
        Self::new(value.edges)
    }
}

#[cfg(test)]
mod tests {
    use crate::edges::{EdgeStruct, EdgeStructOption, TwoArrayEdgeValueStruct};
    use crate::nodes::{NodeStruct, NodeStructOption};
    use core::fmt::Debug;

    use super::*;

    fn test_edge_list_graph<'a, E, NI>(elg: &'a E, check: &[&NI])
    where
        E: Graph<NI>,
        NI: PartialEq + Default + Debug + 'a,
        E::Error: Debug,
    {
        let default = NI::default();
        let mut collect: [&NI; 256] = core::array::from_fn(|_| &default);
        let node_iter = elg.get_nodes().expect("iterator");
        for (node, slot) in node_iter.zip(collect.iter_mut()) {
            *slot = node;
        }
        let final_slice = &collect[..check.len()];
        assert_eq!(final_slice, check);
    }

    #[test]
    fn test_edge_list_with_array_nodes() {
        let nodes = [1, 2, 3];
        let valid_edges = [(1, 3), (3, 1)];
        let ewn = EdgeNodeList::new(valid_edges, nodes).unwrap();
        ewn.integrity_check().unwrap();
        test_edge_list_graph(&ewn, &[&1, &2, &3]);
        ewn.integrity_check().unwrap();
    }

    #[test]
    fn test_edge_list_with_slice_nodes() {
        let nodes = [1, 2, 3].as_slice();
        let valid_edges = [(1, 3), (3, 1)].as_slice();
        let ewn = EdgeNodeList::new(valid_edges, nodes).unwrap();
        ewn.integrity_check().unwrap();
        test_edge_list_graph(&ewn, &[&1, &2, &3]);
        ewn.integrity_check().unwrap();
    }

    #[test]
    fn test_edges_with_nodes() {
        let nodes = NodeStruct([1, 2, 3]);
        let valid_edges = EdgeStruct([(1, 3), (3, 1)]);
        let ewn = EdgeNodeList::new(valid_edges, nodes).unwrap();
        ewn.integrity_check().unwrap();
        test_edge_list_graph(&ewn, &[&1, &2, &3]);
        ewn.integrity_check().unwrap();
    }
    #[test]
    fn test_edges_with_nodes_broken() {
        let nodes = NodeStruct([1, 2, 3]);
        let valid_edges = EdgeStruct([(1, 3), (3, 1)]);
        let ewn = EdgeNodeList::new(valid_edges, nodes).unwrap();
        assert_eq!(ewn.integrity_check().is_ok(), true);
        let invalid_edges = EdgeStruct([(1, 3), (300, 1)]);
        let other_nodes = NodeStruct([1, 2, 3]);
        let broken_ewn = EdgeNodeList::new(invalid_edges, other_nodes);
        assert_eq!(broken_ewn.is_err(), true);
    }
    #[test]
    fn test_edges_only() {
        let eo = EdgeList::<3, _, _>::new(EdgeStruct([(1usize, 3), (3, 1)])).unwrap();
        test_edge_list_graph(&eo, &[&1, &3]);
        let _ = &eo.integrity_check().unwrap();
    }
    #[test]
    fn test_edges_with_insufficient_capacity() {
        let graph = EdgeList::<1, _, _>::new(EdgeStruct([(1usize, 3), (3, 1)])).unwrap();
        assert!(graph.get_nodes().is_err());
        let graph = EdgeList::<2, _, _>::new(EdgeStruct([(1usize, 3), (3, 1)])).unwrap();
        assert!(graph.get_nodes().is_ok());
    }
    #[test]
    fn test_edges_with_values() {
        let edge_struct =
            TwoArrayEdgeValueStruct([1u32, 3, 8], [8, 1, 2], [None, Some('a'), Some('x')]);
        let eo = EdgeList::<5, _, _>::new(edge_struct).unwrap();
        test_edge_list_graph(&eo, &[&1, &2, &3, &8, &0]);
        let lambda = || -> Result<(), GraphError<u32>> {
            let _ = &eo.outgoing_edges_for_node(&1)?.for_each(|x| {
                assert_eq!(x, &8);
            });
            Ok(())
        };
        assert!(lambda().is_ok());
    }

    fn test_mutable_nodes<E, NI>(elg: &mut E, add: NI, remove: NI, check: &[&NI])
    where
        E: GraphWithMutableNodes<NI>,
        NI: PartialEq + Default + Debug,
        E::Error: Debug,
    {
        elg.add_node_unchecked(add);
        elg.remove_node_unchecked(remove);
        test_edge_list_graph(elg, check);
    }

    #[test]
    fn test_mutable() {
        let nodes = NodeStructOption([Some(1_u8), Some(2), Some(3), None]);
        let valid_edges = EdgeStruct([(1, 3), (3, 1)]);
        let mut ewn = EdgeNodeList::new(valid_edges, nodes).unwrap();
        test_edge_list_graph(&ewn, &[&1_u8, &2, &3]);
        test_mutable_nodes(&mut ewn, 4_u8, 2, &[&1_u8, &3, &4]);
    }

    #[test]
    fn test_add_edges() {
        fn test<NI, G: GraphWithMutableEdges<NI>>(
            graph: &mut G,
            ok: bool,
            edge: (NI, NI),
            expect_nodes: &[&NI],
        ) where
            NI: PartialEq + Default + Debug,
            GraphError<NI>: From<G::Error>,
            G::Error: Debug,
        {
            let res = graph.add_edge(edge.0, edge.1);
            assert_eq!(res.is_some(), ok);
            test_edge_list_graph(graph, expect_nodes);
        }
        let mut graph =
            EdgeList::<2, _, _>::new(EdgeStructOption([Some((1usize, 3)), None])).unwrap();
        test_edge_list_graph(&graph, &[&1, &3]);
        test(&mut graph, true, (3, 7), &[&1, &3, &7]);
        test(&mut graph, false, (1, 2), &[&1, &3, &7]);
        let mut graph = EdgeList::<2, _, _>::new([Some((1usize, 3)), None]).unwrap();
        test_edge_list_graph(&graph, &[&1, &3]);
        test(&mut graph, true, (3, 7), &[&1, &3, &7]);
        test(&mut graph, false, (1, 2), &[&1, &3, &7]);
        let mut mut_arr = [Some((1usize, 3)), None];
        let mut graph = EdgeList::<2, _, _>::new(mut_arr.as_mut_slice()).unwrap();
        test_edge_list_graph(&graph, &[&1, &3]);
        test(&mut graph, true, (3, 7), &[&1, &3, &7]);
        test(&mut graph, false, (1, 2), &[&1, &3, &7]);
    }
}
