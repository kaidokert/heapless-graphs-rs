// SPDX-License-Identifier: Apache-2.0

// Todo: remove this
#![allow(unused)]

use crate::edges::EdgesIterable;
use crate::graph::NodeIndex;
use crate::{containers::maps::MapTrait, graph::GraphError, Graph};
use core::ops::Range;
use core::{marker::PhantomData, option::Iter, slice::SliceIndex};

use itertools::{merge, Itertools};

use crate::nodes::{IntoNodesIterator, NodesIterable};

enum ProtoGraphError<NI: NodeIndex> {
    /// Edge is referring to a node not present in graph
    EdgeHasInvalidNode,
    /// Given node wasn't found in the graph
    NodeNotFound,
    EdgeNotFound,
    Unusused(NI),
}

trait ProtoGraph {
    type MyNodeIndex: NodeIndex;
    type Error: From<GraphError<Self::MyNodeIndex>>;
    fn get_nodes(&self) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error>;
    fn get_edges(
        &self,
    ) -> Result<impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)>, Self::Error>;
    fn contains_node(&self, node: Self::MyNodeIndex) -> Result<bool, Self::Error>;
    fn contains_edge(
        &self,
        edge: (Self::MyNodeIndex, Self::MyNodeIndex),
    ) -> Result<bool, Self::Error>;
    fn outgoing_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error>;
    fn incoming_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error>;
    fn neighboring_nodes(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error>;
}

pub struct PenMatrix<const N: usize, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    phantom: PhantomData<(EDGEVALUE, ROW)>,
    matrix: COLUMNS,
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> ProtoGraph for PenMatrix<N, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    type MyNodeIndex = usize;
    type Error = GraphError<Self::MyNodeIndex>;
    fn get_nodes(&self) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(0..N)
    }
    fn get_edges(
        &self,
    ) -> Result<impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)>, Self::Error> {
        Ok(self
            .matrix
            .as_ref()
            .iter()
            .enumerate()
            .flat_map(|(row_index, row)| {
                row.as_ref()
                    .iter()
                    .enumerate()
                    .filter_map(move |(column_index, edge)| {
                        edge.as_ref().map(|_| (row_index, column_index))
                    })
            }))
    }
    fn contains_node(&self, node: Self::MyNodeIndex) -> Result<bool, Self::Error> {
        Ok(node < N)
    }
    fn contains_edge(
        &self,
        edge: (Self::MyNodeIndex, Self::MyNodeIndex),
    ) -> Result<bool, Self::Error> {
        Ok(self
            .matrix
            .as_ref()
            .get(edge.0)
            .and_then(|row| row.as_ref().get(edge.1))
            .ok_or(GraphError::NodeNotFound)?
            .is_some())
    }
    fn outgoing_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self
            .matrix
            .as_ref()
            .get(node)
            .ok_or(GraphError::NodeNotFound)?
            .as_ref()
            .iter()
            .enumerate()
            .filter_map(|(index, edge)| edge.as_ref().map(|_| index)))
    }
    fn incoming_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self
            .matrix
            .as_ref()
            .iter()
            .enumerate()
            .filter_map(move |(index, row)| row.as_ref().get(node)?.as_ref().map(|_| index)))
    }
    fn neighboring_nodes(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(merge(self.incoming_edges(node)?, self.outgoing_edges(node)?).dedup())
    }
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> PenMatrix<N, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    pub fn new(matrix: COLUMNS) -> Self {
        Self {
            phantom: Default::default(),
            matrix,
        }
    }
}

pub struct EdgeNodeList<E, N, NI> {
    edges: E,
    nodes: N,
    _phantom: core::marker::PhantomData<NI>,
}

impl<E, N, NI> ProtoGraph for EdgeNodeList<E, N, NI>
where
    NI: NodeIndex + Clone + Copy,
    N: NodesIterable<Node = NI>,
    N: IntoNodesIterator<Node = NI>,
    E: EdgesIterable<Node = NI>,
{
    type MyNodeIndex = NI;
    type Error = GraphError<Self::MyNodeIndex>;

    fn get_nodes(&self) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self.nodes.iter_nodes().copied())
    }

    fn get_edges(
        &self,
    ) -> Result<impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)>, Self::Error> {
        Ok(self.edges.iter_edges().map(|(a, b)| (*a, *b)))
    }

    fn contains_node(&self, node: Self::MyNodeIndex) -> Result<bool, Self::Error> {
        Ok(self.nodes.iter_nodes().any(|n| *n == node))
    }
    fn contains_edge(
        &self,
        edge: (Self::MyNodeIndex, Self::MyNodeIndex),
    ) -> Result<bool, Self::Error> {
        Ok(self
            .edges
            .iter_edges()
            .any(|(a, b)| *a == edge.0 && *b == edge.1))
    }
    fn outgoing_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self
            .edges
            .iter_edges()
            .filter_map(move |(a, b)| if *a == node { Some(*b) } else { None }))
    }

    fn incoming_edges(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self
            .edges
            .iter_edges()
            .filter_map(move |(a, b)| if *b == node { Some(*a) } else { None }))
    }
    fn neighboring_nodes(
        &self,
        node: Self::MyNodeIndex,
    ) -> Result<impl Iterator<Item = Self::MyNodeIndex>, Self::Error> {
        Ok(self.edges.iter_edges().filter_map(move |(a, b)| {
            if *a == node {
                Some(*b)
            } else if *b == node {
                Some(*a)
            } else {
                None
            }
        }))
    }
}

#[cfg(test)]
mod shared {
    pub(crate) fn collect_to_mut_slice<T>(
        iter: impl Iterator<Item = T>,
        collect: &mut [T],
    ) -> &[T] {
        let mut len = 0;
        for item in iter {
            collect[len] = item;
            len += 1;
        }
        &collect[..len]
    }
}

#[cfg(test)]
mod tests {
    //use std;
    use super::shared::collect_to_mut_slice;
    use super::ProtoGraph;

    #[test]
    fn make_matrix() {
        let matrix = [[Some(false); 3]; 3];
        let _pen_matrix = super::PenMatrix::<8, _, _, _>::new(matrix);
    }

    fn make_test_matrix() -> [[Option<bool>; 3]; 3] {
        let row0 = [Some(false), Some(false), None];
        let row1 = [Some(false), Some(false), Some(false)];
        let row2 = [Some(false), None, Some(false)];
        [row0, row1, row2]
    }

    #[test]
    fn test_edges() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [(0usize, 0usize); 16];
        let collected_slice = collect_to_mut_slice(pen_matrix.get_edges().unwrap(), &mut collect);
        assert_eq!(
            collected_slice,
            &[(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 2)]
        );
    }

    #[test]
    fn test_outgoing_edges() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [0usize; 16];
        assert_eq!(
            &[0, 1],
            collect_to_mut_slice(pen_matrix.outgoing_edges(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.outgoing_edges(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 2],
            collect_to_mut_slice(pen_matrix.outgoing_edges(2).unwrap(), &mut collect)
        );
    }

    #[test]
    fn test_incoming_edges() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [0usize; 16];
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.incoming_edges(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 1],
            collect_to_mut_slice(pen_matrix.incoming_edges(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[1, 2],
            collect_to_mut_slice(pen_matrix.incoming_edges(2).unwrap(), &mut collect)
        );
    }
    #[test]
    fn test_neighboring_nodes() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [0usize; 16];
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(2).unwrap(), &mut collect)
        );
    }
}

#[cfg(test)]
mod tests2 {
    use super::shared::collect_to_mut_slice;
    use super::*;

    fn make_test_edgenode() -> EdgeNodeList<[(u8, u8); 3], [(u8); 3], u8> {
        EdgeNodeList {
            edges: [(0u8, 1), (1, 2), (2, 0)],
            nodes: [0u8, 1, 2],
            _phantom: Default::default(),
        }
    }

    #[test]
    fn make_edgenode() {
        let edgenode = make_test_edgenode();
        let mut collect = [0u8; 16];
        assert_eq!(
            [0, 1, 2],
            collect_to_mut_slice(edgenode.get_nodes().unwrap(), &mut collect)
        );
    }
    #[test]
    fn get_edges_edgenode() {
        let edgenode = make_test_edgenode();
        let mut collect = [(0u8, 0u8); 16];
        assert_eq!(
            [(0, 1), (1, 2), (2, 0)],
            collect_to_mut_slice(edgenode.get_edges().unwrap(), &mut collect)
        );
    }

    #[test]
    fn test_outgoing_edges_edgenode() {
        let edgenode = make_test_edgenode();
        let mut collect = [0u8; 16];
        assert_eq!(
            &[1],
            collect_to_mut_slice(edgenode.outgoing_edges(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[2],
            collect_to_mut_slice(edgenode.outgoing_edges(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0],
            collect_to_mut_slice(edgenode.outgoing_edges(2).unwrap(), &mut collect)
        );
    }
    #[test]
    fn test_incoming_edges() {
        let edgenode = make_test_edgenode();
        let mut collect = [0u8; 16];
        assert_eq!(
            &[2],
            collect_to_mut_slice(edgenode.incoming_edges(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0],
            collect_to_mut_slice(edgenode.incoming_edges(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[1],
            collect_to_mut_slice(edgenode.incoming_edges(2).unwrap(), &mut collect)
        );
    }
    #[test]
    fn test_neighboring_nodes() {
        let edgenode = make_test_edgenode();
        let mut collect = [0u8; 16];
        assert_eq!(
            &[1, 2],
            collect_to_mut_slice(edgenode.neighboring_nodes(0).unwrap(), &mut collect)
        );
        assert_eq!(
            &[0, 2],
            collect_to_mut_slice(edgenode.neighboring_nodes(1).unwrap(), &mut collect)
        );
        assert_eq!(
            &[1, 0],
            collect_to_mut_slice(edgenode.neighboring_nodes(2).unwrap(), &mut collect)
        );
    }
}
