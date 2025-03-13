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

trait ProtoGraph {
    type MyNodeIndex: NodeIndex;
    fn get_nodes(&self) -> impl Iterator<Item = Self::MyNodeIndex>;
    fn get_edges(&self) -> impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)>;
    fn contains_node(&self, node: Self::MyNodeIndex) -> bool;
    fn outgoing_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex>;
    fn incoming_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex>;
    fn neighboring_nodes(&self, node: Self::MyNodeIndex)
        -> impl Iterator<Item = Self::MyNodeIndex>;
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
    fn get_nodes(&self) -> impl Iterator<Item = Self::MyNodeIndex> {
        (0..N).into_iter()
    }
    fn get_edges(&self) -> impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)> {
        self.matrix
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
            })
    }
    fn contains_node(&self, node: Self::MyNodeIndex) -> bool {
        node < N
    }
    fn outgoing_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex> {
        self.matrix
            .as_ref()
            .get(node)
            .unwrap()
            .as_ref()
            .iter()
            .enumerate()
            .filter_map(|(index, edge)| edge.as_ref().map(|_| index))
    }
    fn incoming_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex> {
        self.matrix
            .as_ref()
            .iter()
            .enumerate()
            .filter_map(move |(index, row)| row.as_ref().get(node).unwrap().as_ref().map(|_| index))
    }
    fn neighboring_nodes(
        &self,
        node: Self::MyNodeIndex,
    ) -> impl Iterator<Item = Self::MyNodeIndex> {
        merge(self.incoming_edges(node), self.outgoing_edges(node)).dedup()
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
    E: EdgesIterable<Node = NI>,
    N: IntoNodesIterator<Node = NI>,
{
    type MyNodeIndex = NI;

    fn get_nodes(&self) -> impl Iterator<Item = Self::MyNodeIndex> {
        self.nodes.iter_nodes().map(|node| *node)
    }

    fn get_edges(&self) -> impl Iterator<Item = (Self::MyNodeIndex, Self::MyNodeIndex)> {
        self.edges.iter_edges().map(|(from, to)| (*from, *to))
    }

    fn contains_node(&self, node: Self::MyNodeIndex) -> bool {
        self.nodes.iter_nodes().any(|n| *n == node)
    }

    fn outgoing_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex> {
        core::iter::empty()
    }

    fn incoming_edges(&self, node: Self::MyNodeIndex) -> impl Iterator<Item = Self::MyNodeIndex> {
        core::iter::empty()
    }

    fn neighboring_nodes(
        &self,
        node: Self::MyNodeIndex,
    ) -> impl Iterator<Item = Self::MyNodeIndex> {
        core::iter::empty()
    }
}

#[cfg(test)]
mod tests {
    //use std;
    use super::ProtoGraph;

    #[test]
    fn make_matrix() {
        let matrix = [[Some(false); 3]; 3];
        let _pen_matrix = super::PenMatrix::<8, _, _, _>::new(matrix);
    }

    fn collect_to_mut_slice<T>(iter: impl Iterator<Item = T>, collect: &mut [T]) -> &[T] {
        let mut len = 0;
        for item in iter {
            collect[len] = item;
            len += 1;
        }
        &collect[..len]
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
        let collected_slice = collect_to_mut_slice(pen_matrix.get_edges(), &mut collect);
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
            collect_to_mut_slice(pen_matrix.outgoing_edges(0), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.outgoing_edges(1), &mut collect)
        );
        assert_eq!(
            &[0, 2],
            collect_to_mut_slice(pen_matrix.outgoing_edges(2), &mut collect)
        );
    }

    #[test]
    fn test_incoming_edges() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [0usize; 16];
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.incoming_edges(0), &mut collect)
        );
        assert_eq!(
            &[0, 1],
            collect_to_mut_slice(pen_matrix.incoming_edges(1), &mut collect)
        );
        assert_eq!(
            &[1, 2],
            collect_to_mut_slice(pen_matrix.incoming_edges(2), &mut collect)
        );
    }
    #[test]
    fn test_neighboring_nodes() {
        let pen_matrix = super::PenMatrix::<8, _, _, _>::new(make_test_matrix());
        let mut collect = [0usize; 16];
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(0), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(1), &mut collect)
        );
        assert_eq!(
            &[0, 1, 2],
            collect_to_mut_slice(pen_matrix.neighboring_nodes(2), &mut collect)
        );
    }
}

#[cfg(test)]
mod tests2 {
    use super::*;

    #[test]
    fn make_edgenode() {
        let edgenode = EdgeNodeList::<_, _, u8> {
            edges: [(0u8, 1), (1, 2), (2, 0)],
            nodes: [0u8, 1, 2],
            _phantom: Default::default(),
        };
        for node in edgenode.get_nodes() {
            println!("Node: {}", node);
        }
    }
}
