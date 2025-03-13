// SPDX-License-Identifier: Apache-2.0

use super::EdgesIterable;

/// Iterator that yields node indexes from edges in sorted order.
///
/// Warning: This makes a copy of the edges on every invocation,
/// and sorts them. This is extremely inefficient. Only to be used
/// with small edgelist-only graphs.
#[derive(Clone, Copy)]
pub struct EdgesToNodesIterator<'a, const N: usize, NI> {
    row1: [&'a NI; N],
    row2: [&'a NI; N],
    i: usize,
    j: usize,
    back_i: usize,
    back_j: usize,
    last_index: usize,
    back_i_underflow: bool,
    back_j_underflow: bool,
}

#[derive(Debug, PartialEq, Clone, Copy)]
/// Iteration errors for [`EdgesToNodesIterator`] iterator
pub enum EdgeNodeError {
    /// Cannot iterate over empty edges, at least one reference
    /// needs to exist
    EmptyEdges,
    /// Capacity parameter N isn't large enough to process all nodes
    NotEnoughCapacity,
}

/// Iterates over edges, yielding node indexes in sorted order.
/// Capacity needs to be specified at compile time, and be at least half
/// the number of nodes in the graph.
///
/// Only used for edgelist-only graphs.
impl<'a, const N: usize, NI> EdgesToNodesIterator<'a, N, NI>
where
    NI: Ord,
{
    pub fn new<E>(edges: &'a E) -> Result<Self, EdgeNodeError>
    where
        E: EdgesIterable<Node = NI> + 'a,
    {
        let first_ref = edges.iter_edges().next();
        if first_ref.is_none() {
            return Err(EdgeNodeError::EmptyEdges);
        }
        let init = first_ref.unwrap().0;
        let mut row1: [&'a NI; N] = core::array::from_fn(|_| init);
        let mut row2: [&'a NI; N] = core::array::from_fn(|_| init);

        let mut len = 0;
        for (index, edge) in edges.iter_edges().enumerate() {
            if index == N {
                return Err(EdgeNodeError::NotEnoughCapacity);
            }
            row1[index] = edge.0;
            row2[index] = edge.1;
            len = index;
        }
        len += 1;
        let sort_1 = &mut row1[..len];
        let sort_2 = &mut row2[..len];
        sort_1.sort_unstable();
        sort_2.sort_unstable();
        Ok(Self {
            row1,
            row2,
            i: 0,
            j: 0,
            last_index: len - 1,
            back_i: len - 1,
            back_j: len - 1,
            back_i_underflow: false,
            back_j_underflow: false,
        })
    }
}
impl<'a, const N: usize, NI> Iterator for EdgesToNodesIterator<'a, N, NI>
where
    NI: PartialEq + Ord,
{
    type Item = &'a NI;
    fn next(&mut self) -> Option<Self::Item> {
        while self.i <= self.back_i || self.j <= self.back_j {
            let prev_i = self.i;
            let prev_j = self.j;

            // Yield from left column and advance
            if prev_i <= self.back_i
                && (prev_j.wrapping_sub(1) == self.back_j || self.row1[prev_i] < self.row2[prev_j])
            {
                self.i += 1;
                if prev_i == 0 || self.row1[prev_i] != self.row1[prev_i - 1] {
                    return Some(self.row1[prev_i]);
                }
            // Yield from right column and advance
            } else if prev_j <= self.back_j
                && (prev_i.wrapping_sub(1) == self.back_i || self.row2[prev_j] < self.row1[prev_i])
            {
                self.j += 1;
                if prev_j == 0 || self.row2[prev_j] != self.row2[prev_j - 1] {
                    return Some(self.row2[prev_j]);
                }
            // Advance both and yield from left
            } else {
                self.i += 1;
                self.j += 1;
                if (prev_i == 0 || self.row1[prev_i] != self.row1[prev_i - 1])
                    && (prev_j == 0 || self.row2[prev_j] != self.row2[prev_j - 1])
                {
                    return Some(self.row1[prev_i]);
                }
            }
        }
        None
    }
}

impl<const N: usize, NI> DoubleEndedIterator for EdgesToNodesIterator<'_, N, NI>
where
    NI: PartialEq + Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        while (self.back_i >= self.i && !self.back_i_underflow)
            || (self.back_j >= self.j && !self.back_j_underflow)
        {
            let prev_i_underflow = self.back_i_underflow;
            let prev_j_underflow = self.back_j_underflow;
            let prev_i = self.back_i;
            let prev_j = self.back_j;

            // Yield from left column and step back
            if (prev_i >= self.i && !prev_i_underflow)
                && (prev_j.wrapping_add(1) == self.j || self.row1[prev_i] > self.row2[prev_j])
            {
                let (new_back, new_underflow) = self.back_i.overflowing_sub(1);
                self.back_i = new_back;
                self.back_i_underflow = new_underflow;
                if prev_i == self.last_index || self.row1[prev_i] != self.row1[prev_i + 1] {
                    return Some(self.row1[prev_i]);
                }
            // Yield from right column and step back
            } else if (prev_j >= self.j && !prev_j_underflow)
                && (prev_i.wrapping_add(1) == self.i || self.row2[prev_j] > self.row1[prev_i])
            {
                let (new_back, new_underflow) = self.back_j.overflowing_sub(1);
                self.back_j = new_back;
                self.back_j_underflow = new_underflow;
                if prev_j == self.last_index || self.row2[prev_j] != self.row2[prev_j + 1] {
                    return Some(self.row2[prev_j]);
                }
            // Step back both and yield from left
            } else {
                let (new_back, new_underflow) = self.back_i.overflowing_sub(1);
                self.back_i = new_back;
                self.back_i_underflow = new_underflow;
                let (new_back, new_underflow) = self.back_j.overflowing_sub(1);
                self.back_j = new_back;
                self.back_j_underflow = new_underflow;
                if (prev_i == self.last_index
                    || (!prev_i_underflow && (self.row1[prev_i] != self.row1[prev_i + 1])))
                    && (prev_j == self.last_index
                        || (!prev_j_underflow && (self.row2[prev_j] != self.row2[prev_j + 1])))
                {
                    return Some(self.row1[prev_i]);
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edges::{EdgeStruct, EdgeStructOption};

    fn test_node_collect<'a, const C: usize, E, NI>(
        edges: &'a E,
        cmp: Result<&[&NI], EdgeNodeError>,
    ) where
        E: EdgesIterable<Node = NI> + 'a,
        NI: Ord + Default + core::fmt::Debug + 'a,
    {
        let default = NI::default();
        let mut collect: [&NI; 256] = core::array::from_fn(|_| &default);
        let mut last_index = 0;
        let result = EdgesToNodesIterator::<C, _>::new(edges);
        if let Ok(edge_to_nodes) = result {
            for (idx, node) in edge_to_nodes.zip(collect.iter_mut()).enumerate() {
                *node.1 = node.0;
                last_index = idx
            }
            let final_slice = &collect[..last_index + 1];
            assert_eq!(final_slice, cmp.unwrap());
        } else {
            assert_eq!(result.err(), cmp.err());
        }
    }

    // New helper function for backward iteration
    fn test_node_collect_back<'a, const C: usize, E, NI>(
        edges: &'a E,
        cmp: Result<&[&NI], EdgeNodeError>,
    ) where
        E: EdgesIterable<Node = NI> + 'a,
        NI: Ord + Default + core::fmt::Debug + 'a,
    {
        let default = NI::default();
        let mut collect: [&NI; 256] = core::array::from_fn(|_| &default);
        let mut last_index = 0;
        let result = EdgesToNodesIterator::<C, _>::new(edges);
        if let Ok(mut edge_to_nodes) = result {
            while let Some(node) = edge_to_nodes.next_back() {
                collect[last_index] = node;
                last_index += 1;
            }
            let final_slice = &collect[..last_index];
            if let Ok(expected) = cmp {
                // Since next_back yields in reverse order, reverse the expected slice for comparison
                let mut collect_rev: [&NI; 256] = core::array::from_fn(|_| &default);
                let expected_reversed = &mut collect_rev[..expected.len()];
                expected_reversed.clone_from_slice(expected);
                expected_reversed.reverse();
                assert_eq!(final_slice, expected_reversed);
            } else {
                panic!("Expected an error, but got Ok");
            }
        } else {
            assert_eq!(result.err(), cmp.err());
        }
    }

    #[test]
    fn test_corner_cases() {
        let edges = EdgeStructOption::<0, usize>([]);
        test_node_collect::<1, _, _>(&edges, Err(EdgeNodeError::EmptyEdges));
        test_node_collect::<0, _, _>(&edges, Err(EdgeNodeError::EmptyEdges));
        let edges = EdgeStruct([(1, 1)]);
        test_node_collect::<0, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect::<1, _, _>(&edges, Ok(&[&1]));
        let edges = EdgeStruct([(1, 1), (1, 1)]);
        test_node_collect::<0, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect::<1, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect::<2, _, _>(&edges, Ok(&[&1]));
        test_node_collect::<3, _, _>(&edges, Ok(&[&1]));
        test_node_collect::<2, _, _>(&EdgeStruct([(2, 1), (1, 2)]), Ok(&[&1, &2]));
    }
    #[test]
    fn test_corner_cases_backward() {
        // Backward iteration tests for corner cases
        let edges = EdgeStructOption::<0, usize>([]);
        test_node_collect_back::<1, _, _>(&edges, Err(EdgeNodeError::EmptyEdges));
        test_node_collect_back::<0, _, _>(&edges, Err(EdgeNodeError::EmptyEdges));
        let edges = EdgeStruct([(1, 1)]);
        test_node_collect_back::<0, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect_back::<1, _, _>(&edges, Ok(&[&1]));
        let edges = EdgeStruct([(1, 1), (1, 1)]);
        test_node_collect_back::<0, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect_back::<1, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
        test_node_collect_back::<2, _, _>(&edges, Ok(&[&1]));
        test_node_collect_back::<3, _, _>(&edges, Ok(&[&1]));
        test_node_collect_back::<2, _, _>(&EdgeStruct([(2, 1), (1, 2)]), Ok(&[&1, &2]));
    }

    #[test]
    fn test_simple_sequence() {
        let edges = EdgeStructOption::<4, usize>([Some((0, 1)), Some((1, 20)), None, Some((2, 3))]);
        test_node_collect::<5, _, _>(&edges, Ok(&[&0, &1, &2, &3, &20]));
        test_node_collect::<3, _, _>(&edges, Ok(&[&0, &1, &2, &3, &20]));
        test_node_collect::<2, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity))
    }
    #[test]
    fn test_simple_sequence_backward() {
        let edges = EdgeStructOption::<4, usize>([Some((0, 1)), Some((1, 20)), None, Some((2, 3))]);
        test_node_collect_back::<5, _, _>(&edges, Ok(&[&0, &1, &2, &3, &20]));
        test_node_collect_back::<3, _, _>(&edges, Ok(&[&0, &1, &2, &3, &20]));
        test_node_collect_back::<2, _, _>(&edges, Err(EdgeNodeError::NotEnoughCapacity));
    }

    #[test]
    fn test_option_structs() {
        let edges = EdgeStructOption::<4, usize>([Some((0, 1)), Some((1, 20)), None, Some((2, 3))]);
        test_node_collect::<5, _, _>(&edges, Ok(&[&0, &1, &2, &3, &20]));
    }

    #[test]
    fn test_unsorted_edges() {
        let edges = EdgeStruct([(10, 1), (3, 5), (7, 2), (4, 6), (2, 8), (9, 0)]);
        test_node_collect::<12, _, _>(&edges, Ok(&[&0, &1, &2, &3, &4, &5, &6, &7, &8, &9, &10]));
    }
    #[test]
    fn test_unsorted_edges_backward() {
        let edges = EdgeStruct([(10, 1), (3, 5), (7, 2), (4, 6), (2, 8), (9, 0)]);
        test_node_collect_back::<12, _, _>(
            &edges,
            Ok(&[&0, &1, &2, &3, &4, &5, &6, &7, &8, &9, &10]),
        );
    }
    #[test]
    fn test_multiple_edges_with_duplicates() {
        let edges = EdgeStruct([
            (3, 4),
            (1, 2),
            (2, 3),
            (1, 4),
            (2, 2),
            (4, 5),
            (3, 3),
            (5, 6),
            (5, 5),
        ]);
        test_node_collect::<10, _, _>(&edges, Ok(&[&1, &2, &3, &4, &5, &6]));
    }
    #[test]
    fn test_multiple_edges_with_duplicates_backward() {
        let edges = EdgeStruct([
            (3, 4),
            (1, 2),
            (2, 3),
            (1, 4),
            (2, 2),
            (4, 5),
            (3, 3),
            (5, 6),
            (5, 5),
        ]);
        test_node_collect_back::<10, _, _>(&edges, Ok(&[&1, &2, &3, &4, &5, &6]));
    }

    #[test]
    fn test_forward_and_backward_iteration() {
        let edges = EdgeStruct([(1, 3), (2, 4), (5, 7), (6, 8)]);
        let mut iterator =
            EdgesToNodesIterator::<8, _>::new(&edges).expect("Failed to create iterator");
        assert_eq!(iterator.next(), Some(&1));
        assert_eq!(iterator.next_back(), Some(&8));
        assert_eq!(iterator.next(), Some(&2));
        assert_eq!(iterator.next_back(), Some(&7));
        assert_eq!(iterator.next(), Some(&3));
        assert_eq!(iterator.next_back(), Some(&6));
        assert_eq!(iterator.next(), Some(&4));
        assert_eq!(iterator.next_back(), Some(&5));
        assert_eq!(iterator.next(), None);
        assert_eq!(iterator.next_back(), None);
    }
}
