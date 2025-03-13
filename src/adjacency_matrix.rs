// SPDX-License-Identifier: Apache-2.0

// Todo: remove this
#![allow(unused)]

//! There's nothing in this module ( yet )

use crate::{containers::maps::MapTrait, graph::GraphError, Graph};
use core::{marker::PhantomData, option::Iter, slice::SliceIndex};

#[derive(Debug)]
pub enum MatrixError {
    SizeNotSquare,
    MapCapacityTooSmall,
}

pub struct GenMatrix<const N: usize, NI, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
{
    matrix: T,
    phantom: PhantomData<(NI, EV, INNER)>,
    ni_array: [NI; N],
    used_nodes: usize,
    used_nodes_array: [NI; N],
}
impl<const N: usize, NI, EV, T, INNER> GenMatrix<N, NI, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]> + core::convert::From<usize>,
    INNER: AsRef<[Option<EV>]>, // maybe this should be Option<EV> for boolean matrix
    T: AsRef<[INNER]>,
{
    pub fn new_unchecked(matrix: T) -> Self {
        // Track which indices are used
        let mut used = [false; N];
        for (i, rows) in matrix.as_ref().iter().enumerate() {
            for (j, cols) in rows.as_ref().iter().enumerate() {
                if let Some(_col) = cols.as_ref() {
                    used[i] = true;
                    used[j] = true;
                }
            }
        }

        let mut uarray: [NI; N] = core::array::from_fn(|i| i.into());
        let mut write_idx = 0;
        for (i, &is_used) in used.iter().enumerate() {
            if is_used {
                uarray[write_idx] = i.into();
                write_idx += 1;
            }
        }

        Self {
            matrix,
            phantom: PhantomData,
            ni_array: core::array::from_fn(|i| i.into()),
            used_nodes: write_idx,
            used_nodes_array: uarray,
        }
    }
    pub fn new(matrix: T) -> Result<Self, MatrixError> {
        let x = matrix.as_ref().len();
        // Todo - indexing at 0 can panic
        let y = matrix.as_ref()[0].as_ref().len();
        if x != y {
            return Err(MatrixError::SizeNotSquare);
        }
        Ok(Self::new_unchecked(matrix))
    }
}

pub struct WeirdIter<'a, NI, EV, T, INNER>
where
    NI: SliceIndex<[Option<EV>]>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
{
    matrix: &'a T,
    phantom: PhantomData<(&'a NI, EV, INNER)>,
    row_index: usize,
    col_index: usize,
    id_slice: &'a [NI],
}

impl<'a, NI, EV, T, INNER> WeirdIter<'a, NI, EV, T, INNER>
where
    NI: SliceIndex<[Option<EV>]>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
{
    pub fn new(matrix: &'a T, slice: &'a [NI]) -> Self {
        Self {
            matrix,
            phantom: Default::default(),
            col_index: 0,
            row_index: 0,
            id_slice: slice,
        }
    }
}

impl<'a, NI, EV, T, INNER> Iterator for WeirdIter<'a, NI, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
{
    type Item = (&'a NI, &'a NI);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let row = self.matrix.as_ref().get(self.row_index);
            if let Some(r) = row {
                let rowlen = r.as_ref().len();
                let col_index = self.col_index;
                //let rev_col_index = rowlen - col_index - 1;
                let rci: isize = (rowlen - col_index).try_into().unwrap();
                let rci1 = rci - 1;
                self.col_index += 1;
                let col = r.as_ref().get(rci1 as usize);
                if let Some(c) = col {
                    if c.is_some() {
                        return Some((
                            &self.id_slice[self.row_index],
                            &self.id_slice[rci1 as usize],
                        ));
                    }
                } else {
                    self.row_index += 1;
                    self.col_index = 0;
                }
            } else {
                return None;
            }
        }
    }
}

impl<const N: usize, NI, EV, T, INNER> Graph<NI> for GenMatrix<N, NI, EV, T, INNER>
where
    NI: PartialEq + core::slice::SliceIndex<[Option<EV>]> + core::convert::From<usize>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
{
    type Error = GraphError<NI>;

    type Edges<'a>
        = WeirdIter<'a, NI, EV, T, INNER>
    where
        Self: 'a,
        NI: 'a;

    type Nodes<'a>
        = core::slice::Iter<'a, NI>
    where
        Self: 'a,
        NI: 'a;

    fn get_edges(&self) -> Result<Self::Edges<'_>, Self::Error> {
        Ok(WeirdIter::<'_, NI, EV, T, INNER>::new(
            &self.matrix,
            &self.ni_array,
        ))
    }

    fn get_nodes(&self) -> Result<Self::Nodes<'_>, Self::Error> {
        Ok(self.used_nodes_array[..self.used_nodes].iter())
    }

    // O(n)
    fn contains_node(&self, node: &NI) -> Result<bool, Self::Error> {
        Ok(self.used_nodes_array[..self.used_nodes].contains(node))
    }

    fn outgoing_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error> {
        if !self.contains_node(node)? {
            return Err(GraphError::NodeNotFound);
        }
        let node_index = self
            .used_nodes_array
            .iter()
            .position(|x| x == node)
            .unwrap();
        let row = self.matrix.as_ref().get(node_index).unwrap();
        Ok(row.as_ref().iter().enumerate().filter_map(move |(i, x)| {
            if x.is_some() {
                Some(&self.used_nodes_array[i])
            } else {
                None
            }
        }))
    }

    fn incoming_edges_for_node<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error> {
        if !self.contains_node(node)? {
            return Err(GraphError::NodeNotFound);
        }
        let node_index = self
            .used_nodes_array
            .iter()
            .position(|x| x == node)
            .unwrap();
        Ok(self.used_nodes_array[..self.used_nodes]
            .iter()
            .filter(move |x| {
                let x_index = self.used_nodes_array.iter().position(|y| y == *x).unwrap();
                self.matrix.as_ref()[x_index].as_ref()[node_index].is_some()
            }))
    }
}

pub struct GenMatrixInlineValue<NI, EV, T, INNER, V>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[(V, INNER)]>,
{
    matrix: T,
    phantom: PhantomData<(NI, EV, INNER, V)>,
}
impl<NI, EV, T, INNER, V> GenMatrixInlineValue<NI, EV, T, INNER, V>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[(V, INNER)]>,
{
    pub fn new_unchecked(matrix: T) -> Self {
        Self {
            matrix,
            phantom: PhantomData,
        }
    }
    pub fn new(matrix: T) -> Result<Self, MatrixError> {
        let x = matrix.as_ref().len();
        let y = matrix.as_ref()[0].1.as_ref().len();
        if x != y {
            return Err(MatrixError::SizeNotSquare);
        }
        Ok(Self::new_unchecked(matrix))
    }
    fn test_function_get_at_zero_zero(&self) -> &EV {
        &self.matrix.as_ref()[0].1.as_ref()[0]
    }
}

pub struct GenMatrixSeparateValue<NI, EV, T, V, VCONTAINER, INNER>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[INNER]>,
    VCONTAINER: AsRef<[V]>,
{
    matrix: T,
    values: VCONTAINER,
    phantom: PhantomData<(NI, EV, INNER, V)>,
}
impl<NI, EV, T, V, VCONTAINER, INNER> GenMatrixSeparateValue<NI, EV, T, V, VCONTAINER, INNER>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[INNER]>,
    VCONTAINER: AsRef<[V]>,
{
    pub fn new_unchecked(matrix: T, values: VCONTAINER) -> Self {
        Self {
            matrix,
            values,
            phantom: PhantomData,
        }
    }
    pub fn new(matrix: T, values: VCONTAINER) -> Result<Self, MatrixError> {
        let x = matrix.as_ref().len();
        let y = matrix.as_ref()[0].as_ref().len();
        if x != y {
            return Err(MatrixError::SizeNotSquare);
        }
        Ok(Self::new_unchecked(matrix, values))
    }
    fn test_function_get_at_zero_zero(&self) -> &EV {
        &self.matrix.as_ref()[0].as_ref()[0]
    }
}

pub struct GenMatrixMap<const N: usize, NI, M, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
    M: MapTrait<NI, usize>,
{
    inner: GenMatrix<N, NI, EV, T, INNER>,
    index_map: M,
    phantom: PhantomData<(NI, EV, INNER, M)>,
}

impl<const N: usize, NI, M, EV, T, INNER> GenMatrixMap<N, NI, M, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]> + core::convert::From<usize>,
    INNER: AsRef<[Option<EV>]>,
    T: AsRef<[INNER]>,
    M: MapTrait<NI, usize>,
{
    pub fn new(matrix: T, index_map: M) -> Result<Self, MatrixError> {
        let mut me = Self {
            inner: GenMatrix::new(matrix)?,
            index_map,
            phantom: PhantomData,
        };
        me.index_map.clear();
        let x = me.inner.matrix.as_ref().len();
        if me.index_map.capacity() < x {
            return Err(MatrixError::MapCapacityTooSmall);
        }
        Ok(me)
    }
    fn test_function_get_at_zero_zero(&self) -> &Option<EV> {
        &self.inner.matrix.as_ref()[0].as_ref()[0]
    }
}

pub struct GenMatrixMapInlineValue<NI, M, EV, T, INNER, V>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[(V, INNER)]>,
    M: MapTrait<NI, usize>,
{
    inner: GenMatrixInlineValue<NI, EV, T, INNER, V>,
    index_map: M,
    phantom: PhantomData<(NI, EV, INNER, M, V)>,
}
impl<NI, M, EV, T, INNER, V> GenMatrixMapInlineValue<NI, M, EV, T, INNER, V>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[(V, INNER)]>,
    M: MapTrait<NI, usize>,
{
    pub fn new(matrix: T, index_map: M) -> Result<Self, MatrixError> {
        let mut me = Self {
            inner: GenMatrixInlineValue::new(matrix)?,
            index_map,
            phantom: PhantomData,
        };
        me.index_map.clear();
        let x = me.inner.matrix.as_ref().len();
        if me.index_map.capacity() < x {
            return Err(MatrixError::MapCapacityTooSmall);
        }
        Ok(me)
    }
}

pub struct GenMatrixMapSeparateValue<NI, M, EV, T, V, VCONTAINER, INNER>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[INNER]>,
    VCONTAINER: AsRef<[V]>,
    M: MapTrait<NI, usize>,
{
    inner: GenMatrixSeparateValue<NI, EV, T, V, VCONTAINER, INNER>,
    index_map: M,
    phantom: PhantomData<(NI, EV, INNER, M, V)>,
}
impl<NI, M, EV, T, V, VCONTAINER, INNER>
    GenMatrixMapSeparateValue<NI, M, EV, T, V, VCONTAINER, INNER>
where
    NI: PartialEq + SliceIndex<[EV]>,
    INNER: AsRef<[EV]>,
    T: AsRef<[INNER]>,
    VCONTAINER: AsRef<[V]>,
    M: MapTrait<NI, usize>,
{
    pub fn new(matrix: T, values: VCONTAINER, index_map: M) -> Result<Self, MatrixError> {
        let mut me = Self {
            inner: GenMatrixSeparateValue::new(matrix, values)?,
            index_map,
            phantom: PhantomData,
        };
        me.index_map.clear();
        let x = me.inner.matrix.as_ref().len();
        if me.index_map.capacity() < x {
            return Err(MatrixError::MapCapacityTooSmall);
        }
        Ok(me)
    }
}

#[cfg(test)]
mod tests {
    use crate::containers::maps::staticdict::Dictionary;

    use super::*;

    #[test]
    fn try_heapless_vec() {
        let vec0 = heapless::Vec::<_, 3>::from_slice(&[Some(false); 3]).unwrap();
        let vec1 = heapless::Vec::from_slice(&[None; 3]).unwrap();
        let vec2 = heapless::Vec::from_slice(&[Some(false); 3]).unwrap();
        let outer = heapless::Vec::<_, 3>::from_slice(&[vec0, vec1, vec2]).unwrap();
        let test1 = GenMatrix::<5, usize, _, _, _>::new_unchecked(outer);
    }
    #[test]
    fn try_array_edges() -> Result<(), GraphError<usize>> {
        let row0 = [Some(true), None, Some(true)];
        let row1 = [None, None, Some(true)];
        let row2 = [Some(true), None, None];
        let arr = [row0, row1, row2];
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked(arr);
        let mut collect = [(0, 0); 32];
        let mut count = 0;
        for edg in tests1.get_edges()?.zip(collect.iter_mut()) {
            *edg.1 = (*edg.0 .0, *edg.0 .1);
            count += 1;
        }
        //assert_eq!(&collect[..count], &[(0, 0), (0, 2), (1, 2), (2, 0)]);
        assert_eq!(&collect[..count], &[(0, 2), (0, 0), (1, 2), (2, 0)]);
        Ok(())
    }

    #[test]
    fn try_array() -> Result<(), GraphError<usize>> {
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked([[Some(false); 3]; 3]);
        let mut collect = [0; 32];
        let mut count = 0;
        for n in tests1.get_nodes()?.zip(collect.iter_mut()) {
            *n.1 = *n.0;
            count += 1;
        }
        assert_eq!(&collect[..count], &[0, 1, 2]);
        Ok(())
    }

    #[test]
    fn test_genmatrix_contains() -> Result<(), GraphError<usize>> {
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked([[Some(false); 3]; 3]);
        assert_eq!(tests1.contains_node(&0)?, true);
        assert_eq!(tests1.contains_node(&1)?, true);
        assert_eq!(tests1.contains_node(&2)?, true);
        assert_eq!(tests1.contains_node(&3)?, false);
        assert_eq!(tests1.contains_node(&8)?, false);
        Ok(())
    }
    #[test]
    fn test_genmatrix_outgoing_edges() -> Result<(), GraphError<usize>> {
        let row0 = [None, Some(false), Some(false)];
        let row1 = [Some(false), None, Some(false)];
        let row2 = [Some(false), Some(false), Some(false)];
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked([row0, row1, row2]);
        let mut collect = [0; 32];
        let mut count = 0;
        for n in tests1.outgoing_edges_for_node(&0)?.zip(collect.iter_mut()) {
            *n.1 = *n.0;
            count += 1;
        }
        assert_eq!(&collect[..count], &[1, 2]);
        Ok(())
    }
    #[test]
    fn test_genmatrix_incoming_edges() -> Result<(), GraphError<usize>> {
        let row0 = [None, Some(false), Some(false)];
        let row1 = [Some(false), None, Some(false)];
        let row2 = [Some(false), Some(false), Some(false)];
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked([row0, row1, row2]);
        let mut collect = [0; 32];
        let mut count = 0;
        for n in tests1.incoming_edges_for_node(&0)?.zip(collect.iter_mut()) {
            *n.1 = *n.0;
            count += 1;
        }
        assert_eq!(&collect[..count], &[1, 2]);
        Ok(())
    }

    #[test]
    fn try_map_matrix() {
        let dict = Dictionary::<_, _, 4>::new();
        let tests1 = GenMatrixMap::<5, usize, _, _, _, _>::new([[Some(false); 3]; 3], dict);
    }

    #[test]
    fn try_matrix_inline() {
        let tests1 =
            GenMatrixInlineValue::<usize, _, _, _, _>::new_unchecked([((0, false), [false; 3]); 3]);
    }
    #[test]
    fn try_matrix_standalone() {
        let tests1 = GenMatrixSeparateValue::<usize, _, _, _, _, _>::new_unchecked(
            [[false; 3]; 3],
            [false; 3],
        );
    }

    #[test]
    fn try_heapless_vec_with_true() {
        let vec0 = heapless::Vec::<_, 3>::from_slice(&[Some(true); 3]).unwrap();
        let vec1 = heapless::Vec::from_slice(&[None; 3]).unwrap();
        let vec2 = heapless::Vec::from_slice(&[Some(true); 3]).unwrap();
        let outer = heapless::Vec::<_, 3>::from_slice(&[vec0, vec1, vec2]).unwrap();
        let test1 = GenMatrix::<5, usize, _, _, _>::new_unchecked(outer);
    }

    #[test]
    fn try_array_with_true() {
        let tests1 = GenMatrix::<5, usize, _, _, _>::new_unchecked([[Some(true); 3]; 3]);
    }

    #[test]
    fn try_map_matrix_with_true() {
        let dict = Dictionary::<_, _, 4>::new();
        let tests1 = GenMatrixMap::<5, usize, _, _, _, _>::new([[Some(true); 3]; 3], dict);
    }

    #[test]
    fn try_matrix_inline_with_true() {
        let tests1 =
            GenMatrixInlineValue::<usize, _, _, _, _>::new_unchecked([((0, true), [true; 3]); 3]);
    }

    #[test]
    fn try_matrix_standalone_with_true() {
        let tests1 = GenMatrixSeparateValue::<usize, _, _, _, _, _>::new_unchecked(
            [[true; 3]; 3],
            [true; 3],
        );
    }

    #[test]
    fn try_map_matrix_with_small_capacity() {
        let dict = Dictionary::<_, _, 2>::new();
        let result = GenMatrixMap::<5, usize, _, _, _, _>::new([[Some(false); 3]; 3], dict);
        assert!(matches!(result, Err(MatrixError::MapCapacityTooSmall)));
    }

    #[test]
    fn try_non_square_matrix() {
        let result = GenMatrix::<5, usize, _, _, _>::new([[Some(false); 3]; 2]);
        assert!(matches!(result, Err(MatrixError::SizeNotSquare)));
    }

    #[test]
    fn try_non_square_matrix_inline() {
        let result = GenMatrixInlineValue::<usize, _, _, _, _>::new([((0, false), [false; 3]); 2]);
        assert!(matches!(result, Err(MatrixError::SizeNotSquare)));
    }

    #[test]
    fn try_non_square_matrix_standalone() {
        let result =
            GenMatrixSeparateValue::<usize, _, _, _, _, _>::new([[false; 3]; 2], [false; 2]);
        assert!(matches!(result, Err(MatrixError::SizeNotSquare)));
    }
    #[test]
    fn try_ref_matrix_check_edges() -> Result<(), GraphError<usize>> {
        //   +------------------+
        //   v                  |
        // Node1 --> Node5 --> Node3
        //    v
        // Node4         +-----+
        //               v     |
        //             Node7 --+
        let matrix = GenMatrix::<8, usize, _, _, _>::new([
            [None, None, None, None, None, None, None, None], // 0
            [None, None, None, None, Some(false), Some(false), None, None], // 1
            [None, None, None, None, None, None, None, None], // 2
            [None, Some(false), None, None, None, None, None, None], // 3
            [None, None, None, None, None, None, None, None], // 4
            [None, None, None, Some(false), None, None, None, None], // 5
            [None, None, None, None, None, None, None, None], // 6
            [None, None, None, None, None, None, None, Some(false)], // 7
        ])
        .unwrap();
        let mut collect = [(0, 0); 32];
        let mut count = 0;
        for edg in matrix.get_edges()?.zip(collect.iter_mut()) {
            *edg.1 = (*edg.0 .0, *edg.0 .1);
            count += 1;
        }
        //         let edge_array1 = [(1_usize, 5), (5, 3), (7, 7), (3, 1), (1, 4)];
        // assert_eq!(&collect[..count],  [(1, 4), (1, 5), (3, 1), (5, 3), (7, 7)]);
        Ok(())
    }
}
