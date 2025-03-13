// SPDX-License-Identifier: Apache-2.0

// Todo: remove this
#![allow(unused)]

//! There's nothing in this module ( yet )

use crate::{containers::maps::MapTrait, graph::GraphError, Graph};
use core::{marker::PhantomData, option::Iter, slice::SliceIndex};

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
}
impl<const N: usize, NI, EV, T, INNER> GenMatrix<N, NI, EV, T, INNER>
where
    NI: PartialEq + SliceIndex<[Option<EV>]> + core::convert::From<usize>,
    INNER: AsRef<[Option<EV>]>, // maybe this should be Option<EV> for boolean matrix
    T: AsRef<[INNER]>,
{
    pub fn new_unchecked(matrix: T) -> Self {
        Self {
            matrix,
            phantom: PhantomData,
            ni_array: core::array::from_fn(|i| i.into()),
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
                let col_index = self.col_index;
                self.col_index += 1;
                let col = r.as_ref().get(col_index);
                if let Some(c) = col {
                    if c.is_some() {
                        return Some((&self.id_slice[self.row_index], &self.id_slice[col_index]));
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
        let x = self.matrix.as_ref().len();
        Ok(self.ni_array[..x].iter())
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
        assert_eq!(&collect[..count], &[(0, 0), (0, 2), (1, 2), (2, 0)]);
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
}
