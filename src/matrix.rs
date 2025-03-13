// SPDX-License-Identifier: Apache-2.0

// Todo: remove this
#![allow(unused)]

//! There's nothing in this module ( yet )

use crate::{adjacency_list::AsOutgoingNodes, containers::maps::MapTrait, nodes::NodesIterable};
use core::{marker::PhantomData, slice::SliceIndex};

pub struct GenMatrix<const X: usize, NI, EV, T>
where
    NI: PartialEq + SliceIndex<[EV]>,
    T: AsRef<[[EV; X]; X]>,
{
    matrix: T,
    phantom: PhantomData<(NI, EV)>,
}

impl<const X: usize, NI, EV, T> GenMatrix<X, NI, EV, T>
where
    NI: PartialEq + SliceIndex<[EV]>,
    T: AsRef<[[EV; X]; X]>,
{
    pub fn new(matrix: T) -> Self {
        Self {
            matrix,
            phantom: PhantomData,
        }
    }
}

// General matrix structure without node values
pub struct Matrix1<const X: usize, NI, EV>
where
    NI: PartialEq + SliceIndex<[EV]>,
{
    matrix: [[EV; X]; X],
    phantom: PhantomData<NI>,
}

// Matrix with node values in a tuple with edges
pub struct Matrix3<const X: usize, NI, EV, V>
where
    NI: PartialEq + SliceIndex<[EV]>,
{
    matrix: [(V, [EV; X]); X],
    phantom: PhantomData<NI>,
}

// Bool-specialized aliases for non-lookup matrices
type Matrix1b<const X: usize, NI> = Matrix1<X, NI, bool>;
type Matrix3b<const X: usize, NI, V> = Matrix3<X, NI, bool, V>;

/// Matrix structures with indexed lookups

// General matrix with lookup support and no node values
pub struct Matrix1Lookup<const X: usize, NI, EV, M>
where
    M: MapTrait<NI, usize>,
    NI: PartialEq,
{
    ni_to_index_map: M,
    matrix: [[EV; X]; X],
    phantom: PhantomData<NI>,
}

// Matrix with lookup support, with node values in a tuple with edges
pub struct Matrix3Lookup<const X: usize, NI, EV, M, V>
where
    M: MapTrait<NI, usize>,
    NI: PartialEq,
{
    ni_to_index_map: M,
    matrix: [(V, [EV; X]); X],
    phantom: PhantomData<NI>,
}

// Bool-specialized aliases for lookup matrices
type Matrix1Lookupb<const X: usize, NI, M> = Matrix1Lookup<X, NI, bool, M>;
type Matrix3bLookup<const X: usize, NI, M, V> = Matrix3Lookup<X, NI, bool, M, V>;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn try_gen_matrix() {
        let tests1 = GenMatrix::new([[0; 3]; 3]);
    }
}
