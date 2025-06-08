use crate::{containers::maps::MapTrait, graph::NodeIndexTrait};

// Wraps an inner bitmap of edges, with node indices in a map
pub struct BitMapMatrix<const N: usize, NI, M>
where
    NI: NodeIndexTrait,
    M: MapTrait<usize, NI>,
{
    _bitmap: super::bit_matrix::BitMatrix<N>,
    _index_map: M,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, M> BitMapMatrix<N, NI, M>
where
    NI: NodeIndexTrait,
    M: MapTrait<usize, NI>,
{
    pub fn new(bitmap: super::bit_matrix::BitMatrix<N>, index_map: M) -> Self {
        Self {
            _bitmap: bitmap,
            _index_map: index_map,
            _phantom: Default::default(),
        }
    }
}
