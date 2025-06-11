use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, NodeIndexTrait},
};

pub mod by_val;

/// A matrix-based graph representation that maps arbitrary node indices to matrix positions
///
/// This struct wraps a [`Matrix`](super::simple_matrix::Matrix) and provides a mapping
/// from arbitrary node indices to matrix row/column positions, allowing graphs with
/// non-contiguous or non-zero-based node indices.
pub struct MapMatrix<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    inner: super::simple_matrix::Matrix<N, EDGEVALUE, COLUMNS, ROW>,
    index_map: M,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    /// Creates a new MapMatrix with the given matrix data and index mapping
    ///
    /// The `matrix` parameter provides the adjacency matrix data, and `index_map`
    /// maps from the actual node indices to matrix indices (0..N).
    pub fn new(matrix: COLUMNS, index_map: M) -> Result<Self, GraphError<NI>> {
        for (_, idx) in index_map.iter() {
            if *idx >= N {
                return Err(GraphError::IndexOutOfBounds(*idx));
            }
        }
        Ok(Self::new_unchecked(matrix, index_map))
    }

    /// Creates a new MapMatrix with the given matrix data and index mapping
    ///
    /// The `matrix` parameter provides the adjacency matrix data, and `index_map`
    /// maps from the actual node indices to matrix indices (0..N).
    pub fn new_unchecked(matrix: COLUMNS, index_map: M) -> Self {
        Self {
            inner: super::simple_matrix::Matrix::new(matrix),
            index_map,
            _phantom: Default::default(),
        }
    }
}
