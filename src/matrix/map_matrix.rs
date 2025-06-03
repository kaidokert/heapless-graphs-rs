use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, GraphRef, GraphVal, NodeIndexTrait},
};

pub struct MapMatrix<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, NI>,
{
    inner: super::simple_matrix::Matrix<N, EDGEVALUE, COLUMNS, ROW>,
    index_map: M,
    phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> GraphRef<NI>
    for MapMatrix<N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.index_map.iter().map(|(_, v)| v))
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.inner.iter_edges().unwrap().map(|(i, j)| {
            let n = self.index_map.get(&i).unwrap();
            let m = self.index_map.get(&j).unwrap();
            (n, m)
        }))
    }
}
