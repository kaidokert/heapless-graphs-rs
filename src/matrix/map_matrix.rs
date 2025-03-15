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

impl<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> MapMatrix<N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, NI>,
{
    pub fn new(matrix: COLUMNS, index_map: M) -> Self {
        Self {
            inner: super::simple_matrix::Matrix::new(matrix),
            index_map,
            phantom: core::marker::PhantomData,
        }
    }
}

impl<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> GraphRef<NI>
    for MapMatrix<N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait + core::fmt::Debug,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use test_log::test;

    #[test]
    fn test_map_matrix() {
        // Nodeindex is i32 here
        let mut index_map = Dictionary::<_, _, 71>::new();
        index_map.insert(0_usize, 'b');
        index_map.insert(1_usize, 'c');
        index_map.insert(2_usize, 'a');

        let array_data = [
            [Some(true), Some(true), None],
            [None, None, Some(false)],
            [Some(false), None, Some(true)],
        ];
        let map_matrix: MapMatrix<3, _, _, _, _, _> = MapMatrix::new(array_data, index_map);

        let inner = map_matrix.inner.iter_nodes().unwrap();
        let nodes: Vec<usize> = inner.collect();
        assert_eq!(nodes, vec![0, 1, 2]);

        let keys = map_matrix.index_map.keys();
        let keys: Vec<usize> = keys.map(|k| *k).collect();
        assert_eq!(keys, vec![0, 1, 2]);

        let outer = map_matrix.iter_nodes().unwrap();
        let outer_nodes: Vec<char> = outer.map(|n| *n).collect();
        assert_eq!(outer_nodes, vec!['b', 'c', 'a']);

        let edges = map_matrix.iter_edges().unwrap();
        let edges: Vec<(char, char)> = edges.map(|(n, m)| (*n, *m)).collect();
        assert_eq!(
            edges,
            vec![('b', 'b'), ('b', 'c'), ('c', 'a'), ('a', 'b'), ('a', 'a')]
        );
    }
}
