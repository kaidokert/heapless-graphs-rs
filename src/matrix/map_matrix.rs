use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, GraphRef, GraphVal, NodeIndexTrait},
};

pub struct MapMatrix<'a, const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait + 'a,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, &'a NI>,
{
    inner: super::simple_matrix::Matrix<N, EDGEVALUE, COLUMNS, ROW>,
    index_map: M,
    phantom: core::marker::PhantomData<&'a NI>,
}

impl<'a, const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW>
    MapMatrix<'a, N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait + 'a,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, &'a NI>,
{
    pub fn new_from_node_indices(matrix: COLUMNS, mut map: M, node_indices: &'a [NI]) -> Self {
        map.clear();
        for (i, node_index) in node_indices.iter().enumerate() {
            map.insert(i, node_index);
        }
        Self {
            inner: super::simple_matrix::Matrix::new(matrix),
            index_map: map,
            phantom: core::marker::PhantomData,
        }
    }
}

impl<'a, const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> GraphRef<NI>
    for MapMatrix<'a, N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait + core::fmt::Debug + 'a,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, &'a NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'b>(&'b self) -> Result<impl Iterator<Item = &'b NI>, Self::Error>
    where
        'a: 'b,
    {
        Ok(self.index_map.iter().map(|(_, v)| *v))
    }

    fn iter_edges<'b>(&'b self) -> Result<impl Iterator<Item = (&'b NI, &'b NI)>, Self::Error>
    where
        'a: 'b,
    {
        Ok(self.inner.iter_edges().unwrap().map(|(i, j)| {
            let n = self.index_map.get(&i).unwrap();
            let m = self.index_map.get(&j).unwrap();
            (*n, *m)
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
        let array_data = [
            [Some(true), Some(true), None],
            [None, None, Some(false)],
            [Some(false), None, Some(true)],
        ];
        let map_matrix: MapMatrix<3, _, _, _, _, _> = MapMatrix::new_from_node_indices(
            array_data,
            Dictionary::<_, _, 71>::new(),
            &['b', 'c', 'a'],
        );

        let inner = map_matrix.inner.iter_nodes().unwrap();
        let nodes: Vec<usize> = inner.collect();
        assert_eq!(nodes, vec![0, 1, 2]);

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
