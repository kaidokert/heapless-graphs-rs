use crate::graph::{GraphError, GraphVal};

pub struct Matrix<const N: usize, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    matrix: COLUMNS,
    _phantom: core::marker::PhantomData<(EDGEVALUE, ROW)>,
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> Matrix<N, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    pub fn new(matrix: COLUMNS) -> Self {
        Self {
            matrix,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> GraphVal<usize> for Matrix<N, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    type Error = GraphError<usize>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok(0..N)
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (usize, usize)>, Self::Error> {
        Ok(self
            .matrix
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
            }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matrix() {
        let _matrix = Matrix::<3, i32, _, _>::new([
            [Some(1), Some(2), Some(3)],
            [Some(4), Some(5), Some(6)],
            [Some(7), Some(8), Some(9)],
        ]);
    }

    #[test]
    fn test_iter_nodes() {
        let matrix = Matrix::<3, i32, _, _>::new([
            [Some(1), Some(2), Some(3)],
            [Some(4), Some(5), Some(6)],
            [Some(7), Some(8), Some(9)],
        ]);

        let nodes: Vec<usize> = matrix.iter_nodes().unwrap().collect();
        assert_eq!(nodes, vec![0, 1, 2]);

        // Test with different size
        let matrix = Matrix::<5, i32, _, _>::new([
            [Some(1), Some(2), Some(3), Some(4), Some(5)],
            [Some(6), Some(7), Some(8), Some(9), Some(10)],
            [Some(11), Some(12), Some(13), Some(14), Some(15)],
            [Some(16), Some(17), Some(18), Some(19), Some(20)],
            [Some(21), Some(22), Some(23), Some(24), Some(25)],
        ]);

        let nodes: Vec<usize> = matrix.iter_nodes().unwrap().collect();
        assert_eq!(nodes, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn sparse_edges() {
        let matrix = Matrix::<3, _, _, _>::new([
            [None, Some('b'), None],
            [Some('t'), None, Some('z')],
            [None, Some('x'), Some('f')],
        ]);

        let edges: Vec<(usize, usize)> = matrix.iter_edges().unwrap().collect();
        assert_eq!(edges, vec![(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]);
    }
}
