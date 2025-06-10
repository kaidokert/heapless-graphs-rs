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

    pub(crate) fn get_edge_value(&self, row: usize, col: usize) -> Option<&EDGEVALUE> {
        self.matrix.as_ref().get(row)?.as_ref().get(col)?.as_ref()
    }
}

// Note: Implementing GraphRef isn't practical, there's no way to iterate over node refs without
// storage for them.

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

    /// Optimized O(V) outgoing_edges for matrix
    fn outgoing_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..N).filter_map(move |col_index| {
            if node < N {
                self.matrix
                    .as_ref()
                    .get(node)?
                    .as_ref()
                    .get(col_index)?
                    .as_ref()
                    .map(|_| col_index)
            } else {
                None
            }
        }))
    }

    /// Optimized O(V) incoming_edges for matrix
    fn incoming_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..N).filter_map(move |row_index| {
            if node < N {
                self.matrix
                    .as_ref()
                    .get(row_index)?
                    .as_ref()
                    .get(node)?
                    .as_ref()
                    .map(|_| row_index)
            } else {
                None
            }
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::collect;

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

        let mut nodes = [0usize; 8];
        let mut len = 0;
        for node in matrix.iter_nodes().unwrap() {
            nodes[len] = node;
            len += 1;
        }
        assert_eq!(len, 3);
        assert_eq!(&nodes[..len], &[0, 1, 2]);

        // Test with different size
        let matrix = Matrix::<5, i32, _, _>::new([
            [Some(1), Some(2), Some(3), Some(4), Some(5)],
            [Some(6), Some(7), Some(8), Some(9), Some(10)],
            [Some(11), Some(12), Some(13), Some(14), Some(15)],
            [Some(16), Some(17), Some(18), Some(19), Some(20)],
            [Some(21), Some(22), Some(23), Some(24), Some(25)],
        ]);

        let mut nodes = [0usize; 8];
        let mut len = 0;
        for node in matrix.iter_nodes().unwrap() {
            nodes[len] = node;
            len += 1;
        }
        assert_eq!(len, 5);
        assert_eq!(&nodes[..len], &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn sparse_edges() {
        let matrix = Matrix::<3, _, _, _>::new([
            [None, Some('b'), None],
            [Some('t'), None, Some('z')],
            [None, Some('x'), Some('f')],
        ]);

        let mut edges = [(0usize, 0usize); 10];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]);
    }

    #[test]
    fn test_incoming_edges() {
        let matrix = Matrix::<3, _, _, _>::new([
            [None, Some('b'), None],
            [Some('t'), None, Some('z')],
            [None, Some('x'), Some('f')],
        ]);

        // Test node 0 (has incoming edge from node 1)
        let mut incoming = [0usize; 10];
        let incoming_slice = collect(matrix.incoming_edges(0).unwrap(), &mut incoming);
        assert_eq!(incoming_slice, &[1]);

        // Test node 1 (has incoming edges from nodes 0 and 2)
        let incoming_slice = collect(matrix.incoming_edges(1).unwrap(), &mut incoming);
        assert_eq!(incoming_slice, &[0, 2]);

        // Test node 2 (has incoming edges from nodes 1 and 2)
        let incoming_slice = collect(matrix.incoming_edges(2).unwrap(), &mut incoming);
        assert_eq!(incoming_slice, &[1, 2]);

        // Test invalid node index
        let incoming_slice = collect(matrix.incoming_edges(3).unwrap(), &mut incoming);
        assert_eq!(incoming_slice, &[]);
    }
}
