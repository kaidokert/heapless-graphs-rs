use crate::graph::{GraphError, GraphVal};

pub struct BitMatrix<const N: usize> {
    bits: [[u8; N]; 8], // 8 rows, each with N columns
}

impl<const N: usize> BitMatrix<N> {
    pub fn new(bits: [[u8; N]; 8]) -> Self {
        Self { bits }
    }

    pub fn get(&self, row: usize, col: usize) -> bool {
        let byte_col = col / 8;
        let bit_col = col % 8;
        (self.bits[row][byte_col] & (1 << bit_col)) != 0
    }
}

impl<const N: usize> GraphVal<usize> for BitMatrix<N> {
    type Error = GraphError<usize>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok(0..8 * N)
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (usize, usize)>, Self::Error> {
        let row_iter = 0..8;
        let col_iter = 0..8;
        let iter = row_iter
            .flat_map(move |row| col_iter.clone().map(move |col| (row, col)))
            .filter(move |(row, col)| self.get(*row, *col));

        Ok(iter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_matrix() {
        let bits = [
            [0b00001011u8], // 0->0, 0->1, 0->3
            [0b00000000u8],
            [0b00000010u8], // 2->1
            [0b00000100u8], // 3->2
            [0b00000000u8],
            [0b00000001u8], // 5->0
            [0b00000000u8],
            [0b00000000u8],
        ];
        let matrix = BitMatrix::new(bits);
        let nodes = matrix.iter_nodes().unwrap();
        let values = nodes.collect::<Vec<_>>();
        assert_eq!(values, vec![0, 1, 2, 3, 4, 5, 6, 7]);

        // test edges
        let edges = matrix.iter_edges().unwrap();
        let values = edges.collect::<Vec<_>>();
        // edges we expect: 0->0, 0->1, 0->3, 3->1 and that's it
        assert_eq!(values, vec![(0, 0), (0, 1), (0, 3), (2, 1), (3, 2), (5, 0)]);
    }
}
