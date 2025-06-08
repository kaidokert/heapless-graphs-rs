use crate::graph::{GraphError, GraphVal};

// Store edges in bits
pub struct BitMatrix<const N: usize> {
    bits: [[u8; N]; 8], // 8 rows, each with N columns
}

impl<const N: usize> BitMatrix<N> {
    pub fn new(bits: [[u8; N]; 8]) -> Self {
        Self { bits }
    }

    fn get(&self, row: usize, col: usize) -> bool {
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
        let iter = (0..8)
            .flat_map(move |row| (0..8 * N).map(move |col| (row, col)))
            .filter(move |(row, col)| self.get(*row, *col));
        Ok(iter)
    }

    fn outgoing_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..8 * N).filter(move |&col| self.get(node, col)))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_bit_matrix_basic() {
        let bits = [
            [0b00001011u8], // 0->0, 0->1, 0->3
            [0b00000000u8], // 1-> no outgoing edges
            [0b00000010u8], // 2->1
            [0b00000100u8], // 3->2
            [0b00000000u8], // 4-> no outgoing edges
            [0b00000001u8], // 5->0
            [0b00000000u8], // 6-> no outgoing edges
            [0b00000000u8], // 7-> no outgoing edges
        ];

        let matrix = BitMatrix::new(bits);

        // Test nodes iteration
        let mut nodes = [0usize; 16];
        let mut count = 0;
        for node in matrix.iter_nodes().unwrap() {
            nodes[count] = node;
            count += 1;
        }
        assert_eq!(count, 8);
        assert_eq!(&nodes[..count], &[0, 1, 2, 3, 4, 5, 6, 7]);

        // Test edges iteration
        let mut edges = [(0usize, 0usize); 16];
        count = 0;
        for (src, dst) in matrix.iter_edges().unwrap() {
            edges[count] = (src, dst);
            count += 1;
        }
        assert_eq!(count, 6);
        let expected_edges = [(0, 0), (0, 1), (0, 3), (2, 1), (3, 2), (5, 0)];
        assert_eq!(&edges[..count], &expected_edges);

        // Test outgoing edges for node 0
        let mut outgoing_0 = [0usize; 8];
        count = 0;
        for target in matrix.outgoing_edges(0).unwrap() {
            outgoing_0[count] = target;
            count += 1;
        }
        assert_eq!(count, 3);
        assert_eq!(&outgoing_0[..count], &[0, 1, 3]);

        // Test outgoing edges for node 1 (should be empty)
        count = 0;
        for _target in matrix.outgoing_edges(1).unwrap() {
            count += 1;
        }
        assert_eq!(count, 0);

        // Test outgoing edges for node 2
        let mut outgoing_2 = [0usize; 8];
        count = 0;
        for target in matrix.outgoing_edges(2).unwrap() {
            outgoing_2[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(&outgoing_2[..count], &[1]);

        // Test outgoing edges for node 5
        let mut outgoing_5 = [0usize; 8];
        count = 0;
        for target in matrix.outgoing_edges(5).unwrap() {
            outgoing_5[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(&outgoing_5[..count], &[0]);
    }

    #[test]
    fn test_bit_matrix_get() {
        let bits = [
            [0b00000101u8], // 0->0, 0->2
            [0b00000010u8], // 1->1
            [0b00000000u8], // 2-> no edges
            [0b00000000u8], // 3-> no edges
            [0b00000000u8], // 4-> no edges
            [0b00000000u8], // 5-> no edges
            [0b00000000u8], // 6-> no edges
            [0b00000000u8], // 7-> no edges
        ];

        let matrix = BitMatrix::new(bits);

        // Test get method
        assert!(matrix.get(0, 0)); // 0->0 exists
        assert!(!matrix.get(0, 1)); // 0->1 doesn't exist
        assert!(matrix.get(0, 2)); // 0->2 exists
        assert!(!matrix.get(0, 3)); // 0->3 doesn't exist

        assert!(!matrix.get(1, 0)); // 1->0 doesn't exist
        assert!(matrix.get(1, 1)); // 1->1 exists
        assert!(!matrix.get(1, 2)); // 1->2 doesn't exist

        assert!(!matrix.get(2, 0)); // 2->0 doesn't exist
        assert!(!matrix.get(2, 1)); // 2->1 doesn't exist
    }

    #[test]
    fn test_bit_matrix_empty() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];

        let matrix = BitMatrix::new(bits);

        // Test that empty matrix has nodes but no edges
        let mut nodes = [0usize; 16];
        let mut count = 0;
        for node in matrix.iter_nodes().unwrap() {
            nodes[count] = node;
            count += 1;
        }
        assert_eq!(count, 8);
        assert_eq!(&nodes[..count], &[0, 1, 2, 3, 4, 5, 6, 7]);

        // Test that there are no edges
        count = 0;
        for _edge in matrix.iter_edges().unwrap() {
            count += 1;
        }
        assert_eq!(count, 0);

        // Test that all outgoing edge lists are empty
        for node in 0..8 {
            count = 0;
            for _target in matrix.outgoing_edges(node).unwrap() {
                count += 1;
            }
            assert_eq!(count, 0);
        }
    }
}
