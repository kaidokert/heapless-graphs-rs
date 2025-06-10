use crate::graph::{GraphError, GraphVal};

// Store edges in bits
pub struct BitMatrix<const N: usize> {
    bits: [[u8; N]; 8], // 8 rows, each with N columns
}

impl<const N: usize> BitMatrix<N> {
    pub fn new(bits: [[u8; N]; 8]) -> Self {
        Self { bits }
    }

    pub(super) fn get(&self, row: usize, col: usize) -> bool {
        if row >= 8 || col >= 8 * N {
            return false;
        }
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

    fn incoming_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..8 * N).filter(move |&row| self.get(row, node)))
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::tests::collect;

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
    fn test_bit_matrix_bounds_checking() {
        let bits = [
            [0b00000001u8], // 0->0 exists
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];

        let matrix = BitMatrix::new(bits);

        // Test valid bounds
        assert!(matrix.get(0, 0)); // Should be true
        assert!(!matrix.get(0, 1)); // Should be false
        assert!(!matrix.get(7, 7)); // Last valid position, should be false

        // Test row out of bounds
        assert!(!matrix.get(8, 0)); // Row 8 is out of bounds (max is 7)
        assert!(!matrix.get(100, 0)); // Way out of bounds
        assert!(!matrix.get(usize::MAX, 0)); // Maximum value

        // Test column out of bounds (8*N = 8*1 = 8, so max valid col is 7)
        assert!(!matrix.get(0, 8)); // Column 8 is out of bounds
        assert!(!matrix.get(0, 100)); // Way out of bounds
        assert!(!matrix.get(0, usize::MAX)); // Maximum value

        // Test both row and column out of bounds
        assert!(!matrix.get(8, 8));
        assert!(!matrix.get(usize::MAX, usize::MAX));
    }

    #[test]
    fn test_bit_matrix_outgoing_edges_bounds() {
        let bits = [
            [0b00000011u8], // 0->0, 0->1
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];

        let matrix = BitMatrix::new(bits);

        // Test outgoing edges for valid nodes
        let mut outgoing_0 = [0usize; 8];
        let mut count = 0;
        for target in matrix.outgoing_edges(0).unwrap() {
            outgoing_0[count] = target;
            count += 1;
        }
        assert_eq!(count, 2);
        assert_eq!(&outgoing_0[..count], &[0, 1]);

        // Test outgoing edges for out-of-bounds nodes should return empty
        assert_eq!(matrix.outgoing_edges(8).unwrap().count(), 0); // Node 8 is out of bounds
        assert_eq!(matrix.outgoing_edges(100).unwrap().count(), 0); // Node 100 is way out of bounds
        assert_eq!(matrix.outgoing_edges(usize::MAX).unwrap().count(), 0); // usize::MAX should not panic
    }

    #[test]
    fn test_bit_matrix_all_edges_set() {
        // Test a matrix where all possible edges are set
        let bits = [
            [0b11111111u8], // All 8 edges from node 0
            [0b11111111u8], // All 8 edges from node 1
            [0b11111111u8], // All 8 edges from node 2
            [0b11111111u8], // All 8 edges from node 3
            [0b11111111u8], // All 8 edges from node 4
            [0b11111111u8], // All 8 edges from node 5
            [0b11111111u8], // All 8 edges from node 6
            [0b11111111u8], // All 8 edges from node 7
        ];

        let matrix = BitMatrix::new(bits);

        // Should have 8 nodes
        assert_eq!(matrix.iter_nodes().unwrap().count(), 8);

        // Should have 8*8 = 64 edges
        assert_eq!(matrix.iter_edges().unwrap().count(), 64);

        // Each node should have 8 outgoing edges
        for node in 0..8 {
            assert_eq!(matrix.outgoing_edges(node).unwrap().count(), 8);
        }

        // Test specific edge checks
        for row in 0..8 {
            for col in 0..8 {
                assert!(matrix.get(row, col), "Edge {}->{} should exist", row, col);
            }
        }
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
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);

        // Test that all outgoing edge lists are empty
        for node in 0..8 {
            assert_eq!(matrix.outgoing_edges(node).unwrap().count(), 0);
        }
    }

    #[test]
    fn test_bit_matrix_multi_byte() {
        // Test with N=2, so we have 8*2=16 columns requiring 2 bytes per row
        let bits = [
            [0b00000001u8, 0b10000000u8], // 0->0, 0->15 (spans both bytes)
            [0b11110000u8, 0b00001111u8], // 1->4,5,6,7,8,9,10,11 (spans both bytes)
            [0b00000000u8, 0b00000000u8], // 2-> no edges
            [0b01010101u8, 0b10101010u8], // 3->0,2,4,6,9,11,13,15 (alternating pattern)
            [0b00000000u8, 0b00000000u8], // 4-> no edges
            [0b00000000u8, 0b00000000u8], // 5-> no edges
            [0b00000000u8, 0b00000000u8], // 6-> no edges
            [0b00000000u8, 0b00000000u8], // 7-> no edges
        ];

        let matrix = BitMatrix::new(bits);

        // Should have 16 nodes (8*2)
        assert_eq!(matrix.iter_nodes().unwrap().count(), 16);

        // Test specific edge existence across byte boundaries
        assert!(matrix.get(0, 0)); // First bit of first byte
        assert!(matrix.get(0, 15)); // Last bit of second byte
        assert!(!matrix.get(0, 1)); // Should be false
        assert!(!matrix.get(0, 14)); // Should be false

        // Test row 1 with pattern spanning both bytes
        assert!(!matrix.get(1, 0)); // First 4 bits should be 0
        assert!(!matrix.get(1, 1));
        assert!(!matrix.get(1, 2));
        assert!(!matrix.get(1, 3));
        assert!(matrix.get(1, 4)); // Next 4 bits should be 1
        assert!(matrix.get(1, 5));
        assert!(matrix.get(1, 6));
        assert!(matrix.get(1, 7));
        assert!(matrix.get(1, 8)); // First 4 bits of second byte should be 1
        assert!(matrix.get(1, 9));
        assert!(matrix.get(1, 10));
        assert!(matrix.get(1, 11));
        assert!(!matrix.get(1, 12)); // Last 4 bits should be 0
        assert!(!matrix.get(1, 13));
        assert!(!matrix.get(1, 14));
        assert!(!matrix.get(1, 15));

        // Test alternating pattern in row 3: 0b01010101, 0b10101010
        // Let's test each bit individually to verify the pattern
        assert!(matrix.get(3, 0)); // 0b01010101 bit 0 = 1
        assert!(!matrix.get(3, 1)); // 0b01010101 bit 1 = 0
        assert!(matrix.get(3, 2)); // 0b01010101 bit 2 = 1
        assert!(!matrix.get(3, 3)); // 0b01010101 bit 3 = 0
        assert!(matrix.get(3, 4)); // 0b01010101 bit 4 = 1
        assert!(!matrix.get(3, 5)); // 0b01010101 bit 5 = 0
        assert!(matrix.get(3, 6)); // 0b01010101 bit 6 = 1
        assert!(!matrix.get(3, 7)); // 0b01010101 bit 7 = 0

        assert!(!matrix.get(3, 8)); // 0b10101010 bit 0 = 0
        assert!(matrix.get(3, 9)); // 0b10101010 bit 1 = 1
        assert!(!matrix.get(3, 10)); // 0b10101010 bit 2 = 0
        assert!(matrix.get(3, 11)); // 0b10101010 bit 3 = 1
        assert!(!matrix.get(3, 12)); // 0b10101010 bit 4 = 0
        assert!(matrix.get(3, 13)); // 0b10101010 bit 5 = 1
        assert!(!matrix.get(3, 14)); // 0b10101010 bit 6 = 0
        assert!(matrix.get(3, 15)); // 0b10101010 bit 7 = 1

        // Test outgoing edges counts
        assert_eq!(matrix.outgoing_edges(0).unwrap().count(), 2); // 0->0, 0->15
        assert_eq!(matrix.outgoing_edges(1).unwrap().count(), 8); // 8 edges spanning bytes
        assert_eq!(matrix.outgoing_edges(2).unwrap().count(), 0); // No edges
        assert_eq!(matrix.outgoing_edges(3).unwrap().count(), 8); // Alternating pattern = 8 edges

        // Test bounds checking with 16 columns
        assert!(!matrix.get(0, 16)); // Column 16 should be out of bounds
        assert!(!matrix.get(0, 100)); // Way out of bounds
        assert_eq!(matrix.outgoing_edges(8).unwrap().count(), 0); // Row 8 out of bounds
    }

    #[test]
    fn test_incoming_edges() {
        let bits = [
            [0b00000010u8], // 0->1
            [0b00000100u8], // 1->2
            [0b00000001u8], // 2->0
            [0b00000010u8], // 3->1
            [0b00000000u8], // 4-> no edges
            [0b00000000u8], // 5-> no edges
            [0b00000000u8], // 6-> no edges
            [0b00000000u8], // 7-> no edges
        ];
        let matrix = BitMatrix::new(bits);

        // Test node 0's incoming edges (should be from node 2)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2]);

        // Test node 1's incoming edges (should be from nodes 0 and 3)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(1).unwrap(), &mut edges);
        edges_slice.sort_unstable();
        assert_eq!(edges_slice, &[0, 3]);

        // Test node 2's incoming edges (should be from node 1)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[1]);

        // Test node 3's incoming edges (should be empty)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(3).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[]);
    }

    #[test]
    fn test_incoming_edges_empty() {
        let bits = [
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
        ];
        let matrix = BitMatrix::new(bits);

        // Test all nodes have no incoming edges in an empty matrix
        for node in 0..4 {
            let mut edges = [0usize; 4];
            let edges_slice = collect(matrix.incoming_edges(node).unwrap(), &mut edges);
            assert_eq!(edges_slice, &[]);
        }
    }

    #[test]
    fn test_incoming_edges_self_loops() {
        let bits = [
            [0b00000001u8], // 0->0
            [0b00000000u8], // no edges
            [0b00000100u8], // 2->2
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
        ];
        let matrix = BitMatrix::new(bits);

        // Test node 0's incoming edges (should include self-loop)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0]);

        // Test node 2's incoming edges (should include self-loop)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(2).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2]);

        // Test nodes 1 and 3 have no incoming edges
        for node in [1, 3] {
            let mut edges = [0usize; 4];
            let edges_slice = collect(matrix.incoming_edges(node).unwrap(), &mut edges);
            assert_eq!(edges_slice, &[]);
        }
    }

    #[test]
    fn test_incoming_edges_multiple_incoming() {
        let bits = [
            [0b00000010u8], // 0->1
            [0b00000000u8], // no edges
            [0b00000010u8], // 2->1
            [0b00000010u8], // 3->1
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
            [0b00000000u8], // no edges
        ];
        let matrix = BitMatrix::new(bits);

        // Test node 1's incoming edges
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(1).unwrap(), &mut edges);
        edges_slice.sort_unstable();
        assert_eq!(edges_slice, &[0, 2, 3]);
    }
}
