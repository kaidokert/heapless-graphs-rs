use crate::graph::{Graph, GraphError, GraphWithMutableEdges};

/// A space-efficient adjacency matrix implementation using bit-level storage.
///
/// `BitMatrix` represents a directed graph using a bit-packed adjacency matrix.
/// Each bit in the matrix represents the presence (1) or absence (0) of an edge
/// between two nodes. This implementation is particularly memory-efficient for
/// dense graphs, as it uses only one bit per potential edge.
///
/// # Type Parameters
/// * `C` - Number of columns (bytes) per row. Each byte can store 8 edges.
/// * `R` - Number of rows in the matrix. Must equal 8 * C for valid matrices.
///
/// # Matrix Layout
/// The matrix is stored as a 2D array of bytes, where:
/// * Each row represents a source node
/// * Each byte in a row represents 8 potential target nodes
/// * The total number of nodes is 8 * C
/// * The total number of edges is (8 * C)²
///
/// # Example
/// ```
/// use heapless_graphs::matrix::bit_matrix::BitMatrix;
/// use heapless_graphs::graph::Graph;
///
/// // Create a graph with 8 nodes (1 byte per row, 8 rows)
/// let bits = [
///     [0b00000001u8], // Node 0 -> Node 0
///     [0b00000010u8], // Node 1 -> Node 1
///     [0b00000100u8], // Node 2 -> Node 2
///     [0b00001000u8], // Node 3 -> Node 3
///     [0b00010000u8], // Node 4 -> Node 4
///     [0b00100000u8], // Node 5 -> Node 5
///     [0b01000000u8], // Node 6 -> Node 6
///     [0b10000000u8], // Node 7 -> Node 7
/// ];
/// let matrix = BitMatrix::<1, 8>::new(bits).unwrap();
///
/// // Use the public Graph trait API
/// let nodes: Vec<_> = matrix.iter_nodes().unwrap().collect();
/// assert_eq!(nodes, vec![0, 1, 2, 3, 4, 5, 6, 7]);
/// let edges: Vec<_> = matrix.iter_edges().unwrap().collect();
/// assert_eq!(edges, vec![(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7)]);
/// ```
pub struct BitMatrix<const C: usize, const R: usize> {
    bits: [[u8; C]; R], // R rows, each with C columns
}

impl<const C: usize, const R: usize> BitMatrix<C, R> {
    /// Creates a new `BitMatrix` with validation of matrix dimensions.
    ///
    /// # Arguments
    /// * `bits` - The raw bit matrix data. Each row must have C columns of bytes.
    ///
    /// # Returns
    /// * `Ok(Self)` if R = 8*C, ensuring the matrix can represent a valid graph
    /// * `Err(GraphError::InvalidMatrixSize)` if dimensions are invalid
    ///
    /// # Example
    /// ```
    /// use heapless_graphs::matrix::bit_matrix::BitMatrix;
    ///
    /// // Valid: 8 rows, 1 column (8 = 8*1)
    /// let bits = [[0u8]; 8];
    /// assert!(BitMatrix::<1, 8>::new(bits).is_ok());
    ///
    /// // Invalid: 4 rows, 1 column (4 ≠ 8*1)
    /// let bits = [[0u8]; 4];
    /// assert!(BitMatrix::<1, 4>::new(bits).is_err());
    /// ```
    pub fn new(bits: [[u8; C]; R]) -> Result<Self, GraphError<usize>> {
        if R != 8 * C {
            return Err(GraphError::InvalidMatrixSize);
        }
        Ok(Self { bits })
    }

    /// Creates a new `BitMatrix` without dimension validation.
    ///
    /// # Safety
    /// This constructor bypasses the R = 8*C validation. The caller must ensure
    /// that the matrix dimensions are valid, otherwise the graph operations
    /// may not work as expected.
    ///
    /// # Arguments
    /// * `bits` - The raw bit matrix data. Each row must have C columns of bytes.
    pub fn new_unchecked(bits: [[u8; C]; R]) -> Self {
        Self { bits }
    }

    /// Creates a BitMatrix from any graph by copying all edges
    ///
    /// This function iterates over all edges in the source graph and adds them
    /// to a new BitMatrix. The source graph must have usize node indices in the
    /// range 0..8*C, where 8*C is the maximum number of nodes the matrix can hold.
    ///
    /// # Arguments
    /// * `source_graph` - The graph to copy edges from
    ///
    /// # Returns
    /// * `Ok(BitMatrix)` if successful
    /// * `Err(GraphError)` if any node indices are out of range or iteration fails
    ///
    /// # Constraints
    /// * Source graph nodes must be usize indices from 0 to 8*C-1
    /// * BitMatrix dimensions must satisfy R = 8*C constraint
    /// * Only edges are copied; the matrix represents 8*C nodes automatically
    ///
    /// # Example
    /// ```
    /// # use heapless_graphs::matrix::bit_matrix::BitMatrix;
    /// # use heapless_graphs::edgelist::edge_list::EdgeList;
    /// # use heapless_graphs::edges::EdgeStructOption;
    ///
    /// // Create a source graph (edge list)
    /// let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), Some((0, 2)), None]);
    /// let source = EdgeList::<4, usize, _>::new(edges);
    ///
    /// // Convert to BitMatrix (8 nodes capacity)
    /// let matrix: BitMatrix<1, 8> = BitMatrix::from_graph(&source).unwrap();
    /// ```
    pub fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<usize>>
    where
        G: Graph<usize>,
        GraphError<usize>: From<G::Error>,
    {
        // Create empty bit matrix
        let mut bits = [[0u8; C]; R];

        // Validate all nodes are within range first
        for node in source_graph.iter_nodes()? {
            if node >= 8 * C {
                return Err(GraphError::EdgeHasInvalidNode(node));
            }
        }

        // Add all edges to the matrix
        for (source, destination) in source_graph.iter_edges()? {
            // Validate bounds (should be caught above, but double-check)
            if source >= R {
                return Err(GraphError::EdgeHasInvalidNode(source));
            }
            if destination >= 8 * C {
                return Err(GraphError::EdgeHasInvalidNode(destination));
            }

            // Set the bit: source -> destination
            let byte_col = destination / 8;
            let bit_col = destination % 8;
            bits[source][byte_col] |= 1 << bit_col;
        }

        Ok(Self::new_unchecked(bits))
    }

    /// Internal: Checks if an edge exists between two nodes.
    /// Returns true if the edge exists and indices are in bounds, false otherwise.
    pub(super) fn get(&self, row: usize, col: usize) -> bool {
        if row >= R || col >= 8 * C {
            return false;
        }
        let byte_col = col / 8;
        let bit_col = col % 8;
        (self.bits[row][byte_col] & (1 << bit_col)) != 0
    }
}

impl<const C: usize, const R: usize> Graph<usize> for BitMatrix<C, R> {
    type Error = GraphError<usize>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok(0..8 * C)
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (usize, usize)>, Self::Error> {
        let iter = (0..8 * C)
            .flat_map(move |row| (0..8 * C).map(move |col| (row, col)))
            .filter(move |(row, col)| self.get(*row, *col));
        Ok(iter)
    }

    fn outgoing_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..8 * C).filter(move |&col| self.get(node, col)))
    }

    fn incoming_edges(&self, node: usize) -> Result<impl Iterator<Item = usize>, Self::Error> {
        Ok((0..8 * C).filter(move |&row| self.get(row, node)))
    }
}

impl<const C: usize, const R: usize> GraphWithMutableEdges<usize> for BitMatrix<C, R> {
    fn add_edge(&mut self, source: usize, destination: usize) -> Result<(), Self::Error> {
        // Validate bounds (nodes must exist in the matrix)
        if source >= R {
            return Err(GraphError::EdgeHasInvalidNode(source));
        }
        if destination >= 8 * C {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Set the bit: source -> destination
        let byte_col = destination / 8;
        let bit_col = destination % 8;
        self.bits[source][byte_col] |= 1 << bit_col;

        Ok(())
    }

    fn remove_edge(&mut self, source: usize, destination: usize) -> Result<(), Self::Error> {
        // Check bounds and if edge exists
        if source >= R || destination >= 8 * C || !self.get(source, destination) {
            return Err(GraphError::EdgeNotFound(source, destination));
        }

        // Clear the bit: source -> destination
        let byte_col = destination / 8;
        let bit_col = destination % 8;
        self.bits[source][byte_col] &= !(1 << bit_col);

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::tests::{collect, collect_sorted};

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

        let matrix = BitMatrix::new_unchecked(bits);

        // Test nodes iteration
        let mut nodes = [0usize; 16];
        let nodes_slice = collect(matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2, 3, 4, 5, 6, 7]);

        // Test edges iteration
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        let expected_edges = [(0, 0), (0, 1), (0, 3), (2, 1), (3, 2), (5, 0)];
        assert_eq!(edges_slice, &expected_edges);

        // Test outgoing edges for node 0
        let mut outgoing_0 = [0usize; 8];
        let outgoing_slice = collect(matrix.outgoing_edges(0).unwrap(), &mut outgoing_0);
        assert_eq!(outgoing_slice, &[0, 1, 3]);

        // Test outgoing edges for node 1 (should be empty)
        assert_eq!(matrix.outgoing_edges(1).unwrap().count(), 0);

        // Test outgoing edges for node 2
        let mut outgoing_2 = [0usize; 8];
        let outgoing_slice = collect(matrix.outgoing_edges(2).unwrap(), &mut outgoing_2);
        assert_eq!(outgoing_slice, &[1]);

        // Test outgoing edges for node 5
        let mut outgoing_5 = [0usize; 8];
        let outgoing_slice = collect(matrix.outgoing_edges(5).unwrap(), &mut outgoing_5);
        assert_eq!(outgoing_slice, &[0]);
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

        let matrix = BitMatrix::new_unchecked(bits);

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

        let matrix = BitMatrix::new_unchecked(bits);

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

        let matrix = BitMatrix::new_unchecked(bits);

        // Test outgoing edges for valid nodes
        let mut outgoing_0 = [0usize; 8];
        let outgoing_slice = collect(matrix.outgoing_edges(0).unwrap(), &mut outgoing_0);
        assert_eq!(outgoing_slice, &[0, 1]);

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

        let matrix = BitMatrix::new_unchecked(bits);

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

        let matrix = BitMatrix::new_unchecked(bits);

        // Test that empty matrix has nodes but no edges
        let mut nodes = [0usize; 16];
        let nodes_slice = collect(matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2, 3, 4, 5, 6, 7]);

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

        let matrix = BitMatrix::new_unchecked(bits);

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
        let matrix = BitMatrix::new_unchecked(bits);

        // Test node 0's incoming edges (should be from node 2)
        let mut edges = [0usize; 4];
        let edges_slice = collect(matrix.incoming_edges(0).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[2]);

        // Test node 1's incoming edges (should be from nodes 0 and 3)
        let mut edges = [0usize; 4];
        let edges_slice = collect_sorted(matrix.incoming_edges(1).unwrap(), &mut edges);
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
        let matrix = BitMatrix::new_unchecked(bits);

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
        let matrix = BitMatrix::new_unchecked(bits);

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
        let matrix = BitMatrix::new_unchecked(bits);

        // Test node 1's incoming edges
        let mut edges = [0usize; 4];
        let edges_slice = collect_sorted(matrix.incoming_edges(1).unwrap(), &mut edges);
        assert_eq!(edges_slice, &[0, 2, 3]);
    }

    #[test]
    fn test_bit_matrix_new_constructor() {
        // Valid case: 8 rows (R=8) and 1 column (C=1) satisfies R = 8*C
        let valid_bits = [
            [0b00000001u8],
            [0b00000010u8],
            [0b00000100u8],
            [0b00001000u8],
            [0b00010000u8],
            [0b00100000u8],
            [0b01000000u8],
            [0b10000000u8],
        ];
        assert!(BitMatrix::<1, 8>::new(valid_bits).is_ok());

        // Invalid case: 4 rows (R=4) and 1 column (C=1) does not satisfy R = 8*C
        let invalid_bits = [
            [0b00000001u8],
            [0b00000010u8],
            [0b00000100u8],
            [0b00001000u8],
        ];
        assert!(matches!(
            BitMatrix::<1, 4>::new(invalid_bits),
            Err(GraphError::InvalidMatrixSize)
        ));

        // Another valid case: 16 rows (R=16) and 2 columns (C=2) satisfies R = 8*C
        let valid_bits_2 = [
            [0b00000001u8, 0b00000000u8],
            [0b00000010u8, 0b00000000u8],
            [0b00000100u8, 0b00000000u8],
            [0b00001000u8, 0b00000000u8],
            [0b00010000u8, 0b00000000u8],
            [0b00100000u8, 0b00000000u8],
            [0b01000000u8, 0b00000000u8],
            [0b10000000u8, 0b00000000u8],
            [0b00000000u8, 0b00000001u8],
            [0b00000000u8, 0b00000010u8],
            [0b00000000u8, 0b00000100u8],
            [0b00000000u8, 0b00001000u8],
            [0b00000000u8, 0b00010000u8],
            [0b00000000u8, 0b00100000u8],
            [0b00000000u8, 0b01000000u8],
            [0b00000000u8, 0b10000000u8],
        ];
        assert!(BitMatrix::<2, 16>::new(valid_bits_2).is_ok());
    }

    #[test]
    fn test_bit_matrix_add_edge_success() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [
            [0b00000000u8], // Initially no edges
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Add edges
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(1, 2).is_ok());
        assert!(matrix.add_edge(0, 7).is_ok());

        // Verify edges were added
        assert!(matrix.get(0, 1));
        assert!(matrix.get(1, 2));
        assert!(matrix.get(0, 7));
        assert!(!matrix.get(0, 2)); // Should not exist

        // Verify edge count
        assert_eq!(matrix.iter_edges().unwrap().count(), 3);

        // Verify specific edges exist
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 7), (1, 2)]);
    }

    #[test]
    fn test_bit_matrix_add_edge_invalid_nodes() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [[0b00000000u8]; 8];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Try to add edge with invalid source (row >= R)
        let result = matrix.add_edge(8, 1);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(8))));

        // Try to add edge with invalid destination (col >= 8*C)
        let result = matrix.add_edge(0, 8);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(8))));

        // Try with way out of bounds
        let result = matrix.add_edge(100, 200);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(100))));
    }

    #[test]
    fn test_bit_matrix_remove_edge_success() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [
            [0b00001010u8], // 0->1, 0->3
            [0b00000100u8], // 1->2
            [0b00000001u8], // 2->0
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Verify initial state
        assert_eq!(matrix.iter_edges().unwrap().count(), 4);
        assert!(matrix.get(0, 1));
        assert!(matrix.get(0, 3));

        // Remove an edge
        assert!(matrix.remove_edge(0, 1).is_ok());

        // Verify edge was removed
        assert!(!matrix.get(0, 1));
        assert!(matrix.get(0, 3)); // Other edge should remain
        assert_eq!(matrix.iter_edges().unwrap().count(), 3);

        // Verify remaining edges
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 3), (1, 2), (2, 0)]);
    }

    #[test]
    fn test_bit_matrix_remove_edge_not_found() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [
            [0b00000010u8], // 0->1
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Try to remove edge that doesn't exist
        let result = matrix.remove_edge(0, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 2))));

        // Try to remove edge with invalid bounds
        let result = matrix.remove_edge(8, 1);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(8, 1))));

        // Verify original edge is still there
        assert_eq!(matrix.iter_edges().unwrap().count(), 1);
        assert!(matrix.get(0, 1));
    }

    #[test]
    fn test_bit_matrix_add_remove_edge_comprehensive() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [[0b00000000u8]; 8];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Start with empty matrix
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);

        // Add several edges
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(1, 2).is_ok());
        assert!(matrix.add_edge(2, 3).is_ok());
        assert!(matrix.add_edge(0, 3).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 4);

        // Remove some edges
        assert!(matrix.remove_edge(1, 2).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 3);

        // Try to remove the same edge again (should fail)
        let result = matrix.remove_edge(1, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(1, 2))));

        // Add the edge back
        assert!(matrix.add_edge(1, 2).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 4);

        // Verify final edge set
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 3), (1, 2), (2, 3)]);
    }

    #[test]
    fn test_bit_matrix_self_loops() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [[0b00000000u8]; 8];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Add self-loops and regular edges
        assert!(matrix.add_edge(0, 0).is_ok()); // Self-loop
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(2, 2).is_ok()); // Self-loop

        assert_eq!(matrix.iter_edges().unwrap().count(), 3);
        assert!(matrix.get(0, 0));
        assert!(matrix.get(0, 1));
        assert!(matrix.get(2, 2));

        // Remove self-loop
        assert!(matrix.remove_edge(0, 0).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 2);
        assert!(!matrix.get(0, 0));
        assert!(matrix.get(0, 1)); // Regular edge should remain
    }

    #[test]
    fn test_bit_matrix_edge_overwrite() {
        use crate::graph::GraphWithMutableEdges;

        let bits = [[0b00000000u8]; 8];
        let mut matrix = BitMatrix::new_unchecked(bits);

        // Add edge
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.get(0, 1));
        assert_eq!(matrix.iter_edges().unwrap().count(), 1);

        // Add same edge again (should be idempotent)
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.get(0, 1));
        assert_eq!(matrix.iter_edges().unwrap().count(), 1); // Still just one edge
    }

    #[test]
    fn test_bit_matrix_from_graph() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;

        // Create a source graph (map adjacency list with nodes 0, 1, 2)
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // 0 -> 1, 2
        dict.insert(1, [2, 0]).unwrap(); // 1 -> 2, 0
        dict.insert(2, [0, 1]).unwrap(); // 2 -> 0, 1
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to BitMatrix (1 column for 8 nodes: 8 = 8*1)
        let matrix: BitMatrix<1, 8> = BitMatrix::from_graph(&source).unwrap();

        // Verify nodes are represented (BitMatrix always has 0..8*C nodes)
        let node_count = matrix.iter_nodes().unwrap().count();
        assert_eq!(node_count, 8); // BitMatrix always has 8 nodes for 1 column

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]);
    }

    #[test]
    fn test_bit_matrix_from_graph_empty() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;

        // Create an empty source graph
        let dict = Dictionary::<usize, [usize; 2], 8>::default();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to BitMatrix
        let matrix: BitMatrix<1, 8> = BitMatrix::from_graph(&source).unwrap();

        // Verify no edges (but still has 8 nodes)
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);
        assert_eq!(matrix.iter_nodes().unwrap().count(), 8);
    }

    #[test]
    fn test_bit_matrix_from_graph_node_out_of_range() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;

        // Create a source graph with node index too large for 1-column matrix (8 nodes max)
        let mut dict = Dictionary::<usize, [usize; 1], 8>::new();
        dict.insert(0, [1]).unwrap();
        dict.insert(1, [8]).unwrap(); // Node 8 is out of range for 8-node matrix (0..7)
        let source = MapAdjacencyList::new_unchecked(dict);

        // Try to convert to BitMatrix with only 8 nodes (1 column)
        let result: Result<BitMatrix<1, 8>, _> = BitMatrix::from_graph(&source);

        // Should fail because node 8 is out of range
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(8))));
    }

    #[test]
    fn test_bit_matrix_from_graph_single_node() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;

        // Create a source graph with a single node and self-loop
        let mut dict = Dictionary::<usize, [usize; 1], 8>::new();
        dict.insert(5, [5]).unwrap(); // Node 5 -> 5 (self-loop)
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to BitMatrix
        let matrix: BitMatrix<1, 8> = BitMatrix::from_graph(&source).unwrap();

        // Verify self-loop edge
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(5, 5)]);

        // Verify matrix still has all 8 nodes
        assert_eq!(matrix.iter_nodes().unwrap().count(), 8);
    }

    #[test]
    fn test_bit_matrix_from_graph_larger_matrix() {
        use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
        use crate::containers::maps::staticdict::Dictionary;
        use crate::containers::maps::MapTrait;

        // Create a source graph that uses higher node indices
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(8, [9, 10]).unwrap(); // Node 8 -> 9, 10
        dict.insert(9, [10, 11]).unwrap(); // Node 9 -> 10, 11
        dict.insert(15, [8, 9]).unwrap(); // Node 15 -> 8, 9
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to BitMatrix (2 columns for 16 nodes: 16 = 8*2)
        let matrix: BitMatrix<2, 16> = BitMatrix::from_graph(&source).unwrap();

        // Verify nodes are represented (BitMatrix always has 0..16 nodes)
        let node_count = matrix.iter_nodes().unwrap().count();
        assert_eq!(node_count, 16); // BitMatrix always has 16 nodes for 2 columns

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(8, 9), (8, 10), (9, 10), (9, 11), (15, 8), (15, 9)]
        );
    }
}
