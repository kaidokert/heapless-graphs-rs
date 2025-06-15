use crate::{
    containers::maps::MapTrait,
    graph::{Graph, GraphError, NodeIndex},
};

/// A bit-packed adjacency matrix with arbitrary node indices
///
/// This struct combines a [`crate::matrix::bit_matrix::BitMatrix`] for efficient edge storage with an index map
/// that allows arbitrary node indices. It provides the same memory efficiency as
/// BitMatrix while supporting non-contiguous node identifiers.
pub struct BitMapMatrix<const N: usize, const R: usize, NI, M>
where
    NI: NodeIndex,
    M: MapTrait<NI, usize>,
{
    bitmap: super::bit_matrix::BitMatrix<N, R>,
    index_map: M,
    phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, const R: usize, NI, M> BitMapMatrix<N, R, NI, M>
where
    NI: NodeIndex,
    M: MapTrait<NI, usize>,
{
    /// Creates a new BitMapMatrix with the given bitmap and index mapping
    ///
    /// Validates that all indices in the index_map are within valid bounds for the BitMatrix.
    /// BitMatrix supports node indices in the range 0..8*N.
    pub fn new(
        bitmap: super::bit_matrix::BitMatrix<N, R>,
        index_map: M,
    ) -> Result<Self, GraphError<NI>> {
        // BitMatrix supports indices in range 0..8*N
        let max_valid_index = 8 * N;
        for (node, idx) in index_map.iter() {
            if *idx >= max_valid_index {
                return Err(GraphError::IndexOutOfBounds(*idx, *node));
            }
        }
        Ok(Self::new_unchecked(bitmap, index_map))
    }

    /// Creates a new BitMapMatrix with the given bitmap and index mapping without bounds checking
    ///
    /// # Safety
    /// The caller must ensure that all indices in the index_map are within valid bounds
    /// for the BitMatrix (0..8*N).
    pub fn new_unchecked(bitmap: super::bit_matrix::BitMatrix<N, R>, index_map: M) -> Self {
        Self {
            bitmap,
            index_map,
            phantom: core::marker::PhantomData,
        }
    }
}

impl<const N: usize, const R: usize, NI, M> Graph<NI> for BitMapMatrix<N, R, NI, M>
where
    NI: NodeIndex,
    M: MapTrait<NI, usize>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.index_map.iter().map(|(&k, _)| k))
    }

    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.index_map.contains_key(&node))
    }

    /// Note: Uses linear search for backindexing matrix indices to NI, this is slow.
    ///
    /// TODO: Store back-index ?
    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self
            .index_map
            .iter()
            .flat_map(move |(&from_node, &from_idx)| {
                self.index_map
                    .iter()
                    .filter_map(move |(&to_node, &to_idx)| {
                        if self.bitmap.get(from_idx, to_idx) {
                            Some((from_node, to_node))
                        } else {
                            None
                        }
                    })
            }))
    }

    /// Note: Uses linear search for backindexing matrix indices to NI, this is slow.
    ///
    /// TODO: Store back-index ?
    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Fast direct lookup of matrix index for this node
        let matrix_idx = self.index_map.get(&node).copied();

        // Get outgoing edges from bitmap, using usize::MAX as fallback (will be filtered out)
        // Note: BitMatrix::get handles out-of-bounds indices safely by returning false,
        // and the filter below ensures we don't return edges for non-existent nodes.
        // The map_err is needed to convert GraphError<usize> to GraphError<NI> for the trait implementation.
        let outgoing = self
            .bitmap
            .outgoing_edges(matrix_idx.unwrap_or(usize::MAX))
            .map_err(|_| GraphError::NodeNotFound(node))?;

        // Map matrix indices back to node indices by checking all nodes
        Ok(outgoing
            .filter(move |_| matrix_idx.is_some()) // Filter out everything if node doesn't exist
            .filter_map(move |target_idx| {
                self.index_map
                    .iter()
                    .find(|(_, &idx)| idx == target_idx)
                    .map(|(&node, _)| node)
            }))
    }

    /// Note: Uses linear search for backindexing matrix indices to NI, this is slow.
    ///
    /// TODO: Store back-index ?
    fn incoming_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Fast direct lookup of matrix index for this node
        let matrix_idx = self.index_map.get(&node).copied();

        // Get incoming edges from bitmap, using 0 as fallback (will be filtered out)
        let incoming = self
            .bitmap
            .incoming_edges(matrix_idx.unwrap_or(usize::MAX))
            .map_err(|_| GraphError::NodeNotFound(node))?;

        // Map matrix indices back to node indices by checking all nodes
        Ok(incoming
            .filter(move |_| matrix_idx.is_some()) // Filter out everything if node doesn't exist
            .filter_map(move |source_idx| {
                self.index_map
                    .iter()
                    .find(|(_, &idx)| idx == source_idx)
                    .map(|(&node, _)| node)
            }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::tests::collect;

    #[test]
    fn test_bit_map_matrix_basic() {
        // Create a simple 2x2 bit matrix with edges: 0->0, 0->1, 1->0
        let bits = [
            [0b00000011u8], // Row 0: edges to nodes 0 and 1
            [0b00000001u8], // Row 1: edge to node 0
            [0b00000000u8], // Row 2: no edges
            [0b00000000u8], // Row 3: no edges
            [0b00000000u8], // Row 4: no edges
            [0b00000000u8], // Row 5: no edges
            [0b00000000u8], // Row 6: no edges
            [0b00000000u8], // Row 7: no edges
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);

        // Map custom node IDs 'A','B' to matrix indices 0,1
        let mut index_map = Dictionary::<char, usize, 8>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Test node iteration
        let mut nodes = ['\0'; 8];
        let nodes_slice = collect(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice.len(), 2);

        // Check both nodes are present (order may vary)
        assert!(nodes_slice.contains(&'A'));
        assert!(nodes_slice.contains(&'B'));

        // Test contains_node
        assert!(bit_map_matrix.contains_node('A').unwrap());
        assert!(bit_map_matrix.contains_node('B').unwrap());
        assert!(!bit_map_matrix.contains_node('C').unwrap());

        // Test outgoing edges
        let mut outgoing_a = ['\0'; 8];
        let outgoing_slice = collect(bit_map_matrix.outgoing_edges('A').unwrap(), &mut outgoing_a);
        assert_eq!(outgoing_slice.len(), 2); // A->A, A->B

        let mut outgoing_b = ['\0'; 8];
        let outgoing_slice = collect(bit_map_matrix.outgoing_edges('B').unwrap(), &mut outgoing_b);
        assert_eq!(outgoing_slice, &['A']); // B->A
    }

    #[test]
    fn test_bit_map_matrix_empty() {
        // Empty bitmap
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);

        // Empty index map
        let index_map = Dictionary::<u32, usize, 8>::new();
        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Should have no nodes
        assert_eq!(bit_map_matrix.iter_nodes().unwrap().count(), 0);

        // Should have no edges
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 0);

        // Should not contain any nodes
        assert!(!bit_map_matrix.contains_node(42).unwrap());
    }

    #[test]
    fn test_bit_map_matrix_nonexistent_node() {
        let bits = [
            [0b00000001u8], // Row 0: edge to node 0
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);

        let mut index_map = Dictionary::<u32, usize, 8>::new();
        index_map.insert(100, 0).unwrap();

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Test outgoing edges for non-existent node should return empty iterator
        assert_eq!(bit_map_matrix.outgoing_edges(999).unwrap().count(), 0);

        // Test incoming edges for non-existent node should return empty iterator
        assert_eq!(bit_map_matrix.incoming_edges(999).unwrap().count(), 0);
    }

    #[test]
    fn test_bit_map_matrix_incoming_edges() {
        // Create a matrix with edges: A->A, A->B, B->A
        let bits = [
            [0b00000011u8], // Row 0: edges to nodes 0 and 1 (A->A, A->B)
            [0b00000001u8], // Row 1: edge to node 0 (B->A)
            [0b00000000u8], // Row 2: no edges
            [0b00000000u8], // Row 3: no edges
            [0b00000000u8], // Row 4: no edges
            [0b00000000u8], // Row 5: no edges
            [0b00000000u8], // Row 6: no edges
            [0b00000000u8], // Row 7: no edges
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);

        // Map custom node IDs 'A','B' to matrix indices 0,1
        let mut index_map = Dictionary::<char, usize, 8>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Test incoming edges to A (should be from A and B)
        let mut incoming_a = ['\0'; 8];
        let incoming_slice = collect(bit_map_matrix.incoming_edges('A').unwrap(), &mut incoming_a);
        assert_eq!(incoming_slice.len(), 2); // A->A, B->A
        assert!(incoming_slice.contains(&'A'));
        assert!(incoming_slice.contains(&'B'));

        // Test incoming edges to B (should be from A only)
        let mut incoming_b = ['\0'; 8];
        let incoming_slice = collect(bit_map_matrix.incoming_edges('B').unwrap(), &mut incoming_b);
        assert_eq!(incoming_slice, &['A']); // A->B
    }

    #[test]
    fn test_bit_map_matrix_outgoing_edges_bounds() {
        // Create a matrix with edges: A->A, A->B
        let bits = [
            [0b00000011u8], // Row 0: edges to nodes 0 and 1 (A->A, A->B)
            [0b00000000u8], // Row 1: no edges
            [0b00000000u8], // Row 2: no edges
            [0b00000000u8], // Row 3: no edges
            [0b00000000u8], // Row 4: no edges
            [0b00000000u8], // Row 5: no edges
            [0b00000000u8], // Row 6: no edges
            [0b00000000u8], // Row 7: no edges
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);

        // Map custom node IDs 'A','B' to matrix indices 0,1
        let mut index_map = Dictionary::<char, usize, 8>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Test outgoing edges for non-existent node with usize::MAX fallback
        // This should not panic and should return an empty iterator
        let mut outgoing = ['\0'; 8];
        let outgoing_slice = collect(bit_map_matrix.outgoing_edges('C').unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice.len(), 0);

        // Test outgoing edges for non-existent node with 0 fallback
        // This should also not panic and should return an empty iterator
        let mut outgoing = ['\0'; 8];
        let outgoing_slice = collect(bit_map_matrix.outgoing_edges('D').unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice.len(), 0);
    }
}
