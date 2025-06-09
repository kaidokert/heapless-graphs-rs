use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, GraphVal, NodeIndexTrait},
};

/// A bit-packed adjacency matrix with arbitrary node indices
///
/// This struct combines a [`crate::matrix::bit_matrix::BitMatrix`] for efficient edge storage with an index map
/// that allows arbitrary node indices. It provides the same memory efficiency as
/// BitMatrix while supporting non-contiguous node identifiers.
pub struct BitMapMatrix<const N: usize, NI, M>
where
    NI: NodeIndexTrait,
    M: MapTrait<usize, NI>,
{
    bitmap: super::bit_matrix::BitMatrix<N>,
    index_map: M,
    phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, M> BitMapMatrix<N, NI, M>
where
    NI: NodeIndexTrait,
    M: MapTrait<usize, NI>,
{
    /// Creates a new BitMapMatrix with the given bitmap and index mapping
    pub fn new(bitmap: super::bit_matrix::BitMatrix<N>, index_map: M) -> Self {
        Self {
            bitmap,
            index_map,
            phantom: core::marker::PhantomData,
        }
    }
}

impl<const N: usize, NI, M> GraphVal<NI> for BitMapMatrix<N, NI, M>
where
    NI: NodeIndexTrait + Copy,
    M: MapTrait<usize, NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.index_map.iter().map(|(_, &v)| v))
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.bitmap.iter_edges().unwrap().filter_map(|(i, j)| {
            let n = self.index_map.get(&i)?;
            let m = self.index_map.get(&j)?;
            Some((*n, *m))
        }))
    }

    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Find the matrix index for this node
        let matrix_idx = self
            .index_map
            .iter()
            .find(|(_, &v)| v == node)
            .map(|(&k, _)| k);

        // Get outgoing edges from bitmap, or use empty iterator if node not found
        let outgoing = self
            .bitmap
            .outgoing_edges(matrix_idx.unwrap_or(usize::MAX))
            .map_err(|_| GraphError::NodeNotFound(node))?;

        // Chain filters to:
        // 1. Only yield items if the node exists in the index map
        // 2. Map the matrix indices to actual node indices
        Ok(outgoing
            .filter(move |_| matrix_idx.is_some())
            .filter_map(move |target_idx| self.index_map.get(&target_idx).copied()))
    }

    fn contains_node(&self, node: NI) -> Result<bool, Self::Error> {
        Ok(self.index_map.iter().any(|(_, &v)| v == node))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;

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
        let bitmap = super::super::bit_matrix::BitMatrix::new(bits);

        // Map matrix indices 0,1 to custom node IDs 'A','B'
        let mut index_map = Dictionary::<usize, char, 8>::new();
        index_map.insert(0, 'A');
        index_map.insert(1, 'B');

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map);

        // Test node iteration
        let mut nodes = ['\0'; 8];
        let mut count = 0;
        for node in bit_map_matrix.iter_nodes().unwrap() {
            nodes[count] = node;
            count += 1;
        }
        assert_eq!(count, 2);

        // Check both nodes are present (order may vary)
        assert!(nodes[..count].contains(&'A'));
        assert!(nodes[..count].contains(&'B'));

        // Test contains_node
        assert!(bit_map_matrix.contains_node('A').unwrap());
        assert!(bit_map_matrix.contains_node('B').unwrap());
        assert!(!bit_map_matrix.contains_node('C').unwrap());

        // Test outgoing edges
        let mut outgoing_a = ['\0'; 8];
        count = 0;
        for target in bit_map_matrix.outgoing_edges('A').unwrap() {
            outgoing_a[count] = target;
            count += 1;
        }
        assert_eq!(count, 2); // A->A, A->B

        let mut outgoing_b = ['\0'; 8];
        count = 0;
        for target in bit_map_matrix.outgoing_edges('B').unwrap() {
            outgoing_b[count] = target;
            count += 1;
        }
        assert_eq!(count, 1); // B->A
        assert_eq!(outgoing_b[0], 'A');
    }

    #[test]
    fn test_bit_map_matrix_empty() {
        // Empty bitmap
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new(bits);

        // Empty index map
        let index_map = Dictionary::<usize, u32, 8>::new();
        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map);

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
        let bitmap = super::super::bit_matrix::BitMatrix::new(bits);

        let mut index_map = Dictionary::<usize, u32, 8>::new();
        index_map.insert(0, 100);

        let bit_map_matrix = BitMapMatrix::new(bitmap, index_map);

        // Test outgoing edges for non-existent node should return empty iterator
        assert_eq!(bit_map_matrix.outgoing_edges(999).unwrap().count(), 0);
    }
}
