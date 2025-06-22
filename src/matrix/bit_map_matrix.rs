use crate::{
    containers::maps::MapTrait,
    conversions::FromGraph,
    graph::{Graph, GraphError, GraphWithMutableEdges, GraphWithMutableNodes, NodeIndex},
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

impl<const N: usize, const R: usize, NI, M> FromGraph<NI, GraphError<NI>>
    for BitMapMatrix<N, R, NI, M>
where
    NI: NodeIndex + Copy,
    M: MapTrait<NI, usize> + Default,
{
    fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<NI>>
    where
        G: Graph<NI>,
        GraphError<NI>: From<G::Error>,
    {
        // Create default storage for index map
        let mut index_map = M::default();

        // Collect all nodes and assign bit matrix indices
        let max_index = 8 * N; // BitMatrix supports 0..8*N

        // Collect all nodes and assign bit matrix indices
        // Properly handle errors from iter_nodes() while supporting empty graphs
        match source_graph.iter_nodes() {
            Ok(nodes_iter) => {
                for (matrix_index, node) in nodes_iter.enumerate() {
                    if matrix_index >= max_index {
                        return Err(GraphError::OutOfCapacity);
                    }

                    // Insert mapping from node to matrix index
                    index_map
                        .insert(node, matrix_index)
                        .map_err(|_| GraphError::OutOfCapacity)?;
                }
            }
            Err(err) => {
                // Convert error to our error type to examine it
                let graph_error = GraphError::from(err);
                match graph_error {
                    GraphError::OutOfCapacity => {
                        // This is likely an EmptyEdges error from EdgeList - treat as empty graph
                        // Creating an empty matrix with no nodes mapped is valid for empty graphs
                    }
                    other_error => {
                        // Propagate genuine errors (invalid state, iteration failures, etc.)
                        return Err(other_error);
                    }
                }
            }
        }

        // Create empty BitMatrix and populate it with mapped edges
        let mut bitmap = super::bit_matrix::BitMatrix::<N, R>::new([[0u8; N]; R])
            .map_err(|_| GraphError::InvalidMatrixSize)?;

        // Add all edges using mapped indices
        if let Ok(edges_iter) = source_graph.iter_edges() {
            for (src, dst) in edges_iter {
                // Look up matrix indices for both source and destination
                if let (Some(&src_idx), Some(&dst_idx)) = (index_map.get(&src), index_map.get(&dst))
                {
                    // Add edge using matrix indices
                    bitmap
                        .add_edge(src_idx, dst_idx)
                        .map_err(|_| GraphError::OutOfCapacity)?;
                }
                // If we can't find indices for either node, skip the edge
            }
        }

        Ok(Self::new_unchecked(bitmap, index_map))
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

impl<const N: usize, const R: usize, NI, M> GraphWithMutableNodes<NI> for BitMapMatrix<N, R, NI, M>
where
    NI: NodeIndex,
    M: MapTrait<NI, usize>,
{
    fn add_node(&mut self, node: NI) -> Result<(), Self::Error> {
        // Check if node already exists
        if self.index_map.contains_key(&node) {
            return Err(GraphError::DuplicateNode(node));
        }

        // Find an unused matrix index (BitMatrix supports 0..8*N)
        let max_index = 8 * N;
        let unused_index = (0..max_index)
            .find(|&idx| !self.index_map.iter().any(|(_, &used_idx)| used_idx == idx))
            .ok_or(GraphError::OutOfCapacity)?;

        // Insert the new node mapping
        self.index_map
            .insert(node, unused_index)
            .map_err(|_| GraphError::OutOfCapacity)?;

        Ok(())
    }

    fn remove_node(&mut self, node: NI) -> Result<(), Self::Error> {
        // Check if node exists
        if !self.index_map.contains_key(&node) {
            return Err(GraphError::NodeNotFound(node));
        }

        // Check if node has incoming edges
        if self.incoming_edges(node)?.next().is_some() {
            return Err(GraphError::NodeHasIncomingEdges(node));
        }

        // Remove the node mapping (bit matrix position becomes available for reuse)
        self.index_map.remove(&node);
        Ok(())
    }
}

impl<const N: usize, const R: usize, NI, M> GraphWithMutableEdges<NI> for BitMapMatrix<N, R, NI, M>
where
    NI: NodeIndex,
    M: MapTrait<NI, usize>,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Translate node indices to matrix indices
        let source_idx = self
            .index_map
            .get(&source)
            .copied()
            .ok_or(GraphError::EdgeHasInvalidNode(source))?;

        let destination_idx = self
            .index_map
            .get(&destination)
            .copied()
            .ok_or(GraphError::EdgeHasInvalidNode(destination))?;

        // Delegate to underlying BitMatrix implementation
        self.bitmap
            .add_edge(source_idx, destination_idx)
            .map_err(|err| match err {
                GraphError::EdgeHasInvalidNode(_) => {
                    // This shouldn't happen since we validated indices above,
                    // but if it does, convert to source node error
                    GraphError::EdgeHasInvalidNode(source)
                }
                GraphError::OutOfCapacity => GraphError::OutOfCapacity,
                _ => GraphError::EdgeHasInvalidNode(source), // Fallback
            })
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Translate node indices to matrix indices
        let source_idx = self
            .index_map
            .get(&source)
            .copied()
            .ok_or(GraphError::EdgeNotFound(source, destination))?;

        let destination_idx = self
            .index_map
            .get(&destination)
            .copied()
            .ok_or(GraphError::EdgeNotFound(source, destination))?;

        // Delegate to underlying BitMatrix implementation
        self.bitmap
            .remove_edge(source_idx, destination_idx)
            .map_err(|err| match err {
                GraphError::EdgeNotFound(_, _) => {
                    // Convert matrix indices back to node indices for error
                    GraphError::EdgeNotFound(source, destination)
                }
                _ => GraphError::EdgeNotFound(source, destination), // Fallback
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::edges::EdgeStructOption;
    use crate::graph::GraphWithMutableEdges;
    use crate::tests::{collect, collect_sorted};

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
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &['A', 'B']);

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
        let incoming_slice =
            collect_sorted(bit_map_matrix.incoming_edges('A').unwrap(), &mut incoming_a);
        assert_eq!(incoming_slice, &['A', 'B']); // A->A, B->A

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

    #[test]
    fn test_add_node_to_empty_bit_matrix() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let index_map = Dictionary::<u32, usize, 10>::new();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();
        bit_map_matrix.add_node(42).unwrap();

        let mut nodes = [0u32; 2];
        let nodes_slice = collect(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);
        assert_eq!(bit_map_matrix.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_to_existing_bit_matrix() {
        let bits = [
            [0b00000001u8], // Row 0: edge to node 0 (self-loop)
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();
        bit_map_matrix.add_node('B').unwrap();

        let mut nodes = ['\0'; 4];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &['A', 'B']);
        assert_eq!(bit_map_matrix.outgoing_edges('B').unwrap().count(), 0);
        assert_eq!(bit_map_matrix.outgoing_edges('A').unwrap().count(), 1);
    }

    #[test]
    fn test_add_duplicate_node_bit_matrix() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<u32, usize, 8>::new();
        index_map.insert(100, 0).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        let result = bit_map_matrix.add_node(100);
        assert!(matches!(result, Err(GraphError::DuplicateNode(100))));

        let mut nodes = [0u32; 2];
        let nodes_slice = collect(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[100]);
    }

    #[test]
    fn test_add_node_capacity_exceeded_bit_matrix() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<u32, usize, 8>::new();
        for i in 0..8 {
            index_map.insert(i as u32, i).unwrap();
        }

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        let result = bit_map_matrix.add_node(999);
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));

        let mut nodes = [0u32; 10];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_add_multiple_nodes_bit_matrix() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let index_map = Dictionary::<char, usize, 10>::new();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();
        bit_map_matrix.add_node('X').unwrap();
        bit_map_matrix.add_node('Y').unwrap();
        bit_map_matrix.add_node('Z').unwrap();

        let mut nodes = ['\0'; 4];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &['X', 'Y', 'Z']);
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_fills_gaps_bit_matrix() {
        let bits = [[0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8], [0u8]];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<u32, usize, 10>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(30, 2).unwrap();
        index_map.insert(50, 4).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();
        bit_map_matrix.add_node(20).unwrap();

        let mut nodes = [0u32; 6];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20, 30, 50]);
    }

    #[test]
    fn test_add_edge_success() {
        let bits = [[0u8]; 8];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Add edges between existing nodes
        assert!(bit_map_matrix.add_edge('A', 'B').is_ok());
        assert!(bit_map_matrix.add_edge('B', 'C').is_ok());
        assert!(bit_map_matrix.add_edge('A', 'C').is_ok());

        // Verify edges were added
        let edge_count = bit_map_matrix.iter_edges().unwrap().count();
        assert_eq!(edge_count, 3);

        // Verify specific edges exist
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'B'), ('A', 'C'), ('B', 'C')]);
    }

    #[test]
    fn test_add_edge_invalid_nodes() {
        let bits = [[0u8]; 8];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Try to add edge with non-existent source node
        let result = bit_map_matrix.add_edge('X', 'B');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('X'))));

        // Try to add edge with non-existent destination node
        let result = bit_map_matrix.add_edge('A', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('Y'))));

        // Try to add edge with both nodes non-existent
        let result = bit_map_matrix.add_edge('X', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('X'))));
    }

    #[test]
    fn test_remove_edge_success() {
        // Set up matrix with some initial edges
        let bits = [
            [0b00000110u8], // A->B, A->C
            [0b00000100u8], // B->C
            [0b00000000u8], // C->nothing
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Verify initial state
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 3);

        // Remove an edge
        assert!(bit_map_matrix.remove_edge('A', 'B').is_ok());

        // Verify edge was removed
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 2);
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'C'), ('B', 'C')]);
    }

    #[test]
    fn test_remove_edge_not_found() {
        let bits = [
            [0b00000010u8], // A->B
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
            [0b00000000u8],
        ];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Try to remove edge that doesn't exist
        let result = bit_map_matrix.remove_edge('A', 'C');
        assert!(matches!(result, Err(GraphError::EdgeNotFound('A', 'C'))));

        // Try to remove edge with non-existent nodes
        let result = bit_map_matrix.remove_edge('X', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeNotFound('X', 'Y'))));

        // Verify original edge is still there
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_add_remove_edge_comprehensive() {
        let bits = [[0u8]; 8];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<u32, usize, 10>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();
        index_map.insert(40, 3).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Start with empty graph
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 0);

        // Add several edges
        assert!(bit_map_matrix.add_edge(10, 20).is_ok());
        assert!(bit_map_matrix.add_edge(20, 30).is_ok());
        assert!(bit_map_matrix.add_edge(30, 40).is_ok());
        assert!(bit_map_matrix.add_edge(10, 40).is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 4);

        // Remove some edges
        assert!(bit_map_matrix.remove_edge(20, 30).is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 3);

        // Try to remove the same edge again (should fail)
        let result = bit_map_matrix.remove_edge(20, 30);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(20, 30))));

        // Add the edge back
        assert!(bit_map_matrix.add_edge(20, 30).is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 4);

        // Verify final edge set
        let mut edges = [(0u32, 0u32); 8];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(10, 20), (10, 40), (20, 30), (30, 40)]);
    }

    #[test]
    fn test_self_loops() {
        let bits = [[0u8]; 8];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<char, usize, 10>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Add self-loops and regular edges
        assert!(bit_map_matrix.add_edge('A', 'A').is_ok()); // Self-loop
        assert!(bit_map_matrix.add_edge('A', 'B').is_ok());
        assert!(bit_map_matrix.add_edge('B', 'B').is_ok()); // Self-loop

        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 3);

        // Remove self-loop
        assert!(bit_map_matrix.remove_edge('A', 'A').is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 2);

        // Verify remaining edges
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'B'), ('B', 'B')]);
    }

    #[test]
    fn test_edge_idempotency() {
        let bits = [[0u8]; 8];
        let bitmap = super::super::bit_matrix::BitMatrix::new_unchecked(bits);
        let mut index_map = Dictionary::<u32, usize, 10>::new();
        index_map.insert(1, 0).unwrap();
        index_map.insert(2, 1).unwrap();

        let mut bit_map_matrix = BitMapMatrix::new(bitmap, index_map).unwrap();

        // Add edge
        assert!(bit_map_matrix.add_edge(1, 2).is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 1);

        // Add same edge again (should be idempotent)
        assert!(bit_map_matrix.add_edge(1, 2).is_ok());
        assert_eq!(bit_map_matrix.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_bit_map_matrix_from_graph() {
        // Create a source graph (edge list with nodes 10, 20, 30)
        let edges = EdgeStructOption([Some((10, 20)), Some((20, 30)), Some((10, 30)), None]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Convert to BitMapMatrix (1 byte = 8 nodes capacity)
        type TestMatrix = BitMapMatrix<1, 8, usize, Dictionary<usize, usize, 8>>;
        let bit_map_matrix: TestMatrix = BitMapMatrix::from_graph(&source).unwrap();

        // Verify nodes were mapped correctly (should have 3 nodes: 10, 20, 30)
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20, 30]);

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(10, 20), (10, 30), (20, 30)]);

        // Test node containment
        assert!(bit_map_matrix.contains_node(10).unwrap());
        assert!(bit_map_matrix.contains_node(20).unwrap());
        assert!(bit_map_matrix.contains_node(30).unwrap());
        assert!(!bit_map_matrix.contains_node(40).unwrap());
    }

    #[test]
    fn test_bit_map_matrix_from_graph_capacity_exceeded() {
        // Create a source graph with 9 nodes but BitMatrix<1,8> only supports 8
        let edges = EdgeStructOption([
            Some((0, 1)),
            Some((1, 2)),
            Some((2, 3)),
            Some((3, 4)),
            Some((4, 5)),
            Some((5, 6)),
            Some((6, 7)),
            Some((7, 8)),
        ]);
        let source = EdgeList::<8, usize, _>::new(edges);

        // Try to convert to BitMapMatrix<1,8> (can only fit 8 nodes)
        type TestMatrix = BitMapMatrix<1, 8, usize, Dictionary<usize, usize, 10>>;
        let result: Result<TestMatrix, _> = BitMapMatrix::from_graph(&source);

        // Should fail because source has 9 nodes but BitMatrix only supports 8
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_bit_map_matrix_from_graph_with_arbitrary_indices() {
        // Create a source graph with non-contiguous node indices
        let edges = EdgeStructOption([Some((100, 200)), Some((200, 500)), Some((500, 100)), None]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Convert to BitMapMatrix
        type TestMatrix = BitMapMatrix<1, 8, usize, Dictionary<usize, usize, 8>>;
        let bit_map_matrix: TestMatrix = BitMapMatrix::from_graph(&source).unwrap();

        // Verify nodes were mapped correctly
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(bit_map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[100, 200, 500]);

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(bit_map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(100, 200), (200, 500), (500, 100)]);

        // Test outgoing edges
        let mut outgoing = [0usize; 8];
        let outgoing_slice = collect(bit_map_matrix.outgoing_edges(100).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[200]);

        let outgoing_slice = collect(bit_map_matrix.outgoing_edges(200).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[500]);

        let outgoing_slice = collect(bit_map_matrix.outgoing_edges(500).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[100]);
    }

    #[test]
    fn test_bit_map_matrix_from_graph_invalid_dimensions() {
        // Create a source graph
        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), None]);
        let source = EdgeList::<3, usize, _>::new(edges);

        // Try to create BitMapMatrix with invalid dimensions (R ≠ 8*N)
        // N=1, R=4, but 4 ≠ 8*1
        type InvalidMatrix = BitMapMatrix<1, 4, usize, Dictionary<usize, usize, 8>>;
        let result: Result<InvalidMatrix, _> = BitMapMatrix::from_graph(&source);

        // Should fail with InvalidMatrixSize because R ≠ 8*N
        assert!(matches!(result, Err(GraphError::InvalidMatrixSize)));
    }
}
