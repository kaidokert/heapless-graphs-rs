use crate::graph::{Graph, GraphError, GraphWithMutableEdges};

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

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> Matrix<N, EDGEVALUE, COLUMNS, ROW>
where
    EDGEVALUE: Default,
    ROW: AsRef<[Option<EDGEVALUE>]> + AsMut<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]> + AsMut<[ROW]> + Default,
{
    /// Creates a Matrix from any graph by copying all edges
    ///
    /// This function iterates over all edges in the source graph and adds them
    /// to a new Matrix. The source graph must have usize node indices in the
    /// range 0..N, where N is the matrix size.
    ///
    /// # Arguments
    /// * `source_graph` - The graph to copy edges from
    ///
    /// # Returns
    /// * `Ok(Matrix)` if successful
    /// * `Err(GraphError)` if any node indices are out of range or iteration fails
    ///
    /// # Constraints
    /// * Source graph nodes must be usize indices from 0 to N-1
    /// * Edge values use EDGEVALUE::default() for all edges
    /// * Matrix must have mutable storage (AsMut traits)
    ///
    /// # Example
    /// # use heapless_graphs::matrix::simple_matrix::Matrix;
    /// # use heapless_graphs::edgelist::edge_list::EdgeList;
    /// # use heapless_graphs::edges::EdgeStructOption;
    ///
    /// // Create a source graph (edge list)
    /// let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), Some((0, 2)), None]);
    /// let source = EdgeList::<4, usize, _>::new(edges);
    ///
    /// // Convert to Matrix (3x3 matrix to fit nodes 0, 1, 2)
    /// let matrix: Matrix<3, (), [[Option<()>; 3]; 3], _> =
    ///     Matrix::from_graph(&source).unwrap();
    pub fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<usize>>
    where
        G: Graph<usize>,
        GraphError<usize>: From<G::Error>,
    {
        // Create empty matrix with default storage
        let mut matrix = Self::new(COLUMNS::default());

        // Validate all nodes are within range first
        for node in source_graph.iter_nodes()? {
            if node >= N {
                return Err(GraphError::EdgeHasInvalidNode(node));
            }
        }

        // Add all edges to the matrix
        for (source, destination) in source_graph.iter_edges()? {
            // These should already be validated above, but double-check for safety
            if source >= N {
                return Err(GraphError::EdgeHasInvalidNode(source));
            }
            if destination >= N {
                return Err(GraphError::EdgeHasInvalidNode(destination));
            }

            // Set edge in matrix
            if !matrix.set_edge_value(source, destination, Some(EDGEVALUE::default())) {
                // This should not happen since we validated indices
                return Err(GraphError::OutOfCapacity);
            }
        }

        Ok(matrix)
    }
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> Matrix<N, EDGEVALUE, COLUMNS, ROW>
where
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
{
    pub(crate) fn get_edge_value(&self, row: usize, col: usize) -> Option<&EDGEVALUE> {
        self.matrix.as_ref().get(row)?.as_ref().get(col)?.as_ref()
    }

    pub(crate) fn set_edge_value(
        &mut self,
        row: usize,
        col: usize,
        value: Option<EDGEVALUE>,
    ) -> bool
    where
        ROW: AsMut<[Option<EDGEVALUE>]>,
        COLUMNS: AsMut<[ROW]>,
    {
        if let Some(matrix_row) = self.matrix.as_mut().get_mut(row) {
            if let Some(cell) = matrix_row.as_mut().get_mut(col) {
                *cell = value;
                return true;
            }
        }
        false
    }
}

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> Graph<usize> for Matrix<N, EDGEVALUE, COLUMNS, ROW>
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

impl<const N: usize, EDGEVALUE, ROW, COLUMNS> GraphWithMutableEdges<usize>
    for Matrix<N, EDGEVALUE, COLUMNS, ROW>
where
    EDGEVALUE: Default,
    ROW: AsRef<[Option<EDGEVALUE>]> + AsMut<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]> + AsMut<[ROW]>,
{
    fn add_edge(&mut self, source: usize, destination: usize) -> Result<(), Self::Error> {
        // Validate node indices
        if source >= N {
            return Err(GraphError::EdgeHasInvalidNode(source));
        }
        if destination >= N {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Set edge to default value
        if self.set_edge_value(source, destination, Some(EDGEVALUE::default())) {
            Ok(())
        } else {
            // This should not happen since we validated indices above
            Err(GraphError::OutOfCapacity)
        }
    }

    fn remove_edge(&mut self, source: usize, destination: usize) -> Result<(), Self::Error> {
        // Validate node indices
        if source >= N {
            return Err(GraphError::EdgeHasInvalidNode(source));
        }
        if destination >= N {
            return Err(GraphError::EdgeHasInvalidNode(destination));
        }

        // Check if edge exists before removing
        if self.get_edge_value(source, destination).is_none() {
            return Err(GraphError::EdgeNotFound(source, destination));
        }

        // Remove edge
        if self.set_edge_value(source, destination, None) {
            Ok(())
        } else {
            // This should not happen since we validated indices above
            Err(GraphError::EdgeNotFound(source, destination))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adjacency_list::map_adjacency_list::MapAdjacencyList;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::containers::maps::MapTrait;
    use crate::graph::GraphWithMutableEdges;
    use crate::tests::{collect, collect_sorted};

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
        let nodes_slice = collect(matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2]);

        // Test with different size
        let matrix = Matrix::<5, i32, _, _>::new([
            [Some(1), Some(2), Some(3), Some(4), Some(5)],
            [Some(6), Some(7), Some(8), Some(9), Some(10)],
            [Some(11), Some(12), Some(13), Some(14), Some(15)],
            [Some(16), Some(17), Some(18), Some(19), Some(20)],
            [Some(21), Some(22), Some(23), Some(24), Some(25)],
        ]);

        let mut nodes = [0usize; 8];
        let nodes_slice = collect(matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[0, 1, 2, 3, 4]);
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

    #[test]
    fn test_mutable_edges_add_edge_success() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, None, None],
            [None, None, None],
            [None, None, None],
        ]);

        // Add edges
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(1, 2).is_ok());
        assert!(matrix.add_edge(0, 2).is_ok());
        assert!(matrix.add_edge(2, 0).is_ok());

        // Verify edges were added
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 1), (0, 2), (1, 2), (2, 0)]);

        // Verify specific edges exist
        assert!(matrix.get_edge_value(0, 1).is_some());
        assert!(matrix.get_edge_value(1, 2).is_some());
        assert!(matrix.get_edge_value(0, 2).is_some());
        assert!(matrix.get_edge_value(2, 0).is_some());

        // Verify non-edges don't exist
        assert!(matrix.get_edge_value(1, 0).is_none());
        assert!(matrix.get_edge_value(2, 1).is_none());
    }

    #[test]
    fn test_mutable_edges_add_edge_invalid_nodes() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, None, None],
            [None, None, None],
            [None, None, None],
        ]);

        // Try to add edge with invalid source
        let result = matrix.add_edge(3, 1);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Try to add edge with invalid destination
        let result = matrix.add_edge(1, 3);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Try to add edge with both invalid
        let result = matrix.add_edge(5, 4);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(5))));
    }

    #[test]
    fn test_mutable_edges_remove_edge_success() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, Some(1), Some(2)],
            [Some(3), None, Some(4)],
            [Some(5), None, Some(6)],
        ]);

        // Initial edge count
        assert_eq!(matrix.iter_edges().unwrap().count(), 6);

        // Remove edges
        assert!(matrix.remove_edge(0, 1).is_ok()); // Remove (0, 1)
        assert!(matrix.remove_edge(1, 2).is_ok()); // Remove (1, 2)

        // Verify edges were removed
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 2), (1, 0), (2, 0), (2, 2)]);

        // Verify specific edges were removed
        assert!(matrix.get_edge_value(0, 1).is_none());
        assert!(matrix.get_edge_value(1, 2).is_none());

        // Verify remaining edges still exist
        assert!(matrix.get_edge_value(0, 2).is_some());
        assert!(matrix.get_edge_value(1, 0).is_some());
        assert!(matrix.get_edge_value(2, 0).is_some());
        assert!(matrix.get_edge_value(2, 2).is_some());
    }

    #[test]
    fn test_mutable_edges_remove_edge_not_found() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, Some(1), None],
            [None, None, Some(2)],
            [Some(3), None, None],
        ]);

        // Try to remove edge that doesn't exist
        let result = matrix.remove_edge(0, 2);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 2))));

        // Try to remove edge with invalid source
        let result = matrix.remove_edge(3, 1);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Try to remove edge with invalid destination
        let result = matrix.remove_edge(1, 3);
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(3))));

        // Verify original edges are unchanged
        assert_eq!(matrix.iter_edges().unwrap().count(), 3);
    }

    #[test]
    fn test_mutable_edges_add_remove_comprehensive() {
        let mut matrix = Matrix::<4, i32, _, _>::new([
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
        ]);

        // Start with empty matrix
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);

        // Add edges
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(0, 2).is_ok());
        assert!(matrix.add_edge(1, 3).is_ok());
        assert!(matrix.add_edge(2, 3).is_ok());
        assert!(matrix.add_edge(3, 0).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 5);

        // Remove some edges
        assert!(matrix.remove_edge(0, 1).is_ok());
        assert!(matrix.remove_edge(2, 3).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 3);

        // Try to remove already removed edge
        let result = matrix.remove_edge(0, 1);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(0, 1))));

        // Add edges back
        assert!(matrix.add_edge(0, 1).is_ok());
        assert!(matrix.add_edge(2, 3).is_ok());
        assert_eq!(matrix.iter_edges().unwrap().count(), 5);

        // Verify final state
        let mut edges = [(0usize, 0usize); 8];
        let sorted_edges = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(sorted_edges, &[(0, 1), (0, 2), (1, 3), (2, 3), (3, 0)]);
    }

    #[test]
    fn test_mutable_edges_overwrite_existing() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, Some(42), None],
            [None, None, None],
            [None, None, None],
        ]);

        // Verify initial edge value
        assert_eq!(*matrix.get_edge_value(0, 1).unwrap(), 42);

        // Add edge over existing - should overwrite with default value
        assert!(matrix.add_edge(0, 1).is_ok());

        // Should now have default value (0 for i32)
        assert_eq!(*matrix.get_edge_value(0, 1).unwrap(), 0);

        // Edge count should remain the same
        assert_eq!(matrix.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_mutable_edges_self_loops() {
        let mut matrix = Matrix::<3, i32, _, _>::new([
            [None, None, None],
            [None, None, None],
            [None, None, None],
        ]);

        // Add self-loops
        assert!(matrix.add_edge(0, 0).is_ok());
        assert!(matrix.add_edge(1, 1).is_ok());
        assert!(matrix.add_edge(2, 2).is_ok());

        // Verify self-loops exist
        let mut edges = [(0usize, 0usize); 8];
        let edges_slice = collect(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(0, 0), (1, 1), (2, 2)]);

        // Remove self-loops
        assert!(matrix.remove_edge(0, 0).is_ok());
        assert!(matrix.remove_edge(1, 1).is_ok());
        assert!(matrix.remove_edge(2, 2).is_ok());

        // Verify all removed
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_matrix_from_graph() {
        // Create a source graph (adjacency list with nodes 0, 1, 2)
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // 0 -> 1, 2
        dict.insert(1, [2, 0]).unwrap(); // 1 -> 2, 0
        dict.insert(2, [0, 1]).unwrap(); // 2 -> 0, 1
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to Matrix (4x4 to fit nodes 0, 1, 2 with space)
        let matrix: Matrix<4, (), [[Option<()>; 4]; 4], [Option<()>; 4]> =
            Matrix::from_graph(&source).unwrap();

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
        );

        // Verify nodes are preserved
        let node_count = matrix.iter_nodes().unwrap().count();
        assert_eq!(node_count, 4); // Matrix always has N nodes (0..N)
    }

    #[test]
    fn test_matrix_from_graph_empty() {
        // Create an empty source graph
        let dict = Dictionary::<usize, [usize; 2], 8>::default();
        let source = MapAdjacencyList::new_unchecked(dict);

        // Convert to Matrix
        let matrix: Matrix<3, (), [[Option<()>; 3]; 3], [Option<()>; 3]> =
            Matrix::from_graph(&source).unwrap();

        // Verify no edges
        assert_eq!(matrix.iter_edges().unwrap().count(), 0);

        // Matrix still has N nodes (0..N)
        let node_count = matrix.iter_nodes().unwrap().count();
        assert_eq!(node_count, 3);
    }

    #[test]
    fn test_matrix_from_graph_node_out_of_range() {
        // Create a source graph with node index too large for 2x2 matrix
        let mut dict = Dictionary::<usize, [usize; 2], 8>::new();
        dict.insert(0, [1, 2]).unwrap(); // Node 2 is out of range for 2x2 matrix
        let source = MapAdjacencyList::new_unchecked(dict);

        // Try to convert to 2x2 Matrix (can only fit nodes 0, 1)
        let result: Result<Matrix<2, (), [[Option<()>; 2]; 2], [Option<()>; 2]>, _> =
            Matrix::from_graph(&source);

        // Should fail because node 2 is out of range
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode(2))));
    }
}
