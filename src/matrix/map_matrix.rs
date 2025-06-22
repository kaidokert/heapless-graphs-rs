use crate::{
    containers::maps::MapTrait,
    conversions::FromGraph,
    graph::{Graph, GraphError, GraphWithMutableEdges, GraphWithMutableNodes, NodeIndex},
};

/// A matrix-based graph representation that maps arbitrary node indices to matrix positions
///
/// This struct wraps a [`Matrix`](super::simple_matrix::Matrix) and provides a mapping
/// from arbitrary node indices to matrix row/column positions, allowing graphs with
/// non-contiguous or non-zero-based node indices.
pub struct MapMatrix<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    inner: super::simple_matrix::Matrix<N, EDGEVALUE, COLUMNS, ROW>,
    index_map: M,
    _phantom: core::marker::PhantomData<NI>,
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    /// Creates a new MapMatrix with the given matrix data and index mapping
    ///
    /// The `matrix` parameter provides the adjacency matrix data, and `index_map`
    /// maps from the actual node indices to matrix indices (0..N).
    pub fn new(matrix: COLUMNS, index_map: M) -> Result<Self, GraphError<NI>> {
        for (node, idx) in index_map.iter() {
            if *idx >= N {
                return Err(GraphError::IndexOutOfBounds(*idx, *node));
            }
        }
        Ok(Self::new_unchecked(matrix, index_map))
    }

    /// Creates a new MapMatrix with the given matrix data and index mapping
    ///
    /// The `matrix` parameter provides the adjacency matrix data, and `index_map`
    /// maps from the actual node indices to matrix indices (0..N).
    pub fn new_unchecked(matrix: COLUMNS, index_map: M) -> Self {
        Self {
            inner: super::simple_matrix::Matrix::new(matrix),
            index_map,
            _phantom: Default::default(),
        }
    }
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> FromGraph<NI, GraphError<NI>>
    for MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex + Copy,
    EDGEVALUE: Default,
    ROW: AsRef<[Option<EDGEVALUE>]> + AsMut<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]> + AsMut<[ROW]> + Default,
    M: MapTrait<NI, usize> + Default,
{
    fn from_graph<G>(source_graph: &G) -> Result<Self, GraphError<NI>>
    where
        G: Graph<NI>,
        GraphError<NI>: From<G::Error>,
    {
        // Create default storage for matrix and index map
        let mut index_map = M::default();

        // Collect all nodes and assign matrix indices
        // Properly handle errors from iter_nodes() while supporting empty graphs
        match source_graph.iter_nodes() {
            Ok(nodes_iter) => {
                for (matrix_index, node) in nodes_iter.enumerate() {
                    if matrix_index >= N {
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

        // Create empty matrix and populate it with mapped edges
        let mut inner_matrix =
            super::simple_matrix::Matrix::<N, EDGEVALUE, COLUMNS, ROW>::new(COLUMNS::default());

        // Add all edges using mapped indices
        if let Ok(edges_iter) = source_graph.iter_edges() {
            for (src, dst) in edges_iter {
                // Look up matrix indices for both source and destination
                if let (Some(&src_idx), Some(&dst_idx)) = (index_map.get(&src), index_map.get(&dst))
                {
                    // Add edge using matrix indices
                    inner_matrix
                        .add_edge(src_idx, dst_idx)
                        .map_err(|_| GraphError::OutOfCapacity)?;
                }
                // If we can't find indices for either node, skip the edge
            }
        }

        Ok(Self {
            inner: inner_matrix,
            index_map,
            _phantom: Default::default(),
        })
    }
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> Graph<NI>
    for MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
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
                        if self.inner.get_edge_value(from_idx, to_idx).is_some() {
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

        Ok(self
            .inner
            .outgoing_edges(matrix_idx.unwrap_or(usize::MAX))
            .map_err(|_| GraphError::Unexpected)?
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

        Ok(self
            .inner
            .incoming_edges(matrix_idx.unwrap_or(usize::MAX))
            .map_err(|_| GraphError::Unexpected)?
            .filter(move |_| matrix_idx.is_some()) // Filter out everything if node doesn't exist
            .filter_map(move |source_idx| {
                self.index_map
                    .iter()
                    .find(|(_, &idx)| idx == source_idx)
                    .map(|(&node, _)| node)
            }))
    }
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW>
    crate::graph::GraphWithEdgeValues<NI, EDGEVALUE>
    for MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    fn iter_edge_values<'a>(
        &'a self,
    ) -> Result<impl Iterator<Item = (NI, NI, Option<&'a EDGEVALUE>)>, Self::Error>
    where
        EDGEVALUE: 'a,
    {
        Ok(self
            .index_map
            .iter()
            .flat_map(move |(&from_node, &from_idx)| {
                self.index_map
                    .iter()
                    .filter_map(move |(&to_node, &to_idx)| {
                        let value = self.inner.get_edge_value(from_idx, to_idx);
                        if value.is_some() {
                            Some((from_node, to_node, value))
                        } else {
                            None
                        }
                    })
            }))
    }
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> GraphWithMutableNodes<NI>
    for MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    fn add_node(&mut self, node: NI) -> Result<(), Self::Error> {
        // Check if node already exists
        if self.index_map.contains_key(&node) {
            return Err(GraphError::DuplicateNode(node));
        }

        // Find an unused matrix index using iterator approach
        let unused_index = (0..N)
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

        // Remove the node mapping (matrix position becomes available for reuse)
        self.index_map.remove(&node);
        Ok(())
    }
}

impl<const N: usize, NI, EDGEVALUE, M, COLUMNS, ROW> GraphWithMutableEdges<NI>
    for MapMatrix<N, NI, EDGEVALUE, M, COLUMNS, ROW>
where
    NI: NodeIndex,
    EDGEVALUE: Default,
    ROW: AsRef<[Option<EDGEVALUE>]> + AsMut<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]> + AsMut<[ROW]>,
    M: MapTrait<NI, usize>,
{
    fn add_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Look up matrix indices for both nodes
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

        // Set edge value in the underlying matrix (using default value for edge)
        let success =
            self.inner
                .set_edge_value(source_idx, destination_idx, Some(EDGEVALUE::default()));

        if success {
            Ok(())
        } else {
            Err(GraphError::OutOfCapacity)
        }
    }

    fn remove_edge(&mut self, source: NI, destination: NI) -> Result<(), Self::Error> {
        // Look up matrix indices for both nodes
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

        // Check if edge exists before removing
        if self
            .inner
            .get_edge_value(source_idx, destination_idx)
            .is_none()
        {
            return Err(GraphError::EdgeNotFound(source, destination));
        }

        // Remove edge by setting value to None
        let success = self.inner.set_edge_value(source_idx, destination_idx, None);

        if success {
            Ok(())
        } else {
            Err(GraphError::EdgeNotFound(source, destination))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;
    use crate::edgelist::edge_list::EdgeList;
    use crate::edges::EdgeStructOption;
    use crate::graph::GraphWithEdgeValues;
    use crate::graph::GraphWithMutableEdges;
    use crate::tests::{collect, collect_sorted};

    #[test]
    fn test_graphval_iter_nodes() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(100, 0).unwrap();
        index_map.insert(200, 1).unwrap();
        index_map.insert(300, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test Graph iter_nodes (returns owned values)
        let mut nodes = [0u32; 8];
        let nodes_slice = collect(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice.len(), 3);

        // Check all expected nodes are present
        let mut found_100 = false;
        let mut found_200 = false;
        let mut found_300 = false;

        for &node in nodes_slice.iter() {
            match node {
                100 => found_100 = true,
                200 => found_200 = true,
                300 => found_300 = true,
                _ => panic!("Unexpected node: {}", node),
            }
        }

        assert!(found_100);
        assert!(found_200);
        assert!(found_300);
    }

    #[test]
    fn test_graphval_iter_edges() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test Graph iter_edges (returns owned values)
        let mut edges = [(0u32, 0u32); 16];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(
            edges_slice,
            &[(10, 10), (10, 20), (20, 20), (20, 30), (30, 10), (30, 30)]
        );
    }

    #[test]
    fn test_graphval_outgoing_edges() {
        let matrix = [
            [Some(1), Some(2), None], // 10 -> 10, 20
            [None, None, Some(6)],    // 20 -> 30
            [Some(7), None, None],    // 30 -> 10
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test outgoing edges from node 10 (Graph version)
        let mut targets = [0u32; 8];
        let targets_slice = collect(map_matrix.outgoing_edges(10).unwrap(), &mut targets);
        assert_eq!(targets_slice.len(), 2);

        // Check both targets found
        let mut found_10 = false;
        let mut found_20 = false;
        for &target in targets_slice.iter() {
            match target {
                10 => found_10 = true,
                20 => found_20 = true,
                _ => panic!("Unexpected target: {}", target),
            }
        }
        assert!(found_10);
        assert!(found_20);

        // Test outgoing edges from node 20
        let mut targets = [0u32; 8];
        let targets_slice = collect(map_matrix.outgoing_edges(20).unwrap(), &mut targets);
        assert_eq!(targets_slice, &[30]);

        // Test outgoing edges from node 30
        let mut targets = [0u32; 8];
        let targets_slice = collect(map_matrix.outgoing_edges(30).unwrap(), &mut targets);
        assert_eq!(targets_slice, &[10]);
    }

    #[test]
    fn test_graphval_contains_node() {
        let matrix = [
            [Some(1), None, None],
            [None, None, None],
            [None, None, None],
        ];

        let mut index_map = Dictionary::<i32, usize, 3>::new();
        index_map.insert(42, 0).unwrap();
        index_map.insert(84, 1).unwrap();

        type ValMatrix = MapMatrix<
            3,
            i32,
            i32,
            Dictionary<i32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test Graph contains_node
        assert!(map_matrix.contains_node(42).unwrap());
        assert!(map_matrix.contains_node(84).unwrap());
        assert!(!map_matrix.contains_node(999).unwrap());
    }

    #[test]
    fn test_graphval_nonexistent_node_outgoing() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<i32, usize, 3>::new();
        index_map.insert(100, 0).unwrap();
        index_map.insert(200, 1).unwrap();
        index_map.insert(300, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            i32,
            i32,
            Dictionary<i32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test outgoing edges for non-existent node should return empty iterator
        let outgoing_count = map_matrix.outgoing_edges(999).unwrap().count();
        assert_eq!(outgoing_count, 0);
    }

    #[test]
    fn test_graphval_with_char_nodes() {
        let matrix = [[Some(true), Some(false)], [None, Some(true)]];

        let mut index_map = Dictionary::<char, usize, 2>::new();
        index_map.insert('X', 0).unwrap();
        index_map.insert('Y', 1).unwrap();

        type CharMatrix = MapMatrix<
            2,
            char,
            bool,
            Dictionary<char, usize, 2>,
            [[Option<bool>; 2]; 2],
            [Option<bool>; 2],
        >;
        let map_matrix = CharMatrix::new(matrix, index_map).unwrap();

        // Test with char node types
        assert_eq!(map_matrix.iter_nodes().unwrap().count(), 2);
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 3);

        // Test specific outgoing edges
        let x_outgoing = map_matrix.outgoing_edges('X').unwrap().count();
        assert_eq!(x_outgoing, 2); // X -> X, Y

        let y_outgoing = map_matrix.outgoing_edges('Y').unwrap().count();
        assert_eq!(y_outgoing, 1); // Y -> Y
    }

    #[test]
    fn test_graphval_empty_matrix() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Should have 3 nodes but no edges
        assert_eq!(map_matrix.iter_nodes().unwrap().count(), 3);
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_graphval_with_edge_values() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test iter_edge_values
        let mut edges_with_values = [(0u32, 0u32, 0i32); 16];
        let edges_slice = collect_sorted(
            map_matrix
                .iter_edge_values()
                .unwrap()
                .filter_map(|(src, dst, value_opt)| value_opt.map(|v| (src, dst, *v))),
            &mut edges_with_values,
        );
        assert_eq!(
            edges_slice,
            &[
                (10, 10, 1),
                (10, 20, 2),
                (20, 20, 5),
                (20, 30, 6),
                (30, 10, 7),
                (30, 30, 9)
            ]
        );

        // Test outgoing_edge_values from node 10
        let mut outgoing = [(0u32, 0i32); 8];
        let outgoing_slice = collect_sorted(
            map_matrix
                .outgoing_edge_values(10)
                .unwrap()
                .filter_map(|(dst, value_opt)| value_opt.map(|v| (dst, *v))),
            &mut outgoing,
        );
        assert_eq!(outgoing_slice, &[(10, 1), (20, 2)]);
    }

    #[test]
    fn test_graphval_incoming_edges() {
        let matrix = [
            [Some(1), Some(2), None], // 10 -> 10, 20
            [Some(3), None, None],    // 20 -> 10
            [Some(4), Some(5), None], // 30 -> 10, 20
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test incoming edges to node 10 (should be from 10, 20, 30)
        let mut sources = [0u32; 8];
        let sources_slice = collect_sorted(map_matrix.incoming_edges(10).unwrap(), &mut sources);
        assert_eq!(sources_slice, &[10, 20, 30]);

        // Test incoming edges to node 20 (should be from 10, 30)
        let mut sources = [0u32; 8];
        let sources_slice = collect_sorted(map_matrix.incoming_edges(20).unwrap(), &mut sources);
        assert_eq!(sources_slice, &[10, 30]);

        // Test incoming edges to node 30 (should be empty)
        let incoming_count = map_matrix.incoming_edges(30).unwrap().count();
        assert_eq!(incoming_count, 0);
    }

    #[test]
    fn test_graphval_incoming_edges_nonexistent_node() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        // Test incoming edges for non-existent node should return empty iterator
        let incoming_count = map_matrix.incoming_edges(999).unwrap().count();
        assert_eq!(incoming_count, 0);
    }

    #[test]
    fn test_add_node_to_empty_matrix() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];
        let index_map = Dictionary::<u32, usize, 5>::new();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        map_matrix.add_node(42).unwrap();

        let mut nodes = [0u32; 2];
        let nodes_slice = collect(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[42]);
        assert_eq!(map_matrix.outgoing_edges(42).unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_to_existing_matrix() {
        let matrix = [
            [Some(1), None, None],
            [None, None, None],
            [None, None, None],
        ];
        let mut index_map = Dictionary::<u32, usize, 5>::new();
        index_map.insert(10, 0).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        map_matrix.add_node(20).unwrap();

        let mut nodes = [0u32; 4];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20]);
        assert_eq!(map_matrix.outgoing_edges(20).unwrap().count(), 0);
        assert_eq!(map_matrix.outgoing_edges(10).unwrap().count(), 1);
    }

    #[test]
    fn test_add_duplicate_node() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];
        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        let result = map_matrix.add_node(10);
        assert!(matches!(result, Err(GraphError::DuplicateNode(10))));

        let mut nodes = [0u32; 2];
        let nodes_slice = collect(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10]);
    }

    #[test]
    fn test_add_node_capacity_exceeded() {
        let matrix = [[None, None], [None, None]];
        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();

        type ValMatrix = MapMatrix<
            2,
            u32,
            i32,
            Dictionary<u32, usize, 3>,
            [[Option<i32>; 2]; 2],
            [Option<i32>; 2],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        let result = map_matrix.add_node(30);
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));

        let mut nodes = [0u32; 4];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20]);
    }

    #[test]
    fn test_add_multiple_nodes() {
        let matrix = [
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
        ];
        let index_map = Dictionary::<u32, usize, 10>::new();

        type ValMatrix = MapMatrix<
            4,
            u32,
            i32,
            Dictionary<u32, usize, 10>,
            [[Option<i32>; 4]; 4],
            [Option<i32>; 4],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        map_matrix.add_node(100).unwrap();
        map_matrix.add_node(200).unwrap();
        map_matrix.add_node(300).unwrap();

        let mut nodes = [0u32; 4];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[100, 200, 300]);
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_add_node_fills_gaps() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];
        let mut index_map = Dictionary::<u32, usize, 5>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(30, 2).unwrap();

        type ValMatrix = MapMatrix<
            3,
            u32,
            i32,
            Dictionary<u32, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = ValMatrix::new(matrix, index_map).unwrap();

        map_matrix.add_node(20).unwrap();

        let mut nodes = [0u32; 4];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20, 30]);
    }

    #[test]
    fn test_add_edge_success() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];
        let mut index_map = Dictionary::<char, usize, 5>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        type MutableMatrix = MapMatrix<
            3,
            char,
            i32,
            Dictionary<char, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Add edges between existing nodes
        assert!(map_matrix.add_edge('A', 'B').is_ok());
        assert!(map_matrix.add_edge('B', 'C').is_ok());
        assert!(map_matrix.add_edge('A', 'C').is_ok());

        // Verify edges were added
        let edge_count = map_matrix.iter_edges().unwrap().count();
        assert_eq!(edge_count, 3);

        // Verify specific edges exist
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'B'), ('A', 'C'), ('B', 'C')]);
    }

    #[test]
    fn test_add_edge_invalid_nodes() {
        let matrix = [[None, None], [None, None]];
        let mut index_map = Dictionary::<char, usize, 5>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        type MutableMatrix = MapMatrix<
            2,
            char,
            i32,
            Dictionary<char, usize, 5>,
            [[Option<i32>; 2]; 2],
            [Option<i32>; 2],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Try to add edge with non-existent source node
        let result = map_matrix.add_edge('X', 'B');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('X'))));

        // Try to add edge with non-existent destination node
        let result = map_matrix.add_edge('A', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('Y'))));

        // Try to add edge with both nodes non-existent
        let result = map_matrix.add_edge('X', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeHasInvalidNode('X'))));
    }

    #[test]
    fn test_remove_edge_success() {
        // Set up matrix with some initial edges
        let matrix = [
            [Some(1), Some(2), Some(3)], // A->A, A->B, A->C
            [None, Some(4), None],       // B->B
            [None, None, None],          // C has no edges
        ];
        let mut index_map = Dictionary::<char, usize, 5>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        type MutableMatrix = MapMatrix<
            3,
            char,
            i32,
            Dictionary<char, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Verify initial state (A->A, A->B, A->C, B->B)
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 4);

        // Remove an edge
        assert!(map_matrix.remove_edge('A', 'B').is_ok());

        // Verify edge was removed
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 3);
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'A'), ('A', 'C'), ('B', 'B')]);
    }

    #[test]
    fn test_remove_edge_not_found() {
        let matrix = [
            [Some(1), None, None],
            [None, None, None],
            [None, None, None],
        ];
        let mut index_map = Dictionary::<char, usize, 5>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();
        index_map.insert('C', 2).unwrap();

        type MutableMatrix = MapMatrix<
            3,
            char,
            i32,
            Dictionary<char, usize, 5>,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Try to remove edge that doesn't exist
        let result = map_matrix.remove_edge('A', 'B');
        assert!(matches!(result, Err(GraphError::EdgeNotFound('A', 'B'))));

        // Try to remove edge with non-existent nodes
        let result = map_matrix.remove_edge('X', 'Y');
        assert!(matches!(result, Err(GraphError::EdgeNotFound('X', 'Y'))));

        // Verify original edge is still there
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 1);
    }

    #[test]
    fn test_add_remove_edge_comprehensive() {
        let matrix = [
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
            [None, None, None, None],
        ];
        let mut index_map = Dictionary::<u32, usize, 10>::new();
        index_map.insert(10, 0).unwrap();
        index_map.insert(20, 1).unwrap();
        index_map.insert(30, 2).unwrap();
        index_map.insert(40, 3).unwrap();

        type MutableMatrix = MapMatrix<
            4,
            u32,
            i32,
            Dictionary<u32, usize, 10>,
            [[Option<i32>; 4]; 4],
            [Option<i32>; 4],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Start with empty graph
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 0);

        // Add several edges
        assert!(map_matrix.add_edge(10, 20).is_ok());
        assert!(map_matrix.add_edge(20, 30).is_ok());
        assert!(map_matrix.add_edge(30, 40).is_ok());
        assert!(map_matrix.add_edge(10, 40).is_ok());
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 4);

        // Remove some edges
        assert!(map_matrix.remove_edge(20, 30).is_ok());
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 3);

        // Try to remove the same edge again (should fail)
        let result = map_matrix.remove_edge(20, 30);
        assert!(matches!(result, Err(GraphError::EdgeNotFound(20, 30))));

        // Add the edge back
        assert!(map_matrix.add_edge(20, 30).is_ok());
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 4);

        // Verify final edge set
        let mut edges = [(0u32, 0u32); 8];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(10, 20), (10, 40), (20, 30), (30, 40)]);
    }

    #[test]
    fn test_self_loops() {
        let matrix = [[None, None], [None, None]];
        let mut index_map = Dictionary::<char, usize, 5>::new();
        index_map.insert('A', 0).unwrap();
        index_map.insert('B', 1).unwrap();

        type MutableMatrix = MapMatrix<
            2,
            char,
            i32,
            Dictionary<char, usize, 5>,
            [[Option<i32>; 2]; 2],
            [Option<i32>; 2],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Add self-loops and regular edges
        assert!(map_matrix.add_edge('A', 'A').is_ok()); // Self-loop
        assert!(map_matrix.add_edge('A', 'B').is_ok());
        assert!(map_matrix.add_edge('B', 'B').is_ok()); // Self-loop

        assert_eq!(map_matrix.iter_edges().unwrap().count(), 3);

        // Remove self-loop
        assert!(map_matrix.remove_edge('A', 'A').is_ok());
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 2);

        // Verify remaining edges
        let mut edges = [('\0', '\0'); 8];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[('A', 'B'), ('B', 'B')]);
    }

    #[test]
    fn test_edge_overwrite() {
        let matrix = [[Some(5), None], [None, None]];
        let mut index_map = Dictionary::<u32, usize, 5>::new();
        index_map.insert(1, 0).unwrap();
        index_map.insert(2, 1).unwrap();

        type MutableMatrix = MapMatrix<
            2,
            u32,
            i32,
            Dictionary<u32, usize, 5>,
            [[Option<i32>; 2]; 2],
            [Option<i32>; 2],
        >;
        let mut map_matrix = MutableMatrix::new(matrix, index_map).unwrap();

        // Initial edge exists
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 1);

        // Add edge to same position (should overwrite)
        assert!(map_matrix.add_edge(1, 1).is_ok());
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 1); // Still one edge, but different target

        // Verify the new edge exists
        let mut edges = [(0u32, 0u32); 8];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(1, 1)]); // Self-loop now exists
    }

    #[test]
    fn test_map_matrix_from_graph() {
        // Create a source graph (edge list with nodes 10, 20, 30)
        let edges = EdgeStructOption([Some((10, 20)), Some((20, 30)), Some((10, 30)), None]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Convert to MapMatrix (4x4 matrix to accommodate mapping)
        type TestMatrix = MapMatrix<
            4,
            usize,
            (),
            Dictionary<usize, usize, 8>,
            [[Option<()>; 4]; 4],
            [Option<()>; 4],
        >;
        let map_matrix: TestMatrix = MapMatrix::from_graph(&source).unwrap();

        // Verify nodes were mapped correctly (should have 3 nodes: 10, 20, 30)
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[10, 20, 30]);

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(10, 20), (10, 30), (20, 30)]);

        // Test node containment
        assert!(map_matrix.contains_node(10).unwrap());
        assert!(map_matrix.contains_node(20).unwrap());
        assert!(map_matrix.contains_node(30).unwrap());
        assert!(!map_matrix.contains_node(40).unwrap());
    }

    #[test]
    fn test_map_matrix_from_graph_empty() {
        // Create an empty source graph
        let edges = EdgeStructOption([None, None, None, None]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Convert to MapMatrix
        type TestMatrix = MapMatrix<
            3,
            usize,
            (),
            Dictionary<usize, usize, 8>,
            [[Option<()>; 3]; 3],
            [Option<()>; 3],
        >;
        let map_matrix: TestMatrix = MapMatrix::from_graph(&source).unwrap();

        // Verify no nodes or edges
        assert_eq!(map_matrix.iter_nodes().unwrap().count(), 0);
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 0);
    }

    #[test]
    fn test_map_matrix_from_graph_capacity_exceeded() {
        // Create a source graph with 4 nodes but matrix only supports 3
        let edges = EdgeStructOption([Some((0, 1)), Some((1, 2)), Some((2, 3)), Some((3, 0))]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Try to convert to 3x3 MapMatrix (can only fit 3 nodes)
        type TestMatrix = MapMatrix<
            3,
            usize,
            (),
            Dictionary<usize, usize, 8>,
            [[Option<()>; 3]; 3],
            [Option<()>; 3],
        >;
        let result: Result<TestMatrix, _> = MapMatrix::from_graph(&source);

        // Should fail because source has 4 nodes but matrix only supports 3
        assert!(matches!(result, Err(GraphError::OutOfCapacity)));
    }

    #[test]
    fn test_map_matrix_from_graph_with_arbitrary_indices() {
        // Create a source graph with non-contiguous node indices
        let edges = EdgeStructOption([Some((100, 200)), Some((200, 500)), Some((500, 100)), None]);
        let source = EdgeList::<4, usize, _>::new(edges);

        // Convert to MapMatrix
        type TestMatrix = MapMatrix<
            4,
            usize,
            (),
            Dictionary<usize, usize, 8>,
            [[Option<()>; 4]; 4],
            [Option<()>; 4],
        >;
        let map_matrix: TestMatrix = MapMatrix::from_graph(&source).unwrap();

        // Verify nodes were mapped correctly
        let mut nodes = [0usize; 8];
        let nodes_slice = collect_sorted(map_matrix.iter_nodes().unwrap(), &mut nodes);
        assert_eq!(nodes_slice, &[100, 200, 500]);

        // Verify edges were copied correctly
        let mut edges = [(0usize, 0usize); 16];
        let edges_slice = collect_sorted(map_matrix.iter_edges().unwrap(), &mut edges);
        assert_eq!(edges_slice, &[(100, 200), (200, 500), (500, 100)]);

        // Test outgoing edges
        let mut outgoing = [0usize; 8];
        let outgoing_slice = collect(map_matrix.outgoing_edges(100).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[200]);

        let outgoing_slice = collect(map_matrix.outgoing_edges(200).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[500]);

        let outgoing_slice = collect(map_matrix.outgoing_edges(500).unwrap(), &mut outgoing);
        assert_eq!(outgoing_slice, &[100]);
    }
}
