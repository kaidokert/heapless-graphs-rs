use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, GraphVal, NodeIndexTrait},
};

use super::MapMatrix;

impl<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> GraphVal<NI>
    for MapMatrix<N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait + Copy,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<usize, NI>,
{
    type Error = GraphError<NI>;

    fn iter_nodes(&self) -> Result<impl Iterator<Item = NI>, Self::Error> {
        Ok(self.index_map.iter().map(|(_, &v)| v))
    }

    fn iter_edges(&self) -> Result<impl Iterator<Item = (NI, NI)>, Self::Error> {
        Ok(self.inner.iter_edges().unwrap().filter_map(|(i, j)| {
            let n = *self.index_map.get(&i)?;
            let m = *self.index_map.get(&j)?;
            Some((n, m))
        }))
    }

    fn outgoing_edges(&self, node: NI) -> Result<impl Iterator<Item = NI>, Self::Error> {
        // Find the matrix index for this node, or use usize::MAX for not found
        let matrix_idx = self
            .index_map
            .iter()
            .find(|(_, &v)| v == node)
            .map(|(&k, _)| k)
            .unwrap_or(usize::MAX);

        Ok(self
            .inner
            .outgoing_edges(matrix_idx)
            .unwrap()
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
    fn test_graphval_iter_nodes() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<usize, u32, 3>::new();
        index_map.insert(0, 100);
        index_map.insert(1, 200);
        index_map.insert(2, 300);

        type ValMatrix = MapMatrix<
            3,
            u32,
            Dictionary<usize, u32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Test GraphVal iter_nodes (returns owned values)
        let mut nodes = [0u32; 8];
        let mut count = 0;
        for node in map_matrix.iter_nodes().unwrap() {
            nodes[count] = node;
            count += 1;
        }

        assert_eq!(count, 3);

        // Check all expected nodes are present
        let mut found_100 = false;
        let mut found_200 = false;
        let mut found_300 = false;

        for i in 0..count {
            match nodes[i] {
                100 => found_100 = true,
                200 => found_200 = true,
                300 => found_300 = true,
                _ => panic!("Unexpected node: {}", nodes[i]),
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

        let mut index_map = Dictionary::<usize, u32, 3>::new();
        index_map.insert(0, 10);
        index_map.insert(1, 20);
        index_map.insert(2, 30);

        type ValMatrix = MapMatrix<
            3,
            u32,
            Dictionary<usize, u32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Test GraphVal iter_edges (returns owned values)
        let mut edges = [(0u32, 0u32); 16];
        let mut count = 0;
        for (src, dst) in map_matrix.iter_edges().unwrap() {
            edges[count] = (src, dst);
            count += 1;
        }

        assert_eq!(count, 6); // 6 Some values in matrix, all mapped

        // Verify expected edges exist
        let expected_edges = [
            (10, 10), // (0,0) -> Some(1)
            (10, 20), // (0,1) -> Some(2)
            (20, 20), // (1,1) -> Some(5)
            (20, 30), // (1,2) -> Some(6)
            (30, 10), // (2,0) -> Some(7)
            (30, 30), // (2,2) -> Some(9)
        ];

        for &expected_edge in &expected_edges {
            let mut found = false;
            for i in 0..count {
                if edges[i] == expected_edge {
                    found = true;
                    break;
                }
            }
            assert!(found, "Expected edge {:?} not found", expected_edge);
        }
    }

    #[test]
    fn test_graphval_outgoing_edges() {
        let matrix = [
            [Some(1), Some(2), None], // 10 -> 10, 20
            [None, None, Some(6)],    // 20 -> 30
            [Some(7), None, None],    // 30 -> 10
        ];

        let mut index_map = Dictionary::<usize, u32, 3>::new();
        index_map.insert(0, 10);
        index_map.insert(1, 20);
        index_map.insert(2, 30);

        type ValMatrix = MapMatrix<
            3,
            u32,
            Dictionary<usize, u32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Test outgoing edges from node 10 (GraphVal version)
        let mut targets = [0u32; 8];
        let mut count = 0;
        for target in map_matrix.outgoing_edges(10).unwrap() {
            targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 2);

        // Check both targets found
        let mut found_10 = false;
        let mut found_20 = false;
        for i in 0..count {
            match targets[i] {
                10 => found_10 = true,
                20 => found_20 = true,
                _ => panic!("Unexpected target: {}", targets[i]),
            }
        }
        assert!(found_10);
        assert!(found_20);

        // Test outgoing edges from node 20
        let mut targets = [0u32; 8];
        count = 0;
        for target in map_matrix.outgoing_edges(20).unwrap() {
            targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(targets[0], 30);

        // Test outgoing edges from node 30
        let mut targets = [0u32; 8];
        count = 0;
        for target in map_matrix.outgoing_edges(30).unwrap() {
            targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(targets[0], 10);
    }

    #[test]
    fn test_graphval_contains_node() {
        let matrix = [
            [Some(1), None, None],
            [None, None, None],
            [None, None, None],
        ];

        let mut index_map = Dictionary::<usize, i32, 3>::new();
        index_map.insert(0, 42);
        index_map.insert(1, 84);

        type ValMatrix = MapMatrix<
            3,
            i32,
            Dictionary<usize, i32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Test GraphVal contains_node
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

        let mut index_map = Dictionary::<usize, i32, 3>::new();
        index_map.insert(0, 100);
        index_map.insert(1, 200);
        index_map.insert(2, 300);

        type ValMatrix = MapMatrix<
            3,
            i32,
            Dictionary<usize, i32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Test outgoing edges for non-existent node should return empty iterator
        let outgoing_count = map_matrix.outgoing_edges(999).unwrap().count();
        assert_eq!(outgoing_count, 0);
    }

    #[test]
    fn test_graphval_with_char_nodes() {
        let matrix = [[Some(true), Some(false)], [None, Some(true)]];

        let mut index_map = Dictionary::<usize, char, 2>::new();
        index_map.insert(0, 'X');
        index_map.insert(1, 'Y');

        type CharMatrix = MapMatrix<
            2,
            char,
            Dictionary<usize, char, 2>,
            bool,
            [[Option<bool>; 2]; 2],
            [Option<bool>; 2],
        >;
        let map_matrix = CharMatrix::new(matrix, index_map);

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

        let mut index_map = Dictionary::<usize, u32, 3>::new();
        index_map.insert(0, 10);
        index_map.insert(1, 20);
        index_map.insert(2, 30);

        type ValMatrix = MapMatrix<
            3,
            u32,
            Dictionary<usize, u32, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = ValMatrix::new(matrix, index_map);

        // Should have 3 nodes but no edges
        assert_eq!(map_matrix.iter_nodes().unwrap().count(), 3);
        assert_eq!(map_matrix.iter_edges().unwrap().count(), 0);
    }
}
