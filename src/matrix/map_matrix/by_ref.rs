use crate::{
    containers::maps::MapTrait,
    graph::{GraphError, GraphRef, GraphVal, NodeIndexTrait},
};

use super::MapMatrix;

impl<const N: usize, NI, M, EDGEVALUE, COLUMNS, ROW> GraphRef<NI>
    for MapMatrix<N, NI, M, EDGEVALUE, COLUMNS, ROW>
where
    NI: NodeIndexTrait,
    ROW: AsRef<[Option<EDGEVALUE>]>,
    COLUMNS: AsRef<[ROW]>,
    M: MapTrait<NI, usize>,
{
    type Error = GraphError<NI>;

    fn iter_nodes<'a>(&'a self) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self.index_map.iter().map(|(k, _)| k))
    }

    fn iter_edges<'a>(&'a self) -> Result<impl Iterator<Item = (&'a NI, &'a NI)>, Self::Error>
    where
        NI: 'a,
    {
        Ok(self
            .index_map
            .iter()
            .flat_map(move |(from_node, &from_idx)| {
                self.index_map.iter().filter_map(move |(to_node, &to_idx)| {
                    if self.inner.get_edge_value(from_idx, to_idx).is_some() {
                        Some((from_node, to_node))
                    } else {
                        None
                    }
                })
            }))
    }

    fn outgoing_edges<'a>(
        &'a self,
        node: &'a NI,
    ) -> Result<impl Iterator<Item = &'a NI>, Self::Error>
    where
        NI: 'a,
    {
        // Fast direct lookup of matrix index for this node
        let matrix_idx = self.index_map.get(node).copied();

        Ok(self
            .inner
            .outgoing_edges(matrix_idx.unwrap_or(usize::MAX))
            .unwrap()
            .filter(move |_| matrix_idx.is_some()) // Filter out everything if node doesn't exist
            .filter_map(move |target_idx| {
                self.index_map
                    .iter()
                    .find(|(_, &idx)| idx == target_idx)
                    .map(|(node, _)| node)
            }))
    }

    fn contains_node(&self, node: &NI) -> Result<bool, Self::Error> {
        Ok(self.index_map.contains_key(node))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::maps::staticdict::Dictionary;

    type TestMatrix = MapMatrix<
        3,
        &'static str,
        Dictionary<&'static str, usize, 3>,
        i32,
        [[Option<i32>; 3]; 3],
        [Option<i32>; 3],
    >;

    #[test]
    fn test_graphref_new_map_matrix() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("a", 0);
        index_map.insert("b", 1);
        index_map.insert("c", 2);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Basic construction should succeed
        assert_eq!(GraphRef::iter_nodes(&map_matrix).unwrap().count(), 3);
    }

    #[test]
    fn test_graphref_iter_nodes() {
        let matrix = [
            [Some(1), Some(2), None],
            [None, Some(5), Some(6)],
            [Some(7), None, Some(9)],
        ];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("alice", 0);
        index_map.insert("bob", 1);
        index_map.insert("charlie", 2);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Collect nodes into array for testing (no-std compatible)
        let mut nodes = [""; 8];
        let mut count = 0;
        for node in GraphRef::iter_nodes(&map_matrix).unwrap() {
            nodes[count] = node;
            count += 1;
        }

        assert_eq!(count, 3);
        // Note: iteration order depends on map implementation, so check contents not order
        let mut found_alice = false;
        let mut found_bob = false;
        let mut found_charlie = false;

        for i in 0..count {
            match nodes[i] {
                "alice" => found_alice = true,
                "bob" => found_bob = true,
                "charlie" => found_charlie = true,
                _ => panic!("Unexpected node: {}", nodes[i]),
            }
        }

        assert!(found_alice);
        assert!(found_bob);
        assert!(found_charlie);
    }

    #[test]
    fn test_graphref_iter_edges() {
        let matrix = [
            [Some(1), Some(2), None], // alice -> alice, alice -> bob
            [None, Some(5), Some(6)], // bob -> bob, bob -> charlie
            [Some(7), None, Some(9)], // charlie -> alice, charlie -> charlie
        ];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("alice", 0);
        index_map.insert("bob", 1);
        index_map.insert("charlie", 2);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Collect edges into array for testing (no-std compatible)
        let mut edges = [("", ""); 16];
        let mut count = 0;
        for (src, dst) in GraphRef::iter_edges(&map_matrix).unwrap() {
            edges[count] = (src, dst);
            count += 1;
        }

        assert_eq!(count, 6); // 6 Some values in matrix, all mapped

        // Verify expected edges exist
        let mut found_edges = [false; 6];
        let expected_edges = [
            ("alice", "alice"),     // (0,0) -> Some(1)
            ("alice", "bob"),       // (0,1) -> Some(2)
            ("bob", "bob"),         // (1,1) -> Some(5)
            ("bob", "charlie"),     // (1,2) -> Some(6)
            ("charlie", "alice"),   // (2,0) -> Some(7)
            ("charlie", "charlie"), // (2,2) -> Some(9)
        ];

        for i in 0..count {
            for (j, &expected) in expected_edges.iter().enumerate() {
                if edges[i] == expected {
                    found_edges[j] = true;
                }
            }
        }

        for &found in &found_edges {
            assert!(found, "Not all expected edges were found");
        }
    }

    #[test]
    fn test_graphref_outgoing_edges() {
        let matrix = [
            [Some(1), Some(2), None], // alice -> alice, bob
            [None, None, Some(6)],    // bob -> charlie
            [Some(7), None, None],    // charlie -> alice
        ];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("alice", 0);
        index_map.insert("bob", 1);
        index_map.insert("charlie", 2);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Test outgoing edges from alice
        let mut alice_targets = [""; 8];
        let mut count = 0;
        for target in GraphRef::outgoing_edges(&map_matrix, &"alice").unwrap() {
            alice_targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 2);
        // Check both targets found
        let mut found_alice = false;
        let mut found_bob = false;
        for i in 0..count {
            match alice_targets[i] {
                "alice" => found_alice = true,
                "bob" => found_bob = true,
                _ => panic!("Unexpected target: {}", alice_targets[i]),
            }
        }
        assert!(found_alice);
        assert!(found_bob);

        // Test outgoing edges from bob
        let mut bob_targets = [""; 8];
        count = 0;
        for target in GraphRef::outgoing_edges(&map_matrix, &"bob").unwrap() {
            bob_targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(bob_targets[0], "charlie");

        // Test outgoing edges from charlie
        let mut charlie_targets = [""; 8];
        count = 0;
        for target in GraphRef::outgoing_edges(&map_matrix, &"charlie").unwrap() {
            charlie_targets[count] = target;
            count += 1;
        }
        assert_eq!(count, 1);
        assert_eq!(charlie_targets[0], "alice");
    }

    #[test]
    fn test_graphref_contains_node() {
        let matrix = [
            [Some(1), None, None],
            [None, None, None],
            [None, None, None],
        ];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("exists", 0);
        index_map.insert("also_exists", 1);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Test through GraphRef trait method
        assert!(GraphRef::contains_node(&map_matrix, &"exists").unwrap());
        assert!(GraphRef::contains_node(&map_matrix, &"also_exists").unwrap());
        assert!(!GraphRef::contains_node(&map_matrix, &"not_exists").unwrap());
    }

    #[test]
    fn test_graphref_empty_matrix() {
        let matrix = [[None, None, None], [None, None, None], [None, None, None]];

        let mut index_map = Dictionary::<&'static str, usize, 3>::new();
        index_map.insert("x", 0);
        index_map.insert("y", 1);
        index_map.insert("z", 2);

        let map_matrix = TestMatrix::new(matrix, index_map);

        // Should have 3 nodes but no edges
        assert_eq!(GraphRef::iter_nodes(&map_matrix).unwrap().count(), 3);
        assert_eq!(GraphRef::iter_edges(&map_matrix).unwrap().count(), 0);
    }

    #[test]
    fn test_graphref_sparse_index_mapping() {
        // Test with non-contiguous indices in the map
        let matrix = [
            [Some(10), None, None],
            [None, Some(20), None],
            [None, None, Some(30)],
        ];

        let mut index_map = Dictionary::<u32, usize, 3>::new();
        index_map.insert(100, 0); // Map node 100 to matrix index 0
        index_map.insert(200, 1); // Map node 200 to matrix index 1
        index_map.insert(300, 2); // Map node 300 to matrix index 2

        type SparseMatrix = MapMatrix<
            3,
            u32,
            Dictionary<u32, usize, 3>,
            i32,
            [[Option<i32>; 3]; 3],
            [Option<i32>; 3],
        >;
        let map_matrix = SparseMatrix::new(matrix, index_map);

        // Verify nodes
        let mut nodes = [&0u32; 8];
        let mut count = 0;
        for node in GraphRef::iter_nodes(&map_matrix).unwrap() {
            nodes[count] = node;
            count += 1;
        }
        assert_eq!(count, 3);

        // Verify edges map correctly
        let mut edges = [(&0u32, &0u32); 8];
        count = 0;
        for (src, dst) in GraphRef::iter_edges(&map_matrix).unwrap() {
            edges[count] = (src, dst);
            count += 1;
        }
        assert_eq!(count, 3); // Three diagonal edges

        // Should have self-loops: 100->100, 200->200, 300->300
        let expected = [(&100, &100), (&200, &200), (&300, &300)];
        for &expected_edge in &expected {
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
}
