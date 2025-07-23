use heapless_graphs::adjacency_list::map_adjacency_list::MapAdjacencyList;
use heapless_graphs::containers::maps::staticdict::Dictionary;
use heapless_graphs::containers::maps::MapTrait;
use heapless_graphs::edgelist::edge_node_list::EdgeNodeList;
use heapless_graphs::edges::EdgeStructOption;
use heapless_graphs::graph::{Graph, GraphError, GraphWithMutableEdges, GraphWithMutableNodes};
use heapless_graphs::matrix::bit_map_matrix::BitMapMatrix;
use heapless_graphs::matrix::bit_matrix::BitMatrix;
use heapless_graphs::matrix::map_matrix::MapMatrix;
use heapless_graphs::nodes::NodeStructOption;

// A generic test function to verify remove_node behavior
fn test_remove_node_with_outgoing_edges<G>(mut graph: G)
where
    G: GraphWithMutableNodes<usize>
        + GraphWithMutableEdges<usize>
        + Graph<usize, Error = GraphError<usize>>,
{
    // Add nodes 0, 1, 2
    graph.add_node(0).unwrap();
    graph.add_node(1).unwrap();
    graph.add_node(2).unwrap();

    // Add edges 0->1 and 1->2
    graph.add_edge(0, 1).unwrap();
    graph.add_edge(1, 2).unwrap();

    // 1. Attempt to remove node 0 (has outgoing edge to 1)
    let result = graph.remove_node(0);
    assert!(
        matches!(result, Err(GraphError::NodeHasOutgoingEdges(0))),
        "Should fail removing node 0 due to outgoing edge"
    );
    assert!(graph.contains_node(0).unwrap(), "Node 0 should still exist");

    // 2. Attempt to remove node 1 (has incoming from 0 and outgoing to 2)
    let result = graph.remove_node(1);
    assert!(
        matches!(result, Err(GraphError::NodeHasIncomingEdges(1))),
        "Should fail removing node 1 due to incoming edge"
    );
    assert!(graph.contains_node(1).unwrap(), "Node 1 should still exist");

    // 3. Remove the edge 0->1
    graph.remove_edge(0, 1).unwrap();

    // 4. Now, removing node 0 should succeed as it has no more outgoing edges
    let result = graph.remove_node(0);
    assert!(result.is_ok(), "Should succeed removing node 0 now");
    assert!(!graph.contains_node(0).unwrap(), "Node 0 should be gone");

    // 5. Attempt to remove node 1 again (still has outgoing edge to 2)
    let result = graph.remove_node(1);
    assert!(
        matches!(result, Err(GraphError::NodeHasOutgoingEdges(1))),
        "Should fail removing node 1 due to outgoing edge to 2"
    );

    // 6. Remove edge 1->2
    graph.remove_edge(1, 2).unwrap();

    // 7. Now removing node 1 should succeed
    let result = graph.remove_node(1);
    assert!(result.is_ok(), "Should succeed removing node 1 now");
    assert!(!graph.contains_node(1).unwrap(), "Node 1 should be gone");
}

// A generic test function to verify remove_node behavior for isolated nodes
fn test_remove_isolated_node<G>(mut graph: G)
where
    G: GraphWithMutableNodes<usize> + Graph<usize, Error = GraphError<usize>>,
{
    // Add nodes 0, 1, 2
    graph.add_node(0).unwrap();
    graph.add_node(1).unwrap();
    graph.add_node(2).unwrap();

    // Remove node 1, which is isolated
    let result = graph.remove_node(1);
    assert!(result.is_ok(), "Should succeed removing isolated node 1");
    assert!(!graph.contains_node(1).unwrap(), "Node 1 should be gone");

    // Verify other nodes are unaffected
    assert!(graph.contains_node(0).unwrap(), "Node 0 should still exist");
    assert!(graph.contains_node(2).unwrap(), "Node 2 should still exist");
}

#[test]
fn remove_node_map_adjacency_list() {
    let dict = Dictionary::<usize, NodeStructOption<5, usize>, 10>::new();
    let graph = MapAdjacencyList::new(dict).unwrap();
    test_remove_node_with_outgoing_edges(graph);
}

#[test]
fn remove_isolated_node_map_adjacency_list() {
    let dict = Dictionary::<usize, NodeStructOption<5, usize>, 10>::new();
    let graph = MapAdjacencyList::new(dict).unwrap();
    test_remove_isolated_node(graph);
}

#[test]
fn remove_isolated_node_edge_node_list() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_isolated_node(graph);
}

#[test]
fn remove_isolated_node_bit_map_matrix() {
    let bitmap = BitMatrix::<1, 8>::new_unchecked([[0; 1]; 8]);
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = BitMapMatrix::new(bitmap, index_map).unwrap();
    test_remove_isolated_node(graph);
}

#[test]
fn remove_isolated_node_map_matrix() {
    let matrix = [[None; 10]; 10];
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = MapMatrix::<10, usize, (), _, _, _>::new(matrix, index_map).unwrap();
    test_remove_isolated_node(graph);
}

// A generic test function to verify remove_node behavior for nonexistent nodes
fn test_remove_nonexistent_node<G>(mut graph: G)
where
    G: GraphWithMutableNodes<usize> + Graph<usize, Error = GraphError<usize>>,
{
    // Add some nodes
    graph.add_node(0).unwrap();
    graph.add_node(2).unwrap();

    // Attempt to remove a node that doesn't exist
    let result = graph.remove_node(1);
    assert!(
        matches!(result, Err(GraphError::NodeNotFound(1))),
        "Should fail removing nonexistent node 1"
    );

    // Verify other nodes are unaffected
    assert!(graph.contains_node(0).unwrap(), "Node 0 should still exist");
    assert!(graph.contains_node(2).unwrap(), "Node 2 should still exist");
    assert_eq!(graph.iter_nodes().unwrap().count(), 2);
}

#[test]
fn remove_nonexistent_node_map_adjacency_list() {
    let dict = Dictionary::<usize, NodeStructOption<5, usize>, 10>::new();
    let graph = MapAdjacencyList::new(dict).unwrap();
    test_remove_nonexistent_node(graph);
}

#[test]
fn remove_nonexistent_node_edge_node_list() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_nonexistent_node(graph);
}

#[test]
fn remove_nonexistent_node_bit_map_matrix() {
    let bitmap = BitMatrix::<1, 8>::new_unchecked([[0; 1]; 8]);
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = BitMapMatrix::new(bitmap, index_map).unwrap();
    test_remove_nonexistent_node(graph);
}

#[test]
fn remove_nonexistent_node_map_matrix() {
    let matrix = [[None; 10]; 10];
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = MapMatrix::<10, usize, (), _, _, _>::new(matrix, index_map).unwrap();
    test_remove_nonexistent_node(graph);
}

#[test]
fn remove_node_edge_node_list() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_node_with_outgoing_edges(graph);
}

#[test]
fn remove_node_bit_map_matrix() {
    let bitmap = BitMatrix::<1, 8>::new_unchecked([[0; 1]; 8]);
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = BitMapMatrix::new(bitmap, index_map).unwrap();
    test_remove_node_with_outgoing_edges(graph);
}

#[test]
fn remove_node_map_matrix() {
    let matrix = [[None; 10]; 10];
    let index_map = Dictionary::<usize, usize, 10>::new();
    let graph = MapMatrix::<10, usize, (), _, _, _>::new(matrix, index_map).unwrap();
    test_remove_node_with_outgoing_edges(graph);
}
