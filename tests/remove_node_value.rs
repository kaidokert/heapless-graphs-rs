use heapless_graphs::graph::{
    Graph, GraphError, GraphWithMutableEdges, GraphWithMutableNodeValues,
};

// A generic test function to verify remove_node_value behavior
fn test_remove_node_value_with_edges<G, V>(mut graph: G)
where
    G: GraphWithMutableNodeValues<usize, V>
        + GraphWithMutableEdges<usize>
        + Graph<usize, Error = GraphError<usize>>,
    V: Default + PartialEq,
{
    // Add nodes with default values
    graph.add_node_value(0, V::default()).unwrap();
    graph.add_node_value(1, V::default()).unwrap();
    graph.add_node_value(2, V::default()).unwrap();

    // Add edges
    graph.add_edge(0, 1).unwrap();
    graph.add_edge(1, 2).unwrap();

    // 1. Attempt to remove node 0 (has an outgoing edge)
    let result = graph.remove_node_value(0);
    assert!(
        matches!(result, Err(GraphError::NodeHasOutgoingEdges(0))),
        "Should fail to remove node 0 due to an outgoing edge"
    );
    assert!(graph.contains_node(0).unwrap(), "Node 0 should still exist");

    // 2. Attempt to remove node 1 (has both incoming and outgoing edges)
    let result = graph.remove_node_value(1);
    assert!(
        matches!(result, Err(GraphError::NodeHasIncomingEdges(1))),
        "Should fail to remove node 1 due to an incoming edge"
    );
    assert!(graph.contains_node(1).unwrap(), "Node 1 should still exist");

    // 3. Remove the edge 0->1, making node 1 only have an outgoing edge
    graph.remove_edge(0, 1).unwrap();

    // 4. Attempt to remove node 1 again (still has an outgoing edge)
    let result = graph.remove_node_value(1);
    assert!(
        matches!(result, Err(GraphError::NodeHasOutgoingEdges(1))),
        "Should fail to remove node 1 due to an outgoing edge after removing the incoming one"
    );
    assert!(graph.contains_node(1).unwrap(), "Node 1 should still exist");

    // 5. Remove the edge 1->2, isolating node 1
    graph.remove_edge(1, 2).unwrap();

    // 6. Now, removing node 1 should succeed
    let result = graph.remove_node_value(1);
    assert!(result.is_ok(), "Should succeed in removing isolated node 1");
    assert!(!graph.contains_node(1).unwrap(), "Node 1 should be gone");
}

// A generic test function to verify remove_node_value for isolated nodes
fn test_remove_isolated_node_value<G, V>(mut graph: G)
where
    G: GraphWithMutableNodeValues<usize, V> + Graph<usize, Error = GraphError<usize>>,
    V: Default + PartialEq,
{
    // Add nodes with default values
    graph.add_node_value(0, V::default()).unwrap();
    graph.add_node_value(1, V::default()).unwrap();
    graph.add_node_value(2, V::default()).unwrap();

    // Remove an isolated node
    let result = graph.remove_node_value(1);
    assert!(result.is_ok(), "Should succeed in removing isolated node 1");
    assert!(!graph.contains_node(1).unwrap(), "Node 1 should be gone");

    // Verify other nodes are unaffected
    assert!(graph.contains_node(0).unwrap(), "Node 0 should still exist");
    assert!(graph.contains_node(2).unwrap(), "Node 2 should still exist");
}

// A generic test function to verify remove_node_value for non-existent nodes
fn test_remove_nonexistent_node_value<G, V>(mut graph: G)
where
    G: GraphWithMutableNodeValues<usize, V> + Graph<usize, Error = GraphError<usize>>,
    V: Default,
{
    // Add some nodes
    graph.add_node_value(0, V::default()).unwrap();
    graph.add_node_value(2, V::default()).unwrap();

    // Attempt to remove a node that doesn't exist
    let result = graph.remove_node_value(1);
    assert!(
        matches!(result, Err(GraphError::NodeNotFound(1))),
        "Should fail to remove non-existent node 1"
    );

    // Verify the graph is unchanged
    assert_eq!(graph.iter_nodes().unwrap().count(), 2);
}

use heapless_graphs::edgelist::edge_node_list::EdgeNodeList;
use heapless_graphs::edges::EdgeStructOption;
use heapless_graphs::nodes::NodeValueStructOption;

#[test]
fn remove_node_value_with_edges_edgenodelist() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeValueStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_node_value_with_edges::<_, i32>(graph);
}

#[test]
fn remove_isolated_node_value_edgenodelist() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeValueStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_isolated_node_value::<_, i32>(graph);
}

#[test]
fn remove_nonexistent_node_value_edgenodelist() {
    let edges = EdgeStructOption([None; 10]);
    let nodes = NodeValueStructOption([None; 10]);
    let graph = EdgeNodeList::new(edges, nodes).unwrap();
    test_remove_nonexistent_node_value::<_, i32>(graph);
}
