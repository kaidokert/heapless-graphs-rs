pub mod bellman_ford;
pub mod dijkstra;
pub mod greedy_coloring;
pub mod kahns;
pub mod kruskals;
pub mod topological_sort;
pub mod traversal;

use crate::edgelist::edge_list::EdgeListError;
use crate::graph::{GraphError, NodeIndexTrait};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AlgorithmError<NI: NodeIndexTrait> {
    QueueCapacityExceeded,
    StackCapacityExceeded,
    EdgeCapacityExceeded,
    CycleDetected,
    ResultCapacityExceeded,
    GraphError(GraphError<NI>),
}

impl<NI: NodeIndexTrait> From<GraphError<NI>> for AlgorithmError<NI> {
    fn from(e: GraphError<NI>) -> Self {
        AlgorithmError::GraphError(e)
    }
}

impl<NI: NodeIndexTrait> From<EdgeListError<NI>> for AlgorithmError<NI> {
    fn from(e: EdgeListError<NI>) -> Self {
        match e {
            EdgeListError::GraphError(ge) => AlgorithmError::GraphError(ge),
            EdgeListError::EdgeNodeError(_) => AlgorithmError::GraphError(GraphError::NodeNotFound),
        }
    }
}
