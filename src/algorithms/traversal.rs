use crate::graph::{GraphRef, NodeIndexTrait};
use crate::visited::VisitedTracker;

pub fn dfs_recursive_unchecked<G, NI, VT, F>(
    graph: &G,
    start_node: &NI,
    visited: &mut VT,
    operation: &mut F,
) -> Result<(), G::Error>
where
    G: GraphRef<NI>,
    NI: NodeIndexTrait + core::fmt::Debug,
    VT: VisitedTracker<NI> + ?Sized,
    for<'a> F: FnMut(&'a NI),
{
    if !visited.is_visited(start_node) {
        visited.mark_visited(start_node);
        operation(start_node);
    }
    for next_node in graph.outgoing_edges(start_node)? {
        log::info!("Visiting node: {:?}", next_node);
        if !visited.is_visited(next_node) {
            dfs_recursive_unchecked(graph, next_node, visited, operation)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edgelist::edge_list::EdgeList;
    use test_log::test;

    struct Collector<T, const N: usize> {
        nodes: [T; N],
        index: usize,
    }
    impl<T: Default, const N: usize> Collector<T, N> {
        fn new() -> Self {
            Self {
                nodes: core::array::from_fn(|_| T::default()),
                index: 0,
            }
        }
        fn push(&mut self, node: T) {
            self.nodes[self.index] = node;
            self.index += 1;
        }
        fn result(&self) -> &[T] {
            &self.nodes[..self.index]
        }
    }

    #[test]
    fn test_dfs_recursive_unchecked() {
        let graph =
            EdgeList::<8, _, _>::new([(0usize, 1usize), (0, 2), (1, 2), (2, 0), (2, 3), (3, 3)]);
        let mut visited = [false; 16];
        let mut collector = Collector::<usize, 16>::new();
        dfs_recursive_unchecked(&graph, &0, visited.as_mut_slice(), &mut |x| {
            collector.push(*x);
        })
        .unwrap();
        assert_eq!(collector.result(), &[0, 1, 2, 3]);
    }
}
