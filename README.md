### Heapless graphs in Rust

[![crate](https://img.shields.io/crates/v/heapless_graphs.svg)](https://crates.io/crates/heapless_graphs)
[![documentation](https://docs.rs/heapless_graphs/badge.svg)](https://docs.rs/heapless_graphs/)
[![Build and test](https://github.com/kaidokert/heapless-graphs-rs/actions/workflows/build.yaml/badge.svg)](https://github.com/kaidokert/heapless-graphs-rs/actions/workflows/build.yaml)
[![Coverage Status](https://coveralls.io/repos/github/kaidokert/heapless-graphs-rs/badge.svg?branch=main)](https://coveralls.io/github/kaidokert/heapless-graphs-rs?branch=main)

Heapless graphs library. Please see crate documentation for detailed usage.

This crate provides composable building blocks for graph structures, all with
statically sized memory allocation.

The main aim is to provide very flexible and optionally compact memory storage
of graphs, suitable for using in `no_std` environments, specifically
microcontrollers.

Three types of graphs are implemented: adjacency lists, edge lists, and adjacency matrices, all
implementing the same shared trait for a graph.

Graphs storing values for nodes expose them through `GraphWithNodeValues`. When
mutability is required, the `GraphWithMutableNodeValues` trait allows adding or
removing nodes together with their values while performing the same integrity
checks as normal node insertion/removal. At the moment this capability is
available on `EdgeNodeList` only, as adjacency-list and matrix graphs do not
store node values.

Code example with a simple graph:
```Rust
   // Make a graph from edges and nodes
   let graph = EdgeNodeList::new(
     [(1_usize, 5), (5, 3), (7, 7)],
     [7, 4, 3, 1, 5]).unwrap();
   // Visited array tracker
   let mut visited = [false; 10];
   // Do a depth first traversal, starting from node 5
   dfs_recursive(&graph, 5, visited.as_mut_slice(), &mut |x| {
     println!("node: {}",x)
   });
   # Prints: node: 5, 3
```

A code golf version, with only edges:
```Rust
    dfs_recursive_unchecked(
        &EdgeList::<3, _, _>::new([(1, 5), (5, 3), (7, 7)]).unwrap(),
        5,
        [false; 10].as_mut_slice(),
        &mut |x| println!("node: {}", x),
    );
   # Prints: node: 5, 3
```

This is still quite a raw draft, with APIs subject to change, see
[TODO](TODO.md) for a long list of things that may change.

_Note:_ This is mostly a Rust learning exercise. If you are looking for
production quality graph implementations, see [petgraph](https://crates.io/crates/petgraph)
or various other [graph libraries](https://crates.io/keywords/graph).

## Contributing

Constructive criticism, suggestions and better design ideas very welcome !

See [DESIGN](DESIGN.md) for some design notes.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.
