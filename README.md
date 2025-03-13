### Heapless graphs in Rust

[![Build and test](https://github.com/kaidokert/heapless-graphs-rs/actions/workflows/build.yaml/badge.svg)](https://github.com/kaidokert/heapless-graphs-rs/actions/workflows/build.yaml)
[![Coverage Status](https://coveralls.io/repos/github/kaidokert/heapless-graphs-rs/badge.svg?branch=main)](https://coveralls.io/github/kaidokert/heapless-graphs-rs?branch=main)

Heapless graphs library. Please see crate documentation for detailed usage.

This crate provides composable building blocks for graph structures, all with
statically sized memory allocation.

The main aim is to provide very flexible and optionally compact memory storage
of graphs, suitable for using in `no_std` environments, specifically
microcontrollers.

Two types of graphs are implemented: adjacency lists and edge lists, both
implement the same shared trait for a graph.

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
```

This is still quite a raw draft, with none of the APIs stable for use, see
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
