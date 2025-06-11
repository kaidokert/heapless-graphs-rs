
### Outline

Rules

- No dynamic allocation
- No unsafe
- As few trait constraints as possible, while providing functionality
- Especially, as little `Copy` as possible
- Minimal dependencies, self-contained for basic algos

Limitations
- No mutable references to graph elements - i don't think this is
  practically possible without resorting to a lot of `unsafe`
  However, graphs themselves of course can be mutable: e.g. nodes
  + edges can be added/removed.

## Core concepts

Graphs are composed of Edges ( always ) and Nodes ( sometimes ).

## Node Index or NI

All traits are generic over a notion of "Node Index" or NI, that can be
mostly any type that implements PartialEq + PartialOrd (NodeIndex).

NI also requires Copy, since iterators return owned values.

## Node + Edge structs
Nodes and Edges are arbitrary structures with different memory layouts.

Both provide NodeRef and EdgeRef traits to access elements.

On top of those, there are generic iterators that can access any structure
that implements the above traits.

There are `Iterable` and `Iterator` blanket trait implementations for all
of the above, that provide consistent interfaces to obtain either reference
or owning iterators.

## Graphs
Based on those, Graph traits are built, that provide access to edges, nodes,
edges for nodes etc.

There's a special case implemented for edges-only graph where iterator over
`nodes` is provided by a separate iterator implementation that yields all
unique node indices from edge lists.

In principle, a user can plug in their own data structure as a node and/or
edge holder, and as long as NodeRef+EdgeRef are implemented, it can be used
as part of the graph.

Values at both Nodes and Edges are optional, and are provided through
corresponding EdgeRefValue + NodeRefValue traits.

### Graph Implementations

The library provides several graph implementations:

- **EdgeList**: Stores edges as a list, good for sparse graphs
- **AdjacencyList**: Stores outgoing edges per node, optimized for outgoing_edges()
- **Matrix-based**: Adjacency matrices with various optimizations:
  - **BitMatrix**: Bit-packed matrix for unweighted graphs
  - **SimpleMatrix**: Basic matrix for weighted graphs
  - **MapMatrix**: Matrix with arbitrary node indices via mapping
  - **BitMapMatrix**: Bit-packed matrix with arbitrary node indices

### Performance Characteristics

Matrix implementations provide O(1) access for both incoming_edges() and
outgoing_edges() operations, while other implementations may fall back to
O(E) filtering of all edges for incoming_edges(). Algorithms automatically
benefit from these optimizations when available.

## Algorithms

Caller should provide all allocated storage - arrays for storing output
slice values, stack/dequeues and maps for intermediate storage. Storage
that is temporary of known size, for the algorithm use only should be
moved in and consumed.

Exception for cases where the storage size that the algo needs can be
known at compile time - then simply create that storage in the algo.
