
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
mostly any type that implements PartialEq.

NI does currently _not_ require a Copy trait, but that may need changing
for better error handling.

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
