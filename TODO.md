
All dependencies are optional

Readonly graph class
- [x] Edge only edge list
- [x] Edge+Node edge list
- [x] Implement an adjacency list graph
- [x] Adjacency list for slices of nodes
- [x] Adjacency list for Maps/dicts/StaticDict
- [x] Implement hashmap based adjacency list
- [x] Implement Adj list of a HashMap of nodes + Set of edges
- [x] Topological sort demo
- [x] Add edges tests
- [x] Remove Edges tests
- [x] Access edge values in algorithms
- [x] Access node values in algorithms
- [x] Implement MutableEdges graphs - e.g graphs with edges added / removed
- [x] Add / remove Nodes tests - some done
- [x] Implement graph-level operations using MutableNodeValue trait for nodes with values
- [x] Implement edgelist with add/remove nodes ( ? ) and edges
- [x] Make GraphError generic over NI
- [x] Maybe make GraphError take a lifetime for node refs ? (Not needed - NodeIndex is Copy)
- [ ] Check duplicate nodes in integrity_check ?
- [ ] Adjacency list AsRef[NI,C] doesn't work with heapless::Vec, figure that out
- [x] Sort out inconsistent parameter type ordering, it's all over the place. NI first ? or const usize: ?
- [x] Deal with the DoubleEndedIterator dependency - doesn't really work everywhere and shouldn't be a hard requirement
      it's currently only used by `.rev()` call in iterative DFS impl.
- [ ] clean up TODOs in code
- [ ] Provide `std` implementations of all the traits as well ? E.g. implement NodeRef for Vec etc
- [x] Consolidate error impls for algorithms
- [x] Implement an adjacency matrix
- [x] EdgesOnly is a bit useless abstraction for Adjacency List, this should work directly on the container
- [x] All struct formats in nodes/ and edges/ are just wrappers for arrays, simplify and implement
      the traits directly on arrays and slices ? (Done - traits implemented on both arrays/slices and wrappers for clarity)
- [ ] Make sure Debug/Default is derived or implemented for everything where applicable
- [ ] Map Matrices use linear search for mapping indices to NI - slow. Possibly could store a back-index

Path Finding Algorithms:
- [x] Dijkstra's Algorithm: Finds the shortest path from a source node to all other nodes in a graph with non-negative edge weights.
- [x] A* Algorithm: An extension of Dijkstra's, optimized with heuristics for pathfinding, especially useful in AI and games.
- [x] Bellman-Ford Algorithm: Finds shortest paths from a source node to all other nodes, handling graphs with negative edge weights.

Graph Traversal:
- [x] Topological Sort: Orders nodes in a Directed Acyclic Graph (DAG) such that for every directed edge u -> v, u appears before v.
- [x] Kahn's for topological sort - order a graph without considering a starting node
- [x] Connected Components: Identifies and returns all connected components in an undirected graph.

Graph Properties:
- [x] Cycle Detection: Detects cycles in a graph, useful for ensuring acyclic properties in DAGs and dependency graphs.
- [x] Strongly Connected Components (SCC): Finds SCCs in a directed graph using Kosaraju's or Tarjan's algorithm.
- [x] Minimum Spanning Tree (MST): Finds the minimum spanning tree in a graph using algorithms like Kruskal's or Prim's.
- [x] Graph Coloring: Greedy coloring algorithm to assign colors to vertices such that no adjacent vertices share the same color.

Graph Manipulation:
- [x] Node Removal: Removes a specific node and its associated edges from the graph. (implemented but lightly tested)
- [x] Node Addition: Adds a new node to the graph. (implemented but lightly tested)
- [x] Node Addition with Values: Implement GraphWithMutableNodeValues trait that uses MutableNodeValue for adding nodes with associated values
- [x] Edge Addition: Adds a new edge to the graph. (implemented but lightly tested)
- [x] Edge Removal: Removes a specific edge from the graph - how to refer to it when we have duplicates ?
- [x] Transposing a graph

Graph Measurements:
- [ ] Degree Calculation: Calculates the in-degree and out-degree of a node.
- [ ] Graph Diameter: Computes the longest shortest path between any two nodes in the graph.
- [ ] Clustering Coefficient: Measures the degree to which nodes in a graph tend to cluster together.

Flow Algorithms:
- [ ] Maximum Flow: Implements the Ford-Fulkerson or Edmonds-Karp algorithm to find the maximum flow in a flow network.
- [ ] Minimum Cut: Finds the minimum cut in a flow network using the max-flow min-cut theorem.

- [x] Convert graphs from any type to any type
- [ ] Provide a more readable user guide
- [ ] macros to construct graphs with easier syntax

## Non-goals / bad ideas:
- Can we turn DFS / BFS into iterators ? That'd be awkward as they need extra storage
- Make a mutable iterator for '&a mut T - not feasible without `unsafe` or huge deps
