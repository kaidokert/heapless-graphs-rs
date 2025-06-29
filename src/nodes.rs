// SPDX-License-Identifier: Apache-2.0

//! Node structures
//!
//! This module implements various structures to use in both
//! edge list graphs with associated nodes and adjacency list graphs.

use core::marker::PhantomData;

/// Node index NI array of N elements, every item is a valid node
///
/// Alternatively, use an array `[NI;N]` or a slice: `&[NI]` directly
#[derive(Debug)]
pub struct NodeStruct<const N: usize, NI>(pub [NI; N]);
/// Node index NI array of N elements, nodes optionally populated
#[derive(Debug)]
pub struct NodeStructOption<const N: usize, NI>(pub [Option<NI>; N]);

/// Node index NI array of N elements, with node value V, every item is a valid node
#[derive(Debug)]
pub struct NodeValueStruct<const N: usize, NI, V>(pub [(NI, V); N]);

/// Node index NI array of N elements, with node value V, optionally populated
#[derive(Debug)]
pub struct NodeValueStructOption<const N: usize, NI, V>(pub [Option<(NI, V)>; N]);

/// Node index NI array of N elements, values in parallel array, every item is a valid node
#[derive(Debug)]
pub struct NodeValueTwoArray<const N: usize, NI, V>(pub [NI; N], pub [V; N]);

#[cfg(feature = "heapless")]
/// [Heapless vector](heapless::Vec) of node indexes
#[derive(Debug, Default)]
pub struct NodeStructVec<const N: usize, NI>(pub heapless::Vec<NI, N>);

#[cfg(feature = "heapless")]
/// [Heapless vector](heapless::Vec) of optionally populated node indexes
#[derive(Debug, Default)]
pub struct NodeStructOptionVec<const N: usize, NI>(pub heapless::Vec<Option<NI>, N>);

#[cfg(feature = "heapless")]
/// [Heapless vector](heapless::Vec) of node indexes with values
#[derive(Debug, Default)]
pub struct NodeStructVecValue<const N: usize, NI, V>(pub heapless::Vec<(NI, V), N>);

#[cfg(feature = "heapless")]
/// [Heapless vector](heapless::Vec) of optionally populated node indexes with values
#[derive(Debug, Default)]
pub struct NodeStructVecOptionValue<const N: usize, NI, V>(pub heapless::Vec<Option<(NI, V)>, N>);

/* Doesn't provide DoubleEndedIterator - not practical to use
#[cfg(feature = "heapless")]
pub struct NodeStructOptionSet<const N: usize, NI>(pub heapless::FnvIndexSet<NI, N>);
 */

/// Reference to a node, implemented for all node structures
///
/// It's used to implement iterators [`NodeRefIterator`] and
/// [`NodeOwningIterator`] through a common accessor interface
pub trait NodeRef {
    type NodeIndex;
    /// Reference to a node at given index
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex>;
    /// Check if node at index exists
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity()
    }
    /// Total capacity of the container
    fn capacity(&self) -> usize;
}

/// Extension of [`NodeRef`] that provides access to node values
///
/// This trait allows retrieving values associated with nodes in addition
/// to the basic node reference functionality.
pub trait NodeRefValue<V>: NodeRef {
    /// Returns a reference to a value of a node at index
    fn get_node_value(&self, index: usize) -> Option<&V>;
}

/// Implement NodeRef for slices directly, similar to [NodeStruct]
impl<T> NodeRef for &[T] {
    type NodeIndex = T;

    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.get(index)
    }

    fn capacity(&self) -> usize {
        self.len()
    }
}

/// Implement NodeRef for fixed-size arrays, similar to [NodeStruct]
impl<T, const N: usize> NodeRef for [T; N] {
    type NodeIndex = T;

    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.get(index)
    }

    fn capacity(&self) -> usize {
        self.len()
    }
}

impl<const N: usize, NI> NodeRef for NodeStruct<N, NI> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index)
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<const N: usize, NI> Default for NodeStruct<N, NI>
where
    NI: Default,
{
    fn default() -> Self {
        Self(core::array::from_fn(|_| NI::default()))
    }
}

impl<const N: usize, NI> NodeRef for NodeStructOption<N, NI> {
    type NodeIndex = NI;
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity() && self.0[index].is_some()
    }
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index).and_then(|ni| ni.as_ref())
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<const N: usize, NI> Default for NodeStructOption<N, NI> {
    fn default() -> Self {
        Self(core::array::from_fn(|_| None))
    }
}

impl<const N: usize, NI, V> NodeRef for NodeValueStruct<N, NI, V> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index).map(|ni| &ni.0)
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<const N: usize, NI, V> Default for NodeValueStruct<N, NI, V>
where
    NI: Default,
    V: Default,
{
    fn default() -> Self {
        Self(core::array::from_fn(|_| (NI::default(), V::default())))
    }
}

impl<const N: usize, NI, V> NodeRefValue<V> for NodeValueStruct<N, NI, V> {
    fn get_node_value(&self, index: usize) -> Option<&V> {
        self.0.get(index).map(|ni| &ni.1)
    }
}

impl<const N: usize, NI, V> NodeRef for NodeValueStructOption<N, NI, V> {
    type NodeIndex = NI;
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity() && self.0[index].is_some()
    }
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        if let Some(ni) = self.0.get(index) {
            ni.as_ref().map(|(ni, _)| ni)
        } else {
            None
        }
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}
impl<const N: usize, NI, V> Default for NodeValueStructOption<N, NI, V> {
    fn default() -> Self {
        Self(core::array::from_fn(|_| None))
    }
}

impl<const N: usize, NI, V> NodeRefValue<V> for NodeValueStructOption<N, NI, V> {
    fn get_node_value(&self, index: usize) -> Option<&V> {
        if let Some(ni) = self.0.get(index) {
            ni.as_ref().map(|(_, v)| v)
        } else {
            None
        }
    }
}

impl<const N: usize, NI, V> NodeRef for NodeValueTwoArray<N, NI, V> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index)
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<const N: usize, NI, V> Default for NodeValueTwoArray<N, NI, V>
where
    NI: Default,
    V: Default,
{
    fn default() -> Self {
        Self(
            core::array::from_fn(|_| NI::default()),
            core::array::from_fn(|_| V::default()),
        )
    }
}

impl<const N: usize, NI, V> NodeRefValue<V> for NodeValueTwoArray<N, NI, V> {
    fn get_node_value(&self, index: usize) -> Option<&V> {
        self.1.get(index)
    }
}

// #region NodeStructVec variants

#[cfg(feature = "heapless")]
impl<const N: usize, NI> NodeRef for NodeStructVec<N, NI> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index)
    }
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

/// Implement NodeRef for heapless::Vec<NI,N>, similar to [NodeStructVec]
#[cfg(feature = "heapless")]
impl<const N: usize, NI> NodeRef for heapless::Vec<NI, N> {
    type NodeIndex = NI;
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.get(index)
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
}

// #endregion NodeStructVec variants

#[cfg(feature = "heapless")]
impl<const N: usize, NI> NodeRef for NodeStructOptionVec<N, NI> {
    type NodeIndex = NI;
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity() && self.0.get(index).is_some()
    }
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index).and_then(|x| x.as_ref())
    }
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

#[cfg(feature = "heapless")]
impl<const N: usize, NI, V> NodeRef for NodeStructVecValue<N, NI, V> {
    type NodeIndex = NI;
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity() && self.0.get(index).is_some()
    }
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index).map(|(ni, _)| ni)
    }
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

#[cfg(feature = "heapless")]
impl<const N: usize, NI, V> NodeRefValue<V> for NodeStructVecValue<N, NI, V> {
    fn get_node_value(&self, index: usize) -> Option<&V> {
        self.0.get(index).map(|(_, v)| v)
    }
}

#[cfg(feature = "heapless")]
impl<const N: usize, NI, V> NodeRef for NodeStructVecOptionValue<N, NI, V> {
    type NodeIndex = NI;
    fn valid_node(&self, index: usize) -> bool {
        index < self.capacity() && self.0.get(index).is_some()
    }
    fn get_node(&self, index: usize) -> Option<&Self::NodeIndex> {
        self.0.get(index).and_then(|x| x.as_ref().map(|(ni, _)| ni))
    }
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

#[cfg(feature = "heapless")]
impl<const N: usize, NI, V> NodeRefValue<V> for NodeStructVecOptionValue<N, NI, V> {
    fn get_node_value(&self, index: usize) -> Option<&V> {
        self.0.get(index).and_then(|x| x.as_ref().map(|(_, v)| v))
    }
}

macro_rules! define_node_iterator {
    (
        $(#[$attr:meta])*
        $name:ident,
        $(lifetime: $lifetime:lifetime,)?
        struct_ref: $struct_ref:ty,
        item: $item:ty,
        $(where_clause: $where_clause:tt,)?
        get_node: $get_node:expr
    ) => {
        $(#[$attr])*
        #[derive(Clone)]
        pub struct $name<$($lifetime,)? T> {
            struct_ref: $struct_ref,
            index: usize,
            last_index: usize,
            back_index: usize,
            last_back_index: usize,
            overflow: bool,
        }
        impl<$($lifetime,)? T> $name<$($lifetime,)? T>
        where
            T: NodeRef,
            $( T::NodeIndex: $where_clause )?
        {
            pub fn new(struct_ref: $struct_ref) -> Self {
                let cap = struct_ref.capacity();
                Self {
                    struct_ref,
                    index: 0,
                    last_index: 0,
                    back_index: cap,
                    last_back_index: cap,
                    overflow: false,
                }
            }
        }

        impl<$($lifetime,)? T> Iterator for $name<$($lifetime,)? T>
        where
            T: NodeRef,
            $( T::NodeIndex: $where_clause )?
        {
            type Item = $item;
            fn next(&mut self) -> Option<Self::Item> {
                while !self.struct_ref.valid_node(self.index) {
                    self.index += 1;
                    if self.index >= self.struct_ref.capacity() {
                        return None;
                    }
                }
                if self.index < self.back_index {
                    self.last_index = self.index;
                    self.index += 1;
                    ($get_node)(self.struct_ref.get_node(self.last_index))
                } else {
                    None
                }
            }
        }

        impl<$($lifetime,)? T> DoubleEndedIterator for $name<$($lifetime,)? T>
        where
            T: NodeRef,
            $( T::NodeIndex: $where_clause )?
        {
            fn next_back(&mut self) -> Option<Self::Item> {
                if self.overflow {
                    return None;
                }
                while !self.struct_ref.valid_node(self.back_index) {
                    if let Some(val) = self.back_index.checked_sub(1) {
                        self.back_index = val;
                    } else {
                        return None;
                    }
                }
                if self.back_index >= self.index {
                    self.last_back_index = self.back_index;
                    (self.back_index, self.overflow) = self.back_index.overflowing_sub(1);
                    ($get_node)(self.struct_ref.get_node(self.last_back_index))
                } else {
                    None
                }
            }
        }
    }
}

define_node_iterator!(
    /// By-reference iterator over the nodes, for any struct that implements [`NodeRef`]
    NodeRefIterator,
    lifetime: 'a,
    struct_ref: &'a T,
    item: &'a T::NodeIndex,
    get_node: |node| node
);

define_node_iterator!(
    /// Owning iterator over the nodes, for any struct that implements [`NodeRef`]
    NodeOwningIterator,
    struct_ref: T,
    item: T::NodeIndex,
    where_clause: Copy,
    get_node: |node: Option<&T::NodeIndex> | node.copied()
);

/// Iterator that yields node value refs with indices
pub struct NodeStructValueIterator<'a, T, V> {
    inner: NodeRefIterator<'a, T>,
    _phantom: PhantomData<&'a V>,
}

impl<'a, T, V> Iterator for NodeStructValueIterator<'a, T, V>
where
    T: NodeRefValue<V>,
{
    type Item = (&'a T::NodeIndex, Option<&'a V>);
    fn next(&mut self) -> Option<Self::Item> {
        while self.inner.index < self.inner.struct_ref.capacity() {
            if let Some(node_index) = self.inner.next() {
                let val = self.inner.struct_ref.get_node_value(self.inner.last_index);
                return Some((node_index, val));
            }
        }
        None
    }
}

impl<'a, T, V> DoubleEndedIterator for NodeStructValueIterator<'a, T, V>
where
    T: NodeRefValue<V> + NodeRef,
    V: 'a,
    Self: 'a,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(node_index) = self.inner.next_back() {
            let val = self
                .inner
                .struct_ref
                .get_node_value(self.inner.last_back_index);
            Some((node_index, val))
        } else {
            None
        }
    }
}

macro_rules! node_struct_into_iter {
    ($struct_name:ident, $($gen:ident), *) => {
        impl<const N: usize, $($gen,)* > IntoIterator for $struct_name<N, $($gen,)*>
        where Self: NodeRef<NodeIndex = NI>, NI: Copy
        {
            type IntoIter = NodeOwningIterator<Self>;
            type Item = < NodeOwningIterator<Self > as Iterator>::Item;
            fn into_iter(self) -> Self::IntoIter {
                NodeOwningIterator::new(self)
            }
        }
    };
}

node_struct_into_iter!(NodeStruct, NI);
node_struct_into_iter!(NodeStructOption, NI);
node_struct_into_iter!(NodeValueStruct, NI, V);
node_struct_into_iter!(NodeValueStructOption, NI, V);
node_struct_into_iter!(NodeValueTwoArray, NI, V);

#[cfg(feature = "heapless")]
node_struct_into_iter!(NodeStructVec, NI);
#[cfg(feature = "heapless")]
node_struct_into_iter!(NodeStructOptionVec, NI);
#[cfg(feature = "heapless")]
node_struct_into_iter!(NodeStructVecValue, NI, V);
#[cfg(feature = "heapless")]
node_struct_into_iter!(NodeStructVecOptionValue, NI, V);

/// Provide a reference iterator over nodes
/// Trait for iterating over nodes in a node collection
///
/// Provides read-only iteration over node references. This trait is
/// automatically implemented for any type that implements [`NodeRef`].
pub trait NodesIterable {
    type Node;
    // todo: Maybe doesn't need to be DoubleEnded
    type Iter<'a>: DoubleEndedIterator<Item = &'a Self::Node>
    where
        Self: 'a;
    /// Return iterator that yields node references
    fn iter_nodes(&self) -> Self::Iter<'_>;
}
impl<T> NodesIterable for T
where
    T: NodeRef,
{
    type Node = T::NodeIndex;
    type Iter<'a>
        = NodeRefIterator<'a, T>
    where
        Self: 'a;

    fn iter_nodes(&self) -> Self::Iter<'_> {
        NodeRefIterator::new(self)
    }
}

/// Trait for iterating over nodes with their associated values
///
/// Extends [`NodesIterable`] to provide iteration over both nodes and their
/// values. This trait is automatically implemented for any type that implements
/// [`NodeRefValue`].
pub trait NodesValuesIterable<V>: NodesIterable {
    type IterValues<'a>: DoubleEndedIterator<Item = (&'a Self::Node, Option<&'a V>)>
    where
        <Self as NodesIterable>::Node: 'a,
        Self: 'a,
        V: 'a;
    fn iter_nodes_values(&self) -> Self::IterValues<'_>;
}

impl<T, V> NodesValuesIterable<V> for T
where
    T: NodeRefValue<V>,
{
    type IterValues<'a>
        = NodeStructValueIterator<'a, T, V>
    where
        <T as NodeRef>::NodeIndex: 'a,
        Self: 'a,
        V: 'a;
    fn iter_nodes_values(&self) -> Self::IterValues<'_> {
        Self::IterValues {
            inner: NodeRefIterator::new(self),
            _phantom: Default::default(),
        }
    }
}

/// Trait for converting node collections into owning iterators
///
/// This trait provides a way to consume a node collection and obtain an
/// iterator that owns the nodes. It's automatically implemented for any
/// type that implements [`IntoIterator`].
pub trait IntoNodesIterator {
    type Node;
    type NodeOwningIterator: Iterator<Item = Self::Node>;
    /// Returns an iterator over nodes
    fn into_nodes_iterator(self) -> Self::NodeOwningIterator;
}

impl<T> IntoNodesIterator for T
where
    T: IntoIterator,
    T::Item: PartialEq,
    <T as IntoIterator>::IntoIter: DoubleEndedIterator,
{
    type Node = T::Item;
    type NodeOwningIterator = T::IntoIter;
    fn into_nodes_iterator(self) -> Self::NodeOwningIterator {
        self.into_iter()
    }
}

/// Trait for node collections that support adding and removing nodes
///
/// This trait allows dynamic addition and removal of nodes to/from a node collection,
/// returning the index where the node was inserted/removed if successful.
pub trait MutableNodes<NI: PartialEq> {
    fn add(&mut self, node: NI) -> Option<usize>;
    fn remove(&mut self, node: NI) -> Option<usize>;
}

/// Trait for node collections that support adding and removing nodes with associated values
///
/// This trait allows dynamic addition and removal of nodes along with their values to/from a
/// node collection, returning the index where the node was inserted/removed if successful.
pub trait MutableNodeValue<NI: PartialEq, V> {
    fn add_value(&mut self, node: NI, value: V) -> Option<usize>;
    fn remove_value(&mut self, node: NI) -> Option<usize>;
}

/// # Performance Note
///
/// Both `add()` and `remove()` operations use linear search (O(n)) to find empty slots
/// or matching nodes in the array. For better performance with larger datasets, consider
/// using map-based containers instead.
impl<const N: usize, NI: PartialEq> MutableNodes<NI> for NodeStructOption<N, NI> {
    fn add(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.is_none()) {
            self.0[index] = Some(node);
            return Some(index);
        }
        None
    }

    fn remove(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.as_ref() == Some(&node)) {
            self.0[index] = None;
            return Some(index);
        }
        None
    }
}

/// # Performance Note
///
/// Both `add_value()` and `remove_value()` operations use linear search (O(n)) to find empty slots
/// or matching nodes in the array. For better performance with larger datasets, consider
/// using map-based containers instead.
impl<const N: usize, NI: PartialEq, V> MutableNodeValue<NI, V> for NodeValueStructOption<N, NI, V> {
    fn add_value(&mut self, node: NI, value: V) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.is_none()) {
            self.0[index] = Some((node, value));
            return Some(index);
        }
        None
    }

    fn remove_value(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self
            .0
            .iter()
            .position(|opt| opt.as_ref().map(|(ni, _)| ni) == Some(&node))
        {
            self.0[index] = None;
            return Some(index);
        }
        None
    }
}

// Dual implementation: NodeValueStructOption can also implement MutableNodes
// by using Default values when no explicit value is provided
impl<const N: usize, NI: PartialEq, V: Default> MutableNodes<NI>
    for NodeValueStructOption<N, NI, V>
{
    fn add(&mut self, node: NI) -> Option<usize> {
        // Add with default value
        self.add_value(node, V::default())
    }

    fn remove(&mut self, node: NI) -> Option<usize> {
        // Reuse existing remove logic from MutableNodeValue
        <Self as MutableNodeValue<NI, V>>::remove_value(self, node)
    }
}

#[cfg(feature = "heapless")]
/// # Performance Note
///
/// The `remove()` operation uses linear search (O(n)) to find matching nodes in the vector,
/// followed by shifting all subsequent elements. The `add()` operation is O(1) when capacity
/// is available. For better removal performance, consider using option-based containers.
impl<const N: usize, NI: PartialEq> MutableNodes<NI> for NodeStructVec<N, NI> {
    fn add(&mut self, node: NI) -> Option<usize> {
        self.0.push(node).ok().map(|_| self.0.len() - 1)
    }

    fn remove(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|ni| *ni == node) {
            self.0.remove(index);
            return Some(index);
        }
        None
    }
}

#[cfg(feature = "heapless")]
/// # Performance Note
///
/// Both `add()` and `remove()` operations may use linear search (O(n)). The `add()` operation
/// first searches for an empty slot, then appends if none found. The `remove()` operation
/// searches for the matching node and marks it as None, preserving indices.
impl<const N: usize, NI: PartialEq> MutableNodes<NI> for NodeStructOptionVec<N, NI> {
    fn add(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.is_none()) {
            self.0[index] = Some(node);
            return Some(index);
        }
        self.0.push(Some(node)).ok().map(|_| self.0.len() - 1)
    }

    fn remove(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.as_ref() == Some(&node)) {
            self.0[index] = None;
            return Some(index);
        }
        None
    }
}

#[cfg(feature = "heapless")]
/// # Performance Note
///
/// The `remove_value()` operation uses linear search (O(n)) to find matching nodes in the vector,
/// followed by shifting all subsequent elements. The `add_value()` operation is O(1) when capacity
/// is available. For better removal performance, consider using option-based containers.
impl<const N: usize, NI: PartialEq, V> MutableNodeValue<NI, V> for NodeStructVecValue<N, NI, V> {
    fn add_value(&mut self, node: NI, value: V) -> Option<usize> {
        self.0.push((node, value)).ok().map(|_| self.0.len() - 1)
    }

    fn remove_value(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|(ni, _)| *ni == node) {
            self.0.remove(index);
            return Some(index);
        }
        None
    }
}

#[cfg(feature = "heapless")]
/// # Performance Note
///
/// Both `add_value()` and `remove_value()` operations may use linear search (O(n)). The `add_value()` operation
/// first searches for an empty slot, then appends if none found. The `remove_value()` operation
/// searches for the matching node and marks it as None, preserving indices.
impl<const N: usize, NI: PartialEq, V> MutableNodeValue<NI, V>
    for NodeStructVecOptionValue<N, NI, V>
{
    fn add_value(&mut self, node: NI, value: V) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|opt| opt.is_none()) {
            self.0[index] = Some((node, value));
            return Some(index);
        }
        self.0
            .push(Some((node, value)))
            .ok()
            .map(|_| self.0.len() - 1)
    }

    fn remove_value(&mut self, node: NI) -> Option<usize> {
        if let Some(index) = self
            .0
            .iter()
            .position(|opt| opt.as_ref().map(|(ni, _)| ni) == Some(&node))
        {
            self.0[index] = None;
            return Some(index);
        }
        None
    }
}

// Dual implementation: NodeStructVecOptionValue can also implement MutableNodes
// by using Default values when no explicit value is provided
#[cfg(feature = "heapless")]
impl<const N: usize, NI: PartialEq, V: Default> MutableNodes<NI>
    for NodeStructVecOptionValue<N, NI, V>
{
    fn add(&mut self, node: NI) -> Option<usize> {
        // Add with default value
        self.add_value(node, V::default())
    }

    fn remove(&mut self, node: NI) -> Option<usize> {
        // Reuse existing remove logic from MutableNodeValue
        <Self as MutableNodeValue<NI, V>>::remove_value(self, node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::collect;
    use core::fmt::Debug;

    fn iterate_over<N, NI>(nodes: &N, cmp: &[NI])
    where
        N: NodesIterable<Node = NI> + ?Sized,
        NI: core::fmt::Debug + Default + PartialEq + Copy,
    {
        let mut collect_array: [NI; 8] = core::array::from_fn(|_| NI::default());
        for node in nodes.iter_nodes().zip(collect_array.iter_mut()) {
            *node.1 = *node.0;
        }

        let final_slice = &collect_array[..cmp.len()];
        assert_eq!(final_slice, cmp);
        // Ensure we can loop twice and didn't consume anything
        for _node in nodes.iter_nodes().zip(collect_array.iter_mut()) {}
    }

    static EXPECTED: [usize; 3] = [1, 3, 2];

    #[test]
    fn test_node_array_iter() {
        let nodes = [1, 3, 2];
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_slice_iter() {
        let nodes = [1, 3, 2].as_slice();
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(2 * 8, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_nodestruct_iter() {
        let nodes = NodeStruct([1, 3, 2]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_option_all() {
        let nodes = NodeStructOption([Some(1), Some(3), Some(2)]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8 * 2, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_option_some() {
        let nodes = NodeStructOption([None, Some(1), Some(3), None, Some(2)]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(5 * 8 * 2, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_value() {
        let nodes = NodeValueStruct([(1, "a"), (3, "b"), (2, "c")]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8 * 3, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_value_option_all() {
        let nodes = NodeValueStructOption([Some((1, "a")), Some((3, "b")), Some((2, "c"))]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8 * 3, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_value_option_some() {
        let nodes =
            NodeValueStructOption([None, Some((1, "a")), Some((3, "b")), None, Some((2, "c"))]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(5 * 8 * 3, core::mem::size_of_val(&nodes));
    }

    #[test]
    fn test_node_iter_value_two_array() {
        let nodes = NodeValueTwoArray([1, 3, 2], ["a", "b", "c"]);
        iterate_over(&nodes, &EXPECTED);
        assert_eq!(3 * 8 * 3, core::mem::size_of_val(&nodes));
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_node_iter_vec() {
        let nodes = NodeStructVec::<3, _>(heapless::Vec::from_slice(&[1, 3, 2]).unwrap());
        iterate_over(&nodes, &EXPECTED);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_node_iter_vec_heapless() {
        let nodes = heapless::Vec::<_, 3>::from_slice(&[1, 3, 2]).unwrap();
        iterate_over(&nodes, &EXPECTED);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_node_iter_vec_option() {
        let nodes = NodeStructOptionVec::<3, _>(
            heapless::Vec::from_slice(&[Some(1), Some(3), Some(2)]).unwrap(),
        );
        iterate_over(&nodes, &EXPECTED);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_node_iter_vec_option_value() {
        let nodes = NodeStructVecOptionValue::<3, _, _>(
            heapless::Vec::from_slice(&[Some((1, "a")), Some((3, "b")), Some((2, "c"))]).unwrap(),
        );
        iterate_over(&nodes, &EXPECTED);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_node_iter_vec_value() {
        let nodes = NodeStructVecValue::<3, _, _>(
            heapless::Vec::from_slice(&[(1, "a"), (3, "b"), (2, "c")]).unwrap(),
        );
        iterate_over(&nodes, &EXPECTED);
    }

    #[test]
    fn test_node_get_values() {
        fn test_value<V, T: NodeRefValue<V>>(nodes: &T, idx: usize, val: Option<&V>)
        where
            V: PartialEq + core::fmt::Debug,
        {
            assert_eq!(nodes.get_node_value(idx), val);
        }
        fn test_123<T: NodeRefValue<&'static str>>(nodes: &T) {
            test_value(nodes, 1, Some(&"b"));
            test_value(nodes, 2, Some(&"c"));
            test_value(nodes, 3, None);
        }
        test_123(&NodeValueStruct([(1, "a"), (3, "b"), (2, "c")]));
        test_123(&NodeValueStructOption([
            Some((1, "a")),
            Some((3, "b")),
            Some((2, "c")),
        ]));
        test_123(&NodeValueTwoArray([1, 3, 2], ["a", "b", "c"]));
        #[cfg(feature = "heapless")]
        {
            test_123(&NodeStructVecValue::<3, _, _>(
                heapless::Vec::from_slice(&[(1, "a"), (3, "b"), (2, "c")]).unwrap(),
            ));
            test_123(&NodeStructVecOptionValue::<3, _, _>(
                heapless::Vec::from_slice(&[Some((1, "a")), Some((3, "b")), Some((2, "c"))])
                    .unwrap(),
            ));
        }
    }

    fn add_node<NI: PartialEq, T: MutableNodes<NI>>(f: &mut T, to_add: NI) -> Option<usize> {
        f.add(to_add)
    }
    fn add_node_value<NI: PartialEq, V, T: MutableNodeValue<NI, V>>(
        f: &mut T,
        to_add: NI,
        value: V,
    ) -> Option<usize> {
        f.add_value(to_add, value)
    }
    fn remove_node_value<NI: PartialEq, V, T: MutableNodeValue<NI, V>>(
        f: &mut T,
        to_remove: NI,
    ) -> Option<usize> {
        f.remove_value(to_remove)
    }
    fn remove_node<NI: PartialEq, T: MutableNodes<NI>>(f: &mut T, to_remove: NI) -> Option<usize> {
        f.remove(to_remove)
    }

    #[test]
    fn test_mutable_nodes() {
        let mut nodes = NodeStructOption([None, Some(1), Some(3), None, Some(2)]);
        assert_eq!(add_node(&mut nodes, 4), Some(0));
        assert_eq!(remove_node(&mut nodes, 3), Some(2));
        iterate_over(&nodes, &[4, 1, 2]);
        assert_eq!(add_node(&mut nodes, 5), Some(2));
        assert_eq!(add_node(&mut nodes, 8), Some(3));
        assert_eq!(add_node(&mut nodes, 100), None);
    }
    #[test]
    fn test_mutable_value_nodes() {
        let mut nodes =
            NodeValueStructOption([Some((5_u8, Some('b'))), None, Some((2, Some('x')))]);
        assert_eq!(add_node_value(&mut nodes, 4, Some('c')), Some(1));
        assert_eq!(remove_node_value(&mut nodes, 2), Some(2));
        iterate_over(&nodes, &[5, 4]);
    }
    #[test]
    fn node_values_iterable() {
        fn test<NI, V, T>(t: &T, cmp: &[V])
        where
            NI: PartialEq + Debug,
            V: Default + Debug + Copy + PartialEq,
            T: NodesValuesIterable<V, Node = NI>,
        {
            let mut collect_array = [V::default(); 16];
            let mut len = 0;
            for (src, dst) in t.iter_nodes_values().zip(collect_array.iter_mut()) {
                if let Some(v) = src.1 {
                    *dst = *v;
                    len += 1;
                }
            }
            assert_eq!(&collect_array[..len], cmp);
        }
        fn test_from_front_back<NI, V, T>(
            t: &T,
            from_front: isize,
            vfront: Option<&V>,
            from_back: isize,
            vback: Option<&V>,
        ) where
            NI: PartialEq + Debug,
            V: Default + Debug + Copy + PartialEq,
            T: NodesValuesIterable<V, Node = NI>,
        {
            let mut iterator = t.iter_nodes_values();
            if from_front >= 0 {
                assert_eq!(
                    iterator.nth(from_front as usize).map(|v| v.1.unwrap()),
                    vfront
                );
            }
            assert_eq!(
                iterator.rev().nth(from_back as usize).map(|v| v.1.unwrap()),
                vback
            )
        }
        let values = NodeValueStruct([(1_usize, "a"), (3, "b"), (2, "c")]);
        test(&values, &["a", "b", "c"]);
        test_from_front_back(&values, 0, Some(&"a"), 0, Some(&"c"));
        test_from_front_back(&values, 1, Some(&"b"), 0, Some(&"c"));
        test_from_front_back(&values, 2, Some(&"c"), 0, None);
        test_from_front_back(&values, 3, None, 3, None);
        test_from_front_back(&values, -1, None, 1, Some(&"b"));
        test_from_front_back(&values, -1, None, 2, Some(&"a"));
        test_from_front_back(&values, -1, None, 3, None);
        let values = NodeValueTwoArray([1_usize, 2], ["xf", "bz"]);
        test(&values, &["xf", "bz"]);
        let values = NodeValueStructOption([
            Some((1, 'b')),
            None,
            None,
            Some((2, 'f')),
            None,
            Some((3, 'x')),
            None,
            None,
            Some((4, 'y')),
            Some((100, 'z')),
        ]);
        test(&values, &['b', 'f', 'x', 'y', 'z']);
        let values = NodeValueStructOption([
            Some((1, Some('b'))),
            None,
            Some((2, None)),
            Some((100, Some('z'))),
        ]);
        test(&values, &[Some('b'), None, Some('z')]);
    }

    #[test]
    fn test_mutable_node_value_comprehensive() {
        // Test NodeValueStructOption
        let mut nodes = NodeValueStructOption::<5, u32, &str>([None; 5]);

        // Test add_value
        assert_eq!(nodes.add_value(1, "hello"), Some(0));
        assert_eq!(nodes.add_value(2, "world"), Some(1));
        assert_eq!(nodes.add_value(3, "test"), Some(2));

        // Verify current state
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2, 3]);

        // Test remove (disambiguate since this type implements both traits)
        assert_eq!(
            <NodeValueStructOption<5, u32, &str> as MutableNodeValue<u32, &str>>::remove_value(
                &mut nodes, 2
            ),
            Some(1)
        ); // Remove middle element
        assert_eq!(
            <NodeValueStructOption<5, u32, &str> as MutableNodeValue<u32, &str>>::remove_value(
                &mut nodes, 999
            ),
            None
        ); // Remove non-existent

        // Verify after removal
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 3]);

        // Test that removed slot can be reused
        assert_eq!(nodes.add_value(4, "reuse"), Some(1));

        // Fill remaining capacity
        assert_eq!(nodes.add_value(5, "five"), Some(3));
        assert_eq!(nodes.add_value(6, "six"), Some(4));

        // Verify full state
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 4, 3, 5, 6]);

        // Test capacity limits
        assert_eq!(nodes.add_value(7, "overflow"), None);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_mutable_node_value_vec_types() {
        // Test NodeStructVecValue
        let mut vec_nodes = NodeStructVecValue::<5, u32, i32>(heapless::Vec::new());

        // Test add_value - should append to end
        assert_eq!(vec_nodes.add_value(10, 100), Some(0));
        assert_eq!(vec_nodes.add_value(20, 200), Some(1));
        assert_eq!(vec_nodes.add_value(30, 300), Some(2));

        // Verify state
        let mut collected = [0u32; 8];
        let slice = collect(vec_nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[10, 20, 30]);

        // Test remove from middle - should shift elements
        assert_eq!(vec_nodes.remove_value(20), Some(1));

        // Verify remaining elements
        let mut collected = [0u32; 8];
        let slice = collect(vec_nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[10, 30]);
    }

    #[test]
    fn test_mutable_nodes_edge_cases() {
        let mut nodes = NodeStructOption::<3, u32>([Some(1), None, Some(3)]);

        // Verify initial state
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 3]);

        // Test adding to middle slot
        assert_eq!(nodes.add(2), Some(1));

        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2, 3]);

        // Test removing and re-adding to same slot
        assert_eq!(nodes.remove(2), Some(1));
        assert_eq!(nodes.add(4), Some(1)); // Should reuse slot 1

        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 4, 3]);

        // Test full capacity
        assert_eq!(nodes.add(5), None);

        // Test removing non-existent
        assert_eq!(nodes.remove(999), None);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_option_value_container_gaps() {
        // Start with a simple test - just verify basic functionality
        let mut nodes = NodeStructVecOptionValue::<8, u32, i32>(heapless::Vec::new());

        // Add one element
        assert_eq!(nodes.add_value(1, 10), Some(0));

        // Verify state
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1]);

        // Add second element
        assert_eq!(nodes.add_value(2, 20), Some(1));

        // Verify state
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2]);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_vec_behavior_basic() {
        // Test basic Vec behavior for MutableNodes
        let mut vec_nodes = NodeStructVec::<5, u32>(heapless::Vec::new());

        // Add elements
        assert_eq!(vec_nodes.add(1), Some(0));
        assert_eq!(vec_nodes.add(2), Some(1));
        assert_eq!(vec_nodes.add(3), Some(2));

        // Verify state
        let mut collected = [0u32; 8];
        let slice = collect(vec_nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2, 3]);

        // Remove middle element (should shift)
        assert_eq!(vec_nodes.remove(2), Some(1));

        let mut collected = [0u32; 8];
        let slice = collect(vec_nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 3]); // 3 shifted down
    }

    #[test]
    fn test_dual_trait_implementation() {
        // Test that NodeValueStructOption implements both traits when V: Default
        let mut nodes = NodeValueStructOption::<5, u32, i32>([None; 5]);

        // Use as MutableNodes (adds with default values)
        assert_eq!(nodes.add(1), Some(0)); // Adds (1, 0) since i32::default() = 0
        assert_eq!(nodes.add(2), Some(1)); // Adds (2, 0)

        // Use as MutableNodeValue (adds with explicit values)
        assert_eq!(nodes.add_value(3, 100), Some(2)); // Adds (3, 100)

        // Verify all nodes exist
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2, 3]);

        // Verify values - nodes added via MutableNodes have default values
        assert_eq!(nodes.0[0], Some((1, 0))); // Default value
        assert_eq!(nodes.0[1], Some((2, 0))); // Default value
        assert_eq!(nodes.0[2], Some((3, 100))); // Explicit value

        // Remove works from either trait (need to disambiguate since both traits have remove)
        assert_eq!(
            <NodeValueStructOption<5, u32, i32> as MutableNodes<u32>>::remove(&mut nodes, 2),
            Some(1)
        );

        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 3]);
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_dual_trait_heapless_vec() {
        // Test that NodeStructVecOptionValue implements both traits when V: Default
        let mut nodes = NodeStructVecOptionValue::<8, u32, &str>(heapless::Vec::new());

        // Use as MutableNodes (adds with default values)
        assert_eq!(nodes.add(1), Some(0)); // Adds (1, "") since &str::default() = ""

        // Use as MutableNodeValue (adds with explicit values)
        assert_eq!(nodes.add_value(2, "hello"), Some(1));

        // Verify both approaches work
        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[1, 2]);

        // Verify values
        assert_eq!(nodes.0[0], Some((1, ""))); // Default value
        assert_eq!(nodes.0[1], Some((2, "hello"))); // Explicit value

        // Remove middle to create gap, then test gap filling (disambiguate remove call)
        assert_eq!(
            <NodeStructVecOptionValue<8, u32, &str> as MutableNodes<u32>>::remove(&mut nodes, 1),
            Some(0)
        );

        // Add new element - should fill the gap
        assert_eq!(nodes.add(3), Some(0));

        let mut collected = [0u32; 8];
        let slice = collect(nodes.iter_nodes().copied(), &mut collected);
        assert_eq!(slice, &[3, 2]);
    }
}
