// SPDX-License-Identifier: Apache-2.0

//! Edge structures
//!
//! This module implements various structures to compose into
//! edge lists, along with iterators to traverse them.

use core::{
    iter::{FusedIterator, IntoIterator},
    marker::PhantomData,
    ops::Deref,
};

mod edges_to_nodes;

pub use edges_to_nodes::{EdgeNodeError, EdgesToNodesIterator};

/// Node index NI pairs array of E elements, every item a valid edge
#[derive(Debug)]
pub struct EdgeStruct<const E: usize, NI>(pub [(NI, NI); E]);
/// Node index NI pairs array of E elements, optionally populated
#[derive(Debug)]
pub struct EdgeStructOption<const E: usize, NI>(pub [Option<(NI, NI)>; E]);
/// Node index NI pairs array of E elements, with value V
#[derive(Debug)]
pub struct EdgeValueStruct<const E: usize, NI, V>(pub [(NI, NI, V); E]);
/// Node index NI pairs array of E elements, with value V, optionally populated
#[derive(Debug)]
pub struct EdgeValueStructOption<const E: usize, NI, V>(pub [Option<(NI, NI, V)>; E]);
/// Node index NI pairs E elements, in two parallel arrays
#[derive(Debug)]
pub struct TwoArrayEdgeStruct<const E: usize, NI>(pub [NI; E], pub [NI; E]);
/// Node index NI pairs E elements, with edge value V, in three parallel arrays
#[derive(Debug)]
pub struct TwoArrayEdgeValueStruct<const E: usize, NI, V>(pub [NI; E], pub [NI; E], pub [V; E]);
#[cfg(feature = "heapless")]
#[derive(Debug, Default)]
struct EdgeVec<const E: usize, NI>(heapless::Vec<(NI, NI), E>);
#[cfg(feature = "heapless")]
#[derive(Debug, Default)]
struct EdgeVecValue<const E: usize, NI, V>(heapless::Vec<(NI, NI, V), E>);

/// Extension of [`EdgeRef`] that provides access to edge values
///
/// This trait allows retrieving values associated with edges in addition
/// to the basic edge reference functionality.
pub trait EdgeRefValue<V>: EdgeRef {
    fn get_edge_value(&self, index: usize) -> Option<&V>;
}

/// Reference to an edge, represented as a pair of node indices
///
/// This trait provides basic access to edge data in edge collections.
/// It's used to implement iterators and provide a common interface
/// for accessing edge information.
pub trait EdgeRef {
    type NodeIndex;
    /// Reference to an edge at given index
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)>;
    /// Check if edge at index exists
    fn valid_edge(&self, index: usize) -> bool {
        index < self.capacity()
    }
    /// Total capacity of the container
    fn capacity(&self) -> usize;
}

// #region EdgeStruct variants

// Deref
impl<const E: usize, NI> Deref for EdgeStruct<E, NI> {
    type Target = [(NI, NI); E];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
// Implement EdgeRef for slices of (NI, NI)
impl<NI> EdgeRef for &[(NI, NI)] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}
// Implement EdgeRef for mutable slices of (NI, NI)
impl<NI> EdgeRef for &mut [(NI, NI)] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}
// Implement EdgeRef for fixed-size arrays of (NI, NI)
impl<NI, const E: usize> EdgeRef for [(NI, NI); E] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}
// The wrapper struct forwards to the array implementation
impl<const E: usize, NI> EdgeRef for EdgeStruct<E, NI>
where
    [(NI, NI); E]: EdgeRef<NodeIndex = NI>,
{
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        (**self).get_edge(index)
    }
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
}

// #endregion EdgeStruct variants

// #region EdgeStructOption variants

impl<const E: usize, NI> Deref for EdgeStructOption<E, NI> {
    type Target = [Option<(NI, NI)>; E];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<NI> EdgeRef for &[Option<(NI, NI)>] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        Some((&self[index].as_ref()?.0, &self[index].as_ref()?.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
    fn valid_edge(&self, index: usize) -> bool {
        index < self.capacity() && self[index].is_some()
    }
}

impl<NI> EdgeRef for &mut [Option<(NI, NI)>] {
    type NodeIndex = NI;

    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        Some((&self[index].as_ref()?.0, &self[index].as_ref()?.1))
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn valid_edge(&self, index: usize) -> bool {
        index < self.capacity() && self[index].is_some()
    }
}

impl<NI, const E: usize> EdgeRef for [Option<(NI, NI)>; E] {
    type NodeIndex = NI;

    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        Some((&self[index].as_ref()?.0, &self[index].as_ref()?.1))
    }

    fn capacity(&self) -> usize {
        self.len()
    }

    fn valid_edge(&self, index: usize) -> bool {
        index < self.capacity() && self[index].is_some()
    }
}

impl<const E: usize, NI> EdgeRef for EdgeStructOption<E, NI>
where
    [Option<(NI, NI)>; E]: EdgeRef<NodeIndex = NI>,
{
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        (**self).get_edge(index)
    }
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
    fn valid_edge(&self, index: usize) -> bool {
        (**self).valid_edge(index)
    }
}

impl<const E: usize, NI> Default for EdgeStructOption<E, NI> {
    fn default() -> Self {
        Self(core::array::from_fn(|_| None))
    }
}

// #endregion EdgeStructOption variants

// #region EdgeValueStruct variants

impl<const E: usize, NI, V> Deref for EdgeValueStruct<E, NI, V> {
    type Target = [(NI, NI, V); E];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// Implement EdgeRef for slices of (NI, NI, V)
impl<NI, V> EdgeRef for &[(NI, NI, V)] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}

impl<NI, V> EdgeRef for &mut [(NI, NI, V)] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}

impl<NI, V> EdgeRefValue<V> for &[(NI, NI, V)] {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        self.get(index).map(|e| &e.2)
    }
}

impl<NI, V> EdgeRefValue<V> for &mut [(NI, NI, V)] {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        self.get(index).map(|e| &e.2)
    }
}

impl<const E: usize, NI, V> EdgeRef for [(NI, NI, V); E] {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.len()
    }
}

impl<const E: usize, NI, V> EdgeRef for EdgeValueStruct<E, NI, V> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        (**self).get_edge(index)
    }
    fn capacity(&self) -> usize {
        (**self).capacity()
    }
}

impl<const E: usize, NI, V> EdgeRefValue<V> for [(NI, NI, V); E] {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        self.get(index).map(|e| &e.2)
    }
}

impl<const E: usize, NI, V> EdgeRefValue<V> for EdgeValueStruct<E, NI, V> {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        self.0.get(index).map(|e| &e.2)
    }
}

// #endregion

// #region EdgeValueStructOption variants
// todo: plain array version of this

impl<const E: usize, NI, V> Deref for EdgeValueStructOption<E, NI, V> {
    type Target = [Option<(NI, NI, V)>; E];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const E: usize, NI, V> EdgeRef for EdgeValueStructOption<E, NI, V> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.0.get(index)?;
        Some((&edge.as_ref()?.0, &edge.as_ref()?.1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
    fn valid_edge(&self, index: usize) -> bool {
        index < self.capacity() && self.0[index].is_some()
    }
}

impl<const E: usize, NI, V> Default for EdgeValueStructOption<E, NI, V> {
    fn default() -> Self {
        Self(core::array::from_fn(|_| None))
    }
}

impl<const E: usize, NI, V> EdgeRefValue<V> for EdgeValueStructOption<E, NI, V> {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        let edge = self.0.get(index)?;
        Some(&edge.as_ref()?.2)
    }
}
// #endregion EdgeValueStructOption variants

// #region TwoArrayEdgeStruct variants

// no Deref, it doesn't make sense here

impl<const E: usize, NI> EdgeRef for ([NI; E], [NI; E]) {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge0 = self.0.get(index)?;
        let edge1 = self.1.get(index)?;
        Some((edge0, edge1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}
impl<NI> EdgeRef for (&[NI], &[NI]) {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge0 = self.0.get(index)?;
        let edge1 = self.1.get(index)?;
        Some((edge0, edge1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<NI> EdgeRef for (&mut [NI], &mut [NI]) {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge0 = self.0.get(index)?;
        let edge1 = self.1.get(index)?;
        Some((edge0, edge1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

impl<const E: usize, NI> EdgeRef for TwoArrayEdgeStruct<E, NI> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge0 = self.0.get(index)?;
        let edge1 = self.1.get(index)?;
        Some((edge0, edge1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

// #endregion TwoArrayEdgeStruct variants

// #region TwoArrayEdgeValueStruct variants

// no Deref, it doesn't make sense
// todo: plain array version of this

impl<const E: usize, NI, V> EdgeRef for TwoArrayEdgeValueStruct<E, NI, V> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge0 = self.0.get(index)?;
        let edge1 = self.1.get(index)?;
        Some((edge0, edge1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}
impl<const E: usize, NI, V> EdgeRefValue<V> for TwoArrayEdgeValueStruct<E, NI, V> {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        let edge = self.2.get(index)?;
        Some(edge)
    }
}

// #endregion TwoArrayEdgeStruct variants

// #region EdgeVec variants

#[cfg(feature = "heapless")]
impl<const E: usize, NI> EdgeRef for EdgeVec<E, NI> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.0.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

#[cfg(feature = "heapless")]
impl<const E: usize, NI> EdgeRef for heapless::Vec<(NI, NI), E> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
}

// #endregion EdgeVec variants

// #region EdgeVecValue variants

#[cfg(feature = "heapless")]
impl<const E: usize, NI, V> EdgeRef for EdgeVecValue<E, NI, V> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.0.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.0.len()
    }
}

#[cfg(feature = "heapless")]
impl<const E: usize, NI, V> EdgeRef for heapless::Vec<(NI, NI, V), E> {
    type NodeIndex = NI;
    fn get_edge(&self, index: usize) -> Option<(&Self::NodeIndex, &Self::NodeIndex)> {
        let edge = self.get(index)?;
        Some((&edge.0, &edge.1))
    }
    fn capacity(&self) -> usize {
        self.capacity()
    }
}

#[cfg(feature = "heapless")]
impl<const E: usize, NI, V> EdgeRefValue<V> for EdgeVecValue<E, NI, V> {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        let edge = self.0.get(index)?;
        Some(&edge.2)
    }
}

#[cfg(feature = "heapless")]
impl<const E: usize, NI, V> EdgeRefValue<V> for heapless::Vec<(NI, NI, V), E> {
    fn get_edge_value(&self, index: usize) -> Option<&V> {
        let edge = self.get(index)?;
        Some(&edge.2)
    }
}

// #region EdgeVecValue variants

macro_rules! define_edge_iterator {
    (
        $(#[$attr:meta])*
        $name:ident,
        $(lifetime: $lifetime:lifetime,)?
        struct_ref: $struct_ref:ty,
        item: $item:ty,
        $(where_clause: $where_clause:tt,)?
        get_edge: $get_edge:expr
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

impl <$($lifetime,)? T> $name<$($lifetime,)? T>
where
    T: EdgeRef,
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
    T: EdgeRef,
    $( T::NodeIndex: $where_clause )?
{
    type Item = ($item, $item);
    fn next(&mut self) -> Option<Self::Item> {
        while !self.struct_ref.valid_edge(self.index) {
            self.index += 1;
            if self.index >= self.struct_ref.capacity() {
                return None;
            }
        }
        if self.index < self.back_index {
            self.last_index = self.index;
            self.index += 1;
            ($get_edge)(self.struct_ref.get_edge(self.last_index))
        } else {
            None
        }
    }
}

impl<$($lifetime,)? T> DoubleEndedIterator for $name<$($lifetime,)? T>
where
    T: EdgeRef,
    $( T::NodeIndex: $where_clause )?
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.overflow {
            return None;
        }
        while !self.struct_ref.valid_edge(self.back_index) {
            if let Some(val) = self.back_index.checked_sub(1) {
                self.back_index = val;
            } else {
                return None;
            }
        }
        if self.back_index >= self.index {
            self.last_back_index = self.back_index;
            (self.back_index, self.overflow) = self.back_index.overflowing_sub(1);
            ($get_edge)(self.struct_ref.get_edge(self.last_back_index))
        } else {
            None
        }
    }
}
}
}
define_edge_iterator!(
    /// By-reference iterator over the edges, for any struct that implements [`EdgeRef`]
    EdgeRefIterator,
    lifetime: 'a,
    struct_ref: &'a T,
    item: &'a T::NodeIndex,
    get_edge: |edge| edge
);

define_edge_iterator!(
    /// Owning iterator over the edges, for any struct that implements [`EdgeRef`]
    EdgeOwningIterator,
    struct_ref: T,
    item: T::NodeIndex,
    where_clause: Copy,
    get_edge: |edge: Option<(&T::NodeIndex, &T::NodeIndex)>| edge.map(|(src, dst)| (*src, *dst))
);

impl<T> FusedIterator for EdgeRefIterator<'_, T> where T: EdgeRef {}

/* This can't be made into a blanket impl */
macro_rules! edge_struct_into_iter {
    ($struct_name:ident, $($gen:ident),*) => {
        impl<const E: usize, $($gen,)* > IntoIterator for $struct_name<E, $($gen,)*>
        where
            Self: EdgeRef<NodeIndex=NI>, NI: Copy,
        {
            type IntoIter = EdgeOwningIterator<Self >;
            type Item = <EdgeOwningIterator<Self > as Iterator>::Item;
            fn into_iter(self) -> Self::IntoIter {
                EdgeOwningIterator::new(self)
            }
        }
    };
}

edge_struct_into_iter!(EdgeStruct, NI);
edge_struct_into_iter!(EdgeStructOption, NI);
edge_struct_into_iter!(EdgeValueStruct, NI, V);
edge_struct_into_iter!(EdgeValueStructOption, NI, V);
edge_struct_into_iter!(TwoArrayEdgeStruct, NI);
edge_struct_into_iter!(TwoArrayEdgeValueStruct, NI, V);
#[cfg(feature = "heapless")]
edge_struct_into_iter!(EdgeVec, NI);
#[cfg(feature = "heapless")]
edge_struct_into_iter!(EdgeVecValue, NI, V);

/// Iterator that yields edge value refs with indices
pub struct EdgeStructValueIterator<'a, T, V> {
    inner: EdgeRefIterator<'a, T>,
    _phantom: PhantomData<&'a V>,
}

impl<'a, T, V> Iterator for EdgeStructValueIterator<'a, T, V>
where
    T: EdgeRefValue<V>,
{
    type Item = (&'a T::NodeIndex, &'a T::NodeIndex, Option<&'a V>);
    fn next(&mut self) -> Option<Self::Item> {
        while self.inner.index < self.inner.struct_ref.capacity() {
            if let Some((src, dst)) = self.inner.next() {
                let value = self.inner.struct_ref.get_edge_value(self.inner.last_index);
                return Some((src, dst, value));
            }
        }
        None
    }
}
impl<T, V> DoubleEndedIterator for EdgeStructValueIterator<'_, T, V>
where
    T: EdgeRefValue<V>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some((src, dst)) = self.inner.next_back() {
            let value = self
                .inner
                .struct_ref
                .get_edge_value(self.inner.last_back_index);
            Some((src, dst, value))
        } else {
            None
        }
    }
}

/// Provide a reference iterator over edges
/// Trait for iterating over edges in an edge collection
///
/// Provides read-only iteration over edge references. This trait is
/// automatically implemented for any type that implements [`EdgeRef`].
pub trait EdgesIterable {
    type Node;
    // todo: Maybe doesn't need to be DoubleEnded
    type Iter<'a>: DoubleEndedIterator<Item = (&'a Self::Node, &'a Self::Node)>
    where
        Self: 'a;
    /// Return iterator that yields edge references
    fn iter_edges(&self) -> Self::Iter<'_>;
}

impl<T> EdgesIterable for T
where
    T: EdgeRef,
{
    type Node = T::NodeIndex; // (&NI, &NI)
    type Iter<'a>
        = EdgeRefIterator<'a, T>
    where
        Self: 'a;
    fn iter_edges(&self) -> Self::Iter<'_> {
        EdgeRefIterator::new(self)
    }
}

/// Trait for iterating over edges with their associated values
///
/// Extends [`EdgesIterable`] to provide iteration over both edges and their
/// values. This trait is automatically implemented for any type that implements
/// [`EdgeRefValue`].
pub trait EdgeValuesIterable<V>: EdgesIterable {
    type IterValues<'a>: DoubleEndedIterator<Item = (&'a Self::Node, &'a Self::Node, Option<&'a V>)>
    where
        Self: 'a,
        V: 'a;
    fn iter_edges_values(&self) -> Self::IterValues<'_>;
}
impl<T, V> EdgeValuesIterable<V> for T
where
    T: EdgeRefValue<V>,
{
    type IterValues<'a>
        = EdgeStructValueIterator<'a, T, V>
    where
        Self: 'a,
        V: 'a;
    fn iter_edges_values(&self) -> Self::IterValues<'_> {
        Self::IterValues {
            inner: EdgeRefIterator::new(self),
            _phantom: PhantomData,
        }
    }
}

/// Trait for edge collections that support adding and removing edges
///
/// This trait allows dynamic addition and removal of edges to/from an edge collection,
/// returning the index where the edge was inserted/removed if successful.
pub trait MutableEdges<NI: PartialEq> {
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize>;
    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize>;
}

/// Trait for edge collections that support adding and removing edges with associated values
///
/// This trait allows dynamic addition and removal of edges along with their values to/from an
/// edge collection, returning the index where the edge was inserted/removed if successful.
pub trait MutableEdgeValue<NI: PartialEq, V> {
    fn add_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize>;
    fn remove_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize>;
}

impl<const E: usize, NI: PartialEq> MutableEdges<NI> for EdgeStructOption<E, NI> {
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| x.is_none()) {
            self.0[index] = Some(edge);
            Some(index)
        } else {
            None
        }
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| x.as_ref() == Some(&edge)) {
            self.0[index] = None;
            Some(index)
        } else {
            None
        }
    }
}
impl<const E: usize, NI: PartialEq> MutableEdges<NI> for [Option<(NI, NI)>; E] {
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.iter().position(|x| x.is_none()) {
            self[index] = Some(edge);
            Some(index)
        } else {
            None
        }
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.iter().position(|x| x.as_ref() == Some(&edge)) {
            self[index] = None;
            Some(index)
        } else {
            None
        }
    }
}
impl<NI: PartialEq> MutableEdges<NI> for &mut [Option<(NI, NI)>] {
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.iter().position(|x| x.is_none()) {
            self[index] = Some(edge);
            Some(index)
        } else {
            None
        }
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.iter().position(|x| x.as_ref() == Some(&edge)) {
            self[index] = None;
            Some(index)
        } else {
            None
        }
    }
}
impl<const E: usize, NI: PartialEq, V: PartialEq> MutableEdgeValue<NI, V>
    for EdgeValueStructOption<E, NI, V>
{
    fn add_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| x.is_none()) {
            self.0[index] = Some(edge);
            Some(index)
        } else {
            None
        }
    }

    fn remove_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| x.as_ref() == Some(&edge)) {
            self.0[index] = None;
            Some(index)
        } else {
            None
        }
    }
}

// Dual implementation: EdgeValueStructOption can also implement MutableEdges
// by using Default values when no explicit value is provided
impl<const E: usize, NI: PartialEq, V: PartialEq + Default> MutableEdges<NI>
    for EdgeValueStructOption<E, NI, V>
{
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        // Add with default value
        self.add_edge_value((edge.0, edge.1, V::default()))
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        // Find and remove edge by source/destination only, ignoring value
        if let Some(index) = self.0.iter().position(|x| {
            if let Some((src, dst, _)) = x.as_ref() {
                *src == edge.0 && *dst == edge.1
            } else {
                false
            }
        }) {
            self.0[index] = None;
            Some(index)
        } else {
            None
        }
    }
}
#[cfg(feature = "heapless")]
impl<const E: usize, NI: PartialEq> MutableEdges<NI> for EdgeVec<E, NI> {
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        self.0.push(edge).ok().map(|_| self.0.len() - 1)
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| *x == edge) {
            self.0.remove(index);
            Some(index)
        } else {
            None
        }
    }
}
#[cfg(feature = "heapless")]
impl<const E: usize, NI: PartialEq, V: PartialEq> MutableEdgeValue<NI, V>
    for EdgeVecValue<E, NI, V>
{
    fn add_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize> {
        self.0.push(edge).ok().map(|_| self.0.len() - 1)
    }

    fn remove_edge_value(&mut self, edge: (NI, NI, V)) -> Option<usize> {
        if let Some(index) = self.0.iter().position(|x| *x == edge) {
            self.0.remove(index);
            Some(index)
        } else {
            None
        }
    }
}

// Dual implementation: EdgeVecValue can also implement MutableEdges
// by using Default values when no explicit value is provided
#[cfg(feature = "heapless")]
impl<const E: usize, NI: PartialEq, V: PartialEq + Default> MutableEdges<NI>
    for EdgeVecValue<E, NI, V>
{
    fn add_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        // Add with default value
        self.add_edge_value((edge.0, edge.1, V::default()))
    }

    fn remove_edge(&mut self, edge: (NI, NI)) -> Option<usize> {
        // Find and remove edge by source/destination only, ignoring value
        if let Some(index) = self.0.iter().position(|x| x.0 == edge.0 && x.1 == edge.1) {
            self.0.remove(index);
            Some(index)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::fmt::Debug;

    fn use_edges<T, NI>(edges: &T)
    where
        T: EdgesIterable<Node = NI>,
        NI: core::fmt::Debug + PartialEq + Ord,
    {
        for edge in edges.iter_edges() {
            let foo = edge;
            assert!(foo.0 < foo.1);
        }
        for revedge in edges.iter_edges().rev() {
            let foo = revedge;
            assert!(foo.0 < foo.1);
        }
    }

    fn iterate_over<T, NI>(x: &T, cmp: &[(&NI, &NI)])
    where
        T: EdgesIterable<Node = NI>,
        NI: core::fmt::Debug + PartialEq,
    {
        let mut iter = x.iter_edges();
        let arr: [(&NI, &NI); 3] = core::array::from_fn(|_| iter.next().unwrap());
        assert_eq!(&arr, cmp);
    }

    #[test]
    fn test_basic_corner_cases() {
        let edge_list = EdgeStruct::<0, usize>([]);
        let iter = &mut edge_list.into_iter();
        assert!(iter.next().is_none());
        let edge_list = EdgeStruct([(2, 3)]);
        let iter = &mut edge_list.into_iter();
        assert_eq!(iter.next(), Some((2, 3)));
        assert!(iter.next().is_none());
    }

    static EXPECTED: [(&usize, &usize); 3] = [(&0, &1), (&1, &20), (&2, &3)];

    #[test]
    fn test_edges_array() {
        let edge_list = [(0, 1), (1, 20), (2, 3)];
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_slice() {
        let edge_list = [(0, 1), (1, 20), (2, 3)].as_slice();
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_mut_slice() {
        let mut arr = [(0, 1), (1, 20), (2, 3)];
        let edge_list = arr.as_mut_slice();
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_value_slice() {
        let arr = [(0, 1, 'a'), (1, 20, 'b'), (2, 3, 'c')];
        let edge_list = arr.as_slice();
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_value_mut_slice() {
        let mut arr = [(0, 1, 'a'), (1, 20, 'b'), (2, 3, 'c')];
        let edge_list = arr.as_mut_slice();
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_edgestruct() {
        let edge_list = EdgeStruct::<3, usize>([(0, 1), (1, 20), (2, 3)]);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
        use_edges(&edge_list);
    }
    #[test]
    fn test_edges_edgestruct_option() {
        let edge_list = EdgeStructOption::<3, usize>([Some((0, 1)), Some((1, 20)), Some((2, 3))]);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }
    #[test]
    fn test_edges_edgestruct_option_free_slots() {
        let edge_list =
            EdgeStructOption::<4, usize>([Some((0, 1)), Some((1, 20)), None, Some((2, 3))]);
        iterate_over(&edge_list, &EXPECTED);
    }
    #[test]
    fn test3() {
        let edge_list: EdgeValueStruct<3, usize, char> =
            EdgeValueStruct([(0, 1, 'a'), (1, 20, 'b'), (2, 3, 'c')]);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }
    #[test]
    fn test4() {
        let edge_list: EdgeValueStructOption<4, usize, char> = EdgeValueStructOption([
            Some((0, 1, 'a')),
            None,
            Some((1, 20, 'b')),
            Some((2, 3, 'c')),
        ]);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }
    #[test]
    fn test5() {
        let edge_list = TwoArrayEdgeStruct::<3, usize>([0, 1, 2], [1, 20, 3]);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }

    #[test]
    fn test6() {
        let edge_list =
            TwoArrayEdgeValueStruct::<3, usize, _>([0, 1, 2], [1, 20, 3], ['b', 'c', 'd']);
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test8() {
        let edge_list =
            EdgeVec::<3, usize>(heapless::Vec::from_slice(&[(0, 1), (1, 20), (2, 3)]).unwrap());
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }
    #[cfg(feature = "heapless")]
    #[test]
    fn test9() {
        let edge_list = EdgeVecValue::<3, usize, _>(
            heapless::Vec::from_slice(&[(0, 1, 'a'), (1, 20, 'b'), (2, 3, 'c')]).unwrap(),
        );
        iterate_over(&edge_list, &EXPECTED);
        (&edge_list).iter_edges();
    }

    #[test]
    fn edge_values_iterable() {
        fn test<'a, NI, V, T>(t: &'a T, cmp: &[V])
        where
            T: EdgeValuesIterable<V, Node = NI>,
            NI: PartialEq + Ord + 'a,
            V: Default + Debug + Copy + PartialEq + 'a,
        {
            let mut collect = [V::default(); 8];
            let mut len = 0;
            for edge in t.iter_edges_values().zip(collect.iter_mut()) {
                if let Some(v) = edge.0 .2 {
                    *edge.1 = *v;
                    len += 1;
                }
            }
            assert_eq!(&collect[..len], cmp);
        }
        fn test_from_front_back<'a, NI, V, T>(
            t: &'a T,
            from_front: isize,
            vfront: Option<&V>,
            from_back: isize,
            vback: Option<&V>,
        ) where
            T: EdgeValuesIterable<V, Node = NI>,
            NI: PartialEq + Ord + 'a,
            V: Default + Debug + Copy + PartialEq + 'a,
        {
            let mut iterator = t.iter_edges_values();
            if from_front >= 0 {
                assert_eq!(
                    iterator.nth(from_front as usize).map(|x| x.2.unwrap()),
                    vfront
                );
            }
            assert_eq!(
                iterator.rev().nth(from_back as usize).map(|x| x.2.unwrap()),
                vback
            );
        }
        let edges = EdgeValueStruct([(0, 1, 'a'), (1, 20, 'b'), (2, 3, 'c')]);
        test(&edges, &['a', 'b', 'c']);
        test_from_front_back(&edges, 0, Some(&'a'), 0, Some(&'c'));
        test_from_front_back(&edges, 1, Some(&'b'), 0, Some(&'c'));
        test_from_front_back(&edges, 2, Some(&'c'), 0, None);
        test_from_front_back(&edges, 3, None, 3, None);
        test_from_front_back(&edges, -1, None, 1, Some(&'b'));
        test_from_front_back(&edges, -1, None, 2, Some(&'a'));
        test_from_front_back(&edges, -1, None, 3, None);

        let edges = TwoArrayEdgeValueStruct::<3, usize, _>(
            [0, 1, 2],
            [1, 20, 3],
            [Some('b'), None, Some('d')],
        );
        test(&edges, &[Some('b'), None, Some('d')]);
        let edges =
            EdgeValueStructOption([Some((0, 1, 'a')), None, None, Some((1, 20, 'b')), None]);
        test(&edges, &['a', 'b']);

        let value_array = [(0, 1, 'x'), (1, 20, 'y'), (2, 3, 'z')];
        let value_slice = value_array.as_slice();
        test(&value_slice, &['x', 'y', 'z']);

        let mut mut_value_array = [(0, 1, 'x'), (1, 20, 'y'), (2, 3, 'z')];
        let value_mut_slice = mut_value_array.as_mut_slice();
        test(&value_mut_slice, &['x', 'y', 'z']);
    }

    #[test]
    fn test_mutable_edges_trait() {
        // Test adding edges using the renamed trait
        let mut edges = EdgeStructOption::<5, u32>([None, None, None, None, None]);

        // Test add_edge
        assert_eq!(edges.add_edge((1, 2)), Some(0));
        assert_eq!(edges.add_edge((3, 4)), Some(1));
        assert_eq!(edges.add_edge((5, 6)), Some(2));

        // Verify edges were added
        assert_eq!(edges.0[0], Some((1, 2)));
        assert_eq!(edges.0[1], Some((3, 4)));
        assert_eq!(edges.0[2], Some((5, 6)));

        // Test that remove_edge now works
        assert_eq!(edges.remove_edge((1, 2)), Some(0));
        assert_eq!(edges.0[0], None);

        // Test removing non-existent edge
        assert_eq!(edges.remove_edge((99, 100)), None);
    }

    #[test]
    fn test_mutable_edges_with_values() {
        // Test with edge values
        let mut edges = EdgeValueStructOption::<3, u32, &str>([None, None, None]);

        // Test add_edge_value with values
        assert_eq!(edges.add_edge_value((1, 2, "first")), Some(0));
        assert_eq!(edges.add_edge_value((3, 4, "second")), Some(1));

        // Verify edges were added
        assert_eq!(edges.0[0], Some((1, 2, "first")));
        assert_eq!(edges.0[1], Some((3, 4, "second")));

        // Test capacity limit
        assert_eq!(edges.add_edge_value((5, 6, "third")), Some(2));
        assert_eq!(edges.add_edge_value((7, 8, "fourth")), None); // Should fail
    }

    #[test]
    fn test_remove_edge_edgestruct_option() {
        let mut edges =
            EdgeStructOption::<5, u32>([Some((1, 2)), Some((3, 4)), None, Some((5, 6)), None]);

        // Test removing existing edge
        assert_eq!(edges.remove_edge((3, 4)), Some(1));
        assert_eq!(edges.0[1], None);

        // Test removing edge from middle
        assert_eq!(edges.remove_edge((1, 2)), Some(0));
        assert_eq!(edges.0[0], None);

        // Test removing non-existent edge
        assert_eq!(edges.remove_edge((99, 100)), None);

        // Verify remaining edge is intact
        assert_eq!(edges.0[3], Some((5, 6)));
        assert_eq!(edges.remove_edge((5, 6)), Some(3));
        assert_eq!(edges.0[3], None);
    }

    #[test]
    fn test_remove_edge_option_array() {
        let mut edges: [Option<(u32, u32)>; 4] =
            [Some((10, 20)), None, Some((30, 40)), Some((50, 60))];

        // Test removing existing edge
        assert_eq!(edges.remove_edge((30, 40)), Some(2));
        assert_eq!(edges[2], None);

        // Test removing first edge
        assert_eq!(edges.remove_edge((10, 20)), Some(0));
        assert_eq!(edges[0], None);

        // Test removing non-existent edge
        assert_eq!(edges.remove_edge((99, 100)), None);

        // Verify last edge is intact
        assert_eq!(edges[3], Some((50, 60)));
    }

    #[test]
    fn test_remove_edge_option_slice() {
        let mut array = [Some((1, 2)), Some((3, 4)), None, Some((5, 6))];
        let mut edges = array.as_mut_slice();

        // Test removing existing edge
        assert_eq!(edges.remove_edge((3, 4)), Some(1));
        assert_eq!(edges[1], None);

        // Test removing edge that doesn't exist
        assert_eq!(edges.remove_edge((99, 100)), None);

        // Verify other edges are intact
        assert_eq!(edges[0], Some((1, 2)));
        assert_eq!(edges[3], Some((5, 6)));
    }

    #[test]
    fn test_remove_edge_with_values() {
        let mut edges = EdgeValueStructOption::<4, u32, &str>([
            Some((1, 2, "first")),
            Some((3, 4, "second")),
            None,
            Some((5, 6, "third")),
        ]);

        // Test removing edge with value
        assert_eq!(edges.remove_edge_value((3, 4, "second")), Some(1));
        assert_eq!(edges.0[1], None);

        // Test removing with wrong value (should not match)
        assert_eq!(edges.remove_edge_value((1, 2, "wrong")), None);
        assert_eq!(edges.0[0], Some((1, 2, "first"))); // Should still be there

        // Test removing with correct value
        assert_eq!(edges.remove_edge_value((1, 2, "first")), Some(0));
        assert_eq!(edges.0[0], None);

        // Verify remaining edge
        assert_eq!(edges.0[3], Some((5, 6, "third")));
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_remove_edge_vec() {
        let mut edges = EdgeVec::<10, u32>(heapless::Vec::new());

        // Add some edges
        edges.add_edge((1, 2));
        edges.add_edge((3, 4));
        edges.add_edge((5, 6));

        assert_eq!(edges.0.len(), 3);

        // Test removing middle edge (should shift elements)
        assert_eq!(edges.remove_edge((3, 4)), Some(1));
        assert_eq!(edges.0.len(), 2);
        assert_eq!(edges.0[0], (1, 2));
        assert_eq!(edges.0[1], (5, 6)); // Should have shifted

        // Test removing non-existent edge
        assert_eq!(edges.remove_edge((99, 100)), None);
        assert_eq!(edges.0.len(), 2);

        // Test removing first edge
        assert_eq!(edges.remove_edge((1, 2)), Some(0));
        assert_eq!(edges.0.len(), 1);
        assert_eq!(edges.0[0], (5, 6));
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_remove_edge_vec_with_values() {
        let mut edges = EdgeVecValue::<10, u32, &str>(heapless::Vec::new());

        // Add some edges
        edges.add_edge_value((1, 2, "first"));
        edges.add_edge_value((3, 4, "second"));
        edges.add_edge_value((5, 6, "third"));

        assert_eq!(edges.0.len(), 3);

        // Test removing edge with value
        assert_eq!(edges.remove_edge_value((3, 4, "second")), Some(1));
        assert_eq!(edges.0.len(), 2);
        assert_eq!(edges.0[0], (1, 2, "first"));
        assert_eq!(edges.0[1], (5, 6, "third")); // Should have shifted

        // Test removing with wrong value
        assert_eq!(edges.remove_edge_value((1, 2, "wrong")), None);
        assert_eq!(edges.0.len(), 2);

        // Test removing with correct value
        assert_eq!(edges.remove_edge_value((1, 2, "first")), Some(0));
        assert_eq!(edges.0.len(), 1);
        assert_eq!(edges.0[0], (5, 6, "third"));
    }

    #[test]
    fn test_remove_edge_comprehensive() {
        // Test edge case: empty container
        let mut edges = EdgeStructOption::<3, u32>([None, None, None]);
        assert_eq!(edges.remove_edge((1, 2)), None);

        // Test edge case: single edge
        edges.add_edge((1, 2));
        assert_eq!(edges.remove_edge((1, 2)), Some(0));
        assert_eq!(edges.0[0], None);

        // Test edge case: duplicate edges
        let mut edges = EdgeStructOption::<5, u32>([
            Some((1, 2)),
            Some((1, 2)), // Duplicate
            Some((3, 4)),
            None,
            None,
        ]);

        // Should remove first occurrence
        assert_eq!(edges.remove_edge((1, 2)), Some(0));
        assert_eq!(edges.0[0], None);
        assert_eq!(edges.0[1], Some((1, 2))); // Duplicate should remain

        // Remove the duplicate
        assert_eq!(edges.remove_edge((1, 2)), Some(1));
        assert_eq!(edges.0[1], None);

        // Now it should not find any more
        assert_eq!(edges.remove_edge((1, 2)), None);
    }

    #[test]
    fn test_dual_implementation_edge_value_struct() {
        // Test that EdgeValueStructOption can implement both traits
        let mut edges = EdgeValueStructOption::<5, u32, i32>([None, None, None, None, None]);

        // Test using MutableEdgeValue trait
        assert_eq!(edges.add_edge_value((1, 2, 100)), Some(0));
        assert_eq!(edges.add_edge_value((3, 4, 200)), Some(1));

        // Test using MutableEdges trait (should use default value)
        assert_eq!(edges.add_edge((5, 6)), Some(2));

        // Verify what was stored
        assert_eq!(edges.0[0], Some((1, 2, 100)));
        assert_eq!(edges.0[1], Some((3, 4, 200)));
        assert_eq!(edges.0[2], Some((5, 6, 0))); // Default value for i32 is 0

        // Test removing with MutableEdges (ignores value)
        assert_eq!(edges.remove_edge((1, 2)), Some(0)); // Should remove by source/dest only
        assert_eq!(edges.0[0], None);

        // Test removing with MutableEdgeValue (exact match required)
        assert_eq!(edges.remove_edge_value((3, 4, 200)), Some(1));
        assert_eq!(edges.0[1], None);

        // Verify remaining edge
        assert_eq!(edges.0[2], Some((5, 6, 0)));
    }

    #[cfg(feature = "heapless")]
    #[test]
    fn test_dual_implementation_edge_vec_value() {
        // Test that EdgeVecValue can implement both traits
        let mut edges = EdgeVecValue::<10, u32, i32>(heapless::Vec::new());

        // Test using MutableEdgeValue trait
        edges.add_edge_value((1, 2, 100));
        edges.add_edge_value((3, 4, 200));

        // Test using MutableEdges trait (should use default value)
        edges.add_edge((5, 6));

        assert_eq!(edges.0.len(), 3);
        assert_eq!(edges.0[0], (1, 2, 100));
        assert_eq!(edges.0[1], (3, 4, 200));
        assert_eq!(edges.0[2], (5, 6, 0)); // Default value for i32 is 0

        // Test removing with MutableEdges (ignores value, matches by source/dest)
        assert_eq!(edges.remove_edge((1, 2)), Some(0)); // Should remove by source/dest only
        assert_eq!(edges.0.len(), 2);
        assert_eq!(edges.0[0], (3, 4, 200)); // Should have shifted

        // Test removing with MutableEdgeValue (exact match required)
        assert_eq!(edges.remove_edge_value((3, 4, 200)), Some(0));
        assert_eq!(edges.0.len(), 1);
        assert_eq!(edges.0[0], (5, 6, 0));
    }
}
