#![feature(trusted_len)]
#![feature(ptr_metadata)]
#![feature(unsize)]

use std::alloc::{Layout, LayoutError};
use std::marker::PhantomData;
use std::ptr::NonNull;

pub struct Box<Header, Fields: FieldSequence> {
    memory: NonNull<Header>,
    _type: PhantomData<*mut (Header, Fields::Metadata)>,
}

impl<H, FS: FieldSequence> Box<H, FS> {
    pub fn new<IS: InitializerSequence<FS>>(header: H, initializers: IS) -> Self {
        todo!()
    }

    pub fn fields(&self) -> &FS {
        todo!() // return tuple of refs to fields
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Represent a sequence of concatenated fields
pub unsafe trait FieldSequence {
    /// Compound metadata for the sequence (tuple of metadata usually).
    type Metadata;

    /// Tuple of references to fields
    type Ref<'m>
    where
        Self: 'm;
    /// Tuple of mut references to fields
    type RefMut<'m>
    where
        Self: 'm;

    unsafe fn deref(metadata: &Self::Metadata, base: *const u8) -> Self::Ref<'_>;
    unsafe fn deref_mut(metadata: &mut Self::Metadata, base: *mut u8) -> Self::RefMut<'_>;
    unsafe fn drop_in_place(metadata: &mut Self::Metadata, base: *mut u8);
}

/// Represent a sequence of initializer that can initialize a [`FieldSequence`]
pub unsafe trait InitializerSequence<Fields: FieldSequence> {
    fn extend_layout_with_fields(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, Fields::Metadata), LayoutError>;

    unsafe fn initialize_fields(self, base: *mut u8, metadata: &Fields::Metadata);
}

// T
unsafe impl<F: Field> FieldSequence for F {
    type Metadata = Metadata<F>;
    type Ref<'m> = &'m F::Target where Self: 'm;
    type RefMut<'m> = &'m mut F::Target where Self: 'm;

    unsafe fn deref(metadata: &Self::Metadata, base: *const u8) -> Self::Ref<'_> {
        metadata.deref(base)
    }
    unsafe fn deref_mut(metadata: &mut Self::Metadata, base: *mut u8) -> Self::RefMut<'_> {
        metadata.deref_mut(base)
    }
    unsafe fn drop_in_place(metadata: &mut Self::Metadata, base: *mut u8) {
        metadata.drop_in_place(base)
    }
}
unsafe impl<F, T> InitializerSequence<F> for T
where
    F: Field,
    T: Initializer<F>,
{
    fn extend_layout_with_fields(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, <F as FieldSequence>::Metadata), LayoutError> {
        extend_layout_with_field(self, layout)
    }

    unsafe fn initialize_fields(self, base: *mut u8, metadata: &<F as FieldSequence>::Metadata) {
        metadata.initialize_field(base, self)
    }
}

// (T0, T1)
unsafe impl<F0: Field, F1: Field> FieldSequence for (F0, F1) {
    type Metadata = (Metadata<F0>, Metadata<F1>);
    type Ref<'m> = (&'m F0::Target, &'m F1::Target) where Self: 'm;
    type RefMut<'m> = (&'m mut F0::Target, &'m mut F1::Target) where Self: 'm;

    unsafe fn deref(metadata: &Self::Metadata, base: *const u8) -> Self::Ref<'_> {
        (metadata.0.deref(base), metadata.1.deref(base))
    }
    unsafe fn deref_mut(metadata: &mut Self::Metadata, base: *mut u8) -> Self::RefMut<'_> {
        (metadata.0.deref_mut(base), metadata.1.deref_mut(base))
    }
    unsafe fn drop_in_place(metadata: &mut Self::Metadata, base: *mut u8) {
        metadata.0.drop_in_place(base);
        metadata.1.drop_in_place(base);
    }
}
unsafe impl<F0, F1, T0, T1> InitializerSequence<(F0, F1)> for (T0, T1)
where
    F0: Field,
    F1: Field,
    T0: Initializer<F0>,
    T1: Initializer<F1>,
{
    fn extend_layout_with_fields(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, <(F0, F1) as FieldSequence>::Metadata), LayoutError> {
        let (layout, metadata0) = extend_layout_with_field(&self.0, layout)?;
        let (layout, metadata1) = extend_layout_with_field(&self.1, &layout)?;
        Ok((layout, (metadata0, metadata1)))
    }

    unsafe fn initialize_fields(
        self,
        base: *mut u8,
        metadata: &<(F0, F1) as FieldSequence>::Metadata,
    ) {
        metadata.0.initialize_field(base, self.0);
        metadata.1.initialize_field(base, self.1)
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Indicates that a metadata type can represent a DST field.
///
/// [`Self`] in this case is the field specific metadata : slice length, `dyn` vtable.
/// It is created from various initializers defined by the [`Initializer`] trait.
/// This metadata is packed with a memory offset in a [`Metadata`] struct to be able to access the field from the base allocation.
///
/// This trait is unsafe to implement, as packed DST containers will use its functions assuming invariants are met.
/// The functions themselves are unsafe due to creating reference to the DST field from raw pointers.
pub unsafe trait Field {
    /// Type stored in the field, can be a DST : `[T]`, `dyn Trait`.
    type Target: ?Sized;

    /// Derefs take the metadata by reference to tie the lifetimes of the header to the DST lifetime.
    ///
    /// SAFETY: field_addr must point to a valid initialized field that the metadata represents.
    unsafe fn deref(&self, field_addr: *const u8) -> &Self::Target;
    unsafe fn deref_mut(&mut self, field_addr: *mut u8) -> &mut Self::Target;
}

/// Defines what can initialize a [`Field`].
///
/// Initialization is split in two steps :
/// - getting layout and metadata for the packed allocation
/// - using the values to initialize the fresh allocation at the field offset.
pub unsafe trait Initializer<Field> {
    /// Computes the required layout and metadata for the field.
    fn analyze(&self) -> Result<(Layout, Field), LayoutError>;

    /// Initialize the allocation memory with the content of the initializer.
    ///
    /// SAFETY: `field_addr` must match the layout requirements of [`Self::analyze`].
    unsafe fn initialize(self, field_addr: *mut u8);
}

/// Complete metadata for a [`Field`] : ties the field metadata with its offset.
///
/// TODO add a First variant with recomputed offset ?
pub struct Metadata<F> {
    /// Offset of field from base of allocation, in bytes.
    offset: usize,
    /// Field specific metadata.
    field: F,
}

impl<F> Metadata<F> {
    /// Offset from base of allocation in bytes.
    ///
    /// SAFETY: must be a valid metadata attached to a valid packed allocation.
    unsafe fn offset(&self) -> isize {
        // Alloc cannot allocate more than isize::MAX
        isize::try_from(self.offset).unwrap_unchecked()
    }

    // SAFETY: base must have the right layout at offset for initialization.
    unsafe fn initialize_field<T: Initializer<F>>(&self, base: *mut u8, initializer: T) {
        let field_addr = base.offset(self.offset());
        initializer.initialize(field_addr)
    }
}

/// [`Field`] operations from *base* allocation pointer ; applies offset.
///
/// SAFETY: must be used on a pointer to valid initialized memory which matches the layout and offset of self.
impl<F: Field> Metadata<F> {
    unsafe fn deref(&self, base: *const u8) -> &F::Target {
        let field_addr = base.offset(self.offset());
        F::deref(&self.field, field_addr)
    }
    unsafe fn deref_mut(&mut self, base: *mut u8) -> &mut F::Target {
        let field_addr = base.offset(self.offset());
        F::deref_mut(&mut self.field, field_addr)
    }
    unsafe fn drop_in_place(&mut self, base: *mut u8) {
        // For all covered DST ([T], str, dyn trait) we can use drop_in_place(*mut DST).
        // It can be added to the Field trait in case of specialized behavior.
        std::ptr::drop_in_place(self.deref_mut(base));
    }
}

fn extend_layout_with_field<F, T: Initializer<F>>(
    initializer: &T,
    layout: &Layout,
) -> Result<(Layout, Metadata<F>), LayoutError> {
    let (field_layout, field) = initializer.analyze()?;
    let (layout, offset) = layout.extend(field_layout)?;
    let metadata = Metadata { offset, field };
    Ok((layout, metadata))
}

///////////////////////////////////////////////////////////////////////////////

/// Represents a field containing a [`std::slice`] `[T]` of dynamic length.
///
/// Slices must be initialized with a fixed length iterator of `T` values ([`std::iter::TrustedLen`]).
///
/// Partial initialization can be achieved using a slice of [`std::mem::MaybeUninit`], initialized to `uninit()`.
/// This means adding a safe interface on top to implement something akin to [`Vec`] with data inline to header.
pub struct Slice<T> {
    length: usize,
    _type: PhantomData<[T]>,
}

unsafe impl<T> Field for Slice<T> {
    type Target = [T];

    unsafe fn deref(&self, field_addr: *const u8) -> &Self::Target {
        std::slice::from_raw_parts(field_addr.cast(), self.length)
    }
    unsafe fn deref_mut(&mut self, field_addr: *mut u8) -> &mut Self::Target {
        std::slice::from_raw_parts_mut(field_addr.cast(), self.length)
    }
}

unsafe impl<T, Iter> Initializer<Slice<T>> for Iter
where
    Iter: std::iter::TrustedLen<Item = T>,
{
    fn analyze(&self) -> Result<(Layout, Slice<T>), LayoutError> {
        // Final allocation is never 0 due to metadata, so no special case.
        // If the iterator exceeds isize::MAX the final allocation would fail so no need for a size check.
        let (lower, _higher) = self.size_hint();
        let layout = Layout::array::<T>(lower)?;

        let metadata = Slice {
            length: lower,
            _type: PhantomData,
        };
        Ok((layout, metadata))
    }
    unsafe fn initialize(self, field_addr: *mut u8) {
        let mut ptr: *mut T = field_addr.cast();
        for v in self {
            ptr.write(v);
            ptr = ptr.offset(1);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Represent a field containing a [`String`].
///
/// Must be initialized by copying data from a [`&str`].
pub struct Str {
    length: usize,
    _type: PhantomData<str>, // only for type classification as DST-like
}

unsafe impl Field for Str {
    type Target = str;

    unsafe fn deref(&self, field_addr: *const u8) -> &Self::Target {
        let s = std::slice::from_raw_parts(field_addr, self.length);
        std::str::from_utf8_unchecked(s)
    }
    unsafe fn deref_mut(&mut self, field_addr: *mut u8) -> &mut Self::Target {
        let s = std::slice::from_raw_parts_mut(field_addr, self.length);
        std::str::from_utf8_unchecked_mut(s)
    }
}

unsafe impl Initializer<Str> for &'_ str {
    fn analyze(&self) -> Result<(Layout, Str), LayoutError> {
        let length = self.len();
        let layout = Layout::array::<u8>(length)?;
        let metadata = Str {
            length,
            _type: PhantomData,
        };
        Ok((layout, metadata))
    }
    unsafe fn initialize(self, field_addr: *mut u8) {
        std::ptr::copy_nonoverlapping(self.as_ptr(), field_addr, self.len())
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Represent a field containing an *unsized* value ([`std::marker::Unsize`]).
///
/// Can store any value, but this is most useful for storing :
/// - `dyn Trait` objects initialized from a concrete value
/// - slices `[T]`, that must be initialized from a fixed length `[T; N]` due to the current unsize machinery
/// - [`str`], but what are the initializers ?
///
/// Initializers are constrained by what the unsize std machinery supports.
pub struct Unsized<Dyn> {
    metadata: <Dyn as std::ptr::Pointee>::Metadata,
    _type: PhantomData<Dyn>,
}

unsafe impl<Dyn> Field for Unsized<Dyn> {
    type Target = Dyn;

    unsafe fn deref(&self, field_addr: *const u8) -> &Self::Target {
        let ptr = std::ptr::from_raw_parts(field_addr.cast(), self.metadata);
        &*ptr
    }
    unsafe fn deref_mut(&mut self, field_addr: *mut u8) -> &mut Self::Target {
        let ptr = std::ptr::from_raw_parts_mut(field_addr.cast(), self.metadata);
        &mut *ptr
    }
}

unsafe impl<Dyn, T> Initializer<Unsized<Dyn>> for T
where
    T: std::marker::Unsize<Dyn>,
{
    fn analyze(&self) -> Result<(Layout, Unsized<Dyn>), LayoutError> {
        let layout = Layout::for_value(self);
        let metadata = std::ptr::metadata(self as &Dyn);
        let metadata = Unsized {
            metadata,
            _type: PhantomData,
        };
        Ok((layout, metadata))
    }
    unsafe fn initialize(self, field_addr: *mut u8) {
        let ptr: *mut T = field_addr.cast();
        ptr.write(self)
    }
}
