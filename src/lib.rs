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

pub trait FieldSequence {
    type Metadata;
}

pub trait InitializerSequence<Fields>
where
    Fields: FieldSequence,
{
    fn extend_with_metadata(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, Fields::Metadata), LayoutError>;
}

impl<F: Field> FieldSequence for F {
    type Metadata = Metadata<F>;
}
impl<F, T> InitializerSequence<F> for T
where
    F: Field,
    T: Initializer<F>,
{
    fn extend_with_metadata(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, <F as FieldSequence>::Metadata), LayoutError> {
        extend_layout_with_metadata(self, layout)
    }
}

impl<F0: Field, F1: Field> FieldSequence for (F0, F1) {
    type Metadata = (Metadata<F0>, Metadata<F1>);
}
impl<F0, F1, T0, T1> InitializerSequence<(F0, F1)> for (T0, T1)
where
    F0: Field,
    F1: Field,
    T0: Initializer<F0>,
    T1: Initializer<F1>,
{
    fn extend_with_metadata(
        &self,
        layout: &Layout,
    ) -> Result<(Layout, <(F0, F1) as FieldSequence>::Metadata), LayoutError> {
        let (layout, metadata0) = extend_layout_with_metadata(&self.0, layout)?;
        let (layout, metadata1) = extend_layout_with_metadata(&self.1, &layout)?;
        Ok((layout, (metadata0, metadata1)))
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Indicates that a metadata type can represent a DST field.
///
/// [`Self`] in this case is the field specific metadata : slice length, `dyn` vtable.
/// It is created from various initializers defined by the [`Initializer`] trait.
///
/// This trait is unsafe to implement, as packed DST containers will use its functions assuming invariants are met.
/// The functions themselves are unsafe due to creating reference to the DST field from raw pointers.
pub unsafe trait Field {
    /// Type stored in the field, can be a DST : `[T]`, `dyn Trait`.
    type Target: ?Sized;

    // Derefs take the metadata by reference to tie the lifetimes of the header to the DST lifetime.
    // Safety: base points to start of valid packed allocation to which metadata is attached, and field referenced by metadata has been initialized.
    unsafe fn deref(metadata: &Metadata<Self>, base: *const u8) -> &Self::Target;
    unsafe fn deref_mut(metadata: &mut Metadata<Self>, base: *mut u8) -> &mut Self::Target;
    unsafe fn drop_in_place(metadata: &Metadata<Self>, base: *mut u8);

    // TODO add *_first variants with layout offset computation ?
}

/// Complete metadata for a [`Field`] : ties the field metadata with its offset.
pub struct Metadata<F: ?Sized> {
    /// Offset of field from base of allocation, in bytes.
    offset: usize,
    /// Field specific metadata.
    field: F,
}
impl<F: ?Sized> Metadata<F> {
    /// Offset from base of allocation in bytes.
    ///
    /// SAFETY: must be a valid metadata attached to a valid packed allocation.
    unsafe fn offset(&self) -> isize {
        // Alloc cannot allocate more than isize::MAX
        isize::try_from(self.offset).unwrap_unchecked()
    }
}

/// Defines what can initialize a [`Field`].
///
/// Initialization is split in two steps :
/// - getting layout and metadata for the packed allocation
/// - using the values to initialize the fresh allocation at the field offset.
pub unsafe trait Initializer<Field> {
    /// Computes the required layout and metadata for the field.
    fn metadata(&self) -> Result<(Layout, Field), LayoutError>;

    /// Initialize the allocation memory with the content of the initializer.
    ///
    /// `field_addr` is guaranteed to match the layout requirements of [`Self::metadata`].
    /// It must be initialized by this method.
    unsafe fn initialize_memory(self, field_addr: *mut u8);
}

fn extend_layout_with_metadata<F, T: Initializer<F>>(
    initializer: &T,
    layout: &Layout,
) -> Result<(Layout, Metadata<F>), LayoutError> {
    let (field_layout, field) = initializer.metadata()?;
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

    unsafe fn deref(metadata: &Metadata<Self>, base: *const u8) -> &Self::Target {
        std::slice::from_raw_parts(base.offset(metadata.offset()).cast(), metadata.field.length)
    }
    unsafe fn deref_mut(metadata: &mut Metadata<Self>, base: *mut u8) -> &mut Self::Target {
        std::slice::from_raw_parts_mut(base.offset(metadata.offset()).cast(), metadata.field.length)
    }
    unsafe fn drop_in_place(metadata: &Metadata<Self>, base: *mut u8) {
        let slice_addr: *mut T = base.offset(metadata.offset()).cast();
        let length = isize::try_from(metadata.field.length).unwrap_unchecked(); // Successful alloc => length < isize::MAX
        for i in 0..length {
            std::ptr::drop_in_place(slice_addr.offset(i))
        }
    }
}

unsafe impl<T, Iter> Initializer<Slice<T>> for Iter
where
    Iter: std::iter::TrustedLen<Item = T>,
{
    fn metadata(&self) -> Result<(Layout, Slice<T>), LayoutError> {
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
    unsafe fn initialize_memory(self, field_addr: *mut u8) {
        let mut ptr: *mut T = field_addr.cast();
        for v in self {
            ptr.write(v);
            ptr = ptr.offset(1);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

// TODO str support

///////////////////////////////////////////////////////////////////////////////

/// Represent a field containing an *unsized* value ([`std::marker::Unsize`]).
///
/// Can store any value, but this is most useful for storing :
/// - `dyn Trait` objects
/// - slices `[T]`, with the limitation that they must be initialized from a fixed length `[T; N]` due to the current unsize machinery
///
/// Initializers are constrained by what the unsize std machinery supports.
pub struct Unsized<Dyn> {
    metadata: <Dyn as std::ptr::Pointee>::Metadata,
    _type: PhantomData<Dyn>,
}

unsafe impl<Dyn> Field for Unsized<Dyn> {
    type Target = Dyn;

    unsafe fn deref(metadata: &Metadata<Self>, base: *const u8) -> &Self::Target {
        let value_addr = base.offset(metadata.offset());
        let ptr = std::ptr::from_raw_parts(value_addr.cast(), metadata.field.metadata);
        &*ptr
    }
    unsafe fn deref_mut(metadata: &mut Metadata<Self>, base: *mut u8) -> &mut Self::Target {
        let value_addr = base.offset(metadata.offset());
        let ptr = std::ptr::from_raw_parts_mut(value_addr.cast(), metadata.field.metadata);
        &mut *ptr
    }
    unsafe fn drop_in_place(metadata: &Metadata<Self>, base: *mut u8) {
        let value_addr = base.offset(metadata.offset());
        let ptr = std::ptr::from_raw_parts_mut(value_addr.cast(), metadata.field.metadata);
        std::ptr::drop_in_place::<Dyn>(ptr) // Will call the vtable drop if actual dyn Trait
    }
}

unsafe impl<Dyn, T> Initializer<Unsized<Dyn>> for T
where
    T: std::marker::Unsize<Dyn>,
{
    fn metadata(&self) -> Result<(Layout, Unsized<Dyn>), LayoutError> {
        let layout = Layout::for_value(self);
        let metadata = std::ptr::metadata(self as &Dyn);
        let metadata = Unsized {
            metadata,
            _type: PhantomData,
        };
        Ok((layout, metadata))
    }
    unsafe fn initialize_memory(self, field_addr: *mut u8) {
        let ptr: *mut T = field_addr.cast();
        ptr.write(self)
    }
}
