#![feature(trusted_len)]
#![feature(ptr_metadata)]
#![feature(unsize)]

//#![feature(maybe_uninit_slice)]

use std::alloc::{Layout, LayoutError};
use std::marker::PhantomData;
use std::mem::MaybeUninit;

/*
pub struct Box<Header, Fields: FieldSequence> {
    memory: NonNull<Header>,
    _type: PhantomData<*mut (Header, Fields::Metadata)>,
}

impl<H, FS: FieldSequence> Box<H, FS> {
    pub fn new() -> Self {
        todo!()
    }

    pub fn fields(&self) -> &FS {
        todo!() // return tuple of refs to fields
    }
}

///////////////////////////////////////////////////////////////////////////////

pub trait FieldSequence {
    type Sizes;
    type Metadata;

    fn extend_layout(
        layout: &Layout,
        size: Self::Sizes,
    ) -> Result<(Layout, Self::Metadata), LayoutError>;
}

impl<T: FieldDescriptor> FieldSequence for T {
    type Sizes = T::Size;
    type Metadata = T::MetadataFirst;

    fn extend_layout(
        layout: &Layout,
        size: Self::Sizes,
    ) -> Result<(Layout, Self::Metadata), LayoutError> {
        T::extend_layout_first(layout, size)
    }
}

impl<T0: FieldDescriptor, T1: FieldDescriptor> FieldSequence for (T0, T1) {
    type Sizes = (T0::Size, T1::Size);
    type Metadata = (T0::MetadataFirst, T1::Metadata);

    fn extend_layout(
        layout: &Layout,
        size: Self::Sizes,
    ) -> Result<(Layout, Self::Metadata), LayoutError> {
        let (layout, metadata0) = T0::extend_layout_first(layout, size.0)?;
        let (layout, metadata1) = T1::extend_layout(&layout, size.1)?;
        Ok((layout, (metadata0, metadata1)))
    }
}

impl<T0: FieldDescriptor, T1: FieldDescriptor, T2: FieldDescriptor> FieldSequence for (T0, T1, T2) {
    type Sizes = (T0::Size, T1::Size, T2::Size);
    type Metadata = (T0::MetadataFirst, T1::Metadata, T2::Metadata);

    fn extend_layout(
        layout: &Layout,
        size: Self::Sizes,
    ) -> Result<(Layout, Self::Metadata), LayoutError> {
        let (layout, metadata0) = T0::extend_layout_first(layout, size.0)?;
        let (layout, metadata1) = T1::extend_layout(&layout, size.1)?;
        let (layout, metadata2) = T2::extend_layout(&layout, size.2)?;
        Ok((layout, (metadata0, metadata1, metadata2)))
    }
}
*/

///////////////////////////////////////////////////////////////////////////////

pub unsafe trait Field {
    type Target: ?Sized;

    // Derefs take the metadata by reference to tie the lifetimes of the header to the DST lifetime.
    // Safety: base points to start of valid packed allocation to which metadata is attached, and field referenced by metadata has been initialized.
    unsafe fn deref(metadata: &Metadata<Self>, base: *const u8) -> &Self::Target;
    unsafe fn deref_mut(metadata: &mut Metadata<Self>, base: *mut u8) -> &mut Self::Target;
    unsafe fn drop_in_place(metadata: &Metadata<Self>, base: *mut u8);

    // TODO add *_first variants with layout offset computation ?
}

pub struct Metadata<F: ?Sized> {
    /// Offset of field from base of allocation, in bytes.
    offset: usize,
    /// Field specific metadata.
    field: F,
}
impl<F: ?Sized> Metadata<F> {
    // SAFETY: must be a valid metadata attached to a valid packed allocation.
    unsafe fn offset(&self) -> isize {
        // Alloc cannot allocate more than isize::MAX
        isize::try_from(self.offset).unwrap_unchecked()
    }
}

pub unsafe trait Initializer<F>
where
    F: Field,
{
    fn metadata(&self) -> Result<(Layout, F), LayoutError>;

    /// Initialize the allocation memory with the content of the initializer.
    /// The allocation is guaranteed to match the layout requirements returned by [`Self::metadata`].
    unsafe fn initialize_memory(self, allocation: *mut u8);
}

///////////////////////////////////////////////////////////////////////////////

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
    unsafe fn initialize_memory(self, allocation: *mut u8) {
        let mut ptr: *mut T = allocation.cast();
        for v in self {
            ptr.write(v);
            ptr = ptr.offset(1);
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

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
        std::ptr::drop_in_place::<Dyn>(ptr) // May call the vtable drop if actual Dyn type
    }
}

unsafe impl<Dyn, T> Initializer<Unsized<Dyn>> for T
where
    Unsized<Dyn>: Field,
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
    unsafe fn initialize_memory(self, allocation: *mut u8) {
        let ptr: *mut T = allocation.cast();
        ptr.write(self)
    }
}
