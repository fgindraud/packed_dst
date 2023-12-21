#![feature(maybe_uninit_slice)]
#![feature(ptr_metadata)]
#![feature(trusted_len)]
#![feature(unsize)]

use std::alloc::{Layout, LayoutError};
use std::marker::{PhantomData, Unsize};
use std::mem::MaybeUninit;
use std::ptr::{NonNull, Pointee};

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

///////////////////////////////////////////////////////////////////////////////

pub trait FieldDescriptor {
    /// Type describing the field size. Passed by value as it is generally Copy.
    type Size;

    /// Metadata stored alongside the header in the packed DST
    type Metadata;
    /// Metadata if the field is the first one. Usually can avoid storing the offset.
    type MetadataFirst;

    /// Add field to an existing layout
    fn extend_layout(
        layout: &Layout,
        size: Self::Size,
    ) -> Result<(Layout, Self::Metadata), LayoutError>;
    /// Add first DST field to existing layout
    fn extend_layout_first(
        layout: &Layout,
        size: Self::Size,
    ) -> Result<(Layout, Self::MetadataFirst), LayoutError>;

    // Access object by offsetting base ptr. Ties ref on metadata to result !
    unsafe fn get<'f>(base: *const u8, metadata: &'f Self::Metadata, size: Self::Size) -> &'f Self;
    unsafe fn get_mut<'f>(
        base: *mut u8,
        metadata: &'f mut Self::Metadata,
        size: Self::Size,
    ) -> &'f mut Self;
}

pub struct MaybeUninitSliceMetadata<T> {
    offset: usize,
    _slice_type: PhantomData<[MaybeUninit<T>]>,
}

pub struct MaybeUninitSliceMetadataFirst<T> {
    _slice_type: PhantomData<[MaybeUninit<T>]>,
}

impl<T> FieldDescriptor for [MaybeUninit<T>] {
    type Size = usize;
    type Metadata = MaybeUninitSliceMetadata<T>;
    type MetadataFirst = MaybeUninitSliceMetadataFirst<T>;

    fn extend_layout(
        layout: &Layout,
        size: Self::Size,
    ) -> Result<(Layout, Self::Metadata), LayoutError> {
        let slice = Layout::array::<T>(size)?;
        let (layout, offset) = layout.extend(slice)?;
        let metadata = MaybeUninitSliceMetadata {
            offset,
            _slice_type: PhantomData,
        };
        Ok((layout, metadata))
    }
    fn extend_layout_first(
        layout: &Layout,
        size: Self::Size,
    ) -> Result<(Layout, Self::MetadataFirst), LayoutError> {
        let slice = Layout::array::<T>(size)?;
        let (layout, _offset) = layout.extend(slice)?;
        let metadata = MaybeUninitSliceMetadataFirst {
            _slice_type: PhantomData,
        };
        Ok((layout, metadata))
    }

    unsafe fn get<'f>(base: *const u8, metadata: &'f Self::Metadata, size: Self::Size) -> &'f Self {
        // Alloc cannot allocate more than isize::MAX
        let offset = isize::try_from(metadata.offset).unwrap_unchecked();
        let slice_addr = base.offset(offset);
        std::slice::from_raw_parts(slice_addr.cast(), size)
    }
    unsafe fn get_mut<'f>(
        base: *mut u8,
        metadata: &'f mut Self::Metadata,
        size: Self::Size,
    ) -> &'f mut Self {
        // Alloc cannot allocate more than isize::MAX
        let offset = isize::try_from(metadata.offset).unwrap_unchecked();
        let slice_addr = base.offset(offset);
        std::slice::from_raw_parts_mut(slice_addr.cast(), size)
    }
}

///////////////////////////////////////////////////////////////////////////////

pub trait Descriptor {
    type Metadata;
}

pub unsafe trait Initializer<Field>
where
    Field: Descriptor,
{
    fn metadata(&self) -> Result<(Layout, Field::Metadata), LayoutError>;

    /// Initialize the allocation memory with the content of the initializer.
    /// The allocation is guaranteed to match the layout requirements returned by [`Self::metadata`].
    unsafe fn initialize_memory(self, allocation: *mut u8);
}

pub struct Slice<T>(PhantomData<[T]>);

impl<T> Descriptor for Slice<T> {
    type Metadata = usize;
}

unsafe impl<T, I> Initializer<Slice<T>> for I
where
    I: std::iter::TrustedLen<Item = T>,
{
    fn metadata(&self) -> Result<(Layout, usize), LayoutError> {
        let (lower, _higher) = self.size_hint();
        // Final allocation is never 0 due to metadata, so no special case.
        // If the iterator exceeds isize::MAX the final allocation would fail so no need for a size check.
        let layout = Layout::array::<T>(lower)?;
        Ok((layout, lower))
    }
    unsafe fn initialize_memory(self, allocation: *mut u8) {
        let mut ptr: *mut T = allocation.cast();
        for v in self {
            ptr.write(v);
            ptr = ptr.offset(1);
        }
    }
}

pub struct Unsized<Dyn>(PhantomData<Dyn>);

impl<Dyn> Descriptor for Unsized<Dyn> {
    type Metadata = <Dyn as Pointee>::Metadata;
}

unsafe impl<Dyn, T> Initializer<Unsized<Dyn>> for T
where
    T: Unsize<Dyn>,
    Unsized<Dyn>: Descriptor<Metadata = <Dyn as Pointee>::Metadata>,
{
    fn metadata(&self) -> Result<(Layout, <Unsized<Dyn> as Descriptor>::Metadata), LayoutError> {
        let layout = Layout::for_value(self);
        let metadata = std::ptr::metadata(self as &Dyn);
        Ok((layout, metadata))
    }
    unsafe fn initialize_memory(self, allocation: *mut u8) {
        let ptr: *mut T = allocation.cast();
        ptr.write(self)
    }
}
