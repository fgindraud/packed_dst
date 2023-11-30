#![feature(maybe_uninit_slice)]

use std::alloc::{Layout, LayoutError};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

pub struct Box<Header, Fields: FieldSequence> {
    memory: NonNull<u8>,
    _type: PhantomData<*mut (Header, Fields::Metadata)>,
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

impl<T0: Field, T1: Field> FieldSequence for (T0, T1) {
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

impl<T0: Field, T1: Field, T2: Field> FieldSequence for (T0, T1, T2) {
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

pub trait Field {
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

impl<T> Field for [MaybeUninit<T>] {
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
