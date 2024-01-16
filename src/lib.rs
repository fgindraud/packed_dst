#![feature(trusted_len)]
#![feature(ptr_metadata)]
#![feature(layout_for_ptr)]
#![feature(unsize)]

use std::alloc::{Layout, LayoutError};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

pub struct Box<Fields: FieldSequence> {
    /// Points to header with metadata. DST fields follow in repr C layout.
    packed_allocation: NonNull<Fields::Metadata>,
}

impl<FS: FieldSequence> Box<FS> {
    pub fn new<IS: InitializerSequence<FS>>(initializers: IS) -> Result<Self, LayoutError> {
        let (layout, metadata) = initializers.pack_fields()?;
        unsafe {
            let base = std::alloc::alloc(layout);
            let base = NonNull::new(base).unwrap_or_else(|| std::alloc::handle_alloc_error(layout));
            let mut header = base.cast::<FS::Metadata>();
            // From there to Box all operations are moves. No panic should occur.
            header.as_ptr().write(metadata);
            initializers.initialize_fields(base.as_ptr(), header.as_mut());
            Ok(Box {
                packed_allocation: header,
            })
        }
    }

    pub fn fields(&self) -> FS::Ref<'_> {
        unsafe {
            let base = self.packed_allocation.as_ptr().cast();
            FS::deref(self.packed_allocation.as_ref(), base)
        }
    }

    pub fn fields_mut(&mut self) -> FS::RefMut<'_> {
        unsafe {
            let base = self.packed_allocation.as_ptr().cast();
            FS::deref_mut(self.packed_allocation.as_mut(), base)
        }
    }

    pub fn layout(&self) -> Layout {
        unsafe { FS::layout(self.packed_allocation.as_ref()) }
    }
}

impl<FS: FieldSequence> Drop for Box<FS> {
    fn drop(&mut self) {
        unsafe {
            let layout = FS::layout(self.packed_allocation.as_ref());
            let base = self.packed_allocation.as_ptr().cast();
            FS::drop_in_place(self.packed_allocation.as_mut(), base);
            std::ptr::drop_in_place(self.packed_allocation.as_ptr()); // Metadata block
            std::alloc::dealloc(base, layout)
        }
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Represent a sequence of concatenated fields.
///
/// This defines the metadata and field operations for the whole packed DST bundle.
/// This trait is already implemented for [`tuple`] of various sizes.
///
/// It can be implemented on custom structs for a nicer interface, but requires unsafe.
/// A better extension strategy is to make a wrapper around [`Box`] with the needed types.
pub unsafe trait FieldSequence {
    /// Compound metadata for the sequence (tuple of metadata usually).
    type Metadata;

    /// References to fields (usually packed in a tuple)
    type Ref<'m>
    where
        Self: 'm;
    /// `mut` references to fields (usually packed in a tuple)
    type RefMut<'m>
    where
        Self: 'm;

    /// Allocation layout for packed field sequence and metadata header
    ///
    /// SAFETY: must match layout from [`InitializerSequence::pack_fields`]
    fn layout(metadata: &Self::Metadata) -> Layout;

    unsafe fn deref(metadata: &Self::Metadata, base: *const u8) -> Self::Ref<'_>;
    unsafe fn deref_mut(metadata: &mut Self::Metadata, base: *mut u8) -> Self::RefMut<'_>;
    unsafe fn drop_in_place(metadata: &mut Self::Metadata, base: *mut u8);
}

/// Represent a sequence of initializer that can initialize a [`FieldSequence`]
pub unsafe trait InitializerSequence<Fields: FieldSequence> {
    /// Compute the packed [`Layout`] and the set of field [`FieldSequence::Metadata`].
    ///
    /// SAFETY: layout must match with [`FieldSequence::layout`] on the returned metadata.
    fn pack_fields(&self) -> Result<(Layout, Fields::Metadata), LayoutError>;

    unsafe fn initialize_fields(self, base: *mut u8, metadata: &mut Fields::Metadata);
}

// T
unsafe impl<F: Field> FieldSequence for F {
    type Metadata = Metadata<F>;
    type Ref<'m> = &'m F::Target where Self: 'm;
    type RefMut<'m> = &'m mut F::Target where Self: 'm;

    fn layout(metadata: &Self::Metadata) -> Layout {
        // SAFETY: successfully computed once if metadata exists.
        unsafe {
            let layout = Layout::new::<<F as FieldSequence>::Metadata>();
            let (layout, _) = layout.extend(metadata.field.layout()).unwrap_unchecked();
            layout.pad_to_align()
        }
    }
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
    fn pack_fields(&self) -> Result<(Layout, <F as FieldSequence>::Metadata), LayoutError> {
        let layout = Layout::new::<<F as FieldSequence>::Metadata>();
        let (layout, metadata) = extend_layout_with_field(self, &layout)?;
        Ok((layout.pad_to_align(), metadata))
    }

    unsafe fn initialize_fields(
        self,
        base: *mut u8,
        metadata: &mut <F as FieldSequence>::Metadata,
    ) {
        metadata.initialize_field(base, self)
    }
}

// (T0, T1)
unsafe impl<F0: Field, F1: Field> FieldSequence for (F0, F1) {
    type Metadata = (Metadata<F0>, Metadata<F1>);
    type Ref<'m> = (&'m F0::Target, &'m F1::Target) where Self: 'm;
    type RefMut<'m> = (&'m mut F0::Target, &'m mut F1::Target) where Self: 'm;

    fn layout(metadata: &Self::Metadata) -> Layout {
        // SAFETY: successfully computed once if metadata exists.
        unsafe {
            let layout = Layout::new::<<(F0, F1) as FieldSequence>::Metadata>();
            let (layout, _) = layout.extend(metadata.0.field.layout()).unwrap_unchecked();
            let (layout, _) = layout.extend(metadata.1.field.layout()).unwrap_unchecked();
            layout.pad_to_align()
        }
    }
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
    fn pack_fields(&self) -> Result<(Layout, <(F0, F1) as FieldSequence>::Metadata), LayoutError> {
        let layout = Layout::new::<<(F0, F1) as FieldSequence>::Metadata>();
        let (layout, metadata0) = extend_layout_with_field(&self.0, &layout)?;
        let (layout, metadata1) = extend_layout_with_field(&self.1, &layout)?;
        Ok((layout.pad_to_align(), (metadata0, metadata1)))
    }

    unsafe fn initialize_fields(
        self,
        base: *mut u8,
        metadata: &mut <(F0, F1) as FieldSequence>::Metadata,
    ) {
        metadata.0.initialize_field(base, self.0);
        metadata.1.initialize_field(base, self.1)
    }
}

///////////////////////////////////////////////////////////////////////////////

/// Indicates that a *descriptor* type can represent a DST field.
///
/// [`Self`] in this case is the field specific metadata : slice length, `dyn` vtable.
/// It is created from various initializers defined by the [`Initializer`] trait.
/// This metadata is packed with a memory offset in a [`Metadata`] struct to be able to access the field from the base allocation.
///
/// This trait is unsafe to implement, as packed DST containers will use its functions assuming invariants are met.
/// The functions themselves are unsafe due to creating reference to the DST field from raw pointers.
pub unsafe trait Field {
    /// Type stored in the field, can be a DST : `[T]`, `dyn Trait`.
    type Target: ?std::marker::Sized;

    /// Field [`Layout``] in memory
    fn layout(&self) -> Layout;

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
    /// Computes the required metadata for the field.
    /// The actual memory [`Layout`] can be retrieved from [`Field::layout`].
    fn analyze(&self) -> Result<Field, LayoutError>;

    /// Initialize the allocation memory with the content of the initializer.
    ///
    /// SAFETY: `field_addr` must match the layout requirements of [`Self::analyze`].
    unsafe fn initialize(self, field_addr: *mut u8, descriptor: &mut Field);
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
    unsafe fn initialize_field<T: Initializer<F>>(&mut self, base: *mut u8, initializer: T) {
        let field_addr = base.offset(self.offset());
        initializer.initialize(field_addr, &mut self.field)
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
        // Also works on Sized as deref_mut points to the MaybeUninit.
        std::ptr::drop_in_place(self.deref_mut(base));
    }
}

fn extend_layout_with_field<F, T>(
    initializer: &T,
    layout: &Layout,
) -> Result<(Layout, Metadata<F>), LayoutError>
where
    F: Field,
    T: Initializer<F>,
{
    let field = initializer.analyze()?;
    let (layout, offset) = layout.extend(field.layout())?;
    let metadata = Metadata { offset, field };
    Ok((layout, metadata))
}

///////////////////////////////////////////////////////////////////////////////

/// Represent a normal sized field.
pub struct Sized<T> {
    /// Store the sized field in metadata header and keep DST field zero sized.
    /// This enable Rust layout optimizations to work, and automatically packs sized fields at the front.
    ///
    /// - starts uninit at [`Initializer::analyze`]
    /// - copied as uninit in the allocation
    /// - initialized during [`Initializer::initialize`]
    /// - can be safely deref if successful using [`MaybeUninit::assume_init_ref`] (and mut)
    /// - will be dropped by [`std::ptr::drop_in_place`] on [`Field::deref_mut`] like others, no special case needed
    value: MaybeUninit<T>,
}

unsafe impl<T> Field for Sized<T> {
    type Target = T;

    fn layout(&self) -> Layout {
        // Actual DST field is zero sized.
        Layout::new::<()>()
    }

    unsafe fn deref(&self, _field_addr: *const u8) -> &Self::Target {
        self.value.assume_init_ref()
    }
    unsafe fn deref_mut(&mut self, _field_addr: *mut u8) -> &mut Self::Target {
        self.value.assume_init_mut()
    }
}

unsafe impl<T> Initializer<Sized<T>> for T {
    fn analyze(&self) -> Result<Sized<T>, LayoutError> {
        Ok(Sized {
            value: MaybeUninit::uninit(),
        })
    }
    unsafe fn initialize(self, _field_addr: *mut u8, descriptor: &mut Sized<T>) {
        descriptor.value.write(self);
    }
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

    fn layout(&self) -> Layout {
        // SAFETY: Layout was checked in Initializer::analyze()
        unsafe { Layout::array::<T>(self.length).unwrap_unchecked() }
    }

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
    fn analyze(&self) -> Result<Slice<T>, LayoutError> {
        // Final allocation is never 0 due to metadata, so no special case.
        // If the iterator exceeds isize::MAX the final allocation would fail so no need for a size check.
        let (lower, _higher) = self.size_hint();
        let _check_layout_validity = Layout::array::<T>(lower)?;
        Ok(Slice {
            length: lower,
            _type: PhantomData,
        })
    }
    unsafe fn initialize(self, field_addr: *mut u8, descriptor: &mut Slice<T>) {
        let base: *mut T = field_addr.cast();
        let mut ptr = base;
        for v in self {
            ptr.write(v);
            ptr = ptr.offset(1);
        }
        debug_assert_eq!(base.offset(descriptor.length as isize), ptr);
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

    fn layout(&self) -> Layout {
        // SAFETY: Layout was checked in Initializer::analyze()
        unsafe { Layout::array::<u8>(self.length).unwrap_unchecked() }
    }

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
    fn analyze(&self) -> Result<Str, LayoutError> {
        let length = self.len();
        let _check_layout_validity = Layout::array::<u8>(length)?;
        Ok(Str {
            length,
            _type: PhantomData,
        })
    }
    unsafe fn initialize(self, field_addr: *mut u8, descriptor: &mut Str) {
        debug_assert_eq!(descriptor.length, self.len());
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
pub struct Unsized<Dyn: ?std::marker::Sized> {
    metadata: <Dyn as std::ptr::Pointee>::Metadata,
    _type: PhantomData<Dyn>,
}

unsafe impl<Dyn: ?std::marker::Sized> Field for Unsized<Dyn> {
    type Target = Dyn;

    fn layout(&self) -> Layout {
        // SAFETY: metadata has been initialized, and only metadata is needed for Layout::for_value_raw(ptr);
        unsafe {
            let dyn_null: *const Dyn = std::ptr::from_raw_parts(std::ptr::null(), self.metadata);
            Layout::for_value_raw(dyn_null)
        }
    }

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
    Dyn: ?std::marker::Sized,
    T: std::marker::Unsize<Dyn>,
{
    fn analyze(&self) -> Result<Unsized<Dyn>, LayoutError> {
        // Not passing the concrete Layout here may force the code to access it through the vtable.
        // This is for the allocation so not that critical for performance, and compiler may devirtualize the call anyway.
        Ok(Unsized {
            metadata: std::ptr::metadata(self as &Dyn),
            _type: PhantomData,
        })
    }
    unsafe fn initialize(self, field_addr: *mut u8, _descriptor: &mut Unsized<Dyn>) {
        let ptr: *mut T = field_addr.cast();
        ptr.write(self)
    }
}

///////////////////////////////////////////////////////////////////////////////

#[test]
fn test() {
    let mut dst: Box<(Slice<usize>, Unsized<dyn AsRef<str>>)> =
        Box::new(([42, 43].into_iter(), "blah")).unwrap();
    let (slice, string) = dst.fields();
    assert_eq!(slice, &[42, 43]);
    assert_eq!(string.as_ref(), "blah");
    dst.fields_mut().0.into_iter().for_each(|i| *i += 1);
    assert_eq!(dst.fields().0, &[43, 44]);

    let mut sized = Box::<Sized<Vec<usize>>>::new(vec![42, 43]).unwrap();
    sized.fields_mut()[0] = 0;
    assert_eq!(sized.fields(), &[0, 43]);

    let zst = Box::<Sized<()>>::new(()).unwrap(); // FIXME will fail if static offset optim

    // layouts
    assert_eq!(
        dst.layout(),
        Layout::array::<usize>(2 /*offsets*/ + 1 + 2 /*slice*/ + 1 + 2 /*dyn str*/).unwrap()
    );
    assert_eq!(
        sized.layout(),
        Layout::array::<usize>(1 /*offset*/ + 3 /*vec*/).unwrap()
    );
    assert_eq!(
        zst.layout(),
        Layout::array::<usize>(1 /*offset*/).unwrap()
    )
}
