use std::alloc::Layout;
use std::marker::PhantomData;
use std::ptr::NonNull;

pub struct Box<Descriptor> {
    memory: NonNull<u8>,
    _type: PhantomData<*mut Descriptor>,
}



mod old {
    // Build a repr(C) struct
    // strategy : extract non DST stuff in repr(Rust) header. header defines size of DST.
    // build Layout with header + sequence of DST extend. Store offsets.
    // allocate. fill header and DST arrays.
    // return a "handle" ; try to make it Box<something> ?
    // access by deref or something ?
    use std::alloc::Layout;
    use std::marker::PhantomData;
    use std::ops::{Deref, DerefMut};
    use std::pin::Pin;
    struct Slice<T> {
        offset: usize, // From this struct position
        length: usize,
        _slice_type: PhantomData<[T]>,
    }

    impl<T> Deref for Slice<T> {
        type Target = [T];
        fn deref(&self) -> &Self::Target {
            unsafe {
                let slice_descriptor_addr = self.as_ptr().cast::<u8>();
                let slice_origin_addr = slice_descriptor_addr.wrapping_add(self.offset);
                std::slice::from_raw_parts(slice_origin_addr.cast(), self.length)
            }
        }
    }
    impl<T> DerefMut for Slice<T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe {
                let slice_descriptor_addr = self.as_mut_ptr().cast::<u8>();
                let slice_origin_addr = slice_descriptor_addr.wrapping_add(self.offset);
                std::slice::from_raw_parts_mut(slice_origin_addr.cast(), self.length)
            }
        }
    }

    impl<T> Slice<T> {
        const A: usize = 42;
    }

    struct InlineBuffer<T> {
        value: usize,
        buffer: Slice<T>,
    }

    impl<T: Default> InlineBuffer<T> {
        fn new(length: usize) -> Pin<Box<Self>> {
            let layout = Layout::new::<Self>();
            let (layout, slice_offset) =
                layout.extend(Layout::array::<T>(length).unwrap()).unwrap();
            let layout = layout.pad_to_align();

            let mut header = InlineBuffer {
                value: 42,
                buffer: Slice {
                    offset: slice_offset, // FIXME from field
                    length,
                    _slice_type: PhantomData,
                },
            };

            let header_addr: *const u8 = std::ptr::addr_of!(header).cast();
            let buffer_addr: *const u8 = std::ptr::addr_of!(header.buffer).cast();

            unsafe {
                header.buffer.offset -=
                    usize::try_from(buffer_addr.offset_from(header_addr)).unwrap();

                let memory = std::alloc::alloc(layout);
                memory.cast::<Self>().write(header);
                let slice: *mut T = memory.wrapping_add(slice_offset).cast();
                for i in 0..length {
                    slice.wrapping_add(i).write(T::default());
                }
                Pin::new_unchecked(Box::from_raw(memory.cast()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
    }
}
