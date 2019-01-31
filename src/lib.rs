extern crate base2;
extern crate int;

/// - `size` is the size of read/write item.
/// - `f` is a read/write function.
///   1. `offset`
///   1. `size`
///   1. current `value`
/// - initial `value`
fn fold_size<R>(
    mut size: u8,
    f: &mut FnMut(u8, u8, R) -> std::io::Result<R>,
    mut result: R
) -> std::io::Result<R> {
    let mut offset = 0;
    while size >= 8 {
        result = f(offset, 8, result)?;
        offset += 8;
        size -= 8;
    }
    if size > 0 {
        result = f(offset, size, result)?;
    }
    Ok(result)
}

/// The structure is required to cache unsaved bits.
/// The unsaved bits will be written when `io_drop()` or `drop()` is called.
/// Don't create the structure directly.
/// Use the `UseBitWrite::use_bit_write()` function to write bits.
pub struct BitWrite<'t> {
    w: &'t mut std::io::Write,
    buffer: u8,
    // 0..7
    size: u8,
}

impl BitWrite<'_> {

    fn write_buffer(&mut self) -> std::io::Result<()> {
        self.w.write_all(&[self.buffer])
    }

    fn io_drop(&mut self) -> std::io::Result<()> {
        if self.size > 0 {
            self.write_buffer()?;
            self.size = 0;
        }
        Ok(())
    }

    /// - `size` is in the [0..8] range.
    fn write_u8(&mut self, mut value: u8, size: u8) -> std::io::Result<()> {
        use base2::Base2;
        value &= u8::mask(size);
        self.buffer |= value << self.size;
        self.size += size;
        if self.size >= 8 {
            self.write_buffer()?;
            self.size -= 8;
            self.buffer = value >> (size - self.size)
        }
        Ok(())
    }

    /// Little-endian bit write.
    pub fn write<T: int::UInt>(&mut self, value: T, size: u8) -> std::io::Result<()> {
        fold_size(
            size,
            &mut |o, s, _| self.write_u8((value >> o).as_(), s),
            ()
        )
    }
}

impl Drop for BitWrite<'_> {
    fn drop(&mut self) {
        let _ignore_error = self.io_drop();
    }
}

pub trait UseBitWrite: Sized + std::io::Write {
    /// Creates a `BitWrite` object and pass it to the given scope function `f`.
    ///
    /// ```
    /// let mut v = vec![];
    /// {
    ///     use bitrw::UseBitWrite;
    ///     std::io::Cursor::new(&mut v).use_bit_write(&mut |w| {
    ///         w.write(0_u8, 0)?; //  0
    ///         w.write(1_u16, 1)?; //  1
    ///         w.write(2_u32, 2)?; //  3
    ///         w.write(3_u64, 3)?; //  6
    ///         w.write(4_u128, 4)?; // 10
    ///         w.write(5_usize, 5)?; // 15
    ///         w.write(6_u8, 6)?; // 21
    ///         w.write(0xFFFF_u16, 12)?; // 33
    ///         Ok(())
    ///     });
    /// }
    /// assert_eq!(v, [0b00_011_10_1, 0b0_00101_01, 0b111_00011, 0b11111111, 0b1]);
    /// ```
    fn use_bit_write<R>(
        &mut self,
        f: &mut Fn(&mut BitWrite) -> std::io::Result<R>
    ) -> std::io::Result<R> {
        let mut adapter = BitWrite { w: self, buffer: 0, size: 0 };
        let result = f(&mut adapter)?;
        adapter.io_drop()?;
        Ok(result)
    }
}

impl<T: std::io::Write> UseBitWrite for T {}

/// Provides `BitRead` from a `Read`.
///
/// ```
/// use bitrw::UseBitRead;
/// let mut c = std::io::Cursor::new(&[0b00_11_10_1_0, 0b1_110_101_1, 0b1101000]);
/// let mut r = c.use_bit_read();
/// assert_eq!(r.read::<u8>(0).unwrap(), 0);
/// assert_eq!(r.read::<u16>(1).unwrap(), 0);
/// assert_eq!(r.read::<u32>(1).unwrap(), 1);
/// assert_eq!(r.read::<u64>(2).unwrap(), 2);
/// assert_eq!(r.read::<u128>(2).unwrap(), 3);
/// assert_eq!(r.read::<usize>(3).unwrap(), 4);
/// assert_eq!(r.read::<u8>(3).unwrap(), 5);
/// assert_eq!(r.read::<u16>(3).unwrap(), 6);
/// assert_eq!(r.read::<u32>(8).unwrap(), 0b11010001);
/// ```
pub struct BitRead<'t> {
    r: &'t mut std::io::Read,
    buffer: u8,
    // 0..7
    size: u8,
}

impl BitRead<'_> {
    fn read_u8(&mut self, size: u8) -> std::io::Result<u8> {
        use base2::Base2;
        let b16 = if self.size >= size {
            self.buffer as u16
        } else {
            let mut b = [0];
            self.r.read_exact(&mut b)?;
            let result = ((b[0] as u16) << self.size) | (self.buffer as u16);
            self.size += 8;
            result
        };
        self.size -= size;
        self.buffer = (b16 >> size) as u8;
        Ok((b16 & u16::mask(size)) as u8)
    }

    /// Little-endian bit read.
    pub fn read<T: int::UInt>(&mut self, size: u8) -> std::io::Result<T> {
        fold_size(
            size,
            &mut |o, s, r| Ok(r | (T::from_u8(self.read_u8(s)?) << o)),
            T::_0
        )
    }
}

pub trait UseBitRead: Sized + std::io::Read {
    fn use_bit_read(&mut self) -> BitRead {
        BitRead { r: self, buffer: 0, size: 0 }
    }
}

impl<T: std::io::Read> UseBitRead for T {}
