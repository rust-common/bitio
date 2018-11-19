extern crate base2;
extern crate int;

use base2::Base2;
use int::UInt;

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

pub trait BitWrite {
    fn write_u8(&mut self, value: u8, size: u8) -> std::io::Result<()>;
    // Little-endian.
    fn write<T: UInt>(&mut self, value: T, size: u8) -> std::io::Result<()> {
        fold_size(
            size,
            &mut |o, s, _| self.write_u8((value >> o).as_(), s),
            ()
        )
    }
}

pub trait BitRead {
    fn read_u8(&mut self, size: u8) -> std::io::Result<u8>;
    // Little-endian.
    fn read<T: UInt>(&mut self, size: u8) -> std::io::Result<T> {
        fold_size(
            size,
            &mut |o, s, r| Ok(r | (T::from_u8(self.read_u8(s)?) << o)),
            T::_0
        )
    }
}

pub struct BitWriteAdapter<'t> {
    w: &'t mut std::io::Write,
    buffer: u8,
    // 0..7
    size: u8,
}

impl<'t> BitWriteAdapter<'t> {
    fn write_buffer(&mut self) -> std::io::Result<()> {
        self.w.write_all(&[self.buffer])
    }
    pub fn io_drop(&mut self) -> std::io::Result<()> {
        if self.size > 0 {
            self.write_buffer()?;
            self.size = 0;
        }
        Ok(())
    }
}

impl<'t> Drop for BitWriteAdapter<'t> {
    fn drop(&mut self) {
        let _ignore_error = self.io_drop();
    }
}

impl<'t> BitWrite for BitWriteAdapter<'t> {
    // size is in [0..8]
    fn write_u8(&mut self, mut value: u8, size: u8) -> std::io::Result<()> {
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
}

/// Creates a `BitWrite` object and pass it to the given scope function `f`.
///
/// ```
/// let mut v = vec![];
/// {
///     use bitrw::BitWrite;
///     let mut c = std::io::Cursor::new(&mut v);
///     bitrw::with_bit_writer(&mut c, &mut |w| {
///         w.write(0_u8, 0)?; //  0
///         w.write(1_u16, 1)?; //  1
///         w.write(2_u32, 2)?; //  3
///         w.write(3_u64, 3)?; //  6
///         w.write(4_u128, 4)?; // 10
///         w.write(5_usize, 5)?; // 15
///         w.write(6_u8, 6)?; // 21
///         w.write(0xFFFF_u16, 12)?; // 32
///         Ok(())
///     });
/// }
/// assert_eq!(v, [0b00_011_10_1, 0b0_00101_01, 0b111_00011, 0b11111111, 0b1]);
/// ```
pub fn with_bit_writer<R>(
    w: &mut std::io::Write,
    f: &mut Fn(&mut BitWriteAdapter) -> std::io::Result<R>
) -> std::io::Result<R> {
    let mut adapter = BitWriteAdapter { w: w, buffer: 0, size: 0 };
    let result = f(&mut adapter)?;
    adapter.io_drop()?;
    Ok(result)
}

/// Provides `BitRead` from a `Read`.
///
/// ```
/// use bitrw::BitRead;
/// let mut c = std::io::Cursor::new(&[0b00_11_10_1_0, 0b1_110_101_1, 0b1101000]);
/// let mut r = bitrw::BitReadAdapter::new(&mut c);
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
pub struct BitReadAdapter<'t> {
    r: &'t mut std::io::Read,
    buffer: u8,
    // 0..7
    size: u8,
}

impl<'t> BitReadAdapter<'t> {
    pub fn new(r: &'t mut std::io::Read) -> Self {
        Self { r: r, buffer: 0, size: 0 }
    }
}

impl<'t> BitRead for BitReadAdapter<'t> {
    fn read_u8(&mut self, size: u8) -> std::io::Result<u8> {
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
}
