use ::std::io::{Read, Write, Seek, SeekFrom, Result, Error, ErrorKind};

/// A pseudo reader which raises an error after specified bytes reading.
/// 
/// Read bytes until error raising are 0x00, 0x01, ... (n & 0xff for n-th byte.)
pub struct ErrorRaisingReader {
    raise_after: usize,
    total_read: usize,
}

impl ErrorRaisingReader {
    /// Create a new instance of `ErrorRaisingReader`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// extern crate debugutil;
    /// use debugutil::io::ErrorRaisingReader;
    /// use std::io::Read;
    /// 
    /// # fn main() {
    /// let mut r = ErrorRaisingReader::new(10); // an error will be raised after 10 bytes reading.
    /// let buf = &mut [0; 7];
    /// 
    /// assert_eq!(r.read(buf).unwrap(), 7);
    /// assert_eq!(buf, &[0, 1, 2, 3, 4, 5, 6]);
    /// 
    /// assert_eq!(r.read(buf).unwrap(), 3);
    /// assert_eq!(&buf[0 .. 3], &[7, 8, 9]);
    /// 
    /// assert!(r.read(buf).is_err()); // an error is raised after 10 bytes reading.
    /// # }
    /// ```
    pub fn new(raise_after: usize) -> Self {
        Self { raise_after, total_read: 0 }
    }
}

impl Read for ErrorRaisingReader {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        if self.total_read >= self.raise_after {
            return Err(error());
        }

        let size = ::std::cmp::min(self.raise_after - self.total_read, buf.len());
        for i in 0 .. size {
            buf[i] = ((self.total_read + i) & 0xff) as u8;
        }
        self.total_read += size;
        Ok(size)
    }
}

/// A pseudo writer which raises an error after specified bytes writing.
pub struct ErrorRaisingWriter {
    raise_after: usize,
}

impl ErrorRaisingWriter {
    /// Create a new instance of `ErrorRaisingWriter`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// extern crate debugutil;
    /// use debugutil::io::ErrorRaisingWriter;
    /// use std::io::Write;
    /// 
    /// # fn main() {
    /// let mut w = ErrorRaisingWriter::new(10); // an error will be raised after 10 bytes writing.
    /// let buf = &[0; 7];
    ///
    /// assert_eq!(w.write(buf).unwrap(), 7);
    /// assert!(w.flush().is_ok());
    /// assert_eq!(w.write(buf).unwrap(), 3);
    ///
    /// assert!(w.write(buf).is_err()); // an error is raised after 10 bytes writing.
    /// assert!(w.write(buf).is_err()); // an error is also raised on calling `flush()`.
    /// # }
    /// ```
    pub fn new(raise_after: usize) -> Self {
        Self { raise_after }
    }
}

impl Write for ErrorRaisingWriter {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        if self.raise_after <= 0 {
            return Err(error())
        }

        let size = ::std::cmp::min(self.raise_after, buf.len());
        self.raise_after -= size;
        Ok(size)
    }

    fn flush(&mut self) -> Result<()> {
        if self.raise_after <= 0 {
            Err(error())
        } else {
            Ok(())
        }
    }
}

/// A pseudo seeker which raises an error after specified times seeks.
pub struct ErrorRaisingSeeker {
    curr_pos: u64,
    end_pos: u64,
    raise_after: usize,
}

impl ErrorRaisingSeeker {
    /// Create a new instance of `ErrorRaisingSeeker`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// extern crate debugutil;
    /// use debugutil::io::ErrorRaisingSeeker;
    /// use std::io::{Seek, SeekFrom};
    /// 
    /// # fn main() {
    /// let mut s = ErrorRaisingSeeker::new(4096, 3); // an error will be raised after 3 seeks
    ///
    /// assert_eq!(s.seek(SeekFrom::Start(10)).unwrap(), 10);
    /// assert_eq!(s.seek(SeekFrom::End(-10)).unwrap(), 4086);
    /// assert_eq!(s.seek(SeekFrom::Current(100)).unwrap(), 4186);
    /// assert!(s.seek(SeekFrom::Start(10)).is_err());
    /// # }
    /// ```

    pub fn new(end_pos: u64, raise_after: usize) -> Self {
        Self { curr_pos: 0, end_pos, raise_after }
    }

    fn checked_calc_offset(base: u64, offset: i64) -> Option<u64> {
        if offset >= 0 {
            base.checked_add(offset as u64)
        } else {
            offset.checked_neg().and_then(|abs_offset| base.checked_sub(abs_offset as u64))
        }
    }

    fn pos_calc_error() -> Error {
        Error::new(ErrorKind::InvalidInput, "calculated position was overflowed or negative")
    }
}

impl Seek for ErrorRaisingSeeker {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        if self.raise_after <= 0 {
            return Err(error());
        }

        self.raise_after -= 1;
        self.curr_pos = match pos {
            SeekFrom::Start(offset) => {
                offset
            },
            SeekFrom::End(offset) => {
                try!(ErrorRaisingSeeker::checked_calc_offset(self.end_pos, offset).ok_or_else(Self::pos_calc_error))
            },
            SeekFrom::Current(offset) => {
                try!(ErrorRaisingSeeker::checked_calc_offset(self.curr_pos, offset).ok_or_else(Self::pos_calc_error))
            },
        };
        Ok(self.curr_pos)
    }
}

fn error() -> Error {
    Error::new(ErrorKind::Other, "planned error")
}

/// Equivalent to `ErrorRaisingReader::new`
pub fn error_raising_reader(raise_after: usize) -> ErrorRaisingReader {
    ErrorRaisingReader::new(raise_after)

}

/// Equivalent to `ErrorRaisingWriter::new`
pub fn error_raising_writer(raise_after: usize) -> ErrorRaisingWriter {
    ErrorRaisingWriter::new(raise_after)
}

/// Equivalent to `ErrorRaisingSeeker::new`
pub fn error_raising_seeker(end_pos: u64, raise_after: usize) -> ErrorRaisingSeeker {
    ErrorRaisingSeeker::new(end_pos, raise_after)
}



#[cfg(test)]
mod tests {
    use super::*;
    use ::std::error::Error;

    #[test]
    fn error_raising_reader_test() {
        let mut r = error_raising_reader(10);
        let buf = &mut [0; 7];

        assert_eq!(r.read(buf).unwrap(), 7);
        assert_eq!(buf, &[0, 1, 2, 3, 4, 5, 6]);

        assert_eq!(r.read(&mut buf[0 .. 0]).unwrap(), 0);

        assert_eq!(r.read(buf).unwrap(), 3);
        assert_eq!(&buf[0 .. 3], &[7, 8, 9]);

        let e = r.read(buf).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Other);
        assert_eq!(e.description(), "planned error");
    }

    #[test]
    fn error_raising_writer_test() {
        let mut w = error_raising_writer(10);
        let buf = &[0; 7];

        assert_eq!(w.write(buf).unwrap(), 7);
        assert_eq!(w.write(&buf[0 .. 0]).unwrap(), 0);
        assert!(w.flush().is_ok());
        assert_eq!(w.write(buf).unwrap(), 3);

        let e = w.write(buf).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Other);
        assert_eq!(e.description(), "planned error");

        let e = w.flush().unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Other);
        assert_eq!(e.description(), "planned error");
    }

    #[test]
    fn error_raising_seeker_test() {
        let mut s = error_raising_seeker(4096, 7);

        assert_eq!(s.seek(SeekFrom::Start(10)).unwrap(), 10);
        assert_eq!(s.seek(SeekFrom::End(-10)).unwrap(), 4086);
        assert_eq!(s.seek(SeekFrom::Current(100)).unwrap(), 4186);

        assert_eq!(s.seek(SeekFrom::Start(u64::max_value() - 5)).unwrap(), u64::max_value() - 5);
        let e = s.seek(SeekFrom::Current(10)).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::InvalidInput);
        assert_eq!(e.description(), "calculated position was overflowed or negative");

        let e = s.seek(SeekFrom::End(-10000)).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::InvalidInput);
        assert_eq!(e.description(), "calculated position was overflowed or negative");

        assert_eq!(s.seek(SeekFrom::Current(0)).unwrap(), u64::max_value() - 5);

        let e = s.seek(SeekFrom::Start(10)).unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Other);
        assert_eq!(e.description(), "planned error");
    }
}
