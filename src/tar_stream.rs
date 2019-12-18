use std::io::{self, Write, Seek, SeekFrom};
use tar::Header;

/// A tar file builder that allows streaming the data of individual entries.  Note this still
/// requires the underlying writer to support seeking, since it backtracks after each entry to fill
/// in missing header metadata (notably, the entry size).
pub struct TarStream<W> {
    w: W,
}

pub struct TarEntryStream<W> {
    w: W,
    header: Header,
    header_pos: u64,
    data_pos: u64,
}

impl<W: Write + Seek> TarStream<W> {
    pub fn new(w: W) -> TarStream<W> {
        TarStream { w }
    }

    pub fn start_entry(mut self, h: Header) -> io::Result<TarEntryStream<W>> {
        let header_pos = self.w.seek(SeekFrom::Current(0))?;
        self.w.write_all(h.as_bytes())?;
        let data_pos = self.w.seek(SeekFrom::Current(0))?;
        Ok(TarEntryStream {
            w: self.w,
            header: h,
            header_pos,
            data_pos,
        })
    }

    pub fn finish(mut self) -> io::Result<()> {
        self.w.write_all(&[0; 1024])?;
        Ok(())
    }
}

impl<W: Write + Seek> TarEntryStream<W> {
    pub fn finish_entry(mut self) -> io::Result<TarStream<W>> {
        let start = self.data_pos;
        let end = self.w.seek(SeekFrom::Current(0))?;

        let pad = [0; 512];
        let block_off = ((end - start) % 512) as usize;
        if block_off != 0 {
            self.w.write_all(&pad[block_off..])?;
        }

        let final_pos = self.w.seek(SeekFrom::Current(0))?;

        let mut h = self.header;
        h.set_size(end - start);
        h.set_cksum();
        self.w.seek(SeekFrom::Start(self.header_pos))?;
        self.w.write_all(h.as_bytes())?;
        self.w.seek(SeekFrom::Start(final_pos))?;

        Ok(TarStream { w: self.w })
    }
}

impl<W: Write> Write for TarEntryStream<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.w.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.w.flush()
    }
}
