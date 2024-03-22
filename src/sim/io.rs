//! IO handling for LC-3.
//! 
//! The interface for IO devices is defined with the [`IODevice`] trait.
//! This is exposed to the simulator with the [`SimIO`] enum.
//! 
//! Besides those two key items, this module also includes:
//! - [`NoIO`]: The implementation for no IO.
//! - [`BiChannelIO`]: The basic implementation for basic IO.
//! - [`CustomIO`]: A wrapper around custom IO implementations.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::TryRecvError;
use std::sync::{mpsc, Arc};
use std::thread::JoinHandle;

const KBSR: u16 = 0xFE00;
const KBDR: u16 = 0xFE02;
const DSR: u16  = 0xFE04;
const DDR: u16  = 0xFE06;
const MCR: u16  = 0xFFFE;

/// An IO device that can be read/written to.
pub trait IODevice {
    /// Reads the data at the given memory-mapped address.
    /// 
    /// If successful, this returns the value returned from that address.
    /// If unsuccessful, this returns `None`.
    fn io_read(&self, addr: u16) -> Option<u16>;

    /// Writes the data to the given memory-mapped address.
    /// 
    /// This returns whether the write was successful or not.
    fn io_write(&self, addr: u16, data: u16) -> bool;

    /// Tries to close this IO device.
    fn close(self);
}
impl dyn IODevice {} // assert IODevice is dyn safe

/// No IO. All reads and writes are unsuccessful.
pub struct NoIO;
impl IODevice for NoIO {
    fn io_read(&self, _addr: u16) -> Option<u16> {
        None
    }

    fn io_write(&self, _addr: u16, _data: u16) -> bool {
        false
    }
    
    fn close(self) {}
}

/// [`BiChannelIO::new`] helper, indicating the channel is closed and
/// no more reads/writes should come from it.
#[derive(Clone, Copy, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Stop;

/// An IO that reads from one channel and writes to another.
/// 
/// This binds the reader channel to the KBSR and KBDR.
/// When a character is ready from the reader channel,
/// the KBSR status is enabled and the character is accessible from the KBDR.
/// 
/// This binds the writer channel to the DSR and DDR.
/// When a character is ready to be written to the writer channel,
/// the DSR status is enabled and the character can be written to the DDR.
/// 
/// This IO type also exposes the MCR in the MCR MMIO address.
pub struct BiChannelIO {
    read_status:  Arc<AtomicBool>,
    read_data:    mpsc::Receiver<u8>,
    #[allow(unused)]
    read_handler: JoinHandle<()>,

    write_status:  Arc<AtomicBool>,
    write_data:    mpsc::Sender<u8>,
    write_handler: JoinHandle<()>,

    mcr: Arc<AtomicBool>
}
impl BiChannelIO {
    /// Creates a new bi-channel IO device with the given reader and writer.
    /// 
    /// This calls the reader function every time the IO input receives a byte.
    /// The reader function should block until a byte is ready, or return Stop
    /// if there are no more bytes to read.
    /// 
    /// This calls the writer function every time a byte needs to be written to the
    /// IO output.
    /// and calls the writer function everytime a byte needs to be written to the
    /// IO output.
    pub fn new(
        mut reader: impl FnMut() -> Result<u8, Stop> + Send + 'static, 
        mut writer: impl FnMut(u8) -> Result<(), Stop> + Send + 'static, 
        mcr: Arc<AtomicBool>
    ) -> Self {
        let (read_tx, read_rx) = mpsc::sync_channel(1);
        let (write_tx, write_rx) = mpsc::channel();

        let readst = Arc::new(AtomicBool::default());
        let read_status = Arc::clone(&readst);
        let writest = Arc::new(AtomicBool::default());
        let write_status = Arc::clone(&writest);

        // Reader thread:
        let read_handler = std::thread::spawn(move || loop {
            let Ok(byte) = reader() else { return };
            
            let result = read_tx.send(byte);
            readst.store(true, Ordering::Relaxed);

            let Ok(()) = result else { return };
        });

        // Writer thread:
        let write_handler = std::thread::spawn(move || {
            writest.store(true, Ordering::Relaxed);
            for byte in write_rx {
                writest.store(false, Ordering::Relaxed); // no receiving while processing results
                let Ok(()) = writer(byte) else { return };
                writest.store(true, Ordering::Relaxed); // ready to receive
            }
        });
        
        Self {
            read_status, 
            read_data: read_rx, 
            read_handler, 
            write_status, 
            write_data: write_tx, 
            write_handler, 
            mcr
        }
    }

    /// Creates a bi-channel IO device with stdin being the read data and stdout being the write data.
    /// 
    /// Note that due to how stdin works in terminals, data is only sent once a new line is typed.
    /// Additionally, this flushes stdout every time a byte is written.
    pub fn stdio(mcr: Arc<AtomicBool>) -> Self {
        use std::io::{self, BufRead, Write};

        Self::new(
            || {
                let mut stdin = io::stdin().lock();
                let &[byte, ..] = stdin.fill_buf().unwrap() else {
                    // terminal stdin would poll, so this is unreachable with terminal stdin
                    return Err(Stop);
                };

                Ok(byte)
            }, 
            |byte| {
                io::stdout().write_all(&[byte]).unwrap();
                io::stdout().flush().unwrap();
                Ok(())
            }, 
            mcr
        )
    }
}

impl IODevice for BiChannelIO {
    fn io_read(&self, addr: u16) -> Option<u16> {
        match addr {
            KBSR => Some(io_bool(self.read_status.load(Ordering::Relaxed))),
            KBDR => match self.read_data.try_recv() {
                Ok(b) => {
                    self.read_status.store(false, Ordering::Release);
                    Some(u16::from(b))
                },
                Err(TryRecvError::Empty) => None,

                // this can occur if the read handler panicked.
                // however, this just means we can't get the data, so just return None
                Err(TryRecvError::Disconnected) => None,
            },
            DSR => Some(io_bool(self.write_status.load(Ordering::Acquire))),
            MCR => Some(io_bool(self.mcr.load(Ordering::Relaxed))),
            _ => None
        }
    }

    fn io_write(&self, addr: u16, data: u16) -> bool {
        match addr {
            DDR => self.write_data.send(data as u8).is_ok(),
            MCR => {
                // store whether last bit is 1 (e.g., if data is negative)
                self.mcr.store((data as i16) < 0, Ordering::Relaxed);
                true
            }
            _ => false
        }
    }
    
    fn close(self) {
        let Self {
            read_status: _,
            read_data,
            read_handler: _,
            write_status: _,
            write_data,
            write_handler,
            mcr: _
        } = self;

        // Drop the channels.
        std::mem::drop(read_data);
        std::mem::drop(write_data);

        // Wait for the write handler to join.
        // This shouldn't block for long, because we just
        // disconnected the channel.

        // We're not going to wait for the read handler
        // because it can hang on reading, which prevents it from seeing
        // the channel is disconnected.

        // Also, don't error.
        // Skill issue.
        let _ = write_handler.join();
    }
}
/// Converts boolean data to a register word
fn io_bool(b: bool) -> u16 {
    match b {
        true  => 0x8000,
        false => 0x0000,
    }
}

// `Box<dyn IODevice>` does not work.
// It doesn't implement IODevice because it doesn't implement close
// (because you can't close on an unsized dyn IODevice).
// 
// However, changing the signature makes BiChannelIO annoying.
// So, this hack basically puts the device in an Option
// and closes it by taking it out and closing it without consuming the entire object,
// making close only require &mut Self instead of Self.
trait IODeviceMutClosable {
    fn io_read(&self, addr: u16) -> Option<u16>;
    fn io_write(&self, addr: u16, data: u16) -> bool;

    /// Closes but doesn't consume the object.
    /// 
    /// The object should not be used after this point.
    fn take_close(&mut self);
}
impl<D: IODevice> IODeviceMutClosable for Option<D> {
    fn io_read(&self, addr: u16) -> Option<u16> {
        self.as_ref().unwrap().io_read(addr)
    }
    fn io_write(&self, addr: u16, data: u16) -> bool {
        self.as_ref().unwrap().io_write(addr, data)
    }
    fn take_close(&mut self) {
        self.take().unwrap().close()
    }
}

/// An opaque box that holds custom defined IO.
/// 
/// This can be used to use a different implementation of IO
/// than the ones implemented in this module.
pub struct CustomIO(Box<dyn IODeviceMutClosable>);
impl CustomIO {
    /// Creates a new custom IO.
    pub fn new(device: impl IODevice + 'static) -> Self {
        CustomIO(Box::new(Some(device)))
    }
}
impl IODevice for CustomIO {
    fn io_read(&self, addr: u16) -> Option<u16> {
        self.0.io_read(addr)
    }

    fn io_write(&self, addr: u16, data: u16) -> bool {
        self.0.io_write(addr, data)
    }

    fn close(mut self) {
        self.0.take_close();
        std::mem::drop(self)
    }
}

/// All the variants of IO accepted by the Simulator.
pub enum SimIO {
    /// No IO. This corresponds to the implementation of [`NoIO`].
    None,
    /// A bi-channel IO implementation. See [`BiChannelIO`].
    BiChannel(BiChannelIO),
    /// A custom IO implementation. See [`CustomIO`].
    Custom(CustomIO)
}
impl std::fmt::Debug for SimIO {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SimIO")
            .finish_non_exhaustive()
    }
}
impl From<NoIO> for SimIO {
    fn from(_value: NoIO) -> Self {
        SimIO::None
    }
}
impl From<BiChannelIO> for SimIO {
    fn from(value: BiChannelIO) -> Self {
        SimIO::BiChannel(value)
    }
}
impl From<CustomIO> for SimIO {
    fn from(value: CustomIO) -> Self {
        SimIO::Custom(value)
    }
}
impl IODevice for SimIO {
    fn io_read(&self, addr: u16) -> Option<u16> {
        match self {
            SimIO::None => NoIO.io_read(addr),
            SimIO::BiChannel(io) => io.io_read(addr),
            SimIO::Custom(io) => io.io_read(addr)
        }
    }

    fn io_write(&self, addr: u16, data: u16) -> bool {
        match self {
            SimIO::None => NoIO.io_write(addr, data),
            SimIO::BiChannel(io) => io.io_write(addr, data),
            SimIO::Custom(io) => io.io_write(addr, data)
        }
    }

    fn close(self) {
        match self {
            SimIO::None => NoIO.close(),
            SimIO::BiChannel(io) => io.close(),
            SimIO::Custom(io) => io.close()
        }
    }
}