//! IO handling for LC-3.
//! 
//! The main struct of this module is the [`SimIO`] struct,
//! which handles the keyboard and display.

use std::io::{stdin, stdout, BufRead, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::TryRecvError;
use std::sync::{mpsc, Arc};
use std::thread::JoinHandle;

const KBSR: u16 = 0xFE00;
const KBDR: u16 = 0xFE02;
const DSR: u16  = 0xFE04;
const DDR: u16  = 0xFE06;

/// Simulator input/output.
/// 
/// This contains a **keyboard**, which is accessible through the KBSR and KBDR. 
/// (Note that due to the limitations of terminals, the key is displayed and
/// characters only appear once a new line appears in the input.)
/// 
/// This also contains a **display**, which is accessible through the DSR and DDR.
pub struct SimIO {
    /// Whether the keyboard has received a new character.
    kb_status: Arc<AtomicBool>,
    /// A channel to access the keyboard's characters.
    kb_data: mpsc::Receiver<u8>,
    /// The thread where the keyboard's process occurs.
    #[allow(unused)]
    kb_handler: JoinHandle<()>,
    
    /// Whether the display is ready to receive a new character.
    display_status: Arc<AtomicBool>,
    /// A channel to send characters to the display.
    display_data: mpsc::Sender<u8>,
    /// The thread where the display's process occurs.
    display_handler: JoinHandle<()>,
}

impl SimIO {
    /// Creates the IO processes.
    pub fn new() -> SimIO {
        let (kb_send, kb_recv) = mpsc::sync_channel(1);
        let (ds_send, ds_recv) = mpsc::channel();
        
        let kbs = Arc::new(AtomicBool::new(false));
        let kb_status = Arc::clone(&kbs);
        let dss = Arc::new(AtomicBool::new(false));
        let display_status = Arc::clone(&dss);

        let kb_status = Arc::clone(&kb_status);
        let display_status = Arc::clone(&display_status);

        // STDIN loop
        let kb_handler = std::thread::spawn(move || loop {
            let buf = stdin().lock().fill_buf().unwrap().to_vec();
            for byte in buf {
                let result = kb_send.send(byte);
                kbs.store(true, Ordering::Relaxed);

                match result {
                    Ok(_)  => stdin().lock().consume(1),
                    Err(_) => return,
                }
            }
        });

        // STDOUT loop
        let display_handler = std::thread::spawn(move || loop {
            dss.store(true, Ordering::Relaxed);
            let result = ds_recv.recv();
            
            dss.store(false, Ordering::Release);
            match result {
                Ok(b) => {
                    stdout().write_all(&[b]).unwrap();
                    stdout().flush().unwrap();
                },
                Err(_) => return,
            }
        });

        Self {
            kb_status,
            kb_data: kb_recv,
            kb_handler,

            display_status,
            display_data: ds_send,
            display_handler,
        }
    }

    /// Reads the data at the given memory-mapped address (which is controlled by SimIO).
    /// 
    /// If successful, this returns the value returned from that address.
    /// If unsuccessful, this returns `None`.
    pub fn io_read(&self, addr: u16) -> Option<u16> {
        match addr {
            KBSR => match self.kb_status.load(Ordering::Relaxed) {
                true  => Some(0x8000),
                false => Some(0x0000),
            },
            KBDR => match self.kb_data.try_recv() {
                Ok(b) => {
                    self.kb_status.store(false, Ordering::Release);
                    Some(u16::from(b))
                },
                Err(TryRecvError::Empty) => None,
                Err(TryRecvError::Disconnected) => None, // unreachable: keyboard disconnected
            },
            DSR => match self.display_status.load(Ordering::Acquire) {
                true  => Some(0x8000),
                false => Some(0x0000)
            }
            _ => None
        }
    }

    /// Writes the data to the given memory-mapped address (which is controlled by SimIO).
    /// 
    /// This returns whether the write was successful or not.
    pub fn io_write(&self, addr: u16, data: u16) -> bool {
        match addr {
            DDR => self.display_data.send(data as u8).is_ok(),
            _ => false
        }
    }

    /// Closes the keyboard and display channels and waits for the display to complete.
    pub fn join(self) -> std::thread::Result<()> {
        let Self { kb_status: _, kb_data, kb_handler: _, display_status: _, display_data, display_handler } = self;

        std::mem::drop(kb_data);
        std::mem::drop(display_data);

        display_handler.join()
    }
}

impl std::fmt::Debug for SimIO {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SimIO").finish_non_exhaustive()
    }
}
impl Default for SimIO {
    fn default() -> Self {
        Self::new()
    }
}