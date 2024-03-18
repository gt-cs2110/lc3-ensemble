use std::io::{stdin, stdout, BufRead, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::TryRecvError;
use std::sync::{mpsc, Arc};

const KBSR: u16 = 0xFE00;
const KBDR: u16 = 0xFE02;
const DSR: u16  = 0xFE04;
const DDR: u16  = 0xFE06;

pub(crate) struct SimIO {
    pub(crate) kb_status: Arc<AtomicBool>,
    pub(crate) kb_data: mpsc::Receiver<u8>,

    pub(crate) display_status: Arc<AtomicBool>,
    pub(crate) display_data: mpsc::SyncSender<u8>
}

impl SimIO {
    pub(crate) fn new() -> SimIO {
        let (kb_send, kb_recv) = mpsc::sync_channel(1);
        let (ds_send, ds_recv) = mpsc::sync_channel(1);
        
        let io = Self {
            kb_status: Arc::new(AtomicBool::new(false)),
            kb_data: kb_recv,

            display_status: Arc::new(AtomicBool::new(false)),
            display_data: ds_send
        };

        let kb_status = Arc::clone(&io.kb_status);
        let display_status = Arc::clone(&io.display_status);

        // STDIN loop
        std::thread::spawn(move || loop {
            let buf = stdin().lock().fill_buf().unwrap().to_vec();
            for byte in buf {
                kb_status.store(true, Ordering::Relaxed);
                let result = kb_send.send(byte);
                kb_status.store(false, Ordering::Release);

                match result {
                    Ok(_)  => stdin().lock().consume(1),
                    Err(_) => return,
                }
            }
        });

        // STDOUT loop
        std::thread::spawn(move || loop {
            display_status.store(true, Ordering::Relaxed);
            let result = ds_recv.recv();
            display_status.store(true, Ordering::Release);

            match result {
                Ok(b) => {
                    stdout().write_all(&[b]).unwrap();
                    stdout().flush().unwrap();
                },
                Err(_) => return,
            }
        });

        io
    }

    pub(crate) fn io_read(&self, addr: u16) -> Option<u16> {
        match addr {
            KBSR => match self.kb_status.load(Ordering::Relaxed) {
                true  => Some(0x8000),
                false => Some(0x0000),
            },
            KBDR => match self.kb_data.try_recv() {
                Ok(b) => Some(u16::from(b)),
                Err(TryRecvError::Empty) => None,
                Err(TryRecvError::Disconnected) => None, // unreachable: keyboard disconnected
            },
            DSR => match self.display_status.load(Ordering::Relaxed) {
                true  => Some(0x8000),
                false => Some(0x0000)
            }
            _ => None
        }
    }
    pub(crate) fn io_write(&self, addr: u16, data: u16) -> bool {
        match addr {
            DDR => match self.display_data.try_send(data as u8) {
                Ok(()) => true,
                Err(_) => false,
            },
            _ => false
        }
    }
}
impl std::fmt::Debug for SimIO {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SimIO").finish_non_exhaustive()
    }
}