/// Flat byte-addressed deterministic RAM for the RISC-V VM.

pub const DEFAULT_MEM_SIZE: usize = 1 << 24; // 16 MiB

/// Memory access record for the constraint system.
#[derive(Debug, Clone, Copy)]
pub struct MemoryAccess {
    pub addr: u32,
    pub clk: u32,
    pub is_write: bool,
    pub value: u32,
}

pub struct Memory {
    data: Vec<u8>,
    /// Ordered log of all memory accesses for the permutation argument.
    pub access_log: Vec<MemoryAccess>,
}

impl Memory {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0u8; size],
            access_log: Vec::new(),
        }
    }

    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Read a byte.
    pub fn read_byte(&mut self, addr: u32, clk: u32) -> u8 {
        let a = addr as usize;
        assert!(a < self.data.len(), "Memory read OOB: 0x{:08x}", addr);
        let val = self.data[a];
        self.access_log.push(MemoryAccess {
            addr,
            clk,
            is_write: false,
            value: val as u32,
        });
        val
    }

    /// Write a byte.
    pub fn write_byte(&mut self, addr: u32, val: u8, clk: u32) {
        let a = addr as usize;
        assert!(a < self.data.len(), "Memory write OOB: 0x{:08x}", addr);
        self.data[a] = val;
        self.access_log.push(MemoryAccess {
            addr,
            clk,
            is_write: true,
            value: val as u32,
        });
    }

    /// Read a 16-bit halfword (little-endian).
    pub fn read_half(&mut self, addr: u32, clk: u32) -> u16 {
        let lo = self.read_byte(addr, clk) as u16;
        let hi = self.read_byte(addr.wrapping_add(1), clk) as u16;
        lo | (hi << 8)
    }

    /// Write a 16-bit halfword (little-endian).
    pub fn write_half(&mut self, addr: u32, val: u16, clk: u32) {
        self.write_byte(addr, val as u8, clk);
        self.write_byte(addr.wrapping_add(1), (val >> 8) as u8, clk);
    }

    /// Read a 32-bit word (little-endian).
    pub fn read_word(&mut self, addr: u32, clk: u32) -> u32 {
        let lo = self.read_half(addr, clk) as u32;
        let hi = self.read_half(addr.wrapping_add(2), clk) as u32;
        lo | (hi << 16)
    }

    /// Write a 32-bit word (little-endian).
    pub fn write_word(&mut self, addr: u32, val: u32, clk: u32) {
        self.write_half(addr, val as u16, clk);
        self.write_half(addr.wrapping_add(2), (val >> 16) as u16, clk);
    }

    /// Bulk write without logging (for initial program loading).
    pub fn write_bytes_no_log(&mut self, addr: u32, data: &[u8]) {
        let start = addr as usize;
        let end = start + data.len();
        assert!(end <= self.data.len(), "Bulk write OOB");
        self.data[start..end].copy_from_slice(data);
    }

    /// Read without logging (for inspection/debugging).
    pub fn peek_word(&self, addr: u32) -> u32 {
        let a = addr as usize;
        u32::from_le_bytes([
            self.data[a],
            self.data[a + 1],
            self.data[a + 2],
            self.data[a + 3],
        ])
    }

    /// Read a byte without logging (for inspection).
    pub fn peek_byte(&self, addr: u32) -> u8 {
        self.data[addr as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_word_read_write() {
        let mut mem = Memory::new(1024);
        mem.write_word(0, 0xDEADBEEF, 0);
        let val = mem.read_word(0, 1);
        assert_eq!(val, 0xDEADBEEF);
    }

    #[test]
    fn test_byte_order() {
        let mut mem = Memory::new(1024);
        mem.write_word(0, 0x04030201, 0);
        assert_eq!(mem.peek_byte(0), 0x01);
        assert_eq!(mem.peek_byte(1), 0x02);
        assert_eq!(mem.peek_byte(2), 0x03);
        assert_eq!(mem.peek_byte(3), 0x04);
    }

    #[test]
    fn test_access_log() {
        let mut mem = Memory::new(1024);
        mem.write_word(0, 42, 0);
        let _ = mem.read_word(0, 1);
        // write_word does 4 byte writes, read_word does 4 byte reads
        assert_eq!(mem.access_log.len(), 8);
    }
}
