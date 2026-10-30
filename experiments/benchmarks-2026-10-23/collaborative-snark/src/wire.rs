//! Framing is counted as online application bytes; no private state is transferred online.
use crate::field::L;
use anyhow::{Result, ensure};
use std::{
    io::{Read, Write},
};

pub struct Reader<'a>(pub &'a [u8]);
impl<'a> Reader<'a> {
    pub fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        ensure!(self.0.len() >= n, "truncated message");
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Ok(a)
    }
    pub fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into()?))
    }
    pub fn field(&mut self) -> Result<L> {
        Ok(bytemuck::pod_read_unaligned(self.take(32)?))
    }
    pub fn fields(&mut self) -> Result<Vec<L>> {
        let n = usize::try_from(self.u64()?)?;
        ensure!(n <= self.0.len() / 32, "field vector length");
        self.take(n * 32).map(|b| {
            b.chunks_exact(32)
                .map(bytemuck::pod_read_unaligned)
                .collect()
        })
    }
    pub fn hash(&mut self) -> Result<[u8; 32]> {
        Ok(self.take(32)?.try_into()?)
    }
    pub fn finish(self) -> Result<()> {
        ensure!(self.0.is_empty(), "trailing message bytes");
        Ok(())
    }
}
pub fn field(b: &mut Vec<u8>, x: L) {
    b.extend_from_slice(bytemuck::bytes_of(&x));
}
pub fn fields(b: &mut Vec<u8>, xs: &[L]) {
    b.extend((xs.len() as u64).to_le_bytes());
    b.extend_from_slice(bytemuck::cast_slice(xs));
}
pub fn send(s: &mut impl Write, b: &[u8]) -> Result<u64> {
    s.write_all(&(b.len() as u64).to_le_bytes())?;
    s.write_all(b)?;
    Ok(8 + b.len() as u64)
}
pub fn receive(s: &mut impl Read) -> Result<Vec<u8>> {
    let mut h = [0; 8];
    s.read_exact(&mut h)?;
    let n = usize::try_from(u64::from_le_bytes(h))?;
    ensure!(n <= 1 << 30, "wire frame exceeds 1 GiB");
    let mut b = vec![0; n];
    s.read_exact(&mut b)?;
    Ok(b)
}
pub fn command(tag: u8, xs: &[L]) -> Vec<u8> {
    let mut b = vec![tag];
    b.extend_from_slice(bytemuck::cast_slice(xs));
    b
}
pub fn scalars(b: &[u8], n: usize) -> Result<Vec<L>> {
    ensure!(b.len() == n * 32, "response field count");
    Ok(b.chunks_exact(32)
        .map(bytemuck::pod_read_unaligned)
        .collect())
}

pub const START: u8 = 1;
pub const SC1_INIT: u8 = 2;
pub const SC1_COL_ROUND: u8 = 3;
pub const SC1_COL_FOLD: u8 = 4;
pub const CONVERSION_MASK: u8 = 5;
pub const CONVERSION_OPEN: u8 = 6;
pub const SC1_SLOT_ROUND: u8 = 7;
pub const SC1_SLOT_FOLD: u8 = 8;
pub const SC1_ENDPOINT: u8 = 9;
pub const SC2_INIT: u8 = 10;
pub const SC2_ROUND: u8 = 11;
pub const SC2_FOLD: u8 = 12;
pub const SC2_ENDPOINT: u8 = 13;
pub const PCS_INIT: u8 = 14;
pub const PCS_FRONTEND: u8 = 15;
pub const PCS_MASK: u8 = 16;
pub const PCS_WEIGHTS: u8 = 17;
pub const PCS_ROUND: u8 = 18;
pub const PCS_FOLD: u8 = 19;
pub const PCS_TAIL: u8 = 20;
pub const PCS_QUERIES: u8 = 21;
pub const STOP: u8 = 22;
