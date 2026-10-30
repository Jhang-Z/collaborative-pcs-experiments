//! The Fiat–Shamir hash chain of Section 4.9: ρ_i = G_i(ρ_{i-1}, rt_i, m_i), with G_i a
//! domain-separated counter-mode oracle. Challenges are parsed from the output blocks: 256 bits
//! per element of L, and fixed-width bit strings for query indices.

use binius_hash::{HashSuite,Blake3HashSuite};
use digest::Digest;
type PrefixDigest = <Blake3HashSuite as HashSuite>::LeafHash;
use std::{rc::Rc,cell::RefCell};

use crate::{
	field::{L, from_words},
	merkle::{Hash, Hasher},
};

pub struct Transcript<'a, H: HashSuite> {
	hasher: &'a Hasher<H>,
	chain: Rc<RefCell<Vec<u8>>>,
	round: u64,
 global: Option<Rc<RefCell<Vec<u8>>>>,
}

impl<'a, H: HashSuite> Transcript<'a, H> {
	/// Starts the chain from the instance x = (pp, r, s_x), given as bytes.
	pub fn new(hasher: &'a Hasher<H>, instance: &[u8]) -> Self {
		Self { hasher, chain: Rc::new(RefCell::new(instance.to_vec())), round: 0, global: None }
	}

	/// Digest of every absorbed message, for binding a following protocol.
	pub fn state(&self) -> Hash { self.global.as_ref().map_or_else(||self.hasher.hash(&[b"b2pcs-state-v4",&self.chain.borrow()]),|p|self.hasher.hash(&[b"v04-prefix",&p.borrow()])) }
 pub fn absorb(&mut self, role:&[u8], msg:&[u8]) {
  let p=self.global.as_ref().expect("absorb requires global transcript");
  let mut v=p.borrow_mut();v.extend_from_slice(&(role.len() as u64).to_le_bytes());v.extend_from_slice(role);
  v.extend_from_slice(&(msg.len() as u64).to_le_bytes());v.extend_from_slice(msg);
 }

	/// Absorbs round i's oracle root and message and returns its challenge stream.
	pub fn round(&mut self, root: &Hash, msg: &[u8]) -> Challenges<'a, H> {
		self.round += 1;
  if let Some(shared)=&self.global {
   let mut p=shared.borrow_mut();
   p.extend_from_slice(&self.round.to_le_bytes());p.extend_from_slice(root);
   p.extend_from_slice(&(msg.len() as u64).to_le_bytes());p.extend_from_slice(msg);
   let payload=p.clone();drop(p);
   let cached=prefix_hash(&payload);
   let mut c=Challenges {hasher:self.hasher,standalone:None,counter:1,buf:[0;32],used:0,bitbuf:0,nbits:0,global:Some((shared.clone(),payload,cached))};
   c.buf=c.block(0);
   #[cfg(test)] {c.buf=testing::override_block(msg,c.buf);}
   c.record(&c.buf);return c;
  }
		let prior = std::mem::take(&mut *self.chain.borrow_mut());
		let mut ch = Challenges { hasher: self.hasher,
            standalone: Some((self.chain.clone(), self.round, prior, *root, msg.to_vec())),
            counter: 1, buf: [0; 32], used: 0, bitbuf: 0, nbits: 0, global: None };
        // Retain every raw output block, including block zero for an empty challenge.
        ch.buf = ch.block(0);
        ch.record(&ch.buf);
		ch
	}
}

impl<'a> Transcript<'a,Blake3HashSuite> {
 pub fn new_global(hasher: &'a Hasher<Blake3HashSuite>, instance: &[u8]) -> Self {
  let mut t=Self::new(hasher,instance);t.global=Some(Rc::new(RefCell::new(Vec::new())));t.absorb(b"layout",crate::params::LAYOUT_ID);t.absorb(b"instance",instance);t
 }
}

pub struct Challenges<'a, H: HashSuite> {
	hasher: &'a Hasher<H>,
	standalone: Option<(Rc<RefCell<Vec<u8>>>,u64,Vec<u8>,Hash,Vec<u8>)>,
	counter: u64,
	buf: Hash,
	used: usize,
	bitbuf: u128,
	nbits: u32,
 global: Option<(Rc<RefCell<Vec<u8>>>,Vec<u8>,PrefixDigest)>,
}

impl<H: HashSuite> Challenges<'_, H> {
	fn block(&self, c: u64) -> Hash {
		if let Some((_,_,prefix))=&self.global {let mut h=prefix.clone();Digest::update(&mut h,8u64.to_le_bytes());Digest::update(&mut h,c.to_le_bytes());return h.finalize().as_slice().try_into().expect("32-byte digest");}
  let (_,round,prior,root,msg)=self.standalone.as_ref().expect("standalone challenge");
  self.hasher.hash(&[b"b2pcs-FS-v4",crate::params::LAYOUT_ID,&round.to_le_bytes(),prior,root,msg,&c.to_le_bytes()])
	}

	fn record(&self,b:&Hash) {crate::transport::broadcast(b);if let Some((s,_,_))=&self.global {s.borrow_mut().extend_from_slice(b);}if let Some((s,_,_,_,_))=&self.standalone {s.borrow_mut().extend_from_slice(b);}}
 fn next_bytes(&mut self, out: &mut [u8]) {
		for b in out {
			if self.used == 32 {
				self.buf = self.block(self.counter);
    self.record(&self.buf);
				self.counter += 1;
				self.used = 0;
			}
			*b = self.buf[self.used];
			self.used += 1;
		}
	}

	/// A uniformly random element of L (d = 256 bits).
	pub fn field(&mut self) -> L {
		let mut b = [0u8; 32];
		self.next_bytes(&mut b);
		from_words([
			u128::from_le_bytes(b[..16].try_into().unwrap()),
			u128::from_le_bytes(b[16..].try_into().unwrap()),
		])
	}

	/// A uniformly random integer of `bits` bits (bits ≤ 64).
	pub fn bits(&mut self, bits: u32) -> u64 {
		while self.nbits < bits {
			let mut b = [0u8; 8];
			self.next_bytes(&mut b);
			self.bitbuf |= (u64::from_le_bytes(b) as u128) << self.nbits;
			self.nbits += 64;
		}
		let v = (self.bitbuf & ((1u128 << bits) - 1)) as u64;
		self.bitbuf >>= bits;
		self.nbits -= bits;
		v
	}
}

#[cfg(test)]
mod global_tests {
 use super::*;
 use binius_hash::Blake3HashSuite;
 #[test]
 fn later_challenge_blocks_and_messages_bind_next_stage() {
  let h=Hasher::<Blake3HashSuite>::default();
  let mut a=Transcript::new_global(&h,b"test");
  let mut b=Transcript::new_global(&h,b"test");
  a.round(&[0;32],b"first").field();
  let mut c=b.round(&[0;32],b"first");c.field();c.field();
  assert_ne!(a.state(),b.state());
  let x=a.round(&[0;32],b"next").field();
  let y=b.round(&[0;32],b"next").field();
  assert_ne!(x,y);
 }
}

#[cfg(test)]
mod literal_tests {
 use super::*;use binius_hash::Blake3HashSuite;
 #[test]fn global_blocks_match_literal_full_prefix_hash(){
  let h=Hasher::<Blake3HashSuite>::default();let mut t=Transcript::new_global(&h,b"literal");t.absorb(b"large message",&vec![17;100_000]);
  let mut c=t.round(&[3;32],b"stage");let p=c.global.as_ref().unwrap().1.clone();
  for ctr in 0u64..4 {let expected=h.hash(&[b"v04-FS-block",&p,&ctr.to_le_bytes()]);let got=c.field();assert_eq!(bytemuck::cast::<L,[u8;32]>(got),expected);}
 }
}

// Exact prefix of Hasher::hash([domain, full_public_prefix, counter]); cloning the BLAKE3 context
// changes no hash input bytes and avoids hashing multi-megabyte G openings per block.
fn prefix_hash(payload:&[u8])->PrefixDigest {
 let mut h=PrefixDigest::new();let tag=b"v04-FS-block";
 Digest::update(&mut h,(tag.len() as u64).to_le_bytes());Digest::update(&mut h,tag);
 Digest::update(&mut h,(payload.len() as u64).to_le_bytes());Digest::update(&mut h,payload);h
}

// Force the first raw RO block at an identified message, including verifier replays.
// This hook does not exist in production builds and is isolated per test thread.
#[cfg(test)]
pub(crate) mod testing {
 use super::*;
 struct Forced {message:Vec<u8>,block:Hash,used:bool}
 thread_local! {static FORCED:RefCell<Option<Forced>>=const {RefCell::new(None)};}
 struct Reset;
 impl Drop for Reset {fn drop(&mut self){FORCED.with(|f|{f.borrow_mut().take();});}}
 pub fn with_field<R>(message:&[u8],value:L,f:impl FnOnce()->R)->R {
  FORCED.with(|slot| {assert!(slot.borrow().is_none());*slot.borrow_mut()=Some(Forced{message:message.to_vec(),block:bytemuck::cast(value),used:false});});
  let _reset=Reset;let result=f();
  FORCED.with(|slot|assert!(slot.borrow().as_ref().unwrap().used,"forced challenge was not reached"));result
 }
 pub(super) fn override_block(message:&[u8],block:Hash)->Hash {
  FORCED.with(|slot| {let mut slot=slot.borrow_mut();if let Some(f)=slot.as_mut(){if f.message==message {f.used=true;return f.block;}}block})
 }
}

#[cfg(test)]
mod standalone_v4_tests {
 use super::*;
 use binius_hash::{Blake3HashSuite,Sha256HashSuite};
 fn literal<H:HashSuite>() {
  let h=Hasher::<H>::default();let mut t=Transcript::new(&h,b"full instance");
  let mut prior=b"full instance".to_vec();
  for (round,count) in [(1u64,17usize),(2,1),(3,4)] {
   let root=[round as u8;32];let msg=vec![round as u8;43];
   let mut c=t.round(&root,&msg);let mut raw=Vec::new();
   for counter in 0..count {
    let expected=h.hash(&[b"b2pcs-FS-v4",crate::params::LAYOUT_ID,&round.to_le_bytes(),&prior,&root,&msg,&(counter as u64).to_le_bytes()]);
    assert_eq!(bytemuck::cast::<L,[u8;32]>(c.field()),expected);
    raw.extend(expected);
   }
   assert_eq!(*t.chain.borrow(),raw);prior=raw;
  }
  let mut a=Transcript::new(&h,b"same");let mut b=Transcript::new(&h,b"same");
  a.round(&[0;32],b"first").field();
  let mut c=b.round(&[0;32],b"first");c.field();c.field();
  assert_ne!(a.state(),b.state());
  assert_ne!(a.round(&[0;32],b"next").field(),b.round(&[0;32],b"next").field());
  let mut empty=Transcript::new(&h,b"instance");drop(empty.round(&[0;32],b""));
  assert_eq!(empty.chain.borrow().len(),32);
 }
 #[test] fn standalone_hashes_literal_full_vectors(){literal::<Blake3HashSuite>();literal::<Sha256HashSuite>();}
 #[test] fn query_bits_match_literal_bitstream_and_block_count(){
  let h=Hasher::<Blake3HashSuite>::default();let mut t=Transcript::new(&h,b"queries");
  let mut c=t.round(&[7;32],b"indices");let bytes:Vec<u8>=(0..150u64).flat_map(|i|c.block(i)).collect();
  let mut offset=0;
  for i in 0..871 {for width in [8u32,14-(i%2) as u32] {
   let expected=(0..width).map(|j|(((bytes[(offset+j as usize)/8]>>((offset+j as usize)%8))&1) as u64)<<j).sum::<u64>();
   assert_eq!(c.bits(width),expected);offset+=width as usize;
  }}
  assert_eq!(t.chain.borrow().len()/32,offset.div_ceil(256));
 }
}
