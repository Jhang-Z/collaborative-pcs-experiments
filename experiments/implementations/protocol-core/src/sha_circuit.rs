//! Fixed 32-byte SHA-256 relation. Bits within words are little-endian;
//! message/digest bytes use SHA-256's big-endian word convention.
//! All gate outputs are retained to keep the R1CS sparse.
use crate::spartan::Base;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bit {
	Const(bool),
	Wire(usize),
}
type Word = [Bit; 32];
#[derive(Clone, Copy)]
struct Gate {
	a: Bit,
	b: Bit,
	and: bool,
}

pub struct ShaCircuit {
    pub keccak: bool,
	pub base: Base,
	pub private_len: usize,
	pub constraint_len: usize,
 pub sha_private_len:usize,
 pub mask_start:Option<(usize,usize)>,
	pub and_gates: usize,
	pub xor_gates: usize,
	gates: Vec<Gate>,
	outputs: [Bit; 256],
}

#[derive(Default)]
struct Builder {
	gates: Vec<Gate>,
}
impl Builder {
	fn gate(&mut self, a: Bit, b: Bit, and: bool) -> Bit {
		match (a, b, and) {
			(Bit::Const(x), Bit::Const(y), _) => return Bit::Const(if and { x & y } else { x ^ y }),
			(Bit::Const(false), _, true) | (_, Bit::Const(false), true) => return Bit::Const(false),
			(Bit::Const(true), b, true) | (Bit::Const(false), b, false) => return b,
			(a, Bit::Const(true), true) | (a, Bit::Const(false), false) => return a,
			_ if a == b => return if and { a } else { Bit::Const(false) },
			_ => {}
		}
		let out = Bit::Wire(256 + self.gates.len());
		self.gates.push(Gate { a, b, and });
		out
	}
	fn xor(&mut self, a: Word, b: Word) -> Word {
		std::array::from_fn(|i| self.gate(a[i], b[i], false))
	}
	fn and(&mut self, a: Word, b: Word) -> Word {
		std::array::from_fn(|i| self.gate(a[i], b[i], true))
	}
	fn xor3(&mut self, a: Word, b: Word, c: Word) -> Word {
		let t = self.xor(a, b);
		self.xor(t, c)
	}
	fn add(&mut self, a: Word, b: Word) -> Word {
		let mut carry = Bit::Const(false);
		std::array::from_fn(|i| {
			let p = self.gate(a[i], b[i], false);
			let s = self.gate(p, carry, false);
			if i < 31 {
				let t = self.gate(a[i], b[i], true);
				let u = self.gate(p, carry, true);
				carry = self.gate(t, u, false);
			}
			s
		})
	}
	fn sum(&mut self, words: &[Word]) -> Word {
		words.iter().copied().reduce(|a, b| self.add(a, b)).unwrap()
	}
}
fn constant(x: u32) -> Word {
	std::array::from_fn(|i| Bit::Const((x >> i) & 1 != 0))
}
fn rotr(a: Word, n: usize) -> Word {
	std::array::from_fn(|i| a[(i + n) % 32])
}
fn shr(a: Word, n: usize) -> Word {
	std::array::from_fn(|i| if i + n < 32 { a[i + n] } else { Bit::Const(false) })
}
const IV: [u32; 8] = [
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];
const K: [u32; 64] = [
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be,
	0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa,
	0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85,
	0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
	0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

impl ShaCircuit {
	pub fn new() -> Self {
		let mut b = Builder::default();
		let mut w = [constant(0); 64];
		for t in 0..8 {
			w[t] = std::array::from_fn(|i| Bit::Wire(t * 32 + i));
		}
		w[8] = constant(0x80000000);
		w[15] = constant(256);
		for t in 16..64 {
			let s0 = b.xor3(rotr(w[t - 15], 7), rotr(w[t - 15], 18), shr(w[t - 15], 3));
			let s1 = b.xor3(rotr(w[t - 2], 17), rotr(w[t - 2], 19), shr(w[t - 2], 10));
			w[t] = b.sum(&[w[t - 16], s0, w[t - 7], s1]);
		}
		let mut v = IV.map(constant);
		for t in 0..64 {
			let s1 = b.xor3(rotr(v[4], 6), rotr(v[4], 11), rotr(v[4], 25));
			let fg = b.xor(v[5], v[6]);
			let ef = b.and(v[4], fg);
			let ch = b.xor(v[6], ef);
			let t1 = b.sum(&[v[7], s1, ch, constant(K[t]), w[t]]);
			let s0 = b.xor3(rotr(v[0], 2), rotr(v[0], 13), rotr(v[0], 22));
			let ab = b.xor(v[0], v[1]);
			let ac = b.xor(v[0], v[2]);
			let bc = b.and(ab, ac);
			let maj = b.xor(v[0], bc);
			let t2 = b.add(s0, maj);
			v = [b.add(t1, t2), v[0], v[1], v[2], b.add(v[3], t1), v[4], v[5], v[6]];
		}
		for i in 0..8 {
			v[i] = b.add(v[i], constant(IV[i]));
		}
		let outputs = std::array::from_fn(|i| v[i / 32][i % 32]);
		let private_len = 256 + b.gates.len();
		let public_one = private_len;
		let sig = |s: Bit| -> Vec<usize> {
			match s {
				Bit::Const(false) => vec![],
				Bit::Const(true) => vec![public_one],
				Bit::Wire(i) => vec![i],
			}
		};
		let (mut aa, mut bb, mut cc) = (Vec::new(), Vec::new(), Vec::new());
		let mut and_gates = 0;
		for (i, g) in b.gates.iter().enumerate() {
			if g.and {
				aa.push(sig(g.a));
				bb.push(sig(g.b));
				cc.push(vec![256 + i]);
				and_gates += 1;
			} else {
				let mut row = sig(g.a);
				row.extend(sig(g.b));
				row.push(256 + i);
				aa.push(row);
				bb.push(vec![public_one]);
				cc.push(vec![]);
			}
		}
		for (i, &out) in outputs.iter().enumerate() {
			let mut row = sig(out);
			row.push(public_one + 1 + i);
			aa.push(row);
			bb.push(vec![public_one]);
			cc.push(vec![]);
		}
		let constraint_len = aa.len();
		let m = constraint_len.next_power_of_two();
		let n = (private_len + 257).next_power_of_two();
		aa.resize(m, vec![]);
		bb.resize(m, vec![]);
		cc.resize(m, vec![]);
		let xor_gates = b.gates.len() - and_gates;
		Self {
            keccak: false,
			base: Base {
				log_m0: m.trailing_zeros() as usize,
				log_n0: n.trailing_zeros() as usize,
				a: aa,
				b: bb,
				c: cc,
			},
			private_len,
			constraint_len,
   sha_private_len:private_len,mask_start:None,
			and_gates,
			xor_gates,
			gates: b.gates,
			outputs,
		}
	}
 /// Separate fixed Keccak-f[1600]/256 relation; preserves the SHA constructors.
 pub fn new_keccak_zk()->Self {
  let c=crate::keccak_circuit::KeccakCircuit::new(256);
  let private_len=c.private_len();let constraint_len=c.constraint_len;
  Self::with_zk_masks(Self{keccak:true,base:c.base,private_len,constraint_len,
   sha_private_len:private_len,mask_start:None,and_gates:38400,xor_gates:0,
   gates:vec![],outputs:std::array::from_fn(|i|Bit::Wire(24*1600+i))})
 }
 pub fn new_zk()->Self {
  Self::with_zk_masks(Self::new())
 }
 fn with_zk_masks(mut c:Self)->Self {let start=(c.private_len+1023)&!1023;let row=(c.constraint_len+1023)&!1023;let new_private=start+4096;
  for m in [&mut c.base.a,&mut c.base.b,&mut c.base.c] {for r in m.iter_mut(){for x in r {if *x>=c.private_len {*x+=new_private-c.private_len;}}}}
  c.private_len=new_private;c.constraint_len=row+3072;c.mask_start=Some((start,row));
  let m=c.constraint_len.next_power_of_two();let n=(new_private+257).next_power_of_two();c.base.log_m0=m.trailing_zeros() as usize;c.base.log_n0=n.trailing_zeros() as usize;
  c.base.a.resize(m,vec![]);c.base.b.resize(m,vec![]);c.base.c.resize(m,vec![]);
  for b in 0..3 {for j in 0..1024 {let p=start+b*1024+j;let r=row+b*1024+j;
   c.base.a[r]=vec![if b==1 {new_private}else{p}];
   c.base.b[r]=vec![if b==0 {new_private}else{p}];c.base.c[r]=vec![p];
  }}c
 }
 /// Small irregular AND/XOR correctness fixture, not a SHA or performance workload.
 pub fn synthetic_zk(count:usize)->Self {
  assert!(count>=8);let private_len=256+count;let one=private_len;
  let mut gates=Vec::new();let(mut a,mut b,mut c)=(vec![],vec![],vec![]);
  for i in 0..count {let l=(i*17+3)%(256+i);let r=(i*31+11)%(256+i);let and=i%3!=0;
   gates.push(Gate{a:Bit::Wire(l),b:Bit::Wire(r),and});
   if and {a.push(vec![l]);b.push(vec![r]);c.push(vec![256+i]);}
   else {a.push(vec![l,r,256+i]);b.push(vec![one]);c.push(vec![]);}
  }
  let outputs=std::array::from_fn(|i|Bit::Wire(256+i%count));
  for i in 0..256 {a.push(vec![256+i%count,one+1+i]);b.push(vec![one]);c.push(vec![]);}
  let constraint_len=a.len();let m=constraint_len.next_power_of_two();let n=(private_len+257).next_power_of_two();a.resize(m,vec![]);b.resize(m,vec![]);c.resize(m,vec![]);
  Self::with_zk_masks(Self{keccak:false,base:Base{log_m0:m.trailing_zeros() as usize,log_n0:n.trailing_zeros() as usize,a,b,c},private_len,constraint_len,sha_private_len:private_len,mask_start:None,and_gates:(0..count).filter(|i|i%3!=0).count(),xor_gates:(0..count).filter(|i|i%3==0).count(),gates,outputs})
 }
 pub fn randomize_masks(&self,z:&mut [bool],rows:&mut [Vec<bool>;3],rng:&mut impl rand::Rng) {
  use rand::RngExt;
  let (start,row)=self.mask_start.expect("zk circuit");
  for v in &mut z[start..start+4096] {*v=rng.random();}
  for b in 0..3 {for j in 0..1024 {let v=z[start+b*1024+j];let r=row+b*1024+j;
   rows[0][r]=if b==1 {true}else{v};rows[1][r]=if b==0 {true}else{v};rows[2][r]=v;
  }}
 }
	/// Padded private vector, row values (including public contribution), public digest.
	pub fn witness(&self, msg: &[u8]) -> (Vec<bool>, [Vec<bool>; 3], [u8; 32]) {
		let mut z = vec![false; self.base.n0()];
        if self.keccak {
            let input: &[u8;200]=msg.try_into().expect("Keccak200-byte state");
            z[..40000].copy_from_slice(&crate::keccak_circuit::trace(input));
        } else {
            assert_eq!(msg.len(),32);
		for t in 0..8 {
			let word = u32::from_be_bytes(msg[4 * t..4 * t + 4].try_into().unwrap());
			for i in 0..32 {
				z[t * 32 + i] = (word >> i) & 1 != 0;
			}
		}
        }
		let val = |s: Bit, z: &[bool]| match s {
			Bit::Const(v) => v,
			Bit::Wire(i) => z[i],
		};
		for (i, g) in self.gates.iter().enumerate() {
			let (a, b) = (val(g.a, &z), val(g.b, &z));
			z[256 + i] = if g.and { a & b } else { a ^ b };
		}
		let mut digest = [0u8; 32];
        if self.keccak {
            for i in 0..256 {digest[i/8]|=(val(self.outputs[i],&z) as u8)<<(i%8);}
        } else {
		for t in 0..8 {
			let mut word = 0u32;
			for i in 0..32 {
				word |= (val(self.outputs[t * 32 + i], &z) as u32) << i;
			}
			digest[t * 4..t * 4 + 4].copy_from_slice(&word.to_be_bytes());
		}
        }
		let public = self.public(&digest);
		for (i, &v) in public.iter().enumerate() {
			z[self.private_len + i] = v;
		}
		let rows = std::array::from_fn(|t| {
			let mat = [&self.base.a, &self.base.b, &self.base.c][t];
			mat.iter().map(|row| row.iter().fold(false, |v, &i| v ^ z[i])).collect()
		});
		z[self.private_len..].fill(false);
		(z, rows, digest)
	}
	pub fn public(&self, digest: &[u8; 32]) -> Vec<bool> {
		let mut v = vec![true];
        if self.keccak {v.extend((0..256).map(|i|digest[i/8]>>(i%8)&1!=0));return v;}
		for chunk in digest.chunks_exact(4) {
			let w = u32::from_be_bytes(chunk.try_into().unwrap());
			v.extend((0..32).map(|i| (w >> i) & 1 != 0));
		}
		v
	}
	pub fn nnz(&self) -> usize {
		[&self.base.a, &self.base.b, &self.base.c]
			.iter()
			.flat_map(|m| m.iter())
			.map(Vec::len)
			.sum()
	}
}
impl Default for ShaCircuit {
	fn default() -> Self {
		Self::new()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha2::{Digest, Sha256};
	#[test]
	fn sha_circuit_matches_reference_and_relation() {
		let c = ShaCircuit::new();
		for msg in [[0u8; 32], [255u8; 32], std::array::from_fn(|i| i as u8)] {
			let (z, r, d) = c.witness(&msg);
			assert_eq!(d.as_slice(), Sha256::digest(msg).as_slice());
			assert!(r[0].iter().zip(&r[1]).zip(&r[2]).all(|((&a, &b), &v)| a & b == v));
			assert!(z[c.private_len..].iter().all(|&v| !v));
			// Mutating a public digest must violate an output constraint.
			let mut all = z;
			let mut bad = d;
			bad[0] ^= 1;
			for (i, &v) in c.public(&bad).iter().enumerate() {
				all[c.private_len + i] = v;
			}
			assert!(c.base.a.iter().zip(&c.base.b).zip(&c.base.c).any(|((a, b), d)| {
				let lin = |row: &Vec<usize>| row.iter().fold(false, |v, &i| v ^ all[i]);
				lin(a) & lin(b) != lin(d)
			}));
		}
		eprintln!(
			"SHA circuit private={} constraints={} AND={} XOR={} nnz={}",
			c.private_len,
			c.constraint_len,
			c.and_gates,
			c.xor_gates,
			c.nnz()
		);
	}
}

#[cfg(test)] mod keccak_adapter_tests {
 use super::*;
 #[test] fn masked_keccak_rows_and_private_extension() {
  let c=ShaCircuit::new_keccak_zk();let input=std::array::from_fn::<_,200,_>(|i|i as u8);
  let(mut z,mut rows,d)=c.witness(&input);
  assert_eq!(d,crate::keccak_circuit::reference(&input)[..32]);
  let mut rng=<rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(20261029);c.randomize_masks(&mut z,&mut rows,&mut rng);
  assert!(rows[0].iter().zip(&rows[1]).zip(&rows[2]).all(|((&a,&b),&c)|a&b==c));
  let p=c.public(&d);for(i,&v)in p.iter().enumerate(){z[c.private_len+i]=v;}
  for(j,((a,b),v))in c.base.a.iter().zip(&c.base.b).zip(&c.base.c).enumerate(){
   let eval=|r:&Vec<usize>|r.iter().fold(false,|s,&i|s^z[i]);assert_eq!(eval(a)&eval(b),eval(v),"row{j}");
  }
  assert_eq!((c.private_len,c.constraint_len,c.base.n0(),c.base.m0()),(45056,41984,65536,65536));
 }
}
