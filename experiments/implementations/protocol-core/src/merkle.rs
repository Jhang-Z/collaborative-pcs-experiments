//! Merkle trees in the format of Section 4.9: leaves are salted, position-tagged fibres; party
//! subtrees sit at depth log2(N) of one global tree per round. Leaves are hashed with the suite's
//! digest and internal nodes with its two-to-one compression, so leaf and node inputs are
//! separated.

use std::collections::BTreeSet;

use binius_hash::{CompressionFunction, HashSuite};
use digest::{Digest, Output};

pub type Hash = [u8; 32];

pub struct Hasher<H: HashSuite> {
	compression: H::Compression,
 role:u64,
 standalone_layer:Option<u64>,
}

impl<H: HashSuite> Default for Hasher<H> {
	fn default() -> Self {
		Self { compression: H::Compression::default(),role:0,standalone_layer:None }
	}
}

impl<H: HashSuite> Hasher<H> {
	pub fn scoped(role:u64)->Self {Self{compression:H::Compression::default(),role,standalone_layer:None}}
 pub fn at_layer(&self,layer:u64)->Self {
  if self.role==0 {Self{compression:H::Compression::default(),role:0,standalone_layer:Some(layer)}}
  else {Self::scoped(self.role|(layer<<8))}
 }
 pub(crate) fn standalone(&self)->bool {self.role==0}
 /// Leaf hash of (tag, position, payload, salt).
	pub fn leaf(&self, tag: u64, pos: u64, payload: &[u8], salt: &[u8]) -> Hash {
        if let Some(layer)=self.standalone_layer {return self.hash(&[b"b2pcs-MT-v4",&layer.to_le_bytes(),b"leaf",&tag.to_le_bytes(),&pos.to_le_bytes(),payload,salt]);}
        if self.role!=0 && payload.len()==64 && salt.len()==32 {
        let mut input=[0u8;128];input[..8].copy_from_slice(b"v04-leaf");
        input[8..16].copy_from_slice(&self.role.to_le_bytes());input[16..24].copy_from_slice(&tag.to_le_bytes());
        input[24..32].copy_from_slice(&pos.to_le_bytes());input[32..96].copy_from_slice(payload);input[96..].copy_from_slice(salt);
        return H::LeafHash::digest(input).as_slice().try_into().expect("32-byte digest");
            }

		let mut h = H::LeafHash::new();
  if self.role!=0 {Digest::update(&mut h,b"v04-leaf");Digest::update(&mut h,self.role.to_le_bytes());}
		Digest::update(&mut h, tag.to_le_bytes());
		Digest::update(&mut h, pos.to_le_bytes());
		Digest::update(&mut h, payload);
		Digest::update(&mut h, salt);
		let out = h.finalize();
		out.as_slice().try_into().expect("32-byte digest")
	}

	pub fn node(&self, l: &Hash, r: &Hash) -> Hash {
        if let Some(layer)=self.standalone_layer {return self.hash(&[b"b2pcs-MT-v4",&layer.to_le_bytes(),b"node",l,r]);}
        if self.role!=0 {
        let role=self.role.to_le_bytes();let parts:[&[u8];4]=[b"v04-node",&role,l,r];
        let mut input=[0u8;112];let mut offset=0;
        for part in parts {input[offset..offset+8].copy_from_slice(&(part.len() as u64).to_le_bytes());offset+=8;
            input[offset..offset+part.len()].copy_from_slice(part);offset+=part.len();}
        return H::LeafHash::digest(input).as_slice().try_into().expect("32-byte digest");
            }
		let (mut a, mut b) = (Output::<H::LeafHash>::default(), Output::<H::LeafHash>::default());
		a.copy_from_slice(l);
		b.copy_from_slice(r);
		let out = self.compression.compress([a, b]);
		out.as_slice().try_into().expect("32-byte digest")
	}

    #[cfg(test)]
	pub(crate) fn leaf_reference(&self, tag: u64, pos: u64, payload: &[u8], salt: &[u8]) -> Hash {
        if let Some(layer)=self.standalone_layer {return self.hash(&[b"b2pcs-MT-v4",&layer.to_le_bytes(),b"leaf",&tag.to_le_bytes(),&pos.to_le_bytes(),payload,salt]);}
		let mut h = H::LeafHash::new();
  if self.role!=0 {Digest::update(&mut h,b"v04-leaf");Digest::update(&mut h,self.role.to_le_bytes());}
		Digest::update(&mut h, tag.to_le_bytes());
		Digest::update(&mut h, pos.to_le_bytes());
		Digest::update(&mut h, payload);
		Digest::update(&mut h, salt);
		let out = h.finalize();
		out.as_slice().try_into().expect("32-byte digest")
	}
    #[cfg(test)]
	pub(crate) fn node_reference(&self, l: &Hash, r: &Hash) -> Hash {
        if let Some(layer)=self.standalone_layer {return self.hash(&[b"b2pcs-MT-v4",&layer.to_le_bytes(),b"node",l,r]);}
  if self.role!=0 {return self.hash(&[b"v04-node",&self.role.to_le_bytes(),l,r]);}
		let (mut a, mut b) = (Output::<H::LeafHash>::default(), Output::<H::LeafHash>::default());
		a.copy_from_slice(l);
		b.copy_from_slice(r);
		let out = self.compression.compress([a, b]);
		out.as_slice().try_into().expect("32-byte digest")
	}

	/// Arbitrary-length hash, used for the Fiat–Shamir chain.
	pub fn hash(&self, parts: &[&[u8]]) -> Hash {
		let mut h = H::LeafHash::new();
		for p in parts {
			Digest::update(&mut h, (p.len() as u64).to_le_bytes());
			Digest::update(&mut h, p);
		}
		h.finalize().as_slice().try_into().expect("32-byte digest")
	}
}

/// A complete binary tree over 2^depth leaves, stored level by level (level 0 = leaves).
pub struct Tree {
	levels: Vec<Vec<Hash>>,
}

impl Tree {
	pub fn build<H: HashSuite>(hasher: &Hasher<H>, leaves: Vec<Hash>) -> Self {
		assert!(leaves.len().is_power_of_two());
		let mut levels = vec![leaves];
		while levels.last().unwrap().len() > 1 {
			let prev = levels.last().unwrap();
            let role=hasher.role;let standalone_layer=hasher.standalone_layer;
            let next=if prev.len()>=32768 {
                crate::parallel::map(prev.len()/2, |i| Hasher::<H>{compression:H::Compression::default(),role,standalone_layer}.node(&prev[2*i],&prev[2*i+1]))
            } else {prev.chunks_exact(2).map(|p|hasher.node(&p[0],&p[1])).collect()};
			levels.push(next);
		}
		Self { levels }
	}

	pub fn root(&self) -> Hash {
		self.levels.last().unwrap()[0]
	}

	pub fn depth(&self) -> usize {
		self.levels.len() - 1
	}

	/// Sibling path of leaf `idx`, bottom up.
	pub fn path(&self, mut idx: usize) -> Vec<Hash> {
		let mut out = Vec::with_capacity(self.depth());
		for level in &self.levels[..self.depth()] {
			out.push(level[idx ^ 1]);
			idx >>= 1;
		}
		out
	}
}

/// Recomputes the root from a leaf and its sibling path.
pub fn root_from_path<H: HashSuite>(hasher: &Hasher<H>, leaf: Hash, mut idx: usize, path: &[Hash]) -> Hash {
	let mut acc = leaf;
	for sib in path {
		acc = if idx & 1 == 0 { hasher.node(&acc, sib) } else { hasher.node(sib, &acc) };
		idx >>= 1;
	}
	acc
}

/// Number of sibling hashes a batched opening of `leaves` needs in a tree of the given depth,
/// when siblings that the verifier can recompute (or that repeat) are not transmitted.
pub fn multiproof_size(leaves: impl IntoIterator<Item = usize>, depth: usize) -> usize {
	let mut known: BTreeSet<usize> = leaves.into_iter().collect();
	let mut count = 0;
	for _ in 0..depth {
		let mut parents = BTreeSet::new();
		for &i in &known {
			if !known.contains(&(i ^ 1)) {
				count += 1;
			}
			parents.insert(i >> 1);
		}
		known = parents;
	}
	count
}

#[cfg(test)]
mod tests {
	use binius_hash::Blake3HashSuite;

	use super::*;

	#[test]
	fn paths_verify_and_multiproof_counts() {
		let h = Hasher::<Blake3HashSuite>::default();
		let leaves: Vec<Hash> = (0..16u64).map(|i| h.leaf(1, i, &[i as u8], &[0; 4])).collect();
		let t = Tree::build(&h, leaves.clone());
		for i in 0..16 {
			assert_eq!(root_from_path(&h, leaves[i], i, &t.path(i)), t.root());
		}
		assert_eq!(multiproof_size([0], 4), 4);
		assert_eq!(multiproof_size([0, 1], 4), 3);
		assert_eq!(multiproof_size(0..16, 4), 0);
	}

}

#[cfg(test)]
mod fixed_buffer_tests {
    use super::*;
    use binius_hash::{Blake3HashSuite,Sha256HashSuite};
    fn check<H:HashSuite>() {
        for role in [0,1,2,u64::MAX] {for layer in [0,1,37] {
            let h=Hasher::<H>::scoped(role).at_layer(layer);
            for tag in [0,1,1u64<<32] {for pos in [0,17,u64::MAX] {
                for n in [0,1,32,64,128,4096] {for sn in [0,16,32] {
                    let p=(0..n).map(|i|(i*73+19) as u8).collect::<Vec<_>>();
                    let s=(0..sn).map(|i|(i*41+23) as u8).collect::<Vec<_>>();
                    let old=h.leaf_reference(tag,pos,&p,&s);let fast=h.leaf(tag,pos,&p,&s);assert_eq!(fast,old);
                    let right=h.leaf_reference(tag,pos.wrapping_add(1),&s,&p);assert_eq!(h.node(&old,&right),h.node_reference(&old,&right));
                }}
            }}
            let leaves=(0..64).map(|i|h.leaf_reference(0,i,&[i as u8;64],&[27;32])).collect::<Vec<_>>();
            let actual=Tree::build(&h,leaves.clone());let mut levels=vec![leaves];
            while levels.last().unwrap().len()>1 {let prev=levels.last().unwrap();levels.push(prev.chunks_exact(2).map(|p|h.node_reference(&p[0],&p[1])).collect());}
            assert_eq!(actual.levels,levels);
        }}
    }
    #[test]fn fixed_buffers_preserve_all_hash_bytes(){check::<Blake3HashSuite>();check::<Sha256HashSuite>();}
}

#[cfg(test)]
mod standalone_v4_tests {
 use super::*;
 use binius_hash::{Blake3HashSuite,Sha256HashSuite};
 fn separated<H:HashSuite>() {
  let h=Hasher::<H>::default();let layers=[0,1,2,1u64<<32,(1u64<<63)|2,(1u64<<63)|3,(1u64<<63)|4];
  let mut roots=BTreeSet::new();let mut nodes=BTreeSet::new();
  for layer in layers {
   let domain=h.at_layer(layer);
   let leaves=(0..8u64).map(|i|domain.leaf(0,i,&[19;64],&[71;32])).collect::<Vec<_>>();
   let tree=Tree::build(&domain,leaves.clone());assert!(roots.insert(tree.root()));
   assert!(nodes.insert(domain.node(&[3;32],&[4;32])));
   for i in 0..8 {assert_eq!(root_from_path(&domain,leaves[i],i,&tree.path(i)),tree.root());
    assert_ne!(root_from_path(&h.at_layer(layer^16),leaves[i],i,&tree.path(i)),tree.root());}
   assert_eq!(domain.leaf(0,0,&[19;64],&[71;32]),h.hash(&[b"b2pcs-MT-v4",&layer.to_le_bytes(),b"leaf",&0u64.to_le_bytes(),&0u64.to_le_bytes(),&[19;64],&[71;32]]));
  }
 }
 #[test] fn standalone_tree_domains_and_paths_are_separated(){separated::<Blake3HashSuite>();separated::<Sha256HashSuite>();}
 #[test] fn parallel_tree_keeps_standalone_layer(){
  let h=Hasher::<Blake3HashSuite>::default().at_layer(5);
  let leaves=(0..32768u64).map(|i|h.leaf(5,i,&[9;64],&[27;32])).collect::<Vec<_>>();
  let tree=Tree::build(&h,leaves.clone());
  assert_eq!(root_from_path(&h,leaves[17001],17001,&tree.path(17001)),tree.root());
 }
}
