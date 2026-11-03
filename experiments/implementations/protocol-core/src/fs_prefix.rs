//! Exact cached BLAKE3 evaluation of the existing length-framed public prefix.
//!
//! The payload length changes chunk zero. Every later complete chunk is immutable
//! in an append-only transcript and can retain its non-root chaining value.

use blake3::{Hasher, hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root}};

const CHUNK: usize = 1024;
const TAG: &[u8] = b"v04-FS-block";
const HEADER: usize = 8 + TAG.len() + 8;

#[derive(Clone)]
pub(super) struct Subtree { start: usize, chunks: usize, cv: [u8;32] }

#[derive(Default)]
pub(super) struct PrefixCache { forest: Vec<Subtree>, complete: usize }

pub(super) enum Snapshot {
    Short(Box<Hasher>),
    Tree { first: [u8;32], forest: Vec<Subtree>, tail: Vec<u8>, offset: usize },
}

fn subtree(start: usize, bytes: &[u8]) -> [u8;32] {
    #[cfg(test)] super::PREFIX_HASHED_BYTES.with(|n|n.set(n.get()+bytes.len()));
    let mut h=Hasher::new();
    h.set_input_offset((start*CHUNK) as u64).update(bytes);
    h.finalize_non_root()
}

fn push(stack: &mut Vec<Subtree>, mut right: Subtree) {
    while let Some(left)=stack.last() {
        if left.chunks!=right.chunks || left.start%(2*left.chunks)!=0 {break;}
        debug_assert_eq!(left.start+left.chunks,right.start);
        let left=stack.pop().unwrap();
        right=Subtree {start:left.start,chunks:2*left.chunks,
            cv:merge_subtrees_non_root(&left.cv,&right.cv,Mode::Hash)};
    }
    stack.push(right);
}

impl PrefixCache {
    pub(super) fn snapshot(&mut self, payload: &[u8]) -> Snapshot {
        let mut header=[0u8;HEADER];
        header[..8].copy_from_slice(&(TAG.len() as u64).to_le_bytes());
        header[8..8+TAG.len()].copy_from_slice(TAG);
        header[8+TAG.len()..].copy_from_slice(&(payload.len() as u64).to_le_bytes());
        let length=HEADER+payload.len();
        if length<CHUNK {
            #[cfg(test)] super::PREFIX_HASHED_BYTES.with(|n|n.set(n.get()+length));
            let mut h=Hasher::new();h.update(&header).update(payload);
            return Snapshot::Short(Box::new(h));
        }
        let mut first=[0u8;CHUNK];
        first[..HEADER].copy_from_slice(&header);
        first[HEADER..].copy_from_slice(&payload[..CHUNK-HEADER]);
        let end=length/CHUNK;
        let mut start=self.complete.max(1);
        debug_assert!(start<=end,"public transcript must be append-only");
        while start<end {
            let remaining=end-start;
            let largest=1usize<<((usize::BITS-1)-remaining.leading_zeros());
            let chunks=largest.min(1usize<<start.trailing_zeros());
            let bytes=&payload[start*CHUNK-HEADER..(start+chunks)*CHUNK-HEADER];
            push(&mut self.forest,Subtree {start,chunks,cv:subtree(start,bytes)});
            start+=chunks;
        }
        self.complete=end;
        Snapshot::Tree {first:subtree(0,&first),forest:self.forest.clone(),
            tail:payload[end*CHUNK-HEADER..].to_vec(),offset:end}
    }
}

impl Snapshot {
    pub(super) fn block(&self, counter: u64) -> [u8;32] {
        let mut suffix=[0u8;16];
        suffix[..8].copy_from_slice(&8u64.to_le_bytes());
        suffix[8..].copy_from_slice(&counter.to_le_bytes());
        match self {
            Self::Short(prefix)=>{
                let mut h=(**prefix).clone();h.update(&suffix);*h.finalize().as_bytes()
            }
            Self::Tree {first,forest,tail,offset}=>{
                let mut stack=Vec::with_capacity(forest.len()+2);
                stack.push(Subtree {start:0,chunks:1,cv:*first});
                for node in forest {push(&mut stack,node.clone());}
                let mut ending=[0u8;CHUNK+16];
                ending[..tail.len()].copy_from_slice(tail);
                ending[tail.len()..tail.len()+16].copy_from_slice(&suffix);
                let length=tail.len()+16;
                let (last,last_offset)=if length>CHUNK {
                    push(&mut stack,Subtree {start:*offset,chunks:1,cv:subtree(*offset,&ending[..CHUNK])});
                    (&ending[CHUNK..length],offset+1)
                } else {(&ending[..length],*offset)};
                // Keep the final chunk separate so the final parent receives ROOT,
                // including when the complete input has a power-of-two chunk count.
                let mut cv=subtree(last_offset,last);
                while stack.len()>1 {
                    cv=merge_subtrees_non_root(&stack.pop().unwrap().cv,&cv,Mode::Hash);
                }
                *merge_subtrees_root(&stack[0].cv,&cv,Mode::Hash).as_bytes()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn literal(payload: &[u8], counter: u64) -> [u8;32] {
        let mut h=Hasher::new();
        for part in [TAG,payload,&counter.to_le_bytes()] {
            h.update(&(part.len() as u64).to_le_bytes()).update(part);
        }
        *h.finalize().as_bytes()
    }
    #[test]
    fn exact_at_chunk_and_root_boundaries() {
        let mut lengths=vec![0,1,63,64,65,995,996,997];
        for chunks in [1,2,3,4,5,7,8,9,15,16,17,31,32,33,127,128,129,1024] {
            for delta in -2i64..=2 {
                lengths.push((chunks*1024-44+delta) as usize);
                lengths.push((chunks*1024-28+delta) as usize);
            }
        }
        lengths.sort_unstable();lengths.dedup();
        let mut payload=Vec::new();let mut cache=PrefixCache::default();
        for len in lengths {
            payload.extend((payload.len()..len).map(|i|(i.wrapping_mul(37)^(i>>5)) as u8));
            let snapshot=cache.snapshot(&payload);
            for counter in [0,1,3,255,256,u64::MAX] {
                assert_eq!(snapshot.block(counter),literal(&payload,counter),"len={len},counter={counter}");
            }
        }
    }
    #[test]
    fn frozen_snapshot_survives_later_appends() {
        let mut payload=vec![29;100_000];let mut cache=PrefixCache::default();
        let old=cache.snapshot(&payload);
        let expected=(0..4).map(|c|literal(&payload,c)).collect::<Vec<_>>();
        for n in [1,19,1024,300_000] {
            payload.extend(vec![n as u8;n]);
            let new=cache.snapshot(&payload);
            assert_eq!(new.block(0),literal(&payload,0));
            for (c,wanted) in expected.iter().enumerate() {assert_eq!(old.block(c as u64),*wanted);}
        }
    }
    #[test]
    fn all_prefix_regions_remain_bound() {
        let original=(0..20_000).map(|i|i as u8).collect::<Vec<_>>();
        let expected=PrefixCache::default().snapshot(&original).block(0);
        for position in [0,995,996,997,1024,8192,19_999] {
            let mut changed=original.clone();changed[position]^=1;
            let actual=PrefixCache::default().snapshot(&changed).block(0);
            assert_eq!(actual,literal(&changed,0));assert_ne!(actual,expected);
        }
    }
}
