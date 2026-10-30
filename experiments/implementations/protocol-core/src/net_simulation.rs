//! Sequential computation trace of the external PCS TCP schedule, with fresh offline state.
use std::{io::Read, time::Instant};
use binius_hash::HashSuite;
use rand::{SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};
use crate::{field::{D, Field, L, LOG_D}, fs::Transcript, merkle::{Hasher, Tree},
    net::{ExternalArtifact, NetReport, external_instance, to_l}, pcs_codec,
    protocol::{Challenges, Opening, Party, Proof, TAG_TAIL, dummy_root, bound_instance, l_bytes, sample_queries},
    setup::Setup};

pub struct Exchange {
    pub command: u8,
    pub coordinator_ns: u64,
    pub party_ns: Vec<u64>,
    pub request_bytes: Vec<usize>,
    pub response_bytes: Vec<usize>,
}

#[cfg(test)]
mod standalone_v4_tests {
 use super::*;
 #[test] fn sequential_external_schedule_produces_complete_verifiable_v4_proof(){
  let setup=Setup::new(crate::params::Params{n_parties:4,ell:11,beta:2,gamma:14,tau:3,salt_bytes:32});
  let (artifact,trace)=simulate_external::<binius_hash::Blake3HashSuite>(&setup,73,&[0x93;64]);
  let proof=pcs_codec::decode_proof(&setup,&artifact.proof).unwrap();assert!(crate::protocol::verify::<binius_hash::Blake3HashSuite>(&setup,&artifact.instance,&proof).is_ok());
  assert_eq!(trace.exchanges.len(),setup.params.folds()+5);
  let committed = trace.exchanges.iter().filter(|e| e.command==105).last().unwrap();
  assert!(committed.response_bytes.iter().all(|&n| n==32+8), "terminal upload must contain only the commitment hash");
  let disclosed = trace.exchanges.iter().find(|e| e.command==106).unwrap();
  let tail_bytes=((1usize<<setup.params.tau)+1)*32;
  assert!(disclosed.response_bytes.iter().all(|&n| n>=tail_bytes+8), "every party discloses coefficients and salt after queries");
 }
}
pub struct Trace {
    pub exchanges: Vec<Exchange>,
    pub coordinator_final_ns: u64,
}
struct Recorder { trace: Trace, checkpoint: Instant }
impl Recorder {
    fn exchange(&mut self, tag: u8, parties: &mut [Party], request: &[u8],
                mut compute: impl FnMut(&mut Party, &[u8]) -> Vec<u8>) -> Vec<Vec<u8>> {
        let coordinator_ns = self.checkpoint.elapsed().as_nanos() as u64;
        let mut party_ns = Vec::with_capacity(parties.len());
        let replies: Vec<_> = parties.iter_mut().map(|q| {
            let start = Instant::now();
            let reply = compute(q, request);
            party_ns.push(start.elapsed().as_nanos() as u64);
            reply
        }).collect();
        self.trace.exchanges.push(Exchange { command: tag, coordinator_ns, party_ns,
            request_bytes: vec![request.len()+8; parties.len()],
            response_bytes: replies.iter().map(|r| r.len()+8).collect() });
        self.checkpoint = Instant::now();
        replies
    }
}
fn fresh_rng() -> StdRng {
    let mut entropy = [0;32];
    std::fs::File::open("/dev/urandom").unwrap().read_exact(&mut entropy).unwrap();
    StdRng::from_seed(entropy)
}

/// Same online messages and kernels as net::run_party_external/run_aggregator_external.
/// All states coexist on this sequential measurement host; no process privacy is claimed.
pub fn simulate_external<H: HashSuite>(setup: &Setup, seed: u64, input: &[u8]) -> (ExternalArtifact, Trace) {
    let prep = Instant::now();
    let p = &setup.params;
    let (n, k, np) = (p.n(), p.k(), p.n_parties);
    let (inst, wit) = external_instance(setup, seed, input, &mut fresh_rng());
    let mut parties: Vec<_> = (0..np).map(|i| {
        let mut q = Party::new(i,n,0); q.rng = fresh_rng(); q.prepare_salts(setup); q
    }).collect();
    let mut dealer = fresh_rng();
    for &x in &setup.layout.pad {
        for (q, value) in parties.iter_mut().zip(setup.sharing.random_shares(&mut dealer)) { q.row[x] = value; }
    }
    let sharing = Instant::now();
    let mut client = fresh_rng();
    for x in (0..n).filter(|&x| !setup.layout.is_pad[x]) {
        let values: Vec<_> = (0..k).map(|y| wit.table[y*n+x]).collect();
        for (q, value) in parties.iter_mut().zip(setup.sharing.share(&values, &mut client)) { q.row[x] = value; }
    }
    let client_share = sharing.elapsed();
    drop(wit); drop(client); drop(dealer);
    let preparation = prep.elapsed();
    let hasher = Hasher::<H>::default();
    let online = Instant::now();
    let mut rec = Recorder { trace: Trace { exchanges: vec![], coordinator_final_ns: 0 }, checkpoint: Instant::now() };
    let dummy2 = dummy_root(&hasher,2);
    let dummy3 = dummy_root(&hasher,3);
    let dummy4 = dummy_root(&hasher,4);
    let mut tr = Transcript::new(&hasher, &bound_instance(setup,&inst,&[]));
    // GO -> initial encoding/commitment and xi; setup, shares and salts are offline.
    let r1 = rec.exchange(101, &mut parties, b"go", |q, request| {
        assert_eq!(request,b"go");
        let start=Instant::now(); let cw=setup.row.encode(&q.row); q.time.encode+=start.elapsed();
        q.commit_layer(setup,&hasher,0,cw);
        let xi=q.frontend(setup,&inst,None)[0];
        let mut msg=q.subtrees[0].root().to_vec(); msg.extend(l_bytes(&[xi])); msg
    });
    let mut roots=vec![Tree::build(&hasher.at_layer(0),r1.iter().map(|m|m[..32].try_into().unwrap()).collect())];
    let xi: L=r1.iter().map(|m|to_l(&m[32..])[0]).sum();
    let alpha=tr.round(&roots[0].root(),l_bytes(&[xi])).field();
    let r2=rec.exchange(102,&mut parties,l_bytes(&[alpha]),|q,request|l_bytes(&q.frontend(setup,&inst,Some(to_l(request)[0]))).to_vec());
    let mut t=vec![L::ZERO;D];
    for msg in r2 { for (a,b) in t.iter_mut().zip(to_l(&msg)) { *a+=b; } }
    let mut c2=tr.round(&dummy2,l_bytes(&t));
    let mut ch2: Vec<L>=(0..LOG_D).map(|_|c2.field()).collect();
    ch2.extend((0..setup.n_omega()).map(|_|c2.field()));
    let mut masks=vec![vec![];np];
    let r3=rec.exchange(103,&mut parties,l_bytes(&ch2),|q,request| {
        let ch=to_l(request); masks[q.id]=setup.mask_weight(&ch[LOG_D..]);
        l_bytes(&[q.h_omega(setup,&masks[q.id])]).to_vec()
    });
    let h_omega: L=r3.iter().map(|m|to_l(m)[0]).sum();
    let eps=tr.round(&dummy3,l_bytes(&[h_omega])).field();
    // EPS -> weights and first round coefficients, exactly as in the TCP party.
    let mut messages=rec.exchange(104,&mut parties,l_bytes(&[eps]),|q,request| {
        let ch=Challenges { alpha,r_pp:ch2[..LOG_D].to_vec(),omega:ch2[LOG_D..].to_vec(),eps:to_l(request)[0],r:vec![] };
        q.weights(setup,&inst,&ch,&masks[q.id]);
        let(a,b)=q.round_poly(); let mut m=vec![0;32];m.extend(l_bytes(&[a,b]));m
    });
    let mut coeffs=vec![];
    for j in 0..p.folds() {
        if j>0 { roots.push(Tree::build(&hasher.at_layer(j as u64),messages.iter().map(|m|m[..32].try_into().unwrap()).collect())); }
        let(mut g0,mut g2)=(L::ZERO,L::ZERO);
        for m in &messages { let v=to_l(&m[32..]);g0+=v[0];g2+=v[1]; }
        coeffs.push((g0,g2));
        let root=if j==0 {dummy4}else{roots[j].root()};
        let rj=tr.round(&root,l_bytes(&[g0,g2])).field();
        messages=rec.exchange(105,&mut parties,l_bytes(&[rj]),|q,request| {
            q.fold(setup,&hasher,j,to_l(request)[0]);
            if j+1<p.folds() {
                let(a,b)=q.round_poly();let mut m=q.subtrees[j+1].root().to_vec();m.extend(l_bytes(&[a,b]));m
            } else { hasher.at_layer(TAG_TAIL).leaf(TAG_TAIL,q.id as u64,l_bytes(&q.row),&q.tail_salt).to_vec() }
        });
    }
    let tl=1usize<<p.tau;
    let leaves=messages.iter().map(|m|m.as_slice().try_into().unwrap()).collect();
    let tail_root=Tree::build(&hasher.at_layer(TAG_TAIL),leaves).root();
    let queries=sample_queries(setup,&mut tr,&tail_root);
    let qb:Vec<u8>=queries.iter().flat_map(|&(i,q)|[(i as u64).to_le_bytes(),(q as u64).to_le_bytes()].concat()).collect();
    let answers=rec.exchange(106,&mut parties,&qb,|q,request| {
        let mut ans=l_bytes(&q.row).to_vec();ans.extend(q.tail_salt);
        for b in request.chunks_exact(16) {
            let id=u64::from_le_bytes(b[..8].try_into().unwrap()) as usize;
            let pos=u64::from_le_bytes(b[8..].try_into().unwrap()) as usize;
            if id!=q.id {continue;}
            for j in 0..p.folds() {
                let x=pos>>j;ans.extend(l_bytes(&q.codewords[j][2*x..2*x+2]));ans.extend(q.salts[j][x]);
                for h in q.subtrees[j].path(x) {ans.extend(h);}
            }
        }
        ans
    });
    let tails:Vec<_>=answers.iter().map(|m|to_l(&m[..32*tl])).collect();
    let tail_salts:Vec<[u8;32]>=answers.iter().map(|m|m[32*tl..32*tl+32].try_into().unwrap()).collect();
    let mut cursors=vec![32*(tl+1);np];
    let openings=queries.iter().map(|&(i,_)|(0..p.folds()).map(|j| {
        let m=&answers[i];let o=&mut cursors[i];let v=to_l(&m[*o..*o+64]);*o+=64;
        let salt=m[*o..*o+32].try_into().unwrap();*o+=32;
        let depth=p.m()-j-1;
        let mut path:Vec<_>=(0..depth).map(|d|m[*o+32*d..*o+32*(d+1)].try_into().unwrap()).collect();
        *o+=32*depth;path.extend(roots[j].path(i));Opening{values:[v[0],v[1]],salt,path}
    }).collect()).collect();
    assert!(cursors.iter().zip(&answers).all(|(&at,m)|at==m.len()));
    let proof=Proof{roots:roots.iter().map(Tree::root).collect(),tail_root,xi,t,h_omega,coeffs,tails,tail_salts,openings};
    let serializing=Instant::now();let bytes=pcs_codec::encode_proof(&proof);let serialization=serializing.elapsed();
    rec.trace.coordinator_final_ns=rec.checkpoint.elapsed().as_nanos() as u64;
    let mut report=NetReport {online:online.elapsed(),serialization,preparation,client_share,proof_bytes:bytes.len(),..Default::default()};
    report.online_party_payload=(0..np).map(|i| {
        let up=rec.trace.exchanges.iter().map(|e|(e.response_bytes[i]-8) as u64).sum();
        let down=rec.trace.exchanges.iter().map(|e|(e.request_bytes[i]-8) as u64).sum();(up,down)
    }).collect();
    report.online_bytes=report.online_party_payload.iter().map(|(a,b)|a+b).sum();
    (ExternalArtifact{report,instance:inst,proof:bytes,input_prefix_hash:Sha256::digest(input).into(),commitment:proof.roots[0]},rec.trace)
}
