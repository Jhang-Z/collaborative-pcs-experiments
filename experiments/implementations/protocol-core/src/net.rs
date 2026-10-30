//! Networked execution in a star topology: one aggregator process (F_Agg, F_rand, Fiat–Shamir,
//! relaying the initial shares), N server processes, and one input client that shares the packed
//! table and leaves, connected over TCP. Every message is
//! length-prefixed; both ends count bytes. The aggregator measures wall-clock time per phase.

use std::{
	io::{BufReader, BufWriter, Read, Write},
	net::{TcpListener, TcpStream},
	time::{Duration, Instant},
};

use binius_hash::HashSuite;
use rand::{SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};

use crate::{
	field::{D, Field, L, LOG_D, Random, from_words},
	fs::Transcript,
	merkle::{Hash, Hasher, Tree},
	protocol::{Challenges, Opening, Party, Proof, TAG_TAIL, dummy_root, bound_instance, l_bytes, proof_size, sample_queries, verify},
	setup::{Instance, Setup, fill_owner, instance_point, partial_claim},
};

pub struct Conn {
	r: BufReader<TcpStream>,
	w: BufWriter<TcpStream>,
	pub sent: u64,
	pub recv: u64,
	pub payload: u64,
	pub sent_payload: u64,
	pub recv_payload: u64,
}

impl Conn {
	pub fn new(s: TcpStream) -> Self {
		s.set_nodelay(true).unwrap();
		Self { r: BufReader::with_capacity(1 << 20, s.try_clone().unwrap()), w: BufWriter::with_capacity(1 << 20, s), sent: 0, recv: 0, payload: 0, sent_payload:0, recv_payload:0 }
	}

	pub fn send(&mut self, bytes: &[u8]) {
		self.w.write_all(&(bytes.len() as u64).to_le_bytes()).unwrap();
		self.w.write_all(bytes).unwrap();
		self.w.flush().unwrap();
		self.sent += 8 + bytes.len() as u64;
		self.payload += bytes.len() as u64;
		self.sent_payload += bytes.len() as u64;
	}

	pub fn recv(&mut self) -> Vec<u8> {
		let mut len = [0u8; 8];
		self.r.read_exact(&mut len).unwrap();
		let mut buf = vec![0u8; u64::from_le_bytes(len) as usize];
		self.r.read_exact(&mut buf).unwrap();
		self.recv += 8 + buf.len() as u64;
		self.payload += buf.len() as u64;
		self.recv_payload += buf.len() as u64;
		buf
	}

	pub fn send_l(&mut self, v: &[L]) {
		self.send(l_bytes(v));
	}

	pub fn recv_l(&mut self) -> Vec<L> {
		to_l(&self.recv())
	}
}

pub fn to_l(b: &[u8]) -> Vec<L> {
	b.chunks_exact(32)
		.map(|c| {
			from_words([u128::from_le_bytes(c[..16].try_into().unwrap()), u128::from_le_bytes(c[16..].try_into().unwrap())])
		})
		.collect()
}

fn hash_from(b: &[u8]) -> Hash {
	b[..32].try_into().unwrap()
}

/// Identifies the client's connection to the aggregator.
const CLIENT_ID: u64 = u64::MAX;

fn fresh_rng() -> StdRng {
	let mut entropy=[0;32];std::fs::File::open("/dev/urandom").expect("OS randomness").read_exact(&mut entropy).unwrap();
	StdRng::from_seed(entropy)
}
fn configuration(setup:&Setup,point_seed:u64,bits:usize)->Vec<u8> {
	let p=&setup.params;let mut v=b"PCSNET01".to_vec();
	for x in [p.n_parties,p.ell,p.beta,p.gamma,p.tau,p.salt_bytes,bits] {v.extend((x as u64).to_le_bytes());}
	v.extend(point_seed.to_le_bytes());v
}

/// External bytes map LSB-first to the field basis, in owner/column/logical-row order.
/// Only tensor masks are fresh random values; unused data capacity is zero.
pub fn external_instance(setup:&Setup,point_seed:u64,input:&[u8],rng:&mut impl rand::Rng)->(Instance,crate::setup::Witness) {
	assert!(input.len()%32==0 && input.len()*8<=crate::params::input_bits(&setup.layout));
	let(n,k)=(setup.params.n(),setup.params.k());let mut table=vec![L::ZERO;n*k];let mut at=0;
	for owner in 0..setup.params.n_parties {for &x in &setup.layout.owned[owner] {for y in 0..k {
		table[y*n+x]=if setup.layout.mask_index(owner,y,x).is_some(){L::random(&mut *rng)}
		else if at<input.len(){let b=&input[at..at+32];at+=32;from_words([u128::from_le_bytes(b[..16].try_into().unwrap()),u128::from_le_bytes(b[16..].try_into().unwrap())])}else{L::ZERO};
	}}}
	assert_eq!(at,input.len());let point=instance_point(setup,point_seed);
	let s_x=(0..setup.params.n_parties).map(|i|partial_claim(setup,i,&table,&point)).sum();
	let(r_h,r_a,r_b)=point;(Instance{r_h,r_a,r_b,s_x},crate::setup::Witness{table})
}

/// Fresh client preprocessing for the external-input runner. No secret seed is an argument.
pub fn run_client_external(setup:&Setup,point_seed:u64,input:&[u8],addr:&str,prepared:&mut impl FnMut(Duration,u64))->(Duration,u64) {
	let mut rng=fresh_rng();let(inst,wit)=external_instance(setup,point_seed,input,&mut rng);
	let mut conn=Conn::new(connect(addr));conn.send(&CLIENT_ID.to_le_bytes());
	conn.send(&configuration(setup,point_seed,input.len()*8));conn.send_l(&[inst.s_x]);
	conn.send(&Sha256::digest(input));assert_eq!(conn.recv(),b"share");
	let start=Instant::now();let(n,k,np)=(setup.params.n(),setup.params.k(),setup.params.n_parties);
	let cols:Vec<_>=(0..n).filter(|&x|!setup.layout.is_pad[x]).collect();
	let mut out=vec![vec![L::ZERO;cols.len()];np];
	for(c,&x)in cols.iter().enumerate(){let vals:Vec<_>=(0..k).map(|y|wit.table[y*n+x]).collect();
		for(i,s)in setup.sharing.share(&vals,&mut rng).into_iter().enumerate(){out[i][c]=s;}}
	let sharing=start.elapsed();for v in &out{conn.send_l(v);}
	conn.send(&(sharing.as_micros() as u64).to_le_bytes());
	drop(out);drop(wit);drop(rng);prepared(sharing,conn.sent);
	conn.send(b"client_ready");(sharing,conn.sent)
}

/// The input client: fills the whole table (data entries and tensor masks), computes the claim,
/// shares every non-padding column, sends each server its shares through the aggregator, and
/// leaves. Reports its local sharing time.
pub fn run_client(setup: &Setup, seed: u64, n_data: Option<usize>, addr: &str) {
	let p = &setup.params;
	let (n, k, np) = (p.n(), p.k(), p.n_parties);
	let mut conn = Conn::new(connect(addr));
	conn.send(&CLIENT_ID.to_le_bytes());
	let point = instance_point(setup, seed);
	let mut table = vec![L::ZERO; k * n];
	let mut s_x = L::ZERO;
	for owner in 0..np {
		fill_owner(setup, &mut table, owner, seed, n_data);
		s_x += partial_claim(setup, owner, &table, &point);
	}
	conn.send_l(&[s_x]);
	conn.recv(); // start signal
	let t0 = Instant::now();
	let cols: Vec<usize> = (0..n).filter(|&x| !setup.layout.is_pad[x]).collect();
	let mut out = vec![vec![L::ZERO; cols.len()]; np];
	let mut rng = StdRng::seed_from_u64(seed ^ 0xc11e);
	for (c, &x) in cols.iter().enumerate() {
		let vals: Vec<L> = (0..k).map(|y| table[y * n + x]).collect();
		for (i, s) in setup.sharing.share(&vals, &mut rng).into_iter().enumerate() {
			out[i][c] = s;
		}
	}
	let share_us = t0.elapsed().as_micros() as u64;
	for v in &out {
		conn.send_l(v);
	}
	conn.send(&share_us.to_le_bytes());
}

/// One server process. It holds no plaintext input: its share-row arrives from the client.
pub fn run_party<H: HashSuite>(setup: &Setup, id: usize, seed: u64, addr: &str) {
	run_party_inner::<H>(setup,id,seed,addr,None,&mut |_|{});
}

/// Independent party role. All share/mask/salt preparation finishes before its ready ack.
pub fn run_party_external<H:HashSuite>(setup:&Setup,id:usize,point_seed:u64,bits:usize,addr:&str,event:&mut impl FnMut(&str)) {
	run_party_inner::<H>(setup,id,point_seed,addr,Some(bits),event);
}
fn run_party_inner<H:HashSuite>(setup:&Setup,id:usize,seed:u64,addr:&str,external:Option<usize>,event:&mut dyn FnMut(&str)) {
	let p = &setup.params;
	let n = p.n();
	let hasher = Hasher::<H>::default();
	let mut conn = Conn::new(connect(addr));
	conn.send(&(id as u64).to_le_bytes());
	if let Some(bits)=external {conn.send(&configuration(setup,seed,bits));}
	let point = instance_point(setup, seed);
	let inst = Instance { r_h: point.0, r_a: point.1, r_b: point.2, s_x: L::ZERO };
	let mut party = Party::new(id, n, seed.wrapping_add(id as u64 + 1));
	if external.is_some(){party.rng=fresh_rng();party.prepare_salts(setup);}

	// Preprocessing: shares of the padding columns from F_rand.
	let padding=conn.recv_l();assert_eq!(padding.len(),setup.layout.pad.len());
	for (&x, s) in setup.layout.pad.iter().zip(padding) {
		party.row[x] = s;
	}
	conn.recv(); // start signal

	// Initial sharing: the client's shares of all non-padding columns, in column order.
	let shares=conn.recv_l();assert_eq!(shares.len(),n-setup.layout.pad.len());
	for (x, v) in (0..n).filter(|&x| !setup.layout.is_pad[x]).zip(shares) {
		party.row[x] = v;
	}
	if external.is_some(){event("party_ready");conn.send(b"ready");assert_eq!(conn.recv(),b"go");}

	// Commitment of layer 0, then round 1 (root, ξ_p).
	let t0 = Instant::now();
	let cw = setup.row.encode(&party.row);
	party.time.encode += t0.elapsed();
	party.commit_layer(setup, &hasher, 0, cw);
	let xi = party.frontend(setup, &inst, None)[0];
	let mut msg = party.subtrees[0].root().to_vec();
	msg.extend_from_slice(l_bytes(&[xi]));
	conn.send(&msg);
	let alpha = conn.recv_l()[0];
	// Round 2: T_p.
	let t = party.frontend(setup, &inst, Some(alpha));
	conn.send_l(&t);
	let ch2 = conn.recv_l();
	let (r_pp, omega) = (ch2[..LOG_D].to_vec(), ch2[LOG_D..].to_vec());
	// Round 3: H_ω.
	let mask_w = setup.mask_weight(&omega);
	conn.send_l(&[party.h_omega(setup, &mask_w)]);
	let eps = conn.recv_l()[0];
	let ch = Challenges { alpha, r_pp, omega, eps, r: Vec::new() };
	party.weights(setup, &inst, &ch, &mask_w);
	// Folding rounds: (root of layer j for j ≥ 1, g_{i,j,0}, g_{i,j,2}).
	for j in 0..p.folds() {
		let (g0, g2) = party.round_poly();
		let mut msg = if j == 0 { vec![0u8; 32] } else { party.subtrees[j].root().to_vec() };
		msg.extend_from_slice(l_bytes(&[g0, g2]));
		conn.send(&msg);
		let rj = conn.recv_l()[0];
		party.fold(setup, &hasher, j, rj);
	}
	// Commit terminal coefficients before queries; disclose them with the answers.
	let t0 = Instant::now();
	let mut salt = party.tail_salt;
	if external.is_none(){rand::Rng::fill_bytes(&mut party.rng, &mut salt);}
	let tail_leaf = hasher.at_layer(TAG_TAIL).leaf(TAG_TAIL, id as u64, l_bytes(&party.row), &salt);
	party.time.hash += t0.elapsed();
	conn.send(&tail_leaf);
	// Queries: answer those on the own row (values, salt, subtree path), in query order.
	let qb = conn.recv();
	let mut ans = l_bytes(&party.row).to_vec();
	ans.extend_from_slice(&salt);
	for q in qb.chunks_exact(16) {
		let (xa, qa) = (u64::from_le_bytes(q[..8].try_into().unwrap()) as usize, u64::from_le_bytes(q[8..].try_into().unwrap()) as usize);
		if xa != id {
			continue;
		}
		for j in 0..p.folds() {
			let qj = qa >> j;
			ans.extend_from_slice(l_bytes(&party.codewords[j][2 * qj..2 * qj + 2]));
			ans.extend_from_slice(&party.salts[j][qj]);
			for h in party.subtrees[j].path(qj) {
				ans.extend_from_slice(&h);
			}
		}
	}
	conn.send(&ans);
	// Diagnostics are requested only after complete proof serialization, so they cannot
	// consume a rate-limited link during the measured online interval.
	if external.is_some(){assert_eq!(conn.recv(),b"report");}
	// Report: local compute time (ms) and bytes.
	let tt = &party.time;
	let rep: Vec<u64> = [tt.share, tt.encode, tt.hash, tt.frontend, tt.weights, tt.rounds]
		.iter()
		.map(|d| d.as_micros() as u64)
		.chain([conn.sent, conn.recv])
		.collect();
	conn.send(bytemuck::cast_slice(&rep));
}

fn connect(addr: &str) -> TcpStream {
	for _ in 0..600 {
		if let Ok(s) = TcpStream::connect(addr) {
			return s;
		}
		std::thread::sleep(Duration::from_millis(100));
	}
	panic!("cannot connect to {addr}");
}

/// Wall-clock phases measured by the aggregator, plus traffic.
#[derive(Debug, Default)]
pub struct NetReport {
	/// New external runner: all-ready through complete proof serialization; no verification.
	pub online: Duration,
	pub serialization: Duration,
	pub preparation: Duration,
	/// External runner only: per-party online (upload, download) payload, no TCP framing.
	pub online_party_payload: Vec<(u64,u64)>,
	pub sharing: Duration,
	pub commit_frontend: Duration,
	pub folding: Duration,
	pub termination: Duration,
	pub total: Duration,
	pub verify: Duration,
	/// Per-party bytes sent and received (as counted by each party).
	pub party_bytes: Vec<(u64, u64)>,
	/// Per-party local compute time, µs: share, encode, hash, frontend, weights, rounds.
	pub party_compute_us: Vec<[u64; 6]>,
	pub proof_ok: bool,
	/// Aggregator-party application bytes during commitment/opening, each link counted once.
	pub online_bytes: u64,
	pub proof_bytes: usize,
	/// The client's local sharing time and the bytes it sent.
	pub client_share: Duration,
	pub client_sent: u64,
}

/// Receive one message from every party concurrently (one thread per connection), so that a
/// party whose message exceeds the socket buffers does not wait for the parties before it.
/// Used for the query answers; the per-round messages of at most a few KiB fit in the socket
/// buffers and are read in order.
fn recv_all(conns: &mut [Conn]) -> Vec<Vec<u8>> {
	std::thread::scope(|s| {
		let hs: Vec<_> = conns.iter_mut().map(|c| s.spawn(move || c.recv())).collect();
		hs.into_iter().map(|h| h.join().unwrap()).collect()
	})
}

/// The aggregator: accepts N parties, runs the protocol, assembles and verifies the proof.
pub fn run_aggregator<H: HashSuite>(setup: &Setup, seed: u64, listener: TcpListener) -> NetReport {
	run_aggregator_inner::<H>(setup,seed,listener,None,&mut |_|{}).report
}

pub struct ExternalArtifact {
	pub report:NetReport,
	pub instance:Instance,
	pub proof:Vec<u8>,
	pub input_prefix_hash:Hash,
	pub commitment:Hash,
}
pub fn run_aggregator_external<H:HashSuite>(setup:&Setup,point_seed:u64,bits:usize,listener:TcpListener,event:&mut impl FnMut(&str))->ExternalArtifact {
	run_aggregator_inner::<H>(setup,point_seed,listener,Some(bits),event)
}
fn run_aggregator_inner<H:HashSuite>(setup:&Setup,seed:u64,listener:TcpListener,external:Option<usize>,event:&mut dyn FnMut(&str))->ExternalArtifact {
	let preparation=Instant::now();
	let p = &setup.params;
	let np = p.n_parties;
	let hasher = Hasher::<H>::default();
	let mut conns: Vec<Option<Conn>> = (0..np).map(|_| None).collect();
	let mut client = None;
	for _ in 0..np + 1 {
		let (s, _) = listener.accept().unwrap();
		let mut c = Conn::new(s);
		let identity=c.recv();assert_eq!(identity.len(),8);let id=u64::from_le_bytes(identity.try_into().unwrap());
		if let Some(bits)=external{assert_eq!(c.recv(),configuration(setup,seed,bits),"role configuration mismatch");}
		match id {
			CLIENT_ID => {assert!(client.is_none());client = Some(c);},
			id => {assert!((id as usize)<np && conns[id as usize].is_none());conns[id as usize] = Some(c);},
		}
	}
	let mut conns: Vec<Conn> = conns.into_iter().map(Option::unwrap).collect();
	let mut client = client.expect("no client connected");
	let s_x: L = client.recv_l()[0];
	let input_prefix_hash=if external.is_some(){client.recv().try_into().expect("32-byte input hash")}else{[0;32]};
	let point = instance_point(setup, seed);
	let inst = Instance { r_h: point.0, r_a: point.1, r_b: point.2, s_x };

	// Preprocessing: F_rand deals the padding columns.
	let mut dealer = if external.is_some(){fresh_rng()}else{StdRng::seed_from_u64(seed ^ 0x5eed)};
	let mut pad = vec![vec![L::ZERO; setup.layout.pad.len()]; np];
	for c in 0..setup.layout.pad.len() {
		for (i, s) in setup.sharing.random_shares(&mut dealer).into_iter().enumerate() {
			pad[i][c] = s;
		}
	}
	for (c, v) in conns.iter_mut().zip(&pad) {
		c.send_l(v);
	}
	drop(pad);
	for c in conns.iter_mut() {
		c.send(&[1]);
	}
	client.send(if external.is_some(){b"share"}else{&[1]});

	let mut rep = NetReport::default();
	let start = Instant::now();
	// Sharing: relay the client's message for server i to server i, forwarding each one while
	// the next is still arriving.
	std::thread::scope(|sc| {
		for c in conns.iter_mut() {
			let m = client.recv();
			sc.spawn(move || c.send(&m));
		}
	});
	rep.sharing = start.elapsed();
	rep.client_share = Duration::from_micros(u64::from_le_bytes(client.recv()[..8].try_into().unwrap()));
	if external.is_some(){assert_eq!(client.recv(),b"client_ready");}
	rep.client_sent = client.recv;
	drop(client);
	if external.is_some(){for c in &mut conns{assert_eq!(c.recv(),b"ready");}event("all_parties_ready");}
	rep.preparation=preparation.elapsed();
	let bytes_before_online: u64 = conns.iter().map(|c| c.payload).sum();
	let directions_before:Vec<_>=conns.iter().map(|c|(c.recv_payload,c.sent_payload)).collect();
	if external.is_some(){event("online_start");}
	let t1 = Instant::now();
	if external.is_some(){for c in &mut conns{c.send(b"go");}}

	let bcast = |conns: &mut [Conn], v: &[L]| conns.iter_mut().for_each(|c| c.send_l(v));
	let dummy2 = dummy_root(&hasher,2);
    let dummy3 = dummy_root(&hasher,3);
    let dummy4 = dummy_root(&hasher,4);
	let mut tr = Transcript::new(&hasher, &bound_instance(setup,&inst,&[]));
	// Round 1.
	let r1: Vec<Vec<u8>> = conns.iter_mut().map(|c| c.recv()).collect();
	let mut roots = vec![Tree::build(&hasher.at_layer(0), r1.iter().map(|m| hash_from(m)).collect())];
	let xi: L = r1.iter().map(|m| to_l(&m[32..])[0]).sum();
	let alpha = tr.round(&roots[0].root(), l_bytes(&[xi])).field();
	bcast(&mut conns, &[alpha]);
	// Round 2.
	let mut t = vec![L::ZERO; D];
	for c in conns.iter_mut() {
		for (a, b) in t.iter_mut().zip(c.recv_l()) {
			*a += b;
		}
	}
	let mut c2 = tr.round(&dummy2, l_bytes(&t));
	let mut ch2: Vec<L> = (0..LOG_D).map(|_| c2.field()).collect();
	ch2.extend((0..setup.n_omega()).map(|_| c2.field()));
	bcast(&mut conns, &ch2);
	// Round 3.
	let h_omega: L = conns.iter_mut().map(|c| c.recv_l()[0]).sum();
	let eps = tr.round(&dummy3, l_bytes(&[h_omega])).field();
	bcast(&mut conns, &[eps]);
	rep.commit_frontend = t1.elapsed();
	let t2 = Instant::now();
	// Folding rounds.
	let mut coeffs = Vec::new();
	for j in 0..p.folds() {
		let ms: Vec<Vec<u8>> = conns.iter_mut().map(|c| c.recv()).collect();
		if j > 0 {
			roots.push(Tree::build(&hasher.at_layer(j as u64), ms.iter().map(|m| hash_from(m)).collect()));
		}
		let (mut g0, mut g2) = (L::ZERO, L::ZERO);
		for m in &ms {
			let v = to_l(&m[32..]);
			g0 += v[0];
			g2 += v[1];
		}
		coeffs.push((g0, g2));
		let root = if j == 0 { dummy4 } else { roots[j].root() };
		let rj = tr.round(&root, l_bytes(&[g0, g2])).field();
		bcast(&mut conns, &[rj]);
	}
	rep.folding = t2.elapsed();
	let t3 = Instant::now();
	// Tails, queries, openings.
	let tl = 1usize << p.tau;
	let tm: Vec<Vec<u8>> = conns.iter_mut().map(|c| c.recv()).collect();
	let leaves = tm.iter().map(|m| m.as_slice().try_into().unwrap()).collect();
	let tail_root = Tree::build(&hasher.at_layer(TAG_TAIL), leaves).root();
	let queries = sample_queries(setup, &mut tr, &tail_root);
	let qb: Vec<u8> = queries.iter().flat_map(|&(x, q)| [(x as u64).to_le_bytes(), (q as u64).to_le_bytes()].concat()).collect();
	for c in conns.iter_mut() {
		c.send(&qb);
	}
	let answers: Vec<Vec<u8>> = recv_all(&mut conns);
	let tails: Vec<Vec<L>> = answers.iter().map(|m| to_l(&m[..32 * tl])).collect();
	let tail_salts: Vec<[u8; 32]> = answers.iter().map(|m| m[32 * tl..32 * tl + 32].try_into().unwrap()).collect();
	let mut cursor = vec![32 * (tl + 1); np];
	let openings = queries
		.iter()
		.map(|&(xa, _)| {
			(0..p.folds())
				.map(|j| {
					let a = &answers[xa];
					let mut o = cursor[xa];
					let values = to_l(&a[o..o + 64]);
					o += 64;
					let salt: [u8; 32] = a[o..o + 32].try_into().unwrap();
					o += 32;
					let depth = p.m() - j - 1;
					let mut path: Vec<Hash> = (0..depth).map(|d| hash_from(&a[o + 32 * d..])).collect();
					o += 32 * depth;
					cursor[xa] = o;
					path.extend(roots[j].path(xa));
					Opening { values: [values[0], values[1]], salt, path }
				})
				.collect()
		})
		.collect();
	rep.termination = t3.elapsed();
	rep.total = start.elapsed();
	rep.online_bytes = conns.iter().map(|c| c.payload).sum::<u64>() - bytes_before_online;
	rep.online_party_payload=conns.iter().zip(directions_before).map(|(c,(up,down))|(c.recv_payload-up,c.sent_payload-down)).collect();
	let serializing=Instant::now();
	let proof = Proof {
		roots: roots.iter().map(Tree::root).collect(),
		tail_root,
		xi,
		t,
		h_omega,
		coeffs,
		tails,
		tail_salts,
		openings,
	};
	let proof_bytes=if external.is_some(){crate::pcs_codec::encode_proof(&proof)}else{Vec::new()};
	rep.serialization=serializing.elapsed();
	if external.is_some(){
		rep.online=t1.elapsed();rep.total=rep.online;rep.proof_bytes=proof_bytes.len();event("online_complete");
		for c in &mut conns{c.send(b"report");}
	}
	for c in conns.iter_mut() {
		let r: Vec<u64> = c.recv().chunks_exact(8).map(|b| u64::from_le_bytes(b.try_into().unwrap())).collect();
		rep.party_compute_us.push(r[..6].try_into().unwrap());
		rep.party_bytes.push((r[6], r[7]));
	}
	if external.is_none(){let tv=Instant::now();let verified=verify::<H>(setup,&inst,&proof);
		rep.proof_ok=verified.is_ok();rep.verify=tv.elapsed();if let Ok(queries)=verified{rep.proof_bytes=proof_size(setup,&proof,&queries).total;}}
	ExternalArtifact{report:rep,instance:inst,proof:proof_bytes,input_prefix_hash,commitment:proof.roots[0]}
}

#[cfg(test)]
mod external_tests {
	use super::*;
	#[test]
	fn external_bits_and_claim_match_independent_bit_sum() {
		let bits=4096;let gamma=16;let tau=3;
		let setup=Setup::new(crate::params::Params{n_parties:4,ell:crate::params::ell_for_bits(4,gamma,tau,2,bits),beta:2,gamma,tau,salt_bytes:32});
		let input:Vec<u8>=(0..bits/8).map(|i|(i*73+11) as u8).collect();
		let(a,wa)=external_instance(&setup,71,&input,&mut StdRng::seed_from_u64(1));
		let(b,wb)=external_instance(&setup,71,&input,&mut StdRng::seed_from_u64(2));
		assert_eq!(a.s_x,b.s_x);assert_ne!(wa.table,wb.table);
		let mut offset=0;let mut sum=L::ZERO;
		for owner in 0..4 {for &x in &setup.layout.owned[owner] {for y in 0..setup.params.k() {
			if setup.layout.mask_index(owner,y,x).is_some(){continue;}
			let value=wa.table[y*setup.params.n()+x];
			for h in 0..D {let expected=offset<bits && input[offset/8]>>(offset%8)&1==1;
				assert_eq!(crate::field::bit(value,h),expected);
				if expected {sum+=crate::field::chi(h,&a.r_h)*crate::field::chi(y,&a.r_a)*crate::field::chi(x,&a.r_b);}
				offset+=1;
			}
		}}}
		assert!(offset>=bits);assert_eq!(sum,a.s_x);
	}
}

#[cfg(test)]
mod standalone_v4_tcp_tests {
 use super::*;
 use binius_hash::Blake3HashSuite;
 #[test]
 fn standalone_tcp_legacy_and_fresh_external_schedules_verify(){
  let p=crate::params::Params{n_parties:4,ell:11,beta:2,gamma:14,tau:3,salt_bytes:32};
  for external in [false,true] {
   let listener=TcpListener::bind("127.0.0.1:0").unwrap();let addr=listener.local_addr().unwrap().to_string();
   std::thread::scope(|scope| {
    for id in 0..p.n_parties {let p=p.clone();let addr=addr.clone();scope.spawn(move||{
     let setup=Setup::new(p);if external {run_party_external::<Blake3HashSuite>(&setup,id,79,512,&addr,&mut |_|{});}else{run_party::<Blake3HashSuite>(&setup,id,79,&addr);}
    });}
    let cp=p.clone();let client_addr=addr.clone();scope.spawn(move||{
     let setup=Setup::new(cp);if external {run_client_external(&setup,79,&[0x97;64],&client_addr,&mut |_,_|{});}else{run_client(&setup,79,Some(512),&client_addr);}
    });
    let setup=Setup::new(p.clone());
    if external {let artifact=run_aggregator_external::<Blake3HashSuite>(&setup,79,512,listener,&mut |_|{});
     let proof=crate::pcs_codec::decode_proof(&setup,&artifact.proof).unwrap();assert!(verify::<Blake3HashSuite>(&setup,&artifact.instance,&proof).is_ok());
    } else {assert!(run_aggregator::<Blake3HashSuite>(&setup,79,listener).proof_ok);}
   });
  }
 }
}
