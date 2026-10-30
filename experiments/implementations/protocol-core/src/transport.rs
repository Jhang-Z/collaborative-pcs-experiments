//! Local TCP execution of the existing ideal-message schedule, not a secure MPC realization.
//! Enabled explicitly by a benchmark caller; normal proofs/verifiers open no sockets.
use std::{cell::{Cell,RefCell},io::{Read,Write},net::{TcpListener,TcpStream},time::Instant};
use crate::{field::L,merkle::Hash,protocol::Opening};
thread_local! {static WIRE:RefCell<Option<Wire>>=const{RefCell::new(None)}; static PAUSED:Cell<bool>=const{Cell::new(false)};}
#[derive(Clone,Copy,Default,Debug)]
pub struct Stats {pub up:u64,pub down:u64,pub framing:u64,pub rounds:u64,pub seconds:f64,pub input_bytes:u64}
struct Wire {client:Vec<TcpStream>,server:Vec<TcpStream>,stats:Stats}
pub fn start(n:usize) {
    let listener=TcpListener::bind("127.0.0.1:0").unwrap();let addr=listener.local_addr().unwrap();
    let(mut client,mut server)=(Vec::new(),Vec::new());
    for _ in 0..n {let a=TcpStream::connect(addr).unwrap();let(b,_)=listener.accept().unwrap();a.set_nodelay(true).unwrap();b.set_nodelay(true).unwrap();client.push(a);server.push(b);}
    WIRE.with(|w|{assert!(w.borrow().is_none());*w.borrow_mut()=Some(Wire{client,server,stats:Stats::default()});});
}
pub fn stop()->Stats {WIRE.with(|w|w.borrow_mut().take().map_or(Stats::default(),|w|w.stats))}
pub fn stats()->Stats {WIRE.with(|w|w.borrow().as_ref().map_or(Stats::default(),|w|w.stats))}
pub fn party_count()->usize {WIRE.with(|w|w.borrow().as_ref().map_or(1,|w|w.client.len()))}
pub fn enabled()->bool {!PAUSED.with(Cell::get)&&WIRE.with(|w|w.borrow().is_some())}
pub struct Pause(bool);
pub fn pause()->Pause {Pause(PAUSED.with(|p|p.replace(true)))}
impl Drop for Pause {fn drop(&mut self){PAUSED.with(|p|p.set(self.0));}}
fn send(mut stream:&TcpStream,data:&[u8]) {stream.write_all(&(data.len() as u64).to_le_bytes()).unwrap();stream.write_all(data).unwrap();}
fn recv(mut stream:&TcpStream)->Vec<u8> {let mut b=[0;8];stream.read_exact(&mut b).unwrap();let mut data=vec![0;u64::from_le_bytes(b) as usize];stream.read_exact(&mut data).unwrap();data}
fn exchange(messages:Vec<Vec<u8>>,up:bool,input:bool)->Vec<Vec<u8>> {
    if !enabled(){return messages;}
    WIRE.with(|cell|{
        let mut w=cell.borrow_mut();let w=w.as_mut().unwrap();assert_eq!(messages.len(),w.client.len());
        let start=Instant::now();let count=messages.iter().map(|x|x.len() as u64).sum::<u64>();
        // A blocking I/O coordinator and the same bounded pool of party workers.
        let received=std::thread::scope(|scope| {
            if up {
                let reader=scope.spawn(||w.server.iter().map(recv).collect::<Vec<_>>());
                crate::parallel::map(messages.len(),|i|send(&w.client[i],&messages[i]));reader.join().unwrap()
            } else {
                let writer=scope.spawn(||{for(i,m)in messages.iter().enumerate(){send(&w.server[i],m);}});
                let r=crate::parallel::map(messages.len(),|i|recv(&w.client[i]));writer.join().unwrap();r
            }
        });
        assert_eq!(received.iter().map(|x|x.len() as u64).sum::<u64>(),count);
        if input{w.stats.input_bytes+=count;}if up{w.stats.up+=count;}else{w.stats.down+=count;}w.stats.framing+=8*messages.len() as u64;w.stats.rounds+=1;w.stats.seconds+=start.elapsed().as_secs_f64();received
    })
}
pub fn broadcast(data:&[u8]) {
    if !enabled(){return;}
    let n=WIRE.with(|w|w.borrow().as_ref().unwrap().client.len());
    for received in exchange(vec![data.to_vec();n],false,false){assert_eq!(received,data);}
}
pub fn values<T:bytemuck::Pod>(a:Vec<Vec<T>>,up:bool)->Vec<Vec<T>> {
    if !enabled(){return a;}
    exchange(a.iter().map(|v|bytemuck::cast_slice(v).to_vec()).collect(),up,!up).into_iter().map(|b|b.chunks_exact(std::mem::size_of::<T>()).map(bytemuck::pod_read_unaligned).collect()).collect()
}
pub fn arrays<const K:usize>(a:Vec<[L;K]>)->Vec<[L;K]> {
    if !enabled(){return a;}
    values(a.into_iter().map(Vec::from).collect(),true).into_iter().map(|v|v.try_into().ok().unwrap()).collect()
}
pub fn scalars(a:Vec<L>)->Vec<L> {arrays(a.into_iter().map(|v|[v]).collect()).into_iter().map(|v|v[0]).collect()}
pub fn hashes(a:Vec<Hash>)->Vec<Hash> {
    if !enabled(){return a;}
    exchange(a.into_iter().map(Vec::from).collect(),true,false).into_iter().map(|v|v.try_into().unwrap()).collect()
}
pub fn openings(mut a:Vec<Vec<Opening>>,queries:&[(usize,usize)],n:usize)->Vec<Vec<Opening>> {
    if !enabled(){return a;}
    let mut messages=vec![Vec::new();n];
    for (ops,&(i,_)) in a.iter().zip(queries) {for op in ops {messages[i].extend_from_slice(bytemuck::cast_slice(&op.values));messages[i].extend(op.salt);for h in &op.path{messages[i].extend(h);}}}
    let messages=exchange(messages,true,false);let mut at=vec![0;n];
    for(ops,&(i,_))in a.iter_mut().zip(queries){for op in ops{
        let b=&messages[i];let p=&mut at[i];op.values=bytemuck::pod_read_unaligned(&b[*p..*p+64]);*p+=64;
        op.salt.copy_from_slice(&b[*p..*p+32]);*p+=32;for h in &mut op.path{h.copy_from_slice(&b[*p..*p+32]);*p+=32;}
    }}
    assert!(at.iter().zip(&messages).all(|(p,m)|*p==m.len()));a
}
#[cfg(test)]mod tests{
    use super::*;
    #[test]fn local_tcp_delivers_all_32_parties(){
        start(32);let a:Vec<Vec<u64>>=(0..32).map(|i|(0..32768).map(|j|i*32768+j).collect()).collect();
        assert_eq!(values(a.clone(),false),a);assert_eq!(values(a.clone(),true),a);broadcast(b"next challenge");let s=stop();
        assert_eq!(s.up,32*32768*8);assert_eq!(s.down,s.up+32*14);assert_eq!(s.rounds,3);
    }
}
