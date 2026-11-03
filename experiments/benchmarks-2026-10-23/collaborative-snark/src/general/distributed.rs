//! Owner-exclusive public tables. The controller receives only small reductions/queries.
//! Same-host correctness transport: peer payloads really are serialized and moved.
use std::{collections::HashMap,sync::{Arc,mpsc},thread,time::Instant};
use crate::{field::{B,Field,L,chi,eq_expand},code::RowCode};

#[derive(Clone,Copy,Debug)]
pub struct Vector {pub id:usize,pub len:usize}
#[derive(Clone,Default,serde::Serialize)]
pub struct Stats {pub sent_bytes:u64,pub received_bytes:u64,pub peer_messages:u64,pub resident_array_peak_cells:usize,pub task_wall_seconds:f64}
type Task=Arc<dyn Fn(&mut Owner,&[u8])->Vec<L>+Send+Sync>;
enum Command {Run(Task,Vec<u8>,bool,Option<mpsc::Sender<(usize,Vec<u8>)>>),Stop}
pub struct Owner {
    pub rank:usize,pub n:usize,pub arrays:HashMap<usize,Vec<L>>,
    peers:Vec<mpsc::Sender<(usize,Vec<u8>)>>,incoming:mpsc::Receiver<(usize,Vec<u8>)>,epoch:u64,
    current_cells:usize,stats:Stats,pending:HashMap<u64,Vec<(usize,Vec<u8>)>>,
}
pub fn bounds(len:usize,n:usize,rank:usize)->(usize,usize) {
    let block=len.div_ceil(n);((rank*block).min(len),((rank+1)*block).min(len))
}
fn owner(len:usize,n:usize,index:usize)->usize {index/len.div_ceil(n)}
pub fn pin_compute_thread() {
    if let Ok(cpu)=std::env::var("GENERAL_COMPUTE_CPU") {
        let cpu:usize=cpu.parse().expect("GENERAL_COMPUTE_CPU must be an integer");
        #[cfg(target_os="linux")]
        unsafe {
            let mut mask:libc::cpu_set_t=std::mem::zeroed();libc::CPU_ZERO(&mut mask);libc::CPU_SET(cpu,&mut mask);
            assert_eq!(libc::sched_setaffinity(0,std::mem::size_of_val(&mask),&mask),0,"measurement CPU affinity");
            assert_eq!(libc::sched_getaffinity(0,std::mem::size_of_val(&mask),&mut mask),0);
            assert!(libc::CPU_ISSET(cpu,&mask)&&libc::CPU_COUNT(&mask)==1);
        }
        #[cfg(not(target_os="linux"))]
        let _=cpu;
    }
}
pub fn label(i:usize)->L {crate::field::from_words([i as u128,0])}
pub fn integer(v:L)->usize {crate::field::to_words(v)[0] as usize}
impl Owner {
    pub fn put(&mut self,id:usize,v:Vec<L>) {
        self.current_cells+=v.len();
        if let Some(old)=self.arrays.insert(id,v){self.current_cells-=old.len();}
        self.stats.resident_array_peak_cells=self.stats.resident_array_peak_cells.max(self.current_cells);
    }
    pub fn remove(&mut self,id:usize)->Option<Vec<L>> {let old=self.arrays.remove(&id);if let Some(v)=&old{self.current_cells-=v.len();}old}
    fn send_packet(&mut self,dst:usize,kind:u8,payload:&[u8]) {
        let mut packet=self.epoch.to_le_bytes().to_vec();packet.push(kind);packet.extend_from_slice(payload);
        self.stats.sent_bytes+=packet.len() as u64;self.stats.peer_messages+=1;
        crate::execution_trace::send(self.rank,dst,100+kind as u64,packet.len(),true);
        let _ipc=crate::execution_trace::pause();self.peers[dst].send((self.rank,packet)).unwrap();
    }
    /// Public injective shuffle: exactly the prefix [0,valid) is filled once.
    /// Exact receive counts replace a global barrier; future epochs remain buffered.
    pub fn route_dense(&mut self,id:usize,len:usize,records:Vec<(usize,L)>,valid:usize) {
        assert!(valid<=len);let(lo,hi)=bounds(len,self.n,self.rank);
        let expected=hi.min(valid)-lo.min(valid);let mut filled=0;let mut out=vec![L::ZERO;hi-lo];
        let mut packets=vec![Vec::new();self.n];
        for(index,value)in records {
            assert!(index<valid);let dst=owner(len,self.n,index);
            if dst==self.rank {out[index-lo]=value;filled+=1;}
            else {packets[dst].extend((index as u64).to_le_bytes());packets[dst].extend(bytemuck::bytes_of(&value));}
        }
        self.epoch+=1;
        for(dst,packet)in packets.into_iter().enumerate(){if !packet.is_empty(){self.send_packet(dst,0,&packet);}}
        let mut waiting=self.pending.remove(&self.epoch).unwrap_or_default();
        while filled<expected {
            let(src,packet)=if let Some(p)=waiting.pop(){p}else {
                let p={let _ipc=crate::execution_trace::pause();self.incoming.recv().unwrap()};
                self.stats.received_bytes+=p.1.len() as u64;crate::execution_trace::recv(p.0,self.rank,100+p.1[8] as u64,p.1.len());p
            };
            let epoch=u64::from_le_bytes(packet[..8].try_into().unwrap());
            if epoch>self.epoch {self.pending.entry(epoch).or_default().push((src,packet));continue;}
            assert_eq!(epoch,self.epoch);assert_eq!(packet[8],0);assert_eq!((packet.len()-9)%40,0);
            for record in packet[9..].chunks_exact(40) {
                let index=u64::from_le_bytes(record[..8].try_into().unwrap()) as usize;assert!(index>=lo&&index<hi&&index<valid);
                out[index-lo]=bytemuck::pod_read_unaligned(&record[8..]);filled+=1;
            }
        }
        assert_eq!(filled,expected);assert!(waiting.is_empty());self.put(id,out);
    }
    /// Sparse data packets plus a binary-tree ready/release barrier, without N^2 empty packets.
    pub fn route(&mut self,id:usize,len:usize,records:Vec<(usize,L)>,add:bool) {
        let mut packets=vec![Vec::new();self.n];let (lo,hi)=bounds(len,self.n,self.rank);let mut out=vec![L::ZERO;hi-lo];
        for(index,value)in records {
            assert!(index<len);let dst=owner(len,self.n,index);
            if dst==self.rank {if add{out[index-lo]+=value;}else{out[index-lo]=value;}}
            else{packets[dst].extend((index as u64).to_le_bytes());packets[dst].extend(bytemuck::bytes_of(&value));}
        }
        self.epoch+=1;let mut awaiting=vec![false;self.n];
        for(dst,payload)in packets.into_iter().enumerate(){if !payload.is_empty(){awaiting[dst]=true;self.send_packet(dst,0,&payload);}}
        let children:Vec<usize>=[2*self.rank+1,2*self.rank+2].into_iter().filter(|&i|i<self.n).collect();
        let mut ready=vec![false;children.len()];let mut announced=false;
        let mut waiting=self.pending.remove(&self.epoch).unwrap_or_default();
        loop {
            if !announced&&ready.iter().all(|&v|v)&&awaiting.iter().all(|&v|!v) {
                announced=true;
                if self.rank==0 {for &child in &children{self.send_packet(child,2,&[]);}break;}
                self.send_packet((self.rank-1)/2,1,&[]);
            }
            let(src,packet)=if let Some(p)=waiting.pop(){p}else{
                let p={let _ipc=crate::execution_trace::pause();self.incoming.recv().unwrap()};
                self.stats.received_bytes+=p.1.len() as u64;
                crate::execution_trace::recv(p.0,self.rank,100+p.1[8] as u64,p.1.len());p
            };
            let epoch=u64::from_le_bytes(packet[..8].try_into().unwrap());
            if epoch>self.epoch {self.pending.entry(epoch).or_default().push((src,packet));continue;}
            assert_eq!(epoch,self.epoch);
            match packet[8] {
                0=>{assert_eq!((packet.len()-9)%40,0);for record in packet[9..].chunks_exact(40){
                    let index=u64::from_le_bytes(record[..8].try_into().unwrap()) as usize;assert!(index>=lo&&index<hi);
                    let value=bytemuck::pod_read_unaligned(&record[8..]);if add{out[index-lo]+=value;}else{out[index-lo]=value;}
                }self.send_packet(src,3,&[]);},
                1=>{let i=children.iter().position(|&c|c==src).expect("ready from child");assert!(!ready[i]);ready[i]=true;},
                2=>{assert!(announced&&self.rank>0);assert_eq!(src,(self.rank-1)/2);for &child in &children{self.send_packet(child,2,&[]);}break;},
                3=>{assert!(awaiting[src]);awaiting[src]=false;},
                _=>panic!("peer packet kind"),
            }
        }
        // Every data packet is acknowledged before global Ready and hence before Release.
        // Future epochs can arrive early and are buffered; current data is consumed before release.
        assert!(waiting.is_empty());self.put(id,out);
    }

}
fn twiddle_range(code:&RowCode,log:usize,start:usize,count:usize,period:usize)->Vec<B> {
    if count==0 {return vec![];}
    let origin=code.twiddle(log,0);let basis:Vec<_>=(0..period.ilog2()).map(|b|code.twiddle(log,1<<b)+origin).collect();
    let mut j=start;let mut t=origin;let mut active=j;
    while active!=0 {let b=active.trailing_zeros() as usize;t+=basis[b];active&=active-1;}
    let mut out=Vec::with_capacity(count);
    for _ in 0..count {out.push(t);let next=(j+1)%period;let mut changed=j^next;
        while changed!=0 {let b=changed.trailing_zeros() as usize;t+=basis[b];changed&=changed-1;}j=next;
    }out
}
// Expand only the requested owner range; never replicate a circuit-sized table.
fn equality_range(point:&[L],start:usize,count:usize)->Vec<L> {
    let mut out=Vec::with_capacity(count);let mut cursor=start;
    while out.len()<count {
        let remaining=count-out.len();let max=(usize::BITS-1-remaining.leading_zeros()) as usize;
        let aligned=if cursor==0 {point.len()}else{cursor.trailing_zeros() as usize};
        let bits=max.min(aligned).min(point.len());
        let high=chi(cursor>>bits,&point[bits..]);
        out.extend(eq_expand(&point[..bits]).into_iter().map(|x|x*high));cursor+=1<<bits;
    }out
}
pub(super) struct EqualityLookup {low:Vec<L>,high:Vec<L>,split:usize}
impl EqualityLookup {
    pub(super) fn new(point:&[L])->Self {let split=point.len()/2;Self{low:eq_expand(&point[..split]),high:eq_expand(&point[split..]),split}}
    pub(super) fn value(&self,index:usize)->L {self.low[index&(self.low.len()-1)]*self.high[(index>>self.split)&(self.high.len()-1)]}
}
pub struct Runtime {senders:Vec<mpsc::Sender<Command>>,joins:Vec<thread::JoinHandle<Stats>>,next:usize,next_command:u64,pub n:usize,sealed:bool}
impl Runtime {
    pub fn new(n:usize)->Self {
        let mut sends=vec![];let mut receives=vec![];
        for _ in 0..n {let(s,r)=mpsc::channel();sends.push(s);receives.push(r);}
        let mut senders=vec![];let mut joins=vec![];
        for (rank,incoming) in receives.into_iter().enumerate() {
            let (s,r)=mpsc::channel();senders.push(s);let peers=sends.clone();
            joins.push(thread::spawn(move|| {
                let _encoding=crate::code::sequential_encoding();
                let mut w=Owner{rank,n,arrays:HashMap::new(),peers,incoming,epoch:0,current_cells:0,stats:Stats::default(),pending:HashMap::new()};
                let _actor=crate::execution_trace::scope(rank);
                let _idle_mode=crate::execution_trace::pause();
                let mut pinned=false;
                loop {
                    let command={let _idle=crate::execution_trace::pause();r.recv()};
                    let Ok(Command::Run(task,packet,online,reply))=command else{break};
                    if online&&!pinned {pin_compute_thread();pinned=true;}
                    let _mode=if online{crate::execution_trace::force_online()}else{crate::execution_trace::pause()};
                    crate::execution_trace::recv(n,rank,200,packet.len());
                    assert_eq!(&packet[..8],b"GENKERN1");let seq=&packet[8..16];
                    let arglen=u64::from_le_bytes(packet[16..24].try_into().unwrap()) as usize;assert_eq!(arglen,packet.len()-24);
                    let start=Instant::now();let result=task(&mut w,&packet[24..]);w.stats.task_wall_seconds+=start.elapsed().as_secs_f64();
                    if let Some(reply)=reply {
                        assert!(result.len()<=n.max(4096),"controller response must be a bounded query batch");
                        let mut response=seq.to_vec();response.extend((result.len() as u64).to_le_bytes());response.extend(bytemuck::cast_slice(&result));
                        crate::execution_trace::send(rank,n,201,response.len(),true);
                        drop(_mode);
                        let _ipc=crate::execution_trace::pause();reply.send((rank,response)).unwrap();
                    }else {assert!(result.is_empty(),"effect command returned fields");drop(_mode);}
                }
                w.stats
            }));
        }
        Self{senders,joins,next:0,next_command:0,n,sealed:false}
    }
    #[cfg(test)] pub fn command_count(&self)->u64 {self.next_command}
    pub fn id(&mut self)->usize {let id=self.next;self.next+=1;id}
    fn command(&mut self,payload:&[u8])->Vec<u8> {
        self.next_command+=1;let mut packet=b"GENKERN1".to_vec();packet.extend(self.next_command.to_le_bytes());packet.extend((payload.len() as u64).to_le_bytes());packet.extend(payload);packet
    }
    pub fn run(&mut self,f:impl Fn(&mut Owner)->Vec<L>+Send+Sync+'static)->Vec<Vec<L>> {
        self.run_packets(vec![vec![];self.n],move|w,_|f(w))
    }
    pub fn run_packets(&mut self,payloads:Vec<Vec<u8>>,f:impl Fn(&mut Owner,&[u8])->Vec<L>+Send+Sync+'static)->Vec<Vec<L>> {
        self.dispatch(payloads,Arc::new(f),true)
    }
    /// Effects retain per-owner FIFO order; their completion is joined by a later sync call.
    pub fn run_effect(&mut self,f:impl Fn(&mut Owner)->Vec<L>+Send+Sync+'static) {
        self.run_packets_effect(vec![vec![];self.n],move|w,_|f(w));
    }
    pub fn run_packets_effect(&mut self,payloads:Vec<Vec<u8>>,f:impl Fn(&mut Owner,&[u8])->Vec<L>+Send+Sync+'static) {
        self.dispatch(payloads,Arc::new(f),false);
    }
    pub fn flush(&mut self) {self.run(|_|vec![]);}
    fn dispatch(&mut self,payloads:Vec<Vec<u8>>,task:Task,wait:bool)->Vec<Vec<L>> {
        self.dispatch_selected(payloads,task,wait,false)
    }
    fn dispatch_selected(&mut self,payloads:Vec<Vec<u8>>,task:Task,wait:bool,skip_empty:bool)->Vec<Vec<L>> {
        assert_eq!(payloads.len(),self.n);let channel=wait.then(mpsc::channel);let online=crate::execution_trace::enabled();
        let mut active=0;
        for(rank,payload)in payloads.into_iter().enumerate(){if skip_empty&&payload.is_empty(){continue;}active+=1;let packet=self.command(&payload);
            crate::execution_trace::send(self.n,rank,200,packet.len(),true);
            let reply=channel.as_ref().map(|(s,_)|s.clone());
            let _ipc=crate::execution_trace::pause();self.senders[rank].send(Command::Run(task.clone(),packet,online,reply)).unwrap();
        }
        let Some((s,r))=channel else{return vec![];};
        drop(s);let mut out=vec![vec![];self.n];
        for _ in 0..active {
            let(rank,packet)={let _ipc=crate::execution_trace::pause();r.recv().unwrap()};
            crate::execution_trace::recv(rank,self.n,201,packet.len());
            let count=u64::from_le_bytes(packet[8..16].try_into().unwrap()) as usize;assert_eq!(packet.len(),16+32*count);
            out[rank]=packet[16..].chunks_exact(32).map(bytemuck::pod_read_unaligned).collect();
        }out
    }
    pub fn seal(&mut self) {self.sealed=true;}
    pub fn checkpoint(&self)->usize {self.next}
    pub fn begin_proof(&mut self,checkpoint:usize) {
        self.run(move|w|{w.arrays.retain(|&id,_|id<checkpoint);w.current_cells=w.arrays.values().map(Vec::len).sum();w.stats=Stats::default();vec![]});
        self.next=checkpoint;self.sealed=false;
    }
    /// Setup input only. This whole-array API is forbidden after the online boundary.
    pub fn load(&mut self,mut values:Vec<L>)->Vector {
        assert!(!self.sealed,"whole controller arrays are setup-only");
        let v=Vector{id:self.id(),len:values.len()};let mut chunks=Vec::with_capacity(self.n);
        for rank in (0..self.n).rev() {let (lo,_)=bounds(v.len,self.n,rank);chunks.push(values.split_off(lo));}
        chunks.reverse();self.load_local(v,&mut chunks);v
    }
    pub fn load_parties(&mut self,mut shares:Vec<Vec<L>>)->Vector {
        assert!(!self.sealed,"party inputs are preparation-only");
        assert_eq!(shares.len(),self.n);let size=shares[0].len();assert!(shares.iter().all(|v|v.len()==size));
        let v=Vector{id:self.id(),len:self.n*size};self.load_local(v,&mut shares);v
    }
    fn load_local(&mut self,v:Vector,chunks:&mut [Vec<L>]) {
        for (rank,chunk) in chunks.iter_mut().enumerate() {
            let cells=std::sync::Mutex::new(Some(std::mem::take(chunk)));
            let task:Task=Arc::new(move|w,_|{w.put(v.id,cells.lock().unwrap().take().unwrap());vec![]});
            let(s,r)=mpsc::channel();let packet=self.command(&[]);let online=crate::execution_trace::enabled();
            crate::execution_trace::send(self.n,rank,200,packet.len(),true);
            {let _ipc=crate::execution_trace::pause();self.senders[rank].send(Command::Run(task,packet,online,Some(s))).unwrap();}
            let(_,packet)={let _ipc=crate::execution_trace::pause();r.recv().unwrap()};
            crate::execution_trace::recv(rank,self.n,201,packet.len());
        }
    }
    #[cfg(test)]
    pub fn generate(&mut self,len:usize,f:impl Fn(usize)->L+Send+Sync+'static)->Vector {
        let v=Vector{id:self.id(),len};self.run_effect(move|w| {let(lo,hi)=bounds(len,w.n,w.rank);w.put(v.id,(lo..hi).map(&f).collect());vec![]});v
    }
    pub fn map(&mut self,inputs:&[Vector],f:impl Fn(usize,&[L])->L+Send+Sync+'static)->Vector {
        let len=inputs[0].len;assert!(inputs.iter().all(|v|v.len==len));
        let ids:Vec<_>=inputs.iter().map(|v|v.id).collect();let v=Vector{id:self.id(),len};
        self.run_effect(move|w| {
            let (lo,hi)=bounds(len,w.n,w.rank);let mut point=vec![L::ZERO;ids.len()];let mut out=Vec::with_capacity(hi-lo);
            for j in 0..hi-lo {for (x,&id) in point.iter_mut().zip(&ids) {*x=w.arrays[&id][j];}out.push(f(lo+j,&point));}
            w.put(v.id,out);vec![]
        });v
    }
    pub fn map_local<F:Fn(usize,&[L])->L>(&mut self,inputs:&[Vector],make:impl Fn()->F+Send+Sync+'static)->Vector {
        let len=inputs[0].len;assert!(inputs.iter().all(|v|v.len==len));
        let ids:Vec<_>=inputs.iter().map(|v|v.id).collect();let v=Vector{id:self.id(),len};
        self.run_effect(move|w| {
            let f=make();let(lo,hi)=bounds(len,w.n,w.rank);let mut values=vec![L::ZERO;ids.len()];let mut out=Vec::with_capacity(hi-lo);
            for j in 0..hi-lo {for(x,&id)in values.iter_mut().zip(&ids){*x=w.arrays[&id][j];}out.push(f(lo+j,&values));}
            w.put(v.id,out);vec![]
        });v
    }
    pub fn equality_sum(&mut self,len:usize,points:&[Vec<L>],coefficients:&[L])->Vector {
        assert_eq!(points.len(),coefficients.len());let pp=points.to_vec();let aa=coefficients.to_vec();
        let v=Vector{id:self.id(),len};self.run_effect(move|w| {
            let(lo,hi)=bounds(len,w.n,w.rank);let mut values=vec![L::ZERO;hi-lo];
            for(p,&a)in pp.iter().zip(&aa){let end=hi.min(1<<p.len());if lo<end {
                for(x,y)in values.iter_mut().zip(equality_range(p,lo,end-lo)){*x+=a*y;}
            }}w.put(v.id,values);vec![]
        });v
    }
    pub fn equality_lookup(&mut self,input:Vector,point:&[L])->Vector {
        let p=point.to_vec();self.map_local(&[input],move||{let table=EqualityLookup::new(&p);move|_,v|table.value(integer(v[0]))})
    }
    pub fn pair_layers(&mut self,input:Vector,depth:usize,f:impl Fn(usize,usize,L,L)->L+Send+Sync+'static)->Vec<Vector> {
        assert!(depth==0||input.len>>depth>=self.n);
        let levels:Vec<_>=(1..=depth).map(|d|Vector{id:self.id(),len:input.len>>d}).collect();
        if depth==0 {return levels;}
        let local=levels.clone();self.run_effect(move|w| {
            let mut previous=input;
            for(d,&next)in local.iter().enumerate(){let(lo,_)=bounds(next.len,w.n,w.rank);
                let data=&w.arrays[&previous.id];let values=data.chunks_exact(2).enumerate().map(|(j,a)|f(d,lo+j,a[0],a[1])).collect();
                w.put(next.id,values);previous=next;
            }vec![]
        });levels
    }
    pub fn fold_many(&mut self,inputs:&[Vector],r:L,release:&[Vector])->Vec<Vector> {self.fold_kernels(inputs,r,None,release)}
    pub fn fold_public(&mut self,f:Vector,w:Vector,cw:Vector,r:L,base_log:usize,release:&[Vector])->[Vector;3] {
        self.fold_kernels(&[f,w,cw],r,Some((2,base_log)),release).try_into().unwrap()
    }
    fn fold_kernels(&mut self,inputs:&[Vector],r:L,code:Option<(usize,usize)>,release:&[Vector])->Vec<Vector> {
        let source=inputs.to_vec();assert!(source.iter().all(|v|v.len%2==0));
        let out:Vec<_>=source.iter().map(|v|Vector{id:self.id(),len:v.len/2}).collect();let target=out.clone();
        let released:Vec<_>=release.iter().map(|v|v.id).collect();
        self.run_effect(move|w| {
            for(which,(&input,&output))in source.iter().zip(&target).enumerate(){
                let(lo,hi)=bounds(output.len,w.n,w.rank);
                let temporary=input.len<2*w.n;
                let id=if temporary {let(src_lo,_)=bounds(input.len,w.n,w.rank);
                    let records=w.arrays[&input.id].iter().enumerate().map(|(j,&x)|(src_lo+j,x)).collect();
                    w.route_dense(usize::MAX,2*w.n,records,input.len);usize::MAX
                }else{input.id};
                let twiddles=code.filter(|&(i,_)|i==which).map(|(_,base)|{
                    let code=RowCode::compact(base,2);twiddle_range(&code,input.len.ilog2() as usize,lo,hi-lo,input.len/2)
                });
                let fold=|j:usize,u:L,v:L|{if let Some(t)=&twiddles {let slope=u+v;let a=u+crate::field::mul_b(slope,t[j]);a+(slope+a)*r}else{u+(u+v)*r}};
                let values=if temporary||released.contains(&input.id){
                    let mut a=w.remove(id).unwrap();let half=hi-lo;
                    for j in 0..half {a[j]=fold(j,a[2*j],a[2*j+1]);}a.truncate(half);a
                }else{w.arrays[&id].chunks_exact(2).enumerate().map(|(j,a)|fold(j,a[0],a[1])).collect()};
                w.put(output.id,values);
            }
            for id in &released {w.remove(*id);}vec![]
        });out
    }
    pub fn reindex(&mut self,input:Vector,len:usize,f:impl Fn(usize,L,&mut Vec<(usize,L)>)+Send+Sync+'static,add:bool)->Vector {
        let out=Vector{id:self.id(),len};self.run_effect(move|w| {
            let (lo,_)=bounds(input.len,w.n,w.rank);let mut records=vec![];
            for (j,&x) in w.arrays[&input.id].iter().enumerate() {f(lo+j,x,&mut records);}
            w.route(out.id,len,records,add);vec![]
        });out
    }
    pub fn reindex_dense(&mut self,input:Vector,len:usize,f:impl Fn(usize,L,&mut Vec<(usize,L)>)+Send+Sync+'static)->Vector {
        let out=Vector{id:self.id(),len};self.run_effect(move|w| {
            let(lo,_)=bounds(input.len,w.n,w.rank);let mut records=vec![];
            for(j,&x)in w.arrays[&input.id].iter().enumerate(){f(lo+j,x,&mut records);}
            w.route_dense(out.id,len,records,len);vec![]
        });out
    }
    pub fn slice(&mut self,input:Vector,offset:usize,len:usize)->Vector {
        assert!(offset+len<=input.len);self.reindex_dense(input,len,move|j,x,out|if (offset..offset+len).contains(&j){out.push((j-offset,x));})
    }
    pub fn concat(&mut self,inputs:&[Vector])->Vector {
        let mut offset=0;let parts:Vec<_>=inputs.iter().map(|&v|{let p=(v,offset);offset+=v.len;p}).collect();
        let out=Vector{id:self.id(),len:offset};self.run_effect(move|w| {
            let mut records=vec![];for &(input,offset) in &parts {
                let (lo,_)=bounds(input.len,w.n,w.rank);
                for (j,&x) in w.arrays[&input.id].iter().enumerate() {records.push((offset+lo+j,x));}
            }
            w.route_dense(out.id,out.len,records,out.len);vec![]
        });out
    }
    pub fn pairs(&mut self,input:Vector,f:impl Fn(usize,L,L)->L+Send+Sync+'static)->Vector {
        assert_eq!(input.len%2,0);let len=input.len/2;
        let out=Vector{id:self.id(),len};
        self.run_effect(move|w| {
            let (lo,hi)=bounds(len,w.n,w.rank);
            if input.len>=2*w.n {
                let a=&w.arrays[&input.id];
                let values=(0..a.len()/2).map(|j|f(lo+j,a[2*j],a[2*j+1])).collect();
                w.put(out.id,values);
            }else {
                let (src_lo,_)=bounds(input.len,w.n,w.rank);
                let records=w.arrays[&input.id].iter().enumerate().map(|(j,&x)|(src_lo+j,x)).collect();
                let temp=usize::MAX;w.route_dense(temp,2*w.n,records,input.len);
                let a=w.remove(temp).unwrap();
                w.put(out.id,if lo<hi {vec![f(lo,a[0],a[1])]}else{vec![]});
            }
            vec![]
        });out
    }
    #[cfg(test)]
    pub fn fold(&mut self,input:Vector,r:L)->Vector {self.pairs(input,move|_,a,b|a+(a+b)*r)}
    pub fn pair_reduce(&mut self,inputs:&[Vector],outputs:usize,f:impl Fn(&[[L;2]],&mut[L])+Send+Sync+'static)->Vec<L> {
        let len=inputs[0].len;assert!(inputs.iter().all(|v|v.len==len));assert_eq!(len%2,0);
        let ids:Vec<_>=inputs.iter().map(|v|v.id).collect();let staging:Vec<_>=inputs.iter().map(|_|self.id()).collect();
        let result=self.run(move|w| {
            if len<2*w.n {for (&src,&dst) in ids.iter().zip(&staging) {
                let(lo,_)=bounds(len,w.n,w.rank);let records=w.arrays[&src].iter().enumerate().map(|(j,&x)|(lo+j,x)).collect();
                w.route_dense(dst,2*w.n,records,len);
            }}
            let use_ids=if len<2*w.n {&staging}else{&ids};let count=if len<2*w.n {usize::from(w.rank<len/2)}else{w.arrays[&ids[0]].len()/2};
            if count==0 {for id in &staging {w.remove(*id);}return vec![];}
            let mut out=vec![L::ZERO;outputs];let mut pair=vec![[L::ZERO;2];ids.len()];
            let arrays:Vec<_>=use_ids.iter().map(|id|&w.arrays[id]).collect();
            for j in 0..count {for(v,a)in pair.iter_mut().zip(&arrays){*v=[a[2*j],a[2*j+1]];}f(&pair,&mut out);}
            for id in &staging {w.remove(*id);}out
        });
        let mut out=vec![L::ZERO;outputs];for row in result {for(x,y)in out.iter_mut().zip(row){*x+=y;}}out
    }
    pub fn product_round(&mut self,inputs:&[Vector])->Vec<L> {
        let degree=inputs.len();let points:Vec<_>=(0..=degree).map(crate::product_tree::point).collect();
        self.pair_reduce(inputs,degree+1,move|pairs,out|for(y,&x)in out.iter_mut().zip(&points){*y+=pairs.iter().map(|[a,b]|*a+x*(*a+*b)).product::<L>();})
    }
    pub fn small(&mut self,input:Vector)->Vec<L> {
        assert!(input.len<=self.n.max(8),"no whole-array reads in the controller");
        let parts=self.run(move|w|w.arrays[&input.id].clone());parts.into_iter().flatten().collect()
    }
    #[cfg(test)]
    pub fn get(&mut self,input:Vector,indices:&[usize])->Vec<L> {self.get_many(&indices.iter().map(|&i|(input,i)).collect::<Vec<_>>())}
    pub fn get_many(&mut self,requests:&[(Vector,usize)])->Vec<L> {
        let mut unique=Vec::new();let mut seen=HashMap::new();let mut positions=Vec::with_capacity(requests.len());
        for &(v,index)in requests {assert!(index<v.len);let next=unique.len();
            let slot=*seen.entry((v.id,index)).or_insert_with(||{unique.push((v,index));next});positions.push(slot);
        }
        let mut values=vec![L::ZERO;unique.len()];
        let mut owners=vec![vec![];self.n];
        for(j,&(v,index))in unique.iter().enumerate(){let rank=owner(v.len,self.n,index);let(lo,_)=bounds(v.len,self.n,rank);
            owners[rank].push((j,v.id,index-lo));
        }
        // Independent owners respond concurrently; retain the 4096-cell per-owner cap.
        let batches=owners.iter().map(|v|v.len().div_ceil(4096)).max().unwrap_or(0);
        for batch in 0..batches {let mut packets=vec![vec![];self.n];let mut slots=vec![vec![];self.n];
            for(rank,requests)in owners.iter().enumerate(){for &(j,id,index)in requests.iter().skip(batch*4096).take(4096){
                packets[rank].extend((id as u64).to_le_bytes());packets[rank].extend((index as u64).to_le_bytes());slots[rank].push(j);
            }}
            let parts=self.dispatch_selected(packets,Arc::new(|w,packet|packet.chunks_exact(16).map(|p|{
                let id=u64::from_le_bytes(p[..8].try_into().unwrap()) as usize;
                let index=u64::from_le_bytes(p[8..].try_into().unwrap()) as usize;w.arrays[&id][index]
            }).collect()),true,true);
            for(rank,part)in parts.into_iter().enumerate(){assert_eq!(part.len(),slots[rank].len());for(&i,value)in slots[rank].iter().zip(part){values[i]=value;}}
        }positions.into_iter().map(|i|values[i]).collect()
    }
    pub fn evaluate_batch(&mut self,inputs:&[Vector],point:&[L])->Vec<L> {
        let len=1<<point.len();assert!(inputs.iter().all(|v|v.len==len));let ids:Vec<_>=inputs.iter().map(|v|v.id).collect();let p=point.to_vec();let count=ids.len();
        let partials=self.run(move|w|{let(lo,hi)=bounds(len,w.n,w.rank);let weights=equality_range(&p,lo,hi-lo);
            ids.iter().map(|id|w.arrays[id].iter().zip(&weights).map(|(&x,&y)|x*y).sum()).collect()});
        let mut out=vec![L::ZERO;count];for row in partials {for(x,y)in out.iter_mut().zip(row){*x+=y;}}out
    }
    pub fn release(&mut self,inputs:&[Vector]) {let ids:Vec<_>=inputs.iter().map(|v|v.id).collect();self.run_effect(move|w|{for id in &ids {w.remove(*id);}vec![]});}
    pub fn encode(&mut self,input:Vector)->Vector {
        let bits=input.len.ilog2();let len=4*input.len;
        let mut cw=self.reindex_dense(input,len,move|j,x,out|{let rev=j.reverse_bits()>>(usize::BITS-bits);for q in 0..4 {out.push((4*rev+q,x));}});
        let local=len/self.n;
        let local_stages=if local>=4 {local.ilog2()-2}else{0};
        for stage in 1..=bits {
            if local>=self.n&&local>=4&&stage==local_stages+1 {
                // Rotate ownership once. Each owner then holds complete N-vectors
                // for a balanced range of low coordinates q. The remaining
                // butterflies move party bits into the output's low bits, so
                // this transposed layout is already the final codeword layout.
                let n=self.n;let previous=cw;
                let transposed=self.reindex_dense(previous,len,move|j,x,out|out.push(((j%local)*n+j/local,x)));
                self.release(&[previous]);let result=Vector{id:self.id(),len};
                self.run_effect(move|w| {
                    let code=RowCode::compact(bits as usize,2);let mut values=w.remove(transposed.id).unwrap();
                    let (lo,_)=bounds(len,w.n,w.rank);let q_start=lo/w.n;let groups=values.len()/w.n;
                    for step in 1..=w.n.ilog2() {
                        let block=1usize<<step;let half=block/2;
                        let twiddles=twiddle_range(&code,(local_stages+step+2)as usize,q_start*half,groups*half,local*half);
                        let mut next=vec![L::ZERO;values.len()];
                        for q in 0..groups {for base in (0..w.n).step_by(block) {for i in 0..half {
                            let offset=q*w.n+base;let a=values[offset+i];let b=values[offset+half+i];
                            let u=a+crate::field::mul_b(b,twiddles[q*half+i]);next[offset+2*i]=u;next[offset+2*i+1]=u+b;
                        }}}
                        values=next;
                    }
                    w.put(result.id,values);vec![]
                });return result;
            }
            let block=1usize<<(stage+2);let half=block/2;
            let paired=self.reindex_dense(cw,len,move|j,x,out|{let base=j/block*block;let p=j%block;out.push((base+2*(p%half)+usize::from(p>=half),x));});
            let previous=cw;cw=Vector{id:self.id(),len};let id=cw.id;
            self.run_effect(move|w| {
                let code=RowCode::compact(bits as usize,2);
                let mut output=vec![];
                if len>=2*w.n {
                    let (lo,_)=bounds(len,w.n,w.rank);let src=&w.arrays[&paired.id];
                    let ts=twiddle_range(&code,stage as usize+2,(lo/2)%half,src.len()/2,half);
                    for(q,t)in ts.into_iter().enumerate(){let a=src[2*q];let b=src[2*q+1];let u=a+crate::field::mul_b(b,t);output.extend([u,u+b]);}
                    w.put(id,output);
                }else{
                    let(lo,_)=bounds(len,w.n,w.rank);let records=w.arrays[&paired.id].iter().enumerate().map(|(j,&x)|(lo+j,x)).collect();
                    let temp=usize::MAX;w.route_dense(temp,2*w.n,records,len);let src=w.remove(temp).unwrap();
                    let mut records=vec![];
                    if w.rank<len/2 {let a=src[0];let b=src[1];let t=code.twiddle(stage as usize+2,w.rank%half);let u=a+crate::field::mul_b(b,t);records.extend([(2*w.rank,u),(2*w.rank+1,u+b)]);}
                    w.route_dense(id,len,records,len);
                }
                vec![]
            });
            self.release(&[paired,previous]);
        }
        cw
    }
    pub fn snapshot(&mut self)->Vec<Stats> {
        self.run(|w|vec![label(w.stats.sent_bytes as usize),label(w.stats.received_bytes as usize),label(w.stats.peer_messages as usize),label(w.stats.resident_array_peak_cells),crate::field::from_words([w.stats.task_wall_seconds.to_bits() as u128,0])]).into_iter().map(|v|Stats{sent_bytes:integer(v[0]) as u64,received_bytes:integer(v[1]) as u64,peer_messages:integer(v[2]) as u64,resident_array_peak_cells:integer(v[3]),task_wall_seconds:f64::from_bits(integer(v[4]) as u64)}).collect()
    }
}
impl Drop for Runtime {fn drop(&mut self){for s in &self.senders {let _=s.send(Command::Stop);}for j in self.joins.drain(..){let _=j.join();}}}

#[cfg(test)]mod tests {
    use super::*;
    #[test]fn combined_kernels_preserve_owner_shapes() {
        for n in [8,16,64,128] {for r in [L::ZERO,L::ONE,label(5)] {
            let mut rt=Runtime::new(n);let values=(0..16).map(|i|label(i+1)).collect::<Vec<_>>();
            let code=RowCode::compact(4,2);let encoded=code.encode(&values);
            let f=rt.load(values.clone());let w=rt.load(values.clone());let cw=rt.load(encoded.clone());
            let out=rt.fold_public(f,w,cw,r,4,&[w]);
            let expected=crate::code::fold_coeffs(&values,r);
            assert_eq!(rt.get(out[0],&(0..8).collect::<Vec<_>>()),expected);
            assert_eq!(rt.get(out[1],&(0..8).collect::<Vec<_>>()),expected);
            assert_eq!(rt.get(out[2],&(0..32).collect::<Vec<_>>()),code.fold(&encoded,r));
            let shapes=rt.run(move|owner|out.iter().map(|v|label(owner.arrays[&v.id].len())).collect());
            for(rank,row)in shapes.iter().enumerate(){for(v,&actual)in out.iter().zip(row){let(lo,hi)=bounds(v.len,n,rank);assert_eq!(integer(actual),hi-lo,"N={n},rank={rank}");}}
            let mut folded=out[0];let mut reference=expected;
            while folded.len>1 {let old=folded;folded=rt.fold_many(&[old],r,&[old])[0];reference=crate::code::fold_coeffs(&reference,r);}
            assert_eq!(rt.small(folded),reference);
        }}
    }
    #[test]fn owner_equality_ranges_and_split_lookups_match_literal() {
        for bits in 0..=10 {let point=(0..bits).map(|j|[L::ZERO,L::ONE,label(7)][j%3]).collect::<Vec<_>>();
            let lookup=EqualityLookup::new(&point);let size=1<<bits;
            for start in (0..size).step_by((size/9).max(1)){let count=(size-start).min(37);
                assert_eq!(equality_range(&point,start,count),(start..start+count).map(|i|chi(i,&point)).collect::<Vec<_>>());
            }
            for i in 0..2*size+3 {assert_eq!(lookup.value(i),chi(i,&point));}
        }
    }
    #[test]fn batched_queries_cross_reply_limit_and_restore_duplicates() {
        let mut rt=Runtime::new(8);let input=rt.generate(65536,label);let other=rt.generate(16,|i|label(i+9));
        let requests=(0..70000).rev().map(|i|(input,(13*i)%65536)).chain((0..16).map(|i|(other,i))).collect::<Vec<_>>();
        let expected=(0..70000).rev().map(|i|label((13*i)%65536)).chain((0..16).map(|i|label(i+9))).collect::<Vec<_>>();
        assert_eq!(rt.get_many(&requests),expected);
    }
    #[test]fn repeated_queries_contact_only_the_target_owner() {
        let mut rt=Runtime::new(8);let input=rt.generate(64,label);rt.flush();
        let before=rt.command_count();
        assert_eq!(rt.get(input,&vec![13;1000]),vec![label(13);1000]);
        assert_eq!(rt.command_count()-before,1,"duplicate queries should use one request to one owner");
    }
    #[test]fn effect_commands_preserve_fifo_routes_and_send_no_replies() {
        if std::env::var_os("GENERAL_EFFECT_TRACE_TEST_CHILD").is_none() {
            let status=std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact","general::distributed::tests::effect_commands_preserve_fifo_routes_and_send_no_replies","--nocapture"])
                .env("GENERAL_EFFECT_TRACE_TEST_CHILD","1").status().unwrap();
            assert!(status.success());return;
        }
        for n in [8,16,64,128] {
            let mut rt=Runtime::new(n);
            let gate=Arc::new(std::sync::Barrier::new(n+1));let release=gate.clone();let(s,r)=mpsc::channel();
            let observer=thread::spawn(move||{let returned=r.recv_timeout(std::time::Duration::from_secs(5)).is_ok();release.wait();returned});
            rt.run_effect(move|_|{gate.wait();vec![]});let _=s.send(());assert!(observer.join().unwrap(),"effect waited for kernel completion");
            let input=rt.generate(16,label);
            let doubled=rt.map(&[input],|_,v|v[0]+v[0]);
            let joined=rt.concat(&[input,doubled]);let selected=rt.slice(joined,0,16);
            let rotated=rt.reindex_dense(selected,16,|i,v,out|out.push(((i+5)%16,v)));
            let encoded=rt.encode(rotated);let expected:Vec<_>=(0..16).map(|j|label((j+11)%16)).collect();
            assert_eq!(rt.get(encoded,&(0..64).collect::<Vec<_>>()),RowCode::new(4,2).encode(&expected));
            let mut folded=rotated;let mut reference=expected;
            while folded.len>1 {folded=rt.fold(folded,label(5));reference=crate::code::fold_coeffs(&reference,label(5));}
            assert_eq!(rt.small(folded),reference);rt.release(&[input,doubled,joined,selected,encoded]);rt.flush();
            assert!(rt.run(|w|vec![label(w.pending.len())]).iter().all(|v|v[0]==L::ZERO));
            let path=std::env::temp_dir().join(format!("general-effect-trace-{}-{n}",std::process::id()));let _=std::fs::remove_dir_all(&path);
            crate::execution_trace::start(n);
            let id=rt.id();rt.run_effect(move|w|{w.put(id,vec![label(w.rank)]);vec![]});
            rt.run_packets_effect((0..n).map(|i|(i as u64).to_le_bytes().to_vec()).collect(),move|w,p|{assert_eq!(integer(w.arrays[&id][0]),u64::from_le_bytes(p.try_into().unwrap()) as usize);w.remove(id);vec![]});
            rt.flush();let trace=crate::execution_trace::finish(&path).unwrap();
            assert_eq!(&trace.sent_bytes[..n],vec![16;n]);assert_eq!(trace.sent_bytes[n],n as u64*(24+32+24));
            std::fs::remove_dir_all(path).unwrap();
        }
    }
    #[test]fn one_transpose_encoding_matches_reference_across_boundary() {
        use crate::field::Random;use rand::{SeedableRng,rngs::StdRng};
        let mut rng=StdRng::seed_from_u64(913);
        for n in [8usize,16,64,128] {for bits in [4,2*n.ilog2()as usize-3,2*n.ilog2()as usize-2,14] {
            let values=(0..1usize<<bits).map(|_|L::random(&mut rng)).collect::<Vec<_>>();
            let mut rt=Runtime::new(n);let input=rt.load(values.clone());rt.seal();
            let encoded=rt.encode(input);let expected=RowCode::new(bits,2).encode(&values);
            assert_eq!(rt.get(encoded,&(0..expected.len()).collect::<Vec<_>>()),expected,"N={n},bits={bits}");
        }}
    }
    #[test]fn sharded_encoding_and_folds_match_reference() {
        for n in [8,16,64,128] {let mut rt=Runtime::new(n);let v:Vec<_>=(0..16).map(label).collect();let input=rt.load(v.clone());rt.seal();
            let encoded=rt.encode(input);let code=RowCode::new(4,2);let expected=code.encode(&v);
            for q in (0..64).step_by(32) {let actual=rt.get(encoded,&(q..q+32).collect::<Vec<_>>());for (i,(&a,&b)) in actual.iter().zip(&expected[q..q+32]).enumerate(){assert_eq!(a,b,"N={n}, coordinate {}",q+i);}}
            let mut a=input;let mut old=v;
            while a.len>1 {a=rt.fold(a,label(5));old=crate::code::fold_coeffs(&old,label(5));}
            assert_eq!(rt.small(a),old);let stats=rt.snapshot();assert!(stats.iter().map(|s|s.sent_bytes).sum::<u64>()>0);
            assert_eq!(stats.iter().map(|s|s.sent_bytes).sum::<u64>(),stats.iter().map(|s|s.received_bytes).sum::<u64>());
        }
    }
}
