//! Optional bounded worker pool. Collection order is always the logical party/index order.
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
static ACTIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static WORKERS: AtomicU64 = AtomicU64::new(0);
static PARTIES: AtomicU64 = AtomicU64::new(0);

pub fn map<R: Send>(n: usize, f: impl Fn(usize) -> R + Sync + Send) -> Vec<R> {
    #[cfg(feature = "parallel")]
    { (0..n).into_par_iter().map(f).collect() }
    #[cfg(not(feature = "parallel"))]
    { (0..n).map(f).collect() }
}
pub fn map_mut<T: Send, R: Send>(a: &mut [T], f: impl Fn(usize, &mut T) -> R + Sync + Send) -> Vec<R> {
    #[cfg(feature = "parallel")]
    { a.par_iter_mut().enumerate().with_max_len(1).map(|(i,x)| f(i,x)).collect() }
    #[cfg(not(feature = "parallel"))]
    { a.iter_mut().enumerate().map(|(i,x)| f(i,x)).collect() }
}
pub fn parties<T: Send, R: Send>(a: &mut [T], f: impl Fn(usize, &mut T) -> R + Sync + Send) -> Vec<R> {
    map_mut(a, |i,x| {
        if i < 64 { PARTIES.fetch_or(1 << i, Relaxed); }
        #[cfg(feature = "parallel")]
        if let Some(w) = rayon::current_thread_index() { if w < 64 { WORKERS.fetch_or(1 << w, Relaxed); } }
        let active = ACTIVE.fetch_add(1, Relaxed) + 1;
        PEAK.fetch_max(active, Relaxed);
        let result = f(i,x);
        ACTIVE.fetch_sub(1, Relaxed);
        result
    })
}
pub fn reset_stats() { PEAK.store(0,Relaxed); WORKERS.store(0,Relaxed); PARTIES.store(0,Relaxed); }
pub fn stats() -> (usize,u32,u32) { (PEAK.load(Relaxed), WORKERS.load(Relaxed).count_ones(), PARTIES.load(Relaxed).count_ones()) }

#[cfg(all(test,feature="parallel"))]
mod tests {
    #[test] fn thirty_two_parties_reach_same_barrier() {
        let pool=rayon::ThreadPoolBuilder::new().num_threads(32).build().unwrap();
        let barrier=std::sync::Barrier::new(32);let mut parties=vec![0;32];
        pool.install(||super::parties(&mut parties, |i,p|{barrier.wait();*p=i;}));
        assert_eq!(parties,(0..32).collect::<Vec<_>>());
    }
}
