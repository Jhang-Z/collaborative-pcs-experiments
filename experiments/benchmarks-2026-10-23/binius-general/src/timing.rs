//! Exclusive attribution of existing native spans; no protocol hooks or changes.
use std::{collections::HashMap, sync::{Arc, Mutex}, time::Instant};
use tracing::{span::{Attributes, Id, Record}, Event, Metadata, Subscriber};

pub const NAMES: [&str; 7] = ["witness_preparation", "witness_commitment", "bitand_check",
    "shift_reduction", "inner_pcs_opening", "zk_wrapper", "other_online"];
fn phase(name: &str) -> Option<usize> {
    match name {
        "Prepare witness" => Some(0), "Commit witness" => Some(1),
        "[phase] BitAnd check" => Some(2), "[phase] Shift Reduction" => Some(3),
        "[phase] PCS Opening" => Some(4), "ZK Wrapper" => Some(5), _ => None,
    }
}
fn cpu() -> f64 {
    let mut ts = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // Include a possible Rayon worker, even with its pool size fixed at one.
    assert_eq!(unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut ts) }, 0);
    ts.tv_sec as f64 + ts.tv_nsec as f64 * 1e-9
}
pub struct State {
    stack: Vec<(Id, usize)>, spans: HashMap<u64,(usize,usize)>, next: u64, last: Instant, last_cpu: f64,
    pub wall: [f64; 7], pub cpu: [f64; 7],
}
impl State {
    pub fn new() -> Self { Self { stack: vec![], spans: HashMap::new(), next: 0, last: Instant::now(), last_cpu: cpu(), wall: [0.; 7], cpu: [0.; 7] } }
    pub fn tick(&mut self) {
        let now = Instant::now(); let c = cpu();
        let p = self.stack.last().map_or(6, |x| x.1);
        self.wall[p] += now.duration_since(self.last).as_secs_f64();
        self.cpu[p] += c - self.last_cpu;
        self.last = now; self.last_cpu = c;
    }
    pub fn finish(&mut self) { self.tick(); assert!(self.stack.is_empty()); }
}
#[derive(Clone)]
pub struct Timings(pub Arc<Mutex<State>>);
impl Subscriber for Timings {
    fn enabled(&self, meta: &Metadata<'_>) -> bool { phase(meta.name()).is_some() }
    fn new_span(&self, attrs: &Attributes<'_>) -> Id {
        let mut s = self.0.lock().unwrap(); s.next += 1; let id = s.next;
        s.spans.insert(id, (phase(attrs.metadata().name()).unwrap(),1)); Id::from_u64(id)
    }
    fn record(&self, _: &Id, _: &Record<'_>) {}
    fn record_follows_from(&self, _: &Id, _: &Id) {}
    fn event(&self, _: &Event<'_>) {}
    fn enter(&self, id: &Id) {
        let mut s = self.0.lock().unwrap(); let p = s.spans[&id.into_u64()].0; s.tick();
        // Keep nested wrapper operations out of the inner-IOP stage buckets.
        let p = if s.stack.iter().any(|x| x.1 == 5) { 5 } else { p };
        s.stack.push((id.clone(), p));
    }
    fn exit(&self, id: &Id) {
        let mut s = self.0.lock().unwrap(); s.tick();
        assert_eq!(&s.stack.pop().unwrap().0, id);
    }
    fn clone_span(&self, id: &Id) -> Id {
        self.0.lock().unwrap().spans.get_mut(&id.into_u64()).unwrap().1 += 1; id.clone()
    }
    fn try_close(&self, id: Id) -> bool {
        let mut s = self.0.lock().unwrap(); let refs = &mut s.spans.get_mut(&id.into_u64()).unwrap().1;
        *refs -= 1; if *refs == 0 { s.spans.remove(&id.into_u64()); true } else { false }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn nested_wrapper_is_counted_once() {
        let state = Arc::new(Mutex::new(State::new()));
        tracing::subscriber::with_default(Timings(state.clone()), || {
            let _ignored = tracing::info_span!("unselected").entered();
            { let _w = tracing::debug_span!("Prepare witness").entered(); }
            { let _z = tracing::debug_span!("ZK Wrapper").entered();
              let _p = tracing::info_span!("[phase] PCS Opening").entered(); }
        });
        let mut s = state.lock().unwrap(); s.finish();
        assert!(s.wall[0] > 0. && s.wall[5] > 0.);
        assert_eq!(s.wall[4], 0.);
        assert!(s.spans.is_empty());
    }
}
