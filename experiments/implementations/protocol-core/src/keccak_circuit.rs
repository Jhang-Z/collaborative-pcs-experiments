//! Keccak-f[1600], 24 rounds. Lanes and bytes are little endian, index x+5*y.
//! Linear theta/rho/pi terms live directly in sparse R1CS rows. Each chi bit
//! contributes one multiplication equation; no extra XOR-gate witness table.
use crate::spartan::Base;

const RC: [u64; 24] = [
    0x0000000000000001,0x0000000000008082,0x800000000000808a,0x8000000080008000,
    0x000000000000808b,0x0000000080000001,0x8000000080008081,0x8000000000008009,
    0x000000000000008a,0x0000000000000088,0x0000000080008009,0x000000008000000a,
    0x000000008000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
    0x8000000000008002,0x8000000000000080,0x000000000000800a,0x800000008000000a,
    0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008,
];
const ROT: [usize; 25] = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14];
const PRIVATE: usize = 25 * 1600;

pub struct KeccakCircuit {
    pub base: Base,
    pub public_bits: usize,
    pub constraint_len: usize,
}
fn parity(mut indices: Vec<usize>) -> Vec<usize> {
    indices.sort_unstable();
    let mut out = Vec::with_capacity(indices.len());
    for i in indices {
        if out.last() == Some(&i) { out.pop(); } else { out.push(i); }
    }
    out
}
impl KeccakCircuit {
    /// Public output is either the first four lanes or the full state. Both
    /// shapes execute every round; disclosure is part of the relation identity.
    pub fn new(public_bits: usize) -> Self {
        assert!(matches!(public_bits, 256 | 1600));
        let mut a = Vec::new(); let mut b = Vec::new(); let mut c = Vec::new();
        for (round, &rc) in RC.iter().enumerate() {
            let start = round * 1600;
            let mut moved = vec![Vec::new(); 1600];
            for y in 0..5 { for x in 0..5 { for bit in 0..64 {
                let mut linear = vec![start + (x+5*y)*64 + bit];
                for yy in 0..5 {
                    linear.push(start + ((x+4)%5+5*yy)*64 + bit);
                    linear.push(start + ((x+1)%5+5*yy)*64 + (bit+63)%64);
                }
                let target = (y+5*((2*x+3*y)%5))*64 + (bit+ROT[x+5*y])%64;
                moved[target] = parity(linear);
            } } }
            for y in 0..5 { for x in 0..5 { for bit in 0..64 {
                let mut left = moved[((x+1)%5+5*y)*64+bit].clone();
                left.push(PRIVATE); // NOT in F2
                let right = moved[((x+2)%5+5*y)*64+bit].clone();
                let mut output = moved[(x+5*y)*64+bit].clone();
                output.push(start+1600+(x+5*y)*64+bit);
                if x==0 && y==0 && (rc>>bit)&1 != 0 { output.push(PRIVATE); }
                a.push(parity(left)); b.push(right); c.push(parity(output));
            } } }
        }
        for bit in 0..public_bits {
            a.push(vec![24*1600+bit,PRIVATE+1+bit]);
            b.push(vec![PRIVATE]); c.push(vec![]);
        }
        let constraint_len=a.len();
        let m=constraint_len.next_power_of_two(); let n=(PRIVATE+1+public_bits).next_power_of_two();
        a.resize(m,vec![]); b.resize(m,vec![]); c.resize(m,vec![]);
        Self { base:Base{log_m0:m.ilog2() as usize,log_n0:n.ilog2() as usize,a,b,c},public_bits,constraint_len }
    }
    pub fn private_len(&self) -> usize { PRIVATE }
    pub fn witness(&self, input: &[u8;200]) -> (Vec<bool>,[Vec<bool>;3],Vec<u8>) {
        let mut z=vec![false;self.base.n0()];
        let mut state:[u64;25]=std::array::from_fn(|i|u64::from_le_bytes(input[i*8..i*8+8].try_into().unwrap()));
        for round in 0..=24 {
            for (lane,&v) in state.iter().enumerate() { for bit in 0..64 {z[round*1600+lane*64+bit]=(v>>bit)&1!=0;} }
            if round<24 { permutation_round(&mut state,RC[round]); }
        }
        let output:Vec<u8>=state.iter().flat_map(|v|v.to_le_bytes()).take(self.public_bits/8).collect();
        z[PRIVATE]=true;
        for bit in 0..self.public_bits {z[PRIVATE+1+bit]=output[bit/8]>>(bit%8)&1!=0;}
        let rows=std::array::from_fn(|j|[&self.base.a,&self.base.b,&self.base.c][j].iter()
            .map(|row|row.iter().fold(false,|s,&i|s^z[i])).collect());
        z[PRIVATE..].fill(false);
        (z,rows,output)
    }
}
fn permutation_round(s:&mut [u64;25],rc:u64) {
    let c:[u64;5]=std::array::from_fn(|x|(0..5).fold(0,|v,y|v^s[x+5*y]));
    let d:[u64;5]=std::array::from_fn(|x|c[(x+4)%5]^c[(x+1)%5].rotate_left(1));
    let mut b=[0u64;25];
    for y in 0..5 {for x in 0..5 {b[y+5*((2*x+3*y)%5)]=(s[x+5*y]^d[x]).rotate_left(ROT[x+5*y] as u32);}}
    for y in 0..5 {for x in 0..5 {s[x+5*y]=b[x+5*y]^(!b[(x+1)%5+5*y]&b[(x+2)%5+5*y]);}}
    s[0]^=rc;
}
/// Private round states, input followed by the24successive round outputs.
pub fn trace(input:&[u8;200])->Vec<bool> {
 let mut z=vec![false;PRIVATE];
 let mut state:[u64;25]=std::array::from_fn(|i|u64::from_le_bytes(input[i*8..i*8+8].try_into().unwrap()));
 for round in 0..=24 {
  for(lane,&v)in state.iter().enumerate(){for bit in 0..64{z[round*1600+lane*64+bit]=(v>>bit)&1!=0;}}
  if round<24 {permutation_round(&mut state,RC[round]);}
 }
 z
}
/// Deterministic oracle also used by the adapter. Tests below independently
/// check a known zero-state vector; the experiment runner uses a separate
/// Python lane-cycle implementation and never treats this helper as independent.
pub fn reference(input:&[u8;200]) -> [u8;200] {
    let mut s=std::array::from_fn(|i|u64::from_le_bytes(input[i*8..i*8+8].try_into().unwrap()));
    for rc in RC {permutation_round(&mut s,rc);}
    std::array::from_fn(|i|s[i/8].to_le_bytes()[i%8])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known_zero_state_and_both_public_relations() {
        let known=[0xf1258f7940e1dde7u64,0x84d5ccf933c0478a,0xd598261ea65aa9ee,0xbd1547306f80494d];
        let expected:Vec<_>=known.iter().flat_map(|v|v.to_le_bytes()).collect();
        assert_eq!(&reference(&[0;200])[..32],expected);
        for bits in [256,1600] {
            let c=KeccakCircuit::new(bits);
            for input in [[0u8;200],[255u8;200],std::array::from_fn(|i|i as u8)] {
                let (z,rows,out)=c.witness(&input);
                assert_eq!(out,reference(&input)[..bits/8]);
                assert!(rows[0].iter().zip(&rows[1]).zip(&rows[2]).all(|((&a,&b),&c)|a&b==c));
                assert!(z[PRIVATE..].iter().all(|&v|!v));
                let mut bad=z;bad[PRIVATE]=true;
                for bit in 0..bits {bad[PRIVATE+1+bit]=out[bit/8]>>(bit%8)&1!=0;}
                bad[PRIVATE+1]^=true;
                assert!(c.base.a.iter().zip(&c.base.b).zip(&c.base.c).any(|((a,b),c)| {
                    let eval=|r:&Vec<usize>|r.iter().fold(false,|v,&i|v^bad[i]);eval(a)&eval(b)!=eval(c)
                }));
            }
            assert_eq!(c.base.n0(),65536);assert_eq!(c.base.m0(),65536);
            assert_eq!(c.constraint_len,38400+bits);
        }
    }
}
