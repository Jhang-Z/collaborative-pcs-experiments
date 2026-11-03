//! Six fixed public-input columns, authenticated by one existing batch PCS opening.
use crate::{field::{Field,L},fs::Transcript,public_pcs};
use binius_hash::Blake3HashSuite as H;
use super::{distributed::{Runtime,Vector},public::{self,Committed}};

pub struct Index {pub key:public_pcs::Key,committed:Committed,columns:[Vector;6]}
pub struct Proof {pub values:[L;6],pub opening:public_pcs::Proof}
impl Proof {
    pub fn encode(&self)->Vec<u8>{let mut b=bytemuck::cast_slice(&self.values).to_vec();b.extend(self.opening.encode());b}
}
impl Index {
    pub fn new(rt:&mut Runtime,row_bits:usize,entries:&[(usize,usize,usize)],queries:usize)->Self {
        assert!((1..40).contains(&row_bits)&&queries>0);
        let rows=1<<row_bits;let mut values=vec![L::ZERO;8*rows];
        for &(matrix,row,column) in entries {
            assert!(matrix<3&&row<rows&&column<2);
            // Repeated binary entries cancel, as in the original sparse index.
            values[(2*matrix+column)*rows+row]+=L::ONE;
        }
        let values=rt.load(values);let committed=public::commit(rt,values,queries);
        let columns=std::array::from_fn(|j|rt.slice(values,j*rows,rows));
        Self{key:committed.key.clone(),committed,columns}
    }
}
fn points(row:&[L])->Vec<Vec<L>> {
    (0..6).map(|j|{let mut p=row.to_vec();p.extend((0..3).map(|b|if j&(1<<b)==0{L::ZERO}else{L::ONE}));p}).collect()
}
fn contract(values:&[L;6],rho:[L;3],input:&[L;2])->L {
    (0..3).map(|a|rho[a]*(values[2*a]*input[0]+values[2*a+1]*input[1])).sum()
}
fn begin(key:&public_pcs::Key,row:&[L],rho:[L;3],input:&[L;2],value:L,tr:&mut Transcript<'_,H>) {
    tr.absorb(b"six public input columns v1",&key.binding());
    tr.absorb(b"public column row",bytemuck::cast_slice(row));
    tr.absorb(b"public column mix/input/value",bytemuck::cast_slice(&[rho[0],rho[1],rho[2],input[0],input[1],value]));
}
pub fn prove(rt:&mut Runtime,index:&Index,row:&[L],rho:[L;3],input:&[L;2],tr:&mut Transcript<'_,H>)->(L,Proof) {
    assert_eq!(index.key.log,row.len()+3);
    let values=rt.evaluate_batch(&index.columns,row).try_into().unwrap();let value=contract(&values,rho,input);
    begin(&index.key,row,rho,input,value,tr);
    let opening=public::open_batch(rt,&index.committed,&points(row),&values,tr);
    (value,Proof{values,opening})
}
pub fn verify(key:&public_pcs::Key,row:&[L],rho:[L;3],input:&[L;2],value:L,p:&Proof,tr:&mut Transcript<'_,H>)->Result<(),String> {
    if row.is_empty()||row.len()>=40||key.log!=row.len()+3||key.queries==0{return Err("public column key/row shape".into());}
    if contract(&p.values,rho,input)!=value{return Err("public column contraction".into());}
    begin(key,row,rho,input,value,tr);
    public_pcs::verify_batch(key,&points(row),&p.values,&p.opening,tr)
}

#[cfg(test)]mod tests {
    use super::*;use crate::{field::{eq_expand,Random},merkle::Hasher};
    use rand::{SeedableRng,rngs::StdRng};
    #[test]fn six_columns_match_literal_matrix_and_reject_forged_values() {
        let h=Hasher::<H>::default();let mut rng=StdRng::seed_from_u64(6102);
        for row_bits in [4,6] {for n in [8,16] {
            let rows=1<<row_bits;let mut entries:Vec<_>=(0..3).flat_map(|a|(0..rows).map(move|r|(a,r,(r+a)%2))).collect();
            entries.extend([(1,3,0),(1,3,0),(2,0,1)]);
            let mut rt=Runtime::new(n);let index=Index::new(&mut rt,row_bits,&entries,16);rt.seal();
            let row:Vec<_>=(0..row_bits).map(|_|L::random(&mut rng)).collect();
            let rho=std::array::from_fn(|_|L::random(&mut rng));let input=[L::ONE,L::ZERO];
            let e=eq_expand(&row);let mut expected=[L::ZERO;6];
            for &(a,r,c) in &entries {expected[2*a+c]+=e[r];}
            let (v,mut proof)=prove(&mut rt,&index,&row,rho,&input,&mut Transcript::new_global(&h,b"six"));
            assert_eq!(proof.values,expected);assert_eq!(v,entries.iter().map(|&(a,r,c)|rho[a]*e[r]*input[c]).sum());
            verify(&index.key,&row,rho,&input,v,&proof,&mut Transcript::new_global(&h,b"six")).unwrap();
            // Even a zero-weight column is bound: recompute the aggregate to bypass only its equality check.
            for j in 0..6 {proof.values[j]+=L::ONE;let bad=contract(&proof.values,rho,&input);
                assert!(verify(&index.key,&row,rho,&input,bad,&proof,&mut Transcript::new_global(&h,b"six")).is_err());proof.values[j]+=L::ONE;}
            let mut wrong_row=row.clone();wrong_row[0]+=L::ONE;
            assert!(verify(&index.key,&wrong_row,rho,&input,v,&proof,&mut Transcript::new_global(&h,b"six")).is_err());
            let mut key=index.key.clone();key.root[0]^=1;
            assert!(verify(&key,&row,rho,&input,v,&proof,&mut Transcript::new_global(&h,b"six")).is_err());
            proof.opening.openings[0][0].pair[0]+=L::ONE;
            assert!(verify(&index.key,&row,rho,&input,v,&proof,&mut Transcript::new_global(&h,b"six")).is_err());
        }}
    }
}
