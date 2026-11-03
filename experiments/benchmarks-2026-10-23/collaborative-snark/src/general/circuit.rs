use crate::sha_circuit::ShaCircuit;
use anyhow::{Result,ensure};
use rand::{Rng,RngExt,SeedableRng,rngs::StdRng};
use serde::{Deserialize,Serialize};

pub type Entries=Vec<(usize,usize,usize)>;

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq,Serialize,Deserialize,clap::ValueEnum)]
#[serde(rename_all="snake_case")]
pub enum Task { #[default] XorAnd, NandCopy, LinearFeedback, XorAndRegular, XorAndRandom, XorAndRandom50 }
impl Task {
    fn is_default(&self)->bool{*self==Self::XorAnd}
    fn is_feedback(&self)->bool{matches!(self,Self::LinearFeedback|Self::XorAndRegular|Self::XorAndRandom|Self::XorAndRandom50)}
}

#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct Gate { pub left:Vec<usize>,pub right:usize }

#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct Circuit {
    pub format:String,
    #[serde(default,skip_serializing_if="Task::is_default")]
    pub task:Task,
    pub seed:u64,
    pub inputs:usize,
    pub gates:Vec<Gate>,
    pub max_parties:usize,
    pub virtual_slots:usize,
    pub layout_gates:usize,
    pub base_bits:usize,
    pub base_rows:usize,
    pub mask_bit_start:usize,
    pub mask_row_start:usize,
}

impl Circuit {
    pub fn generate(count:usize,seed:u64,max_parties:usize)->Result<Self> {
        Self::generate_task(count,seed,max_parties,Task::XorAnd)
    }
    pub fn generate_task(count:usize,seed:u64,max_parties:usize,task:Task)->Result<Self> {
        ensure!(count>=16,"at least 16 original constraints");
        ensure!((8..=256).contains(&max_parties)&&max_parties.is_power_of_two(),"maximum party count");
        let inputs=(count/16).max(16);
        let mut rng=StdRng::seed_from_u64(seed);
        let mut gates=Vec::with_capacity(count);
        for j in 0..count {
            let available=inputs+j;
            if task==Task::XorAndRandom50 {
                let is_and=rng.random::<bool>();
                let a=rng.random_range(0..available);
                let mut b=rng.random_range(0..available-1);if b>=a{b+=1;}
                let (left,right)=if is_and{(vec![a],b)}else{let mut left=vec![a,b];left.sort_unstable();(left,usize::MAX)};
                gates.push(Gate{left,right});continue;
            }
            if task.is_feedback() {
                let left=if task==Task::XorAndRandom {
                    let mut left=vec![];
                    while left.len()<3 {let id=rng.random_range(0..available);if !left.contains(&id){left.push(id);}}
                    left.sort_unstable();left
                }else{vec![j,j+13%inputs,j+37%inputs]};
                let right=if task!=Task::LinearFeedback&&j%16==15 {
                    if task==Task::XorAndRandom {rng.random_range(0..available)}else{j+113%inputs}
                }else{usize::MAX}; // Public one, only for the new feedback tasks.
                gates.push(Gate{left,right});continue;
            }
            if task==Task::NandCopy {
                let logical=|id:usize|if id<inputs{id}else{inputs+3*(id-inputs)+2};
                gates.push(Gate{left:vec![logical(rng.random_range(0..available))],right:logical(rng.random_range(0..available))});
                continue;
            }
            let fanin=rng.random_range(1..=3.min(available));
            let mut left=Vec::with_capacity(fanin);
            while left.len()<fanin {let p=rng.random_range(0..available);if !left.contains(&p){left.push(p);}}
            left.sort_unstable();
            gates.push(Gate{left,right:rng.random_range(0..available)});
        }
        let virtual_slots=max_parties/4;
        let raw_rows=if task==Task::NandCopy {inputs+3*count+1}else if task.is_feedback(){inputs+count+1}else{count+1};
        let wires=inputs+if task==Task::NandCopy{3*count}else{count};
        let layout_gates=wires.max(raw_rows).div_ceil(virtual_slots).max(8);
        // Geometry only: the template's SHA/synthetic gates are never executed.
        let geometry=ShaCircuit::synthetic_zk(layout_gates);
        let (mask_bit_start,mask_row_start)=geometry.mask_start.unwrap();
        let c=Self{format:if task==Task::NandCopy{"general-binary-nand-copy-v1"}else if task.is_feedback(){"general-binary-feedback-v1"}else{"general-binary-r1cs-v1"}.into(),task,seed,inputs,gates,
            max_parties,virtual_slots,layout_gates,base_bits:geometry.base.n0(),
            base_rows:geometry.base.m0(),mask_bit_start,mask_row_start};
        ensure!(c.wires_per_virtual()<=mask_bit_start,"wire reserve");
        ensure!(if task==Task::NandCopy||task.is_feedback(){raw_rows.div_ceil(virtual_slots)<=mask_row_start}else{count.div_ceil(virtual_slots)+1<=mask_row_start},"row reserve");
        Ok(c)
    }
    pub fn wire_count(&self)->usize {self.inputs+self.gates.len()*if self.task==Task::NandCopy{3}else{1}}
    pub fn raw_rows(&self)->usize {if self.task==Task::NandCopy{self.inputs+3*self.gates.len()+1}else if self.task.is_feedback(){self.inputs+self.gates.len()+1}else{self.gates.len()+1}}
    fn wires_per_virtual(&self)->usize {self.wire_count().div_ceil(self.virtual_slots)}
    pub fn wire(&self,id:usize)->usize {let per=self.wires_per_virtual();(id/per)*self.base_bits+id%per}
    fn row(&self,id:usize)->usize {let count=if self.task==Task::NandCopy||self.task.is_feedback(){self.raw_rows()}else{self.gates.len()};let per=count.div_ceil(self.virtual_slots);(id/per)*self.base_rows+id%per}
    pub fn bits(&self)->usize {self.base_bits*self.virtual_slots}
    pub fn rows(&self)->usize {self.base_rows*self.virtual_slots}
    pub fn groups(&self,n:usize)->Result<usize> {
        ensure!((8..=self.max_parties).contains(&n)&&n.is_power_of_two(),"party count outside this fixed circuit");
        Ok(self.virtual_slots/(n/4))
    }
    pub fn entries(&self)->(Entries,Entries) {
        let(mut private,mut public)=(vec![],vec![]);
        if self.task==Task::NandCopy {
            for j in 0..self.inputs {let r=self.row(j);for t in 0..3{private.push((t,r,self.wire(j)));}}
            for (j,g) in self.gates.iter().enumerate() {
                let u=self.inputs+3*j;let t=u+1;let z=u+2;let row=self.inputs+3*j;
                let copy=self.row(row);
                if j==0 {public.extend([(0,copy,0),(1,copy,0)]);}else{for a in 0..2 {private.push((a,copy,self.wire(u-3)));}}
                private.push((2,copy,self.wire(u)));
                let and=self.row(row+1);private.extend([(0,and,self.wire(g.left[0])),(1,and,self.wire(g.right)),(2,and,self.wire(t))]);
                let inv=self.row(row+2);private.extend([(0,inv,self.wire(t)),(0,inv,self.wire(z)),(1,inv,self.wire(u)),(2,inv,self.wire(u))]);
            }
            let r=self.row(self.raw_rows()-1);private.push((0,r,self.wire(self.wire_count()-1)));public.extend([(1,r,0),(2,r,1)]);
        }else if self.task.is_feedback(){
            for j in 0..self.inputs {let r=self.row(j);for t in 0..3{private.push((t,r,self.wire(j)));}}
            for (j,g) in self.gates.iter().enumerate() {
                let r=self.row(self.inputs+j);
                for &v in &g.left {private.push((0,r,self.wire(v)));}
                if g.right==usize::MAX {public.push((1,r,0));}else{private.push((1,r,self.wire(g.right)));}
                private.push((2,r,self.wire(self.inputs+j)));
            }
            let r=self.row(self.raw_rows()-1);private.push((0,r,self.wire(self.wire_count()-1)));public.extend([(1,r,0),(2,r,1)]);
        }else{
        for (j,g) in self.gates.iter().enumerate() {
            let row=self.row(j);
            for &v in &g.left {private.push((0,row,self.wire(v)));}
            private.push((1,row,self.wire(g.right)));
            private.push((2,row,self.wire(self.inputs+j)));
        }
        // Public p=(1, output): (last wire + output)*1=0.
        let output_row=self.gates.len().div_ceil(self.virtual_slots);
        private.push((0,output_row,self.wire(self.inputs+self.gates.len()-1)));
        public.extend([(0,output_row,1),(1,output_row,0)]);
        }
        for slot in 0..self.virtual_slots {
            let bit=slot*self.base_bits+self.mask_bit_start;
            let row=slot*self.base_rows+self.mask_row_start;
            for j in 0..1024 {
                private.extend([(0,row+j,bit+j),(2,row+j,bit+j)]);
                public.push((1,row+j,0));
                private.extend([(1,row+1024+j,bit+1024+j),(2,row+1024+j,bit+1024+j)]);
                public.push((0,row+1024+j,0));
                for channel in 0..3 {private.push((channel,row+2048+j,bit+2048+j));}
            }
        }
        (private,public)
    }
    pub fn witness(&self,rng:&mut impl Rng)->(Vec<bool>,[bool;2]) {
        let inputs:Vec<bool>=(0..self.inputs).map(|_|rng.random()).collect();
        self.witness_with_inputs(&inputs,rng).unwrap()
    }
    pub fn witness_with_inputs(&self,inputs:&[bool],rng:&mut impl Rng)->Result<(Vec<bool>,[bool;2])> {
        ensure!(inputs.len()==self.inputs,"initial input length");let mut wires=inputs.to_vec();
        for g in &self.gates {
            if self.task==Task::NandCopy {let t=wires[g.left[0]]&wires[g.right];wires.extend([true,t,!t]);}
            else{let right=if self.task.is_feedback()&&g.right==usize::MAX{true}else{wires[g.right]};wires.push(g.left.iter().fold(false,|s,&v|s^wires[v])&right);}
        }
        let public=[true,*wires.last().unwrap()];
        let mut padded=vec![false;self.bits()];
        for (id,&value) in wires.iter().enumerate(){padded[self.wire(id)]=value;}
        for slot in 0..self.virtual_slots {
            for x in &mut padded[slot*self.base_bits+self.mask_bit_start..][..4096] {*x=rng.random();}
        }
        Ok((padded,public))
    }
    pub fn row_values(&self,witness:&[bool],public:&[bool;2])->[Vec<bool>;3] {
        let mut rows=std::array::from_fn(|_|vec![false;self.rows()]);
        let (private,public_entries)=self.entries();
        for (t,r,c) in private {rows[t][r]^=witness[c];}
        for (t,r,c) in public_entries {rows[t][r]^=public[c];}
        rows
    }
    pub fn check(&self,witness:&[bool],public:&[bool;2])->Result<()> {
        ensure!(witness.len()==self.bits()&&public[0],"witness/public shape");
        let [a,b,c]=self.row_values(witness,public);
        ensure!((0..self.rows()).all(|i|(a[i]&b[i])==c[i]),"R1CS constraint failed");
        Ok(())
    }
    pub fn cross_slot_entries(&self,n:usize)->Result<usize> {
        let groups=self.groups(n)?;
        let row_length=self.base_rows*groups;
        let bit_length=self.base_bits*groups;
        Ok(self.entries().0.iter().filter(|(_,r,c)|r/row_length!=c/bit_length).count())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn random50_binary_gates_preserve_exact_count_and_relation() {
        for count in [16,128,32768] {
            let c=Circuit::generate_task(count,42,32,Task::XorAndRandom50).unwrap();
            assert_eq!(c.gates.len(),count);
            let and_count=c.gates.iter().filter(|g|g.right!=usize::MAX).count();
            assert!(and_count>0&&and_count<count);
            let input:Vec<_>=(0..c.inputs).map(|i|i%3==0).collect();
            let(w,p)=c.witness_with_inputs(&input,&mut StdRng::seed_from_u64(7)).unwrap();
            c.check(&w,&p).unwrap();let mut values=input;
            for (j,g) in c.gates.iter().enumerate() {
                assert!(g.left.iter().all(|&v|v<c.inputs+j));
                let value=if g.right==usize::MAX {
                    assert_eq!(g.left.len(),2);assert_ne!(g.left[0],g.left[1]);values[g.left[0]]^values[g.left[1]]
                }else{
                    assert_eq!(g.left.len(),1);assert!(g.right<c.inputs+j);assert_ne!(g.left[0],g.right);values[g.left[0]]&&values[g.right]
                };
                values.push(value);assert_eq!(w[c.wire(c.inputs+j)],value);
            }
            assert_eq!(p[1],*values.last().unwrap());
            let mut bad=w.clone();bad[c.wire(c.inputs)]=!bad[c.wire(c.inputs)];assert!(c.check(&bad,&p).is_err());
            assert!(c.check(&w,&[true,!p[1]]).is_err());
            let other=Circuit::generate_task(count,42,64,Task::XorAndRandom50).unwrap();
            assert_eq!(serde_json::to_vec(&c.gates).unwrap(),serde_json::to_vec(&other.gates).unwrap());
        }
        assert_eq!(Circuit::generate_task(17,42,32,Task::XorAndRandom50).unwrap().gates.len(),17);
    }
    #[test]
    fn xor_screening_tasks_are_global_boolean_relations() {
        for task in [Task::LinearFeedback,Task::XorAndRegular,Task::XorAndRandom] {
            let c=Circuit::generate_task(128,42,16,task).unwrap();
            let inputs:Vec<bool>=(0..c.inputs).map(|j|j%3==0).collect();
            let(w,p)=c.witness_with_inputs(&inputs,&mut StdRng::seed_from_u64(7)).unwrap();
            c.check(&w,&p).unwrap();assert_eq!(c.raw_rows(),c.inputs+129);
            let mut state=inputs.clone();let mut wires=inputs;
            for (j,g) in c.gates.iter().enumerate() {
                assert_eq!(g.left.len(),3);assert!(g.left.iter().all(|&id|id<c.inputs+j));
                let nonlinear=task!=Task::LinearFeedback&&j%16==15;
                assert_eq!(g.right!=usize::MAX,nonlinear);
                let value=if task==Task::XorAndRandom {
                    let parity=g.left.iter().filter(|&&id|wires[id]).count()%2!=0;
                    parity&&(!nonlinear||wires[g.right])
                }else{
                    let at=j%c.inputs;
                    let parity=state[at]^state[(at+13)%c.inputs]^state[(at+37)%c.inputs];
                    let value=parity&&(!nonlinear||state[(at+113)%c.inputs]);state[at]=value;value
                };
                wires.push(value);assert_eq!(w[c.wire(c.inputs+j)],value);
            }
            assert_eq!(p[1],*wires.last().unwrap());
            for n in [8,16] {assert!(c.cross_slot_entries(n).unwrap()>0);}
            let mut bad=w.clone();bad[c.wire(c.inputs)]=!bad[c.wire(c.inputs)];assert!(c.check(&bad,&p).is_err());
            assert!(c.check(&w,&[true,!p[1]]).is_err());
        }
    }
    #[test]
    fn nand_copy_is_boolean_and_fixed_across_partitions() {
        let c=Circuit::generate_task(64,42,16,Task::NandCopy).unwrap();let input:Vec<_>=(0..c.inputs).map(|i|i%3==0).collect();
        let(w,p)=c.witness_with_inputs(&input,&mut StdRng::seed_from_u64(4)).unwrap();c.check(&w,&p).unwrap();
        assert_eq!(c.raw_rows(),c.inputs+3*64+1);
        for n in [8,16] {assert!(c.cross_slot_entries(n).unwrap()>0);}
        let mut values=input;for g in &c.gates {let t=values[g.left[0]]&&values[g.right];values.extend([true,t,!t]);}
        assert_eq!(p[1],*values.last().unwrap());
        let mut bad=w;bad[c.wire(c.inputs)]=false;assert!(c.check(&bad,&p).is_err());
    }
    #[test]
    fn global_relation_is_fixed_across_partitions_and_mutations_fail() {
        let c=Circuit::generate(64,42,16).unwrap();
        let frozen=serde_json::to_vec(&c).unwrap();
        let (mut w,p)=c.witness(&mut StdRng::seed_from_u64(73));
        c.check(&w,&p).unwrap();
        for n in [8,16] {assert!(c.cross_slot_entries(n).unwrap()>0);assert_eq!(serde_json::to_vec(&c).unwrap(),frozen);}
        w[c.wire(c.inputs)]=!w[c.wire(c.inputs)];
        assert!(c.check(&w,&p).is_err());
        let (w,mut p)=c.witness(&mut StdRng::seed_from_u64(73));p[1]=!p[1];
        assert!(c.check(&w,&p).is_err());
    }
}
