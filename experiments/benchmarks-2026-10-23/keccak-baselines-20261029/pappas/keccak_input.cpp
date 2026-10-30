#include "keccak_input.h"
#include "utils.hpp"
#include "parameters.hpp"
#include <fstream>
#include <array>
#include <stdexcept>
#include <cstring>
#include <mpi.h>
extern int logm,logn;
namespace {
struct Term {size_t wire;int64_t coefficient;};
using LC=std::vector<Term>;
using Row=std::array<LC,3>;
std::vector<Row> rows;
size_t wires,public_start,batch,padded;
std::string directory;
void require(bool b,const char* msg){if(!b)throw std::runtime_error(msg);}
uint64_t read_u64(std::istream& f){unsigned char b[8];f.read((char*)b,8);require(bool(f),"short Keccak input");uint64_t x=0;for(int i=0;i<8;i++)x|=uint64_t(b[i])<<(8*i);return x;}
void magic(std::istream&f,const char* s){char b[8];f.read(b,8);require(bool(f)&&memcmp(s,b,8)==0,"Keccak input format");}
F dot(const LC& terms,const std::vector<F>&w,size_t offset){F y=0;for(auto&t:terms)y+=F(t.coefficient)*w[offset+t.wire];return y;}
}
bool keccak_active(){return !directory.empty();}
size_t keccak_size(){return batch*padded;}
void keccak_load(const std::string& dir){
 directory=dir;std::ifstream f(dir+"/keccak-r1cs.bin",std::ios::binary);magic(f,"PKECR001");
 size_t m=read_u64(f);wires=read_u64(f);public_start=read_u64(f);require(m==193942&&wires==193943&&public_start+256==wires,"unexpected Keccak model dimensions");
 rows.resize(m);for(auto&row:rows)for(auto&lc:row){size_t n=read_u64(f);require(n<=3,"Keccak linear combination length");for(size_t i=0;i<n;i++){size_t wire=read_u64(f);int64_t coeff=(int64_t)read_u64(f);require(wire<wires&&(coeff==-1||coeff==1||coeff==2),"Keccak matrix entry");lc.push_back({wire,coeff});}}
 require(f.peek()==EOF,"trailing Keccak model");
 std::ifstream w(dir+"/keccak-witness.bin",std::ios::binary);magic(w,"PKECW001");batch=read_u64(w);require(read_u64(w)==wires,"Keccak witness dimension");padded=1<<18;pa::keccak_table_length(batch,padded);keccak_index();
}
void keccak_index(){logm=18;for(size_t b=batch;b>1;b>>=1)++logm;logn=logm;}
void keccak_witness(std::vector<F>&w,std::vector<F>&l,std::vector<F>&r,std::vector<F>&o){
 std::ifstream f(directory+"/keccak-witness.bin",std::ios::binary);magic(f,"PKECW001");require(read_u64(f)==batch&&read_u64(f)==wires,"Keccak witness dimensions changed");
 std::ifstream d(directory+"/keccak-output.bin",std::ios::binary);require(bool(d),"missing public Keccak digest");
 w.assign(keccak_size(),F(0));l.assign(keccak_size(),F(0));r=l;o=l;
 for(size_t j=0;j<batch;j++){
  size_t off=j*padded;for(size_t i=0;i<wires;i++){int x=f.get();require(x==0||x==1,"non-Boolean Keccak witness");w[off+i]=F(x);}require(w[off]==F(1),"Keccak constant-one binding");
  unsigned char digest[32];d.read((char*)digest,32);require(bool(d),"short public Keccak digest");
  for(size_t i=0;i<256;i++){unsigned val=(digest[i/8]>>(i%8))&1;require(w[off+public_start+i]==F(val),"Keccak public digest binding");}
  for(size_t i=0;i<rows.size();i++){l[off+i]=dot(rows[i][0],w,off);r[off+i]=dot(rows[i][1],w,off);o[off+i]=dot(rows[i][2],w,off);require(l[off+i]*r[off+i]==o[off+i],"Keccak R1CS unsatisfied");}
 }
 require(f.peek()==EOF&&d.peek()==EOF,"trailing Keccak witness/digest");
 int rank;MPI_Comm_rank(MPI_COMM_WORLD,&rank);if(rank==0){printf("{\"event\":\"keccak_input_checked\",\"messages\":%zu,\"rows\":%zu,\"wires\":%zu,\"source\":\"external_Keccak_R1CS_and_witness\"}\n",batch,keccak_size(),keccak_size());fflush(stdout);}
}
size_t keccak_instance_stride(){return padded;}
void keccak_read_instance(size_t instance,std::vector<F>&w,std::vector<F>&l,std::vector<F>&r,std::vector<F>&o){
 require(instance<batch,"Keccak instance out of range");
 std::ifstream f(directory+"/keccak-witness.bin",std::ios::binary);magic(f,"PKECW001");
 require(read_u64(f)==batch&&read_u64(f)==wires,"Keccak witness dimensions changed");
 f.seekg(24+instance*wires);w.assign(padded,F(0));l.assign(padded,F(0));r=l;o=l;
 for(size_t i=0;i<wires;i++){int x=f.get();require(x==0||x==1,"non-Boolean Keccak witness");w[i]=F(x);}
 require(w[0]==F(1),"Keccak constant-one binding");
 std::ifstream d(directory+"/keccak-output.bin",std::ios::binary);d.seekg(instance*32);
 unsigned char digest[32];d.read((char*)digest,32);require(bool(d),"short public Keccak digest");
 for(size_t i=0;i<256;i++)require(w[public_start+i]==F((digest[i/8]>>(i%8))&1),"Keccak public digest binding");
 for(size_t i=0;i<rows.size();i++){
  l[i]=dot(rows[i][0],w,0);r[i]=dot(rows[i][1],w,0);o[i]=dot(rows[i][2],w,0);
  require(l[i]*r[i]==o[i],"Keccak R1CS unsatisfied");
 }
 if(instance+1==batch)require(f.peek()==EOF&&d.peek()==EOF,"trailing Keccak witness/digest");
}
void keccak_reduce(const std::vector<F>&point,std::vector<F>&a,std::vector<F>&b,std::vector<F>&c,int N){
 require(point.size()==size_t(logm),"Keccak row challenge dimension");int rank;MPI_Comm_rank(MPI_COMM_WORLD,&rank);
 std::vector<F> low(point.begin(),point.begin()+18),high(point.begin()+18,point.end()),beta,outer;precompute_beta(low,beta);precompute_beta(high,outer);
 size_t len=keccak_size()/N,start=rank*len,stop=start+len;a.assign(len,F(0));b=a;c=a;std::array<std::vector<F>*,3> out{&a,&b,&c};
 for(size_t j=start/padded;j<batch&&j*padded<stop;j++)for(size_t row=0;row<rows.size();row++){
  F scale=beta[row]*outer[j];for(size_t mat=0;mat<3;mat++)for(auto&t:rows[row][mat]){size_t col=j*padded+t.wire;if(col>=start&&col<stop)(*out[mat])[col-start]+=scale*F(t.coefficient);}
 }
}
void keccak_check_reduction(int N){
 std::vector<F> point(logm);for(size_t i=0;i<point.size();i++)point[i]=F(i+2,i+3);
 std::vector<F>a,b,c;keccak_reduce(point,a,b,c,N);
 // Independent direct matrix-row path on rank 0, with actual MPI reduction.
 size_t len=keccak_size()/N;int rank;MPI_Comm_rank(MPI_COMM_WORLD,&rank);std::vector<F>w,l,r,o;
 std::vector<unsigned char> raw(batch*wires);std::ifstream f(directory+"/keccak-witness.bin",std::ios::binary);f.seekg(24);f.read((char*)raw.data(),raw.size());require(bool(f),"short witness reduction check");
 std::array<F,3> local{F(0),F(0),F(0)};std::array<std::vector<F>*,3> v{&a,&b,&c};
 for(size_t i=0;i<len;i++){size_t global=rank*len+i,j=global/padded,wire=global%padded;F value=wire<wires?F(raw[j*wires+wire]):F(0);for(size_t k=0;k<3;k++)local[k]+=(*v[k])[i]*value;}
 std::vector<F> all(rank==0?3*N:0);MPI_Gather(local.data(),3*sizeof(F),MPI_BYTE,all.data(),3*sizeof(F),MPI_BYTE,0,MPI_COMM_WORLD);
 if(rank==0){keccak_witness(w,l,r,o);std::vector<F> beta;precompute_beta(point,beta);std::array<F,3> expected{F(0),F(0),F(0)},actual{F(0),F(0),F(0)};std::array<std::vector<F>*,3> z{&l,&r,&o};for(size_t k=0;k<3;k++){for(size_t i=0;i<keccak_size();i++)expected[k]+=beta[i]*(*z[k])[i];for(int p=0;p<N;p++)actual[k]+=all[3*p+k];require(actual[k]==expected[k],"Keccak distributed weighted matrix mismatch");}printf("{\"event\":\"keccak_distributed_reduction_checked\",\"parties\":%d,\"accepted\":true}\n",N);fflush(stdout);}
}
