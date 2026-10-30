#pragma once
#include "coPCS.h"
#include "MPI_utils.hpp"
#include "Fiat_Shamir.h"
#include "timer.hpp"
#include "parameters.hpp"
#include <array>
#include <fstream>
#include <stdexcept>
#include <string>
#include <sys/random.h>
#include <fcntl.h>
#include <unistd.h>
#include <chrono>
#include <cstring>
#include <algorithm>
#include <cmath>
#include <mpi.h>
extern "C" {
#include "blake3.h"
}
namespace pa {
using Bytes=std::vector<unsigned char>;
using Hash=std::array<unsigned char,32>;
using Vec=std::vector<F>;
const size_t Q=520;
const size_t DISCLOSURE=8*Q;
const size_t MASK_PADDING=3*DISCLOSURE;
inline void require(bool b,const char* m){if(!b)throw std::runtime_error(m);}
inline size_t lg(size_t n){require(n && !(n&(n-1)),"not power of two");size_t j=0;while(n>1){n>>=1;++j;}return j;}
inline void u64(Bytes& b,uint64_t x){for(int i=0;i<8;++i)b.push_back(x>>(8*i));}
inline void field(Bytes& b,F x){u64(b,x.real);u64(b,x.img);}
inline void fields(Bytes& b,const Vec& v){for(auto x:v)field(b,x);}
inline void hash(Bytes& b,const Hash& h){b.insert(b.end(),h.begin(),h.end());}
inline Bytes read(const std::string& p){std::ifstream f(p,std::ios::binary);require(bool(f),"open failed");return Bytes(std::istreambuf_iterator<char>(f),{});}
inline void write(const std::string& p,const Bytes& b){std::ofstream f(p,std::ios::binary);f.write((const char*)b.data(),b.size());require(bool(f),"write failed");}
struct Reader{const Bytes& b;size_t pos=0; uint64_t number(){require(pos+8<=b.size(),"truncated");uint64_t v=0;for(int i=0;i<8;i++)v|=uint64_t(b[pos++])<<(8*i);return v;} F value(){auto r=number(),i=number();require(r<PRIME && i<PRIME,"noncanonical field");F x;x.real=r;x.img=i;return x;} Vec values(size_t n){require(n<=(b.size()-pos)/16,"truncated vector");Vec v(n);for(auto&x:v)x=value();return v;} Hash digest(){require(pos+32<=b.size(),"truncated hash");Hash h;std::copy_n(b.begin()+pos,32,h.begin());pos+=32;return h;}void magic(const char*m){require(pos+8<=b.size() && !memcmp(b.data()+pos,m,8),"bad format");pos+=8;}void end(){require(pos==b.size(),"trailing bytes");}};
inline Bytes magic(const char*m){return Bytes(m,m+8);}
inline Hash digest(const Bytes& b){Hash h;blake3_hasher x;blake3_hasher_init(&x);blake3_hasher_update(&x,b.data(),b.size());blake3_hasher_finalize(&x,h.data(),32);return h;}
inline uint64_t secret_component(){static unsigned char buf[32768];static size_t off=sizeof(buf);for(;;){if(off==sizeof(buf)){size_t p=0;while(p<sizeof(buf)){ssize_t n=getrandom(buf+p,sizeof(buf)-p,0);require(n>0,"entropy failed");p+=n;}off=0;}uint64_t v=0;for(int i=0;i<8;i++)v|=uint64_t(buf[off++])<<(8*i);v&=PRIME;if(v<PRIME)return v;}}
inline Hash random_hash(){Hash h;size_t p=0;while(p<h.size()){ssize_t n=getrandom(h.data()+p,h.size()-p,0);require(n>0,"entropy failed");p+=n;}return h;}
inline F secret(){F x;x.real=secret_component();x.img=secret_component();return x;}
struct Statement{size_t N,M,k,kp,m,D,R;Vec point;F y;Bytes bytes;
 explicit Statement(const Bytes& b):bytes(b){Reader r{bytes};r.magic("PAPST002");N=r.number();M=r.number();D=pcs_row_length(N,M,MASK_PADDING);k=N/4;kp=N/2;m=M/k;size_t cutoff=lg(next_pow2(MASK_PADDING))+1;R=lg(D)>cutoff?lg(D)-cutoff:1;point=r.values(lg(M));y=r.value();r.end();}
};
inline Vec beta(Vec p){Vec b;precompute_beta(p,b);return b;}
inline Vec column_weights(const Statement&s){return beta(Vec(s.point.begin(),s.point.begin()+lg(s.k)));}
inline Vec row_weights(const Statement&s){Vec p(s.point.begin()+lg(s.k),s.point.end());while((size_t(1)<<p.size())<s.D)p.push_back(F(0));Vec b=beta(p);require(b.size()==s.D,"padded point dimension");fft(b,lg(b.size()),false);F step=getRootOfUnity(1+lg(4*s.D)).inv(),v=1;for(auto&x:b){x*=v;v*=step;}return b;}
inline Vec encode_row(const Vec& evaluations){Vec c=evaluations;fft(c,lg(c.size()),true);F step=getRootOfUnity(1+lg(4*c.size())),v=1;for(auto&x:c){x*=v;v*=step;}return c;}
inline Vec share(const Vec& values,size_t N){Vec c=values;fft(c,lg(c.size()),true);c.resize(2*N,F(0));fft(c,lg(c.size()),false);Vec out(N);for(size_t i=0;i<N;i++)out[i]=c[2*i+1];return out;}
inline Vec recover(Vec v,size_t kp){size_t N=v.size();fft(v,lg(N),true);for(size_t j=kp;j<N;j++)require(v[j]==F(0),"column degree");F step=getRootOfUnity(1+lg(N)).inv(),w=1;for(auto&x:v){x*=w;w*=step;}fft(v,lg(N),false);Vec out(kp);for(size_t j=0;j<kp;j++)out[j]=v[N*j/kp];return out;}
inline F mle(Vec v,Vec p){for(auto r:p){for(size_t i=0;i<v.size()/2;i++)v[i]=v[2*i]+r*(v[2*i+1]-v[2*i]);v.resize(v.size()/2);}require(v.size()==1,"MLE dimension");return v[0];}
struct Private{Hash session;Vec row;std::vector<Vec> masks;Vec aggregation_masks;};
inline Private load_private(const std::string& dir,const Statement&s,size_t rank){auto b=read(dir+"/party-"+std::to_string(rank)+".private");Reader r{b};r.magic("PAPPR003");require(r.number()==rank,"private rank");require(r.digest()==digest(s.bytes),"private statement binding");Private p;p.session=r.digest();p.row=r.values(s.D);for(size_t i=0;i<s.R;i++)p.masks.push_back(r.values(s.D>>i));p.aggregation_masks=r.values(4*s.R);r.end();return p;}
inline void prepare(const std::string& master,const Statement&s,const std::string& dir){auto input=read(master);require(input.size()>=s.M/8,"short master");Vec bits(s.M);for(size_t i=0;i<s.M;i++)bits[i]=F((input[i/8]>>(i%8))&1);require(mle(bits,s.point)==s.y,"common input claim mismatch");std::vector<Private> all(s.N);for(auto&p:all){p.row.resize(s.D,F(0));for(size_t i=0;i<s.R;i++)p.masks.emplace_back(s.D>>i,F(0));}
 for(size_t c=0;c<s.m+DISCLOSURE;c++){Vec v(s.kp);for(size_t j=0;j<s.kp;j++)v[j]=(c<s.m&&j<s.k)?bits[c*s.k+j]:secret();auto shares=share(v,s.N);for(size_t j=0;j<s.N;j++)all[j].row[c]=shares[j];}
 for(size_t i=0;i<s.R;i++){size_t len=s.D>>i;for(size_t c=0;c<len;c++){if(i+1<s.R && !(c<2 || (c>=len/2 && c<len/2+MASK_PADDING)))continue;Vec v(s.kp);for(auto&x:v)x=secret();auto shares=share(v,s.N);for(size_t j=0;j<s.N;j++)all[j].masks[i][c]=shares[j];}}
 // Check complete column recovery and the transformed native inner product before writing.
 Vec weights=row_weights(s),cw=column_weights(s),ip(s.N,F(0));for(size_t j=0;j<s.N;j++){Vec coeff=encode_row(all[j].row);for(size_t c=0;c<s.D;c++)ip[j]+=weights[c]*coeff[c];}Vec values=recover(ip,s.kp);F y=0;for(size_t j=0;j<s.k;j++)y+=cw[j]*values[j];require(y==s.y,"native weight mapping");
 for(auto&p:all)p.aggregation_masks.resize(4*s.R);for(size_t c=0;c<4*s.R;c++){F sum=0;for(size_t j=1;j<s.N;j++){F r=secret();all[j].aggregation_masks[c]=r;sum+=r;}all[0].aggregation_masks[c]=-sum;}
 Hash session=random_hash();
 for(size_t j=0;j<s.N;j++){auto name=dir+"/party-"+std::to_string(j)+".private";int fd=open(name.c_str(),O_CREAT|O_EXCL|O_WRONLY,0600);require(fd>=0,"preparation already exists");close(fd);Bytes b=magic("PAPPR003");u64(b,j);hash(b,digest(s.bytes));hash(b,session);fields(b,all[j].row);for(auto&m:all[j].masks)fields(b,m);fields(b,all[j].aggregation_masks);write(dir+"/party-"+std::to_string(j)+".private",b);}write(dir+"/statement.bin",s.bytes);
}
}
