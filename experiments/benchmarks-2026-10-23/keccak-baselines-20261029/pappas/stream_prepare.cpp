#include "stream_prepare.hpp"
#include "stream_shares.hpp"
#include "keccak_input.h"
#include <mpi.h>
#include <array>
#include <cstdlib>
#include <limits>
#include <stdexcept>

// Pure RAM: original application input is read normally; no share/state files,
// mappings, swap or disk-backed buffers are created. Chunking is preprocessing.
void keccak_distribute_proving_data(std::vector<F>&l,std::vector<F>&r,
 std::vector<F>&o,std::vector<F>&w,int n,int m,int kp,int k){
 int rank;MPI_Comm_rank(MPI_COMM_WORLD,&rank);
 const char*budget=getenv("PAPPAS_PREPARE_BUFFER_BYTES");
 if(!budget||!*budget)throw std::runtime_error("explicit preparation buffer budget required");
 size_t chunk=std::stoull(budget)/(sizeof(F)*size_t(n));
 if(!chunk||m<=0||m%k||chunk>size_t(std::numeric_limits<int>::max())/2)
  throw std::runtime_error("preparation buffer budget or dimensions");
 size_t rows=size_t(m)/k;
 std::array<std::vector<F>*,4> output{&w,&l,&r,&o};
 for(auto*v:output)v->resize(rows);
 if(rank==0){
  // Same native W,L,R,O PRG order. Each party receives exactly the same
  // four vectors as before; only offline transport framing is segmented.
  for(size_t kind=0;kind<4;kind++){
   size_t cached=std::numeric_limits<size_t>::max();
   std::array<std::vector<F>,4> instance;
   pa::stream_private_table(m,n,k,kp,chunk,
    [&](size_t start,size_t count,std::vector<F>&v){
     v.resize(count);
     for(size_t i=0;i<count;i++){
      size_t j=(start+i)/keccak_instance_stride(),column=(start+i)%keccak_instance_stride();
      if(cached!=j){keccak_read_instance(j,instance[0],instance[1],instance[2],instance[3]);cached=j;}
      v[i]=instance[kind][column];
     }
    },
    [&](int p,size_t first,const std::vector<F>&v){
     if(p==0){std::copy(v.begin(),v.end(),output[kind]->begin()+first);return;}
     std::vector<u64> raw(2*v.size());
     for(size_t i=0;i<v.size();i++){raw[2*i]=v[i].real;raw[2*i+1]=v[i].img;}
     if(MPI_Send(raw.data(),raw.size(),MPI_UINT64_T,p,0,MPI_COMM_WORLD)!=MPI_SUCCESS)
      throw std::runtime_error("send preparation chunk");
    });
  }
  printf("{\"event\":\"keccak_input_checked\",\"messages\":%zu,\"rows\":%d,\"wires\":%d,\"source\":\"external_Keccak_R1CS_and_witness\"}\n",keccak_size()/keccak_instance_stride(),m,m);
 }else{
  for(size_t kind=0;kind<4;kind++)for(size_t first=0;first<rows;first+=chunk){
   size_t count=std::min(chunk,rows-first);std::vector<u64> raw(2*count);
   if(MPI_Recv(raw.data(),raw.size(),MPI_UINT64_T,0,0,MPI_COMM_WORLD,MPI_STATUS_IGNORE)!=MPI_SUCCESS)
    throw std::runtime_error("receive preparation chunk");
   for(size_t i=0;i<count;i++){
    (*output[kind])[first+i].real=raw[2*i];(*output[kind])[first+i].img=raw[2*i+1];
   }
  }
 }
}
