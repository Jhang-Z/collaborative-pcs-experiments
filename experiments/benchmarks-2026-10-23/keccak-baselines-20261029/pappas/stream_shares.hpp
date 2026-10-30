#pragma once
#include "utils.hpp"
#include <algorithm>
#include <cmath>
#include <stdexcept>

namespace pa {
// Same native sharing map and PRG order as compute_secret_shares; only the
// lifetime of the N-by-row output buffer changes. The sink owns persistence.
template<class Read, class Write>
void stream_private_table(size_t length,int n,int k,int kp,size_t chunk_rows,
                          Read read,Write write){
 if(!chunk_rows||k<=0||kp<k||n<kp||length%k)
  throw std::runtime_error("invalid streaming sharing dimensions");
 for(size_t first=0;first<length/size_t(k);first+=chunk_rows){
  size_t count=std::min(chunk_rows,length/size_t(k)-first);
  std::vector<std::vector<F>> shares(n,std::vector<F>(count));
  for(size_t i=0;i<count;i++){
   std::vector<F> buff;read((first+i)*k,k,buff);
   if(buff.size()!=size_t(k))throw std::runtime_error("short streaming source");
   buff.resize(kp,F(0));
   for(int j=k;j<kp;j++)buff[j]=random();
   fft(buff,(int)std::log2(buff.size()),true);
   buff.resize(2*n,F(0));fft(buff,(int)std::log2(buff.size()),false);
   for(int p=0;p<n;p++)shares[p][i]=buff[2*p+1];
  }
  for(int p=0;p<n;p++)write(p,first,shares[p]);
 }
}
}
