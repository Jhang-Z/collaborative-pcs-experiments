#pragma once
#include "config_pc.hpp"
#include <vector>
void keccak_distribute_proving_data(std::vector<F>&l,std::vector<F>&r,
 std::vector<F>&o,std::vector<F>&w,int n,int m,int kp,int k);
