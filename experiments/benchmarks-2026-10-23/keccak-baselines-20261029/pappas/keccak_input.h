#pragma once
#include "config_pc.hpp"
#include <string>
#include <vector>
void keccak_load(const std::string& directory);
bool keccak_active();
void keccak_index();
size_t keccak_size();
void keccak_witness(std::vector<F>& w,std::vector<F>& l,std::vector<F>& r,std::vector<F>& o);
void keccak_read_instance(size_t instance,std::vector<F>& w,std::vector<F>& l,std::vector<F>& r,std::vector<F>& o);
size_t keccak_instance_stride();
void keccak_reduce(const std::vector<F>& point,std::vector<F>& a,std::vector<F>& b,std::vector<F>& c,int N);
void keccak_check_reduction(int N);
