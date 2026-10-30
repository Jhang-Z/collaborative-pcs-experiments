#include "keccak_input.h"
#include "coPIOP.h"
#include "timer.hpp"
#include "parameters.hpp"
#include <mpi.h>
#include <stdexcept>
#include <sys/random.h>
unsigned long int mul_counter=0;
int tensor_row_size=0,cosumcheck_offset=0,sumcheck_offset=4,PC_offset=10,multree_offset=4;
bool isLAN=false;
extern bool data_parallel;
int main(int argc,char**argv){setvbuf(stdout,nullptr,_IONBF,0);MPI_Init(&argc,&argv);int rank,N;MPI_Comm_rank(MPI_COMM_WORLD,&rank);MPI_Comm_size(MPI_COMM_WORLD,&N);try{
 F::init();if(argc<3)throw std::runtime_error("check|prove input-directory [output-directory]");
 pa::validate_parties(N);
 keccak_load(argv[2]);if(keccak_size()%size_t(N))throw std::runtime_error("Keccak table must be divisible by N");std::string command=argv[1];
 if(command=="check"){keccak_check_reduction(N);}
 else if(command=="prove"){
  unsigned seed;if(getrandom(&seed,sizeof(seed),0)!=sizeof(seed))throw std::runtime_error("fresh seed");srand(seed);
  data_parallel=true;
  if(rank==0){printf("{\"event\":\"native_keccak_diagnostic\",\"standalone_verifier_available\":false,\"formal_measurement\":false}\n");fflush(stdout);}
  coPIOP_prove(keccak_size(),N,N/2,N/4,2);
  if(rank==0){printf("{\"event\":\"native_keccak_prover_returned\",\"full_proof_verified\":false}\n");fflush(stdout);}
 }else throw std::runtime_error("unknown Keccak command");
 MPI_Finalize();return 0;
 }catch(const std::exception&e){fprintf(stderr,"Keccak_INPUT_REJECT: %s\n",e.what());MPI_Abort(MPI_COMM_WORLD,2);return 2;}}
