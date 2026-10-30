// Optional PMPI measurement layer. Buffers, proof arithmetic and native MPI stay unchanged.
#include <mpi.h>
#include <sched.h>
#include <semaphore.h>
#include <fcntl.h>
#include <unistd.h>
#include <chrono>
#include <cstdio>
#include <cerrno>
#include <cstdlib>
#include <map>
#include <string>
#include <vector>

namespace {
using Clock = std::chrono::steady_clock;
bool active = false;
int rank_id, parties, collective = 0;
long next_request = 0;
sem_t* token = nullptr;
FILE* output = nullptr;
cpu_set_t original_mask, compute_mask, progress_mask;
Clock::time_point checkpoint;
struct Request { MPI_Request native; long id; };
std::map<MPI_Fint, Request> requests;
std::string token_name;

[[noreturn]] void fail(const char* reason) {
    fprintf(stderr, "SIM_TRACE_REJECT: %s\n", reason);
    PMPI_Abort(MPI_COMM_WORLD, 73);
    std::abort();
}
const char* env(const char* name) {
    const char* value = getenv(name);
    if (!value || !*value) fail(name);
    return value;
}
void affinity(const cpu_set_t& mask) {
    if (sched_setaffinity(0, sizeof(mask), &mask)) fail("affinity");
}
void resume() {
    while (sem_wait(token)) if (errno != EINTR) fail("sem_wait");
    affinity(compute_mask);
    checkpoint = Clock::now();
}
long long suspend() {
    auto end = Clock::now();
    long long ns = std::chrono::duration_cast<std::chrono::nanoseconds>(end-checkpoint).count();
    affinity(progress_mask);
    if (sem_post(token)) fail("sem_post");
    return ns;
}
long long bytes(int count, MPI_Datatype type) {
    int size;
    if (count < 0 || PMPI_Type_size(type, &size) != MPI_SUCCESS || size < 0) fail("datatype/count");
    return (long long)count * size;
}
void world(MPI_Comm comm) {
    if (comm != MPI_COMM_WORLD) fail("unsupported communicator");
}
void emit(const char* op, long long ns, const std::string& fields="") {
    fprintf(output, "{\"op\":\"%s\",\"compute_ns\":%lld%s}\n", op, ns, fields.c_str());
    if (fflush(output)) fail("trace write");
}
std::string pair_fields(int peer, int tag, long long size) {
    if (peer < 0 || peer >= parties || tag < 0) fail("wildcard or invalid peer/tag");
    return ",\"peer\":" + std::to_string(peer) + ",\"tag\":" + std::to_string(tag)
         + ",\"bytes\":" + std::to_string(size);
}
int query(void*, MPI_Status* status) {
    status->MPI_SOURCE=MPI_ANY_SOURCE;status->MPI_TAG=MPI_ANY_TAG;status->MPI_ERROR=MPI_SUCCESS;
    int result=PMPI_Status_set_elements(status,MPI_BYTE,0);
    return result==MPI_SUCCESS?PMPI_Status_set_cancelled(status,0):result;
}
int release(void*) { return MPI_SUCCESS; }
int cancel(void*, int) { fail("proxy cancellation unsupported"); }
long remember(MPI_Request* request) {
    if (*request == MPI_REQUEST_NULL) fail("unexpected null post");
    MPI_Request native=*request, proxy;
    if (PMPI_Grequest_start(query,release,cancel,nullptr,&proxy)!=MPI_SUCCESS) fail("request proxy");
    auto key = PMPI_Request_c2f(proxy);
    if (requests.count(key)) fail("proxy reused");
    long id = ++next_request;
    requests[key] = Request{native,id};
    *request=proxy;
    return id;
}
long lookup(MPI_Request request) {
    if (request == MPI_REQUEST_NULL) return 0;
    auto it = requests.find(PMPI_Request_c2f(request));
    if (it == requests.end()) fail("unmatched request");
    return it->second.id;
}
MPI_Request native_request(MPI_Request request) {
    return request==MPI_REQUEST_NULL?MPI_REQUEST_NULL:requests.at(PMPI_Request_c2f(request)).native;
}
void forget(MPI_Request proxy) {
    if (proxy == MPI_REQUEST_NULL) return;
    requests.erase(PMPI_Request_c2f(proxy));
    if (PMPI_Grequest_complete(proxy)!=MPI_SUCCESS || PMPI_Wait(&proxy,MPI_STATUS_IGNORE)!=MPI_SUCCESS)
        fail("dispose request proxy");
}
void success(int code) { if (code != MPI_SUCCESS) fail("native MPI failed"); }
}

extern "C" void simtrace_begin() {
    if (active || output) fail("duplicate begin");
    PMPI_Comm_rank(MPI_COMM_WORLD, &rank_id);
    PMPI_Comm_size(MPI_COMM_WORLD, &parties);
    int cpu = std::stoi(env("SIM_COMPUTE_CPU"));
    if (cpu < 0 || cpu >= CPU_SETSIZE) fail("compute cpu");
    if (sched_getaffinity(0, sizeof(original_mask), &original_mask)) fail("get affinity");
    CPU_ZERO(&compute_mask); CPU_SET(cpu, &compute_mask); CPU_ZERO(&progress_mask);
    std::string list = env("SIM_PROGRESS_CPUS");
    size_t pos = 0;
    do {
        size_t end = list.find(',', pos);
        int item = std::stoi(list.substr(pos, end-pos));
        if (item < 0 || item >= CPU_SETSIZE || item == cpu) fail("progress cpu");
        CPU_SET(item, &progress_mask);
        if (end == std::string::npos) break;
        pos = end+1;
    } while (true);
    token_name = env("SIM_TOKEN_NAME");
    if (rank_id == 0) {
        token = sem_open(token_name.c_str(), O_CREAT|O_EXCL, 0600, 1);
        if (token == SEM_FAILED) fail("fresh token");
    }
    success(PMPI_Barrier(MPI_COMM_WORLD));
    if (rank_id != 0) token = sem_open(token_name.c_str(), 0);
    if (token == SEM_FAILED) fail("open token");
    std::string path = std::string(env("SIM_TRACE_DIR")) + "/rank-" + std::to_string(rank_id) + ".jsonl";
    output = fopen(path.c_str(), "wx");
    if (!output) fail("fresh trace path");
    fprintf(output,"{\"schema\":\"mpi-local-compute-v1\",\"rank\":%d,\"parties\":%d,\"compute_cpu\":%d}\n",rank_id,parties,cpu);
    fflush(output);
    affinity(progress_mask);
    success(PMPI_Barrier(MPI_COMM_WORLD));
    active = true;
    resume();
}
extern "C" void simtrace_end() {
    if (!active) fail("missing begin");
    long long ns = suspend();
    if (!requests.empty()) fail("pending requests at end");
    emit("end", ns);
    active = false;
    fclose(output); output = nullptr;
    sem_close(token);
    success(PMPI_Barrier(MPI_COMM_WORLD));
    if (rank_id == 0) sem_unlink(token_name.c_str());
    affinity(original_mask);
}

extern "C" int MPI_Send(const void* b,int count,MPI_Datatype type,int peer,int tag,MPI_Comm comm) {
    if (!active) return PMPI_Send(b,count,type,peer,tag,comm);
    auto ns=suspend();world(comm);auto fields=pair_fields(peer,tag,bytes(count,type));
    int code=PMPI_Send(b,count,type,peer,tag,comm);success(code);emit("send",ns,fields);resume();return code;
}
extern "C" int MPI_Recv(void* b,int count,MPI_Datatype type,int peer,int tag,MPI_Comm comm,MPI_Status* status) {
    if (!active) return PMPI_Recv(b,count,type,peer,tag,comm,status);
    auto ns=suspend();world(comm);auto fields=pair_fields(peer,tag,bytes(count,type));
    int code=PMPI_Recv(b,count,type,peer,tag,comm,status);success(code);emit("recv",ns,fields);resume();return code;
}
extern "C" int MPI_Isend(const void* b,int count,MPI_Datatype type,int peer,int tag,MPI_Comm comm,MPI_Request* request) {
    if (!active) return PMPI_Isend(b,count,type,peer,tag,comm,request);
    auto ns=suspend();world(comm);auto fields=pair_fields(peer,tag,bytes(count,type));
    int code=PMPI_Isend(b,count,type,peer,tag,comm,request);success(code);
    fields+=",\"request\":"+std::to_string(remember(request));emit("isend",ns,fields);resume();return code;
}
extern "C" int MPI_Irecv(void* b,int count,MPI_Datatype type,int peer,int tag,MPI_Comm comm,MPI_Request* request) {
    if (!active) return PMPI_Irecv(b,count,type,peer,tag,comm,request);
    auto ns=suspend();world(comm);auto fields=pair_fields(peer,tag,bytes(count,type));
    int code=PMPI_Irecv(b,count,type,peer,tag,comm,request);success(code);
    fields+=",\"request\":"+std::to_string(remember(request));emit("irecv",ns,fields);resume();return code;
}
extern "C" int MPI_Wait(MPI_Request* request,MPI_Status* status) {
    if (!active) return PMPI_Wait(request,status);
    auto ns=suspend();auto saved=*request;auto id=lookup(saved);
    auto native=native_request(saved);int code=PMPI_Wait(&native,status);success(code);forget(saved);*request=MPI_REQUEST_NULL;
    emit("wait",ns,",\"requests\":["+std::to_string(id)+"]");resume();return code;
}
extern "C" int MPI_Waitall(int count,MPI_Request* req,MPI_Status* status) {
    if (!active) return PMPI_Waitall(count,req,status);
    auto ns=suspend();
    if (count<0) fail("waitall count");
    std::vector<MPI_Request> saved(req,req+count);std::string ids;
    for(auto q:saved){if(!ids.empty())ids+=",";ids+=std::to_string(lookup(q));}
    std::vector<MPI_Request> native;for(auto q:saved)native.push_back(native_request(q));
    int code=PMPI_Waitall(count,native.data(),status);success(code);
    for(int i=0;i<count;i++){forget(saved[i]);req[i]=MPI_REQUEST_NULL;}
    emit("waitall",ns,",\"requests\":["+ids+"]");resume();return code;
}
extern "C" int MPI_Barrier(MPI_Comm comm) {
    if (!active) return PMPI_Barrier(comm);
    auto ns=suspend();world(comm);int code=PMPI_Barrier(comm);success(code);
    emit("barrier",ns,",\"collective\":"+std::to_string(collective++));resume();return code;
}
extern "C" int MPI_Bcast(void* b,int count,MPI_Datatype type,int root,MPI_Comm comm) {
    if (!active) return PMPI_Bcast(b,count,type,root,comm);
    auto ns=suspend();world(comm);auto size=bytes(count,type);
    int code=PMPI_Bcast(b,count,type,root,comm);success(code);
    emit("bcast",ns,",\"collective\":"+std::to_string(collective++)+",\"root\":"+std::to_string(root)+",\"bytes\":"+std::to_string(size));resume();return code;
}
extern "C" int MPI_Alltoall(const void* s,int sc,MPI_Datatype st,void* r,int rc,MPI_Datatype rt,MPI_Comm comm) {
    if (!active) return PMPI_Alltoall(s,sc,st,r,rc,rt,comm);
    auto ns=suspend();world(comm);auto size=bytes(sc,st);if(size!=bytes(rc,rt))fail("alltoall lengths");
    int code=PMPI_Alltoall(s,sc,st,r,rc,rt,comm);success(code);
    emit("alltoall",ns,",\"collective\":"+std::to_string(collective++)+",\"bytes\":"+std::to_string(size));resume();return code;
}

// These calls are used by setup/reporting, outside the measured native interval.
extern "C" int MPI_Sendrecv(const void* s,int sc,MPI_Datatype st,int dst,int stag,void* r,int rc,MPI_Datatype rt,int src,int rtag,MPI_Comm c,MPI_Status* status){if(active)fail("online Sendrecv unsupported");return PMPI_Sendrecv(s,sc,st,dst,stag,r,rc,rt,src,rtag,c,status);}
extern "C" int MPI_Allgather(const void* s,int sc,MPI_Datatype st,void* r,int rc,MPI_Datatype rt,MPI_Comm c){if(active)fail("online Allgather unsupported");return PMPI_Allgather(s,sc,st,r,rc,rt,c);}
extern "C" int MPI_Gather(const void* s,int sc,MPI_Datatype st,void* r,int rc,MPI_Datatype rt,int root,MPI_Comm c){if(active)fail("online Gather unsupported");return PMPI_Gather(s,sc,st,r,rc,rt,root,c);}
extern "C" int MPI_Allreduce(const void* s,void* r,int n,MPI_Datatype t,MPI_Op op,MPI_Comm c){if(active)fail("online Allreduce unsupported");return PMPI_Allreduce(s,r,n,t,op,c);}
extern "C" int MPI_Reduce(const void* s,void* r,int n,MPI_Datatype t,MPI_Op op,int root,MPI_Comm c){if(active)fail("online Reduce unsupported");return PMPI_Reduce(s,r,n,t,op,root,c);}
extern "C" int MPI_Ialltoall(const void* s,int sc,MPI_Datatype st,void* r,int rc,MPI_Datatype rt,MPI_Comm c,MPI_Request* req){if(active)fail("online Ialltoall unsupported");return PMPI_Ialltoall(s,sc,st,r,rc,rt,c,req);}
extern "C" int MPI_Test(MPI_Request* r,int* f,MPI_Status* s){if(active)fail("online Test unsupported");return PMPI_Test(r,f,s);}
extern "C" int MPI_Testall(int n,MPI_Request* r,int* f,MPI_Status* s){if(active)fail("online Testall unsupported");return PMPI_Testall(n,r,f,s);}
extern "C" int MPI_Testany(int n,MPI_Request* r,int* i,int* f,MPI_Status* s){if(active)fail("online Testany unsupported");return PMPI_Testany(n,r,i,f,s);}
extern "C" int MPI_Testsome(int n,MPI_Request* r,int* c,int* i,MPI_Status* s){if(active)fail("online Testsome unsupported");return PMPI_Testsome(n,r,c,i,s);}
extern "C" int MPI_Request_get_status(MPI_Request r,int* f,MPI_Status* s){if(active)fail("online Request_get_status unsupported");return PMPI_Request_get_status(r,f,s);}
extern "C" int MPI_Waitany(int n,MPI_Request* r,int* i,MPI_Status* s){if(active)fail("online Waitany unsupported");return PMPI_Waitany(n,r,i,s);}
extern "C" int MPI_Waitsome(int n,MPI_Request* r,int* c,int* i,MPI_Status* s){if(active)fail("online Waitsome unsupported");return PMPI_Waitsome(n,r,c,i,s);}
extern "C" int MPI_Request_free(MPI_Request* r){if(active)fail("online Request_free unsupported");return PMPI_Request_free(r);}
extern "C" int MPI_Cancel(MPI_Request* r){if(active)fail("online Cancel unsupported");return PMPI_Cancel(r);}
