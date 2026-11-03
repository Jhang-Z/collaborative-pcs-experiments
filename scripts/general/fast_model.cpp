// Exact C++17 execution of replay.simulate; input is an analysis DAG, never prover state.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <deque>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <queue>
#include <stdexcept>
#include <unordered_map>
#include <vector>
using Id=uint64_t;
static_assert(sizeof(double)==8&&std::numeric_limits<double>::is_iec559,"IEEE binary64 required");
struct Node { double seconds; uint64_t size; int cpu,src,dst; uint8_t kind; };
struct Reader {
    std::ifstream f;
    explicit Reader(const char* path):f(path,std::ios::binary) {}
    uint64_t integer(unsigned bytes) { unsigned char b[8]; f.read(reinterpret_cast<char*>(b),bytes); if(!f)throw std::runtime_error("short graph");uint64_t x=0;for(unsigned i=0;i<bytes;i++)x|=uint64_t(b[i])<<(8*i);return x; }
    double real(){uint64_t x=integer(8);double y;std::memcpy(&y,&x,8);return y;}
};
struct Graph {
    std::vector<Node> nodes;
    std::vector<Id> needed,offset,children;
    std::vector<std::pair<double,double>> scenarios;
    size_t ncpu=0,nnic=0;
    explicit Graph(const char* path) {
        Reader r(path); if(r.integer(8)!=0x31304c5045524647ULL)throw std::runtime_error("graph magic");
        uint32_t runs=r.integer(4);Id n=r.integer(8);for(uint32_t i=0;i<runs;i++){double rate=r.real(),latency=r.real();scenarios.emplace_back(rate,latency);}
        nodes.resize(n);needed.resize(n);offset.assign(n+1,0);
        std::unordered_map<int64_t,int> cpus,nics;std::vector<std::pair<Id,Id>> edges;
        auto key=[](auto& map,int64_t value){if(value<0)return -1;auto p=map.emplace(value,int(map.size()));return p.first->second;};
        for(Id i=0;i<n;i++) {
            auto& x=nodes[i];x.kind=r.integer(1);x.seconds=r.real();x.cpu=key(cpus,int64_t(r.integer(8)));x.src=key(nics,int64_t(r.integer(8)));x.dst=key(nics,int64_t(r.integer(8)));x.size=r.integer(8);needed[i]=r.integer(8);
            if(x.kind>2||!std::isfinite(x.seconds)||x.seconds<0)throw std::runtime_error("node values");
            for(Id j=0;j<needed[i];j++){Id source=r.integer(8);if(source>=n||source==i)throw std::runtime_error("dependency");edges.emplace_back(source,i);++offset[source+1];}
        }
        if(r.f.peek()!=EOF)throw std::runtime_error("trailing graph data");
        for(Id i=0;i<n;i++)offset[i+1]+=offset[i];children.resize(edges.size());auto cursor=offset;
        // Input targets are ascending, exactly matching Python's children[source].append(target).
        for(auto edge:edges)children[cursor[edge.first]++]=edge.second;
        ncpu=cpus.size();nnic=nics.size();
    }
    double solve(double rate,double latency)const {
        if(!(rate>0&&latency>=0&&std::isfinite(latency)))throw std::runtime_error("network values");
        auto need=needed;std::deque<Id> ready;for(Id i=0;i<nodes.size();i++)if(!need[i])ready.push_back(i);
        using Timer=std::pair<double,Id>;
        std::priority_queue<Timer,std::vector<Timer>,std::greater<Timer>> timers;
        std::vector<std::deque<Id>> queues(nnic),cpus(ncpu);
        std::vector<int> source_order,counts(nnic);std::vector<bool> seen(nnic,false);
        std::vector<double> remaining(nodes.size());Id completed=0;double now=0;
        auto finish=[&](Id i){
            ++completed;const auto& x=nodes[i];
            if(x.cpu>=0&&x.seconds){auto& q=cpus[x.cpu];if(q.empty()||q.front()!=i)throw std::runtime_error("CPU FIFO");q.pop_front();if(!q.empty())timers.emplace(now+nodes[q.front()].seconds,q.front());}
            for(Id j=offset[i];j<offset[i+1];j++){Id target=children[j];if(!--need[target])ready.push_back(target);}
        };
        std::vector<Id> active;std::vector<double> rates;
        const double infinity=std::numeric_limits<double>::infinity();
        while(completed<nodes.size()) {
            while(!ready.empty()) {
                Id i=ready.front();ready.pop_front();const auto& x=nodes[i];
                if(x.kind==1&&x.size&&std::isfinite(rate)) {
                    if(x.src<0||x.dst<0)throw std::runtime_error("NIC id");
                    if(!seen[x.src]){seen[x.src]=true;source_order.push_back(x.src);}
                    queues[x.src].push_back(i);remaining[i]=double(x.size);
                }else {
                    double duration=x.kind==2?latency:x.seconds;
                    if(duration&&x.cpu>=0){auto& q=cpus[x.cpu];q.push_back(i);if(q.size()==1)timers.emplace(now+duration,i);}
                    else if(duration)timers.emplace(now+duration,i);
                    else finish(i);
                }
            }
            if(completed==nodes.size())break;
            active.clear();std::fill(counts.begin(),counts.end(),0);
            // defaultdict insertion order is first-ready-flow order, not numeric NIC order.
            for(int source:source_order)if(!queues[source].empty()){Id i=queues[source].front();active.push_back(i);++counts[nodes[i].dst];}
            rates.resize(active.size());double flow_step=infinity;
            for(size_t j=0;j<active.size();j++){rates[j]=rate/counts[nodes[active[j]].dst];flow_step=std::min(flow_step,remaining[active[j]]/rates[j]);}
            double timer_step=timers.empty()?infinity:std::max(0.,timers.top().first-now);
            double step=std::min(flow_step,timer_step);if(!std::isfinite(step))throw std::runtime_error("cyclic/incomplete trace");
            for(size_t j=0;j<active.size();j++)remaining[active[j]]=std::max(0.,remaining[active[j]]-step*rates[j]);
            now+=step;
            // Finish flows in active-source insertion order before draining timer ties.
            for(Id i:active)if(remaining[i]<=std::max(1e-7,double(nodes[i].size)*1e-12)){auto& q=queues[nodes[i].src];if(q.front()!=i)throw std::runtime_error("TX FIFO");q.pop_front();finish(i);}
            while(!timers.empty()&&timers.top().first<=now+1e-14){Id i=timers.top().second;timers.pop();finish(i);}
        }
        return now;
    }
};
int main(int argc,char**argv) {
    try{if(argc!=2)throw std::runtime_error("usage: fast_model analysis-graph.bin");Graph graph(argv[1]);std::cout<<std::setprecision(17)<<'[';bool comma=false;for(auto scenario:graph.scenarios){if(comma)std::cout<<',';comma=true;std::cout<<graph.solve(scenario.first,scenario.second);}std::cout<<"]\n";return 0;}
    catch(const std::exception& e){std::cerr<<"FAST_REPLAY_REJECT: "<<e.what()<<'\n';return 1;}
}
