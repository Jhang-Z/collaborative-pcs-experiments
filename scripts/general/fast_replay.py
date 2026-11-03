"""Exact compiled execution of the existing analysis model; no prover data spill.

Serialize already validated Graph.nodes once, solve zero/LAN/WAN in one process.
The temporary binary contains only analysis node/resource/dependency metadata.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
FLAGS=['-std=c++17','-O2','-fno-fast-math','-ffp-contract=off']
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def build_engine():
    source=ROOT/'fast_model.cpp';digest=sha(source)
    cache=Path(tempfile.gettempdir())/('sp-general-fast-replay-'+digest)
    cache.mkdir(exist_ok=True);binary=cache/'fast_model';record=cache/'build.json'
    if not binary.exists():
        compiler=shutil.which('c++')
        if not compiler:raise RuntimeError('C++17 compiler not found')
        with tempfile.TemporaryDirectory(dir=cache)as work:
            target=Path(work)/'fast_model';command=[compiler,*FLAGS,str(source),'-o',str(target)]
            subprocess.run(command,check=True)
            identity={'source_sha256':digest,'binary_sha256':sha(target),'compile_command':command,'compiler':subprocess.check_output([compiler,'--version'],text=True).splitlines()[0]}
            os.replace(target,binary)
            record.write_text(json.dumps(identity,indent=2)+'\n')
    identity=json.loads(record.read_text())
    assert identity['source_sha256']==digest and identity['binary_sha256']==sha(binary)
    identity.update(binary=str(binary),bridge_sha256=sha(Path(__file__)),analysis_graph_format='GFREPL01')
    return binary,identity

def write_graph(graph,path,scenarios):
    """Explicit little endian: magic,u32 scenarios,u64 nodes,pairs; each node
    u8 kind,f64 seconds,i64 cpu/src/dst,u64 size,u64 deps,then u64 dependency IDs.
    """
    kinds={'local':0,'flow':1,'latency':2};node=struct.Struct('<BdqqqQQ')
    with Path(path).open('wb',buffering=1024*1024)as f:
        f.write(b'GFREPL01');f.write(struct.pack('<IQ',len(scenarios),len(graph.nodes)))
        for rate,latency in scenarios:f.write(struct.pack('<dd',rate,latency))
        for item in graph.nodes:
            deps=sorted(item['deps'])
            ids=[-1 if item.get(key)is None else item[key]for key in ['cpu','src','dst']]
            f.write(node.pack(kinds[item['kind']],item['seconds'],*ids,item['size'],len(deps)))
            if deps:f.write(struct.pack('<'+'Q'*len(deps),*deps))

def simulate_many(graph,scenarios,engine=None):
    if engine is None:engine,_=build_engine()
    with tempfile.TemporaryDirectory(prefix='sp-analysis-graph-')as work:
        path=Path(work)/'graph.bin';write_graph(graph,path,scenarios)
        values=[float(x)for x in json.loads(subprocess.check_output([str(engine),str(path)],text=True))]
    assert len(values)==len(scenarios)and all(math.isfinite(x)and x>=0 for x in values)
    return values

def replay_pair(graph,engine=None):
    """Same v2 result schema and inputs; run the engine only once for both networks."""
    binary,identity=build_engine()if engine is None else (Path(engine),{'binary_sha256':sha(engine),'compiler':'external engine; build flags not attested'})
    zero,lan,wan=simulate_many(graph,[(math.inf,0.),(10.*1e9/8,2./2000),(.2*1e9/8,50./2000)],binary)
    def result(total,gbps,rtt):
        data=dict(online_s=total,compute_critical_s=zero,zero_network_s=zero,network_increment_s=total-zero,transmitted_bytes=graph.payload,gbps=gbps,rtt_ms=rtt,model='causal-fifo-cpu-tx-fair-rx-v2',actor_cpu_map=graph.cpu_map)
        if hasattr(graph,'logical_sent'):data.update(logical_sent_bytes=graph.logical_sent,physical_sent_bytes=graph.network_sent,physical_received_bytes=graph.network_received,challenge_stages=graph.challenges)
        return data
    return {'LAN':result(lan,10.,2.),'WAN':result(wan,.2,50.),'engine':identity}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--trace',type=Path,required=True);parser.add_argument('--output',type=Path);args=parser.parse_args()
    from general.replay import read_graph
    text=json.dumps(replay_pair(read_graph(args.trace)),indent=2)+'\n'
    if args.output:args.output.write_text(text)
    else:print(text,end='')
