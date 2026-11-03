"""Matched XOR3/AND tasks using the native general unit-entry interface.

Native field wires encode bits by S=1-2b. No general index/auxiliary
authentication, field arithmetic, proof parameters, or protocol is replaced.
"""
from pathlib import Path
import argparse
import hashlib
import json
import struct

ONE=(1<<64)-1
TASKS={'linear_feedback','xor_and_regular','xor_and_random','xor_and_random50'}

def satisfied(rows,w):
    return w[0]==1 and all(sum(w[i] for i in a)*sum(w[i] for i in b)==sum(w[i] for i in c) for a,b,c in rows)

def build(graph,bits):
    if graph['task'] not in TASKS or len(bits)!=graph['inputs'] or any(b not in (0,1) for b in bits):
        raise ValueError('task or Boolean inputs')
    w=[1]+[1-2*b for b in bits]
    logical=list(range(1,len(w)))
    rows=[([i],[i],[0]) for i in logical]
    for gate in graph['gates']:
        left=gate['left'];right=gate['right']
        if len(left) not in (1,2,3) or any(not 0<=i<len(logical) for i in left) or not(right==ONE or 0<=right<len(logical)):
            raise ValueError('XOR/AND gate references')
        u=logical[left[0]]
        for index in left[1:]:
            v=logical[index];t=len(w);w.append(w[u]*w[v]);rows.append(([u],[v],[t]));u=t
        if right!=ONE:
            d=logical[right]
            t=len(w);w.append(w[u]*w[d]);rows.append(([u],[d],[t]))
            z=len(w);w.append(1-2*(((1-w[u])//2)&((1-w[d])//2)))
            rows.append(([z,z,t],[0],[0,u,d]));u=z
        logical.append(u)
    last=logical[-1];output=(1-w[last])//2
    public=len(w);w.append(w[last]);rows.append(([last],[0],[public]))
    assert satisfied(rows,w) and output in (0,1)
    return rows,w,output

def export(graph_path,input_path,out):
    graph=json.loads(Path(graph_path).read_text());bits=list(Path(input_path).read_bytes())
    rows,w,output=build(graph,bits)
    padded=1;minimum=(graph['max_parties']//4)*512
    while padded<max(len(rows),len(w),minimum):padded*=2
    out=Path(out);out.mkdir(parents=True,exist_ok=False)
    relation=bytearray(b'PNXOR001'+struct.pack('<QQQ',len(rows),len(w),padded))
    for row in rows:
        for lc in row:
            relation.extend(struct.pack('<Q',len(lc)))
            for index in lc:relation.extend(struct.pack('<Q',index))
    (out/'relation.bin').write_bytes(relation)
    (out/'witness.bin').write_bytes(b'PNXORW01'+struct.pack('<Q',len(w))+bytes(2 if x==-1 else x for x in w))
    (out/'public-output.bin').write_bytes(bytes([output]))
    metadata=dict(task=graph['task'],inputs=graph['inputs'],gates=len(graph['gates']),
        nonlinear_gates=sum(g['right']!=ONE for g in graph['gates']),logical_rows=len(rows),
        native_wires=len(w),native_padded=padded,max_parties=graph['max_parties'],public_output=output,
        graph_sha256=hashlib.sha256(Path(graph_path).read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(bytes(bits)).hexdigest(),encoding='signs-positive-unit-entries',
        matrix_terms=sum(len(lc) for row in rows for lc in row))
    (out/'application.json').write_text(json.dumps(metadata,indent=2)+'\n')
    return metadata

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--graph',type=Path,required=True);p.add_argument('--input',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();print(json.dumps(export(a.graph,a.input,a.out)))
