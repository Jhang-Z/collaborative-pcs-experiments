"""Keep loader/progress overhead outside the native measured compute intervals."""
import json
import os
from pathlib import Path
import sys

cfg = json.loads(Path(sys.argv[1]).read_text())
rank = int(os.environ['OMPI_COMM_WORLD_RANK'])
os.sched_setaffinity(0, {cfg['dealer_cpu']} if rank == 0 else set(cfg['initial_worker_cpus']))
env = dict(os.environ, LD_PRELOAD=cfg['library'], SIM_COMPUTE_CPU=str(cfg['compute_cpu']),
    SIM_PROGRESS_CPUS=','.join(map(str,cfg['progress_cpus'])), SIM_TOKEN_NAME=cfg['token'],
    SIM_TRACE_DIR=cfg['trace'], PAPPAS_PREPARE_BUFFER_BYTES=str(cfg['prepare_buffer_bytes']),
    OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
os.execve(cfg['binary'], [cfg['binary'], *cfg['argv']], env)
