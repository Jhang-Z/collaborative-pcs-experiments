"""Random XOR/AND reproduction using the frozen general-circuit implementations.

Only explicitly selected measurement fields and payload-free traces are exported.
Private inputs, native witnesses, proof files and their hashes remain local.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

from general.frontend import export as native_export
from general.budget520 import evaluate
from general.replay import read_graph
from general.fast_replay import replay_pair


def read(path):
    return json.loads(path.read_text())


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def oracle(graph, bits):
    """Evaluate the exact two-input Boolean graph without the prover frontend."""
    if len(bits) != graph['inputs'] or any(b not in (0, 1) for b in bits):
        raise ValueError('invalid Boolean input')
    values, xors = bytearray(bits), 0
    for gate in graph['gates']:
        left, right = gate['left'], gate['right']
        xor = right == 2**64 - 1
        if len(left) != (2 if xor else 1) or any(i < 0 or i >= len(values) for i in left):
            raise ValueError('invalid gate')
        if xor:
            values.append(values[left[0]] ^ values[left[1]]); xors += 1
        else:
            if right < 0 or right >= len(values):
                raise ValueError('invalid AND reference')
            values.append(values[left[0]] & values[right])
    return values[-1], xors, len(graph['gates']) - xors


def execute(root, run, job, runtime, resources, settings, timeout, set_phase, command_wall_s):
    from backend import CommandFailed
    work = run / 'private' / job['label']; work.mkdir(mode=0o700)
    kind, n, gates = job['kind'], job['N'], job['size']
    params = settings['parameters']
    if params != dict(gamma=520, tau=4, index_block_bits=3, seed=42):
        raise ValueError('random50 uses the frozen gamma520/tau4/b3/seed42 configuration')
    if settings['networks'] != {'LAN': {'bandwidth_gbps': 10, 'rtt_ms': 2},
                               'WAN': {'bandwidth_gbps': .2, 'rtt_ms': 50}}:
        raise ValueError('random50 replay requires the declared LAN/WAN scenarios')
    cpu = ['taskset', '-c', str(resources['compute_cpu'])]
    environment = dict(os.environ, **runtime.get('environment', {}))
    environment.update(GENERAL_COMPUTE_CPU=str(resources['compute_cpu']),
                       OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1',
                       OMPI_ALLOW_RUN_AS_ROOT='1', OMPI_ALLOW_RUN_AS_ROOT_CONFIRM='1')

    def call(phase, command, check=True):
        set_phase(phase); start = time.monotonic()
        path = work / (phase + '.log')
        try:
            with path.open('x') as log:
                result = subprocess.run(list(map(str, command)), stdout=log,
                    stderr=subprocess.STDOUT, timeout=timeout, env=environment)
        finally:
            command_wall_s[phase] = time.monotonic() - start
        text = path.read_text(errors='replace')
        if check and (result.returncode or re.search(r'SIM_TRACE_REJECT|NAND_REJECT|Circuit too small|wrong timer', text)):
            raise CommandFailed(phase, result.returncode or 1)
        return result.returncode, text

    # Each N uses its natural layout, with the same graph seed and canonical input.
    # This preparation is also inside the case cgroup, outside the online trace.
    source = work / 'input'
    capacity = 16 if kind == 'binius-general' else n
    ours = runtime['binaries']['ours-general']
    call('generate', [*cpu, ours, 'general-input', '--task', 'xor-and-random50',
        '--gates', gates, '--seed', 42, '--max-parties', capacity, '--out', source])
    graph = read(source / 'circuit.json')
    canonical = run / 'private/inputs' / f'random50-{gates}-r{job["repetition"]}'
    if not canonical.exists():
        canonical.mkdir()
        for name in ['input.private', 'statement.json']:
            shutil.copy2(source / name, canonical / name)
        # A public graph shape digest is distinct from the private input digest.
        save(canonical / 'graph.json', dict(inputs=graph['inputs'], gates=graph['gates']))
    else:
        if read(canonical / 'graph.json') != dict(inputs=graph['inputs'], gates=graph['gates']):
            raise ValueError('logical graph changed across schemes or N')
        for name in ['input.private', 'statement.json']:
            shutil.copy2(canonical / name, source / name)
    output, xors, ands = oracle(graph, (source / 'input.private').read_bytes())
    if graph['inputs'] != gates//16 or len(graph['gates']) != gates or output != read(source / 'statement.json')[1]:
        raise ValueError('independent graph/input/output check failed')
    result = dict(inputs=graph['inputs'], xor_gates=xors, and_gates=ands,
        same_logical_graph=True, same_input=True, independent_boolean_oracle=True,
        public_output=output, gamma=520, tau=4, index_block_bits=3,
        max_prover_peak_rss_bytes=None, full_proof_verified=kind != 'native-general')
    binary, proof, trace = runtime['binaries'][kind], work / 'proof', work / 'trace'
    if kind == 'ours-general':
        call('prove', [*cpu, binary, 'general', '--task', 'xor-and-random50', '--gates', gates,
            '--seed', 42, '--max-parties', n, '--parties', n, '--gamma', 520, '--tau', 4,
            '--index-block-bits', 3, '--input', source / 'input.private', '--trace', trace, '--out', proof])
        control = read(proof / 'control.json')
        if (not control['verified_after_decode'] or control['public'] != read(source / 'statement.json')
                or digest(proof / 'circuit.json') != digest(source / 'circuit.json')
                or control['trace']['challenges'] != control['parameters']['expected_challenge_stages']):
            raise ValueError('proof identity or trace coverage failed')
        # Run the verifier from a directory containing public verifier inputs only.
        public_verify = work / 'public-verifier'; public_verify.mkdir()
        for name in ['proof.bin', 'verifier-key.bin', 'statement.json']:
            shutil.copy2(proof / name, public_verify / name)
        command = [*cpu, binary, 'general-verify', '--out', public_verify]
        call('verify', command)
        original = (public_verify / 'proof.bin').read_bytes()
        mutated = bytearray(original); mutated[len(mutated)//2] ^= 1
        (public_verify / 'proof.bin').write_bytes(mutated)
        code, _ = call('negative-proof', command, check=False)
        if code == 0:
            raise ValueError('mutated proof accepted')
        (public_verify / 'proof.bin').write_bytes(original)
        statement = read(public_verify / 'statement.json'); statement[1] = not statement[1]
        save(public_verify / 'statement.json', statement)
        code, _ = call('negative-output', command, check=False)
        if code == 0:
            raise ValueError('wrong public output accepted')
        shutil.copy2(proof / 'statement.json', public_verify / 'statement.json')
        call('restored-verification', command)
        result.update(proof_bytes=len(original), verify_s=control['verify_wall_seconds'],
            public_only_verification=True, mutated_proof_rejected=True, wrong_output_rejected=True,
            budget=evaluate(control['parameters']), proof_format=control['proof_format'])
    elif kind == 'native-general':
        native = work / 'native'; meta = native_export(source / 'circuit.json', source / 'input.private', native)
        if meta['public_output'] != output or meta['graph_sha256'] != digest(source / 'circuit.json') or meta['input_sha256'] != digest(source / 'input.private'):
            raise ValueError('native frontend identity mismatch')
        mpi = [runtime['mpirun'], '--oversubscribe', '--bind-to', 'none', '--mca', 'mpi_yield_when_idle', '1', '-np', n]
        _, text = call('native-relation-check', [*mpi, binary, 'check', native])
        if 'native_xor_relation_checked' not in text:
            raise ValueError('native relation check missing')
        trace.mkdir()
        cfg = dict(binary=binary, argv=['prove', str(native)], library=runtime['mpi_library'],
            trace=str(trace), token='/random50-' + uuid.uuid4().hex,
            compute_cpu=resources['compute_cpu'], progress_cpus=resources['progress_cpus'],
            dealer_cpu=resources['progress_cpus'][0], initial_worker_cpus=resources['progress_cpus'],
            prepare_buffer_bytes=67108864)
        save(work / 'rank-config.json', cfg)
        _, text = call('prove', [*mpi, sys.executable, root / 'scripts/general/timing_rank.py', work / 'rank-config.json'])
        if 'native_general_prover_returned' not in text or not all(re.search(r'Phase\s+' + str(i) + r'(?:\D|$)', text) for i in range(1, 8)):
            raise ValueError('native generation did not complete all seven phases')
        layouts = [json.loads(line) for line in text.splitlines() if line.startswith('{')]
        layouts = [x for x in layouts if x.get('event') in ['compact_static_layout', 'compact_aux_layout']]
        if len(layouts) != 2 or any(x['encoded_local_coefficients'] != x['author_pow2'] for x in layouts):
            raise ValueError('native compact layout changed')
        reported = re.search(r'Vt : ([0-9.]+) sec, Ps: ([0-9.]+) KB', text)
        memory = [read(p) for p in trace.glob('memory-*.json')]
        if not reported or len(memory) != n:
            raise ValueError('native statistics missing')
        result.update(proof_bytes=float(reported[2])*1024, verify_s=float(reported[1]),
            proof_verify_scope='native internal statistics; no exported full proof independent verification',
            embedded_generation_checks=True, max_prover_peak_rss_bytes=max(x['peak_rss_bytes'] for x in memory))
    else:
        args = [*cpu, binary, '--graph', source / 'circuit.json', '--out', proof, '--mode', 'preserved-graph']
        call('prove', [*args, '--input', source / 'input.private', '--runs', 1, '--single'])
        call('verify', [*args, '--verify-only'])
        data, checks = read(proof / 'result.json'), read(proof / 'independent-verify.json')
        if (data['logical_nodes'] != gates or data['public_output'] != output
                or data['graph_sha256'] != digest(source / 'circuit.json')
                or data['input_sha256'] != digest(source / 'input.private')
                or len(data['records']) != 1 or data['records'][0]['warmup']
                or not all(checks[k] for k in ['public_only_accept', 'wrong_output_rejected', 'mutated_proof_rejected'])):
            raise ValueError('Binius independent verification or task identity failed')
        sample = data['records'][0]
        result.update(proof_bytes=sample['proof_bytes'], verify_s=checks['verify_s'],
            parameters=data['parameters'], single_core_s=sample['online_s'],
            timing={'single-core': dict(online_s=sample['online_s'], compute_critical_s=sample['online_s'],
                network_increment_s=0, transmitted_bytes=0)}, public_only_verification=True,
            mutated_proof_rejected=True, wrong_output_rejected=True)
        return result
    headers = [json.loads(p.open().readline()) for p in trace.glob('rank-*.jsonl')]
    if len(headers) != n + (kind == 'ours-general'):
        raise ValueError('incomplete trace ranks')
    if kind == 'ours-general':
        valid = all(h['clock'] == 'CLOCK_THREAD_CPUTIME_ID' for h in headers)
    else:
        valid = all(h['compute_clock'] == 'CLOCK_THREAD_CPUTIME_ID' and h['compute_cpu'] == resources['compute_cpu']
                    and not h['includes_os_descheduling'] for h in headers)
    if not valid:
        raise ValueError('incorrect compute clock or affinity')
    graph = read_graph(trace); timings = replay_pair(graph)
    result.update(timing={k: timings[k] for k in ['LAN', 'WAN']}, total_TX_bytes=graph.payload)
    public_trace = run / 'public/traces' / job['label']; public_trace.mkdir(parents=True)
    # The frozen trace writers emit timings, sizes and dependencies, never payloads.
    for pattern in ['rank-*.jsonl', 'phase-*.json', 'memory-*.json']:
        for path in trace.glob(pattern):
            shutil.copy2(path, public_trace / path.name)
    return result
