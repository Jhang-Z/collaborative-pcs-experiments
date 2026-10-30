"""Actual proof commands and unchanged causal replay. Private files stay in runs/."""
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
import uuid

from replay import coordinator_graph, mpi_graph, read_mpi, replay


class CommandFailed(RuntimeError):
    def __init__(self, phase, code):
        super().__init__(f'{phase} exited with status {code}; inspect the local private log')
        self.phase, self.code = phase, code


def selected_json(path, keys):
    value = json.loads(path.read_text())
    return {key: value[key] for key in keys if key in value}


def execute_job(root, run, job, runtime, resources, settings, timeout, set_phase):
    work = run / 'private' / job['label']
    work.mkdir(mode=0o700)
    kind, n, size = job['kind'], job['N'], job['size']
    binary = runtime['binaries'][kind]
    inputs = run / 'private' / 'inputs'
    master = inputs / 'private-input.bin'
    expected = (inputs / 'public-output.bin').read_bytes()[:size*32] if not kind.endswith('pcs') else None
    cpu = ['taskset', '-c', str(resources['compute_cpu'])]
    environment = dict(os.environ, **runtime.get('environment', {}))
    environment.update(OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')

    def call(phase, command, check=True, env=None):
        set_phase(phase)
        path = work / (phase + '.log')
        with path.open('x') as stream:
            result = subprocess.run(list(map(str, command)), stdout=stream,
                stderr=subprocess.STDOUT, env=env or environment, timeout=timeout)
        if check and result.returncode:
            raise CommandFailed(phase, result.returncode)
        return result.returncode, path.read_text(errors='replace')

    def corruption_check(proof, command):
        original = proof.read_bytes()
        if not original:
            raise ValueError('empty serialized proof')
        corrupted = bytearray(original)
        corrupted[len(corrupted)//2] ^= 1
        try:
            proof.write_bytes(corrupted)
            code, _ = call('negative', command, check=False)
            if code == 0:
                raise ValueError('corrupted proof was accepted')
        finally:
            proof.write_bytes(original)
        call('restored-verification', command)

    proof = work / 'proof'
    trace = work / 'trace.json'
    auxiliary = {}
    verified = True
    if kind == 'ours-app':
        call('prepare', [*cpu, binary, 'prepare', '--application', 'keccak', '--parties', n,
            '--messages', size, '--input', master, '--out', proof,
            '--gamma', settings['parameters']['gamma'], '--tau', settings['parameters']['tau']])
        call('prove', [*cpu, binary, 'simulate', '--out', proof, '--trace', trace, '--isolate-workers'])
        verify = [*cpu, binary, 'verify', '--out', proof]
        call('verify', verify)
        verification = json.loads((proof / 'verify.json').read_text())
        if not verification['accepted'] or verification['private_input_read']:
            raise ValueError('public verification failed or read private input')
        if (proof / 'statement.bin').read_bytes() != expected:
            raise ValueError('independent Keccak oracle mismatch')
        corruption_check(proof / 'proof.bin', verify)
        for path in proof.glob('*.private'):
            path.unlink()
    elif kind == 'ours-pcs':
        call('prove', [*cpu, binary, 'simulate', '--parties', n, '--log-bits', size,
            '--input', inputs / 'pcs-bits.bin', '--out', proof, '--trace', trace,
            '--gamma', settings['parameters']['gamma'], '--tau', settings['parameters']['tau']])
        verify = [*cpu, binary, 'verify', '--out', proof]
        call('verify', verify)
        if not json.loads((proof / 'verify.json').read_text())['verification']:
            raise ValueError('PCS public verification failed')
        corruption_check(proof / 'proof.bin', verify)
    elif kind == 'native-baseline':
        prepared = work / 'circuit'
        call('prepare', [*cpu, binary, 'prepare', '--messages', size, '--out', prepared])
        call('prove', [*cpu, binary, 'prove', '--messages', size, '--input', master,
            '--prepared', prepared, '--out', proof])
        verify = [*cpu, binary, 'verify', '--messages', size, '--prepared', prepared, '--out', proof]
        call('verify', verify)
        if not json.loads((proof / 'verify.json').read_text())['verification']:
            raise ValueError('native public verification failed')
        if (proof / 'digests.bin').read_bytes() != expected:
            raise ValueError('native independent Keccak oracle mismatch')
        corruption_check(proof / 'proof.bin', verify)
    else:
        trace_dir = work / 'trace'
        trace_dir.mkdir()
        # Match the formal tmpfs preparation boundary; do not silently spill to disk.
        with tempfile.TemporaryDirectory(prefix='collab-artifact-', dir='/dev/shm') as temporary:
            temporary = Path(temporary)
            if kind == 'native-pcs':
                from native_inputs import public_point, evaluate_bits
                private, public = temporary / 'private', temporary / 'public'
                private.mkdir(); public.mkdir()
                point = public_point(size)
                raw = (inputs / 'pcs-bits.bin').read_bytes()[:(1 << size)//8]
                value = evaluate_bits([(b >> i) & 1 for b in raw for i in range(8)], point)
                statement = temporary / 'statement.bin'
                statement.write_bytes(b'PAPST002' + struct.pack('<QQ', n, 1 << size) +
                    b''.join(struct.pack('<QQ', *x) for x in point + [value]))
                call('prepare', [*cpu, binary, 'prepare', inputs / 'pcs-bits.bin', statement, private])
                arguments = ['prove', str(private), str(public)]
            else:
                arguments = ['prove', str(inputs / ('pappas-' + str(size)))]
            rank_config = dict(binary=str(binary), argv=arguments, library=runtime['mpi_library'],
                trace=str(trace_dir), token='/collab-artifact-' + uuid.uuid4().hex,
                compute_cpu=resources['compute_cpu'], progress_cpus=resources['progress_cpus'],
                dealer_cpu=resources['progress_cpus'][0], initial_worker_cpus=resources['allowed_cpus'],
                prepare_buffer_bytes=min(64*1024**2, resources['memory_budget_bytes']//32))
            config_path = work / 'rank-config.json'
            config_path.write_text(json.dumps(rank_config))
            mpi = [runtime['mpirun'], '--oversubscribe', '--bind-to', 'none', '--mca',
                   'mpi_yield_when_idle', '1', '-np', n, sys.executable,
                   root / 'scripts/timing_rank.py', config_path]
            if os.getuid() == 0:
                mpi.insert(1, '--allow-run-as-root')
            _, text = call('prove', mpi)
            if kind == 'native-pcs':
                verify = [*cpu, binary, 'verify', public]
                _, text = call('verify', verify)
                verification = json.loads(text.strip())
                if not verification['accepted'] or not verification['public_only']:
                    raise ValueError('Pappas PCS public verification failed')
                corruption_check(public / 'proof.bin', verify)
                auxiliary['verifier'] = {key: verification[key] for key in
                    ['accepted', 'public_only', 'proof_bytes', 'commitment_bytes',
                     'verification_seconds', 'read_seconds', 'verify_including_read_seconds']}
            else:
                verified = False
                if ('native_keccak_prover_returned' not in text or
                    [int(x) for x in re.findall(r'^Phase (\d+):', text, re.M)] != [1, 2, 3, 4, 7] or
                    re.search(r'error|wrong timer|too small|signal|abort', text, re.I)):
                    raise ValueError('Pappas native generation checks failed')
                auxiliary['unavailable'] = ['independent_full_verifier', 'complete_serialized_proof_size']
        ranks = read_mpi(trace_dir)
        if len(ranks) != n or any(t['compute_cpu'] != resources['compute_cpu'] for t in ranks):
            raise ValueError('incomplete or incorrectly pinned MPI trace')
        graph = mpi_graph(ranks)
        local_compute_ns = sum(e['compute_ns'] for t in ranks for e in t['events'])
        destination = run / 'public/traces' / job['label']
        destination.mkdir(parents=True)
        allowed = {'schema', 'rank', 'parties', 'compute_cpu', 'op', 'compute_ns', 'peer',
                   'tag', 'bytes', 'request', 'requests', 'collective', 'root'}
        for path in trace_dir.glob('rank-*.jsonl'):
            lines = [json.loads(line) for line in path.read_text().splitlines()]
            if any(set(line) - allowed for line in lines):
                raise ValueError('unexpected non-public MPI trace field')
            (destination / path.name).write_text(''.join(json.dumps(x) + '\n' for x in lines))

    if kind.startswith('ours-'):
        raw_trace = json.loads(trace.read_text())
        if raw_trace['parties'] != n:
            raise ValueError('trace party count mismatch')
        public_trace = dict(parties=n, coordinator_final_ns=raw_trace['coordinator_final_ns'],
            exchanges=[{k: x[k] for k in ['command', 'party_ns', 'coordinator_ns',
                       'request_bytes', 'response_bytes']} for x in raw_trace['exchanges']])
        destination = run / 'public/traces' / job['label']
        destination.mkdir(parents=True)
        (destination / 'coordinator.json').write_text(json.dumps(public_trace, indent=2) + '\n')
        graph = coordinator_graph(public_trace)
        local_compute_ns = sum(sum(x['party_ns']) + x['coordinator_ns'] for x in
                               public_trace['exchanges']) + public_trace['coordinator_final_ns']
    if kind in ['ours-app', 'ours-pcs', 'native-baseline']:
        auxiliary['prover'] = selected_json(proof / 'prove.json',
            ['proof_bytes', 'proof_count', 'serialization_ms', 'online_exchange_rounds',
             'complete_proof_format', 'matrix_mode', 'zero_knowledge'])
        auxiliary['verifier'] = selected_json(proof / 'verify.json',
            ['accepted', 'verification', 'verify_ms', 'verify_prepare_ms', 'verify_seconds',
             'preparation_seconds', 'private_input_read', 'private_input_loaded',
             'independent_process', 'proof_bytes'])
    if kind == 'native-baseline':
        record = json.loads((proof / 'prove.json').read_text())
        if not record['zero_knowledge']:
            raise ValueError('native baseline did not generate its zero-knowledge proof')
        seconds = record['online_ms'] / 1000
        times = {'LAN': dict(online_s=seconds, compute_critical_s=seconds,
                            network_increment_s=0, transmitted_bytes=0)}
        local_compute_ns = int(round(seconds * 1e9))
    else:
        times = {name: replay(graph, settings['networks'][name]['bandwidth_gbps'],
            settings['networks'][name]['rtt_ms']) for name in job['networks']}
    return dict(full_proof_verified=verified, proof_generation_completed=True,
        negative_control_passed=True if verified else None, local_compute_ns=local_compute_ns,
        timing=times, auxiliary=auxiliary, dimensions=(
            dict(input_bits=1 << size, workers=n) if kind.endswith('pcs') else
            dict(instances=size, rounds=24, private_bits_per_instance=1600,
                 public_bits_per_instance=256, workers=n)))
