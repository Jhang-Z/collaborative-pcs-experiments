"""Run fresh, bounded cases; retain failures and export only public measurements."""
import csv
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import threading
import time

from resources import ancestors, discover, memory_snapshot


def systemd_manager():
    """Use the system manager for root, the current user's manager otherwise."""
    if not shutil.which('systemd-run') or not shutil.which('systemctl'):
        raise RuntimeError('systemd with cgroup v2 is required; see README environment requirements')
    options = [] if os.geteuid() == 0 else ['--user']
    target = 'multi-user.target' if os.geteuid() == 0 else 'default.target'
    result = subprocess.run(['systemctl', *options, 'is-active', target],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError('A working systemd manager is required to enforce RAM/no-swap limits. '
            'Use a normal SSH login on a systemd host, or run as root; see README.')
    return options


def admit_service(cfg):
    actual = discover(cfg['reserve_fraction'], exclude_current_cgroup=True)
    cfg['memory_budget_bytes'] = min(cfg['memory_budget_bytes'], actual['memory_budget_bytes'])
    subprocess.run(['systemctl', *cfg['manager'], 'set-property', '--runtime', cfg['unit'],
        'MemoryMax=' + str(cfg['memory_budget_bytes']), 'MemorySwapMax=0'], check=True)
    admitted = memory_snapshot()
    if admitted.get('memory.max') != cfg['memory_budget_bytes'] or admitted.get('memory.swap.max') != 0:
        raise RuntimeError('Actual service memory/swap enforcement does not match the detected budget')
    cfg['actual_service_capacity'] = actual
    return actual


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def prepare_inputs(root, run, selected):
    from keccak_oracle import outputs
    path = run / 'private/inputs'
    path.mkdir(parents=True, mode=0o700)
    pcs = [x['size'] for x in selected if x['kind'].endswith('pcs')]
    if pcs:
        raw = hashlib.shake_256(b'collab-pcs-experiments/2026-10-23/pcs-input/v1').digest((1 << max(pcs))//8)
        (path / 'pcs-bits.bin').write_bytes(raw)
    sizes = [x['size'] for x in selected if not x['kind'].endswith('pcs')]
    if sizes:
        data = os.urandom(max(sizes)*200)
        private = path / 'private-input.bin'
        private.write_bytes(data); private.chmod(0o600)
        (path / 'public-output.bin').write_bytes(outputs(data))
        save(path / 'contract.json', dict(application='Keccak-f[1600]/256', rounds=24,
            instances=max(sizes), private_bytes_per_instance=200, public_bytes_per_instance=32,
            public_bit_order='byte-lsb-first', full_proof_verified=False))
        exporter = root / 'experiments/benchmarks-2026-10-23/keccak-baselines-20261029/export_pappas.py'
        for size in sorted({x['size'] for x in selected if x['kind'] == 'native-keccak'}):
            with (path / f'export-{size}.log').open('x') as log:
                subprocess.run([sys.executable, str(exporter), '--inputs', str(path),
                    '--instances', str(size), '--out', str(path / ('pappas-' + str(size)))],
                    stdout=log, stderr=subprocess.STDOUT, check=True)


def case(root, run, label):
    from backend import execute_job, CommandFailed
    plan = json.loads((run / 'plan.json').read_text())
    job = next(x for x in plan['jobs'] if x['label'] == label)
    runtime = json.loads((run / 'private/runtime.json').read_text())
    cfg = json.loads((run / 'private/case-resources' / (label + '.json')).read_text())
    # A transient service can have different ancestors from its launcher/session.
    # Recheck inside the actual service, excluding its own provisional leaf limit.
    actual = admit_service(cfg)
    save(run / 'private/case-resources' / (label + '.json'), cfg)
    os.sched_setaffinity(0, set(cfg['progress_cpus']))
    phase, stop = ['starting'], threading.Event()
    samples = run / 'public/resources' / (label + '.jsonl')
    samples.parent.mkdir(parents=True, exist_ok=True)

    def observe():
        os.sched_setaffinity(0, {cfg['progress_cpus'][0]})
        with samples.open('x') as stream:
            while True:
                stream.write(json.dumps(dict(monotonic_s=time.monotonic(), phase=phase[0],
                    **memory_snapshot())) + '\n'); stream.flush()
                if stop.wait(1):
                    break

    observer = threading.Thread(target=observe, daemon=True)
    observer.start()
    result = dict(job, passed=False, formal_performance=plan['performance_sample'],
                  origin_run=run.name, time_adjustments=False)
    start = time.monotonic()
    try:
        result.update(execute_job(root, run, job, runtime, cfg, plan['config'],
                                 cfg['timeout_seconds'], lambda value: phase.__setitem__(0, value)))
        result['passed'] = True
    except Exception as error:
        result['error'] = dict(type=type(error).__name__, phase=phase[0])
        if isinstance(error, CommandFailed):
            result['error']['returncode'] = error.code
    finally:
        stop.set(); observer.join()
    result['execution_wall_s'] = time.monotonic() - start
    resource = memory_snapshot()
    before = {x['path']: x['events'] for x in actual['cgroup_ancestors']}
    ancestor_deltas = {x['path']: {key: x['events'].get(key, 0) - before[x['path']].get(key, 0)
        for key in ['max', 'oom', 'oom_kill']} for x in ancestors(exclude_current=True)
        if x['path'] in before}
    result['resources'] = dict(budget_bytes=cfg['memory_budget_bytes'], enforcement='cgroup-v2-systemd',
        compute_cpu=cfg['compute_cpu'], progress_cpus=cfg['progress_cpus'], final=resource,
        actual_service_capacity=actual, ancestor_event_deltas=ancestor_deltas)
    events = resource.get('memory.events', {})
    result['resource_admitted'] = (
        resource.get('memory.max') == cfg['memory_budget_bytes'] and
        resource.get('memory.swap.max') == 0 and
        resource.get('memory.peak', cfg['memory_budget_bytes']) < cfg['memory_budget_bytes'] and
        all(events.get(key, -1) == 0 for key in ['max', 'oom', 'oom_kill']) and
        all(value == 0 for counts in ancestor_deltas.values() for value in counts.values()) and
        resource.get('memory.swap.peak', resource.get('memory.swap.current', -1)) == 0)
    if not result['resource_admitted']:
        result['passed'] = False
        result.setdefault('error', dict(type='ResourceAdmissionFailed', phase=phase[0]))
    save(run / 'public/cases' / (label + '.json'), result)
    print(json.dumps(dict(label=label, passed=result['passed'],
                          resource_admitted=result['resource_admitted'])), flush=True)
    return 0 if result['passed'] else 1


def summarize(run, state):
    rows, stages = [], []
    for record in state['cases']:
        if not record['passed']:
            continue
        for name, timing in record['timing'].items():
            rows.append(dict(label=record['label'], kind=record['kind'], size=record['size'],
                N=record['N'], network=name, groups=';'.join(record['groups']),
                repetition=record['repetition'], full_proof_verified=record['full_proof_verified'],
                **{key: timing[key] for key in ['online_s', 'compute_critical_s',
                    'network_increment_s', 'transmitted_bytes']},
                memory_peak_bytes=record['resources']['final']['memory.peak'],
                memory_budget_bytes=record['resources']['budget_bytes'], origin_run=run.name))
        trace = run / 'public/traces' / record['label'] / 'coordinator.json'
        if trace.exists():
            trace = json.loads(trace.read_text())
            for exchange in trace['exchanges']:
                stages.append(dict(label=record['label'], command=exchange['command'],
                    worker_critical_s=max(exchange['party_ns'])/1e9,
                    coordinator_s=exchange['coordinator_ns']/1e9))
            stages.append(dict(label=record['label'], command='final-serialization',
                worker_critical_s=0, coordinator_s=trace['coordinator_final_ns']/1e9))
    for name, items, header in [('results.csv', rows, ['label', 'kind', 'size', 'N', 'network']),
                                ('stages.csv', stages, ['label', 'command', 'worker_critical_s', 'coordinator_s'])]:
        with (run / 'public' / name).open('w', newline='') as stream:
            writer = csv.DictWriter(stream, fieldnames=list(items[0]) if items else header)
            writer.writeheader(); writer.writerows(items)
    save(run / 'public/results.json', state)
    text = ['# Reproduction run', '', f'Completed: {sum(x["passed"] for x in state["cases"])}/{state["expected"]} configurations.',
        f'Run complete: {state["complete"]}. Performance sample: {state["performance_sample"]}.', '',
        'Computations are measured sequentially on one core; times are causal parallel/network replay estimates.',
        'Private inputs, shares, proofs and their hashes are not included in this public export.',
        'Pappas Keccak reports author-native generation checks; full_proof_verified is false.', '',
        '| Kind | Size | N | Network | Online (s) | Compute (s) | Network increment (s) |',
        '|---|---:|---:|---|---:|---:|---:|']
    for row in rows:
        text.append(f'| {row["kind"]} | {row["size"]} | {row["N"]} | {row["network"]} | '
                    f'{row["online_s"]:.6f} | {row["compute_critical_s"]:.6f} | {row["network_increment_s"]:.6f} |')
    for record in state['cases']:
        if not record['passed']:
            text += ['', 'Failed configuration: ' + record['label'] + '. Inspect its public status and local private logs.']
    (run / 'public/report.md').write_text('\n'.join(text) + '\n')


def export(run):
    public = run / 'public'
    manifest = {str(p.relative_to(public)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(public.rglob('*')) if p.is_file() and p.name != 'manifest.json'}
    save(public / 'manifest.json', manifest)
    with tarfile.open(run / 'results-public.tar.gz', 'w:gz') as archive:
        for path in sorted(public.rglob('*')):
            if path.is_file():
                archive.add(path, arcname=str(path.relative_to(public)))


def execute(root, run, selected, settings, args):
    from bootstrap import prepare
    (run / 'private').mkdir(mode=0o700)
    (run / 'public').mkdir()
    state = dict(complete=False, expected=len(selected), cases=[],
                 performance_sample=not args.smoke, model='causal-fifo-tx-fair-rx-v1')
    save(run / 'public/settings.json', settings)
    save(run / 'public/plan.json', json.loads((run / 'plan.json').read_text()))
    save(run / 'public/source-manifest.json', json.loads((root / 'SOURCE_MANIFEST.json').read_text()))
    save(run / 'public/operations.json', dict(timeout_seconds=args.timeout_seconds,
        reserve_fraction=args.reserve_fraction, requested_memory_gib=args.memory_gib,
        no_install=args.no_install, cpu_policy='one compute core; separate progress cores',
        preprocessing_in_online_time=False, time_adjustments=False))
    lock_path = root / 'build/benchmark.lock'
    lock_path.parent.mkdir(exist_ok=True)
    with lock_path.open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            # Check resources before downloading/compiling expensive dependencies.
            requested = int(args.memory_gib*1024**3) if args.memory_gib is not None else None
            initial = discover(args.reserve_fraction, requested)
            save(run / 'public/resources-initial.json', initial)
            manager = systemd_manager()
            runtime = prepare(root, {x['kind'] for x in selected}, install=not args.no_install)
            save(run / 'private/runtime.json', runtime)
            save(run / 'public/build-identity.json', dict(
                versions=runtime['versions'], platform=platform.platform(),
                binary_sha256={k: v['binary_sha256'] for k, v in runtime['builds'].items()},
                builds={k: {field: v[field] for field in
                    ['identity', 'rustflags', 'locked', 'measurement_hooks', 'ram_stream_prepare', 'xkcp']
                    if field in v} for k, v in runtime['builds'].items()},
                cpu_features=runtime['inspection']['cpu_features'],
                toolchains_config_sha256=runtime['toolchains_config_sha256'],
                dependency_config_sha256=runtime['dependency_config_sha256'],
                dependency_identities=runtime['dependencies'],
                mpi_library_sha256=runtime.get('mpi_library_sha256'),
                source_manifest_sha256=hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()))
            prepare_inputs(root, run, selected)
            for job in selected:
                state['running'] = job['label']; save(run / 'public/state.json', state)
                cfg = discover(args.reserve_fraction, requested)
                cfg['timeout_seconds'] = args.timeout_seconds
                unit = 'collab-artifact-' + hashlib.sha256((str(run) + job['label']).encode()).hexdigest()[:20]
                cfg.update(unit=unit, manager=manager)
                save(run / 'private/case-resources' / (job['label'] + '.json'), cfg)
                argv = ['systemd-run', *manager, '--wait', '--collect', '--quiet', '--pipe',
                    '--unit=' + unit, '-p', 'MemoryMax=' + str(cfg['memory_budget_bytes']),
                    '-p', 'MemorySwapMax=0', '-p', 'TasksMax=infinity',
                    '-p', 'RuntimeMaxSec=' + str(8*args.timeout_seconds + 120),
                    'taskset', '-c', ','.join(map(str, cfg['allowed_cpus'])),
                    sys.executable, str(root / 'scripts/campaign.py'), str(run), job['label']]
                for variable in ['XDG_RUNTIME_DIR', 'DBUS_SESSION_BUS_ADDRESS']:
                    if variable in os.environ:
                        argv.insert(1, '--setenv=' + variable + '=' + os.environ[variable])
                print(f'Running {job["label"]}, RAM budget {cfg["memory_budget_bytes"]/1024**3:.2f} GiB', flush=True)
                with (run / 'private' / (job['label'] + '-unit.log')).open('x') as log:
                    code = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT).returncode
                path = run / 'public/cases' / (job['label'] + '.json')
                record = json.loads(path.read_text()) if path.exists() else dict(job,
                    passed=False, result_missing=True, error={'type': 'CaseTerminatedBeforeResult'})
                record['unit_returncode'] = code
                record['passed'] = record['passed'] and code == 0
                save(path, record); state['cases'].append(record)
                state.pop('running', None)
                save(run / 'public/state.json', state); summarize(run, state); export(run)
                if not record['passed']:
                    raise RuntimeError('Case failed; retained original failure and stopped: ' + job['label'])
            state['complete'] = True
        except Exception as error:
            state['error'] = str(error)
            raise
        finally:
            save(run / 'public/state.json', state)
            summarize(run, state)
            export(run)
            print(f'Public data: {run / "public/results.csv"}\nBundle: {run / "results-public.tar.gz"}', flush=True)


if __name__ == '__main__':
    directory, label = sys.argv[1:]
    raise SystemExit(case(Path(__file__).resolve().parents[1], Path(directory), label))
