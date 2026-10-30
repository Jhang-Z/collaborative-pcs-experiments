"""Public one-command entry point. Every run has a new directory and manifest."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path

from matrix import jobs

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--groups', nargs='+', choices=['1', '2', '3', '4'])
    parser.add_argument('--instances', nargs='+', type=int)
    parser.add_argument('--config', type=Path, default=ROOT / 'configs/experiments.json')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--plan', action='store_true', help='write the selected job plan; do not install or run proofs')
    parser.add_argument('--check-env', action='store_true', help='inspect the environment without installing')
    parser.add_argument('--smoke', action='store_true', help='small correctness run; never a paper performance sample')
    parser.add_argument('--no-install', action='store_true')
    parser.add_argument('--reserve-fraction', type=float, default=.1)
    parser.add_argument('--memory-gib', type=float)
    parser.add_argument('--timeout-seconds', type=int, default=10800, help='operation watchdog, not a protocol parameter')
    args = parser.parse_args()
    settings = json.loads(args.config.read_text())
    selected = jobs(settings, args.groups, args.instances)
    if not selected:
        parser.error('no configurations match the selection')
    if args.smoke:
        kinds = list(dict.fromkeys(x['kind'] for x in selected))
        selected = [dict(label='smoke-' + kind, kind=kind,
            N=32 if kind == 'ours-app' else (1 if kind == 'native-baseline' else 16),
            size=8 if kind == 'ours-app' else (16 if kind.endswith('pcs') else 2),
            repetition=1, groups=[], networks=list(settings['networks'])) for kind in kinds]
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out = (args.output or ROOT / 'runs' / stamp).resolve()
    if args.check_env:
        from bootstrap import inspect_environment
        report = inspect_environment(ROOT)
        if report['capabilities']['linux_x86_64']:
            from resources import discover, current_cgroup
            from campaign import systemd_manager
            import os
            import shutil
            try:
                report['resources'] = discover(args.reserve_fraction)
                if current_cgroup() is None:
                    raise RuntimeError('cgroup v2 memory controller is unavailable')
                report['systemd_manager'] = 'user' if systemd_manager() else 'system'
                if not shutil.which('taskset'):
                    raise RuntimeError('taskset is required (util-linux)')
                if not os.access('/dev/shm', os.W_OK):
                    raise RuntimeError('/dev/shm is not writable')
            except (RuntimeError, ValueError, OSError) as error:
                report['errors'].append(str(error))
                report['supported'] = False
        print(json.dumps(report, indent=2))
        return
    out.mkdir(parents=True, exist_ok=False)
    (out / 'plan.json').write_text(json.dumps(dict(config=settings, jobs=selected,
        performance_sample=not args.smoke, plan_only=args.plan), indent=2) + '\n')
    if args.plan:
        print(f'Plan only: {len(selected)} unique proof jobs in {out / "plan.json"}')
        return
    from verify_source import verify
    verify(ROOT)
    from campaign import execute
    execute(ROOT, out, selected, settings, args)


if __name__ == '__main__':
    main()
