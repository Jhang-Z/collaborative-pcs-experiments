"""Discover usable host/container capacity; no server-specific CPU or RAM constants."""
import math
import os
from pathlib import Path


def budget_bytes(host_available, constraints, reserve_fraction=.1, requested=None):
    if not 0 < reserve_fraction < 1:
        raise ValueError('memory reserve fraction must be between zero and one')
    available = min([host_available] + [x for x in constraints if x is not None])
    if available <= 0:
        raise ValueError('no available host/container memory')
    automatic = math.floor(available * (1 - reserve_fraction))
    if requested is not None:
        if requested <= 0 or requested > automatic:
            raise ValueError('requested memory exceeds available capacity after the reserve')
        return requested
    return automatic


def cpu_roles(allowed):
    cpus = sorted(set(allowed))
    if len(cpus) < 2:
        raise ValueError('at least two allowed CPUs are required: measured compute and separate MPI progress')
    return cpus[0], cpus[1:]


def current_cgroup():
    root = Path('/sys/fs/cgroup')
    for line in Path('/proc/self/cgroup').read_text().splitlines():
        if line.startswith('0::'):
            relative = line.split(':', 2)[2].lstrip('/')
            path = root / relative
            # Namespaced containers can expose their cgroup directly as the mount root.
            if '..' not in Path(relative).parts and (path / 'memory.current').exists():
                return path
            if (root / 'memory.current').exists():
                return root
    return None


def ancestors(exclude_current=False):
    result = []
    cg = current_cgroup()
    path = cg.parent if cg is not None and exclude_current else cg
    while path is not None and path.is_relative_to('/sys/fs/cgroup'):
        if (path / 'memory.max').exists():
            maximum = (path / 'memory.max').read_text().strip()
            used = int((path / 'memory.current').read_text())
            events = {k: int(v) for k, v in
                (line.split() for line in (path / 'memory.events').read_text().splitlines())}
            result.append(dict(path=str(path.relative_to('/sys/fs/cgroup')),
                maximum=None if maximum == 'max' else int(maximum), current=used,
                available=None if maximum == 'max' else max(0, int(maximum) - used), events=events))
        if path == Path('/sys/fs/cgroup'):
            break
        path = path.parent
    return result


def discover(reserve_fraction=.1, requested=None, exclude_current_cgroup=False):
    info = {line.split(':')[0]: int(line.split()[1]) * 1024
            for line in Path('/proc/meminfo').read_text().splitlines()
            if line.startswith(('MemTotal:', 'MemAvailable:'))}
    limits = ancestors(exclude_current_cgroup)
    compute, progress = cpu_roles(os.sched_getaffinity(0))
    budget = budget_bytes(info['MemAvailable'], [x['available'] for x in limits],
                          reserve_fraction, requested)
    # Linux memory.max is page-granular; record exactly the value the kernel enforces.
    page = os.sysconf('SC_PAGE_SIZE')
    budget -= budget % page
    if not budget:
        raise ValueError('less than one page of safe available memory')
    return dict(host_total_bytes=info['MemTotal'], host_available_bytes=info['MemAvailable'],
                cgroup_ancestors=limits, reserve_fraction=reserve_fraction,
                memory_budget_bytes=budget, compute_cpu=compute, progress_cpus=progress,
                allowed_cpus=sorted(os.sched_getaffinity(0)))


def memory_snapshot():
    cg = current_cgroup()
    if cg is None:
        return {'enforcement': 'unavailable'}
    result = {}
    for name in ['memory.current', 'memory.peak', 'memory.max', 'memory.swap.current', 'memory.swap.peak', 'memory.swap.max']:
        path = cg / name
        if path.exists():
            value = path.read_text().strip()
            result[name] = value if value == 'max' else int(value)
    for name in ['memory.events', 'memory.stat']:
        values = {k: int(v) for k, v in (line.split() for line in (cg / name).read_text().splitlines())}
        result[name] = values if name == 'memory.events' else {
            k: values[k] for k in ['anon', 'file', 'file_dirty', 'kernel', 'pgscan', 'pgsteal', 'pgmajfault'] if k in values}
    result['memory.pressure'] = (cg / 'memory.pressure').read_text().strip()
    return result
