"""Detect, provision and build the fixed proof implementations on Linux.

No benchmark is launched here. Tool and dependency caches stay inside the
artifact; accepted host tools are reused without changing system defaults.
"""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request


KINDS = {'ours-app', 'ours-pcs', 'native-baseline', 'native-pcs', 'native-keccak'}
BENCH = Path('experiments/benchmarks-2026-10-23')


def sha(path):
    with Path(path).open('rb') as stream:
        result = hashlib.file_digest(stream, 'sha256') if hasattr(hashlib, 'file_digest') else None
        if result is not None:
            return result.hexdigest()
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
        return digest.hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def output(argv, env=None):
    result = subprocess.run(list(map(str, argv)), env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    return result.returncode, result.stdout.strip()


def version(text):
    match = re.search(r'(?<!\d)(\d+)\.(\d+)(?:\.(\d+))?', text)
    return tuple(map(int, match.groups(default='0'))) if match else ()


def tool(path, arguments=('--version',)):
    if not path:
        return {'path': None, 'available': False, 'version': None}
    code, text = output([path, *arguments])
    return {'path': str(Path(path).absolute()), 'available': code == 0,
            'version': list(version(text)), 'description': text.splitlines()[0] if text else ''}


def os_release():
    path = Path('/etc/os-release')
    return dict(line.split('=', 1) for line in path.read_text().splitlines()
                if '=' in line) if path.exists() else {}


def inspect_environment(root: Path) -> dict:
    """Read-only inventory; unsupported platforms are returned as diagnostics."""
    root = Path(root).resolve()
    allowed = sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else []
    flags = set()
    cpu = Path('/proc/cpuinfo')
    if cpu.exists():
        # A migratable process must be safe on every allowed CPU.
        sets = []
        for block in cpu.read_text().split('\n\n'):
            fields = dict(line.split(':', 1) for line in block.splitlines() if ':' in line)
            fields = {key.strip(): value.strip() for key, value in fields.items()}
            if fields.get('processor', '').isdigit() and int(fields['processor']) in allowed:
                sets.append(set(fields.get('flags', fields.get('Features', '')).split()))
        flags = set.intersection(*sets) if sets else set()
    tools = {name: tool(shutil.which(name)) for name in
             ['git', 'curl', 'gcc', 'g++', 'make', 'cmake', 'mpicxx', 'mpirun', 'cargo', 'rustc']}
    errors = []
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'amd64'):
        errors.append('The complete artifact requires Linux x86_64; inspection is supported here.')
    if sys.version_info < (3, 10):
        errors.append('Python 3.10 or newer is required.')
    if platform.system() == 'Linux' and 'avx2' not in flags:
        errors.append('Pappas requires AVX2. SHA-NI is reported but is not required: the active hash path selects XKCP SHA3.')
    if platform.system() == 'Linux' and len(allowed) < 2:
        errors.append('The unchanged MPI tracer needs separate compute and progress CPUs (at least two allowed CPUs).')
    return {'platform': platform.system(), 'architecture': platform.machine(),
            'python': sys.executable, 'python_version': list(sys.version_info[:3]),
            'allowed_cpus': allowed, 'cpu_features': sorted(flags),
            'os_release': {k: v.strip('"') for k, v in os_release().items()
                           if k in ('ID', 'ID_LIKE', 'VERSION_ID')},
            'tools': tools, 'supported': not errors, 'errors': errors,
            'capabilities': {
                'linux_x86_64': platform.system() == 'Linux' and platform.machine() in ('x86_64', 'amd64'),
                'python_supported': sys.version_info >= (3, 10),
                'pappas_avx2': 'avx2' in flags,
                'mpi_separate_progress_cpu': len(allowed) >= 2,
                'sha_ni_required': False}}


def run(argv, log, env=None, cwd=None):
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('a') as stream:
        stream.write(json.dumps({'argv': list(map(str, argv)), 'cwd': str(cwd) if cwd else None}) + '\n')
        stream.flush()
        result = subprocess.run(list(map(str, argv)), cwd=cwd, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Build/setup command failed ({result.returncode}); see {log}')


def download(url, target, expected=None, checksum_url=None):
    if not url.startswith('https://'):
        raise ValueError('Only HTTPS dependency downloads are supported')
    if checksum_url:
        with urllib.request.urlopen(checksum_url, timeout=60) as response:
            lines = response.read().decode().splitlines()
        filename = url.rsplit('/', 1)[1]
        matches = [line.split()[0] for line in lines if line.split()
                   and line.split()[-1].lstrip('*') == filename]
        if len(matches) != 1 or not re.fullmatch('[0-9a-fA-F]{64}', matches[0]):
            raise RuntimeError(f'No unique SHA256 for {filename} in the publisher checksum file')
        expected = matches[0].lower()
    if not expected:
        raise ValueError('An expected SHA256 is required')
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists() and sha(target) == expected:
        return expected
    temporary = target.with_suffix(target.suffix + '.partial')
    with urllib.request.urlopen(url, timeout=60) as source, temporary.open('wb') as destination:
        shutil.copyfileobj(source, destination)
    if sha(temporary) != expected:
        temporary.unlink()
        raise RuntimeError(f'SHA256 mismatch for {url}')
    temporary.replace(target)
    return expected


def unpack(archive, destination):
    destination.mkdir(parents=True, exist_ok=True)
    base = destination.resolve()
    with tarfile.open(archive) as stream:
        for item in stream.getmembers():
            target = (base / item.name).resolve()
            if not target.is_relative_to(base):
                raise ValueError('Unsafe archive member')
            if item.issym() or item.islnk():
                link = (target.parent / item.linkname).resolve() if item.issym() else (base / item.linkname).resolve()
                if not link.is_relative_to(base):
                    raise ValueError('Unsafe archive link')
        stream.extractall(base)


def apt_install(packages, root, log):
    distro = os_release()
    family = (distro.get('ID', '') + ' ' + distro.get('ID_LIKE', '')).replace('"', '').split()
    if not {'debian', 'ubuntu'} & set(family) or not shutil.which('apt-get'):
        raise RuntimeError('Automatic system-package installation supports Debian/Ubuntu; install ' + ', '.join(packages))
    if os.geteuid() == 0:
        prefix = []
    elif shutil.which('sudo'):
        if output(['sudo', '-n', 'true'])[0] == 0:
            prefix = ['sudo', '-n']
        elif sys.stdin.isatty():
            # sudo reads its password from the controlling terminal. It is
            # never passed through this program, argv, stdin pipes or logs.
            prefix = ['sudo']
        else:
            raise RuntimeError('System setup needs an interactive terminal. Run: sudo apt-get update && sudo apt-get install --no-install-recommends --no-upgrade -y ' + ' '.join(packages))
    else:
        raise RuntimeError('Missing system packages require root or passwordless sudo: ' + ', '.join(packages))
    run([*prefix, 'apt-get', 'update'], log)
    # Install only absent packages or explicitly versioned parallel compilers;
    # never issue upgrade or change compiler alternatives.
    run([*prefix, 'apt-get', 'install', '--no-install-recommends', '--no-upgrade', '-y', *packages], log)


def compiler_tools(root, config, install, log):
    minimum = config['compiler']['minimum_major']
    selected = None
    for suffix in ['', *('-' + str(x) for x in config['compiler']['parallel_majors'])]:
        cc, cxx = shutil.which('gcc' + suffix), shutil.which('g++' + suffix)
        if cc and cxx and version(output([cxx, '-dumpfullversion'])[1]) >= (minimum, 0, 0):
            selected = (cc, cxx)
            break
    missing = [name for name in ['git', 'make'] if not shutil.which(name)]
    if not selected:
        if not install:
            raise RuntimeError('A GNU C/C++ compiler version >=9 is required (--no-install was set)')
        major = config['compiler']['install_major']
        missing += [f'gcc-{major}', f'g++-{major}']
    if missing:
        if not install:
            raise RuntimeError('Missing tools: ' + ', '.join(missing))
        apt_install(missing, root, log)
    if not selected:
        major = config['compiler']['install_major']
        selected = (shutil.which(f'gcc-{major}'), shutil.which(f'g++-{major}'))
    if not all(selected):
        raise RuntimeError('Compiler installation did not provide the selected parallel compiler')
    return tuple(str(Path(path).resolve()) for path in selected)


def cmake_tool(root, config, install):
    existing = shutil.which('cmake')
    detected = version(output([existing, '--version'])[1]) if existing else ()
    if (3, 10, 0) <= detected < (4, 0, 0):
        return existing
    spec = config['cmake']
    prefix = root / '.toolchains' / ('cmake-' + spec['isolated_version'])
    binary = prefix / 'bin/cmake'
    if not binary.exists():
        if not install:
            raise RuntimeError('CMake 3.10–3.x is required (--no-install was set)')
        archive = root / '.toolchains/downloads' / spec['url'].rsplit('/', 1)[1]
        download(spec['url'], archive, checksum_url=spec['checksums_url'])
        with tempfile.TemporaryDirectory(dir=root / '.toolchains') as temporary:
            unpack(archive, Path(temporary))
            shutil.move(Path(temporary) / ('cmake-' + spec['isolated_version'] + '-linux-x86_64'), prefix)
    if version(output([binary, '--version'])[1]) != tuple(map(int, spec['isolated_version'].split('.'))):
        raise RuntimeError('Isolated CMake version mismatch')
    return str(binary)


def rust_tools(root, config, install, log):
    wanted = config['rust']['version']
    expected = tuple(map(int, wanted.split('.')))
    cargo, rustc = shutil.which('cargo'), shutil.which('rustc')
    if cargo and rustc and version(output([rustc, '--version'])[1]) == expected and version(output([cargo, '--version'])[1]) == expected:
        return cargo, rustc
    rustup = shutil.which('rustup')
    if rustup:
        cc, cp = output([rustup, 'which', '--toolchain', wanted, 'cargo'])
        rc, rp = output([rustup, 'which', '--toolchain', wanted, 'rustc'])
        if cc == rc == 0 and version(output([rp, '--version'])[1]) == expected:
            return cp, rp
    spec = config['rust']
    prefix = root / '.toolchains' / ('rust-' + wanted)
    cargo, rustc = prefix / 'bin/cargo', prefix / 'bin/rustc'
    if not cargo.exists() or not rustc.exists():
        if not install:
            raise RuntimeError(f'Rust {wanted} is required (--no-install was set)')
        archive = root / '.toolchains/downloads' / spec['url'].rsplit('/', 1)[1]
        download(spec['url'], archive, checksum_url=spec['url'] + '.sha256')
        with tempfile.TemporaryDirectory(dir=root / '.toolchains') as temporary:
            unpack(archive, Path(temporary))
            distribution = next(Path(temporary).iterdir())
            run([distribution / 'install.sh', '--prefix=' + str(prefix), '--disable-ldconfig',
                 '--without=rust-docs'], log)
    if version(output([rustc, '--version'])[1]) != expected or version(output([cargo, '--version'])[1]) != expected:
        raise RuntimeError('Isolated Rust/Cargo version mismatch')
    return str(cargo), str(rustc)


def mpi_tools(root, config, install, cc, cxx, jobs, log):
    mpirun, mpicxx = shutil.which('mpirun'), shutil.which('mpicxx')
    if mpirun and mpicxx:
        text = output([mpirun, '--version'])[1]
        wrapper = output([mpicxx, '--showme:version'])[1]
        includes = output([mpicxx, '--showme:incdirs'])[1].split()
        headers = any((Path(directory) / 'mpi.h').is_file() for directory in includes)
        if ('Open MPI' in text and version(text)[:1] in ((4,), (5,))
                and 'Open MPI' in wrapper and version(wrapper)[:1] == version(text)[:1] and headers):
            return mpirun, mpicxx
    spec = config['openmpi']
    prefix = root / '.toolchains' / ('openmpi-' + spec['isolated_version'])
    if not (prefix / 'bin/mpicxx').exists():
        if not install:
            raise RuntimeError('Open MPI 4.x/5.x with development headers is required (--no-install was set)')
        archive = root / '.toolchains/downloads' / spec['url'].rsplit('/', 1)[1]
        download(spec['url'], archive, spec['sha256'])
        source = root / '.toolchains' / ('openmpi-' + spec['isolated_version'] + '-source')
        if not source.exists():
            with tempfile.TemporaryDirectory(dir=root / '.toolchains') as temporary:
                unpack(archive, Path(temporary))
                shutil.move(next(Path(temporary).iterdir()), source)
        environment = dict(os.environ, CC=cc, CXX=cxx)
        run([source / 'configure', '--prefix=' + str(prefix), '--disable-mpi-fortran',
             '--disable-oshmem', '--with-libevent=internal', '--with-hwloc=internal',
             '--with-pmix=internal', '--without-verbs', '--without-ucx'], log, environment, source)
        run(['make', '-j' + str(jobs)], log, environment, source)
        run(['make', 'install'], log, environment, source)
    return str(prefix / 'bin/mpirun'), str(prefix / 'bin/mpicxx')


def dependency(root, name, spec, log):
    if not spec['url'].startswith('https://'):
        raise ValueError('Fixed dependency sources require HTTPS URLs')
    if not re.fullmatch('[0-9a-fA-F]{40}', spec['commit']):
        raise ValueError('Fixed dependency sources require a full immutable Git commit')
    destination = root / spec['directory']
    metadata = json.loads((root / spec['file_manifest']).read_text())
    manifest = metadata.get('files', metadata)
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = destination.with_name(destination.name + '.checkout')
        if temporary.exists():
            raise RuntimeError(f'Incomplete dependency checkout exists: {temporary}; inspect/remove it before retrying')
        environment = dict(os.environ, GIT_TERMINAL_PROMPT='0')
        run(['git', 'clone', '--no-checkout', '--filter=blob:none', spec['url'], temporary], log, environment)
        run(['git', '-C', temporary, 'fetch', '--depth=1', 'origin', spec['commit']], log, environment)
        run(['git', '-C', temporary, 'checkout', '--detach', spec['commit']], log, environment)
        if output(['git', '-C', temporary, 'rev-parse', 'HEAD'])[1] != spec['commit']:
            raise RuntimeError('Dependency commit mismatch: ' + name)
        temporary.rename(destination)
    for path, expected in manifest.items():
        file = destination / path
        if not file.is_file() or sha(file) != expected:
            raise RuntimeError(f'Fixed dependency file mismatch: {name}/{path}')
    if (destination / '.git').exists() and output(['git', '-C', destination, 'rev-parse', 'HEAD'])[1] != spec['commit']:
        raise RuntimeError('Dependency checkout is at a different commit: ' + name)
    return destination, {'commit': spec['commit'], 'file_manifest_sha256': sha(root / spec['file_manifest']),
                         'verified_files': len(manifest)}


def files_manifest(directory):
    return {str(path.relative_to(directory)): sha(path) for path in sorted(directory.rglob('*'))
            if path.is_file() and '.git' not in path.relative_to(directory).parts}


def pappas_source(root, vendor, kind, destination):
    """Same source transformations as the active adapters, plus optional timing hooks."""
    if destination.exists():
        raise RuntimeError('Pappas source staging requires a fresh destination')
    shutil.copytree(vendor, destination, ignore=shutil.ignore_patterns('.git', 'build', 'CMakeFiles', '*.o', 'fft_gkr'))
    adapter = root / BENCH / 'baseline-pappas/adapter'
    src = destination / 'src'
    shutil.copy2(adapter / 'parameters.hpp', src / 'parameters.hpp')
    if kind == 'native-pcs':
        for name in ['pcs_adapter.hpp', 'pcs_proof.hpp']:
            shutil.copy2(adapter / name, src / name)
        shutil.copy2(adapter / 'pcs_main.cpp', src / 'main.cpp')
    else:
        local = root / BENCH / 'keccak-baselines-20261029/pappas'
        for name in ['keccak_input.h', 'keccak_input.cpp', 'stream_prepare.hpp', 'stream_prepare.cpp', 'stream_shares.hpp']:
            shutil.copy2(local / name, src / name)
        shutil.copy2(local / 'keccak_main.cpp', src / 'main.cpp')

        def hook(file, signature, body):
            path = src / file
            text = path.read_text()
            assert text.count(signature) == 1, (file, signature)
            path.write_text('#include "keccak_input.h"\n' + text.replace(signature, signature + '\n' + body))

        hook('MPI_utils.cpp', 'void distribute_index(int N, int M,vector<sparse_eval_data> &index, int type){',
             '    if(keccak_active()){ keccak_index(); return; }')
        hook('MPI_utils.cpp', 'void distribute_proving_data(vector<F> &vL, vector<F> &vR, vector<F> &vO, vector<F> &w, int N, int M, int _k, int k, int cir_type){',
             '    if(keccak_active() && getenv("PAPPAS_PREPARE_BUFFER_BYTES")){ keccak_distribute_proving_data(vL,vR,vO,w,N,M,_k,k); return; }')
        path = src / 'MPI_utils.cpp'
        text = '#include "stream_prepare.hpp"\n' + path.read_text()
        before = '2*((1<<logn) + 3*(1<<logm))/k'
        assert text.count(before) == 1
        path.write_text(text.replace(before, '2*((size_t(1)<<logn) + 3*(size_t(1)<<logm))/k'))
        hook('utils.cpp', 'void prepare_witness_data(size_t size, vector<F> &witness, vector<F> &vL, vector<F> &vR, vector<F> &vO, int type){',
             '    if(keccak_active()){ keccak_witness(witness,vL,vR,vO); return; }')
        hook('Distributed_Sumcheck.cpp', 'void _reduce_R1CS_matrixes(size_t size, vector<F> r, vector<F> &RA, vector<F> &RB, vector<F> &RC, int N){',
             '    if(keccak_active()){ keccak_reduce(r,RA,RB,RC,N); return; }')
        path = src / 'coPIOP.cpp'
        text = '#include "keccak_input.h"\n' + path.read_text()
        for call in ['init_dummy_index_commitment(index,index_data,index_codeword,index_Com,index_rate,N);',
                     'init_dummy_index_commitment(index,batch_row_data[2],batch_codewords[2],batch_MT[2],index_rate,N);']:
            assert call in text
            text = text.replace(call, 'if(!keccak_active()) ' + call)
        before = '    pt_cp.reset();\n    pt.start();'
        assert text.count(before) == 2
        text = text.replace(before, '\n'.join([
            '    if(keccak_active()){ int sr; MPI_Comm_rank(MPI_COMM_WORLD,&sr);',
            '        if(sr==0){ printf("{\\\"event\\\":\\\"online_start\\\"}\\n"); fflush(stdout); } }', before]))
        before = '    pt_cpu.end();\n    MPI_Barrier(MPI_COMM_WORLD);'
        assert text.count(before) == 2
        text = text.replace(before, before + '\n' + '\n'.join([
            '    if(keccak_active()){ double local=pt.get_time(), maximum=0;',
            '        MPI_Allreduce(&local,&maximum,1,MPI_DOUBLE,MPI_MAX,MPI_COMM_WORLD);',
            '        if(rank==0){ printf("{\\\"event\\\":\\\"online_complete\\\",\\\"max_rank_seconds\\\":%.9f}\\n",maximum); fflush(stdout); } }']))
        path.write_text(text)
    path = src / 'merkle_tree.cpp'
    text = path.read_text()
    before = 'data[j+32] = hashes[lvl-1][ i * 2].arr[j];'
    assert text.count(before) == 1
    path.write_text(text.replace(before, 'data[j+32] = hashes[lvl-1][ i * 2 + 1].arr[j];'))
    path = src / ('pcs_proof.hpp' if kind == 'native-pcs' else 'coPIOP.cpp')
    text = path.read_text()
    if kind == 'native-pcs':
        before = 'auto start=std::chrono::steady_clock::now();online_payload=0;'
        assert text.count(before) == 1
        text = text.replace(before, 'if(simtrace_begin) simtrace_begin();' + before)
        before = 'MPI_Barrier(MPI_COMM_WORLD);double secs='
        assert text.count(before) == 1
        text = text.replace(before, 'if(simtrace_end) simtrace_end();' + before)
    else:
        before = '    pt.start();'
        assert text.count(before) == 2
        text = text.replace(before, '    if(simtrace_begin) simtrace_begin();\n' + before)
        before = '    pt.end();\n    pt_cpu.end();'
        assert text.count(before) == 2
        text = text.replace(before, '    pt.end();\n    if(simtrace_end) simtrace_end();\n    pt_cpu.end();')
    path.write_text('extern "C" void simtrace_begin() __attribute__((weak));\nextern "C" void simtrace_end() __attribute__((weak));\n' + text)
    return files_manifest(destination)


def prepare(root: Path, kinds: set[str], install: bool = True) -> dict:
    root = Path(root).resolve()
    if not kinds or not kinds <= KINDS:
        raise ValueError('Unknown or empty implementation selection')
    inspection = inspect_environment(root)
    capabilities = inspection['capabilities']
    if not capabilities['linux_x86_64'] or not capabilities['python_supported']:
        raise RuntimeError('The selected implementations require Linux x86_64 and Python >=3.10.')
    if kinds & {'native-pcs', 'native-keccak'}:
        if not capabilities['pappas_avx2']:
            raise RuntimeError('The selected Pappas implementation requires AVX2 (SHA-NI is not required).')
        if not capabilities['mpi_separate_progress_cpu']:
            raise RuntimeError('The selected MPI tracer requires at least two allowed CPUs.')
    build = root / 'build'
    build.mkdir(exist_ok=True)
    with (build / '.bootstrap.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        config = json.loads((root / 'configs/toolchains.json').read_text())
        dependencies = json.loads((root / 'third_party/dependencies.json').read_text())
        log = build / 'bootstrap.log'
        cc, cxx = compiler_tools(root, config, install, log)
        # Limit compilation using current available RAM, independently of the
        # benchmark memory policy. This never assumes a 256 GiB host.
        memory = next((int(line.split()[1]) * 1024 for line in Path('/proc/meminfo').read_text().splitlines()
                       if line.startswith('MemAvailable:')), 1 << 30)
        spec = importlib.util.spec_from_file_location('artifact_bootstrap_resources', Path(__file__).with_name('resources.py'))
        resources = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(resources)
        constraints = []
        cg = resources.current_cgroup()
        while cg is not None:
            maximum_file = cg / 'memory.max'
            if maximum_file.exists() and maximum_file.read_text().strip() != 'max':
                constraints.append(max(0, int(maximum_file.read_text()) - int((cg / 'memory.current').read_text())))
            if cg == Path('/sys/fs/cgroup'):
                break
            cg = cg.parent
        memory = resources.budget_bytes(memory, constraints)
        jobs = max(1, min(len(inspection['allowed_cpus']), memory // (2 << 30), 4))
        environment = dict(os.environ, CC=cc, CXX=cxx, RAYON_NUM_THREADS='1', OMP_NUM_THREADS='1',
                           RUSTFLAGS='-C target-cpu=native', CARGO_BUILD_JOBS=str(jobs))
        for name in ['CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_TARGET', 'RUSTC_WRAPPER',
                     'RUSTC_WORKSPACE_WRAPPER', 'CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS']:
            environment.pop(name, None)
        versions = {'cc': tool(cc), 'cxx': tool(cxx), 'python': platform.python_version()}
        runtime = {'binaries': {}, 'python': sys.executable, 'versions': versions,
                   'inspection': inspection, 'build_jobs': jobs, 'dependencies': {}, 'builds': {}}
        rust_kinds = kinds & {'ours-app', 'ours-pcs', 'native-baseline'}
        if rust_kinds:
            cargo, rustc = rust_tools(root, config, install, log)
            versions.update(cargo=tool(cargo), rustc=tool(rustc))
            environment.update(RUSTC=rustc, CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=cc)
            _, runtime['dependencies']['binius64'] = dependency(root, 'binius64', dependencies['binius64'], log)
            for kind, directory, binary in [
                ('ours-app', 'collaborative-snark', 'ours-fullnet'),
                ('ours-pcs', 'collaborative-pcs', 'ours-pcs'),
                ('native-baseline', 'keccak-native', 'binius64-keccak-zk-bench')]:
                if kind not in kinds:
                    continue
                source = root / BENCH / directory
                source_hashes = files_manifest(source)
                core = files_manifest(root / 'experiments/implementations/protocol-core')
                identity = hashlib.sha256(json.dumps([source_hashes, core, runtime['dependencies'], versions,
                                                     environment['RUSTFLAGS'], inspection['cpu_features']], sort_keys=True).encode()).hexdigest()
                target = build / 'cache' / identity / kind
                executable = target / 'release' / binary
                record_file = target / 'artifact-build.json'
                if not record_file.exists() or not executable.exists() or json.loads(record_file.read_text()).get('binary_sha256') != sha(executable):
                    run([cargo, 'build', '--release', '--locked', '--manifest-path', source / 'Cargo.toml',
                         '--target-dir', target, '-j', str(jobs)], log, environment, source)
                    save(record_file, {'identity': identity, 'binary_sha256': sha(executable)})
                runtime['binaries'][kind] = str(executable)
                runtime['builds'][kind] = {'identity': identity, 'source_files': source_hashes,
                    'shared_core_source_sha256': hashlib.sha256(json.dumps(core, sort_keys=True).encode()).hexdigest(),
                    'binary_sha256': sha(executable), 'rustflags': environment['RUSTFLAGS'], 'locked': True}
        native_kinds = kinds & {'native-pcs', 'native-keccak'}
        if native_kinds:
            cmake = cmake_tool(root, config, install)
            mpirun, mpicxx = mpi_tools(root, config, install, cc, cxx, jobs, log)
            versions.update(cmake=tool(cmake), mpirun=tool(mpirun), mpicxx=tool(mpicxx))
            environment.update(OMPI_CC=cc, OMPI_CXX=cxx)
            runtime['mpirun'] = str(Path(mpirun).absolute())
            vendor, runtime['dependencies']['pappas'] = dependency(root, 'pappas', dependencies['pappas'], log)
            for kind in sorted(native_kinds):
                with tempfile.TemporaryDirectory(prefix='source-check-', dir=build) as temporary:
                    source = Path(temporary) / 'source'
                    manifest = pappas_source(root, vendor, kind, source)
                    checks = config['formal_source_hashes'][kind]
                    for name, expected in checks.items():
                        if manifest[name] != expected:
                            raise RuntimeError(f'Pappas transformation differs from the measured source: {kind}/{name}')
                    identity = hashlib.sha256(json.dumps([manifest, versions, inspection['cpu_features']], sort_keys=True).encode()).hexdigest()
                    work = build / 'cache' / identity / kind
                    staged = work / 'source'
                    if not staged.exists():
                        work.mkdir(parents=True, exist_ok=True)
                        shutil.move(source, staged)
                    elif files_manifest(staged) != manifest:
                        raise RuntimeError('Cached Pappas build source was modified: ' + str(staged))
                target = work / 'cmake'
                executable = target / 'src/pigeon'
                record_file = work / 'artifact-build.json'
                if not record_file.exists() or not executable.exists() or json.loads(record_file.read_text()).get('binary_sha256') != sha(executable):
                    run([cmake, '-S', staged, '-B', target, '-DCMAKE_BUILD_TYPE=Release',
                         '-DCMAKE_C_COMPILER=' + cc, '-DCMAKE_CXX_COMPILER=' + cxx,
                         '-DMPI_CXX_COMPILER=' + str(mpicxx)], log, environment)
                    run([cmake, '--build', target, '-j' + str(jobs)], log, environment)
                    save(record_file, {'identity': identity, 'binary_sha256': sha(executable)})
                runtime['binaries'][kind] = str(executable)
                runtime['builds'][kind] = {'identity': identity, 'source_files': manifest,
                    'binary_sha256': sha(executable), 'measurement_hooks': True,
                    'ram_stream_prepare': kind == 'native-keccak',
                    'xkcp': {'scope': 'precompiled archive supplied by the fixed Pappas commit; not rebuilt from source',
                             'sha256': sha(staged / 'lib/libXKCP.a')}}
            library_id = hashlib.sha256((sha(root / 'scripts/mpi_trace.cpp') + json.dumps(versions, sort_keys=True)).encode()).hexdigest()
            library = build / 'cache' / library_id / 'mpi-trace.so'
            library_record = library.with_suffix('.json')
            if (not library.exists() or not library_record.exists()
                    or json.loads(library_record.read_text()).get('binary_sha256') != sha(library)):
                library.parent.mkdir(parents=True, exist_ok=True)
                run([mpicxx, '-std=c++17', '-O2', '-fPIC', '-shared', root / 'scripts/mpi_trace.cpp',
                     '-o', library, '-pthread'], log, environment)
                save(library_record, {'identity': library_id, 'binary_sha256': sha(library)})
            runtime['mpi_library'] = str(library)
            runtime['mpi_library_sha256'] = sha(library)
        else:
            runtime.update(mpirun=None, mpi_library=None)
        runtime['toolchains_config_sha256'] = sha(root / 'configs/toolchains.json')
        runtime['dependency_config_sha256'] = sha(root / 'third_party/dependencies.json')
        runtime['environment'] = {'OMPI_CC': cc, 'OMPI_CXX': cxx, 'OMP_NUM_THREADS': '1', 'RAYON_NUM_THREADS': '1'}
        save(build / 'runtime.json', runtime)
        return runtime


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--inspect', action='store_true', help='read-only environment inventory; no downloads or builds')
    parser.add_argument('--kinds', nargs='+', choices=sorted(KINDS), default=sorted(KINDS))
    parser.add_argument('--no-install', action='store_true', help='reuse installed tools only; fixed source dependencies may still download')
    args = parser.parse_args()
    result = inspect_environment(args.root) if args.inspect else prepare(args.root, set(args.kinds), not args.no_install)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
