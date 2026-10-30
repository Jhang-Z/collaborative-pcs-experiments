"""Environment decisions and source integrity, without builds or network jobs."""
import importlib.util
import io
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('artifact_bootstrap_test', ROOT / 'scripts/bootstrap.py')
bootstrap = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(bootstrap)


class ToolVersions(unittest.TestCase):
    def setUp(self):
        self.config = json.loads((ROOT / 'configs/toolchains.json').read_text())

    def test_wrong_rust_version_is_not_silently_accepted_without_install(self):
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(bootstrap.shutil, 'which', side_effect=lambda name: '/tools/' + name if name in ('cargo', 'rustc') else None), \
             patch.object(bootstrap, 'output', return_value=(0, 'rustc 1.99.0')), \
             patch.object(bootstrap, 'run', side_effect=AssertionError('installation was forbidden')):
            with self.assertRaisesRegex(RuntimeError, '1.98.1'):
                bootstrap.rust_tools(Path(temporary), self.config, False, Path(temporary) / 'log')

    def test_cmake4_is_not_silently_used_for_the_pinned_cmake3_path(self):
        with tempfile.TemporaryDirectory() as temporary, \
             patch.object(bootstrap.shutil, 'which', return_value='/tools/cmake'), \
             patch.object(bootstrap, 'output', return_value=(0, 'cmake version 4.3.1')):
            with self.assertRaisesRegex(RuntimeError, 'no-install'):
                bootstrap.cmake_tool(Path(temporary), self.config, False)

    def test_parallel_compiler_is_selected_instead_of_changing_global_defaults(self):
        def locate(name):
            return '/tools/' + name if name in ('gcc', 'g++', 'gcc-12', 'g++-12', 'git', 'make') else None
        def probe(argv, env=None):
            return 0, '12.3.0' if str(argv[0]).endswith('-12') else '8.4.0'
        with patch.object(bootstrap.shutil, 'which', side_effect=locate), \
             patch.object(bootstrap, 'output', side_effect=probe), \
             patch.object(bootstrap, 'apt_install', side_effect=AssertionError('parallel compiler already exists')):
            result = bootstrap.compiler_tools(ROOT, self.config, False, ROOT / 'unused.log')
        self.assertEqual(result, ('/tools/gcc-12', '/tools/g++-12'))


class SourceIntegrity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'cached').mkdir()
        (self.root / 'cached/file.txt').write_text('abc')
        (self.root / 'files.json').write_text(json.dumps({'file.txt':
            'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'}))
        self.spec = {'url': 'https://github.com/example/repository.git',
            'commit': 'a' * 40, 'directory': 'cached', 'file_manifest': 'files.json'}

    def test_verified_source_cache_does_not_need_network(self):
        with patch.object(bootstrap, 'run', side_effect=AssertionError('cache should be reused')):
            directory, identity = bootstrap.dependency(self.root, 'fixture', self.spec, self.root / 'log')
        self.assertEqual(directory, self.root / 'cached')
        self.assertEqual(identity['verified_files'], 1)

    def test_modified_cached_source_is_rejected(self):
        (self.root / 'cached/file.txt').write_text('changed')
        with self.assertRaisesRegex(RuntimeError, 'file mismatch'):
            bootstrap.dependency(self.root, 'fixture', self.spec, self.root / 'log')

    def test_moving_branch_cannot_replace_an_immutable_commit(self):
        self.spec['commit'] = 'main'
        with self.assertRaisesRegex(ValueError, 'commit'):
            bootstrap.dependency(self.root, 'fixture', self.spec, self.root / 'log')

    def test_insecure_source_url_is_rejected_even_for_a_cache(self):
        self.spec['url'] = 'http://github.com/example/repository.git'
        with self.assertRaisesRegex(ValueError, 'HTTPS'):
            bootstrap.dependency(self.root, 'fixture', self.spec, self.root / 'log')

    def test_download_rejects_wrong_hash_and_removes_partial_file(self):
        target = self.root / 'download.tar.gz'
        with patch.object(bootstrap.urllib.request, 'urlopen', return_value=io.BytesIO(b'tampered')):
            with self.assertRaisesRegex(RuntimeError, 'SHA256 mismatch'):
                bootstrap.download('https://example.org/download.tar.gz', target, '0' * 64)
        self.assertFalse(target.exists())
        self.assertFalse(target.with_suffix('.gz.partial').exists())

    def test_archive_cannot_write_outside_its_destination(self):
        archive = self.root / 'source.tar'
        with tarfile.open(archive, 'w') as stream:
            entry = tarfile.TarInfo('../escaped.txt')
            entry.size = 3
            stream.addfile(entry, io.BytesIO(b'bad'))
        with self.assertRaisesRegex(ValueError, 'Unsafe'):
            bootstrap.unpack(archive, self.root / 'unpacked')
        self.assertFalse((self.root / 'escaped.txt').exists())


class RuntimeContract(unittest.TestCase):
    def test_rust_only_prepare_records_binary_without_pappas_cpu_requirements(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'configs').mkdir()
            (root / 'configs/toolchains.json').write_bytes((ROOT / 'configs/toolchains.json').read_bytes())
            source = root / bootstrap.BENCH / 'collaborative-snark'
            source.mkdir(parents=True)
            (source / 'Cargo.toml').write_text('fixture')
            core = root / 'experiments/implementations/protocol-core'
            core.mkdir(parents=True)
            (core / 'Cargo.toml').write_text('shared fixture')
            (root / 'cached').mkdir()
            (root / 'cached/file.txt').write_text('abc')
            (root / 'third_party').mkdir()
            (root / 'third_party/files.json').write_text(json.dumps({'file.txt':
                'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'}))
            (root / 'third_party/dependencies.json').write_text(json.dumps({'binius64': {
                'url': 'https://github.com/example/repository.git', 'commit': 'a' * 40,
                'directory': 'cached', 'file_manifest': 'third_party/files.json'}}))
            original_read = Path.read_text
            def read(path, *args, **kwargs):
                if str(path) == '/proc/meminfo':
                    return 'MemAvailable: 8388608 kB\n'
                if str(path) == '/proc/self/cgroup':
                    return '0::/\n'
                return original_read(path, *args, **kwargs)
            def locate(name):
                return '/tools/' + name if name in ('gcc', 'g++', 'git', 'make', 'cargo', 'rustc') else None
            def external_output(argv, env=None):
                if str(argv[0]).endswith(('cargo', 'rustc')):
                    return 0, Path(argv[0]).name + ' 1.98.1'
                return 0, '12.3.0'
            def external_build(argv, log, env=None, cwd=None):
                self.assertEqual(str(argv[0]), '/tools/cargo')
                self.assertIn('--locked', argv)
                target = Path(argv[argv.index('--target-dir') + 1]) / 'release/ours-fullnet'
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b'fixture binary')
            with patch.object(bootstrap.platform, 'system', return_value='Linux'), \
                 patch.object(bootstrap.platform, 'machine', return_value='x86_64'), \
                 patch.object(bootstrap.os, 'sched_getaffinity', return_value={2}, create=True), \
                 patch.object(Path, 'read_text', read), \
                 patch.object(bootstrap.shutil, 'which', side_effect=locate), \
                 patch.object(bootstrap, 'output', side_effect=external_output), \
                 patch.object(bootstrap, 'run', side_effect=external_build):
                runtime = bootstrap.prepare(root, {'ours-app'}, install=False)
            saved = json.loads((root / 'build/runtime.json').read_text())
            self.assertEqual(saved['binaries'], runtime['binaries'])
            self.assertEqual(set(runtime['binaries']), {'ours-app'})
            self.assertEqual(saved['builds']['ours-app']['binary_sha256'],
                             hashlib.sha256(b'fixture binary').hexdigest())


if __name__ == '__main__':
    unittest.main()
