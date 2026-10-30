import importlib.util
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import campaign


class ExportChecks(unittest.TestCase):
    def test_bundle_excludes_private_material_and_preserves_failure(self):
        with tempfile.TemporaryDirectory() as folder:
            run = Path(folder)
            (run / 'public').mkdir(); (run / 'private').mkdir()
            (run / 'private/proof.bin').write_bytes(b'secret-proof')
            state = dict(complete=False, performance_sample=True, expected=2,
                cases=[dict(label='failed', passed=False, error={'type': 'CommandFailed'})])
            campaign.summarize(run, state); campaign.export(run)
            with tarfile.open(run / 'results-public.tar.gz') as archive:
                names = archive.getnames()
                self.assertNotIn('private/proof.bin', names)
                exported = json.load(archive.extractfile('results.json'))
                self.assertFalse(exported['complete'])
                self.assertFalse(exported['cases'][0]['passed'])
            self.assertEqual(len((run / 'public/results.csv').read_text().splitlines()), 1)

    def test_successful_rows_keep_networks_and_generation_only_scope(self):
        with tempfile.TemporaryDirectory() as folder:
            run = Path(folder); (run / 'public').mkdir()
            timing = dict(online_s=2., compute_critical_s=1., network_increment_s=1., transmitted_bytes=10)
            record = dict(label='pappas', kind='native-keccak', size=32, N=16,
                groups=['3'], repetition=1, passed=True, full_proof_verified=False,
                timing={'LAN':timing, 'WAN':timing}, resources={'budget_bytes':10,
                    'final':{'memory.peak':9}})
            campaign.summarize(run, dict(complete=True, performance_sample=True,
                expected=1, cases=[record]))
            import csv
            with (run / 'public/results.csv').open() as stream:
                rows = list(csv.DictReader(stream))
            self.assertEqual([r['network'] for r in rows], ['LAN', 'WAN'])
            self.assertTrue(all(r['full_proof_verified'] == 'False' for r in rows))


class ManagerChecks(unittest.TestCase):
    @patch('campaign.shutil.which', return_value='/usr/bin/tool')
    @patch('campaign.subprocess.run')
    def test_root_uses_system_manager_and_user_uses_user_manager(self, run, which):
        run.return_value.returncode = 0
        with patch('campaign.os.geteuid', return_value=0):
            self.assertEqual(campaign.systemd_manager(), [])
            self.assertEqual(run.call_args.args[0], ['systemctl', 'is-active', 'multi-user.target'])
        with patch('campaign.os.geteuid', return_value=1000):
            self.assertEqual(campaign.systemd_manager(), ['--user'])
            self.assertIn('--user', run.call_args.args[0])

    @patch('campaign.shutil.which', return_value='/usr/bin/tool')
    @patch('campaign.subprocess.run')
    def test_unenforceable_limits_fail_instead_of_running_unbounded(self, run, which):
        run.return_value.returncode = 1
        with self.assertRaisesRegex(RuntimeError, 'enforce RAM'):
            campaign.systemd_manager()


class ServiceAdmission(unittest.TestCase):
    def config(self):
        return dict(memory_budget_bytes=900, reserve_fraction=.1, manager=['--user'], unit='test.service')

    @patch('campaign.discover')
    @patch('campaign.memory_snapshot')
    @patch('campaign.subprocess.run')
    def test_actual_service_ancestor_can_reduce_launcher_budget(self, run, snapshot, discover):
        discover.return_value = dict(memory_budget_bytes=360, cgroup_ancestors=[])
        snapshot.return_value = {'memory.max':360,'memory.swap.max':0}
        cfg=self.config(); campaign.admit_service(cfg)
        self.assertEqual(cfg['memory_budget_bytes'],360)
        self.assertIn('MemoryMax=360', run.call_args.args[0])
        discover.assert_called_once_with(.1, exclude_current_cgroup=True)

    @patch('campaign.discover')
    @patch('campaign.memory_snapshot')
    @patch('campaign.subprocess.run')
    def test_failure_to_enforce_reduced_budget_stops_before_any_proof(self, run, snapshot, discover):
        discover.return_value = dict(memory_budget_bytes=360,cgroup_ancestors=[])
        snapshot.return_value = {'memory.max':900,'memory.swap.max':0}
        with self.assertRaisesRegex(RuntimeError,'does not match'):
            campaign.admit_service(self.config())


class FailedCommandTiming(unittest.TestCase):
    def test_failed_case_keeps_elapsed_command_time_in_public_record(self):
        from backend import CommandFailed
        with tempfile.TemporaryDirectory() as folder:
            run=Path(folder); (run/'private/case-resources').mkdir(parents=True)
            (run/'public').mkdir()
            job=dict(label='failed-proof',kind='ours-app',N=32,size=8)
            campaign.save(run/'plan.json',dict(jobs=[job],performance_sample=False,config={}))
            campaign.save(run/'private/runtime.json',{})
            campaign.save(run/'private/case-resources/failed-proof.json',dict(
                progress_cpus=[1],compute_cpu=0,memory_budget_bytes=100,timeout_seconds=1))
            snap={'memory.max':100,'memory.peak':10,'memory.swap.max':0,'memory.swap.peak':0,
                'memory.events':{'max':0,'oom':0,'oom_kill':0}}
            def fail(*args):
                args[-2]('prove'); args[-1]['prove']=.25
                raise CommandFailed('prove',7)
            with patch('campaign.admit_service',return_value={'cgroup_ancestors':[]}), \
                 patch('campaign.os.sched_setaffinity',create=True), \
                 patch('campaign.ancestors',return_value=[]), \
                 patch('campaign.memory_snapshot',return_value=snap), \
                 patch('backend.execute_job',side_effect=fail):
                self.assertEqual(campaign.case(ROOT,run,'failed-proof'),1)
            result=json.loads((run/'public/cases/failed-proof.json').read_text())
            self.assertFalse(result['passed'])
            self.assertEqual(result['command_wall_s'],{'prove':.25})
            self.assertEqual(result['error']['returncode'],7)


class PackagedContract(unittest.TestCase):
    def test_canonical_input_contract_loads_from_clean_repository(self):
        path = ROOT / 'experiments/benchmarks-2026-10-23/keccak-baselines-20261029/contract.py'
        spec = importlib.util.spec_from_file_location('artifact_contract', path)
        contract = importlib.util.module_from_spec(spec); spec.loader.exec_module(contract)
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder) / 'inputs'
            contract.create_inputs(target, bytes(200))
            raw, output = contract.load_inputs(target, 1)
            self.assertEqual(raw, bytes(200)); self.assertEqual(len(output), 32)
            (target / 'public-output.bin').write_bytes(bytes(32))
            with self.assertRaises(ValueError):
                contract.load_inputs(target, 1)


if __name__ == '__main__':
    unittest.main()
