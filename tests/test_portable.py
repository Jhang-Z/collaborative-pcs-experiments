import importlib.util
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def load(name):
    path = ROOT / 'scripts' / (name + '.py')
    if not path.exists():
        return None
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Resources(unittest.TestCase):
    def setUp(self):
        self.r = load('resources')
        self.assertIsNotNone(self.r, 'portable resource discovery is not implemented')

    def test_available_memory_not_total_or_a_256gb_assumption(self):
        self.assertEqual(self.r.budget_bytes(1000, [], .1), 900)

    def test_tightest_ancestor_container_budget_wins(self):
        self.assertEqual(self.r.budget_bytes(1000, [800, 400], .1), 360)

    def test_unlimited_ancestor_is_not_zero(self):
        self.assertEqual(self.r.budget_bytes(1000, [None, 800], .1), 720)

    def test_explicit_budget_cannot_exceed_available_capacity(self):
        with self.assertRaises(ValueError):
            self.r.budget_bytes(1000, [400], .1, requested=500)
        self.assertEqual(self.r.budget_bytes(1000, [400], .1, requested=300), 300)

    def test_no_available_capacity_is_a_failure(self):
        with self.assertRaises(ValueError):
            self.r.budget_bytes(1000, [0], .1)

    def test_compute_and_progress_cpus_are_distinct(self):
        self.assertEqual(self.r.cpu_roles([4, 9, 20]), (4, [9, 20]))
        with self.assertRaises(ValueError):
            self.r.cpu_roles([4])


class Matrix(unittest.TestCase):
    def setUp(self):
        self.m = load('matrix')
        self.assertIsNotNone(self.m, 'portable configuration matrix is not implemented')
        self.settings = json.loads((ROOT / 'configs/experiments.json').read_text())

    def test_paper_matrix_has_74_unique_jobs_with_overlap_shared(self):
        jobs = self.m.jobs(self.settings)
        self.assertEqual(len(jobs), 74)
        self.assertEqual(len({j['label'] for j in jobs}), 74)
        shared = [j for j in jobs if j['kind'] == 'ours-app' and j['size'] == 512]
        self.assertEqual(len(shared), 4)
        self.assertTrue(all(j['groups'] == ['1', '4'] for j in shared))

    def test_each_group_can_be_selected_alone_and_multiple_groups_share_proofs(self):
        expected={'1':10,'2':40,'3':16,'4':16}
        for group,count in expected.items():
            jobs=self.m.jobs(self.settings,groups=[group])
            self.assertEqual(len(jobs),count)
            self.assertTrue(all(j['groups']==[group] for j in jobs))
        self.assertEqual(len(self.m.jobs(self.settings,groups=['1','4'])),18)

    def test_4096_subset_only_has_four_requested_cases(self):
        jobs = self.m.jobs(self.settings, groups=['4'], instances=[4096])
        self.assertEqual([j['N'] for j in jobs], [32, 64, 128, 256])
        self.assertTrue(all(j['size'] == 4096 for j in jobs))

    def test_settings_determine_workers_and_repetitions(self):
        self.settings['workers'] = [16, 32]
        self.settings['repetitions'] = 2
        self.assertEqual(len(self.m.jobs(self.settings, groups=['4'], instances=[512])), 4)


if __name__ == '__main__':
    unittest.main()
