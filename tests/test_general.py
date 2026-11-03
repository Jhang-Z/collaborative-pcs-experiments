"""General frontend, task identity, and replay checks without a prover build."""
import itertools
import json
from pathlib import Path
import random
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from general.backend import oracle
from general.frontend import build, satisfied, ONE
from general.replay import Graph, replay
from general.fast_replay import replay_pair
from matrix import jobs
from campaign import prepare_inputs


class GeneralTasks(unittest.TestCase):
    def test_boolean_oracle_and_native_sign_encoding_agree(self):
        for xor, a, b in itertools.product([True, False], [0, 1], [0, 1]):
            gate = {'left': [0, 1], 'right': ONE} if xor else {'left': [0], 'right': 1}
            graph = dict(task='xor_and_random50', inputs=2, gates=[gate])
            rows, witness, output = build(graph, [a, b])
            self.assertEqual(oracle(graph, bytes([a, b])), (output, int(xor), int(not xor)))
            self.assertEqual(output, (a ^ b) if xor else (a & b))
            witness[-1] = -witness[-1]
            self.assertFalse(satisfied(rows, witness))

    def test_mixed_cross_wire_graphs_agree(self):
        rng = random.Random(42)
        for _ in range(16):
            bits = bytes(rng.randrange(2) for _ in range(8)); gates = []
            for j in range(128):
                a, b = rng.sample(range(8 + j), 2)
                gates.append(dict(left=[a, b], right=ONE) if rng.randrange(2) else dict(left=[a], right=b))
            graph = dict(task='xor_and_random50', inputs=8, gates=gates)
            self.assertEqual(oracle(graph, bits)[0], build(graph, bits)[2])

    def test_rejects_non_boolean_and_forward_references(self):
        graph = dict(inputs=2, gates=[dict(left=[0, 1], right=ONE)])
        with self.assertRaises(ValueError):
            oracle(graph, bytes([0, 2]))
        graph['gates'][0]['left'][1] = 2
        with self.assertRaises(ValueError):
            oracle(graph, bytes([0, 1]))

    def test_six_candidate_scales_have_24_pairs_and_one_binius_job_each(self):
        settings = json.loads((ROOT / 'configs/random50.json').read_text())
        selected = jobs(settings)
        self.assertEqual(len(selected), 54)
        self.assertEqual(len({j['label'] for j in selected}), 54)
        for size in settings['groups']['5']['instances']:
            group = [j for j in selected if j['size'] == size]
            self.assertEqual(sum(j['kind'] == 'binius-general' for j in group), 1)
            for kind in ['ours-general', 'native-general']:
                self.assertEqual([j['N'] for j in group if j['kind'] == kind], [16, 32, 64, 128])
        self.assertEqual(len(jobs(settings, instances=[2**20])), 9)

    def test_general_input_is_not_prepared_as_keccak_outside_the_cgroup(self):
        with tempfile.TemporaryDirectory() as folder:
            run = Path(folder); (run / 'private').mkdir()
            prepare_inputs(ROOT, run, [dict(kind='ours-general', size=2**20)])
            self.assertEqual(list((run / 'private/inputs').iterdir()), [])


class GeneralReplay(unittest.TestCase):
    def test_compiled_model_matches_reference_with_shared_cpu_and_network(self):
        graph = Graph(); graph.cpu_map = [0, 1, 0]
        first = graph.add(seconds=.1); graph.nodes[first]['cpu'] = 0
        shared = graph.add(seconds=.2); graph.nodes[shared]['cpu'] = 0
        _, arrived = graph.message(0, 1, 1000000, first)
        last = graph.add(deps=[shared, arrived], seconds=.3); graph.nodes[last]['cpu'] = 1
        actual = replay_pair(graph)
        for name, rate, rtt in [('LAN', 10., 2.), ('WAN', .2, 50.)]:
            expected = replay(graph, rate, rtt)
            self.assertAlmostEqual(actual[name]['online_s'], expected['online_s'], places=12)
            self.assertEqual(actual[name]['transmitted_bytes'], 1000000)


if __name__ == '__main__':
    unittest.main()
