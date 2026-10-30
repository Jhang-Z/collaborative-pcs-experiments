import math
import unittest
from replay import Graph, mpi_graph, coordinator_graph, simulate, replay


def trace(rank, events, n=2):
    return dict(schema='mpi-local-compute-v1', rank=rank, parties=n, events=events)


def event(op, seconds=0, **kwargs):
    return dict(op=op, compute_ns=int(seconds*1e9), **kwargs)


class ReplayChecks(unittest.TestCase):
    def test_one_transfer_has_one_serialization_and_one_latency(self):
        g = Graph(); start = g.add(); g.message(0, 1, 10, start)
        self.assertAlmostEqual(simulate(g, 10, .2), 1.2)

    def test_sender_fifo_and_receiver_fairness(self):
        g = Graph(); start = g.add()
        g.message(0, 2, 10, start); g.message(1, 2, 20, start)
        self.assertAlmostEqual(simulate(g, 10, 0), 3)
        g = Graph(); start = g.add()
        g.message(0, 1, 10, start); g.message(0, 2, 20, start)
        self.assertAlmostEqual(simulate(g, 10, .2), 3.2)

    def test_nonblocking_overlap_wait_and_bytes(self):
        g = mpi_graph([
            trace(0, [event('isend', peer=1, tag=0, bytes=10, request=1),
                      event('wait', .5, requests=[1]), event('end')]),
            trace(1, [event('irecv', peer=0, tag=0, bytes=10, request=1),
                      event('wait', .2, requests=[1]), event('end')])])
        self.assertAlmostEqual(simulate(g, 10, .1), 1.1)
        self.assertEqual(g.payload, 10)

    def test_reused_tags_match_fifo(self):
        a = [event('send', peer=1, tag=0, bytes=10), event('send', peer=1, tag=0, bytes=20), event('end')]
        b = [event('recv', peer=0, tag=0, bytes=10), event('recv', peer=0, tag=0, bytes=20), event('end')]
        self.assertAlmostEqual(simulate(mpi_graph([trace(0,a), trace(1,b)]), 10, .1), 3.1)

    def test_barrier_dependency(self):
        a = [event('barrier', .2, collective=0), event('end', .3)]
        b = [event('barrier', .6, collective=0), event('end', .1)]
        self.assertAlmostEqual(simulate(mpi_graph([trace(0,a), trace(1,b)]), math.inf, 0), .9)

    def test_broadcast_and_alltoall(self):
        a = [event('bcast', collective=0, root=0, bytes=10), event('end')]
        g = mpi_graph([trace(i,a,n=4) for i in range(4)])
        self.assertAlmostEqual(simulate(g, 10, .1), 3.1)
        a = [event('alltoall', collective=0, bytes=10), event('end')]
        g = mpi_graph([trace(i,a,n=4) for i in range(4)])
        self.assertEqual(g.payload, 120)
        # Destination-order FIFO: RX0 takes 3s, RX1 takes 2s, final sends 1s.
        self.assertAlmostEqual(simulate(g, 10, 0), 6)

    def test_broadcast_does_not_add_a_global_barrier(self):
        a = [event('bcast', collective=0, root=0, bytes=10), event('end', 1)]
        b = [event('bcast', 9, collective=0, root=0, bytes=10), event('end')]
        self.assertAlmostEqual(simulate(mpi_graph([trace(0,a),trace(1,b)]),10,0),9)

    def test_coordinator_conversion_matches_hand_calculation(self):
        t = dict(parties=2, exchanges=[dict(command=1, coordinator_ns=100_000_000,
            party_ns=[200_000_000,200_000_000], request_bytes=[1250,1250],
            response_bytes=[1250,1250])], coordinator_final_ns=50_000_000)
        g = coordinator_graph(t)
        self.assertAlmostEqual(replay(g,10,2)['online_s'], .352002)
        self.assertEqual(g.payload,2500)
        self.assertAlmostEqual(replay(g,10,2)['compute_critical_s'],.35)

    def test_malformed_and_unmatched_requests_rejected(self):
        with self.assertRaises(AssertionError):
            mpi_graph([trace(0,[event('wait',requests=[7]),event('end')],n=1)])
        with self.assertRaises(AssertionError):
            mpi_graph([trace(0,[event('send',peer=1,tag=0,bytes=10),event('end')]), trace(1,[event('end')])])
        with self.assertRaises(AssertionError):
            mpi_graph([trace(0,[event('barrier',collective=0),event('end')]),trace(1,[event('end')])])


if __name__ == '__main__':
    unittest.main()
