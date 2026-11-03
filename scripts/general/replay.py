"""Full actor CPU/message replay with coordinator and prover 0 sharing CPU/NIC.

Reuse the native MPI graph and FIFO-TX/fair-RX model. CPU intervals are actual
thread CPU nanoseconds, not elapsed/N. Ready CPU bursts run FIFO without overlap
on each physical node; asynchronous NIC flows advance while CPUs are busy.
"""
from collections import defaultdict, deque
import argparse
import heapq
import importlib.util
import json
import math
from pathlib import Path

_common_path = Path(__file__).resolve().with_name('common_replay.py')
if not _common_path.exists():
    _common_path = Path(__file__).resolve().parents[1] / 'local-simulation' / 'replay.py'
_spec = importlib.util.spec_from_file_location('local_simulation_replay', _common_path)
common = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(common)
Graph = common.Graph
read_mpi = common.read_mpi


def actor_graph(traces):
    """v2 logical ranks 0..N, coordinator N physically colocated with prover 0."""
    assert traces
    n = traces[0]['parties']
    assert n > 0 and len(traces) == n + 1
    assert {t['rank'] for t in traces} == set(range(n + 1))
    graph = Graph()
    sends, receives = defaultdict(list), defaultdict(list)
    graph.actor_count = n + 1
    graph.cpu_map = [*range(n), 0]
    graph.logical_sent = [0] * (n + 1)
    graph.network_sent = [0] * n
    graph.network_received = [0] * n
    graph.challenges = 0
    for trace in sorted(traces, key=lambda t: t['rank']):
        rank = trace['rank']
        assert trace['schema'] == 'collaborative-actor-cpu-v2'
        assert trace['parties'] == n and trace['actors'] == n + 1 and trace['coordinator'] == n
        assert trace['clock'] == 'CLOCK_THREAD_CPUTIME_ID'
        previous = None
        assert trace['events'] and trace['events'][-1]['op'] == 'end'
        for index, event in enumerate(trace['events']):
            ns = event.get('compute_ns', 0)
            assert isinstance(ns, int) and ns >= 0
            point = graph.add(deps=[] if previous is None else [previous], seconds=ns / 1e9)
            graph.nodes[point]['cpu'] = graph.cpu_map[rank]
            previous = point
            op = event['op']
            if op in ('send', 'isend', 'recv'):
                peer, tag, size = event['peer'], event['tag'], event['bytes']
                assert isinstance(peer, int) and 0 <= peer <= n
                assert isinstance(tag, int) and tag >= 0
                assert isinstance(size, int) and size >= 0
                if op in ('send', 'isend'):
                    completed = None
                    if op == 'send':
                        completed = graph.add(deps=[point])
                        previous = completed
                    sends[rank, peer, tag].append((point, completed, size))
                    graph.logical_sent[rank] += size
                else:
                    receives[peer, rank, tag].append((point, size))
            elif op == 'challenge':
                graph.challenges += 1
            elif op == 'end':
                assert index == len(trace['events']) - 1
            else:
                assert op == 'compute', 'unsupported v2 operation: ' + op
    assert set(sends) == set(receives), 'unmatched send/receive channel'
    for (source, destination, tag), sent in sends.items():
        received = receives[source, destination, tag]
        assert len(sent) == len(received), 'unmatched message sequence'
        physical_source = graph.cpu_map[source]
        physical_destination = graph.cpu_map[destination]
        for (posted, completed, size), (received_node, actual) in zip(sent, received):
            assert size == actual, 'actual serialized message sizes differ'
            done, arrival = graph.message(physical_source, physical_destination, size, posted)
            if physical_source != physical_destination:
                graph.network_sent[physical_source] += size
                graph.network_received[physical_destination] += size
            if completed is not None:
                graph.edge(completed, done)
            graph.edge(received_node, arrival)
    return graph


def mpi_graph(traces):
    """Native MPI parser unchanged; attach one physical CPU per existing rank."""
    graph = common.mpi_graph(traces)
    # The shared parser creates a CPU-before and result node per event, plus one
    # request endpoint for nonblocking events. Message/collective nodes follow.
    index = 0
    for trace in sorted(traces, key=lambda t: t['rank']):
        for event in trace['events']:
            graph.nodes[index]['cpu'] = trace['rank']
            index += 3 if event['op'] in ('isend', 'irecv') else 2
    graph.actor_count = len(traces)
    graph.cpu_map = list(range(len(traces)))
    return graph


def simulate(graph, rate, latency):
    """The shared NIC algorithm plus a serial resource queue for each node CPU."""
    assert rate > 0 and latency >= 0
    nodes = graph.nodes
    children = [[] for _ in nodes]
    needed = [len(node['deps']) for node in nodes]
    for target, node in enumerate(nodes):
        for source in node['deps']:
            assert 0 <= source < len(nodes) and source != target
            children[source].append(target)
    ready = deque(i for i, count in enumerate(needed) if not count)
    timers, queues, remaining = [], defaultdict(deque), {}
    cpus = defaultdict(deque)
    completed = 0
    now = 0.

    def finish(index):
        nonlocal completed
        completed += 1
        node = nodes[index]
        cpu = node.get('cpu')
        if cpu is not None and node['seconds']:
            assert cpus[cpu].popleft() == index
            if cpus[cpu]:
                following = cpus[cpu][0]
                heapq.heappush(timers, (now + nodes[following]['seconds'], following))
        for target in children[index]:
            needed[target] -= 1
            if not needed[target]:
                ready.append(target)

    while completed < len(nodes):
        while ready:
            index = ready.popleft()
            node = nodes[index]
            if node['kind'] == 'flow' and node['size'] and math.isfinite(rate):
                queues[node['src']].append(index)
                remaining[index] = float(node['size'])
            else:
                duration = latency if node['kind'] == 'latency' else node['seconds']
                cpu = node.get('cpu')
                if duration and cpu is not None:
                    cpus[cpu].append(index)
                    if len(cpus[cpu]) == 1:
                        heapq.heappush(timers, (now + duration, index))
                elif duration:
                    heapq.heappush(timers, (now + duration, index))
                else:
                    finish(index)
        if completed == len(nodes):
            break
        active = [queue[0] for queue in queues.values() if queue]
        counts = defaultdict(int)
        for index in active:
            counts[nodes[index]['dst']] += 1
        rates = {index: rate / counts[nodes[index]['dst']] for index in active}
        flow_step = min((remaining[index] / rates[index] for index in active), default=math.inf)
        timer_step = max(0., timers[0][0] - now) if timers else math.inf
        step = min(flow_step, timer_step)
        assert math.isfinite(step), 'cyclic/incomplete trace'
        for index in active:
            remaining[index] = max(0., remaining[index] - step * rates[index])
        now += step
        done = [index for index in active if remaining[index] <= max(1e-7, nodes[index]['size'] * 1e-12)]
        for index in done:
            assert queues[nodes[index]['src']].popleft() == index
            del remaining[index]
            finish(index)
        while timers and timers[0][0] <= now + 1e-14:
            _, index = heapq.heappop(timers)
            finish(index)
    return now


def replay(graph, gbps, rtt_ms):
    baseline = simulate(graph, math.inf, 0.)
    total = simulate(graph, gbps * 1e9 / 8, rtt_ms / 2000)
    # Arrival-dependent CPU arbitration can change burst order. The zero-network
    # replay is a comparison, not a universal lower bound for that scheduler.
    result = dict(online_s=total, compute_critical_s=baseline,
                  zero_network_s=baseline, network_increment_s=total - baseline, transmitted_bytes=graph.payload,
                  gbps=gbps, rtt_ms=rtt_ms, model='causal-fifo-cpu-tx-fair-rx-v2',
                  actor_cpu_map=graph.cpu_map)
    if hasattr(graph, 'logical_sent'):
        result.update(logical_sent_bytes=graph.logical_sent, physical_sent_bytes=graph.network_sent,
                      physical_received_bytes=graph.network_received, challenge_stages=graph.challenges)
    return result


def read_graph(directory):
    traces = read_mpi(directory)
    assert traces, 'empty trace directory'
    return actor_graph(traces) if traces[0]['schema'] == 'collaborative-actor-cpu-v2' else mpi_graph(traces)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trace', type=Path, required=True)
    parser.add_argument('--gbps', type=float, required=True)
    parser.add_argument('--rtt-ms', type=float, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = replay(read_graph(args.trace), args.gbps, args.rtt_ms)
    text = json.dumps(result, sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
