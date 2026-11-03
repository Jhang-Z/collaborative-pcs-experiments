"""Common causal CPU/NIC replay for native MPI and sequential coordinator traces."""
from collections import defaultdict, deque
import heapq
import json
import math
from pathlib import Path


class Graph:
    def __init__(self):
        self.nodes = []
        self.payload = 0

    def add(self, kind='local', deps=(), seconds=0., src=None, dst=None, size=0):
        assert seconds >= 0 and math.isfinite(seconds) and size >= 0
        self.nodes.append(dict(kind=kind, deps=set(deps), seconds=seconds,
                               src=src, dst=dst, size=size))
        return len(self.nodes)-1

    def edge(self, target, *sources):
        self.nodes[target]['deps'].update(sources)

    def message(self, source, destination, size, posted):
        if source == destination:
            done = self.add(deps=[posted])
            return done, done
        self.payload += size
        done = self.add('flow', [posted], src=source, dst=destination, size=size)
        arrival = self.add('latency', [done])
        return done, arrival


def mpi_graph(traces):
    n = len(traces)
    assert n > 0 and {t['rank'] for t in traces} == set(range(n))
    g = Graph()
    sends, receives, collectives = defaultdict(list), defaultdict(list), defaultdict(dict)
    for trace in sorted(traces, key=lambda t: t['rank']):
        rank = trace['rank']
        assert trace['schema'] == 'mpi-local-compute-v1' and trace['parties'] == n
        previous, pending = None, {}
        assert trace['events'] and trace['events'][-1]['op'] == 'end'
        for index, event in enumerate(trace['events']):
            assert isinstance(event['compute_ns'], int) and event['compute_ns'] >= 0
            before = g.add(deps=[] if previous is None else [previous], seconds=event['compute_ns']/1e9)
            result = g.add(deps=[before]); previous = result
            op = event['op']
            if op in ['send', 'isend', 'recv', 'irecv']:
                peer, tag, size = event['peer'], event['tag'], event['bytes']
                assert 0 <= peer < n and tag >= 0 and isinstance(size, int) and size >= 0
                endpoint = result if op in ['send', 'recv'] else g.add(deps=[before])
                if op in ['isend', 'irecv']:
                    request = event['request']
                    assert request > 0 and request not in pending
                    pending[request] = endpoint
                key = (rank, peer, tag) if op in ['send', 'isend'] else (peer, rank, tag)
                (sends if op in ['send', 'isend'] else receives)[key].append((before, endpoint, size))
            elif op in ['wait', 'waitall']:
                ids = [request for request in event['requests'] if request]
                assert len(ids) == len(set(ids))
                for request in ids:
                    assert request in pending, 'unmatched or repeated wait'
                    g.edge(result, pending.pop(request))
            elif op in ['barrier', 'bcast', 'alltoall']:
                key = event['collective']
                assert key >= 0 and rank not in collectives[key]
                collectives[key][rank] = (event, before, result)
            elif op == 'end':
                assert index == len(trace['events'])-1 and not pending
            else:
                raise ValueError('unsupported online operation: ' + op)
    assert set(sends) == set(receives), 'unmatched send/receive channel'
    for key, sent in sends.items():
        received = receives[key]
        assert len(sent) == len(received), 'unmatched message sequence'
        for (post, completed, size), (_, received_node, capacity) in zip(sent, received):
            assert size <= capacity, 'receive capacity too small'
            done, arrival = g.message(key[0], key[1], size, post)
            g.edge(completed, done); g.edge(received_node, arrival)
    assert set(collectives) == set(range(len(collectives))), 'collective sequence gap'
    for group in collectives.values():
        assert set(group) == set(range(n)), 'collective participant missing'
        ops = {entry[0]['op'] for entry in group.values()}
        assert len(ops) == 1, 'collective kind mismatch'
        op = next(iter(ops))
        if op == 'barrier':
            before = [entry[1] for entry in group.values()]
            for _, _, result in group.values():
                g.edge(result, *before)
        else:
            sizes = {entry[0]['bytes'] for entry in group.values()}
            assert len(sizes) == 1
            size = next(iter(sizes)); assert isinstance(size, int) and size >= 0
            if op == 'bcast':
                roots = {entry[0]['root'] for entry in group.values()}
                assert len(roots) == 1
                root = next(iter(roots)); assert 0 <= root < n
                for destination in range(n):
                    if destination == root:
                        continue
                    done, arrival = g.message(root, destination, size, group[root][1])
                    g.edge(group[root][2], done)
                    g.edge(group[destination][2], arrival)
            else:
                for source in range(n):
                    for destination in range(n):
                        if source == destination:
                            continue
                        done, arrival = g.message(source, destination, size, group[source][1])
                        g.edge(group[source][2], done)
                        g.edge(group[destination][2], arrival)
    return g


def coordinator_graph(trace):
    """Root and worker0 share a core; preserve the existing exchange barriers."""
    g = Graph(); n = trace['parties']; previous = None
    assert n > 0
    for exchange in trace['exchanges']:
        for key in ['party_ns', 'request_bytes', 'response_bytes']:
            assert len(exchange[key]) == n
        assert exchange['command'] != 22
        root = g.add(deps=[] if previous is None else [previous], seconds=exchange['coordinator_ns']/1e9)
        finished = [g.add(deps=[root], seconds=exchange['party_ns'][0]/1e9)]
        for rank in range(1, n):
            _, request_arrival = g.message(0, rank, exchange['request_bytes'][rank], root)
            work = g.add(deps=[request_arrival], seconds=exchange['party_ns'][rank]/1e9)
            _, response_arrival = g.message(rank, 0, exchange['response_bytes'][rank], work)
            finished.append(response_arrival)
        previous = g.add(deps=finished)
    g.add(deps=[] if previous is None else [previous], seconds=trace['coordinator_final_ns']/1e9)
    return g


def simulate(graph, rate, latency):
    """One active FIFO send per source; fair RX sharing, both NIC limits respected."""
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
    completed = 0; now = 0.

    def finish(index):
        nonlocal completed
        completed += 1
        for target in children[index]:
            needed[target] -= 1
            if not needed[target]:
                ready.append(target)

    while completed < len(nodes):
        while ready:
            index = ready.popleft(); node = nodes[index]
            if node['kind'] == 'flow' and node['size'] and math.isfinite(rate):
                queues[node['src']].append(index); remaining[index] = float(node['size'])
            else:
                duration = latency if node['kind'] == 'latency' else node['seconds']
                if duration:
                    heapq.heappush(timers, (now + duration, index))
                else:
                    finish(index)
        if completed == len(nodes):
            break
        active = [queue[0] for queue in queues.values() if queue]
        counts = defaultdict(int)
        for index in active:
            counts[nodes[index]['dst']] += 1
        rates = {index: rate/counts[nodes[index]['dst']] for index in active}
        flow_step = min((remaining[index]/rates[index] for index in active), default=math.inf)
        timer_step = max(0., timers[0][0]-now) if timers else math.inf
        step = min(flow_step, timer_step)
        assert math.isfinite(step), 'cyclic/incomplete trace'
        for index in active:
            remaining[index] = max(0., remaining[index]-step*rates[index])
        now += step
        done = [index for index in active if remaining[index] <= max(1e-7, nodes[index]['size']*1e-12)]
        for index in done:
            assert queues[nodes[index]['src']].popleft() == index
            del remaining[index]; finish(index)
        while timers and timers[0][0] <= now + 1e-14:
            _, index = heapq.heappop(timers); finish(index)
    return now


def replay(graph, gbps, rtt_ms):
    baseline = simulate(graph, math.inf, 0.)
    total = simulate(graph, gbps*1e9/8, rtt_ms/2000)
    assert total + 1e-10 >= baseline
    return dict(online_s=total, compute_critical_s=baseline, network_increment_s=total-baseline,
                transmitted_bytes=graph.payload, gbps=gbps, rtt_ms=rtt_ms,
                model='causal-fifo-tx-fair-rx-v1')


def read_mpi(directory):
    traces = []
    for path in sorted(Path(directory).glob('rank-*.jsonl')):
        lines = [json.loads(line) for line in path.read_text().splitlines()]
        header, *events = lines
        traces.append(dict(header, events=events))
    return traces
