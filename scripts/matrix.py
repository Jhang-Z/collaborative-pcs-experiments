"""Generate unique proof jobs from the public experiment configuration."""


def jobs(settings, groups=None, instances=None):
    selected = list(settings['groups']) if groups is None else list(groups)
    if any(g not in settings['groups'] for g in selected):
        raise ValueError('unknown experiment group')
    result = {}
    for group in selected:
        config = settings['groups'][group]
        workers = config.get('workers', settings['workers'])
        sizes = config.get('instances', config.get('input_log_bits'))
        if instances is not None and 'instances' in config:
            sizes = [size for size in sizes if size in instances]
        kinds = ['ours-pcs' if group == '2' else 'ours-app']
        kinds += [('native-pcs' if group == '2' else 'native-keccak')
                  for baseline in config['baselines'] if baseline == 'pappas']
        if 'binius64-single-core' in config['baselines']:
            kinds.append('native-baseline')
        for size in sizes:
            for kind in kinds:
                for n in ([1] if kind == 'native-baseline' else workers):
                    for repetition in range(1, settings['repetitions'] + 1):
                        label = f'{kind}-{size}-N{n}-r{repetition}'
                        if label not in result:
                            result[label] = dict(label=label, kind=kind, N=n, size=size,
                                                 repetition=repetition, groups=[], networks=[])
                        job = result[label]
                        job['groups'].append(group)
                        job['networks'] = list(dict.fromkeys(job['networks'] + config['networks']))
    return list(result.values())
