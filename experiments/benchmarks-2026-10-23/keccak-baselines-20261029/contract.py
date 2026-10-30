"""Common private Keccak states and ordered public truncated outputs."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent

_spec = importlib.util.spec_from_file_location('keccak_reference',
    HERE.parents[2] / 'scripts/keccak_oracle.py')
_oracle = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_oracle)

def _outputs(data):
    return _oracle.outputs(data)

def create_inputs(out, data):
    if not data or len(data) % 200:
        raise ValueError('expected whole private 200-byte states')
    out = Path(out)
    out.mkdir()
    with (out / 'private-input.bin').open('xb') as stream:
        os.chmod(stream.name, 0o600)
        stream.write(data)
    (out / 'public-output.bin').write_bytes(_outputs(data))
    (out / 'contract.json').write_text(json.dumps({
        'application': 'Keccak-f[1600]/256', 'rounds': 24,
        'instances': len(data) // 200, 'private_bytes_per_instance': 200,
        'public_bytes_per_instance': 32, 'public_bit_order': 'byte-lsb-first',
        'purpose': 'application input contract; not a proof result',
        'full_proof_verified': False}, indent=2) + '\n')

def load_inputs(directory, instances):
    directory = Path(directory)
    contract = json.loads((directory / 'contract.json').read_text())
    if instances < 1 or instances > contract['instances']:
        raise ValueError('input prefix count')
    data = (directory / 'private-input.bin').read_bytes()[:instances*200]
    output = (directory / 'public-output.bin').read_bytes()[:instances*32]
    if len(data) != instances*200 or len(output) != instances*32 or _outputs(data) != output:
        raise ValueError('private input/public output mismatch')
    return data, output

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--instances', type=int, default=1024)
    args = parser.parse_args()
    if args.instances < 1 or args.instances > sys.maxsize // 200:
        parser.error('instances must be positive and the input length must fit the address space')
    create_inputs(args.out, os.urandom(args.instances*200))
    load_inputs(args.out, args.instances)
    print(json.dumps({'input_contract_verified': True, 'instances': args.instances,
                      'full_proof_verified': False}))
