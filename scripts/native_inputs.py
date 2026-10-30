"""Reference input/statement preparation, not a PCS prover or verifier."""
import argparse
import hashlib
import json
import struct
from pathlib import Path

P = (1 << 61) - 1
ZERO = (0, 0)
ONE = (1, 0)


def add(a, b):
    return ((a[0] + b[0]) % P, (a[1] + b[1]) % P)


def sub(a, b):
    return ((a[0] - b[0]) % P, (a[1] - b[1]) % P)


def mul(a, b):
    # The author's native field represents a + b*i, with i^2 = -1.
    return ((a[0] * b[0] - a[1] * b[1]) % P,
            (a[0] * b[1] + a[1] * b[0]) % P)


def public_point(log_bits):
    """Rejection sampling for a fixed public statement, never secret coins."""
    point = []
    for coordinate in range(log_bits):
        components = []
        for component in range(2):
            counter = 0
            while True:
                tag = f'pappas-pcs-statement/v1/{log_bits}/{coordinate}/{component}/{counter}'
                value = int.from_bytes(hashlib.shake_256(tag.encode()).digest(8), 'little') & P
                if value < P:
                    components.append(value)
                    break
                counter += 1
        point.append(tuple(components))
    return point


def evaluate_bits(bits, point):
    if len(bits) != 1 << len(point) or any(bit not in (0, 1) for bit in bits):
        raise ValueError('expected a Boolean table of size 2^len(point)')
    values = [(bit, 0) for bit in bits]
    # r[0] addresses the least significant bit, matching precompute_beta.
    for r in point:
        values = [add(values[i], mul(r, sub(values[i + 1], values[i])))
                  for i in range(0, len(values), 2)]
    return values[0]


def prepare(master, manifest, log_bits, parties):
    native_limit = 1 << (8 * struct.calcsize('i') - 2)
    if parties < 4 or parties & (parties - 1) or parties > native_limit // 2:
        raise ValueError('parties must be a power of two >=4 within the native FFT range')
    if log_bits < 3 or log_bits >= 8 * struct.calcsize('P'):
        raise ValueError('table exponent does not fit the native dimensions')
    size = 1 << log_bits
    if size < parties // 4 or size // (parties // 4) + 3 * 8 * 520 > native_limit // 4:
        raise ValueError('table packing or encoded row exceeds the native FFT range')
    with Path(master).open('rb') as stream:
        raw = stream.read(size // 8)
    if len(raw) != size // 8:
        raise ValueError('master input is shorter than the requested prefix')
    expected = next(row for row in json.loads(Path(manifest).read_text())['pcs_prefixes']
                    if row['input_bits'] == size)
    digest = hashlib.sha256(raw).hexdigest()
    if digest != expected['input_sha256']:
        raise ValueError('input prefix does not match the shared input manifest')
    bits = [(byte >> bit) & 1 for byte in raw for bit in range(8)]
    point = public_point(log_bits)
    return {
        'status': 'reference statement only; complete PCS execution blocked',
        'input_bits': size, 'input_sha256': digest,
        'bit_order': 'LSB first within each byte, then file order',
        'field': {'characteristic': P, 'extension_degree': 2, 'i_squared': -1},
        'N': parties, 'k': parties // 4, 'k_prime_dimension': parties // 2,
        'degree_bound_exclusive': parties // 2, 'privacy_threshold': parties // 4,
        'native_paper_queries': 520, 'row_rate': '1/4',
        'external_evaluation_point': point,
        'expected_mle_value': evaluate_bits(bits, point),
        'coordinate_convention': 'r[0] is the least significant address bit',
        'internal_padding_point_mapping_verified': False,
        'proof_created': False, 'complete_verification_passed': False,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--master', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--log-bits', type=int, required=True)
    parser.add_argument('--parties', type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(prepare(args.master, args.manifest, args.log_bits, args.parties), indent=2))
