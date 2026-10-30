"""Export the canonical application to the Pappas native-field reader."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
from contract import load_inputs
from relation import Circuit

def export(inputs, instances, out):
    if instances < 1 or instances & (instances-1):
        raise ValueError('native Pappas batch must be a power of two')
    circuit = Circuit.build()
    padded = 1 << (max(circuit.row_count, circuit.public_start+256)-1).bit_length()
    if instances > (1 << (8*struct.calcsize('i')-2)) // padded:
        raise ValueError('native Pappas table exceeds the integer index range')
    data, output = load_inputs(inputs, instances)
    out = Path(out)
    out.mkdir(mode=0o700)
    model = circuit.encode()
    (out / 'keccak-r1cs.bin').write_bytes(model)
    with (out / 'keccak-witness.bin').open('xb') as stream:
        os.chmod(stream.name, 0o600)
        stream.write(b'PKECW001'+struct.pack('<QQ',instances,circuit.public_start+256))
        for j in range(instances):
            witness, result = circuit.witness(data[200*j:200*(j+1)])
            if result != output[32*j:32*(j+1)] or not circuit.check(witness, result):
                raise ValueError('canonical Keccak witness/output mismatch')
            stream.write(bytes(witness))
    (out / 'keccak-output.bin').write_bytes(output)
    dimensions = dict(application='Keccak-f[1600]/256', rounds=24,
        instances=instances, rows_per_instance=circuit.row_count,
        wires_per_instance=circuit.public_start+256, public_start=circuit.public_start,
        padded_rows_per_instance=padded, padded_wires_per_instance=padded,
        model_sha256=hashlib.sha256(model).hexdigest(),
        application_constraints_checked=True, full_proof_verified=False)
    (out / 'application.json').write_text(json.dumps(dimensions, indent=2)+'\n')
    return dimensions

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--instances', type=int, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(export(args.inputs, args.instances, args.out)))
