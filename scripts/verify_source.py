"""Verify the packaged source snapshot; never hashes runtime private data."""
import hashlib
import json
from pathlib import Path


def verify(root):
    manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
    for name, expected in manifest.items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('Packaged source mismatch: ' + name)
    return len(manifest)


if __name__ == '__main__':
    print('Verified packaged source files:', verify(Path(__file__).resolve().parents[1]))
