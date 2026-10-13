#!/usr/bin/env python3
"""Check snapshot integrity, dataset membership, imports, and recorded audit results."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
def read(p): return json.loads((ROOT / p).read_text())
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    manifest = read('data/source_manifest.json')
    paths = {r['path'] for r in manifest['files']}
    for r in manifest['files'] + manifest['vendored_files']:
        assert digest(ROOT / r['path']) == r['sha256'], 'Source changed: ' + r['path']
    for rel in paths:
        for mod in re.findall(r'^import\s+(\S+)', (ROOT / rel).read_text(), re.M):
            if mod.startswith('FLMF.'):
                assert mod.replace('.', '/') + '.lean' in paths, 'Missing import: ' + mod
            else:
                assert mod.startswith('Mathlib') or mod == 'PicardLefschetz.Watson', mod
    for r in read('data/dlmf_source_manifest.json')['records']:
        assert digest(ROOT / r['path']) == r['sha256'], 'DLMF snapshot changed: ' + r['path']
    records = [json.loads(s) for s in (ROOT / 'data/declarations.jsonl').read_text().splitlines()]
    ids = {r['id'] for r in records}
    assert len(ids) == len(records)
    eqs = read('data/equations.json')
    targets = {r['dlmf'] for r in read('data/equation_targets.json')}
    assert targets == {r['equation'] for r in eqs}
    assert len(targets) == 137
    assert all(t.startswith('7.') for t in targets)
    assert {t for r in records for t in r['equations']} == targets
    assert all(r['source_file'] in paths for r in records)
    for eq in eqs:
        assert set(eq['declaration_ids']) <= ids
        assert eq['declaration_ids']
    audit = [json.loads(s) for s in (ROOT / 'data/axiom_audit.jsonl').read_text().splitlines()]
    assert {r['name'] for r in audit} == ids
    assert len(audit) == len(ids)
    indexed = {r['name']: r for r in audit}
    for r in records:
        assert r['axioms'] == sorted(indexed[r['name']]['axioms'])
        assert r['elaborated_type'] == indexed[r['name']]['elaborated_type']
        assert r['source_range'] == indexed[r['name']]['source_range']
        first, col, last, endcol = r['source_range']
        lines = (ROOT / r['source_file']).read_text().splitlines(keepends=True)
        start = sum(map(len, lines[:first - 1])) + col
        end = sum(map(len, lines[:last - 1])) + endcol
        assert r['lean_source'] == ''.join(lines)[start:end]
        assert r['short_name'] in r['lean_source']
        assert r['proof_status'] != 'not_audited'
        if r['proof_status'] == 'standard_axioms_only':
            assert set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    sums = ROOT / 'SHA256SUMS'
    if sums.exists():
        for line in sums.read_text().splitlines():
            expected, rel = line.split('  ', 1)
            assert digest(ROOT / rel) == expected, 'Checksum mismatch: ' + rel
    print(json.dumps({'validation': 'passed', 'equations': len(eqs), 'declarations': len(records),
                      'flmf_source_modules': len(paths), 'axiom_audited': len(audit)}, indent=2))

if __name__ == '__main__':
    main()
