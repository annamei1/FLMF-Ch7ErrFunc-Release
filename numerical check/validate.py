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
    manifest = read('numerical check/source_manifest.json')
    paths = {r['path'] for r in manifest['files']}
    actual_sources = {str(p.relative_to(ROOT)) for p in (ROOT / 'FLMF').rglob('*.lean')}
    actual_sources.add('Chapter7.lean')
    assert paths == actual_sources, 'Source manifest differs from the on-disk modules'
    modules = {r['module'] for r in manifest['files']}
    assert len(modules) == len(paths), 'Duplicate source modules'
    assert all(r['module'].replace('.', '/') + '.lean' == r['path']
               for r in manifest['files']), 'Module name/path mismatch'
    imports = {}
    for r in manifest['files'] + manifest['vendored_files']:
        assert digest(ROOT / r['path']) == r['sha256'], 'Source changed: ' + r['path']
    for rel in paths:
        imports[rel.removesuffix('.lean').replace('/', '.')] = set()
        for mod in re.findall(r'^import\s+(\S+)', (ROOT / rel).read_text(), re.M):
            if mod.startswith('FLMF.'):
                assert mod.replace('.', '/') + '.lean' in paths, 'Missing import: ' + mod
                imports[rel.removesuffix('.lean').replace('/', '.')].add(mod)
            else:
                assert mod.startswith('Mathlib'), mod
    visited, active = set(), set()
    def visit(mod):
        assert mod not in active, 'Import cycle: ' + mod
        if mod in visited:
            return
        active.add(mod)
        for dependency in imports[mod]:
            visit(dependency)
        active.remove(mod)
        visited.add(mod)
    visit('Chapter7')
    assert visited == modules, 'Modules outside the Chapter7 import closure'
    layout = read('numerical check/module_layout.json')['module_mapping']
    assert set(layout.values()) == modules, 'Module migration map is incomplete'
    assert not manifest['vendored_files'], 'Watson must be integrated into FLMF/Support'
    for dependency in manifest.get('integrated_dependencies', []):
        assert (ROOT / dependency['license_file']).is_file(), 'Missing integrated-source license'
    for r in read('numerical check/dlmf_source_manifest.json')['records']:
        assert digest(ROOT / r['path']) == r['sha256'], 'DLMF snapshot changed: ' + r['path']
    records = [json.loads(s) for s in (ROOT / 'numerical check/declarations.jsonl').read_text().splitlines()]
    ids = {r['id'] for r in records}
    assert len(ids) == len(records)
    eqs = read('numerical check/equations.json')
    targets = {r['dlmf'] for r in read('numerical check/equation_targets.json')}
    assert targets == {r['equation'] for r in eqs}
    assert len(targets) == 137
    assert all(t.startswith('7.') for t in targets)
    assert {t for r in records for t in r['equations']} == targets
    assert all(r['source_file'] in paths for r in records)
    for eq in eqs:
        assert set(eq['declaration_ids']) <= ids
        assert eq['declaration_ids']
    audit = [json.loads(s) for s in (ROOT / 'numerical check/axiom_audit.jsonl').read_text().splitlines()]
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
                      'flmf_source_modules': len(paths) - 1, 'entry_points': 1,
                      'axiom_audited': len(audit)}, indent=2))

if __name__ == '__main__':
    main()
