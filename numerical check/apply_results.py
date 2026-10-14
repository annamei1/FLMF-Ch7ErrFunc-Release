#!/usr/bin/env python3
"""Apply numerical labels from a completed isolated run, preserving review evidence."""
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def main():
    latest = json.loads((HERE / 'results/latest.json').read_text())
    run = HERE / 'results' / latest['run']
    results = json.loads((run / 'manifest.json').read_text())
    targets = json.loads((run / 'targets.json').read_text())
    assert len(results) == len(targets) == latest['summary']['completed']
    assert {(r['file'], r['name']) for r in results} == {(r['file'], r['name']) for r in targets}
    sums_path = ROOT / 'SHA256SUMS'
    sums = {rel: sha for sha, rel in
            (line.split('  ', 1) for line in sums_path.read_text().splitlines())} if sums_path.exists() else {}
    for rel, expected in sums.items():
        assert digest((ROOT / rel).read_bytes()) == expected, 'Pre-existing checksum mismatch: ' + rel
    grouped = defaultdict(list)
    labels = {}
    for row in results:
        assert row['worker_exit_code'] == 0, row['name']
        assert row['verdict'] in {'PASS', 'FAIL', 'unable to proceed'}, row['name']
        label = ('Numerical: N/A (' + row['kind'] + ')' if row['verdict'] == 'unable to proceed'
                 else 'Numerical: ' + row['verdict'])
        assert '\n' not in label and '\r' not in label
        labels[row['file'], row['name']] = label
        grouped[row['file']].append(row)
    changes = {}
    for rel, rows in grouped.items():
        before = (ROOT / rel).read_bytes()
        lines = before.decode().splitlines(keepends=True)
        old_lines = lines.copy()
        for row in rows:
            pos = row['annotation_line'] - 1
            existing = lines[pos].strip()
            wanted = labels[rel, row['name']]
            original = row.get('annotation', 'Numerical: Stale')
            assert existing in {original, wanted}, (rel, existing)
            old_lines[pos] = old_lines[pos].replace(existing, original, 1)
            lines[pos] = lines[pos].replace(existing, wanted, 1)
        # Reverting just these annotations must recover the exact checked source.
        assert digest(''.join(old_lines).encode()) == rows[0]['source_sha256'], 'Checked source changed: ' + rel
        assert all(row['source_sha256'] == rows[0]['source_sha256'] for row in rows)
        after = ''.join(lines).encode()
        if after != before:
            changes[rel] = after
    manifest_rel = 'numerical check/source_manifest.json'
    manifest = json.loads((ROOT / manifest_rel).read_text())
    for source in manifest['files']:
        rel = source['path']
        if rel in changes:
            source.setdefault('original_sha256', source['sha256'])
            source['sha256'] = digest(changes[rel])
            source['matches_source_commit'] = False
    manifest['numerical_annotation_refresh'] = {
        'run_manifest': str((run / 'manifest.json').relative_to(ROOT)),
        'run_manifest_sha256': digest((run / 'manifest.json').read_bytes()),
        'completed_at': latest['summary']['finished_at'],
        'counts': dict(Counter(row['verdict'] for row in results)),
        'annotation_only': True,
    }
    output = encoded(manifest)
    if output != (ROOT / manifest_rel).read_bytes():
        changes[manifest_rel] = output
    declaration_path = ROOT / 'numerical check/declarations.jsonl'
    declarations = [json.loads(line) for line in declaration_path.read_text().splitlines()]
    for declaration in declarations:
        rel = declaration['source_file']
        if rel not in grouped:
            continue
        source = changes.get(rel, (ROOT / rel).read_bytes())
        declaration['source_file_sha256'] = digest(source)
        label = labels.get((rel, declaration['short_name']))
        if label is not None:
            declaration['docstring'] = declaration['docstring'].replace('Numerical: Stale', label)
        first, col, last, endcol = declaration['source_range']
        lines = source.decode().splitlines(keepends=True)
        start = sum(map(len, lines[:first - 1])) + col
        end = sum(map(len, lines[:last - 1])) + endcol
        declaration['lean_source'] = ''.join(lines)[start:end]
    output = ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in declarations).encode()
    if output != declaration_path.read_bytes():
        changes['numerical check/declarations.jsonl'] = output
    for rel, data in changes.items():
        (ROOT / rel).write_bytes(data)
        sums[rel] = digest(data)
    if sums_path.exists():
        sums_path.write_text(''.join(f'{sha}  {rel}\n' for rel, sha in sorted(sums.items())))
    application = {
        'run': latest['run'], 'labels': dict(Counter(labels.values())),
        'changed_files': sorted(changes),
        'semantic_labels_changed': False,
    }
    (HERE / 'labels_applied.json').write_bytes(encoded(application))
    print(json.dumps(application, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
