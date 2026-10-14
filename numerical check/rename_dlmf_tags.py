#!/usr/bin/env python3
"""Rename DLMF numerical and semantic review labels throughout the snapshot.

Run without arguments to apply changes, or with --check to detect pending edits.
Recover statuses lost by the earlier Yes/No migration from matching HEAD text.
Preserve unrelated edits and update evidence filenames, references, and hashes.
"""
import argparse
from collections import Counter
from difflib import SequenceMatcher
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FIDELITY = re.compile(
    r'Fidelity[ \t]*:[ \t]*tier[ \t-]*([12])\b'
    r'(?:[ \t]+(PASS|PAS|PA|P|stale|n/a|unable)'
    r'(?=[ \t\r\n(]|$)(?:[ \t]+(\([^\r\n)]*\)))?)?', re.I)
VERIFIED = re.compile(
    r'Verified[ \t]*:[ \t]*(verified|unverified|unferified)[ \t]*'
    r'\(tier[ \t-]*2(?:[ \t]+DIVERGES)?\)', re.I)
TIERS = re.compile(r'tier[ \t_-]*([12])', re.I)
LEGACY_LABEL = re.compile(r'Numerical:[ \t]*(?:Yes|No)\b', re.I)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def numerical_label(match):
    status = (match[2] or 'n/a').lower()
    if status in {'pass', 'pas', 'pa', 'p'}:
        return 'Numerical: PASS'
    if status == 'stale':
        return 'Numerical: Stale'
    reason = ' ' + match[3] if match[3] else ''
    return 'Numerical: N/A' + reason


def matching_spans(baseline, text):
    if baseline == text:
        return [(0, 0, len(text))]
    if '\n' not in baseline and '\n' not in text:
        return [(b.a, b.b, b.size) for b in
                SequenceMatcher(None, baseline, text, autojunk=False).get_matching_blocks()]
    # Compare lines for large source files, rather than individual characters.
    old_lines, lines = baseline.splitlines(keepends=True), text.splitlines(keepends=True)
    old_offsets, offsets = [0], [0]
    for line in old_lines:
        old_offsets.append(old_offsets[-1] + len(line))
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    return [(old_offsets[b.a], offsets[b.b], old_offsets[b.a + b.size] - old_offsets[b.a])
            for b in SequenceMatcher(None, old_lines, lines, autojunk=False).get_matching_blocks()]


def recover_statuses(text, original, counts):
    """Restore only unchanged Yes/No spans that match the previous migration."""
    if not original or not LEGACY_LABEL.search(text):
        return text
    replacements = []
    offset = 0

    def legacy(match):
        nonlocal offset
        label = 'Numerical: ' + ('Yes' if match[1] == '1' else 'No')
        start = match.start() + offset
        replacements.append((start, start + len(label), numerical_label(match)))
        offset += len(label) - len(match[0])
        return label

    baseline = FIDELITY.sub(legacy, original)
    # The earlier migration also shortened successful semantic stamps.
    success = re.compile(r'Verified:[ \t]*verified[ \t]*\(tier[ \t]*2\)', re.I)
    stamps = list(success.finditer(baseline))
    replacements = [
        (start - sum(len(m[0]) - len('Verified: verified') for m in stamps if m.end() <= start),
         end - sum(len(m[0]) - len('Verified: verified') for m in stamps if m.end() <= start),
         label)
        for start, end, label in replacements
    ]
    baseline = success.sub('Verified: verified', baseline)
    blocks = matching_spans(baseline, text)
    edits = []
    for start, end, label in replacements:
        for old_pos, pos, size in blocks:
            if old_pos <= start and end <= old_pos + size:
                at = pos + start - old_pos
                edits.append((at, at + end - start, label))
                break
    for start, end, label in reversed(edits):
        text = text[:start] + label + text[end:]
        counts['recovered_statuses'] += 1
    return text


def normalize(text, counts, original=None):
    text = recover_statuses(text, original, counts)

    def numerical(match):
        counts['numerical_labels'] += 1
        return numerical_label(match)

    def verified(match):
        counts['semantic_labels'] += 1
        return 'Verified: ' + ('verified' if match[1].lower() == 'verified' else 'unverified')

    def terminology(match):
        counts['terminology'] += 1
        name = 'numerical' if match[1] == '1' else 'semantic'
        if match[0].isupper():
            return name.upper()
        return name.capitalize() if match[0][0].isupper() else name

    text = FIDELITY.sub(numerical, text)
    text = VERIFIED.sub(verified, text)
    return TIERS.sub(terminology, text)


def transform(content, path, counts, original=None):
    text = content.decode('utf-8')
    old_text = original.decode('utf-8') if original else None

    def visit(value, old=None):
        if isinstance(value, str):
            return normalize(value, counts, old if isinstance(old, str) else None)
        if isinstance(value, list):
            old = old if isinstance(old, list) else []
            # Match dataset records by identity even if their order changed.
            by_id = {r.get('id', r.get('name')): r for r in old
                     if isinstance(r, dict) and r.get('id', r.get('name')) is not None}
            return [visit(v, by_id.get(v.get('id', v.get('name')),
                                      old[i] if i < len(old) else None)
                          if isinstance(v, dict) else old[i] if i < len(old) else None)
                    for i, v in enumerate(value)]
        if isinstance(value, dict):
            old = old if isinstance(old, dict) else {}
            return {normalize(k, counts): visit(v, old.get(k)) for k, v in value.items()}
        return value

    if path.endswith('.jsonl'):
        rows = [json.loads(line) for line in text.splitlines()]
        old = [json.loads(line) for line in old_text.splitlines()] if old_text else None
        output = ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in visit(rows, old))
    elif path.endswith('.json'):
        output = json.dumps(visit(json.loads(text), json.loads(old_text) if old_text else None),
                            ensure_ascii=False, indent=2) + '\n'
    else:
        output = normalize(text, counts, old_text)
    # Avoid formatting-only changes in JSON that contains no affected text.
    return output.encode('utf-8') if output != text and counts else content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='fail if replacements remain')
    args = parser.parse_args()
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    script_rel = Path(__file__).relative_to(ROOT).as_posix()
    sums_path = ROOT / 'SHA256SUMS'
    sums = {rel: sha for sha, rel in
            (line.split('  ', 1) for line in sums_path.read_text().splitlines())} if sums_path.exists() else {}
    files = sorted((set(filter(None, tracked)) | set(sums)) - {'SHA256SUMS', script_rel})
    changes, renames = {}, {}
    counts = Counter()
    for rel in files:
        path = ROOT / rel
        if not path.is_file() or path.is_symlink():
            continue
        content = path.read_bytes()
        original = None
        if b'Numerical: Yes' in content or b'Numerical: No' in content:
            result = subprocess.run(['git', 'show', 'HEAD:' + rel], cwd=ROOT,
                                    capture_output=True, check=False)
            original = result.stdout if result.returncode == 0 else None
        local_counts = Counter()
        try:
            updated = transform(content, rel, local_counts, original)
        except UnicodeDecodeError:
            continue
        counts.update(local_counts)
        target = TIERS.sub(lambda m: 'numerical' if m[1] == '1' else 'semantic', rel)
        if target != rel:
            if (ROOT / target).exists():
                raise RuntimeError('Rename destination already exists: ' + target)
            renames[rel] = target
        if updated != content or target != rel:
            if rel in sums and digest(content) != sums[rel]:
                raise RuntimeError('Pre-existing checksum mismatch: ' + rel)
            changes[rel] = updated

    print(json.dumps({'files_to_update': len(changes), 'renames': renames,
                      'replacements': dict(counts)}))
    if args.check:
        raise SystemExit(bool(changes))

    manifest_rel = 'numerical check/source_manifest.json'
    manifest = json.loads(changes.get(manifest_rel, (ROOT / manifest_rel).read_bytes()))
    hashes = {}
    for row in manifest['files'] + manifest.get('vendored_files', []):
        rel = row['path']
        if rel in changes:
            hashes[row['sha256']] = digest(changes[rel])
            row.setdefault('original_sha256', row['sha256'])
            row['sha256'] = hashes[row['sha256']]
            row['matches_source_commit'] = False
    if hashes:
        changes[manifest_rel] = (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode()
        declarations_rel = 'numerical check/declarations.jsonl'
        rows = [json.loads(line) for line in
                changes.get(declarations_rel, (ROOT / declarations_rel).read_bytes()).decode().splitlines()]
        for row in rows:
            row['source_file_sha256'] = hashes.get(row['source_file_sha256'], row['source_file_sha256'])
        changes[declarations_rel] = ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in rows).encode()

    for rel, content in changes.items():
        target = renames.get(rel, rel)
        (ROOT / target).write_bytes(content)
        if target != rel:
            (ROOT / rel).unlink()
            sums.pop(rel, None)
        sums[target] = digest(content)
    sums[script_rel] = digest(Path(__file__).read_bytes())
    if sums_path.exists():
        sums_path.write_text(''.join(f'{sha}  {rel}\n' for rel, sha in sorted(sums.items())))


if __name__ == '__main__':
    main()
