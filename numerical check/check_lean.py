#!/usr/bin/env python3
"""Rebuild Chapter7 and compare a fresh Lean audit with the released records."""
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    subprocess.run(['lake', 'build', 'Chapter7'], cwd=ROOT, check=True)
    result = subprocess.run(['lake', 'env', 'lean', 'numerical check/Audit.lean'],
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    # Parse the entire output: never drop errors or non-JSON lines.
    fresh = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    saved = [json.loads(line) for line in (ROOT / 'numerical check/axiom_audit.jsonl').read_text().splitlines()]
    def normalized(rows):
        assert len({r['name'] for r in rows}) == len(rows)
        return {r['name']: (r['elaborated_type'], sorted(r['axioms']), r['source_range']) for r in rows}
    assert normalized(fresh) == normalized(saved), 'Fresh Lean audit differs from the release snapshot'
    print(f'Lean build and all {len(fresh)} declaration audits match the release snapshot.')

if __name__ == '__main__':
    main()
