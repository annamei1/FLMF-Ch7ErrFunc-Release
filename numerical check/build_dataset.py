#!/usr/bin/env python3
"""Rebuild the Chapter 7 inventory from bundled sources; no detector is run.

The tag selection follows FLMF's equation-level convention and honors all
contiguous no-dlmf exclusion comments, including multi-line annotations.
Lean's elaborated types and transitive axioms come from numerical check/Audit.lean.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TAG = re.compile(r'(?:DLMF\s+§?\s*|§)([0-9]+\.[0-9]+\.[0-9]+)')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|partial\s+|local\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([\w\']+)', re.M)

def dump(path, obj):
    (ROOT / path).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')

def namespace(prefix):
    stack = []
    for line in prefix.splitlines():
        line = line.strip()
        m = re.fullmatch(r'namespace\s+([\w.]+)', line)
        if m:
            stack.append(m[1])
        m = re.fullmatch(r'end\s+([\w.]+)', line)
        if m and stack and stack[-1] == m[1]:
            stack.pop()
    return '.'.join(stack)

def scan():
    records = []
    manifest = json.loads((ROOT / 'numerical check/source_manifest.json').read_text())
    for file in manifest['files']:
        p = ROOT / file['path']
        assert hashlib.sha256(p.read_bytes()).hexdigest() == file['sha256'], 'Source snapshot changed: ' + file['path']
        text = p.read_text()
        for doc in re.finditer(r'/--(.*?)-/', text, re.S):
            tags = sorted({t for t in TAG.findall(doc[1]) if t.startswith('7.')}, key=lambda s: list(map(int, s.split('.'))))
            if not tags:
                continue
            suppressed = False
            for line in reversed(text[:doc.start()].splitlines()):
                line = line.strip()
                if not line:
                    continue
                if line.startswith('-- no-dlmf'):
                    suppressed = True
                    break
                if not line.startswith('--'):
                    break
            if suppressed:
                continue
            rest = text[doc.end():]
            decl = DECL.search(rest)
            if not decl:
                continue
            gap = rest[:decl.start()]
            if any(s.strip() and not s.strip().startswith('--') for s in gap.splitlines()):
                continue
            if any(s.strip().startswith('-- no-dlmf') for s in gap.splitlines()):
                continue
            ns = namespace(text[:doc.start()])
            name = '.'.join(filter(None, [ns, decl[2]]))
            start = doc.end() + decl.start()
            # Find the first non-whitespace line of the actual declaration.
            start += len(text[start:]) - len(text[start:].lstrip())
            records.append({
                'id': name, 'name': name, 'short_name': decl[2], 'kind': decl[1],
                'equations': tags, 'source_file': file['path'],
                'source_line': text[:start].count('\n') + 1,
                'source_file_sha256': file['sha256'],
                'docstring': doc[1].strip(),
                'dlmf_urls': ['https://dlmf.nist.gov/' + t.rsplit('.', 1)[0] + '#E' + t.rsplit('.', 1)[1] for t in tags],
                'proof_status': 'not_audited',
                'fidelity_status': 'historical_evidence_only',
            })
    assert len({r['id'] for r in records}) == len(records), 'Duplicate qualified declaration names'
    return sorted(records, key=lambda r: r['id'])

def main():
    records = scan()
    names = ',\n    '.join(json.dumps(r['name'], ensure_ascii=False) for r in records)
    audit = '''import Chapter7
import Lean.Util.CollectAxioms

set_option pp.universes true
set_option pp.fullNames true
set_option format.width 120

-- Full elaborated types include implicit section variables and typeclass assumptions.
-- collectAxioms follows actual declaration dependencies, not merely file imports.
run_cmd Lean.Elab.Command.liftTermElabM do
  let names : Array String := #[
    NAMES
  ]
  for s in names do
    let n := s.toName
    let info ← Lean.getConstInfo n
    let axioms ← Lean.collectAxioms n
    let type ← Lean.Meta.ppExpr info.type
    let some ranges ← Lean.findDeclarationRanges? n | throwError "Missing source range for {n}"
    let r := ranges.range
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson s),
      ("source_range", Lean.toJson #[r.pos.line, r.pos.column, r.endPos.line, r.endPos.column]),
      ("elaborated_type", Lean.toJson type.pretty),
      ("axioms", Lean.toJson (axioms.map toString))]
    IO.println row.compress
'''.replace('NAMES', names)
    (ROOT / 'numerical check/Audit.lean').write_text(audit)
    audit_path = ROOT / 'numerical check/axiom_audit.jsonl'
    audits = {}
    if audit_path.exists():
        audits = {r['name']: r for r in map(json.loads, audit_path.read_text().splitlines())}
        assert set(audits) == {r['name'] for r in records}, 'Audit membership does not match source inventory'
    for r in records:
        if r['name'] in audits:
            a = audits[r['name']]
            r['elaborated_type'] = a['elaborated_type']
            if 'source_range' in a:
                r['source_range'] = a['source_range']
                start_line, start_col, end_line, end_col = a['source_range']
                source_lines = (ROOT / r['source_file']).read_text().splitlines(keepends=True)
                prefix = sum(len(s) for s in source_lines[:start_line - 1]) + start_col
                end = sum(len(s) for s in source_lines[:end_line - 1]) + end_col
                r['lean_source'] = ''.join(source_lines)[prefix:end]
            r['axioms'] = sorted(a['axioms'])
            extra = set(a['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'}
            r['proof_status'] = ('depends_on_sorry' if 'sorryAx' in extra else
                                 'other_axioms' if extra else 'standard_axioms_only')
    (ROOT / 'numerical check/declarations.jsonl').write_text(''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in records))
    t2 = json.loads((ROOT / 'numerical check/evidence/semantic_manifest.json').read_text()) + json.loads((ROOT / 'numerical check/evidence/semantic_definitions.json').read_text())
    t1 = json.loads((ROOT / 'numerical check/evidence/extract_manifest.json').read_text())
    faithful = {r['name'] for r in t2 if r.get('verdict') == 'FAITHFUL'}
    veto = {t for r in t1 if r.get('verdict') == 'FAIL' for t in r.get('tags', [])}
    source_refs = {r['equation']: r for r in json.loads((ROOT / 'numerical check/dlmf_source_manifest.json').read_text())['records']}
    eqs = []
    for target in json.loads((ROOT / 'numerical check/equation_targets.json').read_text()):
        tag = target['dlmf']
        ds = [r for r in records if tag in r['equations']]
        assert ds, 'Uncovered equation ' + tag
        eqs.append({'equation': tag, 'source_reference': source_refs.get(tag), 'declaration_ids': [r['id'] for r in ds],
                    'historical_fidelity_passed': tag not in veto and (any(r['short_name'] in faithful for r in ds) or any(r.get('tag') == tag and r.get('verdict') == 'FAITHFUL' for r in t2)),
                    'historical_fidelity_witnesses': sorted({r['name'] for r in t2 if r.get('verdict') == 'FAITHFUL' and (r.get('tag') == tag or r['name'] in {d['short_name'] for d in ds})}),
                    'proof_status_by_declaration': {r['id']: r['proof_status'] for r in ds},
                    'source_exception': 'documented_source_misprint' if tag == '7.13.5' else None})
    dump('numerical check/equations.json', eqs)
    print(json.dumps({'equations': len(eqs), 'declarations': len(records), 'historical_fidelity_passed': sum(r['historical_fidelity_passed'] for r in eqs), 'audited': len(audits)}))

if __name__ == '__main__':
    main()
