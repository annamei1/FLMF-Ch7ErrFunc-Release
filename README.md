# FLMF Chapter 7

A standalone dataset and Lean source snapshot for **DLMF Chapter 7: Error
Functions, Dawson's and Fresnel Integrals**. Snapshot date: **2026-10-13**.

The dataset contains **137 numbered DLMF equations**, linked to **138 tagged
Lean declarations**. Multiple declarations can represent different parts,
domains, or formulations of one equation. Infrastructure declarations marked `-- no-dlmf` are excluded, including markers
spanning several comment lines. This resolves the older progress scanner's
overcount of 212 tagged declarations; all 137 equations remain covered.
The inventory does not assert that
these declarations are interchangeable or that any one is automatically a
canonical complete formalization of the source equation.

This is a release candidate with explicit proof gaps. Successful compilation
permits Lean's `sorry` admissions; it is not a certificate that every theorem
has a complete proof. See [validation](docs/VALIDATION.md) for the fresh
transitive axiom audit and [known issues](docs/KNOWN_ISSUES.md).

## Contents

- `data/equations.json`: one record per numbered Chapter 7 equation, with its
  declaration IDs and individual proof statuses.
- `data/declarations.jsonl`: one record per tagged declaration, including its
  qualified name, source location, exact Lean declaration text (including its
  definition or proof body), documentation, elaborated Lean type, and
  transitive axioms. Elaborated types include implicit section assumptions.
- `data/axiom_audit.jsonl`: the machine-generated Lean audit output.
- `data/source_manifest.json`: original source commits, file roles, and hashes.
- `data/dlmf_source/`: archived DLMF extraction records, with LaTeX fragments,
  context, constraints, and source URLs. Their original contents are retained
  and hashed; they were not refetched or independently revalidated for this
  export. These cached fragments are not guaranteed complete standalone
  informal statements.
- `data/evidence/`: frozen Chapter 7 numerical/semantic review records. These
  are historical evidence, not freshly rerun checks or proof certificates.
- `FLMF/Functions/Error/` and the four required `FLMF/Functions/Fresnel/`
  modules: the Chapter 7 mathematical source.
- Other bundled `FLMF/` files: supporting modules in Chapter 7's transitive
  import closure. Their role is identified in the source manifest. No other
  chapter is included as a dataset, and the broader FLMF root is omitted.
- `vendor/picard-lefschetz/`: the required Watson module and its license.
- `Chapter7.lean`: the single entry point for this package.

The sources retain their original namespaces, paths, statements, proofs, and
comments. Older progress comments inside the copied files can be stale; the
release records and validation report document the status of this snapshot.
No audit-experiment datasets, scratch files, credentials, original Git history,
or compiled caches are distributed in this folder.

## Build

Install Lean's `elan` toolchain manager, then from this folder run:

```sh
lake exe cache get
lake build Chapter7
```

The toolchain is Lean **4.30.0**. Mathlib is pinned to commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0); transitive dependency
revisions are retained in `lake-manifest.json`. The Watson dependency is
vendored, so no sibling FLMF or picard-lefschetz checkout is required.
Initial dependency downloads require network access.

Use `import Chapter7` to import the whole chapter. Individual source modules
can also be imported by their preserved `FLMF.*` names.

## Validate and reproduce the inventory

Python 3 and the pinned Lean environment are sufficient; no API credentials
or external verification services are needed.

```sh
python3 scripts/validate.py
python3 scripts/check_lean.py
python3 scripts/build_dataset.py
lake env lean scripts/Audit.lean > /tmp/chapter7-axiom-audit.jsonl
```

`validate.py` checks snapshot hashes, import closure, dataset membership, and
consistency with the saved axiom audit. `check_lean.py` runs the targeted build
and compares a fresh Lean audit with the saved result, failing on any difference.
`build_dataset.py` reconstructs the
source inventory and generates `scripts/Audit.lean`; it uses the saved audit
when present. The last command independently reruns that audit. Check its
exit status before accepting its output. It must emit exactly one JSON record
per declaration; errors must never be discarded to fabricate a complete run.
For this unchanged snapshot, compare the new records with the saved audit by
name, elaborated type, and sorted axiom list.

`SHA256SUMS` covers all distributed files except itself. This is an immutable
snapshot manifest: intentional edits require a new snapshot and checksums.

## Interpretation

- `standard_axioms_only`: Lean reports no transitive axioms other than
  `propext`, `Classical.choice`, and `Quot.sound`. For definitions this describes
  construction dependencies, not a separate theorem proof.
- `depends_on_sorry`: the declaration depends on `sorryAx`, possibly through
  a helper whose admission does not appear in the declaration's own body.
- `other_axioms`: a nonstandard axiom other than `sorryAx` was found.
- `not_audited`: no Lean dependency audit is available; never treat this as
  a completed proof.

Historical equation-level fidelity passage is **136/137**, following the
original progress-report convention. It credits an equation when a stored
FAITHFUL judgment exists for a carrier and no recorded numerical FAIL vetoes
it. It does not certify every current variant. In particular, the 7.19.4
historical witness is the `lineBroadeningH` definition; this does not turn the
separate `erf_7_19_4` judgment into FAITHFUL. Witness names are preserved in each
equation record. No numerical or semantic checker was rerun for this export.

Equation **7.13.5** carries an explicit source-misprint exception. See the
[retained investigation](docs/DLMF_7_13_5_MISPRINT.md); this exception is not a
new verified stamp.

## Provenance and license

This snapshot is extracted from [FLMF](https://github.com/math-commons/FLMF).
Exact source revisions and per-file hashes are in `data/source_manifest.json`.
All bundled FLMF Lean source files match the recorded source commit; the
original working tree was not modified.

The mathematical reference is the [NIST DLMF, Chapter 7](https://dlmf.nist.gov/7).
Retain equation IDs and declaration IDs when citing or deriving datasets from
this release. A publication DOI and repository URL can be added after the
owner creates and publishes the new repository.

See [LICENSE](LICENSE) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
