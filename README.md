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

The three original Chapter 7 proof admissions have been repaired. All 138
exported declarations now use only standard Lean axioms in the refreshed
transitive audit. Supporting modules still contain admissions; compilation
alone is not a proof-completeness certificate. See [validation](docs/VALIDATION.md)
and [known issues](docs/KNOWN_ISSUES.md) for proof status and fidelity limitations.

## Contents

- `numerical check/equations.json`: one record per numbered Chapter 7 equation, with its
  declaration IDs and individual proof statuses.
- `numerical check/declarations.jsonl`: one record per tagged declaration, including its
  qualified name, source location, exact Lean declaration text (including its
  definition or proof body), documentation, elaborated Lean type, and
  transitive axioms. Elaborated types include implicit section assumptions.
- `numerical check/axiom_audit.jsonl`: the machine-generated Lean audit output.
- `numerical check/source_manifest.json`: original source commits, file roles, and hashes.
- `numerical check/dlmf_source/`: archived DLMF extraction records, with LaTeX fragments,
  context, constraints, and source URLs. Their original contents are retained
  and hashed; they were not refetched or independently revalidated for this
  export. These cached fragments are not guaranteed complete standalone
  informal statements.
- `numerical check/evidence/`: frozen Chapter 7 numerical/semantic review records and
  explicitly identified upstream review updates. These are review evidence,
  not proof certificates.
- `FLMF/Chapter7/`: 40 modules containing the Chapter 7 mathematical source,
  including the error functions and Fresnel integrals.
- `FLMF/Support/`: 68 supporting modules in the chapter's transitive import
  closure. No other chapter is included as a dataset.
- `numerical check/module_layout.json`: old-to-new module mappings. The source manifest
  retains the original paths and hashes in each module's `origins` records.
- `FLMF/Support/Watson.lean`: the integrated Picard–Lefschetz Watson
  implementation; its Apache License 2.0 is included in the root `LICENSE`.
- `Chapter7.lean`: the single entry point for this package.

The sources retain their original declaration namespaces and names. Module
paths were flattened on 2026-10-14, and small related modules were combined.
The Watson implementation was also integrated into `FLMF/Support/Watson.lean`,
retaining its `PicardLefschetz` declaration namespace.
Two source modules contain local proof repairs and updated proof documentation. `VoigtExtra.lean`
also incorporates the upstream 2026-10-14 update of `erf_7_19_4`, extending its
domain from positive `a` to every nonzero real `a`, with the corresponding proof.
Other local annotation edits are recorded in the source manifest. Older progress
comments inside the copied files can be stale; the release records and validation report document the status of this snapshot.
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
revisions are retained in `lake-manifest.json`. Mathlib is the only direct Lake
dependency. Watson's lemma is implemented locally in `FLMF/Support/Watson.lean`,
so no Picard–Lefschetz package or sibling checkout is required.
Initial dependency downloads require network access.

Use `import Chapter7` to import the whole chapter. Individual modules now use
`FLMF.Chapter7.*` or `FLMF.Support.*` import paths. Declaration names remain
unchanged, for example `FLMF.Error.erf_7_17_3_full`.

```text
Chapter7.lean
FLMF/
  Chapter7/   # 40 modules: chapter results and their direct foundations
  Support/    # 68 modules: reusable supporting mathematics
```

The Dawson definition, ODE, and asymptotic helpers share `Chapter7/Dawson.lean`.
The three parabolic-cylinder files share `Support/ParabolicCylinder.lean`;
the twelve Chebyshev files share `Support/Chebyshev.lean`. The empty zeros
overview is included in `Chapter7/ComplexZeros.lean`. The former error-function
umbrella is replaced by the root `Chapter7.lean` entry point. Import mappings
are recorded in [module_layout.json](<numerical check/module_layout.json>).

## Numerical checks

Dataset records, numerical tools, saved results, and maintenance scripts share
one folder: [`numerical check`](<numerical check/README.md>). It also contains
the historical release build and audit summaries from the former `validation`
folder. For a fresh sample:

```sh
'numerical check/.venv/bin/python' 'numerical check/run_stale.py' --name cerfc_neg --name erf_7_4_3 --name erf_7_19_4
```

See that folder's README for environment setup and result interpretation.

## Validate and reproduce the inventory

Python 3 and the pinned Lean environment are sufficient; no API credentials
or external verification services are needed.

```sh
python3 'numerical check/validate.py'
python3 'numerical check/check_lean.py'
python3 'numerical check/build_dataset.py'
lake env lean 'numerical check/Audit.lean' > /tmp/chapter7-axiom-audit.jsonl
```

`validate.py` checks snapshot hashes, import closure, dataset membership, and
consistency with the saved axiom audit. `check_lean.py` runs the targeted build
and compares a fresh Lean audit with the saved result, failing on any difference.
`build_dataset.py` reconstructs the
source inventory and generates `numerical check/Audit.lean`; it uses the saved audit
when present. The last command independently reruns that audit. Check its
exit status before accepting its output. It must emit exactly one JSON record
per declaration; errors must never be discarded to fabricate a complete run.
For this unchanged snapshot, compare the new records with the saved audit by
name, elaborated type, and sorted axiom list.

`SHA256SUMS` is an optional local integrity checklist. It and `docs/` are
ignored by Git and can remain available in this working copy. Validation also
checks the tracked source hashes and axiom records without these local files.

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
it. It does not certify every current variant. The frozen 7.19.4 historical
witness is the `lineBroadeningH` definition. The later upstream FAITHFUL review
of the updated `erf_7_19_4` statement is recorded separately in
`numerical check/evidence/semantic_updates.json`. Witness names are preserved in each
equation record. A subsequent [targeted numerical rerun](<numerical check/README.md>)
checked all 44 declarations previously marked `Numerical: Stale`: 38 passed and
6 returned `unable to proceed`. Their numerical labels now reflect those results.
The semantic checker was not rerun; the historical evidence records are retained.
The imported nonzero-`a` version of `erf_7_19_4` also passed a fresh numerical
check on 2026-10-14 and carries `Numerical: PASS` and `Verified: verified`.

Equation **7.13.5** carries an explicit source-misprint exception. See the
[retained investigation](docs/DLMF_7_13_5_MISPRINT.md); this exception is not a
new verified stamp.

## Provenance and license

This snapshot is extracted from [FLMF](https://github.com/math-commons/FLMF).
Exact source revisions and per-file hashes are in `numerical check/source_manifest.json`.
The recorded FLMF commit identifies the original snapshot. The source manifest
records the file reorganization, local proof repairs, and annotation changes.
Each new module retains its source origins and their original hashes. The upstream working tree was not modified.

The mathematical reference is the [NIST DLMF, Chapter 7](https://dlmf.nist.gov/7).
Retain equation IDs and declaration IDs when citing or deriving datasets from
this release. A publication DOI and repository URL can be added after the
owner creates and publishes the new repository.

See [LICENSE](LICENSE) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
