# Validation — 2026-10-13

The standalone package built successfully with `lake build Chapter7` under
Lean/Mathlib 4.30.0. The build targeted Chapter 7 and its transitive imports;
it did not build the full FLMF library. Existing dependency caches were reused.
The package uses its bundled FLMF and Watson sources, with no dependency on a
sibling FLMF or picard-lefschetz repository. A network-only, empty-cache
installation was not tested.

A fresh `lake env lean scripts/Audit.lean` run then queried each declaration's
elaborated type, source range, and transitive axioms using `Lean.collectAxioms`.
All 138 records were returned successfully, with no missing declarations or
non-JSON output. Exact declaration text is sliced from the preserved source
using the compiler's ranges; implicit assumptions appear in the elaborated type.

| Measure | Result |
|---|---:|
| Numbered Chapter 7 equations | 137 |
| Exported declarations | 138 |
| Theorems | 124 |
| Definitions | 14 |
| Theorems using only standard Lean axioms | 122 |
| Definitions using only standard Lean axioms | 14 |
| Declarations depending on `sorryAx` | 2 |
| Declarations with other nonstandard axioms | 0 |
| Historical equation-level fidelity passage | 136/137 |

Standard axioms mean only `propext`, `Classical.choice`, and `Quot.sound`.
The axiom audit concerns proof/construction completeness, not mathematical
faithfulness to the intended informal source.

## All declarations depending on an admission

| Equation | Declaration | Location |
|---|---|---|
| 7.17.3 | `FLMF.Error.erf_7_17_3_full` | `FLMF/Functions/Error/Ch7InverseErfExpansion.lean:921` |
| 7.18.13 | `FLMF.Error.cerf_7_18_13` | `FLMF/Functions/Error/ComplexErfcFraction.lean:417` |

The actual source ranges and full axiom lists are recorded per declaration in
`data/declarations.jsonl` and `data/axiom_audit.jsonl`. Supporting-module
admissions do not automatically invalidate every importing theorem; the above
list follows actual transitive declaration dependencies.

## Dataset and packaging checks

- All 137 equation targets have at least one exported declaration.
- Declaration IDs are unique. Equation 7.17.2 has two exported carriers; every
  other equation has one. No record is assigned to a different chapter.
- All 125 bundled FLMF modules match the recorded FLMF source commit. Of these,
  44 are the Chapter 7 modules/root and 81 are supporting imports.
- The import closure is complete, allowing only Mathlib and the bundled Watson
  module as external imports.
- All 137 archived DLMF extraction records are present and hashed.
- Exact source excerpts agree with Lean's declaration ranges.
- Every dataset declaration has an axiom-audit record, with matching type and
  proof-status fields.
- Distribution hashes are recorded in `SHA256SUMS` and checked by
  `python3 scripts/validate.py`.

The older progress scanner reported 212 tagged declarations because it did not
fully honor multi-line `-- no-dlmf` exclusion comments. This export follows those
author exclusions across contiguous comment lines, retaining 138 intended
surface declarations and all 137 targets. Supporting lemmas remain in the Lean
source files as needed for the proofs.

No numerical sweep, semantic-model review, mathematical correction, or proof
repair was performed as part of packaging. Historical fidelity records retain
their original verdicts and unchecked reasons.
