# Known issues in this snapshot

This package preserves the existing mathematical statements and proofs. Exporting
it does not close open proofs or alter verification decisions.

## Admitted Chapter 7 helpers

- `FLMF.Error.inverfc_gap_expansion`, in
  `FLMF/Functions/Error/Ch7InverseErfExpansion.lean`, is admitted. It feeds the
  full four-term inverse-erfc expansion `FLMF.Error.erf_7_17_3_full` (7.17.3).
- `FLMF.Error.cRepErfcPred_ne_zero_of_re_pos` and the private remainder-limit
  lemma in `FLMF/Functions/Error/ComplexErfcFraction.lean` are admitted. They
  feed `FLMF.Error.cerf_7_18_13`, the complex repeated-erfc continued fraction.

Supporting modules contain further admissions. File imports alone do not show
whether a Chapter 7 theorem uses them. The transitive axiom audit in
`data/axiom_audit.jsonl` and the declaration-level statuses are authoritative for
that question; the validation report lists all affected dataset declarations.

## Fidelity exception at 7.13.5

The source investigation in `DLMF_7_13_5_MISPRINT.md` records the incomplete
printed real-part coefficient. The current carrier preserves the printed
approximant and uses an `O(λ⁻³)` bound. Its historical fidelity stamp remains
unverified. The investigation is retained as history; references in that note
to other FLMF documents refer to the upstream source repository.

## Historical review scope

The historical 136/137 fidelity figure is equation-level, not a certification
of all 138 current declarations. Source or dependency changes can invalidate
older review evidence. No historical judgment has been silently upgraded, and
no fresh numerical or semantic verification was performed during packaging.
The original numerical verdicts and unchecked reasons are retained verbatim in
`data/evidence/extract_manifest.json`.

The source extraction caches can contain partial displays and surrounding
context. They are archived reference material, not newly validated standalone
natural-language/formal pairs. The 137 equation targets and 138 declarations
also have different units: do not treat them as 138 independent DLMF equations
or randomly split variants of one equation across training and evaluation.
