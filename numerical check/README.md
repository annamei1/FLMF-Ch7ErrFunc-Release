# Numerical checks and verification records

This folder contains a copy of the numerical auto-extractor from
`~/Documents/GitHub/FLMF-port`, its direct runtime dependencies, and a local
runner for local Lean declarations. By default it selects `Numerical: Stale`
annotations; `--name` and `--all` request fresh reruns regardless of status.
The four upstream Python modules are unchanged. Their original filenames and
terminology are retained so their hashes can be verified against the source.
See `provenance.json` for the upstream commit and copied-file hashes.

The runner does not compile Lean, import into the Lean package, reuse historical
PASS results, or write to mathematical sources or release evidence. Each fresh
run selects all matching declarations, including supporting modules, and writes
its results beneath this folder. Historical annotations remain historical until
explicitly updated using the new evidence.

## Folder contents

The former `data`, `tools`, and `scripts` folders are combined here. Dataset
JSON/JSONL files and maintenance scripts are at this folder's top level.
`evidence/` and `dlmf_source/` retain archived review and reference material;
`vendor/` contains the unchanged Python numerical engine, and `results/`
contains numerical runs. `Audit.lean`, `check_lean.py`, and `validate.py` also
support the Lean proof audit and package checks.

`build.json` and `audit.json` retain the original 2026-10-13 release validation
summaries, including their original commands and proof-gap counts. They are
historical records. Current proof status is recorded in `axiom_audit.jsonl`
and the updated [validation report](../docs/VALIDATION.md).

## Setup and use

From the repository root:

```sh
python3 -m venv 'numerical check/.venv'
'numerical check/.venv/bin/python' -m pip install -r 'numerical check/requirements.txt'
'numerical check/.venv/bin/python' 'numerical check/run_stale.py'
```

If there are no stale annotations, the default command reports that there is
nothing pending. To run a fresh check explicitly:

```sh
'numerical check/.venv/bin/python' 'numerical check/run_stale.py' --name cerfc_neg --name erf_7_4_3 --name erf_7_19_4
```

Repeat `--name` for multiple short declaration names, use `--all` to check all
numerical annotations, or combine either selection with `--limit N`.
All paths in these commands are quoted because the folder name contains a space.

The environment stays in this folder and is ignored by Git. Only `mpmath` and
`psutil` are needed for this numerical run; the upstream registry's optional
SciPy and SymPy dependencies are not installed.

## Memory and time controls

- One declaration per fresh worker process; concurrency is always one.
- A separate parent checks worker resident memory every 0.1 seconds and kills
  the worker above 512 MB. macOS rejects heap/address-space resource limits in
  this environment, so resident memory is enforced by the watchdog. A polling
  limit can briefly overshoot between observations.
- Each worker has an operating-system CPU limit of 85 seconds and a parent
  wall-clock limit of 90 seconds.
- The upstream checker retains its original 8-second per-sample budget and
  bounded-series protections; numerical tolerances and verdict logic are unchanged.
- Memory limits, timeouts, extraction failures, and other worker errors are
  reported as `unable to proceed`; they never become PASS.

The controls can be configured with `--memory-mb`, `--wall-seconds`, and
`--cpu-seconds`. `--limit N` selects only the first N declarations from the
chosen selection for a smoke run. The separate watchdog was tested with a deliberately low 1 MB cutoff.

## Results

`results/latest.json` points to the latest run. Each run includes:

- `targets.json`: the selected declarations and source hashes.
- `run.json`: the checker provenance, dependency versions, controls, and source hashes.
- `manifest.json`: every result, written incrementally after each declaration.
- `summary.json`: verdict counts and the observed peak worker memory.
- `report.txt`: every verdict and exact checker reason, including every unchecked case.
- Per-declaration JSON and logs, including recorded process exit codes and memory peaks.

`unable to proceed` means the declaration was not numerically checked to the
checker's gate. PASS is a sampled numerical result, not a Lean proof or a semantic
verification stamp. The runner verifies that source files remain unchanged.

## Applying reviewed results

On an explicit request to update labels, run:

```sh
python3 'numerical check/apply_results.py'
python3 'numerical check/validate.py'
```

The application script verifies the completed run and checked source hashes,
then replaces each selected stale annotation with `Numerical: PASS`,
`Numerical: FAIL`, or `Numerical: N/A (<kind>)`. It refreshes exported declaration
text and source/checksum metadata. Semantic annotations and the original review
results are preserved. `labels_applied.json` records which run supplied the labels.

## Relocation test — 2026-10-14

A fresh run from outside the repository checked four declarations. Three
passed: `cerfc_neg`, `erf_7_4_3`, and `erf_7_19_4`. `erf_7_17_1` returned
`unable to proceed` with kind `unparsed:forall-body unconsumed`; the current
numerical engine does not parse that quantified statement. This is retained
as an unchecked result, and no source annotations were changed.

The complete report is
[results/2026-10-14_120113_082285/report.txt](results/2026-10-14_120113_082285/report.txt).
All four workers exited normally, the observed maximum worker RSS was 35.297 MB,
and every Lean source hash remained unchanged. The relocated Python environment,
pinned engine files, dataset generator, package validator, and Lean audit were
also checked.
