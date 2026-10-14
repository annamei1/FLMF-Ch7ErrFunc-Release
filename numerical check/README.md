# Numerical checks

The checker extracts DLMF-tagged Lean statements from `FLMF/Chapter7/`,
translates supported formulas into numerical expressions, and compares them
at sampled inputs using high-precision `mpmath` evaluations. The Python engine
and its convention registry are in `vendor/`.

## Setup and use

From the repository root, using Python 3.9 or newer on macOS or Linux:

```sh
python3 -m venv 'numerical check/.venv'
'numerical check/.venv/bin/python' -m pip install -r 'numerical check/requirements.txt'
'numerical check/.venv/bin/python' 'numerical check/run_stale.py' --name cerfc_neg
```

Repeat `--name` to select several Chapter 7 declarations. Use `--all` to check
every numerically annotated Chapter 7 declaration, or add `--limit N` for a
smaller run. Without a selection flag, the runner selects `Numerical: Stale`
annotations and reports when none remain. `--root PATH` selects another checkout
with the same source layout. The Lean build is independent of the checker.

## Method and limits

Each declaration runs in a fresh worker process, with one worker at a time.
Defaults are 512 MB of resident memory, 85 seconds of CPU time, and 90 seconds
of wall time per declaration. The parent monitors memory every 0.1 seconds;
on Linux, the worker also applies heap and address-space limits. Configure
these bounds with `--memory-mb`, `--cpu-seconds`, and `--wall-seconds`.
The engine applies an 8-second per-sample budget and bounded-series protections.

`PASS` means agreement at the sampled inputs; `FAIL` means a sampled discrepancy.
Unsupported statements, extraction errors, timeouts, and memory-limit failures
receive `unable to proceed`. A numerical PASS is sampled evidence, not a Lean
proof or a guarantee of agreement at every input.

The runner reads the Lean sources without changing them or their annotations,
checks source hashes before and after the run, and always computes fresh results.

## Output

Runs are saved under the Git-ignored `results/` folder. `results/latest.json`
identifies the latest run. Each run contains selected declarations and source
hashes, checker hashes and dependency versions, configured limits, individual
JSON results and logs, a summary, and a readable report. Outputs are written
incrementally so completed results survive an interrupted run.

The repository distributes the method; generated runs and archived verification
records are excluded. The engine's license is in [vendor/LICENSE](vendor/LICENSE).
