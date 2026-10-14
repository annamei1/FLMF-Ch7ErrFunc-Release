# FLMF Chapter 7 Release

This is an FLMF Chapter 7 release on **error functions, Dawson's integral, and
Fresnel integrals**, containing **137 numbered DLMF equations**.
All included Lean formalizations are verified by our proof pipeline, and
**78 equations carry numerical PASS annotations**.

Each equation carries its corresponding DLMF tag in the Lean source, so you can
search for its equation number to find the formalization. For example, search
for `DLMF 7.4.2` to find the complementary error function symmetry theorem
`FLMF.Error.cerfc_neg` in [Symmetry.lean](FLMF/Chapter7/Symmetry.lean).

The repository contains Chapter 7 sources, their required supporting mathematics,
and the numerical checking method. Generated results and archived verification
records are excluded.

## Lean build

Install Lean's `elan` toolchain manager, then run:

```sh
lake exe cache get
lake build Chapter7
```

The package pins Lean 4.30.0 and its Mathlib dependency. Use `import Chapter7`
to import the chapter. `FLMF/Chapter7/` contains the chapter modules;
`FLMF/Support/` contains their transitive local dependencies.

## Numerical check

From the repository root, create the Python environment and install the checker dependencies:

```sh
python3 -m venv "numerical check/.venv"
"numerical check/.venv/bin/python" -m pip install -r "numerical check/requirements.txt"
```

Run a fresh check of a selected declaration:

```sh
"numerical check/.venv/bin/python" "numerical check/run_stale.py" --name cerfc_neg
```

Repeat `--name` to select several declarations, use `--all` to rerun all
numerically annotated declarations, or add `--limit N` for a smaller run.
Without a selection flag, the runner checks declarations marked `Numerical: Stale`.

The checker extracts DLMF-tagged statements from the Lean sources and compares
supported formulas at sampled inputs using high-precision numerical evaluations.
Each declaration runs in a separate process with time and memory limits. Results
are saved under `numerical check/results/` as `PASS`, `FAIL`, or `unable to proceed`.
Unsupported statements receive `unable to proceed`; a numerical PASS records
sampled agreement. Running the checker leaves the Lean sources and annotations
unchanged.

See [numerical check/README.md](<numerical check/README.md>) for method details,
resource limits, and output formats. See [LICENSE](LICENSE) for the source license.
