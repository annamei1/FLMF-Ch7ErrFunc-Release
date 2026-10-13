# DLMF 7.13.5 — the displayed `λ⁻³` coefficient is incomplete (missing `+ 1/π²`)

**Status:** open upstream (DLMF erratum candidate). FLMF side repaired 2026-08-12,
proven sorry-free 2026-08-14. This is FLMF's second discovered DLMF misprint,
after 20.10.4/20.10.5 (see `docs/DLMF_MISPRINT.pdf`).

## The display

DLMF §7.13(iii) (https://dlmf.nist.gov/7.13) gives, for the `n`-th complex zero
`zₙ = xₙ + iyₙ` of the Fresnel integral `C(z)` (and, by the section's
cross-reference, of `S(z)` with the 7.13.7 parameters):

```
xₙ ≈ λ + α(απ − 4)/(8πλ³) ,        yₙ ≈ α/(2λ)                     (7.13.5)
```

with (7.13.6, for `C`): `λ = √(4n − 1)`, `α = (2/π)·ln(πλ)`, and (7.13.7, for
`S`): `λ = 2√n`, `α = (2/π)·ln(πλ)`.

## The misprint

The `λ⁻³` coefficient of `xₙ` is incomplete. Deriving the expansion from DLMF's
own 7.5.3 (`C = ½ + f·sin(πz²/2) − g·cos(πz²/2)`, with the auxiliary-function
asymptotics `f ~ 1/(πz)`, `g ~ 1/(π²z³)` of §7.12), the zero equation gives

```
z² = λ² + (2i/π)·ln(πz) + 2/(π²z²) + ⋯
```

and hence

```
xₙ = λ + (α²/8 − α/(2π) + 1/π²)·λ⁻³ + ⋯ .
```

The displayed coefficient is `α(απ − 4)/(8π) = α²/8 − α/(2π)` — the `g`-term
contribution `+ 1/π²` is missing. The residual at DLMF's approximant is
therefore exactly `λ⁻³/π² + o(λ⁻³)`: the approximation error is `Θ(λ⁻³)`, not
`o(λ⁻³)`.

## Numerical evidence

Residual-scaling numerics (guarded mpmath, run to `n = 1000`, two independent
scripts in agreement; recorded 2026-08-12 in the `fresnel-7-13-5-lambda3-misprint`
entry of `docs/ERRATA.md`): with `xₙ` the true `n`-th zero's real part and
`approxₙ = λ + α(απ−4)/(8πλ³)`,

| `n` | `(xₙ − approxₙ)·λ³` (C family) |
|---:|---:|
| 20 | 0.10013 |
| 100 | 0.10102 |
| 1000 | 0.10128 |

approaching `1/π² = 0.101321…`; the `S` family behaves identically. The
imaginary part is unaffected: `(yₙ − α/(2λ))·λ³` stays bounded
(`≈ −0.0325`, i.e. the error there is `Θ(log λ · λ⁻³)`, comfortably inside the
`o(λ⁻¹)` the display supports).

## Consequences for formalization

- Any formal statement asserting the real-part error `o(λ⁻³)` at DLMF's
  approximant is **false**. The sharp true bound at that approximant is
  `O(λ⁻³)` (attained: the error is `Θ(λ⁻³)`).
- The imaginary-part conjunct at `o(λ⁻¹)` is true (its error is
  `Θ(log λ · λ⁻³)`).
- A corrected approximant `λ + (α²/8 − α/(2π) + 1/π²)·λ⁻³` would restore an
  `o(λ⁻³)` real-part statement, but would no longer transcribe the DLMF display.

## FLMF resolution

`FLMF/Functions/Error/ComplexZeros.lean`:

- The approximant definitions `fresnelCZeroReApprox` / `fresnelCZeroImApprox`
  (and the `S` twins) transcribe the DLMF display **verbatim** — the misprinted
  coefficient is deliberately kept, so the defs remain faithful transcriptions.
- The canonical carrier `erf_7_13_5_full` states the sharp true content at
  DLMF's approximant: real parts `=O[atTop] λ⁻³`, imaginary parts
  `=o[atTop] λ⁻¹`, for both `C` and `S` enumerations (1-based, sub-diagonal
  mirror-pair representatives — see the docstring for the enumeration
  subtleties). It is **proven sorry-free** (closed 2026-08-14 by the
  argument-principle zero-count campaign).
- The theorem is intentionally `Verified: unverified`: Tier-2 judges it against
  the printed display, and the deviation (`O(λ⁻³)` at the true strength vs the
  display's misprinted coefficient) is exactly the erratum, not a transcription
  error. It is the one chapter-7 target expected to stay divergent until the
  DLMF itself is corrected.

## History

| date | event |
|---|---|
| 2026-07-27 | Tier-2 re-judge flags the imaginary-part conjunct overclaim (`o(λ⁻³)` → weakened to `o(λ⁻¹)`); ERRATA `erf-7-13-5-im-order`. |
| 2026-08-05 | Forensic pass: earlier false-FAITHFUL traced to truncated DLMF cache chunks (index-origin sentence cut at a `<table>` boundary); per-conjunct falsity analysis; ERRATA `misindexed-713-zeros` addendum. |
| 2026-08-12 | Mirror-pair vacuity found and repaired (whole-quadrant modulus ordering unsatisfiable; ERRATA `fresnel-7-13-5-mirror-vacuous`); the `λ⁻³` misprint discovered numerically and confirmed analytically (ERRATA `fresnel-7-13-5-lambda3-misprint`); statements repaired to the sharp `O(λ⁻³)` form. |
| 2026-08-14 | `erf_7_13_5_full` proven sorry-free (ComplexZeros.lean fully sorry-free). |

## Cross-references

- `docs/ERRATA.md` — entries `fresnel-7-13-5-lambda3-misprint` (the misprint),
  `fresnel-7-13-5-mirror-vacuous`, `erf-7-13-5-im-order`, and the
  `misindexed-713-zeros` addendum (index origin, cache truncation).
- `FLMF/Functions/Error/ComplexZeros.lean` — `erf_7_13_5_full` (carrier),
  `erf_7_13_5`, `erf_7_13_5_S` (component forms), approximant/parameter defs.
- `docs/DLMF_MISPRINT.pdf` — the 20.10.4/20.10.5 precedent (theta-function
  chapter), FLMF's first DLMF misprint find.
- `docs/STANDING_CONSTRAINTS.md` — the `7.13.` bullet (1-based zero
  enumeration), which governs the index convention used here.
