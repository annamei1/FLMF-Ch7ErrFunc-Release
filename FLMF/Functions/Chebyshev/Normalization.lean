import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Chebyshev polynomials: explicit normalization constant (DLMF §18.3)

The Chebyshev polynomials of the first kind `Tₙ` are orthogonal on `[-1, 1]` with
respect to the weight `w(x) = (1 - x²)^(-1/2)`.  DLMF §18.3 records the explicit
*normalization constants* `hₙ = ∫ Tₙ²` of this orthogonal family:

```
hₙ = ⎧ π      if n = 0,
     ⎩ π / 2  if n ≥ 1.
```

In Mathlib the weighted measure is `Polynomial.Chebyshev.measureT`, namely Lebesgue
measure scaled by `√(1 - x²)⁻¹` and restricted to `(-1, 1]`.  We package the
diagonal (`n = m`) and off-diagonal (`n ≠ m`) integrals, and give the closed form
of the normalization constant as a single statement.
-/

open Real
open Polynomial
open Polynomial.Chebyshev
open scoped MeasureTheory

namespace FLMF.Functions.Chebyshev

-- no-dlmf: packaging def (re-exports Mathlib's `measureT` weight measure); not an identity.
/-- The Chebyshev weight `w(x) = (1 - x²)^(-1/2)` on `(-1, 1]`, as a measure. -/
noncomputable def chebyshevWeight : MeasureTheory.Measure ℝ := measureT

-- no-dlmf: instance of DLMF 18.2.1 / the j ≠ k case of DLMF 3.11.8 (off-diagonal
-- case only; DLMF's own §18.3 numbered equations 18.3.1-18.3.2 are a *discrete*
-- orthogonality sum over the zeros of T_{N+1}, not this continuous-weight
-- integral); faithful surface is `T_orthogonality_relation` (DLMF 3.11.8) in
-- FLMF.Functions.Chebyshev, and `inner_eq` below for the combined form.
/-- Distinct first-kind Chebyshev polynomials are orthogonal with respect to the
weight `(1 - x²)^(-1/2)`. -/
theorem orthogonal_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂chebyshevWeight = 0 :=
  integral_eval_T_real_mul_eval_T_real_measureT_of_ne h

-- no-dlmf: instance of DLMF 18.3 (fixed degree n = 0 of the Table 18.3.1 norm data); faithful surface is norm_sq_eq_normalizationConst
/-- The squared norm of `T₀` against the Chebyshev weight is `π` — the `n = 0` case
of the normalization constants recorded in DLMF Table 18.3.1. -/
theorem norm_sq_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂chebyshevWeight = π :=
  integral_eval_T_real_mul_self_measureT_zero

/-- **(DLMF 18.3, normalization for `n ≥ 1`)** — the squared norm of `Tₙ` is `π / 2`.

DAG: E-18.3.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem norm_sq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂chebyshevWeight = π / 2 :=
  integral_T_real_mul_self_measureT_of_ne_zero hn

-- no-dlmf: packaging def for the constant `hₙ`; the identity hₙ = ∫Tₙ² is DLMF 18.3 below.
/-- The DLMF normalization constant `hₙ`:  `π` for `n = 0`, and `π / 2` otherwise. -/
noncomputable def normalizationConst (n : ℕ) : ℝ :=
  if n = 0 then π else π / 2

/-- **(DLMF 18.3)** — the squared norm of `Tₙ` equals the closed-form normalization
constant `hₙ = π · (1 - δₙ₀/2)`.

DAG: E-18.3.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem norm_sq_eq_normalizationConst (n : ℕ) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂chebyshevWeight = normalizationConst n := by
  unfold normalizationConst
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using norm_sq_zero
  · rw [if_neg hn]; exact norm_sq_of_ne_zero hn

/-- **(DLMF 18.3)** — the full orthonormality relation: the integral of `Tₙ · Tₘ`
against the weight equals the Kronecker `δₙₘ` times the normalization constant.

DAG: E-18.3.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem inner_eq (n m : ℕ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂chebyshevWeight =
      if n = m then normalizationConst n else 0 := by
  rcases eq_or_ne n m with rfl | h
  · rw [if_pos rfl]; exact norm_sq_eq_normalizationConst n
  · rw [if_neg h]; exact orthogonal_of_ne h

end FLMF.Functions.Chebyshev
