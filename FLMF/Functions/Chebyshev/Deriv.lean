import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Chebyshev derivative relations (DLMF §18.9)

We record the classical relations between the formal derivatives of the
Chebyshev polynomials of the first kind (`Tₙ`) and the polynomials of the
second kind (`Uₙ`).  The main statement is

* **(DLMF 18.9.21)** `Tₙ'(x) = n Uₙ₋₁(x)`,

together with the companion identity relating `Uₙ'` to `Tₙ₊₁` and `Uₙ`.
All statements are wrappers around Mathlib's `Polynomial.Chebyshev` API.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

variable {R : Type*} [CommRing R]

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9.21
-- surface is eval_derivative_firstKind_nat
/-- the formal derivative of the first-kind Chebyshev
polynomial is a scalar multiple of the second-kind one: `Tₙ' = n Uₙ₋₁`. -/
theorem derivative_firstKind_eq (n : ℤ) :
    derivative (T R n) = (n : R[X]) * U R (n - 1) :=
  T_derivative_eq_U n

-- no-dlmf: OVER-GENERAL — a formal-derivative identity over an arbitrary
-- commutative ring `R`, not the DLMF entry (a differentiation formula for
-- Chebyshev polynomials as functions of a real variable `x`); the faithful
-- DLMF 18.9.21 surface is eval_derivative_firstKind_nat
/-- `n`-restriction of `derivative_firstKind_eq`: `Tₙ' = n Uₙ₋₁` over an
arbitrary commutative ring `R`. -/
theorem derivative_firstKind_eq_nat (n : ℕ) :
    derivative (T R (n : ℤ)) = ((n : ℤ) : R[X]) * U R ((n : ℤ) - 1) :=
  derivative_firstKind_eq (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9.21
-- surface is derivative_firstKind_eq_real_nat
/-- real-coefficient specialization of `derivative_firstKind_eq`:
`Tₙ' = n Uₙ₋₁` over `ℝ`. -/
theorem derivative_firstKind_eq_real (n : ℤ) :
    derivative (T ℝ n) = (n : ℝ[X]) * U ℝ (n - 1) :=
  T_derivative_eq_U n

/-- **DLMF 18.9.21** — real-coefficient specialization: `Tₙ' = n Uₙ₋₁` over `ℝ`
(DLMF-faithful restriction of `derivative_firstKind_eq_real`: `n : ℕ`).
DAG: E-18.9.21.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem derivative_firstKind_eq_real_nat (n : ℕ) :
    derivative (T ℝ (n : ℤ)) = ((n : ℤ) : ℝ[X]) * U ℝ ((n : ℤ) - 1) :=
  derivative_firstKind_eq_real (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9.21
-- surface is eval_derivative_firstKind_nat
/-- Pointwise evaluation form: `Tₙ'(x) = n Uₙ₋₁(x)`. -/
theorem eval_derivative_firstKind (n : ℤ) (x : ℝ) :
    (derivative (T ℝ n)).eval x = (n : ℝ) * (U ℝ (n - 1)).eval x := by
  rw [derivative_firstKind_eq_real]
  simp

/-- **DLMF 18.9.21** — pointwise evaluation form: `Tₙ'(x) = n Uₙ₋₁(x)`
(DLMF-faithful restriction of `eval_derivative_firstKind`: `n : ℕ`).
DAG: E-18.9.21.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem eval_derivative_firstKind_nat (n : ℕ) (x : ℝ) :
    (derivative (T ℝ (n : ℤ))).eval x = ((n : ℤ) : ℝ) * (U ℝ ((n : ℤ) - 1)).eval x :=
  eval_derivative_firstKind (n : ℤ) x

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9.22
-- surface is add_one_mul_firstKind_eq_nat_dlmf
/-- the second-kind derivative relation:
`(n+1) Tₙ₊₁ = x Uₙ - (1 - x²) Uₙ'`. -/
theorem add_one_mul_firstKind_eq (n : ℤ) :
    ((n : R[X]) + 1) * T R (n + 1) = X * U R n - (1 - X ^ 2) * derivative (U R n) :=
  add_one_mul_T_eq_poly_in_U n

-- no-dlmf: OVER-GENERAL — a formal polynomial identity in `R[X]` over an
-- arbitrary commutative ring `R`, in a rearranged formulation; the DLMF entry
-- is an analytic differentiation formula for real `x` involving `√(1-x²)`.
-- The faithful DLMF 18.9.22 surface is add_one_mul_firstKind_eq_nat_dlmf.
/-- `n`-restriction of `add_one_mul_firstKind_eq`: `(n+1) Tₙ₊₁ = x Uₙ - (1 - x²) Uₙ'`
over an arbitrary commutative ring `R`. -/
theorem add_one_mul_firstKind_eq_nat (n : ℕ) :
    (((n : ℤ) : R[X]) + 1) * T R ((n : ℤ) + 1)
      = X * U R (n : ℤ) - (1 - X ^ 2) * derivative (U R (n : ℤ)) :=
  add_one_mul_firstKind_eq (n : ℤ)

/-- **DLMF 18.9.22** — `d/dx[(1-x²)^{1/2} Uₙ(x)] = -(n+1)(1-x²)^{-1/2} Tₙ₊₁(x)`
(DLMF-faithful restriction of `add_one_mul_firstKind_eq_nat`: real variable `x`
with `x² < 1`, stated as the analytic derivative via `Real.sqrt`).
DAG: E-18.9.22.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem add_one_mul_firstKind_eq_nat_dlmf (n : ℕ) (x : ℝ) (hx : x ^ 2 < 1) :
    HasDerivAt (fun x => Real.sqrt (1 - x ^ 2) * (U ℝ (n : ℤ)).eval x)
      (-(((n : ℤ) : ℝ) + 1) * (Real.sqrt (1 - x ^ 2))⁻¹ * (T ℝ ((n : ℤ) + 1)).eval x) x := by
  have hx0 : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  have hf : HasDerivAt (fun x : ℝ => (1 : ℝ) - x ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := hf.sqrt hx0
  have hU : HasDerivAt (fun x : ℝ => (U ℝ (n : ℤ)).eval x)
      ((derivative (U ℝ (n : ℤ))).eval x) x := (U ℝ (n : ℤ)).hasDerivAt x
  have hprod := hsqrt.mul hU
  have hpoly := add_one_mul_firstKind_eq_nat (R := ℝ) n
  have heval := congrArg (Polynomial.eval x) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.eval_intCast] at heval
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hsne : Real.sqrt (1 - x ^ 2) ≠ 0 := by
    have h1 : (0:ℝ) < 1 - x ^ 2 := by nlinarith
    exact (Real.sqrt_pos.mpr h1).ne'
  convert hprod using 1
  field_simp
  rw [hs2]
  linarith [heval]

-- no-dlmf: not itself DLMF 18.9.21 (a different, though related, identity —
-- the companion recurrence-differentiated form, over an arbitrary commutative
-- ring `R` rather than a real-variable analytic formula); the faithful DLMF
-- 18.9.21 surface is eval_derivative_firstKind_nat
/-- The Chebyshev ODE-style relation expressing `(1-x²) Tₙ₊₁'` through `Tₙ` and
`Tₙ₊₁` (companion identity to DLMF 18.9.21, obtained by differentiating the
three-term recurrence). -/
theorem one_sub_X_sq_mul_derivative_firstKind (n : ℤ) :
    (1 - X ^ 2) * derivative (T R (n + 1))
      = ((n : R[X]) + 1) * (T R n - X * T R (n + 1)) :=
  one_sub_X_sq_mul_derivative_T_eq_poly_in_T n

end FLMF.Functions.Chebyshev
