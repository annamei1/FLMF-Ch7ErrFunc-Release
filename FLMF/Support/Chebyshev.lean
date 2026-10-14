import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Ring.NegOnePow
import FLMF.Support.OrthogonalPolynomialsGegenbauerGenerating
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.EReal.Basic
import FLMF.Support.OrthogonalPolynomialsZeros

section

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
Numerical: PASS
Verified: verified
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
Numerical: PASS
Verified: verified
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
Numerical: PASS
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

end

section

/-!
# Chebyshev second-order differential equation (DLMF §18.8)

The Chebyshev polynomials of the first kind `Tₙ` satisfy the second-order linear
ODE

* **(DLMF 18.8, first row)**
  `(1 - x²) Tₙ'' - x Tₙ' + n² Tₙ = 0`,

and the polynomials of the second kind `Uₙ` satisfy

* **(DLMF 18.8, second row)**
  `(1 - x²) Uₙ'' - 3 x Uₙ' + n (n + 2) Uₙ = 0`.

These are wrappers around Mathlib's
`Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T`
and `…_U_eq_poly_in_U`, recast as the vanishing of the full ODE operator, both
as a polynomial identity and pointwise over `ℝ`.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

variable {R : Type*} [CommRing R]

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevT_ode_eval_nat
/-- the Chebyshev ODE for the first kind, in the form
`(1 - X²) Tₙ'' = X Tₙ' - n² Tₙ`. -/
theorem one_sub_X_sq_mul_deriv2_T (n : ℤ) :
    (1 - X ^ 2) * derivative (derivative (T R n))
      = X * derivative (T R n) - (n ^ 2 : R[X]) * T R n := by
  have h := one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := R) n
  simpa [Function.iterate_succ, Function.comp] using h

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevT_ode_eval_nat
/-- the first-kind Chebyshev ODE as the vanishing of the full
differential operator: `(1 - X²) Tₙ'' - X Tₙ' + n² Tₙ = 0`. -/
theorem chebyshevT_ode (n : ℤ) :
    (1 - X ^ 2) * derivative (derivative (T R n)) - X * derivative (T R n)
        + (n ^ 2 : R[X]) * T R n = 0 := by
  rw [one_sub_X_sq_mul_deriv2_T]; ring

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is one_sub_X_sq_mul_deriv2_U_nat
/-- the Chebyshev ODE for the second kind, in the form
`(1 - X²) Uₙ'' = 3 X Uₙ' - n (n + 2) Uₙ`. -/
theorem one_sub_X_sq_mul_deriv2_U (n : ℤ) :
    (1 - X ^ 2) * derivative (derivative (U R n))
      = 3 * X * derivative (U R n) - ((n + 2) * n : R[X]) * U R n := by
  have h := one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := R) n
  simpa [Function.iterate_succ, Function.comp] using h

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevU_ode_eval_nat
/-- the Chebyshev ODE for the second kind, restricted to `n : ℕ`, in the form
`(1 - X²) Uₙ'' = 3 X Uₙ' - n (n + 2) Uₙ`. -/
theorem one_sub_X_sq_mul_deriv2_U_nat (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (U R (n : ℤ)))
      = 3 * X * derivative (U R (n : ℤ)) - (((n : ℤ) + 2) * (n : ℤ) : R[X]) * U R (n : ℤ) :=
  one_sub_X_sq_mul_deriv2_U (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevU_ode_nat
/-- the second-kind Chebyshev ODE as the vanishing of the full
differential operator: `(1 - X²) Uₙ'' - 3 X Uₙ' + n (n + 2) Uₙ = 0`. -/
theorem chebyshevU_ode (n : ℤ) :
    (1 - X ^ 2) * derivative (derivative (U R n)) - 3 * X * derivative (U R n)
        + ((n + 2) * n : R[X]) * U R n = 0 := by
  rw [one_sub_X_sq_mul_deriv2_U]; ring

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevU_ode_eval_nat
/-- the second-kind Chebyshev ODE as the vanishing of the full
differential operator, restricted to `n : ℕ`:
`(1 - X²) Uₙ'' - 3 X Uₙ' + n (n + 2) Uₙ = 0`. -/
theorem chebyshevU_ode_nat (n : ℕ) :
    (1 - X ^ 2) * derivative (derivative (U R (n : ℤ))) - 3 * X * derivative (U R (n : ℤ))
        + (((n : ℤ) + 2) * (n : ℤ) : R[X]) * U R (n : ℤ) = 0 :=
  chebyshevU_ode (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevT_ode_eval_nat
/-- Pointwise evaluation form (first kind):
`(1 - x²) Tₙ''(x) - x Tₙ'(x) + n² Tₙ(x) = 0`. -/
theorem chebyshevT_ode_eval (n : ℤ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (T ℝ n))).eval x
        - x * (derivative (T ℝ n)).eval x + (n : ℝ) ^ 2 * (T ℝ n).eval x = 0 := by
  have h := congrArg (Polynomial.eval x) (chebyshevT_ode (R := ℝ) n)
  simpa using h

/-- **DLMF 18.8** — pointwise evaluation form (first kind):
`(1 - x²) Tₙ''(x) - x Tₙ'(x) + n² Tₙ(x) = 0` (DLMF-faithful restriction
of `chebyshevT_ode_eval`: `n : ℕ`).
DAG: E-18.8.
Numerical: PASS
Verified: verified
-/
theorem chebyshevT_ode_eval_nat (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (T ℝ (n : ℤ)))).eval x
        - x * (derivative (T ℝ (n : ℤ))).eval x
        + ((n : ℤ) : ℝ) ^ 2 * (T ℝ (n : ℤ)).eval x = 0 :=
  chebyshevT_ode_eval (n : ℤ) x

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.8
-- surface is chebyshevU_ode_eval_nat
/-- Pointwise evaluation form (second kind):
`(1 - x²) Uₙ''(x) - 3 x Uₙ'(x) + n (n + 2) Uₙ(x) = 0`. -/
theorem chebyshevU_ode_eval (n : ℤ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (U ℝ n))).eval x
        - 3 * x * (derivative (U ℝ n)).eval x
        + ((n : ℝ) + 2) * (n : ℝ) * (U ℝ n).eval x = 0 := by
  have h := congrArg (Polynomial.eval x) (chebyshevU_ode (R := ℝ) n)
  simpa using h

/-- **DLMF 18.8** — pointwise evaluation form (second kind):
`(1 - x²) Uₙ''(x) - 3 x Uₙ'(x) + n (n + 2) Uₙ(x) = 0` (DLMF-faithful restriction
of `chebyshevU_ode_eval`: `n : ℕ`).
DAG: E-18.8.
Numerical: PASS
Verified: verified
-/
theorem chebyshevU_ode_eval_nat (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (U ℝ (n : ℤ)))).eval x
        - 3 * x * (derivative (U ℝ (n : ℤ))).eval x
        + (((n : ℤ) : ℝ) + 2) * ((n : ℤ) : ℝ) * (U ℝ (n : ℤ)).eval x = 0 :=
  chebyshevU_ode_eval (n : ℤ) x

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev polynomials: special values at the endpoints (DLMF §18.6)

DLMF §18.6 records the values of the Chebyshev polynomials of the first kind
`Tₙ` and second kind `Uₙ` at the endpoints `x = 1` and `x = -1` of the
orthogonality interval `[-1, 1]`:

* `Tₙ(1) = 1`, `Tₙ(-1) = (-1)ⁿ`;
* `Uₙ(1) = n + 1`, `Uₙ(-1) = (-1)ⁿ (n + 1)`.

Mathlib indexes the Chebyshev polynomials by `ℤ`; here we phrase the results for
the classical natural-number index `n : ℕ` (so that `(-1)ⁿ` is a genuine
ring power) and over an arbitrary commutative ring `R`.  These are thin wrappers
around the Mathlib lemmas `T_eval_one`, `T_eval_neg_one`, `U_eval_one`,
`U_eval_neg_one`.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

variable (R : Type*) [CommRing R]

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is `T_table_18_6_1` (FLMF/Support/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the right endpoint:
`Tₙ(1) = 1` (Table 18.6.1, p_n(1) column), over an arbitrary commutative ring
`R`. -/
theorem T_eval_one_nat (n : ℕ) : (T R (n : ℤ)).eval 1 = 1 :=
  T_eval_one R (n : ℤ)

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, p_n(1) column;
-- duplicate of `T_at_one_nat` in FLMF/Support/Chebyshev.lean); conjunction
-- carrier is `T_table_18_6_1` (FLMF/Support/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the right endpoint:
`Tₙ(1) = 1` (Table 18.6.1, p_n(1) column), for the classical real-variable
Chebyshev polynomial (DLMF-faithful restriction of `T_eval_one_nat` to `R = ℝ`). -/
theorem T_eval_one_nat_dlmf (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 :=
  T_eval_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is `T_table_18_6_1` (FLMF/Support/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the left endpoint:
`Tₙ(-1) = (-1)ⁿ` (Table 18.6.1: p_n(-x) row combined with p_n(1) = 1), over an
arbitrary commutative ring `R`. -/
theorem T_eval_neg_one_nat (n : ℕ) : (T R (n : ℤ)).eval (-1) = (-1 : R) ^ n := by
  have h := T_eval_neg_one R (n : ℤ)
  rw [h]
  rw [Int.coe_negOnePow]
  simp

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's T row: the parity
-- p_n(-x) = (-1)^n p_n(x) combined with p_n(1) = 1 at x = 1), not itself a table
-- entry (duplicate of `T_at_neg_one_nat` in FLMF/Support/Chebyshev.lean);
-- conjunction carrier is `T_table_18_6_1` (FLMF/Support/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the left endpoint:
`Tₙ(-1) = (-1)ⁿ` (Table 18.6.1: p_n(-x) row combined with p_n(1) = 1), for the
classical real-variable Chebyshev polynomial (DLMF-faithful restriction of
`T_eval_neg_one_nat` to `R = ℝ`). -/
theorem T_eval_neg_one_nat_dlmf (n : ℕ) : (T ℝ (n : ℤ)).eval (-1) = (-1 : ℝ) ^ n :=
  T_eval_neg_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is U_eval_one_nat_dlmf
/-- Second-kind Chebyshev polynomial at the right endpoint:
`Uₙ(1) = n + 1` (Table 18.6.1, p_n(1) column), over an arbitrary commutative
ring `R`. -/
theorem U_eval_one_nat (n : ℕ) : (U R (n : ℤ)).eval 1 = (n : R) + 1 := by
  have h := U_eval_one R (n : ℤ)
  rw [h]
  push_cast
  ring

/-- **(DLMF 18.6)** Second-kind Chebyshev polynomial at the right endpoint:
`Uₙ(1) = n + 1` (Table 18.6.1, p_n(1) column), for the classical real-variable
Chebyshev polynomial (DLMF-faithful restriction of `U_eval_one_nat` to `R = ℝ`).

DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem U_eval_one_nat_dlmf (n : ℕ) : (U ℝ (n : ℤ)).eval 1 = (n : ℝ) + 1 :=
  U_eval_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is U_eval_neg_one_nat_dlmf
/-- Second-kind Chebyshev polynomial at the left endpoint:
`Uₙ(-1) = (-1)ⁿ (n + 1)` (Table 18.6.1: p_n(-x) row combined with
p_n(1) = n+1), over an arbitrary commutative ring `R`. -/
theorem U_eval_neg_one_nat (n : ℕ) :
    (U R (n : ℤ)).eval (-1) = (-1 : R) ^ n * ((n : R) + 1) := by
  have h := U_eval_neg_one R (n : ℤ)
  rw [h]
  rw [Int.coe_negOnePow]
  push_cast
  simp

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's U row: the parity
-- column p_n(-x) = (-1)^n p_n(x) evaluated at x = 1, combined with the p_n(1) = n+1
-- column), not itself a table entry — Table 18.6.1 has no p_n(-1) column. Mirrors the
-- treatment of `T_at_neg_one_nat` in FLMF/Support/Chebyshev.lean.
/-- Second-kind Chebyshev polynomial at the left endpoint:
`Uₙ(-1) = (-1)ⁿ (n + 1)` (DLMF Table 18.6.1: p_n(-x) row combined with
p_n(1) = n+1), for the classical real-variable Chebyshev polynomial
(restriction of `U_eval_neg_one_nat` to `R = ℝ`). -/
theorem U_eval_neg_one_nat_dlmf (n : ℕ) :
    (U ℝ (n : ℤ)).eval (-1) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) :=
  U_eval_neg_one_nat ℝ n

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev generating function (DLMF §18.12)

The classical generating function for the Chebyshev polynomials of the second kind is

$$\sum_{n=0}^{\infty} U_n(x)\, t^n = \frac{1}{1 - 2 x t + t^2}.$$

Since Mathlib's `Polynomial.Chebyshev.U` is indexed over `ℤ`, and infinite power-series
convergence is delicate, we record the precise *finite* (telescoping) form of this
generating identity, which is the algebraic heart of DLMF 18.12: for every `N`,

$$(1 - 2 x t + t^2) \sum_{n=0}^{N} U_n(x)\, t^n
    = 1 - U_{N+1}(x)\, t^{N+1} + U_N(x)\, t^{N+2}.$$

Dividing by `1 - 2xt + t²` and letting `N → ∞` (for `|t|` small) recovers the stated
power-series identity, since the remainder terms vanish.
-/

open Polynomial
open Polynomial.Chebyshev
open scoped BigOperators

namespace FLMF.Functions.Chebyshev

-- no-dlmf: packaging abbreviation for `(U ℝ n).eval x`, used by the generating-function proof.
/-- Abbreviation for the value `Uₙ(x)` of the second-kind Chebyshev polynomial. -/
noncomputable def Uval (x : ℝ) (n : ℕ) : ℝ := (U ℝ (n : ℤ)).eval x

-- no-dlmf: base-case simp helper (`U₀ = 1`) for the generating-function induction.
@[simp] theorem Uval_zero (x : ℝ) : Uval x 0 = 1 := by
  simp [Uval, U_zero]

-- no-dlmf: base-case simp helper (`U₁ = 2x`) for the generating-function induction.
@[simp] theorem Uval_one (x : ℝ) : Uval x 1 = 2 * x := by
  simp [Uval, U_one]

theorem Uval_add_two (x : ℝ) (n : ℕ) :
    Uval x (n + 2) = 2 * x * Uval x (n + 1) - Uval x n := by
  have h := U_add_two ℝ (n : ℤ)
  have := congrArg (Polynomial.eval x) h
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at this
  simp only [Uval]
  push_cast
  linear_combination this

end FLMF.Functions.Chebyshev

namespace FLMF.Chebyshev

open FLMF.Functions.Chebyshev

-- no-dlmf: packaging abbreviation for `(T ℝ n).eval x`, used by the generating-function proofs.
/-- Abbreviation for the value `Tₙ(x)` of the first-kind Chebyshev polynomial. -/
noncomputable def Tval (x : ℝ) (n : ℕ) : ℝ := (T ℝ (n : ℤ)).eval x

-- no-dlmf: base-case simp helper (`T₀ = 1`) for the generating-function proofs.
@[simp] theorem Tval_zero (x : ℝ) : Tval x 0 = 1 := by
  simp [Tval, T_zero]

private theorem Tval_succ (x : ℝ) (n : ℕ) :
    Tval x (n + 1) = Uval x (n + 1) - x * Uval x n := by
  have h := congrArg (Polynomial.eval x)
    (T_eq_U_sub_X_mul_U ℝ ((n + 1 : ℕ) : ℤ))
  simpa [Tval, Uval] using h

lemma gegenbauer_one_eq_chebyshevU (n : ℕ) (x : ℝ) :
    FLMF.Gegenbauer.gegenbauer 1 n x = Uval x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [FLMF.Gegenbauer.gegenbauer_one]
      · norm_num
      · norm_num
  | more n h0 h1 =>
      have hg := FLMF.Gegenbauer.gegenbauer_recurrence 1 (by norm_num) x n
      have hu := Uval_add_two x n
      rw [h0, h1] at hg
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      linear_combination hg - ((n : ℝ) + 2) * hu

-- no-dlmf: real-`z` restriction of DLMF 18.12.10; faithful surface is
-- chebyshevU_generating_function_complex.
/-- The Chebyshev second-kind generating function (real `z`)
`1 / (1 - 2xz + z²) = ∑ n, Uₙ(x) zⁿ`. -/
theorem chebyshevU_generating_function {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => Uval x n * z ^ n) ((1 - 2 * x * z + z ^ 2)⁻¹) := by
  simpa only [gegenbauer_one_eq_chebyshevU, neg_one_mul, Real.rpow_neg_one] using
    (FLMF.Gegenbauer.gegenbauer_generating_function (lam := (1 : ℝ)) (x := x) (z := z)
      (by norm_num) hx hz)

/-- **DLMF 18.12.10** — the Chebyshev second-kind generating function at DLMF's stated
strength: real `x`, complex `z` with `‖z‖ < 1`,
`1 / (1 - 2xz + z²) = ∑ n, Uₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`): for real `x` with `|x| > 1` the roots of `1 - 2xz + z² = 0` are real
with product `1`, so one root lies strictly inside the open unit disc and the series
diverges there (e.g. `x = 2` has a pole at `z = 2 - √3 ≈ 0.268 < 1`). The
unconstrained-`x` reading of 18.12.10 is therefore false; `|x| ≤ 1` is the
correctness-preserving domain, and `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.10.
Numerical: PASS
Verified: unverified
-/
theorem chebyshevU_generating_function_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Uval x n : ℂ) * z ^ n) ((1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

-- no-dlmf: real-`z` restriction of DLMF 18.12.8; faithful surface is
-- chebyshevT_generating_function_complex.
/-- The Chebyshev first-kind generating function (real `z`)
`(1 - xz) / (1 - 2xz + z²) = ∑ n, Tₙ(x) zⁿ`. -/
theorem chebyshevT_generating_function {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => Tval x n * z ^ n)
      ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) := by
  let SU := (1 - 2 * x * z + z ^ 2)⁻¹
  have hU : HasSum (fun n : ℕ => Uval x n * z ^ n) SU :=
    chebyshevU_generating_function hx hz
  have hshift :
      HasSum (fun n : ℕ => (if n = 0 then 0 else Uval x (n - 1)) * z ^ n) (z * SU) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hU.mul_left z
  have h := hU.sub (hshift.mul_left x)
  convert h using 1
  · funext n
    cases n with
    | zero => simp
    | succ n =>
        rw [show n + 1 = Nat.succ n from rfl]
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
        rw [Tval_succ]
        ring
  · dsimp [SU]
    ring

/-- **DLMF 18.12.8** — the Chebyshev first-kind generating function at DLMF's stated
strength: real `x`, complex `z` with `‖z‖ < 1`,
`(1 - xz) / (1 - 2xz + z²) = ∑ n, Tₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`); see `chebyshevU_generating_function_complex` for why the
unconstrained-`x` reading is false. `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.8.
Numerical: PASS
Verified: unverified
-/
theorem chebyshevT_generating_function_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Tval x n : ℂ) * z ^ n)
      ((1 - (x : ℂ) * z) * (1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

-- no-dlmf: real-`z` restriction of DLMF 18.12.7; faithful surface is
-- chebyshevT_generating_function_symm_complex.
/-- The symmetric Chebyshev first-kind generating function (real `z`)
`(1 - z²) / (1 - 2xz + z²) = 1 + 2 ∑ n ≥ 1, Tₙ(x) zⁿ`. -/
theorem chebyshevT_generating_function_symm {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2 * Tval x n) * z ^ n)
      ((1 - z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹) := by
  let d := 1 - 2 * x * z + z ^ 2
  have hx_sq : x ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := x) (b := 1)).mpr (by simpa using hx)
  have hz_sq : z ^ 2 < 1 := by
    simpa using (sq_lt_sq (a := z) (b := 1)).mpr (by simpa using hz)
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith [sq_nonneg (z - x)]
  have hT := (chebyshevT_generating_function hx hz).mul_left 2
  have hdelta : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have h := hT.sub hdelta
  convert h using 1
  · funext n
    cases n with
    | zero => norm_num
    | succ n => simp [mul_assoc]
  · dsimp [d] at hd_pos ⊢
    have hd : 1 - 2 * x * z + z ^ 2 ≠ 0 := ne_of_gt hd_pos
    calc
      (1 - z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹ =
          2 * ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) -
            (1 - 2 * x * z + z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹ := by ring
      _ = 2 * ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) - 1 := by
        rw [mul_inv_cancel₀ hd]

/-- **DLMF 18.12.7** — the symmetric Chebyshev first-kind generating function at
DLMF's stated strength: real `x`, complex `z` with `‖z‖ < 1`,
`(1 - z²) / (1 - 2xz + z²) = 1 + 2 ∑ n ≥ 1, Tₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`); see `chebyshevU_generating_function_complex` for why the
unconstrained-`x` reading is false. `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.7.
Numerical: PASS
Verified: unverified
-/
theorem chebyshevT_generating_function_symm_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 2 * (Tval x n : ℂ)) * z ^ n)
      ((1 - z ^ 2) * (1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

/-- **DLMF 18.9.9** — `T_n(x) = ½(U_n(x) - U_{n-2}(x))` for `n` a nonnegative integer
and `x` real, using Mathlib's `ℤ`-indexed `Polynomial.Chebyshev.U` (via its standard
backward extension `U_{-1} = 0`, `U_{-2} = -1`) to make sense of `U_{n-2}` at `n = 0, 1`. -/
theorem chebyshevT_eq_half_U_sub (x : ℝ) (n : ℕ) :
    Tval x n = (1 / 2) * (Uval x n - (U ℝ ((n : ℤ) - 2)).eval x) := by
  have h := congrArg (Polynomial.eval x) (two_mul_T_eq_U_sub_U ℝ ((n : ℤ) - 2))
  have hn2 : (n : ℤ) - 2 + 2 = (n : ℤ) := by ring
  rw [hn2] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
  simp only [Tval, Uval]
  linarith [h]

/-- **DLMF 18.9.10**: `(1 - x²) U_n(x) = -½(T_{n+2}(x) - T_n(x))`. -/
theorem one_sub_sq_mul_U (x : ℝ) (n : ℕ) :
    (1 - x ^ 2) * Uval x n = -(1 / 2) * (Tval x (n + 2) - Tval x n) := by
  have hpol := congrArg (Polynomial.eval x) (one_sub_X_sq_mul_U_eq_pol_in_T ℝ (n : ℤ))
  have hrec := congrArg (Polynomial.eval x) (T_eq ℝ ((n : ℤ) + 2))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_ofNat] at hpol hrec
  simp only [Tval, Uval]
  push_cast at hpol hrec ⊢
  ring_nf at hpol hrec ⊢
  linarith [hpol, hrec]

end FLMF.Chebyshev

namespace FLMF.Functions.Chebyshev

-- no-dlmf: finite/telescoping partial-sum identity used as an induction stepping
-- stone toward the DLMF 18.12.10 generating function (proved separately below as
-- chebyshevU_generating_function); not itself a displayed DLMF equation.
/-- **(DLMF 18.12, second kind, finite/telescoping form).**
For every `N`, the partial generating sum of the second-kind Chebyshev polynomials
satisfies
`(1 - 2 x t + t²) · Σ_{n=0}^{N} Uₙ(x) tⁿ = 1 - U_{N+1}(x) t^{N+1} + U_N(x) t^{N+2}`.

-/
theorem secondKind_generating_partial (x t : ℝ) (N : ℕ) :
    (1 - 2 * x * t + t ^ 2) * (∑ n ∈ Finset.range (N + 1), Uval x n * t ^ n)
      = 1 - Uval x (N + 1) * t ^ (N + 1) + Uval x N * t ^ (N + 2) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one, show (0:ℕ)+1 = 1 from rfl,
        Uval_zero, Uval_one]
      ring
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hN2 : Uval x (N + 1 + 1) = 2 * x * Uval x (N + 1) - Uval x N := by
        simpa using Uval_add_two x N
      rw [hN2]
      ring

end FLMF.Functions.Chebyshev

end

section

/-
Chebyshev minimax / equioscillation property.

Among all monic real polynomials of degree `n ≥ 1`, the scaled Chebyshev
polynomial `2^{-(n-1)} • T_n` minimizes the supremum norm on `[-1, 1]`,
and that minimal sup-norm equals `2^{-(n-1)}`.

This is the classical "minimax" property of Chebyshev polynomials,
DLMF §18.14 / approximation theory.  The key extremal input is Mathlib's
`Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`, which says
that a polynomial of degree `≤ n` bounded by `1` on `[-1, 1]` has leading
coefficient at most `2^{n-1}`.
-/
open Polynomial Real

namespace FLMF.Chebyshev

open Polynomial.Chebyshev

-- no-dlmf: packaging def (scaled monic Chebyshev polynomial) for the minimax statement.
/-- The monic Chebyshev polynomial of degree `n` (for `n ≥ 1`):
`2^{-(n-1)} • T_n`, which has leading coefficient `1`. -/
noncomputable def monicT (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ (n - 1))⁻¹ * T ℝ n

-- no-dlmf: technical degree fact about `T ℝ n`; infrastructure for the minimax proof.
lemma natDegree_T_nat (n : ℕ) : (T ℝ (n : ℤ)).natDegree = n := by
  rw [natDegree_T]; simp

-- no-dlmf: technical leading-coefficient fact; infrastructure for the minimax proof.
lemma leadingCoeff_T_nat (n : ℕ) : (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  rw [leadingCoeff_T]; simp

-- no-dlmf: technical nonvanishing fact; infrastructure for the minimax proof.
lemma T_nat_ne_zero (n : ℕ) : (T ℝ (n : ℤ)) ≠ 0 := by
  intro h
  have : (T ℝ (n : ℤ)).leadingCoeff = 0 := by rw [h]; simp
  rw [leadingCoeff_T_nat] at this
  exact (by positivity : (0:ℝ) < 2 ^ (n-1)).ne' this

-- no-dlmf: technical degree fact; infrastructure for the minimax proof.
lemma degree_T_nat (n : ℕ) : (T ℝ (n : ℤ)).degree = (n : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (T_nat_ne_zero n), natDegree_T_nat]

-- no-dlmf: structural property of the packaging def `monicT`; not a DLMF identity.
/-- `monicT n` is monic. -/
theorem monic_monicT (n : ℕ) : (monicT n).Monic := by
  unfold monicT Polynomial.Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T_nat]
  field_simp

-- no-dlmf: structural property of the packaging def `monicT`; not a DLMF identity.
/-- `monicT n` has degree `n`. -/
theorem natDegree_monicT (n : ℕ) : (monicT n).natDegree = n := by
  unfold monicT
  have hc : ((2 : ℝ) ^ (n - 1))⁻¹ ≠ 0 := by positivity
  rw [natDegree_C_mul hc, natDegree_T_nat]

-- no-dlmf: technical sup-norm bound for `monicT`; one half of the minimax proof, not a DLMF eqn.
/-- The supremum-norm bound: `|monicT n (x)| ≤ 2^{-(n-1)}` for `x ∈ [-1,1]`. -/
theorem abs_eval_monicT_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(monicT n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹ := by
  unfold monicT
  rw [eval_mul, eval_C, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2:ℝ)^(n-1))⁻¹)]
  have hT : |(T ℝ (n:ℤ)).eval x| ≤ 1 := by
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨θ, hθ⟩ : ∃ θ, Real.cos θ = x := ⟨Real.arccos x, Real.cos_arccos hx1 hx2⟩
    rw [← hθ, T_real_cos]
    exact Real.abs_cos_le_one _
  calc ((2:ℝ)^(n-1))⁻¹ * |(T ℝ (n:ℤ)).eval x|
      ≤ ((2:ℝ)^(n-1))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left hT (by positivity)
    _ = ((2:ℝ)^(n-1))⁻¹ := by ring

/-- **Chebyshev minimax (lower bound).**  Any monic real polynomial `P` of degree `n ≥ 1`
attains absolute value at least `2^{-(n-1)}` somewhere on `[-1, 1]`. -/
theorem exists_abs_eval_ge_of_monic {n : ℕ} (hn : 1 ≤ n) {P : ℝ[X]}
    (hPmonic : P.Monic) (hPdeg : P.natDegree = n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |P.eval x| := by
  by_contra h
  push_neg at h
  set Q : ℝ[X] := C ((2 : ℝ) ^ (n - 1)) * P with hQ
  have hQdeg : Q.degree ≤ n := by
    have hc : ((2:ℝ)^(n-1)) ≠ 0 := by positivity
    rw [hQ, degree_C_mul hc]
    rw [Polynomial.degree_eq_natDegree hPmonic.ne_zero, hPdeg]
  have hQbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1 := by
    intro x hx
    rw [hQ, eval_mul, eval_C, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^(n-1))]
    have := h x hx
    have hlt : (2:ℝ)^(n-1) * |P.eval x| < (2:ℝ)^(n-1) * ((2:ℝ)^(n-1))⁻¹ :=
      mul_lt_mul_of_pos_left this (by positivity)
    rw [mul_inv_cancel₀ (by positivity : ((2:ℝ)^(n-1)) ≠ 0)] at hlt
    exact le_of_lt hlt
  have hQlc : Q.leadingCoeff = (2:ℝ)^(n-1) := by
    rw [hQ, leadingCoeff_mul, leadingCoeff_C, hPmonic.leadingCoeff, mul_one]
  by_cases hn2 : 2 ≤ n
  · -- equality case via `leadingCoeff_eq_iff`
    have hQT : Q = T ℝ (n : ℤ) :=
      (leadingCoeff_eq_iff_of_forall_abs_le_one hn2 hQdeg hQbnd).mp (by rw [hQlc])
    have hnode0 : node n 0 ∈ Set.Icc (-1:ℝ) 1 := node_mem_Icc
    have horig := h (node n 0) hnode0
    have hPval : P.eval (node n 0) = ((2:ℝ)^(n-1))⁻¹ := by
      have hQe : Q.eval (node n 0) = (2:ℝ)^(n-1) * P.eval (node n 0) := by
        rw [hQ, eval_mul, eval_C]
      rw [hQT, eval_T_real_node (by simp)] at hQe
      simp only [pow_zero] at hQe
      have hc : ((2:ℝ)^(n-1)) ≠ 0 := by positivity
      field_simp at hQe ⊢
      linarith [hQe]
    rw [hPval, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2:ℝ)^(n-1))⁻¹)] at horig
    exact (lt_irrefl _ horig)
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    simp only [Nat.sub_self, pow_zero, inv_one] at h
    have hPeq : P = X + C (P.coeff 0) := by
      ext k
      rcases k with _ | _ | k
      · simp [coeff_X, coeff_C]
      · have hc1 : P.coeff 1 = 1 := by
          have := hPmonic.leadingCoeff
          rw [leadingCoeff, hPdeg] at this; simpa using this
        simp [coeff_X, hc1]
      · have hck : P.coeff (k+2) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hPdeg]; omega
        simp [coeff_X, hck]
    have hP1 : P.eval 1 - P.eval (-1) = 2 := by
      rw [hPeq]; simp; ring
    have h1 := h 1 (by constructor <;> norm_num)
    have h2 := h (-1) (by constructor <;> norm_num)
    have htri : |P.eval 1 - P.eval (-1)| ≤ |P.eval 1| + |P.eval (-1)| := abs_sub _ _
    rw [hP1] at htri; rw [abs_of_pos (by norm_num : (0:ℝ) < 2)] at htri
    linarith

/-- **Chebyshev minimax / equioscillation theorem.**

For `n ≥ 1`, the scaled Chebyshev polynomial `monicT n = 2^{-(n-1)} T_n` is a monic
polynomial of degree `n` whose supremum norm on `[-1, 1]` is `2^{-(n-1)}`, and no monic
polynomial of degree `n` has a strictly smaller maximal absolute value on `[-1, 1]`:
every such polynomial attains absolute value at least `2^{-(n-1)}` somewhere on `[-1, 1]`,
while `monicT n` never exceeds it.  Thus `monicT n` is the minimax monic polynomial. -/
theorem isMinimax {n : ℕ} (hn : 1 ≤ n) :
    (monicT n).Monic ∧ (monicT n).natDegree = n ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(monicT n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) ∧
    (∀ P : ℝ[X], P.Monic → P.natDegree = n →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |P.eval x|) := by
  refine ⟨monic_monicT n, natDegree_monicT n, ?_, ?_⟩
  · intro x hx; exact abs_eval_monicT_le hx
  · intro P hPm hPd; exact exists_abs_eval_ge_of_monic hn hPm hPd

end FLMF.Chebyshev

end

section

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
Numerical: PASS
Verified: verified
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
Numerical: PASS
Verified: verified
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
Numerical: PASS
Verified: verified
-/
theorem inner_eq (n m : ℕ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂chebyshevWeight =
      if n = m then normalizationConst n else 0 := by
  rcases eq_or_ne n m with rfl | h
  · rw [if_pos rfl]; exact norm_sq_eq_normalizationConst n
  · rw [if_neg h]; exact orthogonal_of_ne h

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev product-to-sum identity (DLMF 18.18)

The classical product-to-sum identity for Chebyshev polynomials of the first kind:
`2 Tₘ Tₙ = T_{m+n} + T_{m-n}`.

We record the polynomial identity (a wrapper around Mathlib's `T_mul_T`) and the
evaluated/trigonometric consequences.
-/

open Polynomial Polynomial.Chebyshev Real

namespace FLMF.Functions.Chebyshev

variable {R : Type*} [CommRing R]

-- no-dlmf: strictly-more-general abstract-ring polynomial form; DLMF states the
-- identity for Chebyshev polynomials as functions of the real variable `x`, not as
-- an identity over an arbitrary commutative ring `R`; the faithful DLMF 18.18.21
-- surface is `two_T_mul_T_eval_nat`
/-- Product-to-sum identity for Chebyshev polynomials of the first kind, over an
arbitrary commutative ring: `2 Tₘ Tₙ = T_{m+n} + T_{m-n}`.
-/
theorem two_T_mul_T (m n : ℤ) :
    2 * T R m * T R n = T R (m + n) + T R (m - n) :=
  T_mul_T R m n

-- no-dlmf: quantifies `m,n` over all integers `ℤ`; DLMF 18.18.21 assigns `m,n` as
-- nonnegative integers; faithful surface is two_T_mul_T_eval_nat
/-- Product-to-sum, evaluated form over `ℝ`, for all integers `m,n`:
`2 Tₘ(x) Tₙ(x) = T_{m+n}(x) + T_{m-n}(x)`.
-/
theorem two_T_mul_T_eval (m n : ℤ) (x : ℝ) :
    2 * (T ℝ m).eval x * (T ℝ n).eval x
      = (T ℝ (m + n)).eval x + (T ℝ (m - n)).eval x := by
  have h := two_T_mul_T (R := ℝ) m n
  have := congrArg (fun p : ℝ[X] => p.eval x) h
  simpa [eval_mul, eval_add, eval_ofNat] using this

/-- **DLMF 18.18.21.** For nonnegative integers `m,n`,
`2 Tₘ(x) Tₙ(x) = T_{m+n}(x) + T_{m-n}(x)`.

DAG: E-18.18.21.
Numerical: PASS
Verified: verified
-/
theorem two_T_mul_T_eval_nat (m n : ℕ) (x : ℝ) :
    2 * (T ℝ (m : ℤ)).eval x * (T ℝ (n : ℤ)).eval x
      = (T ℝ ((m : ℤ) + n)).eval x + (T ℝ ((m : ℤ) - n)).eval x :=
  two_T_mul_T_eval (m : ℤ) (n : ℤ) x

-- no-dlmf: instance of DLMF 18.18.21 (specialization x = cos θ of the polynomial
-- identity); faithful surface is two_T_mul_T_eval_nat
/-- Trigonometric product-to-sum form: `2 cos(mθ) cos(nθ) = cos((m+n)θ) + cos((m-n)θ)`,
obtained from the polynomial identity via `Tₙ(cos θ) = cos(nθ)`.
-/
theorem two_cos_mul_cos (m n : ℤ) (θ : ℝ) :
    2 * cos (↑m * θ) * cos (↑n * θ)
      = cos ((↑m + ↑n) * θ) + cos ((↑m - ↑n) * θ) := by
  have h := two_T_mul_T_eval m n (cos θ)
  rw [T_real_cos θ m, T_real_cos θ n, T_real_cos θ (m + n), T_real_cos θ (m - n)] at h
  push_cast at h ⊢
  linarith [h]

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev polynomials: the Rodrigues formula (DLMF §18.5)

The Chebyshev polynomials of the first kind admit the classical *Rodrigues
representation* (DLMF Table 18.5.1 / 18.5.5):
$$
  T_n(x)
    = \frac{(-1)^n\,2^n\,n!}{(2n)!}\,(1-x^2)^{1/2}\,
        \frac{d^n}{dx^n}\!\left[(1-x^2)^{n-1/2}\right],
  \qquad x\in(-1,1).
$$

A fully general inductive proof requires an $n$-th order Leibniz/Faà-di-Bruno
calculus for fractional powers `(1 - x^2) ^ (n - 1/2)`, which is not yet
available in Mathlib.  Here we set up the precise statement together with the
constant and weight occurring in it, and we prove rigorously the two base
cases `n = 0` and `n = 1`, which are genuine calculus identities on the open
interval `(-1, 1)`.

## Main results

* `rodriguesConst` : the scalar prefactor `(-1)^n 2^n n! / (2n)!`.
* `rodriguesRHS`   : the right-hand side of the Rodrigues formula as a function
  of `x`.
* `chebyshevT_rodrigues`      : the general formula (DLMF 18.5.5), stated
  faithfully for all `n`; currently a `sorry` surface.
* `chebyshevT_rodrigues_zero` : the formula for `n = 0` (proven).
* `chebyshevT_rodrigues_one`  : the formula for `n = 1` (proven).
-/

open Polynomial Polynomial.Chebyshev Real

namespace FLMF.Functions.Chebyshev

-- no-dlmf: packaging def for the Rodrigues prefactor; the formula itself is DLMF 18.5.5 below.
/-- The Rodrigues prefactor `(-1)^n · 2^n · n! / (2n)!`. -/
noncomputable def rodriguesConst (n : ℕ) : ℝ :=
  (-1) ^ n * 2 ^ n * (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

-- no-dlmf: packaging def (RHS of the Rodrigues formula); the identity is DLMF 18.5.5 below.
/-- The right-hand side of the Chebyshev–Rodrigues formula, as a real function
of `x`:
`(-1)^n 2^n n!/(2n)! · (1-x^2)^{1/2} · dⁿ/dxⁿ[(1-x^2)^{n-1/2}]`. -/
noncomputable def rodriguesRHS (n : ℕ) (x : ℝ) : ℝ :=
  rodriguesConst n * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
    iteratedDeriv n (fun t => (1 - t ^ 2) ^ ((n : ℝ) - 1 / 2)) x

-- no-dlmf: instance of DLMF 18.5.5 (degree fixed to n = 0); faithful surface is chebyshevT_rodrigues
/-- Rodrigues formula for `T₀`, base case `n = 0`.  Since the prefactor and both
fractional powers cancel, the formula reduces to the constant value
`T₀(x) = 1`. -/
theorem chebyshevT_rodrigues_zero (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (0 : ℕ)).eval x = rodriguesRHS 0 x := by
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hne : (1 - x ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [rodriguesRHS, rodriguesConst, iteratedDeriv_zero]
  -- The inner exponent is `(0 : ℝ) - 1/2 = -(1/2)`.
  have hcast : ((0 : ℕ) : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by norm_num
  rw [hcast]
  -- `(1-x²)^{1/2} · (1-x²)^{-1/2} = 1`.
  have hprod : (1 - x ^ 2) ^ ((1 : ℝ) / 2) * (1 - x ^ 2) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hpos]; norm_num
  rw [show (T ℝ (0 : ℕ)) = 1 from by simp [T_zero]]
  simp only [eval_one]
  rw [mul_assoc, hprod]
  norm_num [Nat.factorial]

-- no-dlmf: proof-internal derivative helper for the n=1 Rodrigues base case.
/-- The (real) derivative of `t ↦ (1 - t^2)^{1/2}` at a point `x ∈ (-1,1)`. -/
private theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hpos : (0 : ℝ) < 1 - x ^ 2) :
    HasDerivAt (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2))
      ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x))) x := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    simpa using (this.const_sub 1)
  have := hbase.rpow_const (p := (1 : ℝ) / 2) (Or.inl (ne_of_gt hpos))
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

-- no-dlmf: instance of DLMF 18.5.5 (degree fixed to n = 1); faithful surface is chebyshevT_rodrigues
/-- Rodrigues formula for `T₁`, base case `n = 1`.  Here
`T₁(x) = x`, and the right-hand side evaluates to `x` after differentiating
`(1-x^2)^{1/2}` once. -/
theorem chebyshevT_rodrigues_one (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (1 : ℕ)).eval x = rodriguesRHS 1 x := by
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hne : (1 - x ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [rodriguesRHS, rodriguesConst, iteratedDeriv_one]
  -- inner exponent `(1 : ℝ) - 1/2 = 1/2`
  have hcast : ((1 : ℕ) : ℝ) - 1 / 2 = (1 : ℝ) / 2 := by norm_num
  -- compute the derivative of `t ↦ (1 - t²)^{1/2}` at `x`
  have hderiv :
      deriv (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2 - 1 / 2 + 1 / 2)) x
        = (1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)) := by
    have : (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2 - 1 / 2 + 1 / 2))
        = (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2)) := by
      norm_num
    rw [this]
    exact (hasDerivAt_sqrt_one_sub_sq hpos).deriv
  rw [hcast]
  have hderiv' :
      deriv (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2)) x
        = (1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)) :=
    (hasDerivAt_sqrt_one_sub_sq hpos).deriv
  rw [hderiv']
  -- Now simplify the product.
  -- `(1-x²)^{1/2} · (1-x²)^{1/2-1} = (1-x²)^{0} = 1`.
  have hprod : (1 - x ^ 2) ^ ((1 : ℝ) / 2) * ((1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1))
      = 1 := by
    rw [← Real.rpow_add hpos]
    norm_num
  -- T₁ = X
  rw [show (T ℝ (1 : ℕ)) = X from by simp [T_one]]
  simp only [eval_X]
  -- Rearrange and use hprod.
  rw [show ((-1 : ℝ) ^ 1 * 2 ^ 1 * (Nat.factorial 1 : ℝ) / (Nat.factorial (2 * 1) : ℝ))
        = -1 from by norm_num [Nat.factorial]]
  have key :
      -1 * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
          ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)))
        = x := by
    have : -1 * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
          ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)))
        = ((1 - x ^ 2) ^ ((1 : ℝ) / 2) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1)) * x := by
      ring
    rw [this, hprod]; ring
  linarith [key]

/-- **DLMF 18.5.5** (row `T_n` of Table 18.5.1) — the Rodrigues formula for the
Chebyshev polynomials of the first kind: for every nonnegative integer `n` and
every `x ∈ (-1, 1)`,
$$
  T_n(x) = \frac{(-1)^n 2^n n!}{(2n)!}\,(1-x^2)^{1/2}\,
    \frac{d^n}{dx^n}\left[(1-x^2)^{n-1/2}\right].
$$

DAG: E-18.5.5.
Numerical: PASS
Verified: unverified
-/
theorem chebyshevT_rodrigues (n : ℕ) (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (n : ℕ)).eval x = rodriguesRHS n x := by
  sorry

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev sum / linearization rule (DLMF 18.18)

Specializing the product-to-sum identity `2 Tₘ Tₙ = T_{m+n} + T_{m-n}` to `m = n = k`
gives `2 (Tₖ)² = T_{2k} + 1`.  Summing over `k = 0, …, n` yields the **sum rule**

`∑_{k=0}^{n} 2 (Tₖ)² = (n + 1) + ∑_{k=0}^{n} T_{2k}`,

a linearization of the sum of squares of Chebyshev polynomials of the first kind.
We record the per-term identity, the polynomial sum rule, the evaluated form, and the
trigonometric consequence `∑ 2 cos²(kθ) = (n+1) + ∑ cos(2kθ)`.
-/

open Polynomial Polynomial.Chebyshev Real Finset

namespace FLMF.Functions.Chebyshev

-- no-dlmf: instance of DLMF 18.18.21 (square specialization m = n = k of the
-- product-to-sum identity); faithful surface is two_T_mul_T_eval_nat
-- (FLMF/Support/Chebyshev.lean)
/-- Square specialization of the product-to-sum identity: `2 (Tₖ)² = T_{2k} + 1`. -/
theorem two_T_sq (R : Type*) [CommRing R] (k : ℤ) :
    2 * T R k * T R k = T R (2 * k) + 1 := by
  have h := T_mul_T R k k
  simpa [two_mul, sub_self, T_zero] using h

-- no-dlmf: strictly-more-general form (an arbitrary commutative ring `R`, not the
-- classical real setting DLMF works in); derived summed specialization of DLMF
-- 18.18.21 (§18.18 itself is a section title, not a numbered display; there is no
-- standalone "DLMF 18.18" formula for this identity to be faithful to)
/-- The polynomial identity
`∑_{k=0}^{n} 2 (Tₖ)² = (n + 1) + ∑_{k=0}^{n} T_{2k}`, over an arbitrary commutative ring `R`.
-/
theorem sum_two_T_sq (R : Type*) [CommRing R] (n : ℕ) :
    ∑ k ∈ range (n + 1), (2 * T R (k : ℤ) * T R (k : ℤ))
      = ((n : R[X]) + 1) + ∑ k ∈ range (n + 1), T R (2 * (k : ℤ)) := by
  have hterm : ∀ k ∈ range (n + 1),
      (2 * T R (k : ℤ) * T R (k : ℤ)) = T R (2 * (k : ℤ)) + 1 := by
    intro k _; exact two_T_sq R (k : ℤ)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_range]
  ring

-- no-dlmf: derived specialization of DLMF 18.18.21 (summing the product-to-sum
-- identity `2 Tₖ Tₖ = T_{2k} + 1` over k = 0,…,n with m = n = k fixed), not itself
-- a DLMF-numbered display — bare "18.18" is §18.18's section title ("Sums"),
-- covering many sub-displays 18.18.1–18.18.40+, none of which state this
-- particular finite-sum identity; the faithful surface of the underlying
-- product-to-sum equation is `two_T_mul_T_eval_nat`
-- (FLMF/Support/Chebyshev.lean)
/-- The sum rule for squares of Chebyshev polynomials of the first kind,
specialized to the classical real setting `R = ℝ` (DLMF-faithful restriction of
`sum_two_T_sq`): `∑_{k=0}^{n} 2 (Tₖ)² = (n + 1) + ∑_{k=0}^{n} T_{2k}` in `ℝ[X]`. -/
theorem sum_two_T_sq_dlmf (n : ℕ) :
    ∑ k ∈ range (n + 1), (2 * T ℝ (k : ℤ) * T ℝ (k : ℤ))
      = ((n : ℝ[X]) + 1) + ∑ k ∈ range (n + 1), T ℝ (2 * (k : ℤ)) :=
  sum_two_T_sq ℝ n

-- no-dlmf: evaluated (`eval x`) corollary of `sum_two_T_sq_dlmf`; a derived
-- sum-of-squares linearization obtained by summing the DLMF 18.18.21
-- product-to-sum identity, not itself a DLMF-numbered display (§18.18 states
-- the product formula and other Chebyshev sums, not this one).
/-- Sum rule for squares, evaluated form over `ℝ`:
`∑_{k=0}^{n} 2 Tₖ(x)² = (n + 1) + ∑_{k=0}^{n} T_{2k}(x)`. -/
theorem sum_two_T_sq_eval (n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), (2 * (T ℝ (k : ℤ)).eval x * (T ℝ (k : ℤ)).eval x)
      = (n + 1 : ℝ) + ∑ k ∈ range (n + 1), (T ℝ (2 * (k : ℤ))).eval x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x) (sum_two_T_sq ℝ n)
  simpa [eval_finsetSum, eval_mul, eval_add, eval_ofNat, eval_one] using h

-- no-dlmf: trigonometric instance (x = cos θ) of the 18.18.21-derived sum rule for
-- squares; not itself a displayed DLMF relation
/-- Trigonometric form:
`∑_{k=0}^{n} 2 cos²(kθ) = (n + 1) + ∑_{k=0}^{n} cos(2kθ)`. -/
theorem sum_two_cos_sq (n : ℕ) (θ : ℝ) :
    ∑ k ∈ range (n + 1), (2 * cos ((k : ℝ) * θ) * cos ((k : ℝ) * θ))
      = (n + 1 : ℝ) + ∑ k ∈ range (n + 1), cos (2 * (k : ℝ) * θ) := by
  have h := sum_two_T_sq_eval n (cos θ)
  have e1 : ∀ k ∈ range (n + 1),
      (2 * (T ℝ (k : ℤ)).eval (cos θ) * (T ℝ (k : ℤ)).eval (cos θ))
        = 2 * cos ((k : ℝ) * θ) * cos ((k : ℝ) * θ) := by
    intro k _; rw [T_real_cos θ (k : ℤ)]; push_cast; ring
  have e2 : ∀ k ∈ range (n + 1),
      (T ℝ (2 * (k : ℤ))).eval (cos θ) = cos (2 * (k : ℝ) * θ) := by
    intro k _; rw [T_real_cos θ (2 * (k : ℤ))]; push_cast; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
  exact h

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev special values (DLMF §18.6)

We record the classical endpoint evaluations for the Chebyshev polynomials of the
first (`Tₙ`) and second (`Uₙ`) kinds.  All statements are wrappers around Mathlib
lemmas.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is firstKind_eval_one_nat
/-- the first-kind Chebyshev polynomial satisfies `Tₙ(1) = 1`
(Table 18.6.1, p_n(1) column). -/
@[simp] theorem firstKind_eval_one (n : ℤ) : (T ℝ n).eval 1 = 1 :=
  T_eval_one ℝ n

/-- **DLMF 18.6** (Table 18.6.1, p_n(1) column) — `Tₙ(1) = 1` (DLMF-faithful
restriction of `firstKind_eval_one`: `n : ℕ`).
DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem firstKind_eval_one_nat (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 :=
  firstKind_eval_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.3
-- surface is secondKind_eval_one_nat
/-- the second-kind Chebyshev polynomial satisfies `Uₙ(1) = n + 1`. -/
@[simp] theorem secondKind_eval_one (n : ℤ) : (U ℝ n).eval 1 = (n : ℝ) + 1 :=
  U_eval_one ℝ n

-- no-dlmf: duplicate of `FLMF.Functions.Chebyshev.U_at_one_nat`
-- (`FLMF/Support/Chebyshev.lean`, tagged DLMF 18.6, semantic-verified). The
-- previous tag `18.6.3` names the Jacobi-polynomial limiting relation
-- `lim_{β→∞} P_n^{(α,β)}(x)/P_n^{(α,β)}(-1) = ((1-x)/2)ⁿ`, an unrelated
-- identity — `Uₙ(1) = n+1` is Table 18.6.1's `p_n(1)` column, already the
-- carrier's tag.
/-- `Uₙ(1) = n + 1`, `n : ℕ`. -/
theorem secondKind_eval_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval 1 = ((n : ℤ) : ℝ) + 1 :=
  secondKind_eval_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.2
-- surface is firstKind_eval_neg_one_nat
/-- the first-kind Chebyshev polynomial satisfies `Tₙ(-1) = (-1)ⁿ`. -/
@[simp] theorem firstKind_eval_neg_one (n : ℤ) : (T ℝ n).eval (-1) = n.negOnePow :=
  T_eval_neg_one ℝ n

-- no-dlmf: duplicate of `FLMF.Functions.Chebyshev.T_at_neg_one_nat`
-- (`FLMF/Support/Chebyshev.lean`, tagged DLMF 18.6, semantic-verified). The
-- previous tag `18.6.2` names the Jacobi-polynomial limiting relation
-- `lim_{α→∞} P_n^{(α,β)}(x)/P_n^{(α,β)}(1) = ((1+x)/2)ⁿ`, an unrelated
-- identity — `Tₙ(-1) = (-1)ⁿ` is Table 18.6.1's parity column, already the
-- carrier's tag.
/-- `Tₙ(-1) = (-1)ⁿ`, `n : ℕ`. -/
theorem firstKind_eval_neg_one_nat (n : ℕ) :
    (T ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow :=
  firstKind_eval_neg_one (n : ℤ)

end FLMF.Functions.Chebyshev

end

section

/-!
# Chebyshev polynomials of the first kind: zeros are real, simple, and in the support

This file packages DLMF 18.2(vi) for the Chebyshev polynomials of the first kind
`T_n`.  The zeros of `T_n` are

  x_k = cos ((2k+1) π / (2n)),   k = 0, …, n-1,

and we prove that:

* there are exactly `n` of them (`FLMF.Chebyshev.card_roots_T`),
* each is a simple root (`FLMF.Chebyshev.rootMultiplicity_Tzero`),
* all of them lie in the open support interval `(-1, 1)`
  (`FLMF.Chebyshev.roots_T_mem_Ioo`).

We also record that the multiset of roots has no repetition
(`FLMF.Chebyshev.roots_T_nodup`), i.e. the zeros are real and simple.

The explicit description of `(T ℝ n).roots` is taken from Mathlib; here we collect the
location/cardinality/simplicity facts in the DLMF form.
-/

open Real Polynomial

namespace FLMF.Chebyshev

open Polynomial.Chebyshev

-- no-dlmf: packaging def for the explicit zero `cos((2k+1)π/(2n))`; the zero facts are DLMF 18.2 below.
/-- The explicit zero of `T_n` of index `k`. -/
noncomputable def Tzero (n k : ℕ) : ℝ := cos ((2 * k + 1) * π / (2 * n))

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — the zeros of `T_n` are exactly the `n` real numbers
`cos ((2k+1) π / (2n))`, `k = 0, …, n-1`.
-/
theorem roots_T_eq (n : ℕ) :
    (T ℝ n).roots =
      ((Finset.range n).image (fun k : ℕ => Tzero n k)).val :=
  roots_T_real n

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — each zero of `T_n` (for `k < n`) is a root.
-/
theorem isRoot_Tzero {n k : ℕ} (hk : k < n) : (T ℝ n).IsRoot (Tzero n k) := by
  rw [← mem_roots (T_ne_zero ℝ n), roots_T_real, Finset.mem_val, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — each zero of `T_n` is a **simple** root: its multiplicity is `1`.
-/
theorem rootMultiplicity_Tzero {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (Tzero n k) = 1 :=
  rootMultiplicity_T_real hk

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`); the cited
-- section states the general orthogonal-polynomial zero properties for p_n(x),
-- not Chebyshev-specific ones; faithful surface is
-- FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq (whose
-- `roots.toFinset.card = n ∧ Multiset.card roots = n` jointly give no-repetition).
/-- The zeros of `T_n` (as a multiset of roots) have no repetition:
the zeros are **real and simple**. -/
theorem roots_T_nodup (n : ℕ) : (T ℝ n).roots.Nodup := by
  rw [roots_T_real]
  exact (Finset.range n).image (fun k : ℕ => Tzero n k) |>.nodup

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`); faithful surface is
-- FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq
/-- `T_n` has exactly `n` distinct real zeros (accounting for the full multiplicity
budget). This is the cardinality part of the general orthogonal-polynomial zeros
property, specialized to the Chebyshev polynomials of the first kind.
-/
theorem card_roots_T (n : ℕ) : Multiset.card (T ℝ n).roots = n := by
  rw [roots_T_real, ← Finset.card_def, Finset.card_image_of_injOn, Finset.card_range]
  exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`, orthogonality interval (-1,1)); faithful surface is orthogonalPoly_roots_mem_Ioo
/-- **All zeros of `T_n` lie in the open support interval `(-1, 1)`.**
This is the location part of the general orthogonal-polynomial zeros property,
specialized to the Chebyshev polynomials of the first kind.
-/
theorem roots_T_mem_Ioo {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ (T ℝ n).roots) :
    x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [roots_T_real, Finset.mem_val, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  -- the angle θ = (2k+1)π/(2n) lies strictly in (0, π), so cos θ ∈ (-1,1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set θ : ℝ := (2 * (k : ℝ) + 1) * π / (2 * n) with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθlt : θ < π := by
    rw [hθ, div_lt_iff₀ (by positivity)]
    have hkn : (2 * (k : ℝ) + 1) < 2 * n := by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      nlinarith
    nlinarith [Real.pi_pos]
  have hmemTzero : Tzero n k = cos θ := rfl
  -- cos π = -1 < cos θ since cos is strictly antitone on [0,π]
  have hlow : (-1 : ℝ) < cos θ := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨hθpos.le, hθlt.le⟩)
      (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_refl π⟩) hθlt
    rw [Real.cos_pi] at this
    exact this
  -- cos θ < cos 0 = 1
  have hhigh : cos θ < 1 := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), Real.pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hθpos.le, hθlt.le⟩) hθpos
    rw [Real.cos_zero] at this
    exact this
  rw [Set.mem_Ioo]
  exact ⟨hlow, hhigh⟩

section GeneralLocation

open MeasureTheory
open FLMF.Functions.OrthogonalPolynomials

/-- **DLMF 18.2(vi)** — location of the zeros of a general orthogonal polynomial:
if `P` has degree `n ≥ 1` and is orthogonal to every polynomial of lower degree
against a positive nondegenerate measure `μ` (finite total mass and finite moments
of every order, matching the Lebesgue–Stieltjes setting of §18.2(i)) whose mass
lies in the closed orthogonality interval `[a, b]` — endpoints taken in `EReal`,
so unbounded orthogonality intervals are included — then every real zero of `P`
lies in the *open* interval `(a, b)`.

Together with `FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq`
(the "real and simple, exactly `n`" half) this renders the full §18.2(vi) zeros
statement; `roots_T_mem_Ioo` above is its Chebyshev-`T` instance.

DAG: E-18.2.
Numerical: N/A (membership)
Verified: unverified
-/
theorem orthogonalPoly_roots_mem_Ioo {μ : Measure ℝ} {n : ℕ}
    (O : OrthogonalPoly μ n) (hn : 1 ≤ n)
    (hfin : IsFiniteMeasure μ)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    {a b : EReal} (hsupp : ∀ᵐ y ∂μ, (↑(y : ℝ) : EReal) ∈ Set.Icc a b)
    {x : ℝ} (hx : x ∈ O.P.roots) :
    (x : EReal) ∈ Set.Ioo a b := by
  sorry

end GeneralLocation

end FLMF.Chebyshev

end

section

/-
  Chebyshev Polynomials

  Classical identities for Chebyshev polynomials of the first and second kind,
  wrapping Mathlib results:

  C1:  T_n(cos θ) = cos(nθ)                (trigonometric definition)
  C2:  U_n(cos θ) sin θ = sin((n+1)θ)      (second kind trig definition)
  C3:  T_n(cosh θ) = cosh(nθ)              (hyperbolic version)
  C4:  U_n(cosh θ) sinh θ = sinh((n+1)θ)   (hyperbolic second kind)
  C5:  T_{n+2}(x) = 2x T_{n+1}(x) - T_n(x) (three-term recurrence)
  C6:  U_{n+2}(x) = 2x U_{n+1}(x) - U_n(x) (second kind recurrence)
  C7:  T_n(1) = 1                           (evaluation at 1)
  C8:  U_n(1) = n + 1                       (evaluation at 1)
  C9:  2 T_m T_k = T_{m+k} + T_{m-k}       (product-to-sum)
  C10: T_{mn} = T_m ∘ T_n                   (composition semigroup)
  C11: |T_n(x)| ≤ 1 for x ∈ [-1,1]         (pointwise bound)
  C12: T_n'(1) = n²                         (derivative at endpoint)
  C13: ∫ T_n T_m dμ_T = 0 for n ≠ m        (orthogonality)
  C14: ∫ T_0² dμ_T = π                      (norm squared, n=0)
  C15: ∫ T_n² dμ_T = π/2 for n ≥ 1         (norm squared)
  C16: T_n(-x) = (-1)^n T_n(x)             (parity)
  C17: T_n(-1) = (-1)^n                     (evaluation at -1)
  C18: T_n(0) = (-1)^(n/2) or 0            (evaluation at 0)

  References:
  - DLMF 18.3: Definition of Classical OPs
  - DLMF 18.7: Interrelations of Classical OPs
  - Abramowitz & Stegun §22
-/

open Polynomial.Chebyshev Polynomial Real Set MeasureTheory

namespace FLMF.Functions.Chebyshev

/-! ## Trigonometric Connection -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.5.1
-- surface is T_cos_nat
/-- **C1**: T_n(cos θ) = cos(nθ).
    The defining property of Chebyshev polynomials of the first kind. -/
theorem T_cos (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (cos θ) = cos (↑n * θ) :=
  T_real_cos θ n

/-- **DLMF 18.5.1** — T_n(cos θ) = cos(nθ) = ½(zⁿ+z⁻ⁿ) with `z = e^{iθ}`
(so `x = cos θ = ½(z+z⁻¹)`), as the display's 2-link conjunction
(DLMF-faithful restriction of `T_cos`: `n : ℕ`).
The second link is the `z = e^{iθ}` instance of `Complex.cos`'s definition
via `Complex.exp`.

DLMF 18.5.1.
DAG: E-18.5.1.
Numerical: PASS
Verified: unverified
-/
theorem T_cos_nat (n : ℕ) (θ : ℝ) :
    ((T ℝ (n : ℤ)).eval (cos θ) = cos (((n : ℤ) : ℝ) * θ)) ∧
      ((cos (((n : ℤ) : ℝ) * θ) : ℂ) =
        1 / 2 * (Complex.exp (Complex.I * θ) ^ n +
          (Complex.exp (Complex.I * θ))⁻¹ ^ n)) := by
  refine ⟨T_cos (n : ℤ) θ, ?_⟩
  push_cast [Complex.ofReal_cos]
  unfold Complex.cos
  rw [show (Complex.exp (Complex.I * θ))⁻¹ = Complex.exp (-(Complex.I * θ)) from
      (Complex.exp_neg _).symm,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e1 : Complex.exp (((n : ℂ) * θ) * Complex.I) = Complex.exp ((n : ℂ) * (Complex.I * θ)) := by
    congr 1; ring
  have e2 : Complex.exp (-((n : ℂ) * θ) * Complex.I) =
      Complex.exp ((n : ℂ) * -(Complex.I * θ)) := by
    congr 1; ring
  rw [e1, e2]
  ring

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.5.2
-- surface is U_cos_sin_nat
/-- **C2**: U_n(cos θ) sin θ = sin((n+1)θ).
    The defining property of Chebyshev polynomials of the second kind. -/
theorem U_cos_sin (n : ℤ) (θ : ℝ) :
    (U ℝ n).eval (cos θ) * sin θ = sin ((↑n + 1) * θ) :=
  U_real_cos θ n

/-- **DLMF 18.5.2** — U_n(cos θ) sin θ = sin((n+1)θ) = ½(z^{n+1}-z^{-(n+1)})/(z-z⁻¹)
form with `z = e^{iθ}`, as the display's 2-link conjunction (DLMF-faithful
restriction of `U_cos_sin`: `n : ℕ`, `sin θ ≠ 0` — DLMF states the first link
as the quotient `U_n(x) = sin((n+1)θ)/sin θ`, undefined at `sin θ = 0`; this
is the equivalent cross-multiplied form under that same domain restriction).
The second link is likewise stated cross-multiplied
(`sin((n+1)θ)·(z-z⁻¹) = sin θ·(z^{n+1}-z^{-(n+1)})`), the `z = e^{iθ}`
instance of `Complex.sin`'s definition via `Complex.exp` — a pure algebraic
identity that needs no side nonvanishing hypothesis.

DLMF 18.5.2.
DAG: E-18.5.2.
Numerical: PASS
Verified: unverified
-/
theorem U_cos_sin_nat (n : ℕ) (θ : ℝ) (_hθ : sin θ ≠ 0) :
    ((U ℝ (n : ℤ)).eval (cos θ) * sin θ = sin ((((n : ℤ) : ℝ) + 1) * θ)) ∧
      ((sin ((((n : ℤ) : ℝ) + 1) * θ) : ℂ) *
          (Complex.exp (Complex.I * θ) - (Complex.exp (Complex.I * θ))⁻¹) =
        (sin θ : ℂ) * (Complex.exp (Complex.I * θ) ^ (n + 1) -
          (Complex.exp (Complex.I * θ))⁻¹ ^ (n + 1))) := by
  refine ⟨U_cos_sin (n : ℤ) θ, ?_⟩
  have hinv : (Complex.exp (Complex.I * θ))⁻¹ = Complex.exp (-(Complex.I * θ)) :=
    (Complex.exp_neg _).symm
  have hpow : ∀ φ : ℂ, Complex.exp φ ^ (n + 1) = Complex.exp (((n : ℂ) + 1) * φ) := by
    intro φ
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  push_cast [Complex.ofReal_sin]
  unfold Complex.sin
  rw [hinv, hpow, hpow]
  have e1 : Complex.exp (-(((n : ℂ) + 1) * θ) * Complex.I) =
      Complex.exp (((n : ℂ) + 1) * -(Complex.I * θ)) := by
    congr 1; ring
  have e2 : Complex.exp ((((n : ℂ) + 1) * θ) * Complex.I) =
      Complex.exp (((n : ℂ) + 1) * (Complex.I * θ)) := by
    congr 1; ring
  rw [e1, e2]
  ring

/-! ## Hyperbolic Connection -/

-- no-dlmf: strictly-more-general total/junk-value form; the (also no-dlmf)
-- `ℕ`-restricted specialization is `T_cosh_nat`
/-- **C3**: T_n(cosh θ) = cosh(nθ) (hyperbolic z = e^θ instance of the
    z-form ½(zⁿ+z⁻ⁿ) displayed in that equation). -/
theorem T_cosh (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (cosh θ) = cosh (↑n * θ) :=
  T_real_cosh θ n

-- no-dlmf: real hyperbolic (z = e^θ, θ real) instance of DLMF 18.5.1's
-- z-parametrized equality, not the displayed cos-form relation itself and
-- narrower than DLMF's complex-z domain (Semantic audit 2026-08-07); the
-- faithful surface of DLMF 18.5.1 is `T_cos_nat`.
/-- T_n(cosh θ) = cosh(nθ), hyperbolic z = e^θ instance (`n : ℕ` restriction
of `T_cosh`). -/
theorem T_cosh_nat (n : ℕ) (θ : ℝ) :
    (T ℝ (n : ℤ)).eval (cosh θ) = cosh (((n : ℤ) : ℝ) * θ) :=
  T_cosh (n : ℤ) θ

-- no-dlmf: strictly-more-general total/junk-value form (quantifies over all
-- `n : ℤ`, including negative `n`, which DLMF 18.5.2 does not cover); the
-- (also no-dlmf) `ℕ`-restricted specialization is `U_cosh_sinh_nat`.
/-- **C4**: U_n(cosh θ) sinh θ = sinh((n+1)θ) (hyperbolic z = e^θ instance of
    the z-form (zⁿ⁺¹−z⁻ⁿ⁻¹)/(z−z⁻¹) displayed in that equation). -/
theorem U_cosh_sinh (n : ℤ) (θ : ℝ) :
    (U ℝ n).eval (cosh θ) * sinh θ = sinh ((↑n + 1) * θ) :=
  U_real_cosh θ n

-- no-dlmf: real hyperbolic (z = e^θ, θ real) instance of DLMF 18.5.2's
-- z-parametrized equality, not the displayed sin-form relation itself and
-- narrower than DLMF's complex-z domain (Semantic audit 2026-08-07); the
-- faithful surface of DLMF 18.5.2 is `U_cos_sin_nat`.
/-- U_n(cosh θ) sinh θ = sinh((n+1)θ), hyperbolic z = e^θ instance (`n : ℕ`
restriction of `U_cosh_sinh`). -/
theorem U_cosh_sinh_nat (n : ℕ) (θ : ℝ) :
    (U ℝ (n : ℤ)).eval (cosh θ) * sinh θ = sinh ((((n : ℤ) : ℝ) + 1) * θ) :=
  U_cosh_sinh (n : ℤ) θ

/-! ## Three-Term Recurrence -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 3.11.7
-- surface is T_recurrence_nat
/-- **C5**: T_{n+2} = 2X · T_{n+1} - T_n. -/
theorem T_recurrence (n : ℤ) :
    T ℝ (n + 2) = 2 * X * T ℝ (n + 1) - T ℝ n :=
  T_add_two ℝ n

/-- **DLMF 3.11.7** — the Chebyshev first-kind recurrence
T_{m+1}(x) - 2x T_m(x) + T_{m-1}(x) = 0 (m ≥ 1), stated at m = n+1 as
T_{n+2} = 2X · T_{n+1} - T_n (DLMF-faithful restriction of `T_recurrence`:
`n : ℕ`).
DAG: E-3.11.7.
Numerical: PASS
Verified: unverified
-/
theorem T_recurrence_nat (n : ℕ) :
    T ℝ ((n : ℤ) + 2) = 2 * X * T ℝ ((n : ℤ) + 1) - T ℝ (n : ℤ) :=
  T_recurrence (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9
-- surface is U_recurrence_nat
/-- **C6**: U_{n+2} = 2X · U_{n+1} - U_n. -/
theorem U_recurrence (n : ℤ) :
    U ℝ (n + 2) = 2 * X * U ℝ (n + 1) - U ℝ n :=
  U_add_two ℝ n

/-- **DLMF 18.9** (18.9.1 specialized by Table 18.9.1, Chebyshev U row:
A_n = 2, B_n = 0, C_n = 1) — U_{n+2} = 2X · U_{n+1} - U_n (DLMF-faithful
restriction of `U_recurrence`: `n : ℕ`).
DAG: E-18.9.
Numerical: PASS
Verified: unverified
-/
theorem U_recurrence_nat (n : ℕ) :
    U ℝ ((n : ℤ) + 2) = 2 * X * U ℝ ((n : ℤ) + 1) - U ℝ (n : ℤ) :=
  U_recurrence (n : ℤ)

/-! ## Initial Values -/

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_0 = 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_0(x) = 1 line of that display). -/
theorem T_zero' : T ℝ 0 = 1 := T_zero ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_1 = X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_1(x) = x line of that display). -/
theorem T_one' : T ℝ 1 = X := T_one ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_2 = 2X² - 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_2(x) = 2x² - 1 line of that display). -/
theorem T_two' : T ℝ 2 = 2 * X ^ 2 - 1 := T_two ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_3 = 4X³ - 3X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_3(x) = 4x³ - 3x line of that display), from the three-term
recurrence applied to `T_1, T_2`. -/
theorem T_three' : T ℝ 3 = 4 * X ^ 3 - 3 * X := by
  have h := T_recurrence 1
  norm_num at h
  rw [h, T_two']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_4 = 8X⁴ - 8X² + 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_4(x) = 8x⁴ - 8x² + 1 line of that display), from the three-term
recurrence applied to `T_2, T_3`. -/
theorem T_four' : T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  have h := T_recurrence 2
  norm_num at h
  rw [h, T_three', T_two']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_5 = 16X⁵ - 20X³ + 5X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_5(x) = 16x⁵ - 20x³ + 5x line of that display), from the three-term
recurrence applied to `T_3, T_4`. -/
theorem T_five' : T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h := T_recurrence 3
  norm_num at h
  rw [h, T_four', T_three']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_6 = 32X⁶ - 48X⁴ + 18X² - 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev
first-kind polynomials: the T_6(x) = 32x⁶ - 48x⁴ + 18x² - 1 line of that display), from the
three-term recurrence applied to `T_4, T_5`. -/
theorem T_six' : T ℝ 6 = 32 * X ^ 6 - 48 * X ^ 4 + 18 * X ^ 2 - 1 := by
  have h := T_recurrence 4
  norm_num at h
  rw [h, T_five', T_four']
  ring

/-- **DLMF 18.5.14.** The explicit low-degree Chebyshev polynomials of the first kind,
`T_0(x)` through `T_6(x)`, as polynomial identities over `ℝ[X]`.

DAG: E-18.5.14.
Numerical: PASS
Verified: verified
-/
theorem T_explicit_degree_le_six :
    T ℝ 0 = 1 ∧ T ℝ 1 = X ∧ T ℝ 2 = 2 * X ^ 2 - 1 ∧
      T ℝ 3 = 4 * X ^ 3 - 3 * X ∧ T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 ∧
      T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X ∧
      T ℝ 6 = 32 * X ^ 6 - 48 * X ^ 4 + 18 * X ^ 2 - 1 :=
  ⟨T_zero', T_one', T_two', T_three', T_four', T_five', T_six'⟩

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_0 = 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_0(x) = 1 line of that display). -/
theorem U_zero' : U ℝ 0 = 1 := U_zero ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_1 = 2X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_1(x) = 2x line of that display). -/
theorem U_one' : U ℝ 1 = 2 * X := U_one ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_2 = 4X² - 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_2(x) = 4x² - 1 line of that display). -/
theorem U_two' : U ℝ 2 = 4 * X ^ 2 - 1 := U_two ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_3 = 8X³ - 4X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_3(x) = 8x³ - 4x line of that display), from the three-term
recurrence applied to `U_1, U_2`. -/
theorem U_three' : U ℝ 3 = 8 * X ^ 3 - 4 * X := by
  have h := U_recurrence 1
  norm_num at h
  rw [h, U_two']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_4 = 16X⁴ - 12X² + 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_4(x) = 16x⁴ - 12x² + 1 line of that display), from the
three-term recurrence applied to `U_2, U_3`. -/
theorem U_four' : U ℝ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 := by
  have h := U_recurrence 2
  norm_num at h
  rw [h, U_three', U_two']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_5 = 32X⁵ - 32X³ + 6X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_5(x) = 32x⁵ - 32x³ + 6x line of that display), from the
three-term recurrence applied to `U_3, U_4`. -/
theorem U_five' : U ℝ 5 = 32 * X ^ 5 - 32 * X ^ 3 + 6 * X := by
  have h := U_recurrence 3
  norm_num at h
  rw [h, U_four', U_three']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_6 = 64X⁶ - 80X⁴ + 24X² - 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_6(x) = 64x⁶ - 80x⁴ + 24x² - 1 line of that display), from the
three-term recurrence applied to `U_4, U_5`. -/
theorem U_six' : U ℝ 6 = 64 * X ^ 6 - 80 * X ^ 4 + 24 * X ^ 2 - 1 := by
  have h := U_recurrence 4
  norm_num at h
  rw [h, U_five', U_four']
  ring

/-- **DLMF 18.5.15.** The explicit low-degree Chebyshev polynomials of the second kind,
`U_0(x)` through `U_6(x)`, as polynomial identities over `ℝ[X]`.

DAG: E-18.5.15.
Numerical: PASS
Verified: verified
-/
theorem U_explicit_degree_le_six :
    U ℝ 0 = 1 ∧ U ℝ 1 = 2 * X ∧ U ℝ 2 = 4 * X ^ 2 - 1 ∧
      U ℝ 3 = 8 * X ^ 3 - 4 * X ∧ U ℝ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 ∧
      U ℝ 5 = 32 * X ^ 5 - 32 * X ^ 3 + 6 * X ∧
      U ℝ 6 = 64 * X ^ 6 - 80 * X ^ 4 + 24 * X ^ 2 - 1 :=
  ⟨U_zero', U_one', U_two', U_three', U_four', U_five', U_six'⟩

/-! ## Evaluation at Special Points -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1
/-- **C7**: T_n(1) = 1. -/
theorem T_at_one (n : ℤ) : (T ℝ n).eval 1 = 1 := T_eval_one ℝ n

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, p_n(1) column);
-- conjunction carrier is T_table_18_6_1
/-- T_n(1) = 1 (DLMF-faithful restriction of `T_at_one`: `n : ℕ`). -/
theorem T_at_one_nat (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 := T_at_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1 (T_n(-1) = (-1)^n is a derived combination of the
-- parity row and the p_n(1) column, not itself a Table 18.6.1 entry)
/-- **C17**: T_n(-1) = (-1)^n. -/
theorem T_at_neg_one (n : ℤ) : (T ℝ n).eval (-1) = n.negOnePow := T_eval_neg_one ℝ n

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's T row: the parity
-- p_n(-x) = (-1)^n p_n(x) combined with p_n(1) = 1 at x = 1), not itself a table
-- entry; conjunction carrier is T_table_18_6_1
/-- T_n(-1) = (-1)^n (`n : ℕ` restriction of `T_at_neg_one`). -/
theorem T_at_neg_one_nat (n : ℕ) :
    (T ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow := T_at_neg_one (n : ℤ)

/-- **C18**: T_n(0) evaluation. DLMF 18.6 (Table 18.6.1, values at 0).

Restricted to 0 ≤ n per DLMF §18.3/§18.6 (Semantic audit 2026-07-29; Mathlib's
Chebyshev T extends to ℤ via T_{-n}=T_n).

DAG: E-18.6.
Numerical: N/A (parity)
Verified: verified
-/
theorem T_at_zero (n : ℤ) (_hn : 0 ≤ n) :
    (T ℝ n).eval 0 = if Even n then ((n / 2).negOnePow : ℤ) else 0 :=
  T_eval_zero ℝ n

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is U_at_one_nat
/-- **C8**: U_n(1) = n + 1. -/
theorem U_at_one (n : ℤ) : (U ℝ n).eval 1 = ↑n + 1 := U_eval_one ℝ n

/-- **DLMF 18.6** (Table 18.6.1, values at ±1) — U_n(1) = n + 1 (DLMF-faithful
restriction of `U_at_one`: `n : ℕ`).
DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem U_at_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval 1 = ((n : ℤ) : ℝ) + 1 := U_at_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form of U_at_neg_one_nat (itself
-- no-dlmf, an instance of DLMF 18.6; the faithful parity surface is U_eval_neg'_nat)
/-- U_n(-1) = (-1)^n (n + 1). -/
theorem U_at_neg_one (n : ℤ) :
    (U ℝ n).eval (-1) = n.negOnePow * (↑n + 1) := U_eval_neg_one ℝ n

-- no-dlmf: instance of DLMF 18.6 (Table 18.6.1 states the parity
-- U_n(-x) = (-1)^n U_n(x) and the value U_n(1) = n + 1; the value at x = -1 is
-- their derived combination, not a table entry); faithful surface is U_eval_neg'_nat
/-- U_n(-1) = (-1)^n (n + 1) (`n : ℕ` restriction of `U_at_neg_one`). -/
theorem U_at_neg_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow * (((n : ℤ) : ℝ) + 1) :=
  U_at_neg_one (n : ℤ)

/-- **DLMF 18.6** (Table 18.6.1, parity) — U_n(-x) = (-1)^n U_n(x), the Chebyshev
second-kind parity relation.
DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem U_eval_neg'_nat (n : ℕ) (x : ℝ) :
    (U ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (U ℝ (n : ℤ)).eval x :=
  U_eval_neg ℝ n x

/-! ## Symmetry -/

-- no-dlmf: index symmetry T_{-n}=T_n of Mathlib's ℤ-indexed extension; no DLMF counterpart
/-- T is even: T(-n) = T(n). -/
theorem T_neg' (n : ℤ) : T ℝ (-n) = T ℝ n := T_neg ℝ n

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1
/-- **C16**: T_n(-x) = (-1)^n T_n(x) (parity in x). -/
theorem T_eval_neg' (n : ℤ) (x : ℝ) :
    (T ℝ n).eval (-x) = n.negOnePow * (T ℝ n).eval x := T_eval_neg ℝ n x

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, parity column);
-- conjunction carrier is T_table_18_6_1
/-- T_n(-x) = (-1)^n T_n(x) (DLMF-faithful restriction of `T_eval_neg'`: `n : ℕ`). -/
theorem T_eval_neg'_nat (n : ℕ) (x : ℝ) :
    (T ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (T ℝ (n : ℤ)).eval x :=
  T_eval_neg' (n : ℤ) x

/-- **DLMF 18.6.** Table 18.6.1's `T_n` row (symmetry and special values): the parity
relation `T_n(-x) = (-1)^n T_n(x)` together with the endpoint value `T_n(1) = 1`. (The
further value `T_n(-1) = (-1)^n` is the `x = 1` instance of the parity relation combined
with the endpoint value, not a separate table entry.)

DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem T_table_18_6_1 (n : ℕ) (x : ℝ) :
    (T ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (T ℝ (n : ℤ)).eval x ∧
      (T ℝ (n : ℤ)).eval 1 = 1 :=
  ⟨T_eval_neg'_nat n x, T_at_one_nat n⟩

/-! ## Product and Composition Identities -/

/-- **C9**: Product-to-sum: 2 T_m T_k = T_{m+k} + T_{m-k} (DLMF 18.18.21, where
DLMF's `m, n` range over nonnegative integers).

DAG: E-18.18.21.
Numerical: PASS
Verified: unverified
-/
theorem T_product_to_sum (m k : ℤ) (_hm : 0 ≤ m) (_hk : 0 ≤ k) :
    2 * T ℝ m * T ℝ k = T ℝ (m + k) + T ℝ (m - k) :=
  T_mul_T ℝ m k

-- no-dlmf: composition/semigroup property T_{mn}=T_m∘T_n; no numbered DLMF equation
-- states this (checked §18.5, §18.7, §18.16 — absent); the previous tag 18.5.4 is
-- unrelated (Chebyshev fourth-kind W_n definition).
/-- **C10**: Composition property: T_{mn} = T_m ∘ T_n (DLMF 18.5.4).
    Chebyshev polynomials form a commutative semigroup under composition.

-/
theorem T_composition (m n : ℤ) :
    T ℝ (m * n) = (T ℝ m).comp (T ℝ n) :=
  T_mul ℝ m n

/-! ## Pointwise Bound -/

-- no-dlmf: strictly-more-general total/junk-value form; see T_abs_le_one_nat and,
-- for the DLMF 18.14.1 general Jacobi form, abs_jacobiP_le_jacobiP_one
-- (FLMF/Functions/Chebyshev/PointwiseBound.lean)
/-- **C11**: |T_n(x)| ≤ 1 for x ∈ [-1,1]. -/
theorem T_abs_le_one (n : ℤ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (T ℝ n).eval x ∈ Icc (-1 : ℝ) 1 :=
  eval_T_real_mem_Icc n hx

-- no-dlmf: instance of DLMF 18.14.1 (Chebyshev T_n is the renormalized Jacobi case
-- α = β = -1/2 of the bound |P_n^{(α,β)}(x)| ≤ P_n^{(α,β)}(1)); faithful surface is
-- abs_jacobiP_le_jacobiP_one (FLMF/Functions/Chebyshev/PointwiseBound.lean)
/-- |T_n(x)| ≤ 1 for x ∈ [-1,1] (`n : ℕ` restriction of `T_abs_le_one`). -/
theorem T_abs_le_one_nat (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (T ℝ (n : ℤ)).eval x ∈ Icc (-1 : ℝ) 1 :=
  T_abs_le_one (n : ℤ) hx

/-! ## Interrelations Between T and U -/

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is `U_eq_X_mul_U_add_T'_nat`
/-- U_{n+1} = X U_n + T_{n+1} (interrelations between T and U). -/
theorem U_eq_X_mul_U_add_T' (n : ℤ) :
    U ℝ (n + 1) = X * U ℝ n + T ℝ (n + 1) :=
  U_eq_X_mul_U_add_T ℝ n

-- no-dlmf: this specific identity `U_{n+1} = X U_n + T_{n+1}` is not itself
-- one of §18.9's stated relations (e.g. `U_{n+1}=2xU_n-U_{n-1}`,
-- `T_n=½(U_n-U_{n-2})`); it is a derived algebraic consequence, not a
-- DLMF-numbered display. `n : ℕ` specialization of `U_eq_X_mul_U_add_T'`.
/-- U_{n+1} = X U_n + T_{n+1} (interrelations between T and U), `n : ℕ`. -/
theorem U_eq_X_mul_U_add_T'_nat (n : ℕ) :
    U ℝ ((n : ℤ) + 1) = X * U ℝ (n : ℤ) + T ℝ ((n : ℤ) + 1) :=
  U_eq_X_mul_U_add_T' (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is T_eq_U_sub_X_mul_U'_nat
/-- T_n = U_n - X U_{n-1} (interrelations between T and U). -/
theorem T_eq_U_sub_X_mul_U' (n : ℤ) :
    T ℝ n = U ℝ n - X * U ℝ (n - 1) :=
  T_eq_U_sub_X_mul_U ℝ n

-- no-dlmf: derived algebraic consequence of DLMF 18.9.9 (T_n = ½(U_n − U_{n−2}))
-- combined with the Chebyshev-U three-term recurrence; not itself a
-- DLMF-numbered display. `n : ℕ` restriction of `T_eq_U_sub_X_mul_U'`.
/-- T_n = U_n - X U_{n-1} (interrelations between T and U), `n : ℕ`. -/
theorem T_eq_U_sub_X_mul_U'_nat (n : ℕ) :
    T ℝ (n : ℤ) = U ℝ (n : ℤ) - X * U ℝ ((n : ℤ) - 1) :=
  T_eq_U_sub_X_mul_U' (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is T_eq_X_mul_U_sub_U'_nat
/-- T_{n+2} = X U_{n+1} - U_n (interrelations between T and U). -/
theorem T_eq_X_mul_U_sub_U' (n : ℤ) :
    T ℝ (n + 2) = X * U ℝ (n + 1) - U ℝ n :=
  T_eq_X_mul_U_sub_U ℝ n

-- no-dlmf: derived algebraic consequence of DLMF 18.9.9 (T_n = ½(U_n − U_{n−2}))
-- combined with the Chebyshev-U three-term recurrence; not itself a
-- DLMF-numbered display. `n : ℕ` restriction of `T_eq_X_mul_U_sub_U'`.
/-- T_{n+2} = X U_{n+1} - U_n (interrelations between T and U), `n : ℕ`. -/
theorem T_eq_X_mul_U_sub_U'_nat (n : ℕ) :
    T ℝ ((n : ℤ) + 2) = X * U ℝ ((n : ℤ) + 1) - U ℝ (n : ℤ) :=
  T_eq_X_mul_U_sub_U' (n : ℤ)

/-! ## Derivatives at Endpoints -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.1
-- surface is T_deriv_at_one_nat
/-- **C12**: T_n'(1) = n². -/
theorem T_deriv_at_one (n : ℤ) :
    (Polynomial.derivative (T ℝ n)).eval 1 = ↑n ^ 2 :=
  derivative_T_eval_one (R := ℝ) n

-- no-dlmf: no DLMF equation number gives Tₙ'(1) = n² directly (Table 18.6.1
-- has no derivative column; §18.9 derivative relations 18.9.21/18.9.22 do not
-- give this endpoint value either) — matches the sibling `U_deriv_at_one`
-- treatment below. `n : ℕ` specialization of `T_deriv_at_one`.
/-- T_n'(1) = n², `n : ℕ`. -/
theorem T_deriv_at_one_nat (n : ℕ) :
    (Polynomial.derivative (T ℝ (n : ℤ))).eval 1 = ((n : ℤ) : ℝ) ^ 2 :=
  T_deriv_at_one (n : ℤ)

-- no-dlmf: endpoint-derivative value 3 U_n'(1) = n(n+1)(n+2); no DLMF equation states
-- it directly (Table 18.6.1 has no p_n'(1) column, only p'_{2n+1}(0); §18.9 derivative
-- equations 18.9.21/18.9.22 do not give this endpoint value either).
/-- 3 U_n'(1) = n(n+1)(n+2). DLMF 18.6 (Table 18.6.1, endpoint derivatives).

-/
theorem U_deriv_at_one (n : ℤ) :
    3 * (Polynomial.derivative (U ℝ n)).eval 1 = (↑n + 2) * (↑n + 1) * ↑n :=
  derivative_U_eval_one (R := ℝ) n

/-! ## Orthogonality with respect to (1-x²)^{-1/2} measure -/

-- no-dlmf: instance of DLMF 18.2.1 / the j ≠ k case of DLMF 3.11.8 (specific family
-- T_n and weight (1-x²)^{-1/2}, off-diagonal case only); faithful surface is
-- T_orthogonality_relation
/-- **C13**: ∫ T_n T_m dμ_T = 0 for n ≠ m.
    Here μ_T is the Chebyshev measure with density (1-x²)^{-1/2} on [-1,1]. -/
theorem T_orthogonal {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 :=
  integral_eval_T_real_mul_eval_T_real_measureT_of_ne h

-- no-dlmf: instance of DLMF 3.11.8 (fixed j = k = 0; equivalently the n = 0 entry of
-- Table 18.3.1's h_n column); faithful surface is T_orthogonality_relation
/-- **C14**: ∫ T_0² dμ_T = π (norm squared of T_0). -/
theorem T_zero_norm_sq :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π :=
  integral_eval_T_real_mul_self_measureT_zero

/-- **C15**: ∫ T_n² dμ_T = π/2 for n ≥ 1. DLMF 18.3 (Table 18.3.1, h_n column:
    h_n = π/2 for T_n, n > 0).

DAG: E-18.3.
Numerical: PASS
Verified: verified
-/
theorem T_norm_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 :=
  integral_T_real_mul_self_measureT_of_ne_zero hn

/-- **DLMF 3.11.8** — the full Chebyshev first-kind orthogonality relation on
[-1,1] with weight (1-x²)^{-1/2} (realized by `measureT`):
∫ T_j T_k dμ_T = π if j = k = 0, π/2 if j = k ≠ 0, and 0 if j ≠ k.
DAG: E-3.11.8.
Numerical: PASS
Verified: unverified
-/
theorem T_orthogonality_relation (j k : ℕ) :
    ∫ x, (T ℝ j).eval x * (T ℝ k).eval x ∂measureT =
      if j = k then (if j = 0 then π else π / 2) else 0 := by
  rcases eq_or_ne j k with rfl | hjk
  · rcases eq_or_ne j 0 with rfl | hj
    · rw [if_pos rfl, if_pos rfl]
      simpa using T_zero_norm_sq
    · rw [if_pos rfl, if_neg hj]
      exact T_norm_sq hj
  · rw [if_neg hjk]
    exact T_orthogonal hjk

/-! ## Degree and Leading Coefficient -/

-- no-dlmf: Table 18.3.1 has no degree column ("p_n has degree n" is §18.2(i)
-- prose, not a displayed equation) — same adjudication as U_degree
-- (2026-08-11 relation-audit); the faithful Table 18.3.1 T-surfaces are the
-- leading-coefficient and normalization lemmas.
/-- deg(T_n) = |n| (DLMF §18.2(i) degree convention).

Restricted to 0 ≤ n per DLMF §18.3/§18.6 (Semantic audit 2026-07-29; Mathlib's
Chebyshev T extends to ℤ via T_{-n}=T_n).
-/
theorem T_degree (n : ℤ) (_hn : 0 ≤ n) : (T ℝ n).degree = n.natAbs := degree_T ℝ n

-- no-dlmf: strictly-more-general total/junk-value form (extends via |n| to negative
-- indices not covered by DLMF's nonnegative-integer convention); the faithful DLMF
-- 18.3 surface is T_leading_coeff_nat
/-- leading_coeff(T_n) = 2^{|n|-1} (Table 18.3.1, leading coefficient κ_n). -/
theorem T_leading_coeff (n : ℤ) :
    (T ℝ n).leadingCoeff = 2 ^ (n.natAbs - 1) := leadingCoeff_T ℝ n

/-- **DLMF 18.3** (Table 18.3.1, leading coefficient κ_n) — leading_coeff(T_0) = 1
and leading_coeff(T_n) = 2^{n-1} for n ≥ 1, stated as the two table rows
explicitly (the earlier single ℕ-truncated-subtraction formula was true in Lean
but transcribed as the false real exponent 2^{-1} at n = 0 by the Numerical
oracle — see the `n ≠ 0` guard precedent of 2026-08-02).
DAG: E-18.3.
Numerical: N/A (conjunction-partial)
Verified: unverified
-/
theorem T_leading_coeff_nat :
    (T ℝ ((0 : ℕ) : ℤ)).leadingCoeff = 1 ∧
      ∀ n : ℕ, n ≠ 0 → (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) :=
  ⟨by simp [T_leading_coeff (0 : ℤ)], fun n _ => by
    simpa using T_leading_coeff (n : ℤ)⟩

-- no-dlmf: Table 18.3.1 has no degree column (its columns are p_n(x), (a,b), w(x),
-- h_n, k_n, k̃_n/k_n, Constraints); "p_n has degree n" is the prose convention of
-- §18.2(i), not a displayed equation. The faithful Table 18.3.1 surfaces for U are
-- U_leading_coeff (k_n column) and the h_n/orthogonality lemmas.
/-- deg(U_n) = n for n : ℕ (Table 18.3.1 lists U_n among the degree-n classical OPs). -/
theorem U_degree (n : ℕ) : (U ℝ (n : ℤ)).degree = n := degree_U_natCast ℝ n

/-- leading_coeff(U_n) = 2^n for n : ℕ. DLMF 18.3 (Table 18.3.1, leading coefficient κ_n).

DAG: E-18.3.
Numerical: PASS
Verified: unverified
-/
theorem U_leading_coeff (n : ℕ) :
    (U ℝ (n : ℤ)).leadingCoeff = 2 ^ n := leadingCoeff_U_natCast ℝ n

end FLMF.Functions.Chebyshev

end
