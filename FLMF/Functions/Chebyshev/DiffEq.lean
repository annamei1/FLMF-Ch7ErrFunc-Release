import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev

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
Fidelity: tier1 PASS
Verified: verified (tier2)
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
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem chebyshevU_ode_eval_nat (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (U ℝ (n : ℤ)))).eval x
        - 3 * x * (derivative (U ℝ (n : ℤ))).eval x
        + (((n : ℤ) : ℝ) + 2) * ((n : ℤ) : ℝ) * (U ℝ (n : ℤ)).eval x = 0 :=
  chebyshevU_ode_eval (n : ℤ) x

end FLMF.Functions.Chebyshev
