import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

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
Fidelity: tier1 PASS
Verified: verified (tier2)
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
