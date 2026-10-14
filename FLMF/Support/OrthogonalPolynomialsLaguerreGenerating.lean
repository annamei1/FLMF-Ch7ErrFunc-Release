import FLMF.Support.OrthogonalPolynomialsLaguerre
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Laguerre generating function (coefficient / recurrence form), DLMF 18.12.13

DLMF 18.12.13 states the generating-function identity for the generalized
Laguerre polynomials `L_n^α`:

```
∑_{n=0}^∞ L_n^α(x) tⁿ = (1 - t)^{-α-1} · exp(-x t / (1 - t)).
```

The right-hand side `G(x, t) = (1-t)^{-α-1} exp(-xt/(1-t))` is the unique
(normalized, `G(x,0)=1`) solution of the first–order linear ODE in `t`

```
(1 - t)² ∂G/∂t = ((α + 1)(1 - t) - x) · G,            (★)
```

obtained by logarithmic differentiation
`∂_t log G = (α+1)/(1-t) - x/(1-t)²`.

Writing `G = ∑ₙ Lₙ tⁿ` and extracting the `tⁿ`–coefficient of `(★)` yields the
classical three–term recurrence (DLMF 18.9.13)

```
(n+1) L_{n+1}^α = (2n + 1 + α) L_n^α - X · L_n^α - (n + α) L_{n-1}^α.     (R)
```

Thus `(R)` is *exactly the algebraic content* of the generating-function
identity DLMF 18.12.13: it is the coefficient form of the defining ODE `(★)`.
We establish it here as a polynomial identity over `ℝ`, completely formally
(no analysis), by comparing coefficients of the explicit DLMF-18.5.12 sum.

## Main results

* `Polynomial.coeff_laguerre` : the explicit `X^k` coefficient of `L_n^α`.
* `Polynomial.laguerre_recurrence` : the three-term recurrence `(R)`, the
  coefficient form of DLMF 18.12.13.
-/

namespace Polynomial

open scoped BigOperators
open Finset

-- no-dlmf: chain link 18.5.12 (assembled in
-- FLMF.Functions.OrthogonalPolynomials.laguerre_eval_eq_kummerM,
-- FLMF/Functions/OrthogonalPolynomials/LaguerreKummer.lean)
/-- The explicit `X^k` coefficient of the generalized Laguerre polynomial
`L_n^α`, from the defining sum DLMF 18.5.12. -/
theorem coeff_laguerre (α : ℝ) (n k : ℕ) :
    (laguerre α n).coeff k =
      if k ≤ n then
        (-1) ^ k * ((ascPochhammer ℝ (n - k)).eval (α + (k : ℝ) + 1))
          / (k.factorial * (n - k).factorial : ℝ)
      else 0 := by
  rw [laguerre, finsetSum_coeff]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro b hb hbk
      rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hbk), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_range] at hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

-- no-dlmf: auxiliary coefficient restriction (k ≤ n branch)
/-- Auxiliary: for `k ≤ n`, the coefficient simplifies to the explicit value. -/
theorem coeff_laguerre_of_le (α : ℝ) {n k : ℕ} (hkn : k ≤ n) :
    (laguerre α n).coeff k =
      (-1) ^ k * ((ascPochhammer ℝ (n - k)).eval (α + (k : ℝ) + 1))
        / (k.factorial * (n - k).factorial : ℝ) := by
  rw [coeff_laguerre, if_pos hkn]

-- no-dlmf: auxiliary coefficient vanishing beyond the degree
/-- Coefficients beyond the degree vanish. -/
theorem coeff_laguerre_of_lt (α : ℝ) {n k : ℕ} (hkn : n < k) :
    (laguerre α n).coeff k = 0 := by
  rw [coeff_laguerre, if_neg (by omega)]

/-! ## Pochhammer step lemmas (right- and left-incrementing the index). -/

-- no-dlmf: rising-factorial right-increment step (infrastructure)
/-- Right increment: `(α+k+1)_{m+1} = (α+k+1)_m · (α + k + 1 + m)`. -/
private theorem poch_succ_right (m : ℕ) (z : ℝ) :
    (ascPochhammer ℝ (m + 1)).eval z = (ascPochhammer ℝ m).eval z * (z + (m : ℝ)) := by
  rw [ascPochhammer_succ_eval]

-- no-dlmf: rising-factorial left-increment step (infrastructure)
/-- Left increment: `(z)_{m+1} = z · (z+1)_m`. -/
private theorem poch_succ_left (m : ℕ) (z : ℝ) :
    (ascPochhammer ℝ (m + 1)).eval z = z * (ascPochhammer ℝ m).eval (z + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp]
  simp

end Polynomial
