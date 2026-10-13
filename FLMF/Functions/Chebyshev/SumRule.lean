import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

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
-- (FLMF/Functions/Chebyshev/ProductToSum.lean)
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
-- (FLMF/Functions/Chebyshev/ProductToSum.lean)
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
