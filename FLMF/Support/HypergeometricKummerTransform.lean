import FLMF.Support.HypergeometricKummerODE
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Kummer's transformation `M(a;b;z) = eᶻ M(b−a;b;−z)` (framework — DLMF 13.2.39)

* `sum_neg_one_pow_choose_ascPochhammer` — the **Chu–Vandermonde identity** in
  Kummer form: `∑ₖ (−1)ᵏ C(n,k) (b−a)ₖ/(b)ₖ = (a)ₙ/(b)ₙ` (the terminating
  Gauss sum `₂F₁(−n, b−a; b; 1)`), by induction on `n` through the recurrence
  `Sₙ₊₁(a,b) = Sₙ(a,b) − ((b−a)/b)·Sₙ(a,b+1)`. Proved under the blanket
  hypothesis `b` off every nonpositive integer, which is narrower than DLMF
  15.4.24 needs (only `n = 0,1,2,…`); the faithful full-strength surface is
  `ordinaryHypergeometric_neg_nat_one_dlmf` in `GaussValues.lean`, via the
  bounded-hypothesis helper `sum_neg_one_pow_choose_ascPochhammer_bounded`
  (also `GaussValues.lean`).
* `kummerCoefficient_eq_sum_div_factorial` — its Cauchy-product form
  `cₙ(a,b) = ∑ₖ (−1)ᵏ cₖ(b−a,b)/(n−k)!`.
* `kummerM_kummer_transform` — **Kummer's transformation** (DLMF 13.2.39):
  `M(a;b;z) = eᶻ · M(b−a;b;−z)`, for `b` off the nonpositive integers, by the
  Cauchy product of the (absolutely convergent, entire) series.
-/

open Nat Finset FormalMultilinearSeries

namespace FLMF.Hypergeometric

section ChuVandermonde

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

-- no-dlmf: narrower-than-DLMF instance of 15.4.24 (blanket avoidance of every
-- nonpositive integer, rather than only the ≤ n poles the finite sum's own
-- denominators can hit); the faithful DLMF-domain surface is
-- `ordinaryHypergeometric_neg_nat_one_dlmf` (GaussValues.lean), via the
-- bounded-hypothesis helper `sum_neg_one_pow_choose_ascPochhammer_bounded`
-- (also GaussValues.lean).
/-- **Chu–Vandermonde, Kummer form** (at `z = 1`):
`∑ₖ (−1)ᵏ C(n,k) (b−a)ₖ/(b)ₖ = (a)ₙ/(b)ₙ`, for `b` off every nonpositive
integer — a narrower hypothesis than DLMF 15.4.24 requires (only
`n = 0,1,2,…`). -/
theorem sum_neg_one_pow_choose_ascPochhammer (n : ℕ) :
    ∀ a b : 𝕂, (∀ k : ℕ, (k : 𝕂) ≠ -b) →
      ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : 𝕂)
        * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)
      = (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹ := by
  induction n with
  | zero =>
    intro a b _
    simp
  | succ n ih =>
    intro a b hb
    have hb0 : b ≠ 0 := fun h => hb 0 (by simp [h])
    have hb1 : ∀ k : ℕ, (k : 𝕂) ≠ -(b + 1) := fun k h =>
      hb (k + 1) (by push_cast; linear_combination h)
    have hB : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn _ => hb kn
    have hB1 : (ascPochhammer 𝕂 n).eval (b + 1) ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn _ => hb1 kn
    have hbridge : b * (ascPochhammer 𝕂 n).eval (b + 1)
        = (ascPochhammer 𝕂 n).eval b * (b + n) := by
      rw [← ascPochhammer_succ_eval', ascPochhammer_succ_eval]
    -- peel the `k = 0` term and split Pascal's rule on the rest
    rw [Finset.sum_range_succ']
    have hsplit : ∀ j ∈ range (n + 1), (-1 : 𝕂) ^ (j + 1) * ((n + 1).choose (j + 1) : 𝕂)
        * ((ascPochhammer 𝕂 (j + 1)).eval (b - a) * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹)
        = -((b - a) * b⁻¹) * ((-1) ^ j * (n.choose j : 𝕂)
            * ((ascPochhammer 𝕂 j).eval (b + 1 - a) * ((ascPochhammer 𝕂 j).eval (b + 1))⁻¹))
          + (-1) ^ (j + 1) * (n.choose (j + 1) : 𝕂)
            * ((ascPochhammer 𝕂 (j + 1)).eval (b - a)
              * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹) := by
      intro j _
      rw [Nat.choose_succ_succ' n j]
      push_cast
      rw [ascPochhammer_succ_eval' j (b - a), ascPochhammer_succ_eval' j b,
        show b - a + 1 = b + 1 - a by ring, mul_inv]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- the first half is `−((b−a)/b) · Sₙ(a, b+1)`
    have hA : ∑ j ∈ range (n + 1), -((b - a) * b⁻¹) * ((-1) ^ j * (n.choose j : 𝕂)
        * ((ascPochhammer 𝕂 j).eval (b + 1 - a) * ((ascPochhammer 𝕂 j).eval (b + 1))⁻¹))
        = -((b - a) * b⁻¹)
          * ((ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval (b + 1))⁻¹) := by
      rw [← Finset.mul_sum, ih a (b + 1) hb1]
    -- the second half is `Sₙ(a, b) − 1`
    have hBsum : ∑ j ∈ range (n + 1), (-1 : 𝕂) ^ (j + 1) * (n.choose (j + 1) : 𝕂)
        * ((ascPochhammer 𝕂 (j + 1)).eval (b - a) * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹)
        = (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹ - 1 := by
      have h1 := Finset.sum_range_succ'
        (fun k => (-1 : 𝕂) ^ k * (n.choose k : 𝕂)
          * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)) (n + 1)
      have h2 := Finset.sum_range_succ
        (fun k => (-1 : 𝕂) ^ k * (n.choose k : 𝕂)
          * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)) (n + 1)
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
        Nat.choose_zero_right, Nat.cast_one, pow_zero, ascPochhammer_zero,
        Polynomial.eval_one, inv_one, mul_one] at h1 h2
      rw [ih a b hb] at h2
      linear_combination h2 - h1
    rw [hA, hBsum]
    -- close with the Pochhammer recursions
    rw [ascPochhammer_succ_eval n a, ascPochhammer_succ_eval' n b, mul_inv]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, ascPochhammer_zero,
      Polynomial.eval_one, inv_one, mul_one]
    field_simp
    linear_combination ((ascPochhammer 𝕂 n).eval a) * hbridge

/-- The Cauchy-product form of Chu–Vandermonde:
`cₙ(a,b) = ∑ₖ (−1)ᵏ cₖ(b−a, b)/(n−k)!`. -/
-- no-dlmf: coefficient Cauchy-product identity for Kummer's transformation, no DLMF counterpart
theorem kummerCoefficient_eq_sum_div_factorial (a b : 𝕂) (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * kummerCoefficient (b - a) b k / ((n - k)! : 𝕂)
      = kummerCoefficient a b n := by
  have hfn : (n ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hstep : ∀ k ∈ range (n + 1), (-1 : 𝕂) ^ k * kummerCoefficient (b - a) b k
      / ((n - k)! : 𝕂)
      = (n ! : 𝕂)⁻¹ * ((-1) ^ k * (n.choose k : 𝕂)
        * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcf : ((n.choose k : ℕ) : 𝕂) * (k ! : 𝕂) * (((n - k)! : ℕ) : 𝕂) = (n ! : 𝕂) := by
      exact_mod_cast congrArg (Nat.cast (R := 𝕂)) (Nat.choose_mul_factorial_mul_factorial hkn)
    have hfk : (k ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hfnk : (((n - k)! : ℕ) : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
    simp only [kummerCoefficient]
    field_simp
    linear_combination (-(ascPochhammer 𝕂 k).eval (b - a)
      * ((ascPochhammer 𝕂 k).eval b)⁻¹) * hcf
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum,
    sum_neg_one_pow_choose_ascPochhammer n a b hb]
  simp only [kummerCoefficient]
  ring

end ChuVandermonde

section Transform

variable {𝕂 : Type*} [RCLike 𝕂] (a b : 𝕂)

/-- **Kummer's transformation** (DLMF 13.2.39):
`M(a;b;z) = eᶻ · M(b−a;b;−z)`, for `b` off the nonpositive integers.

DAG: E-13.2.39.
Numerical: PASS
Verified: unverified
-/
theorem kummerM_kummer_transform (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) (z : 𝕂) :
    ₁F₁ a b z = NormedSpace.exp z * ₁F₁ (b - a) b (-z) := by
  -- absolute summability of both factor series
  have hkum_norm : Summable fun n : ℕ => ‖kummerCoefficient (b - a) b n * (-z) ^ n‖ := by
    have h := (kummerSeries 𝕂 (b - a) b).summable_norm_apply (x := -z)
      (by rw [kummerSeries_radius_eq_top]; simp)
    refine h.congr fun n => ?_
    rw [kummerSeries_apply_eq, smul_eq_mul]
  have hexp_norm : Summable fun n : ℕ => ‖z ^ n / (n ! : 𝕂)‖ := by
    refine (Real.summable_pow_div_factorial ‖z‖).congr fun n => ?_
    rw [norm_div, norm_pow, RCLike.norm_natCast]
  -- the Cauchy product
  have hC := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hkum_norm hexp_norm
  -- identify the three series
  have hM1 : ∑' n : ℕ, kummerCoefficient (b - a) b n * (-z) ^ n = ₁F₁ (b - a) b (-z) :=
    (kummerM_hasSum (b - a) b (-z)).tsum_eq
  have hexp : ∑' n : ℕ, z ^ n / (n ! : 𝕂) = NormedSpace.exp z := by
    rw [NormedSpace.exp_eq_tsum_div]
  -- the diagonal sums collapse by Chu–Vandermonde
  have hdiag : ∀ n : ℕ, ∑ kl ∈ antidiagonal n,
      (kummerCoefficient (b - a) b kl.1 * (-z) ^ kl.1) * (z ^ kl.2 / (kl.2)!)
      = kummerCoefficient a b n * z ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm : ∀ k ∈ range (n + 1),
        (kummerCoefficient (b - a) b k * (-z) ^ k) * (z ^ (n - k) / ((n - k)! : 𝕂))
        = ((-1) ^ k * kummerCoefficient (b - a) b k / ((n - k)! : 𝕂)) * z ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [neg_pow, show z ^ n = z ^ k * z ^ (n - k) by
        rw [← pow_add, Nat.add_sub_cancel' hkn]]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      kummerCoefficient_eq_sum_div_factorial a b hb n]
  -- assemble
  calc ₁F₁ a b z = ∑' n : ℕ, kummerCoefficient a b n * z ^ n :=
        (kummerM_hasSum a b z).tsum_eq.symm
    _ = ∑' n : ℕ, ∑ kl ∈ antidiagonal n,
        (kummerCoefficient (b - a) b kl.1 * (-z) ^ kl.1) * (z ^ kl.2 / (kl.2)!) :=
        (tsum_congr hdiag).symm
    _ = (∑' n : ℕ, kummerCoefficient (b - a) b n * (-z) ^ n)
        * ∑' n : ℕ, z ^ n / (n ! : 𝕂) := hC.symm
    _ = NormedSpace.exp z * ₁F₁ (b - a) b (-z) := by
        rw [hM1, hexp, mul_comm]

end Transform

end FLMF.Hypergeometric
