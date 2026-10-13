import FLMF.Frameworks.Hypergeometric.KummerODE
import FLMF.Frameworks.Hypergeometric.KummerTransform
import FLMF.Functions.IncompleteGamma.Def
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The lower incomplete gamma function as a `₁F₁` instance (bridge — DLMF 8.5.1)

* `lowerGamma_eq_kummerM` — `γ(a,x) = a⁻¹ xᵃ M(a; a+1; −x)` for `0 < a`,
  `0 ≤ x` (DLMF 8.5.1).

The proof expands `e^{−t}` in `γ(a,x) = ∫₀ˣ e^{−t} t^{a−1} dt` into its
exponential series, interchanges sum and integral (the norm-integrals are
dominated by `xᵃ/a · xⁿ/n!`), integrates `t^{a+n−1}` termwise, and matches the
resulting series against the Kummer series through the coefficient identity
`cₙ(a, a+1) = a/((a+n)·n!)`.
-/

noncomputable section

open Nat MeasureTheory Real Set FLMF.Hypergeometric

namespace FLMF.IncompleteGamma

/-- A positive parameter is off the nonpositive integers (the hypothesis of
the framework coefficient collapse `kummerCoefficient_self_succ`). -/
-- no-dlmf: parameter-positivity helper, no DLMF counterpart
theorem param_ne_of_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : (k : ℝ) ≠ -a := by
  intro hk
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  rw [hk] at hk0
  linarith

/-- The termwise integral: `∫₀ˣ t^(a+n−1) dt = x^(a+n)/(a+n)` for `0 < a`,
`0 ≤ x`. -/
-- no-dlmf: termwise-integration helper for the series interchange, no DLMF counterpart
theorem integral_Ioc_rpow_add_nat {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∫ t in Ioc (0 : ℝ) x, t ^ (a + n - 1) = x ^ (a + n) / (a + n) := by
  have han : (0 : ℝ) < a + n := by positivity
  have h := integral_rpow (a := (0 : ℝ)) (b := x) (r := a + n - 1) (Or.inl (by linarith))
  rw [intervalIntegral.integral_of_le hx] at h
  rw [h, show a + (n : ℝ) - 1 + 1 = a + n by ring, Real.zero_rpow han.ne', sub_zero]

/-- **DLMF 8.5.1**: `γ(a,x) = a⁻¹ xᵃ e^{−x} M(1; a+1; x) = a⁻¹ xᵃ M(a; a+1; −x)`,
for `0 < a` and `0 ≤ x` (the full two-link chain DLMF gives).

DAG: E-8.5.1.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem lowerGamma_eq_kummerM {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    lowerGamma a x = a⁻¹ * x ^ a * Real.exp (-x) * ₁F₁ (1 : ℝ) (a + 1) x ∧
    a⁻¹ * x ^ a * Real.exp (-x) * ₁F₁ (1 : ℝ) (a + 1) x = a⁻¹ * x ^ a * ₁F₁ a (a + 1) (-x) := by
  have hheavy : lowerGamma a x = a⁻¹ * x ^ a * ₁F₁ a (a + 1) (-x) := by
    rcases hx.eq_or_lt with rfl | hx0
    · simp [Real.zero_rpow ha.ne']
    -- the termwise integrands
    set F : ℕ → ℝ → ℝ := fun n t => (-1) ^ n / n ! * t ^ (a + n - 1) with hF
    have hFint : ∀ n : ℕ, IntegrableOn (F n) (Ioc (0 : ℝ) x) := by
      intro n
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := x)
        (r := a + n - 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]))
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h).const_mul _
    -- the norm-integrals are summable
    have hFsum : Summable fun n : ℕ => ∫ t in Ioc (0 : ℝ) x, ‖F n t‖ := by
      have hle : ∀ n : ℕ, ∫ t in Ioc (0 : ℝ) x, ‖F n t‖ ≤ x ^ a / a * (x ^ n / n !) := by
        intro n
        have hval : ∫ t in Ioc (0 : ℝ) x, ‖F n t‖
            = 1 / n ! * (x ^ (a + n) / (a + n)) := by
          have heq : ∀ t ∈ Ioc (0 : ℝ) x, ‖F n t‖ = 1 / n ! * t ^ (a + n - 1) := by
            intro t ht
            have htpos : 0 < t := ht.1
            rw [hF]
            rw [norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
              abs_of_nonneg (Real.rpow_nonneg htpos.le _), Nat.abs_cast]
          rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_const_mul,
            integral_Ioc_rpow_add_nat ha hx0.le n]
        rw [hval, Real.rpow_add hx0, Real.rpow_natCast]
        have han : a ≤ a + n := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have h1 : x ^ a * x ^ n / (a + n) ≤ x ^ a * x ^ n / a :=
          div_le_div_of_nonneg_left (by positivity) ha (by linarith)
        calc 1 / n ! * (x ^ a * x ^ n / (a + n))
            ≤ 1 / n ! * (x ^ a * x ^ n / a) := by
              apply mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = x ^ a / a * (x ^ n / n !) := by ring
      refine Summable.of_nonneg_of_le (fun n => ?_) hle
        ((Real.summable_pow_div_factorial x).mul_left _)
      exact integral_nonneg fun t => norm_nonneg _
    -- interchange sum and integral
    have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
    -- the integrand is the sum of its series on `Ioc 0 x`
    have hpt : ∀ t ∈ Ioc (0 : ℝ) x, Real.exp (-t) * t ^ (a - 1) = ∑' n : ℕ, F n t := by
      intro t ht
      have htpos : 0 < t := ht.1
      have hexp : Real.exp (-t) = ∑' n : ℕ, (-t) ^ n / n ! := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      rw [hexp, ← tsum_mul_right]
      refine tsum_congr fun n => ?_
      have ht1 : t ^ (a + n - 1) = t ^ n * t ^ (a - 1) := by
        rw [← Real.rpow_natCast t n, ← Real.rpow_add htpos,
          show (n : ℝ) + (a - 1) = a + n - 1 by ring]
      simp only [hF]
      rw [ht1, neg_pow]
      ring
    -- compute `γ(a,x)` as the integrated series
    have hγ : lowerGamma a x = ∑' n : ℕ, (-1) ^ n / n ! * (x ^ (a + n) / (a + n)) := by
      rw [lowerGamma, setIntegral_congr_fun measurableSet_Ioc hpt, ← hswap]
      refine tsum_congr fun n => ?_
      rw [hF, integral_const_mul, integral_Ioc_rpow_add_nat ha hx0.le n]
    -- the Kummer series, rescaled
    have hM := (kummerM_hasSum a (a + 1) (-x)).mul_left (a⁻¹ * x ^ a)
    have hterm : (fun n : ℕ => a⁻¹ * x ^ a * (kummerCoefficient a (a + 1) n * (-x) ^ n)) =
        fun n : ℕ => (-1) ^ n / n ! * (x ^ (a + n) / (a + n)) := by
      funext n
      rw [kummerCoefficient_self_succ a n (param_ne_of_pos ha), Real.rpow_add hx0, neg_pow,
        ← Real.rpow_natCast x n]
      have han : a + (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hterm] at hM
    rw [hγ, hM.tsum_eq]
  -- the second link: Kummer's transformation (DLMF 13.2.39) relates the two `₁F₁` forms
  -- directly, independent of the series computation above
  have hb : ∀ k : ℕ, (k : ℝ) ≠ -(a + 1) := fun k hk => by
    have hk0 := Nat.cast_nonneg (α := ℝ) k; rw [hk] at hk0; linarith
  have ht := kummerM_kummer_transform a (a + 1) hb (-x)
  rw [show (a + 1) - a = (1 : ℝ) by ring, neg_neg] at ht
  have hlink2 : a⁻¹ * x ^ a * Real.exp (-x) * ₁F₁ (1 : ℝ) (a + 1) x
      = a⁻¹ * x ^ a * ₁F₁ a (a + 1) (-x) := by
    rw [ht, Real.exp_eq_exp_ℝ]; ring
  exact ⟨hheavy.trans hlink2.symm, hlink2⟩

/-! ## Remaining members of the DLMF 8.5.1 chain

  DLMF 8.5.1 is the equality chain
  `γ(a,z) = a⁻¹ zᵃ e^{−z} M(1, 1+a, z) = a⁻¹ zᵃ M(a, 1+a, −z)`.
  The `M(a, 1+a, −z)` member is `lowerGamma_eq_kummerM`; the theorem below
  surfaces the remaining `e^{−z} M(1, 1+a, z)` member, obtained from it by
  Kummer's transformation (DLMF 13.2.39).
-/

-- no-dlmf: chain link 8.5.1 (assembled in lowerGamma_eq_kummerM)
/-- `γ(a,x) = a⁻¹ xᵃ e^{−x} M(1; a+1; x)`, for `0 < a` and `0 ≤ x` — the
Kummer-transform image of `lowerGamma_eq_kummerM`'s first conjunct. -/
theorem lowerGamma_eq_kummerM_exp {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    lowerGamma a x = a⁻¹ * x ^ a * Real.exp (-x) * ₁F₁ (1 : ℝ) (a + 1) x :=
  (lowerGamma_eq_kummerM ha hx).1

end FLMF.IncompleteGamma
