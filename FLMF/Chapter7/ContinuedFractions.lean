import FLMF.Chapter7.Erf
import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.Faddeeva
import FLMF.Support.ContinuedFraction
import FLMF.Support.VanVleck
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

/-!
# Continued-fraction expansions for `erfc` (DLMF §7.9)

Statement surfaces for the Laplace continued-fraction expansions of the
complementary error function (DLMF §7.9).

DLMF §7.9 records three continued fractions:

* **7.9.1** `√π e^{z²} erfc(z) = z / (z² + ½ / (1 + 1 / (z² + 3/2 / (1 + ⋯))))`,
* **7.9.2** `√π e^{z²} erfc(z) = 2z / (2z² + 1 − 1·2 / (2z² + 5 − 3·4 / (2z² + 9 − ⋯)))`,
  the *even part* of (7.9.1), and
* **7.9.3** a continued fraction for the Faddeeva function `w(z)`.

A continued fraction is faithfully stated as the **limit of its convergents**:
we build the partial numerators/denominators `A n`, `B n` of the truncated
fraction via the standard Wallis (fundamental) recurrence and state that the
convergents `A n / B n` tend to the function value as `n → ∞`.

For each of 7.9.1/7.9.2 we surface two theorems:

* `erf_7_9_1`/`erf_7_9_2`: the REAL-argument specialization (`x > 0`), proven
  in full via the real Gaussian-tail-integral (`erfJ`) route — this is exactly
  the `z ∈ (0,∞)` slice of the DLMF identities (valid on `ℜ z > 0`);
* `erf_7_9_1_complex`/`erf_7_9_2_complex`: the DLMF-faithful full-strength
  statement for complex `z` with `ℜ z > 0`, using the complex `cerfc` of
  `FLMF.Functions.Error.ComplexErf`.  The real proof's tail-positivity
  argument does not transfer to the complex domain; instead these are proven
  from the complex tail integrals `Kₙ(z) = ∫₀^∞ sⁿ e^{-s²-2zs} ds` (whose
  `n = 0` value is the Laplace-transform representation DLMF 7.7.3 of `erfc`),
  which give the *exact remainder* of the fraction, combined with Van Vleck's
  sector convergence theorem (`FLMF.Methods.VanVleck`, DLMF 1.12.28) applied to
  the `aₙ ↦ 1` normalization of the fraction.  See the section "The complex
  tail integrals of the DLMF 7.9.1 fraction" below.

7.9.3 is the Faddeeva function `w(z)`, which is complex-valued and not provided
by FLMF; it is recorded as a documented deferral below.
-/

namespace FLMF.Error

open Real Filter Topology MeasureTheory Set
open scoped Real

/-- Wallis (fundamental) recurrence assembling the convergents of a continued
fraction `b 0 + a 1 / (b 1 + a 2 / (b 2 + ⋯))`.  Given partial numerators `a`
and denominators `b`, `cfNum a b n` / `cfDen a b n` is the `n`-th convergent.

`cfNum`/`cfDen` are the classical `Aₙ = bₙ Aₙ₋₁ + aₙ Aₙ₋₂`,
`Bₙ = bₙ Bₙ₋₁ + aₙ Bₙ₋₂` with `A₋₁ = 1, A₀ = b₀, B₋₁ = 0, B₀ = 1` (here indexed
from `0` with the `−1` seeds folded in). -/
noncomputable def cfNum (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | 1 => b 1 * b 0 + a 1
  | (n + 2) => b (n + 2) * cfNum a b (n + 1) + a (n + 2) * cfNum a b n

/-- Partial denominators of the Wallis recurrence; see `cfNum`. -/
noncomputable def cfDen (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => b 1
  | (n + 2) => b (n + 2) * cfDen a b (n + 1) + a (n + 2) * cfDen a b n

/-- The `n`-th convergent `Aₙ / Bₙ` of the continued fraction with partial
numerators `a` and denominators `b`. -/
noncomputable def cfConv (a b : ℕ → ℝ) (n : ℕ) : ℝ := cfNum a b n / cfDen a b n

/-- Complex analog of `cfNum`, for stating the DLMF-faithful (`z ∈ ℂ`) surfaces
`erf_7_9_1_complex`/`erf_7_9_2_complex`. -/
noncomputable def cfNumC (a b : ℕ → ℂ) : ℕ → ℂ
  | 0 => b 0
  | 1 => b 1 * b 0 + a 1
  | (n + 2) => b (n + 2) * cfNumC a b (n + 1) + a (n + 2) * cfNumC a b n

/-- Complex analog of `cfDen`; see `cfNumC`. -/
noncomputable def cfDenC (a b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => b 1
  | (n + 2) => b (n + 2) * cfDenC a b (n + 1) + a (n + 2) * cfDenC a b n

/-- Complex analog of `cfConv`; see `cfNumC`. -/
noncomputable def cfConvC (a b : ℕ → ℂ) (n : ℕ) : ℂ := cfNumC a b n / cfDenC a b n

-- no-dlmf: support def for the 7.9.1 continued-fraction display; surfaced at `erf_7_9_1_complex`
/-- Iterated Gaussian tail integrals `Jₙ(x) = ∫_{t>x} (t-x)^n e^{-t²} dt` (the kernel of the
exact tails of the DLMF 7.9.1 Laplace fraction; `J₀ = (√π/2)·erfc`).

-/
private noncomputable def erfJ (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Set.Ioi x, (t - x) ^ n * Real.exp (-t ^ 2)

/-- The `erfJ` integrand is integrable on `(x, ∞)` for `x ≥ 0` (dominated by `t^n e^{-t²}`). -/
private lemma erfJ_integrableOn (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t - x) ^ n * Real.exp (-t ^ 2)) (Set.Ioi x) := by
  have hs : (-1:ℝ) < (n:ℝ) := lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg n)
  have hdom : IntegrableOn (fun t : ℝ => t ^ ((n:ℝ)) * Real.exp (-1 * t ^ 2)) (Set.Ioi x) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs).mono_set (Set.Ioi_subset_Ioi hx)
  refine hdom.mono' ?_ ?_
  · exact (((continuous_id.sub continuous_const).pow n).mul
      (Real.continuous_exp.comp (continuous_pow 2).neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h1 : x < t := ht
    have h0 : (0:ℝ) ≤ t - x := by linarith
    have hpow : (t - x) ^ n ≤ t ^ n := by gcongr <;> linarith
    have htr : t ^ ((n:ℝ)) = t ^ n := Real.rpow_natCast t n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg h0 n) (Real.exp_pos _).le),
      htr, neg_one_mul]
    exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

/-- `Jₙ(x) > 0`: the integrand is strictly positive on the infinite-volume set `(x, ∞)`. -/
private lemma erfJ_pos (x : ℝ) (hx : 0 < x) (n : ℕ) : 0 < erfJ x n := by
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi x)]
      fun t : ℝ => (t - x) ^ n * Real.exp (-t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h0 : (0:ℝ) ≤ t - x := by
      have : x < t := ht
      linarith
    exact mul_nonneg (pow_nonneg h0 n) (Real.exp_pos _).le
  rw [erfJ, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae (erfJ_integrableOn x hx.le n)]
  have hsub : Set.Ioi x ⊆ Function.support fun t : ℝ => (t - x) ^ n * Real.exp (-t ^ 2) := by
    intro t ht
    have h0 : 0 < t - x := sub_pos.mpr ht
    exact (mul_pos (pow_pos h0 n) (Real.exp_pos _)).ne'
  rw [Set.inter_eq_self_of_subset_right hsub, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- Derivative of `(t-x)^{n+1} e^{-t²}`, arranged as the integrand combination used in the
integration-by-parts recurrence for `erfJ`. -/
private lemma erfJ_hasDerivAt (x : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t - x) ^ (n + 1) * Real.exp (-t ^ 2))
      (((n : ℝ) + 1) * ((t - x) ^ n * Real.exp (-t ^ 2))
        - 2 * ((t - x) ^ (n + 2) * Real.exp (-t ^ 2))
        - 2 * x * ((t - x) ^ (n + 1) * Real.exp (-t ^ 2))) t := by
  have h1 := ((hasDerivAt_id t).sub_const x).pow (n + 1)
  have hp : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).neg
  have h3 := h1.mul hp.exp
  simp only [Nat.add_sub_cancel] at h3
  convert h3 using 1
  simp only [Pi.pow_apply, id_eq]
  push_cast
  ring

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- Integration-by-parts recurrence `(n+1) Jₙ = 2x Jₙ₊₁ + 2 Jₙ₊₂` (the three-term recurrence
of the repeated integrals of `erfc`, DLMF 7.18.12 in `erfJ` normalization). -/
private lemma erfJ_rec (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((n : ℝ) + 1) * erfJ x n = 2 * x * erfJ x (n + 1) + 2 * erfJ x (n + 2) := by
  have hint0 := erfJ_integrableOn x hx n
  have hint1 := erfJ_integrableOn x hx (n + 1)
  have hint2 := erfJ_integrableOn x hx (n + 2)
  have hi0 : IntegrableOn (fun t : ℝ =>
      ((n : ℝ) + 1) * ((t - x) ^ n * Real.exp (-t ^ 2))) (Set.Ioi x) := hint0.const_mul _
  have hi22 : IntegrableOn (fun t : ℝ =>
      2 * ((t - x) ^ (n + 2) * Real.exp (-t ^ 2))) (Set.Ioi x) := hint2.const_mul _
  have hi1 : IntegrableOn (fun t : ℝ =>
      ((n : ℝ) + 1) * ((t - x) ^ n * Real.exp (-t ^ 2))
        - 2 * ((t - x) ^ (n + 2) * Real.exp (-t ^ 2))) (Set.Ioi x) := hi0.sub hi22
  have hi2 : IntegrableOn (fun t : ℝ =>
      2 * x * ((t - x) ^ (n + 1) * Real.exp (-t ^ 2))) (Set.Ioi x) := hint1.const_mul _
  have hφint : IntegrableOn (fun t : ℝ =>
      ((n : ℝ) + 1) * ((t - x) ^ n * Real.exp (-t ^ 2))
        - 2 * ((t - x) ^ (n + 2) * Real.exp (-t ^ 2))
        - 2 * x * ((t - x) ^ (n + 1) * Real.exp (-t ^ 2))) (Set.Ioi x) := hi1.sub hi2
  have hcont : ContinuousWithinAt (fun t : ℝ => (t - x) ^ (n + 1) * Real.exp (-t ^ 2))
      (Set.Ici x) x :=
    (((continuous_id.sub continuous_const).pow (n + 1)).mul
      (Real.continuous_exp.comp (continuous_pow 2).neg)).continuousWithinAt
  have htend : Tendsto (fun t : ℝ => (t - x) ^ (n + 1) * Real.exp (-t ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tendsto_pow_mul_exp_neg_atTop_nhds_zero (n + 1))
    · filter_upwards [Filter.eventually_ge_atTop x] with t ht
      have h0 : (0:ℝ) ≤ t - x := by linarith
      exact mul_nonneg (pow_nonneg h0 _) (Real.exp_pos _).le
    · filter_upwards [Filter.eventually_ge_atTop (max x 1)] with t ht
      have hxt : x ≤ t := le_trans (le_max_left _ _) ht
      have h1t : (1:ℝ) ≤ t := le_trans (le_max_right _ _) ht
      have hpow : (t - x) ^ (n + 1) ≤ t ^ (n + 1) := by gcongr <;> linarith
      have hexp : Real.exp (-t ^ 2) ≤ Real.exp (-t) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc (t - x) ^ (n + 1) * Real.exp (-t ^ 2)
          ≤ t ^ (n + 1) * Real.exp (-t ^ 2) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ ≤ t ^ (n + 1) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t _ => erfJ_hasDerivAt x n t) hφint htend
  have hzero : (∫ t in Set.Ioi x,
      (((n : ℝ) + 1) * ((t - x) ^ n * Real.exp (-t ^ 2))
        - 2 * ((t - x) ^ (n + 2) * Real.exp (-t ^ 2))
        - 2 * x * ((t - x) ^ (n + 1) * Real.exp (-t ^ 2)))) = 0 := by
    rw [hFTC]
    simp
  rw [MeasureTheory.integral_sub hi1 hi2, MeasureTheory.integral_sub hi0 hi22,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul] at hzero
  unfold erfJ
  linarith [hzero]

/-- Base identity `2x J₀ + 2 J₁ = e^{-x²}` (from `∫_{t>x} 2t e^{-t²} dt = e^{-x²}`). -/
private lemma erfJ_baseId (x : ℝ) (hx : 0 < x) :
    2 * x * erfJ x 0 + 2 * erfJ x 1 = Real.exp (-x ^ 2) := by
  have hint0 := erfJ_integrableOn x hx.le 0
  have hint1 := erfJ_integrableOn x hx.le 1
  have hi0 : IntegrableOn (fun t : ℝ =>
      2 * x * ((t - x) ^ 0 * Real.exp (-t ^ 2))) (Set.Ioi x) := hint0.const_mul _
  have hi1 : IntegrableOn (fun t : ℝ =>
      2 * ((t - x) ^ 1 * Real.exp (-t ^ 2))) (Set.Ioi x) := hint1.const_mul _
  have hφint : IntegrableOn (fun t : ℝ =>
      2 * x * ((t - x) ^ 0 * Real.exp (-t ^ 2)) + 2 * ((t - x) ^ 1 * Real.exp (-t ^ 2)))
      (Set.Ioi x) := hi0.add hi1
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -Real.exp (-t ^ 2))
      (2 * x * ((t - x) ^ 0 * Real.exp (-t ^ 2)) + 2 * ((t - x) ^ 1 * Real.exp (-t ^ 2))) t := by
    intro t
    have hp : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).neg
    have h2 := hp.exp.neg
    convert h2 using 1
    ring
  have hcont : ContinuousWithinAt (fun t : ℝ => -Real.exp (-t ^ 2)) (Set.Ici x) x :=
    ((Real.continuous_exp.comp (continuous_pow 2).neg).neg).continuousWithinAt
  have htend : Tendsto (fun t : ℝ => -Real.exp (-t ^ 2)) atTop (𝓝 0) := by
    rw [← neg_zero]
    apply Filter.Tendsto.neg
    have h2 : Tendsto (fun t : ℝ => -t ^ 2) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
    exact Real.tendsto_exp_atBot.comp h2
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t _ => hderiv t) hφint htend
  have hval : (∫ t in Set.Ioi x,
      (2 * x * ((t - x) ^ 0 * Real.exp (-t ^ 2)) + 2 * ((t - x) ^ 1 * Real.exp (-t ^ 2))))
      = Real.exp (-x ^ 2) := by
    rw [hFTC]
    simp
  rw [MeasureTheory.integral_add hi0 hi1,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hval
  unfold erfJ
  linarith [hval]

/-- Bridge to the tail Gaussian integral: `erfc x = (2/√π) J₀(x)` for `x > 0`. -/
private lemma erfc_eq_erfJ (x : ℝ) (hx : 0 < x) :
    erfc x = 2 / Real.sqrt Real.pi * erfJ x 0 := by
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
  have hdisj : Disjoint (Set.Ioc (0:ℝ) x) (Set.Ioi x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have hunion : (∫ t in Set.Ioc 0 x, Real.exp (-t ^ 2)) + ∫ t in Set.Ioi x, Real.exp (-t ^ 2)
      = ∫ t in Set.Ioi (0:ℝ), Real.exp (-t ^ 2) := by
    rw [← MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hx.le]
  have hJ0 : erfJ x 0 = ∫ t in Set.Ioi x, Real.exp (-t ^ 2) := by
    unfold erfJ
    simp
  have hIoc : (∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)) = ∫ t in Set.Ioc 0 x, Real.exp (-t ^ 2) :=
    intervalIntegral.integral_of_le hx.le
  have hgauss := integral_Ioi_gaussian
  have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [erfc, erf, hJ0, hIoc]
  field_simp
  linarith [hunion, hgauss]

-- no-dlmf: support def for the 7.9.1 continued-fraction display; surfaced at `erf_7_9_1_complex`
/-- Partial numerators of the DLMF 7.9.1 fraction (exactly the `a`-sequence of `erf_7_9_1`).

-/
private noncomputable def cfA (x : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else if k = 1 then x else ((k : ℝ) - 1) / 2

-- no-dlmf: support def for the 7.9.1 continued-fraction display; surfaced at `erf_7_9_1_complex`
/-- Partial denominators of the DLMF 7.9.1 fraction (exactly the `b`-sequence of `erf_7_9_1`).

-/
private noncomputable def cfB (x : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else if k % 2 = 1 then x ^ 2 else 1

-- no-dlmf: support def for the 7.9.1 continued-fraction display; surfaced at `erf_7_9_1_complex`
/-- The DLMF 7.9.1 continued fraction packaged as a (non-terminating) `GenContFract`, so the
method kit of `FLMF.Methods.ContinuedFraction` applies.

-/
private noncomputable def erfCF (x : ℝ) : GenContFract ℝ :=
  ⟨cfB x 0, ⟨fun n => some ⟨cfA x (n + 1), cfB x (n + 1)⟩, fun {n} h => by simp at h⟩⟩

/-- The `n`-th partial pair of `erfCF` is `⟨a (n+1), b (n+1)⟩`. -/
private lemma erfCF_s_get? (x : ℝ) (n : ℕ) :
    (erfCF x).s.get? n = some ⟨cfA x (n + 1), cfB x (n + 1)⟩ := rfl

/-- Positivity of the partial numerators (`k ≥ 1`) for `x > 0`. -/
private lemma cfA_pos (x : ℝ) (hx : 0 < x) (k : ℕ) (hk : k ≠ 0) : 0 < cfA x k := by
  unfold cfA
  rcases eq_or_ne k 1 with rfl | h1
  · simpa using hx
  · have hk2 : 2 ≤ k := by omega
    rw [if_neg hk, if_neg h1]
    have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    linarith

/-- Positivity of the partial denominators (`k ≥ 1`) for `x > 0`. -/
private lemma cfB_pos (x : ℝ) (hx : 0 < x) (k : ℕ) (hk : k ≠ 0) : 0 < cfB x k := by
  unfold cfB
  rw [if_neg hk]
  split_ifs
  · positivity
  · norm_num

/-- Value of the partial numerators for `k ≥ 2`: `a k = (k-1)/2`. -/
private lemma cfA_val (x : ℝ) {k : ℕ} (hk : 2 ≤ k) : cfA x k = ((k : ℝ) - 1) / 2 := by
  unfold cfA
  rw [if_neg (by omega), if_neg (by omega)]

/-- Consecutive partial denominators multiply to `x²` (`{x², 1}` alternate), the cross term
driving the two-step gap estimate. -/
private lemma cfB_mul_succ (x : ℝ) (hx : 0 < x) (k : ℕ) (hk : k ≠ 0) :
    cfB x k * cfB x (k + 1) = x ^ 2 := by
  unfold cfB
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [if_neg hk, if_neg (by omega : ¬ k % 2 = 1),
      if_neg (by omega : ¬ k + 1 = 0), if_pos (by omega : (k + 1) % 2 = 1), one_mul]
  · rw [if_neg hk, if_pos (by omega : k % 2 = 1),
      if_neg (by omega : ¬ k + 1 = 0), if_neg (by omega : ¬ (k + 1) % 2 = 1), mul_one]

/-- The `GenContFract` numerator continuants agree with the file's Wallis `cfNum`. -/
private lemma erfCF_num (x : ℝ) : ∀ n, (erfCF x).nums n = cfNum (cfA x) (cfB x) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_num_eq_h]
    rfl
  | one =>
    rw [GenContFract.first_num_eq (erfCF_s_get? x 0)]
    rfl
  | more n ih ih1 =>
    have h := GenContFract.nums_recurrence (erfCF_s_get? x (n + 1)) ih ih1
    simpa [cfNum] using h

/-- The `GenContFract` denominator continuants agree with the file's Wallis `cfDen`. -/
private lemma erfCF_den (x : ℝ) : ∀ n, (erfCF x).dens n = cfDen (cfA x) (cfB x) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_den_eq_one]
    rfl
  | one =>
    rw [GenContFract.first_den_eq (erfCF_s_get? x 0)]
    rfl
  | more n ih ih1 =>
    have h := GenContFract.dens_recurrence (erfCF_s_get? x (n + 1)) ih ih1
    simpa [cfDen] using h

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- `cfConv` of the DLMF 7.9.1 sequences equals the `GenContFract` convergents of `erfCF`. -/
private lemma erfCF_conv (x : ℝ) (n : ℕ) :
    cfConv (cfA x) (cfB x) n = (erfCF x).convs n := by
  rw [cfConv, GenContFract.conv_eq_num_div_den, erfCF_num, erfCF_den]

/-- `erfCF x` is a positive (Stieltjes-type) fraction for `x > 0`. -/
private lemma erfCF_pos (x : ℝ) (hx : 0 < x) :
    ∀ n gp, (erfCF x).s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b := by
  intro n gp h
  rw [erfCF_s_get?, Option.some.injEq] at h
  subst h
  exact ⟨cfA_pos x hx (n + 1) (by omega), cfB_pos x hx (n + 1) (by omega)⟩

-- no-dlmf: support def for the 7.9.1 continued-fraction display; surfaced at `erf_7_9_1_complex`
/-- Exact tails of the DLMF 7.9.1 fraction: `t 0 = √π e^{x²} erfc x` (the value), and for
`n ≥ 1` the `erfJ` ratios `x·Jₙ/Jₙ₋₁` (odd `n`) resp. `Jₙ/(x·Jₙ₋₁)` (even `n`).

-/
private noncomputable def erfTail (x : ℝ) : ℕ → ℝ := fun n =>
  if n = 0 then Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x
  else if n % 2 = 1 then x * erfJ x n / erfJ x (n - 1)
  else erfJ x n / (x * erfJ x (n - 1))

/-- All exact tails are positive for `x > 0`. -/
private lemma erfTail_pos (x : ℝ) (hx : 0 < x) (n : ℕ) : 0 < erfTail x n := by
  unfold erfTail
  split_ifs with h0 h1
  · rw [erfc_eq_erfJ x hx]
    have hJ := erfJ_pos x hx 0
    have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    exact mul_pos (mul_pos hπ (Real.exp_pos _)) (mul_pos (by positivity) hJ)
  · exact div_pos (mul_pos hx (erfJ_pos x hx n)) (erfJ_pos x hx (n - 1))
  · exact div_pos (erfJ_pos x hx n) (mul_pos hx (erfJ_pos x hx (n - 1)))

/-- The exact-tail backwards recurrence `t n = aₙ₊₁/(bₙ₊₁ + t (n+1))`: the base case is
`2xJ₀+2J₁ = e^{-x²}` with the `erfc` bridge, and both parity cases reduce to the
integration-by-parts recurrence `(m+1)Jₘ = 2xJₘ₊₁+2Jₘ₊₂`. -/
private lemma erfTail_rec (x : ℝ) (hx : 0 < x) (n : ℕ) :
    erfTail x n = cfA x (n + 1) / (cfB x (n + 1) + erfTail x (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb := erfJ_baseId x hx
    have hJ0 := erfJ_pos x hx 0
    have hJ1 := erfJ_pos x hx 1
    have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hexp : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h0 : erfTail x 0 = Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x := by
      unfold erfTail; simp
    have h1 : erfTail x 1 = x * erfJ x 1 / erfJ x 0 := by
      unfold erfTail; norm_num
    have ha : cfA x 1 = x := by unfold cfA; norm_num
    have hbb : cfB x 1 = x ^ 2 := by unfold cfB; norm_num
    have hJ0' : erfJ x 0 ≠ 0 := hJ0.ne'
    have hπ' : Real.sqrt Real.pi ≠ 0 := hπ.ne'
    have hx' : x ≠ 0 := hx.ne'
    have hE' : Real.exp (x ^ 2) ≠ 0 := (Real.exp_pos _).ne'
    rw [h0, h1, ha, hbb, erfc_eq_erfJ x hx]
    have hden : x ^ 2 + x * erfJ x 1 / erfJ x 0 = x * Real.exp (-x ^ 2) / (2 * erfJ x 0) := by
      rw [eq_div_iff (mul_pos two_pos hJ0).ne']
      field_simp
      linear_combination hb
    rw [hden, Real.exp_neg]
    field_simp
    try ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hrec := erfJ_rec x hx.le m
    have hJm := erfJ_pos x hx m
    have hJm1 := erfJ_pos x hx (m + 1)
    have hJm2 := erfJ_pos x hx (m + 2)
    have hJm' : erfJ x m ≠ 0 := hJm.ne'
    have hJm1' : erfJ x (m + 1) ≠ 0 := hJm1.ne'
    have hJm2' : erfJ x (m + 2) ≠ 0 := hJm2.ne'
    have hx' : x ≠ 0 := hx.ne'
    have ha : cfA x (m + 2) = ((m:ℝ) + 1) / 2 := by
      rw [cfA_val x (by omega)]; push_cast; ring
    rcases Nat.even_or_odd (m + 1) with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n = m+1 even, so n+1 = m+2 odd: cfB = x²
      have ht1 : erfTail x (m + 1) = erfJ x (m + 1) / (x * erfJ x m) := by
        unfold erfTail
        rw [if_neg (by omega), if_neg (by omega : ¬ (m + 1) % 2 = 1)]
        norm_num
      have ht2 : erfTail x (m + 2) = x * erfJ x (m + 2) / erfJ x (m + 1) := by
        unfold erfTail
        rw [if_neg (by omega), if_pos (by omega : (m + 2) % 2 = 1)]
        norm_num
      have hbval : cfB x (m + 2) = x ^ 2 := by
        unfold cfB
        rw [if_neg (by omega), if_pos (by omega : (m + 2) % 2 = 1)]
      rw [ht1, ht2, ha, hbval]
      field_simp
      linear_combination -hrec
    · -- n = m+1 odd, so n+1 = m+2 even: cfB = 1
      have ht1 : erfTail x (m + 1) = x * erfJ x (m + 1) / erfJ x m := by
        unfold erfTail
        rw [if_neg (by omega), if_pos (by omega : (m + 1) % 2 = 1)]
        norm_num
      have ht2 : erfTail x (m + 2) = erfJ x (m + 2) / (x * erfJ x (m + 1)) := by
        unfold erfTail
        rw [if_neg (by omega), if_neg (by omega : ¬ (m + 2) % 2 = 1)]
        norm_num
      have hbval : cfB x (m + 2) = 1 := by
        unfold cfB
        rw [if_neg (by omega), if_neg (by omega : ¬ (m + 2) % 2 = 1)]
      rw [ht1, ht2, ha, hbval]
      field_simp
      linear_combination -hrec

/-- Continuant denominators of `erfCF` are positive. -/
private lemma erfCF_dens_pos (x : ℝ) (hx : 0 < x) (n : ℕ) : 0 < (erfCF x).dens n :=
  FLMF.Methods.dens_pos (erfCF_pos x hx) n

/-- The `i`-th partial numerator of `erfCF` (with default `0`) is `a (i+1)`. -/
private lemma erfCF_partNum_getD (x : ℝ) (i : ℕ) :
    ((erfCF x).partNums.get? i).getD 0 = cfA x (i + 1) := by
  rw [GenContFract.partNum_eq_s_a (erfCF_s_get? x i)]
  rfl

/-- The partial-numerator products of `erfCF` are positive. -/
private lemma erfCF_partNumProd_pos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 < FLMF.Methods.partNumProd (erfCF x) n := by
  unfold FLMF.Methods.partNumProd
  apply Finset.prod_pos
  intro i _
  rw [erfCF_partNum_getD]
  exact cfA_pos x hx (i + 1) (by omega)

/-- Product recurrence for the partial numerators of `erfCF`. -/
private lemma erfCF_partNumProd_succ (x : ℝ) (n : ℕ) :
    FLMF.Methods.partNumProd (erfCF x) (n + 1) =
      FLMF.Methods.partNumProd (erfCF x) n * cfA x (n + 1) := by
  rw [FLMF.Methods.partNumProd_succ, erfCF_partNum_getD]

/-- Two-step gap estimate `convGap (n+2) · (1 + 2x²/(n+2)) ≤ convGap n`: expanding two steps
of the Wallis recurrence produces the cross term `2·bₙ₊₂bₙ₊₃·aₙ₊₂·BₙBₙ₊₁ = 2x²·aₙ₊₂·BₙBₙ₊₁`,
which dominates the extra `x²/aₙ₊₃`-fraction of the gap since `aₙ₊₃ = (n+2)/2`. -/
private lemma erfCF_gap_two_step (x : ℝ) (hx : 0 < x) (n : ℕ) :
    FLMF.Methods.convGap (erfCF x) (n + 2) * (1 + 2 * x ^ 2 / ((n : ℝ) + 2)) ≤
      FLMF.Methods.convGap (erfCF x) n := by
  have hpos := erfCF_pos x hx
  have hB0 := erfCF_dens_pos x hx n
  have hB1 := erfCF_dens_pos x hx (n + 1)
  have hB2 := erfCF_dens_pos x hx (n + 2)
  have hB3 := erfCF_dens_pos x hx (n + 3)
  have hP1 := erfCF_partNumProd_pos x hx (n + 1)
  have hrec2 : (erfCF x).dens (n + 2) =
      cfB x (n + 2) * (erfCF x).dens (n + 1) + cfA x (n + 2) * (erfCF x).dens n :=
    GenContFract.dens_recurrence (erfCF_s_get? x (n + 1)) rfl rfl
  have hrec3 : (erfCF x).dens (n + 3) =
      cfB x (n + 3) * (erfCF x).dens (n + 2) + cfA x (n + 3) * (erfCF x).dens (n + 1) :=
    GenContFract.dens_recurrence (erfCF_s_get? x (n + 2)) rfl rfl
  have hb23 : cfB x (n + 2) * cfB x (n + 3) = x ^ 2 := cfB_mul_succ x hx (n + 2) (by omega)
  have hb2 : 0 < cfB x (n + 2) := cfB_pos x hx (n + 2) (by omega)
  have hb3 : 0 < cfB x (n + 3) := cfB_pos x hx (n + 3) (by omega)
  have ha2 : 0 < cfA x (n + 2) := cfA_pos x hx (n + 2) (by omega)
  have ha3 : 0 < cfA x (n + 3) := cfA_pos x hx (n + 3) (by omega)
  have ha2v : cfA x (n + 2) = ((n : ℝ) + 1) / 2 := by
    rw [cfA_val x (by omega)]; push_cast; ring
  have ha3v : cfA x (n + 3) = ((n : ℝ) + 2) / 2 := by
    rw [cfA_val x (by omega)]; push_cast; ring
  rw [FLMF.Methods.convGap_eq hpos, FLMF.Methods.convGap_eq hpos]
  have hP3 : FLMF.Methods.partNumProd (erfCF x) (n + 2 + 1) =
      FLMF.Methods.partNumProd (erfCF x) (n + 1) * cfA x (n + 2) * cfA x (n + 3) := by
    rw [erfCF_partNumProd_succ, erfCF_partNumProd_succ]
  rw [hP3]
  have e3 : (erfCF x).dens (n + 2 + 1) = (erfCF x).dens (n + 3) := rfl
  rw [e3]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  -- key continuant inequality
  have hfac : cfA x (n + 2) * cfA x (n + 3) * (1 + 2 * x ^ 2 / ((n : ℝ) + 2)) =
      cfA x (n + 2) * cfA x (n + 3) + cfA x (n + 2) * x ^ 2 := by
    rw [ha2v, ha3v]
    have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    try ring
  have h5 : cfB x (n + 2) * cfB x (n + 3) *
        (cfA x (n + 2) * ((erfCF x).dens n * (erfCF x).dens (n + 1))) =
      x ^ 2 * (cfA x (n + 2) * ((erfCF x).dens n * (erfCF x).dens (n + 1))) := by
    rw [hb23]
  have hkey : cfA x (n + 2) * cfA x (n + 3) * (1 + 2 * x ^ 2 / ((n : ℝ) + 2)) *
        ((erfCF x).dens n * (erfCF x).dens (n + 1)) ≤
      (erfCF x).dens (n + 2) * (erfCF x).dens (n + 3) := by
    rw [hfac, hrec3, hrec2]
    have t1 : 0 ≤ cfB x (n + 3) * (cfB x (n + 2) * (erfCF x).dens (n + 1)) ^ 2 :=
      mul_nonneg hb3.le (sq_nonneg _)
    have t2 : 0 ≤ cfB x (n + 3) * (cfA x (n + 2) * (erfCF x).dens n) ^ 2 :=
      mul_nonneg hb3.le (sq_nonneg _)
    have t3 : 0 ≤ cfA x (n + 3) * cfB x (n + 2) * ((erfCF x).dens (n + 1) * (erfCF x).dens (n + 1)) :=
      mul_nonneg (mul_nonneg ha3.le hb2.le) (mul_nonneg hB1.le hB1.le)
    have t4 : 0 ≤ x ^ 2 * (cfA x (n + 2) * ((erfCF x).dens n * (erfCF x).dens (n + 1))) :=
      mul_nonneg (sq_nonneg x) (mul_nonneg ha2.le (mul_nonneg hB0.le hB1.le))
    nlinarith [t1, t2, t3, t4, h5]
  nlinarith [hkey, hP1, mul_pos hB0 hB1, mul_pos hB2 hB3]

/-- Chained gap estimate: `convGap (2M) · (1 + x²·H_M) ≤ convGap 0` with `H_M` the harmonic
partial sum, by induction on `M` from the two-step estimate. -/
private lemma erfCF_gap_chain (x : ℝ) (hx : 0 < x) (M : ℕ) :
    FLMF.Methods.convGap (erfCF x) (2 * M) *
        (1 + x ^ 2 * ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1)) ≤
      FLMF.Methods.convGap (erfCF x) 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hpos := erfCF_pos x hx
    have h2 := erfCF_gap_two_step x hx (2 * M)
    have hchain : FLMF.Methods.convGap (erfCF x) (2 * M + 2) ≤
        FLMF.Methods.convGap (erfCF x) (2 * M) :=
      le_trans (FLMF.Methods.convGap_succ_le hpos (2 * M + 1))
        (FLMF.Methods.convGap_succ_le hpos (2 * M))
    have hSnn : (0:ℝ) ≤ ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hx2S : (0:ℝ) ≤ x ^ 2 * ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1) :=
      mul_nonneg (sq_nonneg x) hSnn
    have hidx : 2 * (M + 1) = 2 * M + 2 := by ring
    have hs : 2 * x ^ 2 / (((2 * M : ℕ) : ℝ) + 2) = x ^ 2 * ((1:ℝ) / ((M : ℝ) + 1)) := by
      have hne : ((M : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [hs] at h2
    rw [hidx, Finset.sum_range_succ]
    nlinarith [ih, h2, hchain, hx2S]

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- The convergent gap of the DLMF 7.9.1 fraction tends to `0`: the even-index bound
`convGap (2M) ≤ convGap 0 / (1 + x²·H_M)` with `H_M → ∞` (divergent harmonic series), plus
antitonicity of the gap for the full sequence. -/
private lemma erfCF_gap_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => FLMF.Methods.convGap (erfCF x) n) atTop (𝓝 0) := by
  have hpos := erfCF_pos x hx
  have hantitone : Antitone fun n => FLMF.Methods.convGap (erfCF x) n :=
    antitone_nat_of_succ_le fun n => FLMF.Methods.convGap_succ_le hpos n
  have hH : Tendsto
      (fun M : ℕ => 1 + x ^ 2 * ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0:ℝ) < x ^ 2)
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hbound : ∀ M : ℕ, FLMF.Methods.convGap (erfCF x) (2 * M) ≤
      FLMF.Methods.convGap (erfCF x) 0 /
        (1 + x ^ 2 * ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1)) := by
    intro M
    have h := erfCF_gap_chain x hx M
    have hSnn : (0:ℝ) ≤ ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hpos1 : (0:ℝ) < 1 + x ^ 2 * ∑ i ∈ Finset.range M, (1:ℝ) / ((i : ℝ) + 1) := by
      nlinarith [sq_nonneg x]
    rw [le_div_iff₀ hpos1]
    linarith [h]
  have heven : Tendsto (fun M : ℕ => FLMF.Methods.convGap (erfCF x) (2 * M)) atTop (𝓝 0) := by
    apply squeeze_zero (fun M => FLMF.Methods.convGap_nonneg hpos (2 * M)) hbound
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hH
  have hdiv2 : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => Nat.div_le_div_right h)
      (fun b => ⟨2 * b, by omega⟩)
  have hcomp : Tendsto (fun n : ℕ => FLMF.Methods.convGap (erfCF x) (2 * (n / 2))) atTop (𝓝 0) :=
    heven.comp hdiv2
  apply squeeze_zero (fun n => FLMF.Methods.convGap_nonneg hpos n) (fun n => ?_) hcomp
  exact hantitone (by omega : 2 * (n / 2) ≤ n)

/-- The consecutive-convergent difference tends to `0` (the absolute value of the difference
is exactly the signed gap `convGap`). -/
private lemma erfCF_diff_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => (erfCF x).convs (n + 1) - (erfCF x).convs n) atTop (𝓝 0) := by
  have hpos := erfCF_pos x hx
  have hgapT := erfCF_gap_tendsto x hx
  have key : ∀ n, |(erfCF x).convs (n + 1) - (erfCF x).convs n| =
      FLMF.Methods.convGap (erfCF x) n := by
    intro n
    have hnn := FLMF.Methods.convGap_nonneg hpos n
    have hdef : FLMF.Methods.convGap (erfCF x) n =
        (-1) ^ n * ((erfCF x).convs (n + 1) - (erfCF x).convs n) := rfl
    rcases Nat.even_or_odd n with he | ho
    · rw [hdef, he.neg_one_pow, one_mul] at hnn ⊢
      exact abs_of_nonneg hnn
    · rw [hdef, ho.neg_one_pow, neg_one_mul] at hnn ⊢
      rw [abs_of_nonpos (by linarith)]
  have habs0 : Tendsto (fun n => |(erfCF x).convs (n + 1) - (erfCF x).convs n|) atTop (𝓝 0) := by
    have hfe : (fun n => |(erfCF x).convs (n + 1) - (erfCF x).convs n|) =
        fun n => FLMF.Methods.convGap (erfCF x) n := funext key
    rw [hfe]
    exact hgapT
  have hneg : Tendsto (fun n => -|(erfCF x).convs (n + 1) - (erfCF x).convs n|) atTop (𝓝 0) := by
    simpa using habs0.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs0
    (fun n => neg_abs_le _) (fun n => le_abs_self _)

-- no-dlmf: real/narrowed restriction of DLMF 7.9.1; faithful surface is erf_7_9_1_complex
/-- Laplace continued fraction for the complementary error function, stated as
the convergence of its convergents, on the real slice `x > 0` of DLMF 7.9.1.

The partial numerators of `√π e^{x²} erfc(x) = x/(x² + ½/(1 + 1/(x² + 3/2/(1 +
2/(x² + ⋯)))))` are, in the Wallis recurrence convention of `cfConv` (which uses
`a 1, a 2, …` — `a 0` is never read), `a 1 = x` (the leading numerator) and
`a m = (m−1)/2` for `m ≥ 2` (so `a 2 = ½, a 3 = 1, a 4 = 3/2, …`); the partial
denominators alternate `b (2k+1) = x²`, `b (2k+2) = 1` (with `b 0 = 0`, so the
fraction starts `x/(x² + …)`).
The convergents tend to `√π e^{x²} erfc(x)` for `x > 0`
(the `ℜ z > 0` slice of DLMF 7.9.1; the full-strength complex statement is
`erf_7_9_1_complex`).
(Corrected 2026-06-25: the original `a` sequence put the leading `x` at the unused
index `a 0`, dropping the `x/(x²+…)` factor — the convergents then converged to the
wrong value. See docs/ERRATA.md.)
-/
theorem erf_7_9_1 (x : ℝ) (hx : 0 < x) :
    Tendsto
      (cfConv
        (fun k => if k = 0 then 0 else if k = 1 then x else ((k : ℝ) - 1) / 2)
        (fun k => if k = 0 then 0
          else if k % 2 = 1 then x ^ 2 else 1))
      atTop (𝓝 (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x)) := by
  have hpos := erfCF_pos x hx
  have htail : ∀ n, ∃ gp, (erfCF x).s.get? n = some gp ∧
      erfTail x n = gp.a / (gp.b + erfTail x (n + 1)) :=
    fun n => ⟨⟨cfA x (n + 1), cfB x (n + 1)⟩, erfCF_s_get? x n, erfTail_rec x hx n⟩
  have hmain := FLMF.Methods.tendsto_convs_of_tails hpos (erfTail_pos x hx) htail
    (erfCF_diff_tendsto x hx)
  have hlim : (erfCF x).h + erfTail x 0 = Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x := by
    show cfB x 0 + erfTail x 0 = _
    unfold cfB erfTail
    simp
  rw [hlim] at hmain
  have hfun : cfConv (cfA x) (cfB x) = (erfCF x).convs := funext (erfCF_conv x)
  show Tendsto (cfConv (cfA x) (cfB x)) atTop _
  rw [hfun]
  exact hmain

/-! ### The complex tail integrals of the DLMF 7.9.1 fraction

For `ℜ z ≥ 0` put `Kₙ(z) = ∫₀^∞ sⁿ e^{-s²-2zs} ds` (`erfK`).  The substitution
`t = x + s` identifies `Kₙ(x) = e^{x²} Jₙ(x)` for real `x`, and `K₀` is the
Laplace-transform representation `K₀(z) = (√π/2) e^{z²} erfc z` of DLMF 7.7.3
(`gaussLin_integral_eq_cerfc`).  The `Kₙ` obey the same integration-by-parts
recurrence `(n+1)Kₙ = 2zKₙ₊₁ + 2Kₙ₊₂` as `erfJ`, which makes
`Rₙ = (−1)ⁿ 2 Kₙ(z) z^{n mod 2}` a solution of the Wallis recurrence of the
7.9.1 fraction sharing the two seeds of the *remainder* `V Bₙ − Aₙ` at the value
`V = √π e^{z²} erfc z`; hence the two agree (`erfRem_eq`).

This closes DLMF 7.9.1 on `ℜ z > 0` with no analytic continuation.  Writing
`uₙ = V − fₙ = Rₙ/Bₙ`, the determinant formula gives
`fₙ₊₁ − fₙ = ±(z n!/2ⁿ)/(BₙBₙ₊₁)`, while `‖Kₙ(z)‖ ≤ Mₙ = ∫₀^∞ sⁿ e^{-s²} ds`
with `4 MₙMₙ₊₁ 2ⁿ = C·n!` (`erfM_prod`, `C = 4M₀M₁`).  Hence
`‖uₙuₙ₊₁‖ ≤ C‖fₙ₊₁ − fₙ‖`, whereas `uₙ − uₙ₊₁ = fₙ₊₁ − fₙ → 0` by Van Vleck's
theorem applied to the `aₙ ↦ 1` normalization of the fraction (whose partial
denominators are the *positive real* multiples `ρₙ z` of `z`, hence lie in a
sector, and are not summable since `ρₙρₙ₊₁ = 2/(n+1)`).  From
`‖uₙ‖² ≤ ‖uₙ‖‖uₙ − uₙ₊₁‖ + ‖uₙuₙ₊₁‖` one then gets
`‖uₙ‖ ≤ ‖fₙ₊₁−fₙ‖ + √(C‖fₙ₊₁−fₙ‖) → 0`. -/

-- no-dlmf: private kit definition; the real majorant of the complex tail integrals
/-- `Mₙ = ∫₀^∞ sⁿ e^{-s²} ds`, the `z = 0` instance of the tail integrals `erfK`. -/
private noncomputable def erfM (n : ℕ) : ℝ := ∫ s in Set.Ioi (0:ℝ), s ^ n * Real.exp (-s ^ 2)

-- no-dlmf: private kit lemma; `Mₙ` is the `x = 0` value of `erfJ`
private lemma erfM_eq_erfJ (n : ℕ) : erfM n = erfJ 0 n := by
  unfold erfM erfJ
  simp

-- no-dlmf: private kit lemma; integrability of the majorant integrand
private lemma erfM_integrableOn (n : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-s ^ 2)) (Set.Ioi 0) := by
  have h := erfJ_integrableOn 0 le_rfl n
  simpa using h

-- no-dlmf: private kit lemma; nonnegativity of the majorant
private lemma erfM_nonneg (n : ℕ) : 0 ≤ erfM n := by
  refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
  have : (0:ℝ) < s := hs
  positivity

-- no-dlmf: private kit lemma; the `x = 0` case of the `erfJ` recurrence
private lemma erfM_rec (n : ℕ) : ((n : ℝ) + 1) * erfM n = 2 * erfM (n + 2) := by
  have h := erfJ_rec 0 le_rfl n
  rw [erfM_eq_erfJ, erfM_eq_erfJ]
  simpa using h

-- no-dlmf: private kit lemma; the closed form `4 MₙMₙ₊₁ 2ⁿ = (4M₀M₁)·n!`
/-- The products `4 Mₙ Mₙ₊₁ 2ⁿ / n!` are constant: an immediate induction on the
recurrence `2Mₙ₊₂ = (n+1)Mₙ`.  (The constant is `4M₀M₁ = √π`, but its value is
never needed.) -/
private lemma erfM_prod (n : ℕ) :
    4 * erfM n * erfM (n + 1) * 2 ^ n = (4 * erfM 0 * erfM 1) * (Nat.factorial n : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hrec := erfM_rec n
    rw [Nat.factorial_succ]
    push_cast
    linear_combination (-(4 * erfM (n + 1) * 2 ^ n)) * hrec + ((n : ℝ) + 1) * ih

-- no-dlmf: private kit definition; complex Laplace tail integrals of DLMF 7.9.1
/-- `Kₙ(z) = ∫₀^∞ sⁿ e^{-s² − 2zs} ds`, the complex (`ℜ z ≥ 0`) analogue of the
Gaussian tail integrals `erfJ`: `Kₙ(x) = e^{x²} Jₙ(x)` for real `x ≥ 0`. -/
private noncomputable def erfK (z : ℂ) (n : ℕ) : ℂ :=
  ∫ s in Set.Ioi (0:ℝ), (s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))

-- no-dlmf: private kit lemma; pointwise majorization of the `erfK` integrand
private lemma norm_erfK_integrand {z : ℂ} (hz : 0 ≤ z.re) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ‖(s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))‖ ≤ s ^ n * Real.exp (-s ^ 2) := by
  have hre : (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)).re = -s ^ 2 - 2 * z.re * s := by
    simp [Complex.mul_re, pow_two]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
    Complex.norm_exp, hre]
  have hexp : Real.exp (-s ^ 2 - 2 * z.re * s) ≤ Real.exp (-s ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

-- no-dlmf: private kit lemma; integrability of the `erfK` integrand on `ℜ z ≥ 0`
private lemma erfK_integrableOn {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
      (Set.Ioi 0) := by
  refine (erfM_integrableOn n).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_erfK_integrand hz hs n

-- no-dlmf: private kit lemma; `‖Kₙ(z)‖ ≤ Mₙ` on the closed right half-plane
private lemma norm_erfK_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) : ‖erfK z n‖ ≤ erfM n := by
  rw [erfK, erfM]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  exact setIntegral_mono_on (erfK_integrableOn hz n).norm (erfM_integrableOn n)
    measurableSet_Ioi (fun s hs => norm_erfK_integrand hz hs n)

-- no-dlmf: private kit lemma; the derivative behind the `erfK` recurrence
private lemma erfK_hasDerivAt (z : ℂ) (n : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
      (((n : ℂ) + 1) * ((s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * ((s : ℂ) ^ (n + 2) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * z * ((s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))) s := by
  have h1 : HasDerivAt (fun w : ℂ => w ^ (n + 1)) (((n : ℂ) + 1) * (s : ℂ) ^ n) (s : ℂ) := by
    have h := hasDerivAt_pow (n + 1) ((s : ℝ) : ℂ)
    simpa using h
  have h2 : HasDerivAt (fun w : ℂ => -w ^ 2 - 2 * z * w) (-(2 * (s : ℂ)) - 2 * z) (s : ℂ) := by
    have ha := (hasDerivAt_pow 2 ((s : ℝ) : ℂ)).neg
    have hb := (hasDerivAt_id ((s : ℝ) : ℂ)).const_mul (2 * z)
    have := ha.sub hb
    convert this using 1
    simp
  have h3 := h1.mul h2.cexp
  have h4 : HasDerivAt (fun w : ℂ => w ^ (n + 1) * Complex.exp (-w ^ 2 - 2 * z * w))
      (((n : ℂ) + 1) * ((s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * ((s : ℂ) ^ (n + 2) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * z * ((s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      ((s : ℝ) : ℂ) := by
    convert h3 using 1
    ring
  exact h4.comp_ofReal

-- no-dlmf: private kit lemma; decay of the `erfK` primitive at `+∞`
private lemma erfK_tendsto_zero {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp_neg_atTop_nhds_zero (n + 1))
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ), Filter.eventually_ge_atTop (1:ℝ)] with s hs hs1
  refine le_trans (norm_erfK_integrand hz hs (n + 1)) ?_
  have hexp : Real.exp (-s ^ 2) ≤ Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

-- no-dlmf: private kit lemma; integration-by-parts recurrence for the `erfK`
/-- `(n+1) Kₙ = 2z Kₙ₊₁ + 2 Kₙ₊₂`: the complex form of `erfJ_rec`, from
`∫₀^∞ d/ds [sⁿ⁺¹ e^{-s²-2zs}] ds = 0`. -/
private lemma erfK_rec {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ((n : ℂ) + 1) * erfK z n = 2 * z * erfK z (n + 1) + 2 * erfK z (n + 2) := by
  have hi0 := erfK_integrableOn hz n
  have hi1 := erfK_integrableOn hz (n + 1)
  have hi2 := erfK_integrableOn hz (n + 2)
  have hA : IntegrableOn (fun s : ℝ =>
      ((n : ℂ) + 1) * ((s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hi0.const_mul _
  have hB : IntegrableOn (fun s : ℝ =>
      2 * ((s : ℂ) ^ (n + 2) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hi2.const_mul _
  have hC : IntegrableOn (fun s : ℝ =>
      2 * z * ((s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hi1.const_mul _
  have hAB : IntegrableOn (fun s : ℝ =>
      ((n : ℂ) + 1) * ((s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * ((s : ℂ) ^ (n + 2) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hA.sub hB
  have hφint : IntegrableOn (fun s : ℝ =>
      ((n : ℂ) + 1) * ((s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * ((s : ℂ) ^ (n + 2) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        - 2 * z * ((s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hAB.sub hC
  have hcont : ContinuousWithinAt
      (fun s : ℝ => (s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
      (Set.Ici 0) 0 := (by fun_prop : Continuous _).continuousWithinAt
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun s _ => erfK_hasDerivAt z n s) hφint (erfK_tendsto_zero hz n)
  rw [MeasureTheory.integral_sub hAB hC, MeasureTheory.integral_sub hA hB,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul] at hFTC
  simp only [Complex.ofReal_zero] at hFTC
  rw [erfK, erfK, erfK]
  have hz0 : ((0 : ℂ)) ^ (n + 1) * Complex.exp (-(0 : ℂ) ^ 2 - 2 * z * (0 : ℂ)) = 0 := by
    simp
  rw [hz0] at hFTC
  linear_combination hFTC

-- no-dlmf: private kit lemma; the base identity `2zK₀ + 2K₁ = 1`
private lemma erfK_base {z : ℂ} (hz : 0 ≤ z.re) : 2 * z * erfK z 0 + 2 * erfK z 1 = 1 := by
  have hi0 := erfK_integrableOn hz 0
  have hi1 := erfK_integrableOn hz 1
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
        (-(2 * ((s : ℂ) ^ 1 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
          - 2 * z * ((s : ℂ) ^ 0 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))) s := by
    intro s
    have h2 : HasDerivAt (fun w : ℂ => -w ^ 2 - 2 * z * w) (-(2 * (s : ℂ)) - 2 * z) (s : ℂ) := by
      have ha := (hasDerivAt_pow 2 ((s : ℝ) : ℂ)).neg
      have hb := (hasDerivAt_id ((s : ℝ) : ℂ)).const_mul (2 * z)
      have := ha.sub hb
      convert this using 1
      simp
    have h4 : HasDerivAt (fun w : ℂ => Complex.exp (-w ^ 2 - 2 * z * w))
        (-(2 * ((s : ℂ) ^ 1 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
          - 2 * z * ((s : ℂ) ^ 0 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
        ((s : ℝ) : ℂ) := by
      convert h2.cexp using 1
      ring
    exact h4.comp_ofReal
  have hA : IntegrableOn (fun s : ℝ =>
      -(2 * ((s : ℂ) ^ 1 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))))
      (Set.Ioi 0) := (hi1.const_mul _).neg
  have hB : IntegrableOn (fun s : ℝ =>
      2 * z * ((s : ℂ) ^ 0 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hi0.const_mul _
  have hφint : IntegrableOn (fun s : ℝ =>
      -(2 * ((s : ℂ) ^ 1 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
        - 2 * z * ((s : ℂ) ^ 0 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))))
      (Set.Ioi 0) := hA.sub hB
  have hcont : ContinuousWithinAt
      (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ))) (Set.Ici 0) 0 :=
    (by fun_prop : Continuous _).continuousWithinAt
  have htend : Tendsto (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have h := norm_erfK_integrand hz hs0 0
    simp only [pow_zero, one_mul] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun s _ => hderiv s) hφint htend
  rw [MeasureTheory.integral_sub hA hB, MeasureTheory.integral_neg,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hFTC
  simp only [Complex.ofReal_zero] at hFTC
  rw [erfK, erfK]
  have hz0 : Complex.exp (-(0 : ℂ) ^ 2 - 2 * z * (0 : ℂ)) = 1 := by simp
  rw [hz0] at hFTC
  linear_combination -hFTC

-- no-dlmf: private kit lemma; `2K₀(z) = √π e^{z²} erfc z` (the DLMF 7.7.3 Laplace transform)
private lemma erfK_zero_eq (z : ℂ) :
    2 * erfK z 0 = (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z := by
  have ha : (0:ℝ) < (1 : ℂ).re := by norm_num
  have h := gaussLin_integral_eq_cerfc (a := (1 : ℂ)) (z := Complex.I * z) ha
  have hcongr : ∀ s : ℝ,
      Complex.exp (-(1:ℂ) * (s : ℂ) ^ 2 + 2 * Complex.I * (Complex.I * z) * (s : ℂ))
        = (s : ℂ) ^ 0 * Complex.exp (-(s : ℂ) ^ 2 - 2 * z * (s : ℂ)) := by
    intro s
    rw [pow_zero, one_mul]
    congr 1
    linear_combination (2 * z * (s : ℂ)) * Complex.I_sq
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hcongr s)] at h
  rw [erfK, h, Complex.one_cpow]
  have hI : -Complex.I * (Complex.I * z) * 1 = z := by
    have : -Complex.I * (Complex.I * z) = z := by
      linear_combination (-z) * Complex.I_sq
    rw [this, mul_one]
  have hE : Complex.exp (-(Complex.I * z) ^ 2 / 1) = Complex.exp (z ^ 2) := by
    congr 1
    field_simp
    linear_combination (-z ^ 2) * Complex.I_sq
  rw [hI, hE]
  ring

/-! ### The DLMF 7.9.1 fraction over `ℂ` -/

-- no-dlmf: complex partial numerators of the DLMF 7.9.1 fraction
/-- Partial numerators of DLMF 7.9.1 over `ℂ` (the `a`-sequence of
`erf_7_9_1_complex`). -/
private noncomputable def cfAC (z : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k = 1 then z else ((k : ℂ) - 1) / 2

-- no-dlmf: complex partial denominators of the DLMF 7.9.1 fraction
/-- Partial denominators of DLMF 7.9.1 over `ℂ` (the `b`-sequence of
`erf_7_9_1_complex`). -/
private noncomputable def cfBC (z : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k % 2 = 1 then z ^ 2 else 1

-- no-dlmf: the complex DLMF 7.9.1 fraction as a `GenContFract`
/-- The DLMF 7.9.1 fraction over `ℂ`, packaged as a (non-terminating)
`GenContFract`, so that the method kits of `FLMF.Methods.ContinuedFraction` and
`FLMF.Methods.VanVleck` apply. -/
private noncomputable def erfCFC (z : ℂ) : GenContFract ℂ :=
  ⟨cfBC z 0, ⟨fun n => some ⟨cfAC z (n + 1), cfBC z (n + 1)⟩, fun {n} h => by simp at h⟩⟩

-- no-dlmf: private kit lemma; the `n`-th partial pair of `erfCFC`
private lemma erfCFC_s_get? (z : ℂ) (n : ℕ) :
    (erfCFC z).s.get? n = some ⟨cfAC z (n + 1), cfBC z (n + 1)⟩ := rfl

-- no-dlmf: private kit lemma; value of the partial numerators for `k ≥ 2`
private lemma cfAC_val (z : ℂ) {k : ℕ} (hk : 2 ≤ k) : cfAC z k = ((k : ℂ) - 1) / 2 := by
  unfold cfAC
  rw [if_neg (by omega), if_neg (by omega)]

-- no-dlmf: private kit lemma; the `GenContFract` numerator continuants of `erfCFC`
private lemma erfCFC_num (z : ℂ) : ∀ n, (erfCFC z).nums n = cfNumC (cfAC z) (cfBC z) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_num_eq_h]
    rfl
  | one =>
    rw [GenContFract.first_num_eq (erfCFC_s_get? z 0)]
    rfl
  | more n ih ih1 =>
    have h := GenContFract.nums_recurrence (erfCFC_s_get? z (n + 1)) ih ih1
    simpa [cfNumC] using h

-- no-dlmf: private kit lemma; the `GenContFract` denominator continuants of `erfCFC`
private lemma erfCFC_den (z : ℂ) : ∀ n, (erfCFC z).dens n = cfDenC (cfAC z) (cfBC z) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_den_eq_one]
    rfl
  | one =>
    rw [GenContFract.first_den_eq (erfCFC_s_get? z 0)]
    rfl
  | more n ih ih1 =>
    have h := GenContFract.dens_recurrence (erfCFC_s_get? z (n + 1)) ih ih1
    simpa [cfDenC] using h

-- no-dlmf: private kit lemma; `cfConvC` of the 7.9.1 sequences is `erfCFC`'s convergent
private lemma erfCFC_conv (z : ℂ) (n : ℕ) :
    cfConvC (cfAC z) (cfBC z) n = (erfCFC z).convs n := by
  rw [cfConvC, GenContFract.conv_eq_num_div_den, erfCFC_num, erfCFC_den]

-- no-dlmf: private kit lemma; the `i`-th partial numerator of `erfCFC` (with default `0`)
private lemma erfCFC_partNum_getD (z : ℂ) (i : ℕ) :
    ((erfCFC z).partNums.get? i).getD 0 = cfAC z (i + 1) := by
  rw [GenContFract.partNum_eq_s_a (erfCFC_s_get? z i)]
  rfl

-- no-dlmf: private kit lemma; the partial-numerator products are `z·n!/2ⁿ`
private lemma erfCFC_partNumProd (z : ℂ) (n : ℕ) :
    FLMF.Methods.partNumProd (erfCFC z) (n + 1) = z * (Nat.factorial n : ℂ) / 2 ^ n := by
  induction n with
  | zero =>
    rw [FLMF.Methods.partNumProd_succ, erfCFC_partNum_getD]
    simp [FLMF.Methods.partNumProd, cfAC]
  | succ n ih =>
    rw [FLMF.Methods.partNumProd_succ, erfCFC_partNum_getD, ih,
      cfAC_val z (by omega : 2 ≤ n + 1 + 1), Nat.factorial_succ]
    push_cast
    ring

/-! ### The `aₙ ↦ 1` normalization of the DLMF 7.9.1 fraction -/

-- no-dlmf: private kit definition; the positive scaling sequence of the normalization
/-- The positive reals `ρₙ` with `ρ₀ = 1` and `ρₙρₙ₊₁ = 2/(n+1)`: after the
equivalence transformation making every partial numerator `1`, the partial
denominators of the DLMF 7.9.1 fraction are exactly `ρₙ z`. -/
private noncomputable def cfRho : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 2 / (((n : ℝ) + 1) * cfRho n)

-- no-dlmf: private kit lemma; positivity of the scaling sequence
private lemma cfRho_pos : ∀ n, 0 < cfRho n
  | 0 => by norm_num [cfRho]
  | (n + 1) => by
    have h := cfRho_pos n
    rw [cfRho]
    positivity

-- no-dlmf: private kit lemma; the defining product relation `ρₙρₙ₊₁ = 2/(n+1)`
private lemma cfRho_mul_succ (n : ℕ) : cfRho n * cfRho (n + 1) = 2 / ((n : ℝ) + 1) := by
  have h := (cfRho_pos n).ne'
  rw [cfRho]
  field_simp

-- no-dlmf: private kit definition; the equivalence-transformation factors
/-- Equivalence-transformation factors normalizing DLMF 7.9.1 to all-ones partial
numerators: `cₙ = ρₙ/z` for even `n`, `ρₙ z` for odd `n`. -/
private noncomputable def cfCC (z : ℂ) (n : ℕ) : ℂ :=
  if n % 2 = 0 then (cfRho n : ℂ) / z else (cfRho n : ℂ) * z

-- no-dlmf: private kit lemma; the transformation factors are nonzero
private lemma cfCC_ne_zero {z : ℂ} (hz : z ≠ 0) (n : ℕ) : cfCC z n ≠ 0 := by
  have h := (cfRho_pos n).ne'
  have h' : ((cfRho n : ℝ) : ℂ) ≠ 0 := by
    simpa using h
  unfold cfCC
  split_ifs
  · exact div_ne_zero h' hz
  · exact mul_ne_zero h' hz

-- no-dlmf: private kit lemma; consecutive factors multiply to `ρₙρₙ₊₁`
private lemma cfCC_mul_succ {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    cfCC z n * cfCC z (n + 1) = ((cfRho n * cfRho (n + 1) : ℝ) : ℂ) := by
  unfold cfCC
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos h0, if_neg (by omega : ¬ (n + 1) % 2 = 0)]
    push_cast
    field_simp
  · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_neg (by omega : ¬ n % 2 = 0), if_pos (by omega : (n + 1) % 2 = 0)]
    push_cast
    field_simp

-- no-dlmf: private kit lemma; the transformation normalizes the partial numerators
private lemma equivFactor_cfAC {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    FLMF.Methods.equivFactor (cfCC z) n * cfAC z (n + 1) = 1 := by
  cases n with
  | zero =>
    rw [FLMF.Methods.equivFactor_zero]
    unfold cfCC cfAC
    norm_num [cfRho]
    field_simp
  | succ n =>
    rw [FLMF.Methods.equivFactor_succ, cfCC_mul_succ hz, cfRho_mul_succ,
      cfAC_val z (by omega : 2 ≤ n + 1 + 1)]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hnC : ((n : ℂ) + 1) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hn)
    push_cast
    field_simp
    ring

-- no-dlmf: private kit lemma; the transformed partial denominators are `ρₙ z`
private lemma cfCC_mul_cfBC {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    cfCC z n * cfBC z (n + 1) = (cfRho n : ℂ) * z := by
  unfold cfCC cfBC
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos h0, if_neg (by omega : ¬ n + 1 = 0), if_pos (by omega : (n + 1) % 2 = 1)]
    field_simp
  · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_neg (by omega : ¬ n % 2 = 0), if_neg (by omega : ¬ n + 1 = 0),
      if_neg (by omega : ¬ (n + 1) % 2 = 1), mul_one]

-- no-dlmf: private kit lemma; partial pairs of the normalized fraction
private lemma equivTransform_erfCFC_s_get? {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    (FLMF.Methods.equivTransform (cfCC z) (erfCFC z)).s.get? n
      = some ⟨1, (cfRho n : ℂ) * z⟩ := by
  rw [FLMF.Methods.equivTransform_s_get?, erfCFC_s_get?, Option.map_some,
    equivFactor_cfAC hz n, cfCC_mul_cfBC hz n]

-- no-dlmf: private kit lemma; the normalized partial denominators are not summable
/-- `∑ ρₙ‖z‖ = ∞`: by AM–GM, `ρₙ + ρₙ₊₁ ≥ 2√(ρₙρₙ₊₁) = 2√(2/(n+1)) ≥ 1/(n+1)`,
and the harmonic series diverges.  This is the hypothesis of Van Vleck's
convergence theorem (DLMF 1.12.28). -/
private lemma not_summable_cfRho {z : ℂ} (hz : z ≠ 0) :
    ¬ Summable fun n => ‖(cfRho n : ℂ) * z‖ := by
  intro hsum
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ∀ n, ‖(cfRho n : ℂ) * z‖ = cfRho n * ‖z‖ := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cfRho_pos n)]
  have hsum' : Summable cfRho := by
    have h : Summable fun n => (cfRho n * ‖z‖) * ‖z‖⁻¹ := by
      exact (hsum.congr hnorm).mul_right _
    refine h.congr fun n => ?_
    field_simp
  have hsum2 : Summable fun n => cfRho n + cfRho (n + 1) :=
    hsum'.add ((summable_nat_add_iff 1).mpr hsum')
  have hharm : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum2
    have hp := cfRho_mul_succ n
    have h0 := cfRho_pos n
    have h1 := cfRho_pos (n + 1)
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hab : ((n : ℝ) + 1) * (cfRho n * cfRho (n + 1)) = 2 := by
      rw [hp]
      field_simp
    have hSpos : 0 < cfRho n + cfRho (n + 1) := by linarith
    have h8 : 8 ≤ (((n : ℝ) + 1) * (cfRho n + cfRho (n + 1))) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hn.le hn.le) (sq_nonneg (cfRho n - cfRho (n + 1))),
        hab, hn, h0, h1]
    have hone : 1 ≤ ((n : ℝ) + 1) * (cfRho n + cfRho (n + 1)) := by
      nlinarith [h8, mul_pos hn hSpos]
    rw [div_le_iff₀ hn]
    nlinarith [hone]
  have hfalse : Summable fun n : ℕ => 1 / (n : ℝ) := by
    rw [← summable_nat_add_iff 1]
    refine hharm.congr fun n => ?_
    push_cast
    ring
  exact Real.not_summable_one_div_natCast hfalse

-- no-dlmf: private kit lemma; the continuant denominators of `erfCFC` never vanish
private lemma erfCFC_dens_ne_zero {z : ℂ} (hz : 0 < z.re) (n : ℕ) : (erfCFC z).dens n ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hδ : 0 < z.re / ‖z‖ := by positivity
  have hs := equivTransform_erfCFC_s_get? hz0
  have hb0 : ∀ n, ((cfRho n : ℂ) * z) ≠ 0 := by
    intro n
    exact mul_ne_zero (by simpa using (cfRho_pos n).ne') hz0
  have hbc : ∀ n, (z.re / ‖z‖) * ‖(cfRho n : ℂ) * z‖ ≤ ((cfRho n : ℂ) * z).re := by
    intro n
    have hnorm : ‖(cfRho n : ℂ) * z‖ = cfRho n * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cfRho_pos n)]
    have hre : ((cfRho n : ℂ) * z).re = cfRho n * z.re := by
      simp [Complex.mul_re]
    have heq : z.re / ‖z‖ * (cfRho n * ‖z‖) = cfRho n * z.re := by
      rw [mul_comm (cfRho n) ‖z‖, ← mul_assoc, div_mul_cancel₀ _ hzn.ne', mul_comm]
    rw [hnorm, hre, heq]
  have hne := FLMF.Methods.VanVleck.dens_ne_zero hδ hs hb0 hbc n
  intro hzero
  refine hne ?_
  have hnt : ¬ (erfCFC z).TerminatedAt (n - 1) := by
    rw [GenContFract.terminatedAt_iff_s_none, erfCFC_s_get?]
    simp
  have h := (FLMF.Methods.equivTransform_conts (cfCC z) (g := erfCFC z) n (Or.inr hnt)).2
  rw [GenContFract.den_eq_conts_b, h, ← GenContFract.den_eq_conts_b, hzero, mul_zero]

-- no-dlmf: private kit lemma; the consecutive convergents of `erfCFC` close up
/-- Van Vleck's theorem (DLMF 1.12.28) applied to the normalized DLMF 7.9.1
fraction: since its partial denominators `ρₙ z` lie in the sector
`|ph w| ≤ π/2 − ε` and are not absolutely summable, the gap between consecutive
convergents tends to `0`. -/
private lemma erfCFC_diff_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n => (erfCFC z).convs (n + 1) - (erfCFC z).convs n) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hδ : 0 < z.re / ‖z‖ := by positivity
  have hs := equivTransform_erfCFC_s_get? hz0
  have hb0 : ∀ n, ((cfRho n : ℂ) * z) ≠ 0 := by
    intro n
    exact mul_ne_zero (by simpa using (cfRho_pos n).ne') hz0
  have hbc : ∀ n, (z.re / ‖z‖) * ‖(cfRho n : ℂ) * z‖ ≤ ((cfRho n : ℂ) * z).re := by
    intro n
    have hnorm : ‖(cfRho n : ℂ) * z‖ = cfRho n * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cfRho_pos n)]
    have hre : ((cfRho n : ℂ) * z).re = cfRho n * z.re := by
      simp [Complex.mul_re]
    have heq : z.re / ‖z‖ * (cfRho n * ‖z‖) = cfRho n * z.re := by
      rw [mul_comm (cfRho n) ‖z‖, ← mul_assoc, div_mul_cancel₀ _ hzn.ne', mul_comm]
    rw [hnorm, hre, heq]
  have h := FLMF.Methods.VanVleck.tendsto_convs_diff_zero hδ hs hb0 hbc (not_summable_cfRho hz0)
  simpa [FLMF.Methods.equivTransform_convs (cfCC z) (cfCC_ne_zero hz0) (erfCFC z)] using h

/-! ### The exact remainder of the DLMF 7.9.1 fraction -/

-- no-dlmf: private kit definition; the exact remainder `V Bₙ − Aₙ` of DLMF 7.9.1
/-- `Rₙ(z) = (−1)ⁿ 2 Kₙ(z) z^{n mod 2}`: the exact remainder of the DLMF 7.9.1
fraction at the value `V = √π e^{z²} erfc z` (`erfRem_eq`). -/
private noncomputable def erfRem (z : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n * 2 * erfK z n * (if n % 2 = 1 then z else 1)

-- no-dlmf: private kit lemma; the remainder identity `V Bₙ − Aₙ = Rₙ`
/-- **The exact remainder of the DLMF 7.9.1 fraction.**  Both sides satisfy the
Wallis recurrence of the fraction (for the right-hand side this is the
integration-by-parts recurrence `erfK_rec`) and agree at `n = 0, 1` (there the
second seed is the base identity `2zK₀ + 2K₁ = 1`). -/
private lemma erfRem_eq {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z) * cfDenC (cfAC z) (cfBC z) n
      - cfNumC (cfAC z) (cfBC z) n = erfRem z n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have h0 := erfK_zero_eq z
    have hd : cfDenC (cfAC z) (cfBC z) 0 = 1 := rfl
    have hnm : cfNumC (cfAC z) (cfBC z) 0 = 0 := by
      show cfBC z 0 = 0
      unfold cfBC
      norm_num
    have hr : erfRem z 0 = 2 * erfK z 0 := by
      unfold erfRem
      norm_num
    rw [hd, hnm, hr]
    linear_combination -h0
  | one =>
    have h := erfK_base hz
    have h0 := erfK_zero_eq z
    have hd : cfDenC (cfAC z) (cfBC z) 1 = z ^ 2 := by
      show cfBC z 1 = z ^ 2
      unfold cfBC
      norm_num
    have hnm : cfNumC (cfAC z) (cfBC z) 1 = z := by
      show cfBC z 1 * cfBC z 0 + cfAC z 1 = z
      unfold cfBC cfAC
      norm_num
    have hr : erfRem z 1 = -(2 * erfK z 1 * z) := by
      unfold erfRem
      norm_num
    rw [hd, hnm, hr]
    linear_combination z * h - z ^ 2 * h0
  | more n ih ih1 =>
    have hrec := erfK_rec hz n
    have hb : cfBC z (n + 2) = if n % 2 = 1 then z ^ 2 else 1 := by
      unfold cfBC
      rw [if_neg (by omega : ¬ n + 2 = 0)]
      rcases Nat.even_or_odd n with he | ho
      · have h0 : n % 2 = 0 := Nat.even_iff.mp he
        rw [if_neg (by omega : ¬ (n + 2) % 2 = 1), if_neg (by omega : ¬ n % 2 = 1)]
      · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
        rw [if_pos (by omega : (n + 2) % 2 = 1), if_pos h1]
    have ha : cfAC z (n + 2) = ((n : ℂ) + 1) / 2 := by
      rw [cfAC_val z (by omega : 2 ≤ n + 2)]
      push_cast
      ring
    have hstep : cfDenC (cfAC z) (cfBC z) (n + 2)
        = cfBC z (n + 2) * cfDenC (cfAC z) (cfBC z) (n + 1)
          + cfAC z (n + 2) * cfDenC (cfAC z) (cfBC z) n := rfl
    have hstep' : cfNumC (cfAC z) (cfBC z) (n + 2)
        = cfBC z (n + 2) * cfNumC (cfAC z) (cfBC z) (n + 1)
          + cfAC z (n + 2) * cfNumC (cfAC z) (cfBC z) n := rfl
    rw [hstep, hstep']
    have key : cfBC z (n + 2) * erfRem z (n + 1) + cfAC z (n + 2) * erfRem z n
        = erfRem z (n + 2) := by
      unfold erfRem
      rw [hb, ha]
      rcases Nat.even_or_odd n with he | ho
      · have h0 : n % 2 = 0 := Nat.even_iff.mp he
        have e0 : (if n % 2 = 1 then z else (1:ℂ)) = 1 := if_neg (by omega)
        have e1 : (if (n + 1) % 2 = 1 then z else (1:ℂ)) = z := if_pos (by omega)
        have e2 : (if (n + 2) % 2 = 1 then z else (1:ℂ)) = 1 := if_neg (by omega)
        have e3 : (if n % 2 = 1 then z ^ 2 else (1:ℂ)) = 1 := if_neg (by omega)
        rw [e0, e1, e2, e3]
        linear_combination ((-1 : ℂ) ^ n) * hrec
      · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
        have e0 : (if n % 2 = 1 then z else (1:ℂ)) = z := if_pos (by omega)
        have e1 : (if (n + 1) % 2 = 1 then z else (1:ℂ)) = 1 := if_neg (by omega)
        have e2 : (if (n + 2) % 2 = 1 then z else (1:ℂ)) = z := if_pos (by omega)
        have e3 : (if n % 2 = 1 then z ^ 2 else (1:ℂ)) = z ^ 2 := if_pos (by omega)
        rw [e0, e1, e2, e3]
        linear_combination ((-1 : ℂ) ^ n * z) * hrec
    linear_combination cfBC z (n + 2) * ih1 + cfAC z (n + 2) * ih + key

-- no-dlmf: private kit lemma; the product bound on consecutive remainders
/-- `‖RₙRₙ₊₁‖ ≤ C ‖z‖ n!/2ⁿ` with `C = 4M₀M₁`: exactly one of `Rₙ, Rₙ₊₁` carries
the factor `z`, and `4MₙMₙ₊₁2ⁿ = C n!`.  The right-hand side is `C` times the
modulus of the determinant `AₙBₙ₊₁ − Aₙ₊₁Bₙ` of the fraction. -/
private lemma norm_erfRem_mul {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖erfRem z n * erfRem z (n + 1)‖
      ≤ (4 * erfM 0 * erfM 1) * (‖z‖ * (Nat.factorial n : ℝ) / 2 ^ n) := by
  have hK0 := norm_erfK_le hz n
  have hK1 := norm_erfK_le hz (n + 1)
  have hM0 := erfM_nonneg n
  have hM1 := erfM_nonneg (n + 1)
  have hRn : ∀ m : ℕ,
      ‖erfRem z m‖ = 2 * ‖erfK z m‖ * ‖(if m % 2 = 1 then z else (1:ℂ))‖ := by
    intro m
    unfold erfRem
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    norm_num
  have hpf : ‖(if n % 2 = 1 then z else (1:ℂ))‖ * ‖(if (n + 1) % 2 = 1 then z else (1:ℂ))‖
      = ‖z‖ := by
    rcases Nat.even_or_odd n with he | ho
    · have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [if_neg (by omega : ¬ n % 2 = 1), if_pos (by omega : (n + 1) % 2 = 1)]
      simp
    · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [if_pos h1, if_neg (by omega : ¬ (n + 1) % 2 = 1)]
      simp
  have hexpand : ‖erfRem z n * erfRem z (n + 1)‖
      = (2 * ‖erfK z n‖) * (2 * ‖erfK z (n + 1)‖) * ‖z‖ := by
    rw [norm_mul, hRn, hRn, ← hpf]
    ring
  have hmain : (2 * ‖erfK z n‖) * (2 * ‖erfK z (n + 1)‖) ≤ 4 * erfM n * erfM (n + 1) := by
    have h1 : ‖erfK z n‖ * ‖erfK z (n + 1)‖ ≤ erfM n * erfM (n + 1) :=
      mul_le_mul hK0 hK1 (norm_nonneg _) hM0
    nlinarith [h1]
  have hfin : 4 * erfM n * erfM (n + 1)
      = (4 * erfM 0 * erfM 1) * (Nat.factorial n : ℝ) / 2 ^ n := by
    rw [eq_div_iff (by positivity : ((2:ℝ) ^ n) ≠ 0)]
    exact erfM_prod n
  rw [hexpand]
  calc (2 * ‖erfK z n‖) * (2 * ‖erfK z (n + 1)‖) * ‖z‖
      ≤ (4 * erfM n * erfM (n + 1)) * ‖z‖ := mul_le_mul_of_nonneg_right hmain (norm_nonneg z)
    _ = (4 * erfM 0 * erfM 1) * (‖z‖ * (Nat.factorial n : ℝ) / 2 ^ n) := by
        rw [hfin]
        ring

-- no-dlmf: private kit lemma; the elementary quadratic bound closing the argument
/-- If `m² ≤ m s + p` with `s, p ≥ 0` then `m ≤ s + √p`. -/
private lemma le_add_sqrt_of_sq_le {m s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (h : m ^ 2 ≤ m * s + p) : m ≤ s + Real.sqrt p := by
  by_contra hcon
  rw [not_le] at hcon
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  nlinarith [hcon, hsq, hsp]

/-- **DLMF 7.9.1** — Laplace continued fraction for the complementary error
function, for complex `z` with `ℜ z > 0`:
`√π e^{z²} erfc(z) = z/(z² + ½/(1 + 1/(z² + 3/2/(1 + 2/(z² + ⋯)))))`, stated as
the convergence of its convergents `cfConvC`, with the same `a`/`b` sequences
as `erf_7_9_1` (cast to `ℂ`).

DAG: E-7.9.1.
Numerical: PASS
Verified: verified
-/
theorem erf_7_9_1_complex (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (cfConvC
        (fun k => if k = 0 then 0 else if k = 1 then z else ((k : ℂ) - 1) / 2)
        (fun k => if k = 0 then 0
          else if k % 2 = 1 then z ^ 2 else 1))
      atTop (𝓝 ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  set V : ℂ := (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z with hVdef
  set C : ℝ := 4 * erfM 0 * erfM 1 with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact mul_nonneg (mul_nonneg (by norm_num) (erfM_nonneg 0)) (erfM_nonneg 1)
  have hBne : ∀ n, (erfCFC z).dens n ≠ 0 := erfCFC_dens_ne_zero hz
  -- the exact remainder of the fraction
  have hu : ∀ n, V - (erfCFC z).convs n = erfRem z n / (erfCFC z).dens n := by
    intro n
    have hB := hBne n
    rw [GenContFract.conv_eq_num_div_den, eq_div_iff hB, sub_mul, div_mul_cancel₀ _ hB,
      erfCFC_num z n, erfCFC_den z n]
    exact erfRem_eq hz.le n
  -- the determinant formula
  have hdet : ∀ n, (erfCFC z).convs (n + 1) - (erfCFC z).convs n
      = ((-1) ^ n * (z * (Nat.factorial n : ℂ) / 2 ^ n))
          / ((erfCFC z).dens n * (erfCFC z).dens (n + 1)) := by
    intro n
    rw [FLMF.Methods.convs_succ_sub_convs (hBne n) (hBne (n + 1)), erfCFC_partNumProd]
  -- the product bound `‖uₙuₙ₊₁‖ ≤ C‖fₙ₊₁ − fₙ‖`
  have hprodbd : ∀ n, ‖(V - (erfCFC z).convs n) * (V - (erfCFC z).convs (n + 1))‖
      ≤ C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖ := by
    intro n
    have h1 : (0:ℝ) < ‖(erfCFC z).dens n‖ := norm_pos_iff.mpr (hBne n)
    have h2 : (0:ℝ) < ‖(erfCFC z).dens (n + 1)‖ := norm_pos_iff.mpr (hBne (n + 1))
    have hW : ‖((-1:ℂ)) ^ n * (z * (Nat.factorial n : ℂ) / 2 ^ n)‖
        = ‖z‖ * (Nat.factorial n : ℝ) / 2 ^ n := by
      simp [norm_pow]
    have hBB : (0:ℝ) < ‖(erfCFC z).dens n * (erfCFC z).dens (n + 1)‖ :=
      norm_pos_iff.mpr (mul_ne_zero (hBne n) (hBne (n + 1)))
    rw [hu n, hu (n + 1), div_mul_div_comm, norm_div, hdet n, norm_div, hW,
      ← mul_div_assoc, div_le_div_iff₀ hBB hBB]
    exact mul_le_mul_of_nonneg_right (norm_erfRem_mul hz.le n) hBB.le
  -- the quadratic inequality
  have hsq : ∀ n, ‖V - (erfCFC z).convs n‖ ^ 2
      ≤ ‖V - (erfCFC z).convs n‖ * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖
        + C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖ := by
    intro n
    have hid : (V - (erfCFC z).convs n) ^ 2
        = (V - (erfCFC z).convs n)
            * ((erfCFC z).convs (n + 1) - (erfCFC z).convs n)
          + (V - (erfCFC z).convs n) * (V - (erfCFC z).convs (n + 1)) := by
      ring
    calc ‖V - (erfCFC z).convs n‖ ^ 2 = ‖(V - (erfCFC z).convs n) ^ 2‖ := by
          rw [norm_pow]
      _ = ‖(V - (erfCFC z).convs n) * ((erfCFC z).convs (n + 1) - (erfCFC z).convs n)
            + (V - (erfCFC z).convs n) * (V - (erfCFC z).convs (n + 1))‖ := by rw [hid]
      _ ≤ ‖(V - (erfCFC z).convs n) * ((erfCFC z).convs (n + 1) - (erfCFC z).convs n)‖
            + ‖(V - (erfCFC z).convs n) * (V - (erfCFC z).convs (n + 1))‖ := norm_add_le _ _
      _ ≤ ‖V - (erfCFC z).convs n‖ * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖
            + C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖ := by
          rw [norm_mul]
          linarith [hprodbd n]
  -- Van Vleck: the convergent gap tends to `0`
  have hgap0 : Tendsto
      (fun n => ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖) atTop (𝓝 0) := by
    simpa using (erfCFC_diff_tendsto hz).norm
  have hbd : ∀ n, ‖V - (erfCFC z).convs n‖
      ≤ ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖
        + Real.sqrt (C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖) := fun n =>
    le_add_sqrt_of_sq_le (norm_nonneg _) (mul_nonneg hCnn (norm_nonneg _)) (hsq n)
  have hsqrt0 : Tendsto
      (fun n => Real.sqrt (C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖))
      atTop (𝓝 0) := by
    have hC0 : Tendsto
        (fun n => C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖) atTop (𝓝 0) := by
      simpa using hgap0.const_mul C
    have h := (Real.continuous_sqrt.tendsto 0).comp hC0
    rw [Real.sqrt_zero] at h
    exact h
  have hlim : Tendsto
      (fun n => ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖
        + Real.sqrt (C * ‖(erfCFC z).convs (n + 1) - (erfCFC z).convs n‖)) atTop (𝓝 0) := by
    simpa using hgap0.add hsqrt0
  have hu0 : Tendsto (fun n => V - (erfCFC z).convs n) atTop (𝓝 0) :=
    squeeze_zero_norm hbd hlim
  have hmain : Tendsto (fun n => (erfCFC z).convs n) atTop (𝓝 V) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => V) atTop (𝓝 V)).sub hu0
    simpa using h
  show Tendsto (cfConvC (cfAC z) (cfBC z)) atTop _
  have hfun : cfConvC (cfAC z) (cfBC z) = fun n => (erfCFC z).convs n := funext (erfCFC_conv z)
  rw [hfun]
  exact hmain

-- no-dlmf: support def for the 7.9.2 continued-fraction display; surfaced at `erf_7_9_2_complex`
/-- Partial numerators of the DLMF 7.9.2 fraction (exactly the `a`-sequence of `erf_7_9_2`).

-/
private noncomputable def cfA2 (x : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else if k = 1 then 2 * x
    else -(2 * (k : ℝ) - 3) * (2 * (k : ℝ) - 2)

-- no-dlmf: support def for the 7.9.2 continued-fraction display; surfaced at `erf_7_9_2_complex`
/-- Partial denominators of the DLMF 7.9.2 fraction (exactly the `b`-sequence of `erf_7_9_2`).

-/
private noncomputable def cfB2 (x : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else 2 * x ^ 2 + (4 * (k : ℝ) - 3)

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- The even contraction of the 7.9.1 Wallis recurrence produces the 7.9.2 partial
quantities, up to the scaling `cₙ = 2ⁿ`: any solution `u` of the 7.9.1 recurrence
satisfies `2ⁿ⁺² u₂₍ₙ₊₂₎ = b'ₙ₊₂ · 2ⁿ⁺¹ u₂₍ₙ₊₁₎ + a'ₙ₊₂ · 2ⁿ u₂ₙ` with `(a', b')` the
7.9.2 sequences.  Instance of `FLMF.Methods.wallis_even_contraction`: eliminating the
odd-index terms gives `u₂ₙ₊₄ = (x² + (2n+2)/2 + (2n+3)/2) u₂ₙ₊₂ − ((2n+2)/2)((2n+1)/2) u₂ₙ`,
which is the 7.9.2 recurrence after clearing the `/2` denominators (DLMF 7.9.2 is the
even part of 7.9.1). -/
private lemma cf2_even_step (x : ℝ) (u : ℕ → ℝ)
    (hrec : ∀ k, u (k + 2) = cfB x (k + 2) * u (k + 1) + cfA x (k + 2) * u k) (n : ℕ) :
    (2 : ℝ) ^ (n + 2) * u (2 * (n + 2)) =
      cfB2 x (n + 2) * ((2 : ℝ) ^ (n + 1) * u (2 * (n + 1)))
        + cfA2 x (n + 2) * ((2 : ℝ) ^ n * u (2 * n)) := by
  have h := FLMF.Methods.wallis_even_contraction hrec n
  have hb2 : cfB x (2 * n + 2) = 1 := by
    unfold cfB; rw [if_neg (by omega), if_neg (by omega)]
  have hb3 : cfB x (2 * n + 3) = x ^ 2 := by
    unfold cfB; rw [if_neg (by omega), if_pos (by omega)]
  have hb4 : cfB x (2 * n + 4) = 1 := by
    unfold cfB; rw [if_neg (by omega), if_neg (by omega)]
  have ha2 : cfA x (2 * n + 2) = (2 * (n : ℝ) + 1) / 2 := by
    rw [cfA_val x (by omega)]; push_cast; ring
  have ha3 : cfA x (2 * n + 3) = (2 * (n : ℝ) + 2) / 2 := by
    rw [cfA_val x (by omega)]; push_cast; ring
  have ha4 : cfA x (2 * n + 4) = (2 * (n : ℝ) + 3) / 2 := by
    rw [cfA_val x (by omega)]; push_cast; ring
  rw [hb2, hb3, hb4, ha2, ha3, ha4] at h
  have e1 : 2 * (n + 2) = 2 * n + 4 := by omega
  have e2 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [e1, e2]
  unfold cfA2 cfB2
  rw [if_neg (by omega : ¬ n + 2 = 0), if_neg (by omega : ¬ n + 2 = 1),
    if_neg (by omega : ¬ n + 2 = 0)]
  push_cast
  linear_combination (4 * (2 : ℝ) ^ n) * h

-- no-dlmf: private kit lemma; even-contraction continuant identification
/-- The 7.9.2 numerator continuants are the rescaled even-index 7.9.1 numerator
continuants: `A'ₙ = 2ⁿ A₂ₙ` (seeds `A'₀ = 0 = A₀`, `A'₁ = 2x = 2·A₂`, then the
two-seed uniqueness lemma with the even-contraction recurrence). -/
private lemma cfNum2_eq (x : ℝ) (n : ℕ) :
    cfNum (cfA2 x) (cfB2 x) n = 2 ^ n * cfNum (cfA x) (cfB x) (2 * n) := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence (c := fun n => (2 : ℝ) ^ n)
    (v := fun n => cfNum (cfA x) (cfB x) (2 * n))
    (p := fun n => cfB2 x (n + 2)) (q := fun n => cfA2 x (n + 2)) ?_ ?_ ?_ ?_ n
  · simp [cfNum, cfB2, cfB]
  · norm_num [cfNum, cfA2, cfB2, cfA, cfB]
  · intro k
    simp [cfNum]
  · intro k
    exact cf2_even_step x _ (fun j => by simp [cfNum]) k

-- no-dlmf: private kit lemma; even-contraction continuant identification
/-- The 7.9.2 denominator continuants are the rescaled even-index 7.9.1 denominator
continuants: `B'ₙ = 2ⁿ B₂ₙ` (seeds `B'₀ = 1 = B₀`, `B'₁ = 2x²+1 = 2·B₂`, with the
same recurrence as `cfNum2_eq`). -/
private lemma cfDen2_eq (x : ℝ) (n : ℕ) :
    cfDen (cfA2 x) (cfB2 x) n = 2 ^ n * cfDen (cfA x) (cfB x) (2 * n) := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence (c := fun n => (2 : ℝ) ^ n)
    (v := fun n => cfDen (cfA x) (cfB x) (2 * n))
    (p := fun n => cfB2 x (n + 2)) (q := fun n => cfA2 x (n + 2)) ?_ ?_ ?_ ?_ n
  · simp [cfDen]
  · norm_num [cfDen, cfB2, cfA, cfB]
    ring
  · intro k
    simp [cfDen]
  · intro k
    exact cf2_even_step x _ (fun j => by simp [cfDen]) k

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- The 7.9.2 convergents are exactly the even-index 7.9.1 convergents (the `2ⁿ`
scaling cancels in the quotient): DLMF 7.9.2 is the even part of DLMF 7.9.1. -/
private lemma cfConv2_eq (x : ℝ) (n : ℕ) :
    cfConv (cfA2 x) (cfB2 x) n = cfConv (cfA x) (cfB x) (2 * n) := by
  rw [cfConv, cfConv, cfNum2_eq, cfDen2_eq,
    mul_div_mul_left _ _ (by positivity : ((2 : ℝ) ^ n) ≠ 0)]

-- no-dlmf: real/narrowed restriction of DLMF 7.9.2; faithful surface is erf_7_9_2_complex
/-- Even part of the Laplace continued fraction for `erfc`, stated as the
convergence of its convergents, on the real slice `x > 0` of DLMF 7.9.2.

This is `√π e^{x²} erfc(x) = 2x/(2x² + 1 − 1·2/(2x² + 5 − 3·4/(2x² + 9 − ⋯)))`:
leading numerator `b 0 = 0`, `a 1 = 2x`, `a (k+1) = −(2k−1)(2k)` for `k ≥ 1`, and
denominators `b (k+1) = 2x² + (4k−3)` for `k ≥ 0` (`b 1 = 2x²+1`, `b 2 = 2x²+5`,
…).  The convergents tend to `√π e^{x²} erfc(x)` for `x > 0` (the full-strength
complex statement is `erf_7_9_2_complex`).
-/
theorem erf_7_9_2 (x : ℝ) (hx : 0 < x) :
    Tendsto
      (cfConv
        (fun k => if k = 0 then 0
          else if k = 1 then 2 * x
          else -(2 * (k : ℝ) - 3) * (2 * (k : ℝ) - 2))
        (fun k => if k = 0 then 0 else 2 * x ^ 2 + (4 * (k : ℝ) - 3)))
      atTop (𝓝 (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x)) := by
  have h1 : Tendsto (cfConv (cfA x) (cfB x)) atTop
      (𝓝 (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x)) := erf_7_9_1 x hx
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have hcomp : Tendsto (fun n => cfConv (cfA x) (cfB x) (2 * n)) atTop
      (𝓝 (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x)) := h1.comp h2n
  show Tendsto (cfConv (cfA2 x) (cfB2 x)) atTop _
  have hfun : cfConv (cfA2 x) (cfB2 x) = fun n => cfConv (cfA x) (cfB x) (2 * n) :=
    funext (cfConv2_eq x)
  rw [hfun]
  exact hcomp

/-! ### The even part (DLMF 7.9.2) over `ℂ` -/

-- no-dlmf: complex partial numerators of the DLMF 7.9.2 fraction
/-- Partial numerators of DLMF 7.9.2 over `ℂ` (the `a`-sequence of
`erf_7_9_2_complex`). -/
private noncomputable def cfA2C (z : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k = 1 then 2 * z
    else -(2 * (k : ℂ) - 3) * (2 * (k : ℂ) - 2)

-- no-dlmf: complex partial denominators of the DLMF 7.9.2 fraction
/-- Partial denominators of DLMF 7.9.2 over `ℂ` (the `b`-sequence of
`erf_7_9_2_complex`). -/
private noncomputable def cfB2C (z : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else 2 * z ^ 2 + (4 * (k : ℂ) - 3)

-- no-dlmf: private kit lemma; even-contraction step over `ℂ`
/-- The complex form of `cf2_even_step`: the even contraction of the 7.9.1
Wallis recurrence produces the 7.9.2 partial quantities up to the scaling
`cₙ = 2ⁿ`. -/
private lemma cf2C_even_step (z : ℂ) (u : ℕ → ℂ)
    (hrec : ∀ k, u (k + 2) = cfBC z (k + 2) * u (k + 1) + cfAC z (k + 2) * u k) (n : ℕ) :
    (2 : ℂ) ^ (n + 2) * u (2 * (n + 2)) =
      cfB2C z (n + 2) * ((2 : ℂ) ^ (n + 1) * u (2 * (n + 1)))
        + cfA2C z (n + 2) * ((2 : ℂ) ^ n * u (2 * n)) := by
  have h := FLMF.Methods.wallis_even_contraction hrec n
  have hb2 : cfBC z (2 * n + 2) = 1 := by
    unfold cfBC; rw [if_neg (by omega), if_neg (by omega)]
  have hb3 : cfBC z (2 * n + 3) = z ^ 2 := by
    unfold cfBC; rw [if_neg (by omega), if_pos (by omega)]
  have hb4 : cfBC z (2 * n + 4) = 1 := by
    unfold cfBC; rw [if_neg (by omega), if_neg (by omega)]
  have ha2 : cfAC z (2 * n + 2) = (2 * (n : ℂ) + 1) / 2 := by
    rw [cfAC_val z (by omega)]; push_cast; ring
  have ha3 : cfAC z (2 * n + 3) = (2 * (n : ℂ) + 2) / 2 := by
    rw [cfAC_val z (by omega)]; push_cast; ring
  have ha4 : cfAC z (2 * n + 4) = (2 * (n : ℂ) + 3) / 2 := by
    rw [cfAC_val z (by omega)]; push_cast; ring
  rw [hb2, hb3, hb4, ha2, ha3, ha4] at h
  have e1 : 2 * (n + 2) = 2 * n + 4 := by omega
  have e2 : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [e1, e2]
  unfold cfA2C cfB2C
  rw [if_neg (by omega : ¬ n + 2 = 0), if_neg (by omega : ¬ n + 2 = 1),
    if_neg (by omega : ¬ n + 2 = 0)]
  push_cast
  linear_combination (4 * (2 : ℂ) ^ n) * h

-- no-dlmf: private kit lemma; even-contraction continuant identification over `ℂ`
/-- `A'ₙ = 2ⁿ A₂ₙ` for the numerator continuants (complex form of `cfNum2_eq`). -/
private lemma cfNum2C_eq (z : ℂ) (n : ℕ) :
    cfNumC (cfA2C z) (cfB2C z) n = 2 ^ n * cfNumC (cfAC z) (cfBC z) (2 * n) := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence (c := fun n => (2 : ℂ) ^ n)
    (v := fun n => cfNumC (cfAC z) (cfBC z) (2 * n))
    (p := fun n => cfB2C z (n + 2)) (q := fun n => cfA2C z (n + 2)) ?_ ?_ ?_ ?_ n
  · simp [cfNumC, cfB2C, cfBC]
  · norm_num [cfNumC, cfA2C, cfB2C, cfAC, cfBC]
  · intro k
    simp [cfNumC]
  · intro k
    exact cf2C_even_step z _ (fun j => by simp [cfNumC]) k

-- no-dlmf: private kit lemma; even-contraction continuant identification over `ℂ`
/-- `B'ₙ = 2ⁿ B₂ₙ` for the denominator continuants (complex form of `cfDen2_eq`). -/
private lemma cfDen2C_eq (z : ℂ) (n : ℕ) :
    cfDenC (cfA2C z) (cfB2C z) n = 2 ^ n * cfDenC (cfAC z) (cfBC z) (2 * n) := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence (c := fun n => (2 : ℂ) ^ n)
    (v := fun n => cfDenC (cfAC z) (cfBC z) (2 * n))
    (p := fun n => cfB2C z (n + 2)) (q := fun n => cfA2C z (n + 2)) ?_ ?_ ?_ ?_ n
  · simp [cfDenC]
  · norm_num [cfDenC, cfB2C, cfAC, cfBC]
    ring
  · intro k
    simp [cfDenC]
  · intro k
    exact cf2C_even_step z _ (fun j => by simp [cfDenC]) k

-- no-dlmf: private kit lemma; DLMF 7.9.2 is the even part of DLMF 7.9.1 (complex form)
/-- The 7.9.2 convergents are the even-index 7.9.1 convergents (the `2ⁿ` scaling
cancels in the quotient). -/
private lemma cfConv2C_eq (z : ℂ) (n : ℕ) :
    cfConvC (cfA2C z) (cfB2C z) n = cfConvC (cfAC z) (cfBC z) (2 * n) := by
  rw [cfConvC, cfConvC, cfNum2C_eq, cfDen2C_eq,
    mul_div_mul_left _ _ (pow_ne_zero n (two_ne_zero) : ((2 : ℂ) ^ n) ≠ 0)]

/-- **DLMF 7.9.2** — Even part of the Laplace continued fraction for `erfc`,
for complex `z` with `ℜ z > 0`:
`√π e^{z²} erfc(z) = 2z/(2z² + 1 − 1·2/(2z² + 5 − 3·4/(2z² + 9 − ⋯)))`, stated
as the convergence of its convergents `cfConvC`, with the same `a`/`b`
sequences as `erf_7_9_2` (cast to `ℂ`).

DAG: E-7.9.2.
Numerical: PASS
Verified: verified
-/
theorem erf_7_9_2_complex (z : ℂ) (hz : 0 < z.re) :
    Tendsto
      (cfConvC
        (fun k => if k = 0 then 0
          else if k = 1 then 2 * z
          else -(2 * (k : ℂ) - 3) * (2 * (k : ℂ) - 2))
        (fun k => if k = 0 then 0 else 2 * z ^ 2 + (4 * (k : ℂ) - 3)))
      atTop (𝓝 ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z)) := by
  have h1 : Tendsto (cfConvC (cfAC z) (cfBC z)) atTop
      (𝓝 ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z)) := erf_7_9_1_complex z hz
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have hcomp : Tendsto (fun n => cfConvC (cfAC z) (cfBC z) (2 * n)) atTop
      (𝓝 ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z)) := h1.comp h2n
  show Tendsto (cfConvC (cfA2C z) (cfB2C z)) atTop _
  have hfun : cfConvC (cfA2C z) (cfB2C z) = fun n => cfConvC (cfAC z) (cfBC z) (2 * n) :=
    funext (cfConv2C_eq z)
  rw [hfun]
  exact hcomp

-- 7.9.3 (DEFERRED): continued fraction for the Faddeeva function
--   w(z) = (i/√π) / (z − ½/(z − 1/(z − 3/2/(z − ⋯)))),  ℑ z > 0.
-- The left-hand side is the Faddeeva (plasma-dispersion) function `w(z)`, a
-- COMPLEX-valued function on the upper half-plane (`ℑ z > 0`), with an explicit
-- factor of `i = √(−1)`.  FLMF provides only the real-valued `erf`/`erfc`, and
-- `w` has no faithful real-argument specialization here (on the real axis
-- `w(x) = e^{-x²} + (2i/√π) e^{-x²} ∫₀ˣ e^{t²}` is still genuinely complex).
-- Deferred: needs the complex Faddeeva function `w(z)`, not in FLMF.

end FLMF.Error
