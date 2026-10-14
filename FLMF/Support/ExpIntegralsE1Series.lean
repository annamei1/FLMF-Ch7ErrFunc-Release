import FLMF.Support.ExpIntegralsDefinitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Power-series expansion of the exponential integral `E₁` (DLMF 6.6.2)

Target (`C-e1-series`):
`E₁(x) = −γ − ln x + ∑_{k≥1} (−1)^{k+1} xᵏ / (k·k!)`  for `x > 0`,
where `γ = Real.eulerMascheroniConstant`.

The proof has two independent halves.

* **The integral form** `E1_eq_neg_euler_sub_log_add_ein`:
  `E₁(x) = −γ − ln x + Ein(x)` where `Ein(x) = ∫₀ˣ (1 − e^{−t})/t dt`.
  This is obtained by splitting the Euler integral
  `Γ(s) = ∫₀^∞ e^{−t} t^{s−1} dt` at the point `x`:
  `Γ(s) − 1/s = ∫₀ˣ t^{s−1}(e^{−t}−1) + (xˢ−1)/s + ∫ₓ^∞ t^{s−1} e^{−t}`,
  and letting `s → 0⁺`.  The left side tends to `−γ` (the Laurent constant of `Γ`
  at its simple pole, `gammaSubInv_tendsto`, from `Γ'(1) = −γ`); the three right-hand
  pieces tend to `−Ein(x)`, `ln x`, and `E₁(x)` respectively (two dominated-convergence
  limits plus the elementary slope `(xˢ−1)/s → ln x`).  This is the exponential analog
  of the cosine-integral derivation in `Methods/GammaCosIntegral.lean`, but simpler: the
  Mellin transform is bare `Γ(s)` and the tail is absolutely convergent.

* **The series form** `Ein_eq_tsum`:
  `Ein(x) = ∑_{n≥0} (−1)ⁿ x^{n+1} / ((n+1)·(n+1)!)`, obtained by expanding
  `(1 − e^{−t})/t = ∑_{n≥0} (−1)ⁿ tⁿ/(n+1)!` and integrating termwise (the
  norm-integrals are dominated by `xⁿ⁺¹/(n+1)!`).  Reindexing `k = n+1` gives the
  DLMF form `∑_{k≥1} (−1)^{k+1} xᵏ/(k·k!)`.

Combining the two halves yields the headline theorem `E1_series`.
-/

noncomputable section

open MeasureTheory Real Filter Topology Set intervalIntegral Nat

namespace FLMF.ExpIntegrals.Series

/-- `Ein(x) = ∫₀ˣ (1 − e^{−t})/t dt`, the entire "complementary" exponential
integral (DLMF 6.2.3).  The integrand extends continuously to `1` at `t = 0`.

DLMF 6.2.3.
-/
-- DAG: E-6.2.3.
-- Verified: unverified
def Ein (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, (1 - Real.exp (-t)) / t

/-! ## The Laurent constant of `Γ` at `0` -/

/-- `Γ(s) − 1/s → −γ` as `s → 0⁺`: the constant term of the Laurent expansion of
`Γ` at its simple pole `s = 0`, proven from `Γ'(1) = −γ` via the difference quotient
`Γ(s) − 1/s = (Γ(s+1) − Γ(1))/s`.  (Re-proved here, independently of the cosine file,
to avoid pulling in the contour-rotation machinery.) -/
-- no-dlmf: Laurent-constant limit for Γ supporting the E₁ power series; no DLMF entry of its own
theorem gammaSubInv_tendsto :
    Tendsto (fun s : ℝ => Real.Gamma s - 1 / s) (𝓝[>] 0)
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hderiv : HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) 1 :=
    Real.hasDerivAt_Gamma_one
  have hslope : Tendsto (slope Real.Gamma 1) (𝓝[≠] 1) (𝓝 (-Real.eulerMascheroniConstant)) :=
    hasDerivAt_iff_tendsto_slope.mp hderiv
  have hmap : Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 1) := by
        simpa using (continuous_const.add continuous_id : Continuous (fun s : ℝ => 1 + s)).tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_add_of_pos_right 1 (Set.mem_Ioi.mp hs)).ne'
  have hcomp := hslope.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℝ) ≠ 0 := (Set.mem_Ioi.mp hs).ne'
  rw [Function.comp_apply, slope_def_field, Real.Gamma_one,
    add_sub_cancel_left, show (1 : ℝ) + s = s + 1 from by ring, Real.Gamma_add_one hs0,
    sub_div, mul_comm s (Real.Gamma s), mul_div_assoc, div_self hs0, mul_one]

/-! ## The elementary slope `(xˢ − 1)/s → ln x` -/

/-- `(xˢ − 1)/s → ln x` as `s → 0⁺`, for `x > 0`: the derivative of `s ↦ xˢ` at `s = 0`. -/
-- no-dlmf: elementary slope limit supporting the E₁ power series; no DLMF counterpart
theorem rpow_slope_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => (x ^ s - 1) / s) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have hderiv : HasDerivAt (fun s : ℝ => x ^ s) (Real.log x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => Real.log x * s) (Real.log x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.log x)
    have h2 := h1.exp
    rw [mul_zero, Real.exp_zero, one_mul] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with s using Real.rpow_def_of_pos hx s
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hmap : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_mono_right (by intro u hu; exact (Set.mem_Ioi.mp hu).ne') tendsto_id
  have hcomp := hslope.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Function.comp_apply, slope_def_field, Real.rpow_zero, sub_zero]

/-! ## Continuity of the exponent at a fixed point -/

/-- For `t > 0`, `s ↦ t^{s-1}` is continuous, with limit `t⁻¹` as `s → 0⁺`. -/
-- no-dlmf: continuity/limit helper for the exponent; no DLMF counterpart
theorem tendsto_rpow_exp {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s : ℝ => t ^ (s - 1)) (𝓝[>] 0) (𝓝 (t⁻¹)) := by
  have hcont : Continuous (fun s : ℝ => t ^ (s - 1)) := by
    simp_rw [Real.rpow_def_of_pos ht]; fun_prop
  have h : Tendsto (fun s : ℝ => t ^ (s - 1)) (𝓝[>] 0) (𝓝 (t ^ ((0:ℝ) - 1))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rwa [show t ^ ((0:ℝ) - 1) = t⁻¹ from by rw [zero_sub, Real.rpow_neg_one]] at h

/-! ## The `[0,x]` dominated-convergence limit -/

/-- **The `[0,x]` limit.** `∫₀ˣ t^{s−1}(e^{−t}−1) → ∫₀ˣ (e^{−t}−1)/t` as `s → 0⁺`,
by dominated convergence with the `s`-uniform bound `t^{s−1}|e^{−t}−1| ≤ tˢ ≤ 1 + t`. -/
-- no-dlmf: dominated-convergence piece for the E₁ power-series derivation; no DLMF entry of its own
theorem head_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => ∫ t in (0:ℝ)..x, t ^ (s - 1) * (Real.exp (-t) - 1)) (𝓝[>] 0)
      (𝓝 (∫ t in (0:ℝ)..x, (Real.exp (-t) - 1) / t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => 1 + t)
  · -- measurability
    filter_upwards [self_mem_nhdsWithin] with s _
    refine (ContinuousOn.mul ?_ (by fun_prop)).aestronglyMeasurable measurableSet_uIoc
    refine ContinuousOn.rpow_const continuousOn_id (fun t ht => ?_)
    left
    rw [Set.uIoc_of_le hx.le] at ht
    exact ht.1.ne'
  · -- bound
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with s hs0 hs1
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hx.le] at ht
    have ht0 : 0 < t := ht.1
    have hs0' : 0 < s := hs0
    have hs1' : s < 1 := hs1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hexpabs : |Real.exp (-t) - 1| = 1 - Real.exp (-t) := by
      rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)])]; ring
    rw [hexpabs]
    have hb : 1 - Real.exp (-t) ≤ t := by
      have := Real.add_one_le_exp (-t); linarith
    have hpow : t ^ (s - 1) * t = t ^ s := by
      conv_rhs => rw [show s = (s - 1) + 1 from by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have hts : t ^ s ≤ 1 + t := by
      by_cases htle : t ≤ 1
      · have := Real.rpow_le_one ht0.le htle hs0'.le; linarith
      · have htgt : 1 < t := lt_of_not_ge htle
        have := Real.rpow_le_rpow_of_exponent_le htgt.le hs1'.le
        rw [Real.rpow_one] at this; linarith
    calc t ^ (s - 1) * (1 - Real.exp (-t))
        ≤ t ^ (s - 1) * t := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht0.le _)
      _ = t ^ s := hpow
      _ ≤ 1 + t := hts
  · -- bound integrable
    exact (continuous_const.add continuous_id).intervalIntegrable 0 x
  · -- pointwise limit
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hx.le] at ht
    have ht0 : 0 < t := ht.1
    have hlim := (tendsto_rpow_exp ht0).mul_const (Real.exp (-t) - 1)
    rw [show (Real.exp (-t) - 1) / t = t⁻¹ * (Real.exp (-t) - 1) from by rw [div_eq_inv_mul]]
    exact hlim

/-! ## The tail dominated-convergence limit -/

/-- **The tail limit.** `∫ₓ^∞ e^{−t} t^{s−1} → ∫ₓ^∞ e^{−t}/t = E₁(x)` as `s → 0⁺`,
by dominated convergence with the `s`-uniform bound `t^{s−1} ≤ C := max 1 x⁻¹` for `t ≥ x`. -/
-- no-dlmf: dominated-convergence piece for the E₁ power-series derivation; no DLMF entry of its own
theorem tail_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s : ℝ => ∫ t in Ioi x, Real.exp (-t) * t ^ (s - 1)) (𝓝[>] 0)
      (𝓝 (FLMF.ExpIntegrals.Def.E1 x)) := by
  set C : ℝ := max 1 x⁻¹ with hC
  have hexpint : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi x) := by
    have h := exp_neg_integrableOn_Ioi x (b := 1) one_pos
    refine h.congr ?_
    filter_upwards with t using by rw [neg_one_mul]
  have hboundint : Integrable (fun t : ℝ => C * Real.exp (-t)) (volume.restrict (Ioi x)) :=
    hexpint.const_mul C
  -- value: the limit integral equals `E₁ x`
  have hval : (∫ t in Ioi x, Real.exp (-t) / t) = FLMF.ExpIntegrals.Def.E1 x := by
    rw [FLMF.ExpIntegrals.Def.E1_def]
  rw [← hval]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => C * Real.exp (-t))
  · -- measurability
    filter_upwards [self_mem_nhdsWithin] with s _
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine Real.continuous_exp.comp_continuousOn (by fun_prop) |>.mul ?_
    exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (lt_trans hx ht).ne')
  · -- bound
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with s hs0 hs1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx ht
    have htx : x ≤ t := le_of_lt ht
    have hs1' : s - 1 ≤ 0 := by have : s < 1 := hs1; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h1 : t ^ (s - 1) ≤ x ^ (s - 1) := Real.rpow_le_rpow_of_nonpos hx htx hs1'
    have h2 : x ^ (s - 1) ≤ C := by
      by_cases hx1 : 1 ≤ x
      · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 hs1') (le_max_left _ _)
      · have hx1' : x < 1 := lt_of_not_ge hx1
        have h3 : x ^ (s - 1) ≤ x ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx hx1'.le (by have : (0:ℝ) < s := hs0; linarith)
        rw [Real.rpow_neg_one] at h3
        exact le_trans h3 (le_max_right _ _)
    exact le_trans h1 h2
  · exact hboundint
  · -- pointwise limit
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hx ht
    have hlim := (tendsto_rpow_exp ht0).const_mul (Real.exp (-t))
    rw [show Real.exp (-t) / t = Real.exp (-t) * t⁻¹ from by rw [div_eq_mul_inv]]
    exact hlim

/-! ## The split identity and the integral form -/

/-- For `s > 0` and `x > 0`, the split of the Euler integral at `x`:
`Γ(s) − 1/s = ∫₀ˣ t^{s−1}(e^{−t}−1) + (xˢ − 1)/s + ∫ₓ^∞ e^{−t} t^{s−1}`. -/
-- no-dlmf: Euler-integral split identity used in the E₁ power-series derivation; no DLMF entry of its own
theorem gamma_split {x : ℝ} (hx : 0 < x) {s : ℝ} (hs : 0 < s) :
    Real.Gamma s - 1 / s
      = (∫ t in (0:ℝ)..x, t ^ (s - 1) * (Real.exp (-t) - 1))
        + (x ^ s - 1) / s
        + ∫ t in Ioi x, Real.exp (-t) * t ^ (s - 1) := by
  -- integrability of the Euler integrand on the two pieces
  have hgconv : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hs
  have hint_Ioc : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioc 0 x) :=
    hgconv.mono_set Ioc_subset_Ioi_self
  have hint_Ioi : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioi x) :=
    hgconv.mono_set (Set.Ioi_subset_Ioi hx.le)
  -- split the set integral `∫_{Ioi 0} = ∫_{Ioc 0 x} + ∫_{Ioi x}`
  have hsetsplit : (∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ (s - 1))
      = (∫ t in Ioc (0:ℝ) x, Real.exp (-t) * t ^ (s - 1))
        + ∫ t in Ioi x, Real.exp (-t) * t ^ (s - 1) := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint_Ioc hint_Ioi, Set.Ioc_union_Ioi_eq_Ioi hx.le]
  -- the `Ioc 0 x` part as an interval integral, then split off the divergent `t^{s-1}`
  have hrpowII : IntervalIntegrable (fun t : ℝ => t ^ (s - 1)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hAII : IntervalIntegrable (fun t : ℝ => t ^ (s - 1) * (Real.exp (-t) - 1)) volume 0 x :=
    hrpowII.mul_continuousOn (by fun_prop)
  have hIoc_eq : (∫ t in Ioc (0:ℝ) x, Real.exp (-t) * t ^ (s - 1))
      = (∫ t in (0:ℝ)..x, t ^ (s - 1) * (Real.exp (-t) - 1)) + x ^ s / s := by
    rw [← intervalIntegral.integral_of_le hx.le]
    rw [show (fun t => Real.exp (-t) * t ^ (s - 1))
          = (fun t => t ^ (s - 1) * (Real.exp (-t) - 1) + t ^ (s - 1)) from by ext t; ring,
      intervalIntegral.integral_add hAII hrpowII]
    congr 1
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < s - 1)),
      show s - 1 + 1 = s from by ring, Real.zero_rpow hs.ne', sub_zero]
  -- the Euler integral and assemble
  have hgamma : Real.Gamma s = ∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ (s - 1) := by
    rw [Real.Gamma_eq_integral hs]
  rw [hgamma, hsetsplit, hIoc_eq]
  field_simp
  ring

-- no-dlmf: real/narrowed restriction of DLMF 6.6.2; faithful surface is E1_series_complex
/-- **The integral form.** For `x > 0`,
`E₁(x) = −γ − ln x + Ein(x)`, where `Ein(x) = ∫₀ˣ (1 − e^{−t})/t dt`.
-/
theorem E1_eq_neg_euler_sub_log_add_ein {x : ℝ} (hx : 0 < x) :
    FLMF.ExpIntegrals.Def.E1 x
      = -Real.eulerMascheroniConstant - Real.log x + Ein x := by
  -- the RHS family tends to the limit assembled from the three pieces
  have hRHS : Tendsto (fun s : ℝ =>
      (∫ t in (0:ℝ)..x, t ^ (s - 1) * (Real.exp (-t) - 1))
        + (x ^ s - 1) / s
        + ∫ t in Ioi x, Real.exp (-t) * t ^ (s - 1)) (𝓝[>] 0)
      (𝓝 ((∫ t in (0:ℝ)..x, (Real.exp (-t) - 1) / t)
        + Real.log x + FLMF.ExpIntegrals.Def.E1 x)) :=
    ((head_limit hx).add (rpow_slope_tendsto hx)).add (tail_limit hx)
  -- it agrees eventually with `Γ(s) − 1/s`, which tends to `−γ`
  have hkey : -Real.eulerMascheroniConstant
      = (∫ t in (0:ℝ)..x, (Real.exp (-t) - 1) / t)
        + Real.log x + FLMF.ExpIntegrals.Def.E1 x := by
    refine tendsto_nhds_unique gammaSubInv_tendsto (hRHS.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (gamma_split hx (Set.mem_Ioi.mp hs)).symm
  -- relate the head integral to `Ein`
  have hhead : (∫ t in (0:ℝ)..x, (Real.exp (-t) - 1) / t) = -Ein x := by
    rw [Ein, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← neg_div, neg_sub]
  rw [hhead] at hkey
  linarith [hkey]

/-! ## The power series for `Ein` -/

/-- The pointwise expansion `(1 − e^{−t})/t = ∑_{n≥0} (−1)ⁿ tⁿ/(n+1)!` for `t > 0`. -/
-- no-dlmf: pointwise integrand expansion supporting the E₁ power series; no DLMF entry of its own
theorem ein_integrand_hasTsum {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-t)) / t = ∑' n : ℕ, (-1) ^ n * t ^ n / (n + 1)! := by
  have hsum : Summable (fun n : ℕ => (-t) ^ n / n !) := Real.summable_pow_div_factorial (-t)
  have hexp : Real.exp (-t) = ∑' n : ℕ, (-t) ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- shift the exp series:  ∑ₙ (-t)^{n+1}/(n+1)! = e^{-t} - 1
  have hshift : (∑' n : ℕ, (-t) ^ (n + 1) / (n + 1)!) = Real.exp (-t) - 1 := by
    have h := hsum.tsum_eq_zero_add
    rw [hexp]
    rw [h]
    simp
  -- multiply the target series by `t`
  have hmul : (t * ∑' n : ℕ, (-1) ^ n * t ^ n / (n + 1)!) = 1 - Real.exp (-t) := by
    rw [← tsum_mul_left]
    have hterm : ∀ n : ℕ, t * ((-1) ^ n * t ^ n / (n + 1)!) = -((-t) ^ (n + 1) / (n + 1)!) := by
      intro n
      have hpow : (-t) ^ (n + 1) = -((-1) ^ n * t ^ (n + 1)) := by rw [neg_pow, pow_succ]; ring
      rw [hpow]; ring
    rw [tsum_congr hterm, tsum_neg, hshift]
    ring
  rw [div_eq_iff ht.ne', ← hmul]; ring

-- no-dlmf: real/narrowed restriction of DLMF 6.6.4; faithful surface is Ein_eq_tsum_complex
/-- **The series form.** For `0 ≤ x`,
`Ein(x) = ∑_{n≥0} (−1)ⁿ x^{n+1} / ((n+1)·(n+1)!)`, i.e. the DLMF form
`∑_{n=1}^∞ (−1)^{n-1} zⁿ/(n! n)` after reindexing `n ↦ n+1`.
-/
theorem Ein_eq_tsum {x : ℝ} (hx : 0 ≤ x) :
    Ein x = ∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) := by
  rcases hx.eq_or_lt with rfl | hx0
  · have hz : ∀ n : ℕ, (-1 : ℝ) ^ n * (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) = 0 := by
      intro n; rw [zero_pow (Nat.succ_ne_zero n)]; ring
    rw [Ein, intervalIntegral.integral_same, tsum_congr hz, tsum_zero]
  -- termwise integrands
  set F : ℕ → ℝ → ℝ := fun n t => (-1) ^ n * t ^ n / (n + 1)! with hF
  have hFint : ∀ n : ℕ, IntegrableOn (F n) (Ioc (0:ℝ) x) := by
    intro n
    have hcont : Continuous (F n) := by rw [hF]; fun_prop
    exact hcont.integrableOn_Ioc
  -- norm-integrals are summable, dominated by `x·(xⁿ/n!)`
  have hFsum : Summable fun n : ℕ => ∫ t in Ioc (0:ℝ) x, ‖F n t‖ := by
    have hle : ∀ n : ℕ, ∫ t in Ioc (0:ℝ) x, ‖F n t‖ ≤ x * (x ^ n / n !) := by
      intro n
      have heq : ∀ t ∈ Ioc (0:ℝ) x, ‖F n t‖ = t ^ n / (n + 1)! := by
        intro t ht
        have htpos : 0 < t := ht.1
        have hFt : F n t = (-1) ^ n * (t ^ n / (n + 1)!) := by rw [hF]; ring
        rw [hFt, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      have hnfacpos : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hxnn : (0:ℝ) ≤ x * x ^ n := by positivity
      have hval : ∫ t in Ioc (0:ℝ) x, ‖F n t‖ = x ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) := by
        rw [setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le hx0.le,
          intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
          div_div]
      have hden : (n ! : ℝ) ≤ ((n : ℝ) + 1) * (n + 1)! := by
        have h1 : (n ! : ℝ) ≤ ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ n)
        have h2 : (1:ℝ) ≤ (n : ℝ) + 1 := by have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
        nlinarith [hnfacpos, h1, h2, (by positivity : (0:ℝ) < ((n + 1)! : ℝ))]
      rw [hval, pow_succ, mul_comm (x ^ n) x]
      calc x * x ^ n / (((n : ℝ) + 1) * (n + 1)!)
          ≤ x * x ^ n / (n ! : ℝ) := div_le_div_of_nonneg_left hxnn hnfacpos hden
        _ = x * (x ^ n / n !) := by ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hle
      ((Real.summable_pow_div_factorial x).mul_left _)
  -- interchange
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum
  -- pointwise sum on `Ioc 0 x`
  have hpt : ∀ t ∈ Ioc (0:ℝ) x, (1 - Real.exp (-t)) / t = ∑' n : ℕ, F n t := by
    intro t ht
    simp only [hF]; exact ein_integrand_hasTsum ht.1
  -- assemble
  rw [Ein, intervalIntegral.integral_of_le hx0.le,
    setIntegral_congr_fun measurableSet_Ioc hpt, ← hswap]
  refine tsum_congr (fun n => ?_)
  rw [show (∫ t in Ioc (0:ℝ) x, F n t) = ∫ t in (0:ℝ)..x, F n t from
    (intervalIntegral.integral_of_le hx0.le).symm]
  simp only [hF]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  have hnpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hfacne : ((n + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-! ## Complex-domain surface (DLMF 6.6.4 at full strength) -/

/-- **DLMF 6.6.4** — the entire power-series expansion of the complementary
exponential integral for complex `z`, no constraint:
`Ein(z) = ∑_{n≥0} (−1)ⁿ z^{n+1} / ((n+1)·(n+1)!)`, i.e. the DLMF form
`∑_{n=1}^∞ (−1)^{n-1} zⁿ/(n! n)` after reindexing `n ↦ n+1`.  Here `Ein(z)` is
realized by the entire complex integral `∫₀¹ (1 − e^{−zt})/t dt` (DLMF 6.2.3
after the substitution `t ↦ zt`), which agrees with the real `Ein` at `z = x`.

DAG: E-6.6.4.
Numerical: PASS
Verified: verified
-/
theorem Ein_eq_tsum_complex (z : ℂ) :
    (∫ t in (0 : ℝ)..1, (1 - Complex.exp (-(z * (t : ℂ)))) / (t : ℂ))
      = ∑' n : ℕ, (-1 : ℂ) ^ n * z ^ (n + 1) / (((n : ℂ) + 1) * (n + 1)!) := by
  sorry

/-! ## The headline theorem -/

-- no-dlmf: real/narrowed restriction of DLMF 6.6.2; faithful surface is E1_series_complex
/-- The power-series expansion of the exponential integral `E₁`:
for `x > 0`,
`E₁(x) = −γ − ln x + ∑_{n≥0} (−1)ⁿ x^{n+1} / ((n+1)·(n+1)!)`.
Reindexing `k = n+1`, the sum is the classical `∑_{k≥1} (−1)^{k+1} xᵏ/(k·k!)`.
-/
theorem E1_series {x : ℝ} (hx : 0 < x) :
    FLMF.ExpIntegrals.Def.E1 x
      = -Real.eulerMascheroniConstant - Real.log x
        + ∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) := by
  rw [E1_eq_neg_euler_sub_log_add_ein hx, Ein_eq_tsum hx.le]

/-! ## Complex-domain surface (DLMF 6.6.2 at full strength) -/

/-- **DLMF 6.6.2** — the power-series expansion of the exponential integral `E₁`
for complex `z`, no constraint, on the principal branch of `ln`:
`E₁(z) = −γ − ln z − ∑_{n=1}^∞ (−1)ⁿ zⁿ/(n!·n)`.  Here `E₁(z)` is realized via
DLMF 6.2.4, `E₁(z) = Ein(z) − ln z − γ`, with the entire `Ein(z)` of
`Ein_eq_tsum_complex`.

DAG: E-6.6.2.
Numerical: PASS
Verified: unverified
-/
theorem E1_series_complex (z : ℂ) :
    (∫ t in (0 : ℝ)..1, (1 - Complex.exp (-(z * (t : ℂ)))) / (t : ℂ))
        - Complex.log z - (Real.eulerMascheroniConstant : ℂ)
      = -(Real.eulerMascheroniConstant : ℂ) - Complex.log z
        + ∑' n : ℕ, (-1 : ℂ) ^ n * z ^ (n + 1) / (((n : ℂ) + 1) * (n + 1)!) := by
  rw [Ein_eq_tsum_complex]
  ring

end FLMF.ExpIntegrals.Series

namespace FLMF.ExpIntegrals.Def

-- no-dlmf: real/narrowed restriction of DLMF 6.6.2 in `eiSeries` form (the tagged
-- 6.6.1 is the `Ei(x) = γ + ln x + ∑ xⁿ/(n!n)` series, which is the `Ei`
-- *definition* in `Definitions.lean`, not this `E₁` identity); the faithful 6.6.2
-- surface is `Series.E1_series_complex`.
/-- The convergent-series expansion of the exponential integral
`E₁(x) = -γ - ln x - eiSeries(-x)` for `x > 0`, in terms of the `eiSeries`
abbreviation of `Definitions`.  Equivalent to `Series.E1_series`: the alternating
sum `∑_{k≥0} (-1)ᵏ x^{k+1}/((k+1)(k+1)!)` is exactly `-eiSeries(-x)`.
-/
theorem E1_series {x : ℝ} (hx : 0 < x) :
    E1 x = -Real.eulerMascheroniConstant - Real.log x - eiSeries (-x) := by
  rw [FLMF.ExpIntegrals.Series.E1_series hx]
  have hneg : eiSeries (-x)
      = -∑' n : ℕ, (-1) ^ n * x ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) := by
    rw [eiSeries, ← tsum_neg]
    refine tsum_congr (fun n => ?_)
    have h1 : (-x) ^ (n + 1) = -((-1 : ℝ) ^ n * x ^ (n + 1)) := by
      rw [show (-x) = (-1 : ℝ) * x from by ring, mul_pow, pow_succ]; ring
    rw [h1]; ring
  rw [hneg]; ring

-- no-dlmf: chain link 6.2.6 (assembled in expint_6_2_6)
/-- `Ei(-x) = -E₁(x)` for `x > 0`, where both sides are honest convergent
values.  Direct consequence of the series forms of `Ei` (`Ei_def`) and `E₁` (`E1_series`).
-/
theorem Ei_neg_eq_neg_E1 {x : ℝ} (hx : 0 < x) : Ei (-x) = -E1 x := by
  rw [Ei_def, E1_series hx, abs_neg, abs_of_pos hx]; ring

-- no-dlmf: reparametrized corollary of DLMF 6.2.6 (substitute x ↦ -x into the
-- faithful surface `Ei_neg_eq_neg_E1`); not itself a fresh rendering of the
-- DLMF equation
/-- `Ei(x) = -E₁(-x)` for `x < 0` (apply `Ei_neg_eq_neg_E1` at `-x`). -/
theorem Ei_eq_neg_E1_neg {x : ℝ} (hx : x < 0) : Ei x = -E1 (-x) := by
  have := Ei_neg_eq_neg_E1 (x := -x) (by linarith); rwa [neg_neg] at this

-- no-dlmf: reparametrized corollary of DLMF 6.2.6 (equivalent restatement of
-- `Ei_neg_eq_neg_E1`); the chain conjunction is `expint_6_2_6`
/-- Equivalently, `E₁(x) = -Ei(-x)` for `x > 0`. -/
theorem E1_eq_neg_Ei_neg {x : ℝ} (hx : 0 < x) : E1 x = -Ei (-x) := by
  rw [Ei_neg_eq_neg_E1 hx, neg_neg]

/-- **DLMF 6.2.6.** `Ei(-x) = -∫_x^∞ e^{-t}/t dt = -E₁(x)` for `x > 0`: the
tail-integral representation of `Ei(-x)` (via `E1`'s own defining integral),
and the resulting bridge to `E₁`.

DLMF 6.2.6.
DAG: E-6.2.6.
Numerical: PASS
Verified: unverified
-/
theorem expint_6_2_6 {x : ℝ} (hx : 0 < x) :
    Ei (-x) = -(∫ t in Ioi x, Real.exp (-t) / t)
      ∧ -(∫ t in Ioi x, Real.exp (-t) / t) = -E1 x :=
  ⟨by rw [Ei_neg_eq_neg_E1 hx, E1_def], by rw [E1_def]⟩

/-- Pointwise expansion `(e^t − 1)/t = ∑_{n≥0} tⁿ/(n+1)!` for `t > 0`. -/
-- no-dlmf: positive-exponential integrand expansion, companion to `ein_integrand_hasTsum`
private theorem exp_sub_one_integrand_hasTsum {t : ℝ} (ht : 0 < t) :
    (Real.exp t - 1) / t = ∑' n : ℕ, t ^ n / (n + 1)! := by
  have hsum : Summable (fun n : ℕ => t ^ n / n !) := Real.summable_pow_div_factorial t
  have hexp : Real.exp t = ∑' n : ℕ, t ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hshift : (∑' n : ℕ, t ^ (n + 1) / (n + 1)!) = Real.exp t - 1 := by
    have h := hsum.tsum_eq_zero_add
    rw [hexp, h]; simp
  have hmul : t * (∑' n : ℕ, t ^ n / (n + 1)!) = Real.exp t - 1 := by
    rw [← tsum_mul_left]
    have hterm : ∀ n : ℕ, t * (t ^ n / (n + 1)!) = t ^ (n + 1) / (n + 1)! := by
      intro n; rw [pow_succ]; ring
    rw [tsum_congr hterm, hshift]
  rw [div_eq_iff ht.ne', ← hmul]; ring

/-- `∫₀ˣ (e^t − 1)/t dt = eiSeries x` for `x ≥ 0`.  Termwise integration of the
power series `(e^t − 1)/t = ∑ₙ tⁿ/(n+1)!`. -/
-- no-dlmf: series/finite-integral bridge used in the DLMF 6.2.5 principal-value proof
private theorem integral_exp_sub_one_div_eq_eiSeries {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, (Real.exp t - 1) / t) = eiSeries x := by
  rcases hx.eq_or_lt with rfl | hx0
  · have hz : ∀ n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) = 0 := by
      intro n; rw [zero_pow (Nat.succ_ne_zero n)]; ring
    rw [intervalIntegral.integral_same, eiSeries, tsum_congr hz, tsum_zero]
  set F : ℕ → ℝ → ℝ := fun n t => t ^ n / (n + 1)! with hF
  have hFint : ∀ n : ℕ, IntegrableOn (F n) (Ioc (0 : ℝ) x) := by
    intro n
    have hcont : Continuous (F n) := by rw [hF]; fun_prop
    exact hcont.integrableOn_Ioc
  have hFsum : Summable fun n : ℕ => ∫ t in Ioc (0 : ℝ) x, ‖F n t‖ := by
    have hle : ∀ n : ℕ, ∫ t in Ioc (0 : ℝ) x, ‖F n t‖ ≤ x * (x ^ n / n !) := by
      intro n
      have heq : ∀ t ∈ Ioc (0 : ℝ) x, ‖F n t‖ = t ^ n / (n + 1)! := by
        intro t ht
        have htpos : 0 < t := ht.1
        have hFt : F n t = t ^ n / (n + 1)! := by rw [hF]
        rw [hFt, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hnfacpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hxnn : (0 : ℝ) ≤ x * x ^ n := by positivity
      have hval : ∫ t in Ioc (0 : ℝ) x, ‖F n t‖
          = x ^ (n + 1) / (((n : ℝ) + 1) * (n + 1)!) := by
        rw [setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le hx0.le,
          intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
          div_div]
      have hden : (n ! : ℝ) ≤ ((n : ℝ) + 1) * (n + 1)! := by
        have h1 : (n ! : ℝ) ≤ ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ n)
        have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
        nlinarith [hnfacpos, h1, h2, (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
      rw [hval, pow_succ, mul_comm (x ^ n) x]
      calc x * x ^ n / (((n : ℝ) + 1) * (n + 1)!)
          ≤ x * x ^ n / (n ! : ℝ) := div_le_div_of_nonneg_left hxnn hnfacpos hden
        _ = x * (x ^ n / n !) := by ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hle
      ((Real.summable_pow_div_factorial x).mul_left _)
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum
  have hpt : ∀ t ∈ Ioc (0 : ℝ) x, (Real.exp t - 1) / t = ∑' n : ℕ, F n t := by
    intro t ht
    simp only [hF]
    exact exp_sub_one_integrand_hasTsum ht.1
  rw [intervalIntegral.integral_of_le hx0.le,
    setIntegral_congr_fun measurableSet_Ioc hpt, ← hswap, eiSeries]
  refine tsum_congr (fun n => ?_)
  rw [show (∫ t in Ioc (0 : ℝ) x, F n t) = ∫ t in (0 : ℝ)..x, F n t from
    (intervalIntegral.integral_of_le hx0.le).symm]
  simp only [hF]
  rw [intervalIntegral.integral_div, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  have hnpos : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hfacne : ((n + 1)! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- `(e^t − 1)/t` is interval-integrable on `[a, b]` when `0 < a` and `0 < b`. -/
-- no-dlmf: integrability infrastructure for the DLMF 6.2.5 principal-value proof
private theorem intervalIntegrable_exp_sub_one_div_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => (Real.exp t - 1) / t) volume a b := by
  refine (ContinuousOn.div ?_ continuousOn_id ?_).intervalIntegrable
  · fun_prop
  · intro t ht
    rcases mem_uIcc.mp ht with ⟨hat, _⟩ | ⟨hbt, _⟩
    · exact (lt_of_lt_of_le ha hat).ne'
    · exact (lt_of_lt_of_le hb hbt).ne'

/-- `(e^t − 1)/t` is interval-integrable on `[0, b]` (removable singularity at 0). -/
-- no-dlmf: integrability infrastructure for the DLMF 6.2.5 principal-value proof
private theorem intervalIntegrable_exp_sub_one_div_zero {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.exp t - 1) / t) volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  have hcont : Continuous (dslope Real.exp 0) := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope (f := Real.exp) (a := 0) (s := Set.univ) (by simp)).2
      ⟨Real.continuous_exp.continuousOn, (Real.hasDerivAt_exp 0).differentiableAt⟩
  refine (hcont.integrableOn_Ioc (a := 0) (b := b) (μ := volume)).congr_fun ?_
    measurableSet_Ioc
  intro t ht
  have ht0 : t ≠ 0 := ht.1.ne'
  rw [dslope_of_ne Real.exp ht0, slope_def_field, Real.exp_zero, sub_zero]

/-- `eiSeries` tends to `0 = eiSeries 0` as its argument tends to `0`.  Continuity of
the entire power series at the origin, via the bound `|eiSeries y| ≤ e^{|y|} − 1`. -/
-- no-dlmf: continuity infrastructure for the DLMF 6.2.5 principal-value proof
private theorem eiSeries_tendsto_zero :
    Tendsto eiSeries (𝓝 0) (𝓝 0) := by
  -- for every `y`, `|eiSeries y| ≤ e^{|y|} - 1`
  have hbound : ∀ y : ℝ, ‖eiSeries y‖ ≤ Real.exp |y| - 1 := by
    intro y
    -- termwise: `|y^{k+1}/((k+1)(k+1)!)| ≤ |y|^{k+1}/(k+1)!`
    have hle : ∀ k : ℕ,
        ‖y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖
          ≤ |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
      intro k
      have hfac : (0:ℝ) < (Nat.factorial (k + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hden : (Nat.factorial (k + 1) : ℝ) ≤ ((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) k, hfac]
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k : ℝ) + 1)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.factorial (k + 1) : ℝ))]
      have hnum : (0:ℝ) ≤ |y| ^ (k + 1) := by positivity
      exact div_le_div_of_nonneg_left hnum hfac hden
    have hbase : Summable (fun k : ℕ => |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) :=
      (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial |y|)
    have hsummable : Summable
        (fun k : ℕ => y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))) :=
      Summable.of_norm_bounded hbase hle
    have hexpsum : Real.exp |y| = ∑' k : ℕ, |y| ^ k / (Nat.factorial k : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hexpshift : (∑' k : ℕ, |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) = Real.exp |y| - 1 := by
      have h := (Real.summable_pow_div_factorial |y|).tsum_eq_zero_add
      rw [hexpsum, h]; simp
    rw [eiSeries]
    calc ‖∑' k : ℕ, y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖
          ≤ ∑' k : ℕ, ‖y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖ :=
            norm_tsum_le_tsum_norm hsummable.norm
      _ ≤ ∑' k : ℕ, |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) :=
            Summable.tsum_le_tsum hle hsummable.norm hbase
      _ = Real.exp |y| - 1 := hexpshift
  -- `e^{|y|} - 1 → 0` as `y → 0`
  have hexp : Tendsto (fun y : ℝ => Real.exp |y| - 1) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun y : ℝ => Real.exp |y| - 1) := by fun_prop
    have := hc.tendsto 0
    simpa using this
  exact squeeze_zero_norm hbound hexp

-- no-dlmf: chain link 6.2.5 (assembled in expint_6_2_5); the forward PV form
-- `Ei(x) = pv∫_{-∞}^x e^t/t dt`
/-- The Cauchy principal-value integral representation of `Ei` for `x > 0`:
`Ei(x) = PV ∫_{-∞}^x e^t/t dt`.  Concretely, as `ε → 0⁺` the symmetrically
excised integral `∫_{-∞}^{-ε} e^t/t dt + ∫_ε^x e^t/t dt` tends to `Ei(x)` — the path
through the pole at `t = 0` taken as a principal value.
-/
theorem expint_6_2_5_forward {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ =>
        (∫ t in Iic (-ε), Real.exp t / t) + (∫ t in (ε)..x, Real.exp t / t))
      (𝓝[>] 0) (𝓝 (Ei x)) := by
  -- On the eventual set `0 < ε < x`, rewrite the excised integral in closed form.
  have hev : (fun ε : ℝ =>
        (∫ t in Iic (-ε), Real.exp t / t) + (∫ t in (ε)..x, Real.exp t / t))
      =ᶠ[𝓝[>] 0]
      (fun ε : ℝ =>
        (Real.eulerMascheroniConstant + Real.log x + eiSeries (-ε))
          + (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t)
          - (∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t)) := by
    filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεx : ε < x := hε.2
    -- first summand: `∫_{Iic (-ε)} e^t/t = -E1 ε = γ + log ε + eiSeries (-ε)`
    have hfirst : (∫ t in Iic (-ε), Real.exp t / t)
        = Real.eulerMascheroniConstant + Real.log ε + eiSeries (-ε) := by
      rw [integral_Iic_exp_div_eq_neg_E1 ε, E1_series hε0]; ring
    -- second summand: split `e^t/t = (e^t-1)/t + 1/t`
    have hII1 : IntervalIntegrable (fun t : ℝ => (Real.exp t - 1) / t) volume ε x :=
      intervalIntegrable_exp_sub_one_div_pos hε0 (lt_trans hε0 hεx)
    have hII2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume ε x := by
      refine (ContinuousOn.div continuousOn_const continuousOn_id ?_).intervalIntegrable
      intro t ht
      rcases mem_uIcc.mp ht with ⟨hat, _⟩ | ⟨hbt, _⟩
      · exact (lt_of_lt_of_le hε0 hat).ne'
      · exact (lt_of_lt_of_le (lt_trans hε0 hεx) hbt).ne'
    have hsplit : (∫ t in (ε)..x, Real.exp t / t)
        = (∫ t in (ε)..x, (Real.exp t - 1) / t) + (Real.log x - Real.log ε) := by
      have hcongr : (∫ t in (ε)..x, Real.exp t / t)
          = ∫ t in (ε)..x, ((Real.exp t - 1) / t + 1 / t) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        have ht0 : t ≠ 0 := by
          rcases mem_uIcc.mp ht with ⟨hat, _⟩ | ⟨hbt, _⟩
          · exact (lt_of_lt_of_le hε0 hat).ne'
          · exact (lt_of_lt_of_le (lt_trans hε0 hεx) hbt).ne'
        field_simp [ht0]; ring
      rw [hcongr, intervalIntegral.integral_add hII1 hII2]
      congr 1
      rw [integral_one_div_of_pos hε0 (lt_trans hε0 hεx), Real.log_div (lt_trans hε0 hεx).ne' hε0.ne']
    -- split `∫_ε^x = ∫_0^x - ∫_0^ε` for the `(e^t-1)/t` piece
    have hadd : (∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t)
        + (∫ t in (ε)..x, (Real.exp t - 1) / t)
        = (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t) :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_exp_sub_one_div_zero hε0.le) hII1
    rw [hfirst, hsplit]
    linarith [hadd]
  refine Tendsto.congr' hev.symm ?_
  -- `eiSeries (-ε) → 0`
  have hlim1 : Tendsto (fun ε : ℝ => eiSeries (-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by
      have hc : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
        have := (continuous_neg.tendsto (0:ℝ)); simpa using this
      exact hc.mono_left nhdsWithin_le_nhds
    exact eiSeries_tendsto_zero.comp hneg
  -- `∫_0^ε (e^t-1)/t = eiSeries ε → 0` as `ε → 0⁺`
  have hlim2 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t) (𝓝[>] 0) (𝓝 0) := by
    have hcongr : (fun ε : ℝ => ∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t)
        =ᶠ[𝓝[>] 0] (fun ε : ℝ => eiSeries ε) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact integral_exp_sub_one_div_eq_eiSeries (le_of_lt hε)
    refine Tendsto.congr' hcongr.symm ?_
    exact eiSeries_tendsto_zero.mono_left nhdsWithin_le_nhds
  -- the constant part tends to `Ei x`
  have hconst : Real.eulerMascheroniConstant + Real.log x
      + (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t) = Ei x := by
    rw [integral_exp_sub_one_div_eq_eiSeries hx.le, Ei_def, abs_of_pos hx]
  have hfin : Tendsto (fun ε : ℝ =>
        (Real.eulerMascheroniConstant + Real.log x + eiSeries (-ε))
          + (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t)
          - (∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t))
      (𝓝[>] 0) (𝓝 (Ei x)) := by
    have : Tendsto (fun ε : ℝ =>
        (Real.eulerMascheroniConstant + Real.log x + eiSeries (-ε))
          + (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t)
          - (∫ t in (0:ℝ)..ε, (Real.exp t - 1) / t))
      (𝓝[>] 0)
      (𝓝 ((Real.eulerMascheroniConstant + Real.log x + 0)
          + (∫ t in (0:ℝ)..x, (Real.exp t - 1) / t) - 0)) := by
      exact (((tendsto_const_nhds.add hlim1).add tendsto_const_nhds).sub hlim2)
    simpa [← hconst] using this
  exact hfin

-- no-dlmf: chain link 6.2.5 (assembled in expint_6_2_5); the backward PV form
-- `Ei(x) = -pv∫_{-x}^∞ e^{-t}/t dt`, obtained from `expint_6_2_5_forward` by the
-- change of variables `t ↦ -t` (`intervalIntegral.integral_comp_neg` on the finite
-- piece, `integral_Iic_exp_div_eq_neg_E1`/`E1_def` on the tail piece)
/-- The Cauchy principal-value integral representation `Ei(x) = -PV ∫_{-x}^∞
e^{-t}/t dt` for `x > 0`: as `δ → 0⁺` the symmetrically excised integral
`∫_{-x}^{-δ} e^{-t}/t dt + ∫_δ^∞ e^{-t}/t dt` tends to `-Ei(x)`.
-/
theorem expint_6_2_5_backward {x : ℝ} (hx : 0 < x) :
    Tendsto (fun δ : ℝ =>
        (∫ t in (-x)..(-δ), Real.exp (-t) / t) + (∫ t in Ioi δ, Real.exp (-t) / t))
      (𝓝[>] 0) (𝓝 (-(Ei x))) := by
  have hneg := (expint_6_2_5_forward hx).neg
  refine hneg.congr (fun δ => ?_)
  have hpiece1 : (∫ t in (-x)..(-δ), Real.exp (-t) / t)
      = -(∫ t in δ..x, Real.exp t / t) := by
    have h := intervalIntegral.integral_comp_neg (f := fun t : ℝ => Real.exp (-t) / t)
      (a := δ) (b := x)
    simp only [neg_neg] at h
    rw [← h, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    field_simp
  have hpiece2 : (∫ t in Ioi δ, Real.exp (-t) / t) = FLMF.ExpIntegrals.Def.E1 δ :=
    (FLMF.ExpIntegrals.Def.E1_def δ).symm
  have hpiece3 : (∫ t in Iic (-δ), Real.exp t / t) = -FLMF.ExpIntegrals.Def.E1 δ :=
    FLMF.ExpIntegrals.Def.integral_Iic_exp_div_eq_neg_E1 δ
  rw [hpiece1, hpiece2, neg_add, hpiece3]
  ring

/-- **DLMF 6.2.5.** The Cauchy principal-value integral representation of `Ei` for
`x > 0`: `Ei(x) = -PV ∫_{-x}^∞ e^{-t}/t dt = PV ∫_{-∞}^x e^t/t dt`.

DLMF 6.2.5.
DAG: E-6.2.5.
Numerical: PASS
Verified: verified
-/
theorem expint_6_2_5 {x : ℝ} (hx : 0 < x) :
    Tendsto (fun δ : ℝ =>
        (∫ t in (-x)..(-δ), Real.exp (-t) / t) + (∫ t in Ioi δ, Real.exp (-t) / t))
        (𝓝[>] 0) (𝓝 (-(Ei x)))
      ∧ Tendsto (fun ε : ℝ =>
        (∫ t in Iic (-ε), Real.exp t / t) + (∫ t in (ε)..x, Real.exp t / t))
        (𝓝[>] 0) (𝓝 (Ei x)) :=
  ⟨expint_6_2_5_backward hx, expint_6_2_5_forward hx⟩

/-- The unified series definition of `Ei` agrees with its (proper) Lebesgue integral
representation `Ei(x) = ∫_{-∞}^x e^t/t dt` for `x < 0`, where the integral is absolutely
convergent (the path avoids the pole at `t = 0`).  Internal consistency check that the
series definition loses nothing on the integral's convergent domain; the DLMF 6.2.5
principal-value statement (for `x > 0`) is `expint_6_2_5` above. -/
-- no-dlmf: x<0 proper-integral consistency lemma for `Ei`; DLMF 6.2.5 is `expint_6_2_5`
theorem Ei_eq_integral_Iic {x : ℝ} (hx : x < 0) :
    Ei x = ∫ t in Iic x, Real.exp t / t := by
  rw [Ei_eq_neg_E1_neg hx]
  have h := integral_Iic_exp_div_eq_neg_E1 (-x)
  rw [neg_neg] at h
  exact h.symm

end FLMF.ExpIntegrals.Def
