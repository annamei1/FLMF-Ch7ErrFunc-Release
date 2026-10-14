import FLMF.Chapter7.Erf
import FLMF.Chapter7.Definitions
import FLMF.Support.LaplaceTransform
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Laplace transform of `erf(√(bt))`, through `Methods.LaplaceTransform` (DLMF 7.14.3)

**Anchor for M-laplace-transform.** DLMF 7.14.3
(`∫₀^∞ e^{-at} erf(√(bt)) dt = (1/a)√(b/(a+b))`) is proven here *through* the
Laplace module's own operational vocabulary
(`FLMF.Methods.LaplaceTransform.laplaceTransform`,
`laplaceTransform_deriv` — DLMF 1.14.27), rather than by a direct
`Ioi`-integration-by-parts argument on the real integrand:

* `laplaceTransform_erf_sqrt_eq_ofReal` bridges the complex `laplaceTransform`
  of the `ℂ`-cast of `erf(√(bt))` to the real integral.
* `hasDerivAt_fC` supplies the `t`-derivative of `erf(√(bt))` (cast to `ℂ` via
  `HasDerivAt.ofReal_comp`), reusing `hasDerivAt_erf` from `Erf.lean`.
* `laplaceTransform_deriv_fC` invokes `laplaceTransform_deriv` itself: the
  identity `a·L[erf(√(b·))](a) - erf(√(b·0)) = L[f'](a)` where `f'` is the
  derivative kernel above — this is the genuine consumption of the module's
  derivative rule (DLMF 1.14.27), not a re-derivation of it.
* `laplaceTransform_fC'_eq` evaluates `L[f'](a)` via the same real Gamma-
  integral core (`Real.integral_rpow_mul_exp_neg_mul_Ioi`) the original proof
  used, but now only for the *derivative* kernel, feeding into the module's
  algebraic identity rather than a direct IBP of the original integrand.
* `laplaceTransform_erf_sqrt` solves the resulting linear equation in
  `L[erf(√(b·))](a)` for the closed form, and `erf_7_14_3` (in
  `Ch7Integrals.lean`) is now a corollary of it via the bridge.
-/

namespace FLMF.Error

open MeasureTheory Real Set Filter FLMF.Methods.LaplaceTransform
open scoped Real Topology

/-- Bridge: `laplaceTransform (fun t => (erf (√(bt)) : ℂ)) (a:ℂ)` equals the cast
of the real integral, for real `a`, `b`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem laplaceTransform_erf_sqrt_eq_ofReal (a b : ℝ) :
    laplaceTransform (fun t => (erf (Real.sqrt (b * t)) : ℂ)) (a : ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * erf (Real.sqrt (b*t))) : ℝ) := by
  simp only [laplaceTransform]
  have hcongr : ∀ t : ℝ, Complex.exp (-(a:ℂ) * (t:ℂ)) * (erf (Real.sqrt (b*t)) : ℂ)
      = ((Real.exp (-a*t) * erf (Real.sqrt (b*t)) : ℝ) : ℂ) := by
    intro t
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
  exact _root_.integral_ofReal

/-- Complex `f` for the bridge: `f t = (erf (√(bt)) : ℂ)`. -/
-- no-dlmf: Laplace-module bridging definition for 7.14.3, no independent DLMF number
noncomputable def fC (b : ℝ) : ℝ → ℂ := fun t => (erf (Real.sqrt (b * t)) : ℂ)

/-- Complex derivative kernel `f' t = (2/√π) e^{-bt} (√b / (2√t))`, cast from the
real derivative computed by `hasDerivAt_erf` composed with `√(b·)`. -/
-- no-dlmf: Laplace-module bridging definition for 7.14.3, no independent DLMF number
noncomputable def fC' (b : ℝ) : ℝ → ℂ :=
  fun t => (((2 / Real.sqrt Real.pi) * Real.exp (-(b * t)) * (Real.sqrt b / (2 * Real.sqrt t))) : ℂ)

-- no-dlmf: derivative helper feeding `laplaceTransform_deriv`, no independent DLMF number
theorem hasDerivAt_fC (b : ℝ) (hb : 0 < b) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fC b) (fC' b t) t := by
  show HasDerivAt (fun t => (erf (Real.sqrt (b * t)) : ℂ))
    (((2 / Real.sqrt Real.pi) * Real.exp (-(b * t)) * (Real.sqrt b / (2 * Real.sqrt t))) : ℂ) t
  have hbt : HasDerivAt (fun t : ℝ => b * t) b t := by
    simpa using (hasDerivAt_id t).const_mul b
  have hbtne : b * t ≠ 0 := ne_of_gt (mul_pos hb ht)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (b * t))
      (1 / (2 * Real.sqrt (b * t)) * b) t :=
    (Real.hasDerivAt_sqrt hbtne).comp t hbt
  have herf := (hasDerivAt_erf (Real.sqrt (b * t))).comp t hsqrt
  have hrw : (2 / Real.sqrt Real.pi) * Real.exp (-(Real.sqrt (b * t)) ^ 2)
      * (1 / (2 * Real.sqrt (b * t)) * b)
      = (2 / Real.sqrt Real.pi) * Real.exp (-(b * t)) * (Real.sqrt b / (2 * Real.sqrt t)) := by
    have hsqBt : (Real.sqrt (b * t)) ^ 2 = b * t := Real.sq_sqrt (by positivity)
    rw [hsqBt]
    have hsqrtbt : Real.sqrt (b * t) = Real.sqrt b * Real.sqrt t :=
      Real.sqrt_mul hb.le t
    have hsb : Real.sqrt b ≠ 0 := Real.sqrt_ne_zero'.mpr hb
    have hst : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
    have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    rw [hsqrtbt]
    field_simp
    nlinarith [hsqb]
  rw [hrw] at herf
  simpa [Function.comp] using herf.ofReal_comp

/-- `laplaceTransform (fC' b) (a:ℂ)` equals the cast of the real Gamma-integral
`∫ t^{-1/2} e^{-(a+b)t} = (√π)/√(a+b)`, scaled by `√b/(a√π)`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem laplaceTransform_fC'_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    laplaceTransform (fC' b) (a : ℂ)
      = ((Real.sqrt b / Real.sqrt (a + b) : ℝ) : ℂ) := by
  have hab : 0 < a + b := by linarith
  have hgamma_int : IntegrableOn
      (fun t : ℝ => t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))) (Ioi (0:ℝ)) := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) (Ioi (0:ℝ)) := by
      have h0 := Real.GammaIntegral_convergent (by norm_num : (0:ℝ) < 1/2)
      refine h0.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioi
    have hscaled : IntegrableOn
        (fun t : ℝ => ((a + b) * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))
        (Ioi (0:ℝ)) := by
      have h := (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) 0 hab).mpr (by simpa using hbase)
      simpa using h
    have hcm : IntegrableOn
        (fun t : ℝ => (a + b) ^ (-(1/2 : ℝ) + 1) *
          (((a + b) * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))) (Ioi (0:ℝ)) :=
      hscaled.const_mul _
    refine hcm.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [Real.mul_rpow hab.le ht.le]
    have hconst : (a + b) ^ (-(1/2 : ℝ) + 1) * (a + b) ^ ((1/2 : ℝ) - 1) = 1 := by
      rw [← Real.rpow_add hab]
      norm_num
    calc (a + b) ^ (-(1/2 : ℝ) + 1)
            * ((a + b) ^ ((1/2 : ℝ) - 1) * t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))
        = ((a + b) ^ (-(1/2 : ℝ) + 1) * (a + b) ^ ((1/2 : ℝ) - 1))
            * (t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))) := by ring
      _ = t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)) := by rw [hconst]; ring
  have hgamma_val : ∫ t in Ioi (0:ℝ), t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))
      = (1 / (a + b)) ^ (1/2 : ℝ) * Real.Gamma (1/2) :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 1/2) hab
  have hreal : ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
      * (Real.sqrt b / (2 * Real.sqrt t)))
      = Real.sqrt b / Real.sqrt (a + b) := by
    have hpointwise : ∀ t ∈ Ioi (0:ℝ), Real.exp (-a * t) * ((2 / Real.sqrt Real.pi)
        * Real.exp (-(b*t)) * (Real.sqrt b / (2 * Real.sqrt t)))
        = (Real.sqrt b / (a * Real.sqrt Real.pi) * a)
          * (t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))) := by
      intro t ht
      have hst : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
      have htrpow : t ^ ((1/2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
        rw [show (1/2 : ℝ) - 1 = -(1/2 : ℝ) by ring, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
      rw [htrpow]
      have hexp : Real.exp (-a * t) * Real.exp (-(b * t)) = Real.exp (-((a + b) * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have ha' : a ≠ 0 := ne_of_gt ha
      have hpi' : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
      rw [← hexp]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpointwise, integral_const_mul, hgamma_val,
      Real.Gamma_one_half_eq]
    have hab_ne : (a + b) ≠ 0 := ne_of_gt hab
    have hpi_ne : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hrpow : (1 / (a + b) : ℝ) ^ (1/2 : ℝ) = Real.sqrt (1 / (a + b)) := by
      rw [Real.sqrt_eq_rpow]
    rw [hrpow]
    have hsqrt_div : Real.sqrt (1 / (a + b)) = 1 / Real.sqrt (a + b) := by
      rw [Real.sqrt_div' 1 hab.le, Real.sqrt_one]
    rw [hsqrt_div]
    have hsqrtab_ne : Real.sqrt (a + b) ≠ 0 := Real.sqrt_ne_zero'.mpr hab
    field_simp
  simp only [laplaceTransform, fC']
  have hcongr : ∀ t : ℝ, Complex.exp (-(a:ℂ) * (t:ℂ))
      * (((2 / Real.sqrt Real.pi) * Real.exp (-(b * t)) * (Real.sqrt b / (2 * Real.sqrt t))) : ℂ)
      = ((Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
          * (Real.sqrt b / (2 * Real.sqrt t)))) : ℝ) := by
    intro t
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
  rw [show (∫ t in Ioi (0:ℝ),
        ((Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
          * (Real.sqrt b / (2 * Real.sqrt t)))) : ℝ) : ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
          * (Real.sqrt b / (2 * Real.sqrt t))) : ℝ) : ℂ) from
      (_root_.integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ)))
        (f := fun t : ℝ => Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
          * (Real.sqrt b / (2 * Real.sqrt t)))))]
  rw [hreal]

/-- `fC b` is integrable against the Laplace kernel at `a` (bounded by the
integrable exponential kernel, since `‖erf‖ ≤ 1`). -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem integrableOn_fC (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * fC b t) (Ioi 0) := by
  have hv'_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_complex_Ioi (a := -(a:ℂ)) (by simp; linarith) 0
  have hu_meas : AEStronglyMeasurable (fC b) (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    exact Complex.continuous_ofReal.comp
      (continuous_erf.comp (by fun_prop : Continuous fun t : ℝ => Real.sqrt (b * t)))
  have hbound : ∀ t ∈ Ioi (0:ℝ),
      ‖Complex.exp (-(a:ℂ) * t) * fC b t‖ ≤ ‖Complex.exp (-(a:ℂ) * t)‖ := by
    intro t ht
    have hu_le : ‖fC b t‖ ≤ 1 := by
      have h1 : erf (Real.sqrt (b * t)) ≤ 1 := erf_le_one _
      have h2 : 0 ≤ erf (Real.sqrt (b * t)) := erf_nonneg (Real.sqrt_nonneg _)
      unfold fC
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith, h1⟩
    calc ‖Complex.exp (-(a:ℂ) * t) * fC b t‖
        = ‖Complex.exp (-(a:ℂ) * t)‖ * ‖fC b t‖ := norm_mul _ _
      _ ≤ ‖Complex.exp (-(a:ℂ) * t)‖ * 1 := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = ‖Complex.exp (-(a:ℂ) * t)‖ := by ring
  exact Integrable.mono hv'_int (hv'_int.aestronglyMeasurable.mul hu_meas)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hbound t ht)

/-- `fC b` is continuous at `0` within `Ici 0`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem continuousWithinAt_fC (b : ℝ) : ContinuousWithinAt (fC b) (Ici (0:ℝ)) 0 := by
  have hcont : Continuous (fC b) :=
    Complex.continuous_ofReal.comp
      (continuous_erf.comp (by fun_prop : Continuous fun t : ℝ => Real.sqrt (b * t)))
  exact hcont.continuousWithinAt

/-- The boundary term `e^{-at} fC b t → 0` as `t → ∞`, `a > 0`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem tendsto_fC_boundary (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * fC b t) atTop (𝓝 0) := by
  have hu_bdd : ∀ t : ℝ, 0 < t → ‖fC b t‖ ≤ 1 := by
    intro t ht
    have h1 : erf (Real.sqrt (b * t)) ≤ 1 := erf_le_one _
    have h2 : 0 ≤ erf (Real.sqrt (b * t)) := erf_nonneg (Real.sqrt_nonneg _)
    unfold fC
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, h1⟩
  have hv_to0 : Tendsto (fun t : ℝ => Complex.exp (-(a:ℂ) * t)) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖) atTop (𝓝 0) := by
      have heq : ∀ t : ℝ, ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ = Real.exp (-a * t) := by
        intro t
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, mul_comm]
      simp_rw [heq]
      have : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      exact Real.tendsto_exp_atBot.comp this
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hzero_mul : Tendsto (fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ)) * fC b t‖) atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero' (t₀ := atTop)
      (f := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ)) * fC b t‖)
      (g := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖)
    · filter_upwards with t using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      calc ‖Complex.exp (-(a:ℂ) * (t:ℂ)) * fC b t‖
          ≤ ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ * ‖fC b t‖ := norm_mul_le _ _
        _ ≤ ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ * 1 := mul_le_mul_of_nonneg_left (hu_bdd t ht) (norm_nonneg _)
        _ = ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ := by ring
    · simpa using hv_to0.norm
  rwa [tendsto_zero_iff_norm_tendsto_zero]

/-- `fC' b` is integrable against the Laplace kernel at `a`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem integrableOn_fC' (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * fC' b t) (Ioi 0) := by
  have hab : 0 < a + b := by linarith
  have hreal_int : IntegrableOn
      (fun t : ℝ => Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
        * (Real.sqrt b / (2 * Real.sqrt t)))) (Ioi (0:ℝ)) := by
    have hgamma_int : IntegrableOn
        (fun t : ℝ => t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))) (Ioi (0:ℝ)) := by
      have hbase : IntegrableOn (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) (Ioi (0:ℝ)) := by
        have h0 := Real.GammaIntegral_convergent (by norm_num : (0:ℝ) < 1/2)
        refine h0.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioi
      have hscaled : IntegrableOn
          (fun t : ℝ => ((a + b) * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))
          (Ioi (0:ℝ)) := by
        have h := (integrableOn_Ioi_comp_mul_left_iff
          (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) 0 hab).mpr (by simpa using hbase)
        simpa using h
      have hcm : IntegrableOn
          (fun t : ℝ => (a + b) ^ (-(1/2 : ℝ) + 1) *
            (((a + b) * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))) (Ioi (0:ℝ)) :=
        hscaled.const_mul _
      refine hcm.congr_fun (fun t ht => ?_) measurableSet_Ioi
      rw [Real.mul_rpow hab.le ht.le]
      have hconst : (a + b) ^ (-(1/2 : ℝ) + 1) * (a + b) ^ ((1/2 : ℝ) - 1) = 1 := by
        rw [← Real.rpow_add hab]; norm_num
      calc (a + b) ^ (-(1/2 : ℝ) + 1)
              * ((a + b) ^ ((1/2 : ℝ) - 1) * t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))
          = ((a + b) ^ (-(1/2 : ℝ) + 1) * (a + b) ^ ((1/2 : ℝ) - 1))
              * (t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t))) := by ring
        _ = t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)) := by rw [hconst]; ring
    have hc : IntegrableOn
        (fun t : ℝ => (Real.sqrt b / (a * Real.sqrt Real.pi) * a)
          * (t ^ ((1/2 : ℝ) - 1) * Real.exp (-((a + b) * t)))) (Ioi (0:ℝ)) :=
      hgamma_int.const_mul _
    refine hc.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have hst : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
    have htrpow : t ^ ((1/2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      rw [show (1/2 : ℝ) - 1 = -(1/2 : ℝ) by ring, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
    rw [htrpow]
    have hexp : Real.exp (-a * t) * Real.exp (-(b * t)) = Real.exp (-((a + b) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have ha' : a ≠ 0 := ne_of_gt ha
    have hpi' : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    rw [← hexp]; field_simp
  have hC_int : IntegrableOn
      (fun t : ℝ => ((Real.exp (-a * t) * ((2 / Real.sqrt Real.pi) * Real.exp (-(b*t))
        * (Real.sqrt b / (2 * Real.sqrt t)))) : ℝ) : ℝ → ℂ) (Ioi (0:ℝ)) :=
    hreal_int.ofReal
  refine hC_int.congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold fC'
  push_cast
  ring_nf

/-- **The Laplace-routed derivation.** `a * laplaceTransform (fC b) a - fC b 0
= laplaceTransform (fC' b) a`, via the module's own derivative rule
(`laplaceTransform_deriv`, DLMF 1.14.27). -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.3, no independent DLMF number
theorem laplaceTransform_deriv_fC (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    laplaceTransform (fC' b) (a:ℂ)
      = (a:ℂ) * laplaceTransform (fC b) (a:ℂ) - fC b 0 :=
  laplaceTransform_deriv
    (f := fC b) (f' := fC' b) (s := (a:ℂ))
    (fun t ht => hasDerivAt_fC b hb t ht)
    (integrableOn_fC a b ha)
    (integrableOn_fC' a b ha hb)
    (continuousWithinAt_fC b)
    (tendsto_fC_boundary a b ha)

-- no-dlmf: proof-vocabulary corollary of erf_7_14_3 (DLMF 7.14.3); the 1.14.27 citation is the method used, not the equation formalized. The faithful 7.14.3 surface is `erf_7_14_3` in Ch7Integrals.lean.
/-- **`laplaceTransform_erf_sqrt`** — the module-vocabulary corollary:
`laplaceTransform (fun t => (erf (√(bt)) : ℂ)) (a:ℂ) = ((1/a) * √(b/(a+b)) : ℝ)`,
derived through `laplaceTransform_deriv` (DLMF 1.14.27), NOT via direct `Ioi`
integration by parts on the original integrand. -/
theorem laplaceTransform_erf_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    laplaceTransform (fC b) (a:ℂ) = ((1/a) * Real.sqrt (b/(a+b)) : ℝ) := by
  have hkey := laplaceTransform_deriv_fC a b ha hb
  rw [laplaceTransform_fC'_eq a b ha hb] at hkey
  have hfC0 : fC b 0 = 0 := by
    unfold fC
    simp [erf_zero]
  rw [hfC0, sub_zero] at hkey
  have ha_ne : (a:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hval : laplaceTransform (fC b) (a:ℂ) = ((Real.sqrt b / Real.sqrt (a+b)) : ℝ) / (a:ℂ) := by
    rw [eq_comm, div_eq_iff ha_ne, eq_comm, mul_comm]
    exact hkey.symm
  rw [hval]
  have hab : 0 < a + b := by linarith
  have hrw : (Real.sqrt b / Real.sqrt (a+b) : ℝ) / (a:ℝ) = (1/a) * Real.sqrt (b/(a+b)) := by
    rw [Real.sqrt_div hb.le]
    field_simp
  rw [show ((Real.sqrt b / Real.sqrt (a+b) : ℝ) : ℂ) / (a:ℂ)
      = (((Real.sqrt b / Real.sqrt (a+b)) / a : ℝ) : ℂ) by push_cast; ring, hrw]

end FLMF.Error
