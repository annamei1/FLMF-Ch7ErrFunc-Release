import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Field

/-!
# Gaussian–Abelian theorem (method kit — DLMF §1.15, Abelian/Tauberian)

The **Abelian** bridge from a Gaussian-regularized integral to the improper
integral it regularizes: if `∫_0^R f(t) dt → L` as `R → ∞` (conditional/improper
convergence) and `f` is continuous and bounded, then
`∫_{(0,∞)} e^{-ε t²} f(t) dt → L` as `ε ↓ 0`.

This is the dual of the Tauberian direction (`FLMF.Methods.Tauberian`), and the
piece that converts the *Abel-regularized* oscillatory-Gaussian value of
`FLMF.Methods.StationaryPhase.fresnel_regularized` into the value of a genuine
*improper* oscillatory integral (e.g. the Fresnel integrals `C(∞) = S(∞) = 1/2`,
DLMF §7.12). The proof: integrate by parts to move the weight onto
`F(t) = ∫_0^t f`, rescale `u = √ε · t` so the unit-mass Gaussian weight
`2u e^{-u²}` concentrates the mass at `u/√ε → ∞` where `F → L`, then dominated
convergence.
-/

namespace FLMF.Methods.AbelianGaussian

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

-- no-dlmf: technical helper (unit-mass of the Gaussian weight), no DLMF equation
/-- `∫_{Ioi 0} 2εt e^{-εt²} dt = 1` for `ε > 0` (the Gaussian weight has unit mass). -/
theorem weight_integral {ε : ℝ} (hε : 0 < ε) :
    ∫ t in Ioi (0:ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ioi (0:ℝ),
      HasDerivAt (fun t => -Real.exp (-ε * t ^ 2)) (2 * ε * x * Real.exp (-ε * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -ε * t ^ 2) (-ε * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-ε))
    have h3 := (h1.exp).neg
    convert h3 using 1
    ring
  have hcont : ContinuousWithinAt (fun t => -Real.exp (-ε * t ^ 2)) (Ici (0:ℝ)) 0 :=
    Continuous.continuousWithinAt (by fun_prop)
  have htend : Tendsto (fun t : ℝ => -Real.exp (-ε * t ^ 2)) atTop (𝓝 0) := by
    have hq : Tendsto (fun t : ℝ => ε * t ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop hε (tendsto_pow_atTop (by norm_num))
    have hexp : Tendsto (fun t : ℝ => Real.exp (-ε * t ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => -ε * t ^ 2) atTop atBot := by
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr hq
      exact Real.tendsto_exp_atBot.comp this
    simpa using hexp.neg
  have hint : IntegrableOn (fun t => 2 * ε * t * Real.exp (-ε * t ^ 2)) (Ioi 0) := by
    have h := ((integrable_mul_exp_neg_mul_sq hε).const_mul (2 * ε)).integrableOn (s := Ioi 0)
    refine h.congr_fun ?_ measurableSet_Ioi
    intro x _; ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  simpa using key

-- no-dlmf: reusable Abelian/Tauberian method-kit theorem, no specific DLMF equation
/-- **Gaussian–Abelian theorem.** If `∫_0^R f → L` (improper convergence) and `f` is
continuous and bounded by `1`, then the Gaussian-regularized integral
`∫_{Ioi 0} e^{-εt²} f → L` as `ε ↓ 0`. -/
theorem abelian_gaussian (f : ℝ → ℝ) (L : ℝ) (hf : Continuous f) (hfb : ∀ t, |f t| ≤ 1)
    (hconv : Tendsto (fun R => ∫ t in (0:ℝ)..R, f t) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-ε * t ^ 2) * f t) (𝓝[>] 0) (𝓝 L) := by
  set F : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, f s with hFdef
  have hFderiv : ∀ t : ℝ, HasDerivAt F (f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr (fun t => (hFderiv t).continuousAt)
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hFconv : Tendsto F atTop (𝓝 L) := hconv
  -- (1) a uniform bound `|F t - L| ≤ C` for `t ≥ 0`
  obtain ⟨C, hC0, hCb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |F t - L| ≤ C := by
    have h0 : Tendsto (fun t => F t - L) atTop (𝓝 0) := by simpa using hFconv.sub_const L
    have habs : Tendsto (fun t => |F t - L|) atTop (𝓝 0) := by simpa using h0.abs
    obtain ⟨T, hT⟩ := eventually_atTop.1 (habs.eventually (Iic_mem_nhds (by norm_num : (0:ℝ) < 1)))
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T 0)).exists_bound_of_continuousOn
      ((hFcont.sub continuous_const).continuousOn)
    refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun t ht => ?_⟩
    rcases le_total t (max T 0) with h | h
    · exact le_trans (by simpa using hM t ⟨ht, h⟩) (le_max_left _ _)
    · exact le_trans (hT t (le_trans (le_max_left _ _) h)) (le_max_right _ _)
  have hFb : ∀ t : ℝ, 0 ≤ t → |F t| ≤ |L| + C := fun t ht => by
    have h := abs_le.1 (hCb t ht)
    rw [abs_le]
    exact ⟨by nlinarith [h.1, neg_abs_le L], by nlinarith [h.2, le_abs_self L]⟩
  -- (2) the per-ε IBP identity:  ∫_{Ioi 0} e^{-εt²} f = ∫_{Ioi 0} 2εt e^{-εt²} F
  have hIdent : ∀ ε : ℝ, 0 < ε →
      ∫ t in Ioi (0:ℝ), Real.exp (-ε * t ^ 2) * f t
        = ∫ t in Ioi (0:ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) * F t := by
    intro ε hε
    have hexp : Integrable (fun t : ℝ => Real.exp (-ε * t ^ 2)) := integrable_exp_neg_mul_sq hε
    have hwexp : Integrable (fun t : ℝ => t * Real.exp (-ε * t ^ 2)) :=
      integrable_mul_exp_neg_mul_sq hε
    -- LHS integrable on Ioi 0
    have hintL : IntegrableOn (fun t => Real.exp (-ε * t ^ 2) * f t) (Ioi 0) := by
      have h := (hexp.integrableOn (s := Ioi 0)).bdd_mul (f := f) (c := 1)
        (hf.aestronglyMeasurable.restrict)
        (ae_of_all _ (fun t => by simpa [Real.norm_eq_abs] using hfb t))
      refine h.congr ?_
      filter_upwards with t using by rw [mul_comm]
    -- RHS integrable on Ioi 0:  |2εt e^{-εt²} F t| ≤ (|L|+C)·(2εt e^{-εt²})
    have hbase : IntegrableOn (fun t => 2 * ε * t * Real.exp (-ε * t ^ 2)) (Ioi 0) := by
      have := (hwexp.const_mul (2 * ε)).integrableOn (s := Ioi 0)
      refine this.congr_fun ?_ measurableSet_Ioi; intro x _; ring
    have hintR : IntegrableOn (fun t => 2 * ε * t * Real.exp (-ε * t ^ 2) * F t) (Ioi 0) := by
      refine Integrable.mono' (hbase.const_mul (|L| + C))
        (by exact (by fun_prop : Continuous fun t => 2*ε*t*Real.exp (-ε*t^2)*F t).aestronglyMeasurable.restrict)
        ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      have hnn : 0 ≤ 2 * ε * t * Real.exp (-ε * t ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      calc 2*ε*t*Real.exp (-ε*t^2) * |F t|
          ≤ 2*ε*t*Real.exp (-ε*t^2) * (|L| + C) :=
            mul_le_mul_of_nonneg_left (hFb t htpos.le) hnn
        _ = (|L| + C) * (2*ε*t*Real.exp (-ε*t^2)) := by ring
    -- finite IBP on [0,R]:  ∫₀ᴿ e^{-εt²}f = e^{-εR²}F R + ∫₀ᴿ 2εt e^{-εt²} F
    have hexp0 : Tendsto (fun R : ℝ => Real.exp (-ε * R ^ 2)) atTop (𝓝 0) := by
      have hq : Tendsto (fun R : ℝ => ε * R ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop hε (tendsto_pow_atTop (by norm_num))
      exact Real.tendsto_exp_atBot.comp (by simpa [neg_mul] using tendsto_neg_atBot_iff.mpr hq)
    have hIBP_R : ∀ R : ℝ,
        ∫ t in (0:ℝ)..R, Real.exp (-ε * t ^ 2) * f t
          = Real.exp (-ε * R ^ 2) * F R
            + ∫ t in (0:ℝ)..R, 2 * ε * t * Real.exp (-ε * t ^ 2) * F t := by
      intro R
      have hu : ∀ t ∈ uIcc (0:ℝ) R,
          HasDerivAt (fun s => Real.exp (-ε * s ^ 2)) (-(2*ε*t) * Real.exp (-ε*t^2)) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => -ε * s ^ 2) (-ε * (2 * t)) t := by
          simpa using ((hasDerivAt_pow 2 t).const_mul (-ε))
        have := h1.exp
        convert this using 1; ring
      have hv : ∀ t ∈ uIcc (0:ℝ) R, HasDerivAt F (f t) t := fun t _ => hFderiv t
      have hu' : IntervalIntegrable (fun t => -(2*ε*t) * Real.exp (-ε*t^2)) volume 0 R := by
        apply Continuous.intervalIntegrable; fun_prop
      have hv' : IntervalIntegrable f volume 0 R := hf.intervalIntegrable 0 R
      have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      rw [hF0] at key
      simp only [mul_zero, sub_zero] at key
      rw [key]
      have : ∫ t in (0:ℝ)..R, -(2*ε*t) * Real.exp (-ε*t^2) * F t
           = -∫ t in (0:ℝ)..R, 2*ε*t*Real.exp (-ε*t^2) * F t := by
        rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
      rw [this]; ring
    -- pass R → ∞
    have hL : Tendsto (fun R => ∫ t in (0:ℝ)..R, Real.exp (-ε * t ^ 2) * f t) atTop
        (𝓝 (∫ t in Ioi 0, Real.exp (-ε * t ^ 2) * f t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hintL tendsto_id
    have hRr : Tendsto (fun R => ∫ t in (0:ℝ)..R, 2*ε*t*Real.exp (-ε*t^2) * F t) atTop
        (𝓝 (∫ t in Ioi 0, 2*ε*t*Real.exp (-ε*t^2) * F t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hintR tendsto_id
    have hbdry : Tendsto (fun R => Real.exp (-ε * R ^ 2) * F R) atTop (𝓝 0) := by
      have hg0 : Tendsto (fun R => Real.exp (-ε * R ^ 2) * (|L| + C)) atTop (𝓝 0) := by
        simpa only [zero_mul] using hexp0.mul_const (|L| + C)
      refine squeeze_zero_norm' ?_ hg0
      filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hFb R hR) (Real.exp_pos _).le
    have := hL.congr (fun R => hIBP_R R)
    have hsum := (hbdry.add hRr)
    rw [zero_add] at hsum
    exact tendsto_nhds_unique this hsum
  -- (3) change of variables  u = √ε t  and the dominated-convergence limit
  have hCV : ∀ ε : ℝ, 0 < ε →
      ∫ t in Ioi (0:ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) * F t
        = ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε) := by
    intro ε hε
    have hsqpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hpt : ∀ t : ℝ, 2 * ε * t * Real.exp (-ε * t ^ 2) * F t
        = Real.sqrt ε • (2 * (Real.sqrt ε * t) * Real.exp (-(Real.sqrt ε * t) ^ 2)
            * F ((Real.sqrt ε * t) / Real.sqrt ε)) := by
      intro t
      simp only [smul_eq_mul]
      rw [mul_div_cancel_left₀ t hsqpos.ne']
      rw [show -(Real.sqrt ε * t) ^ 2 = -ε * t ^ 2 from by rw [mul_pow, Real.sq_sqrt hε.le]; ring]
      rw [show Real.sqrt ε * (2 * (Real.sqrt ε * t) * Real.exp (-ε * t ^ 2) * F t)
            = (Real.sqrt ε * Real.sqrt ε) * (2 * t * Real.exp (-ε * t ^ 2) * F t) from by ring,
        Real.mul_self_sqrt hε.le]
      ring
    calc ∫ t in Ioi (0:ℝ), 2 * ε * t * Real.exp (-ε * t ^ 2) * F t
        = ∫ t in Ioi (0:ℝ), Real.sqrt ε •
            ((fun u => 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε)) (Real.sqrt ε * t)) :=
          setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
      _ = Real.sqrt ε • ∫ t in Ioi (0:ℝ),
            (fun u => 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε)) (Real.sqrt ε * t) := by
          rw [MeasureTheory.integral_smul]
      _ = Real.sqrt ε • ((Real.sqrt ε)⁻¹ •
            ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε)) := by
          rw [integral_comp_mul_left_Ioi
            (fun u => 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε)) 0 hsqpos, mul_zero]
      _ = ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε) := by
          rw [smul_smul, mul_inv_cancel₀ hsqpos.ne', one_smul]
  -- (4) the dominated-convergence limit of the change-of-variables integral
  have hbound_int : Integrable (fun u => (|L| + C) * (2 * u * Real.exp (-u ^ 2)))
      (volume.restrict (Ioi 0)) := by
    have h1 : Integrable (fun u : ℝ => u * Real.exp (-u ^ 2)) (volume.restrict (Ioi 0)) := by
      have := (integrable_mul_exp_neg_mul_sq (b := (1:ℝ)) one_pos).integrableOn (s := Ioi 0)
      simpa [neg_one_mul] using this
    refine (h1.const_mul (2 * (|L| + C))).congr ?_
    filter_upwards with u using by ring
  have hDCT : Tendsto (fun ε : ℝ => ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * F (u / Real.sqrt ε))
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (|L| + C) * (2 * u * Real.exp (-u ^ 2))) ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (by fun_prop : Continuous fun u => 2*u*Real.exp (-u^2)*F (u / Real.sqrt ε)).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hupos : 0 < u := hu
      have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
      have hnn : 0 ≤ 2 * u * Real.exp (-u ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      calc 2*u*Real.exp (-u^2) * |F (u / Real.sqrt ε)|
          ≤ 2*u*Real.exp (-u^2) * (|L| + C) :=
            mul_le_mul_of_nonneg_left (hFb _ (by positivity)) hnn
        _ = (|L| + C) * (2*u*Real.exp (-u^2)) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hupos : 0 < u := hu
      have hFarg : Tendsto (fun ε : ℝ => F (u / Real.sqrt ε)) (𝓝[>] 0) (𝓝 L) := by
        apply hFconv.comp
        have hsqrt : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] 0) (𝓝[>] 0) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          · exact (show Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝 0) (𝓝 0) by
              simpa using Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with ε hε using Real.sqrt_pos.2 hε
        have hinv := tendsto_inv_nhdsGT_zero.comp hsqrt
        simpa [div_eq_mul_inv] using hinv.const_mul_atTop hupos
      simpa using (tendsto_const_nhds.mul hFarg)
  -- assemble:  goal integral = CV integral, and CV integral → ∫ 2u e^{-u²} L = L
  have hval : ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * L = L := by
    have hw : ∫ u in Ioi (0:ℝ), 2 * 1 * u * Real.exp (-(1:ℝ) * u ^ 2) = 1 := weight_integral one_pos
    calc ∫ u in Ioi (0:ℝ), 2 * u * Real.exp (-u ^ 2) * L
        = ∫ u in Ioi (0:ℝ), (2 * 1 * u * Real.exp (-(1:ℝ) * u ^ 2)) * L := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
            rw [neg_one_mul]; ring
      _ = (∫ u in Ioi (0:ℝ), 2 * 1 * u * Real.exp (-(1:ℝ) * u ^ 2)) * L := by
            rw [MeasureTheory.integral_mul_const]
      _ = L := by rw [hw, one_mul]
  rw [hval] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← hCV ε hε, ← hIdent ε hε]


-- no-dlmf: reusable Abelian/Tauberian method-kit theorem, no specific DLMF equation
/-- **Complex Gaussian–Abelian theorem.** Reduces to the real
`FLMF.Methods.AbelianGaussian.abelian_gaussian` on the real and imaginary parts. -/
theorem abelian_gaussian_complex (f : ℝ → ℂ) (L : ℂ) (hf : Continuous f) (hfb : ∀ t, ‖f t‖ ≤ 1)
    (hconv : Tendsto (fun R => ∫ t in (0:ℝ)..R, f t) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0:ℝ), (Real.exp (-ε * t ^ 2) : ℂ) * f t) (𝓝[>] 0) (𝓝 L) := by
  have hcont_re : Continuous (fun t => (f t).re) := Complex.continuous_re.comp hf
  have hcont_im : Continuous (fun t => (f t).im) := Complex.continuous_im.comp hf
  have hbound_re : ∀ t, |(f t).re| ≤ 1 := fun t => (Complex.abs_re_le_norm _).trans (hfb t)
  have hbound_im : ∀ t, |(f t).im| ≤ 1 := fun t => (Complex.abs_im_le_norm _).trans (hfb t)
  have hconv_re : Tendsto (fun R => ∫ t in (0:ℝ)..R, (f t).re) atTop (𝓝 L.re) := by
    refine ((Complex.continuous_re.tendsto L).comp hconv).congr (fun R => ?_)
    exact (Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (hf.intervalIntegrable 0 R)).symm
  have hconv_im : Tendsto (fun R => ∫ t in (0:ℝ)..R, (f t).im) atTop (𝓝 L.im) := by
    refine ((Complex.continuous_im.tendsto L).comp hconv).congr (fun R => ?_)
    exact (Complex.imCLM.intervalIntegral_comp_comm (μ := volume) (hf.intervalIntegrable 0 R)).symm
  have hre := FLMF.Methods.AbelianGaussian.abelian_gaussian _ _ hcont_re hbound_re hconv_re
  have him := FLMF.Methods.AbelianGaussian.abelian_gaussian _ _ hcont_im hbound_im hconv_im
  have hint : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun t => (Real.exp (-ε * t ^ 2) : ℂ) * f t) (Ioi 0) := by
    intro ε hε
    have hexp : IntegrableOn (fun t => Real.exp (-ε * t ^ 2)) (Ioi 0) :=
      (integrable_exp_neg_mul_sq hε).integrableOn
    refine Integrable.mono' hexp
      ((by fun_prop : Continuous fun t => (Real.exp (-ε * t ^ 2) : ℂ) * f t).aestronglyMeasurable.restrict)
      ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-ε * t ^ 2) * ‖f t‖ ≤ Real.exp (-ε * t ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (hfb t) (Real.exp_pos _).le
      _ = Real.exp (-ε * t ^ 2) := mul_one _
  have hGre : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi (0:ℝ), (Real.exp (-ε * t ^ 2) : ℂ) * f t).re
        = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t ^ 2) * (f t).re := by
    intro ε hε
    rw [← RCLike.re_eq_complex_re, ← integral_re (hint ε hε)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hGim : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi (0:ℝ), (Real.exp (-ε * t ^ 2) : ℂ) * f t).im
        = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t ^ 2) * (f t).im := by
    intro ε hε
    rw [← RCLike.im_eq_complex_im, ← integral_im (hint ε hε)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  set G : ℝ → ℂ := fun ε => ∫ t in Ioi (0:ℝ), (Real.exp (-ε * t ^ 2) : ℂ) * f t with hGdef
  have hGre' : Tendsto (fun ε => (G ε).re) (𝓝[>] 0) (𝓝 L.re) := by
    refine hre.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hGre ε hε).symm
  have hGim' : Tendsto (fun ε => (G ε).im) (𝓝[>] 0) (𝓝 L.im) := by
    refine him.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hGim ε hε).symm
  have hcomb : Tendsto (fun ε => ((G ε).re : ℂ) + ((G ε).im : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 ((L.re : ℂ) + (L.im : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hGre').add
      (((Complex.continuous_ofReal.tendsto _).comp hGim').mul_const Complex.I)
  rw [Complex.re_add_im] at hcomb
  exact hcomb.congr (fun ε => Complex.re_add_im (G ε))

end FLMF.Methods.AbelianGaussian
