import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Field

/-!
# Exponential–Abelian theorem (method kit — DLMF §1.15, Abelian/Tauberian)

The **Abelian** bridge from an exponentially-regularized (Laplace) integral to the
improper integral it regularizes: if `∫_0^R f(t) dt → L` as `R → ∞` (conditional /
improper convergence) and `f` is continuous and bounded, then
`∫_{(0,∞)} e^{-ε t} f(t) dt → L` as `ε ↓ 0`.

This is the exponential-kernel sibling of `FLMF.Methods.AbelianGaussian`: the
Gaussian version (`e^{-εt²}`) converts the regularized oscillatory-Gaussian value
into the improper Fresnel value; this exponential version (`e^{-εt}`) is the one
that pairs with a Laplace-transform value to pin improper integrals such as the
Dirichlet integral `∫_0^∞ (sin t)/t dt = π/2` (Si(∞), DLMF §6.12).

The proof is the same skeleton as the Gaussian case: integrate by parts to move
the weight onto `F(t) = ∫_0^t f`, rescale `u = ε·t` so the unit-mass weight
`e^{-u}` concentrates the mass at `u/ε → ∞` where `F → L`, then dominated
convergence.
-/

namespace FLMF.Methods.AbelianExp

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

-- no-dlmf: reusable Abelian/Tauberian method-kit theorem, no specific DLMF equation
/-- **Exponential–Abelian theorem.** If `∫_0^R f → L` (improper convergence) and `f`
is continuous and bounded by `1`, then the Laplace-regularized integral
`∫_{Ioi 0} e^{-εt} f → L` as `ε ↓ 0`. -/
theorem abelian_exp (f : ℝ → ℝ) (L : ℝ) (hf : Continuous f) (hfb : ∀ t, |f t| ≤ 1)
    (hconv : Tendsto (fun R => ∫ t in (0:ℝ)..R, f t) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * f t) (𝓝[>] 0) (𝓝 L) := by
  set F : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, f s with hFdef
  have hFderiv : ∀ t : ℝ, HasDerivAt F (f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr (fun t => (hFderiv t).continuousAt)
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hFconv : Tendsto F atTop (𝓝 L) := hconv
  -- (1) uniform bound `|F t - L| ≤ C` for `t ≥ 0`
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
  -- e^{-εt} is integrable on Ioi 0 (per ε)
  have hexpIoi : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun t => Real.exp (-ε * t)) (Ioi 0) := by
    intro ε hε
    have := integrableOn_exp_mul_Ioi (a := -ε) (by linarith) (0:ℝ)
    simpa using this
  -- (2) per-ε IBP identity:  ∫_{Ioi 0} e^{-εt} f = ∫_{Ioi 0} ε e^{-εt} F
  have hIdent : ∀ ε : ℝ, 0 < ε →
      ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * f t
        = ∫ t in Ioi (0:ℝ), ε * Real.exp (-ε * t) * F t := by
    intro ε hε
    -- LHS integrable on Ioi 0
    have hintL : IntegrableOn (fun t => Real.exp (-ε * t) * f t) (Ioi 0) := by
      have h := (hexpIoi ε hε).bdd_mul (f := f) (c := 1)
        (hf.aestronglyMeasurable.restrict)
        (ae_of_all _ (fun t => by simpa [Real.norm_eq_abs] using hfb t))
      refine h.congr ?_
      filter_upwards with t using by rw [mul_comm]
    -- weight integrable on Ioi 0
    have hbase : IntegrableOn (fun t => ε * Real.exp (-ε * t)) (Ioi 0) :=
      (hexpIoi ε hε).const_mul ε
    -- RHS integrable on Ioi 0:  |ε e^{-εt} F t| ≤ (|L|+C)·(ε e^{-εt})
    have hintR : IntegrableOn (fun t => ε * Real.exp (-ε * t) * F t) (Ioi 0) := by
      refine Integrable.mono' (hbase.const_mul (|L| + C))
        (by exact (by fun_prop : Continuous fun t => ε * Real.exp (-ε*t) * F t).aestronglyMeasurable.restrict)
        ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      have hnn : 0 ≤ ε * Real.exp (-ε * t) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      calc ε * Real.exp (-ε*t) * |F t|
          ≤ ε * Real.exp (-ε*t) * (|L| + C) := mul_le_mul_of_nonneg_left (hFb t htpos.le) hnn
        _ = (|L| + C) * (ε * Real.exp (-ε*t)) := by ring
    -- finite IBP on [0,R]
    have hexp0 : Tendsto (fun R : ℝ => Real.exp (-ε * R)) atTop (𝓝 0) := by
      have hq : Tendsto (fun R : ℝ => ε * R) atTop atTop := Tendsto.const_mul_atTop hε tendsto_id
      have hneg : Tendsto (fun R : ℝ => -ε * R) atTop atBot := by
        have heq : (fun R : ℝ => -ε * R) = (fun R : ℝ => -(ε * R)) := by funext R; ring
        rw [heq]; exact tendsto_neg_atBot_iff.mpr hq
      exact Real.tendsto_exp_atBot.comp hneg
    have hIBP_R : ∀ R : ℝ,
        ∫ t in (0:ℝ)..R, Real.exp (-ε * t) * f t
          = Real.exp (-ε * R) * F R + ∫ t in (0:ℝ)..R, ε * Real.exp (-ε * t) * F t := by
      intro R
      have hu : ∀ t ∈ uIcc (0:ℝ) R,
          HasDerivAt (fun s => Real.exp (-ε * s)) (-ε * Real.exp (-ε*t)) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => -ε * s) (-ε) t := by
          simpa using (hasDerivAt_id t).const_mul (-ε)
        have := h1.exp
        convert this using 1; ring
      have hv : ∀ t ∈ uIcc (0:ℝ) R, HasDerivAt F (f t) t := fun t _ => hFderiv t
      have hu' : IntervalIntegrable (fun t => -ε * Real.exp (-ε*t)) volume 0 R := by
        apply Continuous.intervalIntegrable; fun_prop
      have hv' : IntervalIntegrable f volume 0 R := hf.intervalIntegrable 0 R
      have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      rw [hF0] at key
      simp only [mul_zero, sub_zero] at key
      rw [key]
      have : ∫ t in (0:ℝ)..R, -ε * Real.exp (-ε*t) * F t
           = -∫ t in (0:ℝ)..R, ε * Real.exp (-ε*t) * F t := by
        rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
      rw [this]; ring
    -- pass R → ∞
    have hL : Tendsto (fun R => ∫ t in (0:ℝ)..R, Real.exp (-ε * t) * f t) atTop
        (𝓝 (∫ t in Ioi 0, Real.exp (-ε * t) * f t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hintL tendsto_id
    have hRr : Tendsto (fun R => ∫ t in (0:ℝ)..R, ε * Real.exp (-ε*t) * F t) atTop
        (𝓝 (∫ t in Ioi 0, ε * Real.exp (-ε*t) * F t)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hintR tendsto_id
    have hbdry : Tendsto (fun R => Real.exp (-ε * R) * F R) atTop (𝓝 0) := by
      have hg0 : Tendsto (fun R => Real.exp (-ε * R) * (|L| + C)) atTop (𝓝 0) := by
        simpa only [zero_mul] using hexp0.mul_const (|L| + C)
      refine squeeze_zero_norm' ?_ hg0
      filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hFb R hR) (Real.exp_pos _).le
    have hcong := hL.congr (fun R => hIBP_R R)
    have hsum := (hbdry.add hRr)
    rw [zero_add] at hsum
    exact tendsto_nhds_unique hcong hsum
  -- (3) change of variables  u = ε t
  have hCV : ∀ ε : ℝ, 0 < ε →
      ∫ t in Ioi (0:ℝ), ε * Real.exp (-ε * t) * F t
        = ∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u / ε) := by
    intro ε hε
    have hpt : ∀ t : ℝ, ε * Real.exp (-ε * t) * F t
        = ε • ((fun u => Real.exp (-u) * F (u / ε)) (ε * t)) := by
      intro t
      simp only [smul_eq_mul]
      rw [mul_div_cancel_left₀ t hε.ne', neg_mul]
      ring
    calc ∫ t in Ioi (0:ℝ), ε * Real.exp (-ε * t) * F t
        = ∫ t in Ioi (0:ℝ), ε • ((fun u => Real.exp (-u) * F (u / ε)) (ε * t)) :=
          setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
      _ = ε • ∫ t in Ioi (0:ℝ), (fun u => Real.exp (-u) * F (u / ε)) (ε * t) := by
          rw [MeasureTheory.integral_smul]
      _ = ε • (ε⁻¹ • ∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u / ε)) := by
          rw [integral_comp_mul_left_Ioi (fun u => Real.exp (-u) * F (u / ε)) 0 hε, mul_zero]
      _ = ∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u / ε) := by
          rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  -- (4) dominated-convergence limit of the change-of-variables integral
  have hbound_int : Integrable (fun u => (|L| + C) * Real.exp (-u)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul (|L| + C)
  have hDCT : Tendsto (fun ε : ℝ => ∫ u in Ioi (0:ℝ), Real.exp (-u) * F (u / ε))
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0:ℝ), Real.exp (-u) * L)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (|L| + C) * Real.exp (-u)) ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (by fun_prop : Continuous fun u => Real.exp (-u) * F (u / ε)).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : 0 < ε := hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hupos : 0 < u := hu
      have hnn : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      calc Real.exp (-u) * |F (u / ε)|
          ≤ Real.exp (-u) * (|L| + C) := mul_le_mul_of_nonneg_left (hFb _ (by positivity)) hnn
        _ = (|L| + C) * Real.exp (-u) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hupos : 0 < u := hu
      have hFarg : Tendsto (fun ε : ℝ => F (u / ε)) (𝓝[>] 0) (𝓝 L) := by
        apply hFconv.comp
        have hinv := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
        simpa [div_eq_mul_inv] using hinv.const_mul_atTop hupos
      simpa using (tendsto_const_nhds.mul hFarg)
  -- assemble:  CV integral → ∫ e^{-u} L = L
  have hval : ∫ u in Ioi (0:ℝ), Real.exp (-u) * L = L := by
    rw [MeasureTheory.integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]
  rw [hval] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [← hCV ε hε, ← hIdent ε hε]


-- no-dlmf: reusable Abelian/Tauberian method-kit theorem, no specific DLMF equation
/-- **Complex exponential–Abelian theorem.** Reduces to the real
`FLMF.Methods.AbelianExp.abelian_exp` on the real and imaginary parts. -/
theorem abelian_exp_complex (f : ℝ → ℂ) (L : ℂ) (hf : Continuous f) (hfb : ∀ t, ‖f t‖ ≤ 1)
    (hconv : Tendsto (fun R => ∫ t in (0:ℝ)..R, f t) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0:ℝ), (Real.exp (-ε * t) : ℂ) * f t) (𝓝[>] 0) (𝓝 L) := by
  have hcont_re : Continuous (fun t => (f t).re) := Complex.continuous_re.comp hf
  have hcont_im : Continuous (fun t => (f t).im) := Complex.continuous_im.comp hf
  have hbound_re : ∀ t, |(f t).re| ≤ 1 := fun t => (Complex.abs_re_le_norm _).trans (hfb t)
  have hbound_im : ∀ t, |(f t).im| ≤ 1 := fun t => (Complex.abs_im_le_norm _).trans (hfb t)
  -- convergence of the real/imag parts of ∫_0^R f
  have hconv_re : Tendsto (fun R => ∫ t in (0:ℝ)..R, (f t).re) atTop (𝓝 L.re) := by
    refine ((Complex.continuous_re.tendsto L).comp hconv).congr (fun R => ?_)
    exact (Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (hf.intervalIntegrable 0 R)).symm
  have hconv_im : Tendsto (fun R => ∫ t in (0:ℝ)..R, (f t).im) atTop (𝓝 L.im) := by
    refine ((Complex.continuous_im.tendsto L).comp hconv).congr (fun R => ?_)
    exact (Complex.imCLM.intervalIntegral_comp_comm (μ := volume) (hf.intervalIntegrable 0 R)).symm
  have hre := FLMF.Methods.AbelianExp.abelian_exp _ _ hcont_re hbound_re hconv_re
  have him := FLMF.Methods.AbelianExp.abelian_exp _ _ hcont_im hbound_im hconv_im
  -- integrability of the complex regularized integrand
  have hint : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun t => (Real.exp (-ε * t) : ℂ) * f t) (Ioi 0) := by
    intro ε hε
    have hexp : IntegrableOn (fun t => Real.exp (-ε * t)) (Ioi 0) := by
      simpa using integrableOn_exp_mul_Ioi (a := -ε) (by linarith) (0:ℝ)
    refine Integrable.mono' hexp
      ((by fun_prop : Continuous fun t => (Real.exp (-ε * t) : ℂ) * f t).aestronglyMeasurable.restrict)
      ?_
    filter_upwards with t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-ε * t) * ‖f t‖ ≤ Real.exp (-ε * t) * 1 :=
          mul_le_mul_of_nonneg_left (hfb t) (Real.exp_pos _).le
      _ = Real.exp (-ε * t) := mul_one _
  -- the re/im of the complex regularized integral are the real abelian_exp integrals
  have hGre : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi (0:ℝ), (Real.exp (-ε * t) : ℂ) * f t).re
        = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * (f t).re := by
    intro ε hε
    rw [← RCLike.re_eq_complex_re, ← integral_re (hint ε hε)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hGim : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi (0:ℝ), (Real.exp (-ε * t) : ℂ) * f t).im
        = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * (f t).im := by
    intro ε hε
    rw [← RCLike.im_eq_complex_im, ← integral_im (hint ε hε)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  -- reconstruct the complex tendsto from re/im
  set G : ℝ → ℂ := fun ε => ∫ t in Ioi (0:ℝ), (Real.exp (-ε * t) : ℂ) * f t with hGdef
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

end FLMF.Methods.AbelianExp
