import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Ch7Definitions
import FLMF.Functions.Error.Ch7IntegralReps
import FLMF.Functions.Error.Ch7LaplaceBridge
import FLMF.Functions.Error.Ch7LaplaceConvolutionBridge
import FLMF.Functions.Error.ComplexErfExtra
import FLMF.Functions.Fresnel.Basic
import FLMF.Functions.Fresnel.Limit
import FLMF.Methods.LaplaceTransform
import FLMF.Methods.ContourRotationGamma
import FLMF.Methods.ParametricIntegralAnalytic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integral representations for the error and Fresnel functions (DLMF §7.14)

Statement surfaces for the integral table DLMF §7.14 (Laplace transforms and
definite integrals of `erf`, `erfc`, and the Fresnel integrals `C`, `S`).

FLMF's `erf`/`erfc`/Fresnel `C`/`S` are REAL-valued, so for the parameter
patterns where DLMF's `t` is a real Laplace-transform variable and only the
transform PARAMETER (`a`, `b`, `c`) genuinely ranges over `ℂ`, each table entry
has both a real specialization (narrower than DLMF, proven) and a DLMF-domain
complex surface (`cerf_*`/`cfresnel_*`, the `no-dlmf`-demoted real theorem's
faithful companion) built from the complex `cerf`/`cerfc`
(`FLMF.Functions.Error.ComplexErf`) and complex `cfresnelAuxF`/`cfresnelAuxG`
(`FLMF.Functions.Fresnel.Complex`). Every complex surface in this file is now
proven; each is obtained from its real anchor by analytic continuation
(identity theorem) in the transform parameter. `erf_7_14_4` itself was
generalized in place to DLMF's complex domain, with no real specialization
retained, and is proven directly by differentiation in `c`. The integrals over
`(0, ∞)` are written with Mathlib's `∫ t in Set.Ioi 0, …`.

Covered as theorems:
* `erf_7_14_2` / `cerf_7_14_2` — DLMF 7.14.2  (Laplace transform of `erf(b t)`).
* `erf_7_14_3` / `cerf_7_14_3` — DLMF 7.14.3  (Laplace transform of `erf(√(b t))`).
* `erf_7_14_4` — DLMF 7.14.4  (Laplace transform of `erfc(√(at)+√(c/t))`, complex domain).
* `erf_7_14_7` / `cfresnel_7_14_7` — DLMF 7.14.7  (Laplace transform of `C(√(2t/π))`).
* `erf_7_14_8` / `cfresnel_7_14_8` — DLMF 7.14.8  (Laplace transform of `S(√(2t/π))`).

* `erf_7_14_5` / `cfresnel_7_14_5` — DLMF 7.14.5  (Laplace transform of `C(t)` via `f`).
* `erf_7_14_6` / `cfresnel_7_14_6` — DLMF 7.14.6  (Laplace transform of `S(t)` via `g`).

Stated elsewhere (cross-reference comment below):
* DLMF 7.14.1 — the Fourier transform `∫₀^∞ e^{2iat} erfc(bt) dt`. Intrinsically
  complex (the RHS uses the complex Dawson integral `cdawson` of §7.2), so it has
  no real anchor to continue from and is stated and proven directly on `ℂ` as
  `erf_7_14_1_full` in `Error/ComplexErfExtra.lean`, alongside the complex
  Gaussian–Fourier integral `erf_7_7_3` its proof consumes. §7.14 is therefore
  8/8 surfaced and proven.
-/

namespace FLMF.Error

open MeasureTheory Real Set Filter
open scoped Real Topology


/-! ### Analytic-continuation toolkit for the `cerf_*`/`cfresnel_*` surfaces

Each complex surface below states DLMF's identity on its full complex parameter
domain, while the real specialization above it proves the identity on the
positive real axis.  The bridge is always the same: both sides are analytic in
the complex parameter on the (open, convex hence preconnected) domain, they
agree on a sequence of positive reals accumulating at an interior point, so the
identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`)
propagates the identity to the whole domain.  The analytic half of the argument
for the parametric integrals is
`FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane`. -/

section Ch714Analytic

-- no-dlmf: identity theorem transfer from the positive reals to the right half-plane
/-- **Identity theorem, right-half-plane form.**  Two functions analytic on
`{a : ℂ | 0 < a.re}` that agree at every positive real number agree on the whole
half-plane: the half-plane is convex, hence preconnected, and the positive reals
`1 + 1/(n+1)` accumulate at the interior point `1`. -/
private lemma aux714_eq_of_analytic_rightHalfPlane {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {a : ℂ | 0 < a.re}) (hG : AnalyticOnNhd ℂ G {a : ℂ | 0 < a.re})
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) :
    ∀ a : ℂ, 0 < a.re → F a = G a := by
  have hU : IsPreconnected {a : ℂ | 0 < a.re} :=
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
  have h₀ : (1 : ℂ) ∈ {a : ℂ | 0 < a.re} := by simp
  have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
        simpa using h.const_add 1
      exact (Complex.continuous_ofReal.tendsto 1).comp h2
    · refine Eventually.of_forall (fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hh : (1 + 1 / ((n : ℝ) + 1)) = 1 := by exact_mod_cast h
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    refine hseq.frequently (Eventually.frequently (Eventually.of_forall (fun n => ?_)))
    exact hreal _ (by positivity)
  intro a ha
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hU h₀ hfreq ha

-- no-dlmf: uniform bound on `[0,∞)` for a continuous function with a finite limit, support lemma
/-- A continuous real function with a finite limit at `+∞` is bounded on `[0, ∞)`. -/
private lemma aux714_bounded_of_tendsto {g : ℝ → ℝ} {L : ℝ} (hgc : Continuous g)
    (hglim : Tendsto g atTop (𝓝 L)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → |g x| ≤ M := by
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hglim 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max X 0)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C (|L| + 1), le_max_of_le_right (by positivity), fun x hx => ?_⟩
  rcases le_or_gt x (max X 0) with hxle | hxgt
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x ⟨hx, hxle⟩) (le_max_left _ _)
  · have hxX : X ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left X 0) hxgt)
    have hd := hX x hxX
    rw [Real.dist_eq] at hd
    have hbnd : |g x| ≤ |L| + 1 := by
      have h2 := abs_sub_abs_le_abs_sub (g x) L
      linarith
    exact le_trans hbnd (le_max_right _ _)

-- no-dlmf: analyticity of a Laplace transform with a polynomially bounded kernel, support lemma
/-- The Laplace transform `a ↦ ∫₀^∞ e^{-a t} χ(t) dt` of a kernel continuous on
`(0, ∞)` and bounded there by `C·t^k` (`k > -1`) is analytic on the right
half-plane `{a | Re a > 0}`.  Domination: on `{σ ≤ Re a}` the parameter
derivative is bounded by `C·t^{k+1}·e^{-σ t}`. -/
private lemma aux714_analyticOnNhd_laplace {χ : ℝ → ℂ} {C k : ℝ} (hk : -1 < k)
    (hχc : ContinuousOn χ (Ioi (0:ℝ))) (hχM : ∀ t : ℝ, 0 < t → ‖χ t‖ ≤ C * t ^ k) :
    AnalyticOnNhd ℂ (fun a : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) * χ t)
      {a : ℂ | 0 < a.re} := by
  have hnorm : ∀ (a : ℂ) (t : ℝ), ‖Complex.exp (-a * (t : ℂ))‖ = Real.exp (-a.re * t) := by
    intro a t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hmeas : ∀ a : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-a * (t : ℂ)) * χ t) (volume.restrict (Ioi (0:ℝ))) := by
    intro a
    refine (ContinuousOn.mul ?_ hχc).aestronglyMeasurable measurableSet_Ioi
    exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  have hmeas' : ∀ a : ℂ, AEStronglyMeasurable
      (fun t : ℝ => -(t : ℂ) * Complex.exp (-a * (t : ℂ)) * χ t)
      (volume.restrict (Ioi (0:ℝ))) := by
    intro a
    refine (ContinuousOn.mul (ContinuousOn.mul ?_ ?_) hχc).aestronglyMeasurable measurableSet_Ioi
    · exact (by fun_prop : Continuous fun t : ℝ => -(t : ℂ)).continuousOn
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane
    (f := fun a t => Complex.exp (-a * (t : ℂ)) * χ t)
    (f' := fun a t => -(t : ℂ) * Complex.exp (-a * (t : ℂ)) * χ t)
    (fun a _ => hmeas a) (fun a ha => ?_) (fun a _ => hmeas' a) ?_ ?_
  · have hbase : IntegrableOn (fun t : ℝ => Real.exp (-a.re * t) * t ^ k) (Ioi (0 : ℝ)) :=
      integrableOn_exp_neg_mul_rpow_Ioi a.re k ha hk
    refine Integrable.mono' (g := fun t : ℝ => C * (Real.exp (-a.re * t) * t ^ k))
      (hbase.const_mul C) (hmeas a) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, hnorm]
    calc Real.exp (-a.re * t) * ‖χ t‖ ≤ Real.exp (-a.re * t) * (C * t ^ k) := by
          gcongr
          exact hχM t ht0
      _ = C * (Real.exp (-a.re * t) * t ^ k) := by ring
  · filter_upwards with t a _
    have h1 : HasDerivAt (fun z : ℂ => -z * (t : ℂ)) (-(t : ℂ)) a := by
      simpa using ((hasDerivAt_id a).neg.mul_const (t : ℂ))
    have h2 := (h1.cexp).mul_const (χ t)
    convert h2 using 1
    ring
  · intro σ hσ
    refine ⟨fun t : ℝ => C * (Real.exp (-σ * t) * t ^ (k + 1)), ?_, ?_⟩
    · exact (integrableOn_exp_neg_mul_rpow_Ioi σ (k + 1) hσ (by linarith)).const_mul C
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha
      have ht0 : (0 : ℝ) < t := ht
      have hpow : t ^ (k + 1) = t ^ k * t := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      rw [norm_mul, norm_mul, hnorm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      calc t * Real.exp (-a.re * t) * ‖χ t‖ ≤ t * Real.exp (-σ * t) * (C * t ^ k) := by
            gcongr
            exact hχM t ht0
        _ = C * (Real.exp (-σ * t) * t ^ (k + 1)) := by rw [hpow]; ring

-- no-dlmf: elementary sector bound for `cerf`, support lemma
/-- If `Re (z²) ≥ 0` (in particular on the closed sector `|ph z| ≤ π/4`), the
segment representation `erf z = (2/√π) z ∫₀¹ e^{-(tz)²} dt` gives
`‖erf z‖ ≤ (2/√π)‖z‖`, since `‖e^{-(tz)²}‖ = e^{-t²Re(z²)} ≤ 1`. -/
private lemma aux714_norm_cerf_le {z : ℂ} (hz : 0 ≤ (z ^ 2).re) :
    ‖cerf z‖ ≤ (2 / Real.sqrt π) * ‖z‖ := by
  have hint : ‖∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2)‖ ≤ 1 := by
    have hb : ∀ t ∈ Set.uIoc (0:ℝ) 1, ‖Complex.exp (-((t : ℂ) * z) ^ 2)‖ ≤ 1 := by
      intro t _
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have hre : (-((t : ℂ) * z) ^ 2).re = -(t ^ 2 * (z ^ 2).re) := by
        have h : (-((t : ℂ) * z) ^ 2) = -((((t ^ 2 : ℝ)) : ℂ) * z ^ 2) := by push_cast; ring
        rw [h, Complex.neg_re, Complex.re_ofReal_mul]
      rw [hre]
      have : 0 ≤ t ^ 2 * (z ^ 2).re := by positivity
      linarith
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa using h
  have hsp : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  unfold cerf
  rw [mul_assoc, norm_mul]
  have hc : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / Real.sqrt π := by
    rw [show ((2 : ℂ) / (Real.sqrt Real.pi : ℂ)) = (((2 / Real.sqrt Real.pi : ℝ)) : ℂ) by
      push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖z * ∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2)‖
      = ‖z‖ * ‖∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2)‖ := norm_mul _ _
    _ ≤ ‖z‖ * 1 := by gcongr
    _ = ‖z‖ := mul_one _

-- no-dlmf: real-integral bridge for a Laplace transform with a real kernel, support lemma
/-- For a real rate `x` and a real kernel `h`, the complex Laplace integral is
the `ofReal` image of the real one. -/
private lemma aux714_laplace_ofReal (h : ℝ → ℝ) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ)) * ((h t : ℝ) : ℂ))
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * h t : ℝ) : ℂ) := by
  have hcongr : ∀ t : ℝ, Complex.exp (-(x : ℂ) * (t : ℂ)) * ((h t : ℝ) : ℂ)
      = ((Real.exp (-x * t) * h t : ℝ) : ℂ) := by
    intro t
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
  exact _root_.integral_ofReal

-- no-dlmf: entirety of the complex Fresnel cosine integral, support lemma
private lemma aux714_differentiable_cfresnelC : Differentiable ℂ FLMF.Fresnel.cfresnelC := by
  have hfun : FLMF.Fresnel.cfresnelC = fun w : ℂ =>
      ((1 / 2) * (1 + Complex.I) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * w)
        + (1 / 2) * (1 - Complex.I) *
            cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w)) / 2 := by
    funext w
    rw [← (FLMF.Fresnel.cfresnel_7_5_8 w).1, ← (FLMF.Fresnel.cfresnel_7_5_8 w).2]
    ring
  rw [hfun]
  have hd : Differentiable ℂ cerf := differentiable_cerf
  fun_prop

-- no-dlmf: entirety of the complex Fresnel sine integral, support lemma
private lemma aux714_differentiable_cfresnelS : Differentiable ℂ FLMF.Fresnel.cfresnelS := by
  have hfun : FLMF.Fresnel.cfresnelS = fun w : ℂ =>
      ((1 / 2) * (1 + Complex.I) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * w)
        - (1 / 2) * (1 - Complex.I) *
            cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w)) / (2 * Complex.I) := by
    funext w
    rw [← (FLMF.Fresnel.cfresnel_7_5_8 w).1, ← (FLMF.Fresnel.cfresnel_7_5_8 w).2]
    field_simp
    ring
  rw [hfun]
  have hd : Differentiable ℂ cerf := differentiable_cerf
  fun_prop

-- no-dlmf: entirety of the complex Fresnel auxiliary `f`, support lemma
private lemma aux714_differentiable_cfresnelAuxF :
    Differentiable ℂ FLMF.Fresnel.cfresnelAuxF := by
  have hC := aux714_differentiable_cfresnelC
  have hS := aux714_differentiable_cfresnelS
  unfold FLMF.Fresnel.cfresnelAuxF
  fun_prop

-- no-dlmf: entirety of the complex Fresnel auxiliary `g`, support lemma
private lemma aux714_differentiable_cfresnelAuxG :
    Differentiable ℂ FLMF.Fresnel.cfresnelAuxG := by
  have hC := aux714_differentiable_cfresnelC
  have hS := aux714_differentiable_cfresnelS
  unfold FLMF.Fresnel.cfresnelAuxG
  fun_prop

-- no-dlmf: real-agreement bridge for the complex auxiliary `f`, support lemma
private lemma aux714_cfresnelAuxF_ofReal (x : ℝ) :
    FLMF.Fresnel.cfresnelAuxF (x : ℂ) = ((fresnelAuxF x : ℝ) : ℂ) := by
  unfold FLMF.Fresnel.cfresnelAuxF fresnelAuxF
  rw [FLMF.Fresnel.cfresnelC_ofReal, FLMF.Fresnel.cfresnelS_ofReal]
  push_cast
  ring

-- no-dlmf: real-agreement bridge for the complex auxiliary `g`, support lemma
private lemma aux714_cfresnelAuxG_ofReal (x : ℝ) :
    FLMF.Fresnel.cfresnelAuxG (x : ℂ) = ((fresnelAuxG x : ℝ) : ℂ) := by
  unfold FLMF.Fresnel.cfresnelAuxG fresnelAuxG
  rw [FLMF.Fresnel.cfresnelC_ofReal, FLMF.Fresnel.cfresnelS_ofReal]
  push_cast
  ring

-- no-dlmf: principal-branch bridge `Complex.sqrt r = √r` for real `r ≥ 0`, support lemma
private lemma aux714_csqrt_ofReal {r : ℝ} (hr : 0 ≤ r) :
    Complex.sqrt (r : ℂ) = (Real.sqrt r : ℂ) := by
  rw [Complex.sqrt, Real.sqrt_eq_rpow,
    show ((2 : ℂ))⁻¹ = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hr]

-- no-dlmf: `(√z)² = z` for the principal complex square root, support lemma
private lemma aux714_csqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

-- no-dlmf: the principal square root has positive real part off the branch cut, support lemma
private lemma aux714_csqrt_re_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  have hkey : 0 < ‖z‖ + z.re := by
    rcases Complex.mem_slitPlane_iff.mp hz with h | h
    · have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h3 : z.re ≤ |z.re| := le_abs_self _
      linarith
    · have h2 : |z.re| < ‖z‖ := Complex.abs_re_lt_norm.mpr h
      have h3 : -z.re ≤ |z.re| := neg_le_abs _
      linarith
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_pos.mpr (by linarith)

-- no-dlmf: `a² + 1` stays off the branch cut when `Re a > 0`, support lemma
private lemma aux714_sq_add_one_mem_slitPlane {a : ℂ} (ha : 0 < a.re) :
    a ^ 2 + 1 ∈ Complex.slitPlane := by
  rcases eq_or_ne a.im 0 with h | h
  · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.add_re, Complex.one_re, pow_two, Complex.mul_re, h, mul_zero, sub_zero]
    nlinarith
  · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [Complex.add_im, Complex.one_im, add_zero, pow_two, Complex.mul_im]
    have : a.re * a.im ≠ 0 := mul_ne_zero (ne_of_gt ha) h
    intro hc
    apply this
    linarith

-- no-dlmf: branch-cut bookkeeping for the surds `√(√(a²+1) ± a)` of 7.14.7/7.14.8, support lemma
/-- For `Re a > 0` the principal root `w = √(a²+1)` has positive real part, and so
do `w + a` and `w - a`: the latter because `(w-a)(w+a) = w² - a² = 1`, so
`w - a = (w+a)⁻¹` and inversion preserves the open right half-plane. -/
private lemma aux714_surd_re_pos {a : ℂ} (ha : 0 < a.re) :
    0 < (Complex.sqrt (a ^ 2 + 1)).re ∧ 0 < (Complex.sqrt (a ^ 2 + 1) + a).re ∧
      0 < (Complex.sqrt (a ^ 2 + 1) - a).re := by
  set w : ℂ := Complex.sqrt (a ^ 2 + 1) with hwdef
  have hw : 0 < w.re := aux714_csqrt_re_pos (aux714_sq_add_one_mem_slitPlane ha)
  have hwa : 0 < (w + a).re := by
    rw [Complex.add_re]
    linarith
  have hsq : w ^ 2 = a ^ 2 + 1 := by rw [hwdef]; exact aux714_csqrt_sq _
  have hne : w + a ≠ 0 := by
    intro hc
    rw [hc] at hwa
    simp at hwa
  have hprod : (w - a) * (w + a) = 1 := by linear_combination hsq
  have hinv : w - a = (w + a)⁻¹ := by
    field_simp
    linear_combination hprod
  have hnormsq : 0 < Complex.normSq (w + a) := by
    rw [Complex.normSq_pos]
    exact hne
  refine ⟨hw, hwa, ?_⟩
  rw [hinv, Complex.inv_re]
  positivity

-- no-dlmf: `‖√z‖ = √‖z‖` for the principal square root, support lemma
private lemma aux714_norm_csqrt (w : ℂ) : ‖Complex.sqrt w‖ = Real.sqrt ‖w‖ := by
  have h : ‖Complex.sqrt w‖ ^ 2 = ‖w‖ := by
    rw [← norm_pow, aux714_csqrt_sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

-- no-dlmf: derivative of the principal square root in the `1/(2√z)` form, support lemma
private lemma aux714_hasDerivAt_csqrt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt Complex.sqrt (1 / (2 * Complex.sqrt z)) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp [Complex.mem_slitPlane_iff] at hz
  have hne : Complex.sqrt z ≠ 0 := by
    rw [Complex.sqrt]
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hz0 h.1
  have heq : z ^ (-1/2 : ℂ) / 2 = 1 / (2 * Complex.sqrt z) := by
    rw [show (-1/2 : ℂ) = -(2⁻¹ : ℂ) by norm_num, Complex.cpow_neg, ← Complex.sqrt]
    field_simp
  have h := Complex.hasDerivAt_sqrt hz
  rwa [heq] at h

-- no-dlmf: a quotient of two right-half-plane points avoids the branch cut, support lemma
private lemma aux714_div_mem_slitPlane {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    u / v ∈ Complex.slitPlane := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  obtain ⟨hre, him⟩ := hc
  have hu' : u = (u / v) * v := by field_simp
  rw [hu', Complex.mul_re, him, zero_mul, sub_zero] at hu
  nlinarith

-- no-dlmf: entirety of the complex complementary error function, support lemma
private lemma aux714_differentiable_cerfc : Differentiable ℂ cerfc := by
  intro z
  have h : DifferentiableAt ℂ (fun w : ℂ => 1 - cerf w) z :=
    ((hasDerivAt_cerf z).const_sub 1).differentiableAt
  exact h

-- no-dlmf: the open sector `|Im z| < Re z` (DLMF's `|ph z| < π/4`) is open, support lemma
private lemma aux714_openSector_isOpen : IsOpen {z : ℂ | |z.im| < z.re} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) Complex.continuous_re

-- no-dlmf: the open sector is convex, hence preconnected, support lemma
private lemma aux714_openSector_isPreconnected : IsPreconnected {z : ℂ | |z.im| < z.re} := by
  refine Convex.isPreconnected ?_
  intro u hu v hv s t hs ht hst
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  have hre : (s • u + t • v).re = s * u.re + t * v.re := by simp [Complex.add_re]
  have him : (s • u + t • v).im = s * u.im + t * v.im := by simp [Complex.add_im]
  rw [hre, him]
  have hbound : |s * u.im + t * v.im| ≤ s * |u.im| + t * |v.im| := by
    calc |s * u.im + t * v.im| ≤ |s * u.im| + |t * v.im| := abs_add_le _ _
      _ = s * |u.im| + t * |v.im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · have ht1 : t = 1 := by linarith
    have hs0' : s = 0 := hs0.symm
    rw [hs0', ht1] at hbound ⊢
    simp only [zero_mul, zero_add, one_mul] at hbound ⊢
    linarith [hv]
  · have hA : s * |u.im| < s * u.re := by nlinarith
    have hB : t * |v.im| ≤ t * v.re := by nlinarith
    linarith

-- no-dlmf: sector bridge `z ≠ 0`, `|ph z| < π/4 ⟹ |Im z| < Re z`, support lemma
/-- DLMF's open phase sector `|ph z| < π/4` (with the `z ≠ 0` presupposition made
explicit) is the open convex cone `|Im z| < Re z`. -/
private lemma aux714_abs_im_lt_re_of_arg {z : ℂ} (hz0 : z ≠ 0)
    (hz : |Complex.arg z| < Real.pi / 4) : |z.im| < z.re := by
  have hpi := Real.pi_pos
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  set θ := Complex.arg z with hθ
  have hsin : Real.sin θ = z.im / ‖z‖ := Complex.sin_arg z
  have hcos : Real.cos θ = z.re / ‖z‖ := Complex.cos_arg hz0
  have habs := abs_lt.mp hz
  have hsinlt : |Real.sin θ| < Real.sin (Real.pi / 4) := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) habs.2
    · have hs : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith)
      rw [abs_of_neg hs, ← Real.sin_neg]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hcosgt : Real.cos (Real.pi / 4) < Real.cos θ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) hz
    rwa [Real.cos_abs] at h
  rw [Real.sin_pi_div_four] at hsinlt
  rw [Real.cos_pi_div_four] at hcosgt
  have hkey : |z.im| / ‖z‖ < z.re / ‖z‖ := by
    rw [← abs_of_pos hn, ← abs_div, abs_of_pos hn, ← hsin, ← hcos]
    linarith
  rwa [div_lt_div_iff_of_pos_right hn] at hkey

-- no-dlmf: `Re (z²) > 0` on the open sector, support lemma
private lemma aux714_re_sq_pos {z : ℂ} (hz : |z.im| < z.re) : 0 < (z ^ 2).re := by
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  rw [h2]
  nlinarith [abs_nonneg z.im, sq_abs z.im]

-- no-dlmf: identity theorem transfer from the positive reals to the open sector
/-- **Identity theorem, sector form.**  Two functions analytic on the open convex
cone `{z | |Im z| < Re z}` (DLMF's `|ph z| < π/4`) that agree at every positive
real number agree on the whole sector: the sector is convex, hence preconnected,
and the positive reals `1 + 1/(n+1)` accumulate at the interior point `1`. -/
private lemma aux714_eq_of_analytic_openSector {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < z.re})
    (hG : AnalyticOnNhd ℂ G {z : ℂ | |z.im| < z.re})
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) :
    ∀ z : ℂ, |z.im| < z.re → F z = G z := by
  have hU : IsPreconnected {z : ℂ | |z.im| < z.re} := aux714_openSector_isPreconnected
  have h₀ : (1 : ℂ) ∈ {z : ℂ | |z.im| < z.re} := by norm_num
  have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
        simpa using h.const_add 1
      exact (Complex.continuous_ofReal.tendsto 1).comp h2
    · refine Eventually.of_forall (fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hh : (1 + 1 / ((n : ℝ) + 1)) = 1 := by exact_mod_cast h
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    refine hseq.frequently (Eventually.frequently (Eventually.of_forall (fun n => ?_)))
    exact hreal _ (by positivity)
  intro z hz
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hU h₀ hfreq hz

end Ch714Analytic

-- DLMF 7.14.1 is SURFACED AND PROVEN — but not here.  It is intrinsically
-- complex (the oscillatory kernel `e^{2iat}` and the RHS auxiliary `F`, the
-- complex Dawson integral `cdawson` of §7.2, have no real specialization), so
-- unlike the rest of §7.14 it has no real anchor + continuation pair and is
-- stated directly on `ℂ` next to the complex machinery it needs, as
-- `FLMF.Error.erf_7_14_1_full` in `Error/ComplexErfExtra.lean`:
--   `∫₀^∞ e^{2iat} erfc(bt) dt = (1/(a√π))·F(a/b) + (i/(2a))·(1 - e^{-(a/b)²})`
-- for `a ∈ ℂ` and `|ph b| < π/4`, with DLMF's `a = 0` limit `1/(b√π)` supplied
-- as the `if a = 0` branch.  Proved by parts against
-- `d/dt cerfc(bt) = -(2b/√π)e^{-(bt)²}`, the remaining half-line Gaussian–
-- Fourier integral being `erf_7_7_3` (DLMF 7.7.3).  (The former narrowed
-- `erf_7_14_1` helper stated there was FALSE and was deleted; see
-- docs/ERRATA.md, `erf-7-14-1-narrowed-false`.)

-- no-dlmf: real/narrowed restriction of DLMF 7.14.2; faithful surface is cerf_7_14_2
/-- Laplace transform of `erf(b t)`, real specialization: for real `a, b > 0`,
`∫₀^∞ e^{-at} erf(bt) dt = (1/a) e^{a²/(4b²)} erfc(a/(2b))`
(DLMF 7.14.2 is stated for `Re a > 0` and complex `b` with `|ph b| < π/4`).
-/
theorem erf_7_14_2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * erf (b * t)
      = (1 / a) * Real.exp (a ^ 2 / (4 * b ^ 2)) * erfc (a / (2 * b)) := by
  -- Routed through `FLMF.Methods.LaplaceTransform` (the anchor for M-laplace-convolution):
  -- `laplaceTransform_erf_scaled_eq_ofReal` bridges this real integral to the module's
  -- complex `laplaceTransform`, and `laplaceTransform_erf_scaled` evaluates it via
  -- `laplaceTransform_convolution` (DLMF 1.14.30/1.14.31, the module's causal-convolution
  -- theorem: `erf(bt)` is the convolution of `h(u) = (2b/√π)e^{-b²u²}` with the constant
  -- function `1`), not by a direct `Ioi` integration argument on the original integrand —
  -- see `Ch7LaplaceConvolutionBridge.lean`.
  have h1 : FLMF.Methods.LaplaceTransform.laplaceTransform (fun t => (erf (b * t) : ℂ)) (a : ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * erf (b*t)) : ℝ) :=
    laplaceTransform_erf_scaled_eq_ofReal a b
  have h2 := laplaceTransform_erf_scaled a b ha hb
  rw [h1] at h2
  exact_mod_cast h2

-- no-dlmf: `a`-direction analytic continuation of DLMF 7.14.2 at a positive real `b`;
-- the seed for the `b`-direction continuation in `cerf_7_14_2`
/-- DLMF 7.14.2 for a **positive real** second parameter `b` and complex `a` with
`Re a > 0`: the identity theorem in `a` applied to the real specialization
`erf_7_14_2`. -/
private lemma aux714_2_realb {b : ℝ} (hb : 0 < b) {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * cerf ((b:ℂ) * (t:ℂ)))
      = (1 / a) * Complex.exp (a ^ 2 / (4 * (b:ℂ) ^ 2)) * cerfc (a / (2 * (b:ℂ))) := by
  have hU : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbC : ((b : ℂ)) ≠ 0 := by
    simpa using hb.ne'
  have hmul : ∀ t : ℝ, ((b:ℂ) * (t:ℂ)) = (((b * t : ℝ)) : ℂ) := by
    intro t; push_cast; ring
  have hχc : ContinuousOn (fun t : ℝ => cerf ((b:ℂ) * (t:ℂ))) (Ioi (0:ℝ)) :=
    (differentiable_cerf.continuous.comp (by fun_prop)).continuousOn
  have hF : AnalyticOnNhd ℂ
      (fun c : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-c * (t:ℂ)) * cerf ((b:ℂ) * (t:ℂ)))
      {c : ℂ | 0 < c.re} := by
    refine aux714_analyticOnNhd_laplace (C := 2 * b / Real.sqrt π) (k := 1)
      (by norm_num) hχc (fun t ht => ?_)
    have hsq : (((b:ℂ) * (t:ℂ)) ^ 2).re = (b * t) ^ 2 := by
      rw [show ((b:ℂ) * (t:ℂ)) ^ 2 = ((((b * t) ^ 2 : ℝ)) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    have hbound := aux714_norm_cerf_le (z := (b:ℂ) * (t:ℂ)) (by rw [hsq]; positivity)
    have hn : ‖(b:ℂ) * (t:ℂ)‖ = b * t := by
      rw [hmul t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < b * t)]
    rw [hn] at hbound
    calc ‖cerf ((b:ℂ) * (t:ℂ))‖ ≤ 2 / Real.sqrt π * (b * t) := hbound
      _ = 2 * b / Real.sqrt π * t ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
  have hG : AnalyticOnNhd ℂ
      (fun c : ℂ => (1 / c) * Complex.exp (c ^ 2 / (4 * (b:ℂ) ^ 2)) * cerfc (c / (2 * (b:ℂ))))
      {c : ℂ | 0 < c.re} := by
    refine DifferentiableOn.analyticOnNhd (fun c hc => ?_) hU
    have hcre : 0 < c.re := hc
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hcre
      simp at hcre
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => (1:ℂ) / w) c :=
      (differentiableAt_const _).div differentiableAt_id hc0
    have hd2 : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp (w ^ 2 / (4 * (b:ℂ) ^ 2))) c :=
      DifferentiableAt.cexp (by fun_prop)
    have hd3 : DifferentiableAt ℂ (fun w : ℂ => cerfc (w / (2 * (b:ℂ)))) c := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := cerfc)
        (f := fun w : ℂ => w / (2 * (b:ℂ))) c (aux714_differentiable_cerfc _)
        (differentiableAt_id.div_const _)
      simpa [Function.comp] using h
    exact ((hd1.mul hd2).mul hd3).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      Complex.exp (-(x:ℂ) * (t:ℂ)) * cerf ((b:ℂ) * (t:ℂ))
        = Complex.exp (-(x:ℂ) * (t:ℂ)) * ((erf (b * t) : ℝ) : ℂ) := by
    intro t _
    congr 1
    rw [hmul t, cerf_ofReal]
  have e1 : ((x:ℂ)) ^ 2 / (4 * (b:ℂ) ^ 2) = (((x ^ 2 / (4 * b ^ 2) : ℝ)) : ℂ) := by
    push_cast; ring
  have e2 : ((x:ℂ)) / (2 * (b:ℂ)) = (((x / (2 * b) : ℝ)) : ℂ) := by push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    aux714_laplace_ofReal (fun t : ℝ => erf (b * t)) x, erf_7_14_2 x b hx hb,
    e1, e2, ← Complex.ofReal_exp, cerfc_ofReal]
  push_cast
  ring

/-- **DLMF 7.14.2** — Laplace transform of the complex error function `erf(bt)`,
for `Re a > 0` and complex `b` with `|ph b| < π/4`:
`∫₀^∞ e^{-at} erf(bt) dt = (1/a) e^{a²/(4b²)} erfc(a/(2b))`.

The `b ≠ 0` hypothesis is DLMF's presupposition made explicit: a phase constraint
`|ph b| < π/4` presumes `b` has a phase, but Lean's total `Complex.arg` sets
`arg 0 = 0`, so `b = 0` would otherwise satisfy `hb` and falsify the statement
(LHS `= 0`, RHS `= 1/a`, since `x/0 = 0` and `erfc 0 = 1`). See docs/ERRATA.md,
`cerf-7-14-2-arg-zero`; the same guard is already carried by `erf_7_14_1_full`.

DAG: E-7.14.2.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem cerf_7_14_2 {a b : ℂ} (ha : 0 < a.re) (hb0 : b ≠ 0)
    (hb : |Complex.arg b| < π / 4) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * cerf (b * (t:ℂ))
      = (1 / a) * Complex.exp (a ^ 2 / (4 * b ^ 2)) * cerfc (a / (2 * b)) := by
  -- Two-step analytic continuation, exactly parallel to `aux714_3_realb`/`cerf_7_14_3`:
  -- `aux714_2_realb` continues the real anchor `erf_7_14_2` in `a` across the right
  -- half-plane at a positive real `b`; here we continue in `b` across the open sector
  -- `|ph b| < π/4 = {|Im b| < Re b}`, on which `Re (b²) > 0` keeps the Gaussian
  -- parameter derivative `(2/√π) e^{-(bt)²} t` dominated by `(2/√π) t e^{-(Re a) t}`.
  have hsπ : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hnormexpA : ∀ t : ℝ, ‖Complex.exp (-a * (t:ℂ))‖ = Real.exp (-a.re * t) := by
    intro t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hnormc : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / Real.sqrt π := by
    rw [show ((2 : ℂ) / (Real.sqrt Real.pi : ℂ)) = (((2 / Real.sqrt Real.pi : ℝ)) : ℂ) by
      push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hresq : ∀ (w : ℂ) (t : ℝ), ((w * (t:ℂ)) ^ 2).re = t ^ 2 * (w ^ 2).re := by
    intro w t
    rw [show (w * (t:ℂ)) ^ 2 = (((t ^ 2 : ℝ)) : ℂ) * w ^ 2 by push_cast; ring,
      Complex.re_ofReal_mul]
  have hnwt : ∀ (w : ℂ) (t : ℝ), 0 < t → ‖w * (t:ℂ)‖ = ‖w‖ * t := by
    intro w t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hcont : ∀ w : ℂ, Continuous
      (fun t : ℝ => Complex.exp (-a * (t:ℂ)) * cerf (w * (t:ℂ))) := by
    intro w
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (differentiable_cerf.continuous.comp (by fun_prop))
  have hcont' : ∀ w : ℂ, Continuous
      (fun t : ℝ => Complex.exp (-a * (t:ℂ)) *
        ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)) ^ 2) * (t:ℂ))) := by
    intro w
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      ((continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))).mul
        Complex.continuous_ofReal)
  have hint : ∀ w : ℂ, |w.im| < w.re →
      IntegrableOn (fun t : ℝ => Complex.exp (-a * (t:ℂ)) * cerf (w * (t:ℂ))) (Ioi (0:ℝ)) := by
    intro w hw
    have hwsq : 0 < (w ^ 2).re := aux714_re_sq_pos hw
    refine Integrable.mono' (g := fun t : ℝ => (2 * ‖w‖ / Real.sqrt π) *
      (Real.exp (-a.re * t) * t ^ (1:ℝ)))
      ((integrableOn_exp_neg_mul_rpow_Ioi a.re 1 ha (by norm_num)).const_mul _)
      (hcont w).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have hb2 : 0 ≤ ((w * (t:ℂ)) ^ 2).re := by rw [hresq]; positivity
    have hbound := aux714_norm_cerf_le hb2
    rw [hnwt w t ht0] at hbound
    rw [norm_mul, hnormexpA t]
    calc Real.exp (-a.re * t) * ‖cerf (w * (t:ℂ))‖
        ≤ Real.exp (-a.re * t) * (2 / Real.sqrt π * (‖w‖ * t)) := by gcongr
      _ = 2 * ‖w‖ / Real.sqrt π * (Real.exp (-a.re * t) * t ^ (1:ℝ)) := by
          rw [Real.rpow_one]; ring
  have hF : AnalyticOnNhd ℂ
      (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a * (t:ℂ)) * cerf (w * (t:ℂ)))
      {z : ℂ | |z.im| < z.re} := by
    refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
      (μ := volume.restrict (Ioi (0:ℝ)))
      (f := fun w t => Complex.exp (-a * (t:ℂ)) * cerf (w * (t:ℂ)))
      (f' := fun w t => Complex.exp (-a * (t:ℂ)) *
        ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)) ^ 2) * (t:ℂ)))
      aux714_openSector_isOpen
      (fun w _ => (hcont w).aestronglyMeasurable)
      (fun w hw => hint w hw)
      (fun w _ => (hcont' w).aestronglyMeasurable)
      ?_ ?_
    · filter_upwards with t w _
      have h1 : HasDerivAt (fun z : ℂ => z * (t:ℂ)) (t:ℂ) w := by
        simpa using (hasDerivAt_id w).mul_const (t:ℂ)
      have h2 : HasDerivAt cerf ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)) ^ 2))
          (w * (t:ℂ)) := hasDerivAt_cerf _
      have h3 : HasDerivAt (fun z : ℂ => cerf (z * (t:ℂ)))
          ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)) ^ 2) * (t:ℂ)) w := by
        have h := HasDerivAt.comp (𝕜 := ℂ) w h2 h1
        simpa [Function.comp] using h
      exact h3.const_mul _
    · intro w₀ hw₀
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp aux714_openSector_isOpen w₀ hw₀
      refine ⟨r, hr, fun t : ℝ => (2 / Real.sqrt π) * (Real.exp (-a.re * t) * t ^ (1:ℝ)),
        (integrableOn_exp_neg_mul_rpow_Ioi a.re 1 ha (by norm_num)).const_mul _, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht0 : (0:ℝ) < t := ht
      have hzs : |z.im| < z.re := hsub hz
      have hzsq : 0 < (z ^ 2).re := aux714_re_sq_pos hzs
      rw [norm_mul, hnormexpA t, norm_mul, norm_mul, hnormc, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht0, Complex.norm_exp]
      have hre : (-(z * (t:ℂ)) ^ 2).re = -(t ^ 2 * (z ^ 2).re) := by
        rw [Complex.neg_re, hresq]
      rw [hre]
      have hexp : Real.exp (-(t ^ 2 * (z ^ 2).re)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith
      calc Real.exp (-a.re * t) * (2 / Real.sqrt π * Real.exp (-(t ^ 2 * (z ^ 2).re)) * t)
          ≤ Real.exp (-a.re * t) * (2 / Real.sqrt π * 1 * t) := by gcongr
        _ = 2 / Real.sqrt π * (Real.exp (-a.re * t) * t ^ (1:ℝ)) := by
            rw [Real.rpow_one]; ring
  have hG : AnalyticOnNhd ℂ
      (fun w : ℂ => (1 / a) * Complex.exp (a ^ 2 / (4 * w ^ 2)) * cerfc (a / (2 * w)))
      {z : ℂ | |z.im| < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) aux714_openSector_isOpen
    have hws : |w.im| < w.re := hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hws
      simp at hws
    have h4 : (4 : ℂ) * w ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hw0)
    have h2 : (2 : ℂ) * w ≠ 0 := mul_ne_zero two_ne_zero hw0
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (a ^ 2 / (4 * z ^ 2))) w :=
      DifferentiableAt.cexp ((differentiableAt_const _).div (by fun_prop) h4)
    have hd3 : DifferentiableAt ℂ (fun z : ℂ => cerfc (a / (2 * z))) w := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := cerfc) (f := fun z : ℂ => a / (2 * z)) w
        (aux714_differentiable_cerfc _) ((differentiableAt_const _).div (by fun_prop) h2)
      simpa [Function.comp] using h
    exact (((differentiableAt_const _).mul hd2).mul hd3).differentiableWithinAt
  exact aux714_eq_of_analytic_openSector hF hG (fun x hx => aux714_2_realb hx ha) b
    (aux714_abs_im_lt_re_of_arg hb0 hb)

-- no-dlmf: real/narrowed restriction of DLMF 7.14.3; faithful surface is cerf_7_14_3
/-- Laplace transform of `erf(√(b t))`, real specialization: for real `a, b > 0`,
`∫₀^∞ e^{-at} erf(√(bt)) dt = (1/a) √(b/(a+b))`
(DLMF 7.14.3 is stated for complex `a, b` with `Re a > 0`, `Re b > 0`).
-/
theorem erf_7_14_3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * erf (Real.sqrt (b * t))
      = (1 / a) * Real.sqrt (b / (a + b)) := by
  -- Routed through `FLMF.Methods.LaplaceTransform` (the anchor for M-laplace-transform):
  -- `laplaceTransform_erf_sqrt_eq_ofReal` bridges this real integral to the module's complex
  -- `laplaceTransform`, and `laplaceTransform_erf_sqrt` evaluates it via `laplaceTransform_deriv`
  -- (DLMF 1.14.27, the module's derivative rule), not by a direct `Ioi` integration by parts on
  -- the original integrand — see `Ch7LaplaceBridge.lean`.
  have h1 : FLMF.Methods.LaplaceTransform.laplaceTransform (fC b) (a : ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * erf (Real.sqrt (b*t))) : ℝ) :=
    laplaceTransform_erf_sqrt_eq_ofReal a b
  have h2 := laplaceTransform_erf_sqrt a b ha hb
  rw [h1] at h2
  exact_mod_cast h2

-- no-dlmf: `a`-direction analytic continuation of DLMF 7.14.3 at a positive real `b`;
-- the seed for the `b`-direction continuation in `cerf_7_14_3`
/-- DLMF 7.14.3 for a **positive real** second parameter `b` and complex `a` with
`Re a > 0`: the identity theorem in `a` applied to the real specialization
`erf_7_14_3`. -/
private lemma aux714_3_realb {b : ℝ} (hb : 0 < b) {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * cerf (Complex.sqrt ((b:ℂ) * (t:ℂ))))
      = (1 / a) * Complex.sqrt ((b:ℂ) / (a + (b:ℂ))) := by
  have hU : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbC : (0:ℝ) < ((b:ℂ)).re := by simpa using hb
  have hmul : ∀ t : ℝ, ((b:ℂ) * (t:ℂ)) = (((b * t : ℝ)) : ℂ) := by
    intro t; push_cast; ring
  have hχc : ContinuousOn (fun t : ℝ => cerf (Complex.sqrt ((b:ℂ) * (t:ℂ)))) (Ioi (0:ℝ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 : ContinuousAt (fun s : ℝ => ((b:ℂ) * (s:ℂ))) t := by fun_prop
    have h2 : ContinuousAt Complex.sqrt ((b:ℂ) * (t:ℂ)) := by
      refine Complex.continuousAt_sqrt (Or.inl ?_)
      rw [hmul t, Complex.ofReal_re]
      positivity
    have h3 : ContinuousAt (fun s : ℝ => Complex.sqrt ((b:ℂ) * (s:ℂ))) t := by
      have h := ContinuousAt.comp (g := Complex.sqrt) (f := fun s : ℝ => (b:ℂ) * (s:ℂ)) h2 h1
      simpa [Function.comp] using h
    have h4 : ContinuousAt (fun s : ℝ => cerf (Complex.sqrt ((b:ℂ) * (s:ℂ)))) t := by
      have h := ContinuousAt.comp (g := cerf) (f := fun s : ℝ => Complex.sqrt ((b:ℂ) * (s:ℂ)))
        (differentiable_cerf _).continuousAt h3
      simpa [Function.comp] using h
    exact h4.continuousWithinAt
  have hF : AnalyticOnNhd ℂ
      (fun c : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-c * (t:ℂ))
        * cerf (Complex.sqrt ((b:ℂ) * (t:ℂ)))) {c : ℂ | 0 < c.re} := by
    refine aux714_analyticOnNhd_laplace (C := 2 * Real.sqrt b / Real.sqrt π) (k := 1/2)
      (by norm_num) hχc (fun t ht => ?_)
    have hsq : (Complex.sqrt ((b:ℂ) * (t:ℂ)) ^ 2).re = b * t := by
      rw [aux714_csqrt_sq, hmul t, Complex.ofReal_re]
    have hbound := aux714_norm_cerf_le (z := Complex.sqrt ((b:ℂ) * (t:ℂ)))
      (by rw [hsq]; positivity)
    have hn : ‖Complex.sqrt ((b:ℂ) * (t:ℂ))‖ = Real.sqrt b * Real.sqrt t := by
      rw [aux714_norm_csqrt, hmul t, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < b * t), Real.sqrt_mul hb.le]
    rw [hn] at hbound
    calc ‖cerf (Complex.sqrt ((b:ℂ) * (t:ℂ)))‖
        ≤ 2 / Real.sqrt π * (Real.sqrt b * Real.sqrt t) := hbound
      _ = 2 * Real.sqrt b / Real.sqrt π * t ^ (1/2 : ℝ) := by
          rw [show Real.sqrt t = t ^ (1/2 : ℝ) from Real.sqrt_eq_rpow t]
          ring
  have hG : AnalyticOnNhd ℂ (fun c : ℂ => (1 / c) * Complex.sqrt ((b:ℂ) / (c + (b:ℂ))))
      {c : ℂ | 0 < c.re} := by
    refine DifferentiableOn.analyticOnNhd (fun c hc => ?_) hU
    have hcre : 0 < c.re := hc
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hcre
      simp at hcre
    have hsum : 0 < (c + (b:ℂ)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith
    have hsum0 : c + (b:ℂ) ≠ 0 := by
      intro h
      rw [h] at hsum
      simp at hsum
    have hslit : (b:ℂ) / (c + (b:ℂ)) ∈ Complex.slitPlane := aux714_div_mem_slitPlane hbC hsum
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => (b:ℂ) / (w + (b:ℂ))) c :=
      (differentiableAt_const _).div (differentiableAt_id.add_const _) hsum0
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => Complex.sqrt ((b:ℂ) / (w + (b:ℂ)))) c := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.sqrt)
        (f := fun w : ℂ => (b:ℂ) / (w + (b:ℂ))) c (Complex.differentiableAt_sqrt hslit) hd1
      simpa [Function.comp] using h
    exact (((differentiableAt_const (1:ℂ)).div differentiableAt_id hc0).mul
      hd2).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hpt : ∀ t ∈ Ioi (0:ℝ),
      Complex.exp (-(x:ℂ) * (t:ℂ)) * cerf (Complex.sqrt ((b:ℂ) * (t:ℂ)))
        = Complex.exp (-(x:ℂ) * (t:ℂ)) * ((erf (Real.sqrt (b * t)) : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    congr 1
    rw [hmul t, aux714_csqrt_ofReal (by positivity), cerf_ofReal]
  have hdiv : ((b:ℂ) / ((x:ℂ) + (b:ℂ))) = (((b / (x + b) : ℝ)) : ℂ) := by push_cast; ring
  have hnn : (0:ℝ) ≤ b / (x + b) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    aux714_laplace_ofReal (fun t : ℝ => erf (Real.sqrt (b * t))) x, erf_7_14_3 x b hx hb,
    hdiv, aux714_csqrt_ofReal hnn]
  push_cast
  ring

/-- **DLMF 7.14.3** — Laplace transform of the complex error function `erf(√(bt))`,
for complex `a, b` with `Re a > 0`, `Re b > 0`:
`∫₀^∞ e^{-at} erf(√(bt)) dt = (1/a) √(b/(a+b))`.

DAG: E-7.14.3.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem cerf_7_14_3 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * cerf (Complex.sqrt (b * (t:ℂ)))
      = (1 / a) * Complex.sqrt (b / (a + b)) := by
  have hU : IsOpen {c : ℂ | 0 < c.re} := isOpen_lt continuous_const Complex.continuous_re
  have hre : ∀ (w : ℂ) (t : ℝ), (w * (t:ℂ)).re = w.re * t := by
    intro w t
    simp [Complex.mul_re]
  have hslit : ∀ w : ℂ, 0 < w.re → ∀ t : ℝ, 0 < t → w * (t:ℂ) ∈ Complex.slitPlane := by
    intro w hw t ht
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hre]
    positivity
  have hnwt : ∀ (w : ℂ) (t : ℝ), 0 < t → ‖w * (t:ℂ)‖ = ‖w‖ * t := by
    intro w t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hnormexpA : ∀ t : ℝ, ‖Complex.exp (-a * (t:ℂ))‖ = Real.exp (-a.re * t) := by
    intro t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hnormexp : ∀ (w : ℂ) (t : ℝ), ‖Complex.exp (-(w * (t:ℂ)))‖ = Real.exp (-(w.re * t)) := by
    intro w t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hsqrtCont : ∀ w : ℂ, 0 < w.re →
      ContinuousOn (fun t : ℝ => Complex.sqrt (w * (t:ℂ))) (Ioi (0:ℝ)) := by
    intro w hw t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 : ContinuousAt (fun s : ℝ => (w * (s:ℂ))) t := by fun_prop
    have h2 : ContinuousAt Complex.sqrt (w * (t:ℂ)) :=
      Complex.continuousAt_sqrt (Or.inl (by rw [hre]; positivity))
    have h : ContinuousAt (fun s : ℝ => Complex.sqrt (w * (s:ℂ))) t := by
      have h := ContinuousAt.comp (g := Complex.sqrt) (f := fun s : ℝ => w * (s:ℂ)) h2 h1
      simpa [Function.comp] using h
    exact h.continuousWithinAt
  have hsqrtNe : ∀ w : ℂ, 0 < w.re → ∀ t : ℝ, 0 < t → Complex.sqrt (w * (t:ℂ)) ≠ 0 := by
    intro w hw t ht hc
    have h : (w * (t:ℂ)) = 0 := by
      rw [← aux714_csqrt_sq (w * (t:ℂ)), hc]
      ring
    have h2 : (w * (t:ℂ)).re = 0 := by rw [h]; simp
    rw [hre] at h2
    nlinarith
  have hmeas : ∀ w : ℂ, 0 < w.re → AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-a * (t:ℂ)) * cerf (Complex.sqrt (w * (t:ℂ))))
      (volume.restrict (Ioi (0:ℝ))) := by
    intro w hw
    refine (ContinuousOn.mul ?_ ?_).aestronglyMeasurable measurableSet_Ioi
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · exact (differentiable_cerf.continuous.comp_continuousOn (hsqrtCont w hw))
  have hmeas' : ∀ w : ℂ, 0 < w.re → AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-a * (t:ℂ)) *
        ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)))
          * (1 / (2 * Complex.sqrt (w * (t:ℂ))) * (t:ℂ)))) (volume.restrict (Ioi (0:ℝ))) := by
    intro w hw
    refine (ContinuousOn.mul ?_ (ContinuousOn.mul (ContinuousOn.mul ?_ ?_)
      (ContinuousOn.mul ?_ ?_))).aestronglyMeasurable measurableSet_Ioi
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · exact continuousOn_const
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · refine ContinuousOn.div continuousOn_const ((continuousOn_const).mul (hsqrtCont w hw)) ?_
      intro t ht
      exact mul_ne_zero two_ne_zero (hsqrtNe w hw t ht)
    · exact (Complex.continuous_ofReal).continuousOn
  have hF : AnalyticOnNhd ℂ
      (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a * (t:ℂ)) * cerf (Complex.sqrt (w * (t:ℂ))))
      {w : ℂ | 0 < w.re} := by
    refine FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane (c := 0) (d := 0)
      (f := fun w t => Complex.exp (-a * (t:ℂ)) * cerf (Complex.sqrt (w * (t:ℂ))))
      (f' := fun w t => Complex.exp (-a * (t:ℂ)) *
        ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)))
          * (1 / (2 * Complex.sqrt (w * (t:ℂ))) * (t:ℂ))))
      (fun w hw => hmeas w hw) (fun w hw => ?_) (fun w hw => hmeas' w hw) ?_ ?_
    · refine Integrable.mono' (g := fun t : ℝ => (2 * Real.sqrt ‖w‖ / Real.sqrt π) *
        (Real.exp (-a.re * t) * t ^ (1/2 : ℝ)))
        ((integrableOn_exp_neg_mul_rpow_Ioi a.re (1/2) ha (by norm_num)).const_mul _)
        (hmeas w hw) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      have hsq : 0 ≤ (Complex.sqrt (w * (t:ℂ)) ^ 2).re := by
        rw [aux714_csqrt_sq, hre]
        positivity
      have hbound := aux714_norm_cerf_le hsq
      have hn : ‖Complex.sqrt (w * (t:ℂ))‖ = Real.sqrt ‖w‖ * Real.sqrt t := by
        rw [aux714_norm_csqrt, hnwt w t ht0, Real.sqrt_mul (norm_nonneg w)]
      rw [hn] at hbound
      rw [norm_mul, hnormexpA t]
      calc Real.exp (-a.re * t) * ‖cerf (Complex.sqrt (w * (t:ℂ)))‖
          ≤ Real.exp (-a.re * t) * (2 / Real.sqrt π * (Real.sqrt ‖w‖ * Real.sqrt t)) := by
            gcongr
        _ = 2 * Real.sqrt ‖w‖ / Real.sqrt π * (Real.exp (-a.re * t) * t ^ (1/2 : ℝ)) := by
            rw [show t ^ (1/2 : ℝ) = Real.sqrt t from (Real.sqrt_eq_rpow t).symm]
            ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have ht0 : (0:ℝ) < t := ht
      have hs : w * (t:ℂ) ∈ Complex.slitPlane := hslit w hw t ht0
      have h1 : HasDerivAt (fun z : ℂ => z * (t:ℂ)) (t:ℂ) w := by
        simpa using (hasDerivAt_id w).mul_const (t:ℂ)
      have h2 : HasDerivAt Complex.sqrt (1 / (2 * Complex.sqrt (w * (t:ℂ)))) (w * (t:ℂ)) :=
        aux714_hasDerivAt_csqrt hs
      have h3 : HasDerivAt (fun z : ℂ => Complex.sqrt (z * (t:ℂ)))
          (1 / (2 * Complex.sqrt (w * (t:ℂ))) * (t:ℂ)) w := by
        have h := HasDerivAt.comp (𝕜 := ℂ) w h2 h1
        simpa [Function.comp] using h
      have h4 : HasDerivAt cerf ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ))))
          (Complex.sqrt (w * (t:ℂ))) := by
        have h := hasDerivAt_cerf (Complex.sqrt (w * (t:ℂ)))
        rwa [aux714_csqrt_sq] at h
      have h5 : HasDerivAt (fun z : ℂ => cerf (Complex.sqrt (z * (t:ℂ))))
          ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(w * (t:ℂ)))
            * (1 / (2 * Complex.sqrt (w * (t:ℂ))) * (t:ℂ))) w := by
        have h := HasDerivAt.comp (𝕜 := ℂ) w h4 h3
        simpa [Function.comp] using h
      exact h5.const_mul (Complex.exp (-a * (t:ℂ)))
    · intro σ hσ
      refine ⟨fun t : ℝ => 1 / (Real.sqrt π * Real.sqrt σ) *
        (Real.exp (-(a.re + σ) * t) * t ^ (1/2 : ℝ)), ?_, ?_⟩
      · exact (integrableOn_exp_neg_mul_rpow_Ioi (a.re + σ) (1/2) (by linarith)
          (by norm_num)).const_mul _
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have ht0 : (0:ℝ) < t := ht
      have hwre : 0 < w.re := lt_of_lt_of_le hσ hw
      have hwn : (0:ℝ) < ‖w‖ := by
        have : (0:ℝ) < w.re := hwre
        have h2 : w.re ≤ ‖w‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm w)
        linarith
      have e3 : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / Real.sqrt π := by
        rw [show ((2 : ℂ) / (Real.sqrt Real.pi : ℂ)) = (((2 / Real.sqrt Real.pi : ℝ)) : ℂ) by
          push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have e4 : ‖(1 : ℂ) / (2 * Complex.sqrt (w * (t:ℂ))) * (t:ℂ)‖
          = t / (2 * (Real.sqrt ‖w‖ * Real.sqrt t)) := by
        rw [norm_mul, norm_div, norm_one, norm_mul, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num,
          aux714_norm_csqrt, hnwt w t ht0,
          Real.sqrt_mul (norm_nonneg w), Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
        have hsw : (0:ℝ) < Real.sqrt ‖w‖ := Real.sqrt_pos.mpr hwn
        field_simp
      rw [norm_mul, norm_mul, norm_mul, hnormexpA t, hnormexp w t, e3, e4]
      have hsimp : t / (2 * (Real.sqrt ‖w‖ * Real.sqrt t))
          = Real.sqrt t / (2 * Real.sqrt ‖w‖) := by
        have h1 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
        have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
        have hsw : (0:ℝ) < Real.sqrt ‖w‖ := Real.sqrt_pos.mpr hwn
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-2 * Real.sqrt ‖w‖) * h1
      rw [hsimp]
      have hb1 : Real.exp (-(w.re * t)) ≤ Real.exp (-(σ * t)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hb2 : Real.sqrt σ ≤ Real.sqrt ‖w‖ := by
        apply Real.sqrt_le_sqrt
        exact le_trans hw (le_trans (le_abs_self _) (Complex.abs_re_le_norm w))
      have hsσ : (0:ℝ) < Real.sqrt σ := Real.sqrt_pos.mpr hσ
      calc Real.exp (-a.re * t) * (2 / Real.sqrt π * Real.exp (-(w.re * t))
            * (Real.sqrt t / (2 * Real.sqrt ‖w‖)))
          ≤ Real.exp (-a.re * t) * (2 / Real.sqrt π * Real.exp (-(σ * t))
            * (Real.sqrt t / (2 * Real.sqrt σ))) := by
            gcongr
        _ = 1 / (Real.sqrt π * Real.sqrt σ) * (Real.exp (-(a.re + σ) * t) * t ^ (1/2 : ℝ)) := by
            rw [show t ^ (1/2 : ℝ) = Real.sqrt t from (Real.sqrt_eq_rpow t).symm,
              show -(a.re + σ) * t = -a.re * t + -(σ * t) by ring, Real.exp_add]
            have hsπ : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
            field_simp
  have hG : AnalyticOnNhd ℂ (fun w : ℂ => (1 / a) * Complex.sqrt (w / (a + w)))
      {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hU
    have hwre : 0 < w.re := hw
    have hsum : 0 < (a + w).re := by
      rw [Complex.add_re]
      linarith
    have hsum0 : a + w ≠ 0 := by
      intro h
      rw [h] at hsum
      simp at hsum
    have hslitw : w / (a + w) ∈ Complex.slitPlane := aux714_div_mem_slitPlane hwre hsum
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => z / (a + z)) w :=
      differentiableAt_id.div ((differentiableAt_const a).add differentiableAt_id) hsum0
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z / (a + z))) w := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.sqrt)
        (f := fun z : ℂ => z / (a + z)) w (Complex.differentiableAt_sqrt hslitw) hd1
      simpa [Function.comp] using h
    exact ((differentiableAt_const _).mul hd2).differentiableWithinAt
  exact aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => aux714_3_realb hx ha) b hb

section Ch714_4Support

-- no-dlmf: `Re √w ≥ 0` for the principal square root, support lemma for DLMF 7.14.4
private lemma aux7144_re_csqrt_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

-- no-dlmf: `Re w ≥ 0 ⟹ √w` lies in the closed cone `|Im| ≤ Re`, support lemma for DLMF 7.14.4
private lemma aux7144_cone_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) :
    |(Complex.sqrt w).im| ≤ (Complex.sqrt w).re := by
  have hx : 0 ≤ (Complex.sqrt w).re := aux7144_re_csqrt_nonneg w
  have h2 : (Complex.sqrt w ^ 2).re = (Complex.sqrt w).re ^ 2 - (Complex.sqrt w).im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  rw [aux714_csqrt_sq] at h2
  nlinarith [sq_abs (Complex.sqrt w).im, abs_nonneg (Complex.sqrt w).im]

-- no-dlmf: the closed cone `|Im| ≤ Re` has nonnegative-real-part products, support lemma for DLMF 7.14.4
private lemma aux7144_re_mul_nonneg_of_cone {u v : ℂ} (hu : |u.im| ≤ u.re) (hv : |v.im| ≤ v.re) :
    0 ≤ (u * v).re := by
  rw [Complex.mul_re]
  nlinarith [abs_nonneg u.im, abs_nonneg v.im, le_abs_self (u.im * v.im), abs_mul u.im v.im,
    neg_abs_le (u.im * v.im)]

-- no-dlmf: the closed cone `|Im| ≤ Re` is closed under addition, support lemma for DLMF 7.14.4
private lemma aux7144_cone_add {u v : ℂ} (hu : |u.im| ≤ u.re) (hv : |v.im| ≤ v.re) :
    |(u + v).im| ≤ (u + v).re := by
  rw [Complex.add_re, Complex.add_im]
  calc |u.im + v.im| ≤ |u.im| + |v.im| := abs_add_le _ _
    _ ≤ u.re + v.re := by linarith

-- no-dlmf: cone bridge `|Im z| ≤ Re z ⟹ |ph z| ≤ π/4`, support lemma for DLMF 7.14.4
private lemma aux7144_arg_le_pi_div_four {z : ℂ} (hz : z ≠ 0) (h : |z.im| ≤ z.re) :
    |Complex.arg z| ≤ Real.pi / 4 := by
  have hre : 0 ≤ z.re := le_trans (abs_nonneg _) h
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : |z.im / ‖z‖| ≤ Real.sqrt 2 / 2 := by
    rw [abs_div, abs_of_pos hn, div_le_div_iff₀ hn (by norm_num)]
    have hsq : (|z.im| * 2) ^ 2 ≤ (Real.sqrt 2 * ‖z‖) ^ 2 := by
      nlinarith [sq_abs z.im, abs_nonneg z.im, hnsq, hs2sq, h, hre]
    have hle := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hle
  have hq : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Complex.arg_of_re_nonneg hre, abs_le]
  rw [abs_le] at hb
  constructor
  · have h1 : Real.arcsin (-(Real.sqrt 2 / 2)) ≤ Real.arcsin (z.im / ‖z‖) :=
      Real.arcsin_le_arcsin hb.1
    rwa [Real.arcsin_neg, hq] at h1
  · have h1 : Real.arcsin (z.im / ‖z‖) ≤ Real.arcsin (Real.sqrt 2 / 2) :=
      Real.arcsin_le_arcsin hb.2
    rwa [hq] at h1

-- no-dlmf: `√(uv) = √u √v` when the phases add inside `(-π, π]`, support lemma for DLMF 7.14.4
private lemma aux7144_csqrt_mul {u v : ℂ} (hu : 0 < u.re) (hv : 0 ≤ v.re) :
    Complex.sqrt (u * v) = Complex.sqrt u * Complex.sqrt v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hargu : |Complex.arg u| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hargv : |Complex.arg v| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hv
  rw [abs_lt] at hargu
  rw [abs_le] at hargv
  have harg : Complex.arg u + Complex.arg v ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith [hargu.1, hargv.1]
    · linarith [hargu.2, hargv.2]
  rw [sqrt_eq_exp (mul_ne_zero hu0 hv0), sqrt_eq_exp hu0, sqrt_eq_exp hv0,
    Complex.log_mul hu0 hv0 harg, ← Complex.exp_add]
  ring_nf

-- no-dlmf: real-scalar special case, support lemma for DLMF 7.14.4
private lemma aux7144_csqrt_mul_ofReal {u : ℂ} (hu : 0 ≤ u.re) {t : ℝ} (ht : 0 < t) :
    Complex.sqrt (u * (t : ℂ)) = Complex.sqrt u * (Real.sqrt t : ℂ) := by
  have h : Complex.sqrt ((t : ℂ) * u) = Complex.sqrt (t : ℂ) * Complex.sqrt u :=
    aux7144_csqrt_mul (by simpa using ht) hu
  rw [mul_comm u (t : ℂ), h, mul_comm]
  congr 1
  rw [Complex.sqrt, Real.sqrt_eq_rpow,
    show ((2 : ℂ))⁻¹ = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow ht.le]

-- no-dlmf: elementary bound `‖erfc z‖ ≤ 1 + (2/√π)‖z‖` on the closed cone, support lemma for DLMF 7.14.4
private lemma aux7144_norm_cerfc_le {z : ℂ} (hz : 0 ≤ (z ^ 2).re) :
    ‖cerfc z‖ ≤ 1 + (2 / Real.sqrt π) * ‖z‖ := by
  unfold cerfc
  calc ‖1 - cerf z‖ ≤ ‖(1:ℂ)‖ + ‖cerf z‖ := norm_sub_le _ _
    _ ≤ 1 + (2 / Real.sqrt π) * ‖z‖ := by
        rw [norm_one]; gcongr; exact aux714_norm_cerf_le hz

-- no-dlmf: Gaussian decay of `erfc` on the closed cone `|ph z| ≤ π/4`, support lemma for DLMF 7.14.4
private lemma aux7144_cerfc_cone_bound {z : ℂ} (hz0 : z ≠ 0) (hcone : |z.im| ≤ z.re) :
    ‖cerfc z‖ ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ‖z‖) * Real.exp (-(z ^ 2).re) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  have hsp : (0:ℝ) < Real.sqrt Real.pi := by positivity
  have hE : (0:ℝ) < Real.exp ((z ^ 2).re) := Real.exp_pos _
  have hsec : |Complex.arg z| ≤ 3 * Real.pi / 4 - Real.pi / 2 := by
    have := aux7144_arg_le_pi_div_four hz0 hcone
    linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 2) (by positivity) (by linarith) hz0 hsec 0
  rw [Finset.range_zero, Finset.sum_empty, sub_zero] at h
  have hsin : Real.sin (2 * (Real.pi / 2) / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * (Real.pi / 2) / 3 = Real.pi / 3 by ring, Real.sin_pi_div_three]
  have hL : ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z‖
      = Real.sqrt Real.pi * Real.exp ((z ^ 2).re) * ‖cerfc z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  rw [hL] at h
  have hR : 2 * (Nat.factorial (2 * 0) : ℝ) / (2 * (Real.sin (2 * (Real.pi / 2) / 3) * ‖z‖))
      ^ (2 * 0 + 1) = 2 / (Real.sqrt 3 * ‖z‖) := by
    rw [hsin]
    norm_num
    ring
  rw [hR] at h
  have h' : ‖cerfc z‖ * (Real.sqrt Real.pi * Real.exp ((z ^ 2).re))
      ≤ 2 / (Real.sqrt 3 * ‖z‖) := by
    rw [show ‖cerfc z‖ * (Real.sqrt Real.pi * Real.exp ((z ^ 2).re))
        = Real.sqrt Real.pi * Real.exp ((z ^ 2).re) * ‖cerfc z‖ by ring]
    exact h
  rw [← le_div_iff₀ (by positivity)] at h'
  refine h'.trans_eq ?_
  rw [Real.exp_neg]
  field_simp

-- no-dlmf: Glasser master integral, support lemma for DLMF 7.14.4
private lemma aux7144_J1 {β γ : ℂ} (hβ0 : β ≠ 0) (hβ : |Complex.arg β| < Real.pi / 4)
    (hγ : |Complex.arg γ| < Real.pi / 4) :
    (∫ t in Ioi (0:ℝ), ((Real.sqrt t : ℝ) : ℂ)⁻¹ *
        Complex.exp (-β ^ 2 * (t:ℂ) - γ ^ 2 / (t:ℂ)))
      = ((Real.sqrt Real.pi : ℂ) / β) * Complex.exp (-2 * β * γ) := by
  have hsub := integral_comp_rpow_Ioi
      (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ *
        Complex.exp (-β ^ 2 * (y:ℂ) - γ ^ 2 / (y:ℂ))) (p := 2) (by norm_num)
  rw [← hsub]
  have hpt : ∀ x ∈ Ioi (0:ℝ),
      (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • (((Real.sqrt (x ^ (2:ℝ)) : ℝ) : ℂ)⁻¹ *
        Complex.exp (-β ^ 2 * ((x ^ (2:ℝ) : ℝ):ℂ) - γ ^ 2 / ((x ^ (2:ℝ) : ℝ):ℂ)))
      = 2 * Complex.exp (-β ^ 2 * (x:ℂ) ^ 2 - γ ^ 2 / (x:ℂ) ^ 2) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have h1 : x ^ ((2:ℝ) - 1) = x := by norm_num [Real.rpow_one]
    have h2 : x ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have h3 : Real.sqrt (x ^ 2) = x := Real.sqrt_sq hx0.le
    have h4 : ((x ^ 2 : ℝ) : ℂ) = (x:ℂ) ^ 2 := by push_cast; ring
    have hxne : ((x:ℝ):ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    rw [h1, h2, h3, h4, Complex.real_smul]
    push_cast
    field_simp
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    erf_7_7_8_dlmf hβ hγ]
  field_simp

-- no-dlmf: the erfc argument lies in the closed cone `|Im| ≤ Re`, support lemma for DLMF 7.14.4
private lemma aux7144_z_cone {a c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    |(Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))).im|
      ≤ (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))).re := by
  refine aux7144_cone_add (aux7144_cone_of_re_nonneg ?_) (aux7144_cone_of_re_nonneg ?_)
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    positivity
  · rw [Complex.div_ofReal_re]
    positivity

-- no-dlmf: `Re (z²) ≥ a.re * t + c.re / t`, support lemma for DLMF 7.14.4
private lemma aux7144_z_re_sq_ge {a c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    a.re * t + c.re / t
      ≤ ((Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))) ^ 2).re := by
  set u := Complex.sqrt (a * (t:ℂ)) with hu
  set v := Complex.sqrt (c / (t:ℂ)) with hv
  have hare : (a * (t:ℂ)).re = a.re * t := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hcre : (c / (t:ℂ)).re = c.re / t := Complex.div_ofReal_re c t
  have hu2 : u ^ 2 = a * (t:ℂ) := aux714_csqrt_sq _
  have hv2 : v ^ 2 = c / (t:ℂ) := aux714_csqrt_sq _
  have hcu : |u.im| ≤ u.re := aux7144_cone_of_re_nonneg (by rw [hare]; positivity)
  have hcv : |v.im| ≤ v.re := aux7144_cone_of_re_nonneg (by rw [hcre]; positivity)
  have hexp : ((u + v) ^ 2).re = (u ^ 2).re + (v ^ 2).re + 2 * (u * v).re := by
    rw [show (u + v) ^ 2 = u ^ 2 + v ^ 2 + 2 * (u * v) by ring]
    simp [Complex.add_re, Complex.mul_re]
  rw [hexp, hu2, hv2, hare, hcre]
  have := aux7144_re_mul_nonneg_of_cone hcu hcv
  linarith

-- no-dlmf: lower bound on `‖z‖`, support lemma for DLMF 7.14.4
private lemma aux7144_z_norm_ge {a c : ℂ} (ha : 0 ≤ a.re) {t : ℝ} (ht : 0 < t) :
    (Complex.sqrt a).re * Real.sqrt t
      ≤ ‖Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))‖ := by
  have hsplit : Complex.sqrt (a * (t:ℂ)) = Complex.sqrt a * (Real.sqrt t : ℂ) :=
    aux7144_csqrt_mul_ofReal ha ht
  have h1 : (Complex.sqrt (a * (t:ℂ))).re = (Complex.sqrt a).re * Real.sqrt t := by
    rw [hsplit]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h2 : 0 ≤ (Complex.sqrt (c / (t:ℂ))).re := aux7144_re_csqrt_nonneg _
  have h3 := Complex.re_le_norm (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))
  rw [Complex.add_re, h1] at h3
  linarith

-- no-dlmf: upper bound on `‖z‖`, support lemma for DLMF 7.14.4
private lemma aux7144_z_norm_le {a c : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))‖
      ≤ Real.sqrt (‖a‖ * t) + Real.sqrt (‖c‖ / t) := by
  refine (norm_add_le _ _).trans ?_
  rw [aux714_norm_csqrt, aux714_norm_csqrt, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]

-- no-dlmf: continuity in `t` of the 7.14.4 integrand on `(0, ∞)`, support lemma for DLMF 7.14.4
private lemma aux7144_integrand_continuousOn {a b c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) :
    ContinuousOn (fun t : ℝ => Complex.exp ((a - b) * (t:ℂ))
      * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))) (Ioi 0) := by
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  have htne : ((t:ℝ):ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun s : ℝ => Complex.exp ((a - b) * (s:ℂ))) t := by fun_prop
  have h2 : ContinuousAt (fun s : ℝ => Complex.sqrt (a * (s:ℂ))) t := by
    refine ContinuousAt.comp (Complex.continuousAt_sqrt (Or.inl ?_)) (by fun_prop)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    positivity
  have h3 : ContinuousAt (fun s : ℝ => Complex.sqrt (c / (s:ℂ))) t := by
    refine ContinuousAt.comp (Complex.continuousAt_sqrt (Or.inl ?_)) ?_
    · rw [Complex.div_ofReal_re]; positivity
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) htne
  exact h1.mul (aux714_differentiable_cerfc.continuous.continuousAt.comp (h2.add h3))

-- no-dlmf: majorant with the `c`-decay factor, `Re a > 0`, support lemma for DLMF 7.14.4
private lemma aux7144_integrand_bound_decay {a b c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))‖
      ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
          * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) * Real.exp (-(c.re / t)) := by
  have hπ : (0:ℝ) < Real.sqrt Real.pi := by positivity
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  have hα : 0 < (Complex.sqrt a).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl ha))
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set z := Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)) with hzdef
  have hzge : (Complex.sqrt a).re * Real.sqrt t ≤ ‖z‖ := aux7144_z_norm_ge ha.le ht
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hzge
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hcone : |z.im| ≤ z.re := aux7144_z_cone ha.le hc ht
  have hsq : a.re * t + c.re / t ≤ (z ^ 2).re := aux7144_z_re_sq_ge ha.le hc ht
  have hcdiv : 0 ≤ c.re / t := by positivity
  have hexp : ‖Complex.exp ((a - b) * (t:ℂ))‖ = Real.exp ((a.re - b.re) * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  have step1 : ‖cerfc z‖
      ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ((Complex.sqrt a).re * Real.sqrt t))
          * Real.exp (-(a.re * t + c.re / t)) := by
    refine (aux7144_cerfc_cone_bound hz0 hcone).trans ?_
    gcongr
  have hrp : t ^ (-(1:ℝ)/2) = (Real.sqrt t)⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  calc ‖Complex.exp ((a - b) * (t:ℂ)) * cerfc z‖
      = Real.exp ((a.re - b.re) * t) * ‖cerfc z‖ := by rw [norm_mul, hexp]
    _ ≤ Real.exp ((a.re - b.re) * t)
          * (2 / (Real.sqrt 3 * Real.sqrt Real.pi * ((Complex.sqrt a).re * Real.sqrt t))
              * Real.exp (-(a.re * t + c.re / t))) := by
        exact mul_le_mul_of_nonneg_left step1 (Real.exp_nonneg _)
    _ = 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
          * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) * Real.exp (-(c.re / t)) := by
        rw [hrp, show Real.exp ((a.re - b.re) * t)
              * (2 / (Real.sqrt 3 * Real.sqrt Real.pi * ((Complex.sqrt a).re * Real.sqrt t))
                * Real.exp (-(a.re * t + c.re / t)))
            = (Real.exp ((a.re - b.re) * t) * Real.exp (-(a.re * t + c.re / t)))
              * (2 / (Real.sqrt 3 * Real.sqrt Real.pi
                * ((Complex.sqrt a).re * Real.sqrt t))) by ring,
          ← Real.exp_add,
          show (a.re - b.re) * t + -(a.re * t + c.re / t) = -b.re * t + -(c.re / t) by ring,
          Real.exp_add]
        field_simp

-- no-dlmf: plain majorant, support lemma for DLMF 7.14.4
private lemma aux7144_integrand_bound_pos {a b c : ℂ} (ha : 0 < a.re) (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))‖
      ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
          * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) := by
  refine (aux7144_integrand_bound_decay ha hc ht).trans ?_
  have hα : 0 < (Complex.sqrt a).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl ha))
  have h1 : Real.exp (-(c.re / t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c.re / t := by positivity
    linarith
  have h2 : (0:ℝ) ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
      * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) := by positivity
  nlinarith

-- no-dlmf: integrability of the 7.14.4 integrand for `Re a > 0`, support lemma for DLMF 7.14.4
private lemma aux7144_lhs_integrable {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    IntegrableOn (fun t : ℝ => Complex.exp ((a - b) * (t:ℂ))
      * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))) (Ioi 0) := by
  refine Integrable.mono' (g := fun t : ℝ =>
      2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
        * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)))
    ((integrableOn_exp_neg_mul_rpow_Ioi b.re (-(1:ℝ)/2) hb (by norm_num)).const_mul _)
    ((aux7144_integrand_continuousOn ha.le hc).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact aux7144_integrand_bound_pos ha hc ht

-- no-dlmf: `√(c/t) = √c/√t`, support lemma for DLMF 7.14.4
private lemma aux7144_csqrt_div_ofReal {u : ℂ} (hu : 0 ≤ u.re) {t : ℝ} (ht : 0 < t) :
    Complex.sqrt (u / (t : ℂ)) = Complex.sqrt u * ((Real.sqrt t : ℝ) : ℂ)⁻¹ := by
  have h0 : u / (t : ℂ) = u * ((1 / t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h0, aux7144_csqrt_mul_ofReal hu (by positivity : (0:ℝ) < 1 / t)]
  congr 1
  rw [one_div, Real.sqrt_inv, Complex.ofReal_inv]

-- no-dlmf: the square of the erfc argument, support lemma for DLMF 7.14.4
private lemma aux7144_z_sq_eq {a c : ℂ} (ha : 0 ≤ a.re) (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))) ^ 2
      = a * (t:ℂ) + c / (t:ℂ) + 2 * (Complex.sqrt a * Complex.sqrt c) := by
  have hS : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hSsq : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = ((t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  have h1 : Complex.sqrt (a * (t:ℂ)) = Complex.sqrt a * ((Real.sqrt t : ℝ) : ℂ) :=
    aux7144_csqrt_mul_ofReal ha ht
  have h2 : Complex.sqrt (c / (t:ℂ)) = Complex.sqrt c * ((Real.sqrt t : ℝ) : ℂ)⁻¹ :=
    aux7144_csqrt_div_ofReal hc ht
  have key : ∀ A C S : ℂ, S ≠ 0 →
      (A * S + C * S⁻¹) ^ 2 = A ^ 2 * S ^ 2 + C ^ 2 / S ^ 2 + 2 * (A * C) := by
    intro A C S hS'
    field_simp
    ring
  rw [h1, h2, key _ _ _ hS, aux714_csqrt_sq, aux714_csqrt_sq, hSsq]

-- no-dlmf: `c`-derivative of the 7.14.4 integrand, support lemma for DLMF 7.14.4
private lemma aux7144_hasDerivAt_integrand {a b : ℂ} (ha : 0 ≤ a.re) {c : ℂ} (hc : 0 < c.re) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun w : ℂ => Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (w / (t:ℂ))))
      (-(1 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
        * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹
        * Complex.exp (-b * (t:ℂ) - c / (t:ℂ))) c := by
  have htne : ((t:ℝ):ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hS : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hSsq : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = ((t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hcne : Complex.sqrt c ≠ 0 := by
    intro h
    have h2 := aux714_csqrt_sq c
    rw [h] at h2
    simp at h2
    exact hc0 h2.symm
  have hslit : c / (t:ℂ) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [Complex.div_ofReal_re]
    positivity
  have hsc : Complex.sqrt (c / (t:ℂ)) = Complex.sqrt c * ((Real.sqrt t : ℝ) : ℂ)⁻¹ :=
    aux7144_csqrt_div_ofReal hc.le ht
  have hd1 : HasDerivAt (fun w : ℂ => w / (t:ℂ)) (1 / (t:ℂ)) c := by
    simpa using (hasDerivAt_id c).div_const ((t:ℝ):ℂ)
  have hd2 : HasDerivAt (fun w : ℂ => Complex.sqrt (w / (t:ℂ)))
      (1 / (2 * Complex.sqrt (c / (t:ℂ))) * (1 / (t:ℂ))) c := by
    simpa [Function.comp] using (aux714_hasDerivAt_csqrt hslit).comp c hd1
  have hd3 : HasDerivAt (fun w : ℂ => Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (w / (t:ℂ)))
      (1 / (2 * Complex.sqrt (c / (t:ℂ))) * (1 / (t:ℂ))) c := by
    simpa using hd2.const_add (Complex.sqrt (a * (t:ℂ)))
  have hd4 : HasDerivAt cerfc
      (-((2 / (Real.sqrt Real.pi : ℂ))
        * Complex.exp (-(Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))) ^ 2)))
      (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))) :=
    (hasDerivAt_cerf _).const_sub 1
  have hd5 := (hd4.comp c hd3).const_mul (Complex.exp ((a - b) * (t:ℂ)))
  simp only [Function.comp] at hd5
  convert hd5 using 1
  rw [aux7144_z_sq_eq ha hc.le ht, hsc]
  have hexp : Complex.exp ((a - b) * (t:ℂ))
      * Complex.exp (-(a * (t:ℂ) + c / (t:ℂ) + 2 * (Complex.sqrt a * Complex.sqrt c)))
      = Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
        * Complex.exp (-b * (t:ℂ) - c / (t:ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hscal : (1 / (2 * (Complex.sqrt c * ((Real.sqrt t : ℝ) : ℂ)⁻¹)) * (1 / (t:ℂ)))
      = 1 / 2 * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹ := by
    rw [show ((t:ℝ):ℂ) = ((Real.sqrt t : ℝ) : ℂ) ^ 2 from hSsq.symm]
    field_simp
  rw [hscal, show Complex.exp ((a - b) * (t:ℂ)) *
        (-((2 / (Real.sqrt Real.pi : ℂ))
          * Complex.exp (-(a * (t:ℂ) + c / (t:ℂ) + 2 * (Complex.sqrt a * Complex.sqrt c))))
        * (1 / 2 * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹))
      = (Complex.exp ((a - b) * (t:ℂ))
          * Complex.exp (-(a * (t:ℂ) + c / (t:ℂ) + 2 * (Complex.sqrt a * Complex.sqrt c))))
        * (-(2 / (Real.sqrt Real.pi : ℂ))
          * (1 / 2 * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹)) from by ring,
    hexp]
  ring

-- no-dlmf: strict cone, support lemma for DLMF 7.14.4
private lemma aux7144_csqrt_strict_cone {w : ℂ} (hw : 0 < w.re) :
    |(Complex.sqrt w).im| < (Complex.sqrt w).re := by
  have hx : 0 ≤ (Complex.sqrt w).re := aux7144_re_csqrt_nonneg w
  have h2 : (Complex.sqrt w ^ 2).re = (Complex.sqrt w).re ^ 2 - (Complex.sqrt w).im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  rw [aux714_csqrt_sq] at h2
  nlinarith [sq_abs (Complex.sqrt w).im, abs_nonneg (Complex.sqrt w).im]

-- no-dlmf: strict phase bound, support lemma for DLMF 7.14.4
private lemma aux7144_arg_lt_pi_div_four {z : ℂ} (h : |z.im| < z.re) : |Complex.arg z| < Real.pi / 4 := by
  have hre : 0 < z.re := lt_of_le_of_lt (abs_nonneg _) h
  have hz : z ≠ 0 := by
    intro hcon
    rw [hcon] at hre
    simp at hre
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2le : Real.sqrt 2 / 2 ≤ 1 := by nlinarith
  have hb : |z.im / ‖z‖| < Real.sqrt 2 / 2 := by
    rw [abs_div, abs_of_pos hn, div_lt_div_iff₀ hn (by norm_num)]
    have hsq : (|z.im| * 2) ^ 2 < (Real.sqrt 2 * ‖z‖) ^ 2 := by
      nlinarith [sq_abs z.im, abs_nonneg z.im, hnsq, hs2sq, h, hre]
    nlinarith [abs_nonneg z.im, hn.le, hs2.le, mul_nonneg hs2.le hn.le]
  have hq : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Complex.arg_of_re_nonneg hre.le, abs_lt]
  rw [abs_lt] at hb
  constructor
  · have h1 : Real.arcsin (-(Real.sqrt 2 / 2)) < Real.arcsin (z.im / ‖z‖) :=
      Real.arcsin_lt_arcsin (by linarith) hb.1 (by linarith [hb.2])
    rwa [Real.arcsin_neg, hq] at h1
  · have h1 : Real.arcsin (z.im / ‖z‖) < Real.arcsin (Real.sqrt 2 / 2) :=
      Real.arcsin_lt_arcsin (by linarith [hb.1]) hb.2 hs2le
    rwa [hq] at h1

-- no-dlmf: integral of the parameter derivative, support lemma for DLMF 7.14.4
private lemma aux7144_integral_deriv_value {a b c : ℂ} (hb : 0 < b.re) (hc : 0 < c.re) :
    (∫ t in Ioi (0:ℝ), -(1 / (Real.sqrt Real.pi : ℂ))
        * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
        * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹
        * Complex.exp (-b * (t:ℂ) - c / (t:ℂ)))
      = -(Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c
            + Complex.sqrt b * Complex.sqrt c)) / (Complex.sqrt b * Complex.sqrt c)) := by
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb; simp at hb
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; simp at hc
  have hbne : Complex.sqrt b ≠ 0 := by
    intro h
    have h2 := aux714_csqrt_sq b
    rw [h] at h2
    simp at h2
    exact hb0 h2.symm
  have hcne : Complex.sqrt c ≠ 0 := by
    intro h
    have h2 := aux714_csqrt_sq c
    rw [h] at h2
    simp at h2
    exact hc0 h2.symm
  have hargb : |Complex.arg (Complex.sqrt b)| < Real.pi / 4 :=
    aux7144_arg_lt_pi_div_four (aux7144_csqrt_strict_cone hb)
  have hargc : |Complex.arg (Complex.sqrt c)| < Real.pi / 4 :=
    aux7144_arg_lt_pi_div_four (aux7144_csqrt_strict_cone hc)
  set K : ℂ := -(1 / (Real.sqrt Real.pi : ℂ))
    * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c)) * (Complex.sqrt c)⁻¹ with hK
  have hcongr : ∀ t : ℝ, -(1 / (Real.sqrt Real.pi : ℂ))
      * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
      * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹
      * Complex.exp (-b * (t:ℂ) - c / (t:ℂ))
      = K * (((Real.sqrt t : ℝ) : ℂ)⁻¹
          * Complex.exp (-Complex.sqrt b ^ 2 * (t:ℂ) - Complex.sqrt c ^ 2 / (t:ℂ))) := by
    intro t
    rw [aux714_csqrt_sq, aux714_csqrt_sq, hK]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t), integral_const_mul,
    aux7144_J1 hbne hargb hargc, hK,
    show Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c
          + Complex.sqrt b * Complex.sqrt c))
        = Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
          * Complex.exp (-2 * Complex.sqrt b * Complex.sqrt c) from by
      rw [← Complex.exp_add]; congr 1; ring]
  field_simp

-- no-dlmf: uniform bound on the parameter derivative, support lemma for DLMF 7.14.4
private lemma aux7144_deriv_bound {a b c : ℂ} (ha : 0 ≤ a.re) {σ : ℝ} (hσ : 0 < σ) (hcσ : σ ≤ c.re)
    {t : ℝ} (ht : 0 < t) :
    ‖-(1 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))
        * (Complex.sqrt c)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹
        * Complex.exp (-b * (t:ℂ) - c / (t:ℂ))‖
      ≤ 1 / (Real.sqrt Real.pi * Real.sqrt σ) * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) := by
  have hπ : (0:ℝ) < Real.sqrt Real.pi := by positivity
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsσ : (0:ℝ) < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hcre : 0 < c.re := lt_of_lt_of_le hσ hcσ
  have hac : 0 ≤ (Complex.sqrt a * Complex.sqrt c).re :=
    aux7144_re_mul_nonneg_of_cone (aux7144_cone_of_re_nonneg ha) (aux7144_cone_of_re_nonneg hcre.le)
  have hrp : t ^ (-(1:ℝ)/2) = (Real.sqrt t)⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have e1 : ‖-(1 / (Real.sqrt Real.pi : ℂ))‖ = 1 / Real.sqrt Real.pi := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]
  have e2 : ‖Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c))‖
      = Real.exp (-2 * (Complex.sqrt a * Complex.sqrt c).re) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have e3 : ‖(Complex.sqrt c)⁻¹‖ = 1 / Real.sqrt ‖c‖ := by
    rw [norm_inv, aux714_norm_csqrt, one_div]
  have e4 : ‖((Real.sqrt t : ℝ) : ℂ)⁻¹‖ = 1 / Real.sqrt t := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hst, one_div]
  have e5 : ‖Complex.exp (-b * (t:ℂ) - c / (t:ℂ))‖ = Real.exp (-b.re * t - c.re / t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.sub_re, Complex.mul_re, Complex.div_ofReal_re]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, e1, e2, e3, e4, e5, hrp]
  have hb1 : Real.exp (-2 * (Complex.sqrt a * Complex.sqrt c).re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hb2 : 1 / Real.sqrt ‖c‖ ≤ 1 / Real.sqrt σ := by
    refine one_div_le_one_div_of_le hsσ (Real.sqrt_le_sqrt ?_)
    exact le_trans hcσ (Complex.re_le_norm c)
  have hb3 : Real.exp (-b.re * t - c.re / t) ≤ Real.exp (-b.re * t) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ c.re / t := by positivity
    linarith
  calc 1 / Real.sqrt Real.pi * Real.exp (-2 * (Complex.sqrt a * Complex.sqrt c).re)
        * (1 / Real.sqrt ‖c‖) * (1 / Real.sqrt t) * Real.exp (-b.re * t - c.re / t)
      ≤ 1 / Real.sqrt Real.pi * 1 * (1 / Real.sqrt σ) * (1 / Real.sqrt t)
          * Real.exp (-b.re * t) := by
        gcongr
    _ = 1 / (Real.sqrt Real.pi * Real.sqrt σ) * (Real.exp (-b.re * t) * (Real.sqrt t)⁻¹) := by
        field_simp

-- no-dlmf: parametric differentiation in `c`, support lemma for DLMF 7.14.4
private lemma aux7144_hasDerivAt_F {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c₀ : ℂ} (hc₀ : 0 < c₀.re) :
    HasDerivAt (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (w / (t:ℂ))))
      (-(Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c₀
            + Complex.sqrt b * Complex.sqrt c₀)) / (Complex.sqrt b * Complex.sqrt c₀))) c₀ := by
  set σ : ℝ := c₀.re / 2 with hσdef
  have hσ : 0 < σ := by rw [hσdef]; positivity
  set s : Set ℂ := Metric.ball c₀ σ with hsdef
  have hsnhds : s ∈ 𝓝 c₀ := Metric.ball_mem_nhds _ hσ
  have hsub : ∀ w ∈ s, σ ≤ w.re := by
    intro w hw
    rw [hsdef, Metric.mem_ball, dist_eq_norm] at hw
    have h3 : |w.re - c₀.re| < σ := by
      refine lt_of_le_of_lt ?_ hw
      rw [show w.re - c₀.re = (w - c₀).re from (Complex.sub_re w c₀).symm]
      exact Complex.abs_re_le_norm _
    have h4 := (abs_lt.mp h3).1
    rw [hσdef] at h4 ⊢
    linarith
  set F : ℂ → ℝ → ℂ := fun w t => Complex.exp ((a - b) * (t:ℂ))
    * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (w / (t:ℂ))) with hFdef
  set F' : ℂ → ℝ → ℂ := fun w t => -(1 / (Real.sqrt Real.pi : ℂ))
    * Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt w))
    * (Complex.sqrt w)⁻¹ * ((Real.sqrt t : ℝ) : ℂ)⁻¹
    * Complex.exp (-b * (t:ℂ) - w / (t:ℂ)) with hF'def
  have hmeas : ∀ᶠ w in 𝓝 c₀, AEStronglyMeasurable (F w) (volume.restrict (Ioi (0:ℝ))) := by
    filter_upwards [hsnhds] with w hw
    exact (aux7144_integrand_continuousOn ha.le
      (le_trans hσ.le (hsub w hw))).aestronglyMeasurable measurableSet_Ioi
  have hint : Integrable (F c₀) (volume.restrict (Ioi (0:ℝ))) := aux7144_lhs_integrable ha hb hc₀.le
  have hF'cont : ContinuousOn (F' c₀) (Ioi (0:ℝ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htne : ((t:ℝ):ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hSne : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    refine ContinuousAt.continuousWithinAt ?_
    rw [hF'def]
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
    · exact ContinuousAt.inv₀ (by fun_prop) hSne
    · exact ContinuousAt.cexp (ContinuousAt.sub (by fun_prop)
        (ContinuousAt.div continuousAt_const (by fun_prop) htne))
  have hF'meas : AEStronglyMeasurable (F' c₀) (volume.restrict (Ioi (0:ℝ))) :=
    hF'cont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), ∀ w ∈ s,
      ‖F' w t‖ ≤ 1 / (Real.sqrt Real.pi * Real.sqrt σ)
        * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact aux7144_deriv_bound ha.le hσ (hsub w hw) ht
  have hboundint : Integrable (fun t : ℝ => 1 / (Real.sqrt Real.pi * Real.sqrt σ)
      * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2))) (volume.restrict (Ioi (0:ℝ))) :=
    (integrableOn_exp_neg_mul_rpow_Ioi b.re (-(1:ℝ)/2) hb (by norm_num)).const_mul _
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), ∀ w ∈ s,
      HasDerivAt (F · t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact aux7144_hasDerivAt_integrand ha.le (lt_of_lt_of_le hσ (hsub w hw)) ht
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le hsnhds hmeas hint hF'meas
    hbound hboundint hdiff
  have hval : (∫ t in Ioi (0:ℝ), F' c₀ t)
      = -(Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c₀
          + Complex.sqrt b * Complex.sqrt c₀)) / (Complex.sqrt b * Complex.sqrt c₀)) :=
    aux7144_integral_deriv_value hb hc₀
  rw [hval] at hres
  exact hres.2

-- no-dlmf: derivative of the closed form, support lemma for DLMF 7.14.4
private lemma aux7144_hasDerivAt_G {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c₀ : ℂ} (hc₀ : 0 < c₀.re) :
    HasDerivAt (fun w : ℂ => Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt w
          + Complex.sqrt b * Complex.sqrt w))
        / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)))
      (-(Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c₀
            + Complex.sqrt b * Complex.sqrt c₀)) / (Complex.sqrt b * Complex.sqrt c₀))) c₀ := by
  have hαp : 0 < (Complex.sqrt a).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl ha))
  have hβp : 0 < (Complex.sqrt b).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl hb))
  have hγp : 0 < (Complex.sqrt c₀).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl hc₀))
  have hβ0 : Complex.sqrt b ≠ 0 := by
    intro h
    rw [h] at hβp
    simp at hβp
  have hγ0 : Complex.sqrt c₀ ≠ 0 := by
    intro h
    rw [h] at hγp
    simp at hγp
  have hsum0 : Complex.sqrt a + Complex.sqrt b ≠ 0 := by
    intro h
    have : (Complex.sqrt a + Complex.sqrt b).re = 0 := by rw [h]; simp
    rw [Complex.add_re] at this
    linarith
  have hslit : c₀ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc₀)
  have hd0 : HasDerivAt Complex.sqrt (1 / (2 * Complex.sqrt c₀)) c₀ := aux714_hasDerivAt_csqrt hslit
  have hd1 : HasDerivAt (fun w : ℂ => -2 * (Complex.sqrt a * Complex.sqrt w
      + Complex.sqrt b * Complex.sqrt w))
      (-2 * ((Complex.sqrt a + Complex.sqrt b) * (1 / (2 * Complex.sqrt c₀)))) c₀ := by
    have h := ((hd0.const_mul (Complex.sqrt a)).add
      (hd0.const_mul (Complex.sqrt b))).const_mul (-2 : ℂ)
    convert h using 1
    ring
  have hd2 := hd1.cexp
  have hd3 := hd2.div_const (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b))
  convert hd3 using 1
  field_simp

-- no-dlmf: the two sides agree on the open right half-plane, support lemma for DLMF 7.14.4
private lemma aux7144_core_eq_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℂ} (hc : 0 < c.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))
      = Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c + Complex.sqrt b * Complex.sqrt c))
          / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)) := by
  set U : Set ℂ := {w : ℂ | 0 < w.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt (0:ℝ)
  set H : ℂ → ℂ := fun w => (∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
      * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (w / (t:ℂ))))
    - Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt w + Complex.sqrt b * Complex.sqrt w))
        / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)) with hH
  have hHderiv : ∀ w ∈ U, HasDerivAt H 0 w := by
    intro w hw
    have hw' : 0 < w.re := hw
    have h3 := (aux7144_hasDerivAt_F ha hb hw').sub (aux7144_hasDerivAt_G ha hb hw')
    rw [hH]
    convert h3 using 1
    ring
  have hHdiff : DifferentiableOn ℂ H U :=
    fun w hw => ((hHderiv w hw).differentiableAt).differentiableWithinAt
  have hHfd : ∀ w ∈ U, fderivWithin ℂ H U w = 0 := by
    intro w hw
    rw [fderivWithin_of_isOpen hUopen hw]
    have hfd := (hHderiv w hw).hasFDerivAt.fderiv
    rw [hfd]
    simp
  have hconst : ∀ w ∈ U, ∀ v ∈ U, H w = H v :=
    fun w hw v hv => hUconv.is_const_of_fderivWithin_eq_zero hHdiff hHfd hw hv
  -- the limit `c = n → ∞` pins the constant at `0`
  have hα : 0 < (Complex.sqrt a).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl ha))
  have hβ : 0 < (Complex.sqrt b).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl hb))
  have hsqrtn : ∀ n : ℕ, Complex.sqrt ((n : ℂ)) = ((Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
    intro n
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring, aux714_csqrt_ofReal (by positivity)]
  have hnU : ∀ n : ℕ, 1 ≤ n → ((n : ℂ)) ∈ U := by
    intro n hn
    show 0 < ((n : ℂ)).re
    rw [Complex.natCast_re]
    exact_mod_cast hn
  have hD0 : Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h
      rw [h] at hβ; simp at hβ
    · intro h
      have h2 : (Complex.sqrt a + Complex.sqrt b).re = 0 := by rw [h]; simp
      rw [Complex.add_re] at h2
      linarith
  have hGlim : Tendsto (fun n : ℕ => Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt ((n : ℂ))
      + Complex.sqrt b * Complex.sqrt ((n : ℂ))))
      / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hre : ∀ n : ℕ, ‖Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt ((n : ℂ))
          + Complex.sqrt b * Complex.sqrt ((n : ℂ))))
          / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b))‖
        = Real.exp (-2 * ((Complex.sqrt a).re + (Complex.sqrt b).re) * Real.sqrt (n : ℝ))
            / ‖Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)‖ := by
      intro n
      rw [norm_div, Complex.norm_exp, hsqrtn n]
      congr 2
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im, Complex.add_im,
        Complex.mul_im]
      ring
    have key : Tendsto (fun n : ℕ =>
        Real.exp (-2 * ((Complex.sqrt a).re + (Complex.sqrt b).re) * Real.sqrt (n : ℝ))
          / ‖Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ =>
          -2 * ((Complex.sqrt a).re + (Complex.sqrt b).re) * Real.sqrt (n : ℝ)) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (by nlinarith)).mpr h1
      simpa using (Real.tendsto_exp_atBot.comp h2).div_const
        ‖Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)‖
    exact key.congr (fun n => (hre n).symm)
  have hFlim : Tendsto (fun n : ℕ => ∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
      * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (((n : ℂ)) / (t:ℂ)))) atTop (𝓝 0) := by
    have hDCT : Tendsto (fun n : ℕ => ∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (((n : ℂ)) / (t:ℂ))))
        atTop (𝓝 (∫ _t in Ioi (0:ℝ), (0:ℂ))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun t : ℝ => 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
          * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2))) ?_ ?_ ?_ ?_
      · filter_upwards with n
        exact (aux7144_integrand_continuousOn ha.le
          (by rw [Complex.natCast_re]; positivity)).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards with n
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact aux7144_integrand_bound_pos ha (by rw [Complex.natCast_re]; positivity) ht
      · exact (integrableOn_exp_neg_mul_rpow_Ioi b.re (-(1:ℝ)/2) hb (by norm_num)).const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) < t := ht
        refine squeeze_zero_norm (fun n => aux7144_integrand_bound_decay ha
          (by rw [Complex.natCast_re]; positivity) ht0) ?_
        have h1 : Tendsto (fun n : ℕ => -((((n : ℂ))).re / t)) atTop atBot := by
          simp only [Complex.natCast_re]
          exact tendsto_neg_atBot_iff.mpr (tendsto_natCast_atTop_atTop.atTop_div_const ht0)
        have h2 : Tendsto (fun n : ℕ => Real.exp (-((((n : ℂ))).re / t))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp h1
        simpa using h2.const_mul (2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
          * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2)))
    simpa using hDCT
  have hHlim : Tendsto (fun n : ℕ => H ((n : ℂ))) atTop (𝓝 0) := by
    rw [hH]
    simpa using hFlim.sub hGlim
  have heq : (fun n : ℕ => H ((n : ℂ))) =ᶠ[atTop] (fun _ : ℕ => H c) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hconst _ (hnU n hn) _ hc
  have hHc : H c = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (Filter.Tendsto.congr' heq hHlim)
  simp only [hH] at hHc
  exact sub_eq_zero.mp hHc

-- no-dlmf: extension of the core identity to the boundary `Re c = 0`, support lemma for DLMF 7.14.4
private lemma aux7144_core_eq_of_re_nonneg {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {c : ℂ} (hc : 0 ≤ c.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))
      = Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c + Complex.sqrt b * Complex.sqrt c))
          / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)) := by
  set cn : ℕ → ℂ := fun n => c + ((1 / ((n:ℝ) + 1) : ℝ) : ℂ) with hcndef
  have hcnre : ∀ n : ℕ, 0 < (cn n).re := by
    intro n
    rw [hcndef]
    simp only [Complex.add_re, Complex.ofReal_re]
    have h : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  have hcntend : Tendsto cn atTop (𝓝 c) := by
    rw [hcndef]
    have h : Tendsto (fun n : ℕ => (((1 / ((n:ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => (((1 / ((n:ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 (((0:ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp h1
      rwa [Complex.ofReal_zero] at h2
    have h3 : Tendsto (fun n : ℕ => c + (((1 / ((n:ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 (c + 0)) :=
      tendsto_const_nhds.add h
    rwa [add_zero] at h3
  have hL : Tendsto (fun n : ℕ => ∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
      * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (cn n / (t:ℂ))))
      atTop (𝓝 (∫ t in Ioi (0:ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => 2 / (Real.sqrt 3 * Real.sqrt Real.pi * (Complex.sqrt a).re)
        * (Real.exp (-b.re * t) * t ^ (-(1:ℝ)/2))) ?_ ?_ ?_ ?_
    · filter_upwards with n
      exact (aux7144_integrand_continuousOn ha.le (hcnre n).le).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards with n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact aux7144_integrand_bound_pos ha (hcnre n).le ht
    · exact (integrableOn_exp_neg_mul_rpow_Ioi b.re (-(1:ℝ)/2) hb (by norm_num)).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      have hd : Tendsto (fun n : ℕ => cn n / (t:ℂ)) atTop (𝓝 (c / (t:ℂ))) :=
        hcntend.div_const _
      have hs : Tendsto (fun n : ℕ => Complex.sqrt (cn n / (t:ℂ))) atTop
          (𝓝 (Complex.sqrt (c / (t:ℂ)))) :=
        (Complex.continuousAt_sqrt (Or.inl (by rw [Complex.div_ofReal_re]; positivity))).tendsto.comp
          hd
      exact tendsto_const_nhds.mul
        ((aux714_differentiable_cerfc.continuous.tendsto _).comp (tendsto_const_nhds.add hs))
  have hs2 : Tendsto (fun n : ℕ => Complex.sqrt (cn n)) atTop (𝓝 (Complex.sqrt c)) :=
    (Complex.continuousAt_sqrt (Or.inl hc)).tendsto.comp hcntend
  have hR : Tendsto (fun n : ℕ => Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt (cn n)
      + Complex.sqrt b * Complex.sqrt (cn n)))
      / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b))) atTop
      (𝓝 (Complex.exp (-2 * (Complex.sqrt a * Complex.sqrt c + Complex.sqrt b * Complex.sqrt c))
        / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)))) :=
    (((Complex.continuous_exp.tendsto _).comp
      (((tendsto_const_nhds.mul hs2).add (tendsto_const_nhds.mul hs2)).const_mul (-2)))).div_const _
  exact tendsto_nhds_unique hL
    (hR.congr (fun n => (aux7144_core_eq_of_re_pos ha hb (hcnre n)).symm))

-- no-dlmf: majorant for small `a`, support lemma for DLMF 7.14.4
private lemma aux7144_integrand_bound_small {a b c : ℂ} (ha : 0 ≤ a.re) (han : ‖a‖ ≤ 1) (hab : a.re ≤ b.re / 2)
    (hc : 0 ≤ c.re) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))‖
      ≤ Real.exp (-(b.re / 2) * t)
        * (1 + 2 / Real.sqrt Real.pi * (Real.sqrt t + Real.sqrt ‖c‖ * t ^ (-(1:ℝ)/2))) := by
  have hπ : (0:ℝ) < Real.sqrt Real.pi := by positivity
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hrp : t ^ (-(1:ℝ)/2) = (Real.sqrt t)⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  set z := Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)) with hzdef
  have hsq : 0 ≤ (z ^ 2).re := by
    have h := aux7144_z_re_sq_ge ha hc ht
    have h1 : 0 ≤ a.re * t := by positivity
    have h2 : 0 ≤ c.re / t := by positivity
    linarith
  have hexp : ‖Complex.exp ((a - b) * (t:ℂ))‖ = Real.exp ((a.re - b.re) * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  have hexple : Real.exp ((a.re - b.re) * t) ≤ Real.exp (-(b.re / 2) * t) := by
    refine Real.exp_le_exp.mpr ?_
    have : a.re - b.re ≤ -(b.re / 2) := by linarith
    nlinarith
  have hzle : ‖z‖ ≤ Real.sqrt t + Real.sqrt ‖c‖ * t ^ (-(1:ℝ)/2) := by
    refine (aux7144_z_norm_le ht).trans ?_
    have h1 : Real.sqrt (‖a‖ * t) ≤ Real.sqrt t := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [norm_nonneg a]
    have h2 : Real.sqrt (‖c‖ / t) = Real.sqrt ‖c‖ * t ^ (-(1:ℝ)/2) := by
      rw [Real.sqrt_div (norm_nonneg c), hrp, div_eq_mul_inv]
    linarith [h2.le, h2.ge]
  calc ‖Complex.exp ((a - b) * (t:ℂ)) * cerfc z‖
      = Real.exp ((a.re - b.re) * t) * ‖cerfc z‖ := by rw [norm_mul, hexp]
    _ ≤ Real.exp (-(b.re / 2) * t)
        * (1 + 2 / Real.sqrt Real.pi * (Real.sqrt t + Real.sqrt ‖c‖ * t ^ (-(1:ℝ)/2))) := by
        refine mul_le_mul hexple ((aux7144_norm_cerfc_le hsq).trans ?_) (norm_nonneg _)
          (Real.exp_nonneg _)
        gcongr

-- no-dlmf: integrability of the small-`a` majorant, support lemma for DLMF 7.14.4
private lemma aux7144_integrable_small_bound {B M : ℝ} (hB : 0 < B) :
    IntegrableOn (fun t : ℝ => Real.exp (-(B / 2) * t)
      * (1 + 2 / Real.sqrt Real.pi * (Real.sqrt t + M * t ^ (-(1:ℝ)/2)))) (Ioi 0) := by
  have h0 := integrableOn_exp_neg_mul_rpow_Ioi (B / 2) 0 (by linarith) (by norm_num)
  have h1 := integrableOn_exp_neg_mul_rpow_Ioi (B / 2) (1/2 : ℝ) (by linarith) (by norm_num)
  have h2 := integrableOn_exp_neg_mul_rpow_Ioi (B / 2) (-(1:ℝ)/2) (by linarith) (by norm_num)
  have hsum := (h0.add (h1.const_mul (2 / Real.sqrt Real.pi))).add
    (h2.const_mul (2 / Real.sqrt Real.pi * M))
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro t htm
  have ht0 : (0:ℝ) < t := htm
  simp only [Pi.add_apply]
  rw [Real.rpow_zero, ← Real.sqrt_eq_rpow]
  ring

-- no-dlmf: the degenerate parameter `a = 0`, support lemma for DLMF 7.14.4
private lemma aux7144_core_eq_zero_a {b c : ℂ} (hb : 0 < b.re) (hc : 0 ≤ c.re) :
    (∫ t in Ioi (0:ℝ), Complex.exp (((0:ℂ) - b) * (t:ℂ))
        * cerfc (Complex.sqrt ((0:ℂ) * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))
      = Complex.exp (-2 * (Complex.sqrt (0:ℂ) * Complex.sqrt c
          + Complex.sqrt b * Complex.sqrt c))
          / (Complex.sqrt b * (Complex.sqrt (0:ℂ) + Complex.sqrt b)) := by
  have hβ : 0 < (Complex.sqrt b).re := aux714_csqrt_re_pos (Complex.mem_slitPlane_iff.mpr (Or.inl hb))
  have hbne : Complex.sqrt b ≠ 0 := by
    intro h
    rw [h] at hβ
    simp at hβ
  set an : ℕ → ℂ := fun n => (((1 / ((n:ℝ) + 1) : ℝ)) : ℂ) with handef
  have hanre : ∀ n : ℕ, 0 < (an n).re := by
    intro n
    rw [handef]
    simp only [Complex.ofReal_re]
    positivity
  have hannorm : ∀ n : ℕ, ‖an n‖ = 1 / ((n:ℝ) + 1) := by
    intro n
    rw [handef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hantend : Tendsto an atTop (𝓝 0) := by
    rw [handef]
    have h1 : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (((1 / ((n:ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 (((0:ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    rwa [Complex.ofReal_zero] at h2
  have hrate : Tendsto (fun n : ℕ => (1:ℝ) / ((n:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hev1 : ∀ᶠ n : ℕ in atTop, (1:ℝ) / ((n:ℝ) + 1) ≤ 1 :=
    Filter.Tendsto.eventually_le_const (by norm_num) hrate
  have hev2 : ∀ᶠ n : ℕ in atTop, (1:ℝ) / ((n:ℝ) + 1) ≤ b.re / 2 :=
    Filter.Tendsto.eventually_le_const (by linarith) hrate
  have hL : Tendsto (fun n : ℕ => ∫ t in Ioi (0:ℝ), Complex.exp ((an n - b) * (t:ℂ))
      * cerfc (Complex.sqrt (an n * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))
      atTop (𝓝 (∫ t in Ioi (0:ℝ), Complex.exp (((0:ℂ) - b) * (t:ℂ))
        * cerfc (Complex.sqrt ((0:ℂ) * (t:ℂ)) + Complex.sqrt (c / (t:ℂ))))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => Real.exp (-(b.re / 2) * t)
        * (1 + 2 / Real.sqrt Real.pi
            * (Real.sqrt t + Real.sqrt ‖c‖ * t ^ (-(1:ℝ)/2)))) ?_ ?_ ?_ ?_
    · filter_upwards with n
      exact (aux7144_integrand_continuousOn (hanre n).le hc).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [hev1, hev2] with n h1 h2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine aux7144_integrand_bound_small (hanre n).le ?_ ?_ hc ht
      · rw [hannorm n]; exact h1
      · have hre : (an n).re = 1 / ((n:ℝ) + 1) := by rw [handef, Complex.ofReal_re]
        rw [hre]; exact h2
    · exact aux7144_integrable_small_bound hb
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hat : Tendsto (fun n : ℕ => an n * (t:ℂ)) atTop (𝓝 ((0:ℂ) * (t:ℂ))) :=
        hantend.mul_const _
      have hsa : Tendsto (fun n : ℕ => Complex.sqrt (an n * (t:ℂ))) atTop
          (𝓝 (Complex.sqrt ((0:ℂ) * (t:ℂ)))) := by
        refine (Complex.continuousAt_sqrt (Or.inl ?_)).tendsto.comp hat
        simp
      have hea : Tendsto (fun n : ℕ => Complex.exp ((an n - b) * (t:ℂ))) atTop
          (𝓝 (Complex.exp (((0:ℂ) - b) * (t:ℂ)))) :=
        (Complex.continuous_exp.tendsto _).comp ((hantend.sub_const b).mul_const _)
      exact hea.mul ((aux714_differentiable_cerfc.continuous.tendsto _).comp (hsa.add tendsto_const_nhds))
  have hsa0 : Tendsto (fun n : ℕ => Complex.sqrt (an n)) atTop (𝓝 (Complex.sqrt (0:ℂ))) :=
    (Complex.continuousAt_sqrt (Or.inl (by simp))).tendsto.comp hantend
  have hden : Complex.sqrt b * (Complex.sqrt (0:ℂ) + Complex.sqrt b) ≠ 0 := by
    rw [Complex.sqrt_zero, zero_add]
    exact mul_ne_zero hbne hbne
  have hnum : Tendsto (fun n : ℕ => Complex.exp (-2 * (Complex.sqrt (an n) * Complex.sqrt c
      + Complex.sqrt b * Complex.sqrt c))) atTop
      (𝓝 (Complex.exp (-2 * (Complex.sqrt (0:ℂ) * Complex.sqrt c
        + Complex.sqrt b * Complex.sqrt c)))) :=
    (Complex.continuous_exp.tendsto _).comp
      (((hsa0.mul tendsto_const_nhds).add tendsto_const_nhds).const_mul (-2))
  have hdenT : Tendsto (fun n : ℕ => Complex.sqrt b * (Complex.sqrt (an n) + Complex.sqrt b))
      atTop (𝓝 (Complex.sqrt b * (Complex.sqrt (0:ℂ) + Complex.sqrt b))) :=
    tendsto_const_nhds.mul (hsa0.add tendsto_const_nhds)
  exact tendsto_nhds_unique hL
    ((hnum.div hdenT hden).congr (fun n => (aux7144_core_eq_of_re_nonneg (hanre n) hb hc).symm))

end Ch714_4Support

/-- **DLMF 7.14.4** — Laplace-type transform of `erfc(√(at) + √(c/t))`: for complex
`a, b, c` with `|ph a| < π/2`, `Re b > 0`, `Re c ≥ 0`,
`∫₀^∞ e^{(a-b)t} erfc(√(at) + √(c/t)) dt = e^{-2(√(ac)+√(bc))} / (√b·(√a+√b))`.
(Corrected 2026-06-24 from the DLMF PDF — the source had dropped every √: the erfc
argument is `√(at)+√(c/t)`, the exponent `-2(√(ac)+√(bc))`, the denominator
`√b(√a+√b)`. The previously-emitted `7.14.4_5` `-at` companion is not a numbered
DLMF equation and has been dropped. See docs/ERRATA.md.
Generalized 2026-08-07 from a real `a,b,c > 0` restriction to DLMF's stated
complex domain — the statement was already an open `sorry`, so no proven proof
needed weakening or preservation.)

DAG: E-7.14.4.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem erf_7_14_4 {a b c : ℂ} (ha : |Complex.arg a| < π / 2) (hb : 0 < b.re)
    (hc : 0 ≤ c.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp ((a - b) * (t:ℂ))
        * cerfc (Complex.sqrt (a * (t:ℂ)) + Complex.sqrt (c / (t:ℂ)))
      = Complex.exp (-2 * (Complex.sqrt (a * c) + Complex.sqrt (b * c)))
          / (Complex.sqrt b * (Complex.sqrt a + Complex.sqrt b)) := by
  rcases Complex.abs_arg_lt_pi_div_two_iff.mp ha with ha' | rfl
  · rw [aux7144_csqrt_mul ha' hc, aux7144_csqrt_mul hb hc]
    exact aux7144_core_eq_of_re_nonneg ha' hb hc
  · have h := aux7144_core_eq_zero_a hb hc
    rw [show ((0:ℂ) * c) = 0 by ring, aux7144_csqrt_mul hb hc, Complex.sqrt_zero]
    rw [Complex.sqrt_zero, zero_mul] at h
    exact h

/-! ### Support lemma for DLMF 7.14.5 / 7.14.6

The route: integrate by parts through the Laplace module's derivative rule
(`laplaceTransform_deriv`, DLMF 1.14.27) with `C' = cosArg`, `S' = sinArg`,
reducing both transforms to the Fresnel kernel Laplace integrals
`∫₀^∞ e^{-at} cos(πt²/2) dt` and `∫₀^∞ e^{-at} sin(πt²/2) dt`; these are the
auxiliary-function Laplace pair `fresnelAux_eq_laplace_pair` (the §7.7.15/7.7.16
infrastructure of `Ch7IntegralReps`) evaluated at `z = a/π`. -/

section Fresnel7145Support

open FLMF.Methods.LaplaceTransform FLMF.Fresnel

/-- **Generic IBP reduction for 7.14.5/7.14.6.** For a bounded continuous `g`
with `g 0 = 0`, `g → 1/2` at `∞`, and `g' = dg` everywhere with `|dg| ≤ 1`, the
Laplace transform of `g` reduces to that of `dg` divided by the rate, via the
Laplace module's derivative rule (DLMF 1.14.27). -/
-- no-dlmf: IBP reduction lemma for 7.14.5/7.14.6; the 1.14.27 citation is the method used
private theorem laplace_fresnel_direct_eq (a : ℝ) (ha : 0 < a) (g dg : ℝ → ℝ)
    (hgc : Continuous g) (hg0 : g 0 = 0) (hglim : Tendsto g atTop (𝓝 (1/2)))
    (hdgc : Continuous dg) (hdg_le : ∀ t : ℝ, |dg t| ≤ 1)
    (hderiv : ∀ t : ℝ, HasDerivAt g (dg t) t) :
    ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * g t
      = (∫ t in Ioi (0:ℝ), Real.exp (-a * t) * dg t) / a := by
  set f : ℝ → ℂ := fun t => ((g t : ℝ) : ℂ) with hfdef
  set f' : ℝ → ℂ := fun t => ((dg t : ℝ) : ℂ) with hf'def
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → |g x| ≤ M := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hglim 1 one_pos
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max X 0)).exists_bound_of_continuousOn
      hgc.continuousOn
    refine ⟨max C (|(1:ℝ)/2| + 1), le_max_of_le_right (by positivity), fun x hx => ?_⟩
    rcases le_or_gt x (max X 0) with hxle | hxgt
    · exact le_trans (by simpa [Real.norm_eq_abs] using hC x ⟨hx, hxle⟩) (le_max_left _ _)
    · have hxX : X ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left X 0) hxgt)
      have hd := hX x hxX
      rw [Real.dist_eq] at hd
      have hbnd : |g x| ≤ |(1:ℝ)/2| + 1 := by
        have h2 := abs_sub_abs_le_abs_sub (g x) ((1:ℝ)/2)
        linarith
      exact le_trans hbnd (le_max_right _ _)
  have hfcont : Continuous f := Complex.continuous_ofReal.comp hgc
  have hfbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M := by
    intro t ht
    rw [hfdef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hMb t ht
  have hf_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f t) (Ioi 0) := by
    refine integrableOn_laplaceTransform_of_exponentialOrder (σ₀ := 0) (M := M) hM0
      hfcont.aestronglyMeasurable ?_ (by simpa using ha)
    intro t ht
    rw [zero_mul, Real.exp_zero, mul_one]
    exact hfbound t (le_of_lt ht)
  have hf'_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f' t) (Ioi 0) := by
    refine integrableOn_laplaceTransform_of_exponentialOrder (σ₀ := 0) (M := 1)
      one_pos.le (Complex.continuous_ofReal.comp hdgc).aestronglyMeasurable ?_
      (by simpa using ha)
    intro t ht
    rw [zero_mul, Real.exp_zero, mul_one]
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
    exact hdg_le t
  have hcont0 : ContinuousWithinAt f (Ici (0:ℝ)) 0 := hfcont.continuousWithinAt
  have hbdry : Tendsto (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f t) atTop (𝓝 0) := by
    have hv_to0 : Tendsto (fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖) atTop (𝓝 0) := by
      have heq : ∀ t : ℝ, ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ = Real.exp (-a * t) := by
        intro t
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      simp_rw [heq]
      have : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      exact Real.tendsto_exp_atBot.comp this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (t₀ := atTop)
      (f := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ)) * f t‖)
      (g := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ * M)
    · filter_upwards with t using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hfbound t ht.le) (norm_nonneg _)
    · simpa using hv_to0.mul_const M
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f (f' t) t := by
    intro t _
    have := (hderiv t).ofReal_comp
    simpa [hfdef, hf'def] using this
  have hkey := laplaceTransform_deriv (f := f) (f' := f') (s := (a:ℂ))
    hd hf_int hf'_int hcont0 hbdry
  have hf0 : f 0 = 0 := by
    rw [hfdef]
    simp only
    rw [hg0, Complex.ofReal_zero]
  rw [hf0, sub_zero] at hkey
  have hbridge : ∀ h : ℝ → ℝ, laplaceTransform (fun t : ℝ => ((h t : ℝ) : ℂ)) (a:ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * h t : ℝ) : ℂ) := by
    intro h
    simp only [laplaceTransform]
    have hcongr : ∀ t : ℝ, Complex.exp (-(a:ℂ) * (t:ℂ)) * ((h t : ℝ) : ℂ)
        = ((Real.exp (-a*t) * h t : ℝ) : ℂ) := by
      intro t
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
    exact _root_.integral_ofReal
  rw [hfdef, hf'def, hbridge g, hbridge dg] at hkey
  have hreal : (∫ t in Ioi (0:ℝ), Real.exp (-a*t) * dg t)
      = a * ∫ t in Ioi (0:ℝ), Real.exp (-a*t) * g t := by
    exact_mod_cast hkey
  rw [eq_div_iff ha.ne', hreal]
  ring

end Fresnel7145Support

-- no-dlmf: real/narrowed restriction of DLMF 7.14.5; faithful surface is cfresnel_7_14_5
/-- Laplace transform of the Fresnel cosine integral `C` via the auxiliary `f`,
real specialization: for real `a > 0`,
`∫₀^∞ e^{-a t} C(t) dt = (1/a) f(a/π)`
(DLMF 7.14.5 is stated for complex `a` with `Re a > 0`).
-/
theorem erf_7_14_5 {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * FLMF.Fresnel.fresnelC t) =
      (1 / a) * fresnelAuxF (a / Real.pi) := by
  have hz : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have hker : fresnelAuxF (a / Real.pi)
      = ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * FLMF.Fresnel.cosArg t := by
    rw [(fresnelAux_eq_laplace_pair hz).1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    unfold FLMF.Fresnel.cosArg
    have harg : -(Real.pi * (a / Real.pi) * u) = -a * u := by
      field_simp
    rw [harg]
  rw [laplace_fresnel_direct_eq a ha FLMF.Fresnel.fresnelC FLMF.Fresnel.cosArg
    FLMF.Fresnel.continuous_fresnelC FLMF.Fresnel.fresnelC_zero FLMF.Fresnel.tendsto_fresnelC
    FLMF.Fresnel.continuous_cosArg (fun t => Real.abs_cos_le_one _)
    (fun t => FLMF.Fresnel.hasDerivAt_fresnelC t)]
  rw [← hker]
  ring

/-- **DLMF 7.14.5** — Laplace transform of the Fresnel cosine integral `C` (real
argument `t`) via the complex auxiliary `f`, for complex `a` with `Re a > 0`:
`∫₀^∞ e^{-a t} C(t) dt = (1/a) f(a/π)`.

DAG: E-7.14.5.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem cfresnel_7_14_5 {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * (FLMF.Fresnel.fresnelC t : ℂ)) =
      (1 / a) * FLMF.Fresnel.cfresnelAuxF (a / (π:ℂ)) := by
  obtain ⟨M, hM0, hMb⟩ := aux714_bounded_of_tendsto FLMF.Fresnel.continuous_fresnelC
    FLMF.Fresnel.tendsto_fresnelC
  have hU : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ
      (fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t:ℂ)) * (FLMF.Fresnel.fresnelC t : ℂ))
      {b : ℂ | 0 < b.re} := by
    refine aux714_analyticOnNhd_laplace (χ := fun t : ℝ => ((FLMF.Fresnel.fresnelC t : ℝ) : ℂ)) (C := M) (k := 0)
      (by norm_num) (Complex.continuous_ofReal.comp FLMF.Fresnel.continuous_fresnelC).continuousOn (fun t ht => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, mul_one]
    exact hMb t ht.le
  have hG : AnalyticOnNhd ℂ (fun b : ℂ => (1 / b) * FLMF.Fresnel.cfresnelAuxF (b / (π:ℂ)))
      {b : ℂ | 0 < b.re} := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hU
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hb
      simp at hb
    have h1 : DifferentiableAt ℂ (fun c : ℂ => (1:ℂ) / c) b :=
      (differentiableAt_const (1:ℂ)).div differentiableAt_id hb0
    have h2 : DifferentiableAt ℂ (fun c : ℂ => FLMF.Fresnel.cfresnelAuxF (c / (π:ℂ))) b :=
      (aux714_differentiable_cfresnelAuxF _).comp b (differentiableAt_id.div_const _)
    exact (h1.mul h2).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x:ℂ) * (t:ℂ)) * (FLMF.Fresnel.fresnelC t : ℂ))
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * FLMF.Fresnel.fresnelC t : ℝ) : ℂ) :=
    aux714_laplace_ofReal FLMF.Fresnel.fresnelC x
  have harg : ((x:ℂ) / (π:ℂ)) = (((x / π : ℝ)) : ℂ) := by push_cast; ring
  rw [hL, erf_7_14_5 hx, harg, aux714_cfresnelAuxF_ofReal]
  push_cast
  ring

-- no-dlmf: real/narrowed restriction of DLMF 7.14.6; faithful surface is cfresnel_7_14_6
/-- Laplace transform of the Fresnel sine integral `S` via the auxiliary `g`,
real specialization: for real `a > 0`,
`∫₀^∞ e^{-a t} S(t) dt = (1/a) g(a/π)`
(DLMF 7.14.6 is stated for complex `a` with `Re a > 0`).
-/
theorem erf_7_14_6 {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * FLMF.Fresnel.fresnelS t) =
      (1 / a) * fresnelAuxG (a / Real.pi) := by
  have hz : 0 < a / Real.pi := div_pos ha Real.pi_pos
  have hker : fresnelAuxG (a / Real.pi)
      = ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * FLMF.Fresnel.sinArg t := by
    rw [(fresnelAux_eq_laplace_pair hz).2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    unfold FLMF.Fresnel.sinArg
    have harg : -(Real.pi * (a / Real.pi) * u) = -a * u := by
      field_simp
    rw [harg]
  rw [laplace_fresnel_direct_eq a ha FLMF.Fresnel.fresnelS FLMF.Fresnel.sinArg
    FLMF.Fresnel.continuous_fresnelS FLMF.Fresnel.fresnelS_zero FLMF.Fresnel.tendsto_fresnelS
    FLMF.Fresnel.continuous_sinArg (fun t => Real.abs_sin_le_one _)
    (fun t => FLMF.Fresnel.hasDerivAt_fresnelS t)]
  rw [← hker]
  ring

/-- **DLMF 7.14.6** — Laplace transform of the Fresnel sine integral `S` (real
argument `t`) via the complex auxiliary `g`, for complex `a` with `Re a > 0`:
`∫₀^∞ e^{-a t} S(t) dt = (1/a) g(a/π)`.

DAG: E-7.14.6.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem cfresnel_7_14_6 {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t:ℂ)) * (FLMF.Fresnel.fresnelS t : ℂ)) =
      (1 / a) * FLMF.Fresnel.cfresnelAuxG (a / (π:ℂ)) := by
  obtain ⟨M, hM0, hMb⟩ := aux714_bounded_of_tendsto FLMF.Fresnel.continuous_fresnelS
    FLMF.Fresnel.tendsto_fresnelS
  have hU : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ
      (fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t:ℂ)) * (FLMF.Fresnel.fresnelS t : ℂ))
      {b : ℂ | 0 < b.re} := by
    refine aux714_analyticOnNhd_laplace (χ := fun t : ℝ => ((FLMF.Fresnel.fresnelS t : ℝ) : ℂ)) (C := M) (k := 0)
      (by norm_num) (Complex.continuous_ofReal.comp FLMF.Fresnel.continuous_fresnelS).continuousOn (fun t ht => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, mul_one]
    exact hMb t ht.le
  have hG : AnalyticOnNhd ℂ (fun b : ℂ => (1 / b) * FLMF.Fresnel.cfresnelAuxG (b / (π:ℂ)))
      {b : ℂ | 0 < b.re} := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hU
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hb
      simp at hb
    have h1 : DifferentiableAt ℂ (fun c : ℂ => (1:ℂ) / c) b :=
      (differentiableAt_const (1:ℂ)).div differentiableAt_id hb0
    have h2 : DifferentiableAt ℂ (fun c : ℂ => FLMF.Fresnel.cfresnelAuxG (c / (π:ℂ))) b :=
      (aux714_differentiable_cfresnelAuxG _).comp b (differentiableAt_id.div_const _)
    exact (h1.mul h2).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x:ℂ) * (t:ℂ)) * (FLMF.Fresnel.fresnelS t : ℂ))
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * FLMF.Fresnel.fresnelS t : ℝ) : ℂ) :=
    aux714_laplace_ofReal FLMF.Fresnel.fresnelS x
  have harg : ((x:ℂ) / (π:ℂ)) = (((x / π : ℝ)) : ℂ) := by push_cast; ring
  rw [hL, erf_7_14_6 hx, harg, aux714_cfresnelAuxG_ofReal]
  push_cast
  ring

/-! ### Support lemmas for DLMF 7.14.7 / 7.14.8

The route: integrate by parts through the Laplace module's derivative rule
(`laplaceTransform_deriv`, DLMF 1.14.27) with
`(d/dt) C(√(2t/π)) = cos t/√(2πt)`, `(d/dt) S(√(2t/π)) = sin t/√(2πt)`, reducing
both transforms to the fractional Gamma moments
`∫₀^∞ t^{-1/2} e^{-at} cos t dt` and `∫₀^∞ t^{-1/2} e^{-at} sin t dt`.  These are
the real and (negated) imaginary parts of the complex-rate Laplace–Mellin formula
`∫₀^∞ t^{-1/2} e^{-(a+i)t} dt = (a+i)^{-1/2} Γ(1/2)`
(`FLMF.Methods.ContourRotation.Gamma.scaled_gamma` at `s = 1/2`, `c = a + i`, in
the closed first quadrant), and the half-angle decomposition of `(a+i)^{-1/2}`
produces the surd values `√(√(a²+1) ± a)/(√2·√(a²+1))`. -/

section Fresnel714Support

open FLMF.Methods.LaplaceTransform FLMF.Fresnel

/-- Principal square root of `(a+i)⁻¹` in closed form: with `r = √(a²+1)`,
`(a+i)^{-1/2} = √(r+a)/(√2·r) - i·√(r-a)/(√2·r)` (half-angle formulas at
`θ = arg(a+i) ∈ (0, π/2)`). -/
-- no-dlmf: cpow evaluation helper for 7.14.7/7.14.8, no DLMF equation
private theorem cpow_neg_half_ofReal_add_I (a : ℝ) (ha : 0 < a) :
    ((a:ℂ) + Complex.I) ^ (-(1/2 : ℂ)) =
      Complex.ofReal (Real.sqrt (Real.sqrt (a^2+1) + a) / (Real.sqrt 2 * Real.sqrt (a^2+1)))
        - Complex.ofReal (Real.sqrt (Real.sqrt (a^2+1) - a) / (Real.sqrt 2 * Real.sqrt (a^2+1)))
          * Complex.I := by
  set z : ℂ := (a:ℂ) + Complex.I with hzdef
  set r : ℝ := Real.sqrt (a^2+1) with hrdef
  have hr2 : (0:ℝ) < a^2 + 1 := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hr2
  have hznorm : ‖z‖ = r := by
    rw [hzdef, hrdef, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hznorm
    simp at hznorm
    exact hr.ne (by rw [← hznorm])
  set θ := z.arg with hθdef
  have him : z.im = 1 := by simp [hzdef]
  have hre : z.re = a := by simp [hzdef]
  have hθ0 : 0 ≤ θ := Complex.arg_nonneg_iff.mpr (by rw [him]; norm_num)
  have hθpi : θ ≤ π := Complex.arg_le_pi z
  have hcosθ : Real.cos θ = a / r := by
    rw [hθdef, Complex.cos_arg hzne, hznorm, hre]
  have har : a ≤ r := by
    rw [hrdef]
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ a^2+1), Real.sqrt_nonneg (a^2+1),
      sq_nonneg (Real.sqrt (a^2+1) - a)]
  have hlog : Complex.log z * (-(1/2 : ℂ))
      = ((-(Real.log r / 2) : ℝ) : ℂ) + ((-(θ/2) : ℝ) : ℂ) * Complex.I := by
    rw [← Complex.re_add_im (Complex.log z), Complex.log_re, Complex.log_im, hznorm, ← hθdef]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hzne, hlog, Complex.exp_add, Complex.exp_ofReal_mul_I,
    ← Complex.ofReal_exp]
  have hu : Real.exp (-(Real.log r / 2)) = (Real.sqrt r)⁻¹ := by
    rw [show -(Real.log r / 2) = Real.log r * (-(1/2)) by ring, ← Real.rpow_def_of_pos hr,
      Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
  have hcoshalf : Real.cos (-(θ/2)) = Real.sqrt (r + a) / (Real.sqrt 2 * Real.sqrt r) := by
    rw [Real.cos_neg]
    rw [Real.cos_half (by linarith [Real.pi_pos]) hθpi, hcosθ]
    rw [show (1 + a/r)/2 = (r+a)/(2*r) by field_simp]
    rw [Real.sqrt_div (by linarith : (0:ℝ) ≤ r + a), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hsinhalf : Real.sin (-(θ/2)) = -(Real.sqrt (r - a) / (Real.sqrt 2 * Real.sqrt r)) := by
    rw [Real.sin_neg]
    rw [Real.sin_half_eq_sqrt hθ0 (by linarith [Real.pi_pos]), hcosθ]
    rw [show (1 - a/r)/2 = (r-a)/(2*r) by field_simp]
    rw [Real.sqrt_div (by linarith : (0:ℝ) ≤ r - a), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [hu, hcoshalf, hsinhalf]
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have hsr : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  push_cast
  have hsqC : (r : ℂ) = (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) := by exact_mod_cast hsq.symm
  rw [hsqC]
  have hsrC : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsr
  have h2C : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
  field_simp
  ring

/-- Integrability of the dominating kernel `t^{-1/2} e^{-at}` on `(0, ∞)`. -/
-- no-dlmf: integrability helper for 7.14.7/7.14.8, no DLMF equation
private theorem integrableOn_rpow_neg_half_mul_exp (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(1/2):ℝ) * Real.exp (-(a * t))) (Ioi (0:ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) (Ioi (0:ℝ)) := by
    have h0 := Real.GammaIntegral_convergent (by norm_num : (0:ℝ) < 1/2)
    refine h0.congr_fun (fun x _ => mul_comm _ _) measurableSet_Ioi
  have hscaled : IntegrableOn
      (fun t : ℝ => (a * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-(a * t))) (Ioi (0:ℝ)) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => x ^ ((1/2 : ℝ) - 1) * Real.exp (-x)) 0 ha).mpr (by simpa using hbase)
    simpa using h
  have hcm : IntegrableOn
      (fun t : ℝ => a ^ (-(1/2 : ℝ) + 1) *
        ((a * t) ^ ((1/2 : ℝ) - 1) * Real.exp (-(a * t)))) (Ioi (0:ℝ)) :=
    hscaled.const_mul _
  refine hcm.congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [Real.mul_rpow ha.le ht.le]
  have hconst : a ^ (-(1/2 : ℝ) + 1) * a ^ ((1/2 : ℝ) - 1) = 1 := by
    rw [← Real.rpow_add ha]; norm_num
  have hexp : t ^ ((1/2:ℝ) - 1) = t ^ (-(1/2):ℝ) := by norm_num
  calc a ^ (-(1/2 : ℝ) + 1)
          * (a ^ ((1/2 : ℝ) - 1) * t ^ ((1/2 : ℝ) - 1) * Real.exp (-(a * t)))
      = (a ^ (-(1/2 : ℝ) + 1) * a ^ ((1/2 : ℝ) - 1))
          * (t ^ ((1/2 : ℝ) - 1) * Real.exp (-(a * t))) := by ring
    _ = t ^ ((1/2 : ℝ) - 1) * Real.exp (-(a * t)) := by rw [hconst]; ring
    _ = t ^ (-(1/2):ℝ) * Real.exp (-(a * t)) := by rw [hexp]

/-- Pointwise real/imaginary decomposition of the Gamma-moment integrand
`t^{-1/2} e^{-(a+i)t}` for `t > 0`. -/
-- no-dlmf: pointwise decomposition helper for 7.14.7/7.14.8, no DLMF equation
private theorem fresnel_kernel_eq (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (t:ℂ) ^ ((1/2:ℂ) - 1) * Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))
      = ((t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.cos t) : ℝ) : ℂ)
        - ((t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.sin t) : ℝ) : ℂ) * Complex.I := by
  have h1 : ((1/2:ℂ) - 1) = ((-(1/2) : ℝ) : ℂ) := by push_cast; norm_num
  rw [h1, ← Complex.ofReal_cpow ht.le]
  have h2 : -(((a:ℂ) + Complex.I) * (t:ℂ)) = ((-(a*t) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h2, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- Integrability of the Gamma-moment integrand `t^{-1/2} e^{-(a+i)t}` on `(0, ∞)`. -/
-- no-dlmf: integrability helper for 7.14.7/7.14.8, no DLMF equation
private theorem fresnel_kernel_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t:ℂ) ^ ((1/2:ℂ) - 1)
      * Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))) (Ioi (0:ℝ)) := by
  have hcont : ContinuousOn (fun t : ℝ => (t:ℂ) ^ ((1/2:ℂ) - 1)
      * Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))) (Ioi (0:ℝ)) := by
    intro t ht
    apply ContinuousWithinAt.mul
    · have h1 : ContinuousAt (fun z : ℂ => z ^ ((1/2:ℂ) - 1)) ((t:ℂ)) := by
        apply continuousAt_cpow_const
        rw [Complex.mem_slitPlane_iff]
        left
        simpa using (ht : (0:ℝ) < t)
      exact (h1.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · have : Continuous (fun t : ℝ => Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))) := by
        fun_prop
      exact this.continuousWithinAt
  refine Integrable.mono' (integrableOn_rpow_neg_half_mul_exp a ha)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_exp]
  have h1 : ‖(t:ℂ) ^ ((1/2:ℂ) - 1)‖ = t ^ (-(1/2):ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    norm_num
  have h2 : (-(((a:ℂ) + Complex.I) * (t:ℂ))).re = -(a * t) := by
    simp [Complex.mul_re]
  rw [h1, h2]

/-- The cosine Gamma moment (with `r = √(a²+1)`):
`∫₀^∞ t^{-1/2} e^{-at} cos t dt = √π·√(r+a)/(√2·r)`. -/
-- no-dlmf: Gamma-moment evaluation feeding 7.14.7, no independent DLMF number
private theorem integral_rpow_neg_half_exp_cos (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.cos t)
      = Real.sqrt π
          * (Real.sqrt (Real.sqrt (a^2+1) + a) / (Real.sqrt 2 * Real.sqrt (a^2+1))) := by
  have hre : (0:ℝ) < ((a:ℂ) + Complex.I).re := by simpa using ha
  have him : (0:ℝ) ≤ ((a:ℂ) + Complex.I).im := by simp
  have hs : (0:ℝ) < (1/2:ℂ).re := by norm_num
  have hΓ := FLMF.Methods.ContourRotation.Gamma.scaled_gamma (1/2:ℂ) hs hre him
  have hint := fresnel_kernel_integrableOn a ha
  have hGamma : Complex.Gamma (1/2:ℂ) = Complex.ofReal (Real.sqrt π) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hprod : ((a:ℂ) + Complex.I) ^ (-(1/2:ℂ)) * Complex.Gamma (1/2:ℂ)
      = Complex.ofReal (Real.sqrt π
            * (Real.sqrt (Real.sqrt (a^2+1) + a) / (Real.sqrt 2 * Real.sqrt (a^2+1))))
        - Complex.ofReal (Real.sqrt π
            * (Real.sqrt (Real.sqrt (a^2+1) - a) / (Real.sqrt 2 * Real.sqrt (a^2+1))))
          * Complex.I := by
    rw [cpow_neg_half_ofReal_add_I a ha, hGamma]
    push_cast
    ring
  rw [hprod] at hΓ
  have hpt : ∀ t ∈ Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.cos t)
      = ((t:ℂ) ^ ((1/2:ℂ) - 1) * Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))).re := by
    intro t ht
    rw [fresnel_kernel_eq a ht]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have h_re := integral_re hint
  rw [RCLike.re_eq_complex_re] at h_re
  rw [h_re, hΓ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]

/-- The sine Gamma moment (with `r = √(a²+1)`):
`∫₀^∞ t^{-1/2} e^{-at} sin t dt = √π·√(r-a)/(√2·r)`. -/
-- no-dlmf: Gamma-moment evaluation feeding 7.14.8, no independent DLMF number
private theorem integral_rpow_neg_half_exp_sin (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.sin t)
      = Real.sqrt π
          * (Real.sqrt (Real.sqrt (a^2+1) - a) / (Real.sqrt 2 * Real.sqrt (a^2+1))) := by
  have hre : (0:ℝ) < ((a:ℂ) + Complex.I).re := by simpa using ha
  have him : (0:ℝ) ≤ ((a:ℂ) + Complex.I).im := by simp
  have hs : (0:ℝ) < (1/2:ℂ).re := by norm_num
  have hΓ := FLMF.Methods.ContourRotation.Gamma.scaled_gamma (1/2:ℂ) hs hre him
  have hint := fresnel_kernel_integrableOn a ha
  have hGamma : Complex.Gamma (1/2:ℂ) = Complex.ofReal (Real.sqrt π) := by
    rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num, Complex.Gamma_ofReal, Real.Gamma_one_half_eq]
  have hprod : ((a:ℂ) + Complex.I) ^ (-(1/2:ℂ)) * Complex.Gamma (1/2:ℂ)
      = Complex.ofReal (Real.sqrt π
            * (Real.sqrt (Real.sqrt (a^2+1) + a) / (Real.sqrt 2 * Real.sqrt (a^2+1))))
        - Complex.ofReal (Real.sqrt π
            * (Real.sqrt (Real.sqrt (a^2+1) - a) / (Real.sqrt 2 * Real.sqrt (a^2+1))))
          * Complex.I := by
    rw [cpow_neg_half_ofReal_add_I a ha, hGamma]
    push_cast
    ring
  rw [hprod] at hΓ
  have hpt : ∀ t ∈ Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * Real.sin t)
      = -(((t:ℂ) ^ ((1/2:ℂ) - 1) * Complex.exp (-(((a:ℂ) + Complex.I) * (t:ℂ)))).im) := by
    intro t ht
    rw [fresnel_kernel_eq a ht]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub, neg_neg]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg]
  have h_im := integral_im hint
  rw [RCLike.im_eq_complex_im] at h_im
  rw [h_im, hΓ]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_sub, neg_neg]

/-- Derivative of the substitution map: `(d/dt)√(2t/π) = 1/√(2πt)` for `t > 0`. -/
-- no-dlmf: chain-rule helper for 7.14.7/7.14.8, no DLMF equation
private theorem hasDerivAt_sqrt_two_mul_div_pi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.sqrt (2 * t / π)) (1 / Real.sqrt (2 * π * t)) t := by
  have hinner : HasDerivAt (fun t : ℝ => 2 * t / π) (2 / π) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).div_const π
  have harg : (0:ℝ) < 2 * t / π := by positivity
  have hsqrt := (Real.hasDerivAt_sqrt harg.ne').comp t hinner
  have hval : 1 / (2 * Real.sqrt (2 * t / π)) * (2 / π) = 1 / Real.sqrt (2 * π * t) := by
    have h1 : Real.sqrt (2 * π * t) = π * Real.sqrt (2 * t / π) := by
      rw [show 2 * π * t = π^2 * (2 * t / π) by field_simp,
        Real.sqrt_mul (by positivity) _, Real.sqrt_sq Real.pi_pos.le]
    rw [h1]
    have hs : Real.sqrt (2 * t / π) ≠ 0 := by positivity
    field_simp
  rw [← hval]
  exact hsqrt

/-- Chain rule for 7.14.7: `(d/dt) C(√(2t/π)) = cos t/√(2πt)` for `t > 0`. -/
-- no-dlmf: chain-rule helper for 7.14.7, no DLMF equation
private theorem hasDerivAt_fresnelC_sqrt_comp {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => fresnelC (Real.sqrt (2*u/π)))
      (Real.cos t / Real.sqrt (2*π*t)) t := by
  have hs := hasDerivAt_sqrt_two_mul_div_pi ht
  have hC := (hasDerivAt_fresnelC (Real.sqrt (2*t/π))).comp t hs
  have hcosArg : cosArg (Real.sqrt (2*t/π)) = Real.cos t := by
    unfold cosArg
    rw [Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  simpa [Function.comp, hcosArg, mul_one_div] using hC

/-- Chain rule for 7.14.8: `(d/dt) S(√(2t/π)) = sin t/√(2πt)` for `t > 0`. -/
-- no-dlmf: chain-rule helper for 7.14.8, no DLMF equation
private theorem hasDerivAt_fresnelS_sqrt_comp {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => fresnelS (Real.sqrt (2*u/π)))
      (Real.sin t / Real.sqrt (2*π*t)) t := by
  have hs := hasDerivAt_sqrt_two_mul_div_pi ht
  have hS := (hasDerivAt_fresnelS (Real.sqrt (2*t/π))).comp t hs
  have hsinArg : sinArg (Real.sqrt (2*t/π)) = Real.sin t := by
    unfold sinArg
    rw [Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  simpa [Function.comp, hsinArg, mul_one_div] using hS

/-- **Generic IBP reduction for 7.14.7/7.14.8.** For a bounded `g` with `g 0 = 0`,
`g → 1/2` at `∞`, and `(d/dt) g(√(2t/π)) = trig t/√(2πt)` (`|trig| ≤ 1`), the
Laplace transform of `g(√(2t/π))` reduces to the fractional Gamma moment of
`trig`, via the Laplace module's derivative rule (DLMF 1.14.27). -/
-- no-dlmf: IBP reduction lemma for 7.14.7/7.14.8; the 1.14.27 citation is the method used
private theorem laplace_fresnel_comp_eq (a : ℝ) (ha : 0 < a) (g trig : ℝ → ℝ)
    (hgc : Continuous g) (hg0 : g 0 = 0) (hglim : Tendsto g atTop (𝓝 (1/2)))
    (htrig_cont : Continuous trig) (htrig_le : ∀ t : ℝ, |trig t| ≤ 1)
    (hderiv : ∀ t : ℝ, 0 < t →
        HasDerivAt (fun u : ℝ => g (Real.sqrt (2*u/π))) (trig t / Real.sqrt (2*π*t)) t) :
    ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * g (Real.sqrt (2*t/π))
      = (∫ t in Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t))
          / (a * Real.sqrt (2*π)) := by
  have hdom := integrableOn_rpow_neg_half_mul_exp a ha
  set f : ℝ → ℂ := fun t => ((g (Real.sqrt (2*t/π)) : ℝ) : ℂ) with hfdef
  set f' : ℝ → ℂ := fun t => ((trig t / Real.sqrt (2*π*t) : ℝ) : ℂ) with hf'def
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → |g x| ≤ M := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hglim 1 one_pos
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max X 0)).exists_bound_of_continuousOn
      hgc.continuousOn
    refine ⟨max C (|(1:ℝ)/2| + 1), le_max_of_le_right (by positivity), fun x hx => ?_⟩
    rcases le_or_gt x (max X 0) with hxle | hxgt
    · exact le_trans (by simpa [Real.norm_eq_abs] using hC x ⟨hx, hxle⟩) (le_max_left _ _)
    · have hxX : X ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left X 0) hxgt)
      have hd := hX x hxX
      rw [Real.dist_eq] at hd
      have hbnd : |g x| ≤ |(1:ℝ)/2| + 1 := by
        have h2 := abs_sub_abs_le_abs_sub (g x) ((1:ℝ)/2)
        linarith
      exact le_trans hbnd (le_max_right _ _)
  have hfcont : Continuous f := by
    apply Complex.continuous_ofReal.comp
    exact hgc.comp (Real.continuous_sqrt.comp (by fun_prop))
  have hfbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M := by
    intro t ht
    rw [hfdef]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hMb _ (Real.sqrt_nonneg _)
  have hf_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f t) (Ioi 0) := by
    refine integrableOn_laplaceTransform_of_exponentialOrder (σ₀ := 0) (M := M) hM0
      hfcont.aestronglyMeasurable ?_ (by simpa using ha)
    intro t ht
    rw [zero_mul, Real.exp_zero, mul_one]
    exact hfbound t (le_of_lt ht)
  have hf'_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f' t) (Ioi 0) := by
    have hdom' : IntegrableOn
        (fun t : ℝ => (Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * Real.exp (-(a * t))))
        (Ioi (0:ℝ)) := hdom.const_mul _
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f' t)
        (volume.restrict (Ioi (0:ℝ))) := by
      have h1 : ContinuousOn f' (Ioi (0:ℝ)) := by
        apply Complex.continuous_ofReal.comp_continuousOn
        apply ContinuousOn.div htrig_cont.continuousOn
          (Real.continuous_sqrt.comp (by fun_prop : Continuous fun t : ℝ => 2*π*t)).continuousOn
        intro t ht
        have htpos : (0:ℝ) < t := ht
        have h2πt : (0:ℝ) < 2*π*t := by positivity
        exact (Real.sqrt_pos.mpr h2πt).ne'
      have h2 : ContinuousOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t)) (Ioi (0:ℝ)) :=
        (Complex.continuous_exp.comp (by fun_prop)).continuousOn
      exact (h2.mul h1).aestronglyMeasurable measurableSet_Ioi
    refine Integrable.mono' hdom' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0:ℝ) < t := ht
    have h2πt : (0:ℝ) < 2*π*t := by positivity
    have hsq : Real.sqrt (2*π*t) = Real.sqrt (2*π) * Real.sqrt t := by
      rw [← Real.sqrt_mul (by positivity) t]
    have hnorm_exp : ‖Complex.exp (-(a:ℂ) * (t : ℂ))‖ = Real.exp (-a * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [norm_mul, hnorm_exp, hf'def]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg (2*π*t))]
    have hrpow : t ^ (-(1/2):ℝ) = (Real.sqrt t)⁻¹ := by
      rw [Real.rpow_neg htpos.le, Real.sqrt_eq_rpow]
    have hsp : (0:ℝ) < Real.sqrt (2*π*t) := Real.sqrt_pos.mpr h2πt
    calc Real.exp (-a * t) * (|trig t| / Real.sqrt (2*π*t))
        ≤ Real.exp (-a * t) * (1 / Real.sqrt (2*π*t)) := by
          gcongr
          exact htrig_le t
      _ = (Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * Real.exp (-(a * t))) := by
          rw [hsq, hrpow]
          have h1 : Real.sqrt (2*π) ≠ 0 := by positivity
          have h2 : Real.sqrt t ≠ 0 := by positivity
          field_simp
  have hcont0 : ContinuousWithinAt f (Ici (0:ℝ)) 0 := hfcont.continuousWithinAt
  have hbdry : Tendsto (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * f t) atTop (𝓝 0) := by
    have hv_to0 : Tendsto (fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖) atTop (𝓝 0) := by
      have heq : ∀ t : ℝ, ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ = Real.exp (-a * t) := by
        intro t
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      simp_rw [heq]
      have : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      exact Real.tendsto_exp_atBot.comp this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (t₀ := atTop)
      (f := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ)) * f t‖)
      (g := fun t : ℝ => ‖Complex.exp (-(a:ℂ) * (t:ℂ))‖ * M)
    · filter_upwards with t using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hfbound t ht.le) (norm_nonneg _)
    · simpa using hv_to0.mul_const M
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have := (hderiv t ht).ofReal_comp
    simpa [hfdef, hf'def] using this
  have hkey := laplaceTransform_deriv (f := f) (f' := f') (s := (a:ℂ))
    hd hf_int hf'_int hcont0 hbdry
  have hf0 : f 0 = 0 := by
    rw [hfdef]
    simp only
    rw [show (2*(0:ℝ)/π) = 0 by norm_num, Real.sqrt_zero, hg0, Complex.ofReal_zero]
  rw [hf0, sub_zero] at hkey
  set I₀ : ℝ := ∫ t in Ioi (0:ℝ), t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t) with hI₀
  have hLf' : laplaceTransform f' (a:ℂ) = ((I₀ / Real.sqrt (2*π) : ℝ) : ℂ) := by
    simp only [laplaceTransform]
    have hcongr : ∀ t ∈ Ioi (0:ℝ), Complex.exp (-(a:ℂ) * (t:ℂ)) * f' t
        = (((Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t)) : ℝ) : ℂ) := by
      intro t ht
      have htpos : (0:ℝ) < t := ht
      have h2πt : (0:ℝ) < 2*π*t := by positivity
      have hsq : Real.sqrt (2*π*t) = Real.sqrt (2*π) * Real.sqrt t := by
        rw [← Real.sqrt_mul (by positivity) t]
      have hrpow : t ^ (-(1/2):ℝ) = (Real.sqrt t)⁻¹ := by
        rw [Real.rpow_neg htpos.le, Real.sqrt_eq_rpow]
      have hreal : Real.exp (-a*t) * (trig t / Real.sqrt (2*π*t))
          = (Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t)) := by
        rw [hsq, hrpow]
        have h1 : Real.sqrt (2*π) ≠ 0 := by positivity
        have h2 : Real.sqrt t ≠ 0 := by positivity
        field_simp
      rw [hf'def]
      simp only
      rw [← hreal]
      push_cast
      ring
    have hof : (∫ t in Ioi (0:ℝ),
          (((Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t)) : ℝ) : ℂ))
        = (((∫ t in Ioi (0:ℝ),
            (Real.sqrt (2*π))⁻¹ * (t ^ (-(1/2):ℝ) * (Real.exp (-(a*t)) * trig t))) : ℝ) : ℂ) :=
      _root_.integral_ofReal
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hof]
    apply Complex.ofReal_inj.mpr
    rw [integral_const_mul, ← hI₀, inv_mul_eq_div]
  rw [hLf'] at hkey
  have hbridge : laplaceTransform f (a:ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * g (Real.sqrt (2*t/π))) : ℝ) := by
    simp only [laplaceTransform]
    have hcongr : ∀ t : ℝ, Complex.exp (-(a:ℂ) * (t:ℂ)) * f t
        = ((Real.exp (-a*t) * g (Real.sqrt (2*t/π)) : ℝ) : ℂ) := by
      intro t
      rw [hfdef]
      simp only
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
    exact _root_.integral_ofReal
  have ha_ne : (a:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hval : laplaceTransform f (a:ℂ) = ((I₀ / Real.sqrt (2*π) : ℝ) : ℂ) / (a:ℂ) := by
    rw [eq_div_iff ha_ne, mul_comm]
    exact hkey.symm
  rw [hbridge] at hval
  have hfinal : ((∫ t in Ioi (0:ℝ), Real.exp (-a*t) * g (Real.sqrt (2*t/π))) : ℝ)
      = (I₀ / Real.sqrt (2*π)) / a := by
    have h2 : ((I₀ / Real.sqrt (2*π) : ℝ) : ℂ) / (a:ℂ)
        = (((I₀ / Real.sqrt (2*π)) / a : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2] at hval
    exact_mod_cast hval
  rw [hfinal]
  have hsπ : Real.sqrt (2*π) ≠ 0 := by positivity
  field_simp

end Fresnel714Support

-- no-dlmf: real/narrowed restriction of DLMF 7.14.7; faithful surface is cfresnel_7_14_7
/-- Laplace transform of the Fresnel cosine integral `C(√(2t/π))`, real
specialization: for real `a > 0`
(DLMF 7.14.7 is stated for complex `a` with `Re a > 0`).
-/
theorem erf_7_14_7 (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ),
        Real.exp (-a * t) * FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / Real.pi))
      = (Real.sqrt (a ^ 2 + 1) + a) ^ (1 / 2 : ℝ)
          / (2 * a * Real.sqrt (a ^ 2 + 1)) := by
  rw [laplace_fresnel_comp_eq a ha FLMF.Fresnel.fresnelC Real.cos
    FLMF.Fresnel.continuous_fresnelC FLMF.Fresnel.fresnelC_zero FLMF.Fresnel.tendsto_fresnelC
    Real.continuous_cos (fun t => Real.abs_cos_le_one t)
    (fun t ht => hasDerivAt_fresnelC_sqrt_comp ht)]
  rw [integral_rpow_neg_half_exp_cos a ha]
  set r : ℝ := Real.sqrt (a^2+1) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) π]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hπ : Real.sqrt π ≠ 0 := by positivity
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have hane : a ≠ 0 := ha.ne'
  have hrne : r ≠ 0 := hr.ne'
  field_simp
  linear_combination (-1 : ℝ) * h2

/-- **DLMF 7.14.7** — Laplace transform of the Fresnel cosine integral
`C(√(2t/π))` (real argument), for complex `a` with `Re a > 0`:
`∫₀^∞ e^{-at} C(√(2t/π)) dt = (√(a²+1)+a)^{1/2} / (2a√(a²+1))`.

DAG: E-7.14.7.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem cfresnel_7_14_7 {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ),
        Complex.exp (-a * (t:ℂ)) * (FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π)) : ℂ)
      = Complex.sqrt (Complex.sqrt (a ^ 2 + 1) + a) / (2 * a * Complex.sqrt (a ^ 2 + 1)) := by
  obtain ⟨M, hM0, hMb⟩ := aux714_bounded_of_tendsto FLMF.Fresnel.continuous_fresnelC
    FLMF.Fresnel.tendsto_fresnelC
  have hU : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ
      (fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t:ℂ))
        * (FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π)) : ℂ)) {b : ℂ | 0 < b.re} := by
    refine aux714_analyticOnNhd_laplace
      (χ := fun t : ℝ => ((FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π)) : ℝ) : ℂ)) (C := M) (k := 0)
      (by norm_num) (Complex.continuous_ofReal.comp (FLMF.Fresnel.continuous_fresnelC.comp
        (Real.continuous_sqrt.comp (by fun_prop)))).continuousOn (fun t ht => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, mul_one]
    exact hMb _ (Real.sqrt_nonneg _)
  have hG : AnalyticOnNhd ℂ
      (fun b : ℂ => Complex.sqrt (Complex.sqrt (b ^ 2 + 1) + b)
        / (2 * b * Complex.sqrt (b ^ 2 + 1))) {b : ℂ | 0 < b.re} := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hU
    have hbre : 0 < b.re := hb
    obtain ⟨hw, hwa, -⟩ := aux714_surd_re_pos hbre
    have hslit1 : b ^ 2 + 1 ∈ Complex.slitPlane := aux714_sq_add_one_mem_slitPlane hbre
    have hslit2 : Complex.sqrt (b ^ 2 + 1) + b ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hwa)
    have hd1 : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (c ^ 2 + 1)) b := by
      have h := (Complex.differentiableAt_sqrt hslit1).comp b
        (show DifferentiableAt ℂ (fun c : ℂ => c ^ 2 + 1) b by fun_prop)
      simpa [Function.comp] using h
    have hd1' : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (c ^ 2 + 1) + c) b :=
      hd1.add differentiableAt_id
    have hd2 : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (Complex.sqrt (c ^ 2 + 1) + c)) b := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.sqrt)
        (f := fun c : ℂ => Complex.sqrt (c ^ 2 + 1) + c) b
        (Complex.differentiableAt_sqrt hslit2) hd1'
      simpa [Function.comp] using h
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hbre
      simp at hbre
    have hwne : Complex.sqrt (b ^ 2 + 1) ≠ 0 := by
      intro h
      rw [h] at hw
      simp at hw
    have hden : (2 : ℂ) * b * Complex.sqrt (b ^ 2 + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hb0) hwne
    exact (hd2.div (((differentiableAt_const (2:ℂ)).mul differentiableAt_id).mul hd1)
      hden).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hr0 : (0:ℝ) ≤ x ^ 2 + 1 := by positivity
  have hcast : ((x:ℂ) ^ 2 + 1) = (((x ^ 2 + 1 : ℝ)) : ℂ) := by push_cast; ring
  have hw : Complex.sqrt ((x:ℂ) ^ 2 + 1) = ((Real.sqrt (x ^ 2 + 1) : ℝ) : ℂ) := by
    rw [hcast, aux714_csqrt_ofReal hr0]
  have hxle : x ≤ Real.sqrt (x ^ 2 + 1) := by
    nlinarith [Real.sq_sqrt hr0, Real.sqrt_nonneg (x ^ 2 + 1)]
  have hsum : (0:ℝ) ≤ Real.sqrt (x ^ 2 + 1) + x := by linarith
  have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x:ℂ) * (t:ℂ))
        * ((FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π)) : ℝ) : ℂ))
      = ((∫ t in Ioi (0 : ℝ),
          Real.exp (-x * t) * FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π)) : ℝ) : ℂ) :=
    aux714_laplace_ofReal (fun t : ℝ => FLMF.Fresnel.fresnelC (Real.sqrt (2 * t / π))) x
  rw [hL, erf_7_14_7 x hx, ← Real.sqrt_eq_rpow, hw,
    show ((Real.sqrt (x ^ 2 + 1) : ℝ) : ℂ) + (x:ℂ) = (((Real.sqrt (x ^ 2 + 1) + x : ℝ)) : ℂ) by
      push_cast; ring,
    aux714_csqrt_ofReal hsum]
  push_cast
  ring

-- no-dlmf: real/narrowed restriction of DLMF 7.14.8; faithful surface is cfresnel_7_14_8
/-- Laplace transform of the Fresnel sine integral `S(√(2t/π))`, real
specialization: for real `a > 0`
(DLMF 7.14.8 is stated for complex `a` with `Re a > 0`).
-/
theorem erf_7_14_8 (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ),
        Real.exp (-a * t) * FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / Real.pi))
      = (Real.sqrt (a ^ 2 + 1) - a) ^ (1 / 2 : ℝ)
          / (2 * a * Real.sqrt (a ^ 2 + 1)) := by
  rw [laplace_fresnel_comp_eq a ha FLMF.Fresnel.fresnelS Real.sin
    FLMF.Fresnel.continuous_fresnelS FLMF.Fresnel.fresnelS_zero FLMF.Fresnel.tendsto_fresnelS
    Real.continuous_sin (fun t => Real.abs_sin_le_one t)
    (fun t ht => hasDerivAt_fresnelS_sqrt_comp ht)]
  rw [integral_rpow_neg_half_exp_sin a ha]
  set r : ℝ := Real.sqrt (a^2+1) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) π]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hπ : Real.sqrt π ≠ 0 := by positivity
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have hane : a ≠ 0 := ha.ne'
  have hrne : r ≠ 0 := hr.ne'
  field_simp
  linear_combination (-(Real.sqrt (r-a))) * h2

/-- **DLMF 7.14.8** — Laplace transform of the Fresnel sine integral
`S(√(2t/π))` (real argument), for complex `a` with `Re a > 0`:
`∫₀^∞ e^{-at} S(√(2t/π)) dt = (√(a²+1)-a)^{1/2} / (2a√(a²+1))`.

DAG: E-7.14.8.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem cfresnel_7_14_8 {a : ℂ} (ha : 0 < a.re) :
    ∫ t in Ioi (0 : ℝ),
        Complex.exp (-a * (t:ℂ)) * (FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π)) : ℂ)
      = Complex.sqrt (Complex.sqrt (a ^ 2 + 1) - a) / (2 * a * Complex.sqrt (a ^ 2 + 1)) := by
  obtain ⟨M, hM0, hMb⟩ := aux714_bounded_of_tendsto FLMF.Fresnel.continuous_fresnelS
    FLMF.Fresnel.tendsto_fresnelS
  have hU : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ
      (fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t:ℂ))
        * (FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π)) : ℂ)) {b : ℂ | 0 < b.re} := by
    refine aux714_analyticOnNhd_laplace
      (χ := fun t : ℝ => ((FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π)) : ℝ) : ℂ)) (C := M) (k := 0)
      (by norm_num) (Complex.continuous_ofReal.comp (FLMF.Fresnel.continuous_fresnelS.comp
        (Real.continuous_sqrt.comp (by fun_prop)))).continuousOn (fun t ht => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_zero, mul_one]
    exact hMb _ (Real.sqrt_nonneg _)
  have hG : AnalyticOnNhd ℂ
      (fun b : ℂ => Complex.sqrt (Complex.sqrt (b ^ 2 + 1) - b)
        / (2 * b * Complex.sqrt (b ^ 2 + 1))) {b : ℂ | 0 < b.re} := by
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hU
    have hbre : 0 < b.re := hb
    obtain ⟨hw, -, hwm⟩ := aux714_surd_re_pos hbre
    have hslit1 : b ^ 2 + 1 ∈ Complex.slitPlane := aux714_sq_add_one_mem_slitPlane hbre
    have hslit2 : Complex.sqrt (b ^ 2 + 1) - b ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl hwm)
    have hd1 : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (c ^ 2 + 1)) b := by
      have h := (Complex.differentiableAt_sqrt hslit1).comp b
        (show DifferentiableAt ℂ (fun c : ℂ => c ^ 2 + 1) b by fun_prop)
      simpa [Function.comp] using h
    have hd1' : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (c ^ 2 + 1) - c) b :=
      hd1.sub differentiableAt_id
    have hd2 : DifferentiableAt ℂ (fun c : ℂ => Complex.sqrt (Complex.sqrt (c ^ 2 + 1) - c)) b := by
      have h := DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.sqrt)
        (f := fun c : ℂ => Complex.sqrt (c ^ 2 + 1) - c) b
        (Complex.differentiableAt_sqrt hslit2) hd1'
      simpa [Function.comp] using h
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hbre
      simp at hbre
    have hwne : Complex.sqrt (b ^ 2 + 1) ≠ 0 := by
      intro h
      rw [h] at hw
      simp at hw
    have hden : (2 : ℂ) * b * Complex.sqrt (b ^ 2 + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hb0) hwne
    exact (hd2.div (((differentiableAt_const (2:ℂ)).mul differentiableAt_id).mul hd1)
      hden).differentiableWithinAt
  refine aux714_eq_of_analytic_rightHalfPlane hF hG (fun x hx => ?_) a ha
  have hr0 : (0:ℝ) ≤ x ^ 2 + 1 := by positivity
  have hcast : ((x:ℂ) ^ 2 + 1) = (((x ^ 2 + 1 : ℝ)) : ℂ) := by push_cast; ring
  have hw : Complex.sqrt ((x:ℂ) ^ 2 + 1) = ((Real.sqrt (x ^ 2 + 1) : ℝ) : ℂ) := by
    rw [hcast, aux714_csqrt_ofReal hr0]
  have hxle : x ≤ Real.sqrt (x ^ 2 + 1) := by
    nlinarith [Real.sq_sqrt hr0, Real.sqrt_nonneg (x ^ 2 + 1)]
  have hsum : (0:ℝ) ≤ Real.sqrt (x ^ 2 + 1) - x := by linarith
  have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x:ℂ) * (t:ℂ))
        * ((FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π)) : ℝ) : ℂ))
      = ((∫ t in Ioi (0 : ℝ),
          Real.exp (-x * t) * FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π)) : ℝ) : ℂ) :=
    aux714_laplace_ofReal (fun t : ℝ => FLMF.Fresnel.fresnelS (Real.sqrt (2 * t / π))) x
  rw [hL, erf_7_14_8 x hx, ← Real.sqrt_eq_rpow, hw,
    show ((Real.sqrt (x ^ 2 + 1) : ℝ) : ℂ) - (x:ℂ) = (((Real.sqrt (x ^ 2 + 1) - x : ℝ)) : ℂ) by
      push_cast; ring,
    aux714_csqrt_ofReal hsum]
  push_cast
  ring

end FLMF.Error
