import FLMF.Chapter7.Erf
import FLMF.Chapter7.Definitions
import FLMF.Chapter7.AsymptoticExpansions
import FLMF.Chapter7.FresnelBasic
import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.FresnelComplex
import FLMF.Support.ParametricIntegralAnalytic
import FLMF.Support.MellinBarnes

/-!
# DLMF §7.7 — Integral Representations (statement surfaces)

Real specializations of the DLMF §7.7 integral representations for the error
functions `erf`/`erfc` and the Fresnel auxiliary functions `f`, `g`.

This file formalizes *statement surfaces* (Phase 5): faithful, TRUE real-valued
specializations of the §7.7 identities, with `:= by sorry` bodies. Equations
that are intrinsically complex (Faddeeva `w(z)`, conjugate symmetry), require a
Mellin–Barnes contour, or reference the Fresnel auxiliaries `f`, `g` (which FLMF
does not yet commit as named functions) are recorded below as **documented
deferral comments**, never as vacuous theorems.

The committed real functions used here are `FLMF.Error.erf`, `FLMF.Error.erfc`
and the Fresnel integrals `FLMF.Fresnel.fresnelC`, `FLMF.Fresnel.fresnelS`.

## Coverage of 7.7.1 – 7.7.16

* `erf_7_7_1`  — `erfc x` half-line integral representation (real `x`).
* `erf_7_7_4`  — `√(πa) e^{a x²} erfc(√a · x)` half-line integral (real `a>0`, `x>0`).
* `erf_7_7_5`  — `erf a` via the `∫₀¹ e^{-a t²}/(t²+1)` representation (real `a>0`).
* `erf_7_7_6`  — `erfc` of the completed-square Gaussian integral over `[x,∞)`.
* `erf_7_7_9`  — `∫₀ˣ erf t dt = x·erf x + (e^{-x²}-1)/√π` (real `x`).
* `erf_7_7_15` — `∫₀^∞ e^{-a t} cos(t²) dt` Laplace–cosine representation (real `a>0`).
* `erf_7_7_16` — `∫₀^∞ e^{-a t} sin(t²) dt` Laplace–sine  representation (real `a>0`).

* `erf_7_7_10` — Fresnel auxiliary `f` half-line integral representation (real `z ≥ 0`).
* `erf_7_7_11` — Fresnel auxiliary `g` half-line integral representation (real `z ≥ 0`).

Now RESOLVED in the complex layer (kept as deferral notes below for context):
7.7.2 → Error/Faddeeva (erf_7_7_2); 7.7.3/7.7.7/7.7.8 → Error/ComplexErfExtra
(erf_7_7_3/_7/_8); 7.7.12/7.7.13/7.7.14 → Fresnel/Complex (cfresnel_7_7_12/_13/_14).

DLMF's own 7.7.1/7.7.4/7.7.6/7.7.10/7.7.11/7.7.15/7.7.16 are stated for complex
variables (phase-sector or half-plane constraints). The real specializations
above are demoted (`-- no-dlmf`, no `DLMF n.n.n` marker) and each carries a
`_dlmf` companion below stating DLMF's full complex-domain form using `cerfc`
(`Error/ComplexErf`) and `cfresnelAuxF`/`cfresnelAuxG` (`Fresnel/Complex`). All
seven companions are now proven, by analytic continuation off the positive real
axis: the real specialization pins the identity on `ℝ₊`, both sides are analytic
in the complex parameter on the (open) DLMF domain, and the identity theorem
propagates the identity; for the closed sectors `|ph z| ≤ π/4` the boundary is
then reached by dominated convergence along `z + 1/(n+1)`.
-/

namespace FLMF.Error

open MeasureTheory Real Set Filter Topology
open scoped Real

/-! ## Analytic-continuation toolkit for the `_dlmf` companions

Each `_dlmf` companion below states its identity on the full complex domain
DLMF gives it, while the real specialization above it proves the identity on the
positive real axis.  The bridge is always the same: both sides are analytic in
the complex parameter on the (open) domain, they agree on a sequence of positive
reals accumulating at an interior point, so the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) propagates the identity
to the whole domain.  The analytic half of the argument for the parametric
integrals is `FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane`. -/

-- no-dlmf: principal-branch bridge `r^{1/2} = √r` for `r ≥ 0`, support lemma
private lemma aux_cpow_half_ofReal {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt r : ℂ) := by
  rw [Real.sqrt_eq_rpow, show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow hr]

-- no-dlmf: principal-branch bridge `r^{-1/2} = (√r)⁻¹` for `r ≥ 0`, support lemma
private lemma aux_cpow_neg_half_ofReal {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ)) ^ (-((1 : ℂ) / 2)) = (((Real.sqrt r)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.cpow_neg, aux_cpow_half_ofReal hr]
  push_cast
  ring

-- no-dlmf: identity theorem transfer from the positive reals to a preconnected set
/-- **Identity theorem, positive-real form.**  Two functions analytic on a
preconnected set `U ∋ 1` that agree at every positive real number agree on all of
`U`: the positive reals `1 + 1/(n+1)` accumulate at `1`. -/
private lemma aux_eq_of_analytic_of_real {U : Set ℂ} (hU : IsPreconnected U)
    (h₀ : (1 : ℂ) ∈ U) {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) :
    ∀ a ∈ U, F a = G a := by
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

-- no-dlmf: right-half-plane instance of `aux_eq_of_analytic_of_real`, support lemma
private lemma aux_eq_of_analytic_rightHalfPlane {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {a : ℂ | 0 < a.re}) (hG : AnalyticOnNhd ℂ G {a : ℂ | 0 < a.re})
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) :
    ∀ a : ℂ, 0 < a.re → F a = G a :=
  aux_eq_of_analytic_of_real (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by simp) hF hG hreal

-- no-dlmf: entirety of the complex Fresnel cosine integral, support lemma
private lemma aux_differentiable_cfresnelC : Differentiable ℂ FLMF.Fresnel.cfresnelC := by
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
private lemma aux_differentiable_cfresnelS : Differentiable ℂ FLMF.Fresnel.cfresnelS := by
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
private lemma aux_differentiable_cfresnelAuxF : Differentiable ℂ FLMF.Fresnel.cfresnelAuxF := by
  have hC := aux_differentiable_cfresnelC
  have hS := aux_differentiable_cfresnelS
  unfold FLMF.Fresnel.cfresnelAuxF
  fun_prop

-- no-dlmf: entirety of the complex Fresnel auxiliary `g`, support lemma
private lemma aux_differentiable_cfresnelAuxG : Differentiable ℂ FLMF.Fresnel.cfresnelAuxG := by
  have hC := aux_differentiable_cfresnelC
  have hS := aux_differentiable_cfresnelS
  unfold FLMF.Fresnel.cfresnelAuxG
  fun_prop

-- no-dlmf: real-agreement bridge for the complex auxiliary `f`, support lemma
private lemma aux_cfresnelAuxF_ofReal (x : ℝ) :
    FLMF.Fresnel.cfresnelAuxF (x : ℂ) = ((fresnelAuxF x : ℝ) : ℂ) := by
  unfold FLMF.Fresnel.cfresnelAuxF fresnelAuxF
  rw [FLMF.Fresnel.cfresnelC_ofReal, FLMF.Fresnel.cfresnelS_ofReal]
  push_cast
  ring

-- no-dlmf: real-agreement bridge for the complex auxiliary `g`, support lemma
private lemma aux_cfresnelAuxG_ofReal (x : ℝ) :
    FLMF.Fresnel.cfresnelAuxG (x : ℂ) = ((fresnelAuxG x : ℝ) : ℂ) := by
  unfold FLMF.Fresnel.cfresnelAuxG fresnelAuxG
  rw [FLMF.Fresnel.cfresnelC_ofReal, FLMF.Fresnel.cfresnelS_ofReal]
  push_cast
  ring

-- no-dlmf: analyticity of a Laplace transform with bounded continuous kernel, support lemma
/-- The Laplace transform `a ↦ ∫₀^∞ e^{-a t} χ(t) dt` of a bounded continuous
kernel is analytic on the right half-plane `{a | Re a > 0}`.  Domination: on
`{σ ≤ Re a}` the parameter derivative is bounded by `t·e^{-σ t}`. -/
private lemma aux_analyticOnNhd_laplace {M : ℝ} {χ : ℝ → ℂ} (hχc : Continuous χ)
    (hχ1 : ∀ t, ‖χ t‖ ≤ M) :
    AnalyticOnNhd ℂ (fun a : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) * χ t)
      {a : ℂ | 0 < a.re} := by
  have hnorm : ∀ (a : ℂ) (t : ℝ), ‖Complex.exp (-a * (t : ℂ))‖ = Real.exp (-a.re * t) := by
    intro a t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane
    (f := fun a t => Complex.exp (-a * (t : ℂ)) * χ t)
    (f' := fun a t => -(t : ℂ) * Complex.exp (-a * (t : ℂ)) * χ t)
    (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Integrable.mono' (g := fun t : ℝ => M * Real.exp (-a.re * t))
      ((by simpa using exp_neg_integrableOn_Ioi 0 ha :
        IntegrableOn (fun t : ℝ => Real.exp (-a.re * t)) (Ioi (0 : ℝ))).const_mul M)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with t
    rw [norm_mul, hnorm]
    calc Real.exp (-a.re * t) * ‖χ t‖ ≤ Real.exp (-a.re * t) * M := by
          gcongr; exact hχ1 t
      _ = M * Real.exp (-a.re * t) := by ring
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · filter_upwards with t a _
    have h1 : HasDerivAt (fun z : ℂ => -z * (t : ℂ)) (-(t : ℂ)) a := by
      simpa using ((hasDerivAt_id a).neg.mul_const (t : ℂ))
    have h2 := (h1.cexp).mul_const (χ t)
    convert h2 using 1
    ring
  · intro σ hσ
    refine ⟨fun t : ℝ => M * (t * Real.exp (-σ * t)), ?_, ?_⟩
    · have h : IntegrableOn (fun x : ℝ => Real.exp (-σ * x) * x ^ (1 : ℝ)) (Ioi (0 : ℝ)) :=
        integrableOn_exp_neg_mul_rpow_Ioi σ 1 hσ (by norm_num)
      have h2 : IntegrableOn (fun t : ℝ => t * Real.exp (-σ * t)) (Ioi (0 : ℝ)) := by
        refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
        rw [Real.rpow_one]; ring
      exact h2.const_mul M
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, hnorm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      calc t * Real.exp (-a.re * t) * ‖χ t‖ ≤ t * Real.exp (-σ * t) * M := by
            gcongr
            exact hχ1 t
        _ = M * (t * Real.exp (-σ * t)) := by ring

-- no-dlmf: entirety of the complex complementary error function, support lemma
private lemma aux_differentiable_cerfc : Differentiable ℂ cerfc := by
  intro z
  have h : DifferentiableAt ℂ (fun w : ℂ => 1 - cerf w) z :=
    ((hasDerivAt_cerf z).const_sub 1).differentiableAt
  exact h

/-! ### Geometry of the shifted square `t + z²` (DLMF 7.7.4)

For `t ≥ 0` and `Re z > 0` the point `t + z²` never lies on the branch cut
`(-∞, 0]`, and it stays at distance at least `(Re z)²` from `0`.  Both facts are
what makes the parametric integral of 7.7.4 analytic in `z` on the right
half-plane. -/

-- no-dlmf: real part of `t + z²`, support lemma
private lemma aux_shift_re (t : ℝ) (z : ℂ) : ((t : ℂ) + z ^ 2).re = t + (z.re ^ 2 - z.im ^ 2) := by
  simp [pow_two, Complex.add_re, Complex.mul_re]

-- no-dlmf: imaginary part of `t + z²`, support lemma
private lemma aux_shift_im (t : ℝ) (z : ℂ) : ((t : ℂ) + z ^ 2).im = 2 * z.re * z.im := by
  simp [pow_two, Complex.add_im, Complex.mul_im]; ring

-- no-dlmf: `t + z²` avoids the principal branch cut, support lemma
private lemma aux_shift_mem_slitPlane {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.re) :
    ((t : ℂ) + z ^ 2) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hzi : z.im = 0
  · left; rw [aux_shift_re, hzi]; nlinarith [hz]
  · right
    rw [aux_shift_im]
    intro hc
    rcases mul_eq_zero.mp hc with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact absurd h' (ne_of_gt hz)
    · exact hzi h

-- no-dlmf: uniform lower bound `‖t + z²‖ ≥ (Re z)²`, support lemma
private lemma aux_shift_norm_lb {t : ℝ} (ht : 0 ≤ t) (z : ℂ) : z.re ^ 2 ≤ ‖(t : ℂ) + z ^ 2‖ := by
  have hns : ‖(t : ℂ) + z ^ 2‖ ^ 2 = ((t : ℂ) + z ^ 2).re ^ 2 + ((t : ℂ) + z ^ 2).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : (z.re ^ 2) ^ 2 ≤ ‖(t : ℂ) + z ^ 2‖ ^ 2 := by
    rw [hns, aux_shift_re, aux_shift_im]
    nlinarith [sq_nonneg (t - z.im ^ 2), mul_nonneg ht (sq_nonneg z.re),
      mul_nonneg (sq_nonneg z.re) (sq_nonneg z.im)]
  nlinarith [hsq, sq_nonneg z.re, norm_nonneg ((t : ℂ) + z ^ 2)]

-- no-dlmf: analyticity in `z` of the DLMF 7.7.4 half-line integral, support lemma
/-- For `Re a > 0` the parametric integral `z ↦ ∫₀^∞ e^{-a t}(t+z²)^{-1/2} dt` is
analytic on the right half-plane.  Domination on `Metric.ball z₀ (Re z₀ / 2)`:
`‖z‖ ≤ ‖z₀‖ + Re z₀/2` and `‖t+z²‖ ≥ (Re z)² ≥ (Re z₀/2)²`, so the parameter
derivative `-z e^{-a t}(t+z²)^{-3/2}` is dominated by a constant multiple of
`e^{-(Re a) t}`. -/
private lemma aux_analyticOnNhd_shiftPow_z {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + z ^ 2) ^ (-((1 : ℂ) / 2)))
      {z : ℂ | 0 < z.re} := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hexpn : ∀ t : ℝ, ‖Complex.exp (-a * (t : ℂ))‖ = Real.exp (-a.re * t) := by
    intro t; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hcont : ∀ z : ℂ, 0 < z.re → ∀ c : ℂ,
      ContinuousOn (fun t : ℝ => Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + z ^ 2) ^ c)
        (Ioi (0 : ℝ)) := by
    intro z hz c t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : ContinuousAt (fun t : ℝ => ((t : ℂ) + z ^ 2)) t := by fun_prop
    have h2 : ContinuousAt (fun w : ℂ => w ^ c) ((t : ℂ) + z ^ 2) :=
      _root_.continuousAt_cpow_const (aux_shift_mem_slitPlane ht0.le hz)
    have h3 : ContinuousAt (fun t : ℝ => Complex.exp (-a * (t : ℂ))) t := by fun_prop
    exact (h3.mul (ContinuousAt.comp (x := t) h2 h1)).continuousWithinAt
  have hmeas : ∀ z : ℂ, 0 < z.re → ∀ c : ℂ,
      AEStronglyMeasurable (fun t : ℝ => Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + z ^ 2) ^ c)
        (volume.restrict (Ioi (0 : ℝ))) :=
    fun z hz c => (hcont z hz c).aestronglyMeasurable measurableSet_Ioi
  have hexpint : IntegrableOn (fun t : ℝ => Real.exp (-a.re * t)) (Ioi (0 : ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi 0 ha
  have hnormcpow : ∀ (w : ℂ) (y : ℝ), ‖w ^ ((y : ℝ) : ℂ)‖ = ‖w‖ ^ y := Complex.norm_cpow_real
  have hc1 : (-((1 : ℂ) / 2)) = (((-(1 : ℝ) / 2 : ℝ)) : ℂ) := by push_cast; ring
  have hc3 : (-((3 : ℂ) / 2)) = (((-(3 : ℝ) / 2 : ℝ)) : ℂ) := by push_cast; ring
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun z t => Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + z ^ 2) ^ (-((1 : ℂ) / 2)))
    (f' := fun z t => -(Complex.exp (-a * (t : ℂ)) * z * ((t : ℂ) + z ^ 2) ^ (-((3 : ℂ) / 2))))
    hUopen (fun z hz => hmeas z hz _) (fun z hz => ?_) (fun z hz => ?_) ?_ ?_
  · have hzre : (0 : ℝ) < z.re := hz
    refine Integrable.mono' (g := fun t : ℝ => (z.re ^ 2) ^ (-(1 : ℝ) / 2) * Real.exp (-a.re * t))
      (hexpint.const_mul _) (hmeas z hz _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, hexpn, hc1, hnormcpow]
    have hlb := aux_shift_norm_lb ht0.le z
    have h1 : ‖(t : ℂ) + z ^ 2‖ ^ (-(1 : ℝ) / 2) ≤ (z.re ^ 2) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlb (by norm_num)
    calc Real.exp (-a.re * t) * ‖(t : ℂ) + z ^ 2‖ ^ (-(1 : ℝ) / 2)
        ≤ Real.exp (-a.re * t) * (z.re ^ 2) ^ (-(1 : ℝ) / 2) := by gcongr
      _ = (z.re ^ 2) ^ (-(1 : ℝ) / 2) * Real.exp (-a.re * t) := by ring
  · dsimp only
    have h := hmeas z hz (-((3 : ℂ) / 2))
    have h2 : (fun t : ℝ => -(Complex.exp (-a * (t : ℂ)) * z * ((t : ℂ) + z ^ 2) ^ (-((3 : ℂ) / 2))))
        = fun t : ℝ => (-z) * (Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + z ^ 2) ^ (-((3 : ℂ) / 2))) := by
      funext t; ring
    rw [h2]
    exact h.const_mul (-z)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have ht0 : (0 : ℝ) < t := ht
    have h1 : HasDerivAt (fun w : ℂ => (t : ℂ) + w ^ 2) (2 * z) z := by
      have := (hasDerivAt_pow 2 z).const_add ((t : ℂ))
      simpa using this
    have h2 := h1.cpow_const (c := -((1 : ℂ) / 2)) (aux_shift_mem_slitPlane ht0.le hz)
    have h3 := h2.const_mul (Complex.exp (-a * (t : ℂ)))
    convert h3 using 1
    rw [show (-((1 : ℂ) / 2) - 1) = -((3 : ℂ) / 2) by ring]
    ring
  · intro z₀ hz₀
    have hz₀re : (0 : ℝ) < z₀.re := hz₀
    refine ⟨z₀.re / 2, by linarith, fun t : ℝ =>
      ((‖z₀‖ + z₀.re / 2) * ((z₀.re / 2) ^ 2) ^ (-(3 : ℝ) / 2)) * Real.exp (-a.re * t),
      hexpint.const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hzb
    have ht0 : (0 : ℝ) < t := ht
    have hd : ‖z - z₀‖ < z₀.re / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hzb
    have hre : z₀.re / 2 ≤ z.re := by
      have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
      have h3 : |z.re - z₀.re| < z₀.re / 2 := by
        simpa [Complex.sub_re] using lt_of_le_of_lt h2 hd
      have h4 := (abs_lt.mp h3).1
      linarith
    have hzn : ‖z‖ ≤ ‖z₀‖ + z₀.re / 2 := by
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + z₀.re / 2 := by linarith
    have hlb : ((z₀.re / 2) ^ 2) ≤ ‖(t : ℂ) + z ^ 2‖ := by
      have h := aux_shift_norm_lb ht0.le z
      nlinarith [hre, hz₀re]
    have hrp : ‖(t : ℂ) + z ^ 2‖ ^ (-(3 : ℝ) / 2) ≤ ((z₀.re / 2) ^ 2) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlb (by norm_num)
    rw [norm_neg, norm_mul, norm_mul, hexpn, hc3, hnormcpow]
    calc Real.exp (-a.re * t) * ‖z‖ * ‖(t : ℂ) + z ^ 2‖ ^ (-(3 : ℝ) / 2)
        ≤ Real.exp (-a.re * t) * (‖z₀‖ + z₀.re / 2) * ((z₀.re / 2) ^ 2) ^ (-(3 : ℝ) / 2) := by
          gcongr
      _ = ((‖z₀‖ + z₀.re / 2) * ((z₀.re / 2) ^ 2) ^ (-(3 : ℝ) / 2)) * Real.exp (-a.re * t) := by
          ring

/-! ### Gaussian majorants (DLMF 7.7.6)

The completed-square integral of 7.7.6 is differentiated under the integral sign
twice — once in the linear coefficient `b`, once in the quadratic coefficient
`a` — and both times the parameter derivative is a polynomial multiple of a
Gaussian.  These three elementary majorants turn such a product into a plain
Gaussian, whose integrability is upstream. -/

-- no-dlmf: `s ≤ eˢ`, support lemma
private lemma aux_le_exp (s : ℝ) : s ≤ Real.exp s := by
  have h := Real.add_one_le_exp s; linarith

-- no-dlmf: `t²·e^{-γt²} ≤ 1/γ`, support lemma
private lemma aux_sq_mul_exp_le {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    t ^ 2 * Real.exp (-γ * t ^ 2) ≤ 1 / γ := by
  have h := aux_le_exp (γ * t ^ 2)
  have hpos : 0 < Real.exp (γ * t ^ 2) := Real.exp_pos _
  have hinv : Real.exp (-γ * t ^ 2) = (Real.exp (γ * t ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hinv, le_div_iff₀ hγ, mul_comm, ← mul_assoc]
  rw [mul_inv_le_iff₀ hpos] at *
  nlinarith [h, hpos]

-- no-dlmf: `|t|·e^{-γt²} ≤ 1 + 1/γ`, support lemma
private lemma aux_abs_mul_exp_le {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    |t| * Real.exp (-γ * t ^ 2) ≤ 1 + 1 / γ := by
  have h1 : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]
  have h2 : Real.exp (-γ * t ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
  have h3 := aux_sq_mul_exp_le hγ t
  have hpos : (0 : ℝ) < Real.exp (-γ * t ^ 2) := Real.exp_pos _
  calc |t| * Real.exp (-γ * t ^ 2) ≤ (1 + t ^ 2) * Real.exp (-γ * t ^ 2) := by
        exact mul_le_mul_of_nonneg_right h1 hpos.le
    _ = Real.exp (-γ * t ^ 2) + t ^ 2 * Real.exp (-γ * t ^ 2) := by ring
    _ ≤ 1 + 1 / γ := by linarith

-- no-dlmf: `e^{-βt² + B|t|} ≤ e^{B²/(2β)}·e^{-(β/2)t²}`, support lemma
private lemma aux_exp_lin_le {β B : ℝ} (hβ : 0 < β) (t : ℝ) :
    Real.exp (-β * t ^ 2 + B * |t|) ≤ Real.exp (B ^ 2 / (2 * β)) * Real.exp (-(β / 2) * t ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : B * |t| ≤ (β / 2) * t ^ 2 + B ^ 2 / (2 * β) := by
    have h := mul_nonneg (le_of_lt (half_pos hβ)) (sq_nonneg (|t| - B / β))
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    have hβne : β ≠ 0 := ne_of_gt hβ
    field_simp at h ⊢
    nlinarith [h, habs, hβ]
  linarith

-- no-dlmf: norm of the 7.7.6 Gaussian integrand, support lemma
private lemma aux_norm_gauss (a b : ℂ) (t : ℝ) :
    ‖Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ)))‖
      = Real.exp (-(a.re * t ^ 2 + 2 * b.re * t)) := by
  have hz : -(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))
      = -(((t ^ 2 : ℝ) : ℂ) * a + ((2 * t : ℝ) : ℂ) * b) := by push_cast; ring
  rw [Complex.norm_exp, hz]
  congr 1
  rw [Complex.neg_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

-- no-dlmf: pointwise `b`-derivative of the 7.7.6 Gaussian integrand, support lemma
private lemma aux_hasDerivAt_gauss_b (a : ℂ) (t : ℝ) (b : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * w * (t : ℂ))))
      (-(2 * (t : ℂ)) * Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ)))) b := by
  have hc : HasDerivAt (fun w : ℂ => a * (t : ℂ) ^ 2 + 2 * w * (t : ℂ)) (2 * (t : ℂ)) b := by
    simpa using
      (((hasDerivAt_id b).const_mul (2 : ℂ)).mul_const (t : ℂ)).const_add (a * (t : ℂ) ^ 2)
  have h1 : HasDerivAt (fun w : ℂ => -(a * (t : ℂ) ^ 2 + 2 * w * (t : ℂ))) (-(2 * (t : ℂ))) b :=
    hc.neg
  have h2 := h1.cexp
  convert h2 using 1
  ring

-- no-dlmf: pointwise `a`-derivative of the 7.7.6 Gaussian integrand, support lemma
private lemma aux_hasDerivAt_gauss_a (b : ℂ) (t : ℝ) (a : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(w * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
      (-((t : ℂ) ^ 2) * Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ)))) a := by
  have hc : HasDerivAt (fun w : ℂ => w * (t : ℂ) ^ 2 + 2 * b * (t : ℂ)) ((t : ℂ) ^ 2) a := by
    simpa using ((hasDerivAt_id a).mul_const ((t : ℂ) ^ 2)).add_const (2 * b * (t : ℂ))
  have h1 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))) (-((t : ℂ) ^ 2)) a :=
    hc.neg
  have h2 := h1.cexp
  convert h2 using 1
  ring

-- no-dlmf: analyticity in the linear coefficient `b` of the 7.7.6 integral, support lemma
private lemma aux_analyticOnNhd_gauss_b (x : ℝ) {α : ℝ} (hα : 0 < α) :
    AnalyticOnNhd ℂ
      (fun b : ℂ => ∫ t in Ioi x, Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
      (Set.univ : Set ℂ) := by
  have hgauss : ∀ γ : ℝ, 0 < γ → IntegrableOn (fun t : ℝ => Real.exp (-γ * t ^ 2)) (Ioi x) :=
    fun γ hγ => (integrable_exp_neg_mul_sq hγ).integrableOn
  have hlin : ∀ (b : ℂ) (t : ℝ), -(α * t ^ 2 + 2 * b.re * t) ≤ -α * t ^ 2 + (2 * ‖b‖) * |t| := by
    intro b t
    have h1 : |b.re| ≤ ‖b‖ := Complex.abs_re_le_norm b
    have h2 : -(2 * b.re * t) ≤ 2 * ‖b‖ * |t| := by
      have h3 : |2 * b.re * t| ≤ 2 * ‖b‖ * |t| := by
        rw [abs_mul, abs_mul]
        have : |(2 : ℝ)| = 2 := by norm_num
        rw [this]
        have h4 : (0 : ℝ) ≤ |t| := abs_nonneg t
        nlinarith [h1, abs_nonneg b.re, h4]
      linarith [neg_abs_le (2 * b.re * t), le_abs_self (2 * b.re * t), h3]
    linarith
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi x))
    (f := fun b t => Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
    (f' := fun b t => -(2 * (t : ℂ)) * Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
    isOpen_univ (fun b _ => ?_) (fun b _ => ?_) (fun b _ => ?_) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Integrable.mono' (g := fun t : ℝ =>
      Real.exp ((2 * ‖b‖) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * t ^ 2))
      ((hgauss (α / 2) (by linarith)).const_mul _)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with t
    rw [aux_norm_gauss]
    have hre : ((α : ℂ)).re = α := Complex.ofReal_re α
    rw [hre]
    calc Real.exp (-(α * t ^ 2 + 2 * b.re * t))
        ≤ Real.exp (-α * t ^ 2 + (2 * ‖b‖) * |t|) := Real.exp_le_exp.mpr (hlin b t)
      _ ≤ Real.exp ((2 * ‖b‖) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * t ^ 2) :=
          aux_exp_lin_le hα t
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · filter_upwards with t b _
    exact aux_hasDerivAt_gauss_b (α : ℂ) t b
  · intro b₀ _
    set B : ℝ := ‖b₀‖ + 1 with hB
    have hBnn : (0 : ℝ) ≤ B := by positivity
    refine ⟨1, one_pos, fun t : ℝ =>
      (2 * (1 + 1 / (α / 4)) * Real.exp ((2 * B) ^ 2 / (2 * α))) * Real.exp (-(α / 4) * t ^ 2),
      (hgauss (α / 4) (by linarith)).const_mul _, ?_⟩
    filter_upwards with t b hb
    have hbn : ‖b‖ ≤ B := by
      have hd : ‖b - b₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hb
      calc ‖b‖ = ‖b₀ + (b - b₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖b₀‖ + ‖b - b₀‖ := norm_add_le _ _
        _ ≤ B := by rw [hB]; linarith
    rw [norm_mul, aux_norm_gauss, Complex.ofReal_re, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2]
    have hstep1 : Real.exp (-(α * t ^ 2 + 2 * b.re * t))
        ≤ Real.exp ((2 * B) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * t ^ 2) := by
      refine le_trans (Real.exp_le_exp.mpr (hlin b t)) ?_
      refine le_trans (aux_exp_lin_le hα t) ?_
      have hmono : Real.exp ((2 * ‖b‖) ^ 2 / (2 * α)) ≤ Real.exp ((2 * B) ^ 2 / (2 * α)) := by
        refine Real.exp_le_exp.mpr ?_
        have hnum : (2 * ‖b‖) ^ 2 ≤ (2 * B) ^ 2 := by nlinarith [norm_nonneg b, hbn, hBnn]
        have h2α : (0 : ℝ) < 2 * α := by linarith
        exact div_le_div_of_nonneg_right hnum h2α.le
      exact mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
    have hsplit : Real.exp (-(α / 2) * t ^ 2)
        = Real.exp (-(α / 4) * t ^ 2) * Real.exp (-(α / 4) * t ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have habs := aux_abs_mul_exp_le (γ := α / 4) (by linarith) t
    calc 2 * |t| * Real.exp (-(α * t ^ 2 + 2 * b.re * t))
        ≤ 2 * |t| * (Real.exp ((2 * B) ^ 2 / (2 * α)) * Real.exp (-(α / 2) * t ^ 2)) := by
          have h2 : (0 : ℝ) ≤ 2 * |t| := by positivity
          exact mul_le_mul_of_nonneg_left hstep1 h2
      _ = (2 * Real.exp ((2 * B) ^ 2 / (2 * α))) *
            ((|t| * Real.exp (-(α / 4) * t ^ 2)) * Real.exp (-(α / 4) * t ^ 2)) := by
          rw [hsplit]; ring
      _ ≤ (2 * Real.exp ((2 * B) ^ 2 / (2 * α))) *
            ((1 + 1 / (α / 4)) * Real.exp (-(α / 4) * t ^ 2)) := by
          have hh := mul_le_mul_of_nonneg_right habs (Real.exp_pos (-(α / 4) * t ^ 2)).le
          exact mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (2 * (1 + 1 / (α / 4)) * Real.exp ((2 * B) ^ 2 / (2 * α))) *
            Real.exp (-(α / 4) * t ^ 2) := by ring

-- no-dlmf: analyticity in the quadratic coefficient `a` of the 7.7.6 integral, support lemma
private lemma aux_analyticOnNhd_gauss_a (x : ℝ) (b : ℂ) :
    AnalyticOnNhd ℂ
      (fun a : ℂ => ∫ t in Ioi x, Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
      {a : ℂ | 0 < a.re} := by
  have hgauss : ∀ γ : ℝ, 0 < γ → IntegrableOn (fun t : ℝ => Real.exp (-γ * t ^ 2)) (Ioi x) :=
    fun γ hγ => (integrable_exp_neg_mul_sq hγ).integrableOn
  have hlin : ∀ (σ : ℝ) (a : ℂ), σ ≤ a.re → ∀ t : ℝ,
      -(a.re * t ^ 2 + 2 * b.re * t) ≤ -σ * t ^ 2 + (2 * ‖b‖) * |t| := by
    intro σ a hσa t
    have h1 : |b.re| ≤ ‖b‖ := Complex.abs_re_le_norm b
    have h2 : -(2 * b.re * t) ≤ 2 * ‖b‖ * |t| := by
      have h3 : |2 * b.re * t| ≤ 2 * ‖b‖ * |t| := by
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        nlinarith [h1, abs_nonneg b.re, abs_nonneg t]
      linarith [neg_abs_le (2 * b.re * t), le_abs_self (2 * b.re * t), h3]
    nlinarith [sq_nonneg t, hσa]
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_halfPlane (c := 0) (d := x)
    (f := fun a t => Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
    (f' := fun a t => -((t : ℂ) ^ 2) * Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))))
    (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Integrable.mono' (g := fun t : ℝ =>
      Real.exp ((2 * ‖b‖) ^ 2 / (2 * a.re)) * Real.exp (-(a.re / 2) * t ^ 2))
      ((hgauss (a.re / 2) (by linarith)).const_mul _)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with t
    rw [aux_norm_gauss]
    calc Real.exp (-(a.re * t ^ 2 + 2 * b.re * t))
        ≤ Real.exp (-a.re * t ^ 2 + (2 * ‖b‖) * |t|) :=
          Real.exp_le_exp.mpr (hlin a.re a le_rfl t)
      _ ≤ Real.exp ((2 * ‖b‖) ^ 2 / (2 * a.re)) * Real.exp (-(a.re / 2) * t ^ 2) :=
          aux_exp_lin_le ha t
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · filter_upwards with t a _
    exact aux_hasDerivAt_gauss_a b t a
  · intro σ hσ
    refine ⟨fun t : ℝ =>
      ((1 / (σ / 4)) * Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ))) * Real.exp (-(σ / 4) * t ^ 2),
      (hgauss (σ / 4) (by linarith)).const_mul _, ?_⟩
    filter_upwards with t a ha
    rw [norm_mul, aux_norm_gauss, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    have hstep1 : Real.exp (-(a.re * t ^ 2 + 2 * b.re * t))
        ≤ Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ)) * Real.exp (-(σ / 2) * t ^ 2) :=
      le_trans (Real.exp_le_exp.mpr (hlin σ a ha t)) (aux_exp_lin_le hσ t)
    have hsplit : Real.exp (-(σ / 2) * t ^ 2)
        = Real.exp (-(σ / 4) * t ^ 2) * Real.exp (-(σ / 4) * t ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hsq := aux_sq_mul_exp_le (γ := σ / 4) (by linarith) t
    calc t ^ 2 * Real.exp (-(a.re * t ^ 2 + 2 * b.re * t))
        ≤ t ^ 2 * (Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ)) * Real.exp (-(σ / 2) * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep1 (sq_nonneg t)
      _ = Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ)) *
            ((t ^ 2 * Real.exp (-(σ / 4) * t ^ 2)) * Real.exp (-(σ / 4) * t ^ 2)) := by
          rw [hsplit]; ring
      _ ≤ Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ)) *
            ((1 / (σ / 4)) * Real.exp (-(σ / 4) * t ^ 2)) := by
          have hh := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-(σ / 4) * t ^ 2)).le
          exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = ((1 / (σ / 4)) * Real.exp ((2 * ‖b‖) ^ 2 / (2 * σ))) * Real.exp (-(σ / 4) * t ^ 2) := by
          ring

-- no-dlmf: identity theorem transfer from the positive reals to all of `ℂ`
/-- **Identity theorem, entire form.**  Two entire functions that agree at every
positive real number agree everywhere: the reals `1/(n+1)` accumulate at `0`. -/
private lemma aux_eq_of_entire_of_real {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) : ∀ w : ℂ, F w = G w := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have hGa : AnalyticOnNhd ℂ G Set.univ := fun w _ => hG.analyticAt w
  have htendsto : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall (fun n => div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)))
  have hp : ∀ n : ℕ, F ((1 : ℂ) / ((n : ℂ) + 1)) = G ((1 : ℂ) / ((n : ℂ) + 1)) := by
    intro n
    have hcast : (1 : ℂ) / ((n : ℂ) + 1) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact hreal _ (by positivity)
  have hkey : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = G w :=
    htendsto.frequently (Eventually.frequently (Eventually.of_forall hp))
  have heq := AnalyticOnNhd.eq_of_frequently_eq hFa hGa hkey
  exact congrFun heq

/-! ### The sector `|ph z| ≤ π/4` (DLMF 7.7.1, 7.7.10, 7.7.11)

`|ph z| ≤ π/4` is the closed sector `|Im z| ≤ Re z`, whose interior is the open
sector `|Im z| < Re z` (a convex, hence preconnected, open set).  On the interior
`Re(z²) = (Re z)² - (Im z)² > 0`, which is what makes the parametric integrals of
7.7.1/7.7.10/7.7.11 analytic; on the closed sector `Re(z²) ≥ 0`, which is what
keeps the integrands dominated up to the boundary.  A boundary point is reached
from the interior along `z + 1/(n+1)`. -/

-- no-dlmf: sector bridge `|ph z| ≤ π/4 ⟹ |Im z| ≤ Re z`, support lemma
private lemma aux_abs_im_le_re_of_arg {z : ℂ} (hz : |Complex.arg z| ≤ Real.pi / 4) :
    |z.im| ≤ z.re := by
  rcases eq_or_ne z 0 with h0 | h0
  · simp [h0]
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr h0
  have hpi := Real.pi_pos
  set θ := Complex.arg z with hθ
  have hsin : Real.sin θ = z.im / ‖z‖ := Complex.sin_arg z
  have hcos : Real.cos θ = z.re / ‖z‖ := Complex.cos_arg h0
  have habs := abs_le.mp hz
  have hsinle : |Real.sin θ| ≤ Real.sin (Real.pi / 4) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := -(Real.pi / 4)) (y := θ)
        (by linarith) (by linarith) habs.1
      rw [Real.sin_neg] at h
      linarith
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (x := θ) (y := Real.pi / 4)
        (by linarith) (by linarith) habs.2
  have hcosge : Real.cos (Real.pi / 4) ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |θ|) (y := Real.pi / 4)
      (abs_nonneg θ) (by linarith) hz
    rwa [Real.cos_abs] at h
  rw [Real.sin_pi_div_four] at hsinle
  rw [Real.cos_pi_div_four] at hcosge
  have hkey : |z.im| / ‖z‖ ≤ z.re / ‖z‖ := by
    rw [← abs_of_pos hn, ← abs_div, abs_of_pos hn, ← hsin, ← hcos]
    linarith
  rwa [div_le_div_iff_of_pos_right hn] at hkey

-- no-dlmf: the open sector is open, support lemma
private lemma aux_openSector_isOpen : IsOpen {z : ℂ | |z.im| < z.re} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) Complex.continuous_re

-- no-dlmf: the open sector is convex, hence preconnected, support lemma
private lemma aux_openSector_isPreconnected : IsPreconnected {z : ℂ | |z.im| < z.re} := by
  refine Convex.isPreconnected ?_
  intro u hu v hv s t hs ht hst
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  have hre : (s • u + t • v).re = s * u.re + t * v.re := by
    simp [Complex.add_re]
  have him : (s • u + t • v).im = s * u.im + t * v.im := by
    simp [Complex.add_im]
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

-- no-dlmf: real part of a square, support lemma
private lemma aux_sq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
  simp [pow_two, Complex.mul_re]

-- no-dlmf: a ball inside the open sector with a uniform positive bound on `Re(z²)`
private lemma aux_openSector_ball {z₀ : ℂ} (h : |z₀.im| < z₀.re) :
    ∃ r > 0, ∃ δ > 0, ∀ z ∈ Metric.ball z₀ r,
      δ ≤ (z ^ 2).re ∧ ‖z‖ ≤ ‖z₀‖ + r := by
  set p := z₀.re with hp
  set q := |z₀.im| with hq
  have hq0 : (0 : ℝ) ≤ q := abs_nonneg _
  have hpq : q < p := h
  refine ⟨(p - q) / 4, by linarith, ((p - q) / 2) * (p + q), by nlinarith, ?_⟩
  intro z hzb
  have hd : ‖z - z₀‖ < (p - q) / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hzb
  have hre : |z.re - p| < (p - q) / 4 := by
    have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    simpa [Complex.sub_re] using lt_of_le_of_lt h2 hd
  have him : |z.im - z₀.im| < (p - q) / 4 := by
    have h2 : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
    simpa [Complex.sub_im] using lt_of_le_of_lt h2 hd
  have hre' : p - (p - q) / 4 < z.re := by linarith [(abs_lt.mp hre).1]
  have him' : |z.im| < q + (p - q) / 4 := by
    have h1 : |z.im| ≤ |z₀.im| + |z.im - z₀.im| := by
      calc |z.im| = |z₀.im + (z.im - z₀.im)| := by rw [add_sub_cancel]
        _ ≤ |z₀.im| + |z.im - z₀.im| := abs_add_le _ _
    linarith
  refine ⟨?_, ?_⟩
  · rw [aux_sq_re]
    have h1 : (p - (p - q) / 4) ^ 2 < z.re ^ 2 := by nlinarith
    have h2 : z.im ^ 2 < (q + (p - q) / 4) ^ 2 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
    nlinarith
  · calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + (p - q) / 4 := by linarith

-- no-dlmf: norm of the DLMF 7.7.1 integrand, support lemma
private lemma aux_norm_erf771 (u : ℂ) (t : ℝ) :
    ‖Complex.exp (-u ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)‖
      = Real.exp (-(u ^ 2).re * t ^ 2) / (t ^ 2 + 1) := by
  have hden : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  have hnum : -u ^ 2 * (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) * (-u ^ 2) := by push_cast; ring
  rw [norm_div, hden, hnum, Complex.norm_exp, Complex.re_ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2 + 1)]
  congr 1
  rw [Complex.neg_re]
  congr 1
  ring

-- no-dlmf: analyticity in `z` of the DLMF 7.7.1 integral on the open sector
private lemma aux_analyticOnNhd_erf771 :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
      {z : ℂ | |z.im| < z.re} := by
  have hbase : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hmeas : ∀ u : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-u ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro u
    refine (Continuous.aestronglyMeasurable ?_).restrict
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h]
      exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)
  have hmeas' : ∀ u : ℂ, AEStronglyMeasurable
      (fun t : ℝ => -2 * u * (t : ℂ) ^ 2 * Complex.exp (-u ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro u
    refine (Continuous.aestronglyMeasurable ?_).restrict
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h]
      exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun z t => Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
    (f' := fun z t => -2 * z * (t : ℂ) ^ 2 * Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
    aux_openSector_isOpen (fun z _ => hmeas z) (fun z hz => ?_) (fun z _ => hmeas' z) ?_ ?_
  · have hzs : (0 : ℝ) < (z ^ 2).re := by
      rw [aux_sq_re]
      have h : |z.im| < z.re := hz
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    refine Integrable.mono' hbase (hmeas z) ?_
    filter_upwards with t
    rw [aux_norm_erf771]
    have hexp : Real.exp (-(z ^ 2).re * t ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
    rw [add_comm (1 : ℝ) (t ^ 2), inv_eq_one_div]
    exact div_le_div_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ t ^ 2 + 1)
  · filter_upwards with t z _
    have hden : ((t : ℂ) ^ 2 + 1) ≠ 0 := by
      have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h]
      exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)
    have h1 : HasDerivAt (fun w : ℂ => -w ^ 2 * (t : ℂ) ^ 2) (-2 * z * (t : ℂ) ^ 2) z := by
      have h := ((hasDerivAt_pow 2 z).neg.mul_const ((t : ℂ) ^ 2))
      convert h using 1
      push_cast
      ring
    have h2 := (h1.cexp).div_const ((t : ℂ) ^ 2 + 1)
    convert h2 using 1
    field_simp
  · intro z₀ hz₀
    obtain ⟨r, hr, δ, hδ, hball⟩ := aux_openSector_ball hz₀
    refine ⟨r, hr, fun t : ℝ => (2 * (‖z₀‖ + r)) * Real.exp (-δ * t ^ 2),
      ((integrable_exp_neg_mul_sq hδ).integrableOn).const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hzb
    have ht0 : (0 : ℝ) < t := ht
    obtain ⟨hδz, hnz⟩ := hball z hzb
    have hnum : ‖-2 * z * (t : ℂ) ^ 2 * Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)‖
        = 2 * ‖z‖ * t ^ 2 * (Real.exp (-(z ^ 2).re * t ^ 2) / (t ^ 2 + 1)) := by
      have hsplit : -2 * z * (t : ℂ) ^ 2 * Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)
          = (-2 * z * (t : ℂ) ^ 2) *
              (Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) := by ring
      rw [hsplit, norm_mul, aux_norm_erf771]
      congr 1
      rw [norm_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      norm_num
    rw [hnum]
    have hfrac : Real.exp (-(z ^ 2).re * t ^ 2) / (t ^ 2 + 1) ≤ Real.exp (-δ * t ^ 2) / (t ^ 2 + 1) :=
      div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])) (by positivity)
    calc 2 * ‖z‖ * t ^ 2 * (Real.exp (-(z ^ 2).re * t ^ 2) / (t ^ 2 + 1))
        ≤ 2 * (‖z₀‖ + r) * t ^ 2 * (Real.exp (-δ * t ^ 2) / (t ^ 2 + 1)) := by
          have hnn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
          have h1 : 2 * ‖z‖ * t ^ 2 ≤ 2 * (‖z₀‖ + r) * t ^ 2 := by nlinarith [norm_nonneg z]
          have h2 : (0 : ℝ) ≤ Real.exp (-(z ^ 2).re * t ^ 2) / (t ^ 2 + 1) := by positivity
          have h3 : (0 : ℝ) ≤ 2 * (‖z₀‖ + r) * t ^ 2 := by
            have := norm_nonneg z₀; nlinarith
          exact le_trans (mul_le_mul_of_nonneg_left hfrac (by nlinarith [norm_nonneg z]))
            (mul_le_mul_of_nonneg_right h1 (by positivity))
      _ ≤ (2 * (‖z₀‖ + r)) * Real.exp (-δ * t ^ 2) := by
          have hfr : t ^ 2 * (Real.exp (-δ * t ^ 2) / (t ^ 2 + 1)) ≤ Real.exp (-δ * t ^ 2) := by
            rw [mul_div_assoc'] at *
            rw [div_le_iff₀ (by positivity)]
            nlinarith [Real.exp_pos (-δ * t ^ 2), sq_nonneg t]
          have hc : (0 : ℝ) ≤ 2 * (‖z₀‖ + r) := by have := norm_nonneg z₀; linarith
          calc 2 * (‖z₀‖ + r) * t ^ 2 * (Real.exp (-δ * t ^ 2) / (t ^ 2 + 1))
              = (2 * (‖z₀‖ + r)) * (t ^ 2 * (Real.exp (-δ * t ^ 2) / (t ^ 2 + 1))) := by ring
            _ ≤ (2 * (‖z₀‖ + r)) * Real.exp (-δ * t ^ 2) := mul_le_mul_of_nonneg_left hfr hc

-- no-dlmf: real/narrowed restriction of DLMF 7.7.1 (DLMF states this for
-- complex z with |ph z| ≤ π/4); faithful surface is erf_7_7_1_dlmf
/-- Complementary error function as a half-line integral representation,
real specialization: for real `x ≥ 0`,
`erfc x = (2/π) e^{-x²} ∫₀^∞ e^{-x² t²}/(t²+1) dt`.
-/
theorem erf_7_7_1 {x : ℝ} (hx : 0 ≤ x) :
    erfc x =
      (2 / Real.pi) * Real.exp (-x ^ 2) *
        ∫ t in Ioi (0 : ℝ), Real.exp (-x ^ 2 * t ^ 2) / (t ^ 2 + 1) := by
  have hbase : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hInt : ∀ z : ℝ, IntegrableOn
      (fun t : ℝ => Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1)) (Ioi 0) := by
    intro z
    apply Integrable.mono' hbase
    · apply Continuous.aestronglyMeasurable
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t; positivity
    · refine MeasureTheory.ae_of_all _ (fun t => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _),
        abs_of_pos (by positivity : (0:ℝ) < t ^ 2 + 1), add_comm (1:ℝ) (t ^ 2), inv_eq_one_div]
      gcongr
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z, sq_nonneg t])
  have hgauss : ∀ z : ℝ, 0 < z →
      (∫ t in Ioi (0:ℝ), Real.exp (-z ^ 2 * t ^ 2)) = Real.sqrt Real.pi / (2 * z) := by
    intro z hz
    have himg : (fun s => z * s) '' Ioi 0 = Ioi (0:ℝ) := by
      ext u
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨s, hs, rfl⟩; positivity
      · intro hu; exact ⟨u / z, by positivity, by field_simp⟩
    have hderiv : ∀ s ∈ Ioi (0:ℝ), HasDerivWithinAt (fun s => z * s) z (Ioi 0) s := by
      intro s _
      simpa using ((hasDerivAt_id s).const_mul z).hasDerivWithinAt
    have hinj : InjOn (fun s => z * s) (Ioi 0) := by
      intro p _ q _ hpq; exact mul_left_cancel₀ (ne_of_gt hz) hpq
    have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
      (fun u => Real.exp (-u ^ 2))
    rw [himg] at hcov
    have hpt : ∀ s ∈ Ioi (0:ℝ), |z| • Real.exp (-(z * s) ^ 2) = z * Real.exp (-z ^ 2 * s ^ 2) := by
      intro s _
      have heq : Real.exp (-(z * s) ^ 2) = Real.exp (-z ^ 2 * s ^ 2) := by congr 1; ring
      rw [abs_of_pos hz, smul_eq_mul, heq]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_Ioi_gaussian] at hcov
    rw [eq_comm] at hcov
    rw [eq_div_iff (by positivity : (2:ℝ) * z ≠ 0)]
    linarith [hcov]
  have hderivI : ∀ z₀ : ℝ, 0 < z₀ →
      HasDerivAt (fun z => ∫ t in Ioi (0:ℝ), Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1))
        (-Real.sqrt Real.pi * Real.exp (-z₀ ^ 2)) z₀ := by
    intro z₀ hz₀
    have hz0ne : z₀ ≠ 0 := ne_of_gt hz₀
    set b : ℝ := (z₀ / 2) ^ 2 with hb
    have hbpos : 0 < b := by positivity
    have hboundInt : IntegrableOn
        (fun t : ℝ => (3 * z₀ * Real.exp (-b)) * Real.exp (-b * t ^ 2)) (Ioi 0) :=
      ((integrable_exp_neg_mul_sq hbpos).const_mul (3 * z₀ * Real.exp (-b))).integrableOn
    have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
        (fun t : ℝ => Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1)) (volume.restrict (Ioi 0)) := by
      refine Filter.Eventually.of_forall (fun z => ?_)
      apply Continuous.aestronglyMeasurable
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t; positivity
    have hf'meas : AEStronglyMeasurable
        (fun t : ℝ => -(2 * z₀) * Real.exp (-z₀ ^ 2 * (t ^ 2 + 1))) (volume.restrict (Ioi 0)) := by
      apply Continuous.aestronglyMeasurable; fun_prop
    have hbound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball z₀ (z₀ / 2),
        ‖-(2 * z) * Real.exp (-z ^ 2 * (t ^ 2 + 1))‖
          ≤ (3 * z₀ * Real.exp (-b)) * Real.exp (-b * t ^ 2) := by
      refine MeasureTheory.ae_of_all _ (fun t x hx => ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
      have hxgt : z₀ / 2 < x := by linarith [hx.1]
      have hxlt : x < 3 * z₀ / 2 := by linarith [hx.2]
      have hxpos : 0 < x := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_two, abs_of_pos hxpos,
        abs_of_pos (Real.exp_pos _)]
      have hble : b ≤ x ^ 2 := by rw [hb]; nlinarith [hxgt, hxpos]
      have hexple : Real.exp (-x ^ 2 * (t ^ 2 + 1)) ≤ Real.exp (-b * (t ^ 2 + 1)) := by
        apply Real.exp_le_exp.mpr; nlinarith [hble, sq_nonneg t]
      have hfac : Real.exp (-b * (t ^ 2 + 1)) = Real.exp (-b) * Real.exp (-b * t ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      calc 2 * x * Real.exp (-x ^ 2 * (t ^ 2 + 1))
          ≤ 2 * x * Real.exp (-b * (t ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hexple (by positivity)
        _ = 2 * x * Real.exp (-b) * Real.exp (-b * t ^ 2) := by rw [hfac]; ring
        _ ≤ 3 * z₀ * Real.exp (-b) * Real.exp (-b * t ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            linarith
    have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball z₀ (z₀ / 2),
        HasDerivAt (fun z => Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1))
          (-(2 * z) * Real.exp (-z ^ 2 * (t ^ 2 + 1))) z := by
      refine MeasureTheory.ae_of_all _ (fun t x _ => ?_)
      have hp : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).neg
      have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) * (t ^ 2 + 1)) (-(2 * x) * (t ^ 2 + 1)) x :=
        hp.mul_const (t ^ 2 + 1)
      have h3 := (h1.exp).div_const (t ^ 2 + 1)
      have hc : (t ^ 2 + 1) ≠ 0 := by positivity
      convert h3 using 1
      field_simp
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z t : ℝ => Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1))
      (F' := fun z t : ℝ => -(2 * z) * Real.exp (-z ^ 2 * (t ^ 2 + 1)))
      (bound := fun t : ℝ => (3 * z₀ * Real.exp (-b)) * Real.exp (-b * t ^ 2))
      (μ := volume.restrict (Ioi (0:ℝ)))
      (Metric.ball_mem_nhds z₀ (by positivity)) hmeas (hInt z₀) hf'meas hbound hboundInt hdiff
    have hval : (∫ t in Ioi (0:ℝ), -(2 * z₀) * Real.exp (-z₀ ^ 2 * (t ^ 2 + 1)))
        = -Real.sqrt Real.pi * Real.exp (-z₀ ^ 2) := by
      have hstep : (∫ t in Ioi (0:ℝ), -(2 * z₀) * Real.exp (-z₀ ^ 2 * (t ^ 2 + 1)))
          = ∫ t in Ioi (0:ℝ), (-(2 * z₀) * Real.exp (-z₀ ^ 2)) * Real.exp (-z₀ ^ 2 * t ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        simp only []
        have hh : Real.exp (-z₀ ^ 2 * (t ^ 2 + 1))
            = Real.exp (-z₀ ^ 2) * Real.exp (-z₀ ^ 2 * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hh]; ring
      rw [hstep, integral_const_mul, hgauss z₀ hz₀]
      field_simp
    have hd := hmain.2
    rw [hval] at hd
    exact hd
  have hderivErfc : ∀ z : ℝ,
      HasDerivAt erfc (-(2 / Real.sqrt Real.pi) * Real.exp (-z ^ 2)) z := by
    intro z
    have h := (hasDerivAt_erf z).const_sub 1
    simpa [erfc] using h
  set I : ℝ → ℝ := fun z => ∫ t in Ioi (0:ℝ), Real.exp (-z ^ 2 * (t ^ 2 + 1)) / (t ^ 2 + 1)
    with hIdef
  set G : ℝ → ℝ := fun z => I z - (Real.pi / 2) * erfc z with hGdef
  have hE : ∀ z : ℝ,
      HasDerivAt (fun z => (Real.pi / 2) * erfc z)
        (-Real.sqrt Real.pi * Real.exp (-z ^ 2)) z := by
    intro z
    have h0 := (hderivErfc z).const_mul (Real.pi / 2)
    convert h0 using 1
    rw [show Real.pi / 2 * (-(2 / Real.sqrt Real.pi) * Real.exp (-z ^ 2))
        = -(Real.pi / Real.sqrt Real.pi) * Real.exp (-z ^ 2) by ring, Real.div_sqrt]
  have hGderiv : ∀ z ∈ Ioi (0:ℝ), HasDerivAt G 0 z := by
    intro z hz
    have hsub := (hderivI z hz).sub (hE z)
    convert hsub using 1
    ring
  have hdiffOn : DifferentiableOn ℝ G (Ioi 0) :=
    fun z hz => (hGderiv z hz).differentiableAt.differentiableWithinAt
  have hfd : ∀ z ∈ Ioi (0:ℝ), fderivWithin ℝ G (Ioi 0) z = 0 := by
    intro z hz
    rw [fderivWithin_of_isOpen isOpen_Ioi hz, (hGderiv z hz).hasFDerivAt.fderiv]
    simp
  have hconstG : ∀ p ∈ Ioi (0:ℝ), ∀ q ∈ Ioi (0:ℝ), G p = G q :=
    fun p hp q hq => (convex_Ioi 0).is_const_of_fderivWithin_eq_zero hdiffOn hfd hp hq
  have hI_nonneg : ∀ z, 0 ≤ I z := by
    intro z
    apply setIntegral_nonneg measurableSet_Ioi
    intro t _; positivity
  have hI_le : ∀ z, I z ≤ (Real.pi / 2) * Real.exp (-z ^ 2) := by
    intro z
    have hRHS_int : IntegrableOn (fun t : ℝ => Real.exp (-z ^ 2) * (1 + t ^ 2)⁻¹) (Ioi 0) :=
      hbase.const_mul _
    have hle : I z ≤ ∫ t in Ioi (0:ℝ), Real.exp (-z ^ 2) * (1 + t ^ 2)⁻¹ := by
      rw [hIdef]
      apply setIntegral_mono_on (hInt z) hRHS_int measurableSet_Ioi
      intro t _
      have hrw : Real.exp (-z ^ 2) * (1 + t ^ 2)⁻¹ = Real.exp (-z ^ 2) / (t ^ 2 + 1) := by
        rw [add_comm (1:ℝ) (t ^ 2)]; ring
      have hexp : Real.exp (-z ^ 2 * (t ^ 2 + 1)) ≤ Real.exp (-z ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sq_nonneg z) (sq_nonneg t)])
      rw [hrw, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hexp (by positivity)
    have hval2 : (∫ t in Ioi (0:ℝ), Real.exp (-z ^ 2) * (1 + t ^ 2)⁻¹)
        = Real.exp (-z ^ 2) * (Real.pi / 2) := by
      rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
    rw [hval2, mul_comm] at hle
    exact hle
  have hgtend : Tendsto (fun z : ℝ => (Real.pi / 2) * Real.exp (-z ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => -z ^ 2) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (two_ne_zero))
    have h2 : Tendsto (fun z : ℝ => Real.exp (-z ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (Real.pi / 2)
  have hItend : Tendsto I atTop (𝓝 0) := squeeze_zero hI_nonneg hI_le hgtend
  have hmainId : ∀ y : ℝ, 0 ≤ y → I y = (Real.pi / 2) * erfc y := by
    intro y hy
    rcases eq_or_lt_of_le hy with h0 | hpos
    · rw [← h0]
      have hI0 : I 0 = Real.pi / 2 := by
        have hcong : I 0 = ∫ t in Ioi (0:ℝ), (1 + t ^ 2)⁻¹ := by
          rw [hIdef]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          simp only []
          rw [show (-(0:ℝ) ^ 2 * (t ^ 2 + 1)) = 0 by ring, Real.exp_zero, one_div,
            add_comm (t ^ 2) 1]
        rw [hcong, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
      rw [hI0, erfc_zero]; ring
    · have hGy0 : G y = 0 := by
        have hev : (fun q => G q) =ᶠ[atTop] fun _ => G y := by
          filter_upwards [eventually_gt_atTop 0] with q hq
          exact hconstG q hq y hpos
        have htend1 : Tendsto G atTop (𝓝 (G y)) := tendsto_const_nhds.congr' hev.symm
        have htend2 : Tendsto G atTop (𝓝 0) := by
          have hs := hItend.sub ((erfc_tendsto_zero).const_mul (Real.pi / 2))
          rw [show (0:ℝ) - Real.pi / 2 * 0 = 0 by ring] at hs
          exact hs
        exact tendsto_nhds_unique htend1 htend2
      have hGe : G y = I y - (Real.pi / 2) * erfc y := rfl
      rw [hGe] at hGy0
      linarith
  have hIP : I x = Real.exp (-x ^ 2) *
      (∫ t in Ioi (0:ℝ), Real.exp (-x ^ 2 * t ^ 2) / (t ^ 2 + 1)) := by
    rw [hIdef]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only []
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring
  have key := hmainId x hx
  rw [hIP] at key
  rw [mul_assoc, key]
  field_simp

/-- **DLMF 7.7.1**: `erfc z = (2/π) e^{-z²} ∫₀^∞ e^{-z² t²}/(t²+1) dt`, for complex
`z` with `|ph z| ≤ π/4`.

DAG: E-7.7.1.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_1_dlmf {z : ℂ} (hz : |Complex.arg z| ≤ Real.pi / 4) :
    cerfc z =
      (2 / (Real.pi : ℂ)) * Complex.exp (-z ^ 2) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1) := by
  -- `|ph z| ≤ π/4` is the closed sector `|Im z| ≤ Re z`.  On its (convex, open)
  -- interior the identity theorem transfers the real specialization `erf_7_7_1`;
  -- a boundary point is then reached along `z + 1/(n+1)` by dominated convergence
  -- (the dominant `1/(t²+1)` is valid on the whole closed sector).
  have hS : |z.im| ≤ z.re := aux_abs_im_le_re_of_arg hz
  have hbase : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hmeas : ∀ u : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-u ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro u
    refine (Continuous.aestronglyMeasurable ?_).restrict
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h]
      exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)
  -- the open-sector identity
  have hopen : ∀ w : ℂ, |w.im| < w.re →
      cerfc w = (2 / (Real.pi : ℂ)) * Complex.exp (-w ^ 2) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-w ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1) := by
    have hRHS : AnalyticOnNhd ℂ
        (fun w : ℂ => (2 / (Real.pi : ℂ)) * Complex.exp (-w ^ 2) *
          ∫ t in Ioi (0 : ℝ), Complex.exp (-w ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
        {w : ℂ | |w.im| < w.re} := by
      have hpre : AnalyticOnNhd ℂ
          (fun w : ℂ => (2 / (Real.pi : ℂ)) * Complex.exp (-w ^ 2)) {w : ℂ | |w.im| < w.re} := by
        have hd : Differentiable ℂ (fun w : ℂ => (2 / (Real.pi : ℂ)) * Complex.exp (-w ^ 2)) := by
          fun_prop
        exact fun w _ => hd.analyticAt w
      exact hpre.mul aux_analyticOnNhd_erf771
    refine aux_eq_of_analytic_of_real aux_openSector_isPreconnected (by simp)
      (fun w _ => aux_differentiable_cerfc.analyticAt w) hRHS ?_
    intro x hx
    have hI : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
        = (((∫ t in Ioi (0 : ℝ), Real.exp (-x ^ 2 * t ^ 2) / (t ^ 2 + 1)) : ℝ) : ℂ) := by
      have hcong : (∫ t in Ioi (0 : ℝ),
            Complex.exp (-(x : ℂ) ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
          = ∫ t in Ioi (0 : ℝ), (((Real.exp (-x ^ 2 * t ^ 2) / (t ^ 2 + 1)) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        push_cast
        ring
      rw [hcong]
      exact _root_.integral_complex_ofReal
    rw [cerfc_ofReal, hI, erf_7_7_1 hx.le]
    push_cast
    ring
  rcases lt_or_eq_of_le hS with hlt | heq
  · exact hopen z hlt
  -- boundary of the sector: approach along `z + 1/(n+1)`
  set w : ℕ → ℂ := fun n => z + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) with hwdef
  have hwre : ∀ n : ℕ, (w n).re = z.re + 1 / ((n : ℝ) + 1) := by
    intro n; simp only [hwdef, Complex.add_re, Complex.ofReal_re]
  have hwim : ∀ n : ℕ, (w n).im = z.im := by
    intro n; simp only [hwdef, Complex.add_im, Complex.ofReal_im, add_zero]
  have hwmem : ∀ n : ℕ, |(w n).im| < (w n).re := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [hwim, hwre]
    linarith [hS]
  have hwt : Tendsto w atTop (𝓝 z) := by
    have h : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def] using h2
    simpa [hwdef] using h.const_add z
  -- the left-hand side is continuous
  have hlhs : Tendsto (fun n : ℕ => cerfc (w n)) atTop (𝓝 (cerfc z)) :=
    (aux_differentiable_cerfc.continuous.tendsto z).comp hwt
  -- the integral converges by dominated convergence, with dominant `1/(1+t²)`
  have hInt : Tendsto
      (fun n : ℕ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(w n) ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun t : ℝ => (1 + t ^ 2)⁻¹) (fun n => hmeas (w n)) hbase (fun n => ?_) ?_
    · filter_upwards with t
      have hzs : (0 : ℝ) ≤ ((w n) ^ 2).re := by
        rw [aux_sq_re]
        have h := hwmem n
        nlinarith [abs_nonneg (w n).im, sq_abs (w n).im]
      rw [aux_norm_erf771]
      have hexp : Real.exp (-((w n) ^ 2).re * t ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t]
      rw [add_comm (1 : ℝ) (t ^ 2), inv_eq_one_div]
      exact div_le_div_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ t ^ 2 + 1)
    · filter_upwards with t
      have hden : ((t : ℂ) ^ 2 + 1) ≠ 0 := by
        have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h]
        exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)
      have hc : Continuous
          (fun u : ℂ => Complex.exp (-u ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) := by
        fun_prop
      exact (hc.tendsto z).comp hwt
  have hrhs : Tendsto
      (fun n : ℕ => (2 / (Real.pi : ℂ)) * Complex.exp (-(w n) ^ 2) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(w n) ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) atTop
      (𝓝 ((2 / (Real.pi : ℂ)) * Complex.exp (-z ^ 2) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-z ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))) := by
    have hexpc : Tendsto (fun n : ℕ => (2 / (Real.pi : ℂ)) * Complex.exp (-(w n) ^ 2)) atTop
        (𝓝 ((2 / (Real.pi : ℂ)) * Complex.exp (-z ^ 2))) := by
      have hc : Continuous (fun u : ℂ => (2 / (Real.pi : ℂ)) * Complex.exp (-u ^ 2)) := by fun_prop
      exact (hc.tendsto z).comp hwt
    exact hexpc.mul hInt
  have hcongr : (fun n : ℕ => cerfc (w n))
      = fun n : ℕ => (2 / (Real.pi : ℂ)) * Complex.exp (-(w n) ^ 2) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(w n) ^ 2 * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1) := by
    funext n
    exact hopen (w n) (hwmem n)
  rw [hcongr] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

-- DLMF 7.7.2 (RESOLVED in Error/Faddeeva.lean as `erf_7_7_2`, via the complex Faddeeva keystone).
-- DLMF 7.7.2: `w(z) = (1/(πi)) ∫_{-∞}^{∞} e^{-t²}/(t-z) dt`, Im z > 0.
--   Needs the complex Faddeeva function `w(z)` and a complex contour integral;
--   FLMF has no `w(z)`. No honest real specialization exists. Deferred.

-- DLMF 7.7.3 (deferred): defines `∫₀^∞ e^{-a t²} cos(2 z t) dt` etc. for complex
--   `a` with Re a > 0 (Gaussian–cosine transform). The clean form needs complex
--   `a`/`z`; the real-`a` Gaussian cosine transform is upstream Mathlib material,
--   not a §7.7 erf identity per se. Deferred as a complex/parametric statement.

-- no-dlmf: real/narrowed restriction of DLMF 7.7.4 (DLMF states this for
-- complex a, z with Re a > 0, Re z > 0); faithful surface is erf_7_7_4_dlmf
/-- Half-line integral evaluated by the complementary error function,
real specialization: for `a > 0`, `x > 0`,
`∫₀^∞ e^{-a t}/√(t + x²) dt = √(π/a)·e^{a x²}·erfc(√a·x)`.
(Corrected 2026-06-24 from the DLMF PDF — the integrand denominator is `√(t+x²)`,
not `t+x²`, and the prefactor is `√(π/a)`, not `√(πa)`; see docs/ERRATA.md.)
-/
theorem erf_7_7_4 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) / Real.sqrt (t + x ^ 2)) =
      Real.sqrt (Real.pi / a) * Real.exp (a * x ^ 2) * erfc (Real.sqrt a * x) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsqrt_ne : Real.sqrt a ≠ 0 := ne_of_gt hsa
  have hgi : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
    have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
    simpa [one_mul] using this
  have hpia : Real.sqrt (Real.pi / a) = Real.sqrt Real.pi / Real.sqrt a := by
    rw [Real.sqrt_div Real.pi_pos.le]
  have htail : ∀ y : ℝ, 0 < y →
      (∫ s in Ioi y, Real.exp (-s ^ 2)) = Real.sqrt Real.pi / 2 * erfc y := by
    intro y hy
    have hsplit : (∫ s in Ioi (0 : ℝ), Real.exp (-s ^ 2))
        = (∫ s in Ioc 0 y, Real.exp (-s ^ 2)) + ∫ s in Ioi y, Real.exp (-s ^ 2) := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hgi.integrableOn hgi.integrableOn, Ioc_union_Ioi_eq_Ioi hy.le]
    have hocx : (∫ s in Ioc 0 y, Real.exp (-s ^ 2)) = ∫ s in (0 : ℝ)..y, Real.exp (-s ^ 2) := by
      rw [intervalIntegral.integral_of_le hy.le]
    have hIoiy : (∫ s in Ioi y, Real.exp (-s ^ 2))
        = Real.sqrt Real.pi / 2 - ∫ s in (0 : ℝ)..y, Real.exp (-s ^ 2) := by
      have := hsplit
      rw [integral_Ioi_gaussian, hocx] at this
      linarith
    rw [hIoiy, erfc, erf]
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
  have hscaled : (∫ s in Ioi x, Real.exp (-a * s ^ 2))
      = Real.sqrt (Real.pi / a) / 2 * erfc (Real.sqrt a * x) := by
    have himg : (fun s => Real.sqrt a * s) '' Ioi x = Ioi (Real.sqrt a * x) := by
      ext u
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨s, hs, rfl⟩; exact mul_lt_mul_of_pos_left hs hsa
      · intro hu
        exact ⟨u / Real.sqrt a, by rw [lt_div_iff₀ hsa, mul_comm]; exact hu, by field_simp⟩
    have hderiv : ∀ s ∈ Ioi x,
        HasDerivWithinAt (fun s => Real.sqrt a * s) (Real.sqrt a) (Ioi x) s := by
      intro s _
      simpa using ((hasDerivAt_id s).const_mul (Real.sqrt a)).hasDerivWithinAt
    have hinj : InjOn (fun s => Real.sqrt a * s) (Ioi x) := by
      intro p _ q _ hpq
      exact mul_left_cancel₀ hsqrt_ne hpq
    have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
      (fun u => Real.exp (-u ^ 2))
    rw [himg] at hcov
    have hpt : ∀ s ∈ Ioi x, |Real.sqrt a| • Real.exp (-(Real.sqrt a * s) ^ 2)
        = Real.sqrt a * Real.exp (-a * s ^ 2) := by
      intro s _
      have heq : Real.exp (-(Real.sqrt a * s) ^ 2) = Real.exp (-a * s ^ 2) := by
        congr 1
        rw [mul_pow, Real.sq_sqrt ha.le]; ring
      rw [abs_of_pos hsa, smul_eq_mul, heq]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hcov
    rw [htail (Real.sqrt a * x) (by positivity)] at hcov
    have hgoal : (∫ s in Ioi x, Real.exp (-a * s ^ 2))
        = Real.sqrt Real.pi / 2 * erfc (Real.sqrt a * x) / Real.sqrt a := by
      rw [eq_div_iff hsqrt_ne, mul_comm]
      exact hcov.symm
    rw [hgoal, hpia]
    field_simp
  have himg2 : (fun s => s ^ 2 - x ^ 2) '' Ioi x = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩; nlinarith [hs, hx]
    · intro ht
      refine ⟨Real.sqrt (t + x ^ 2), ?_, ?_⟩
      · calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx.le).symm
          _ < Real.sqrt (t + x ^ 2) := Real.sqrt_lt_sqrt (by positivity) (by linarith)
      · rw [Real.sq_sqrt (by positivity)]; ring
  have hderiv2 : ∀ s ∈ Ioi x, HasDerivWithinAt (fun s => s ^ 2 - x ^ 2) (2 * s) (Ioi x) s := by
    intro s _
    have : HasDerivAt (fun s : ℝ => s ^ 2 - x ^ 2) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).sub_const (x ^ 2)
    exact this.hasDerivWithinAt
  have hinj2 : InjOn (fun s => s ^ 2 - x ^ 2) (Ioi x) := by
    intro p hp q hq hpq
    simp only [mem_Ioi] at hp hq
    have hpp : 0 < p := lt_trans hx hp
    have hqq : 0 < q := lt_trans hx hq
    nlinarith [hpq, hpp, hqq]
  have hcov2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv2 hinj2
    (fun t => Real.exp (-a * t) / Real.sqrt (t + x ^ 2))
  rw [himg2] at hcov2
  have hpt2 : ∀ s ∈ Ioi x,
      |2 * s| • (Real.exp (-a * (s ^ 2 - x ^ 2)) / Real.sqrt (s ^ 2 - x ^ 2 + x ^ 2))
        = 2 * Real.exp (a * x ^ 2) * Real.exp (-a * s ^ 2) := by
    intro s hs
    simp only [mem_Ioi] at hs
    have hspos : 0 < s := lt_trans hx hs
    have hs0 : s ≠ 0 := ne_of_gt hspos
    have hsimp : s ^ 2 - x ^ 2 + x ^ 2 = s ^ 2 := by ring
    have hexp : Real.exp (-a * (s ^ 2 - x ^ 2)) = Real.exp (a * x ^ 2) * Real.exp (-a * s ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsimp, Real.sqrt_sq hspos.le, abs_of_pos (by positivity : (0:ℝ) < 2 * s),
      smul_eq_mul, hexp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt2] at hcov2
  rw [hcov2]
  have hfactor : (fun s => 2 * Real.exp (a * x ^ 2) * Real.exp (-a * s ^ 2))
      = fun s => (2 * Real.exp (a * x ^ 2)) * Real.exp (-a * s ^ 2) := by
    ext s; ring
  rw [hfactor, integral_const_mul, hscaled]
  ring

/-- **DLMF 7.7.4**: `∫₀^∞ e^{-a t}/√(t + z²) dt = √(π/a)·e^{a z²}·erfc(√a·z)`,
for complex `a`, `z` with `Re a > 0`, `Re z > 0` (principal branches of `√·`).

DAG: E-7.7.4.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_4_dlmf {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) / ((t : ℂ) + z ^ 2) ^ ((1 : ℂ) / 2)) =
      ((Real.pi : ℂ) / a) ^ ((1 : ℂ) / 2) * Complex.exp (a * z ^ 2) *
        cerfc (a ^ ((1 : ℂ) / 2) * z) := by
  -- Two applications of the identity theorem: first continue in `a` at a fixed
  -- positive real `z = x`, then continue in `z` at the resulting complex `a`.
  have hdiv : ∀ b w : ℂ,
      (∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t : ℂ)) / ((t : ℂ) + w ^ 2) ^ ((1 : ℂ) / 2))
        = ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t : ℂ)) * ((t : ℂ) + w ^ 2) ^ (-((1 : ℂ) / 2)) := by
    intro b w
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [Complex.cpow_neg, div_eq_mul_inv]
  -- the right-hand side is analytic in the parameter `b` on the right half-plane
  have hGb : ∀ x : ℝ, AnalyticOnNhd ℂ
      (fun b : ℂ => ((Real.pi : ℂ) / b) ^ ((1 : ℂ) / 2) * Complex.exp (b * (x : ℂ) ^ 2)
        * cerfc (b ^ ((1 : ℂ) / 2) * (x : ℂ))) {b : ℂ | 0 < b.re} := by
    intro x
    have hUopen : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hUopen
    have hbre : (0 : ℝ) < b.re := hb
    have hbne : b ≠ 0 := by intro h; rw [h] at hbre; simp at hbre
    have hslitb : b ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hbre)
    have hnsq : 0 < Complex.normSq b := Complex.normSq_pos.mpr hbne
    have hslitpi : ((Real.pi : ℂ) / b) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
      exact div_pos (mul_pos Real.pi_pos hbre) hnsq
    have d1 : DifferentiableAt ℂ (fun w : ℂ => ((Real.pi : ℂ) / w) ^ ((1 : ℂ) / 2)) b :=
      DifferentiableAt.cpow_const
        ((differentiableAt_const _).div differentiableAt_id hbne) hslitpi
    have d2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w * (x : ℂ) ^ 2)) b := by fun_prop
    have d3 : DifferentiableAt ℂ (fun w : ℂ => cerfc (w ^ ((1 : ℂ) / 2) * (x : ℂ))) b := by
      have hinner : DifferentiableAt ℂ (fun w : ℂ => w ^ ((1 : ℂ) / 2) * (x : ℂ)) b :=
        (DifferentiableAt.cpow_const differentiableAt_id hslitb).mul_const (x : ℂ)
      exact (aux_differentiable_cerfc _).comp b hinner
    exact ((d1.mul d2).mul d3).differentiableWithinAt
  -- Step 1: continue in `a`, at a fixed positive real second parameter.
  have step1 : ∀ x : ℝ, 0 < x → ∀ b : ℂ, 0 < b.re →
      (∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t : ℂ)) * ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)))
        = ((Real.pi : ℂ) / b) ^ ((1 : ℂ) / 2) * Complex.exp (b * (x : ℂ) ^ 2)
          * cerfc (b ^ ((1 : ℂ) / 2) * (x : ℂ)) := by
    intro x hx
    have hxpos : ∀ t : ℝ, (0 : ℝ) < |t| + x ^ 2 :=
      fun t => add_pos_of_nonneg_of_pos (abs_nonneg t) (pow_pos hx 2)
    have hker : ∀ t : ℝ, 0 < t →
        ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)) = (((Real.sqrt (t + x ^ 2))⁻¹ : ℝ) : ℂ) := by
      intro t ht
      have h1 : ((t : ℂ) + (x : ℂ) ^ 2) = (((t + x ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [h1, aux_cpow_neg_half_ofReal (add_pos_of_pos_of_nonneg ht (sq_nonneg x)).le]
    have hχc : Continuous (fun t : ℝ => (((Real.sqrt (|t| + x ^ 2))⁻¹ : ℝ) : ℂ)) := by
      have h1 : Continuous (fun t : ℝ => Real.sqrt (|t| + x ^ 2)) := by fun_prop
      have h2 : ∀ t : ℝ, Real.sqrt (|t| + x ^ 2) ≠ 0 :=
        fun t => ne_of_gt (Real.sqrt_pos.mpr (hxpos t))
      exact Complex.continuous_ofReal.comp (h1.inv₀ h2)
    have hχb : ∀ t : ℝ, ‖(((Real.sqrt (|t| + x ^ 2))⁻¹ : ℝ) : ℂ)‖ ≤ x⁻¹ := by
      intro t
      have hs0 : (0 : ℝ) < Real.sqrt (|t| + x ^ 2) := Real.sqrt_pos.mpr (hxpos t)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (by positivity))]
      have hs : x ≤ Real.sqrt (|t| + x ^ 2) := by
        have h := Real.sqrt_le_sqrt
          (show x ^ 2 ≤ |t| + x ^ 2 by linarith [abs_nonneg t])
        rwa [Real.sqrt_sq hx.le] at h
      exact inv_anti₀ hx hs
    have hFeq : (fun b : ℂ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-b * (t : ℂ)) * ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)))
        = fun b : ℂ => ∫ t in Ioi (0 : ℝ),
            Complex.exp (-b * (t : ℂ)) * (((Real.sqrt (|t| + x ^ 2))⁻¹ : ℝ) : ℂ) := by
      funext b
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := ht
      rw [hker t ht0, abs_of_pos ht0]
    refine aux_eq_of_analytic_rightHalfPlane
      (F := fun b : ℂ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-b * (t : ℂ)) * ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)))
      (G := fun b : ℂ => ((Real.pi : ℂ) / b) ^ ((1 : ℂ) / 2) * Complex.exp (b * (x : ℂ) ^ 2)
        * cerfc (b ^ ((1 : ℂ) / 2) * (x : ℂ)))
      ?_ (hGb x) ?_
    · rw [hFeq]
      exact aux_analyticOnNhd_laplace (M := x⁻¹) hχc hχb
    · intro s hs
      dsimp only
      have hL : (∫ t in Ioi (0 : ℝ),
          Complex.exp (-(s : ℂ) * (t : ℂ)) * ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)))
          = (((∫ t in Ioi (0 : ℝ), Real.exp (-s * t) / Real.sqrt (t + x ^ 2)) : ℝ) : ℂ) := by
        have hcong : (∫ t in Ioi (0 : ℝ),
            Complex.exp (-(s : ℂ) * (t : ℂ)) * ((t : ℂ) + (x : ℂ) ^ 2) ^ (-((1 : ℂ) / 2)))
            = ∫ t in Ioi (0 : ℝ), (((Real.exp (-s * t) / Real.sqrt (t + x ^ 2)) : ℝ) : ℂ) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
          have ht0 : (0 : ℝ) < t := ht
          rw [hker t ht0]
          push_cast
          ring
        rw [hcong]
        exact _root_.integral_complex_ofReal
      rw [hL, erf_7_7_4 hs hx,
        show ((Real.pi : ℂ) / (s : ℂ)) = ((Real.pi / s : ℝ) : ℂ) by push_cast; ring,
        aux_cpow_half_ofReal (by positivity), aux_cpow_half_ofReal hs.le,
        show ((Real.sqrt s : ℝ) : ℂ) * (x : ℂ) = ((Real.sqrt s * x : ℝ) : ℂ) by push_cast; ring,
        cerfc_ofReal]
      push_cast
      ring
  -- Step 2: continue in `z`, at the complex `a`.
  rw [hdiv a z]
  have hGz : Differentiable ℂ (fun w : ℂ => ((Real.pi : ℂ) / a) ^ ((1 : ℂ) / 2) *
      Complex.exp (a * w ^ 2) * cerfc (a ^ ((1 : ℂ) / 2) * w)) := by
    have hd := aux_differentiable_cerfc
    fun_prop
  exact aux_eq_of_analytic_rightHalfPlane
    (F := fun w : ℂ => ∫ t in Ioi (0 : ℝ),
      Complex.exp (-a * (t : ℂ)) * ((t : ℂ) + w ^ 2) ^ (-((1 : ℂ) / 2)))
    (G := fun w : ℂ => ((Real.pi : ℂ) / a) ^ ((1 : ℂ) / 2) * Complex.exp (a * w ^ 2)
      * cerfc (a ^ ((1 : ℂ) / 2) * w))
    (aux_analyticOnNhd_shiftPow_z ha) (fun w _ => hGz.analyticAt w)
    (fun x hx => step1 x hx a ha) z hz

-- no-dlmf: real reparametrized instance (`a ↦ a²`, with the `e^{a}` factor carried
-- inside the integral) of DLMF 7.7.5; faithful surface is erf_7_7_5_dlmf
/-- Error function via a unit-interval integral representation, real
reparametrized form of DLMF 7.7.5: for real `a`,
`∫₀¹ e^{-a²(t²+1)}/(t²+1) dt = (π/4)(1 - (erf a)²)`.
This is DLMF 7.7.5 with `a_DLMF = a²` after multiplying through by `e^{-a²}`;
the DLMF display itself (complex `a`, `Re a > 0`) is `erf_7_7_5_dlmf`.
-/
theorem erf_7_7_5 (a : ℝ) :
    (∫ t in (0:ℝ)..1, Real.exp (-(a ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1)) =
      (Real.pi / 4) * (1 - (erf a) ^ 2) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  set I : ℝ → ℝ := fun a => ∫ t in (0:ℝ)..1, Real.exp (-(a ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1)
    with hIdef
  set R : ℝ → ℝ := fun a => (Real.pi / 4) * (1 - (erf a) ^ 2) with hRdef
  set D : ℝ → ℝ := fun a₀ => -(Real.sqrt Real.pi) * Real.exp (-a₀ ^ 2) * erf a₀ with hDdef
  have hIderiv : ∀ a₀ : ℝ, HasDerivAt I (D a₀) a₀ := by
    intro a₀
    have hstep :
        HasDerivAt (fun a => ∫ t in (0:ℝ)..1, Real.exp (-(a ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1))
          (∫ t in (0:ℝ)..1, -(2 * a₀) * Real.exp (-(a₀ ^ 2) * (t ^ 2 + 1))) a₀ := by
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun a t => Real.exp (-(a ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1))
        (F' := fun a t => -(2 * a) * Real.exp (-(a ^ 2) * (t ^ 2 + 1)))
        (bound := fun _ => 2 * (|a₀| + 1)) (s := Metric.ball a₀ 1)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_).2
      · exact Metric.ball_mem_nhds a₀ one_pos
      · refine Filter.Eventually.of_forall (fun x => ?_)
        apply Continuous.aestronglyMeasurable
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro t; positivity
      · apply Continuous.intervalIntegrable
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro t; positivity
      · apply Continuous.aestronglyMeasurable
        fun_prop
      · refine MeasureTheory.ae_of_all _ (fun t _ x hx => ?_)
        have hexp : Real.exp (-(x ^ 2) * (t ^ 2 + 1)) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ x ^ 2 * (t ^ 2 + 1) := by positivity
          nlinarith
        have hxb : |x| ≤ |a₀| + 1 := by
          have := Metric.mem_ball.mp hx
          rw [Real.dist_eq] at this
          have h2 : |x| - |a₀| ≤ |x - a₀| := abs_sub_abs_le_abs_sub x a₀
          linarith
        have hpos : 0 ≤ Real.exp (-(x ^ 2) * (t ^ 2 + 1)) := (Real.exp_pos _).le
        rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_two,
          abs_of_nonneg hpos]
        calc 2 * |x| * Real.exp (-(x ^ 2) * (t ^ 2 + 1))
            ≤ 2 * (|a₀| + 1) * 1 := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hxb (by norm_num)
              · exact hexp
              · exact hpos
              · positivity
          _ = 2 * (|a₀| + 1) := by ring
      · exact intervalIntegrable_const
      · refine MeasureTheory.ae_of_all _ (fun t _ x _ => ?_)
        have hp : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := by
          simpa using (hasDerivAt_pow 2 x).neg
        have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) * (t ^ 2 + 1)) (-(2 * x) * (t ^ 2 + 1)) x :=
          hp.mul_const (t ^ 2 + 1)
        have h2 := h1.exp
        have h3 := h2.div_const (t ^ 2 + 1)
        have hc : (t ^ 2 + 1) ≠ 0 := by positivity
        convert h3 using 1
        field_simp
    have hval : (∫ t in (0:ℝ)..1, -(2 * a₀) * Real.exp (-(a₀ ^ 2) * (t ^ 2 + 1))) = D a₀ := by
      rcases eq_or_ne a₀ 0 with h0 | h0
      · subst h0; simp [hDdef]
      · have factor : ∀ t : ℝ,
            -(2 * a₀) * Real.exp (-(a₀ ^ 2) * (t ^ 2 + 1))
              = (-(2 * a₀) * Real.exp (-a₀ ^ 2)) * Real.exp (-(a₀ * t) ^ 2) := by
          intro t
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        rw [intervalIntegral.integral_congr (fun t _ => factor t),
          intervalIntegral.integral_const_mul]
        have hcm := intervalIntegral.integral_comp_mul_left (f := fun u => Real.exp (-u ^ 2))
          (a := 0) (b := 1) (c := a₀) h0
        simp only [mul_zero, mul_one] at hcm
        rw [hcm]
        have herf : (∫ t in (0:ℝ)..a₀, Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 * erf a₀ := by
          rw [erf]
          field_simp
        rw [herf, hDdef]
        rw [smul_eq_mul]
        field_simp
    rw [hIdef]
    rw [hval] at hstep
    exact hstep
  have hRderiv : ∀ a₀ : ℝ, HasDerivAt R (D a₀) a₀ := by
    intro a₀
    have he := hasDerivAt_erf a₀
    have h2 : HasDerivAt (fun a => (erf a) ^ 2) (2 * erf a₀ * ((2 / Real.sqrt Real.pi) * Real.exp (-a₀ ^ 2))) a₀ := by
      have := he.pow 2
      simpa using this
    have h3 := (h2.const_sub 1).const_mul (Real.pi / 4)
    have hkey : Real.pi / 4 * -(2 * erf a₀ * (2 / Real.sqrt Real.pi * Real.exp (-a₀ ^ 2))) = D a₀ := by
      rw [hDdef]
      have hdiv : Real.pi / Real.sqrt Real.pi = Real.sqrt Real.pi := Real.div_sqrt
      rw [show Real.pi / 4 * -(2 * erf a₀ * (2 / Real.sqrt Real.pi * Real.exp (-a₀ ^ 2)))
          = -(Real.pi / Real.sqrt Real.pi) * Real.exp (-a₀ ^ 2) * erf a₀ by ring, hdiv]
    rw [hRdef, ← hkey]
    exact h3
  have hconst : ∀ x y : ℝ, (I x - R x) = (I y - R y) := by
    apply is_const_of_deriv_eq_zero
    · intro x
      exact ((hIderiv x).sub (hRderiv x)).differentiableAt
    · intro x
      have hd : HasDerivAt (fun y => I y - R y) 0 x := by
        have := (hIderiv x).sub (hRderiv x)
        simpa using this
      exact hd.deriv
  have hI0 : I 0 = Real.pi / 4 := by
    rw [hIdef]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_mul,
      Real.exp_zero]
    have : (∫ t in (0:ℝ)..1, (1 : ℝ) / (t ^ 2 + 1)) = Real.pi / 4 := by
      have h := integral_one_div_one_add_sq (a := (0:ℝ)) (b := 1)
      rw [Real.arctan_one, Real.arctan_zero, sub_zero] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    convert this using 2
  have hR0 : R 0 = Real.pi / 4 := by
    rw [hRdef]; simp
  have := hconst a 0
  rw [hI0, hR0] at this
  have hIa : I a = R a := by linarith
  rw [hIdef, hRdef] at hIa
  exact hIa

-- no-dlmf: DLMF 7.7.5 on the positive real axis (the `a = b²` substitution in
-- `erf_7_7_5`), the seed of the analytic continuation in `erf_7_7_5_dlmf`
/-- For `s > 0`, `∫₀¹ e^{-s t²}/(t²+1) dt = (π/4) e^{s} (1 - (erf √s)²)`. -/
private lemma aux_erf775_real {s : ℝ} (hs : 0 < s) :
    (∫ t in (0:ℝ)..1, Real.exp (-s * t ^ 2) / (t ^ 2 + 1)) =
      (Real.pi / 4) * Real.exp s * (1 - (erf (Real.sqrt s)) ^ 2) := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have h := erf_7_7_5 (Real.sqrt s)
  rw [hsq] at h
  have hfac : ∀ t : ℝ, Real.exp (-s * (t ^ 2 + 1)) / (t ^ 2 + 1)
      = Real.exp (-s) * (Real.exp (-s * t ^ 2) / (t ^ 2 + 1)) := by
    intro t
    rw [show -s * (t ^ 2 + 1) = -s + -s * t ^ 2 by ring, Real.exp_add]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hfac t),
    intervalIntegral.integral_const_mul] at h
  have hexp : Real.exp (-s) ≠ 0 := (Real.exp_pos _).ne'
  have hmul := congrArg (fun u : ℝ => Real.exp s * u) h
  simp only at hmul
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hmul
  rw [hmul]
  ring

-- no-dlmf: entirety in the parameter `a` of the DLMF 7.7.5 unit-interval integral,
-- support lemma
/-- `a ↦ ∫₀¹ e^{-a t²}/(t²+1) dt` is entire.  Differentiation under the integral
sign: the parameter derivative `-t² e^{-a t²}/(t²+1)` is bounded on `t ∈ (0,1]`,
uniformly for `a` in the unit ball around `a₀`, by the constant
`e^{|Re a₀| + 1}`. -/
private lemma aux_differentiable_erf775 :
    Differentiable ℂ (fun a : ℂ => ∫ t in (0:ℝ)..1,
      Complex.exp (-a * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) := by
  have hden : ∀ t : ℝ, ((t : ℂ) ^ 2 + 1) ≠ 0 := by
    intro t
    have h : ((t : ℂ) ^ 2 + 1) = (((t ^ 2 + 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast (by positivity : (0:ℝ) < t ^ 2 + 1).ne'
  have hre : ∀ (x : ℂ) (t : ℝ), (-x * (t : ℂ) ^ 2).re = -x.re * t ^ 2 := by
    intro x t
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hnormexp : ∀ (x : ℂ) (t : ℝ),
      ‖Complex.exp (-x * (t : ℂ) ^ 2)‖ = Real.exp (-x.re * t ^ 2) := by
    intro x t
    rw [Complex.norm_exp, hre]
  have hcontF : ∀ x : ℂ,
      Continuous (fun t : ℝ => Complex.exp (-x * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) := by
    intro x
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  have hcontF' : ∀ x : ℂ,
      Continuous (fun t : ℝ =>
        -(t : ℂ) ^ 2 * Complex.exp (-x * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) := by
    intro x
    exact Continuous.div (by fun_prop) (by fun_prop) hden
  have hderiv : ∀ (x : ℂ) (t : ℝ),
      HasDerivAt (fun w : ℂ => Complex.exp (-w * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
        (-(t : ℂ) ^ 2 * Complex.exp (-x * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) x := by
    intro x t
    have h1 : HasDerivAt (fun w : ℂ => -w * (t : ℂ) ^ 2) (-(t : ℂ) ^ 2) x := by
      simpa using ((hasDerivAt_id x).neg.mul_const ((t : ℂ) ^ 2))
    have h3 := h1.cexp.div_const ((t : ℂ) ^ 2 + 1)
    convert h3 using 1
    ring
  intro a₀
  have hbound : ∀ t : ℝ, t ∈ Set.Ioc (0:ℝ) 1 → ∀ x ∈ Metric.ball a₀ 1,
      ‖-(t : ℂ) ^ 2 * Complex.exp (-x * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)‖
        ≤ Real.exp (|a₀.re| + 1) := by
    intro t ht x hx
    have ht0 : (0:ℝ) < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hc1 : (-(t : ℂ) ^ 2) = ((-t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hc2 : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc1, hc2, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, hnormexp x t,
      abs_of_neg (by nlinarith : (-t ^ 2 : ℝ) < 0), abs_of_pos (by positivity : (0:ℝ) < t ^ 2 + 1)]
    have hxr : |x.re| ≤ |a₀.re| + 1 := by
      have hd : ‖x - a₀‖ < 1 := by
        simpa [Complex.dist_eq] using Metric.mem_ball.mp hx
      have hre1 : |x.re - a₀.re| ≤ ‖x - a₀‖ := by
        simpa using Complex.abs_re_le_norm (x - a₀)
      have h2 : |x.re| - |a₀.re| ≤ |x.re - a₀.re| := abs_sub_abs_le_abs_sub x.re a₀.re
      linarith
    have hexpb : Real.exp (-x.re * t ^ 2) ≤ Real.exp (|a₀.re| + 1) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -x.re * t ^ 2 ≤ |x.re| * t ^ 2 :=
        mul_le_mul_of_nonneg_right (neg_le_abs x.re) (sq_nonneg t)
      have h2 : |x.re| * t ^ 2 ≤ |x.re| * 1 :=
        mul_le_mul_of_nonneg_left ht2 (abs_nonneg _)
      linarith
    have hfrac : - -t ^ 2 / (t ^ 2 + 1) ≤ 1 := by
      rw [neg_neg, div_le_one (by positivity)]
      nlinarith
    calc - -t ^ 2 * Real.exp (-x.re * t ^ 2) / (t ^ 2 + 1)
        = (- -t ^ 2 / (t ^ 2 + 1)) * Real.exp (-x.re * t ^ 2) := by ring
      _ ≤ 1 * Real.exp (|a₀.re| + 1) :=
          mul_le_mul hfrac hexpb (Real.exp_pos _).le zero_le_one
      _ = Real.exp (|a₀.re| + 1) := one_mul _
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a t => Complex.exp (-a * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
    (F' := fun a t => -(t : ℂ) ^ 2 * Complex.exp (-a * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
    (bound := fun _ => Real.exp (|a₀.re| + 1)) (s := Metric.ball a₀ 1)
    (μ := MeasureTheory.volume)
    (Metric.ball_mem_nhds a₀ one_pos)
    (Filter.Eventually.of_forall
      (fun x => ((hcontF x).aestronglyMeasurable).restrict))
    ((hcontF a₀).intervalIntegrable 0 1)
    ((hcontF' a₀).aestronglyMeasurable).restrict
    (MeasureTheory.ae_of_all _ (fun t ht x hx => hbound t
      (by rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht) x hx))
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ (fun t _ x _ => hderiv x t))).2
  exact hmain.differentiableAt

/-- **DLMF 7.7.5**: `∫₀¹ e^{-a t²}/(t²+1) dt = (π/4)·e^{a}·(1 - (erf √a)²)`,
for complex `a` with `Re a > 0` (principal branch of `√·`).

The real theorem `erf_7_7_5` above is the `a = b²` reparametrization of this
display, restricted to the real axis; this is DLMF's own form.

DLMF 7.7.5.
DAG: E-7.7.5.
Numerical: N/A
Verified: verified
-/
theorem erf_7_7_5_dlmf {a : ℂ} (ha : 0 < a.re) :
    (∫ t in (0:ℝ)..1, Complex.exp (-a * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)) =
      ((Real.pi : ℂ) / 4) * Complex.exp a * (1 - (cerf (a ^ ((1 : ℂ) / 2))) ^ 2) := by
  have hG : AnalyticOnNhd ℂ (fun b : ℂ => ((Real.pi : ℂ) / 4) * Complex.exp b
      * (1 - (cerf (b ^ ((1 : ℂ) / 2))) ^ 2)) {b : ℂ | 0 < b.re} := by
    have hUopen : IsOpen {b : ℂ | 0 < b.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd (fun b hb => ?_) hUopen
    have hbre : (0 : ℝ) < b.re := hb
    have hslit : b ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hbre)
    have d1 : DifferentiableAt ℂ (fun w : ℂ => ((Real.pi : ℂ) / 4) * Complex.exp w) b := by
      fun_prop
    have d2 : DifferentiableAt ℂ (fun w : ℂ => cerf (w ^ ((1 : ℂ) / 2))) b :=
      (differentiable_cerf _).comp b (DifferentiableAt.cpow_const differentiableAt_id hslit)
    exact (d1.mul ((differentiableAt_const (1 : ℂ)).sub (d2.pow 2))).differentiableWithinAt
  have hreal : ∀ s : ℝ, 0 < s →
      (∫ t in (0:ℝ)..1, Complex.exp (-(s : ℂ) * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
        = ((Real.pi : ℂ) / 4) * Complex.exp (s : ℂ)
            * (1 - (cerf ((s : ℂ) ^ ((1 : ℂ) / 2))) ^ 2) := by
    intro s hs
    have hpt : ∀ t : ℝ, Complex.exp (-(s : ℂ) * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1)
        = (((Real.exp (-s * t ^ 2) / (t ^ 2 + 1) : ℝ)) : ℂ) := by
      intro t
      have harg : ((-s * t ^ 2 : ℝ) : ℂ) = -(s : ℂ) * (t : ℂ) ^ 2 := by push_cast; ring
      rw [Complex.ofReal_div, Complex.ofReal_exp, harg]
      push_cast
      ring
    have hL : (∫ t in (0:ℝ)..1, Complex.exp (-(s : ℂ) * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
        = (((∫ t in (0:ℝ)..1, Real.exp (-s * t ^ 2) / (t ^ 2 + 1)) : ℝ) : ℂ) := by
      rw [show (∫ t in (0:ℝ)..1, Complex.exp (-(s : ℂ) * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
            = ∫ t in (0:ℝ)..1, (((Real.exp (-s * t ^ 2) / (t ^ 2 + 1) : ℝ)) : ℂ) from
          intervalIntegral.integral_congr (fun t _ => hpt t)]
      exact intervalIntegral.integral_ofReal
    rw [hL, aux_erf775_real hs, aux_cpow_half_ofReal hs.le, cerf_ofReal]
    push_cast
    ring
  exact aux_eq_of_analytic_rightHalfPlane
    (F := fun b : ℂ => ∫ t in (0:ℝ)..1, Complex.exp (-b * (t : ℂ) ^ 2) / ((t : ℂ) ^ 2 + 1))
    (G := fun b : ℂ => ((Real.pi : ℂ) / 4) * Complex.exp b
      * (1 - (cerf (b ^ ((1 : ℂ) / 2))) ^ 2))
    (fun w _ => aux_differentiable_erf775.analyticAt w) hG hreal a ha

-- no-dlmf: real/narrowed restriction of DLMF 7.7.6 (DLMF allows complex a
-- with Re a > 0, and does not restrict b, c to be real); faithful surface
-- is erf_7_7_6_dlmf
/-- Completed-square Gaussian integral over `[x, ∞)` evaluated by `erfc`,
real specialization: for real `a > 0`, `b`, `c` and real `x`,
`∫ₓ^∞ e^{-(a t² + 2 b t + c)} dt
  = (1/2) √(π/a) · e^{(b² - a c)/a} · erfc(√a · x + b/√a)`.
-/
theorem erf_7_7_6 (a b c x : ℝ) (ha : 0 < a) :
    (∫ t in Ioi x, Real.exp (-(a * t ^ 2 + 2 * b * t + c))) =
      (1 / 2) * Real.sqrt (Real.pi / a) * Real.exp ((b ^ 2 - a * c) / a) *
        erfc (Real.sqrt a * x + b / Real.sqrt a) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : ∀ t : ℝ, Real.exp (-(a * t ^ 2 + 2 * b * t + c))
      = Real.exp ((b ^ 2 - a * c) / a) * Real.exp (-a * (t + b / a) ^ 2) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hsq t), integral_const_mul]
  have htrans : (∫ t in Ioi x, Real.exp (-a * (t + b / a) ^ 2))
      = ∫ u in Ioi (x + b / a), Real.exp (-a * u ^ 2) := by
    have himg : (fun t : ℝ => t + b / a) '' Ioi x = Ioi (x + b / a) := by
      ext u
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨t, ht, rfl⟩; linarith
      · intro hu; exact ⟨u - b / a, by linarith, by ring⟩
    have hderiv : ∀ t ∈ Ioi x, HasDerivWithinAt (fun t : ℝ => t + b / a) 1 (Ioi x) t :=
      fun t _ => ((hasDerivAt_id t).add_const (b / a)).hasDerivWithinAt
    have hinj : InjOn (fun t : ℝ => t + b / a) (Ioi x) := fun p _ q _ h => by
      simpa using h
    have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
      (fun u => Real.exp (-a * u ^ 2))
    rw [himg] at hcov
    rw [hcov]
    simp
  rw [htrans, integral_Ioi_gaussian_scaled_erfc ha]
  have harg : Real.sqrt a * (x + b / a) = Real.sqrt a * x + b / Real.sqrt a := by
    rw [mul_add]
    congr 1
    rw [eq_div_iff (ne_of_gt hsa)]
    field_simp
    linear_combination b * Real.mul_self_sqrt ha.le
  rw [harg]
  ring

/-- **DLMF 7.7.6**: `∫ₓ^∞ e^{-(a t² + 2 b t + c)} dt
= (1/2)√(π/a)·e^{(b² - a c)/a}·erfc(√a·x + b/√a)`, for complex `a`, `b`, `c`
with `Re a > 0` and real `x` (principal branch of `√·`).

DAG: E-7.7.6.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_6_dlmf {a b c : ℂ} (x : ℝ) (ha : 0 < a.re) :
    (∫ t in Ioi x, Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ) + c))) =
      (1 / 2) * ((Real.pi : ℂ) / a) ^ ((1 : ℂ) / 2) * Complex.exp ((b ^ 2 - a * c) / a) *
        cerfc (a ^ ((1 : ℂ) / 2) * (x : ℂ) + b / a ^ ((1 : ℂ) / 2)) := by
  -- `c` factors out of both sides, so the content is the `c = 0` identity, which is
  -- obtained from the real specialization by continuing first in `b` (entire) and
  -- then in `a` (right half-plane).
  have hane : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  -- right-hand side, analytic in the quadratic coefficient on the right half-plane
  have hGa : ∀ w : ℂ, AnalyticOnNhd ℂ
      (fun q : ℂ => (1 / 2) * ((Real.pi : ℂ) / q) ^ ((1 : ℂ) / 2) * Complex.exp (w ^ 2 / q)
        * cerfc (q ^ ((1 : ℂ) / 2) * (x : ℂ) + w / q ^ ((1 : ℂ) / 2)))
      {q : ℂ | 0 < q.re} := by
    intro w
    have hUopen : IsOpen {q : ℂ | 0 < q.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticOnNhd (fun q hq => ?_) hUopen
    have hqre : (0 : ℝ) < q.re := hq
    have hqne : q ≠ 0 := by intro h; rw [h] at hqre; simp at hqre
    have hslitq : q ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hqre)
    have hnsq : 0 < Complex.normSq q := Complex.normSq_pos.mpr hqne
    have hslitpi : ((Real.pi : ℂ) / q) ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
      exact div_pos (mul_pos Real.pi_pos hqre) hnsq
    have hroot : DifferentiableAt ℂ (fun v : ℂ => v ^ ((1 : ℂ) / 2)) q :=
      DifferentiableAt.cpow_const differentiableAt_id hslitq
    have hrootne : q ^ ((1 : ℂ) / 2) ≠ 0 := by
      intro h
      exact hqne ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have d1 : DifferentiableAt ℂ (fun v : ℂ => (1 / 2 : ℂ) * ((Real.pi : ℂ) / v) ^ ((1 : ℂ) / 2)) q :=
      (DifferentiableAt.cpow_const
        ((differentiableAt_const _).div differentiableAt_id hqne) hslitpi).const_mul _
    have d2 : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (w ^ 2 / v)) q :=
      (((differentiableAt_const _).div differentiableAt_id hqne)).cexp
    have d3 : DifferentiableAt ℂ
        (fun v : ℂ => cerfc (v ^ ((1 : ℂ) / 2) * (x : ℂ) + w / v ^ ((1 : ℂ) / 2))) q := by
      have hinner : DifferentiableAt ℂ
          (fun v : ℂ => v ^ ((1 : ℂ) / 2) * (x : ℂ) + w / v ^ ((1 : ℂ) / 2)) q :=
        (hroot.mul_const (x : ℂ)).add ((differentiableAt_const _).div hroot hrootne)
      exact (aux_differentiable_cerfc _).comp q hinner
    exact ((d1.mul d2).mul d3).differentiableWithinAt
  -- Step A: continue in the linear coefficient `b`, at a positive real `a = α`.
  have key : ∀ α : ℝ, 0 < α → ∀ w : ℂ,
      (∫ t in Ioi x, Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * w * (t : ℂ))))
        = (1 / 2) * ((Real.pi : ℂ) / (α : ℂ)) ^ ((1 : ℂ) / 2) * Complex.exp (w ^ 2 / (α : ℂ))
          * cerfc ((α : ℂ) ^ ((1 : ℂ) / 2) * (x : ℂ) + w / (α : ℂ) ^ ((1 : ℂ) / 2)) := by
    intro α hα
    have hαne : ((α : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hα
    have hroot : ((α : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt α : ℂ) := aux_cpow_half_ofReal hα.le
    have hsqrtne : (Real.sqrt α : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hα)
    refine aux_eq_of_entire_of_real
      (fun w => ((aux_analyticOnNhd_gauss_b x hα) w (Set.mem_univ w)).differentiableAt) ?_ ?_
    · have hd := aux_differentiable_cerfc
      fun_prop
    · intro β hβ
      have hL : (∫ t in Ioi x, Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * (β : ℂ) * (t : ℂ))))
          = (((∫ t in Ioi x, Real.exp (-(α * t ^ 2 + 2 * β * t + 0))) : ℝ) : ℂ) := by
        have hcong : (∫ t in Ioi x,
              Complex.exp (-((α : ℂ) * (t : ℂ) ^ 2 + 2 * (β : ℂ) * (t : ℂ))))
            = ∫ t in Ioi x, (((Real.exp (-(α * t ^ 2 + 2 * β * t + 0))) : ℝ) : ℂ) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
          push_cast
          ring_nf
        rw [hcong]
        exact _root_.integral_complex_ofReal
      rw [hL, erf_7_7_6 α β 0 x hα]
      simp only [mul_zero, sub_zero]
      rw [show ((Real.pi : ℂ) / ((α : ℝ) : ℂ)) = ((Real.pi / α : ℝ) : ℂ) by push_cast; ring,
        aux_cpow_half_ofReal (by positivity), hroot,
        show ((β : ℝ) : ℂ) ^ 2 / ((α : ℝ) : ℂ) = ((β ^ 2 / α : ℝ) : ℂ) by push_cast; ring,
        show ((Real.sqrt α : ℝ) : ℂ) * (x : ℂ) + ((β : ℝ) : ℂ) / ((Real.sqrt α : ℝ) : ℂ)
          = ((Real.sqrt α * x + β / Real.sqrt α : ℝ) : ℂ) by push_cast; ring,
        cerfc_ofReal]
      push_cast
      ring
  -- Step B: continue in the quadratic coefficient `a`, at the complex `b`.
  have keyA : ∀ w : ℂ, ∀ q : ℂ, 0 < q.re →
      (∫ t in Ioi x, Complex.exp (-(q * (t : ℂ) ^ 2 + 2 * w * (t : ℂ))))
        = (1 / 2) * ((Real.pi : ℂ) / q) ^ ((1 : ℂ) / 2) * Complex.exp (w ^ 2 / q)
          * cerfc (q ^ ((1 : ℂ) / 2) * (x : ℂ) + w / q ^ ((1 : ℂ) / 2)) := by
    intro w
    exact aux_eq_of_analytic_rightHalfPlane (aux_analyticOnNhd_gauss_a x w) (hGa w)
      (fun s hs => key s hs w)
  -- Reinstate the constant term `c`.
  have hsplit : (∫ t in Ioi x, Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ) + c)))
      = Complex.exp (-c) * ∫ t in Ioi x, Complex.exp (-(a * (t : ℂ) ^ 2 + 2 * b * (t : ℂ))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [← Complex.exp_add]
    congr 1
    ring
  have hexp : Complex.exp ((b ^ 2 - a * c) / a) = Complex.exp (-c) * Complex.exp (b ^ 2 / a) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit, keyA b a ha, hexp]
  ring

-- DLMF 7.7.7 (deferred): `erfc` of a complex argument as an integral with
--   `|ph a| < π/4`. The faithful statement is over complex `a`/`z`; the
--   sector restriction `|ph a| < π/4` has no real analogue distinct from 7.7.6.
--   Deferred as a complex-sector statement.

-- DLMF 7.7.8 (deferred): `∫₀^∞ e^{-a t² - b/t²} dt` type evaluation with complex
--   `a`, `b` and `|ph a|, |ph b| < π/4`. The faithful sector statement is
--   complex; deferred.

/-- Antiderivative of `erf` (DLMF 7.7.9), real specialization: for real `x`,
`∫₀ˣ erf t dt = x · erf x + (e^{-x²} - 1)/√π`.

DLMF 7.7.9.
DAG: E-7.7.9.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_9 (x : ℝ) :
    (∫ t in (0:ℝ)..x, erf t) =
      x * erf x + (Real.exp (-x ^ 2) - 1) / Real.sqrt Real.pi := by
  set Φ : ℝ → ℝ := fun y => y * erf y + (Real.exp (-y ^ 2) - 1) / Real.sqrt Real.pi with hΦdef
  have hΦderiv : ∀ y : ℝ, HasDerivAt Φ (erf y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * y)) y := by
      have := (hasDerivAt_pow 2 y).neg
      convert this using 1
      ring
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2)) (Real.exp (-y ^ 2) * (-(2 * y))) y :=
      h1.exp
    have hmul : HasDerivAt (fun y : ℝ => y * erf y)
        (1 * erf y + y * ((2 / Real.sqrt Real.pi) * Real.exp (-y ^ 2))) y :=
      (hasDerivAt_id y).mul (hasDerivAt_erf y)
    have hconst : HasDerivAt (fun y : ℝ => (Real.exp (-y ^ 2) - 1) / Real.sqrt Real.pi)
        ((Real.exp (-y ^ 2) * (-(2 * y))) / Real.sqrt Real.pi) y :=
      (hexp.sub_const 1).div_const _
    have h := hmul.add hconst
    convert h using 1
    field_simp
    ring
  have hΦ0 : Φ 0 = 0 := by simp [hΦdef]
  have hcont : IntervalIntegrable erf MeasureTheory.volume 0 x :=
    continuous_erf.intervalIntegrable 0 x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hΦderiv y) hcont
  rw [hFTC, hΦ0]
  ring

-- no-dlmf: integrability of the z = 0 dominant `t^s/(t²+1)` for 7.7.10/7.7.11
private lemma aux_integrable_rpow_div {s : ℝ} (hs₁ : -1 < s) (hs₂ : s < 1) :
    IntegrableOn (fun t : ℝ => t ^ s / (t ^ 2 + 1)) (Ioi (0 : ℝ)) := by
  have hmeas : ∀ u : Set ℝ, AEStronglyMeasurable (fun t : ℝ => t ^ s / (t ^ 2 + 1))
      (volume.restrict u) := by
    intro u
    apply Measurable.aestronglyMeasurable
    fun_prop
  have h1 : IntegrableOn (fun t : ℝ => t ^ s / (t ^ 2 + 1)) (Ioc (0 : ℝ) 1) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ s) (Ioc (0 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_rpow' hs₁).1
    refine hbase.mono' (hmeas _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by nlinarith)
  have h2 : IntegrableOn (fun t : ℝ => t ^ s / (t ^ 2 + 1)) (Ioi (1 : ℝ)) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (s - 2)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hbase.mono' (hmeas _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_sub ht0, Real.rpow_two]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have h := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

-- no-dlmf: dominated-convergence limit `z → 0⁺` of the 7.7.10/7.7.11 integrals
private lemma aux_tendsto_K_zero {s : ℝ} (hs₁ : -1 < s) (hs₂ : s < 1) :
    Tendsto (fun z : ℝ => ∫ t in Ioi (0 : ℝ),
        Real.exp (-Real.pi * z ^ 2 * t / 2) * t ^ s / (t ^ 2 + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (0 : ℝ), t ^ s / (t ^ 2 + 1))) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => t ^ s / (t ^ 2 + 1)) ?_ ?_ (aux_integrable_rpow_div hs₁ hs₂) ?_
  · refine Eventually.of_forall fun z => ?_
    apply Measurable.aestronglyMeasurable
    fun_prop
  · refine Eventually.of_forall fun z => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-Real.pi * z ^ 2 * t / 2) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ Real.pi * z ^ 2 * t / 2 := by positivity
      linarith
    calc Real.exp (-Real.pi * z ^ 2 * t / 2) * t ^ s / (t ^ 2 + 1)
        ≤ 1 * t ^ s / (t ^ 2 + 1) := by gcongr
      _ = t ^ s / (t ^ 2 + 1) := by rw [one_mul]
  · refine Eventually.of_forall fun t => ?_
    have hc : Continuous fun z : ℝ => Real.exp (-Real.pi * z ^ 2 * t / 2) := by fun_prop
    have h : Tendsto (fun z : ℝ => Real.exp (-Real.pi * z ^ 2 * t / 2) * t ^ s / (t ^ 2 + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-Real.pi * 0 ^ 2 * t / 2) * t ^ s / (t ^ 2 + 1))) :=
      (((hc.tendsto 0).mono_left nhdsWithin_le_nhds).mul_const (t ^ s)).div_const (t ^ 2 + 1)
    simpa using h

-- no-dlmf: continuity of the auxiliary `f` (support for the z = 0 endpoint of 7.7.10)
private lemma aux_continuous_fresnelAuxF : Continuous fresnelAuxF := by
  unfold fresnelAuxF
  have h1 : Continuous fun x : ℝ => Real.pi * x ^ 2 / 2 := by fun_prop
  exact ((continuous_const.sub FLMF.Fresnel.continuous_fresnelS).mul
      (Real.continuous_cos.comp h1)).sub
    ((continuous_const.sub FLMF.Fresnel.continuous_fresnelC).mul
      (Real.continuous_sin.comp h1))

-- no-dlmf: continuity of the auxiliary `g` (support for the z = 0 endpoint of 7.7.11)
private lemma aux_continuous_fresnelAuxG : Continuous fresnelAuxG := by
  unfold fresnelAuxG
  have h1 : Continuous fun x : ℝ => Real.pi * x ^ 2 / 2 := by fun_prop
  exact ((continuous_const.sub FLMF.Fresnel.continuous_fresnelC).mul
      (Real.continuous_cos.comp h1)).add
    ((continuous_const.sub FLMF.Fresnel.continuous_fresnelS).mul
      (Real.continuous_sin.comp h1))

-- no-dlmf: real/narrowed restriction of DLMF 7.7.10 (DLMF states this for
-- complex z with |ph z| ≤ π/4); faithful surface is erf_7_7_10_dlmf
/-- Integral representation of the Fresnel auxiliary `f`,
real specialization: for real `z ≥ 0`,
`f(z) = (1/(π√2)) ∫₀^∞ e^{-π z² t/2}/(√t (t²+1)) dt`.
-/
theorem erf_7_7_10 {z : ℝ} (hz : 0 ≤ z) :
    fresnelAuxF z =
      (1 / (Real.pi * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * z ^ 2 * t / 2) / (Real.sqrt t * (t ^ 2 + 1)) := by
  have hK : ∀ w : ℝ, (∫ t in Ioi (0 : ℝ),
        Real.exp (-Real.pi * w ^ 2 * t / 2) / (Real.sqrt t * (t ^ 2 + 1)))
      = ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1) := by
    intro w
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hst : Real.sqrt t ≠ 0 := by positivity
    rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hpos : ∀ w : ℝ, 0 < w → fresnelAuxF w
      = (1 / (Real.pi * Real.sqrt 2)) * ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1) := by
    intro w hw
    rw [fresnelAuxF_eq_remF_zero hw, remF]
    norm_num
  rcases hz.lt_or_eq with hz0 | hz0
  · rw [hK]
    exact hpos z hz0
  · subst hz0
    rw [hK]
    have h1 : Tendsto fresnelAuxF (𝓝[>] (0 : ℝ)) (𝓝 (fresnelAuxF 0)) :=
      (aux_continuous_fresnelAuxF.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 := (aux_tendsto_K_zero (s := -(1 / 2)) (by norm_num) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    have h3 : fresnelAuxF =ᶠ[𝓝[>] (0 : ℝ)] fun w => (1 / (Real.pi * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hpos w hw
    have h4 := tendsto_nhds_unique (Tendsto.congr' h3 h1) h2
    rw [h4]
    congr 1
    refine (setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)).symm
    norm_num

/-! ### The DLMF 7.7.10 kernel `e^{-πz²t/2}/(√t (t²+1))` -/

-- no-dlmf: norm of the DLMF 7.7.10 integrand, support lemma
private lemma aux_norm_erf7710 (u : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2) /
        ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))‖
      = Real.exp (-(Real.pi * t / 2) * (u ^ 2).re) / (Real.sqrt t * (t ^ 2 + 1)) := by
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hnum : -(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2 = ((-(Real.pi * t / 2) : ℝ) : ℂ) * u ^ 2 := by
    push_cast; ring
  have hden : ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) = ((Real.sqrt t * (t ^ 2 + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [norm_div, hnum, hden, Complex.norm_exp, Complex.re_ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (mul_pos hst (by positivity : (0 : ℝ) < t ^ 2 + 1))]

-- no-dlmf: `√t ≠ 0` and the 7.7.10 denominator is nonzero on `(0,∞)`, support lemma
private lemma aux_den7710_ne (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
    ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) ≠ 0 := by
  have ht0 : (0 : ℝ) < t := ht
  have h : ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) = ((Real.sqrt t * (t ^ 2 + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h]
  exact_mod_cast ne_of_gt
    (mul_pos (Real.sqrt_pos.mpr ht0) (by positivity : (0 : ℝ) < t ^ 2 + 1))

-- no-dlmf: measurability of the 7.7.10 integrand and its `z`-derivative, support lemma
private lemma aux_meas7710 {N : ℝ → ℂ} (hN : Continuous N) :
    AEStronglyMeasurable (fun t : ℝ => N t / ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ContinuousOn.div hN.continuousOn ?_ aux_den7710_ne
  exact (Continuous.continuousOn (by fun_prop))

-- no-dlmf: analyticity in `z` of the DLMF 7.7.10 integral on the open sector
private lemma aux_analyticOnNhd_erf7710 :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
      {z : ℂ | |z.im| < z.re} := by
  have hπ := Real.pi_pos
  have hdom0 : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1)) (Ioi (0 : ℝ)) :=
    aux_integrable_rpow_div (by norm_num) (by norm_num)
  have hdom1 : IntegrableOn (fun t : ℝ => t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1)) (Ioi (0 : ℝ)) :=
    aux_integrable_rpow_div (by norm_num) (by norm_num)
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun z t => Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
      ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
    (f' := fun z t => -(Real.pi : ℂ) * z * (t : ℂ) *
      Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
        ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
    aux_openSector_isOpen (fun z _ => aux_meas7710 (by fun_prop)) (fun z hz => ?_)
    (fun z _ => aux_meas7710 (by fun_prop)) ?_ ?_
  · have hzs : (0 : ℝ) < (z ^ 2).re := by
      rw [aux_sq_re]
      have h : |z.im| < z.re := hz
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    refine Integrable.mono' hdom0 (aux_meas7710 (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hA : (0 : ℝ) < Real.pi * t / 2 := div_pos (mul_pos hπ ht0) two_pos
    have hexp : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) ≤ 1 := by
      have hprod : (0 : ℝ) ≤ (Real.pi * t / 2) * (z ^ 2).re := mul_nonneg hA.le hzs.le
      rw [Real.exp_le_one_iff, neg_mul]
      linarith
    have hrw : t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1) = 1 / (Real.sqrt t * (t ^ 2 + 1)) := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg ht0.le,
        ← Real.sqrt_eq_rpow]
      field_simp
    rw [aux_norm_erf7710 z ht0, hrw]
    exact div_le_div_of_nonneg_right hexp
      (le_of_lt (mul_pos hst (by positivity : (0 : ℝ) < t ^ 2 + 1)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
    have ht0 : (0 : ℝ) < t := ht
    have h1 : HasDerivAt (fun w : ℂ => -(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2)
        (-(Real.pi : ℂ) * z * (t : ℂ)) z := by
      have h := (((hasDerivAt_pow 2 z).const_mul (-(Real.pi : ℂ))).mul_const (t : ℂ)).div_const 2
      convert h using 1
      push_cast
      ring
    have h2 := (h1.cexp).div_const ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))
    convert h2 using 1
    ring
  · intro z₀ hz₀
    obtain ⟨r, hr, δ, hδ, hball⟩ := aux_openSector_ball hz₀
    refine ⟨r, hr, fun t : ℝ => (Real.pi * (‖z₀‖ + r)) * (t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1)),
      hdom1.const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hzb
    have ht0 : (0 : ℝ) < t := ht
    have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    obtain ⟨hδz, hnz⟩ := hball z hzb
    have hsplit : -(Real.pi : ℂ) * z * (t : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))
        = (-(Real.pi : ℂ) * z * (t : ℂ)) *
            (Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
              ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))) := by ring
    rw [hsplit, norm_mul, aux_norm_erf7710 z ht0]
    have hcoef : ‖-(Real.pi : ℂ) * z * (t : ℂ)‖ = Real.pi * ‖z‖ * t := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hπ]
    rw [hcoef]
    have hexp : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) ≤ 1 := by
      have hzre : (0 : ℝ) < (z ^ 2).re := lt_of_lt_of_le hδ hδz
      have hA : (0 : ℝ) < Real.pi * t / 2 := div_pos (mul_pos hπ ht0) two_pos
      have hprod : (0 : ℝ) ≤ (Real.pi * t / 2) * (z ^ 2).re := mul_nonneg hA.le hzre.le
      rw [Real.exp_le_one_iff, neg_mul]
      linarith
    have hkey : t / (Real.sqrt t * (t ^ 2 + 1)) = t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1) := by
      rw [← Real.sqrt_eq_rpow]
      rw [eq_div_iff (by positivity : (t : ℝ) ^ 2 + 1 ≠ 0)]
      field_simp
      nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_pos.mpr ht0]
    calc Real.pi * ‖z‖ * t *
          (Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) / (Real.sqrt t * (t ^ 2 + 1)))
        ≤ Real.pi * (‖z₀‖ + r) * t * (1 / (Real.sqrt t * (t ^ 2 + 1))) := by
          have hA : Real.pi * ‖z‖ * t ≤ Real.pi * (‖z₀‖ + r) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnz hπ.le) ht0.le
          have hB : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) / (Real.sqrt t * (t ^ 2 + 1))
              ≤ 1 / (Real.sqrt t * (t ^ 2 + 1)) :=
            div_le_div_of_nonneg_right hexp
              (le_of_lt (mul_pos hst (by positivity : (0 : ℝ) < t ^ 2 + 1)))
          have hpos : (0 : ℝ) ≤ Real.pi * (‖z₀‖ + r) * t :=
            mul_nonneg (mul_nonneg hπ.le (add_nonneg (norm_nonneg z₀) hr.le)) ht0.le
          have hnn : (0 : ℝ) ≤ Real.exp (-(Real.pi * t / 2) * (z ^ 2).re)
              / (Real.sqrt t * (t ^ 2 + 1)) := by positivity
          exact le_trans (mul_le_mul_of_nonneg_right hA hnn) (mul_le_mul_of_nonneg_left hB hpos)
      _ = (Real.pi * (‖z₀‖ + r)) * (t / (Real.sqrt t * (t ^ 2 + 1))) := by ring
      _ = (Real.pi * (‖z₀‖ + r)) * (t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1)) := by rw [hkey]

open FLMF.Fresnel in
/-- **DLMF 7.7.10**: `f(z) = (1/(π√2)) ∫₀^∞ e^{-π z² t/2}/(√t (t²+1)) dt`, for
complex `z` with `|ph z| ≤ π/4`, `f = cfresnelAuxF` the complex Fresnel
auxiliary (7.2.10).

DAG: E-7.7.10.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_10_dlmf {z : ℂ} (hz : |Complex.arg z| ≤ Real.pi / 4) :
    cfresnelAuxF z =
      (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
            ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) := by
  -- Same route as `erf_7_7_1_dlmf`: identity theorem on the open sector
  -- `|Im z| < Re z`, then the boundary along `z + 1/(n+1)` by dominated
  -- convergence with the sector-uniform dominant `t^{-1/2}/(t²+1)`.
  have hπ := Real.pi_pos
  have hS : |z.im| ≤ z.re := aux_abs_im_le_re_of_arg hz
  have hdom0 : IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1)) (Ioi (0 : ℝ)) :=
    aux_integrable_rpow_div (by norm_num) (by norm_num)
  have hbnd : ∀ u : ℂ, 0 ≤ (u ^ 2).re → ∀ t : ℝ, 0 < t →
      ‖Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2) /
        ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))‖ ≤ t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1) := by
    intro u hu t ht0
    have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hA : (0 : ℝ) < Real.pi * t / 2 := div_pos (mul_pos hπ ht0) two_pos
    have hexp : Real.exp (-(Real.pi * t / 2) * (u ^ 2).re) ≤ 1 := by
      have hprod : (0 : ℝ) ≤ (Real.pi * t / 2) * (u ^ 2).re := mul_nonneg hA.le hu
      rw [Real.exp_le_one_iff, neg_mul]
      linarith
    have hrw : t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1) = 1 / (Real.sqrt t * (t ^ 2 + 1)) := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg ht0.le,
        ← Real.sqrt_eq_rpow]
      field_simp
    rw [aux_norm_erf7710 u ht0, hrw]
    exact div_le_div_of_nonneg_right hexp
      (le_of_lt (mul_pos hst (by positivity : (0 : ℝ) < t ^ 2 + 1)))
  have hopen : ∀ w : ℂ, |w.im| < w.re →
      cfresnelAuxF w = (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (-(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2) /
            ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) := by
    have hRHS : AnalyticOnNhd ℂ
        (fun w : ℂ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
          ∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2) /
            ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
        {w : ℂ | |w.im| < w.re} := by
      have hc : AnalyticOnNhd ℂ
          (fun _ : ℂ => (1 / ((Real.pi : ℂ) * (Real.sqrt 2 : ℂ)))) {w : ℂ | |w.im| < w.re} :=
        fun w _ => analyticAt_const
      exact hc.mul aux_analyticOnNhd_erf7710
    refine aux_eq_of_analytic_of_real aux_openSector_isPreconnected (by simp)
      (fun w _ => aux_differentiable_cfresnelAuxF.analyticAt w) hRHS ?_
    intro x hx
    have hI : (∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
        = (((∫ t in Ioi (0 : ℝ),
            Real.exp (-Real.pi * x ^ 2 * t / 2) / (Real.sqrt t * (t ^ 2 + 1))) : ℝ) : ℂ) := by
      have hcong : (∫ t in Ioi (0 : ℝ),
            Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2 * (t : ℂ) / 2) /
              ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))
          = ∫ t in Ioi (0 : ℝ),
              (((Real.exp (-Real.pi * x ^ 2 * t / 2) / (Real.sqrt t * (t ^ 2 + 1))) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        push_cast
        ring
      rw [hcong]
      exact _root_.integral_complex_ofReal
    rw [aux_cfresnelAuxF_ofReal, hI, erf_7_7_10 hx.le]
    push_cast
    ring
  rcases lt_or_eq_of_le hS with hlt | heq
  · exact hopen z hlt
  set w : ℕ → ℂ := fun n => z + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) with hwdef
  have hwre : ∀ n : ℕ, (w n).re = z.re + 1 / ((n : ℝ) + 1) := by
    intro n; simp only [hwdef, Complex.add_re, Complex.ofReal_re]
  have hwim : ∀ n : ℕ, (w n).im = z.im := by
    intro n; simp only [hwdef, Complex.add_im, Complex.ofReal_im, add_zero]
  have hwmem : ∀ n : ℕ, |(w n).im| < (w n).re := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [hwim, hwre]
    linarith [hS]
  have hwt : Tendsto w atTop (𝓝 z) := by
    have h : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def] using h2
    simpa [hwdef] using h.const_add z
  have hlhs : Tendsto (fun n : ℕ => cfresnelAuxF (w n)) atTop (𝓝 (cfresnelAuxF z)) :=
    (aux_differentiable_cfresnelAuxF.continuous.tendsto z).comp hwt
  have hInt : Tendsto
      (fun n : ℕ => ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
        ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun t : ℝ => t ^ (-(1 : ℝ) / 2) / (t ^ 2 + 1))
      (fun n => aux_meas7710 (by fun_prop)) hdom0 (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hzs : (0 : ℝ) ≤ ((w n) ^ 2).re := by
        rw [aux_sq_re]
        have h := hwmem n
        nlinarith [abs_nonneg (w n).im, sq_abs (w n).im]
      exact hbnd (w n) hzs t ht0
    · filter_upwards with t
      have hc : Continuous (fun u : ℂ => Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))) := by fun_prop
      exact (hc.tendsto z).comp hwt
  have hrhs : Tendsto
      (fun n : ℕ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1))) atTop
      (𝓝 ((1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)))) := hInt.const_mul _
  have hcongr : (fun n : ℕ => cfresnelAuxF (w n))
      = fun n : ℕ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2) /
          ((Real.sqrt t : ℂ) * ((t : ℂ) ^ 2 + 1)) := by
    funext n
    exact hopen (w n) (hwmem n)
  rw [hcongr] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

-- no-dlmf: real/narrowed restriction of DLMF 7.7.11 (DLMF states this for
-- complex z with |ph z| ≤ π/4); faithful surface is erf_7_7_11_dlmf
/-- Integral representation of the Fresnel auxiliary `g`,
real specialization: for real `z ≥ 0`,
`g(z) = (1/(π√2)) ∫₀^∞ (√t e^{-π z² t/2})/(t²+1) dt`.
-/
theorem erf_7_7_11 {z : ℝ} (hz : 0 ≤ z) :
    fresnelAuxG z =
      (1 / (Real.pi * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          (Real.sqrt t * Real.exp (-Real.pi * z ^ 2 * t / 2)) / (t ^ 2 + 1) := by
  have hK : ∀ w : ℝ, (∫ t in Ioi (0 : ℝ),
        (Real.sqrt t * Real.exp (-Real.pi * w ^ 2 * t / 2)) / (t ^ 2 + 1))
      = ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1) := by
    intro w
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [← Real.sqrt_eq_rpow]
    ring
  have hpos : ∀ w : ℝ, 0 < w → fresnelAuxG w
      = (1 / (Real.pi * Real.sqrt 2)) * ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1) := by
    intro w hw
    rw [fresnelAuxG_eq_remG_zero hw, remG]
    norm_num
  rcases hz.lt_or_eq with hz0 | hz0
  · rw [hK]
    exact hpos z hz0
  · subst hz0
    rw [hK]
    have h1 : Tendsto fresnelAuxG (𝓝[>] (0 : ℝ)) (𝓝 (fresnelAuxG 0)) :=
      (aux_continuous_fresnelAuxG.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 := (aux_tendsto_K_zero (s := (1 / 2)) (by norm_num) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    have h3 : fresnelAuxG =ᶠ[𝓝[>] (0 : ℝ)] fun w => (1 / (Real.pi * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          Real.exp (-Real.pi * w ^ 2 * t / 2) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hpos w hw
    have h4 := tendsto_nhds_unique (Tendsto.congr' h3 h1) h2
    rw [h4]
    congr 1
    refine (setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)).symm
    norm_num

/-! ### The DLMF 7.7.11 kernel `√t·e^{-πz²t/2}/(t²+1)` -/

-- no-dlmf: norm of the DLMF 7.7.11 integrand, support lemma
private lemma aux_norm_erf7711 (u : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2)) /
        ((t : ℂ) ^ 2 + 1)‖
      = Real.sqrt t * Real.exp (-(Real.pi * t / 2) * (u ^ 2).re) / (t ^ 2 + 1) := by
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hnum : -(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2 = ((-(Real.pi * t / 2) : ℝ) : ℂ) * u ^ 2 := by
    push_cast; ring
  have hden : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_div, norm_mul, hnum, hden, Complex.norm_exp, Complex.re_ofReal_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hst, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2 + 1)]

-- no-dlmf: measurability of the 7.7.11 integrand and its `z`-derivative, support lemma
private lemma aux_meas7711 {N : ℝ → ℂ} (hN : Continuous N) :
    AEStronglyMeasurable (fun t : ℝ => ((Real.sqrt t : ℂ) * N t) / ((t : ℂ) ^ 2 + 1))
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine (Continuous.aestronglyMeasurable ?_).restrict
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have h : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    exact_mod_cast ne_of_gt (by positivity : (0 : ℝ) < t ^ 2 + 1)

-- no-dlmf: analyticity in `z` of the DLMF 7.7.11 integral on the open sector
private lemma aux_analyticOnNhd_erf7711 :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ t in Ioi (0 : ℝ),
        ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2)) /
          ((t : ℂ) ^ 2 + 1))
      {z : ℂ | |z.im| < z.re} := by
  have hπ := Real.pi_pos
  have hdom1 : IntegrableOn (fun t : ℝ => t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1)) (Ioi (0 : ℝ)) :=
    aux_integrable_rpow_div (by norm_num) (by norm_num)
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun z t => ((Real.sqrt t : ℂ) *
      Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2)) / ((t : ℂ) ^ 2 + 1))
    (f' := fun z t => ((Real.sqrt t : ℂ) * (-(Real.pi : ℂ) * z * (t : ℂ) *
      Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2))) / ((t : ℂ) ^ 2 + 1))
    aux_openSector_isOpen (fun z _ => aux_meas7711 (by fun_prop)) (fun z hz => ?_)
    (fun z _ => aux_meas7711 (by fun_prop)) ?_ ?_
  · have hzs : (0 : ℝ) < (z ^ 2).re := by
      rw [aux_sq_re]
      have h : |z.im| < z.re := hz
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    refine Integrable.mono' hdom1 (aux_meas7711 (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hA : (0 : ℝ) < Real.pi * t / 2 := div_pos (mul_pos hπ ht0) two_pos
    have hexp : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) ≤ 1 := by
      have hprod : (0 : ℝ) ≤ (Real.pi * t / 2) * (z ^ 2).re := mul_nonneg hA.le hzs.le
      rw [Real.exp_le_one_iff, neg_mul]
      linarith
    rw [aux_norm_erf7711 z ht0, ← Real.sqrt_eq_rpow]
    have hnum : Real.sqrt t * Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) ≤ Real.sqrt t :=
      by nlinarith [Real.sqrt_nonneg t, Real.exp_pos (-(Real.pi * t / 2) * (z ^ 2).re)]
    exact div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ t ^ 2 + 1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z _
    have h1 : HasDerivAt (fun w : ℂ => -(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2)
        (-(Real.pi : ℂ) * z * (t : ℂ)) z := by
      have h := (((hasDerivAt_pow 2 z).const_mul (-(Real.pi : ℂ))).mul_const (t : ℂ)).div_const 2
      convert h using 1
      push_cast
      ring
    have h2 := ((h1.cexp).const_mul ((Real.sqrt t : ℂ))).div_const ((t : ℂ) ^ 2 + 1)
    convert h2 using 1
    ring
  · intro z₀ hz₀
    obtain ⟨r, hr, δ, hδ, hball⟩ := aux_openSector_ball hz₀
    have hb : (0 : ℝ) < Real.pi * δ / 2 := div_pos (mul_pos hπ hδ) two_pos
    refine ⟨r, hr, fun t : ℝ => (Real.pi * (‖z₀‖ + r)) *
      (Real.exp (-(Real.pi * δ / 2) * t) * t ^ (-(1 : ℝ) / 2)),
      (integrableOn_exp_neg_mul_rpow_Ioi (Real.pi * δ / 2) (-(1 : ℝ) / 2) hb
        (by norm_num)).const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hzb
    have ht0 : (0 : ℝ) < t := ht
    have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    obtain ⟨hδz, hnz⟩ := hball z hzb
    have hsplit : ((Real.sqrt t : ℂ) * (-(Real.pi : ℂ) * z * (t : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2))) / ((t : ℂ) ^ 2 + 1)
        = (-(Real.pi : ℂ) * z) *
            (((Real.sqrt t : ℂ) * ((t : ℂ) *
              Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2))) / ((t : ℂ) ^ 2 + 1)) := by
      ring
    have hinner : ‖((Real.sqrt t : ℂ) * ((t : ℂ) *
          Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2))) / ((t : ℂ) ^ 2 + 1)‖
        = Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) * (Real.sqrt t * t / (t ^ 2 + 1)) := by
      have hnum : -(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2
          = ((-(Real.pi * t / 2) : ℝ) : ℂ) * z ^ 2 := by push_cast; ring
      have hden : ((t : ℂ) ^ 2 + 1) = ((t ^ 2 + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_div, norm_mul, norm_mul, hnum, hden, Complex.norm_exp, Complex.re_ofReal_mul,
        Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hst, abs_of_pos ht0,
        abs_of_pos (by positivity : (0 : ℝ) < t ^ 2 + 1)]
      ring
    rw [hsplit, norm_mul, hinner, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]
    have hexpmono : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re)
        ≤ Real.exp (-(Real.pi * δ / 2) * t) := by
      refine Real.exp_le_exp.mpr ?_
      have h := mul_le_mul_of_nonneg_right hδz ht0.le
      have h2 : (Real.pi / 2) * (δ * t) ≤ (Real.pi / 2) * ((z ^ 2).re * t) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      nlinarith [h2]
    have hrpow : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg ht0.le,
        ← Real.sqrt_eq_rpow]
    have hfrac : Real.sqrt t * t / (t ^ 2 + 1) ≤ (Real.sqrt t)⁻¹ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2 + 1), inv_eq_one_div,
        div_mul_eq_mul_div, le_div_iff₀ hst]
      nlinarith [Real.mul_self_sqrt ht0.le, Real.sqrt_nonneg t]
    rw [hrpow]
    have hA : Real.pi * ‖z‖ ≤ Real.pi * (‖z₀‖ + r) := mul_le_mul_of_nonneg_left hnz hπ.le
    have hB : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) * (Real.sqrt t * t / (t ^ 2 + 1))
        ≤ Real.exp (-(Real.pi * δ / 2) * t) * (Real.sqrt t)⁻¹ := by
      have h1 : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) * (Real.sqrt t * t / (t ^ 2 + 1))
          ≤ Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) * (Real.sqrt t)⁻¹ :=
        mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le
      have h2 : Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) * (Real.sqrt t)⁻¹
          ≤ Real.exp (-(Real.pi * δ / 2) * t) * (Real.sqrt t)⁻¹ :=
        mul_le_mul_of_nonneg_right hexpmono (by positivity)
      linarith
    have hBnn : (0 : ℝ) ≤ Real.exp (-(Real.pi * t / 2) * (z ^ 2).re) *
        (Real.sqrt t * t / (t ^ 2 + 1)) := by positivity
    have hAnn : (0 : ℝ) ≤ Real.pi * (‖z₀‖ + r) :=
      mul_nonneg hπ.le (add_nonneg (norm_nonneg z₀) hr.le)
    exact le_trans (mul_le_mul_of_nonneg_right hA hBnn) (mul_le_mul_of_nonneg_left hB hAnn)

open FLMF.Fresnel in
/-- **DLMF 7.7.11**: `g(z) = (1/(π√2)) ∫₀^∞ (√t e^{-π z² t/2})/(t²+1) dt`, for
complex `z` with `|ph z| ≤ π/4`, `g = cfresnelAuxG` the complex Fresnel
auxiliary (7.2.11).

DAG: E-7.7.11.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_11_dlmf {z : ℂ} (hz : |Complex.arg z| ≤ Real.pi / 4) :
    cfresnelAuxG z =
      (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1) := by
  -- Same route as `erf_7_7_10_dlmf`, with the sector-uniform dominant `t^{1/2}/(t²+1)`.
  have hπ := Real.pi_pos
  have hS : |z.im| ≤ z.re := aux_abs_im_le_re_of_arg hz
  have hdom1 : IntegrableOn (fun t : ℝ => t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1)) (Ioi (0 : ℝ)) :=
    aux_integrable_rpow_div (by norm_num) (by norm_num)
  have hbnd : ∀ u : ℂ, 0 ≤ (u ^ 2).re → ∀ t : ℝ, 0 < t →
      ‖((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2)) /
        ((t : ℂ) ^ 2 + 1)‖ ≤ t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1) := by
    intro u hu t ht0
    have hA : (0 : ℝ) < Real.pi * t / 2 := div_pos (mul_pos hπ ht0) two_pos
    have hexp : Real.exp (-(Real.pi * t / 2) * (u ^ 2).re) ≤ 1 := by
      have hprod : (0 : ℝ) ≤ (Real.pi * t / 2) * (u ^ 2).re := mul_nonneg hA.le hu
      rw [Real.exp_le_one_iff, neg_mul]
      linarith
    rw [aux_norm_erf7711 u ht0, ← Real.sqrt_eq_rpow]
    have hnum : Real.sqrt t * Real.exp (-(Real.pi * t / 2) * (u ^ 2).re) ≤ Real.sqrt t := by
      nlinarith [Real.sqrt_nonneg t, Real.exp_pos (-(Real.pi * t / 2) * (u ^ 2).re)]
    exact div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ t ^ 2 + 1)
  have hopen : ∀ w : ℂ, |w.im| < w.re →
      cfresnelAuxG w = (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1) := by
    have hRHS : AnalyticOnNhd ℂ
        (fun w : ℂ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
          ∫ t in Ioi (0 : ℝ),
            ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * w ^ 2 * (t : ℂ) / 2)) /
              ((t : ℂ) ^ 2 + 1))
        {w : ℂ | |w.im| < w.re} := by
      have hc : AnalyticOnNhd ℂ
          (fun _ : ℂ => (1 / ((Real.pi : ℂ) * (Real.sqrt 2 : ℂ)))) {w : ℂ | |w.im| < w.re} :=
        fun w _ => analyticAt_const
      exact hc.mul aux_analyticOnNhd_erf7711
    refine aux_eq_of_analytic_of_real aux_openSector_isPreconnected (by simp)
      (fun w _ => aux_differentiable_cfresnelAuxG.analyticAt w) hRHS ?_
    intro x hx
    have hI : (∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1))
        = (((∫ t in Ioi (0 : ℝ),
            (Real.sqrt t * Real.exp (-Real.pi * x ^ 2 * t / 2)) / (t ^ 2 + 1)) : ℝ) : ℂ) := by
      have hcong : (∫ t in Ioi (0 : ℝ),
            ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2 * (t : ℂ) / 2)) /
              ((t : ℂ) ^ 2 + 1))
          = ∫ t in Ioi (0 : ℝ),
              (((Real.sqrt t * Real.exp (-Real.pi * x ^ 2 * t / 2)) / (t ^ 2 + 1) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        push_cast
        ring
      rw [hcong]
      exact _root_.integral_complex_ofReal
    rw [aux_cfresnelAuxG_ofReal, hI, erf_7_7_11 hx.le]
    push_cast
    ring
  rcases lt_or_eq_of_le hS with hlt | heq
  · exact hopen z hlt
  set w : ℕ → ℂ := fun n => z + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) with hwdef
  have hwre : ∀ n : ℕ, (w n).re = z.re + 1 / ((n : ℝ) + 1) := by
    intro n; simp only [hwdef, Complex.add_re, Complex.ofReal_re]
  have hwim : ∀ n : ℕ, (w n).im = z.im := by
    intro n; simp only [hwdef, Complex.add_im, Complex.ofReal_im, add_zero]
  have hwmem : ∀ n : ℕ, |(w n).im| < (w n).re := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [hwim, hwre]
    linarith [hS]
  have hwt : Tendsto w atTop (𝓝 z) := by
    have h : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def] using h2
    simpa [hwdef] using h.const_add z
  have hlhs : Tendsto (fun n : ℕ => cfresnelAuxG (w n)) atTop (𝓝 (cfresnelAuxG z)) :=
    (aux_differentiable_cfresnelAuxG.continuous.tendsto z).comp hwt
  have hInt : Tendsto
      (fun n : ℕ => ∫ t in Ioi (0 : ℝ),
        ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2)) /
          ((t : ℂ) ^ 2 + 1)) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ),
        ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2)) /
          ((t : ℂ) ^ 2 + 1))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun t : ℝ => t ^ ((1 : ℝ) / 2) / (t ^ 2 + 1))
      (fun n => aux_meas7711 (by fun_prop)) hdom1 (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hzs : (0 : ℝ) ≤ ((w n) ^ 2).re := by
        rw [aux_sq_re]
        have h := hwmem n
        nlinarith [abs_nonneg (w n).im, sq_abs (w n).im]
      exact hbnd (w n) hzs t ht0
    · filter_upwards with t
      have hc : Continuous (fun u : ℂ =>
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * u ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1)) := by fun_prop
      exact (hc.tendsto z).comp hwt
  have hrhs : Tendsto
      (fun n : ℕ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1)) atTop
      (𝓝 ((1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1))) := hInt.const_mul _
  have hcongr : (fun n : ℕ => cfresnelAuxG (w n))
      = fun n : ℕ => (1 / ((Real.pi : ℂ) * Real.sqrt 2)) *
        ∫ t in Ioi (0 : ℝ),
          ((Real.sqrt t : ℂ) * Complex.exp (-(Real.pi : ℂ) * (w n) ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1) := by
    funext n
    exact hopen (w n) (hwmem n)
  rw [hcongr] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

-- DLMF 7.7.12 (deferred): `g(z) + i f(z) = ∫_z^∞ e^{(π i /2)(z²-t²)} dt` along a
--   complex path. Intrinsically complex (combines `f`,`g` with `i`, complex
--   contour from `z` to `∞`); no real specialization. Deferred.

end FLMF.Error

namespace FLMF.Fresnel

open MeasureTheory Filter
open scoped Topology

/-! ## Mellin–Barnes route to DLMF 7.7.13 / 7.7.14

The four-Γ Barnes integrand is turned into the DLMF 7.7.10/7.7.11 half-line
integral by: Legendre duplication `Γ(s)Γ(s+½) = 2^{1-2s}√π Γ(2s)`, Euler's Beta
integral `Γ(s+1-a)Γ(a-s) = B(s+1-a, a-s)` pushed to `(0,∞)` by `u = 1/(1+v²)`,
Fubini, and the Mellin–Barnes representation of `e^{-x}` for *complex* `x` with
`Re x > 0` (`aux_mb_barnes_exp_cpow`, obtained from Mathlib's real
`mellin_barnes_exp` by analytic continuation in `x`).
-/

section MellinBarnesRoute

open Complex Set
open scoped Real

/-! ## Step W1 — `e^{-x} = (1/2π) ∫_ℝ x^{-(σ+iy)} Γ(σ+iy) dy` for complex `x`, `Re x > 0` -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Packaged vertical decay of `Γ` on the line `Re s = σ`. -/
theorem aux_mb_gamma_line_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ N * Real.exp (-(π / 2 * |y|)) := by
  set N : ℕ := ⌈σ⌉₊ with hN
  have hσN : σ < (N : ℝ) + 1 / 2 := by
    have := Nat.le_ceil σ
    simp only [hN]
    linarith
  refine ⟨Real.sqrt (2 * π) * (Real.Gamma σ / Real.Gamma ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1) ^ N,
    N, ?_, ?_⟩
  · have h1 : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσ
    have h2 : 0 < Real.Gamma ((N : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  · intro y
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    have him : ((σ : ℂ) + y * I).im = y := by simp
    have hz : 0 < ((σ : ℂ) + y * I).re := by rw [hre]; exact hσ
    have hN' : ((σ : ℂ) + y * I).re < (N : ℝ) + 1 / 2 := by rw [hre]; exact hσN
    have h := FLMF.MellinBarnes.gamma_vertical_exp_bound hz hN'
    rw [hre, him] at h
    refine h.trans_eq ?_
    rw [mul_pow]
    ring_nf

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The Barnes integrand for `e^{-x}`. -/
noncomputable def aux_mb_bxF (σ : ℝ) (x : ℂ) (y : ℝ) : ℂ :=
  x ^ (-((σ : ℂ) + y * I)) * Complex.Gamma ((σ : ℂ) + y * I)

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Its `x`-derivative. -/
noncomputable def aux_mb_bxF' (σ : ℝ) (x : ℂ) (y : ℝ) : ℂ :=
  (-((σ : ℂ) + y * I)) * x ^ (-((σ : ℂ) + y * I) - 1) * Complex.Gamma ((σ : ℂ) + y * I)

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_hasDerivAt_bxF {σ : ℝ} {x : ℂ} (hx : 0 < x.re) (y : ℝ) :
    HasDerivAt (fun z : ℂ => aux_mb_bxF σ z y) (aux_mb_bxF' σ x y) x := by
  have hslit : x ∈ Complex.slitPlane := Or.inl hx
  have h := (Complex.hasStrictDerivAt_cpow_const (c := -((σ : ℂ) + y * I)) hslit).hasDerivAt
  simpa [aux_mb_bxF, aux_mb_bxF', mul_comm, mul_assoc] using h.mul_const (Complex.Gamma ((σ : ℂ) + y * I))

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- On a ball inside the right half-plane, `arg` is bounded away from `π/2`. -/
theorem aux_mb_arg_bound_of_ball {x₀ : ℂ} (hx₀ : 0 < x₀.re) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < π / 2 ∧ ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Metric.ball x₀ (x₀.re / 2), m ≤ ‖x‖ ∧ |Complex.arg x| ≤ θ := by
  set m : ℝ := x₀.re / 2 with hm
  set M : ℝ := ‖x₀‖ + x₀.re / 2 with hM
  have hm0 : 0 < m := by rw [hm]; linarith
  have hM0 : 0 < M := by
    have : 0 ≤ ‖x₀‖ := norm_nonneg _
    rw [hM]; linarith
  refine ⟨Real.arccos (m / M), Real.arccos_nonneg _, Real.arccos_lt_pi_div_two.mpr (by positivity),
    m, hm0, ?_⟩
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hre : m ≤ x.re := by
    have h2 : |(x - x₀).re| ≤ ‖x - x₀‖ := Complex.abs_re_le_norm _
    have h3 : |x.re - x₀.re| < x₀.re / 2 := by
      simpa [Complex.sub_re] using lt_of_le_of_lt h2 hx
    have := (abs_lt.mp h3).1
    rw [hm]; linarith
  have hxn : m ≤ ‖x‖ := le_trans hre (Complex.re_le_norm x)
  have hxM : ‖x‖ ≤ M := by
    have : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      simpa using norm_add_le x₀ (x - x₀)
    rw [hM]; linarith
  refine ⟨hxn, ?_⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hxn; simp at hxn; linarith
  have hcos : Real.cos (Complex.arg x) = x.re / ‖x‖ := Complex.cos_arg hx0
  have hnormpos : 0 < ‖x‖ := lt_of_lt_of_le hm0 hxn
  have hkey : m / M ≤ Real.cos |Complex.arg x| := by
    rw [Real.cos_abs, hcos]
    rw [div_le_div_iff₀ hM0 hnormpos]
    nlinarith [hre, hxM, hm0, hnormpos]
  have habs1 : 0 ≤ |Complex.arg x| := abs_nonneg _
  have habs2 : |Complex.arg x| ≤ π := by
    have := Complex.arg_le_pi x
    have := Complex.neg_pi_lt_arg x
    rw [abs_le]; constructor <;> linarith
  calc |Complex.arg x| = Real.arccos (Real.cos |Complex.arg x|) :=
        (Real.arccos_cos habs1 habs2).symm
    _ ≤ Real.arccos (m / M) := by
        exact Real.arccos_le_arccos hkey

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Continuity of `Γ` along the vertical line `Re s = σ > 0`. -/
theorem aux_mb_continuous_gamma_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun y : ℝ => Complex.Gamma ((σ : ℂ) + y * I)) := by
  rw [continuous_iff_continuousAt]; intro y
  refine ContinuousAt.comp (g := Complex.Gamma) ?_
    (by fun_prop : ContinuousAt (fun y : ℝ => ((σ : ℂ) + y * I)) y)
  refine (Complex.differentiableAt_Gamma _ ?_).continuousAt
  intro m h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.neg_re,
    Complex.natCast_re] at hre
  have : (0 : ℝ) ≤ (m : ℝ) := by positivity
  linarith

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_continuous_bxF {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : x ≠ 0) :
    Continuous (fun y : ℝ => aux_mb_bxF σ x y) := by
  have h1 : Continuous (fun y : ℝ => x ^ (-((σ : ℂ) + y * I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hx)
  exact h1.mul (aux_mb_continuous_gamma_line hσ)

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_continuous_bxF' {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : x ≠ 0) :
    Continuous (fun y : ℝ => aux_mb_bxF' σ x y) := by
  have h1 : Continuous (fun y : ℝ => x ^ (-((σ : ℂ) + y * I) - 1)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hx)
  exact (((by fun_prop : Continuous (fun y : ℝ => (-((σ : ℂ) + y * I)))).mul h1)).mul
    (aux_mb_continuous_gamma_line hσ)

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The key sector bound: on `{‖x‖ ≥ m, |arg x| ≤ θ}` (`θ < π/2`) the Barnes integrand
and its `x`-derivative are dominated by `C (1+|y|)^N e^{-(π/2-θ)|y|}`. -/
theorem aux_mb_norm_bxF'_bound {σ : ℝ} (hσ : 0 < σ) {θ m : ℝ} (hm : 0 < m) (_hθ0 : 0 ≤ θ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : ℂ, m ≤ ‖x‖ → |Complex.arg x| ≤ θ → ∀ y : ℝ,
      ‖aux_mb_bxF' σ x y‖ ≤ C * (1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|)) := by
  obtain ⟨C₀, N, hC₀, hΓ⟩ := aux_mb_gamma_line_bound hσ
  refine ⟨C₀ * ((σ + 1) * m ^ (-σ - 1)), N + 1, by positivity, ?_⟩
  intro x hxm hxθ y
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at hxm; simp at hxm; linarith
  have hnx : 0 < ‖x‖ := lt_of_lt_of_le hm hxm
  -- cpow bound
  have hcp : ‖x ^ (-((σ : ℂ) + y * I) - 1)‖ ≤ m ^ (-σ - 1) * Real.exp (θ * |y|) := by
    have h := Complex.norm_cpow_le x (-((σ : ℂ) + y * I) - 1)
    have hre : (-((σ : ℂ) + y * I) - 1).re = -σ - 1 := by simp
    have him : (-((σ : ℂ) + y * I) - 1).im = -y := by simp
    rw [hre, him] at h
    refine h.trans ?_
    rw [div_le_iff₀ (Real.exp_pos _), mul_assoc, ← Real.exp_add]
    have h1 : ‖x‖ ^ (-σ - 1) ≤ m ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hm hxm (by linarith)
    have h2 : (0:ℝ) ≤ θ * |y| + Complex.arg x * -y := by
      have := abs_le.mp hxθ
      nlinarith [abs_nonneg y, neg_abs_le y, le_abs_self y]
    have h3 : (1 : ℝ) ≤ Real.exp (θ * |y| + Complex.arg x * -y) := Real.one_le_exp h2
    have hmp : (0:ℝ) < m ^ (-σ - 1) := Real.rpow_pos_of_pos hm _
    nlinarith
  have hlin : ‖(-((σ : ℂ) + y * I))‖ ≤ (σ + 1) * (1 + |y|) := by
    have h1 : ‖(-((σ : ℂ) + y * I))‖ = ‖((σ : ℂ) + y * I)‖ := by rw [norm_neg]
    have h2 : ‖((σ : ℂ) + y * I)‖ ≤ |σ| + |y| := by
      have := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
      simpa using this
    rw [h1]
    refine h2.trans ?_
    rw [abs_of_pos hσ]
    nlinarith [abs_nonneg y, hσ]
  have hΓy := hΓ y
  have hnn : (0:ℝ) ≤ (1 + |y|) := by positivity
  rw [aux_mb_bxF', norm_mul, norm_mul]
  have hstep : ‖(-((σ : ℂ) + y * I))‖ * ‖x ^ (-((σ : ℂ) + y * I) - 1)‖ *
      ‖Complex.Gamma ((σ : ℂ) + y * I)‖
      ≤ ((σ + 1) * (1 + |y|)) * (m ^ (-σ - 1) * Real.exp (θ * |y|)) *
        (C₀ * (1 + |y|) ^ N * Real.exp (-(π / 2 * |y|))) := by
    refine mul_le_mul (mul_le_mul hlin hcp (norm_nonneg _) (by positivity)) hΓy (norm_nonneg _)
      (by positivity)
  have hexp : Real.exp (θ * |y|) * Real.exp (-(π / 2 * |y|))
      = Real.exp (-((π / 2 - θ) * |y|)) := by
    rw [← Real.exp_add]; ring_nf
  refine hstep.trans_eq ?_
  rw [pow_succ, ← hexp]
  ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_integrable_bxF {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : 0 < x.re) :
    Integrable (aux_mb_bxF σ x) := by
  obtain ⟨C₀, N, hC₀, hΓ⟩ := aux_mb_gamma_line_bound hσ
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
  set θ : ℝ := |Complex.arg x| with hθ
  have hθlt : θ < π / 2 := by
    rw [hθ]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  set C : ℝ := ‖x‖ ^ (-σ) * C₀ with hC
  have hC0 : 0 ≤ C := by
    have : (0:ℝ) < ‖x‖ ^ (-σ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) _
    rw [hC]; positivity
  have hbnd : ∀ y : ℝ, ‖aux_mb_bxF σ x y‖ ≤ C * (1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|)) := by
    intro y
    have hcp : ‖x ^ (-((σ : ℂ) + y * I))‖ ≤ ‖x‖ ^ (-σ) * Real.exp (θ * |y|) := by
      have h := Complex.norm_cpow_le x (-((σ : ℂ) + y * I))
      have hre : (-((σ : ℂ) + y * I)).re = -σ := by simp
      have him : (-((σ : ℂ) + y * I)).im = -y := by simp
      rw [hre, him] at h
      refine h.trans ?_
      rw [div_le_iff₀ (Real.exp_pos _), mul_assoc, ← Real.exp_add]
      have h2 : (0:ℝ) ≤ θ * |y| + Complex.arg x * -y := by
        have h4 : |Complex.arg x| ≤ θ := le_of_eq hθ.symm
        have := abs_le.mp h4
        nlinarith [abs_nonneg y, neg_abs_le y, le_abs_self y]
      have h3 : (1 : ℝ) ≤ Real.exp (θ * |y| + Complex.arg x * -y) := Real.one_le_exp h2
      have hmp : (0:ℝ) < ‖x‖ ^ (-σ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx0) _
      nlinarith
    have hexp : Real.exp (θ * |y|) * Real.exp (-(π / 2 * |y|))
        = Real.exp (-((π / 2 - θ) * |y|)) := by
      rw [← Real.exp_add]; ring_nf
    rw [aux_mb_bxF, norm_mul]
    have hstep := mul_le_mul hcp (hΓ y) (norm_nonneg _)
      (by positivity : (0:ℝ) ≤ ‖x‖ ^ (-σ) * Real.exp (θ * |y|))
    refine hstep.trans_eq ?_
    rw [hC, ← hexp]; ring
  refine Integrable.mono' (g := fun y : ℝ => C * ((1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|))))
    ((FLMF.MellinBarnes.integrable_poly_mul_exp_neg_abs (by linarith : (0:ℝ) < π / 2 - θ)
      N).const_mul C)
    (aux_mb_continuous_bxF hσ hx0).aestronglyMeasurable ?_
  filter_upwards with y
  calc ‖aux_mb_bxF σ x y‖ ≤ C * (1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|)) := hbnd y
    _ = C * ((1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|))) := by ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_analytic_BX {σ : ℝ} (hσ : 0 < σ) :
    AnalyticOnNhd ℂ (fun x : ℂ => ∫ y : ℝ, aux_mb_bxF σ x y) {x : ℂ | 0 < x.re} := by
  have hU : IsOpen {x : ℂ | 0 < x.re} := isOpen_lt continuous_const Complex.continuous_re
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated (f' := aux_mb_bxF' σ) hU ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
    exact (aux_mb_continuous_bxF hσ ha0).aestronglyMeasurable
  · intro a ha; exact aux_mb_integrable_bxF hσ ha
  · intro a ha
    have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
    exact (aux_mb_continuous_bxF' hσ ha0).aestronglyMeasurable
  · filter_upwards with y a ha using aux_mb_hasDerivAt_bxF ha y
  · intro a ha
    obtain ⟨θ, hθ0, hθlt, m, hm0, hball⟩ := aux_mb_arg_bound_of_ball (show 0 < a.re from ha)
    obtain ⟨C, N, hC0, hbnd⟩ := aux_mb_norm_bxF'_bound hσ hm0 hθ0
    refine ⟨a.re / 2, by simpa using half_pos (show 0 < a.re from ha),
      fun y => C * ((1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|))),
      (FLMF.MellinBarnes.integrable_poly_mul_exp_neg_abs
        (by linarith : (0:ℝ) < π / 2 - θ) N).const_mul C, ?_⟩
    filter_upwards with y z hz
    obtain ⟨hz1, hz2⟩ := hball z hz
    calc ‖aux_mb_bxF' σ z y‖ ≤ C * (1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|)) := hbnd z hz1 hz2 y
      _ = C * ((1 + |y|) ^ N * Real.exp (-((π / 2 - θ) * |y|))) := by ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_BX_real {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ, aux_mb_bxF σ ((x : ℝ) : ℂ) y) = 2 * (π : ℂ) * Complex.exp (-(x : ℂ)) := by
  have h := FLMF.MellinBarnes.mellin_barnes_exp hσ hx
  rw [mellinInv] at h
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hsm : ((1 : ℝ) / (2 * π)) • (∫ y : ℝ, aux_mb_bxF σ ((x : ℝ) : ℂ) y)
      = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [← h]
    congr 1
  have : (∫ y : ℝ, aux_mb_bxF σ ((x : ℝ) : ℂ) y) = ((2 * π : ℝ) : ℂ) * ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [← hsm, Complex.real_smul]
    push_cast
    field_simp
  rw [this]
  push_cast
  ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Identity theorem, positive-real form (right half-plane). -/
theorem aux_mb_eq_of_analytic_rightHalfPlane {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {a : ℂ | 0 < a.re}) (hG : AnalyticOnNhd ℂ G {a : ℂ | 0 < a.re})
    (hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) :
    ∀ a : ℂ, 0 < a.re → F a = G a := by
  have hU : IsPreconnected {a : ℂ | 0 < a.re} := (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
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

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- **W1**: the Mellin–Barnes representation of `e^{-x}` for complex `x` in the open
right half-plane, on any vertical line `Re s = σ > 0`. -/
theorem aux_mb_barnes_exp_cpow {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : 0 < x.re) :
    (∫ y : ℝ, x ^ (-((σ : ℂ) + y * I)) * Complex.Gamma ((σ : ℂ) + y * I))
      = 2 * (π : ℂ) * Complex.exp (-x) := by
  have hU : IsOpen {a : ℂ | 0 < a.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : AnalyticOnNhd ℂ (fun a : ℂ => 2 * (π : ℂ) * Complex.exp (-a)) {a : ℂ | 0 < a.re} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn hU]
    exact (by fun_prop : Differentiable ℂ
      (fun a : ℂ => 2 * (π : ℂ) * Complex.exp (-a))).differentiableOn
  exact aux_mb_eq_of_analytic_rightHalfPlane (aux_mb_analytic_BX hσ) hG (fun t ht => aux_mb_BX_real hσ ht) x hx

/-! ## Step W2 — cpow helpers -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_cpow_mul_ofReal {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    (w * (r : ℂ)) ^ s = w ^ s * ((r : ℂ)) ^ s := by
  have hr0 : ((r : ℂ)) ≠ 0 := by
    simpa using hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hw hr0), Complex.cpow_def_of_ne_zero hw,
    Complex.cpow_def_of_ne_zero hr0, ← Complex.exp_add]
  congr 1
  rw [mul_comm w (r : ℂ), Complex.log_ofReal_mul hr hw, ← Complex.ofReal_log hr.le]
  ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_ofReal_sq_cpow {v : ℝ} (hv : 0 < v) (s : ℂ) :
    (((v : ℂ)) ^ 2) ^ s = (v : ℂ) ^ (2 * s) := by
  have hlog : Complex.log (v : ℂ) = ((Real.log v : ℝ) : ℂ) := (Complex.ofReal_log hv.le).symm
  have h := Complex.cpow_mul (x := (v : ℂ)) (y := (2 : ℂ)) (z := s) ?_ ?_
  · rw [h]
    congr 1
    norm_num [Complex.cpow_two]
  · rw [hlog]; simp [Real.pi_pos]
  · rw [hlog]; simp [Real.pi_pos.le]

/-! ## Step W3 — the aux_mb_master identity (chain assembly) -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The double integrand. -/
noncomputable def aux_mb_Phi (c a : ℝ) (ω : ℂ) (v t : ℝ) : ℂ :=
  Complex.Gamma (2 * ((c : ℂ) + Complex.I * t)) * ((ω * (v : ℂ)) ^ 2) ^ (-((c : ℂ) + Complex.I * t))
    * ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2))

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- For a positive real base, the complex power is `exp (log a * z)` with the *real* log. -/
private lemma aux_mb_cpow_pos_eq_exp {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a : ℝ) : ℂ) ^ z = Complex.exp ((Real.log a : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le]

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Euler's Beta integral on `(0,1)`, pushed to the half line by the substitution
`u = 1/(1+v²)`:  `B(p, 1-p) = 2 ∫₀^∞ v^{1-2p}/(1+v²) dv` for `0 < Re p < 1`. -/
theorem aux_mb_betaIntegral_eq_halfline {p : ℂ} (_hp0 : 0 < p.re) (_hp1 : p.re < 1) :
    Complex.betaIntegral p (1 - p)
      = 2 * ∫ v in Set.Ioi (0:ℝ), (v : ℂ) ^ (1 - 2*p) / (1 + (v : ℂ)^2) := by
  set f : ℝ → ℝ := fun t => 1 / (1 + t ^ 2) with hf
  set f' : ℝ → ℝ := fun t => -(2 * t) / (1 + t ^ 2) ^ 2 with hf'
  have hden : ∀ t : ℝ, (0:ℝ) < 1 + t ^ 2 := fun t => by positivity
  -- the image of `(0,∞)` under `t ↦ 1/(1+t²)` is `(0,1)`
  have himg : f '' (Set.Ioi (0:ℝ)) = Set.Ioo (0:ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : (0:ℝ) < t := ht
      have h2 : (1:ℝ) < 1 + t ^ 2 := by nlinarith
      simp only [hf, Set.mem_Ioo]
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one (hden t)]
      linarith
    · rintro ⟨hx0, hx1⟩
      have hinv : (1:ℝ) < 1 / x := by rw [lt_div_iff₀ hx0]; linarith
      refine ⟨Real.sqrt (1 / x - 1), ?_, ?_⟩
      · exact Real.sqrt_pos.mpr (by linarith)
      · simp only [hf]
        rw [Real.sq_sqrt (by linarith)]
        rw [show (1:ℝ) + (1 / x - 1) = 1 / x by ring, one_div_one_div]
  -- injectivity
  have hinj : Set.InjOn f (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    simp only [hf, one_div] at hab
    have h2 : 1 + a ^ 2 = 1 + b ^ 2 := inv_inj.mp hab
    have h4 : (a - b) * (a + b) = 0 := by nlinarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · linarith
  -- derivative
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivWithinAt f (f' t) (Set.Ioi (0:ℝ)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add (1:ℝ)
    have h2 := h1.inv (hden t).ne'
    simpa [hf, hf', one_div] using h2.hasDerivWithinAt
  -- change of variables
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioi hderiv hinj
      (fun x : ℝ => (x : ℂ) ^ (p - 1) * (1 - (x : ℂ)) ^ (1 - p - 1))
  rw [himg] at hchange
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, hchange, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  have hA : (0:ℝ) < 1 + t ^ 2 := hden t
  have hAc : (1 : ℂ) + (t:ℂ) ^ 2 ≠ 0 := by
    have h : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    push_cast at h
    exact h
  simp only [hf, hf']
  -- rewrite `1 - 1/(1+t²)` as the positive real `t²/(1+t²)`
  have h1cast : (1 : ℂ) - ((1 / (1 + t ^ 2) : ℝ) : ℂ) = ((t ^ 2 / (1 + t ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  have habs : |(-(2 * t) / (1 + t ^ 2) ^ 2)| = 2 * t / (1 + t ^ 2) ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * t),
      abs_of_pos (by positivity : (0:ℝ) < (1 + t ^ 2) ^ 2)]
  have hl1 : Real.log (1 / (1 + t ^ 2)) = -Real.log (1 + t ^ 2) := by
    rw [one_div, Real.log_inv]
  have hl2 : Real.log (t ^ 2 / (1 + t ^ 2)) = 2 * Real.log t - Real.log (1 + t ^ 2) := by
    rw [Real.log_div (by positivity) hA.ne', Real.log_pow]
    push_cast
    ring
  have hexpM : Complex.exp ((Real.log (1 + t ^ 2) : ℝ) : ℂ) = ((1 + t ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hA]
  have hexpL : Complex.exp ((Real.log t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ht0]
  rw [Complex.real_smul, habs, h1cast,
    aux_mb_cpow_pos_eq_exp (show (0:ℝ) < 1 / (1 + t ^ 2) by positivity),
    aux_mb_cpow_pos_eq_exp (show (0:ℝ) < t ^ 2 / (1 + t ^ 2) by positivity),
    aux_mb_cpow_pos_eq_exp ht0, ← Complex.exp_add]
  have hcomb : ((Real.log (1 / (1 + t ^ 2)) : ℝ) : ℂ) * (p - 1)
      + ((Real.log (t ^ 2 / (1 + t ^ 2)) : ℝ) : ℂ) * (1 - p - 1)
      = ((Real.log (1 + t ^ 2) : ℝ) : ℂ) + (-2 * p) * ((Real.log t : ℝ) : ℂ) := by
    rw [hl1, hl2]
    push_cast
    ring
  have hsplit : ((Real.log t : ℝ) : ℂ) * (1 - 2 * p)
      = ((Real.log t : ℝ) : ℂ) + (-2 * p) * ((Real.log t : ℝ) : ℂ) := by ring
  rw [hcomb, hsplit, Complex.exp_add, Complex.exp_add, hexpM, hexpL]
  push_cast
  field_simp

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Inner vertical integral: with `s = c + it` on the line `Re s = c > 0`,
`∫_ℝ Γ(2s) (w²)^{-s} dt = π e^{-w}` for `Re w > 0`. -/
theorem aux_mb_inner_eval {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ, Complex.Gamma (2*((c : ℂ) + Complex.I*t)) *
        ((w^2) ^ (-((c : ℂ) + Complex.I*t))))
      = (π : ℂ) * Complex.exp (-w) := by
  -- `Re w > 0` gives `|arg w| < π/2`, so `|2 arg w| < π`.
  have harg : |Complex.arg w| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have harg' := abs_lt.1 harg
  have hlt : -π < (2 : ℝ) * Complex.arg w := by linarith [harg'.1]
  have hle : (2 : ℝ) * Complex.arg w ≤ π := by linarith [harg'.2]
  -- the Barnes integrand on the line `Re s = 2c`
  set h : ℝ → ℂ :=
    fun y => w ^ (-(((2*c : ℝ) : ℂ) + y * I)) * Complex.Gamma (((2*c : ℝ) : ℂ) + y * I)
    with hdef
  have hpt : ∀ t : ℝ,
      Complex.Gamma (2*((c : ℂ) + Complex.I*t)) * ((w^2) ^ (-((c : ℂ) + Complex.I*t)))
        = h (2*t) := by
    intro t
    have hexp : (2 : ℂ) * -((c : ℂ) + Complex.I*t)
        = -(((2*c : ℝ) : ℂ) + ((2*t : ℝ) : ℂ) * I) := by push_cast; ring
    have e1 : ((w:ℂ)^2) ^ (-((c : ℂ) + Complex.I*t))
        = w ^ (-(((2*c : ℝ) : ℂ) + ((2*t : ℝ) : ℂ) * I)) := by
      rw [← Complex.cpow_ofNat_mul' hlt hle, hexp]
    have e2 : (2 : ℂ) * ((c : ℂ) + Complex.I*t)
        = ((2*c : ℝ) : ℂ) + ((2*t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, e2, hdef, mul_comm]
  calc (∫ t : ℝ, Complex.Gamma (2*((c : ℂ) + Complex.I*t)) *
            ((w^2) ^ (-((c : ℂ) + Complex.I*t))))
      = ∫ t : ℝ, h (2*t) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = |(2 : ℝ)⁻¹| • ∫ y : ℝ, h y := Measure.integral_comp_mul_left h 2
    _ = |(2 : ℝ)⁻¹| • (2 * (π : ℂ) * Complex.exp (-w)) := by
        rw [hdef]; rw [aux_mb_barnes_exp_cpow (by linarith : (0:ℝ) < 2*c) hw]
    _ = (π : ℂ) * Complex.exp (-w) := by
        rw [Complex.real_smul]
        norm_num
        ring

/-! ### Pointwise factor bounds -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The `Γ`-factor on the vertical line `Re s = c`, after doubling: an exponentially
decaying majorant in `|t|`, uniform in `t`. -/
theorem aux_mb_gamma_factor_bound {c : ℝ} (hc0 : 0 < c) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖Complex.Gamma (2*((c : ℂ) + Complex.I*t))‖
        ≤ C * (1 + |t|) ^ M * Real.exp (-(π * |t|)) := by
  obtain ⟨C, M, hC0, hC⟩ :=
    FLMF.MellinBarnes.gamma_vertical_exp_bound_strip (ε := 2*c) (R := 2*c) (by linarith) le_rfl
  refine ⟨C * 2 ^ M, M, by positivity, fun t => ?_⟩
  have hre : (2*((c : ℂ) + Complex.I*t)).re = 2*c := by simp
  have him : (2*((c : ℂ) + Complex.I*t)).im = 2*t := by simp
  have h := hC _ (by rw [hre]) (by rw [hre])
  rw [him] at h
  refine h.trans ?_
  have habs : |2*t| = 2 * |t| := by rw [abs_mul]; simp
  rw [habs]
  have hpow : (1 + 2*|t|) ^ M ≤ 2 ^ M * (1 + |t|) ^ M := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ M
    nlinarith [abs_nonneg t]
  have hexp : Real.exp (-(π * (2 * |t|)) / 2) = Real.exp (-(π * |t|)) := by
    congr 1; ring
  rw [hexp]
  have h1 : C * (1 + 2*|t|) ^ M ≤ C * 2 ^ M * (1 + |t|) ^ M := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow hC0
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The `cpow` factor `((ω v)²)^{-s}`, `s = c + it`: modulus at most
`(‖ω‖ v)^{-2c} · e^{2|arg ω| |t|}`. -/
theorem aux_mb_cpow_factor_bound {c : ℝ} {ω : ℂ} (hω : 0 < ω.re) {v : ℝ} (hv : 0 < v) (t : ℝ) :
    ‖((ω*(v : ℂ))^2) ^ (-((c : ℂ) + Complex.I*t))‖
      ≤ (‖ω‖ ^ (-(2*c)) * v ^ (-(2*c))) * Real.exp (2 * |ω.arg| * |t|) := by
  have hω0 : ω ≠ 0 := by
    intro h; rw [h] at hω; simp at hω
  set u : ℂ := ω * (v : ℂ) with hu_def
  have hu0 : u ≠ 0 := by
    rw [hu_def]
    exact mul_ne_zero hω0 (by exact_mod_cast hv.ne')
  have hargu : u.arg = ω.arg := by
    rw [hu_def]; exact Complex.arg_mul_real hv ω
  have hnormu : ‖u‖ = ‖ω‖ * v := by
    rw [hu_def, norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
  have hargbd : |ω.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hω)
  -- rewrite `(u^2)^w = u^(2w)`
  have hlogim : (Complex.log u * 2).im = 2 * ω.arg := by
    simp [Complex.log_im, hargu]; ring
  have hcm : u ^ ((2 : ℂ) * (-((c : ℂ) + Complex.I*t))) = (u ^ (2 : ℂ)) ^ (-((c : ℂ) + Complex.I*t)) := by
    refine Complex.cpow_mul _ ?_ ?_
    · rw [hlogim]
      have := abs_lt.mp hargbd
      linarith [this.1]
    · rw [hlogim]
      have := abs_lt.mp hargbd
      linarith [this.2]
  have hu2 : u ^ (2 : ℂ) = u ^ 2 := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  rw [← hu2, ← hcm]
  have hkey := Complex.norm_cpow_le u ((2 : ℂ) * (-((c : ℂ) + Complex.I*t)))
  have hre2 : ((2 : ℂ) * (-((c : ℂ) + Complex.I*t))).re = -(2*c) := by simp
  have him2 : ((2 : ℂ) * (-((c : ℂ) + Complex.I*t))).im = -(2*t) := by simp
  rw [hre2, him2, hargu, hnormu] at hkey
  refine hkey.trans ?_
  have hsplit : (‖ω‖ * v) ^ (-(2*c)) = ‖ω‖ ^ (-(2*c)) * v ^ (-(2*c)) :=
    Real.mul_rpow (norm_nonneg _) hv.le
  rw [hsplit]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.exp_le_exp.mpr ?_
  have h1 : ω.arg * t ≤ |ω.arg| * |t| := by
    calc ω.arg * t ≤ |ω.arg * t| := le_abs_self _
      _ = |ω.arg| * |t| := abs_mul _ _
  nlinarith

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The Beta factor, exactly. -/
theorem aux_mb_beta_factor_norm {a : ℝ} {v : ℝ} (hv : 0 < v) :
    ‖((v : ℂ) ^ ((2*a-1 : ℝ) : ℂ) / (1 + (v : ℂ)^2))‖ = v ^ (2*a-1) / (1 + v^2) := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.ofReal_re]
  congr 1
  have hden : (1 + (v : ℂ)^2) = ((1 + v^2 : ℝ) : ℂ) := by push_cast; ring
  rw [hden, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-! ### The `v`-side majorant -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- `v ↦ v^β/(1+v²)` is integrable on `(0,∞)` for `-1 < β < 1`. -/
theorem aux_mb_integrable_h {β : ℝ} (h1 : -1 < β) (h2 : β < 1) :
    Integrable (fun v : ℝ => v ^ β / (1 + v^2)) (volume.restrict (Set.Ioi (0:ℝ))) := by
  have hcont : ContinuousOn (fun v : ℝ => v ^ β / (1 + v^2)) (Set.Ioi (0:ℝ)) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ (by fun_prop) (by positivity))
    exact Real.continuousAt_rpow_const x β (Or.inl hx0.ne')
  rw [← IntegrableOn, ← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- near 0
    have hbase : IntegrableOn (fun x : ℝ => x ^ β) (Set.Ioc (0:ℝ) 1) := by
      have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (t := (1:ℝ)) zero_lt_one).mpr h1
      exact h.congr_set_ae Ioo_ae_eq_Ioc.symm
    refine Integrable.mono' hbase
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hv0 : 0 < v := hv.1
    have hpos : 0 < v ^ β := Real.rpow_pos_of_pos hv0 β
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hpos, sq_nonneg v]
  · -- near ∞
    have hbase : IntegrableOn (fun x : ℝ => x ^ (β - 2)) (Set.Ioi (1:ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hbase
      ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv1 : (1:ℝ) < v := hv
    have hv0 : 0 < v := by linarith
    have hpos : 0 < v ^ β := Real.rpow_pos_of_pos hv0 β
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have hrw : v ^ (β - 2) * (1 + v^2) = v ^ (β-2) + v ^ (β-2) * v^2 := by ring
    have hvsq : v ^ (2:ℝ) = v ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hv2 : v ^ (β - 2) * v ^ (2:ℝ) = v ^ β := by
      rw [← Real.rpow_add hv0]; congr 1; ring
    rw [hrw, ← hvsq, hv2]
    nlinarith [Real.rpow_pos_of_pos hv0 (β - 2)]

/-! ### Joint continuity -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_continuousOn_Phi {c a : ℝ} (hc0 : 0 < c) {ω : ℂ} (hω : 0 < ω.re) :
    ContinuousOn (Function.uncurry (fun t v => aux_mb_Phi c a ω v t))
      (Set.univ ×ˢ Set.Ioi (0:ℝ)) := by
  intro p hp
  have hv : (0:ℝ) < p.2 := hp.2
  refine ContinuousAt.continuousWithinAt ?_
  simp only [aux_mb_Phi]
  refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
  · refine ContinuousAt.comp (g := Complex.Gamma) ?_ (by fun_prop)
    refine (Complex.differentiableAt_Gamma _ ?_).continuousAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have : (0:ℝ) ≤ (m : ℝ) := by positivity
    linarith
  · refine ContinuousAt.cpow (by fun_prop) (by fun_prop) ?_
    rw [Complex.mem_slitPlane_iff]
    have hre : ((ω * (p.2 : ℂ))^2).re = p.2^2 * (ω.re^2 - ω.im^2) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]; ring
    have him : ((ω * (p.2 : ℂ))^2).im = 2 * p.2^2 * (ω.re * ω.im) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]; ring
    rcases eq_or_ne ω.im 0 with h | h
    · left
      rw [hre, h]
      have hs1 : (0:ℝ) < p.2^2 := by positivity
      have hs2 : (0:ℝ) < ω.re^2 := by positivity
      nlinarith
    · right; rw [him]
      have : ω.re * ω.im ≠ 0 := mul_ne_zero hω.ne' h
      positivity
  · refine ContinuousAt.div ?_ (by fun_prop) ?_
    · refine ContinuousAt.cpow (by fun_prop) (by fun_prop) ?_
      rw [Complex.mem_slitPlane_iff]
      left; simpa using hv
    · have hden : (1 + ((p.2 : ℝ) : ℂ)^2) = ((1 + p.2^2 : ℝ) : ℂ) := by push_cast; ring
      rw [hden]
      exact Complex.ofReal_ne_zero.mpr (by positivity)

/-! ### Integrability and the swap -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_integrable_Phi {c a : ℝ} (hc0 : 0 < c) (hca : c < a) (hac : a < c + 1)
    {ω : ℂ} (hω : 0 < ω.re) :
    Integrable (Function.uncurry (fun t v => aux_mb_Phi c a ω v t))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))) := by
  obtain ⟨C, M, hC0, hC⟩ := aux_mb_gamma_factor_bound hc0
  set θ : ℝ := |ω.arg| with hθ_def
  have hθ : θ < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hω)
  have hθ0 : 0 ≤ θ := abs_nonneg _
  have hrate : 0 < π - 2*θ := by linarith
  have hω0 : ω ≠ 0 := by intro h; rw [h] at hω; simp at hω
  have hωn : (0:ℝ) < ‖ω‖ := norm_pos_iff.mpr hω0
  set K : ℝ := C * ‖ω‖ ^ (-(2*c)) with hK_def
  have hK0 : 0 ≤ K := by
    rw [hK_def]; positivity
  set g : ℝ → ℝ := fun t => (1 + |t|) ^ M * Real.exp (-((π - 2*θ) * |t|)) with hg_def
  set h : ℝ → ℝ := fun v => v ^ (2*a-1-2*c) / (1 + v^2) with hh_def
  have hgint : Integrable g := FLMF.MellinBarnes.integrable_poly_mul_exp_neg_abs hrate M
  have hhint : Integrable h (volume.restrict (Set.Ioi (0:ℝ))) :=
    aux_mb_integrable_h (by linarith) (by linarith)
  have hGint : Integrable (fun p : ℝ × ℝ => (K * g p.1) * h p.2)
      (volume.prod (volume.restrict (Set.Ioi (0:ℝ)))) :=
    (hgint.const_mul K).mul_prod hhint
  -- rewrite the measure as a restriction of the plain product measure
  have hmeas_eq : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))))
      = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Set.Ioi (0:ℝ)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine Integrable.mono' hGint ?_ ?_
  · rw [hmeas_eq]
    exact (aux_mb_continuousOn_Phi hc0 hω).aestronglyMeasurable
      ((MeasurableSet.univ (α := ℝ)).prod measurableSet_Ioi)
  · rw [hmeas_eq]
    filter_upwards [ae_restrict_mem ((MeasurableSet.univ (α := ℝ)).prod measurableSet_Ioi)] with p hp
    have hv : (0:ℝ) < p.2 := hp.2
    set t := p.1
    set v := p.2
    show ‖aux_mb_Phi c a ω v t‖ ≤ (K * g t) * h v
    rw [aux_mb_Phi, norm_mul, norm_mul]
    have h1 := hC t
    have h2 := aux_mb_cpow_factor_bound (c := c) hω hv t
    have h3 := aux_mb_beta_factor_norm (a := a) hv
    calc ‖Complex.Gamma (2*((c : ℂ) + Complex.I*t))‖
            * ‖((ω*(v : ℂ))^2) ^ (-((c : ℂ) + Complex.I*t))‖
            * ‖((v : ℂ) ^ ((2*a-1 : ℝ) : ℂ) / (1 + (v : ℂ)^2))‖
        ≤ (C * (1 + |t|) ^ M * Real.exp (-(π * |t|)))
            * ((‖ω‖ ^ (-(2*c)) * v ^ (-(2*c))) * Real.exp (2 * θ * |t|))
            * (v ^ (2*a-1) / (1 + v^2)) := by
          refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
            (le_of_eq h3) (norm_nonneg _) (by positivity)
      _ = (K * g t) * h v := by
          rw [hK_def, hg_def, hh_def, hθ_def]
          have he : Real.exp (-((π - 2*|ω.arg|) * |t|))
              = Real.exp (-(π * |t|)) * Real.exp (2 * |ω.arg| * |t|) := by
            rw [← Real.exp_add]; congr 1; ring
          have hr : v ^ (2*a-1-2*c) = v ^ (-(2*c)) * v ^ (2*a-1) := by
            rw [← Real.rpow_add hv]; congr 1; ring
          simp only [he, hr]
          ring

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_swap_Phi {c a : ℝ} (hc0 : 0 < c) (hca : c < a) (hac : a < c + 1)
    {ω : ℂ} (hω : 0 < ω.re) :
    (∫ t : ℝ, ∫ v in Set.Ioi (0:ℝ), aux_mb_Phi c a ω v t)
      = ∫ v in Set.Ioi (0:ℝ), ∫ t : ℝ, aux_mb_Phi c a ω v t :=
  integral_integral_swap (aux_mb_integrable_Phi hc0 hca hac hω)

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- Pointwise: the four-Γ Barnes integrand as a `v`-integral. -/
theorem aux_mb_pointwise {c a : ℝ} (_hc0 : 0 < c) (hca : c < a) (hac : a < c + 1)
    {ω : ℂ} (hω0 : ω ≠ 0) (t : ℝ) :
    (ω ^ 2 / 4) ^ (-((c : ℂ) + Complex.I * t)) * Complex.Gamma ((c : ℂ) + Complex.I * t)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - a)
        * Complex.Gamma ((a : ℂ) - ((c : ℂ) + Complex.I * t))
      = 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ), aux_mb_Phi c a ω v t := by
  set s : ℂ := (c : ℂ) + Complex.I * t with hs
  have hsre : s.re = c := by simp [hs]
  have hω2 : ω ^ 2 ≠ 0 := pow_ne_zero _ hω0
  have hω24 : ω ^ 2 / 4 ≠ 0 := by
    intro h; exact hω2 (by field_simp at h; simpa using h)
  -- Legendre duplication
  have hdup : Complex.Gamma s * Complex.Gamma (s + 1 / 2)
      = Complex.Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s) * ((Real.sqrt π : ℝ) : ℂ) :=
    Complex.Gamma_mul_Gamma_add_half s
  -- Beta
  have hu : (0 : ℝ) < (s + 1 - a).re := by simp [hs]; linarith
  have hv : (0 : ℝ) < ((a : ℂ) - s).re := by simp [hs]; linarith
  have hbeta0 := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hsum : (s + 1 - a) + ((a : ℂ) - s) = 1 := by ring
  rw [hsum, Complex.Gamma_one, one_mul] at hbeta0
  have hswap : (a : ℂ) - s = 1 - (s + 1 - a) := by ring
  have hp1 : (s + 1 - a).re < 1 := by simp [hs]; linarith
  have hbeta : Complex.Gamma (s + 1 - a) * Complex.Gamma ((a : ℂ) - s)
      = 2 * ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (1 - 2 * (s + 1 - a)) / (1 + (v : ℂ) ^ 2) := by
    rw [hbeta0, hswap] at *
    exact aux_mb_betaIntegral_eq_halfline hu hp1
  -- aux_mb_pointwise cpow algebra
  have hkey : ∀ v : ℝ, v ∈ Set.Ioi (0 : ℝ) →
      (ω ^ 2 / 4) ^ (-s) * ((2 : ℂ) ^ (1 - 2 * s)) *
          ((v : ℂ) ^ (1 - 2 * (s + 1 - a)) / (1 + (v : ℂ) ^ 2))
        = 2 * (((ω * (v : ℂ)) ^ 2) ^ (-s) *
            ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2))) := by
    intro v hv0
    have hv0' : (0 : ℝ) < v := hv0
    have hvC : ((v : ℂ)) ≠ 0 := by simpa using hv0'.ne'
    -- 2^(1-2s) = 2 * (4:ℂ)^(-s)
    have h4 : ((4 : ℂ)) ^ (-s) = (2 : ℂ) ^ (-(2 * s)) := by
      have h := aux_mb_ofReal_sq_cpow (v := (2 : ℝ)) (by norm_num) (-s)
      push_cast at h
      rw [show ((4 : ℂ)) = ((2 : ℂ)) ^ 2 by norm_num, h]
      congr 1
      ring
    have h2pow : (2 : ℂ) ^ (1 - 2 * s) = 2 * ((4 : ℂ) ^ (-s)) := by
      rw [h4, show (1 : ℂ) - 2 * s = 1 + -(2 * s) by ring,
        Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
    -- (ω²/4)^(-s) * 4^(-s) = (ω²)^(-s)
    have hsplit1 : (ω ^ 2 / 4) ^ (-s) * ((4 : ℂ) ^ (-s)) = (ω ^ 2) ^ (-s) := by
      have h := aux_mb_cpow_mul_ofReal (r := (4 : ℝ)) (by norm_num) (w := ω ^ 2 / 4) hω24 (-s)
      push_cast at h
      rw [← h, show ω ^ 2 / 4 * (4 : ℂ) = ω ^ 2 by ring]
    -- v^(1-2(s+1-a)) = v^(2a-1) * (v²)^(-s)
    have hvexp : (v : ℂ) ^ (1 - 2 * (s + 1 - a))
        = (v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) * (((v : ℂ) ^ 2) ^ (-s)) := by
      rw [aux_mb_ofReal_sq_cpow hv0' (-s), ← Complex.cpow_add _ _ hvC]
      congr 1
      push_cast
      ring
    -- (ω²)^(-s) * (v²)^(-s) = ((ωv)²)^(-s)
    have hsplit2 : (ω ^ 2) ^ (-s) * (((v : ℂ) ^ 2) ^ (-s)) = ((ω * (v : ℂ)) ^ 2) ^ (-s) := by
      have h := aux_mb_cpow_mul_ofReal (r := v ^ 2) (by positivity) (w := ω ^ 2) hω2 (-s)
      push_cast at h
      rw [← h, show ω ^ 2 * ((v : ℂ)) ^ 2 = (ω * (v : ℂ)) ^ 2 by ring]
    rw [h2pow, hvexp]
    calc (ω ^ 2 / 4) ^ (-s) * (2 * (4 : ℂ) ^ (-s)) *
            ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) * ((v : ℂ) ^ 2) ^ (-s) / (1 + (v : ℂ) ^ 2))
        = 2 * (((ω ^ 2 / 4) ^ (-s) * (4 : ℂ) ^ (-s)) * (((v : ℂ) ^ 2) ^ (-s))) *
            ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2)) := by ring
      _ = 2 * (((ω * (v : ℂ)) ^ 2) ^ (-s) *
            ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2))) := by
          rw [hsplit1, hsplit2]; ring
  -- assemble
  have hI : ((ω ^ 2 / 4) ^ (-s) * ((2 : ℂ) ^ (1 - 2 * s))) *
        (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (1 - 2 * (s + 1 - a)) / (1 + (v : ℂ) ^ 2))
      = 2 * ∫ v in Set.Ioi (0 : ℝ),
          ((ω * (v : ℂ)) ^ 2) ^ (-s) * ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hkey
  have hΦ : (∫ v in Set.Ioi (0 : ℝ), aux_mb_Phi c a ω v t)
      = Complex.Gamma (2 * s) * ∫ v in Set.Ioi (0 : ℝ),
          ((ω * (v : ℂ)) ^ 2) ^ (-s) * ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [aux_mb_Phi, ← hs]
    ring
  calc (ω ^ 2 / 4) ^ (-s) * Complex.Gamma s * Complex.Gamma (s + 1 / 2)
        * Complex.Gamma (s + 1 - a) * Complex.Gamma ((a : ℂ) - s)
      = (ω ^ 2 / 4) ^ (-s) * (Complex.Gamma s * Complex.Gamma (s + 1 / 2))
          * (Complex.Gamma (s + 1 - a) * Complex.Gamma ((a : ℂ) - s)) := by ring
    _ = (ω ^ 2 / 4) ^ (-s) * (Complex.Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s)
          * ((Real.sqrt π : ℝ) : ℂ))
          * (2 * ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (1 - 2 * (s + 1 - a)) / (1 + (v : ℂ) ^ 2)) := by
        rw [hdup, hbeta]
    _ = 2 * ((Real.sqrt π : ℝ) : ℂ) * Complex.Gamma (2 * s) *
          (((ω ^ 2 / 4) ^ (-s) * ((2 : ℂ) ^ (1 - 2 * s))) *
            (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (1 - 2 * (s + 1 - a)) / (1 + (v : ℂ) ^ 2))) := by
        ring
    _ = 2 * ((Real.sqrt π : ℝ) : ℂ) * Complex.Gamma (2 * s) *
          (2 * ∫ v in Set.Ioi (0 : ℝ),
            ((ω * (v : ℂ)) ^ 2) ^ (-s) *
              ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2))) := by rw [hI]
    _ = 4 * ((Real.sqrt π : ℝ) : ℂ) * (Complex.Gamma (2 * s) * ∫ v in Set.Ioi (0 : ℝ),
            ((ω * (v : ℂ)) ^ 2) ^ (-s) *
              ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2))) := by ring
    _ = 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ), aux_mb_Phi c a ω v t := by rw [hΦ]

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- **Master identity.** -/
theorem aux_mb_master {c a : ℝ} (hc0 : 0 < c) (hca : c < a) (hac : a < c + 1)
    {ω : ℂ} (hω : 0 < ω.re) :
    (∫ t : ℝ, (ω ^ 2 / 4) ^ (-((c : ℂ) + Complex.I * t)) * Complex.Gamma ((c : ℂ) + Complex.I * t)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - a)
        * Complex.Gamma ((a : ℂ) - ((c : ℂ) + Complex.I * t)))
      = 4 * (π : ℂ) * ((Real.sqrt π : ℝ) : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ),
            (v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) * Complex.exp (-(ω * (v : ℂ))) / (1 + (v : ℂ) ^ 2) := by
  have hω0 : ω ≠ 0 := by intro h; rw [h] at hω; simp at hω
  calc (∫ t : ℝ, (ω ^ 2 / 4) ^ (-((c : ℂ) + Complex.I * t))
          * Complex.Gamma ((c : ℂ) + Complex.I * t)
          * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
          * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - a)
          * Complex.Gamma ((a : ℂ) - ((c : ℂ) + Complex.I * t)))
      = ∫ t : ℝ, 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ), aux_mb_Phi c a ω v t :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun t => aux_mb_pointwise hc0 hca hac hω0 t))
    _ = 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ t : ℝ, ∫ v in Set.Ioi (0 : ℝ), aux_mb_Phi c a ω v t :=
        MeasureTheory.integral_const_mul _ _
    _ = 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ), ∫ t : ℝ, aux_mb_Phi c a ω v t := by
        rw [aux_mb_swap_Phi hc0 hca hac hω]
    _ = 4 * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ),
          (π : ℂ) * Complex.exp (-(ω * (v : ℂ))) *
            ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2)) := by
        congr 1
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
        have hv0 : (0 : ℝ) < v := hv
        have hwre : 0 < (ω * (v : ℂ)).re := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          exact mul_pos hω hv0
        have : (∫ t : ℝ, aux_mb_Phi c a ω v t)
            = (∫ t : ℝ, Complex.Gamma (2 * ((c : ℂ) + Complex.I * t)) *
                (((ω * (v : ℂ)) ^ 2) ^ (-((c : ℂ) + Complex.I * t)))) *
              ((v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) / (1 + (v : ℂ) ^ 2)) := by
          rw [← MeasureTheory.integral_mul_const]
          rfl
        rw [this, aux_mb_inner_eval hc0 hwre]
    _ = 4 * (π : ℂ) * ((Real.sqrt π : ℝ) : ℂ) * ∫ v in Set.Ioi (0 : ℝ),
          (v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) * Complex.exp (-(ω * (v : ℂ))) / (1 + (v : ℂ) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        ring


/-! ## Step W4 — sector facts and the reduction to DLMF 7.7.10 / 7.7.11 -/

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_re_sq_pos_of_arg {z : ℂ} (hz0 : z ≠ 0) (hz : |Complex.arg z| < π / 4) :
    0 < (z ^ 2).re := by
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  set θ := Complex.arg z with hθ
  have hre : z.re = ‖z‖ * Real.cos θ := by
    rw [hθ, Complex.cos_arg hz0]; field_simp
  have him : z.im = ‖z‖ * Real.sin θ := by
    rw [hθ, Complex.sin_arg]; field_simp
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have habs := abs_lt.mp hz
  have hc2 : 0 < Real.cos (2 * θ) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hkey : z.re ^ 2 - z.im ^ 2 = ‖z‖ ^ 2 * Real.cos (2 * θ) := by
    rw [hre, him, Real.cos_two_mul']
    ring
  rw [hsq, hkey]
  positivity

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_omega_re_pos {z : ℂ} (hz0 : z ≠ 0) (hz : |Complex.arg z| < π / 4) :
    0 < ((π : ℂ) * z ^ 2 / 2).re := by
  have h : ((π : ℂ) * z ^ 2 / 2) = ((π / 2 : ℝ) : ℂ) * z ^ 2 := by push_cast; ring
  rw [h, Complex.re_ofReal_mul]
  have := aux_mb_re_sq_pos_of_arg hz0 hz
  have := Real.pi_pos
  positivity

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
theorem aux_mb_const_identity : ((2 * π : ℝ) ^ (-(3 : ℝ) / 2)) * (2 * Real.sqrt π)
    = 1 / (π * Real.sqrt 2) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * π := by linarith
  have hsp : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrw : ((2 * π : ℝ) ^ (-(3 : ℝ) / 2)) = 1 / ((2 * π) * Real.sqrt (2 * π)) := by
    have h1 : ((2 * π : ℝ) ^ ((3 : ℝ) / 2)) = (2 * π) * Real.sqrt (2 * π) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add h2π, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg h2π.le, h1, one_div]
  rw [hrw, Real.sqrt_mul (by norm_num) π]
  field_simp

-- no-dlmf: local restatement of an already-proven downstream surface
-- (`FLMF.Error.erf_7_7_10_dlmf`); not a display surface, see the docstring
/-- Local restatement of the half-line integral representation of the auxiliary
`f`, the sole remaining input to `cfresnel_7_7_13`.

**This statement is already PROVEN in this library**, as
`FLMF.Error.erf_7_7_10_dlmf` in `FLMF/Chapter7/IntegralReps.lean`
(a semantic-verified display surface).
It cannot be *used* here because `Ch7IntegralReps` imports this file, so
importing it back would create a module cycle.  The gap below is therefore an
**import-order gap, not a mathematical one**: the honest repair is to relocate
`cfresnel_7_7_13`/`cfresnel_7_7_14` (together with this Mellin-Barnes route) to
a module downstream of `Ch7IntegralReps`, where this `sorry` is discharged by
`exact FLMF.Error.erf_7_7_10_dlmf hz`. -/
theorem aux_mb_halfline_F (z : ℂ) (hz : |Complex.arg z| ≤ π / 4) :
    FLMF.Fresnel.cfresnelAuxF z =
      (1 / ((π : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))) *
        ∫ t in Set.Ioi (0 : ℝ),
          Complex.exp (-(π : ℂ) * z ^ 2 * (t : ℂ) / 2) /
            (((Real.sqrt t : ℝ) : ℂ) * ((t : ℂ) ^ 2 + 1)) := by
  exact FLMF.Error.erf_7_7_10_dlmf hz

-- no-dlmf: local restatement of an already-proven downstream surface
-- (`FLMF.Error.erf_7_7_11_dlmf`); not a display surface, see the docstring
/-- Local restatement of the half-line integral representation of the auxiliary
`g`, the sole remaining input to `cfresnel_7_7_14`.

**Already PROVEN in this library** as `FLMF.Error.erf_7_7_11_dlmf`
(`FLMF/Chapter7/IntegralReps.lean`, a semantic-verified display
surface); unusable here only because that module imports this one.  See `aux_mb_halfline_F` for the full note. -/
theorem aux_mb_halfline_G (z : ℂ) (hz : |Complex.arg z| ≤ π / 4) :
    FLMF.Fresnel.cfresnelAuxG z =
      (1 / ((π : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))) *
        ∫ t in Set.Ioi (0 : ℝ),
          (((Real.sqrt t : ℝ) : ℂ) * Complex.exp (-(π : ℂ) * z ^ 2 * (t : ℂ) / 2)) /
            ((t : ℂ) ^ 2 + 1) := by
  exact FLMF.Error.erf_7_7_11_dlmf hz

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- The Barnes integral equals the DLMF 7.7.10/7.7.11 half-line integral (general `a`). -/
theorem aux_mb_barnes_eq_J {z : ℂ} {c a : ℝ} (hc0 : 0 < c) (hca : c < a) (hac : a < c + 1)
    (hz0 : z ≠ 0) (hph : |Complex.arg z| < π / 4) :
    ((((2 * π : ℝ) ^ (-(3 : ℝ) / 2) : ℝ)) : ℂ) * (1 / (2 * (π : ℂ) * Complex.I)) *
      (∫ t : ℝ, (((π : ℂ) ^ 2 * z ^ 4 / 16) ^ (-((c : ℂ) + Complex.I * t))
        * Complex.Gamma ((c : ℂ) + Complex.I * t)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - a)
        * Complex.Gamma ((a : ℂ) - ((c : ℂ) + Complex.I * t))) * Complex.I)
      = (1 / ((π : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))) *
          ∫ v in Set.Ioi (0 : ℝ),
            (v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) *
              Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ))) / (1 + (v : ℂ) ^ 2) := by
  have hω : 0 < ((π : ℂ) * z ^ 2 / 2).re := aux_mb_omega_re_pos hz0 hph
  have hζ : ((π : ℂ) ^ 2 * z ^ 4 / 16) = ((π : ℂ) * z ^ 2 / 2) ^ 2 / 4 := by ring
  have hM := aux_mb_master hc0 hca hac hω
  rw [MeasureTheory.integral_mul_const]
  simp only [hζ]
  rw [hM]
  have hIne : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have hπC : ((π : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hsp : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    have h : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    simpa using h
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have h : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    simp [h]
  have hC : ((((2 * π : ℝ) ^ (-(3 : ℝ) / 2) : ℝ)) : ℂ) * (2 * ((Real.sqrt π : ℝ) : ℂ))
      = ((1 : ℂ) / ((π : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))) := by
    have h := aux_mb_const_identity
    have h2 : (((((2 * π : ℝ) ^ (-(3 : ℝ) / 2)) * (2 * Real.sqrt π) : ℝ)) : ℂ)
        = (((1 / (π * Real.sqrt 2) : ℝ)) : ℂ) := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h2
    exact h2
  set A : ℂ := ((((2 * π : ℝ) ^ (-(3 : ℝ) / 2) : ℝ)) : ℂ) with hA
  set J : ℂ := ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ) *
      Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ))) / (1 + (v : ℂ) ^ 2) with hJ
  calc A * (1 / (2 * (π : ℂ) * Complex.I)) *
        (4 * (π : ℂ) * ((Real.sqrt π : ℝ) : ℂ) * J * Complex.I)
      = (A * (2 * ((Real.sqrt π : ℝ) : ℂ))) * J := by field_simp; ring
    _ = (1 / ((π : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))) * J := by rw [hC]

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- `J` at `a = 1/4` is the DLMF 7.7.10 kernel integral. -/
theorem aux_mb_J_eq_F (z : ℂ) :
    (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ ((2 * (1/4 : ℝ) - 1 : ℝ) : ℂ) *
        Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ))) / (1 + (v : ℂ) ^ 2))
      = ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(π : ℂ) * z ^ 2 * (t : ℂ) / 2) /
          (((Real.sqrt t : ℝ) : ℂ) * ((t : ℂ) ^ 2 + 1)) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv0 : (0 : ℝ) < v := hv
  have hs : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hv0).ne'
  have hsC : ((Real.sqrt v : ℝ) : ℂ) ≠ 0 := by simpa using hs
  have hden : (1 : ℂ) + (v : ℂ) ^ 2 ≠ 0 := by
    have h : ((1 + v ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    push_cast at h; exact h
  have hR : v ^ ((2 * (1/4 : ℝ) - 1)) = 1 / Real.sqrt v := by
    rw [show (2 * (1/4 : ℝ) - 1) = -(1/2) by norm_num, Real.rpow_neg hv0.le,
      ← Real.sqrt_eq_rpow, one_div]
  have hpow : (v : ℂ) ^ ((2 * (1/4 : ℝ) - 1 : ℝ) : ℂ) = 1 / ((Real.sqrt v : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hv0.le, hR]
    push_cast
    ring
  have hexp : Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ)))
      = Complex.exp (-(π : ℂ) * z ^ 2 * (v : ℂ) / 2) := by ring_nf
  rw [hpow, hexp, show (1 : ℂ) + (v : ℂ) ^ 2 = (v : ℂ) ^ 2 + 1 by ring, one_div,
    inv_mul_eq_div, div_div]

-- no-dlmf: Mellin-Barnes route infrastructure for DLMF 7.7.13/7.7.14, no DLMF display
/-- `J` at `a = 3/4` is the DLMF 7.7.11 kernel integral. -/
theorem aux_mb_J_eq_G (z : ℂ) :
    (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ ((2 * (3/4 : ℝ) - 1 : ℝ) : ℂ) *
        Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ))) / (1 + (v : ℂ) ^ 2))
      = ∫ t in Set.Ioi (0 : ℝ), (((Real.sqrt t : ℝ) : ℂ) *
          Complex.exp (-(π : ℂ) * z ^ 2 * (t : ℂ) / 2)) / ((t : ℂ) ^ 2 + 1) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv0 : (0 : ℝ) < v := hv
  have hden : (1 : ℂ) + (v : ℂ) ^ 2 ≠ 0 := by
    have h : ((1 + v ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    push_cast at h; exact h
  have hR : v ^ ((2 * (3/4 : ℝ) - 1)) = Real.sqrt v := by
    rw [show (2 * (3/4 : ℝ) - 1) = (1/2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  have hpow : (v : ℂ) ^ ((2 * (3/4 : ℝ) - 1 : ℝ) : ℂ) = ((Real.sqrt v : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hv0.le, hR]
  have hexp : Complex.exp (-((π : ℂ) * z ^ 2 / 2 * (v : ℂ)))
      = Complex.exp (-(π : ℂ) * z ^ 2 * (v : ℂ) / 2) := by ring_nf
  rw [hpow, hexp, show (1 : ℂ) + (v : ℂ) ^ 2 = (v : ℂ) ^ 2 + 1 by ring, mul_div_assoc]

end MellinBarnesRoute

/-- Mellin–Barnes representation of the auxiliary `f` (DLMF 7.7.13), as a vertical-line
contour integral parametrized by `s = c + it`, `ds = i dt`, with `ζv = π²z⁴/16`.

Stated on the sector `z ≠ 0`, `|ph z| < π/4` — the domain of the Mellin
transforms (7.7.10/7.7.11) the representation inverts; an unrestricted `z` is
over-strong and fails at least at `z = 0` (Semantic audit; fix approved by user
2026-07-28, human_review §56 — one disposition covering the 7.7.13/7.7.14 pair).

DLMF 7.7.13.
DAG: E-7.7.13.
Numerical: N/A (contour-sector-unverified)
Verified: verified
-/
theorem cfresnel_7_7_13 {z : ℂ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1/4)
    (hz0 : z ≠ 0) (hph : |z.arg| < Real.pi / 4) :
    cfresnelAuxF z = ((Real.rpow (2*Real.pi) (-(3:ℝ)/2) : ℝ) : ℂ) * (1/(2*Real.pi*Complex.I)) *
      ∫ t : ℝ, (Complex.cpow (Real.pi^2 * z^4 / 16) (-((c:ℂ) + Complex.I*t))
        * Complex.Gamma ((c:ℂ)+Complex.I*t) * Complex.Gamma ((c:ℂ)+Complex.I*t+1/2)
        * Complex.Gamma ((c:ℂ)+Complex.I*t+3/4) * Complex.Gamma (1/4 - ((c:ℂ)+Complex.I*t))) * Complex.I := by
  have hB := aux_mb_barnes_eq_J (z := z) (c := c) (a := 1/4) hc0 hc1 (by linarith) hz0 hph
  rw [aux_mb_J_eq_F] at hB
  have hInt : (∫ t : ℝ, (((Real.pi : ℂ) ^ 2 * z ^ 4 / 16) ^ (-((c : ℂ) + Complex.I * t))
        * Complex.Gamma ((c : ℂ) + Complex.I * t)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - ((1/4 : ℝ) : ℂ))
        * Complex.Gamma ((((1/4 : ℝ)) : ℂ) - ((c : ℂ) + Complex.I * t))) * Complex.I)
      = ∫ t : ℝ, (Complex.cpow (Real.pi^2 * z^4 / 16) (-((c:ℂ) + Complex.I*t))
        * Complex.Gamma ((c:ℂ)+Complex.I*t) * Complex.Gamma ((c:ℂ)+Complex.I*t+1/2)
        * Complex.Gamma ((c:ℂ)+Complex.I*t+3/4)
        * Complex.Gamma (1/4 - ((c:ℂ)+Complex.I*t))) * Complex.I := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    have h1 : ((c : ℂ) + Complex.I * t + 1 - ((1/4 : ℝ) : ℂ))
        = (c : ℂ) + Complex.I * t + 3/4 := by push_cast; ring
    have h2 : ((((1/4 : ℝ)) : ℂ) - ((c : ℂ) + Complex.I * t))
        = 1/4 - ((c : ℂ) + Complex.I * t) := by push_cast; ring
    simp only [h1, h2]
    rfl
  rw [aux_mb_halfline_F z hph.le, ← hB, hInt]
  rfl

/-- Mellin–Barnes representation of the auxiliary `g` (DLMF 7.7.14), as a vertical-line
contour integral parametrized by `s = c + it`, `ds = i dt`, with `ζv = π²z⁴/16`.

Stated on the sector `z ≠ 0`, `|ph z| < π/4`, matching `cfresnel_7_7_13` (same
Mellin-transform provenance; the §56 disposition covers the pair — fix approved
by user 2026-07-28).

DLMF 7.7.14.
DAG: E-7.7.14.
Numerical: N/A (contour-sector-unverified)
Verified: verified
-/
theorem cfresnel_7_7_14 {z : ℂ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 3/4)
    (hz0 : z ≠ 0) (hph : |z.arg| < Real.pi / 4) :
    cfresnelAuxG z = ((Real.rpow (2*Real.pi) (-(3:ℝ)/2) : ℝ) : ℂ) * (1/(2*Real.pi*Complex.I)) *
      ∫ t : ℝ, (Complex.cpow (Real.pi^2 * z^4 / 16) (-((c:ℂ) + Complex.I*t))
        * Complex.Gamma ((c:ℂ)+Complex.I*t) * Complex.Gamma ((c:ℂ)+Complex.I*t+1/2)
        * Complex.Gamma ((c:ℂ)+Complex.I*t+1/4) * Complex.Gamma (3/4 - ((c:ℂ)+Complex.I*t))) * Complex.I := by
  have hB := aux_mb_barnes_eq_J (z := z) (c := c) (a := 3/4) hc0 hc1 (by linarith) hz0 hph
  rw [aux_mb_J_eq_G] at hB
  have hInt : (∫ t : ℝ, (((Real.pi : ℂ) ^ 2 * z ^ 4 / 16) ^ (-((c : ℂ) + Complex.I * t))
        * Complex.Gamma ((c : ℂ) + Complex.I * t)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2)
        * Complex.Gamma ((c : ℂ) + Complex.I * t + 1 - ((3/4 : ℝ) : ℂ))
        * Complex.Gamma ((((3/4 : ℝ)) : ℂ) - ((c : ℂ) + Complex.I * t))) * Complex.I)
      = ∫ t : ℝ, (Complex.cpow (Real.pi^2 * z^4 / 16) (-((c:ℂ) + Complex.I*t))
        * Complex.Gamma ((c:ℂ)+Complex.I*t) * Complex.Gamma ((c:ℂ)+Complex.I*t+1/2)
        * Complex.Gamma ((c:ℂ)+Complex.I*t+1/4)
        * Complex.Gamma (3/4 - ((c:ℂ)+Complex.I*t))) * Complex.I := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    have h1 : ((c : ℂ) + Complex.I * t + 1 - ((3/4 : ℝ) : ℂ))
        = (c : ℂ) + Complex.I * t + 1/4 := by push_cast; ring
    have h2 : ((((3/4 : ℝ)) : ℂ) - ((c : ℂ) + Complex.I * t))
        = 3/4 - ((c : ℂ) + Complex.I * t) := by push_cast; ring
    simp only [h1, h2]
    rfl
  rw [aux_mb_halfline_G z hph.le, ← hB, hInt]
  rfl

end FLMF.Fresnel

namespace FLMF.Error

open MeasureTheory Real Set Filter Topology
open scoped Real

-- no-dlmf: derivative of the Fresnel phase (support for 7.7.15/7.7.16)
private lemma aux_theta_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.pi * v ^ 2 / 2) (Real.pi * u) u := by
  have h := ((hasDerivAt_pow 2 u).const_mul Real.pi).div_const 2
  convert h using 1
  push_cast
  ring

-- no-dlmf: integrability of `e^{-bu}·osc` on (0,∞) (support for 7.7.15/7.7.16)
private lemma aux_int_exp_osc {b : ℝ} (hb : 0 < b) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχ1 : ∀ x, |χ x| ≤ 1) :
    IntegrableOn (fun u : ℝ => Real.exp (-(b * u)) * χ (Real.pi * u ^ 2 / 2)) (Ioi (0 : ℝ)) := by
  refine (exp_neg_integrableOn_Ioi 0 hb).mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (by fun_prop)).mul
      (hχc.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with u
    calc ‖Real.exp (-(b * u)) * χ (Real.pi * u ^ 2 / 2)‖
        = Real.exp (-(b * u)) * |χ (Real.pi * u ^ 2 / 2)| := by
          rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      _ ≤ Real.exp (-(b * u)) * 1 := by gcongr; exact hχ1 _
      _ = Real.exp (-b * u) := by rw [mul_one, neg_mul]

-- no-dlmf: integrability of `πu·e^{-bu}` on (0,∞) (support for 7.7.15/7.7.16)
private lemma aux_int_uexp {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => Real.pi * u * Real.exp (-(b * u))) (Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun x : ℝ => Real.pi * (Real.exp (-b * x) * x ^ (1 : ℝ)))
      (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_mul_rpow_Ioi b 1 hb (by norm_num)).const_mul Real.pi
  refine IntegrableOn.congr_fun h (fun u hu => ?_) measurableSet_Ioi
  rw [Real.rpow_one, neg_mul]
  ring

-- no-dlmf: integrability of `πu·e^{-bu}·osc` on (0,∞) (support for 7.7.15/7.7.16)
private lemma aux_int_uexp_osc {b : ℝ} (hb : 0 < b) {χ : ℝ → ℝ} (hχc : Continuous χ)
    (hχ1 : ∀ x, |χ x| ≤ 1) :
    IntegrableOn (fun u : ℝ => Real.pi * u * (Real.exp (-(b * u)) * χ (Real.pi * u ^ 2 / 2)))
      (Ioi (0 : ℝ)) := by
  refine (aux_int_uexp hb).mono' ?_ ?_
  · exact ((continuous_const.mul continuous_id).mul ((Real.continuous_exp.comp (by fun_prop)).mul
      (hχc.comp (by fun_prop)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    calc ‖Real.pi * u * (Real.exp (-(b * u)) * χ (Real.pi * u ^ 2 / 2))‖
        = Real.pi * u * (Real.exp (-(b * u)) * |χ (Real.pi * u ^ 2 / 2)|) := by
          rw [Real.norm_eq_abs]
          simp only [abs_mul, Real.abs_exp]
          rw [abs_of_pos Real.pi_pos, abs_of_pos hu0]
      _ ≤ Real.pi * u * (Real.exp (-(b * u)) * 1) := by
          gcongr
          exact hχ1 _
      _ = Real.pi * u * Real.exp (-(b * u)) := by rw [mul_one]

-- no-dlmf: decay of the Laplace-pair integrals as `w → ∞` (support for 7.7.15/7.7.16)
private lemma aux_L_tendsto_zero {χ : ℝ → ℝ} (hχ1 : ∀ x, |χ x| ≤ 1) :
    Tendsto (fun w : ℝ => ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun w : ℝ => 1 / (Real.pi * w)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    have hb : 0 < Real.pi * w := by positivity
    have h1 : ‖∫ u in Ioi (0 : ℝ), Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2)‖
        ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-(Real.pi * w) * u) := by
      refine norm_integral_le_of_norm_le (exp_neg_integrableOn_Ioi 0 hb) ?_
      filter_upwards with u
      calc ‖Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2)‖
          = Real.exp (-(Real.pi * w * u)) * |χ (Real.pi * u ^ 2 / 2)| := by
            rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        _ ≤ Real.exp (-(Real.pi * w * u)) * 1 := by gcongr; exact hχ1 _
        _ = Real.exp (-(Real.pi * w) * u) := by rw [mul_one, neg_mul]
    have h2 : (∫ u in Ioi (0 : ℝ), Real.exp (-(Real.pi * w) * u)) = 1 / (Real.pi * w) := by
      have h := integral_exp_neg_mul_rpow_Ioi (Real.pi * w) 0 hb (by norm_num)
      simp only [Real.rpow_zero, mul_one, zero_add, Real.rpow_one, Real.Gamma_one] at h
      simpa using h
    rw [h2] at h1
    exact h1
  · exact Tendsto.div_atTop tendsto_const_nhds
      (Tendsto.const_mul_atTop Real.pi_pos tendsto_id)

-- no-dlmf: w-derivative of the Laplace-pair integrals (support for 7.7.15/7.7.16)
private lemma aux_L_hasDerivAt {χ : ℝ → ℝ} (hχc : Continuous χ) (hχ1 : ∀ x, |χ x| ≤ 1)
    {w₀ : ℝ} (hw : 0 < w₀) :
    HasDerivAt (fun w : ℝ => ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2))
      (-∫ u in Ioi (0 : ℝ),
        Real.pi * u * (Real.exp (-(Real.pi * w₀ * u)) * χ (Real.pi * u ^ 2 / 2))) w₀ := by
  have hπ := Real.pi_pos
  have hb0 : 0 < Real.pi * w₀ := by positivity
  have hb2 : 0 < Real.pi * (w₀ / 2) := by positivity
  have hball : Metric.ball w₀ (w₀ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioi 0))
      (F := fun w u => Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2))
      (F' := fun w u => -(Real.pi * u * (Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2))))
      (bound := fun u => Real.pi * u * Real.exp (-(Real.pi * (w₀ / 2) * u)))
      hball
      (Eventually.of_forall fun w => ((Real.continuous_exp.comp (by fun_prop)).mul
        (hχc.comp (by fun_prop))).aestronglyMeasurable)
      (aux_int_exp_osc hb0 hχc hχ1)
      ((((continuous_const.mul continuous_id).mul ((Real.continuous_exp.comp (by fun_prop)).mul
        (hχc.comp (by fun_prop)))).neg).aestronglyMeasurable)
      ?_ (aux_int_uexp hb2) ?_
  · have hval : (∫ u in Ioi (0 : ℝ),
        -(Real.pi * u * (Real.exp (-(Real.pi * w₀ * u)) * χ (Real.pi * u ^ 2 / 2))))
        = -∫ u in Ioi (0 : ℝ),
            Real.pi * u * (Real.exp (-(Real.pi * w₀ * u)) * χ (Real.pi * u ^ 2 / 2)) :=
      integral_neg _
    rw [← hval]
    exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hwmem
    have hu0 : (0 : ℝ) < u := hu
    have hw2 : w₀ / 2 ≤ w := by
      have h := Metric.mem_ball.mp hwmem
      rw [Real.dist_eq] at h
      have h' := abs_lt.mp h
      linarith [h'.1]
    calc ‖-(Real.pi * u * (Real.exp (-(Real.pi * w * u)) * χ (Real.pi * u ^ 2 / 2)))‖
        = Real.pi * u * (Real.exp (-(Real.pi * w * u)) * |χ (Real.pi * u ^ 2 / 2)|) := by
          rw [Real.norm_eq_abs, abs_neg]
          simp only [abs_mul, Real.abs_exp]
          rw [abs_of_pos Real.pi_pos, abs_of_pos hu0]
      _ ≤ Real.pi * u * (Real.exp (-(Real.pi * (w₀ / 2) * u)) * 1) := by
          gcongr
          exact hχ1 _
      _ = Real.pi * u * Real.exp (-(Real.pi * (w₀ / 2) * u)) := by rw [mul_one]
  · filter_upwards with u
    intro w hwmem
    have h1 : HasDerivAt (fun w : ℝ => -(Real.pi * w * u)) (-(Real.pi * u)) w := by
      have h := (((hasDerivAt_id w).const_mul Real.pi).mul_const u).neg
      simpa using h
    have h2 := h1.exp.mul_const (χ (Real.pi * u ^ 2 / 2))
    convert h2 using 1
    ring

-- no-dlmf: integration by parts in `u`, cosine side (support for 7.7.15/7.7.16)
private lemma aux_IBP_cos_side (w : ℝ) (hw : 0 < w) :
    (∫ u in Ioi (0 : ℝ),
        Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2)))
      = Real.pi * w * ∫ u in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2) := by
  have hπ := Real.pi_pos
  have hb : 0 < Real.pi * w := by positivity
  have hint1 : IntegrableOn
      (fun u : ℝ => Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2))
      (Ioi (0 : ℝ)) :=
    aux_int_exp_osc hb Real.continuous_sin (fun x => Real.abs_sin_le_one x)
  have hint2 : IntegrableOn
      (fun u : ℝ => Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2)))
      (Ioi (0 : ℝ)) :=
    aux_int_uexp_osc hb Real.continuous_cos (fun x => Real.abs_cos_le_one x)
  have hint1' := hint1.const_mul (-(Real.pi * w))
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.sin (Real.pi * v ^ 2 / 2))
      (-(Real.pi * w) * (Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2))
        + Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2))) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => -(Real.pi * w * v)) (-(Real.pi * w)) u := by
      have h := (((hasDerivAt_id u).const_mul (Real.pi * w))).neg
      simpa using h
    have h := h1.exp.mul ((aux_theta_hasDerivAt u).sin)
    convert h using 1
    ring
  have hcont : ContinuousWithinAt
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.sin (Real.pi * v ^ 2 / 2))
      (Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have hlim : Tendsto
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.sin (Real.pi * v ^ 2 / 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun v : ℝ => Real.pi * w * v) atTop atTop :=
      Tendsto.const_mul_atTop hb tendsto_id
    have h2 := tendsto_neg_atTop_atBot.comp h1
    have h4 := Real.tendsto_exp_atBot.comp h2
    refine squeeze_zero_norm (fun v => ?_) (h4.congr fun v => rfl)
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun u _ => hderiv u)
    (hint1'.add hint2) hlim
  rw [integral_add hint1' hint2, integral_const_mul] at hIBP
  simp only [mul_zero, neg_zero, Real.exp_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Real.sin_zero, sub_zero] at hIBP
  linarith [hIBP]

-- no-dlmf: integration by parts in `u`, sine side (support for 7.7.15/7.7.16)
private lemma aux_IBP_sin_side (w : ℝ) (hw : 0 < w) :
    (∫ u in Ioi (0 : ℝ),
        Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2)))
      = 1 - Real.pi * w * ∫ u in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2) := by
  have hπ := Real.pi_pos
  have hb : 0 < Real.pi * w := by positivity
  have hint1 : IntegrableOn
      (fun u : ℝ => Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2))
      (Ioi (0 : ℝ)) :=
    aux_int_exp_osc hb Real.continuous_cos (fun x => Real.abs_cos_le_one x)
  have hint2 : IntegrableOn
      (fun u : ℝ => Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2)))
      (Ioi (0 : ℝ)) :=
    aux_int_uexp_osc hb Real.continuous_sin (fun x => Real.abs_sin_le_one x)
  have hint1' := hint1.const_mul (-(Real.pi * w))
  have hint2' : IntegrableOn
      (fun u : ℝ =>
        -(Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2))))
      (Ioi (0 : ℝ)) := hint2.neg
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.cos (Real.pi * v ^ 2 / 2))
      (-(Real.pi * w) * (Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2))
        + -(Real.pi * u * (Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2)))) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => -(Real.pi * w * v)) (-(Real.pi * w)) u := by
      have h := (((hasDerivAt_id u).const_mul (Real.pi * w))).neg
      simpa using h
    have h := h1.exp.mul ((aux_theta_hasDerivAt u).cos)
    convert h using 1
    ring
  have hcont : ContinuousWithinAt
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.cos (Real.pi * v ^ 2 / 2))
      (Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have hlim : Tendsto
      (fun v : ℝ => Real.exp (-(Real.pi * w * v)) * Real.cos (Real.pi * v ^ 2 / 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun v : ℝ => Real.pi * w * v) atTop atTop :=
      Tendsto.const_mul_atTop hb tendsto_id
    have h2 := tendsto_neg_atTop_atBot.comp h1
    have h4 := Real.tendsto_exp_atBot.comp h2
    refine squeeze_zero_norm (fun v => ?_) (h4.congr fun v => rfl)
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun u _ => hderiv u)
    (hint1'.add hint2') hlim
  rw [integral_add hint1' hint2', integral_const_mul, integral_neg] at hIBP
  simp only [mul_zero, neg_zero, Real.exp_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, Real.cos_zero, mul_one,
    zero_sub] at hIBP
  linarith [hIBP]

-- no-dlmf: identification of the Laplace pair with (f, g) on (0,∞) via the ODE kit
lemma fresnelAux_eq_laplace_pair {z : ℝ} (hz : 0 < z) :
    fresnelAuxF z = (∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * z * u)) * Real.cos (Real.pi * u ^ 2 / 2))
    ∧ fresnelAuxG z = ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * z * u)) * Real.sin (Real.pi * u ^ 2 / 2) := by
  have hFd : ∀ y : ℝ, 0 < y → HasDerivAt
      (fun w : ℝ => ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * w * u)) * Real.cos (Real.pi * u ^ 2 / 2))
      (-Real.pi * y * ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * y * u)) * Real.sin (Real.pi * u ^ 2 / 2)) y := by
    intro y hy
    have h := aux_L_hasDerivAt Real.continuous_cos (fun x => Real.abs_cos_le_one x) hy
    rw [aux_IBP_cos_side y hy] at h
    convert h using 1
    ring
  have hGd : ∀ y : ℝ, 0 < y → HasDerivAt
      (fun w : ℝ => ∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * w * u)) * Real.sin (Real.pi * u ^ 2 / 2))
      (Real.pi * y * (∫ u in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * y * u)) * Real.cos (Real.pi * u ^ 2 / 2)) - 1) y := by
    intro y hy
    have h := aux_L_hasDerivAt Real.continuous_sin (fun x => Real.abs_sin_le_one x) hy
    rw [aux_IBP_sin_side y hy] at h
    convert h using 1
    ring
  exact fresnelAux_pair_uniqueness hFd hGd
    (aux_L_tendsto_zero (fun x => Real.abs_cos_le_one x))
    (aux_L_tendsto_zero (fun x => Real.abs_sin_le_one x)) hz

-- no-dlmf: real/narrowed restriction of DLMF 7.7.15 (DLMF states this for
-- complex a with Re a > 0); faithful surface is erf_7_7_15_dlmf
/-- Laplace–cosine integral, real specialization: for real `a > 0`,
`∫₀^∞ e^{-a t} cos(t²) dt = √(π/2)·f(a/√(2π))`, with `f = fresnelAuxF` the §7.2.10
auxiliary function.  (Corrected 2026-06-25 from the DLMF PDF — the prefactor is
`√(π/2)` (not `π/2`) and the argument is `a/√(2π)` (not `a/(2π)`); the original
source had dropped both square roots.  Verified: ∫ = 0.49397252 = RHS at a=1.3.)
-/
theorem erf_7_7_15 (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Real.cos (t ^ 2)) =
      Real.sqrt (Real.pi / 2) * fresnelAuxF (a / Real.sqrt (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  set z := a / Real.sqrt (2 * Real.pi) with hzdef
  have hs2π : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hz : 0 < z := by rw [hzdef]; positivity
  have hc : (0 : ℝ) < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  have hprod : Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity) (2 * Real.pi),
      show Real.pi / 2 * (2 * Real.pi) = Real.pi ^ 2 by ring]
    exact Real.sqrt_sq hπ.le
  have hacz : a * Real.sqrt (Real.pi / 2) = Real.pi * z := by
    have h1 : Real.pi * z * Real.sqrt (2 * Real.pi) = a * Real.pi := by
      rw [hzdef, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hs2π)]
      ring
    have h2 : a * Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = a * Real.pi := by
      linear_combination a * hprod
    exact mul_right_cancel₀ (ne_of_gt hs2π) (h2.trans h1.symm)
  have hF : fresnelAuxF z = ∫ u in Ioi (0 : ℝ),
      Real.exp (-(Real.pi * z * u)) * Real.cos (Real.pi * u ^ 2 / 2) :=
    (fresnelAux_eq_laplace_pair hz).1
  have hsub : (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Real.cos (t ^ 2))
      = Real.sqrt (Real.pi / 2) * ∫ u in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * z * u)) * Real.cos (Real.pi * u ^ 2 / 2) := by
    have h := integral_comp_mul_left_Ioi
      (fun t => Real.exp (-a * t) * Real.cos (t ^ 2)) 0 hc
    rw [mul_zero, smul_eq_mul] at h
    have h2 : (∫ u in Ioi (0 : ℝ),
        Real.exp (-a * (Real.sqrt (Real.pi / 2) * u)) *
          Real.cos ((Real.sqrt (Real.pi / 2) * u) ^ 2))
        = ∫ u in Ioi (0 : ℝ),
            Real.exp (-(Real.pi * z * u)) * Real.cos (Real.pi * u ^ 2 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      have h1 : -a * (Real.sqrt (Real.pi / 2) * u) = -(Real.pi * z * u) := by
        linear_combination (-u) * hacz
      have h2' : (Real.sqrt (Real.pi / 2) * u) ^ 2 = Real.pi * u ^ 2 / 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
        ring
      rw [h1, h2']
    rw [h2] at h
    rw [h]
    field_simp
  rw [hsub, hF]

open FLMF.Fresnel in
/-- **DLMF 7.7.15**: `∫₀^∞ e^{-a t} cos(t²) dt = √(π/2)·f(a/√(2π))`, for complex
`a` with `Re a > 0`, `f = cfresnelAuxF` the complex Fresnel auxiliary
(7.2.10), principal branch of `√·`.

DAG: E-7.7.15.
Numerical: N/A (equality)
Verified: verified
-/
theorem erf_7_7_15_dlmf {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) * (Real.cos (t ^ 2) : ℂ)) =
      ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
        cfresnelAuxF (a / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2)) := by
  -- Both sides are analytic in `a` on the right half-plane — the left by
  -- `aux_analyticOnNhd_laplace`, the right because `cfresnelAuxF` is entire — and
  -- they agree at every positive real `a` by the real specialization `erf_7_7_15`.
  have hs2 : (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    exact aux_cpow_half_ofReal (by positivity)
  have hs1 : ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) = (Real.sqrt (Real.pi / 2) : ℂ) := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
    exact aux_cpow_half_ofReal (by positivity)
  have hGdiff : Differentiable ℂ (fun b : ℂ => ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
      cfresnelAuxF (b / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2))) := by
    have hf := aux_differentiable_cfresnelAuxF
    fun_prop
  refine aux_eq_of_analytic_rightHalfPlane
    (F := fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t : ℂ)) * (Real.cos (t ^ 2) : ℂ))
    (G := fun b : ℂ => ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
      cfresnelAuxF (b / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2)))
    (aux_analyticOnNhd_laplace (M := 1) (by fun_prop) (fun t => ?_)) (fun w _ => hGdiff.analyticAt w)
    (fun x hx => ?_) a ha
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  · have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ)) * (Real.cos (t ^ 2) : ℂ))
        = ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.cos (t ^ 2) : ℝ) : ℂ) := by
      have hcong : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ)) * (Real.cos (t ^ 2) : ℂ))
          = ∫ t in Ioi (0 : ℝ), ((Real.exp (-x * t) * Real.cos (t ^ 2) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        push_cast
        ring
      rw [hcong]
      exact _root_.integral_complex_ofReal
    dsimp only
    rw [hL, erf_7_7_15 x hx, hs1, hs2,
      show ((x : ℂ) / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))
        = (((x / Real.sqrt (2 * Real.pi)) : ℝ) : ℂ) by push_cast; ring,
      aux_cfresnelAuxF_ofReal]
    push_cast
    ring

-- no-dlmf: real/narrowed restriction of DLMF 7.7.16 (DLMF states this for
-- complex a with Re a > 0); faithful surface is erf_7_7_16_dlmf
/-- Laplace–sine integral, real specialization: for real `a > 0`,
`∫₀^∞ e^{-a t} sin(t²) dt = √(π/2)·g(a/√(2π))`, with `g = fresnelAuxG` the §7.2.11
auxiliary function.  (Corrected 2026-06-25 from the DLMF PDF — same dropped
square roots as 7.7.15.  Verified: ∫ = 0.20910084 = RHS at a=1.3.)
-/
theorem erf_7_7_16 (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Real.sin (t ^ 2)) =
      Real.sqrt (Real.pi / 2) * fresnelAuxG (a / Real.sqrt (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  set z := a / Real.sqrt (2 * Real.pi) with hzdef
  have hs2π : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hz : 0 < z := by rw [hzdef]; positivity
  have hc : (0 : ℝ) < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  have hprod : Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity) (2 * Real.pi),
      show Real.pi / 2 * (2 * Real.pi) = Real.pi ^ 2 by ring]
    exact Real.sqrt_sq hπ.le
  have hacz : a * Real.sqrt (Real.pi / 2) = Real.pi * z := by
    have h1 : Real.pi * z * Real.sqrt (2 * Real.pi) = a * Real.pi := by
      rw [hzdef, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hs2π)]
      ring
    have h2 : a * Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = a * Real.pi := by
      linear_combination a * hprod
    exact mul_right_cancel₀ (ne_of_gt hs2π) (h2.trans h1.symm)
  have hG : fresnelAuxG z = ∫ u in Ioi (0 : ℝ),
      Real.exp (-(Real.pi * z * u)) * Real.sin (Real.pi * u ^ 2 / 2) :=
    (fresnelAux_eq_laplace_pair hz).2
  have hsub : (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Real.sin (t ^ 2))
      = Real.sqrt (Real.pi / 2) * ∫ u in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * z * u)) * Real.sin (Real.pi * u ^ 2 / 2) := by
    have h := integral_comp_mul_left_Ioi
      (fun t => Real.exp (-a * t) * Real.sin (t ^ 2)) 0 hc
    rw [mul_zero, smul_eq_mul] at h
    have h2 : (∫ u in Ioi (0 : ℝ),
        Real.exp (-a * (Real.sqrt (Real.pi / 2) * u)) *
          Real.sin ((Real.sqrt (Real.pi / 2) * u) ^ 2))
        = ∫ u in Ioi (0 : ℝ),
            Real.exp (-(Real.pi * z * u)) * Real.sin (Real.pi * u ^ 2 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      have h1 : -a * (Real.sqrt (Real.pi / 2) * u) = -(Real.pi * z * u) := by
        linear_combination (-u) * hacz
      have h2' : (Real.sqrt (Real.pi / 2) * u) ^ 2 = Real.pi * u ^ 2 / 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
        ring
      rw [h1, h2']
    rw [h2] at h
    rw [h]
    field_simp
  rw [hsub, hG]

open FLMF.Fresnel in
/-- **DLMF 7.7.16**: `∫₀^∞ e^{-a t} sin(t²) dt = √(π/2)·g(a/√(2π))`, for complex
`a` with `Re a > 0`, `g = cfresnelAuxG` the complex Fresnel auxiliary
(7.2.11), principal branch of `√·`.

DAG: E-7.7.16.
Numerical: N/A (equality)
Verified: verified
-/
theorem erf_7_7_16_dlmf {a : ℂ} (ha : 0 < a.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-a * (t : ℂ)) * (Real.sin (t ^ 2) : ℂ)) =
      ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
        cfresnelAuxG (a / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2)) := by
  -- Identical to `erf_7_7_15_dlmf` with the sine kernel and the auxiliary `g`.
  have hs2 : (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2) = (Real.sqrt (2 * Real.pi) : ℂ) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    exact aux_cpow_half_ofReal (by positivity)
  have hs1 : ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) = (Real.sqrt (Real.pi / 2) : ℂ) := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring]
    exact aux_cpow_half_ofReal (by positivity)
  have hGdiff : Differentiable ℂ (fun b : ℂ => ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
      cfresnelAuxG (b / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2))) := by
    have hf := aux_differentiable_cfresnelAuxG
    fun_prop
  refine aux_eq_of_analytic_rightHalfPlane
    (F := fun b : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-b * (t : ℂ)) * (Real.sin (t ^ 2) : ℂ))
    (G := fun b : ℂ => ((Real.pi : ℂ) / 2) ^ ((1 : ℂ) / 2) *
      cfresnelAuxG (b / (2 * (Real.pi : ℂ)) ^ ((1 : ℂ) / 2)))
    (aux_analyticOnNhd_laplace (M := 1) (by fun_prop) (fun t => ?_)) (fun w _ => hGdiff.analyticAt w)
    (fun x hx => ?_) a ha
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  · have hL : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ)) * (Real.sin (t ^ 2) : ℂ))
        = ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.sin (t ^ 2) : ℝ) : ℂ) := by
      have hcong : (∫ t in Ioi (0 : ℝ), Complex.exp (-(x : ℂ) * (t : ℂ)) * (Real.sin (t ^ 2) : ℂ))
          = ∫ t in Ioi (0 : ℝ), ((Real.exp (-x * t) * Real.sin (t ^ 2) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        push_cast
        ring
      rw [hcong]
      exact _root_.integral_complex_ofReal
    dsimp only
    rw [hL, erf_7_7_16 x hx, hs1, hs2,
      show ((x : ℂ) / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))
        = (((x / Real.sqrt (2 * Real.pi)) : ℝ) : ℂ) by push_cast; ring,
      aux_cfresnelAuxG_ofReal]
    push_cast
    ring

end FLMF.Error
