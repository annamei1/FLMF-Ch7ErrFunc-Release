import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.Faddeeva
import FLMF.Chapter7.ContinuedFractions
import FLMF.Chapter7.InverseErf
import FLMF.Support.ParametricIntegralAnalytic
import FLMF.Chapter7.ErfcLeading
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Additional complex/Gaussian error-function identities (DLMF §7.7, §7.9, §7.14)

Extra error-function entries that depend on the complex `cerf`/`cerfc` keystone,
the Faddeeva function `w`, and the continued-fraction machinery of §7.9:

* `cdawson`   — the complex Dawson integral `F(z) = (√π/2) e^{-z²} erfi(z)`,
  built from the complex error function (honest, `sorry`-free definition).
* `erf_7_7_3` — Gaussian integral `∫₀^∞ e^{-at²+2izt} dt` (complex form).
* `erf_7_7_7` / `erf_7_7_7_dlmf` — two-sided Gaussian integral over `(x,∞)`,
  real-domain instance and DLMF's full complex-sector surface.
* `erf_7_7_8` / `erf_7_7_8_dlmf` — two-sided Gaussian integral over `(0,∞)`,
  real-domain instance and DLMF's full complex-sector surface.
* `erf_7_14_1` / `erf_7_14_1_dlmf` / `erf_7_14_1_full` — `∫₀^∞ e^{2iat} erfc(bt) dt`
  via the complex Dawson integral: half-plane instance, `a ≠ 0` sector instance,
  and DLMF's full surface with the `a = 0` limiting convention.
* `erf_7_9_3` — Gautschi continued fraction for the Faddeeva function `w`.

Since `FLMF.Error.cfConv` is real-valued, the §7.9.3 convergents are built with
the complex-valued Wallis recurrence `cfNumC`/`cfDenC`/`cfConvC` imported from
`Ch7ContinuedFractions`.
-/

namespace FLMF.Error

open Real Filter Topology
open MeasureTheory Set

/-- Complex Dawson integral `F(z) = (√π/2) e^{-z²} · (-i)·erf(iz)` (DLMF 7.2.5 complex form;
F(z) = (√π/2)e^{-z²}erfi(z) with erfi(z) = -i·erf(iz)).

DLMF 7.2.5.
-/
-- DAG: E-7.2.5.
-- Verified: verified
noncomputable def cdawson (z : ℂ) : ℂ :=
  (Real.sqrt Real.pi / 2 : ℂ) * Complex.exp (-z^2) * (-Complex.I) * cerf (Complex.I * z)

/-- **DLMF 7.4.4** — the complex Dawson integral is odd: `F(-z) = -F(z)`.

The Gaussian factor `e^{-z²}` is even, and `cerf` is odd (`cerf_neg`), so the
product changes sign. This is the DLMF-faithful (complex `z`) surface of 7.4.4;
the real specialization is `erf_7_4_4` in `Error/Ch7Symmetry.lean`.

DLMF 7.4.4.
DAG: E-7.4.4.
Numerical: N/A
Verified: verified
-/
theorem cdawson_neg (z : ℂ) : cdawson (-z) = -cdawson z := by
  unfold cdawson
  have hsq : (-z) ^ 2 = z ^ 2 := by ring
  have harg : Complex.I * -z = -(Complex.I * z) := by ring
  rw [hsq, harg, cerf_neg]
  ring

/-- Gaussian integral `∫₀^∞ e^{-at²+2izt} dt = ½√(π/a) e^{-z²/a} erfc(-iz/√a)`,
valid for `ℜ a > 0` (DLMF 7.7.3).

DLMF 7.7.3.
DAG: E-7.7.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_3 {a z : ℂ} (ha : 0 < a.re) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ)))
      = (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-z^2/a)
          *cerfc (-Complex.I*z*a^(-(1:ℂ)/2)) :=
  gaussLin_integral_eq_cerfc ha

-- no-dlmf: vanishing criterion on the half-line (zero derivative on (0,∞) plus
-- vanishing limit at +∞); proof infrastructure, no DLMF identity number
private theorem eq_zero_of_hasDerivAt_zero_of_tendsto_Ioi {f : ℝ → ℝ}
    (hf : ∀ y, 0 < y → HasDerivAt f 0 y) (h0 : Tendsto f atTop (𝓝 0))
    {x : ℝ} (hx : 0 < x) : f x = 0 := by
  have hconst : ∀ y, x ≤ y → f y = f x := by
    intro y hxy
    have hcont : ContinuousOn f (Icc x y) := fun z hz =>
      ((hf z (lt_of_lt_of_le hx hz.1)).continuousAt).continuousWithinAt
    have hderiv : ∀ z ∈ Ico x y, HasDerivWithinAt f 0 (Ici z) z := fun z hz =>
      (hf z (lt_of_lt_of_le hx hz.1)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv y (right_mem_Icc.mpr hxy)
  have hlim : Tendsto f atTop (𝓝 (f x)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop x] with y hy
    exact (hconst y hy).symm
  exact tendsto_nhds_unique hlim h0

-- no-dlmf: global integrability of the two-sided Gaussian integrand
-- `e^{-a²t² - b²/t²}` (dominated by the Gaussian `e^{-a²t²}`); support
-- infrastructure for 7.7.7/7.7.8, no DLMF identity number
private theorem integrable_twoSidedGaussian {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-a^2*t^2 - b^2/t^2)) := by
  have hfm : Measurable (fun t : ℝ => Real.exp (-a^2*t^2 - b^2/t^2)) := by fun_prop
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(a^2) * t^2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine hgauss.mono' hfm.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ b^2/t^2 := by positivity
  nlinarith

-- no-dlmf: real-domain restriction (a, x positive reals, b an unconstrained
-- real) of the two-sided Gaussian integral, narrower than DLMF's complex
-- sector `|ph a| < π/4` with complex `b`; faithful surface is erf_7_7_7_dlmf
/-- Two-sided Gaussian integral over `(x,∞)`
`∫ₓ^∞ e^{-a²t² - b²/t²} dt = (√π/(4a))·(e^{2ab} erfc(ax+b/x) + e^{-2ab} erfc(ax-b/x))`,
for real `a, x > 0` and real `b` (real-domain instance). -/
theorem erf_7_7_7 {a b x : ℝ} (hx : 0 < x) (ha : 0 < a) :
    (∫ t in Set.Ioi x, Real.exp (-a^2*t^2 - b^2/t^2))
      = (Real.sqrt Real.pi/(4*a)) * (Real.exp (2*a*b)*FLMF.Error.erfc (a*x + b/x)
          + Real.exp (-2*a*b)*FLMF.Error.erfc (a*x - b/x)) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have ha' : a ≠ 0 := ne_of_gt ha
  set f : ℝ → ℝ := fun t => Real.exp (-a^2*t^2 - b^2/t^2) with hfdef
  have hfm : Measurable f := by rw [hfdef]; fun_prop
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => (Real.exp_pos _).le
  have hint : Integrable f := integrable_twoSidedGaussian ha b
  set L : ℝ → ℝ := fun y => ∫ t in Ioi y, f t with hLdef
  set R : ℝ → ℝ := fun y => (Real.sqrt Real.pi/(4*a)) * (Real.exp (2*a*b)*erfc (a*y + b/y)
      + Real.exp (-2*a*b)*erfc (a*y - b/y)) with hRdef
  -- `L` written against the primitive `z ↦ ∫_0^z f`
  have hLeq : L = fun z => (∫ t in Ioi (0:ℝ), f t) - ∫ t in (0:ℝ)..z, f t := by
    funext z
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (a := (0:ℝ)) (b := z)
      hint.integrableOn hint.integrableOn
    simp only [hLdef]
    linarith
  -- derivative of `L` on (0,∞)
  have hL : ∀ y, 0 < y → HasDerivAt L (-(f y)) y := by
    intro y hy
    have hcontAt : ContinuousAt f y := by
      have h2 : ContinuousAt (fun t : ℝ => -a^2*t^2 - b^2/t^2) y := by
        have hden : ContinuousAt (fun t : ℝ => b^2/t^2) y :=
          ContinuousAt.div continuousAt_const (by fun_prop) (pow_ne_zero 2 (ne_of_gt hy))
        exact ((continuousAt_const.mul ((continuousAt_id.pow 2))).sub hden)
      exact Real.continuous_exp.continuousAt.comp h2
    have hprim : HasDerivAt (fun z : ℝ => ∫ t in (0:ℝ)..z, f t) (f y) y :=
      intervalIntegral.integral_hasDerivAt_right hint.intervalIntegrable
        (hfm.stronglyMeasurable.stronglyMeasurableAtFilter) hcontAt
    rw [hLeq]
    simpa using (hasDerivAt_const y (∫ t in Ioi (0:ℝ), f t)).sub hprim
  -- derivative of `R` on (0,∞)
  have hR : ∀ y, 0 < y → HasDerivAt R (-(f y)) y := by
    intro y hy
    have hy' : y ≠ 0 := ne_of_gt hy
    have hinv : HasDerivAt (fun z : ℝ => b / z) (-(b / y^2)) y := by
      have h := (hasDerivAt_inv hy').const_mul b
      simpa [div_eq_mul_inv, mul_comm, neg_mul, mul_neg] using h
    have hlin : HasDerivAt (fun z : ℝ => a * z) a y := by
      simpa using (hasDerivAt_id y).const_mul a
    have hu : HasDerivAt (fun z : ℝ => a * z + b / z) (a + -(b/y^2)) y := hlin.add hinv
    have hv : HasDerivAt (fun z : ℝ => a * z - b / z) (a - -(b/y^2)) y := hlin.sub hinv
    have hcu : HasDerivAt (fun z : ℝ => erfc (a * z + b / z))
        (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y + b/y)^2)) * (a + -(b/y^2))) y := by
      have h := (hasDerivAt_erfc (a*y + b/y)).comp y hu
      simpa [Function.comp] using h
    have hcv : HasDerivAt (fun z : ℝ => erfc (a * z - b / z))
        (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y - b/y)^2)) * (a - -(b/y^2))) y := by
      have h := (hasDerivAt_erfc (a*y - b/y)).comp y hv
      simpa [Function.comp] using h
    have hDR : HasDerivAt R ((Real.sqrt Real.pi/(4*a)) *
        (Real.exp (2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y + b/y)^2)) * (a + -(b/y^2)))
          + Real.exp (-2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y - b/y)^2)) * (a - -(b/y^2))))) y := by
      rw [hRdef]
      exact ((hcu.const_mul (Real.exp (2*a*b))).add
        (hcv.const_mul (Real.exp (-2*a*b)))).const_mul _
    have h1 : Real.exp (2*a*b) * Real.exp (-(a*y + b/y)^2) = f y := by
      rw [hfdef, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have h2 : Real.exp (-2*a*b) * Real.exp (-(a*y - b/y)^2) = f y := by
      rw [hfdef, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hval : (Real.sqrt Real.pi/(4*a)) *
        (Real.exp (2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y + b/y)^2)) * (a + -(b/y^2)))
          + Real.exp (-2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y - b/y)^2)) * (a - -(b/y^2))))
        = -(f y) := by
      have e1 : (Real.sqrt Real.pi/(4*a)) *
          (Real.exp (2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y + b/y)^2)) * (a + -(b/y^2)))
            + Real.exp (-2*a*b) * (-(2 / Real.sqrt Real.pi * Real.exp (-(a*y - b/y)^2)) * (a - -(b/y^2))))
          = (Real.sqrt Real.pi/(4*a)) * (-(2 / Real.sqrt Real.pi)) *
            ((Real.exp (2*a*b) * Real.exp (-(a*y + b/y)^2)) * (a + -(b/y^2))
              + (Real.exp (-2*a*b) * Real.exp (-(a*y - b/y)^2)) * (a - -(b/y^2))) := by ring
      rw [e1, h1, h2]
      field_simp
      ring
    rw [hval] at hDR
    exact hDR
  -- both sides vanish at +∞
  have hLtop : Tendsto L atTop (𝓝 0) := by
    have hbound : ∀ y : ℝ, L y ≤ (Real.sqrt (Real.pi/a^2)/2) * erfc (a*y) := by
      intro y
      have hg : (∫ t in Ioi y, Real.exp (-(a^2) * t^2))
          = (Real.sqrt (Real.pi / a^2) / 2) * erfc (Real.sqrt (a^2) * y) :=
        integral_Ioi_gaussian_scaled_erfc (by positivity) y
      rw [Real.sqrt_sq ha.le] at hg
      rw [hLdef, ← hg]
      refine setIntegral_mono_on hint.integrableOn
        ((integrable_exp_neg_mul_sq (show (0:ℝ) < a^2 by positivity)).integrableOn)
        measurableSet_Ioi ?_
      intro t _
      apply Real.exp_le_exp.mpr
      have h1 : 0 ≤ b^2/t^2 := by positivity
      nlinarith
    have h0 : ∀ y : ℝ, 0 ≤ L y := fun y =>
      setIntegral_nonneg measurableSet_Ioi (fun t _ => hf_nonneg t)
    have herfc : Tendsto (fun y : ℝ => (Real.sqrt (Real.pi/a^2)/2) * erfc (a*y))
        atTop (𝓝 0) := by
      have hay : Tendsto (fun y : ℝ => a * y) atTop atTop :=
        Filter.tendsto_id.const_mul_atTop ha
      have h := (erfc_tendsto_zero.comp hay).const_mul (Real.sqrt (Real.pi/a^2)/2)
      simpa [Function.comp] using h
    exact squeeze_zero h0 hbound herfc
  have hRtop : Tendsto R atTop (𝓝 0) := by
    have hb0 : Tendsto (fun y : ℝ => b / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hay : Tendsto (fun y : ℝ => a * y) atTop atTop :=
      Filter.tendsto_id.const_mul_atTop ha
    have hu : Tendsto (fun y : ℝ => a * y + b / y) atTop atTop := by
      have h := hb0.add_atTop hay
      simpa [add_comm] using h
    have hv : Tendsto (fun y : ℝ => a * y - b / y) atTop atTop := by
      have hb0' : Tendsto (fun y : ℝ => -(b / y)) atTop (𝓝 0) := by
        simpa using hb0.neg
      have h := hb0'.add_atTop hay
      refine h.congr fun y => by ring
    have hcu : Tendsto (fun y : ℝ => erfc (a*y + b/y)) atTop (𝓝 0) := by
      simpa [Function.comp] using erfc_tendsto_zero.comp hu
    have hcv : Tendsto (fun y : ℝ => erfc (a*y - b/y)) atTop (𝓝 0) := by
      simpa [Function.comp] using erfc_tendsto_zero.comp hv
    have h := (((hcu.const_mul (Real.exp (2*a*b))).add
      (hcv.const_mul (Real.exp (-2*a*b)))).const_mul (Real.sqrt Real.pi/(4*a)))
    simpa [hRdef] using h
  -- derivative matching on the half-line closes the identity
  have hD : ∀ y, 0 < y → HasDerivAt (fun z => L z - R z) 0 y := by
    intro y hy
    simpa using (hL y hy).sub (hR y hy)
  have hDtop : Tendsto (fun z => L z - R z) atTop (𝓝 0) := by
    simpa using hLtop.sub hRtop
  have hzero := eq_zero_of_hasDerivAt_zero_of_tendsto_Ioi hD hDtop hx
  have hLR : L x = R x := by linarith [hzero]
  simpa [hLdef, hRdef] using hLR

-- no-dlmf: elementary identity |sin θ| = sin|θ| on |θ| ≤ π; support for the sector description
private theorem absSinAbs {θ : ℝ} (h : |θ| ≤ Real.pi) : |Real.sin θ| = Real.sin |θ| := by
  rcases le_or_gt 0 θ with hp | hn
  · rw [abs_of_nonneg hp,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hp (by rwa [abs_of_nonneg hp] at h))]
  · have hge : -Real.pi ≤ θ := by rw [abs_of_neg hn] at h; linarith
    have hs : Real.sin θ ≤ 0 := by
      have h0 : 0 ≤ Real.sin (-θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at h0; linarith
    rw [abs_of_neg hn, Real.sin_neg, abs_of_nonpos hs]

-- no-dlmf: geometric description of DLMF's sector |ph a| < π/4 as the open convex cone {|Im a| < Re a}
private theorem memSector {a : ℂ} :
    (a ≠ 0 ∧ |Complex.arg a| < Real.pi / 4) ↔ |a.im| < a.re := by
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨ha0, harg⟩
    have hnorm : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
    have hcos : Real.cos (Complex.arg a) = a.re / ‖a‖ := Complex.cos_arg ha0
    have hsin : Real.sin (Complex.arg a) = a.im / ‖a‖ := Complex.sin_arg a
    have h1 : Real.cos (Real.pi/4) < Real.cos (Complex.arg a) := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (Complex.arg a))
        (by linarith) harg
      rwa [Real.cos_abs] at this
    have h2 : Real.sin |Complex.arg a| < Real.sin (Real.pi/4) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [abs_nonneg (Complex.arg a)]) (by linarith) harg
    have h3 : |Real.sin (Complex.arg a)| = Real.sin |Complex.arg a| := absSinAbs (by linarith)
    rw [hsin, abs_div, abs_of_pos hnorm] at h3
    rw [hcos, Real.cos_pi_div_four] at h1
    rw [Real.sin_pi_div_four, ← h3] at h2
    have h4 : |a.im| / ‖a‖ < a.re / ‖a‖ := by linarith
    exact (div_lt_div_iff_of_pos_right hnorm).mp h4
  · intro h
    have hre : 0 < a.re := lt_of_le_of_lt (abs_nonneg _) h
    have ha0 : a ≠ 0 := by intro h0; rw [h0] at hre; simp at hre
    refine ⟨ha0, ?_⟩
    by_contra hc
    push_neg at hc
    have hnorm : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha0
    have hlt : |Complex.arg a| < Real.pi/2 :=
      (Complex.abs_arg_lt_pi_div_two_iff (z := a)).mpr (Or.inl hre)
    have hcos : Real.cos (Complex.arg a) = a.re / ‖a‖ := Complex.cos_arg ha0
    have hsin : Real.sin (Complex.arg a) = a.im / ‖a‖ := Complex.sin_arg a
    have h1 : Real.cos (Complex.arg a) ≤ Real.cos (Real.pi/4) := by
      have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hc
      rwa [Real.cos_abs] at this
    have h2 : Real.sin (Real.pi/4) ≤ Real.sin |Complex.arg a| :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hc
    have h3 : |Real.sin (Complex.arg a)| = Real.sin |Complex.arg a| := absSinAbs (by linarith)
    rw [hsin, abs_div, abs_of_pos hnorm] at h3
    rw [hcos, Real.cos_pi_div_four] at h1
    rw [Real.sin_pi_div_four, ← h3] at h2
    have h4 : a.re / ‖a‖ ≤ |a.im| / ‖a‖ := by linarith
    have h5 := (div_le_div_iff_of_pos_right hnorm).mp h4
    linarith

-- no-dlmf: set-level form of `memSector`
private theorem sectorEq :
    {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi / 4} = {a : ℂ | |a.im| < a.re} := by
  ext a; exact memSector

-- no-dlmf: the sector is convex, hence preconnected — the hypothesis of the identity theorem
private theorem isPreconnectedSector :
    IsPreconnected {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi / 4} := by
  rw [sectorEq]
  refine Convex.isPreconnected ?_
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] at *
  have h1 : |s * x.im + t * y.im| ≤ s * |x.im| + t * |y.im| := by
    calc |s * x.im + t * y.im| ≤ |s * x.im| + |t * y.im| := abs_add_le _ _
      _ = s * |x.im| + t * |y.im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
  rcases lt_or_eq_of_le hs with hs' | hs'
  · nlinarith [abs_nonneg x.im, abs_nonneg y.im]
  · have ht' : t = 1 := by linarith
    have hs0 : s = 0 := hs'.symm
    subst hs0; subst ht'; simpa using hy

-- no-dlmf: Re(a²) > 0 on the sector; the convergence condition for the Gaussian factor
private theorem reSqPos {a : ℂ} (h : |a.im| < a.re) : 0 < (a^2).re := by
  have h2 : (a^2).re = a.re^2 - a.im^2 := by rw [pow_two, Complex.mul_re]; ring
  rw [h2]
  nlinarith [abs_nonneg a.im, sq_abs a.im]

-- no-dlmf: uniform lower bound Re(a²) ≥ ρ²cos 2φ on a truncated subsector; the domination input
private theorem reSqGe (φ ρ : ℝ) (hφ : 0 ≤ φ) (hφ4 : φ < Real.pi/4) {a : ℂ}
    (ha : a ≠ 0) (haφ : |Complex.arg a| ≤ φ) (hρ : 0 < ρ) (haρ : ρ ≤ ‖a‖) :
    ρ^2 * Real.cos (2*φ) ≤ (a^2).re := by
  have hpi := Real.pi_pos
  have hnorm : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hcos : Real.cos (Complex.arg a) = a.re / ‖a‖ := Complex.cos_arg ha
  have hsin : Real.sin (Complex.arg a) = a.im / ‖a‖ := Complex.sin_arg a
  have hre : a.re = ‖a‖ * Real.cos (Complex.arg a) := by rw [hcos]; field_simp
  have him : a.im = ‖a‖ * Real.sin (Complex.arg a) := by rw [hsin]; field_simp
  have hsq : (a^2).re = ‖a‖^2 * Real.cos (2 * Complex.arg a) := by
    rw [pow_two, Complex.mul_re, hre, him, Real.cos_two_mul']; ring
  have hmono : Real.cos (2*φ) ≤ Real.cos (2 * Complex.arg a) := by
    have h1 : Real.cos (2*φ) ≤ Real.cos (2 * |Complex.arg a|) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [abs_nonneg (Complex.arg a)])
        (by linarith) (by linarith)
    rwa [show (2 * |Complex.arg a|) = |2 * Complex.arg a| by rw [abs_mul]; norm_num,
      Real.cos_abs] at h1
  have hcpos : 0 < Real.cos (2*φ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [hsq]
  calc ρ^2 * Real.cos (2*φ) ≤ ‖a‖^2 * Real.cos (2*φ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hcpos.le
    _ ≤ ‖a‖^2 * Real.cos (2*Complex.arg a) := mul_le_mul_of_nonneg_left hmono (by positivity)

-- no-dlmf: elementary bound e^{-y} ≤ 1/y for y > 0
private theorem expNegLeInv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1/y := by
  have h1 : y ≤ Real.exp y := le_trans (by linarith) (Real.add_one_le_exp y)
  calc Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
    _ ≤ y⁻¹ := by gcongr
    _ = 1/y := (one_div y).symm

-- no-dlmf: elementary bound t^{-2}e^{-c/t²} ≤ 1/c, taming the singular factor at t → 0⁺
private theorem invSqMulExpLe {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    Real.exp (-(c/t^2)) / t^2 ≤ 1/c := by
  have hy : 0 < c/t^2 := by positivity
  have h := expNegLeInv hy
  rw [one_div, inv_div] at h
  have ht2 : (0:ℝ) < t^2 := by positivity
  rw [div_le_div_iff₀ ht2 hc]
  have h2 := mul_le_mul_of_nonneg_right h hc.le
  rw [div_mul_cancel₀ _ (ne_of_gt hc)] at h2
  linarith

-- no-dlmf: integrability of t²e^{-ct²} on a half-line
private theorem integrableOnSqMulExp {c : ℝ} (hc : 0 < c) {d : ℝ} (hd : 0 ≤ d) :
    IntegrableOn (fun t : ℝ => t^2 * Real.exp (-c*t^2)) (Ioi d) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hc (s := (2:ℝ)) (by norm_num)
  have key : ∀ t : ℝ, t ^ (2:ℝ) = t^(2:ℕ) := fun t => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]; exact Real.rpow_natCast t 2
  have heq : Set.EqOn (fun t : ℝ => t ^ (2:ℝ) * Real.exp (-c*t^2))
      (fun t : ℝ => t^2 * Real.exp (-c*t^2)) (Ioi (0:ℝ)) := fun t _ => by
    simp only [key t]
  exact (h.congr_fun heq measurableSet_Ioi).mono_set (Ioi_subset_Ioi hd)

-- no-dlmf: integrability of e^{-ct²} on a half-line
private theorem integrableOnExpNegSq {c : ℝ} (hc : 0 < c) (d : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-c*t^2)) (Ioi d) :=
  (integrable_exp_neg_mul_sq hc).integrableOn

-- no-dlmf: modulus of the two-sided Gaussian integrand
private theorem normGauss (a b : ℂ) (t : ℝ) :
    ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖
      = Real.exp (-(a^2).re*t^2) * Real.exp (-(b^2).re/t^2) := by
  have ht : ((t:ℂ))^2 = ((t^2 : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  rw [ht, Complex.sub_re, Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

-- no-dlmf: majorant for the integrand on (d,∞), d > 0, complex b
private theorem normGaussLeFar (a b : ℂ) {d t : ℝ} (hd : 0 < d) (ht : d < t) :
    ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖
      ≤ Real.exp (‖b‖^2/d^2) * Real.exp (-(a^2).re*t^2) := by
  have ht2 : (0:ℝ) < t^2 := by nlinarith
  have hd2 : (0:ℝ) < d^2 := by positivity
  have hdt : d^2 ≤ t^2 := by nlinarith
  have hb : -(b^2).re ≤ ‖b‖^2 := by
    have h1 : |(b^2).re| ≤ ‖b^2‖ := Complex.abs_re_le_norm _
    have h2 : ‖b^2‖ = ‖b‖^2 := by rw [norm_pow]
    rw [h2] at h1
    linarith [abs_le.mp h1]
  have h1 : -(b^2).re/t^2 ≤ ‖b‖^2/d^2 := by
    calc -(b^2).re/t^2 ≤ ‖b‖^2/t^2 := by gcongr
      _ ≤ ‖b‖^2/d^2 := by gcongr
  rw [normGauss, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le

-- no-dlmf: majorant for the integrand on (0,∞) when Re(b²) ≥ 0
private theorem normGaussLeNonneg (a b : ℂ) (hb : 0 ≤ (b^2).re) (t : ℝ) :
    ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖ ≤ Real.exp (-(a^2).re*t^2) := by
  rw [normGauss]
  have h1 : -(b^2).re/t^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg t)
  have h2 : Real.exp (-(b^2).re/t^2) ≤ 1 := Real.exp_le_one_iff.mpr h1
  nlinarith [Real.exp_pos (-(a^2).re*t^2)]

-- no-dlmf: integrability of the complex integrand on (d,∞), d > 0
private theorem integrableOnCGaussFar {a b : ℂ} (ha : 0 < (a^2).re) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) (Ioi d) := by
  have hmeas : Measurable (fun t : ℝ => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) := by fun_prop
  refine Integrable.mono' (g := fun t : ℝ => Real.exp (‖b‖^2/d^2) * Real.exp (-(a^2).re*t^2))
    ((integrableOnExpNegSq ha d).const_mul _) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact normGaussLeFar a b hd ht

-- no-dlmf: integrability of the complex integrand on (0,∞) when Re(b²) ≥ 0
private theorem integrableOnCGaussNonneg {a b : ℂ} (ha : 0 < (a^2).re) (hb : 0 ≤ (b^2).re)
    (d : ℝ) : IntegrableOn (fun t : ℝ => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) (Ioi d) := by
  have hmeas : Measurable (fun t : ℝ => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) := by fun_prop
  refine Integrable.mono' (g := fun t : ℝ => Real.exp (-(a^2).re*t^2))
    (integrableOnExpNegSq ha d) hmeas.aestronglyMeasurable ?_
  filter_upwards with t
  exact normGaussLeNonneg a b hb t

-- no-dlmf: parameter derivative of the integrand in b
private theorem hasDerivAtGaussB (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-a^2*(t:ℂ)^2 - w^2/(t:ℂ)^2))
      (Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*b)/(t:ℂ)^2)) b := by
  have h2 : HasDerivAt (fun w : ℂ => w^2) (2*b) b := by simpa using hasDerivAt_pow 2 b
  have h : HasDerivAt (fun w : ℂ => -a^2*(t:ℂ)^2 - w^2/(t:ℂ)^2) (-(2*b)/(t:ℂ)^2) b := by
    have := (h2.div_const ((t:ℂ)^2)).const_sub (-a^2*(t:ℂ)^2)
    simpa [neg_div] using this
  simpa using h.cexp

-- no-dlmf: parameter derivative of the integrand in a
private theorem hasDerivAtGaussA (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      (Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*a)*(t:ℂ)^2)) a := by
  have h2 : HasDerivAt (fun w : ℂ => w^2) (2*a) a := by simpa using hasDerivAt_pow 2 a
  have h : HasDerivAt (fun w : ℂ => -w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) (-(2*a)*(t:ℂ)^2) a := by
    have := ((h2.neg.mul_const ((t:ℂ)^2)).sub_const (b^2/(t:ℂ)^2))
    simpa [neg_mul] using this
  simpa using h.cexp

-- no-dlmf: modulus of the b-derivative factor
private theorem normDerivB (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(-(2*z)/(t:ℂ)^2)‖ = 2*‖z‖/t^2 := by
  rw [norm_div, norm_neg, norm_mul, norm_pow]
  simp [abs_of_pos ht]

-- no-dlmf: modulus of the a-derivative factor
private theorem normDerivA (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(-(2*z)*(t:ℂ)^2)‖ = 2*‖z‖*t^2 := by
  rw [norm_mul, norm_neg, norm_mul, norm_pow]
  simp [abs_of_pos ht]

-- no-dlmf: the (x,∞)-integral is entire in b (differentiation under the integral sign)
private theorem analyticBEntire {a : ℂ} (ha : 0 < (a^2).re) {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (fun b : ℂ => ∫ t in Ioi x, Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      Set.univ := by
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (μ := volume.restrict (Ioi x))
    (f := fun b t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
    (f' := fun b t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*b)/(t:ℂ)^2))
    isOpen_univ (fun b _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun b _ => integrableOnCGaussFar ha hx)
    (fun b _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (by filter_upwards with t b _ using hasDerivAtGaussB a b t) ?_
  intro b₀ _
  set R : ℝ := ‖b₀‖ + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  refine ⟨1, one_pos, fun t => (Real.exp (R^2/x^2) * (2*R/x^2)) * Real.exp (-(a^2).re*t^2),
    (integrableOnExpNegSq ha x).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
  have hxt' : x < t := ht
  have hnz : ‖z‖ ≤ R := by
    have h := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at h
    have h2 := norm_sub_norm_le z b₀
    simp only [hRdef]; linarith
  have ht0 : 0 < t := lt_trans hx hxt'
  have ht2 : (0:ℝ) < t^2 := by positivity
  have hx2 : (0:ℝ) < x^2 := by positivity
  have hxt : x^2 ≤ t^2 := by nlinarith
  rw [norm_mul, normDerivB z ht0]
  have h1 : ‖Complex.exp (-a^2*(t:ℂ)^2 - z^2/(t:ℂ)^2)‖
      ≤ Real.exp (R^2/x^2) * Real.exp (-(a^2).re*t^2) := by
    refine le_trans (normGaussLeFar a z hx hxt') ?_
    gcongr
  have h2 : 2*‖z‖/t^2 ≤ 2*R/x^2 := by gcongr
  calc ‖Complex.exp (-a^2*(t:ℂ)^2 - z^2/(t:ℂ)^2)‖ * (2*‖z‖/t^2)
      ≤ (Real.exp (R^2/x^2) * Real.exp (-(a^2).re*t^2)) * (2*R/x^2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (Real.exp (R^2/x^2) * (2*R/x^2)) * Real.exp (-(a^2).re*t^2) := by ring

-- no-dlmf: the (x,∞)-integral is analytic in a on the sector
private theorem analyticASectorFar (b : ℂ) {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (fun a : ℂ => ∫ t in Ioi x, Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi/4} := by
  have hpi := Real.pi_pos
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_sector (d := x) (θ := Real.pi/4)
    (by linarith)
    (f := fun a t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
    (f' := fun a t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*a)*(t:ℂ)^2))
    (fun a _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun a ha hph => integrableOnCGaussFar (reSqPos (memSector.mp ⟨ha, hph⟩)) hx)
    (fun a _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (by filter_upwards with t a _ _ using hasDerivAtGaussA a b t) ?_
  intro φ ρ R hφ hρ
  set φ₀ := max φ 0 with hφ₀def
  have hφ₀ : 0 ≤ φ₀ := le_max_right _ _
  have hφ₀4 : φ₀ < Real.pi/4 := max_lt hφ (by linarith)
  set c := ρ^2 * Real.cos (2*φ₀) with hcdef
  have hcos : 0 < Real.cos (2*φ₀) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  refine ⟨fun t => (2*R*Real.exp (‖b‖^2/x^2)) * (t^2 * Real.exp (-c*t^2)),
    (integrableOnSqMulExp hc hx.le).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha0 haφ haρ haR
  have hxt' : x < t := ht
  have ht0 : 0 < t := lt_trans hx hxt'
  have ht2 : (0:ℝ) ≤ t^2 := by positivity
  have hcle : c ≤ (a^2).re := reSqGe φ₀ ρ hφ₀ hφ₀4 ha0 (haφ.trans (le_max_left _ _)) hρ haρ
  rw [norm_mul, normDerivA a ht0]
  have h1 : ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖
      ≤ Real.exp (‖b‖^2/x^2) * Real.exp (-c*t^2) := by
    refine le_trans (normGaussLeFar a b hx hxt') ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
  have h2 : 2*‖a‖*t^2 ≤ 2*R*t^2 := by
    have : ‖a‖ ≤ R := haR
    nlinarith
  calc ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖ * (2*‖a‖*t^2)
      ≤ (Real.exp (‖b‖^2/x^2) * Real.exp (-c*t^2)) * (2*R*t^2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (2*R*Real.exp (‖b‖^2/x^2)) * (t^2 * Real.exp (-c*t^2)) := by ring

-- no-dlmf: the (0,∞)-integral is analytic in b on the sector
private theorem analyticBSectorZero {a : ℂ} (ha : 0 < (a^2).re) :
    AnalyticOnNhd ℂ (fun b : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      {b : ℂ | b ≠ 0 ∧ |Complex.arg b| < Real.pi/4} := by
  have hpi := Real.pi_pos
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_sector (d := (0:ℝ)) (θ := Real.pi/4)
    (by linarith)
    (f := fun b t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
    (f' := fun b t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*b)/(t:ℂ)^2))
    (fun b _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun b hb hph => integrableOnCGaussNonneg ha (reSqPos (memSector.mp ⟨hb, hph⟩)).le 0)
    (fun b _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (by filter_upwards with t b _ _ using hasDerivAtGaussB a b t) ?_
  intro φ ρ R hφ hρ
  set φ₀ := max φ 0 with hφ₀def
  have hφ₀ : 0 ≤ φ₀ := le_max_right _ _
  have hφ₀4 : φ₀ < Real.pi/4 := max_lt hφ (by linarith)
  set c := ρ^2 * Real.cos (2*φ₀) with hcdef
  have hcos : 0 < Real.cos (2*φ₀) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  refine ⟨fun t => (2*R/c) * Real.exp (-(a^2).re*t^2),
    (integrableOnExpNegSq ha 0).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb0 hbφ hbρ hbR
  have ht0 : 0 < t := ht
  have ht2 : (0:ℝ) < t^2 := by positivity
  have hcle : c ≤ (b^2).re := reSqGe φ₀ ρ hφ₀ hφ₀4 hb0 (hbφ.trans (le_max_left _ _)) hρ hbρ
  have hR0 : 0 ≤ R := le_trans (norm_nonneg b) hbR
  rw [norm_mul, normDerivB b ht0, normGauss]
  have h1 : Real.exp (-(b^2).re/t^2) ≤ Real.exp (-(c/t^2)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    gcongr
  have h2 : 2*‖b‖/t^2 ≤ 2*R/t^2 := by gcongr
  calc Real.exp (-(a^2).re*t^2) * Real.exp (-(b^2).re/t^2) * (2*‖b‖/t^2)
      ≤ Real.exp (-(a^2).re*t^2) * Real.exp (-(c/t^2)) * (2*R/t^2) := by gcongr
    _ = (2*R) * (Real.exp (-(c/t^2))/t^2) * Real.exp (-(a^2).re*t^2) := by ring
    _ ≤ (2*R) * (1/c) * Real.exp (-(a^2).re*t^2) := by
        have h3 := invSqMulExpLe hc ht0
        have h4 : (0:ℝ) ≤ 2*R := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h4)
          (Real.exp_pos _).le
    _ = (2*R/c) * Real.exp (-(a^2).re*t^2) := by ring

-- no-dlmf: the (0,∞)-integral is analytic in a on the sector
private theorem analyticASectorZero {b : ℂ} (hb : 0 ≤ (b^2).re) :
    AnalyticOnNhd ℂ (fun a : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi/4} := by
  have hpi := Real.pi_pos
  refine FLMF.Methods.analyticOnNhd_integral_Ioi_sector (d := (0:ℝ)) (θ := Real.pi/4)
    (by linarith)
    (f := fun a t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
    (f' := fun a t => Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2) * (-(2*a)*(t:ℂ)^2))
    (fun a _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (fun a ha hph => integrableOnCGaussNonneg (reSqPos (memSector.mp ⟨ha, hph⟩)) hb 0)
    (fun a _ _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (by filter_upwards with t a _ _ using hasDerivAtGaussA a b t) ?_
  intro φ ρ R hφ hρ
  set φ₀ := max φ 0 with hφ₀def
  have hφ₀ : 0 ≤ φ₀ := le_max_right _ _
  have hφ₀4 : φ₀ < Real.pi/4 := max_lt hφ (by linarith)
  set c := ρ^2 * Real.cos (2*φ₀) with hcdef
  have hcos : 0 < Real.cos (2*φ₀) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  refine ⟨fun t => (2*R) * (t^2 * Real.exp (-c*t^2)),
    (integrableOnSqMulExp hc le_rfl).const_mul _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha0 haφ haρ haR
  have ht0 : 0 < t := ht
  have ht2 : (0:ℝ) ≤ t^2 := by positivity
  have hcle : c ≤ (a^2).re := reSqGe φ₀ ρ hφ₀ hφ₀4 ha0 (haφ.trans (le_max_left _ _)) hρ haρ
  rw [norm_mul, normDerivA a ht0]
  have h1 : ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖ ≤ Real.exp (-c*t^2) := by
    refine le_trans (normGaussLeNonneg a b hb t) (Real.exp_le_exp.mpr (by nlinarith))
  have h2 : 2*‖a‖*t^2 ≤ 2*R*t^2 := by
    have : ‖a‖ ≤ R := haR
    nlinarith
  calc ‖Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖ * (2*‖a‖*t^2)
      ≤ Real.exp (-c*t^2) * (2*R*t^2) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (2*R) * (t^2 * Real.exp (-c*t^2)) := by ring

-- no-dlmf: `cerfc` is entire
private theorem differentiableCerfc : Differentiable ℂ cerfc := by
  have h : cerfc = fun w : ℂ => 1 - cerf w := rfl
  rw [h]
  exact fun z => (differentiable_cerf z).const_sub 1

-- no-dlmf: chain rule for `cerfc ∘ f` at a point
private theorem differentiableAtCerfcComp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (fun w => cerfc (f w)) z := by
  have h : DifferentiableAt ℂ (cerfc ∘ f) z := (differentiableCerfc (f z)).comp z hf
  exact h

-- no-dlmf: chain rule for `cerfc ∘ f`
private theorem differentiableCerfcComp {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => cerfc (f z)) :=
  fun z => differentiableAtCerfcComp (hf z)

-- no-dlmf: the 7.7.7 right-hand side is entire in b
private theorem analyticRhs777B (a : ℂ) (x : ℝ) :
    AnalyticOnNhd ℂ (fun b : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*a)) *
      (Complex.exp (2*a*b)*cerfc (a*(x:ℂ) + b/(x:ℂ))
        + Complex.exp (-2*a*b)*cerfc (a*(x:ℂ) - b/(x:ℂ)))) Set.univ := by
  have hdiff : Differentiable ℂ (fun b : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*a)) *
      (Complex.exp (2*a*b)*cerfc (a*(x:ℂ) + b/(x:ℂ))
        + Complex.exp (-2*a*b)*cerfc (a*(x:ℂ) - b/(x:ℂ)))) := by
    refine Differentiable.const_mul (Differentiable.add ?_ ?_) _
    · exact (Differentiable.cexp (by fun_prop)).mul (differentiableCerfcComp (by fun_prop))
    · exact (Differentiable.cexp (by fun_prop)).mul (differentiableCerfcComp (by fun_prop))
  exact fun z _ => hdiff.analyticAt z

-- no-dlmf: the 7.7.7 right-hand side is analytic in a off a = 0
private theorem analyticRhs777A (b : ℂ) (x : ℝ) :
    AnalyticOnNhd ℂ (fun a : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*a)) *
      (Complex.exp (2*a*b)*cerfc (a*(x:ℂ) + b/(x:ℂ))
        + Complex.exp (-2*a*b)*cerfc (a*(x:ℂ) - b/(x:ℂ))))
      {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi/4} := by
  have hopen : IsOpen {a : ℂ | a ≠ 0} := isOpen_ne
  have hmain : AnalyticOnNhd ℂ (fun a : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*a)) *
      (Complex.exp (2*a*b)*cerfc (a*(x:ℂ) + b/(x:ℂ))
        + Complex.exp (-2*a*b)*cerfc (a*(x:ℂ) - b/(x:ℂ)))) {a : ℂ | a ≠ 0} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn hopen]
    intro a ha
    have ha' : a ≠ 0 := ha
    have h4a : (4:ℂ)*a ≠ 0 := by simp [ha']
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ((differentiableAt_const _).div (by fun_prop) h4a) ?_
    refine DifferentiableAt.add ?_ ?_
    · exact (DifferentiableAt.cexp (by fun_prop)).mul (differentiableAtCerfcComp (by fun_prop))
    · exact (DifferentiableAt.cexp (by fun_prop)).mul (differentiableAtCerfcComp (by fun_prop))
  exact hmain.mono (fun a ha => ha.1)

-- no-dlmf: the 7.7.8 right-hand side is entire in b
private theorem analyticRhs778B (a : ℂ) :
    AnalyticOnNhd ℂ (fun b : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*a)) * Complex.exp (-2*a*b))
      Set.univ := by
  have hdiff : Differentiable ℂ
      (fun b : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*a)) * Complex.exp (-2*a*b)) := by
    exact Differentiable.const_mul (Differentiable.cexp (by fun_prop)) _
  exact fun z _ => hdiff.analyticAt z

-- no-dlmf: the 7.7.8 right-hand side is analytic in a off a = 0
private theorem analyticRhs778A (b : ℂ) :
    AnalyticOnNhd ℂ (fun a : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*a)) * Complex.exp (-2*a*b))
      {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi/4} := by
  have hopen : IsOpen {a : ℂ | a ≠ 0} := isOpen_ne
  have hmain : AnalyticOnNhd ℂ
      (fun a : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*a)) * Complex.exp (-2*a*b))
      {a : ℂ | a ≠ 0} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn hopen]
    intro a ha
    have ha' : a ≠ 0 := ha
    have h2a : (2:ℂ)*a ≠ 0 := by simp [ha']
    exact (((differentiableAt_const _).div (by fun_prop) h2a).mul
      (DifferentiableAt.cexp (by fun_prop))).differentiableWithinAt
  exact hmain.mono (fun a ha => ha.1)

-- no-dlmf: the complex integral at real parameters is the cast of the real integral
private theorem lhsOfReal (a b : ℝ) (x : ℝ) :
    (∫ t in Ioi x, Complex.exp (-(a:ℂ)^2*(t:ℂ)^2 - (b:ℂ)^2/(t:ℂ)^2))
      = ((∫ t in Ioi x, Real.exp (-a^2*t^2 - b^2/t^2) : ℝ) : ℂ) := by
  have h : ∀ t : ℝ, Complex.exp (-(a:ℂ)^2*(t:ℂ)^2 - (b:ℂ)^2/(t:ℂ)^2)
      = ((Real.exp (-a^2*t^2 - b^2/t^2) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [h]
  exact integral_complex_ofReal

-- no-dlmf: the 7.7.7 right-hand side at real parameters is the cast of the real one
private theorem rhs777OfReal (a x b : ℝ) :
    ((Real.sqrt Real.pi : ℂ)/(4*(a:ℂ))) *
      (Complex.exp (2*(a:ℂ)*(b:ℂ))*cerfc ((a:ℂ)*(x:ℂ) + (b:ℂ)/(x:ℂ))
        + Complex.exp (-2*(a:ℂ)*(b:ℂ))*cerfc ((a:ℂ)*(x:ℂ) - (b:ℂ)/(x:ℂ)))
      = (((Real.sqrt Real.pi/(4*a)) * (Real.exp (2*a*b)*FLMF.Error.erfc (a*x + b/x)
          + Real.exp (-2*a*b)*FLMF.Error.erfc (a*x - b/x)) : ℝ) : ℂ) := by
  have h1 : (a:ℂ)*(x:ℂ) + (b:ℂ)/(x:ℂ) = ((a*x + b/x : ℝ) : ℂ) := by push_cast; ring
  have h2 : (a:ℂ)*(x:ℂ) - (b:ℂ)/(x:ℂ) = ((a*x - b/x : ℝ) : ℂ) := by push_cast; ring
  have h3 : (2*(a:ℂ)*(b:ℂ)) = ((2*a*b : ℝ) : ℂ) := by push_cast; ring
  have h4 : (-2*(a:ℂ)*(b:ℂ)) = ((-2*a*b : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, h3, h4, cerfc_ofReal, cerfc_ofReal, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  ring

-- no-dlmf: the 7.7.8 right-hand side at real parameters is the cast of the real one
private theorem rhs778OfReal (a b : ℝ) :
    ((Real.sqrt Real.pi : ℂ)/(2*(a:ℂ))) * Complex.exp (-2*(a:ℂ)*(b:ℂ))
      = (((Real.sqrt Real.pi/(2*a)) * Real.exp (-2*a*b) : ℝ) : ℂ) := by
  have h4 : (-2*(a:ℂ)*(b:ℂ)) = ((-2*a*b : ℝ) : ℂ) := by push_cast; ring
  rw [h4, ← Complex.ofReal_exp]
  push_cast
  ring

-- no-dlmf: Re(r²) > 0 for a positive real r
private theorem reSqOfRealPos {r : ℝ} (hr : 0 < r) : 0 < (((r:ℂ))^2).re := by
  have h : ((r:ℂ))^2 = ((r^2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_re]
  positivity

-- no-dlmf: at a = 0 the integrand has a positive lower bound, so it is not integrable on a half-line of infinite measure
private theorem notIntegrableGaussZero (b : ℂ) {d : ℝ} (hd : 0 < d) :
    ¬ IntegrableOn (fun t : ℝ => Complex.exp (-(0:ℂ)^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) (Ioi d) := by
  intro hint
  set c : ℝ := Real.exp (-(‖b‖^2/d^2)) with hcdef
  have hcpos : 0 < c := Real.exp_pos _
  have hb : (b^2).re ≤ ‖b‖^2 := by
    have h1 : |(b^2).re| ≤ ‖b^2‖ := Complex.abs_re_le_norm _
    have h2 : ‖b^2‖ = ‖b‖^2 := by rw [norm_pow]
    rw [h2] at h1
    linarith [abs_le.mp h1]
  have hbound : ∀ t ∈ Ioi d, c ≤ ‖Complex.exp (-(0:ℂ)^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖ := by
    intro t ht
    have hdt : d < t := ht
    have ht2 : (0:ℝ) < t^2 := by nlinarith
    have hd2 : (0:ℝ) < d^2 := by positivity
    have hdt2 : d^2 ≤ t^2 := by nlinarith
    rw [normGauss]
    have h0 : (((0:ℂ))^2).re = 0 := by norm_num
    rw [h0]
    have hkey : (b^2).re/t^2 ≤ ‖b‖^2/d^2 := by
      rcases le_or_gt 0 ((b^2).re) with h | h
      · calc (b^2).re/t^2 ≤ ‖b‖^2/t^2 := by gcongr
          _ ≤ ‖b‖^2/d^2 := by gcongr
      · have hn : (b^2).re/t^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h.le (by positivity)
        have hp : (0:ℝ) ≤ ‖b‖^2/d^2 := by positivity
        linarith
    have : c ≤ Real.exp (-(b^2).re/t^2) := by
      rw [hcdef]
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    simpa using this
  have hnorm : Integrable (fun t : ℝ => ‖Complex.exp (-(0:ℂ)^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)‖)
      (volume.restrict (Ioi d)) := hint.norm
  have hconst : Integrable (fun _ : ℝ => c) (volume.restrict (Ioi d)) := by
    refine Integrable.mono' hnorm aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos hcpos]
    exact hbound t ht
  rcases integrable_const_iff.mp hconst with h | h
  · exact absurd h (ne_of_gt hcpos)
  · haveI := h
    have h2 : (volume.restrict (Ioi d)) Set.univ ≠ ⊤ := measure_ne_top _ _
    rw [Measure.restrict_apply_univ, Real.volume_Ioi] at h2
    exact h2 rfl

-- no-dlmf: 1 lies in the sector; the base point of the identity theorem
private theorem oneMemSector : (1:ℂ) ∈ {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < Real.pi/4} := by
  refine memSector.mpr ?_
  simp

-- no-dlmf: a sequence of nonzero points tending to 0, the identity-theorem witness
private theorem tendstoWitnessZero :
    Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall (fun n => div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)))

-- no-dlmf: a sequence of positive reals ≠ 1 tending to 1, the identity-theorem witness
private theorem tendstoWitnessOne :
    Tendsto (fun n : ℕ => (1 : ℂ) + 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h1 : Tendsto (fun n : ℕ => (1:ℂ)/((n:ℂ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1)).add h1
    simpa using h2
  · refine Eventually.of_forall (fun n => ?_)
    have h : (1:ℂ)/((n:ℂ)+1) ≠ 0 := div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)
    intro hmem
    simp only [Set.mem_singleton_iff] at hmem
    exact h (by linear_combination hmem)

/-- **DLMF 7.7.7** — the two-sided Gaussian integral over `(x,∞)`,
`∫ₓ^∞ e^{-a²t² - b²/t²} dt = (√π/(4a))·(e^{2ab} erfc(ax+b/x) + e^{-2ab} erfc(ax-b/x))`,
for real `x > 0`, complex `a` with `|ph a| < π/4`, and complex `b`.

DAG: E-7.7.7.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_7_dlmf {a b : ℂ} {x : ℝ} (hx : 0 < x)
    (hph : |Complex.arg a| < Real.pi / 4) :
    (∫ t in Set.Ioi x, Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      = ((Real.sqrt Real.pi : ℂ)/(4*a)) * (Complex.exp (2*a*b)*cerfc (a*(x:ℂ) + b/(x:ℂ))
          + Complex.exp (-2*a*b)*cerfc (a*(x:ℂ) - b/(x:ℂ))) := by
  have anchor : ∀ r s : ℝ, 0 < r →
      (∫ t in Ioi x, Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - (s:ℂ)^2/(t:ℂ)^2))
        = ((Real.sqrt Real.pi : ℂ)/(4*(r:ℂ))) *
          (Complex.exp (2*(r:ℂ)*(s:ℂ))*cerfc ((r:ℂ)*(x:ℂ) + (s:ℂ)/(x:ℂ))
            + Complex.exp (-2*(r:ℂ)*(s:ℂ))*cerfc ((r:ℂ)*(x:ℂ) - (s:ℂ)/(x:ℂ))) := by
    intro r s hr
    rw [lhsOfReal, rhs777OfReal]
    exact congrArg (fun y : ℝ => (y:ℂ)) (erf_7_7_7 hx hr)
  have step1 : ∀ r : ℝ, 0 < r → ∀ w : ℂ,
      (∫ t in Ioi x, Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2))
        = ((Real.sqrt Real.pi : ℂ)/(4*(r:ℂ))) *
          (Complex.exp (2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) + w/(x:ℂ))
            + Complex.exp (-2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) - w/(x:ℂ))) := by
    intro r hr
    have hf := analyticBEntire (reSqOfRealPos hr) hx
    have hg := analyticRhs777B (r:ℂ) x
    have hp : ∀ n : ℕ,
        (fun w : ℂ => ∫ t in Ioi x, Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2))
            ((1:ℂ)/((n:ℂ)+1))
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*(r:ℂ))) *
              (Complex.exp (2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) + w/(x:ℂ))
                + Complex.exp (-2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) - w/(x:ℂ))))
            ((1:ℂ)/((n:ℂ)+1)) := by
      intro n
      have hcast : (1:ℂ)/((n:ℂ)+1) = (((1:ℝ)/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
      simp only
      rw [hcast]
      exact anchor r (1/((n:ℝ)+1)) hr
    have hkey : ∃ᶠ w in 𝓝[≠] (0:ℂ),
        (fun w : ℂ => ∫ t in Ioi x, Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2)) w
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*(r:ℂ))) *
              (Complex.exp (2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) + w/(x:ℂ))
                + Complex.exp (-2*(r:ℂ)*w)*cerfc ((r:ℂ)*(x:ℂ) - w/(x:ℂ)))) w :=
      tendstoWitnessZero.frequently (Eventually.frequently (Eventually.of_forall hp))
    exact congrFun (AnalyticOnNhd.eq_of_frequently_eq hf hg hkey)
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [integral_undef (notIntegrableGaussZero b hx)]
    simp
  · have hf := analyticASectorFar b hx
    have hg := analyticRhs777A b x
    have hp : ∀ n : ℕ,
        (fun w : ℂ => ∫ t in Ioi x, Complex.exp (-w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
            ((1:ℂ)+1/((n:ℂ)+1))
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*w)) *
              (Complex.exp (2*w*b)*cerfc (w*(x:ℂ) + b/(x:ℂ))
                + Complex.exp (-2*w*b)*cerfc (w*(x:ℂ) - b/(x:ℂ))))
            ((1:ℂ)+1/((n:ℂ)+1)) := by
      intro n
      have hpos : (0:ℝ) < 1 + 1/((n:ℝ)+1) := by positivity
      have hcast : (1:ℂ)+1/((n:ℂ)+1) = ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
      simp only
      rw [hcast]
      exact step1 (1 + 1/((n:ℝ)+1)) hpos b
    have hkey : ∃ᶠ w in 𝓝[≠] (1:ℂ),
        (fun w : ℂ => ∫ t in Ioi x, Complex.exp (-w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) w
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(4*w)) *
              (Complex.exp (2*w*b)*cerfc (w*(x:ℂ) + b/(x:ℂ))
                + Complex.exp (-2*w*b)*cerfc (w*(x:ℂ) - b/(x:ℂ)))) w :=
      tendstoWitnessOne.frequently (Eventually.frequently (Eventually.of_forall hp))
    exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnectedSector
      oneMemSector hkey ⟨ha0, hph⟩

-- no-dlmf: real-domain restriction (a, b positive reals) of the two-sided
-- Gaussian integral, narrower than DLMF's complex sectors `|ph a| < π/4` and
-- `|ph b| < π/4`; faithful surface is erf_7_7_8_dlmf
/-- Two-sided Gaussian integral over `(0,∞)`
`∫₀^∞ e^{-a²t² - b²/t²} dt = (√π/(2a))·e^{-2ab}`, for real `a, b > 0`
(real-domain instance). -/
theorem erf_7_7_8 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ioi (0:ℝ), Real.exp (-a^2*t^2 - b^2/t^2))
      = (Real.sqrt Real.pi/(2*a)) * Real.exp (-2*a*b) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  set f : ℝ → ℝ := fun t => Real.exp (-a^2*t^2 - b^2/t^2) with hfdef
  have hint : Integrable f := integrable_twoSidedGaussian ha b
  set L : ℝ → ℝ := fun y => ∫ t in Ioi y, f t with hLdef
  -- the tail integral is continuous from the right at 0
  have hLeq : L = fun z => (∫ t in Ioi (0:ℝ), f t) - ∫ t in (0:ℝ)..z, f t := by
    funext z
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (a := (0:ℝ)) (b := z)
      hint.integrableOn hint.integrableOn
    simp only [hLdef]
    linarith
  have hprim : Continuous (fun z : ℝ => ∫ t in (0:ℝ)..z, f t) :=
    intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0
  have h1 : Tendsto L (𝓝[>] (0:ℝ)) (𝓝 (∫ t in Ioi (0:ℝ), f t)) := by
    rw [hLeq]
    have h := (hprim.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    have h' := (tendsto_const_nhds (x := ∫ t in Ioi (0:ℝ), f t)
      (f := 𝓝[>] (0:ℝ))).sub h
    simpa using h'
  -- on (0,∞) the tail integral agrees with the 7.7.7 right-hand side
  have h2 : L =ᶠ[𝓝[>] (0:ℝ)] fun x => (Real.sqrt Real.pi/(4*a)) *
      (Real.exp (2*a*b)*erfc (a*x + b/x) + Real.exp (-2*a*b)*erfc (a*x - b/x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact erf_7_7_7 hx ha
  -- limits of the 7.7.7 right-hand side as x → 0⁺
  have hbx : Tendsto (fun x : ℝ => b / x) (𝓝[>] (0:ℝ)) atTop := by
    have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hb
    simpa [div_eq_mul_inv] using h
  have hax : Tendsto (fun x : ℝ => a * x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => a * x) (𝓝 (0:ℝ)) (𝓝 (a * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ => a * x + b / x) (𝓝[>] (0:ℝ)) atTop := hax.add_atTop hbx
  have hv : Tendsto (fun x : ℝ => a * x - b / x) (𝓝[>] (0:ℝ)) atBot := by
    have hbx' : Tendsto (fun x : ℝ => -(b / x)) (𝓝[>] (0:ℝ)) atBot :=
      tendsto_neg_atTop_atBot.comp hbx
    have h := hax.add_atBot hbx'
    refine h.congr fun x => by ring
  have herfc2 : Tendsto erfc atBot (𝓝 2) := by
    have h := (tendsto_const_nhds (x := (1:ℝ)) (f := atBot)).sub erf_tendsto_atBot
    have h12 : (1:ℝ) - (-1) = 2 := by norm_num
    rw [h12] at h
    simpa [erfc] using h
  have hcu : Tendsto (fun x : ℝ => erfc (a*x + b/x)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    erfc_tendsto_zero.comp hu
  have hcv : Tendsto (fun x : ℝ => erfc (a*x - b/x)) (𝓝[>] (0:ℝ)) (𝓝 2) :=
    herfc2.comp hv
  have h3 : Tendsto (fun x : ℝ => (Real.sqrt Real.pi/(4*a)) *
      (Real.exp (2*a*b)*erfc (a*x + b/x) + Real.exp (-2*a*b)*erfc (a*x - b/x)))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.sqrt Real.pi/(4*a)) *
        (Real.exp (2*a*b)*0 + Real.exp (-2*a*b)*2))) :=
    ((hcu.const_mul _).add (hcv.const_mul _)).const_mul _
  have h4 : Tendsto L (𝓝[>] (0:ℝ)) (𝓝 ((Real.sqrt Real.pi/(4*a)) *
      (Real.exp (2*a*b)*0 + Real.exp (-2*a*b)*2))) :=
    h3.congr' h2.symm
  have hkey := tendsto_nhds_unique h1 h4
  have hL0 : (∫ t in Set.Ioi (0:ℝ), Real.exp (-a^2*t^2 - b^2/t^2))
      = ∫ t in Ioi (0:ℝ), f t := rfl
  rw [hL0, hkey]
  field_simp
  ring

/-- **DLMF 7.7.8** — the two-sided Gaussian integral over `(0,∞)`,
`∫₀^∞ e^{-a²t² - b²/t²} dt = (√π/(2a))·e^{-2ab}`, for complex `a, b` with
`|ph a| < π/4` and `|ph b| < π/4`.

DAG: E-7.7.8.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_8_dlmf {a b : ℂ} (hpha : |Complex.arg a| < Real.pi / 4)
    (hphb : |Complex.arg b| < Real.pi / 4) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (-a^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
      = ((Real.sqrt Real.pi : ℂ)/(2*a)) * Complex.exp (-2*a*b) := by
  have hpi := Real.pi_pos
  rcases eq_or_ne a 0 with rfl | ha0
  · have hni : ¬ IntegrableOn (fun t : ℝ => Complex.exp (-(0:ℂ)^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
        (Ioi (0:ℝ)) := fun hint =>
      notIntegrableGaussZero b one_pos (hint.mono_set (Ioi_subset_Ioi (by norm_num)))
    rw [integral_undef hni]
    simp
  have hrea : 0 < (a^2).re := reSqPos (memSector.mp ⟨ha0, hpha⟩)
  rcases eq_or_ne b 0 with rfl | hb0
  · have h73 := erf_7_7_3 (a := a^2) (z := 0) hrea
    have hint : (∫ t in Ioi (0:ℝ), Complex.exp (-a^2*(t:ℂ)^2 - (0:ℂ)^2/(t:ℂ)^2))
        = ∫ t in Ioi (0:ℝ), Complex.exp (-(a^2)*(t:ℂ)^2 + 2*Complex.I*0*(t:ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      congr 1
      ring
    have hlogim : (Complex.log a * 2).im = 2 * Complex.arg a := by
      simp [Complex.mul_im, Complex.log_im]
      ring
    have hb1 : -Real.pi < (Complex.log a * 2).im := by
      rw [hlogim]; cases abs_lt.mp hpha with | intro h1 h2 => linarith
    have hb2 : (Complex.log a * 2).im ≤ Real.pi := by
      rw [hlogim]; cases abs_lt.mp hpha with | intro h1 h2 => linarith
    have hmul : a ^ ((2:ℂ) * (-(1:ℂ)/2)) = (a ^ (2:ℂ)) ^ (-(1:ℂ)/2) :=
      Complex.cpow_mul (-(1:ℂ)/2) hb1 hb2
    have hpow : a ^ (2:ℂ) = a^(2:ℕ) := by
      have h := Complex.cpow_natCast a 2
      simpa using h
    rw [show (2:ℂ) * (-(1:ℂ)/2) = -1 by ring, Complex.cpow_neg_one, hpow] at hmul
    rw [hint, h73, ← hmul]
    simp [cerfc_zero]
    field_simp
  have hreb : 0 < (b^2).re := reSqPos (memSector.mp ⟨hb0, hphb⟩)
  have anchor : ∀ r s : ℝ, 0 < r → 0 < s →
      (∫ t in Ioi (0:ℝ), Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - (s:ℂ)^2/(t:ℂ)^2))
        = ((Real.sqrt Real.pi : ℂ)/(2*(r:ℂ))) * Complex.exp (-2*(r:ℂ)*(s:ℂ)) := by
    intro r s hr hs
    rw [lhsOfReal, rhs778OfReal]
    exact congrArg (fun y : ℝ => (y:ℂ)) (erf_7_7_8 hr hs)
  have step1 : ∀ r : ℝ, 0 < r → ∀ w : ℂ, w ≠ 0 → |Complex.arg w| < Real.pi/4 →
      (∫ t in Ioi (0:ℝ), Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2))
        = ((Real.sqrt Real.pi : ℂ)/(2*(r:ℂ))) * Complex.exp (-2*(r:ℂ)*w) := by
    intro r hr
    have hf := analyticBSectorZero (reSqOfRealPos hr)
    have hg : AnalyticOnNhd ℂ
        (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*(r:ℂ))) * Complex.exp (-2*(r:ℂ)*w))
        {w : ℂ | w ≠ 0 ∧ |Complex.arg w| < Real.pi/4} :=
      (analyticRhs778B (r:ℂ)).mono (fun z _ => Set.mem_univ z)
    have hp : ∀ n : ℕ,
        (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2))
            ((1:ℂ)+1/((n:ℂ)+1))
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*(r:ℂ))) * Complex.exp (-2*(r:ℂ)*w))
            ((1:ℂ)+1/((n:ℂ)+1)) := by
      intro n
      have hpos : (0:ℝ) < 1 + 1/((n:ℝ)+1) := by positivity
      have hcast : (1:ℂ)+1/((n:ℂ)+1) = ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
      simp only
      rw [hcast]
      exact anchor r (1 + 1/((n:ℝ)+1)) hr hpos
    have hkey : ∃ᶠ w in 𝓝[≠] (1:ℂ),
        (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-(r:ℂ)^2*(t:ℂ)^2 - w^2/(t:ℂ)^2)) w
          = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*(r:ℂ))) * Complex.exp (-2*(r:ℂ)*w)) w :=
      tendstoWitnessOne.frequently (Eventually.frequently (Eventually.of_forall hp))
    intro w hw0 hwph
    exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnectedSector
      oneMemSector hkey ⟨hw0, hwph⟩
  have hf := analyticASectorZero hreb.le
  have hg := analyticRhs778A b
  have hp : ∀ n : ℕ,
      (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2))
          ((1:ℂ)+1/((n:ℂ)+1))
        = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*w)) * Complex.exp (-2*w*b))
          ((1:ℂ)+1/((n:ℂ)+1)) := by
    intro n
    have hpos : (0:ℝ) < 1 + 1/((n:ℝ)+1) := by positivity
    have hcast : (1:ℂ)+1/((n:ℂ)+1) = ((1 + 1/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
    simp only
    rw [hcast]
    exact step1 (1 + 1/((n:ℝ)+1)) hpos b hb0 hphb
  have hkey : ∃ᶠ w in 𝓝[≠] (1:ℂ),
      (fun w : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-w^2*(t:ℂ)^2 - b^2/(t:ℂ)^2)) w
        = (fun w : ℂ => ((Real.sqrt Real.pi : ℂ)/(2*w)) * Complex.exp (-2*w*b)) w :=
    tendstoWitnessOne.frequently (Eventually.frequently (Eventually.of_forall hp))
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg isPreconnectedSector
    oneMemSector hkey ⟨ha0, hpha⟩

-- no-dlmf: Re(b²) > 0 on the sector, in the form the §7.14 lemmas consume
private theorem reSqPos14 {b : ℂ} (hb0 : b ≠ 0) (hph : |Complex.arg b| < Real.pi/4) :
    0 < (b^2).re := reSqPos (memSector.mp ⟨hb0, hph⟩)
-- no-dlmf: Gaussian decay of `cerfc` along a ray in the sector, from the n = 0 Poincaré remainder bound `cerfc_poincare_bound`
private theorem cerfcRay {b : ℂ} (hb0 : b ≠ 0) (hph : |Complex.arg b| < Real.pi/4)
    {t : ℝ} (ht : 0 < t) :
    ‖cerfc (b*(t:ℂ))‖
      ≤ (2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖ * t)) * Real.exp (-((b^2).re*t^2)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  have hsp : (0:ℝ) < Real.sqrt Real.pi := by positivity
  have hz0 : b*(t:ℂ) ≠ 0 := mul_ne_zero hb0 (by exact_mod_cast ne_of_gt ht)
  have harg : Complex.arg (b*(t:ℂ)) = Complex.arg b := by
    rw [mul_comm]; exact Complex.arg_real_mul b ht
  have hsec : |Complex.arg (b*(t:ℂ))| ≤ 3*Real.pi/4 - Real.pi/2 := by
    rw [harg]; linarith
  have h := cerfc_poincare_bound (δ := Real.pi/2) (by positivity) (by linarith) hz0 hsec 0
  rw [Finset.range_zero, Finset.sum_empty, sub_zero] at h
  have hsin : Real.sin (2*(Real.pi/2)/3) = Real.sqrt 3 / 2 := by
    rw [show 2*(Real.pi/2)/3 = Real.pi/3 by ring, Real.sin_pi_div_three]
  have hnbt : ‖b*(t:ℂ)‖ = ‖b‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hL : ‖(Real.sqrt Real.pi : ℂ) * Complex.exp ((b*(t:ℂ))^2) * cerfc (b*(t:ℂ))‖
      = Real.sqrt Real.pi * Real.exp ((b^2).re*t^2) * ‖cerfc (b*(t:ℂ))‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
    congr 2
    have hsq : (b*(t:ℂ))^2 = b^2 * ((t^2 : ℝ):ℂ) := by push_cast; ring
    rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hL] at h
  have hR : 2 * (Nat.factorial (2*0) : ℝ) / (2 * (Real.sin (2*(Real.pi/2)/3) * ‖b*(t:ℂ)‖)) ^ (2*0+1)
      = 2/(Real.sqrt 3 * ‖b‖ * t) := by
    rw [hsin, hnbt]
    norm_num
    ring
  rw [hR] at h
  have hApos : 0 < Real.sqrt Real.pi * Real.exp ((b^2).re*t^2) := by positivity
  have hgoal : (2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖ * t)) * Real.exp (-((b^2).re*t^2))
      = (2/(Real.sqrt 3 * ‖b‖ * t)) / (Real.sqrt Real.pi * Real.exp ((b^2).re*t^2)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hgoal, le_div_iff₀ hApos]
  calc ‖cerfc (b*(t:ℂ))‖ * (Real.sqrt Real.pi * Real.exp ((b^2).re*t^2))
      = Real.sqrt Real.pi * Real.exp ((b^2).re*t^2) * ‖cerfc (b*(t:ℂ))‖ := by ring
    _ ≤ 2/(Real.sqrt 3 * ‖b‖ * t) := h

-- no-dlmf: completing the square: -βt² + αt ≤ α²/(2β) - (β/2)t²
private theorem quadBound {α β : ℝ} (hβ : 0 < β) (t : ℝ) :
    -β*t^2 + α*t ≤ α^2/(2*β) + (-(β/2))*t^2 := by
  have h : α^2/(2*β) + (-(β/2))*t^2 - (-β*t^2 + α*t) = (α - β*t)^2/(2*β) := by
    field_simp
    ring
  have hpos : 0 ≤ (α - β*t)^2/(2*β) := by positivity
  linarith

-- no-dlmf: real part of the Gaussian-times-oscillation exponent
private theorem reGaussOsc (a b : ℂ) (t : ℝ) :
    (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ)).re = -(b^2).re*t^2 + (2*Complex.I*a).re*t := by
  have hsq : ((t:ℂ))^2 = ((t^2 : ℝ) : ℂ) := by push_cast; ring
  rw [hsq, Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

-- no-dlmf: integrability of e^{-b²t²+2iat} on (0,∞)
private theorem integrableGaussOsc {a b : ℂ} (hb : 0 < (b^2).re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ)))
      (Ioi (0:ℝ)) := by
  have hmeas : Measurable
      (fun t : ℝ => Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ))) := by fun_prop
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re)) *
        Real.exp (-((b^2).re/2)*t^2)) (Ioi (0:ℝ)) :=
    ((integrable_exp_neg_mul_sq (b := (b^2).re/2) (by positivity)).integrableOn).const_mul _
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Complex.norm_exp, reGaussOsc, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (quadBound hb t)

-- no-dlmf: continuity of t ↦ e^{2iat} erfc(bt)
private theorem continuousErfcOsc (a b : ℂ) :
    Continuous (fun t : ℝ => Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ))) := by
  have hc : Continuous cerfc := by
    have h : cerfc = fun w : ℂ => 1 - cerf w := rfl
    rw [h]
    exact continuous_const.sub differentiable_cerf.continuous
  exact (Complex.continuous_exp.comp (by fun_prop)).mul (hc.comp (by fun_prop))

-- no-dlmf: integrability of t ↦ e^{2iat} erfc(bt) on (0,∞)
private theorem integrableErfcOsc {a b : ℂ} (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi/4) :
    IntegrableOn (fun t : ℝ => Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      (Ioi (0:ℝ)) := by
  have hβ : 0 < (b^2).re := reSqPos14 hb0 hph
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set C : ℝ := 2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  have hu : Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ) = Ioi (0:ℝ) := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hu, integrableOn_union]
  refine ⟨(continuousErfcOsc a b).integrableOn_Ioc, ?_⟩
  have hmeas : Measurable
      (fun t : ℝ => Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ))) :=
    (continuousErfcOsc a b).measurable
  have hint : IntegrableOn
      (fun t : ℝ => (C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re))) *
        Real.exp (-((b^2).re/2)*t^2)) (Ioi (1:ℝ)) :=
    ((integrable_exp_neg_mul_sq (b := (b^2).re/2) (by positivity)).integrableOn).const_mul _
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1:ℝ) < t := ht
  have ht0 : (0:ℝ) < t := by linarith
  rw [norm_mul, Complex.norm_exp]
  have hre1 : (2*Complex.I*a*(t:ℂ)).re = (2*Complex.I*a).re * t := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre1]
  have hb1 : ‖cerfc (b*(t:ℂ))‖ ≤ (C/t) * Real.exp (-((b^2).re*t^2)) := by
    have h := cerfcRay hb0 hph ht0
    have heq : (2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖ * t)) = C/t := by
      rw [hCdef]; field_simp
    rwa [heq] at h
  have hb2 : (C/t) ≤ C := by
    rw [div_le_iff₀ ht0]
    nlinarith
  have hstep : Real.exp ((2*Complex.I*a).re * t) * ‖cerfc (b*(t:ℂ))‖
      ≤ Real.exp ((2*Complex.I*a).re * t) * (C * Real.exp (-((b^2).re*t^2))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hb1 ?_) (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le
  refine le_trans hstep ?_
  have hq := quadBound (α := (2*Complex.I*a).re) hβ t
  calc Real.exp ((2*Complex.I*a).re * t) * (C * Real.exp (-((b^2).re*t^2)))
      = C * Real.exp (-(b^2).re*t^2 + (2*Complex.I*a).re*t) := by
        rw [Real.exp_add]; ring_nf
    _ ≤ C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re) + (-((b^2).re/2))*t^2) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) hC0.le
    _ = (C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re))) *
          Real.exp (-((b^2).re/2)*t^2) := by rw [Real.exp_add]; ring

-- no-dlmf: K·e^{-ct²} → 0 at +∞
private theorem tendstoExpNegSq {c : ℝ} (hc : 0 < c) (K : ℝ) :
    Tendsto (fun t : ℝ => K * Real.exp (-c*t^2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => c*t^2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun t : ℝ => -(c*t^2)) atTop atBot := tendsto_neg_atTop_atBot.comp h1
  have h3 : Tendsto (fun t : ℝ => Real.exp (-(c*t^2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h2
  have h4 := h3.const_mul K
  simp only [mul_zero] at h4
  refine h4.congr (fun t => by ring_nf)

-- no-dlmf: e^{2iat} erfc(bt) → 0 at +∞, the boundary term of the integration by parts
private theorem tendstoErfcOscZero {a b : ℂ} (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi/4) :
    Tendsto (fun t : ℝ => Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      atTop (𝓝 0) := by
  have hβ : 0 < (b^2).re := reSqPos14 hb0 hph
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set C : ℝ := 2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine squeeze_zero_norm' (a := fun t : ℝ =>
    (C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re))) * Real.exp (-((b^2).re/2)*t^2)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht1
    have ht0 : (0:ℝ) < t := by linarith
    rw [norm_mul, Complex.norm_exp]
    have hre1 : (2*Complex.I*a*(t:ℂ)).re = (2*Complex.I*a).re * t := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hre1]
    have hb1 : ‖cerfc (b*(t:ℂ))‖ ≤ (C/t) * Real.exp (-((b^2).re*t^2)) := by
      have h := cerfcRay hb0 hph ht0
      have heq : (2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖ * t)) = C/t := by
        rw [hCdef]; field_simp
      rwa [heq] at h
    have hb2 : (C/t) ≤ C := by
      rw [div_le_iff₀ ht0]; nlinarith
    have hstep : Real.exp ((2*Complex.I*a).re * t) * ‖cerfc (b*(t:ℂ))‖
        ≤ Real.exp ((2*Complex.I*a).re * t) * (C * Real.exp (-((b^2).re*t^2))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hb1 ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right hb2 (Real.exp_pos _).le
    refine le_trans hstep ?_
    have hq := quadBound (α := (2*Complex.I*a).re) hβ t
    calc Real.exp ((2*Complex.I*a).re * t) * (C * Real.exp (-((b^2).re*t^2)))
        = C * Real.exp (-(b^2).re*t^2 + (2*Complex.I*a).re*t) := by
          rw [Real.exp_add]; ring_nf
      _ ≤ C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re) + (-((b^2).re/2))*t^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) hC0.le
      _ = (C * Real.exp ((2*Complex.I*a).re^2/(2*(b^2).re))) *
            Real.exp (-((b^2).re/2)*t^2) := by rw [Real.exp_add]; ring
  · exact tendstoExpNegSq (by positivity) _

-- no-dlmf: t·erfc(bt) → 0 at +∞, the boundary term of the a = 0 integration by parts
private theorem tendstoTErfcZero {b : ℂ} (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi/4) :
    Tendsto (fun t : ℝ => (t:ℂ) * cerfc (b*(t:ℂ))) atTop (𝓝 0) := by
  have hβ : 0 < (b^2).re := reSqPos14 hb0 hph
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set C : ℝ := 2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine squeeze_zero_norm' (a := fun t : ℝ => C * Real.exp (-((b^2).re)*t^2)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hb1 : ‖cerfc (b*(t:ℂ))‖ ≤ (C/t) * Real.exp (-((b^2).re*t^2)) := by
      have h := cerfcRay hb0 hph ht0
      have heq : (2/(Real.sqrt 3 * Real.sqrt Real.pi * ‖b‖ * t)) = C/t := by
        rw [hCdef]; field_simp
      rwa [heq] at h
    calc t * ‖cerfc (b*(t:ℂ))‖ ≤ t * ((C/t) * Real.exp (-((b^2).re*t^2))) :=
          mul_le_mul_of_nonneg_left hb1 ht0.le
      _ = C * Real.exp (-((b^2).re)*t^2) := by
          field_simp
  · exact tendstoExpNegSq hβ _

-- no-dlmf: derivative of `cerfc`
private theorem hasDerivAtCerfc (z : ℂ) :
    HasDerivAt cerfc (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-z^2))) z := by
  have h : cerfc = fun w : ℂ => 1 - cerf w := rfl
  rw [h]
  exact (hasDerivAt_cerf z).const_sub 1

-- no-dlmf: derivative of t ↦ e^{2iat} erfc(bt)
private theorem hasDerivAtErfcOsc (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (2*Complex.I*a*(s:ℂ)) * cerfc (b*(s:ℂ)))
      (Complex.exp (2*Complex.I*a*(t:ℂ)) * (2*Complex.I*a) * cerfc (b*(t:ℂ))
        + Complex.exp (2*Complex.I*a*(t:ℂ)) *
            (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b)) t := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (2*Complex.I*a*z))
      (Complex.exp (2*Complex.I*a*(t:ℂ)) * (2*Complex.I*a)) (t:ℂ) := by
    have h := ((hasDerivAt_id ((t:ℂ))).const_mul (2*Complex.I*a)).cexp
    simpa using h
  have h2 : HasDerivAt (fun z : ℂ => cerfc (b*z))
      (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b) (t:ℂ) := by
    have hinner : HasDerivAt (fun z : ℂ => b*z) b (t:ℂ) := by
      simpa using (hasDerivAt_id ((t:ℂ))).const_mul b
    exact (hasDerivAtCerfc (b*(t:ℂ))).comp ((t:ℂ)) hinner
  exact (h1.mul h2).comp_ofReal

-- no-dlmf: derivative of t ↦ t·erfc(bt)
private theorem hasDerivAtTErfc (b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s:ℂ) * cerfc (b*(s:ℂ)))
      (1 * cerfc (b*(t:ℂ))
        + (t:ℂ) * (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b)) t := by
  have h1 : HasDerivAt (fun z : ℂ => z) 1 (t:ℂ) := hasDerivAt_id _
  have h2 : HasDerivAt (fun z : ℂ => cerfc (b*z))
      (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b) (t:ℂ) := by
    have hinner : HasDerivAt (fun z : ℂ => b*z) b (t:ℂ) := by
      simpa using (hasDerivAt_id ((t:ℂ))).const_mul b
    exact (hasDerivAtCerfc (b*(t:ℂ))).comp ((t:ℂ)) hinner
  exact (h1.mul h2).comp_ofReal

-- no-dlmf: (b²)^{-1/2} = b⁻¹ on the sector, reconciling `erf_7_7_3` with the §7.14 normalisation
private theorem cpowSqNegHalf {b : ℂ} (hb0 : b ≠ 0) (hph : |Complex.arg b| < Real.pi/4) :
    (b^2)^(-(1:ℂ)/2) = b⁻¹ := by
  have hpi := Real.pi_pos
  have hlogim : (Complex.log b * 2).im = 2 * Complex.arg b := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  have hb1 : -Real.pi < (Complex.log b * 2).im := by
    rw [hlogim]; cases abs_lt.mp hph with | intro h1 h2 => linarith
  have hb2 : (Complex.log b * 2).im ≤ Real.pi := by
    rw [hlogim]; cases abs_lt.mp hph with | intro h1 h2 => linarith
  have hmul : b ^ ((2:ℂ) * (-(1:ℂ)/2)) = (b ^ (2:ℂ)) ^ (-(1:ℂ)/2) :=
    Complex.cpow_mul (-(1:ℂ)/2) hb1 hb2
  have hpow : b ^ (2:ℂ) = b^(2:ℕ) := by
    have h := Complex.cpow_natCast b 2
    simpa using h
  rw [show (2:ℂ) * (-(1:ℂ)/2) = -1 by ring, Complex.cpow_neg_one, hpow] at hmul
  exact hmul.symm

-- no-dlmf: the a = 0 branch of DLMF 7.14.1, assembled in `erf_7_14_1_full`
private theorem integralErfcOscAZero {b : ℂ} (hb0 : b ≠ 0) (hph : |Complex.arg b| < Real.pi/4) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (2*Complex.I*(0:ℂ)*(t:ℂ)) * cerfc (b*(t:ℂ)))
      = 1/(b*(Real.sqrt Real.pi : ℂ)) := by
  have hβ : 0 < (b^2).re := reSqPos14 hb0 hph
  have hπne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hsimp : (∫ t in Ioi (0:ℝ), Complex.exp (2*Complex.I*(0:ℂ)*(t:ℂ)) * cerfc (b*(t:ℂ)))
      = ∫ t in Ioi (0:ℝ), cerfc (b*(t:ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    norm_num
  have hI0 : IntegrableOn (fun t : ℝ => cerfc (b*(t:ℂ))) (Ioi (0:ℝ)) := by
    have h := integrableErfcOsc (a := 0) hb0 hph
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    norm_num
  have hgauss : IntegrableOn (fun t : ℝ => (t:ℂ) * Complex.exp (-b^2*(t:ℂ)^2)) (Ioi (0:ℝ)) :=
    (integrable_mul_cexp_neg_mul_sq hβ).integrableOn
  have hD : ∀ t : ℝ, (1 * cerfc (b*(t:ℂ))
        + (t:ℂ) * (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b))
      = cerfc (b*(t:ℂ))
        + (-(2*b/(Real.sqrt Real.pi:ℂ))) * ((t:ℂ) * Complex.exp (-b^2*(t:ℂ)^2)) := by
    intro t
    have hsq : (b*(t:ℂ))^2 = b^2*(t:ℂ)^2 := by ring
    rw [hsq]; ring
  have hcont : ContinuousWithinAt (fun s : ℝ => (s:ℂ) * cerfc (b*(s:ℂ))) (Ici (0:ℝ)) 0 := by
    have hc : Continuous cerfc := by
      have h : cerfc = fun w : ℂ => 1 - cerf w := rfl
      rw [h]
      exact continuous_const.sub differentiable_cerf.continuous
    exact (Complex.continuous_ofReal.mul (hc.comp (by fun_prop))).continuousWithinAt
  have hDint : IntegrableOn (fun t : ℝ => cerfc (b*(t:ℂ))
      + (-(2*b/(Real.sqrt Real.pi:ℂ))) * ((t:ℂ) * Complex.exp (-b^2*(t:ℂ)^2))) (Ioi (0:ℝ)) :=
    hI0.add (hgauss.const_mul _)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun s : ℝ => (s:ℂ) * cerfc (b*(s:ℂ)))
    (f' := fun t : ℝ => cerfc (b*(t:ℂ))
      + (-(2*b/(Real.sqrt Real.pi:ℂ))) * ((t:ℂ) * Complex.exp (-b^2*(t:ℂ)^2)))
    (a := 0) (m := 0) hcont
    (fun t _ => by
      have h := hasDerivAtTErfc b t
      rw [hD t] at h
      exact h) hDint (tendstoTErfcZero hb0 hph)
  rw [integral_add hI0 (hgauss.const_mul _), integral_const_mul,
    integral_mul_cexp_neg_mul_sq hβ] at hres
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hres
  rw [hsimp]
  have hb2ne : (b:ℂ)^2 ≠ 0 := pow_ne_zero 2 hb0
  field_simp at hres ⊢
  linear_combination hres

-- no-dlmf: the a ≠ 0 branch of DLMF 7.14.1, assembled in `erf_7_14_1_full`
private theorem integralErfcOscANe {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi/4) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      = (1/(a*(Real.sqrt Real.pi : ℂ)))*cdawson (a/b)
          + (Complex.I/(2*a))*(1 - Complex.exp (-(a/b)^2)) := by
  have hβ : 0 < (b^2).re := reSqPos14 hb0 hph
  have hπne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hI1 : IntegrableOn (fun t : ℝ => Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      (Ioi (0:ℝ)) := integrableErfcOsc hb0 hph
  have hI2 : IntegrableOn (fun t : ℝ => Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ)))
      (Ioi (0:ℝ)) := integrableGaussOsc hβ
  have hD : ∀ t : ℝ, (Complex.exp (2*Complex.I*a*(t:ℂ)) * (2*Complex.I*a) * cerfc (b*(t:ℂ))
        + Complex.exp (2*Complex.I*a*(t:ℂ)) *
            (-((2/(Real.sqrt Real.pi:ℂ)) * Complex.exp (-(b*(t:ℂ))^2)) * b))
      = (2*Complex.I*a) * (Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
        + (-(2*b/(Real.sqrt Real.pi:ℂ))) *
            Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ)) := by
    intro t
    have hsq : (b*(t:ℂ))^2 = b^2*(t:ℂ)^2 := by ring
    rw [hsq, Complex.exp_add]
    ring
  have hcont : ContinuousWithinAt
      (fun s : ℝ => Complex.exp (2*Complex.I*a*(s:ℂ)) * cerfc (b*(s:ℂ))) (Ici (0:ℝ)) 0 :=
    (continuousErfcOsc a b).continuousWithinAt
  have hDint : IntegrableOn (fun t : ℝ =>
      (2*Complex.I*a) * (Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
        + (-(2*b/(Real.sqrt Real.pi:ℂ))) *
            Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ))) (Ioi (0:ℝ)) :=
    (hI1.const_mul _).add (hI2.const_mul _)
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun s : ℝ => Complex.exp (2*Complex.I*a*(s:ℂ)) * cerfc (b*(s:ℂ)))
    (f' := fun t : ℝ => (2*Complex.I*a) * (Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      + (-(2*b/(Real.sqrt Real.pi:ℂ))) * Complex.exp (-b^2*(t:ℂ)^2 + 2*Complex.I*a*(t:ℂ)))
    (a := 0) (m := 0) hcont
    (fun t _ => by
      have h := hasDerivAtErfcOsc a b t
      rw [hD t] at h
      exact h) hDint
    (tendstoErfcOscZero hb0 hph)
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    erf_7_7_3 (a := b^2) (z := a) hβ, cpowSqNegHalf hb0 hph] at hres
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, cerfc_zero,
    zero_sub] at hres
  have hcerfcw : cerfc (-Complex.I*a*b⁻¹) = 1 + cerf (Complex.I*(a/b)) := by
    have harg : -Complex.I*a*b⁻¹ = -(Complex.I*(a/b)) := by
      field_simp
    rw [harg]
    show (1 : ℂ) - cerf (-(Complex.I*(a/b))) = 1 + cerf (Complex.I*(a/b))
    rw [cerf_neg]
    ring
  have hexpw : Complex.exp (-a^2/b^2) = Complex.exp (-(a/b)^2) := by
    congr 1
    field_simp
  rw [hcerfcw, hexpw] at hres
  set J : ℂ := ∫ t in Ioi (0:ℝ), Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ))
    with hJdef
  unfold cdawson
  field_simp at hres ⊢
  linear_combination (-Complex.I) * hres + (2*a*J) * Complex.I_sq

-- The former `erf_7_14_1` helper (`ℜ b > 0`, no `a ≠ 0` guard) was FALSE on
-- both counts — refuted at `a = 0, b = 1` (RHS `0` by `x/0 = 0` junk vs LHS
-- `1/√π`), and the half-plane `ℜ b > 0` is not a valid domain at all (the
-- integral diverges for `|ph b| ≥ π/4`). It was superseded by the proven
-- `erf_7_14_1_dlmf` below and deleted; see docs/ERRATA.md,
-- `erf-7-14-1-narrowed-false`.

-- no-dlmf: `a ≠ 0` restriction of the phase-sector integral formula, omitting
-- DLMF's stated `a = 0` limiting convention; faithful surface is
-- `erf_7_14_1_full`
/-- Integral of `erfc` against a complex exponential, `a ≠ 0` case:
`∫₀^∞ e^{2iat} erfc(bt) dt = (1/(a√π))·F(a/b) + (i/(2a))·(1 - e^{-(a/b)²})`,
with `F` the complex Dawson integral, for `a ∈ ℂ`, `a ≠ 0`, and the sector
`|ph b| < π/4`. -/
theorem erf_7_14_1_dlmf {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi / 4) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      = (1/(a*(Real.sqrt Real.pi : ℂ)))*cdawson (a/b)
          + (Complex.I/(2*a))*(1 - Complex.exp (-(a/b)^2)) := by
  exact integralErfcOscANe ha0 hb0 hph

/-- **DLMF 7.14.1** — `∫₀^∞ e^{2iat} erfc(bt) dt = (1/(a√π))·F(a/b) +
(i/(2a))·(1 - e^{-(a/b)²})`, with `F` the complex Dawson integral, for
`a ∈ ℂ` and DLMF's sector `|ph b| < π/4`; at `a = 0` the right side is taken
in DLMF's stated limiting sense, with value `1/(b√π)`.

DAG: E-7.14.1.
Numerical: PASS
Verified: verified
-/
theorem erf_7_14_1_full {a b : ℂ} (hb0 : b ≠ 0)
    (hph : |Complex.arg b| < Real.pi / 4) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (2*Complex.I*a*(t:ℂ)) * cerfc (b*(t:ℂ)))
      = if a = 0 then 1/(b*(Real.sqrt Real.pi : ℂ))
        else (1/(a*(Real.sqrt Real.pi : ℂ)))*cdawson (a/b)
            + (Complex.I/(2*a))*(1 - Complex.exp (-(a/b)^2)) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [if_pos rfl]
    exact integralErfcOscAZero hb0 hph
  · rw [if_neg ha0]
    exact integralErfcOscANe ha0 hb0 hph

/-! ### The DLMF 7.9.1 ↦ 7.9.3 convergent identity

The Gautschi fraction (7.9.3) at `z` and the Laplace fraction (7.9.1) at
`ζ = -i z` are the *same* fraction up to an explicit period-4 rescaling of the
Wallis continuants.  Writing `s` for the scale sequence
`s 0 = 1, s 1 = -z, s (n+2) = -s n` (so `s = 1, -z, -1, z, 1, -z, …`), the
continuants satisfy, for every `n`,

* `Bₙ(7.9.1 at ζ) = s n · Bₙ(7.9.3 at z)`,
* `Aₙ(7.9.1 at ζ) = i · s n · Aₙ(7.9.3 at z)`,

hence `Aₙ/Bₙ(7.9.1 at ζ) = i · Aₙ/Bₙ(7.9.3 at z)` whenever `z ≠ 0`.  Both
continuant identities are instances of `FLMF.Methods.eq_mul_of_wallis_recurrence`
(a straight `n ↔ n` correspondence — no contraction is involved); the two
coefficient identities that make the rescaled Gautschi continuants solve the
Laplace recurrence are `gautschi_coeffB` and `gautschi_coeffA` below. -/

-- no-dlmf: private period-4 scale sequence for the 7.9.1 ↦ 7.9.3 continuant correspondence
/-- The scale sequence `s 0 = 1`, `s 1 = -z`, `s (n+2) = -s n`, i.e.
`s = 1, -z, -1, z, 1, -z, …` (period 4). -/
private noncomputable def gautschiScale (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => -z
  | (n + 2) => -(gautschiScale z n)

-- no-dlmf: recursion equation of the private scale sequence
private lemma gautschiScale_add_two (z : ℂ) (n : ℕ) :
    gautschiScale z (n + 2) = -(gautschiScale z n) := rfl

-- no-dlmf: closed form of the private scale sequence at even indices
private lemma gautschiScale_even (z : ℂ) (m : ℕ) :
    gautschiScale z (2 * m) = (-1) ^ m := by
  induction m with
  | zero => rfl
  | succ k ih =>
      have h : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h, gautschiScale_add_two, ih, pow_succ]
      ring

-- no-dlmf: closed form of the private scale sequence at odd indices
private lemma gautschiScale_odd (z : ℂ) (m : ℕ) :
    gautschiScale z (2 * m + 1) = (-1) ^ (m + 1) * z := by
  induction m with
  | zero => show -z = _; ring
  | succ k ih =>
      have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [h, gautschiScale_add_two, ih, pow_succ]
      ring

-- no-dlmf: nonvanishing of the private scale sequence (needed to cancel it in the quotient)
private lemma gautschiScale_ne_zero {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    gautschiScale z n ≠ 0 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    rw [gautschiScale_even]
    exact pow_ne_zero _ (by norm_num)
  · subst hm
    rw [gautschiScale_odd]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hz

-- no-dlmf: partial numerators of the DLMF 7.9.3 fraction (the `a`-sequence of `erf_7_9_3`)
private noncomputable def cfA793 : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k = 1 then 1 else -((k : ℂ) - 1) / 2

-- no-dlmf: partial denominators of the DLMF 7.9.3 fraction (the `b`-sequence of `erf_7_9_3`)
private noncomputable def cfB793 (z : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else z

-- no-dlmf: partial numerators of the DLMF 7.9.1 fraction (the `a`-sequence of `erf_7_9_1_complex`)
private noncomputable def cfA791 (w : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k = 1 then w else ((k : ℂ) - 1) / 2

-- no-dlmf: partial denominators of the DLMF 7.9.1 fraction (the `b`-sequence of `erf_7_9_1_complex`)
private noncomputable def cfB791 (w : ℂ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k % 2 = 1 then w ^ 2 else 1

-- no-dlmf: value lemma for the private 7.9.3 numerator sequence
private lemma cfA793_add_two (n : ℕ) : cfA793 (n + 2) = -((n : ℂ) + 1) / 2 := by
  show (if n + 2 = 0 then 0 else if n + 2 = 1 then 1 else (-(((n + 2 : ℕ) : ℂ) - 1) / 2)) = _
  rw [if_neg (by omega), if_neg (by omega)]
  push_cast
  ring

-- no-dlmf: value lemma for the private 7.9.3 denominator sequence
private lemma cfB793_add_two (z : ℂ) (n : ℕ) : cfB793 z (n + 2) = z := by
  show (if n + 2 = 0 then 0 else z) = z
  rw [if_neg (by omega)]

-- no-dlmf: value lemma for the private 7.9.1 numerator sequence
private lemma cfA791_add_two (w : ℂ) (n : ℕ) : cfA791 w (n + 2) = ((n : ℂ) + 1) / 2 := by
  show (if n + 2 = 0 then 0 else if n + 2 = 1 then w else ((((n + 2 : ℕ) : ℂ) - 1) / 2)) = _
  rw [if_neg (by omega), if_neg (by omega)]
  push_cast
  ring

-- no-dlmf: value lemma for the private 7.9.1 denominator sequence at even index
private lemma cfB791_even (w : ℂ) (m : ℕ) : cfB791 w (2 * m + 2) = 1 := by
  show (if 2 * m + 2 = 0 then 0 else if (2 * m + 2) % 2 = 1 then w ^ 2 else 1) = 1
  rw [if_neg (by omega), if_neg (by omega)]

-- no-dlmf: value lemma for the private 7.9.1 denominator sequence at odd index
private lemma cfB791_odd (w : ℂ) (m : ℕ) : cfB791 w (2 * m + 3) = w ^ 2 := by
  show (if 2 * m + 3 = 0 then 0 else if (2 * m + 3) % 2 = 1 then w ^ 2 else 1) = w ^ 2
  rw [if_neg (by omega), if_pos (by omega)]

-- no-dlmf: `ζ² = -z²` for `ζ = -i z`, the bridge between the two `b`-sequences
private lemma neg_I_mul_sq (z : ℂ) : (-Complex.I * z) ^ 2 = -z ^ 2 := by
  linear_combination z ^ 2 * Complex.I_sq

-- no-dlmf: coefficient identity (A) `s(n+2)·b_G(n+2) = s(n+1)·b_L(n+2)`
private lemma gautschi_coeffB (z : ℂ) (n : ℕ) :
    gautschiScale z (n + 2) * cfB793 z (n + 2)
      = cfB791 (-Complex.I * z) (n + 2) * gautschiScale z (n + 1) := by
  rw [cfB793_add_two]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst hm
    have e2 : 2 * m + 2 = 2 * (m + 1) := by omega
    rw [cfB791_even, e2, gautschiScale_even, gautschiScale_odd, one_mul]
  · subst hm
    have e2 : 2 * m + 1 + 2 = 2 * m + 3 := by omega
    have e3 : (2 * m + 3 : ℕ) = 2 * (m + 1) + 1 := by omega
    have e1 : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [e2, cfB791_odd, neg_I_mul_sq, e3, gautschiScale_odd, e1, gautschiScale_even,
      pow_succ, pow_succ]
    ring

-- no-dlmf: coefficient identity (B) `s(n+2)·a_G(n+2) = s(n)·a_L(n+2)`
private lemma gautschi_coeffA (z : ℂ) (n : ℕ) :
    gautschiScale z (n + 2) * cfA793 (n + 2)
      = cfA791 (-Complex.I * z) (n + 2) * gautschiScale z n := by
  rw [cfA793_add_two, cfA791_add_two, gautschiScale_add_two]
  ring

-- no-dlmf: the shared Wallis step for the 7.9.1 ↦ 7.9.3 continuant correspondence
/-- Any solution `u` of the 7.9.3 Wallis recurrence, rescaled by `c · s`, solves the
7.9.1 recurrence at `ζ = -i z`.  This is the `hv` hypothesis of
`FLMF.Methods.eq_mul_of_wallis_recurrence` for both continuant families
(`c = 1` for the denominators, `c = i` for the numerators). -/
private lemma gautschi_step (z : ℂ) (σ u : ℕ → ℂ) (c : ℂ)
    (hσ : ∀ k, σ k = c * gautschiScale z k)
    (hu : ∀ k, u (k + 2) = cfB793 z (k + 2) * u (k + 1) + cfA793 (k + 2) * u k)
    (n : ℕ) :
    σ (n + 2) * u (n + 2)
      = cfB791 (-Complex.I * z) (n + 2) * (σ (n + 1) * u (n + 1))
        + cfA791 (-Complex.I * z) (n + 2) * (σ n * u n) := by
  rw [hσ, hσ, hσ, hu n]
  linear_combination (c * u (n + 1)) * gautschi_coeffB z n + (c * u n) * gautschi_coeffA z n

-- no-dlmf: denominator-continuant correspondence `B_L(ζ) = s · B_G(z)`
private lemma cfDenC_791_eq (z : ℂ) (n : ℕ) :
    cfDenC (cfA791 (-Complex.I * z)) (cfB791 (-Complex.I * z)) n
      = gautschiScale z n * cfDenC cfA793 (cfB793 z) n := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence
    (c := gautschiScale z)
    (v := fun k => cfDenC cfA793 (cfB793 z) k)
    (p := fun k => cfB791 (-Complex.I * z) (k + 2))
    (q := fun k => cfA791 (-Complex.I * z) (k + 2)) ?_ ?_ ?_ ?_ n
  · show (1 : ℂ) = gautschiScale z 0 * 1
    show (1 : ℂ) = 1 * 1
    ring
  · show cfB791 (-Complex.I * z) 1 = gautschiScale z 1 * cfB793 z 1
    show (if (1 : ℕ) = 0 then 0 else if (1 : ℕ) % 2 = 1 then (-Complex.I * z) ^ 2 else 1)
        = (-z) * (if (1 : ℕ) = 0 then 0 else z)
    norm_num
    linear_combination z ^ 2 * Complex.I_sq
  · intro k
    show cfDenC _ _ (k + 2) = _
    rfl
  · intro k
    exact gautschi_step z (gautschiScale z) _ 1 (fun j => (one_mul _).symm)
      (fun j => rfl) k

-- no-dlmf: numerator-continuant correspondence `A_L(ζ) = i · s · A_G(z)`
private lemma cfNumC_791_eq (z : ℂ) (n : ℕ) :
    cfNumC (cfA791 (-Complex.I * z)) (cfB791 (-Complex.I * z)) n
      = Complex.I * gautschiScale z n * cfNumC cfA793 (cfB793 z) n := by
  refine FLMF.Methods.eq_mul_of_wallis_recurrence
    (c := fun k => Complex.I * gautschiScale z k)
    (v := fun k => cfNumC cfA793 (cfB793 z) k)
    (p := fun k => cfB791 (-Complex.I * z) (k + 2))
    (q := fun k => cfA791 (-Complex.I * z) (k + 2)) ?_ ?_ ?_ ?_ n
  · show cfB791 (-Complex.I * z) 0 = Complex.I * gautschiScale z 0 * cfB793 z 0
    show (if (0 : ℕ) = 0 then 0 else if (0 : ℕ) % 2 = 1 then (-Complex.I * z) ^ 2 else 1)
        = Complex.I * 1 * (if (0 : ℕ) = 0 then 0 else z)
    norm_num
  · show cfB791 (-Complex.I * z) 1 * cfB791 (-Complex.I * z) 0 + cfA791 (-Complex.I * z) 1
        = Complex.I * gautschiScale z 1 * (cfB793 z 1 * cfB793 z 0 + cfA793 1)
    show _ * (if (0 : ℕ) = 0 then (0 : ℂ) else _) + (if (1 : ℕ) = 0 then 0 else
          if (1 : ℕ) = 1 then (-Complex.I * z) else (((1 : ℕ) : ℂ) - 1) / 2)
        = Complex.I * (-z) * ((if (1 : ℕ) = 0 then 0 else z) * (if (0 : ℕ) = 0 then (0 : ℂ) else z)
            + (if (1 : ℕ) = 0 then 0 else if (1 : ℕ) = 1 then 1 else -(((1 : ℕ) : ℂ) - 1) / 2))
    norm_num
  · intro k
    show cfNumC _ _ (k + 2) = _
    rfl
  · intro k
    exact gautschi_step z (fun j => Complex.I * gautschiScale z j) _ Complex.I
      (fun j => rfl) (fun j => rfl) k

-- no-dlmf: convergent correspondence `f_n(7.9.1 at -i z) = i · f_n(7.9.3 at z)`
/-- The `n`-th convergent of the Laplace fraction (DLMF 7.9.1) at `ζ = -i z` equals
`i` times the `n`-th convergent of the Gautschi fraction (DLMF 7.9.3) at `z`: the
period-4 scale `s n` cancels in the quotient (it is nonzero as `z ≠ 0`). -/
private lemma cfConvC_791_eq {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    cfConvC (cfA791 (-Complex.I * z)) (cfB791 (-Complex.I * z)) n
      = Complex.I * cfConvC cfA793 (cfB793 z) n := by
  simp only [cfConvC, cfNumC_791_eq, cfDenC_791_eq]
  rw [mul_comm Complex.I (gautschiScale z n), mul_assoc,
    mul_div_mul_left _ _ (gautschiScale_ne_zero hz n), mul_div_assoc]

/-- Gautschi continued fraction for the Faddeeva function (DLMF 7.9.3):
`w(z) = (i/√π)·1/(z − ½/(z − 1/(z − 3/2/(z − ⋯))))` for `ℑ z > 0`, stated as the
convergence of the convergents of a local complex Wallis recurrence (partial
numerators after the leading `1` are `−j/2` for `j = 1,2,3,…`).

This is derived from `erf_7_9_1_complex` (7.9.1) at `ζ = -i z`, which lies in
the half-plane `ℜ ζ = ℑ z > 0`, via the exact per-convergent identity
`cfConvC_791_eq`: the two fractions have the same convergents up to the factor `i`
and the period-4 continuant rescaling `s`, and `√π e^{ζ²} erfc ζ = √π w(z)` because
`ζ² = -z²` and `w(z) = e^{-z²} erfc(-i z)`.

DLMF 7.9.3.
DAG: E-7.9.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_9_3 {z : ℂ} (hz : 0 < z.im) :
    Filter.Tendsto
      (fun N => (Complex.I/(Real.sqrt Real.pi : ℂ)) *
        cfConvC
          (fun k => if k = 0 then 0 else if k = 1 then 1 else -((k:ℂ)-1)/2)
          (fun k => if k = 0 then 0 else z) N)
      Filter.atTop (nhds (faddeeva z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hre : (-Complex.I * z).re = z.im := by simp [Complex.mul_re]
  have h1 : Filter.Tendsto
      (cfConvC (cfA791 (-Complex.I * z)) (cfB791 (-Complex.I * z))) Filter.atTop
      (nhds ((Real.sqrt Real.pi : ℂ) * Complex.exp ((-Complex.I * z) ^ 2)
        * cerfc (-Complex.I * z))) :=
    erf_7_9_1_complex (-Complex.I * z) (by rw [hre]; exact hz)
  have hval : (Real.sqrt Real.pi : ℂ) * Complex.exp ((-Complex.I * z) ^ 2)
      * cerfc (-Complex.I * z) = (Real.sqrt Real.pi : ℂ) * faddeeva z := by
    rw [faddeeva_eq_cerfc_neg_I_mul, neg_I_mul_sq, neg_mul, mul_assoc]
  rw [hval] at h1
  have hfun : cfConvC (cfA791 (-Complex.I * z)) (cfB791 (-Complex.I * z))
      = fun N => Complex.I * cfConvC cfA793 (cfB793 z) N :=
    funext (cfConvC_791_eq hz0)
  rw [hfun] at h1
  have hsp : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have h2 := h1.const_mul ((Real.sqrt Real.pi : ℂ)⁻¹)
  rw [inv_mul_cancel_left₀ hsp] at h2
  have h3 : (fun N => (Real.sqrt Real.pi : ℂ)⁻¹ * (Complex.I * cfConvC cfA793 (cfB793 z) N))
      = fun N => (Complex.I/(Real.sqrt Real.pi : ℂ)) * cfConvC cfA793 (cfB793 z) N := by
    funext N
    field_simp
  rw [h3] at h2
  exact h2

end FLMF.Error
