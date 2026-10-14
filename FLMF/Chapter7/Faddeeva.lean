import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.Voigt
import FLMF.Chapter7.VoigtExtra
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Faddeeva function `w(z)` (DLMF §7.2(ii), R2)

`w(z) = e^{-z²} erfc(-iz)` is the scaled complex complementary error function
(a.k.a. the Faddeeva / Faddeyeva / plasma-dispersion function). We define it on
top of the complex `cerf`/`cerfc` keystone (`Error/ComplexErf.lean`) and record
the chapter-7 identities that were previously deferred for lack of a complex
error function:

* 7.2.3 — defining relation (proven, `rfl`)
* 7.4.3 — reflection `w(-z) = 2e^{-z²} - w(z)` (PROVEN via `cerf_neg`)
* 7.6.3 — Maclaurin series  (surface)
* 7.7.2 — Cauchy integral representation, `Im z > 0`  (surface)
* 7.10.2 — first-order ODE `w' = -2z w + 2i/√π`  (surface)
* 7.10.3 — derivative recurrence  (surface)
* 7.19.3 — Voigt combination `U + iV` via `w`  (surface)

DLMF 7.9.3 (the continued fraction for `w`) remains a documented deferral: the
exact Gautschi partial-numerator pattern needs careful transcription that we did
not pin down here.
-/

namespace FLMF.Error

open scoped Real

-- no-dlmf: encodes w(z) via the second limb of DLMF 7.2.3; the chain display is surfaced at `erf_7_2_3`
/-- The Faddeeva function `w(z) = e^{-z²} erfc(-iz)` (DLMF 7.2.3).

-/
noncomputable def faddeeva (z : ℂ) : ℂ := Complex.exp (-z ^ 2) * cerfc (-(Complex.I * z))

-- no-dlmf: chain link 7.2.3 (assembled in `erf_7_2_3` below, alongside
-- `erf_7_2_3_integral`); this half is the definitional relation
-- `w(z) = e^{-z²} erfc(-iz)`, immediate by `rfl` from `faddeeva`'s definition
/-- Defining relation `w(z) = e^{-z²} erfc(-iz)` (DLMF 7.2.3). -/
theorem faddeeva_eq_cerfc_neg_I_mul (z : ℂ) :
    faddeeva z = Complex.exp (-z ^ 2) * cerfc (-(Complex.I * z)) := rfl

/-- Reflection formula `w(-z) = 2e^{-z²} - w(z)` (DLMF 7.4.3).  Proven from the
oddness of the complex error function (`cerf_neg`).

DLMF 7.4.3.
DAG: E-7.4.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_4_3 (z : ℂ) : faddeeva (-z) = 2 * Complex.exp (-z ^ 2) - faddeeva z := by
  simp only [faddeeva, cerfc]
  have key : cerf (-(Complex.I * -z)) = -cerf (-(Complex.I * z)) := by
    have h : -(Complex.I * -z) = -(-(Complex.I * z)) := by ring
    rw [h, cerf_neg]
  rw [show (-z) ^ 2 = z ^ 2 from by ring, key]
  ring

/-- First-order differential equation `w'(z) = -2z·w(z) + 2i/√π` (DLMF 7.10.2).

DLMF 7.10.2.
DAG: E-7.10.2.
Numerical: PASS
Verified: verified
-/
theorem erf_7_10_2 (z : ℂ) :
    HasDerivAt faddeeva (-2 * z * faddeeva z + 2 * Complex.I / (Real.sqrt Real.pi : ℂ)) z := by
  -- Derivative of the Gaussian prefactor `e^{-z²}`.
  have hgauss : HasDerivAt (fun w : ℂ => Complex.exp (-w ^ 2))
      (-2 * z * Complex.exp (-z ^ 2)) z := by
    have hinner : HasDerivAt (fun w : ℂ => -w ^ 2) (-2 * z) z := by
      have h := ((hasDerivAt_id z).pow 2).neg
      convert h using 1
      simp only [id_eq]
      ring
    have h := hinner.cexp
    convert h using 1
    ring
  -- `(-(iz))² = -z²`, so the chain-rule exponential is `e^{z²}`.
  have harg : -(-(Complex.I * z)) ^ 2 = z ^ 2 := by
    linear_combination (-(z ^ 2)) * Complex.I_sq
  -- Derivative of `z ↦ erfc(-iz)` via the `cerf` keystone and the chain rule.
  have hcerfc : HasDerivAt (fun w : ℂ => cerfc (-(Complex.I * w)))
      (2 * Complex.I / (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2)) z := by
    have hu : HasDerivAt (fun w : ℂ => -(Complex.I * w)) (-Complex.I) z := by
      have h := ((hasDerivAt_id z).const_mul Complex.I).neg
      convert h using 1
      ring
    have hcomp := (hasDerivAt_cerf (-(Complex.I * z))).comp z hu
    simp only [Function.comp_def] at hcomp
    have hsub := hcomp.const_sub 1
    have hfun : (fun w : ℂ => 1 - cerf (-(Complex.I * w)))
        = fun w : ℂ => cerfc (-(Complex.I * w)) := by
      funext w
      rw [cerfc]
    rw [hfun] at hsub
    convert hsub using 1
    rw [harg]
    ring
  -- Product rule, then `e^{-z²}·e^{z²} = 1` collapses the inhomogeneous term.
  have hprod := hgauss.mul hcerfc
  have hexp : Complex.exp (-z ^ 2) * Complex.exp (z ^ 2) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hderiv_eq : -2 * z * faddeeva z + 2 * Complex.I / (Real.sqrt Real.pi : ℂ)
      = -2 * z * Complex.exp (-z ^ 2) * cerfc (-(Complex.I * z))
        + Complex.exp (-z ^ 2) * (2 * Complex.I / (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2)) := by
    rw [faddeeva]
    linear_combination (-(2 * Complex.I / (Real.sqrt Real.pi : ℂ))) * hexp
  rw [hderiv_eq]
  exact hprod

/-- Derivative recurrence
`w⁽ⁿ⁺²⁾(z) + 2z·w⁽ⁿ⁺¹⁾(z) + 2(n+1)·w⁽ⁿ⁾(z) = 0` (DLMF 7.10.3).

DLMF 7.10.3.
DAG: E-7.10.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_10_3 (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 2) faddeeva z + 2 * z * iteratedDeriv (n + 1) faddeeva z
      + 2 * ((n : ℂ) + 1) * iteratedDeriv n faddeeva z = 0 := by
  -- `w` is entire, hence `C^∞`, and every iterated derivative is differentiable.
  have hdiff : Differentiable ℂ faddeeva := fun w => (erf_7_10_2 w).differentiableAt
  have hcd : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) faddeeva := hdiff.contDiff
  have hdiffn : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m faddeeva) := by
    intro m
    rw [iteratedDeriv_eq_iterate]
    exact (hcd.iterate_deriv m).differentiable (by simp)
  have hDn : ∀ (m : ℕ) (w : ℂ), HasDerivAt (iteratedDeriv m faddeeva)
      (iteratedDeriv (m + 1) faddeeva w) w := by
    intro m w
    rw [iteratedDeriv_succ]
    exact ((hdiffn m) w).hasDerivAt
  have hderiv1 : deriv faddeeva = fun w : ℂ => -2 * w * faddeeva w
      + 2 * Complex.I / (Real.sqrt Real.pi : ℂ) := funext fun w => (erf_7_10_2 w).deriv
  -- Induct: differentiate the ODE 7.10.2 `n` more times.
  induction n generalizing z with
  | zero =>
      simp only [Nat.zero_add]
      have h2 : HasDerivAt (fun y : ℂ => -2 * y * faddeeva y
            + 2 * Complex.I / (Real.sqrt Real.pi : ℂ))
          (-2 * faddeeva z
            + -2 * z * (-2 * z * faddeeva z + 2 * Complex.I / (Real.sqrt Real.pi : ℂ))) z := by
        have h := (((hasDerivAt_id z).const_mul (-2 : ℂ)).mul (erf_7_10_2 z)).add_const
          (2 * Complex.I / (Real.sqrt Real.pi : ℂ))
        convert h using 1
        simp only [id_eq]
        ring
      have h3 : iteratedDeriv 2 faddeeva z
          = -2 * faddeeva z
            + -2 * z * (-2 * z * faddeeva z + 2 * Complex.I / (Real.sqrt Real.pi : ℂ)) := by
        rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
        exact h2.deriv
      rw [h3, iteratedDeriv_one, (erf_7_10_2 z).deriv, iteratedDeriv_zero]
      push_cast
      ring
  | succ m ih =>
      -- The inductive hypothesis, read as a closed form for `w⁽ᵐ⁺²⁾`.
      have hfun : iteratedDeriv (m + 2) faddeeva
          = fun w : ℂ => -2 * w * iteratedDeriv (m + 1) faddeeva w
              - 2 * ((m : ℂ) + 1) * iteratedDeriv m faddeeva w := by
        funext w
        linear_combination ih w
      have hda : HasDerivAt (fun w : ℂ => -2 * w * iteratedDeriv (m + 1) faddeeva w
            - 2 * ((m : ℂ) + 1) * iteratedDeriv m faddeeva w)
          (-2 * iteratedDeriv (m + 1) faddeeva z + -2 * z * iteratedDeriv (m + 2) faddeeva z
            - 2 * ((m : ℂ) + 1) * iteratedDeriv (m + 1) faddeeva z) z := by
        have h1 := ((hasDerivAt_id z).const_mul (-2 : ℂ)).mul (hDn (m + 1) z)
        have h2 := (hDn m z).const_mul (2 * ((m : ℂ) + 1))
        have h := h1.sub h2
        convert h using 1
        simp only [id_eq]
        ring
      have h3 : iteratedDeriv (m + 3) faddeeva z
          = -2 * iteratedDeriv (m + 1) faddeeva z + -2 * z * iteratedDeriv (m + 2) faddeeva z
            - 2 * ((m : ℂ) + 1) * iteratedDeriv (m + 1) faddeeva z := by
        conv_lhs => rw [show m + 3 = (m + 2) + 1 from rfl, iteratedDeriv_succ, hfun]
        exact hda.deriv
      rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, h3]
      push_cast
      ring

/-! ### Support lemmas for the Cauchy integral representation (DLMF 7.7.2)

The proof of `erf_7_7_2` matches the Faddeeva ODE 7.10.2 against the same ODE
for the Cauchy-type integral `G(w) = (1/(πi)) ∫_ℝ e^{-t²}/(t-w) dt` on the open
upper half-plane, then pins the constant `e^{w²}(w(w) - G(w))` down the ray
`w = iy`, `y → ∞`. -/

section Erf772Support

open MeasureTheory Filter

-- no-dlmf: support lemma for erf_7_7_2 (Cauchy-kernel denominator is nonvanishing)
private lemma sub_ofReal_ne_zero {w : ℂ} (hw : 0 < w.im) (t : ℝ) : (t : ℂ) - w ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.sub_im, Complex.ofReal_im] at him
  linarith

-- no-dlmf: support lemma for erf_7_7_2 (lower bound on the Cauchy-kernel denominator)
private lemma im_le_norm_ofReal_sub (w : ℂ) (t : ℝ) : w.im ≤ ‖(t : ℂ) - w‖ := by
  have h := Complex.abs_im_le_norm ((t : ℂ) - w)
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
  exact (le_abs_self _).trans h

-- no-dlmf: support lemma for erf_7_7_2 (the complex Gaussian on ℝ is the real one)
private lemma cexp_neg_ofReal_sq (t : ℝ) :
    Complex.exp (-(t : ℂ) ^ 2) = ((Real.exp (-t ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  norm_cast

-- no-dlmf: support lemma for erf_7_7_2 (norm bound on the Cauchy kernel)
private lemma norm_cauchyKernel_le {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)‖ ≤ Real.exp (-t ^ 2) / w.im := by
  rw [norm_div, cexp_neg_ofReal_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr
  exact im_le_norm_ofReal_sub w t

-- no-dlmf: support lemma for erf_7_7_2 (norm bound on the squared Cauchy kernel)
private lemma norm_cauchyKernelSq_le {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2‖ ≤ Real.exp (-t ^ 2) / w.im ^ 2 := by
  rw [norm_div, cexp_neg_ofReal_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_pow]
  gcongr
  exact im_le_norm_ofReal_sub w t

-- no-dlmf: support lemma for erf_7_7_2 (norm bound on the t-weighted Cauchy kernel)
private lemma norm_cauchyKernelMul_le {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    ‖2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)‖
      ≤ 2 * (|t| * Real.exp (-t ^ 2)) / w.im := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnum : ‖2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2)‖ = 2 * (|t| * Real.exp (-t ^ 2)) := by
    rw [cexp_neg_ofReal_sq, norm_mul, norm_mul, h2, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, mul_assoc]
  rw [norm_div, hnum]
  gcongr
  exact im_le_norm_ofReal_sub w t

-- no-dlmf: support lemma for erf_7_7_2 (integrable dominating function)
private lemma integrable_gaussian_div_const (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-t ^ 2) / c) := by
  simpa using (integrable_exp_neg_mul_sq one_pos).div_const c

-- no-dlmf: support lemma for erf_7_7_2 (integrability of the Cauchy kernel)
private lemma integrable_cauchyKernel {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => sub_ofReal_ne_zero hw t)
  exact Integrable.mono' (integrable_gaussian_div_const w.im) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cauchyKernel_le hw))

-- no-dlmf: support lemma for erf_7_7_2 (integrability of the squared Cauchy kernel)
private lemma integrable_cauchyKernelSq {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop)
      (fun t => pow_ne_zero 2 (sub_ofReal_ne_zero hw t))
  exact Integrable.mono' (integrable_gaussian_div_const (w.im ^ 2)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cauchyKernelSq_le hw))

-- no-dlmf: support lemma for erf_7_7_2 (integrability of the t-weighted Cauchy kernel)
private lemma integrable_cauchyKernelMul {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun t : ℝ => 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)) := by
  have hcont : Continuous
      (fun t : ℝ => 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => sub_ofReal_ne_zero hw t)
  have hg : Integrable (fun t : ℝ => 2 * (|t| * Real.exp (-t ^ 2)) / w.im) := by
    have := ((integrable_mul_exp_neg_mul_sq one_pos).abs.const_mul 2).div_const w.im
    simpa [abs_mul, Real.abs_exp] using this
  exact Integrable.mono' hg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cauchyKernelMul_le hw))

-- no-dlmf: support lemma for erf_7_7_2 (integrability of the complex Gaussian)
private lemma integrable_cexp_neg_ofReal_sq :
    Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2)) := by
  have h : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq one_pos
  refine (h.ofReal (𝕜 := ℂ)).congr ?_
  filter_upwards with t
  exact (cexp_neg_ofReal_sq t).symm

-- no-dlmf: support lemma for erf_7_7_2 (the Gaussian integral, complex-valued form)
private lemma integral_cexp_neg_ofReal_sq :
    ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have h1 : (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2)) = ∫ t : ℝ, ((Real.exp (-t ^ 2) : ℝ) : ℂ) := by
    congr 1
    funext t
    exact cexp_neg_ofReal_sq t
  rw [h1, integral_complex_ofReal]
  norm_cast
  simpa using integral_gaussian 1

-- no-dlmf: support lemma for erf_7_7_2 (t-derivative of the Cauchy kernel)
private lemma cauchyKernel_hasDerivAt_ofReal {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2) / ((s : ℂ) - w))
      (-(2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
        - Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) t := by
  have hgauss : HasDerivAt (fun u : ℂ => Complex.exp (-u ^ 2))
      (-2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2)) (t : ℂ) := by
    have hinner : HasDerivAt (fun u : ℂ => -u ^ 2) (-2 * (t : ℂ)) (t : ℂ) := by
      have h := ((hasDerivAt_id (t : ℂ)).pow 2).neg
      convert h using 1
      simp only [id_eq]
      ring
    have h := hinner.cexp
    convert h using 1
    ring
  have hden : HasDerivAt (fun u : ℂ => u - w) 1 (t : ℂ) := (hasDerivAt_id _).sub_const w
  have hdiv := hgauss.div hden (sub_ofReal_ne_zero hw t)
  have hcomp := hdiv.comp_ofReal
  convert hcomp using 1
  field_simp

-- no-dlmf: support lemma for erf_7_7_2 (∫_ℝ d/dt[e^{-t²}/(t-w)] dt = 0 by decay at ±∞)
private lemma integral_cauchyKernel_deriv_eq_zero {w : ℂ} (hw : 0 < w.im) :
    ∫ t : ℝ, (-(2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
        - Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) = 0 := by
  set f : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) with hf
  set f' : ℝ → ℂ := fun t => -(2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
      - Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2 with hf'
  have hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := cauchyKernel_hasDerivAt_ofReal hw
  have hint' : Integrable f' := (integrable_cauchyKernelMul hw).neg.sub (integrable_cauchyKernelSq hw)
  have hcont : Continuous f :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => sub_ofReal_ne_zero hw t)
  have hdecay_top : Tendsto (fun t : ℝ => Real.exp (-t ^ 2) / w.im) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have h3 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    simpa using h3.div_const w.im
  have hdecay_bot : Tendsto (fun t : ℝ => Real.exp (-t ^ 2) / w.im) atBot (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have h1 : Tendsto (fun t : ℝ => t ^ 2) atBot atTop := by
      have := h0.comp tendsto_neg_atBot_atTop
      simpa [Function.comp_def, neg_sq] using this
    have h3 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    simpa using h3.div_const w.im
  have htop : Tendsto f atTop (nhds 0) :=
    squeeze_zero_norm (fun t => norm_cauchyKernel_le hw t) hdecay_top
  have hbot : Tendsto f atBot (nhds 0) :=
    squeeze_zero_norm (fun t => norm_cauchyKernel_le hw t) hdecay_bot
  have hIoi : ∫ t in Set.Ioi (0 : ℝ), f' t = 0 - f 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun x _ => hderiv x) hint'.integrableOn htop
  have hIic : ∫ t in Set.Iic (0 : ℝ), f' t = f 0 - 0 :=
    MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun x _ => hderiv x) hint'.integrableOn hbot
  have hsum := intervalIntegral.integral_Iic_add_Ioi
    (hint'.integrableOn (s := Set.Iic 0)) (hint'.integrableOn (s := Set.Ioi 0))
  rw [hIic, hIoi] at hsum
  rw [← hsum]
  ring

-- no-dlmf: support lemma for erf_7_7_2 (differentiation under the integral sign)
private lemma hasDerivAt_integral_cauchyKernel {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun u : ℂ => ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u))
      (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) w := by
  have hball : Metric.ball w (w.im / 2) ∈ nhds w := Metric.ball_mem_nhds w (by linarith)
  have hxim : ∀ x ∈ Metric.ball w (w.im / 2), w.im / 2 < x.im := by
    intro x hx
    have h := Complex.abs_im_le_norm (x - w)
    rw [Complex.sub_im] at h
    have hd := mem_ball_iff_norm.mp hx
    have h2 := abs_lt.mp (lt_of_le_of_lt h hd)
    linarith [h2.1]
  have hd2 : ∀ x ∈ Metric.ball w (w.im / 2), ∀ t : ℝ,
      HasDerivAt (fun u : ℂ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u))
        (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - x) ^ 2) x := by
    intro x hx t
    have hx0 : 0 < x.im := lt_trans (by linarith) (hxim x hx)
    have h1 : HasDerivAt (fun u : ℂ => (t : ℂ) - u) (-1) x :=
      (hasDerivAt_id x).const_sub (t : ℂ)
    have h3 := (hasDerivAt_const x (Complex.exp (-(t : ℂ) ^ 2))).div h1 (sub_ofReal_ne_zero hx0 t)
    convert h3 using 1
    ring
  have hmeas : ∀ᶠ x in nhds w, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - x)) MeasureTheory.volume := by
    refine Filter.eventually_of_mem hball (fun x hx => ?_)
    have hx0 : 0 < x.im := lt_trans (by linarith) (hxim x hx)
    exact (Continuous.div (by fun_prop) (by fun_prop)
      (fun t => sub_ofReal_ne_zero hx0 t)).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂MeasureTheory.volume, ∀ x ∈ Metric.ball w (w.im / 2),
      ‖Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - x) ^ 2‖ ≤ Real.exp (-t ^ 2) / (w.im / 2) ^ 2 := by
    refine Filter.Eventually.of_forall (fun t x hx => ?_)
    have hx0 : 0 < x.im := lt_trans (by linarith) (hxim x hx)
    refine (norm_cauchyKernelSq_le hx0 t).trans ?_
    gcongr
    exact (hxim x hx).le
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2) MeasureTheory.volume :=
    (Continuous.div (by fun_prop) (by fun_prop)
      (fun t => pow_ne_zero 2 (sub_ofReal_ne_zero hw t))).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeas
    (integrable_cauchyKernel hw) hmeas' hbound (integrable_gaussian_div_const ((w.im / 2) ^ 2))
    (Filter.Eventually.of_forall (fun t x hx => hd2 x hx t))).2

-- no-dlmf: support lemma for erf_7_7_2 (the ∫kernel² integral via integration by parts)
private lemma integral_cauchyKernelSq_eq {w : ℂ} (hw : 0 < w.im) :
    (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2)
      = -(2 * w) * (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
        - 2 * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hneg : Integrable
      (fun t : ℝ => -(2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))) :=
    (integrable_cauchyKernelMul hw).neg
  have hsub := integral_sub hneg (integrable_cauchyKernelSq hw)
  rw [integral_cauchyKernel_deriv_eq_zero hw] at hsub
  have h3 : (∫ t : ℝ, -(2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)))
      = -∫ t : ℝ, 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) := integral_neg _
  have h2 : (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) ^ 2)
      = -∫ t : ℝ, 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) := by
    linear_combination hsub + h3
  have hpt : ∀ t : ℝ, (2 * w) * (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
      = 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)
        - 2 * Complex.exp (-(t : ℂ) ^ 2) := by
    intro t
    have h := sub_ofReal_ne_zero hw t
    field_simp
    ring
  have h4 : (∫ t : ℝ, (2 * w) * (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)))
      = (∫ t : ℝ, 2 * (t : ℂ) * Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
        - ∫ t : ℝ, 2 * Complex.exp (-(t : ℂ) ^ 2) := by
    rw [← integral_sub (integrable_cauchyKernelMul hw) (integrable_cexp_neg_ofReal_sq.const_mul 2)]
    congr 1
    funext t
    exact hpt t
  have h5 : (∫ t : ℝ, (2 * w) * (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w)))
      = (2 * w) * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w) := integral_const_mul _ _
  have h6 : (∫ t : ℝ, 2 * Complex.exp (-(t : ℂ) ^ 2))
      = 2 * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_cexp_neg_ofReal_sq]
  rw [h2]
  linear_combination h4 - h5 - h6

-- no-dlmf: support lemma for erf_7_7_2 (the Cauchy integral satisfies the Faddeeva ODE 7.10.2)
private lemma hasDerivAt_cauchyG {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun u : ℂ => (1 / ((Real.pi : ℂ) * Complex.I))
        * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - u))
      (-2 * w * ((1 / ((Real.pi : ℂ) * Complex.I))
          * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - w))
        + 2 * Complex.I / (Real.sqrt Real.pi : ℂ)) w := by
  have h := (hasDerivAt_integral_cauchyKernel hw).const_mul (1 / ((Real.pi : ℂ) * Complex.I))
  convert h using 1
  rw [integral_cauchyKernelSq_eq hw]
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (Real.pi : ℂ) * Complex.I_sq + hsq

-- no-dlmf: chain link 7.7.2 (assembled in `erf_7_7_2` below, alongside
-- `erf_7_7_2_halfline`); this half is the full-line Cauchy integral representation
/-- Cauchy-type integral representation
`w(z) = (1/(πi)) ∫_{-∞}^{∞} e^{-t²}/(t - z) dt` for `Im z > 0` (DLMF 7.7.2). -/
theorem faddeeva_eq_cauchyIntegral_real {z : ℂ} (hz : 0 < z.im) :
    faddeeva z =
      (1 / ((Real.pi : ℂ) * Complex.I)) * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z) := by
  -- `φ(u) := e^{u²}(w(u) − G(u))` has zero derivative on the upper half-plane
  -- (both `w` and `G` solve 7.10.2), hence is constant there; the constant is 0
  -- because `φ(iy) → 0` as `y → ∞`.
  set S : Set ℂ := {u : ℂ | 0 < u.im} with hS
  set φ : ℂ → ℂ := fun v => Complex.exp (v ^ 2) * (faddeeva v
      - (1 / ((Real.pi : ℂ) * Complex.I)) * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - v))
    with hφ
  have hopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_im
  have hconv : Convex ℝ S := convex_halfSpace_im_gt 0
  have hφderiv : ∀ u ∈ S, HasDerivAt φ 0 u := by
    intro u hu
    have hu' : 0 < u.im := hu
    have hexp : HasDerivAt (fun v : ℂ => Complex.exp (v ^ 2))
        (2 * u * Complex.exp (u ^ 2)) u := by
      have hinner : HasDerivAt (fun v : ℂ => v ^ 2) (2 * u) u := by
        have h := (hasDerivAt_id u).pow 2
        convert h using 1
        simp only [id_eq]
        push_cast
        ring
      have h := hinner.cexp
      convert h using 1
      ring
    have hd := (erf_7_10_2 u).sub (hasDerivAt_cauchyG hu')
    have h := hexp.mul hd
    rw [hφ]
    convert h using 1
    simp only [Pi.sub_apply]
    ring
  have hdiffOn : DifferentiableOn ℂ φ S := fun u hu =>
    ((hφderiv u hu).differentiableAt).differentiableWithinAt
  have hfd : ∀ u ∈ S, fderivWithin ℂ φ S u = 0 := by
    intro u hu
    rw [fderivWithin_of_isOpen hopen hu, (hφderiv u hu).hasFDerivAt.fderiv]
    ext
    simp
  have hzS : z ∈ S := hz
  have hconstφ : ∀ y : ℝ, 0 < y → φ (Complex.I * (y : ℂ)) = φ z := by
    intro y hy
    have hyS : Complex.I * (y : ℂ) ∈ S := by
      simpa [hS] using hy
    exact hconv.is_const_of_fderivWithin_eq_zero hdiffOn hfd hyS hzS
  -- the first piece of φ(iy) is erfc(y), which tends to 0
  have hterm1 : ∀ y : ℝ, Complex.exp ((Complex.I * (y : ℂ)) ^ 2) * faddeeva (Complex.I * (y : ℂ))
      = ((erfc y : ℝ) : ℂ) := by
    intro y
    rw [faddeeva_eq_cerfc_neg_I_mul]
    have harg : -(Complex.I * (Complex.I * (y : ℂ))) = ((y : ℝ) : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    rw [harg, cerfc_ofReal, ← mul_assoc, ← Complex.exp_add]
    simp
  have hlim1 : Filter.Tendsto (fun y : ℝ =>
      Complex.exp ((Complex.I * (y : ℂ)) ^ 2) * faddeeva (Complex.I * (y : ℂ)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun y : ℝ => ((erfc y : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp erfc_tendsto_zero
      simpa using h2
    exact Filter.Tendsto.congr (fun y => (hterm1 y).symm) h0
  -- the second piece is O(e^{-y²}) and also tends to 0
  have hlim2 : Filter.Tendsto (fun y : ℝ =>
      Complex.exp ((Complex.I * (y : ℂ)) ^ 2) * ((1 / ((Real.pi : ℂ) * Complex.I))
        * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - Complex.I * (y : ℂ))))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun y : ℝ => Real.exp (-y ^ 2) * (Real.sqrt Real.pi / Real.pi)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy1
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
      have him : (Complex.I * (y : ℂ)).im = y := by simp
      have hexpnorm : ‖Complex.exp ((Complex.I * (y : ℂ)) ^ 2)‖ = Real.exp (-y ^ 2) := by
        rw [Complex.norm_exp]
        congr 1
        have h2 : (Complex.I * (y : ℂ)) ^ 2 = ((-(y ^ 2) : ℝ) : ℂ) := by
          push_cast
          linear_combination (y : ℂ) ^ 2 * Complex.I_sq
        rw [h2, Complex.ofReal_re]
      have hker : ‖∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - Complex.I * (y : ℂ))‖
          ≤ Real.sqrt Real.pi / y := by
        have hyim : 0 < (Complex.I * (y : ℂ)).im := by rw [him]; exact hy0
        have hb := MeasureTheory.norm_integral_le_of_norm_le
          (integrable_gaussian_div_const y)
          (Filter.Eventually.of_forall (fun t => by
            have h := norm_cauchyKernel_le hyim t
            rwa [him] at h))
        refine hb.trans ?_
        rw [MeasureTheory.integral_div]
        have hg : (∫ t : ℝ, Real.exp (-t ^ 2)) = Real.sqrt Real.pi := by
          simpa using integral_gaussian 1
        rw [hg]
      have hc : ‖(1 / ((Real.pi : ℂ) * Complex.I))‖ = 1 / Real.pi := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      rw [norm_mul, norm_mul, hexpnorm, hc]
      have hstep : 1 / Real.pi * (Real.sqrt Real.pi / y) ≤ Real.sqrt Real.pi / Real.pi := by
        have heq : (1 : ℝ) / Real.pi * (Real.sqrt Real.pi / y)
            = Real.sqrt Real.pi / (Real.pi * y) := by ring
        rw [heq]
        gcongr
        nlinarith [Real.pi_pos]
      calc Real.exp (-y ^ 2) * (1 / Real.pi
              * ‖∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - Complex.I * (y : ℂ))‖)
          ≤ Real.exp (-y ^ 2) * (1 / Real.pi * (Real.sqrt Real.pi / y)) := by
            gcongr
        _ ≤ Real.exp (-y ^ 2) * (Real.sqrt Real.pi / Real.pi) := by
            gcongr
    · have h1 : Filter.Tendsto (fun y : ℝ => Real.exp (-y ^ 2)) Filter.atTop (nhds 0) := by
        have h1' : Filter.Tendsto (fun t : ℝ => t ^ 2) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop two_ne_zero
        exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1')
      simpa using h1.mul_const (Real.sqrt Real.pi / Real.pi)
  -- combine: φ(iy) → 0
  have hφlim : Filter.Tendsto (fun y : ℝ => φ (Complex.I * (y : ℂ))) Filter.atTop (nhds 0) := by
    have hsplit : ∀ y : ℝ, φ (Complex.I * (y : ℂ))
        = Complex.exp ((Complex.I * (y : ℂ)) ^ 2) * faddeeva (Complex.I * (y : ℂ))
          - Complex.exp ((Complex.I * (y : ℂ)) ^ 2) * ((1 / ((Real.pi : ℂ) * Complex.I))
            * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - Complex.I * (y : ℂ))) := by
      intro y
      rw [hφ]
      ring
    have h := hlim1.sub hlim2
    rw [sub_zero] at h
    exact Filter.Tendsto.congr (fun y => (hsplit y).symm) h
  -- hence the constant value of φ on S is 0
  have hconst_ev : ∀ᶠ y : ℝ in Filter.atTop, φ (Complex.I * (y : ℂ)) = φ z :=
    (Filter.eventually_gt_atTop 0).mono (fun y hy => hconstφ y hy)
  have hφz : φ z = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hφlim.congr' hconst_ev)
  -- conclude
  have hsub : faddeeva z - (1 / ((Real.pi : ℂ) * Complex.I))
      * (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)) = 0 := by
    rcases mul_eq_zero.mp hφz with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact h
  exact sub_eq_zero.mp hsub

-- no-dlmf: support lemma for erf_7_7_2 (shifted Cauchy-kernel denominator is nonvanishing)
private lemma add_ofReal_ne_zero {w : ℂ} (hw : 0 < w.im) (t : ℝ) : (t : ℂ) + w ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.add_im, Complex.ofReal_im] at him
  linarith

-- no-dlmf: support lemma for erf_7_7_2 (norm bound on the shifted Cauchy kernel)
private lemma norm_cauchyKernelAdd_le {w : ℂ} (hw : 0 < w.im) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + w)‖ ≤ Real.exp (-t ^ 2) / w.im := by
  rw [norm_div, cexp_neg_ofReal_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr
  have h := Complex.abs_im_le_norm ((t : ℂ) + w)
  rw [Complex.add_im, Complex.ofReal_im, zero_add] at h
  exact (le_abs_self _).trans h

-- no-dlmf: support lemma for erf_7_7_2 (integrability of the shifted Cauchy kernel)
private lemma integrable_cauchyKernelAdd {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + w)) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + w)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => add_ofReal_ne_zero hw t)
  exact Integrable.mono' (integrable_gaussian_div_const w.im) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_cauchyKernelAdd_le hw))

-- no-dlmf: chain link 7.7.2 (assembled in `erf_7_7_2` below, alongside
-- `faddeeva_eq_cauchyIntegral_real`); the half-line form, obtained from the full-line
-- Cauchy integral by splitting `ℝ` at `0` and reflecting the negative half via
-- `integral_comp_neg_Ioi`, using the evenness of `e^{-t²}`
private lemma erf_7_7_2_halfline {z : ℂ} (hz : 0 < z.im) :
    faddeeva z =
      (2 * z / ((Real.pi : ℂ) * Complex.I)) *
        ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) ^ 2 - z ^ 2) := by
  set f : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z) with hf
  have hg : ∀ t : ℝ, f (-t) = - (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + z)) := by
    intro t
    simp only [hf]
    have h1 : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
    have h2 : (-(t : ℂ)) ^ 2 = (t : ℂ) ^ 2 := by ring
    have h3 : -(t : ℂ) - z = -((t : ℂ) + z) := by ring
    rw [h1, h2, h3, div_neg]
  have hrefl := integral_comp_neg_Ioi (0 : ℝ) f
  simp only [neg_zero] at hrefl
  -- hrefl : ∫ t in Ioi 0, f (-t) = ∫ t in Iic 0, f t
  have hrefl' : ∫ t in Set.Iic (0 : ℝ), f t
      = - ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + z) := by
    rw [← hrefl, ← MeasureTheory.integral_neg]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hg t)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    ((integrable_cauchyKernel hz).integrableOn (s := Set.Iic (0 : ℝ)))
    ((integrable_cauchyKernel hz).integrableOn (s := Set.Ioi (0 : ℝ)))
  rw [hrefl'] at hsplit
  -- hsplit : -(∫ Ioi 0, g_add) + (∫ Ioi 0, f) = ∫ t : ℝ, f t
  have hptwise : ∀ t ∈ Set.Ioi (0 : ℝ), f t - Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + z)
      = (2 * z) * (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) ^ 2 - z ^ 2)) := by
    intro t _
    simp only [hf]
    have hne1 : (t : ℂ) - z ≠ 0 := sub_ofReal_ne_zero hz t
    have hne2 : (t : ℂ) + z ≠ 0 := add_ofReal_ne_zero hz t
    have hne3 : (t : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
      have heq : (t : ℂ) ^ 2 - z ^ 2 = ((t : ℂ) - z) * ((t : ℂ) + z) := by ring
      rw [heq]
      exact mul_ne_zero hne1 hne2
    field_simp
    ring
  have hInt : ∫ t in Set.Ioi (0 : ℝ), (f t - Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) + z))
      = ∫ t in Set.Ioi (0 : ℝ), (2 * z) * (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) ^ 2 - z ^ 2)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hptwise
  rw [MeasureTheory.integral_sub (integrable_cauchyKernel hz).integrableOn
    (integrable_cauchyKernelAdd hz).integrableOn, MeasureTheory.integral_const_mul] at hInt
  -- hInt : (∫ Ioi 0, f) - (∫ Ioi 0, g_add) = (2*z) * ∫ Ioi 0, exp(-t²)/(t²-z²)
  have hkey : ∫ t : ℝ, f t
      = (2 * z) * ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) ^ 2 - z ^ 2) := by
    linear_combination hInt - hsplit
  rw [faddeeva_eq_cauchyIntegral_real hz, hkey]
  ring

/-- **DLMF 7.7.2**: the Faddeeva function's Cauchy integral representations,
`w(z) = (1/(πi)) ∫_{-∞}^{∞} e^{-t²}/(t-z) dt = (2z/(πi)) ∫_0^∞ e^{-t²}/(t²-z²) dt`,
for `Im z > 0`.

DLMF 7.7.2.
DAG: E-7.7.2.
Numerical: PASS
Verified: verified
-/
theorem erf_7_7_2 {z : ℂ} (hz : 0 < z.im) :
    faddeeva z =
      (1 / ((Real.pi : ℂ) * Complex.I)) * ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z) ∧
    faddeeva z =
      (2 * z / ((Real.pi : ℂ) * Complex.I)) *
        ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) ^ 2 - z ^ 2) :=
  ⟨faddeeva_eq_cauchyIntegral_real hz, erf_7_7_2_halfline hz⟩

end Erf772Support

section Erf773Support

/-! ### The Gaussian-linear half-line integral (support for DLMF 7.7.3 and 7.19.3)

This support block houses the generic integral
`∫₀^∞ e^{-at²+2izt} dt = ½√π·a^{-1/2}·e^{-z²/a}·erfc(-iz·a^{-1/2})` (`ℜa > 0`) and its
ODE-matching infrastructure.  Mathematically this is the content of DLMF 7.7.3, whose
tagged surface `erf_7_7_3` lives in `ComplexErfExtra.lean`; it is homed *here* because
`ComplexErfExtra.lean` imports this file (for `faddeeva`), so the Voigt assembly
`erf_7_19_3` below could not import it from there without a cycle.  `erf_7_7_3` applies
`gaussLin_integral_eq_cerfc` directly. -/

open MeasureTheory Set Filter Topology

-- no-dlmf: real part of the Gaussian-linear exponent `-a t² + c t` for real `t`;
-- support computation for 7.7.3, no DLMF identity number
private theorem gaussLin_re (a c : ℂ) (t : ℝ) :
    (-a*(t:ℂ)^2 + c*(t:ℂ)).re = -a.re*t^2 + c.re*t := by
  simp [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

-- no-dlmf: integrability of the Gaussian-linear integrand `e^{-at²+ct}` on ℝ for
-- `ℜ a > 0` (specialization of Mathlib's `integrable_cexp_quadratic`); support
-- infrastructure for 7.7.3, no DLMF identity number
private theorem integrable_gaussLin {a : ℂ} (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-a*(t:ℂ)^2 + c*(t:ℂ))) := by
  simpa using integrable_cexp_quadratic ha c 0

-- no-dlmf: integrability of the first Gaussian moment `t·e^{-at²+ct}` on ℝ for
-- `ℜ a > 0` (domination by `|t|·e^{-ℜa·t²/2}` after completing the square);
-- support infrastructure for 7.7.3, no DLMF identity number
private theorem integrable_mul_gaussLin {a : ℂ} (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun t : ℝ => (t:ℂ) * Complex.exp (-a*(t:ℂ)^2 + c*(t:ℂ))) := by
  have hr : 0 < a.re / 2 := by linarith
  have hbase : Integrable (fun x : ℝ => |x * Real.exp (-(a.re/2) * x ^ 2)|) :=
    (integrable_mul_exp_neg_mul_sq hr).abs
  have hbound : Integrable (fun x : ℝ =>
      Real.exp (c.re^2 / (2*a.re)) * |x * Real.exp (-(a.re/2) * x ^ 2)|) :=
    hbase.const_mul _
  refine hbound.mono' ?_ ?_
  · fun_prop
  · filter_upwards with t
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, gaussLin_re]
    have key : -a.re*t^2 + c.re*t ≤ c.re^2/(2*a.re) + (-(a.re/2) * t^2) := by
      have h2 : c.re^2/(2*a.re) + (-(a.re/2) * t^2) - (-a.re*t^2 + c.re*t)
          = (a.re*t - c.re)^2/(2*a.re) := by
        field_simp
        ring
      have h3 : (0:ℝ) ≤ (a.re*t - c.re)^2/(2*a.re) :=
        div_nonneg (sq_nonneg _) (by linarith)
      linarith
    calc |t| * Real.exp (-a.re*t^2 + c.re*t)
        ≤ |t| * (Real.exp (c.re^2/(2*a.re)) * Real.exp (-(a.re/2) * t^2)) := by
          rw [← Real.exp_add]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) (abs_nonneg t)
      _ = Real.exp (c.re^2 / (2*a.re)) * (|t| * Real.exp (-(a.re/2) * t^2)) := by ring
      _ = Real.exp (c.re^2 / (2*a.re)) * |t * Real.exp (-(a.re/2) * t^2)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]

-- no-dlmf: decay of the Gaussian-linear integrand at `+∞` (squeeze against
-- `e^{-ℜa·t²/2}`); support infrastructure for 7.7.3, no DLMF identity number
private theorem tendsto_gaussLin_zero {a : ℂ} (ha : 0 < a.re) (c : ℂ) :
    Tendsto (fun t : ℝ => Complex.exp (-a*(t:ℂ)^2 + c*(t:ℂ))) atTop (𝓝 0) := by
  have hr : 0 < a.re / 2 := by linarith
  have hbound : ∀ᶠ t : ℝ in atTop, ‖Complex.exp (-a*(t:ℂ)^2 + c*(t:ℂ))‖
      ≤ Real.exp (c.re^2/(2*a.re)) * Real.exp (-(a.re/2 * t^2)) := by
    filter_upwards with t
    rw [Complex.norm_exp, gaussLin_re, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h2 : c.re^2/(2*a.re) + -(a.re/2 * t^2) - (-a.re*t^2 + c.re*t)
        = (a.re*t - c.re)^2/(2*a.re) := by
      field_simp
      ring
    have h3 : (0:ℝ) ≤ (a.re*t - c.re)^2/(2*a.re) :=
      div_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hg : Tendsto (fun t : ℝ => Real.exp (c.re^2/(2*a.re)) * Real.exp (-(a.re/2 * t^2)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => a.re/2 * t^2) atTop atTop := by
      apply Tendsto.const_mul_atTop hr
      exact tendsto_pow_atTop two_ne_zero
    have h2 : Tendsto (fun t : ℝ => -(a.re/2 * t^2)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h1
    have h3 : Tendsto (fun t : ℝ => Real.exp (-(a.re/2 * t^2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h2
    have h4 := h3.const_mul (Real.exp (c.re^2/(2*a.re)))
    simpa using h4
  exact squeeze_zero_norm' hbound hg

-- no-dlmf: `t`-derivative of the Gaussian-linear integrand along the real line;
-- support infrastructure for 7.7.3, no DLMF identity number
private theorem hasDerivAt_gaussLin {a w : ℂ} (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-a*(s:ℂ)^2 + 2*Complex.I*w*(s:ℂ)))
      ((-2*a*(t:ℂ) + 2*Complex.I*w) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ))) t := by
  have hpow : HasDerivAt (fun u : ℂ => u^2) (2*(t:ℂ)) (t:ℂ) := by
    simpa using hasDerivAt_pow 2 (t:ℂ)
  have h1 : HasDerivAt (fun u : ℂ => -a*u^2) (-a*(2*(t:ℂ))) (t:ℂ) := hpow.const_mul (-a)
  have h2 : HasDerivAt (fun u : ℂ => 2*Complex.I*w*u) (2*Complex.I*w) (t:ℂ) := by
    simpa using (hasDerivAt_id (t:ℂ)).const_mul (2*Complex.I*w)
  have hg : HasDerivAt (fun u : ℂ => -a*u^2 + 2*Complex.I*w*u)
      (-a*(2*(t:ℂ)) + 2*Complex.I*w) (t:ℂ) := h1.add h2
  have hexp := hg.cexp
  have h3 := hexp.comp_ofReal
  convert h3 using 1
  ring

-- no-dlmf: fundamental-theorem evaluation `∫₀^∞ d/dt[e^{-at²+2izt}] dt = -1`
-- (boundary value 1 at `t = 0`, decay at `+∞`); the integration-by-parts input
-- for the 7.7.3 ODE, no DLMF identity number
private theorem integral_gaussLin_deriv {a : ℂ} (ha : 0 < a.re) (w : ℂ) :
    (∫ t in Ioi (0:ℝ), ((-2*a*(t:ℂ) + 2*Complex.I*w)
        * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))) = -1 := by
  have hderiv : ∀ t ∈ Ici (0:ℝ),
      HasDerivAt (fun s : ℝ => Complex.exp (-a*(s:ℂ)^2 + 2*Complex.I*w*(s:ℂ)))
        ((-2*a*(t:ℂ) + 2*Complex.I*w) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ))) t :=
    fun t _ => hasDerivAt_gaussLin t
  have hfeq : (fun t : ℝ => (-2*a*(t:ℂ) + 2*Complex.I*w)
      * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))
      = fun t : ℝ => (-2*a)*((t:ℂ) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))
        + (2*Complex.I*w)*Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)) := by
    funext t; ring
  have hint : Integrable (fun t : ℝ => (-2*a*(t:ℂ) + 2*Complex.I*w)
      * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ))) := by
    rw [hfeq]
    exact ((integrable_mul_gaussLin ha (2*Complex.I*w)).const_mul (-2*a)).add
      ((integrable_gaussLin ha (2*Complex.I*w)).const_mul (2*Complex.I*w))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint.integrableOn
    (tendsto_gaussLin_zero ha (2*Complex.I*w))
  rw [h]
  norm_num

-- no-dlmf: differentiation of `z ↦ ∫₀^∞ e^{-at²+2izt} dt` under the integral sign
-- (dominated locally on a unit ball in `z`); support infrastructure for 7.7.3,
-- no DLMF identity number
private theorem hasDerivAt_gaussLin_integral {a : ℂ} (ha : 0 < a.re) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ)))
      (∫ t in Ioi (0:ℝ), 2*Complex.I*(t:ℂ) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z₀*(t:ℂ)))
      z₀ := by
  have hr : 0 < a.re / 2 := by linarith
  set K : ℝ := 2*(|z₀.im| + 1) with hK
  set bound : ℝ → ℝ := fun t =>
    2 * Real.exp (K^2/(2*a.re)) * |t * Real.exp (-(a.re/2) * t^2)| with hbdef
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (z : ℂ) (t : ℝ) => Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ)))
    (F' := fun (z : ℂ) (t : ℝ) => 2*Complex.I*(t:ℂ)
      * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ)))
    (x₀ := z₀) (bound := bound)
    (μ := volume.restrict (Ioi (0:ℝ))) (s := Metric.ball z₀ 1)
    (Metric.ball_mem_nhds z₀ one_pos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · filter_upwards with z
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · exact (integrable_gaussLin ha (2*Complex.I*z₀)).integrableOn
  · exact ((continuous_const.mul Complex.continuous_ofReal).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have ht0 : (0:ℝ) < t := ht
    have hnorm : ‖2*Complex.I*(t:ℂ) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ))‖
        = 2 * |t| * Real.exp (-a.re*t^2 + (2*Complex.I*z).re*t) := by
      rw [norm_mul, Complex.norm_exp, gaussLin_re]
      simp [Complex.norm_I]
    rw [hnorm, hbdef]
    have him : |z.im| < |z₀.im| + 1 := by
      have h1 : ‖z - z₀‖ < 1 := by
        rw [← dist_eq_norm]; exact hz
      have h2 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        have h5 := Complex.abs_im_le_norm (z - z₀)
        rwa [Complex.sub_im] at h5
      have h6 : |z.im| - |z₀.im| ≤ |z.im - z₀.im| := abs_sub_abs_le_abs_sub _ _
      linarith
    have hcre : (2*Complex.I*z).re = -2*z.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have hexp_le : Real.exp (-a.re*t^2 + (2*Complex.I*z).re*t)
        ≤ Real.exp (K^2/(2*a.re)) * Real.exp (-(a.re/2) * t^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlin : (2*Complex.I*z).re*t ≤ K*t := by
        rw [hcre]
        have h7 : -2*z.im ≤ 2*|z.im| := by
          have h8 := neg_abs_le z.im
          nlinarith [abs_nonneg z.im]
        have hKz : 2*|z.im| ≤ K := by rw [hK]; linarith
        nlinarith
      have h2 : K^2/(2*a.re) + (-(a.re/2) * t^2) - (-a.re*t^2 + K*t)
          = (a.re*t - K)^2/(2*a.re) := by
        field_simp
        ring
      have h3 : (0:ℝ) ≤ (a.re*t - K)^2/(2*a.re) :=
        div_nonneg (sq_nonneg _) (by linarith)
      linarith
    calc 2 * |t| * Real.exp (-a.re*t^2 + (2*Complex.I*z).re*t)
        ≤ 2 * |t| * (Real.exp (K^2/(2*a.re)) * Real.exp (-(a.re/2) * t^2)) := by
          apply mul_le_mul_of_nonneg_left hexp_le
          positivity
      _ = 2 * Real.exp (K^2/(2*a.re)) * (|t| * Real.exp (-(a.re/2) * t^2)) := by ring
      _ = 2 * Real.exp (K^2/(2*a.re)) * |t * Real.exp (-(a.re/2) * t^2)| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  · exact ((integrable_mul_exp_neg_mul_sq hr).abs.const_mul _).integrableOn
  · filter_upwards with t z hz
    have h1 : HasDerivAt (fun z : ℂ => 2*Complex.I*z*(t:ℂ)) (2*Complex.I*(t:ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (2*Complex.I)).mul_const (t:ℂ)
    have hg : HasDerivAt (fun z : ℂ => -a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ))
        (2*Complex.I*(t:ℂ)) z := h1.const_add (-a*(t:ℂ)^2)
    have h2 := hg.cexp
    convert h2 using 1
    ring

-- no-dlmf: the principal half-power of a right-half-plane point has positive real
-- part (`|arg| < π/4` after halving); cpow support for 7.7.3, no DLMF identity number
private theorem re_cpow_half_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w ^ ((1:ℂ)/2)).re := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
  have him : (Complex.log w * ((1:ℂ)/2)).im = w.arg / 2 := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  rw [him]
  have harg : |w.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have harg' := abs_lt.mp harg
  have hcos : 0 < Real.cos (w.arg / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> [linarith [Real.pi_pos]; linarith [Real.pi_pos]]
  positivity

-- no-dlmf: squaring is injective on the open right half-plane (`u+v ≠ 0` there);
-- support lemma for identifying principal square roots, no DLMF identity number
private theorem eq_of_sq_eq_sq_of_pos_re {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re)
    (h : u^2 = v^2) : u = v := by
  have hfac : (u - v) * (u + v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact sub_eq_zero.mp h1
  · exfalso
    have h3 : (u + v).re = 0 := by rw [h2]; simp
    rw [Complex.add_re] at h3
    linarith

-- no-dlmf: `a^{-1/2}·a^{-1/2} = a⁻¹` for `a ≠ 0` (cpow addition law); support
-- algebra for 7.7.3, no DLMF identity number
private theorem cpow_neg_half_mul_self {a : ℂ} (ha : 0 < a.re) :
    a^(-(1:ℂ)/2) * a^(-(1:ℂ)/2) = a⁻¹ := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  rw [← Complex.cpow_add _ _ ha0]
  norm_num [Complex.cpow_neg_one]

-- no-dlmf: positivity of `ℜ(a^{-1/2})` on the right half-plane; cpow support for
-- 7.7.3, no DLMF identity number
private theorem re_cpow_neg_half_pos {a : ℂ} (ha : 0 < a.re) : 0 < (a^(-(1:ℂ)/2)).re := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have h1 : 0 < (a ^ ((1:ℂ)/2)).re := re_cpow_half_pos ha
  have hne : a ^ ((1:ℂ)/2) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, ha0]
  have h2 : a^(-(1:ℂ)/2) = (a ^ ((1:ℂ)/2))⁻¹ := by
    rw [neg_div, Complex.cpow_neg]
  rw [h2, Complex.inv_re]
  exact div_pos h1 (Complex.normSq_pos.mpr hne)

-- no-dlmf: reconciliation of Mathlib's half-line Gaussian value `(π/a)^{1/2}/2`
-- with the DLMF normalization `½√π·a^{-1/2}` (both sides square to `π/(4a)` and
-- have positive real part); support algebra for 7.7.3, no DLMF identity number
private theorem pi_div_cpow_half_eq {a : ℂ} (ha : 0 < a.re) :
    ((Real.pi : ℂ) / a) ^ ((1:ℂ)/2) / 2 = (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have hπa0 : (Real.pi : ℂ)/a ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) ha0
  have hrea : 0 < ((Real.pi:ℂ)/a).re := by
    rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
    have h5 : 0 < a.re / Complex.normSq a :=
      div_pos ha (Complex.normSq_pos.mpr ha0)
    positivity
  have hueq : ((Real.pi : ℂ) / a) ^ ((1:ℂ)/2) = (Real.sqrt Real.pi : ℂ) * a^(-(1:ℂ)/2) := by
    apply eq_of_sq_eq_sq_of_pos_re (re_cpow_half_pos hrea)
    · rw [Complex.re_ofReal_mul]
      have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      have h6 := re_cpow_neg_half_pos ha
      positivity
    · have hu2 : (((Real.pi : ℂ) / a) ^ ((1:ℂ)/2))^2 = (Real.pi : ℂ) / a := by
        rw [sq, ← Complex.cpow_add _ _ hπa0]
        norm_num [Complex.cpow_one]
      have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ)^2 = (Real.pi : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
      have hv2 : ((Real.sqrt Real.pi : ℂ) * a^(-(1:ℂ)/2))^2 = (Real.pi : ℂ) * a⁻¹ := by
        calc ((Real.sqrt Real.pi : ℂ) * a^(-(1:ℂ)/2))^2
            = ((Real.sqrt Real.pi : ℝ) : ℂ)^2 * (a^(-(1:ℂ)/2) * a^(-(1:ℂ)/2)) := by ring
          _ = (Real.pi : ℂ) * a⁻¹ := by rw [hsq, cpow_neg_half_mul_self ha]
      rw [hu2, hv2, div_eq_mul_inv]
  rw [hueq]
  ring

-- no-dlmf: the 7.7.3 right-hand side satisfies the ODE `R' = i/a - (2z/a)R`
-- (product/chain rule through `cerfc` and the Gaussian factor); support
-- infrastructure for 7.7.3, no DLMF identity number
private theorem hasDerivAt_erf773_rhs {a : ℂ} (ha : 0 < a.re) (w : ℂ) :
    HasDerivAt (fun u : ℂ => (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-u^2/a)
        *cerfc (-Complex.I*u*a^(-(1:ℂ)/2)))
      (Complex.I/a - 2*w/a * ((1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-w^2/a)
        *cerfc (-Complex.I*w*a^(-(1:ℂ)/2)))) w := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have hπ0 : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  set c : ℂ := a^(-(1:ℂ)/2) with hc
  have hc2 : c * c = a⁻¹ := cpow_neg_half_mul_self ha
  have hE : HasDerivAt (fun u : ℂ => Complex.exp (-u^2/a))
      (Complex.exp (-w^2/a) * (-(2*w)/a)) w := by
    have hp : HasDerivAt (fun u : ℂ => u^2) (2*w) w := by
      simpa using hasDerivAt_pow 2 w
    have hin : HasDerivAt (fun u : ℂ => -u^2/a) (-(2*w)/a) w := (hp.neg).div_const a
    exact hin.cexp
  have hsq : -(-Complex.I*w*c)^2 = w^2/a := by
    have h1 : (-Complex.I*w*c)^2 = Complex.I^2 * (w^2 * (c*c)) := by ring
    rw [Complex.I_sq, hc2] at h1
    rw [h1, div_eq_mul_inv]
    ring
  have hinner : HasDerivAt (fun u : ℂ => -Complex.I*u*c) (-Complex.I*c) w := by
    simpa using ((hasDerivAt_id w).const_mul (-Complex.I)).mul_const c
  have hcerf : HasDerivAt (fun u : ℂ => cerf (-Complex.I*u*c))
      ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (w^2/a) * (-Complex.I*c)) w := by
    have h := (hasDerivAt_cerf (-Complex.I*w*c)).comp w hinner
    rw [hsq] at h
    exact h
  have hG : HasDerivAt (fun u : ℂ => cerfc (-Complex.I*u*c))
      (-((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (w^2/a) * (-Complex.I*c))) w := by
    have hfun : (fun u : ℂ => cerfc (-Complex.I*u*c))
        = fun u : ℂ => 1 - cerf (-Complex.I*u*c) := by
      funext u; rfl
    rw [hfun]
    exact hcerf.const_sub 1
  have hprod := (hE.const_mul ((1/2)*(Real.sqrt Real.pi : ℂ)*c)).mul hG
  convert hprod using 1
  have hEX : Complex.exp (-w^2/a) * Complex.exp (w^2/a) = 1 := by
    rw [← Complex.exp_add]
    have h0 : -w^2/a + w^2/a = 0 := by ring
    rw [h0, Complex.exp_zero]
  have hB : (1/2)*(Real.sqrt Real.pi : ℂ)*c * Complex.exp (-w^2/a)
      * -((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (w^2/a) * (-Complex.I*c))
      = Complex.I/a := by
    have h1 : (1/2)*(Real.sqrt Real.pi : ℂ)*c * Complex.exp (-w^2/a)
        * -((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (w^2/a) * (-Complex.I*c))
        = ((Real.sqrt Real.pi : ℂ) * (2 / (Real.sqrt Real.pi : ℂ)) / 2) * Complex.I
          * (c*c) * (Complex.exp (-w^2/a) * Complex.exp (w^2/a)) := by ring
    have hππ : (Real.sqrt Real.pi : ℂ) * (2 / (Real.sqrt Real.pi : ℂ)) = 2 := by
      field_simp
    rw [h1, hππ, hc2, hEX]
    rw [div_eq_mul_inv]
    ring_nf
  have hA : (1/2)*(Real.sqrt Real.pi : ℂ)*c * (Complex.exp (-w^2/a) * (-(2*w)/a))
      * cerfc (-Complex.I*w*c)
      = -(2*w/a * ((1/2)*(Real.sqrt Real.pi : ℂ)*c*Complex.exp (-w^2/a)
          *cerfc (-Complex.I*w*c))) := by ring
  rw [hA, hB]
  ring


-- no-dlmf: generic Gaussian-linear half-line integral; the mathematical content of
-- DLMF 7.7.3, whose tagged display surface is `erf_7_7_3` in ComplexErfExtra.lean
-- (which applies this lemma).  Homed here to avoid an import cycle — see the section
-- comment above.
theorem gaussLin_integral_eq_cerfc {a z : ℂ} (ha : 0 < a.re) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*z*(t:ℂ)))
      = (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-z^2/a)
          *cerfc (-Complex.I*z*a^(-(1:ℂ)/2)) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  -- both sides satisfy the same first-order linear ODE `y' = i/a - (2z/a)y` in `z`
  have hL' : ∀ w : ℂ, HasDerivAt
      (fun u : ℂ => ∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*u*(t:ℂ)))
      (Complex.I/a - 2*w/a
        * ∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ))) w := by
    intro w
    have hd := hasDerivAt_gaussLin_integral ha w
    have hibp := integral_gaussLin_deriv ha w
    have hfeq : (fun t : ℝ => (-2*a*(t:ℂ) + 2*Complex.I*w)
        * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))
        = fun t : ℝ => (-2*a)*((t:ℂ) * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))
          + (2*Complex.I*w)*Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)) := by
      funext t; ring
    rw [hfeq] at hibp
    rw [integral_add
        (((integrable_mul_gaussLin ha (2*Complex.I*w)).const_mul (-2*a)).integrableOn)
        (((integrable_gaussLin ha (2*Complex.I*w)).const_mul (2*Complex.I*w)).integrableOn),
      integral_const_mul, integral_const_mul] at hibp
    have hM : (∫ t in Ioi (0:ℝ), 2*Complex.I*(t:ℂ)
        * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)))
        = 2*Complex.I * ∫ t in Ioi (0:ℝ), (t:ℂ)
            * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)) := by
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    rw [hM] at hd
    set M : ℂ := ∫ t in Ioi (0:ℝ), (t:ℂ)
      * Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)) with hMdef
    set L : ℂ := ∫ t in Ioi (0:ℝ),
      Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*w*(t:ℂ)) with hLdef
    convert hd using 1
    field_simp
    linear_combination Complex.I * hibp - 2*w*L*Complex.I_sq
  have hR' : ∀ w : ℂ, HasDerivAt
      (fun u : ℂ => (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-u^2/a)
        *cerfc (-Complex.I*u*a^(-(1:ℂ)/2)))
      (Complex.I/a - 2*w/a * ((1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)
        *Complex.exp (-w^2/a)*cerfc (-Complex.I*w*a^(-(1:ℂ)/2)))) w :=
    fun w => hasDerivAt_erf773_rhs ha w
  -- hence the exponentially-weighted difference has zero derivative everywhere
  have hF' : ∀ w : ℂ, HasDerivAt
      (fun u : ℂ => Complex.exp (u^2/a)
        * ((∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*u*(t:ℂ)))
          - (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-u^2/a)
            *cerfc (-Complex.I*u*a^(-(1:ℂ)/2)))) 0 w := by
    intro w
    have hEd : HasDerivAt (fun u : ℂ => Complex.exp (u^2/a))
        (Complex.exp (w^2/a) * (2*w/a)) w := by
      have hp : HasDerivAt (fun u : ℂ => u^2) (2*w) w := by
        simpa using hasDerivAt_pow 2 w
      have hin : HasDerivAt (fun u : ℂ => u^2/a) (2*w/a) w := hp.div_const a
      exact hin.cexp
    have hsub := (hL' w).sub (hR' w)
    have hmul := hEd.mul hsub
    convert hmul using 1
    simp only [Pi.sub_apply]
    ring
  -- a globally zero derivative forces the weighted difference to be constant
  have hconst := is_const_of_deriv_eq_zero
    (fun w => (hF' w).differentiableAt) (fun w => (hF' w).deriv) z 0
  -- pin the constant at `z = 0` via the complex half-line Gaussian integral
  have hL0 : (∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*(0:ℂ)*(t:ℂ)))
      = ((Real.pi:ℂ)/a)^((1:ℂ)/2)/2 := by
    have hfun : (fun t : ℝ => Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*(0:ℂ)*(t:ℂ)))
        = fun t : ℝ => Complex.exp (-a*(t:ℂ)^2) := by
      funext t
      norm_num
    rw [hfun]
    exact integral_gaussian_complex_Ioi ha
  have hF0 : Complex.exp ((0:ℂ)^2/a)
      * ((∫ t in Ioi (0:ℝ), Complex.exp (-a*(t:ℂ)^2 + 2*Complex.I*(0:ℂ)*(t:ℂ)))
        - (1/2)*(Real.sqrt Real.pi : ℂ)*a^(-(1:ℂ)/2)*Complex.exp (-(0:ℂ)^2/a)
          *cerfc (-Complex.I*(0:ℂ)*a^(-(1:ℂ)/2))) = 0 := by
    rw [hL0, pi_div_cpow_half_eq ha]
    norm_num [cerfc_zero]
  rw [hF0] at hconst
  have hne := Complex.exp_ne_zero (z^2/a)
  have hzero := (mul_eq_zero.mp hconst).resolve_left hne
  exact sub_eq_zero.mp hzero

-- no-dlmf: integrability of `e^{-s-ts²}·g(s)` on `(0,∞)` for bounded continuous `g`;
-- support for the 7.19.3 assembly, no DLMF identity number
private theorem integrableOn_exp_quad_trig {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : ∀ s, |g s| ≤ 1) (hcont : Continuous g) :
    IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * g s) (Set.Ioi 0) := by
  have hexpInt : Integrable (fun s : ℝ => Real.exp (-s)) (volume.restrict (Set.Ioi 0)) := by
    have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
    simpa [neg_mul, one_mul] using this
  refine hexpInt.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc Real.exp (-s - t * s ^ 2) * |g s|
      ≤ Real.exp (-s - t * s ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (hg s) (Real.exp_pos _).le
    _ ≤ Real.exp (-s) := by
        rw [mul_one]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg s, ht.le])

/-- Voigt combination `U(x,t) + iV(x,t) = √(π/(4t))·e^{z²}·erfc(z)` with
`z = (1 - ix)/(2√t)` (DLMF 7.19.3). The hypotheses `x : ℝ`, `t : ℝ`, `0 < t`
are not extra restrictions: they are DLMF's own domain for `U`, `V`,
established at 7.19.1/7.19.2 (`x ∈ ℝ`, `t > 0`) and inherited by 7.19.3,
which only additionally fixes `z = (1 - ix)/(2√t)`.

DLMF 7.19.3.
DAG: E-7.19.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_3 (x t : ℝ) (ht : 0 < t) :
    (FLMF.Voigt.voigtU x t : ℂ) + Complex.I * (FLMF.Voigt.voigtV x t : ℂ)
      = (Real.sqrt (Real.pi / (4 * t)) : ℂ) *
          Complex.exp (((1 - Complex.I * x) / (2 * (Real.sqrt t : ℂ))) ^ 2) *
          cerfc ((1 - Complex.I * x) / (2 * (Real.sqrt t : ℂ))) := by
  have hst : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst0 : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hst.ne'
  have ht0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  -- integrabilities of the two Laplace integrands
  have hIcos : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
      (Set.Ioi 0) :=
    integrableOn_exp_quad_trig ht (fun s => Real.abs_cos_le_one _) (by fun_prop)
  have hIsin : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
      (Set.Ioi 0) :=
    integrableOn_exp_quad_trig ht (fun s => Real.abs_sin_le_one _) (by fun_prop)
  -- combine the two Laplace representations (7.19.10/11 kit) into one complex integral
  have hcomb : (FLMF.Voigt.voigtU x t : ℂ) + Complex.I * (FLMF.Voigt.voigtV x t : ℂ)
      = ∫ s in Set.Ioi (0:ℝ),
          Complex.exp (-(t:ℂ)*(s:ℂ)^2 + 2*Complex.I*(((x:ℂ) + Complex.I)/2)*(s:ℂ)) := by
    have hIcosC : IntegrableOn
        (fun s : ℝ => ((Real.exp (-s - t * s ^ 2) * Real.cos (x * s) : ℝ) : ℂ)) (Set.Ioi 0) :=
      hIcos.ofReal
    have hIsinC : IntegrableOn
        (fun s : ℝ => ((Real.exp (-s - t * s ^ 2) * Real.sin (x * s) : ℝ) : ℂ)) (Set.Ioi 0) :=
      hIsin.ofReal
    rw [voigtU_eq_laplace ht x, voigtV_eq_laplace ht x]
    rw [← integral_complex_ofReal (f := fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.cos (x * s)),
        ← integral_complex_ofReal (f := fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.sin (x * s)),
        ← integral_const_mul, ← integral_add hIcosC (hIsinC.const_mul Complex.I)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    have hexp : (-(t:ℂ)*(s:ℂ)^2 + 2*Complex.I*(((x:ℂ) + Complex.I)/2)*(s:ℂ))
        = ((-s - t*s^2 : ℝ) : ℂ) + ((x*s : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination (s:ℂ) * Complex.I_sq
    rw [hexp, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_exp]
    push_cast
    ring
  -- the Gaussian-linear keystone (DLMF 7.7.3) at `a = t`, `z = (x+i)/2`
  have ha : 0 < ((t:ℂ)).re := by simpa using ht
  have hcore := gaussLin_integral_eq_cerfc (a := (t:ℂ)) (z := ((x:ℂ) + Complex.I)/2) ha
  -- the principal power `t^{-1/2}` of a positive real is `(√t)⁻¹`
  have hcpow : (t:ℂ) ^ (-(1:ℂ)/2) = ((Real.sqrt t : ℝ) : ℂ)⁻¹ := by
    have h1 : (-(1:ℂ)/2) = ((-(1/2 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [h1, ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_inv]
    congr 1
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  rw [hcpow] at hcore
  -- identify the erfc argument and the exponent with `z = (1-ix)/(2√t)`
  have hz : -Complex.I * (((x:ℂ) + Complex.I)/2) * ((Real.sqrt t : ℝ) : ℂ)⁻¹
      = (1 - Complex.I * (x:ℂ)) / (2 * ((Real.sqrt t : ℝ) : ℂ)) := by
    field_simp
    linear_combination -Complex.I_sq
  have hsq : ((Real.sqrt t : ℝ) : ℂ)^2 = (t:ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  have hkey : -(((x:ℂ) + Complex.I)^2) = (1 - Complex.I * (x:ℂ))^2 := by
    linear_combination (-(1:ℂ) - (x:ℂ)^2) * Complex.I_sq
  have hzsq : -((((x:ℂ) + Complex.I)/2)^2)/(t:ℂ)
      = ((1 - Complex.I * (x:ℂ)) / (2 * ((Real.sqrt t : ℝ) : ℂ)))^2 := by
    calc -((((x:ℂ) + Complex.I)/2)^2)/(t:ℂ)
        = -(((x:ℂ) + Complex.I)^2) / (4 * (t:ℂ)) := by ring
      _ = (1 - Complex.I * (x:ℂ))^2 / (4 * (t:ℂ)) := by rw [hkey]
      _ = ((1 - Complex.I * (x:ℂ)) / (2 * ((Real.sqrt t : ℝ) : ℂ)))^2 := by
          rw [div_pow, mul_pow, hsq]
          norm_num
  rw [hz, hzsq] at hcore
  -- the prefactor: `√(π/(4t)) = ½·√π·(√t)⁻¹`
  have hconst : ((Real.sqrt (Real.pi / (4 * t)) : ℝ) : ℂ)
      = 1/2 * ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ)⁻¹ := by
    have h4 : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
      rw [show (4:ℝ) * t = (2*Real.sqrt t)^2 by rw [mul_pow, Real.sq_sqrt ht.le]; norm_num]
      exact Real.sqrt_sq (by positivity)
    have hr : Real.sqrt (Real.pi / (4 * t)) = Real.sqrt Real.pi / (2 * Real.sqrt t) := by
      rw [Real.sqrt_div Real.pi_pos.le, h4]
    rw [hr]
    push_cast
    field_simp
  rw [hcomb, hcore, hconst]

end Erf773Support

/-! ## Remaining members of the DLMF 7.2.3 chain -/

-- no-dlmf: chain link 7.2.3 (assembled in `erf_7_2_3` below, alongside
-- `faddeeva_eq_cerfc_neg_I_mul`); this half is the integral-representation
-- member of the chain
/-- The Faddeeva function has the Dawson-type integral representation
`w(z) = e^{-z²}(1 + (2i/√π) ∫₀ᶻ e^{t²} dt)`, the contour integral being taken
along the straight segment `0 → z`, parametrised (as for `cerf`) via
`∫₀ᶻ e^{t²} dt = z ∫₀¹ e^{(t z)²} dt`. -/
theorem erf_7_2_3_integral (z : ℂ) :
    faddeeva z =
      Complex.exp (-z ^ 2) *
        (1 + (2 * Complex.I / (Real.sqrt Real.pi : ℂ)) *
          (z * ∫ t in (0 : ℝ)..1, Complex.exp (((t : ℂ) * z) ^ 2))) := by
  unfold faddeeva cerfc cerf
  have hcongr : (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * (-(Complex.I * z))) ^ 2))
      = ∫ t in (0:ℝ)..1, Complex.exp (((t : ℂ) * z) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    show Complex.exp (-((t:ℂ) * (-(Complex.I * z))) ^ 2) = Complex.exp (((t:ℂ) * z) ^ 2)
    congr 1
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    ring_nf
    ring_nf at hI
    linear_combination (-(t:ℂ)^2*z^2) * hI
  rw [hcongr]
  ring

/-- **DLMF 7.2.3**: the Faddeeva function's Dawson-type integral representation
and its definitional relation to `erfc`,
`w(z) = e^{-z²}(1 + (2i/√π) ∫₀ᶻ e^{t²} dt) = e^{-z²} erfc(-iz)`.

DLMF 7.2.3.
DAG: E-7.2.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_2_3 (z : ℂ) :
    faddeeva z =
      Complex.exp (-z ^ 2) *
        (1 + (2 * Complex.I / (Real.sqrt Real.pi : ℂ)) *
          (z * ∫ t in (0 : ℝ)..1, Complex.exp (((t : ℂ) * z) ^ 2))) ∧
    faddeeva z = Complex.exp (-z ^ 2) * cerfc (-(Complex.I * z)) :=
  ⟨erf_7_2_3_integral z, faddeeva_eq_cerfc_neg_I_mul z⟩

/-! ### Support lemmas for the Maclaurin series (DLMF 7.6.3)

`erf_7_6_3` is proven from the Dawson-type representation `erf_7_2_3_integral`:
the even-index half of the series sums to `e^{-z²}` (the exponential series),
and the odd-index half is the termwise integration of
`(2i/√π)·z·∫₀¹ e^{-(1-t²)z²} dt`, whose coefficients are the Wallis-type
moments `∫₀¹ (1-t²)^m dt = √π·m!/(2Γ(m+3/2))`. -/

section Erf763Support

open MeasureTheory Set

-- no-dlmf: support lemma for erf_7_6_3 (Wallis-moment recurrence, by parts)
private lemma erf763_wallis_rec (m : ℕ) :
    (2*(m:ℝ)+3) * ∫ t in (0:ℝ)..1, (1 - t^2)^(m+1)
      = (2*(m:ℝ)+2) * ∫ t in (0:ℝ)..1, (1 - t^2)^m := by
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * (1 - s^2)^(m+1))
      ((2*(m:ℝ)+3) * (1 - t^2)^(m+1) - (2*(m:ℝ)+2) * (1 - t^2)^m) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => 1 - s^2) (-(2*t)) t := by
      have h := ((hasDerivAt_id t).pow 2).const_sub 1
      convert h using 1
      simp only [id_eq]
      ring
    have h2 := h1.pow (m+1)
    have h3 := (hasDerivAt_id t).mul h2
    convert h3 using 1
    simp only [id_eq, Pi.pow_apply]
    push_cast
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => (2*(m:ℝ)+3) * (1 - t^2)^(m+1) - (2*(m:ℝ)+2) * (1 - t^2)^m)
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hint
  have h0 : (1:ℝ) * (1 - 1^2)^(m+1) - 0 * (1 - 0^2)^(m+1) = 0 := by
    simp
  rw [h0] at hftc
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  linarith [hftc]

-- no-dlmf: support lemma for erf_7_6_3 (Γ(3/2) = √π/2)
private lemma erf763_gamma_three_halves : Real.Gamma (3/2) = Real.sqrt Real.pi / 2 := by
  have h : (3/2 : ℝ) = 1/2 + 1 := by norm_num
  rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

-- no-dlmf: support lemma for erf_7_6_3 (the Wallis moments in closed Γ form)
private lemma erf763_wallis (m : ℕ) :
    Real.Gamma ((m:ℝ) + 3/2) * ∫ t in (0:ℝ)..1, (1 - t^2)^m
      = Real.sqrt Real.pi * m.factorial / 2 := by
  induction m with
  | zero =>
      simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
      rw [erf763_gamma_three_halves]
      norm_num
  | succ m ih =>
      have hrec := erf763_wallis_rec m
      have hgam : Real.Gamma ((m+1:ℕ) + 3/2) = ((m:ℝ) + 3/2) * Real.Gamma ((m:ℝ) + 3/2) := by
        have h : ((m+1:ℕ) : ℝ) + 3/2 = ((m:ℝ) + 3/2) + 1 := by push_cast; ring
        rw [h, Real.Gamma_add_one (by positivity)]
      have hfac : ((m+1:ℕ).factorial : ℝ) = ((m:ℝ)+1) * m.factorial := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hne : (2*(m:ℝ)+3) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [hgam, hfac]
      calc (2*(m:ℝ)+3) * (((m:ℝ) + 3/2) * Real.Gamma ((m:ℝ) + 3/2)
              * ∫ t in (0:ℝ)..1, (1 - t^2)^(m+1))
          = ((m:ℝ) + 3/2) * Real.Gamma ((m:ℝ) + 3/2)
              * ((2*(m:ℝ)+3) * ∫ t in (0:ℝ)..1, (1 - t^2)^(m+1)) := by ring
        _ = ((m:ℝ) + 3/2) * Real.Gamma ((m:ℝ) + 3/2)
              * ((2*(m:ℝ)+2) * ∫ t in (0:ℝ)..1, (1 - t^2)^m) := by rw [hrec]
        _ = (2*(m:ℝ)+2) * ((m:ℝ) + 3/2)
              * (Real.Gamma ((m:ℝ) + 3/2) * ∫ t in (0:ℝ)..1, (1 - t^2)^m) := by ring
        _ = (2*(m:ℝ)+2) * ((m:ℝ) + 3/2) * (Real.sqrt Real.pi * m.factorial / 2) := by rw [ih]
        _ = (2*(m:ℝ)+3) * (Real.sqrt Real.pi * (((m:ℝ)+1) * m.factorial) / 2) := by ring

-- no-dlmf: support lemma for erf_7_6_3 (the Wallis moments are at most 1)
private lemma erf763_wallis_le_one (m : ℕ) : (∫ t in (0:ℝ)..1, (1 - t^2)^m) ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun t : ℝ => (1 - t^2)^m)
    (g := fun _ : ℝ => (1:ℝ)) (by norm_num : (0:ℝ) ≤ 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable continuous_const 0 1)
    (fun u hu => by
      have h0 : 0 ≤ 1 - u^2 := by nlinarith [hu.1, hu.2]
      have h1 : 1 - u^2 ≤ 1 := by nlinarith [hu.1]
      exact pow_le_one₀ h0 h1)
  simpa using h

-- no-dlmf: support lemma for erf_7_6_3 (lower bound Γ(m+3/2) ≥ √π·m!/2)
private lemma erf763_gamma_ge (m : ℕ) :
    Real.sqrt Real.pi * m.factorial / 2 ≤ Real.Gamma ((m:ℝ) + 3/2) := by
  have hpos : 0 < Real.Gamma ((m:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
  calc Real.sqrt Real.pi * m.factorial / 2
      = Real.Gamma ((m:ℝ) + 3/2) * ∫ t in (0:ℝ)..1, (1 - t^2)^m := (erf763_wallis m).symm
    _ ≤ Real.Gamma ((m:ℝ) + 3/2) * 1 := by
        have := erf763_wallis_le_one m
        gcongr
    _ = Real.Gamma ((m:ℝ) + 3/2) := mul_one _

-- no-dlmf: support lemma for erf_7_6_3 (Γ(n/2+1) at even indices is a factorial)
private lemma erf763_gammaHalf_even (m : ℕ) :
    Complex.Gamma (((2*m : ℕ) : ℂ)/2 + 1) = ((m.factorial : ℕ) : ℂ) := by
  have h : ((2*m : ℕ) : ℂ)/2 + 1 = (m : ℂ) + 1 := by push_cast; ring
  rw [h, Complex.Gamma_nat_eq_factorial]

-- no-dlmf: support lemma for erf_7_6_3 (Γ(n/2+1) at odd indices is the real Γ(m+3/2))
private lemma erf763_gammaHalf_odd (m : ℕ) :
    Complex.Gamma (((2*m+1 : ℕ) : ℂ)/2 + 1) = ((Real.Gamma ((m:ℝ) + 3/2) : ℝ) : ℂ) := by
  have h : ((2*m+1 : ℕ) : ℂ)/2 + 1 = (((m:ℝ) + 3/2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.Gamma_ofReal]

-- no-dlmf: support lemma for erf_7_6_3 (the even-index half is the exponential series)
private lemma erf763_even_sum (z : ℂ) :
    ∑' m : ℕ, (Complex.I*z)^(2*m) / Complex.Gamma (((2*m : ℕ) : ℂ)/2 + 1)
      = Complex.exp (-z^2) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  refine tsum_congr fun m => ?_
  rw [erf763_gammaHalf_even m]
  have hIz : (Complex.I*z)^2 = -z^2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [pow_mul, hIz]

-- no-dlmf: support lemma for erf_7_6_3 (summability of the even-index half)
private lemma erf763_summable_even (z : ℂ) :
    Summable (fun m : ℕ => (Complex.I*z)^(2*m) / Complex.Gamma (((2*m:ℕ):ℂ)/2 + 1)) := by
  refine Summable.of_norm ?_
  have hnorm : ∀ m : ℕ, ‖(Complex.I*z)^(2*m) / Complex.Gamma (((2*m:ℕ):ℂ)/2 + 1)‖
      = (‖z‖^2)^m / m.factorial := by
    intro m
    rw [erf763_gammaHalf_even m, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_natCast, ← pow_mul, mul_comm 2 m, pow_mul]
  simp only [hnorm]
  exact Real.summable_pow_div_factorial (‖z‖^2)

-- no-dlmf: support lemma for erf_7_6_3 (summability of the odd-index half)
private lemma erf763_summable_odd (z : ℂ) :
    Summable (fun m : ℕ => (Complex.I*z)^(2*m+1) / Complex.Gamma (((2*m+1:ℕ):ℂ)/2 + 1)) := by
  refine Summable.of_norm ?_
  have hb : ∀ m : ℕ, ‖(Complex.I*z)^(2*m+1) / Complex.Gamma (((2*m+1:ℕ):ℂ)/2 + 1)‖
      ≤ (2 * ‖z‖ / Real.sqrt Real.pi) * ((‖z‖^2)^m / m.factorial) := by
    intro m
    have hpos : 0 < Real.Gamma ((m:ℝ) + 3/2) := Real.Gamma_pos_of_pos (by positivity)
    have hfac : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hsq : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    rw [erf763_gammaHalf_odd m, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hz1 : ‖z‖^(2*m+1) = ‖z‖ * (‖z‖^2)^m := by
      rw [← pow_mul]
      ring
    rw [hz1, div_le_iff₀ hpos]
    have h2 : (2 * ‖z‖ / Real.sqrt Real.pi) * ((‖z‖^2)^m / m.factorial)
        * Real.Gamma ((m:ℝ) + 3/2)
        = (‖z‖ * (‖z‖^2)^m)
            * (Real.Gamma ((m:ℝ) + 3/2) * 2 / (Real.sqrt Real.pi * m.factorial)) := by
      field_simp
    rw [h2]
    have h3 : (1:ℝ) ≤ Real.Gamma ((m:ℝ) + 3/2) * 2 / (Real.sqrt Real.pi * m.factorial) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [erf763_gamma_ge m]
    nlinarith [h3, norm_nonneg z, pow_nonneg (sq_nonneg (‖z‖ : ℝ)) m,
      mul_nonneg (norm_nonneg z) (pow_nonneg (sq_nonneg (‖z‖:ℝ)) m)]
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) hb ?_
  exact (Real.summable_pow_div_factorial (‖z‖^2)).mul_left _

-- no-dlmf: support lemma for erf_7_6_3 (the integrand as its exponential series)
private lemma erf763_pt (z : ℂ) (t : ℝ) :
    Complex.exp (((t:ℂ)^2 - 1) * z^2)
      = ∑' m : ℕ, (((t:ℂ)^2 - 1) * z^2)^m / m.factorial := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

-- no-dlmf: support lemma for erf_7_6_3 (integrability of each series term)
private lemma erf763_term_integrable (z : ℂ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => (((t:ℂ)^2 - 1) * z^2)^m / m.factorial) (Ioc (0:ℝ) 1) :=
  Continuous.integrableOn_Ioc (by fun_prop)

-- no-dlmf: support lemma for erf_7_6_3 (summability of the termwise integral norms)
private lemma erf763_summable_integral (z : ℂ) :
    Summable fun m : ℕ => ∫ t in Ioc (0:ℝ) 1, ‖(((t:ℂ)^2 - 1) * z^2)^m / m.factorial‖ := by
  have hbound : ∀ m : ℕ, (∫ t in Ioc (0:ℝ) 1, ‖(((t:ℂ)^2 - 1) * z^2)^m / m.factorial‖)
      ≤ (‖z‖^2)^m / m.factorial := by
    intro m
    have hle : ∀ t ∈ Ioc (0:ℝ) 1, ‖(((t:ℂ)^2 - 1) * z^2)^m / m.factorial‖
        ≤ (‖z‖^2)^m / m.factorial := by
      intro t ht
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast]
      gcongr
      have h1 : ‖(t:ℂ)^2 - 1‖ ≤ 1 := by
        have h : (t:ℂ)^2 - 1 = ((t^2 - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [ht.1, ht.2]
      have h2 : ‖z^2‖ = ‖z‖^2 := norm_pow z 2
      calc ‖(t:ℂ)^2 - 1‖ * ‖z^2‖ ≤ 1 * ‖z^2‖ := by gcongr
        _ = ‖z‖^2 := by rw [one_mul, h2]
    calc (∫ t in Ioc (0:ℝ) 1, ‖(((t:ℂ)^2 - 1) * z^2)^m / m.factorial‖)
        ≤ ∫ _ in Ioc (0:ℝ) 1, (‖z‖^2)^m / m.factorial := by
          refine setIntegral_mono_on ?_ (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc hle
          exact (erf763_term_integrable z m).norm
      _ = (‖z‖^2)^m / m.factorial := by
          rw [setIntegral_const, smul_eq_mul,
            Real.volume_real_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
          norm_num
  refine Summable.of_nonneg_of_le
    (fun m => integral_nonneg fun t => norm_nonneg _) hbound
    (Real.summable_pow_div_factorial (‖z‖^2))

-- no-dlmf: support lemma for erf_7_6_3 (sum–integral interchange)
private lemma erf763_swap (z : ℂ) :
    ∫ t in Ioc (0:ℝ) 1, Complex.exp (((t:ℂ)^2 - 1) * z^2)
      = ∑' m : ℕ, ∫ t in Ioc (0:ℝ) 1, (((t:ℂ)^2 - 1) * z^2)^m / m.factorial := by
  rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => erf763_pt z t]
  exact (integral_tsum_of_summable_integral_norm (erf763_term_integrable z)
    (erf763_summable_integral z)).symm

-- no-dlmf: support lemma for erf_7_6_3 (evaluation of the termwise integral)
private lemma erf763_term_eval (z : ℂ) (m : ℕ) :
    ∫ t in Ioc (0:ℝ) 1, (((t:ℂ)^2 - 1) * z^2)^m / m.factorial
      = z^(2*m) / m.factorial * (((-1:ℝ)^m * ∫ t in (0:ℝ)..1, (1 - t^2)^m : ℝ) : ℂ) := by
  have hsplit : ∀ t : ℝ, (((t:ℂ)^2 - 1) * z^2)^m / m.factorial
      = z^(2*m) / m.factorial * (((t^2 - 1)^m : ℝ) : ℂ) := by
    intro t
    rw [mul_pow, ← pow_mul]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => hsplit t]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_ofReal]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  show (t^2 - 1)^m = (-1:ℝ)^m * (1 - t^2)^m
  rw [← mul_pow]
  congr 1
  ring

-- no-dlmf: support lemma for erf_7_6_3 (the odd-index half as the Dawson-type integral)
private lemma erf763_odd_sum (z : ℂ) :
    ∑' m : ℕ, (Complex.I*z)^(2*m+1) / Complex.Gamma (((2*m+1:ℕ):ℂ)/2 + 1)
      = 2 * Complex.I / (Real.sqrt Real.pi : ℂ) * z
          * ∫ t in Ioc (0:ℝ) 1, Complex.exp (((t:ℂ)^2 - 1) * z^2) := by
  rw [erf763_swap z, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hI : (Complex.I*z)^(2*m+1) = Complex.I * (-1:ℂ)^m * z^(2*m+1) := by
    rw [mul_pow, pow_succ, pow_mul, Complex.I_sq]
    ring
  rw [erf763_term_eval z m, erf763_gammaHalf_odd m, hI]
  push_cast
  set G : ℂ := ((Real.Gamma ((m:ℝ)+3/2) : ℝ) : ℂ) with hG
  set J : ℂ := ((∫ t in (0:ℝ)..1, (1 - t^2)^m : ℝ) : ℂ) with hJ
  have hΓpos : 0 < Real.Gamma ((m:ℝ)+3/2) := Real.Gamma_pos_of_pos (by positivity)
  have hG0 : G ≠ 0 := by
    rw [hG]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hΓpos)
  have hs0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  have hm0 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hwC : G * J = ((Real.sqrt Real.pi : ℝ):ℂ) * ((m.factorial : ℕ) : ℂ) / 2 := by
    rw [hG, hJ, ← Complex.ofReal_mul, erf763_wallis m]
    push_cast
    ring
  field_simp
  linear_combination (-2 * z^(2*m+1)) * hwC

/-- Maclaurin series `w(z) = ∑ₙ (iz)ⁿ / Γ(½n+1)`, convergent for all `z`
(DLMF 7.6.3).

DLMF 7.6.3.
DAG: E-7.6.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_6_3 (z : ℂ) :
    faddeeva z = ∑' n : ℕ, (Complex.I * z) ^ n / Complex.Gamma ((n : ℂ) / 2 + 1) := by
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ => (Complex.I * z) ^ n / Complex.Gamma ((n : ℂ) / 2 + 1))
    (erf763_summable_even z) (erf763_summable_odd z)
  rw [← hsplit]
  simp only []
  rw [erf763_even_sum z, erf763_odd_sum z, erf_7_2_3_integral z]
  have hpull : Complex.exp (-z^2) * ∫ t in (0:ℝ)..1, Complex.exp (((t:ℂ)*z)^2)
      = ∫ t in Ioc (0:ℝ) 1, Complex.exp (((t:ℂ)^2 - 1) * z^2) := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← hpull]
  ring

end Erf763Support

end FLMF.Error
