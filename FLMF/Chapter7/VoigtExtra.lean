import FLMF.Chapter7.Voigt
import FLMF.Chapter7.Erf
import FLMF.Support.LaplaceTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Voigt functions: §7.19 statement surfaces (DLMF 7.19.2–7.19.11)

Statement surfaces for the DLMF §7.19 Voigt-function identities, stated against
the committed `FLMF.Voigt.voigtU` and `FLMF.Voigt.voigtV` (real-valued, with the
DLMF 7.19.1 normalization `1/√(4πt)`; see `FLMF/Chapter7/Voigt.lean`).

Faithful, TRUE statements with `sorry` bodies (Phase-5 surfaces), except where a
DLMF equation is inherently complex (`U + iV = √(π/4t) e^{z²} erfc z` with the
complex argument `z`, DLMF 7.19.3) and is recorded as a documented deferral
comment instead of a fake theorem.

* 7.19.2 — defining integral of `V`.
* 7.19.3 — DEFERRED (complex erfc / Faddeeva `w(z)`).
* 7.19.4 — line-broadening integral `= (1/(aπ)) U(u/a, 1/(4a²))`.
* 7.19.5 — limits as `t → 0⁺`.
* 7.19.6 — parity symmetries of `U` and `V`.
* 7.19.7 — bounds `0 < U ≤ 1`, `-1 ≤ V ≤ 1`.
* 7.19.8, 7.19.9 — first-order differential relations between `U` and `V`.
* 7.19.10, 7.19.11 — cosine / sine Laplace-type integral representations.
-/

namespace FLMF.Error

open Real MeasureTheory Filter Topology

-- no-dlmf: definitional unfolding of `voigtV` (the identity is `rfl`); the DLMF
-- 7.19.2 tag now lives on `voigtV`'s own def (`FLMF.Voigt.voigtV`, Voigt.lean)
/-- Defining integral of the Voigt function `V` (DLMF 7.19.2).

DLMF 7.19.2.
-/
theorem erf_7_19_2 (x t : ℝ) :
    FLMF.Voigt.voigtV x t
      = (1 / Real.sqrt (4 * Real.pi * t))
          * ∫ y : ℝ, y * Real.exp (-(x - y) ^ 2 / (4 * t)) / (1 + y ^ 2) := by
  rfl

-- DLMF 7.19.3:  U(x,t) + i V(x,t) = √(π/(4t)) · e^{z²} · erfc(z),  z = (1 - i x)/(2√t).
-- RESOLVED in Error/Faddeeva.lean as `erf_7_19_3`, via the complex Faddeeva/cerfc keystone.
-- Original deferral kept for context: this identity is inherently complex — it combines the two real Voigt
-- functions into U + i·V and equates them to e^{z²} erfc(z) evaluated at the
-- complex argument z = (1 - i x)/(2√t) (equivalently the Faddeeva function w).
-- FLMF's `erfc` is REAL-valued and there is no complex erfc / Faddeeva `w(z)` in
-- FLMF, so no faithful real specialization exists. Stated as a documented
-- deferral rather than a vacuous theorem.

-- no-dlmf: support lemma (Gaussian×cosine closed form); no DLMF equation surface
/-- Gaussian–cosine integral: `∫_ℝ e^{-b(y-x₀)²} cos(sy) dy = √(π/b) e^{-s²/(4b)} cos(sx₀)`
(`b > 0`), obtained as the real part of Mathlib's `integral_cexp_quadratic`. -/
lemma gaussian_cos_integral {b : ℝ} (hb : 0 < b) (s x₀ : ℝ) :
    ∫ y : ℝ, Real.exp (-b * (y - x₀) ^ 2) * Real.cos (s * y)
      = Real.sqrt (Real.pi / b) * (Real.exp (-s ^ 2 / (4 * b)) * Real.cos (s * x₀)) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hB : (-(b : ℂ)).re < 0 := by simpa using hb
  set c : ℂ := 2 * b * x₀ + s * Complex.I with hc
  set d : ℂ := -(b * x₀ ^ 2 : ℂ) with hd
  have hint : Integrable fun y : ℝ => Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d) :=
    integrable_cexp_quadratic' hB c d
  have hval := integral_cexp_quadratic hB c d
  have hre : ∀ y : ℝ, (Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d)).re
      = Real.exp (-b * (y - x₀) ^ 2) * Real.cos (s * y) := by
    intro y
    have hz : -(b:ℂ) * y ^ 2 + c * y + d
        = ((-b * (y - x₀) ^ 2 : ℝ) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I := by
      rw [hc, hd]; push_cast; ring
    rw [hz, Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
  have hLHS : ∫ y : ℝ, Real.exp (-b * (y - x₀) ^ 2) * Real.cos (s * y)
      = (∫ y : ℝ, Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d)).re := by
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hre y).symm)
  have hkey : c ^ 2 = ((4*b^2*x₀^2 - s^2 : ℝ) : ℂ) + ((4*b*x₀*s : ℝ) : ℂ) * Complex.I := by
    rw [hc]
    linear_combination (norm := (push_cast; ring_nf)) ((s:ℂ)^2) * Complex.I_sq
  have hexp : d - c ^ 2 / (4 * -(b:ℂ))
      = ((-s ^ 2 / (4 * b) : ℝ) : ℂ) + ((s * x₀ : ℝ) : ℂ) * Complex.I := by
    rw [hd, hkey]
    push_cast
    field_simp
    ring
  have hcoef : ((Real.pi : ℂ)) / -(-(b:ℂ)) = ((Real.pi / b : ℝ) : ℂ) := by
    push_cast; ring
  have hcpow : ((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [hLHS, hval, hcoef, hexp, hcpow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_im, mul_zero, mul_one, add_zero, zero_add]

-- no-dlmf: support lemma (Gaussian×sine closed form); no DLMF equation surface
/-- Gaussian–sine integral: `∫_ℝ e^{-b(y-x₀)²} sin(sy) dy = √(π/b) e^{-s²/(4b)} sin(sx₀)`
(`b > 0`), obtained as the imaginary part of Mathlib's `integral_cexp_quadratic`. -/
lemma gaussian_sin_integral {b : ℝ} (hb : 0 < b) (s x₀ : ℝ) :
    ∫ y : ℝ, Real.exp (-b * (y - x₀) ^ 2) * Real.sin (s * y)
      = Real.sqrt (Real.pi / b) * (Real.exp (-s ^ 2 / (4 * b)) * Real.sin (s * x₀)) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hB : (-(b : ℂ)).re < 0 := by simpa using hb
  set c : ℂ := 2 * b * x₀ + s * Complex.I with hc
  set d : ℂ := -(b * x₀ ^ 2 : ℂ) with hd
  have hint : Integrable fun y : ℝ => Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d) :=
    integrable_cexp_quadratic' hB c d
  have hval := integral_cexp_quadratic hB c d
  have him : ∀ y : ℝ, (Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d)).im
      = Real.exp (-b * (y - x₀) ^ 2) * Real.sin (s * y) := by
    intro y
    have hz : -(b:ℂ) * y ^ 2 + c * y + d
        = ((-b * (y - x₀) ^ 2 : ℝ) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I := by
      rw [hc, hd]; push_cast; ring
    rw [hz, Complex.exp_im]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add]
  have hLHS : ∫ y : ℝ, Real.exp (-b * (y - x₀) ^ 2) * Real.sin (s * y)
      = (∫ y : ℝ, Complex.exp (-(b:ℂ) * y ^ 2 + c * y + d)).im := by
    have h := integral_im hint
    simp only [RCLike.im_to_complex] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (him y).symm)
  have hkey : c ^ 2 = ((4*b^2*x₀^2 - s^2 : ℝ) : ℂ) + ((4*b*x₀*s : ℝ) : ℂ) * Complex.I := by
    rw [hc]
    linear_combination (norm := (push_cast; ring_nf)) ((s:ℂ)^2) * Complex.I_sq
  have hexp : d - c ^ 2 / (4 * -(b:ℂ))
      = ((-s ^ 2 / (4 * b) : ℝ) : ℂ) + ((s * x₀ : ℝ) : ℂ) * Complex.I := by
    rw [hd, hkey]
    push_cast
    field_simp
    ring
  have hcoef : ((Real.pi : ℂ)) / -(-(b:ℂ)) = ((Real.pi / b : ℝ) : ℂ) := by
    push_cast; ring
  have hcpow : ((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / b) : ℝ) : ℂ) := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [hLHS, hval, hcoef, hexp, hcpow]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, mul_zero, mul_one, sub_zero, zero_add]

-- no-dlmf: support kit lemma; DLMF citation is context, not an equation surface
/-- Laplace-type representation of the Voigt function `U`:
`U(x,t) = ∫₀^∞ e^{-s-ts²} cos(xs) ds` for `t > 0` (DLMF 7.19.10 in unscaled form),
by expanding `1/(1+y²)` as a Laplace integral and applying Fubini. -/
lemma voigtU_eq_laplace {t : ℝ} (ht : 0 < t) (x : ℝ) :
    FLMF.Voigt.voigtU x t
      = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s - t * s ^ 2) * Real.cos (x * s) := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  set b : ℝ := 1 / (4 * t) with hbdef
  have hgauss : ∀ y : ℝ, FLMF.Voigt.gauss x t y = Real.exp (-b * (y - x) ^ 2) := by
    intro y
    unfold FLMF.Voigt.gauss
    congr 1
    rw [hbdef]
    field_simp
    ring
  have hexpInt : Integrable (fun s : ℝ => Real.exp (-s)) (volume.restrict (Set.Ioi 0)) := by
    have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
    simpa [neg_mul, one_mul] using this
  have hgaussInt : Integrable (fun y : ℝ => Real.exp (-b * (y - x) ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right x
  have hprod : Integrable (fun p : ℝ × ℝ => Real.exp (-b * (p.1 - x) ^ 2) * Real.exp (-p.2))
      (volume.prod (volume.restrict (Set.Ioi 0))) := hgaussInt.mul_prod hexpInt
  have hF : Integrable
      (Function.uncurry fun y s : ℝ =>
        Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.cos (y * s)))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    refine hprod.mono' ?_ ?_
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · filter_upwards with p
      simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
        (Real.exp_pos _).le
  have hswap := MeasureTheory.integral_integral_swap hF
  have hker : ∀ y : ℝ, FLMF.Voigt.kernelU x t y
      = ∫ s in Set.Ioi (0:ℝ),
          Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.cos (y * s)) := by
    intro y
    rw [MeasureTheory.integral_const_mul]
    have hl : ∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * Real.cos (y * s) = 1 / (1 + y ^ 2) := by
      simpa [neg_mul, one_mul, one_pow] using
        FLMF.Methods.LaplaceTransform.laplace_cos 1 y one_pos
    rw [hl]
    unfold FLMF.Voigt.kernelU
    rw [hgauss y, mul_one_div]
  have hinner : ∀ s : ℝ,
      (∫ y : ℝ, Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.cos (y * s)))
        = Real.sqrt (Real.pi / b)
            * (Real.exp (-s) * (Real.exp (-s ^ 2 / (4 * b)) * Real.cos (s * x))) := by
    intro s
    have hcomm : (fun y : ℝ => Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.cos (y * s)))
        = fun y : ℝ => Real.exp (-s) * (Real.exp (-b * (y - x) ^ 2) * Real.cos (s * y)) := by
      funext y; rw [mul_comm y s]; ring
    rw [hcomm, MeasureTheory.integral_const_mul, gaussian_cos_integral hb s x]
    ring
  have hsqrt : Real.sqrt (Real.pi / b) = Real.sqrt (4 * Real.pi * t) := by
    rw [hbdef]; congr 1; field_simp
  unfold FLMF.Voigt.voigtU
  rw [integral_congr_ae (Filter.Eventually.of_forall hker), hswap,
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => hinner s),
    MeasureTheory.integral_const_mul, hsqrt, ← mul_assoc]
  have hone : 1 / Real.sqrt (4 * Real.pi * t) * Real.sqrt (4 * Real.pi * t) = 1 := by
    rw [one_div, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity))]
  rw [hone, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have hexp : -s + -s ^ 2 / (4 * b) = -s - t * s ^ 2 := by
    rw [hbdef]; field_simp; ring
  rw [← mul_assoc, ← Real.exp_add, hexp, mul_comm s x]

-- no-dlmf: support kit lemma; DLMF citation is context, not an equation surface
/-- Laplace-type representation of the Voigt function `V`:
`V(x,t) = ∫₀^∞ e^{-s-ts²} sin(xs) ds` for `t > 0` (DLMF 7.19.11 in unscaled form),
by expanding `y/(1+y²)` as a Laplace integral and applying Fubini. -/
lemma voigtV_eq_laplace {t : ℝ} (ht : 0 < t) (x : ℝ) :
    FLMF.Voigt.voigtV x t
      = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s - t * s ^ 2) * Real.sin (x * s) := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  set b : ℝ := 1 / (4 * t) with hbdef
  have hgauss : ∀ y : ℝ, FLMF.Voigt.gauss x t y = Real.exp (-b * (y - x) ^ 2) := by
    intro y
    unfold FLMF.Voigt.gauss
    congr 1
    rw [hbdef]
    field_simp
    ring
  have hexpInt : Integrable (fun s : ℝ => Real.exp (-s)) (volume.restrict (Set.Ioi 0)) := by
    have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
    simpa [neg_mul, one_mul] using this
  have hgaussInt : Integrable (fun y : ℝ => Real.exp (-b * (y - x) ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right x
  have hprod : Integrable (fun p : ℝ × ℝ => Real.exp (-b * (p.1 - x) ^ 2) * Real.exp (-p.2))
      (volume.prod (volume.restrict (Set.Ioi 0))) := hgaussInt.mul_prod hexpInt
  have hF : Integrable
      (Function.uncurry fun y s : ℝ =>
        Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.sin (y * s)))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    refine hprod.mono' ?_ ?_
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · filter_upwards with p
      simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _))
        (Real.exp_pos _).le
  have hswap := MeasureTheory.integral_integral_swap hF
  have hker : ∀ y : ℝ, FLMF.Voigt.kernelV x t y
      = ∫ s in Set.Ioi (0:ℝ),
          Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.sin (y * s)) := by
    intro y
    rw [MeasureTheory.integral_const_mul]
    have hl : ∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * Real.sin (y * s) = y / (1 + y ^ 2) := by
      simpa [neg_mul, one_mul, one_pow] using
        FLMF.Methods.LaplaceTransform.laplace_sin 1 y one_pos
    rw [hl]
    unfold FLMF.Voigt.kernelV
    rw [hgauss y]
    ring
  have hinner : ∀ s : ℝ,
      (∫ y : ℝ, Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.sin (y * s)))
        = Real.sqrt (Real.pi / b)
            * (Real.exp (-s) * (Real.exp (-s ^ 2 / (4 * b)) * Real.sin (s * x))) := by
    intro s
    have hcomm : (fun y : ℝ => Real.exp (-b * (y - x) ^ 2) * (Real.exp (-s) * Real.sin (y * s)))
        = fun y : ℝ => Real.exp (-s) * (Real.exp (-b * (y - x) ^ 2) * Real.sin (s * y)) := by
      funext y; rw [mul_comm y s]; ring
    rw [hcomm, MeasureTheory.integral_const_mul, gaussian_sin_integral hb s x]
    ring
  have hsqrt : Real.sqrt (Real.pi / b) = Real.sqrt (4 * Real.pi * t) := by
    rw [hbdef]; congr 1; field_simp
  unfold FLMF.Voigt.voigtV
  rw [integral_congr_ae (Filter.Eventually.of_forall hker), hswap,
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => hinner s),
    MeasureTheory.integral_const_mul, hsqrt, ← mul_assoc]
  have hone : 1 / Real.sqrt (4 * Real.pi * t) * Real.sqrt (4 * Real.pi * t) = 1 := by
    rw [one_div, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity))]
  rw [hone, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have hexp : -s + -s ^ 2 / (4 * b) = -s - t * s ^ 2 := by
    rw [hbdef]; field_simp; ring
  rw [← mul_assoc, ← Real.exp_add, hexp, mul_comm s x]

-- no-dlmf: encodes H(a,u) via the first limb of DLMF 7.19.4; the chain display is surfaced at `erf_7_19_4`
/-- The line-broadening function `H(a,u)` (DLMF 7.19.4), defined by its
integral representation `H(a,u) = (a/π) ∫_ℝ e^{-t²} dt/((u-t)²+a²)`.

-/
noncomputable def lineBroadeningH (a u : ℝ) : ℝ :=
  (a / Real.pi) * ∫ s : ℝ, Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2)

-- no-dlmf: chain link 7.19.4 (assembled in `erf_7_19_4` below, alongside
-- `lineBroadeningH_eq_voigtU`); the defining integral representation, `rfl`
-- from `lineBroadeningH`'s own definition
theorem lineBroadeningH_eq_integral (a u : ℝ) :
    lineBroadeningH a u = (a / Real.pi) * ∫ s : ℝ, Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2) :=
  rfl

-- no-dlmf: chain link 7.19.4 (assembled in `erf_7_19_4` below, alongside
-- `lineBroadeningH_eq_integral`); the Voigt-`U` representation
theorem lineBroadeningH_eq_voigtU {a : ℝ} (ha : a ≠ 0) (u : ℝ) :
    lineBroadeningH a u
      = (1 / (a * Real.sqrt Real.pi)) * FLMF.Voigt.voigtU (u / a) (1 / (4 * a ^ 2)) := by
  unfold lineBroadeningH
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (4 * Real.pi * (1 / (4 * a ^ 2))) = Real.sqrt Real.pi / |a| := by
    rw [show 4 * Real.pi * (1 / (4 * a ^ 2)) = Real.pi / a ^ 2 by field_simp,
      Real.sqrt_div hπ.le, Real.sqrt_sq_eq_abs]
  have hker : ∀ y : ℝ, FLMF.Voigt.kernelU (u / a) (1 / (4 * a ^ 2)) y
      = a ^ 2 * (Real.exp (-(u - a * y) ^ 2) / ((a * y) ^ 2 + a ^ 2)) := by
    intro y
    unfold FLMF.Voigt.kernelU FLMF.Voigt.gauss
    have h1 : -(u / a - y) ^ 2 / (4 * (1 / (4 * a ^ 2))) = -(u - a * y) ^ 2 := by
      field_simp
    rw [h1]
    have h2 : (0:ℝ) < 1 + y ^ 2 := by positivity
    have h3 : (0:ℝ) < (a * y) ^ 2 + a ^ 2 := by positivity
    field_simp
    ring
  have hA : (∫ y : ℝ, Real.exp (-(u - a * y) ^ 2) / ((a * y) ^ 2 + a ^ 2))
      = |a⁻¹| • ∫ z : ℝ, Real.exp (-(u - z) ^ 2) / (z ^ 2 + a ^ 2) :=
    Measure.integral_comp_mul_left
      (fun z : ℝ => Real.exp (-(u - z) ^ 2) / (z ^ 2 + a ^ 2)) a
  have hB : (∫ z : ℝ, Real.exp (-(u - z) ^ 2) / (z ^ 2 + a ^ 2))
      = ∫ s : ℝ, Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2) := by
    have hC : (∫ z : ℝ, Real.exp (-(u - z) ^ 2) / ((u - (u - z)) ^ 2 + a ^ 2))
        = ∫ s : ℝ, Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2) :=
      integral_sub_left_eq_self
        (fun s : ℝ => Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2)) volume u
    rw [← hC]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  unfold FLMF.Voigt.voigtU
  rw [hsqrt, integral_congr_ae (Filter.Eventually.of_forall hker),
    MeasureTheory.integral_const_mul, hA, hB, smul_eq_mul,
    abs_inv]
  set S := Real.sqrt Real.pi with hS
  have hSpos : (0:ℝ) < S := Real.sqrt_pos.mpr hπ
  have hSS : S * S = Real.pi := Real.mul_self_sqrt hπ.le
  rw [← hSS]
  field_simp

/-- **DLMF 7.19.4.** The line-broadening function `H(a,u)`, both as its
defining integral `(a/π) ∫_ℝ e^{-t²} dt/((u-t)²+a²)` and as the Voigt-`U`
value `(1/(a√π))·U(u/a, 1/(4a²))`, for every nonzero real `a`.

DLMF 7.19.4.
DAG: E-7.19.4.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_4 {a : ℝ} (ha : a ≠ 0) (u : ℝ) :
    lineBroadeningH a u = (a / Real.pi) * ∫ s : ℝ, Real.exp (-s ^ 2) / ((u - s) ^ 2 + a ^ 2) ∧
    lineBroadeningH a u
      = (1 / (a * Real.sqrt Real.pi)) * FLMF.Voigt.voigtU (u / a) (1 / (4 * a ^ 2)) :=
  ⟨lineBroadeningH_eq_integral a u, lineBroadeningH_eq_voigtU ha u⟩

-- no-dlmf: dominated-convergence support for the `t → 0⁺` limits (DLMF 7.19.5 context)
/-- As `t → 0⁺`, `∫₀^∞ e^{-s-ts²} g(s) ds → ∫₀^∞ e^{-s} g(s) ds` for bounded
continuous `g`, by dominated convergence with dominating function `e^{-s}`. -/
private lemma _tendsto_laplace_aux {g : ℝ → ℝ} (hg : ∀ s, |g s| ≤ 1)
    (hcont : Continuous g) :
    Tendsto (fun t : ℝ => ∫ s in Set.Ioi (0:ℝ), Real.exp (-s - t * s ^ 2) * g s)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * g s)) := by
  have hexpInt : Integrable (fun s : ℝ => Real.exp (-s)) (volume.restrict (Set.Ioi 0)) := by
    have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
    simpa [neg_mul, one_mul] using this
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => Real.exp (-s)) ?_ ?_ hexpInt ?_
  · filter_upwards with t
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc Real.exp (-s - t * s ^ 2) * |g s|
        ≤ Real.exp (-s - t * s ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (hg s) (Real.exp_pos _).le
      _ ≤ Real.exp (-s) := by
          rw [mul_one]
          apply Real.exp_le_exp.mpr
          nlinarith [le_of_lt (Set.mem_Ioi.mp ht), sq_nonneg s]
  · filter_upwards with s
    have hc : Continuous (fun t : ℝ => Real.exp (-s - t * s ^ 2) * g s) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_mul, sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds

/-- Limits of `U` and `V` as `t → 0⁺` (DLMF 7.19.5).

DLMF 7.19.5.
DAG: E-7.19.5.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_5 (x : ℝ) :
    Tendsto (fun t : ℝ => FLMF.Voigt.voigtU x t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (1 / (1 + x ^ 2)))
      ∧ Tendsto (fun t : ℝ => FLMF.Voigt.voigtV x t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (x / (1 + x ^ 2))) := by
  constructor
  · have hlim := _tendsto_laplace_aux (g := fun s => Real.cos (x * s))
      (fun s => Real.abs_cos_le_one _) (by fun_prop)
    have hval : ∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * Real.cos (x * s) = 1 / (1 + x ^ 2) := by
      simpa [neg_mul, one_mul, one_pow] using
        FLMF.Methods.LaplaceTransform.laplace_cos 1 x one_pos
    rw [hval] at hlim
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (voigtU_eq_laplace ht x).symm
  · have hlim := _tendsto_laplace_aux (g := fun s => Real.sin (x * s))
      (fun s => Real.abs_sin_le_one _) (by fun_prop)
    have hval : ∫ s in Set.Ioi (0:ℝ), Real.exp (-s) * Real.sin (x * s) = x / (1 + x ^ 2) := by
      simpa [neg_mul, one_mul, one_pow] using
        FLMF.Methods.LaplaceTransform.laplace_sin 1 x one_pos
    rw [hval] at hlim
    refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (voigtV_eq_laplace ht x).symm

-- no-dlmf: packaging of `voigtU_neg`/`voigtV_neg` (Voigt.lean), each already
-- marked "elementary parity, no specific DLMF identity number"; over-strong
-- vs. DLMF 7.19.6 in quantifying over all real t rather than t > 0 — the
-- faithful surface is `erf_7_19_6_dlmf` below
theorem erf_7_19_6 (x t : ℝ) :
    FLMF.Voigt.voigtU (-x) t = FLMF.Voigt.voigtU x t
      ∧ FLMF.Voigt.voigtV (-x) t = -FLMF.Voigt.voigtV x t :=
  ⟨FLMF.Voigt.voigtU_neg x t, FLMF.Voigt.voigtV_neg x t⟩

/-- Parity symmetries of the Voigt functions on their DLMF domain `t > 0`:
`U(-x,t) = U(x,t)` and `V(-x,t) = -V(x,t)` (DLMF 7.19.6; `x` real, and `t > 0`
per the §7.19 definitions of `U`, `V` — the parity also holds junk-vacuously for
`t ≤ 0` in FLMF's encoding, see `erf_7_19_6` above, but that is not DLMF's scope).

DLMF 7.19.6.
DAG: E-7.19.6.
Numerical: N/A
Verified: verified
-/
theorem erf_7_19_6_dlmf {t : ℝ} (_ht : 0 < t) (x : ℝ) :
    FLMF.Voigt.voigtU (-x) t = FLMF.Voigt.voigtU x t
      ∧ FLMF.Voigt.voigtV (-x) t = -FLMF.Voigt.voigtV x t :=
  erf_7_19_6 x t

/-- Bounds `0 < U(x,t) ≤ 1` and `-1 ≤ V(x,t) ≤ 1` for `t > 0` (DLMF 7.19.7).

DLMF 7.19.7.
DAG: E-7.19.7.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_7 {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < FLMF.Voigt.voigtU x t ∧ FLMF.Voigt.voigtU x t ≤ 1
      ∧ -1 ≤ FLMF.Voigt.voigtV x t ∧ FLMF.Voigt.voigtV x t ≤ 1 := by
  have hgaussInt : (∫ y : ℝ, FLMF.Voigt.gauss x t y) = Real.sqrt (4 * Real.pi * t) := by
    have hfun : (fun y : ℝ => FLMF.Voigt.gauss x t y)
        = (fun y : ℝ => Real.exp (-(1 / (4 * t)) * (y - x) ^ 2)) := by
      funext y
      unfold FLMF.Voigt.gauss
      congr 1
      field_simp
      ring
    rw [hfun]
    have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun z : ℝ => Real.exp (-(1 / (4 * t)) * z ^ 2)) x
    rw [hshift, integral_gaussian]
    rw [show Real.pi / (1 / (4 * t)) = 4 * Real.pi * t by field_simp]
  have hsqrtpos : (0:ℝ) < Real.sqrt (4 * Real.pi * t) := by
    apply Real.sqrt_pos.mpr
    have := Real.pi_pos
    positivity
  have hUle_pt : (fun y : ℝ => FLMF.Voigt.kernelU x t y) ≤ fun y => FLMF.Voigt.gauss x t y := by
    intro y
    have hb := FLMF.Voigt.norm_kernelU_le x t y
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).2
  have hVle_pt : (fun y : ℝ => FLMF.Voigt.kernelV x t y) ≤ fun y => FLMF.Voigt.gauss x t y := by
    intro y
    have hb := FLMF.Voigt.norm_kernelV_le x t y
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).2
  have hVge_pt : (fun y : ℝ => -FLMF.Voigt.gauss x t y) ≤ fun y => FLMF.Voigt.kernelV x t y := by
    intro y
    have hb := FLMF.Voigt.norm_kernelV_le x t y
    rw [Real.norm_eq_abs] at hb
    exact (abs_le.mp hb).1
  have hUle : (∫ y : ℝ, FLMF.Voigt.kernelU x t y) ≤ ∫ y : ℝ, FLMF.Voigt.gauss x t y :=
    integral_mono (FLMF.Voigt.integrable_kernelU ht x) (FLMF.Voigt.integrable_gauss ht x) hUle_pt
  have hVle : (∫ y : ℝ, FLMF.Voigt.kernelV x t y) ≤ ∫ y : ℝ, FLMF.Voigt.gauss x t y :=
    integral_mono (FLMF.Voigt.integrable_kernelV ht x) (FLMF.Voigt.integrable_gauss ht x) hVle_pt
  have hVge : (-∫ y : ℝ, FLMF.Voigt.gauss x t y) ≤ ∫ y : ℝ, FLMF.Voigt.kernelV x t y := by
    have hmono := integral_mono (FLMF.Voigt.integrable_gauss ht x).neg
      (FLMF.Voigt.integrable_kernelV ht x) hVge_pt
    simpa [integral_neg] using hmono
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 0 < (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelU x t y
    apply mul_pos (by positivity)
    apply integral_pos_of_integrable_nonneg_nonzero (x := (0:ℝ))
      (FLMF.Voigt.continuous_kernelU x t) (FLMF.Voigt.integrable_kernelU ht x)
    · intro y
      unfold FLMF.Voigt.kernelU
      have h1 := FLMF.Voigt.gauss_nonneg x t y
      have h2 := FLMF.Voigt.one_add_sq_pos y
      positivity
    · unfold FLMF.Voigt.kernelU
      have h1 := FLMF.Voigt.gauss_pos x t 0
      have h2 := FLMF.Voigt.one_add_sq_pos (0:ℝ)
      positivity
  · show (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelU x t y ≤ 1
    rw [hgaussInt] at hUle
    calc (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelU x t y
        ≤ (1 / Real.sqrt (4 * Real.pi * t)) * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left hUle (by positivity)
      _ = 1 := by field_simp
  · show -1 ≤ (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelV x t y
    rw [hgaussInt] at hVge
    have heq : -(1:ℝ) = (1 / Real.sqrt (4 * Real.pi * t)) * (-(Real.sqrt (4 * Real.pi * t))) := by
      field_simp
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hVge]
  · show (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelV x t y ≤ 1
    rw [hgaussInt] at hVle
    calc (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, FLMF.Voigt.kernelV x t y
        ≤ (1 / Real.sqrt (4 * Real.pi * t)) * Real.sqrt (4 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left hVle (by positivity)
      _ = 1 := by field_simp

-- no-dlmf: integrability support for the differential relations (DLMF 7.19.8/9 context)
/-- `s ↦ e^{-s-ts²} g(s)` is integrable on `(0,∞)` for continuous `g` with `|g| ≤ 1`. -/
private lemma _integrableOn_exp_trig {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
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

-- no-dlmf: pointwise dominating bound for the differentiated integrands (7.19.8/9 context)
/-- Pointwise bound `|s e^{-s-ts²} v| ≤ s e^{-ts²}` for `s > 0`, `|v| ≤ 1`. -/
private lemma _abs_mul_exp_trig_le {t : ℝ} (_ht : 0 < t) {s : ℝ} (hs : 0 < s) {v : ℝ}
    (hv : |v| ≤ 1) :
    |s * (Real.exp (-s - t * s ^ 2) * v)| ≤ s * Real.exp (-t * s ^ 2) := by
  have h1 : Real.exp (-s - t * s ^ 2) * |v| ≤ Real.exp (-t * s ^ 2) := by
    calc Real.exp (-s - t * s ^ 2) * |v|
        ≤ Real.exp (-s - t * s ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
      _ ≤ Real.exp (-t * s ^ 2) := by
          rw [mul_one]
          exact Real.exp_le_exp.mpr (by linarith)
  calc |s * (Real.exp (-s - t * s ^ 2) * v)|
      = s * (Real.exp (-s - t * s ^ 2) * |v|) := by
        rw [abs_mul, abs_mul, Real.abs_exp, abs_of_pos hs]
    _ ≤ s * Real.exp (-t * s ^ 2) := mul_le_mul_of_nonneg_left h1 hs.le

-- no-dlmf: integrability support for the differential relations (DLMF 7.19.8/9 context)
/-- `s ↦ s e^{-s-ts²} g(s)` is integrable on `(0,∞)` for continuous `g` with `|g| ≤ 1`. -/
private lemma _integrableOn_mul_exp_trig {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : ∀ s, |g s| ≤ 1) (hcont : Continuous g) :
    IntegrableOn (fun s : ℝ => s * (Real.exp (-s - t * s ^ 2) * g s)) (Set.Ioi 0) := by
  have hbound : Integrable (fun s : ℝ => s * Real.exp (-t * s ^ 2))
      (volume.restrict (Set.Ioi 0)) := (integrable_mul_exp_neg_mul_sq ht).restrict
  refine hbound.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs]
  exact _abs_mul_exp_trig_le ht (Set.mem_Ioi.mp hs) (hg _)

-- no-dlmf: differentiation under the integral sign for the Laplace representation of U
/-- For `t > 0`, `∂U/∂x (x,t) = -∫₀^∞ s e^{-s-ts²} sin(xs) ds`, by differentiating
the Laplace representation under the integral sign. -/
private lemma _hasDerivAt_voigtU {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x' : ℝ => FLMF.Voigt.voigtU x' t)
      (-∫ s in Set.Ioi (0:ℝ), s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s))) x := by
  have hbound : Integrable (fun s : ℝ => s * Real.exp (-t * s ^ 2))
      (volume.restrict (Set.Ioi 0)) := (integrable_mul_exp_neg_mul_sq ht).restrict
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0:ℝ))) (𝕜 := ℝ)
    (F := fun x' : ℝ => fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.cos (x' * s))
    (F' := fun x' : ℝ => fun s : ℝ => -(s * (Real.exp (-s - t * s ^ 2) * Real.sin (x' * s))))
    (x₀ := x) (bound := fun s : ℝ => s * Real.exp (-t * s ^ 2))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x' =>
      Continuous.aestronglyMeasurable (by fun_prop))
    (_integrableOn_exp_trig ht (fun s => Real.abs_cos_le_one _) (by fun_prop))
    (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ hbound ?_
  · have hrepr : (fun x' : ℝ => FLMF.Voigt.voigtU x' t)
        = fun x' : ℝ => ∫ s in Set.Ioi (0:ℝ),
            Real.exp (-s - t * s ^ 2) * Real.cos (x' * s) := by
      funext x'
      exact voigtU_eq_laplace ht x'
    rw [hrepr]
    simpa [integral_neg] using key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x' _
    rw [norm_neg, Real.norm_eq_abs]
    exact _abs_mul_exp_trig_le ht (Set.mem_Ioi.mp hs) (Real.abs_sin_le_one _)
  · filter_upwards with s
    intro x' _
    have h1 := (Real.hasDerivAt_cos (x' * s)).comp x' (hasDerivAt_mul_const s)
    have h2 := h1.const_mul (Real.exp (-s - t * s ^ 2))
    convert h2 using 1
    ring

-- no-dlmf: differentiation under the integral sign for the Laplace representation of V
/-- For `t > 0`, `∂V/∂x (x,t) = ∫₀^∞ s e^{-s-ts²} cos(xs) ds`, by differentiating
the Laplace representation under the integral sign. -/
private lemma _hasDerivAt_voigtV {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x' : ℝ => FLMF.Voigt.voigtV x' t)
      (∫ s in Set.Ioi (0:ℝ), s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s))) x := by
  have hbound : Integrable (fun s : ℝ => s * Real.exp (-t * s ^ 2))
      (volume.restrict (Set.Ioi 0)) := (integrable_mul_exp_neg_mul_sq ht).restrict
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0:ℝ))) (𝕜 := ℝ)
    (F := fun x' : ℝ => fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.sin (x' * s))
    (F' := fun x' : ℝ => fun s : ℝ => s * (Real.exp (-s - t * s ^ 2) * Real.cos (x' * s)))
    (x₀ := x) (bound := fun s : ℝ => s * Real.exp (-t * s ^ 2))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x' =>
      Continuous.aestronglyMeasurable (by fun_prop))
    (_integrableOn_exp_trig ht (fun s => Real.abs_sin_le_one _) (by fun_prop))
    (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ hbound ?_
  · have hrepr : (fun x' : ℝ => FLMF.Voigt.voigtV x' t)
        = fun x' : ℝ => ∫ s in Set.Ioi (0:ℝ),
            Real.exp (-s - t * s ^ 2) * Real.sin (x' * s) := by
      funext x'
      exact voigtV_eq_laplace ht x'
    rw [hrepr]
    exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro x' _
    rw [Real.norm_eq_abs]
    exact _abs_mul_exp_trig_le ht (Set.mem_Ioi.mp hs) (Real.abs_cos_le_one _)
  · filter_upwards with s
    intro x' _
    have h1 := (Real.hasDerivAt_sin (x' * s)).comp x' (hasDerivAt_mul_const s)
    have h2 := h1.const_mul (Real.exp (-s - t * s ^ 2))
    convert h2 using 1
    ring

/-- Differential relation `V = x U + 2t ∂U/∂x` (DLMF 7.19.8), for `t > 0` (the
DLMF §7.19 domain).

DLMF 7.19.8.
DAG: E-7.19.8.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_8 (x : ℝ) {t : ℝ} (ht : 0 < t) :
    FLMF.Voigt.voigtV x t
      = x * FLMF.Voigt.voigtU x t
          + 2 * t * deriv (fun x' : ℝ => FLMF.Voigt.voigtU x' t) x := by
  have hEsin : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
      (Set.Ioi 0) := _integrableOn_exp_trig ht (fun s => Real.abs_sin_le_one _) (by fun_prop)
  have hEcos : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
      (Set.Ioi 0) := _integrableOn_exp_trig ht (fun s => Real.abs_cos_le_one _) (by fun_prop)
  have hSsin : IntegrableOn
      (fun s : ℝ => s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))
      (Set.Ioi 0) := _integrableOn_mul_exp_trig ht (fun s => Real.abs_sin_le_one _) (by fun_prop)
  -- FTC of the total s-derivative of `e^{-s-ts²} sin(xs)` over `(0,∞)`
  have hderiv : ∀ s ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.sin (x * σ))
        (-(Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
          - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))
          + x * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s))) s := by
    intro s _
    have h1 : HasDerivAt (fun σ : ℝ => -σ - t * σ ^ 2) (-1 - t * (2 * s)) s := by
      simpa using ((hasDerivAt_id s).neg.sub ((hasDerivAt_pow 2 s).const_mul t))
    have h3 : HasDerivAt (fun σ : ℝ => Real.sin (x * σ)) (Real.cos (x * s) * x) s := by
      simpa using (Real.hasDerivAt_sin (x * s)).comp s ((hasDerivAt_id s).const_mul x)
    have h4 := h1.exp.mul h3
    convert h4 using 1
    ring
  have hf'int : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))
        + x * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s))) (Set.Ioi 0) :=
    (hEsin.neg.sub (hSsin.const_mul (2 * t))).add (hEcos.const_mul x)
  have hcont : ContinuousWithinAt
      (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.sin (x * σ)) (Set.Ici 0) 0 :=
    Continuous.continuousWithinAt (by fun_prop)
  have htend : Tendsto (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.sin (x * σ))
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun σ : ℝ => Real.exp (-σ)) _ tendsto_exp_neg_atTop_nhds_zero
    intro σ
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc Real.exp (-σ - t * σ ^ 2) * |Real.sin (x * σ)|
        ≤ Real.exp (-σ - t * σ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le
      _ ≤ Real.exp (-σ) := by
          rw [mul_one]
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg σ, ht.le])
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int htend
  have hFTC0 : (∫ s in Set.Ioi (0:ℝ),
      (-(Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))
        + x * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))) = 0 := by
    rw [hFTC]
    simp
  have hI1 : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))) (Set.Ioi 0) :=
    hEsin.neg.sub (hSsin.const_mul (2 * t))
  have hI2 : IntegrableOn (fun s : ℝ =>
      x * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s))) (Set.Ioi 0) :=
    hEcos.const_mul x
  have hI3 : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.sin (x * s))) (Set.Ioi 0) := hEsin.neg
  have hI4 : IntegrableOn (fun s : ℝ =>
      2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))) (Set.Ioi 0) :=
    hSsin.const_mul (2 * t)
  rw [integral_add hI1 hI2, integral_sub hI3 hI4, integral_neg,
    integral_const_mul, integral_const_mul] at hFTC0
  have hV := voigtV_eq_laplace ht x
  have hU := voigtU_eq_laplace ht x
  have hD : deriv (fun x' : ℝ => FLMF.Voigt.voigtU x' t) x
      = -∫ s in Set.Ioi (0:ℝ), s * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)) :=
    (_hasDerivAt_voigtU ht x).deriv
  rw [hV, hU, hD]
  linarith [hFTC0]

/-- Differential relation `U = 1 - x V - 2t ∂V/∂x` (DLMF 7.19.9), for `t > 0`
(the DLMF §7.19 domain).

DLMF 7.19.9.
DAG: E-7.19.9.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_9 (x : ℝ) {t : ℝ} (ht : 0 < t) :
    FLMF.Voigt.voigtU x t
      = 1 - x * FLMF.Voigt.voigtV x t
          - 2 * t * deriv (fun x' : ℝ => FLMF.Voigt.voigtV x' t) x := by
  have hEsin : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.sin (x * s))
      (Set.Ioi 0) := _integrableOn_exp_trig ht (fun s => Real.abs_sin_le_one _) (by fun_prop)
  have hEcos : IntegrableOn (fun s : ℝ => Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
      (Set.Ioi 0) := _integrableOn_exp_trig ht (fun s => Real.abs_cos_le_one _) (by fun_prop)
  have hScos : IntegrableOn
      (fun s : ℝ => s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))
      (Set.Ioi 0) := _integrableOn_mul_exp_trig ht (fun s => Real.abs_cos_le_one _) (by fun_prop)
  -- FTC of the total s-derivative of `e^{-s-ts²} cos(xs)` over `(0,∞)`
  have hderiv : ∀ s ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.cos (x * σ))
        (-(Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
          - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))
          - x * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s))) s := by
    intro s _
    have h1 : HasDerivAt (fun σ : ℝ => -σ - t * σ ^ 2) (-1 - t * (2 * s)) s := by
      simpa using ((hasDerivAt_id s).neg.sub ((hasDerivAt_pow 2 s).const_mul t))
    have h3 : HasDerivAt (fun σ : ℝ => Real.cos (x * σ)) (-Real.sin (x * s) * x) s := by
      simpa using (Real.hasDerivAt_cos (x * s)).comp s ((hasDerivAt_id s).const_mul x)
    have h4 := h1.exp.mul h3
    convert h4 using 1
    ring
  have hf'int : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))
        - x * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s))) (Set.Ioi 0) :=
    (hEcos.neg.sub (hScos.const_mul (2 * t))).sub (hEsin.const_mul x)
  have hcont : ContinuousWithinAt
      (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.cos (x * σ)) (Set.Ici 0) 0 :=
    Continuous.continuousWithinAt (by fun_prop)
  have htend : Tendsto (fun σ : ℝ => Real.exp (-σ - t * σ ^ 2) * Real.cos (x * σ))
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun σ : ℝ => Real.exp (-σ)) _ tendsto_exp_neg_atTop_nhds_zero
    intro σ
    rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
    calc Real.exp (-σ - t * σ ^ 2) * |Real.cos (x * σ)|
        ≤ Real.exp (-σ - t * σ ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ ≤ Real.exp (-σ) := by
          rw [mul_one]
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg σ, ht.le])
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int htend
  have hFTC0 : (∫ s in Set.Ioi (0:ℝ),
      (-(Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))
        - x * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s)))) = -1 := by
    rw [hFTC]
    simp
  have hI1 : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.cos (x * s))
        - 2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))) (Set.Ioi 0) :=
    hEcos.neg.sub (hScos.const_mul (2 * t))
  have hI2 : IntegrableOn (fun s : ℝ =>
      x * (Real.exp (-s - t * s ^ 2) * Real.sin (x * s))) (Set.Ioi 0) :=
    hEsin.const_mul x
  have hI3 : IntegrableOn (fun s : ℝ =>
      -(Real.exp (-s - t * s ^ 2) * Real.cos (x * s))) (Set.Ioi 0) := hEcos.neg
  have hI4 : IntegrableOn (fun s : ℝ =>
      2 * t * (s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)))) (Set.Ioi 0) :=
    hScos.const_mul (2 * t)
  rw [integral_sub hI1 hI2, integral_sub hI3 hI4, integral_neg,
    integral_const_mul, integral_const_mul] at hFTC0
  have hV := voigtV_eq_laplace ht x
  have hU := voigtU_eq_laplace ht x
  have hD : deriv (fun x' : ℝ => FLMF.Voigt.voigtV x' t) x
      = ∫ s in Set.Ioi (0:ℝ), s * (Real.exp (-s - t * s ^ 2) * Real.cos (x * s)) :=
    (_hasDerivAt_voigtV ht x).deriv
  rw [hV, hU, hD]
  linarith [hFTC0]

/-- Cosine integral representation of `U` (DLMF 7.19.10).

DLMF 7.19.10 states this for `U(x,t)` on its 7.19.1 domain `x ∈ ℝ`, `t > 0`;
here `x = u/a` and `t = 1/(4a²) > 0` is recorded explicitly (it already follows
from `ha`) so the domain constraint is visible on the statement.
DAG: E-7.19.10.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_10 {a : ℝ} (ha : 0 < a) (u : ℝ) (_ht : 0 < 1 / (4 * a ^ 2)) :
    FLMF.Voigt.voigtU (u / a) (1 / (4 * a ^ 2))
      = a * ∫ s in Set.Ioi (0 : ℝ),
          Real.exp (-a * s - s ^ 2 / 4) * Real.cos (u * s) := by
  have ht : (0:ℝ) < 1 / (4 * a ^ 2) := by positivity
  rw [voigtU_eq_laplace ht (u / a)]
  have h := MeasureTheory.integral_comp_mul_left_Ioi
      (fun s => Real.exp (-s - 1 / (4 * a ^ 2) * s ^ 2) * Real.cos (u / a * s)) 0 ha
  simp only [mul_zero] at h
  have hcong : ∀ σ ∈ Set.Ioi (0:ℝ),
      Real.exp (-(a * σ) - 1 / (4 * a ^ 2) * (a * σ) ^ 2) * Real.cos (u / a * (a * σ))
        = Real.exp (-a * σ - σ ^ 2 / 4) * Real.cos (u * σ) := by
    intro σ _
    have h1 : -(a * σ) - 1 / (4 * a ^ 2) * (a * σ) ^ 2 = -a * σ - σ ^ 2 / 4 := by
      field_simp
    have h2 : u / a * (a * σ) = u * σ := by field_simp
    rw [h1, h2]
  rw [setIntegral_congr_fun measurableSet_Ioi hcong] at h
  rw [h, smul_eq_mul, mul_inv_cancel_left₀ ha.ne']

/-- Sine integral representation of `V` (DLMF 7.19.11).

DLMF 7.19.11.
DAG: E-7.19.11.
Numerical: PASS
Verified: verified
-/
theorem erf_7_19_11 {a : ℝ} (ha : 0 < a) (u : ℝ) :
    FLMF.Voigt.voigtV (u / a) (1 / (4 * a ^ 2))
      = a * ∫ s in Set.Ioi (0 : ℝ),
          Real.exp (-a * s - s ^ 2 / 4) * Real.sin (u * s) := by
  have ht : (0:ℝ) < 1 / (4 * a ^ 2) := by positivity
  rw [voigtV_eq_laplace ht (u / a)]
  have h := MeasureTheory.integral_comp_mul_left_Ioi
      (fun s => Real.exp (-s - 1 / (4 * a ^ 2) * s ^ 2) * Real.sin (u / a * s)) 0 ha
  simp only [mul_zero] at h
  have hcong : ∀ σ ∈ Set.Ioi (0:ℝ),
      Real.exp (-(a * σ) - 1 / (4 * a ^ 2) * (a * σ) ^ 2) * Real.sin (u / a * (a * σ))
        = Real.exp (-a * σ - σ ^ 2 / 4) * Real.sin (u * σ) := by
    intro σ _
    have h1 : -(a * σ) - 1 / (4 * a ^ 2) * (a * σ) ^ 2 = -a * σ - σ ^ 2 / 4 := by
      field_simp
    have h2 : u / a * (a * σ) = u * σ := by field_simp
    rw [h1, h2]
  rw [setIntegral_congr_fun measurableSet_Ioi hcong] at h
  rw [h, smul_eq_mul, mul_inv_cancel_left₀ ha.ne']

end FLMF.Error
