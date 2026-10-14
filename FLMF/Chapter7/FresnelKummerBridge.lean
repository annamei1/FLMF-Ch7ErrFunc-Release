import FLMF.Support.HypergeometricKummerODE
import FLMF.Chapter7.FresnelBasic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Fresnel integrals as a `₁F₁` instance (bridge — DLMF 7.11.6)

* `fresnel_eq_kummerM` — `C(x) + i S(x) = x · M(1/2; 3/2; iπx²/2)`
  (DLMF 7.11.6), for all real `x`.

The combined integrand `cos(πt²/2) + i sin(πt²/2) = e^{iπt²/2}` is expanded
into the exponential series; the termwise pieces are the monomials
`(iπ/2)ⁿ t^{2n}/n!`, so the sum–integral interchange (norm-integrals dominated
by `(d−c)·((π/2)R²)ⁿ/n!` on `Ioc c d`) and termwise integration work on both
orientations of the interval — exactly the gaussian/erf pattern, over `ℂ`. The
Kummer series is matched through `cₙ(1/2,3/2) = 1/((2n+1)·n!)`.
-/

noncomputable section

open Nat MeasureTheory Real Set Complex FLMF.Hypergeometric

namespace FLMF.Fresnel

/-- The combined Fresnel integrand, `e^{iπt²/2}` in rectangular form. -/
-- no-dlmf: series-term helper for the 7.11.4 proof, no DLMF counterpart
private def fresnelTerm (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.pi : ℂ) / 2 * Complex.I) ^ n / n ! * (t : ℂ) ^ (2 * n)

-- no-dlmf: norm helper for the 7.11.4 proof, no DLMF counterpart
private theorem norm_fresnelConst : ‖(Real.pi : ℂ) / 2 * Complex.I‖ = Real.pi / 2 := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_div]
  simp [abs_of_pos Real.pi_pos]

-- no-dlmf: summability helper for the sum-integral interchange in the 7.11.4 proof
private theorem fresnelTerm_summable_integral {c d : ℝ} (hcd : c ≤ d) :
    Summable fun n : ℕ => ∫ t in Ioc c d, ‖fresnelTerm n t‖ := by
  set R : ℝ := max |c| |d| with hR
  have hbound : ∀ n : ℕ, ∫ t in Ioc c d, ‖fresnelTerm n t‖
      ≤ (d - c) * ((Real.pi / 2 * R ^ 2) ^ n / n !) := by
    intro n
    have hle : ∀ t ∈ Ioc c d, ‖fresnelTerm n t‖ ≤ (Real.pi / 2 * R ^ 2) ^ n / n ! := by
      intro t ht
      have htR : |t| ≤ R := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · calc -R ≤ -|c| := by simp [hR]
            _ ≤ c := neg_abs_le c
            _ ≤ t := ht.1.le
        · calc t ≤ d := ht.2
            _ ≤ |d| := le_abs_self d
            _ ≤ R := le_max_right _ _
      have habs : ‖fresnelTerm n t‖ = (Real.pi / 2) ^ n * |t| ^ (2 * n) / n ! := by
        simp only [fresnelTerm]
        rw [norm_mul, norm_div, norm_pow, norm_fresnelConst, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
        ring
      rw [habs, mul_pow, ← pow_mul]
      gcongr
    calc ∫ t in Ioc c d, ‖fresnelTerm n t‖
        ≤ ∫ _ in Ioc c d, (Real.pi / 2 * R ^ 2) ^ n / n ! := by
          refine setIntegral_mono_on ?_ (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc hle
          exact ((continuous_const.mul
            ((Complex.continuous_ofReal).pow _)).integrableOn_Ioc).norm
      _ = (d - c) * ((Real.pi / 2 * R ^ 2) ^ n / n !) := by
          rw [setIntegral_const, smul_eq_mul, volume_real_Ioc_of_le hcd]
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun t => norm_nonneg _) hbound
    ((Real.summable_pow_div_factorial (Real.pi / 2 * R ^ 2)).mul_left _)

-- no-dlmf: duplicate of DLMF 7.11.6; canonical surface is `erf_7_11_6` (Error/Ch7RelationsOther.lean)
/-- **The Fresnel integrals as a terminating-free `₁F₁` instance**
(DLMF 7.11.6): `C(x) + i S(x) = x · M(1/2; 3/2; iπx²/2)`, for all real `x`.

-/
theorem fresnel_eq_kummerM (x : ℝ) :
    (fresnelC x : ℂ) + Complex.I * fresnelS x
      = x * ₁F₁ ((1 : ℂ) / 2) (3 / 2) (Complex.I * Real.pi * x ^ 2 / 2) := by
  -- the combined integrand is the sum of its series, pointwise
  have hpt : ∀ t : ℝ, (cosArg t : ℂ) + Complex.I * sinArg t = ∑' n : ℕ, fresnelTerm n t := by
    intro t
    have h1 : (cosArg t : ℂ) + Complex.I * sinArg t
        = Complex.exp (((Real.pi * t ^ 2 / 2 : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, cosArg, sinArg, Complex.ofReal_cos, Complex.ofReal_sin]
      ring
    rw [h1, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    refine tsum_congr fun n => ?_
    have harg : ((Real.pi * t ^ 2 / 2 : ℝ) : ℂ) * Complex.I
        = (Real.pi : ℂ) / 2 * Complex.I * (t : ℂ) ^ 2 := by
      push_cast
      ring
    rw [fresnelTerm, harg, mul_pow, pow_mul]
    ring
  -- interchange on `Ioc c d`
  have hswap : ∀ {c d : ℝ}, c ≤ d →
      ∫ t in Ioc c d, ((cosArg t : ℂ) + Complex.I * sinArg t)
        = ∑' n : ℕ, ∫ t in Ioc c d, fresnelTerm n t := by
    intro c d hcd
    have hFint : ∀ n : ℕ, IntegrableOn (fresnelTerm n) (Ioc c d) := by
      intro n
      exact ((continuous_const.mul ((Complex.continuous_ofReal).pow _)).integrableOn_Ioc)
    rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => hpt t]
    exact (integral_tsum_of_summable_integral_norm hFint
      (fresnelTerm_summable_integral hcd)).symm
  -- the termwise interval integral
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..x, fresnelTerm n t
      = ((Real.pi : ℂ) / 2 * Complex.I) ^ n / n !
        * ((x ^ (2 * n + 1) / (2 * n + 1) : ℝ) : ℂ) := by
    intro n
    simp only [fresnelTerm]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcast : (fun t : ℝ => ((t : ℂ)) ^ (2 * n)) = fun t : ℝ => ((t ^ (2 * n) : ℝ) : ℂ) := by
      funext t
      push_cast
      ring
    rw [hcast, intervalIntegral.integral_ofReal, integral_pow]
    norm_num
  -- the combined Fresnel integral as a series
  have hI : (fresnelC x : ℂ) + Complex.I * fresnelS x
      = ∑' n : ℕ, ((Real.pi : ℂ) / 2 * Complex.I) ^ n / n !
        * ((x ^ (2 * n + 1) / (2 * n + 1) : ℝ) : ℂ) := by
    have hint1 : IntervalIntegrable (fun t : ℝ => (cosArg t : ℂ)) volume 0 x :=
      (Complex.continuous_ofReal.comp continuous_cosArg).intervalIntegrable 0 x
    have hint2 : IntervalIntegrable (fun t : ℝ => Complex.I * (sinArg t : ℂ)) volume 0 x :=
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_sinArg)).intervalIntegrable
        0 x
    have hsplit : (fresnelC x : ℂ) + Complex.I * fresnelS x
        = ∫ t in (0 : ℝ)..x, ((cosArg t : ℂ) + Complex.I * sinArg t) := by
      rw [fresnelC, fresnelS, ← intervalIntegral.integral_ofReal (f := cosArg),
        ← intervalIntegral.integral_ofReal (f := sinArg),
        ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hint1 hint2]
    rw [hsplit]
    rcases le_total 0 x with hx | hx
    · rw [intervalIntegral.integral_of_le hx, hswap hx]
      refine tsum_congr fun n => ?_
      rw [← hterm n, intervalIntegral.integral_of_le hx]
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx, hswap hx,
        ← tsum_neg]
      refine tsum_congr fun n => ?_
      rw [← hterm n, intervalIntegral.integral_symm x 0, intervalIntegral.integral_of_le hx]
  -- match against the Kummer series
  have hM := (kummerM_hasSum ((1 : ℂ) / 2) (3 / 2)
    (Complex.I * Real.pi * x ^ 2 / 2)).mul_left (x : ℂ)
  have hterm2 : (fun n : ℕ => (x : ℂ) * (kummerCoefficient ((1 : ℂ) / 2) (3 / 2) n
      * (Complex.I * Real.pi * x ^ 2 / 2) ^ n)) =
      fun n : ℕ => ((Real.pi : ℂ) / 2 * Complex.I) ^ n / n !
        * ((x ^ (2 * n + 1) / (2 * n + 1) : ℝ) : ℂ) := by
    funext n
    rw [kummerCoefficient_one_half n,
      show Complex.I * Real.pi * x ^ 2 / 2 = (Real.pi : ℂ) / 2 * Complex.I * (x : ℂ) ^ 2 by
        ring,
      mul_pow]
    have h2n : (2 * (n : ℂ) + 1) ≠ 0 := by
      intro hk
      have h2 : ((2 * n + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hk
      exact Nat.cast_ne_zero.2 (by lia) h2
    have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    field_simp
    ring
  rw [hterm2] at hM
  rw [hI, hM.tsum_eq]

end FLMF.Fresnel
