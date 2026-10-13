import Mathlib

/-!
# The Goodwin–Staton integral

The Goodwin–Staton integral (cf. DLMF 7.2.5) is

`G(z) = ∫₀^∞ e^{-t²} / (t + z) dt`,   `z ∉ (-∞, 0]`.

In this file we set up the basic analytic infrastructure using the truncated
(finite-interval) version
`G_T(z, b) = ∫₀^b e^{-t²} / (t + z) dt`.
We prove continuity and interval-integrability of the integrand on the
relevant interval for `z > 0`, the boundary value `G_T(z, 0) = 0`,
positivity, the pointwise bound on the integrand, and the elementary upper
bound `0 ≤ G_T(z, b) ≤ b / z`.
-/

namespace FLMF.GoodwinStaton

open scoped Real
open intervalIntegral MeasureTheory

-- no-dlmf: integrand of the truncated Goodwin–Staton integral; analytic infrastructure, no DLMF identity
/-- The integrand of the Goodwin–Staton integral:
`t ↦ exp(-t²) / (t + z)`. -/
noncomputable def gsIntegrand (z : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2) / (t + z)

-- no-dlmf: truncated (finite-interval) Goodwin–Staton integral; setup infrastructure, not the DLMF defining identity
/-- The truncated Goodwin–Staton integral
`G_T(z, b) = ∫₀^b exp(-t²)/(t+z) dt`. -/
noncomputable def goodwinStatonTrunc (z b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..b, gsIntegrand z t

-- no-dlmf: positivity of the denominator; analytic infrastructure, no DLMF identity
/-- For `z > 0` and `t ≥ 0` the denominator `t + z` is positive. -/
theorem denom_pos {z t : ℝ} (hz : 0 < z) (ht : 0 ≤ t) : 0 < t + z := by
  linarith

-- no-dlmf: nonnegativity of the integrand; analytic infrastructure, no DLMF identity
/-- For `z > 0` the integrand is nonnegative on `t ≥ 0`. -/
theorem gsIntegrand_nonneg {z : ℝ} (hz : 0 < z) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gsIntegrand z t := by
  unfold gsIntegrand
  exact div_nonneg (Real.exp_nonneg _) (le_of_lt (denom_pos hz ht))

-- no-dlmf: continuity of the integrand; analytic infrastructure, no DLMF identity
/-- For `z > 0` the integrand is continuous on a set where `t + z > 0`. -/
theorem continuousOn_gsIntegrand {z : ℝ} {s : Set ℝ}
    (hs : ∀ t ∈ s, 0 < t + z) : ContinuousOn (gsIntegrand z) s := by
  unfold gsIntegrand
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  · fun_prop
  · intro t ht
    exact ne_of_gt (hs t ht)

-- no-dlmf: interval-integrability of the integrand; analytic infrastructure, no DLMF identity
/-- For `z > 0` the integrand is interval-integrable on `[0, b]` when `0 ≤ b`. -/
theorem intervalIntegrable_gsIntegrand {z b : ℝ} (hz : 0 < z) (hb : 0 ≤ b) :
    IntervalIntegrable (gsIntegrand z) MeasureTheory.volume 0 b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hb]
  apply continuousOn_gsIntegrand
  intro t ht
  exact denom_pos hz ht.1

-- no-dlmf: boundary value G_T(z,0)=0; analytic infrastructure, no DLMF identity
/-- The truncated Goodwin–Staton integral vanishes at `b = 0`. -/
theorem goodwinStatonTrunc_zero (z : ℝ) : goodwinStatonTrunc z 0 = 0 := by
  unfold goodwinStatonTrunc
  rw [intervalIntegral.integral_same]

-- no-dlmf: nonnegativity of the truncated integral; analytic infrastructure, no DLMF identity
/-- For `z > 0` and `0 ≤ b`, the truncated Goodwin–Staton integral is
nonnegative. -/
theorem goodwinStatonTrunc_nonneg {z b : ℝ} (hz : 0 < z) (hb : 0 ≤ b) :
    0 ≤ goodwinStatonTrunc z b := by
  unfold goodwinStatonTrunc
  apply intervalIntegral.integral_nonneg hb
  intro t ht
  exact gsIntegrand_nonneg hz ht.1

-- no-dlmf: pointwise upper bound on the integrand; analytic infrastructure, no DLMF identity
/-- Pointwise upper bound: for `z > 0`, `t ≥ 0`, the integrand is bounded by
`1 / z`. -/
theorem gsIntegrand_le {z : ℝ} (hz : 0 < z) {t : ℝ} (ht : 0 ≤ t) :
    gsIntegrand z t ≤ 1 / z := by
  unfold gsIntegrand
  have h1 : Real.exp (-t ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
  have hden : 0 < t + z := denom_pos hz ht
  have hstep : Real.exp (-t ^ 2) / (t + z) ≤ 1 / (t + z) :=
    div_le_div_of_nonneg_right h1 hden.le
  have hstep2 : (1 : ℝ) / (t + z) ≤ 1 / z :=
    one_div_le_one_div_of_le hz (by linarith)
  exact le_trans hstep hstep2

-- no-dlmf: elementary upper bound G_T ≤ b/z; analytic infrastructure, no DLMF identity
/-- For `z > 0` and `0 ≤ b`, the truncated Goodwin–Staton integral is bounded
above by `b / z`. -/
theorem goodwinStatonTrunc_le {z b : ℝ} (hz : 0 < z) (hb : 0 ≤ b) :
    goodwinStatonTrunc z b ≤ b / z := by
  unfold goodwinStatonTrunc
  have hib := intervalIntegrable_gsIntegrand hz hb
  have hconst : IntervalIntegrable (fun _ : ℝ => 1 / z) MeasureTheory.volume 0 b :=
    intervalIntegral.intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hb hib hconst
    (fun t ht => gsIntegrand_le hz ht.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  calc (∫ t in (0:ℝ)..b, gsIntegrand z t) ≤ b * (1 / z) := hmono
    _ = b / z := by ring

end FLMF.GoodwinStaton
