import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Voigt functions `U` and `V` (DLMF §7.19)

The Voigt functions arise as convolutions of a Lorentzian profile with a Gaussian.
Following DLMF 7.19.1, for `x : ℝ` and `t > 0` we define

`U(x,t) = (1/√(4πt)) ∫_ℝ exp(-(x-y)²/(4t)) / (1+y²) dy`
`V(x,t) = (1/√(4πt)) ∫_ℝ y exp(-(x-y)²/(4t)) / (1+y²) dy`

Main results:

* `FLMF.Voigt.integrable_kernelU` / `integrable_kernelV`: the integrands are integrable.
* `FLMF.Voigt.voigtU_neg` : `U(-x,t) = U(x,t)` (`U` is even in `x`).
* `FLMF.Voigt.voigtV_neg` : `V(-x,t) = -V(x,t)` (`V` is odd in `x`).
* `FLMF.Voigt.voigtU_nonneg` : `U(x,t) ≥ 0` for `t > 0`.
-/

namespace FLMF.Voigt

open MeasureTheory Real Filter Topology Set

-- no-dlmf: Gaussian factor of the Voigt integrands; building block, no DLMF identity
/-- The Gaussian factor `exp(-(x-y)²/(4t))` appearing in the Voigt integrands. -/
noncomputable def gauss (x t y : ℝ) : ℝ := Real.exp (-(x - y) ^ 2 / (4 * t))

-- no-dlmf: integrand of the Voigt function U; building block, no DLMF identity
/-- The integrand of the Voigt function `U`. -/
noncomputable def kernelU (x t y : ℝ) : ℝ := gauss x t y / (1 + y ^ 2)

-- no-dlmf: integrand of the Voigt function V; building block, no DLMF identity
/-- The integrand of the Voigt function `V`. -/
noncomputable def kernelV (x t y : ℝ) : ℝ := y * gauss x t y / (1 + y ^ 2)

/-- The Voigt function `U(x,t)` (DLMF 7.19.1).

DLMF 7.19.1.
-/
-- DAG: E-7.19.1.
-- Verified: verified
noncomputable def voigtU (x t : ℝ) : ℝ :=
  (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, kernelU x t y

/-- The Voigt function `V(x,t)` (DLMF 7.19.2).

DLMF 7.19.2.
-/
-- DAG: E-7.19.2.
-- Verified: verified
noncomputable def voigtV (x t : ℝ) : ℝ :=
  (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, kernelV x t y

-- no-dlmf: positivity of the Gaussian factor; analytic infrastructure, no DLMF identity
theorem gauss_pos (x t y : ℝ) : 0 < gauss x t y := Real.exp_pos _

-- no-dlmf: nonnegativity of the Gaussian factor; analytic infrastructure, no DLMF identity
theorem gauss_nonneg (x t y : ℝ) : 0 ≤ gauss x t y := (gauss_pos x t y).le

-- no-dlmf: integrability of the Gaussian factor; analytic infrastructure, no DLMF identity
/-- `y ↦ exp(-(x-y)²/(4t))` is integrable for `t > 0`. -/
theorem integrable_gauss {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => gauss x t y) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have hbase : Integrable (fun z : ℝ => Real.exp (-(1 / (4 * t)) * z ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hshift := hbase.comp_sub_right x
  refine hshift.congr ?_
  filter_upwards with y
  simp only [gauss]
  congr 1
  field_simp
  ring

-- no-dlmf: continuity of the Gaussian factor; analytic infrastructure, no DLMF identity
theorem continuous_gauss (x t : ℝ) : Continuous (fun y : ℝ => gauss x t y) := by
  unfold gauss; fun_prop

-- no-dlmf: positivity of 1+y²; elementary helper, no DLMF identity
theorem one_add_sq_pos (y : ℝ) : (0 : ℝ) < 1 + y ^ 2 := by positivity

-- no-dlmf: continuity of the U integrand; analytic infrastructure, no DLMF identity
theorem continuous_kernelU (x t : ℝ) : Continuous (fun y : ℝ => kernelU x t y) := by
  unfold kernelU
  exact (continuous_gauss x t).div (by fun_prop) (fun y => (one_add_sq_pos y).ne')

-- no-dlmf: continuity of the V integrand; analytic infrastructure, no DLMF identity
theorem continuous_kernelV (x t : ℝ) : Continuous (fun y : ℝ => kernelV x t y) := by
  unfold kernelV
  exact ((continuous_id.mul (continuous_gauss x t)).div (by fun_prop)
    (fun y => (one_add_sq_pos y).ne'))

-- no-dlmf: pointwise dominating bound for the U integrand; analytic infrastructure, no DLMF identity
/-- `|kernelU x t y| ≤ gauss x t y`. -/
theorem norm_kernelU_le (x t y : ℝ) : ‖kernelU x t y‖ ≤ gauss x t y := by
  have hpos := one_add_sq_pos y
  rw [Real.norm_eq_abs, kernelU, abs_div, abs_of_pos hpos, abs_of_pos (gauss_pos x t y),
    div_le_iff₀ hpos]
  nlinarith [gauss_nonneg x t y, sq_nonneg y]

-- no-dlmf: pointwise dominating bound for the V integrand; analytic infrastructure, no DLMF identity
/-- `|kernelV x t y| ≤ gauss x t y`. -/
theorem norm_kernelV_le (x t y : ℝ) : ‖kernelV x t y‖ ≤ gauss x t y := by
  have hpos := one_add_sq_pos y
  rw [Real.norm_eq_abs, kernelV, abs_div, abs_of_pos hpos, abs_mul,
    abs_of_pos (gauss_pos x t y), div_le_iff₀ hpos]
  have hy : |y| ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  nlinarith [gauss_nonneg x t y, abs_nonneg y]

-- no-dlmf: integrability of the U integrand; analytic infrastructure, no DLMF identity
/-- The integrand of `U` is integrable for `t > 0`. -/
theorem integrable_kernelU {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => kernelU x t y) := by
  refine Integrable.mono' (integrable_gauss ht x)
    (continuous_kernelU x t).aestronglyMeasurable ?_
  filter_upwards with y using norm_kernelU_le x t y

-- no-dlmf: integrability of the V integrand; analytic infrastructure, no DLMF identity
/-- The integrand of `V` is integrable for `t > 0`. -/
theorem integrable_kernelV {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => kernelV x t y) := by
  refine Integrable.mono' (integrable_gauss ht x)
    (continuous_kernelV x t).aestronglyMeasurable ?_
  filter_upwards with y using norm_kernelV_le x t y

-- no-dlmf: evenness of U in x; elementary parity, no specific DLMF identity number
/-- `U` is even in `x`: `U(-x,t) = U(x,t)`. -/
theorem voigtU_neg (x t : ℝ) : voigtU (-x) t = voigtU x t := by
  unfold voigtU
  congr 1
  rw [← integral_neg_eq_self (fun y : ℝ => kernelU x t y) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [kernelU, gauss]
  have h1 : (-x - y) ^ 2 = (x - -y) ^ 2 := by ring
  have h2 : (1 : ℝ) + y ^ 2 = 1 + (-y) ^ 2 := by ring
  rw [h1, h2]

-- no-dlmf: oddness of V in x; elementary parity, no specific DLMF identity number
/-- `V` is odd in `x`: `V(-x,t) = -V(x,t)`. -/
theorem voigtV_neg (x t : ℝ) : voigtV (-x) t = -voigtV x t := by
  unfold voigtV
  rw [neg_mul_eq_mul_neg]
  congr 1
  rw [← integral_neg]
  rw [← integral_neg_eq_self (fun y : ℝ => -kernelV x t y) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [kernelV, gauss]
  have h1 : (-x - y) ^ 2 = (x - -y) ^ 2 := by ring
  have h2 : (1 : ℝ) + y ^ 2 = 1 + (-y) ^ 2 := by ring
  rw [h1, h2]
  ring

-- no-dlmf: nonnegativity of U; analytic infrastructure, no specific DLMF identity number
/-- `U(x,t) ≥ 0` for `t > 0`. -/
theorem voigtU_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ voigtU x t := by
  unfold voigtU
  apply mul_nonneg
  · positivity
  · apply integral_nonneg
    intro y
    simp only [kernelU, Pi.zero_apply]
    have := gauss_nonneg x t y
    have := one_add_sq_pos y
    positivity

end FLMF.Voigt
