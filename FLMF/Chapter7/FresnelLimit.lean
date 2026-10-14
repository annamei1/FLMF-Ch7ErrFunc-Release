import FLMF.Chapter7.FresnelBasic
import FLMF.Support.StationaryPhase
import FLMF.Support.AbelianGaussian
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Limits of the Fresnel integrals at `+∞` (DLMF §7.12)

The Fresnel integrals satisfy `C(x) → 1/2` and `S(x) → 1/2` as `x → +∞`
(DLMF 7.2.7 in conjunction with the normalization `C(∞) = S(∞) = 1/2`,
DLMF 7.5.1).

This module proves the **convergence half** of that statement, sorry-free:
`C` and `S` each converge at `+∞` to *some* real limit
(`exists_tendsto_fresnelC`, `exists_tendsto_fresnelS`). The mechanism is the
oscillatory-tail (non-stationary-phase) bound

`|∫ₐᵇ cos(πt²/2) dt| ≤ 3/(π a)`  (and the same for `sin`),  for `0 < a ≤ b`,

obtained by one integration by parts (`u = 1/(πt)`, `dv = d sin(πt²/2)`),
exactly mirroring `FLMF/Functions/ExpIntegrals/SiLeading.lean`'s
`abs_integral_sin_div_le` for `Si`. The tail bound makes `C` and `S` Cauchy at
`atTop`, hence convergent in the complete space `ℝ`.

It also records, sorry-free, the **Abel value** of the (full-line) regularized
Fresnel Gaussian: with the DLMF phase `a = π/2`,

`lim_{ε↓0} ∫_ℝ e^{-(ε - i(π/2))x²} dx = (2i)^{1/2} = 1 + i`   (`abel_value_eq`),

via `FLMF.Methods.StationaryPhase.fresnel_regularized` and
`cpow_half_pos_mul_I`. Its real/imaginary parts are `1` (full line), i.e. `1/2`
on the half line `(0,∞)` — the conjectured limit values of `C` and `S`.

## Value identification (`L_C = L_S = 1/2`)

The limits are pinned to `1/2` via the **Abelian bridge**
(`tendsto_fresnelC`, `tendsto_fresnelS`), sorry-free. Two ingredients combine:

1. **Abelian–Gaussian** (`FLMF.Methods.AbelianGaussian.abelian_gaussian`): the
   improper convergence `∫_0^R cosArg → L_C` (the convergence half above) implies
   the Gaussian-regularized half-line value
   `lim_{ε↓0} ∫_{(0,∞)} e^{-εt²} cosArg = L_C` (likewise for `sinArg`/`L_S`).

2. **Regularized full-line Fresnel Gaussian**
   (`FLMF.Methods.StationaryPhase.fresnel_regularized` with `a = π/2`):
   `lim_{ε↓0} ∫_ℝ e^{-(ε - i(π/2))x²} dx = (2i)^{1/2} = 1 + i` (`abel_value_eq`).
   Taking real/imaginary parts and using the integrand's evenness
   (`integral_comp_abs`) gives `2·lim_{ε↓0} ∫_{(0,∞)} e^{-εt²} cosArg = 1` and
   `2·lim_{ε↓0} ∫_{(0,∞)} e^{-εt²} sinArg = 1`.

Uniqueness of limits then forces `L_C = L_S = 1/2`, hence
`C(x) → 1/2` and `S(x) → 1/2` as `x → +∞` (DLMF 7.5.1).
-/

namespace FLMF.Fresnel

open scoped Real Interval
open MeasureTheory intervalIntegral Set Filter Topology

/-- **Integration-by-parts identity for the cosine tail.** For `0 < a ≤ b`,
`∫ₐᵇ cos(πt²/2) dt = sin(πb²/2)/(πb) - sin(πa²/2)/(πa) + ∫ₐᵇ sin(πt²/2)/(πt²) dt`.
We use `u = 1/(πt)`, `v = sin(πt²/2)`, with `v' = π t cos(πt²/2)` and
`u' = -1/(πt²)`; note `cos(πt²/2) = u·v'`. -/
-- no-dlmf: integration-by-parts tail identity, no DLMF counterpart
theorem integral_cosArg_eq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, cosArg t)
      = Real.sin (Real.pi * b ^ 2 / 2) / (Real.pi * b)
        - Real.sin (Real.pi * a ^ 2 / 2) / (Real.pi * a)
        + ∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) := by
  have hpi := Real.pi_pos
  have hsubset : ∀ x ∈ [[a, b]], x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hu : ∀ x ∈ [[a, b]], HasDerivAt (fun y : ℝ => (Real.pi * y)⁻¹)
      (-(Real.pi * x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := hsubset x hx
    have hpx : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt hpi) hx0
    have h1 : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    have := (h1.inv hpx)
    convert this using 1
    field_simp
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (fun y : ℝ => Real.sin (Real.pi * y ^ 2 / 2))
      (Real.pi * x * cosArg x) x := by
    intro x _
    have hp : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2 / 2) (Real.pi * x) x := by
      have : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2 / 2)
          (Real.pi * (2 * x ^ (2-1)) / 2) x := by
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ (2-1)) x := hasDerivAt_pow 2 x
        simpa using (h2.const_mul Real.pi).div_const 2
      convert this using 1
      norm_num; ring
    have := (Real.hasDerivAt_sin (Real.pi * x ^ 2 / 2)).comp x hp
    rw [cosArg]
    convert this using 1
    ring
  have hu' : IntervalIntegrable (fun x => -(Real.pi * x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      have hx0 : x ≠ 0 := hsubset x hx
      have : (0:ℝ) < x ^ 2 := by positivity
      positivity
  have hv' : IntervalIntegrable (fun x => Real.pi * x * cosArg x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (Continuous.continuousOn (by fun_prop)).mul continuous_cosArg.continuousOn
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : (∫ x in a..b, (Real.pi * x)⁻¹ * (Real.pi * x * cosArg x))
      = ∫ t in a..b, cosArg t := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : x ≠ 0 := hsubset x hx
    have hpx : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt hpi) hx0
    field_simp
  rw [hlhs] at hIBP
  rw [hIBP]
  have hrhs : (∫ x in a..b, -(Real.pi * x ^ 2)⁻¹ * Real.sin (Real.pi * x ^ 2 / 2))
      = - ∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [neg_mul, neg_inj, div_eq_mul_inv]; ring
  rw [hrhs]
  rw [div_eq_inv_mul (Real.sin (Real.pi * b ^ 2 / 2)),
      div_eq_inv_mul (Real.sin (Real.pi * a ^ 2 / 2))]
  ring

/-- **Integration-by-parts identity for the sine tail.** For `0 < a ≤ b`,
`∫ₐᵇ sin(πt²/2) dt = -cos(πb²/2)/(πb) + cos(πa²/2)/(πa) - ∫ₐᵇ cos(πt²/2)/(πt²) dt`.
Here `v = -cos(πt²/2)`, `v' = π t sin(πt²/2)`. -/
-- no-dlmf: integration-by-parts tail identity, no DLMF counterpart
theorem integral_sinArg_eq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, sinArg t)
      = -Real.cos (Real.pi * b ^ 2 / 2) / (Real.pi * b)
        + Real.cos (Real.pi * a ^ 2 / 2) / (Real.pi * a)
        - ∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) := by
  have hpi := Real.pi_pos
  have hsubset : ∀ x ∈ [[a, b]], x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hu : ∀ x ∈ [[a, b]], HasDerivAt (fun y : ℝ => (Real.pi * y)⁻¹)
      (-(Real.pi * x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := hsubset x hx
    have hpx : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt hpi) hx0
    have h1 : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    have := (h1.inv hpx)
    convert this using 1
    field_simp
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (fun y : ℝ => -Real.cos (Real.pi * y ^ 2 / 2))
      (Real.pi * x * sinArg x) x := by
    intro x _
    have hp : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2 / 2) (Real.pi * x) x := by
      have : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2 / 2)
          (Real.pi * (2 * x ^ (2-1)) / 2) x := by
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ (2-1)) x := hasDerivAt_pow 2 x
        simpa using (h2.const_mul Real.pi).div_const 2
      convert this using 1
      norm_num; ring
    have := ((Real.hasDerivAt_cos (Real.pi * x ^ 2 / 2)).comp x hp).neg
    rw [sinArg]
    convert this using 1
    ring
  have hu' : IntervalIntegrable (fun x => -(Real.pi * x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      have hx0 : x ≠ 0 := hsubset x hx
      positivity
  have hv' : IntervalIntegrable (fun x => Real.pi * x * sinArg x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (Continuous.continuousOn (by fun_prop)).mul continuous_sinArg.continuousOn
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hlhs : (∫ x in a..b, (Real.pi * x)⁻¹ * (Real.pi * x * sinArg x))
      = ∫ t in a..b, sinArg t := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : x ≠ 0 := hsubset x hx
    have hpx : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt hpi) hx0
    field_simp
  rw [hlhs] at hIBP
  rw [hIBP]
  have hrhs : (∫ x in a..b, -(Real.pi * x ^ 2)⁻¹ * -Real.cos (Real.pi * x ^ 2 / 2))
      = ∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [neg_mul_neg, div_eq_mul_inv]; ring
  rw [hrhs]
  ring

/-- Auxiliary: `∫ₐᵇ 1/(π t²) dt = (1/a - 1/b)/π` for `0 < a ≤ b`. -/
-- no-dlmf: elementary auxiliary integral, no DLMF counterpart
theorem integral_inv_pi_sq (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (Real.pi * t ^ 2)⁻¹) = (1 / a - 1 / b) / Real.pi := by
  have hpi := Real.pi_pos
  have hderiv : ∀ x ∈ [[a, b]], HasDerivAt (fun y : ℝ => -(Real.pi * y)⁻¹)
      ((Real.pi * x ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    have hpx : Real.pi * x ≠ 0 := mul_ne_zero (ne_of_gt hpi) hx0
    have h1 : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
      simpa using (hasDerivAt_id x).const_mul Real.pi
    have := (h1.inv hpx).neg
    convert this using 1
    field_simp
  have hint : IntervalIntegrable (fun t => (Real.pi * t ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hab)
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp
  ring

/-- **Oscillatory tail bound for the cosine integral.** For `0 < a ≤ b`,
`|∫ₐᵇ cos(πt²/2) dt| ≤ 3/(π a)` — the non-stationary-phase decay underlying
`C(x) → 1/2`. -/
-- no-dlmf: oscillatory tail bound (convergence infrastructure), no DLMF counterpart
theorem abs_integral_cosArg_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, cosArg t| ≤ 3 / (Real.pi * a) := by
  have hpi := Real.pi_pos
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [integral_cosArg_eq a b ha hab]
  have htail_int : IntervalIntegrable
      (fun t => Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_sinArg.continuousOn)
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
      positivity
  have habs_int : IntervalIntegrable
      (fun t => |Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|) volume a b :=
    htail_int.abs
  have hinv_int : IntervalIntegrable (fun t => (Real.pi * t ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
      positivity
  have hstep1 : |∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
      ≤ ∫ t in a..b, |Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have hstep2 : (∫ t in a..b, |Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|)
      ≤ ∫ t in a..b, (Real.pi * t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hab habs_int hinv_int
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * x ^ 2)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * x ^ 2)]
    calc |Real.sin (Real.pi * x ^ 2 / 2)| ≤ 1 := Real.abs_sin_le_one _
      _ = (Real.pi * x ^ 2)⁻¹ * (Real.pi * x ^ 2) := by
            rw [inv_mul_cancel₀]; positivity
  have htail : |∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
      ≤ (1 / a - 1 / b) / Real.pi := by
    calc |∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
        ≤ ∫ t in a..b, (Real.pi * t ^ 2)⁻¹ := le_trans hstep1 hstep2
      _ = (1 / a - 1 / b) / Real.pi := integral_inv_pi_sq a b ha hab
  set Sb := Real.sin (Real.pi * b ^ 2 / 2) / (Real.pi * b) with hSb
  set Sa := Real.sin (Real.pi * a ^ 2 / 2) / (Real.pi * a) with hSa
  set I := ∫ t in a..b, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) with hI
  have hSbbd : |Sb| ≤ 1 / (Real.pi * b) := by
    rw [hSb, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * b)]
    gcongr
    exact Real.abs_sin_le_one _
  have hSabd : |Sa| ≤ 1 / (Real.pi * a) := by
    rw [hSa, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * a)]
    gcongr
    exact Real.abs_sin_le_one _
  have hb_le_a : 1 / (Real.pi * b) ≤ 1 / (Real.pi * a) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have htail' : (1 / a - 1 / b) / Real.pi ≤ 1 / (Real.pi * a) := by
    have h1 : 1 / a - 1 / b ≤ 1 / a := by
      have : 0 ≤ 1 / b := by positivity
      linarith
    calc (1 / a - 1 / b) / Real.pi ≤ (1 / a) / Real.pi := by gcongr
      _ = 1 / (Real.pi * a) := by rw [div_div, mul_comm]
  calc |Sb - Sa + I| ≤ |Sb| + |Sa| + |I| := by
        calc |Sb - Sa + I| ≤ |Sb - Sa| + |I| := abs_add_le _ _
          _ ≤ (|Sb| + |Sa|) + |I| := by gcongr; exact abs_sub _ _
    _ ≤ 1 / (Real.pi * b) + 1 / (Real.pi * a) + (1 / a - 1 / b) / Real.pi := by
        gcongr
    _ ≤ 1 / (Real.pi * a) + 1 / (Real.pi * a) + 1 / (Real.pi * a) := by
        gcongr
    _ = 3 / (Real.pi * a) := by ring

/-- **Oscillatory tail bound for the sine integral.** For `0 < a ≤ b`,
`|∫ₐᵇ sin(πt²/2) dt| ≤ 3/(π a)`. -/
-- no-dlmf: oscillatory tail bound (convergence infrastructure), no DLMF counterpart
theorem abs_integral_sinArg_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, sinArg t| ≤ 3 / (Real.pi * a) := by
  have hpi := Real.pi_pos
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [integral_sinArg_eq a b ha hab]
  have htail_int : IntervalIntegrable
      (fun t => Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_cosArg.continuousOn)
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
      positivity
  have habs_int : IntervalIntegrable
      (fun t => |Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|) volume a b :=
    htail_int.abs
  have hinv_int : IntervalIntegrable (fun t => (Real.pi * t ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      rw [uIcc_of_le hab] at hx
      have : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
      positivity
  have hstep1 : |∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
      ≤ ∫ t in a..b, |Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have hstep2 : (∫ t in a..b, |Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|)
      ≤ ∫ t in a..b, (Real.pi * t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hab habs_int hinv_int
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le ha hx.1
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * x ^ 2)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * x ^ 2)]
    calc |Real.cos (Real.pi * x ^ 2 / 2)| ≤ 1 := Real.abs_cos_le_one _
      _ = (Real.pi * x ^ 2)⁻¹ * (Real.pi * x ^ 2) := by
            rw [inv_mul_cancel₀]; positivity
  have htail : |∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
      ≤ (1 / a - 1 / b) / Real.pi := by
    calc |∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
        ≤ ∫ t in a..b, (Real.pi * t ^ 2)⁻¹ := le_trans hstep1 hstep2
      _ = (1 / a - 1 / b) / Real.pi := integral_inv_pi_sq a b ha hab
  set Cb := -Real.cos (Real.pi * b ^ 2 / 2) / (Real.pi * b) with hCb
  set Ca := Real.cos (Real.pi * a ^ 2 / 2) / (Real.pi * a) with hCa
  set I := ∫ t in a..b, Real.cos (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2) with hI
  have hCbbd : |Cb| ≤ 1 / (Real.pi * b) := by
    rw [hCb, neg_div, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * b)]
    gcongr
    exact Real.abs_cos_le_one _
  have hCabd : |Ca| ≤ 1 / (Real.pi * a) := by
    rw [hCa, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * a)]
    gcongr
    exact Real.abs_cos_le_one _
  have hb_le_a : 1 / (Real.pi * b) ≤ 1 / (Real.pi * a) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have htail' : (1 / a - 1 / b) / Real.pi ≤ 1 / (Real.pi * a) := by
    have h1 : 1 / a - 1 / b ≤ 1 / a := by
      have : 0 ≤ 1 / b := by positivity
      linarith
    calc (1 / a - 1 / b) / Real.pi ≤ (1 / a) / Real.pi := by gcongr
      _ = 1 / (Real.pi * a) := by rw [div_div, mul_comm]
  calc |Cb + Ca - I| ≤ |Cb| + |Ca| + |I| := by
        calc |Cb + Ca - I| ≤ |Cb + Ca| + |I| := abs_sub _ _
          _ ≤ (|Cb| + |Ca|) + |I| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 / (Real.pi * b) + 1 / (Real.pi * a) + (1 / a - 1 / b) / Real.pi := by
        gcongr
    _ ≤ 1 / (Real.pi * a) + 1 / (Real.pi * a) + 1 / (Real.pi * a) := by
        gcongr
    _ = 3 / (Real.pi * a) := by ring

/-- **Cauchy increment for `C`.** For thresholds `N ≤ u, v` (`N > 0`),
`|C(v) - C(u)| ≤ 3/(π N)`. -/
-- no-dlmf: Cauchy-increment helper (convergence infrastructure), no DLMF counterpart
theorem fresnelC_increment_bound (N u v : ℝ) (hN : 0 < N) (hu : N ≤ u) (hv : N ≤ v) :
    |fresnelC v - fresnelC u| ≤ 3 / (Real.pi * N) := by
  have hpi := Real.pi_pos
  have key : ∀ p q : ℝ, N ≤ p → p ≤ q → |fresnelC q - fresnelC p| ≤ 3 / (Real.pi * N) := by
    intro p q hp hpq
    have hp0 : 0 < p := lt_of_lt_of_le hN hp
    have hdiff : fresnelC q - fresnelC p = ∫ t in p..q, cosArg t := by
      rw [fresnelC, fresnelC, intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_cosArg 0 q) (intervalIntegrable_cosArg 0 p)]
    rw [hdiff]
    calc |∫ t in p..q, cosArg t| ≤ 3 / (Real.pi * p) := abs_integral_cosArg_le p q hp0 hpq
      _ ≤ 3 / (Real.pi * N) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          gcongr
  rcases le_total u v with h | h
  · exact key u v hu h
  · rw [abs_sub_comm]; exact key v u hv h

/-- **Cauchy increment for `S`.** For thresholds `N ≤ u, v` (`N > 0`),
`|S(v) - S(u)| ≤ 3/(π N)`. -/
-- no-dlmf: Cauchy-increment helper (convergence infrastructure), no DLMF counterpart
theorem fresnelS_increment_bound (N u v : ℝ) (hN : 0 < N) (hu : N ≤ u) (hv : N ≤ v) :
    |fresnelS v - fresnelS u| ≤ 3 / (Real.pi * N) := by
  have hpi := Real.pi_pos
  have key : ∀ p q : ℝ, N ≤ p → p ≤ q → |fresnelS q - fresnelS p| ≤ 3 / (Real.pi * N) := by
    intro p q hp hpq
    have hp0 : 0 < p := lt_of_lt_of_le hN hp
    have hdiff : fresnelS q - fresnelS p = ∫ t in p..q, sinArg t := by
      rw [fresnelS, fresnelS, intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_sinArg 0 q) (intervalIntegrable_sinArg 0 p)]
    rw [hdiff]
    calc |∫ t in p..q, sinArg t| ≤ 3 / (Real.pi * p) := abs_integral_sinArg_le p q hp0 hpq
      _ ≤ 3 / (Real.pi * N) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          gcongr
  rcases le_total u v with h | h
  · exact key u v hu h
  · rw [abs_sub_comm]; exact key v u hv h

/-- **Convergence from a uniform Cauchy increment.** A real function `f` whose
increments past every threshold `N > 0` are bounded by `3/(π N)` converges at
`atTop` (completeness of `ℝ`). -/
-- no-dlmf: generic completeness/convergence lemma, no DLMF counterpart
theorem tendsto_of_increment_bound (f : ℝ → ℝ)
    (hbd : ∀ N u v : ℝ, 0 < N → N ≤ u → N ≤ v → |f v - f u| ≤ 3 / (Real.pi * N)) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hpi := Real.pi_pos
  rw [← cauchy_map_iff_exists_tendsto]
  rw [Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, ?_⟩
  intro ε hε
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℝ, 0 < N ∧ 3 / (Real.pi * N) < ε := by
    refine ⟨(4 / (Real.pi * ε)), by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have hNe : Real.pi * (4 / (Real.pi * ε)) = 4 / ε := by
      field_simp
    rw [hNe, mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt hε), mul_one]
    norm_num
  refine ⟨f '' (Set.Ici N), ?_, ?_⟩
  · rw [Filter.mem_map]
    apply Filter.mem_of_superset (Filter.Ici_mem_atTop N)
    intro x hx
    exact ⟨x, hx, rfl⟩
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [Real.dist_eq]
    calc |f u - f v| ≤ 3 / (Real.pi * N) := hbd N v u hN1 hv hu
      _ < ε := hN2

-- no-dlmf: mere-existence convergence lemma (no limit value asserted); the
-- DLMF 7.2.9 result `lim C(x) = 1/2` is proved below as `tendsto_fresnelC`
/-- **The Fresnel cosine integral converges at `+∞`** (to some real limit). The
classical value of that limit is `1/2` (DLMF 7.2.9); identifying it is the
Abelian-bridge frontier described in the module header.

DLMF 7.2.9.
-/
theorem exists_tendsto_fresnelC : ∃ L : ℝ, Tendsto fresnelC atTop (𝓝 L) :=
  tendsto_of_increment_bound fresnelC fresnelC_increment_bound

-- no-dlmf: mere-existence convergence lemma (no limit value asserted); the
-- DLMF 7.2.9 result `lim S(x) = 1/2` is proved below as `tendsto_fresnelS`
/-- **The Fresnel sine integral converges at `+∞`** (to some real limit). The
classical value is `1/2` (DLMF 7.2.9).

DLMF 7.2.9.
-/
theorem exists_tendsto_fresnelS : ∃ L : ℝ, Tendsto fresnelS atTop (𝓝 L) :=
  tendsto_of_increment_bound fresnelS fresnelS_increment_bound

/-- **The full-line Abel value of the Fresnel Gaussian** with the DLMF phase
`a = π/2`: `(π/(π/2) · i)^{1/2} = (2i)^{1/2} = 1 + i`. Combined with
`FLMF.Methods.StationaryPhase.fresnel_regularized (π/2)`, this says
`lim_{ε↓0} ∫_ℝ e^{-(ε - i(π/2))x²} dx = 1 + i`; on the half line `(0,∞)` the
value is `(1+i)/2`, whose real and imaginary parts `1/2` are the conjectured
limits of `C` and `S`. -/
-- no-dlmf: Abel-value/Gaussian-regularization step, no DLMF counterpart
theorem abel_value_eq :
    ((((Real.pi / (Real.pi / 2) : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ)) = 1 + Complex.I := by
  have hr : (Real.pi / (Real.pi / 2) : ℝ) = 2 := by field_simp
  rw [hr, FLMF.Methods.StationaryPhase.cpow_half_pos_mul_I 2 (by norm_num),
    mul_comm Complex.I ((Real.pi / 4 : ℝ) : ℂ), Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four, mul_add,
    show (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ)
        = (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2) from by push_cast; ring,
    show (Real.sqrt 2 : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I)
        = ((Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2)) * Complex.I from by push_cast; ring]
  have h2' : (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2) = 1 := by
    have hr2 : (Real.sqrt 2 : ℝ) * ((Real.sqrt 2 : ℝ) / 2) = 1 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    calc (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2)
        = (((Real.sqrt 2 : ℝ) * ((Real.sqrt 2 : ℝ) / 2) : ℝ) : ℂ) := by push_cast; ring
      _ = 1 := by rw [hr2]; norm_num
  rw [h2', one_mul]

/-- The real part of the Fresnel Gaussian integrand (DLMF phase `a = π/2`) is the
Gaussian-damped cosine: `Re e^{-((ε - i(π/2))x²)} = e^{-εx²}·cos(πx²/2)`. -/
-- no-dlmf: real-part helper for the Gaussian-regularization step, no DLMF counterpart
theorem cgauss_re (ε x : ℝ) :
    (Complex.exp (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re
      = Real.exp (-ε * x ^ 2) * cosArg x := by
  rw [cosArg, Complex.exp_re]
  have hre : (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2).re
      = -ε * x ^ 2 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, pow_two]
  have him : (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2).im
      = Real.pi * x ^ 2 / 2 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, pow_two]; ring
  rw [hre, him]

/-- The imaginary part of the Fresnel Gaussian integrand (DLMF phase `a = π/2`) is
the Gaussian-damped sine: `Im e^{-((ε - i(π/2))x²)} = e^{-εx²}·sin(πx²/2)`. -/
-- no-dlmf: imaginary-part helper for the Gaussian-regularization step, no DLMF counterpart
theorem cgauss_im (ε x : ℝ) :
    (Complex.exp (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im
      = Real.exp (-ε * x ^ 2) * sinArg x := by
  rw [sinArg, Complex.exp_im]
  have hre : (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2).re
      = -ε * x ^ 2 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, pow_two]
  have him : (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2).im
      = Real.pi * x ^ 2 / 2 := by
    simp [Complex.sub_re, Complex.mul_re, Complex.mul_im, pow_two]; ring
  rw [hre, him]

-- no-dlmf: chain link 7.2.9 (assembled in `fresnel_7_2_9`) — DLMF 7.2.9 is an
-- equation group asserting BOTH `lim C(x) = 1/2` and `lim S(x) = 1/2`; this is
-- the `C` limb alone.
/-- **The Fresnel cosine integral tends to `1/2` at `+∞`** (the `C` limb of DLMF 7.2.9).

Combines the convergence half (`exists_tendsto_fresnelC`) with the Abelian–Gaussian
bridge (`FLMF.Methods.AbelianGaussian.abelian_gaussian`) and the regularized
full-line Fresnel value (`FLMF.Methods.StationaryPhase.fresnel_regularized` at
`a = π/2`, `abel_value_eq`). Taking the real part of the regularized full-line
integral and using evenness identifies the half-line limit as `1/2`.
-/
theorem tendsto_fresnelC : Tendsto fresnelC atTop (𝓝 (1 / 2)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_fresnelC
  have hAcos : Tendsto
      (fun ε : ℝ => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * cosArg t)
      (𝓝[>] 0) (𝓝 L) :=
    FLMF.Methods.AbelianGaussian.abelian_gaussian cosArg L continuous_cosArg
      (fun t => Real.abs_cos_le_one _) hL
  have hComplex := FLMF.Methods.StationaryPhase.fresnel_regularized (Real.pi / 2)
    (show (0:ℝ) < Real.pi / 2 by positivity).ne'
  rw [abel_value_eq] at hComplex
  have hRe : Tendsto (fun ε : ℝ =>
      (∫ x : ℝ, Complex.exp
        (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have := (Complex.continuous_re.continuousAt.tendsto).comp hComplex
    simpa using this
  have hEq : ∀ ε : ℝ, 0 < ε →
      (∫ x : ℝ, Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re
        = 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * cosArg t := by
    intro ε hε
    have hb : (0 : ℝ) < ((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)).re := by
      simp [Complex.sub_re, Complex.mul_re]; exact hε
    have hint : Integrable (fun x : ℝ =>
        Complex.exp (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)) :=
      integrable_cexp_neg_mul_sq hb
    have hre_comm : (∫ x : ℝ, Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re
        = ∫ x : ℝ, (Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re := by
      simpa using (integral_re hint).symm
    rw [hre_comm]
    have hcongr : (fun x : ℝ =>
        (Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).re)
        = fun x : ℝ => Real.exp (-ε * x ^ 2) * cosArg x := by
      funext x; exact cgauss_re ε x
    rw [hcongr]
    have hgeven : ∀ x : ℝ, Real.exp (-ε * x ^ 2) * cosArg x
        = (fun y : ℝ => Real.exp (-ε * y ^ 2) * cosArg y) |x| := by
      intro x; simp only [cosArg, sq_abs]
    rw [show (∫ x : ℝ, Real.exp (-ε * x ^ 2) * cosArg x)
          = ∫ x : ℝ, (fun y : ℝ => Real.exp (-ε * y ^ 2) * cosArg y) |x|
        from integral_congr_ae (Filter.Eventually.of_forall hgeven)]
    exact integral_comp_abs (f := fun y : ℝ => Real.exp (-ε * y ^ 2) * cosArg y)
  have h2Ioi : Tendsto
      (fun ε : ℝ => 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * cosArg t)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    refine hRe.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hEq ε hε
  have hIoiHalf : Tendsto
      (fun ε : ℝ => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * cosArg t)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have := h2Ioi.const_mul (1 / 2 : ℝ); simpa using this
  have hLval : L = 1 / 2 := tendsto_nhds_unique hAcos hIoiHalf
  rwa [hLval] at hL

-- no-dlmf: chain link 7.2.9 (assembled in `fresnel_7_2_9`) — the `S` limb alone
-- of the two-equation group DLMF 7.2.9.
/-- **The Fresnel sine integral tends to `1/2` at `+∞`** (the `S` limb of DLMF 7.2.9).

The sine analogue of `tendsto_fresnelC`: take the *imaginary* part of the
regularized full-line Fresnel value (`abel_value_eq`).
-/
theorem tendsto_fresnelS : Tendsto fresnelS atTop (𝓝 (1 / 2)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_fresnelS
  have hAsin : Tendsto
      (fun ε : ℝ => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * sinArg t)
      (𝓝[>] 0) (𝓝 L) :=
    FLMF.Methods.AbelianGaussian.abelian_gaussian sinArg L continuous_sinArg
      (fun t => Real.abs_sin_le_one _) hL
  have hComplex := FLMF.Methods.StationaryPhase.fresnel_regularized (Real.pi / 2)
    (show (0:ℝ) < Real.pi / 2 by positivity).ne'
  rw [abel_value_eq] at hComplex
  have hIm : Tendsto (fun ε : ℝ =>
      (∫ x : ℝ, Complex.exp
        (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have := (Complex.continuous_im.continuousAt.tendsto).comp hComplex
    simpa using this
  have hEq : ∀ ε : ℝ, 0 < ε →
      (∫ x : ℝ, Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im
        = 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * sinArg t := by
    intro ε hε
    have hb : (0 : ℝ) < ((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)).re := by
      simp [Complex.sub_re, Complex.mul_re]; exact hε
    have hint : Integrable (fun x : ℝ =>
        Complex.exp (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)) :=
      integrable_cexp_neg_mul_sq hb
    have him_comm : (∫ x : ℝ, Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im
        = ∫ x : ℝ, (Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im := by
      simpa using (integral_im hint).symm
    rw [him_comm]
    have hcongr : (fun x : ℝ =>
        (Complex.exp
          (-((ε : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * (x : ℂ) ^ 2)).im)
        = fun x : ℝ => Real.exp (-ε * x ^ 2) * sinArg x := by
      funext x; exact cgauss_im ε x
    rw [hcongr]
    have hgeven : ∀ x : ℝ, Real.exp (-ε * x ^ 2) * sinArg x
        = (fun y : ℝ => Real.exp (-ε * y ^ 2) * sinArg y) |x| := by
      intro x; simp only [sinArg, sq_abs]
    rw [show (∫ x : ℝ, Real.exp (-ε * x ^ 2) * sinArg x)
          = ∫ x : ℝ, (fun y : ℝ => Real.exp (-ε * y ^ 2) * sinArg y) |x|
        from integral_congr_ae (Filter.Eventually.of_forall hgeven)]
    exact integral_comp_abs (f := fun y : ℝ => Real.exp (-ε * y ^ 2) * sinArg y)
  have h2Ioi : Tendsto
      (fun ε : ℝ => 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * sinArg t)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    refine hIm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hEq ε hε
  have hIoiHalf : Tendsto
      (fun ε : ℝ => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t ^ 2) * sinArg t)
      (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
    have := h2Ioi.const_mul (1 / 2 : ℝ); simpa using this
  have hLval : L = 1 / 2 := tendsto_nhds_unique hAsin hIoiHalf
  rwa [hLval] at hL

/-- **DLMF 7.2.9** — the limiting values of the Fresnel integrals at `+∞`:
`lim_{x→∞} C(x) = 1/2` and `lim_{x→∞} S(x) = 1/2`.  The tagged entry is an
equation group asserting both limits; this assembles the two limbs
`tendsto_fresnelC` and `tendsto_fresnelS`.

DLMF 7.2.9.
DAG: E-7.2.9.
Numerical: PASS
Verified: verified
-/
theorem fresnel_7_2_9 :
    Tendsto fresnelC atTop (𝓝 (1 / 2)) ∧ Tendsto fresnelS atTop (𝓝 (1 / 2)) :=
  ⟨tendsto_fresnelC, tendsto_fresnelS⟩

-- no-dlmf: derived IBP tail bound (uniform 3/(πx) estimate); §7.12 gives
-- Poincaré asymptotic expansions/remainder-integral formulas for erfc and the
-- Fresnel auxiliary functions f, g, not this closed-form numeric bound for `C`
/-- **Convergence rate of the Fresnel cosine integral** (DLMF §7.12). For `x > 0`,
`|C(x) - 1/2| ≤ 3/(π x)`: the oscillatory tail `∫_x^∞ cos(πt²/2)` equals
`1/2 - C(x)` and is bounded by `3/(π x)`.

DLMF 7.12.
-/
theorem fresnelC_dist_half_le (x : ℝ) (hx : 0 < x) :
    |fresnelC x - 1 / 2| ≤ 3 / (Real.pi * x) := by
  have htail : Tendsto (fun R => ∫ t in x..R, cosArg t) atTop (𝓝 (1 / 2 - fresnelC x)) := by
    refine (tendsto_fresnelC.sub_const (fresnelC x)).congr (fun R => ?_)
    rw [fresnelC, fresnelC, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_cosArg 0 R) (intervalIntegrable_cosArg 0 x)]
  have hbound : |1 / 2 - fresnelC x| ≤ 3 / (Real.pi * x) :=
    le_of_tendsto htail.abs (by
      filter_upwards [eventually_ge_atTop x] with R hR
      exact abs_integral_cosArg_le x R hx hR)
  rwa [abs_sub_comm] at hbound

-- no-dlmf: derived IBP tail bound (uniform 3/(πx) estimate); §7.12 gives
-- Poincaré asymptotic expansions/remainder-integral formulas for erfc and the
-- Fresnel auxiliary functions f, g, not this closed-form numeric bound for `S`
/-- **Convergence rate of the Fresnel sine integral** (DLMF §7.12). For `x > 0`,
`|S(x) - 1/2| ≤ 3/(π x)`.

DLMF 7.12.
-/
theorem fresnelS_dist_half_le (x : ℝ) (hx : 0 < x) :
    |fresnelS x - 1 / 2| ≤ 3 / (Real.pi * x) := by
  have htail : Tendsto (fun R => ∫ t in x..R, sinArg t) atTop (𝓝 (1 / 2 - fresnelS x)) := by
    refine (tendsto_fresnelS.sub_const (fresnelS x)).congr (fun R => ?_)
    rw [fresnelS, fresnelS, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_sinArg 0 R) (intervalIntegrable_sinArg 0 x)]
  have hbound : |1 / 2 - fresnelS x| ≤ 3 / (Real.pi * x) :=
    le_of_tendsto htail.abs (by
      filter_upwards [eventually_ge_atTop x] with R hR
      exact abs_integral_sinArg_le x R hx hR)
  rwa [abs_sub_comm] at hbound

/-- The second-order Fresnel tail `∫_x^R sin(πt²/2)/(πt²)` is bounded by `1/(πx)`. -/
-- no-dlmf: remainder tail bound for the leading asymptotic, no DLMF counterpart
private theorem abs_integral_sinArg_div_pi_sq_le (x R : ℝ) (hx : 0 < x) (hxR : x ≤ R) :
    |∫ t in x..R, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)| ≤ 1 / (Real.pi * x) := by
  have hpi := Real.pi_pos
  have htail_int : IntervalIntegrable
      (fun t => Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)) volume x R := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; rw [uIcc_of_le hxR] at ht
    have : (0:ℝ) < t := lt_of_lt_of_le hx ht.1; positivity
  have hinv_int : IntervalIntegrable (fun t => (Real.pi * t ^ 2)⁻¹) volume x R := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht; rw [uIcc_of_le hxR] at ht
    have : (0:ℝ) < t := lt_of_lt_of_le hx ht.1; positivity
  have hstep2 : (∫ t in x..R, |Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|)
      ≤ ∫ t in x..R, (Real.pi * t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hxR htail_int.abs hinv_int
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hx ht.1
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.pi * t ^ 2),
      div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * t ^ 2)]
    calc |Real.sin (Real.pi * t ^ 2 / 2)| ≤ 1 := Real.abs_sin_le_one _
      _ = (Real.pi * t ^ 2)⁻¹ * (Real.pi * t ^ 2) := by field_simp
  calc |∫ t in x..R, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)|
      ≤ ∫ t in x..R, |Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hxR
    _ ≤ ∫ t in x..R, (Real.pi * t ^ 2)⁻¹ := hstep2
    _ = (1 / x - 1 / R) / Real.pi := integral_inv_pi_sq x R hx hxR
    _ ≤ 1 / (Real.pi * x) := by
        have hR0 : 0 < R := lt_of_lt_of_le hx hxR
        have hpos : (0:ℝ) < 1 / R := by positivity
        rw [show 1 / (Real.pi * x) = (1 / x) / Real.pi from by field_simp]
        gcongr
        linarith

-- no-dlmf: derived IBP quantitative bound; DLMF 7.12.2 states the Poincaré
-- *asymptotic* series for the auxiliary function `f(z)`, not this closed-form
-- numeric error estimate for `C`
/-- **Sharper leading-order asymptotic of the Fresnel cosine integral**
(DLMF 7.12.2: the leading `1/(πx)` term of the auxiliary function `f(z)`, inserted
into the `C(z)` representation DLMF 7.5.3). For `x > 0`,
`|C(x) - (1/2 + sin(πx²/2)/(πx))| ≤ 1/(πx)`: the explicit oscillatory leading
term `sin(πx²/2)/(πx)` of `C(x) - 1/2`, remainder `∫_x^∞ sin(πt²/2)/(πt²)` bounded
by `1/(πx)`. Obtained by integrating the tail `∫_x^∞ cos(πt²/2)` by parts.

DLMF 7.12.2.
-/
theorem fresnelC_sub_leading_le (x : ℝ) (hx : 0 < x) :
    |fresnelC x - (1 / 2 + Real.sin (Real.pi * x ^ 2 / 2) / (Real.pi * x))| ≤ 1 / (Real.pi * x) := by
  set S : ℝ := Real.sin (Real.pi * x ^ 2 / 2) / (Real.pi * x) with hS
  have hsinR : Tendsto (fun R : ℝ => Real.sin (Real.pi * R ^ 2 / 2) / (Real.pi * R)) atTop (𝓝 0) := by
    have hg0 : Tendsto (fun R : ℝ => (Real.pi * R)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop Real.pi_pos tendsto_id)
      simpa only [Function.comp_def, id_eq] using h
    refine squeeze_zero_norm' ?_ hg0
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    have hpr : 0 < Real.pi * R := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpr, ← one_div]
    gcongr
    exact Real.abs_sin_le_one _
  have hcos_tail : Tendsto (fun R => ∫ t in x..R, cosArg t) atTop (𝓝 (1 / 2 - fresnelC x)) := by
    refine (tendsto_fresnelC.sub_const (fresnelC x)).congr (fun R => ?_)
    rw [fresnelC, fresnelC, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_cosArg 0 R) (intervalIntegrable_cosArg 0 x)]
  have heq : ∀ R, x ≤ R → (∫ t in x..R, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2))
      = (∫ t in x..R, cosArg t)
        - Real.sin (Real.pi * R ^ 2 / 2) / (Real.pi * R) + S := by
    intro R hR
    have h := integral_cosArg_eq x R hx hR
    rw [hS]; linarith
  have hdev : Tendsto (fun R => ∫ t in x..R, Real.sin (Real.pi * t ^ 2 / 2) / (Real.pi * t ^ 2))
      atTop (𝓝 ((1 / 2 - fresnelC x) - 0 + S)) := by
    refine (((hcos_tail.sub hsinR).add tendsto_const_nhds)).congr' ?_
    filter_upwards [eventually_ge_atTop x] with R hR
    exact (heq R hR).symm
  have hlimbound : |(1 / 2 - fresnelC x) - 0 + S| ≤ 1 / (Real.pi * x) :=
    le_of_tendsto hdev.abs (by
      filter_upwards [eventually_ge_atTop x] with R hR
      exact abs_integral_sinArg_div_pi_sq_le x R hx hR)
  rwa [show fresnelC x - (1 / 2 + S) = -((1 / 2 - fresnelC x) - 0 + S) from by ring, abs_neg]

end FLMF.Fresnel
