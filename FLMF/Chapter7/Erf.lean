import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Error functions `erf` and `erfc` (DLMF §7.2)

We define the error function
`erf(x) = (2/√π) ∫_0^x e^{-t²} dt`
and the complementary error function `erfc(x) = 1 - erf(x)`, reusing Mathlib's
Gaussian-integral groundwork.

Main results:

* `FLMF.Error.erf_zero` : `erf 0 = 0`.
* `FLMF.Error.continuous_erf` : `erf` is continuous.
* `FLMF.Error.erfc_zero` : `erfc 0 = 1`.
* `FLMF.Error.erf_tendsto_one` : `erf x → 1` as `x → ∞`.
* `FLMF.Error.erfc_tendsto_zero` : `erfc x → 0` as `x → ∞`.
-/

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set intervalIntegral

-- no-dlmf: real/narrowed twin of DLMF 7.2.1; canonical surface is `cerf` (ComplexErf.lean)
/-- The error function `erf(x) = (2/√π) ∫_0^x e^{-t²} dt` (DLMF 7.2.1).

-/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0)..x, Real.exp (-t ^ 2)

-- no-dlmf: real/narrowed twin of DLMF 7.2.2; canonical surface is `cerfc` (ComplexErf.lean)
/-- The complementary error function `erfc(x) = 1 - erf(x)` (DLMF 7.2.2).

-/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

-- no-dlmf: continuity of the Gaussian integrand; analytic infrastructure, no DLMF identity
/-- `t ↦ e^{-t²}` is continuous. -/
theorem continuous_gaussian : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) := by
  fun_prop

-- no-dlmf: interval-integrability of the Gaussian; analytic infrastructure, no DLMF identity
/-- `t ↦ e^{-t²}` is interval-integrable on every interval. -/
theorem intervalIntegrable_gaussian (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t ^ 2)) MeasureTheory.volume a b :=
  continuous_gaussian.intervalIntegrable a b

-- no-dlmf: basic special value erf(0)=0; no specific DLMF identity number
@[simp]
theorem erf_zero : erf 0 = 0 := by
  simp [erf]

-- no-dlmf: basic special value erfc(0)=1; no specific DLMF identity number
@[simp]
theorem erfc_zero : erfc 0 = 1 := by
  simp [erfc]

-- no-dlmf: continuity of erf; analytic infrastructure, no DLMF identity
/-- `erf` is continuous. -/
theorem continuous_erf : Continuous erf := by
  unfold erf
  refine continuous_const.mul ?_
  -- `x ↦ ∫_0^x f` is continuous when `f` is interval integrable on all intervals.
  exact continuous_primitive (fun a b => intervalIntegrable_gaussian a b) 0

-- no-dlmf: continuity of erfc; analytic infrastructure, no DLMF identity
/-- `erfc` is continuous. -/
theorem continuous_erfc : Continuous erfc := by
  unfold erfc
  exact continuous_const.sub continuous_erf

-- no-dlmf: half-line Gaussian integral (Mathlib groundwork); analytic infrastructure, no DLMF identity
/-- The half-line Gaussian integral: `∫_{(0,∞)} e^{-t²} = √π / 2`. -/
theorem integral_Ioi_gaussian :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi 1
  simp only [div_one] at h
  simpa using h

-- no-dlmf: convergence of the Gaussian primitive; analytic infrastructure, no DLMF identity
/-- The interval integral `∫_0^x e^{-t²}` tends to `√π/2` as `x → ∞`. -/
theorem tendsto_intervalIntegral_gaussian :
    Tendsto (fun x : ℝ => ∫ t in (0)..x, Real.exp (-t ^ 2)) atTop
      (𝓝 (Real.sqrt Real.pi / 2)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi 0) := by
    have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
    simpa [one_mul] using this.integrableOn
  have h := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [integral_Ioi_gaussian] at h
  exact h

-- no-dlmf: chain link 7.2.4 (assembled in `erf_7_2_4` below, alongside `erfc_tendsto_zero`)
/-- `erf x → 1` as `x → ∞` (the first limb of 7.2.4, real axis). -/
theorem erf_tendsto_one : Tendsto erf atTop (𝓝 1) := by
  unfold erf
  have hpi : Real.sqrt Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  have h := tendsto_intervalIntegral_gaussian.const_mul (2 / Real.sqrt Real.pi)
  have : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  rwa [this] at h

-- no-dlmf: chain link 7.2.4 (assembled in `erf_7_2_4` below, alongside `erf_tendsto_one`)
/-- `erfc x → 0` as `x → ∞` (the second limb of 7.2.4, real axis). -/
theorem erfc_tendsto_zero : Tendsto erfc atTop (𝓝 0) := by
  unfold erfc
  have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub erf_tendsto_one
  simpa using h

-- no-dlmf: real-axis (ph z = 0) instance of DLMF 7.2.4; the canonical carrier is
-- cerf_7_2_4 (Error/Ch7SectorExpansions.lean)
/-- The limiting values of the real error functions at `+∞`: `lim_{x→∞} erf x = 1` and
`lim_{x→∞} erfc x = 0`. This is the real-axis (`ph z = 0`) instance of 7.2.4, whose
display is a sector statement (`|ph z| ≤ π/4 − δ`) carried by `cerf_7_2_4`; it assembles
the two limbs `erf_tendsto_one` and `erfc_tendsto_zero`.
-/
theorem erf_7_2_4 :
    Tendsto erf atTop (𝓝 1) ∧ Tendsto erfc atTop (𝓝 0) :=
  ⟨erf_tendsto_one, erfc_tendsto_zero⟩

-- no-dlmf: first-derivative of erf via FTC; analytic infrastructure (used by 7.14.3), no
-- distinct DLMF identity number (7.10.1 is the general (n+1)-th derivative, stated separately)
/-- `erf` has derivative `(2/√π) e^{-x²}` at every `x : ℝ` (FTC applied to the defining
Gaussian integral). -/
theorem hasDerivAt_erf (x : ℝ) :
    HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)) x := by
  unfold erf
  have hderiv : HasDerivAt (fun y : ℝ => ∫ t in (0)..y, Real.exp (-t ^ 2))
      (Real.exp (-x ^ 2)) x :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_gaussian 0 x)
      (continuous_gaussian.stronglyMeasurableAtFilter _ _)
      continuous_gaussian.continuousAt
  simpa using hderiv.const_mul (2 / Real.sqrt Real.pi)

-- no-dlmf: monotonicity of erf; analytic infrastructure (used by 7.14.3), no DLMF identity
/-- `erf` is monotone (its derivative `(2/√π) e^{-x²}` is nonnegative everywhere). -/
theorem monotone_erf : Monotone erf := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (hasDerivAt_erf x).differentiableAt
  · intro x
    rw [(hasDerivAt_erf x).deriv]
    positivity

-- no-dlmf: erf ≤ 1 bound (used by 7.14.3), no DLMF identity number
/-- `erf x ≤ 1` for every `x : ℝ` (monotone limit `erf → 1`). -/
theorem erf_le_one (x : ℝ) : erf x ≤ 1 :=
  monotone_erf.ge_of_tendsto erf_tendsto_one x

-- no-dlmf: erf ≥ 0 bound for x ≥ 0 (used by 7.14.3), no DLMF identity number
/-- `erf x ≥ 0` for `x ≥ 0` (monotone, `erf 0 = 0`). -/
theorem erf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ erf x := by
  have := monotone_erf hx
  rwa [erf_zero] at this

/-- **Tail Gaussian integral via `erfc`.** For `a > 0` and any real `x`,
`∫_{x}^{∞} e^{-a t²} dt = (√(π/a)/2) · erfc(√a · x)`.

Proved by splitting the tail at `0` against the half-line Gaussian integral
(`integral_Ioi_gaussian`) for the `a = 1` case, then rescaling by `u = √a · t`
(`MeasureTheory.integral_comp_mul_left_Ioi`). -/
theorem integral_Ioi_gaussian_scaled_erfc {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ t in Set.Ioi x, Real.exp (-a * t ^ 2)
      = (Real.sqrt (Real.pi / a) / 2) * erfc (Real.sqrt a * x) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  -- Step 1: the `a = 1` case, for every real endpoint `y`.
  have hbase : ∀ y : ℝ, ∫ t in Set.Ioi y, Real.exp (-t ^ 2)
      = (Real.sqrt Real.pi / 2) * erfc y := by
    intro y
    have hint0 : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi (0 : ℝ)) := by
      have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
      simpa [one_mul] using this.integrableOn
    have hinty : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi y) := by
      have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
      simpa [one_mul] using this.integrableOn
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi' hint0 hinty
    rw [integral_Ioi_gaussian] at hsplit
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hrhs : (Real.sqrt Real.pi / 2) * erfc y
        = Real.sqrt Real.pi / 2 - ∫ t in (0 : ℝ)..y, Real.exp (-t ^ 2) := by
      unfold erfc erf
      field_simp
    rw [hrhs]
    linarith [hsplit]
  -- Step 2: rescale `u = √a · t`.
  have hcomp : ∀ t : ℝ, Real.exp (-a * t ^ 2)
      = Real.exp (-(Real.sqrt a * t) ^ 2) := by
    intro t
    rw [mul_pow, Real.sq_sqrt ha.le]
    ring_nf
  calc ∫ t in Set.Ioi x, Real.exp (-a * t ^ 2)
      = ∫ t in Set.Ioi x, Real.exp (-(Real.sqrt a * t) ^ 2) := by
        simp_rw [hcomp]
    _ = (Real.sqrt a)⁻¹ • ∫ u in Set.Ioi (Real.sqrt a * x), Real.exp (-u ^ 2) :=
        MeasureTheory.integral_comp_mul_left_Ioi (fun u => Real.exp (-u ^ 2)) x hsa
    _ = (Real.sqrt a)⁻¹ * ((Real.sqrt Real.pi / 2) * erfc (Real.sqrt a * x)) := by
        rw [hbase (Real.sqrt a * x), smul_eq_mul]
    _ = (Real.sqrt (Real.pi / a) / 2) * erfc (Real.sqrt a * x) := by
        rw [Real.sqrt_div Real.pi_pos.le]
        field_simp

-- no-dlmf: real/narrowed restriction of DLMF 7.2.2; canonical surface is `cerfc` (ComplexErf.lean)
/-- **DLMF 7.2.2**: the complementary error function's tail-integral representation
and its complementary relation to `erf`, `erfc z = (2/√π) ∫_z^∞ e^{-t²} dt = 1 - erf z`.

-/
theorem erf_7_2_2 (z : ℝ) :
    erfc z = (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi z, Real.exp (-t ^ 2) ∧
    erfc z = 1 - erf z := by
  refine ⟨?_, rfl⟩
  have h := integral_Ioi_gaussian_scaled_erfc (a := 1) one_pos z
  simp only [neg_mul, one_mul, div_one, Real.sqrt_one] at h
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  rw [h]
  field_simp

-- no-dlmf: derivative of erfc via `erfc = 1 - erf` (DLMF 7.2.2) and
-- `hasDerivAt_erf`; analogous to `hasDerivAt_erf`'s own no-dlmf marker (7.10.1
-- is the general (n+1)-th derivative; the base derivative isn't independently
-- numbered, and 7.2.1 defines `erf`, not this derivative of `erfc`)
/-- Derivative of the complementary error function:
`erfc'(x) = -(2/√π) e^{-x²}` (from `erfc = 1 - erf` and DLMF 7.2.1).

DLMF 7.2.1.
-/
theorem hasDerivAt_erfc (x : ℝ) :
    HasDerivAt erfc (-((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))) x := by
  simpa [erfc] using (hasDerivAt_erf x).const_sub 1

end FLMF.Error
