import Mathlib

/-!
# Dawson function `F(x)`

This module defines the Dawson integral
`F(x) = e^{-x^2} ∫_0^x e^{t^2} dt`
(DLMF 7.2) and proves some basic properties.
-/

namespace FLMF

open scoped Real
open intervalIntegral MeasureTheory

/-- The Dawson function `F(x) = e^{-x²} ∫₀ˣ e^{t²} dt` (DLMF 7.2).

DLMF 7.2.
-/
-- DAG: E-7.2.
-- Verified: unverified (tier2 DIVERGES)
noncomputable def dawson (x : ℝ) : ℝ :=
    Real.exp (-x ^ 2) * ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

-- no-dlmf: continuity of the integrand e^{t²}; analytic infrastructure, no DLMF identity
/-- The integrand `t ↦ e^{t²}` is continuous. -/
theorem continuous_exp_sq : Continuous fun t : ℝ => Real.exp (t ^ 2) :=
  Real.continuous_exp.comp (continuous_pow 2)

-- no-dlmf: interval-integrability of e^{t²}; analytic infrastructure, no DLMF identity
/-- The integrand `t ↦ e^{t²}` is interval-integrable on any interval. -/
theorem intervalIntegrable_exp_sq (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t ^ 2)) MeasureTheory.volume a b :=
  continuous_exp_sq.intervalIntegrable a b

-- no-dlmf: basic special value F(0)=0; no specific DLMF identity number
/-- `dawson 0 = 0`. -/
@[simp]
theorem dawson_zero : dawson 0 = 0 := by
  simp [dawson]

-- no-dlmf: oddness symmetry F(-x)=-F(x); basic parity, no specific DLMF identity number
/-- The Dawson function is odd: `F(-x) = -F(x)`. -/
theorem dawson_neg (x : ℝ) : dawson (-x) = -dawson x := by
  unfold dawson
  have heven : (∫ t in (0 : ℝ)..x, Real.exp ((-t) ^ 2))
      = ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2) := by
    simp
  have hcn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := x)
      (fun t => Real.exp (t ^ 2))
  -- hcn : ∫ t in 0..x, exp((-t)^2) = ∫ t in -x..0, exp(t^2)
  rw [heven] at hcn
  have hsym : (∫ t in (0 : ℝ)..(-x), Real.exp (t ^ 2))
      = -∫ t in (0 : ℝ)..x, Real.exp (t ^ 2) := by
    rw [hcn, intervalIntegral.integral_symm]
    simp
  rw [hsym]
  ring_nf

-- no-dlmf: continuity of F; analytic infrastructure, no DLMF identity
/-- The Dawson function is continuous. -/
theorem continuous_dawson : Continuous dawson := by
  unfold dawson
  refine (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))).mul ?_
  exact continuous_primitive (fun a b => intervalIntegrable_exp_sq a b) 0

-- no-dlmf: derivative of the inner primitive (FTC helper); analytic infrastructure, no DLMF identity
/-- The derivative of the inner integral `∫₀ˣ e^{t²} dt` is `e^{x²}`. -/
theorem hasDerivAt_integral_exp_sq (x : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)) (Real.exp (x ^ 2)) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact intervalIntegrable_exp_sq 0 x
  · exact continuous_exp_sq.stronglyMeasurableAtFilter _ _
  · exact continuous_exp_sq.continuousAt

-- no-dlmf: derived ODE consequence of the DLMF 7.2.5 definition (FTC + product
-- rule); §7.2 defines `F` but does not itself state this derivative identity
/-- The derivative of the Dawson function:
`F'(x) = 1 - 2 x F(x)` (DLMF 7.2).

DLMF 7.2.
-/
theorem hasDerivAt_dawson (x : ℝ) :
    HasDerivAt dawson (1 - 2 * x * dawson x) x := by
  have hexp : HasDerivAt (fun x => Real.exp (-x ^ 2)) (Real.exp (-x ^ 2) * (-(2 * x))) x := by
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := by
      have := (hasDerivAt_pow 2 x)
      simpa using this.neg
    simpa using (Real.hasDerivAt_exp (-x ^ 2)).comp x h1
  have hint := hasDerivAt_integral_exp_sq x
  have hres := hexp.mul hint
  have hone : Real.exp (-x ^ 2) * Real.exp (x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  convert hres using 1
  unfold dawson
  -- goal: 1 - 2 * x * (exp(-x²) * I) = exp(-x²)*(-(2x)) * I + exp(x²) * exp(-x²)
  set I := ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2) with hI
  have hone' : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [mul_comm]; exact hone
  nlinarith [hone, hone']

end FLMF
