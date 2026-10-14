import Mathlib

section

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
-- Verified: unverified
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

end

section

/-!
# Leading asymptotic of the Dawson function

We prove `F(x) ~ 1/(2x)` as `x → ∞`, in the precise form

`Tendsto (fun x => 2 * x * dawson x) atTop (𝓝 1)`   (DLMF 7.12).
-/

namespace FLMF

open scoped Real
open intervalIntegral MeasureTheory Filter Topology

-- no-dlmf: abbreviation for the inner primitive; analytic infrastructure, no DLMF identity
/-- Inner integral `I(x) = ∫₀ˣ e^{t²} dt`. -/
noncomputable def dawsonInt (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

-- no-dlmf: definitional rewrite of dawson; analytic infrastructure, no DLMF identity
theorem dawson_eq (x : ℝ) : dawson x = Real.exp (-x ^ 2) * dawsonInt x := rfl

-- no-dlmf: derivative helper for the asymptotic proof; analytic infrastructure, no DLMF identity
/-- Derivative of `t ↦ e^{t²}/(2t)` at `t ≠ 0` is `e^{t²}(1 - 1/(2t²))`. -/
theorem hasDerivAt_aux (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2) / (2 * t))
      (Real.exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) t := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (Real.exp (t ^ 2) * (2 * t)) t := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    simpa [mul_comm] using (Real.hasDerivAt_exp (t ^ 2)).comp t h1
  have hden : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ))
  have hne : (2 * t) ≠ 0 := mul_ne_zero two_ne_zero ht
  have hd := hexp.div hden hne
  convert hd using 1
  field_simp

end FLMF

end

section

/-!
# Dawson ODE `F'(x) = 1 - 2 x F(x)`

The Dawson function `F` (defined in `FLMF.Functions.Error.Dawson`) satisfies the
first-order linear ODE
`F'(x) = 1 - 2 x F(x)`  (DLMF 7.2).

This module packages that fact in `deriv` form and records differentiability.
-/

namespace FLMF

open scoped Real

-- no-dlmf: differentiability of F; analytic infrastructure, no DLMF identity
/-- The Dawson function is differentiable everywhere. -/
theorem differentiable_dawson : Differentiable ℝ dawson := fun x =>
  (hasDerivAt_dawson x).differentiableAt

-- no-dlmf: derived ODE consequence of the DLMF 7.2.5 definition (via
-- `hasDerivAt_dawson`); §7.2 defines `F` but does not itself state this identity
/-- The Dawson ODE in `deriv` form: `F'(x) = 1 - 2 x F(x)` (DLMF 7.2).

DLMF 7.2.
-/
theorem deriv_dawson (x : ℝ) : deriv dawson x = 1 - 2 * x * dawson x :=
  (hasDerivAt_dawson x).deriv

-- no-dlmf: derived ODE consequence of the DLMF 7.2.5 definition (funext of
-- `deriv_dawson`); §7.2 defines `F` but does not itself state this identity
/-- The Dawson ODE as a global identity of functions:
`F' = fun x => 1 - 2 x F(x)` (DLMF 7.2).

DLMF 7.2.
-/
theorem deriv_dawson_eq : deriv dawson = fun x => 1 - 2 * x * dawson x :=
  funext deriv_dawson

end FLMF

end
