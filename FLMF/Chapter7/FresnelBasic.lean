import Mathlib

/-!
# Fresnel integrals `C(x)` and `S(x)`

This module defines the Fresnel integrals in the normalized form used by the DLMF
(DLMF 7.2.7):
$$C(x) = \int_0^x \cos\!\left(\tfrac{\pi t^2}{2}\right)\,dt, \qquad
  S(x) = \int_0^x \sin\!\left(\tfrac{\pi t^2}{2}\right)\,dt.$$

We provide:
* the definitions `fresnelC`, `fresnelS`;
* continuity of the integrands;
* their interval integrability on any `0..x`;
* the values at `0`;
* the derivatives via the fundamental theorem of calculus.
-/

namespace FLMF.Fresnel

open scoped Real
open intervalIntegral MeasureTheory

/-- The Fresnel integrand for `C`: `t ↦ cos(π t² / 2)`. -/
-- no-dlmf: integrand helper for the C(x) integral; the identity is on fresnelC
noncomputable def cosArg (t : ℝ) : ℝ := Real.cos (Real.pi * t ^ 2 / 2)

/-- The Fresnel integrand for `S`: `t ↦ sin(π t² / 2)`. -/
-- no-dlmf: integrand helper for the S(x) integral; the identity is on fresnelS
noncomputable def sinArg (t : ℝ) : ℝ := Real.sin (Real.pi * t ^ 2 / 2)

-- no-dlmf: real/narrowed twin of DLMF 7.2.7; canonical surface is `cfresnelC` (Complex.lean)
/-- The Fresnel cosine integral `C(x) = ∫₀ˣ cos(π t² / 2) dt` (DLMF 7.2.7).

-/
noncomputable def fresnelC (x : ℝ) : ℝ := ∫ t in (0)..x, cosArg t

-- no-dlmf: real/narrowed twin of DLMF 7.2.8; canonical surface is `cfresnelS` (Complex.lean)
/-- The Fresnel sine integral `S(x) = ∫₀ˣ sin(π t² / 2) dt` (DLMF 7.2.8).

-/
noncomputable def fresnelS (x : ℝ) : ℝ := ∫ t in (0)..x, sinArg t

/-- The argument map `t ↦ π t² / 2` is continuous. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem continuous_phase : Continuous fun t : ℝ => Real.pi * t ^ 2 / 2 := by
  fun_prop

/-- The Fresnel cosine integrand is continuous. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem continuous_cosArg : Continuous cosArg :=
  Real.continuous_cos.comp continuous_phase

/-- The Fresnel sine integrand is continuous. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem continuous_sinArg : Continuous sinArg :=
  Real.continuous_sin.comp continuous_phase

/-- The Fresnel cosine integrand is interval integrable on any `a..b`. -/
-- no-dlmf: integrability helper, no DLMF counterpart
theorem intervalIntegrable_cosArg (a b : ℝ) :
    IntervalIntegrable cosArg volume a b :=
  continuous_cosArg.intervalIntegrable a b

/-- The Fresnel sine integrand is interval integrable on any `a..b`. -/
-- no-dlmf: integrability helper, no DLMF counterpart
theorem intervalIntegrable_sinArg (a b : ℝ) :
    IntervalIntegrable sinArg volume a b :=
  continuous_sinArg.intervalIntegrable a b

/-- `C(0) = 0`. -/
-- no-dlmf: trivial value at 0 from the integral def, not a numbered DLMF identity
@[simp] theorem fresnelC_zero : fresnelC 0 = 0 := by
  simp [fresnelC, integral_same]

/-- `S(0) = 0`. -/
-- no-dlmf: trivial value at 0 from the integral def, not a numbered DLMF identity
@[simp] theorem fresnelS_zero : fresnelS 0 = 0 := by
  simp [fresnelS, integral_same]

/-- **Fundamental theorem of calculus** for `C`:
the derivative of `C` at `x` is `cos(π x² / 2)`. -/
-- no-dlmf: FTC for the integral def (integrand of 7.2.7), not a numbered DLMF identity
theorem hasDerivAt_fresnelC (x : ℝ) :
    HasDerivAt fresnelC (cosArg x) x :=
  integral_hasDerivAt_right (intervalIntegrable_cosArg 0 x)
    continuous_cosArg.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_cosArg.continuousAt

/-- **Fundamental theorem of calculus** for `S`:
the derivative of `S` at `x` is `sin(π x² / 2)`. -/
-- no-dlmf: FTC for the integral def (integrand of 7.2.8), not a numbered DLMF identity
theorem hasDerivAt_fresnelS (x : ℝ) :
    HasDerivAt fresnelS (sinArg x) x :=
  integral_hasDerivAt_right (intervalIntegrable_sinArg 0 x)
    continuous_sinArg.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_sinArg.continuousAt

/-- The derivative of `C` at `x` equals `cos(π x² / 2)`. -/
-- no-dlmf: derivative from the integral def (integrand of 7.2.7), not a numbered DLMF identity
theorem deriv_fresnelC (x : ℝ) :
    deriv fresnelC x = Real.cos (Real.pi * x ^ 2 / 2) :=
  (hasDerivAt_fresnelC x).deriv

/-- The derivative of `S` at `x` equals `sin(π x² / 2)`. -/
-- no-dlmf: derivative from the integral def (integrand of 7.2.8), not a numbered DLMF identity
theorem deriv_fresnelS (x : ℝ) :
    deriv fresnelS x = Real.sin (Real.pi * x ^ 2 / 2) :=
  (hasDerivAt_fresnelS x).deriv

/-- `C` is differentiable everywhere. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem differentiable_fresnelC : Differentiable ℝ fresnelC :=
  fun x => (hasDerivAt_fresnelC x).differentiableAt

/-- `S` is differentiable everywhere. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem differentiable_fresnelS : Differentiable ℝ fresnelS :=
  fun x => (hasDerivAt_fresnelS x).differentiableAt

/-- `C` is continuous. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem continuous_fresnelC : Continuous fresnelC :=
  differentiable_fresnelC.continuous

/-- `S` is continuous. -/
-- no-dlmf: regularity helper, no DLMF counterpart
theorem continuous_fresnelS : Continuous fresnelS :=
  differentiable_fresnelS.continuous

end FLMF.Fresnel
