import FLMF.Functions.Error.Dawson

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
