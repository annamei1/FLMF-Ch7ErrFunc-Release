import FLMF.Frameworks.Hypergeometric.Ch15AsymptoticApproximations
import FLMF.Functions.ParabolicCylinder.Basic

/-!
# Parabolic cylinder `U` — real/complex bridge (DLMF §12.2 ↔ §15.12)

The Frameworks layer (`Ch15AsymptoticApproximations`) defines the complex
comparison function `complexParabolicCylinderU` from scratch, because the layer
order Methods → Frameworks → Functions forbids it from importing the Functions
layer.  This file closes the duplication downward: the Functions-layer real
`U(a,x)` (DLMF 12.2.6–7 via the even/odd Kummer basis, `Basic.lean`) is the
restriction of the Frameworks-layer complex comparison function to real
arguments.

The two definitions are term-for-term the same formula; the proof pushes the
`ℝ → ℂ` cast through `exp`, `Γ`, real `rpow` → complex `cpow` (base `2 > 0`),
and the Kummer sum (`kummerM_ofReal`).  Note the sign convention: the real `U`
writes `+ (−C₂)·w₂` where the complex definition writes `− C₂·odd` — the same
value.
-/

open FLMF.Hypergeometric

namespace FLMF.ParabolicCylinder

-- no-dlmf: real↔complex scalar-tower bridge between the Functions-layer `U`
-- and the Frameworks-layer comparison function, no DLMF counterpart
/-- The real parabolic cylinder function `U(a,x)` (DLMF 12.2.6–7) is the
restriction to real arguments of the complex comparison function
`complexParabolicCylinderU` of DLMF §15.12. -/
theorem U_ofReal (a x : ℝ) :
    ((U a x : ℝ) : ℂ) = complexParabolicCylinderU (a : ℂ) (x : ℂ) := by
  unfold U complexParabolicCylinderU pcfEven pcfOdd
  push_cast [← Complex.Gamma_ofReal, Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2),
    kummerM_ofReal, Complex.ofReal_exp]
  ring

end FLMF.ParabolicCylinder
