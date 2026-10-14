import FLMF.Support.HypergeometricTricomi
import FLMF.Support.HypergeometricTricomiODE
import FLMF.Support.HypergeometricTricomiKummerEq
import FLMF.Support.HypergeometricTricomiAsymptotic

/-!
# Confluent hypergeometric functions — Tricomi `U` (chapter, DLMF §13)

The confluent hypergeometric function of the second kind `U(a,b,z)` (Tricomi's
function) is built in the hypergeometric framework
(`FLMF/Frameworks/Hypergeometric/Tricomi*.lean`) as the Laplace-type integral
(DLMF 13.4.4, for `a > 0`, `z > 0`)

$$ U(a,b,z) = \frac{1}{\Gamma(a)} \int_0^\infty e^{-z t}\, t^{a-1} (1+t)^{b-a-1}\, dt. $$

This chapter surfaces that development into the handbook spine and records an
elementary qualitative consequence.

## Framework results surfaced here (`FLMF.Hypergeometric`)

| DLMF | Result |
|---|---|
| 13.4.4 | `tricomiU` (the integral), `tricomiU_integrand_integrableOn` (convergence) |
| 13.4.4 | `tricomiU_nonneg`, `tricomiU_pos` (positivity for `a,z > 0`) |
| 13.3.22 | `tricomiU_deriv` : `U'(z) = -a·U(a+1,b+1,z)` (and `tricomiU_hasDerivAt`) |
| 13.3 | `tricomiU_contiguous` : a three-term contiguous relation |
| 13.2.1 | `tricomiU_kummerODE` : `z U'' + (b-z) U' - a U = 0` (Kummer's equation) |
| 13.7.3 | `tricomiU_asymptotic` : `U(a,b,z) ∼ z^{-a}` as `z → ∞` |

## Added here

* `tricomiU_deriv_neg`, `tricomiU_strictAntiOn` — `U(a,b,·)` is strictly decreasing
  on `(0,∞)` (immediate from `U' = -a U(a+1,b+1,·) < 0`).

## References
- DLMF §13: https://dlmf.nist.gov/13
-/

open Set FLMF.Hypergeometric

namespace FLMF.Functions.Confluent

export FLMF.Hypergeometric (tricomiIntegrand tricomiU tricomiU_integrand_integrableOn
  tricomiU_nonneg tricomiU_pos tricomiU_hasDerivAt tricomiU_deriv tricomiU_contiguous
  tricomiU_kummerODE tricomiU_asymptotic)

-- no-dlmf: qualitative monotonicity consequence (deriv < 0) of the derivative formula 13.3.22; not a DLMF equation itself
/-- The `z`-derivative of `U(a,b,z)` is strictly negative for `a > 0`, `z > 0`:
`U'(z) = -a·U(a+1,b+1,z) < 0` since `a > 0` and `U(a+1,b+1,z) > 0`. -/
theorem tricomiU_deriv_neg {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    deriv (fun z => tricomiU a b z) z < 0 := by
  rw [tricomiU_deriv ha hz]
  have hpos : 0 < tricomiU (a + 1) (b + 1) z := tricomiU_pos (by linarith) hz
  linarith [mul_pos ha hpos]

-- no-dlmf: monotonicity corollary of the 13.4.4 integral representation — no DLMF
-- display states it; the 13.4.4 carrier is the `tricomiU` definition itself
-- (Frameworks/Hypergeometric/Tricomi.lean). User-approved disposition 2026-07-29.
/-- **DLMF 13.4.4 consequence.** `U(a,b,·)` is strictly decreasing on `(0,∞)` for `a > 0`. -/
theorem tricomiU_strictAntiOn {a : ℝ} (ha : 0 < a) (b : ℝ) :
    StrictAntiOn (fun z => tricomiU a b z) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro z hz
    exact (tricomiU_hasDerivAt ha (mem_Ioi.mp hz)).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    exact tricomiU_deriv_neg ha (mem_Ioi.mp hz)

end FLMF.Functions.Confluent
