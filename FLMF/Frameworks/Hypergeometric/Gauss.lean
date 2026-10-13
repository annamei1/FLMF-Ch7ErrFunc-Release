import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import FLMF.Frameworks.Hypergeometric.Pochhammer

/-!
# Gauss hypergeometric `₂F₁` (framework — DLMF §15.2)

`₂F₁(a,b;c;z) = ∑ (a)ₙ(b)ₙ/(c)ₙ · zⁿ/n!` on `|z| < 1` (DLMF 15.2.1), the parent
of Legendre, Jacobi/Gegenbauer/Chebyshev (via the Askey scheme), and the
complete elliptic integrals. **Mathlib already carries the full definition
layer** (`Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric`); FLMF
surfaces it here as the framework anchor rather than rebuilding it.

Surfaced (Mathlib):

* `ordinaryHypergeometric` (notation `₂F₁`) — the sum of the series
  `ordinaryHypergeometricSeries`, over any normed algebra.
* `ordinaryHypergeometricSeries_radius_eq_one` — **radius of convergence 1**
  for parameters off the nonpositive integers (DLMF 15.2.1's disc).
* `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂/₃` — terminating
  (polynomial) cases `a` or `b` or `c` a nonpositive integer.
* `ordinaryHypergeometric_zero` — `₂F₁(a,b;c;0) = 1`.
* `ordinaryHypergeometricSeries_eq_zero_iff`, `..._symm`, `..._eq_tsum` — the
  series calculus.

Added here: `gaussCoefficient_eq_Gamma_quotient` — the coefficient in gamma
form `(a)ₙ(b)ₙ/((c)ₙ n!) = Γ(a+n)Γ(b+n)Γ(c) / (Γ(a)Γ(b)Γ(c+n) n!)`
(DLMF 15.2.2's normalization, via `ascPochhammer_eval_eq_Gamma_div`), the
binding the Mellin–Barnes representation and the connection formulas use.

Euler's integral representation, the hypergeometric ODE, and the contiguous
relations are downstream nodes (`F-2F1-euler-integral`, `F-2F1-ode`,
`F-2F1-contiguous`).
-/

namespace FLMF.Hypergeometric

open Complex

-- no-dlmf: chain link 15.2.1 (assembled in hypergeometric_15_2_1)
/-- The Gauss series coefficient in gamma-quotient form (DLMF 15.2.1/15.2.2):
for parameters off the gamma poles,
`(a)ₙ(b)ₙ/((c)ₙ n!) = (Γ(a+n)/Γ(a)) · (Γ(b+n)/Γ(b)) / ((Γ(c+n)/Γ(c)) · n!)`.
-/
theorem gaussCoefficient_eq_Gamma_quotient (a b c : ℂ) (n : ℕ)
    (ha : ∀ m : ℕ, a ≠ -m) (hb : ∀ m : ℕ, b ≠ -m) (hc : ∀ m : ℕ, c ≠ -m) :
    ordinaryHypergeometricCoefficient a b c n =
      (n.factorial : ℂ)⁻¹ * (Gamma (a + n) / Gamma a) * (Gamma (b + n) / Gamma b) *
        (Gamma (c + n) / Gamma c)⁻¹ := by
  rw [ordinaryHypergeometricCoefficient, ascPochhammer_eval_eq_Gamma_div a n ha,
    ascPochhammer_eval_eq_Gamma_div b n hb, ascPochhammer_eval_eq_Gamma_div c n hc]

end FLMF.Hypergeometric
