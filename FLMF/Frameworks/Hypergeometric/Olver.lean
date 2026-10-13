import Mathlib.Analysis.Analytic.OfScalars
import FLMF.Frameworks.Hypergeometric.Pochhammer

/-!
# Olver's scaled Gauss hypergeometric function (DLMF §15.2)

Olver's scaled hypergeometric function is defined on the unit disc by

`𝐅(a,b;c;z) = ∑ n, (a)ₙ (b)ₙ / (Γ(c+n) n!) · zⁿ`.

Unlike the quotient `₂F₁(a,b;c;z) / Γ(c)`, this defining series remains
meaningful when `c` is a nonpositive integer: reciprocal Gamma vanishes at its
poles, so the affected initial coefficients are zero. As with Mathlib's
`ordinaryHypergeometric`, the `FormalMultilinearSeries.sum` realization has the
standard junk value `0` outside its radius of convergence; analytic continuation
beyond the defining disc is separate infrastructure.
-/

open Nat FormalMultilinearSeries

namespace FLMF.Hypergeometric

/-- The coefficient `(a)ₙ(b)ₙ / (Γ(c+n)n!)` in Olver's scaled Gauss series.

DLMF 15.2.2.
DAG: E-15.2.2.
-/
-- Verified: unverified (tier2 DIVERGES)
noncomputable abbrev olverHypergeometricCoefficient (a b c : ℂ) (n : ℕ) : ℂ :=
  (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
    (Complex.Gamma (c + n))⁻¹

/-- The formal power series for Olver's scaled Gauss hypergeometric function.

DLMF 15.2.2.
DAG: E-15.2.2.
-/
-- Verified: unverified (tier2 DIVERGES)
noncomputable def olverHypergeometricSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ofScalars ℂ (olverHypergeometricCoefficient a b c)

/-- Olver's scaled Gauss hypergeometric function, defined as the sum of its
gamma-denominator series. The series definition is valid for every `c`, including
nonpositive integers.

The §15.1 notation display DLMF 15.1.2, which introduces Olver's bold-`F`
symbol via `𝐅(a,b;c;z) = F(a,b;c;z)/Γ(c)`, is surfaced by this definition —
the relation itself is the proposition 15.2.2, and the display's only content
beyond it is the symbol.

DLMF 15.2.2.
DLMF 15.1.2.
DAG: E-15.2.2.
-/
-- Verified: verified (tier2)
-- Scope: this is the 15.2.2 series on its disc `‖z‖ < 1`; the value 0 outside
-- the disc is Lean's series totalization junk, not DLMF's analytic
-- continuation — that continuation is `principalOlver`.
noncomputable def olverHypergeometric (a b c z : ℂ) : ℂ :=
  (olverHypergeometricSeries a b c).sum z

end FLMF.Hypergeometric
