import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.ErfcLeading
import FLMF.Functions.Error.ErfcSeries
import FLMF.Functions.Error.Dawson
import FLMF.Functions.Error.DawsonODE
import FLMF.Functions.Error.DawsonAsymptotic
import FLMF.Functions.Error.GoodwinStaton
import FLMF.Functions.Error.OwenT
import FLMF.Functions.Error.Voigt
import FLMF.Functions.Error.KummerBridge
import FLMF.Functions.Error.TricomiBridge
import FLMF.Functions.Error.RepeatedErfc
import FLMF.Functions.Error.ComplexErf
import FLMF.Functions.Error.Faddeeva
import FLMF.Functions.Error.ComplexErfExtra
import FLMF.Functions.Error.ComplexZeros
-- DLMF chapter-7 per-equation statement surfaces (Phase 5, surfaces-first)
import FLMF.Functions.Error.Ch7Definitions
import FLMF.Functions.Error.Ch7Symmetry
import FLMF.Functions.Error.Ch7Interrelations
import FLMF.Functions.Error.Ch7Series
import FLMF.Functions.Error.Ch7IntegralReps
import FLMF.Functions.Error.Ch7Inequalities
import FLMF.Functions.Error.Ch7ContinuedFractions
import FLMF.Functions.Error.Ch7Derivatives
import FLMF.Functions.Error.Ch7RelationsOther
import FLMF.Functions.Error.Ch7AsymptoticExpansions
import FLMF.Functions.Error.Ch7SectorExpansions
import FLMF.Functions.Error.Ch7Zeros
import FLMF.Functions.Error.Ch7LaplaceBridge
import FLMF.Functions.Error.Ch7LaplaceConvolutionBridge
import FLMF.Functions.Error.Ch7Integrals
import FLMF.Functions.Error.Ch7InverseErf
import FLMF.Functions.Error.Ch7InverseErfExpansion
import FLMF.Functions.Error.Ch7RepeatedErfc
import FLMF.Functions.Error.ComplexRepeatedErfc
import FLMF.Functions.Error.ComplexTricomi
import FLMF.Functions.Error.ComplexErfcFraction
import FLMF.Functions.Error.Ch7VoigtExtra
import FLMF.Functions.Error.Ch7Applications
/-!
# Error functions, Dawson's and Fresnel integrals (chapter — cf. DLMF §7)

erf, erfc, the Dawson function, and the Fresnel integrals C, S — integral and
series definitions, the reflection `erf(-x) = -erf(x)`, derivatives, and the
large-argument asymptotic `erfc(x) ∼ e^{-x²}/(x√π)`.

**Framework:** bridges to `Frameworks.Hypergeometric` (`₁F₁`).
**Mathlib:** the Gaussian integral `∫ e^{-x²} = √π` is upstream; reuse via
`Bridges.Mathlib`. Fresnel asymptotics use `Methods.StationaryPhase`; erfc uses
`Methods.Watson`.

**Status:** ⬜ gap (Gaussian groundwork exists in the prototype's `Gaussian`).
-/
