import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Exponential integrals `E₁` and `Ei` (DLMF §6.2)

We give the native Lebesgue-integral definitions of the two principal
exponential integrals.

* The exponential integral `E₁(x) = ∫_x^∞ e^{-t}/t dt` for `x > 0`,
  defined as a Lebesgue integral over the unbounded interval `Ioi x`.

* The exponential integral `Ei(x)`, defined (DLMF 6.2.5) by its own integrand
  `Ei(x) = ∫_{-∞}^x e^t/t dt`.  As a plain Lebesgue integral this is faithful for
  `x < 0` (the path avoids the pole at `t = 0`); for `x > 0` the genuine `Ei(x)` is
  the Cauchy *principal value*, which the bare Lebesgue integral does not compute
  (it diverges through `t = 0`, so Lean returns the junk value `0`).  A
  principal-value definition correct on `x > 0` is left to future work; see
  `ERRATA.md` (`ei-li-domain-overextension`).

The DLMF relation `Ei(-x) = -E₁(x)` (DLMF 6.2.6) is proved below
(`Ei_neg_eq_neg_E1`) as a genuine change-of-variables theorem rather than baked
into the definition.  These are bare definitions plus structural lemmas; the
asymptotic content lives in `FLMF.Functions.ExpIntegrals.E1Leading`.
-/

namespace FLMF.ExpIntegrals.Def

open MeasureTheory Real Set

/-- The integrand `t ↦ e^{-t}/t` of the exponential integral `E₁`. -/
-- no-dlmf: integrand helper for the E₁ definition; no standalone DLMF identity
noncomputable def e1Integrand (t : ℝ) : ℝ := Real.exp (-t) / t

/-- The exponential integral `E₁(x) = ∫_x^∞ e^{-t}/t dt`, defined as a
Lebesgue integral over `Ioi x` (DLMF 6.2.1, for `x > 0`).

DLMF 6.2.1.
-/
-- DAG: E-6.2.1.
-- Verified: unverified
noncomputable def E1 (x : ℝ) : ℝ := ∫ t in Ioi x, e1Integrand t

/-- The convergent-series tail of the exponential integral (DLMF 6.6.1/6.6.2):
`eiSeries y = ∑_{k≥0} y^{k+1} / ((k+1)·(k+1)!)`, the entire function with
`E₁(x) = -γ - ln x - eiSeries(-x)` for `x > 0` (see `E1_series` in
`FLMF.Functions.ExpIntegrals.E1Series`) and `Ei(x) = γ + ln x + eiSeries x`.

DLMF 6.6.1.
-/
-- DAG: E-6.6.1.
-- Verified: unverified
noncomputable def eiSeries (y : ℝ) : ℝ :=
  ∑' k : ℕ, y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))

/-- The exponential integral `Ei(x) = γ + ln|x| + ∑_{k≥1} x^k/(k·k!)` (DLMF 6.6.1),
defined uniformly on all of `ℝ ∖ {0}` by its everywhere-convergent series.  This single
formula *is* the genuine real `Ei` for both signs of `x` (correct for `x > 0`, where the
defining Lebesgue integral `∫_{-∞}^x e^t/t` diverges through the pole at `t = 0` and only the
Cauchy principal value is meaningful).  For `x < 0` it agrees with that integral (DLMF 6.2.5);
this equivalence is the *theorem* `Ei_eq_integral_Iic` in
`FLMF.Functions.ExpIntegrals.E1Series`.  (Resolves `ERRATA.md` `ei-li-junk-on-positive-domain`.)

DLMF 6.6.1.
-/
-- DAG: E-6.6.1.
-- Verified: unverified
noncomputable def Ei (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |x| + eiSeries x

/-- Unfolding lemma for `E1`. -/
-- no-dlmf: definitional unfolding of `E1` (the identity is `rfl`); E₁ itself is tagged at its def
theorem E1_def (x : ℝ) : E1 x = ∫ t in Ioi x, Real.exp (-t) / t := rfl

/-- Unfolding lemma for `Ei`: the series form (DLMF 6.6.1), uniform in `x`. -/
-- no-dlmf: definitional unfolding of `Ei` (the identity is `rfl`); Ei itself is tagged at its def
theorem Ei_def (x : ℝ) :
    Ei x = Real.eulerMascheroniConstant + Real.log |x| + eiSeries x := rfl

/-- The pure change-of-variables identity `∫_{-∞}^{-x} e^t/t dt = -E₁(x)` (substitution
`t ↦ -t`).  It needs neither `Ei` nor the series, so it lives here; the DLMF 6.2.6 bridges
`Ei(-x) = -E₁(x)` etc. and the `x < 0` integral representation `Ei_eq_integral_Iic` are
derived from it together with `E1_series` in `FLMF.Functions.ExpIntegrals.E1Series`. -/
-- no-dlmf: change-of-variables infrastructure; the DLMF 6.2.6 relation is `Ei_neg_eq_neg_E1`
theorem integral_Iic_exp_div_eq_neg_E1 (x : ℝ) :
    ∫ t in Iic (-x), Real.exp t / t = -E1 x := by
  unfold E1 e1Integrand
  have h1 := integral_comp_neg_Iic (-x) (fun s : ℝ => Real.exp (-s) / (-s))
  simp only [neg_neg] at h1
  rw [h1, ← integral_neg]
  congr 1; funext s; rw [div_neg]

/-- The integrand of `E₁` is measurable. -/
-- no-dlmf: measurability infrastructure for the E₁ integrand; no DLMF counterpart
theorem e1Integrand_measurable : Measurable e1Integrand := by
  unfold e1Integrand
  fun_prop

end FLMF.ExpIntegrals.Def
