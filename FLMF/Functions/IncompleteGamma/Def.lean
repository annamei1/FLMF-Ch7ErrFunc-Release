import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Lower and upper incomplete Gamma functions (DLMF §8.2)

We define the (real) lower and upper incomplete Gamma functions

* `lowerGamma a x = ∫_0^x e^{-t} t^{a-1} dt`  (γ(a,x))
* `upperGamma a x = ∫_x^∞ e^{-t} t^{a-1} dt`  (Γ(a,x))

and prove the basic additivity relation

  γ(a,x) + Γ(a,x) = Γ(a)   for  0 < a  and  0 ≤ x.

This is DLMF 8.2.3 / 8.2.4.
-/

namespace FLMF.IncompleteGamma

open MeasureTheory Set Real

/-- The lower incomplete Gamma function `γ(a, x) = ∫_0^x e^{-t} t^{a-1} dt`
(DLMF 8.2.1). -/
noncomputable def lowerGamma (a x : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) x, Real.exp (-t) * t ^ (a - 1)

/-- The upper incomplete Gamma function `Γ(a, x) = ∫_x^∞ e^{-t} t^{a-1} dt`
(DLMF 8.2.2). -/
noncomputable def upperGamma (a x : ℝ) : ℝ :=
  ∫ t in Ioi x, Real.exp (-t) * t ^ (a - 1)

/-- The integrand of the Gamma integral is integrable on `Ioi 0` for `0 < a`. -/
-- no-dlmf: convergence/integrability infrastructure, no DLMF counterpart
theorem integrableOn_gammaIntegrand {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 0) :=
  Real.GammaIntegral_convergent ha

/-- The additivity relation `γ(a,x) + Γ(a,x) = Γ(a)` for `0 < a` and `0 ≤ x`
(DLMF 8.2.3).

DAG: E-8.2.3.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem lowerGamma_add_upperGamma {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    lowerGamma a x + upperGamma a x = Real.Gamma a := by
  have hconv := integrableOn_gammaIntegrand ha
  -- Split `Ioi 0` into `Ioc 0 x` and `Ioi x`.
  have hsplit : Ioi (0 : ℝ) = Ioc 0 x ∪ Ioi x := by
    rw [Ioc_union_Ioi_eq_Ioi hx]
  have hdisj : Disjoint (Ioc (0 : ℝ) x) (Ioi x) := Ioc_disjoint_Ioi le_rfl
  have hmeas : MeasurableSet (Ioi x) := measurableSet_Ioi
  -- Restrict integrability to each piece.
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioc 0 x) :=
    hconv.mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi x) :=
    hconv.mono_set (Ioi_subset_Ioi hx)
  -- Now compute Γ(a) by splitting the integral.
  rw [Real.Gamma_eq_integral ha, hsplit,
    setIntegral_union hdisj hmeas hint1 hint2]
  rfl

-- no-dlmf: strictly-more-general total/junk-value form (the empty-interval
-- integral vanishes for every real `a`, not just `Re a > 0`); DLMF 8.2.1 is a
-- definition equation, whose faithful surface is the definition lowerGamma
/-- Trivial value: `γ(a, 0) = 0` (immediate from the defining integral). -/
@[simp]
theorem lowerGamma_zero (a : ℝ) : lowerGamma a 0 = 0 := by
  simp [lowerGamma]

-- no-dlmf: instance of DLMF 8.2.1 (special value z = 0 of the defining
-- integral); faithful surface is the definition lowerGamma
/-- `γ(a, 0) = 0` (restriction of `lowerGamma_zero` to `0 < a`, the domain of
the defining integral). -/
theorem lowerGamma_zero_dlmf (a : ℝ) (_ha : 0 < a) : lowerGamma a 0 = 0 :=
  lowerGamma_zero a

-- no-dlmf: instance of DLMF 8.2.2 (special value z = 0 of the defining
-- integral); faithful surface is the definition upperGamma
/-- For `0 < a`, `Γ(a, 0) = Γ(a)` (immediate from the defining integral). -/
theorem upperGamma_zero {a : ℝ} (ha : 0 < a) : upperGamma a 0 = Real.Gamma a := by
  have := lowerGamma_add_upperGamma ha (le_refl (0 : ℝ))
  simpa using this

end FLMF.IncompleteGamma
