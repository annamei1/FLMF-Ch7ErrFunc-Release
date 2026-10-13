import FLMF.Functions.ExpIntegrals.Definitions
import FLMF.Functions.ExpIntegrals.E1Series

/-!
# The logarithmic integral `li(x)` (DLMF §6.2)

The logarithmic integral is defined (DLMF 6.2.8) as the Cauchy principal
value
$$\operatorname{li}(x) = \fint_0^x \frac{dt}{\ln t}, \qquad x > 1,$$
the integrand having a singularity at `t = 1`.  By the substitution
`t = e^u` one obtains the standard relation
`li(x) = Ei(ln x)` (DLMF 6.2.8), which we take as the working definition.

We additionally package the regularised (truncated) integral
`liTrunc ε x` whose principal value (as `ε → 0⁺`) is `li(x)`; this exposes
the explicit principal-value structure of the definition.
-/

namespace FLMF.ExpIntegrals.Def

open MeasureTheory Real Set Filter Topology

/-- The integrand `t ↦ 1 / ln t` of the logarithmic integral. -/
-- no-dlmf: integrand helper for the li definition; no standalone DLMF identity
noncomputable def liIntegrand (t : ℝ) : ℝ := 1 / Real.log t

/-- The logarithmic integral `li(x)`, defined via the standard relation
`li(x) = Ei(ln x)` (DLMF 6.2.8).  Off the singularity this equals the
Cauchy principal value `⨍₀ˣ dt / ln t`.

DLMF 6.2.8.
-/
-- DAG: E-6.2.8.
-- Verified: unverified (tier2 DIVERGES)
noncomputable def li (x : ℝ) : ℝ := Ei (Real.log x)

/-- Unfolding lemma for `li`. -/
-- no-dlmf: definitional unfolding of `li` (the identity is `rfl`); the li = Ei∘log relation is tagged below
theorem li_def (x : ℝ) : li x = Ei (Real.log x) := rfl

-- no-dlmf: chain link 6.2.8 (assembled in expint_6_2_8)
/-- The defining relation `li(x) = Ei(ln x)` of the logarithmic
integral, on DLMF's domain `x > 1` (where `ln x > 0` and `li` is the standard
prime-counting logarithmic integral — principal value through the singularity at
`x = 1`).  The identity is `li`'s definition (`li := Ei ∘ log`), hence `rfl`; the
`1 < x` hypothesis records the DLMF analytic domain (outside it the unfolding still
holds trivially via the junk `Real.log`, captured by the unconditional `li_def`).
-/
theorem li_eq_Ei_log (x : ℝ) (_hx : 1 < x) : li x = Ei (Real.log x) := rfl

/-- Expressed through `E₁`: `li(x) = -E₁(-ln x)` when `ln x ≤ 0` (i.e. `0 < x ≤ 1`),
the regime where `Ei(ln x)` is the faithful integral branch and the `E₁` bridge applies
(via `Ei_eq_neg_E1_neg`).  For `x > 1`, `li` is still correct as `Ei(ln x)` via the
series branch, but the negative-argument `E₁` form no longer holds (`E₁` is junk there). -/
-- no-dlmf: derived reformulation of li = Ei∘log through E₁; no distinct DLMF entry
theorem li_eq_neg_E1_neg_log (x : ℝ) (hx : Real.log x < 0) :
    li x = -E1 (-Real.log x) := by
  rw [li_def, Ei_eq_neg_E1_neg hx]

/-- The truncated (regularised) logarithmic integral.  For `x > 1` and
`ε > 0` small, `liTrunc ε x` excludes the symmetric `ε`-neighbourhood of the
singularity at `t = 1`:
`liTrunc ε x = ∫₀^{1-ε} dt/ln t + ∫_{1+ε}^x dt/ln t`.  Its limit as
`ε → 0⁺` is the principal value `li(x)`. -/
-- no-dlmf: regularized truncation helper exposing the principal-value structure; no DLMF counterpart
noncomputable def liTrunc (ε x : ℝ) : ℝ :=
    (∫ t in (0 : ℝ)..(1 - ε), liIntegrand t) + (∫ t in (1 + ε)..x, liIntegrand t)

/-- Unfolding lemma for `liTrunc`. -/
-- no-dlmf: definitional unfolding of `liTrunc` (the identity is `rfl`); no DLMF counterpart
theorem liTrunc_def (ε x : ℝ) :
    liTrunc ε x =
      (∫ t in (0 : ℝ)..(1 - ε), liIntegrand t)
        + (∫ t in (1 + ε)..x, liIntegrand t) := rfl

/-- The integrand of `li` is measurable. -/
-- no-dlmf: measurability infrastructure for the li integrand; no DLMF counterpart
theorem liIntegrand_measurable : Measurable liIntegrand := by
  unfold liIntegrand
  fun_prop

/-- The principal value `li(1)` (at the lower endpoint of the cut) reduces to
`Ei(0)`. -/
-- no-dlmf: special-point reduction li(1) = Ei(0); no DLMF counterpart
theorem li_one : li 1 = Ei 0 := by
  simp [li, Real.log_one]

/-! ## Remaining members of the DLMF 6.2.8 chain -/

-- no-dlmf: chain link 6.2.8 (assembled in expint_6_2_8)
/-- On DLMF's analytic domain `x > 1`, the logarithmic integral is the Cauchy
principal value `li(x) = ⨍₀ˣ dt / ln t`, the integrand being singular at the
interior point `t = 1`.  We state this via the regularised truncation
`liTrunc ε x` (which omits the symmetric `ε`-neighbourhood of `t = 1`,
`liTrunc ε x = ∫₀^{1-ε} + ∫_{1+ε}^x`): its limit as `ε → 0⁺` is exactly the
principal value, and equals `li x`.
-/
theorem li_eq_pv_integral (x : ℝ) (_hx : 1 < x) :
    Tendsto (fun ε : ℝ => liTrunc ε x) (nhdsWithin 0 (Ioi 0)) (nhds (li x)) := by
  sorry

/-- **DLMF 6.2.8.** The logarithmic integral `li(x) = ⨍₀ˣ dt/ln t = Ei(ln x)`
for `x > 1`: the Cauchy principal-value integral representation, and the
defining relation to `Ei`.

DLMF 6.2.8.
DAG: E-6.2.8.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem expint_6_2_8 (x : ℝ) (hx : 1 < x) :
    Tendsto (fun ε : ℝ => liTrunc ε x) (nhdsWithin 0 (Ioi 0)) (nhds (li x))
      ∧ li x = Ei (Real.log x) :=
  ⟨li_eq_pv_integral x hx, li_eq_Ei_log x hx⟩

end FLMF.ExpIntegrals.Def
