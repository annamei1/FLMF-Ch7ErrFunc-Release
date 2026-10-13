import FLMF.Frameworks.Hypergeometric.Tricomi
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivative of Tricomi's `U(a;b;z)` (framework — DLMF §13.3)

The first `z`-derivative of the second confluent solution, obtained by
differentiating the integral representation (DLMF 13.4.4) under the integral
sign:

* `tricomiU_hasDerivAt` / `tricomiU_deriv` — `d/dz U(a;b;z) = −a·U(a+1;b+1;z)`
  (DLMF 13.3.22), for `a > 0`, `z > 0`.

The mechanism is `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`:
the `z`-derivative of the integrand `e^{−zt} t^{a−1}(1+t)^{b−a−1}` is
`−t·e^{−zt} t^{a−1}(1+t)^{b−a−1} = −e^{−zt} t^{a}(1+t)^{b−a−1}`, which is exactly
`−tricomiIntegrand (a+1) (b+1) z t` (since `(a+1)−1 = a` and
`(b+1)−(a+1)−1 = b−a−1`). On the ball `‖z'−z‖ < z/2` the derivative is dominated
by `tricomiIntegrand (a+1) (b+1) (z/2)`, which is integrable on `(0,∞)`. The
constant `Γ(a)⁻¹` is carried through, and `Γ(a+1) = a·Γ(a)` collapses
`Γ(a)⁻¹·Γ(a+1)` to `a`.
-/

noncomputable section

open MeasureTheory Real Set Filter Asymptotics Metric
open scoped Topology

namespace FLMF.Hypergeometric

/-- The Tricomi integrand `t ↦ e^{−zt} t^{a−1}(1+t)^{b−a−1}` is continuous on
`(0, ∞)` (the only singular factor is `t^{a−1}` at `t = 0`). -/
-- no-dlmf: integrand continuity, no DLMF counterpart
theorem tricomiIntegrand_continuousOn (a b z : ℝ) :
    ContinuousOn (fun t => tricomiIntegrand a b z t) (Ioi (0 : ℝ)) := by
  unfold tricomiIntegrand
  apply ContinuousOn.mul
  apply ContinuousOn.mul
  · exact ((continuous_const.mul continuous_id).rexp).continuousOn
  · apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    exact Or.inl (ne_of_gt ht)
  · apply ContinuousOn.rpow_const ((continuous_const.add continuous_id).continuousOn)
    intro t ht
    have : (0 : ℝ) < t := ht
    exact Or.inl (by positivity : (1 : ℝ) + t ≠ 0)

/-- The shifted integrand identity: for `t > 0`,
`tricomiIntegrand (a+1) (b+1) z t = e^{−zt} t^{a}(1+t)^{b−a−1}` rewritten so the
exponents match the original family. Concretely
`tricomiIntegrand (a+1) (b+1) z t = e^{−zt} · (t · t^{a−1}) · (1+t)^{b−a−1}`. -/
-- no-dlmf: integrand shift bookkeeping, no DLMF counterpart
theorem tricomiIntegrand_shift {a b z t : ℝ} (ht : 0 < t) :
    tricomiIntegrand (a + 1) (b + 1) z t
      = Real.exp (-z * t) * (t * t ^ (a - 1)) * (1 + t) ^ (b - a - 1) := by
  unfold tricomiIntegrand
  have hexp : t ^ (a + 1 - 1) = t * t ^ (a - 1) := by
    rw [show a + 1 - 1 = 1 + (a - 1) by ring, Real.rpow_add ht, Real.rpow_one]
  rw [hexp]
  congr 2
  ring_nf

/-- The `z`-derivative of the Tricomi integrand, pointwise in `t > 0`:
`∂/∂z [e^{−zt} t^{a−1}(1+t)^{b−a−1}] = −e^{−zt} t^{a}(1+t)^{b−a−1}
= −tricomiIntegrand (a+1) (b+1) z t`. -/
-- no-dlmf: parametric z-derivative of the integrand, no DLMF counterpart
theorem tricomiIntegrand_hasDerivAt_param {a b t : ℝ} (ht : 0 < t) (z : ℝ) :
    HasDerivAt (fun z' => tricomiIntegrand a b z' t)
      (-tricomiIntegrand (a + 1) (b + 1) z t) z := by
  have hexp : HasDerivAt (fun z' => Real.exp (-z' * t))
      (Real.exp (-z * t) * (-t)) z := by
    have h1 : HasDerivAt (fun z' : ℝ => -z' * t) (-t) z := by
      simpa using ((hasDerivAt_id z).neg.mul_const t)
    simpa using (Real.hasDerivAt_exp (-z * t)).comp z h1
  have hmul := hexp.mul_const (t ^ (a - 1) * (1 + t) ^ (b - a - 1))
  -- Massage the function shape `e^{−z't} · (t^{a−1} (1+t)^{b−a−1})` into the
  -- defining `e^{−z't} · t^{a−1} · (1+t)^{b−a−1}`.
  have hfun : (fun z' => Real.exp (-z' * t) * (t ^ (a - 1) * (1 + t) ^ (b - a - 1)))
      = fun z' => tricomiIntegrand a b z' t := by
    funext z'
    unfold tricomiIntegrand
    ring
  rw [hfun] at hmul
  -- Identify the derivative value.
  convert hmul using 1
  rw [tricomiIntegrand_shift ht]
  ring

/-- Domination of the parametric `z`-derivative on the ball `‖z'−z‖ < z/2`:
for `z' > z/2` and `t > 0`,
`‖−tricomiIntegrand (a+1) (b+1) z' t‖ ≤ tricomiIntegrand (a+1) (b+1) (z/2) t`. -/
-- no-dlmf: derivative-domination bound for differentiation under the integral, no DLMF counterpart
theorem tricomiIntegrand_deriv_norm_le {a b z : ℝ} {z' t : ℝ}
    (hz2 : z / 2 ≤ z') (ht : 0 < t) :
    ‖-tricomiIntegrand (a + 1) (b + 1) z' t‖
      ≤ tricomiIntegrand (a + 1) (b + 1) (z / 2) t := by
  rw [norm_neg, Real.norm_of_nonneg (tricomiIntegrand_nonneg _ _ _ ht.le)]
  unfold tricomiIntegrand
  have hexp : Real.exp (-z' * t) ≤ Real.exp (-(z / 2) * t) := by
    apply Real.exp_le_exp.mpr
    have : -z' * t ≤ -(z / 2) * t := by
      apply mul_le_mul_of_nonneg_right _ ht.le
      linarith
    exact this
  have hta : (0 : ℝ) ≤ t ^ (a + 1 - 1) := Real.rpow_nonneg ht.le _
  have htb : (0 : ℝ) ≤ (1 + t) ^ (b + 1 - (a + 1) - 1) := Real.rpow_nonneg (by linarith) _
  gcongr

/-- **DLMF 13.3.22** (`HasDerivAt` form): for `a > 0` and `z > 0`,
`d/dz U(a;b;z) = −a·U(a+1;b+1;z)`.

DAG: E-13.3.22.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem tricomiU_hasDerivAt {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (fun z => tricomiU a b z) (-a * tricomiU (a + 1) (b + 1) z) z := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set ε : ℝ := z / 2 with hε
  have hεpos : 0 < ε := by positivity
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hz2 : (0 : ℝ) < z / 2 := by positivity
  -- a.e. on the restricted measure, `t > 0`.
  have hmeasIoi : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  -- Differentiation under the integral sign.
  obtain ⟨_, hkey⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (x₀ := z) (bound := fun t => tricomiIntegrand (a + 1) (b + 1) (z / 2) t)
      (F := fun z' t => tricomiIntegrand a b z' t)
      (F' := fun z' t => -tricomiIntegrand (a + 1) (b + 1) z' t)
      (s := ball z ε)
      (ball_mem_nhds z hεpos)
      (Filter.Eventually.of_forall fun z' => by
        rw [hμ]; exact (tricomiIntegrand_continuousOn a b z').aestronglyMeasurable hmeasIoi)
      (tricomiU_integrand_integrableOn ha hz)
      (by
        rw [hμ]
        exact ((tricomiIntegrand_continuousOn (a + 1) (b + 1) z).aestronglyMeasurable
          hmeasIoi).neg)
      (by
        rw [hμ]
        refine (ae_restrict_iff' hmeasIoi).2 (Filter.Eventually.of_forall fun t ht z' hz' => ?_)
        have hz'lb : z / 2 ≤ z' := by
          rw [mem_ball, Real.dist_eq] at hz'
          have := abs_lt.1 hz'
          linarith [this.1]
        exact tricomiIntegrand_deriv_norm_le hz'lb ht)
      (tricomiU_integrand_integrableOn ha1 hz2)
      (by
        rw [hμ]
        refine (ae_restrict_iff' hmeasIoi).2 (Filter.Eventually.of_forall fun t ht z' _ => ?_)
        exact tricomiIntegrand_hasDerivAt_param ht z')
  -- `hkey : HasDerivAt (fun z' => ∫ t, F z' t ∂μ) (∫ t, F' z t ∂μ) z`.
  -- Rewrite the derivative value as `-(Γ(a+1) * tricomiU (a+1) (b+1) z)`.
  have hRHS : (∫ t, -tricomiIntegrand (a + 1) (b + 1) z t ∂μ)
      = -(Real.Gamma (a + 1) * tricomiU (a + 1) (b + 1) z) := by
    rw [integral_neg]
    have hUdef : tricomiU (a + 1) (b + 1) z
        = (Real.Gamma (a + 1))⁻¹ * ∫ t, tricomiIntegrand (a + 1) (b + 1) z t ∂μ := by
      rw [hμ]; rfl
    rw [hUdef]
    have hΓ : Real.Gamma (a + 1) ≠ 0 := (Real.Gamma_pos_of_pos ha1).ne'
    field_simp
  -- Multiply the integral derivative by the constant `Γ(a)⁻¹`.
  have hUbase : (fun z' => tricomiU a b z')
      = fun z' => (Real.Gamma a)⁻¹ * ∫ t, tricomiIntegrand a b z' t ∂μ := by
    funext z'; rw [hμ]; rfl
  have hfinal := hkey.const_mul (Real.Gamma a)⁻¹
  rw [← hUbase] at hfinal
  rw [hRHS] at hfinal
  -- Simplify `Γ(a)⁻¹ * -(Γ(a+1) * U) = -a * U` using `Γ(a+1) = a·Γ(a)`.
  have hΓval : (Real.Gamma a)⁻¹ * -(Real.Gamma (a + 1) * tricomiU (a + 1) (b + 1) z)
      = -a * tricomiU (a + 1) (b + 1) z := by
    rw [Real.Gamma_add_one ha.ne']
    have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    field_simp
  rw [hΓval] at hfinal
  exact hfinal

/-- **DLMF 13.3.22** (`deriv` form): for `a > 0` and `z > 0`,
`d/dz U(a;b;z) = −a·U(a+1;b+1;z)`.

DAG: E-13.3.22.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem tricomiU_deriv {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    deriv (fun z => tricomiU a b z) z = -a * tricomiU (a + 1) (b + 1) z :=
  (tricomiU_hasDerivAt ha hz).deriv

end FLMF.Hypergeometric
