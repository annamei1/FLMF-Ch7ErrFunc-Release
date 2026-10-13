import FLMF.Frameworks.Hypergeometric.GaussUniqueness
import FLMF.Methods.ODEContinuation

/-!
# Analytic continuation of `₂F₁` along the Gauss ODE (framework — DLMF §15.2(ii), §15.10)

The Gauss series defines `₂F₁(a,b;c;z)` only on `|z| < 1`; DLMF §15.2(ii)
continues it to `ℂ ∖ [1,∞)` (and, as a multivalued function, to `ℂ ∖ {0,1}`)
— the classical route rides the hypergeometric equation (DLMF 15.10.1), whose
only finite singularities are `z = 0, 1`.  This file instantiates the
`Methods/ODEContinuation` kit for `₂F₁`:

* `analyticOnNhd_ordinaryHypergeometric` — `₂F₁` is analytic on the unit disc.
* `eqOn_ordinaryHypergeometric_of_gaussODE` — **continuation certificate**: an
  analytic solution of the hypergeometric equation on a disc
  `D(z₀,R) ⊆ ℂ ∖ {0,1}`, matching the 1-jet of `₂F₁` at one point of the
  overlap with the unit disc, agrees with `₂F₁` on the whole overlap — it *is*
  the analytic continuation of `₂F₁` there.
* `exists_extension_ordinaryHypergeometric` — the resulting **disc-step
  continuation**: a single analytic function on `D(0,1) ∪ D(z₀,R)` restricting
  to `₂F₁` on the unit disc and to the certified solution on the new disc.

This is the comparison interface for the C2 Phase-2 connection formulas
(DLMF 15.10.11 ff.): a solution basis at `z = 1` — analytic on a preconnected
subdomain of `ℂ ∖ {0,1}` overlapping the unit disc — is matched against `₂F₁`
by its 1-jet at a single interior point.

## References

- DLMF §15.2(ii): https://dlmf.nist.gov/15.2#ii
- DLMF §15.10: https://dlmf.nist.gov/15.10
-/

open Set Metric FLMF.Methods.ODEContinuation
open scoped ENNReal NNReal

namespace FLMF.Hypergeometric

-- no-dlmf: analyticity repackaging of the series (the series is DLMF 15.2.1)
/-- `₂F₁(a,b;c;·)` is analytic on the open unit ball (parameters off the
nonpositive integers). -/
theorem analyticOnNhd_ordinaryHypergeometric {a b c : ℂ}
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c) :
    AnalyticOnNhd ℂ (₂F₁ a b c : ℂ → ℂ) (ball (0 : ℂ) 1) := by
  have h := (ordinaryHypergeometric_hasFPowerSeriesOnBall a b c habc).analyticOnNhd
  rwa [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) by norm_num, Metric.eball_coe,
    NNReal.coe_one] at h

-- no-dlmf: local Gauss-ODE existence bookkeeping, no DLMF counterpart
/-- The explicit ordinary-point radius supplied by
`ODEContinuation.exists_analyticOnNhd_linODE2` after translating the Gauss
equation to a center `z₀`. -/
noncomputable def gaussLocalRadius (a b c z₀ : ℂ) : ℝ :=
  (4 * ode2K (z₀ * (1 - z₀)) (1 - 2 * z₀) (-1)
    (c - (a + b + 1) * z₀) (-(a + b + 1)) (-(a * b)))⁻¹

-- no-dlmf: local Gauss-ODE existence bookkeeping, no DLMF counterpart
theorem gaussLocalRadius_pos (a b c z₀ : ℂ) :
    0 < gaussLocalRadius a b c z₀ := by
  unfold gaussLocalRadius
  exact inv_pos.mpr (mul_pos (by norm_num) (ode2K_pos _ _ _ _ _ _))

-- no-dlmf: ordinary-point neighborhood bookkeeping, no DLMF counterpart
/-- A local-existence radius cut down so its ball avoids both finite singular
points `0` and `1`. -/
noncomputable def gaussOrdinaryRadius (a b c z₀ : ℂ) : ℝ :=
  min (gaussLocalRadius a b c z₀) (min (‖z₀‖ / 2) (‖1 - z₀‖ / 2))

-- no-dlmf: ordinary-point neighborhood bookkeeping, no DLMF counterpart
theorem gaussOrdinaryRadius_pos (a b c : ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz₁ : z₀ ≠ 1) :
    0 < gaussOrdinaryRadius a b c z₀ := by
  apply lt_min (gaussLocalRadius_pos a b c z₀)
  apply lt_min
  · exact div_pos (norm_pos_iff.mpr hz₀) (by norm_num)
  · exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz₁.symm)) (by norm_num)

-- no-dlmf: ordinary-point neighborhood bookkeeping, no DLMF counterpart
theorem gaussOrdinaryBall_subset (a b c z₀ : ℂ) :
    ball z₀ (gaussOrdinaryRadius a b c z₀) ⊆ ({(0 : ℂ), 1} : Set ℂ)ᶜ := by
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro hx0
    subst x
    have hd : dist (0 : ℂ) z₀ < gaussOrdinaryRadius a b c z₀ := by
      simpa [Metric.mem_ball, dist_comm] using hx
    have hr : gaussOrdinaryRadius a b c z₀ ≤ ‖z₀‖ / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [dist_zero_left] at hd
    linarith [norm_nonneg z₀]
  · intro hx1
    subst x
    have hd : dist (1 : ℂ) z₀ < gaussOrdinaryRadius a b c z₀ := by
      simpa [Metric.mem_ball, dist_comm] using hx
    have hr : gaussOrdinaryRadius a b c z₀ ≤ ‖1 - z₀‖ / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [Complex.dist_eq] at hd
    linarith [norm_nonneg (1 - z₀)]

-- no-dlmf: local Gauss-ODE existence, no DLMF counterpart
/-- At every ordinary point `z₀ ∉ {0,1}`, the Gauss equation has an analytic
local solution with an arbitrary prescribed 1-jet.

Together with 1-jet uniqueness and cover gluing, this is the local-existence
input for continuation along paths in `ℂ ∖ {0,1}`. -/
theorem exists_local_gauss_solution (a b c : ℂ) {z₀ w₀ w₁ : ℂ}
    (hz₀ : z₀ ≠ 0) (hz₁ : z₀ ≠ 1) :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (ball z₀ (gaussOrdinaryRadius a b c z₀)) ∧
      f z₀ = w₀ ∧ deriv f z₀ = w₁ ∧
      ∀ x ∈ ball z₀ (gaussOrdinaryRadius a b c z₀),
        x * (1 - x) * deriv (deriv f) x +
          (c - (a + b + 1) * x) * deriv f x - a * b * f x = 0 := by
  have hp₀ : z₀ * (1 - z₀) ≠ 0 :=
    mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁.symm)
  obtain ⟨f, hf, h0, h1, hode⟩ :=
    exists_analyticOnNhd_linODE2
      (z₀ * (1 - z₀)) (1 - 2 * z₀) (-1)
      (c - (a + b + 1) * z₀) (-(a + b + 1)) (-(a * b))
      hp₀ z₀ w₀ w₁
  refine ⟨f, ?_, h0, h1, ?_⟩
  · exact hf.mono (Metric.ball_subset_ball (min_le_left _ _))
  · intro x hx
    have hx' : x ∈ ball z₀
        (4 * ode2K (z₀ * (1 - z₀)) (1 - 2 * z₀) (-1)
          (c - (a + b + 1) * z₀) (-(a + b + 1)) (-(a * b)))⁻¹ := by
      apply Metric.ball_subset_ball (min_le_left _ _) hx
    have h := hode x hx'
    convert h using 1 <;> ring

-- no-dlmf: compatibility of local continuation elements, no DLMF counterpart
/-- Two ordinary-point Gauss solutions with the same 1-jet at a point of their
overlap agree throughout the overlap of their certified balls. -/
theorem local_gauss_solution_eqOn_inter {a b c u v z₀ : ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball u (gaussOrdinaryRadius a b c u)))
    (hg : AnalyticOnNhd ℂ g (ball v (gaussOrdinaryRadius a b c v)))
    (hfode : ∀ z ∈ ball u (gaussOrdinaryRadius a b c u),
      z * (1 - z) * deriv (deriv f) z +
        (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0)
    (hgode : ∀ z ∈ ball v (gaussOrdinaryRadius a b c v),
      z * (1 - z) * deriv (deriv g) z +
        (c - (a + b + 1) * z) * deriv g z - a * b * g z = 0)
    (hz₀ : z₀ ∈ ball u (gaussOrdinaryRadius a b c u) ∩
      ball v (gaussOrdinaryRadius a b c v))
    (hval : f z₀ = g z₀) (hder : deriv f z₀ = deriv g z₀) :
    EqOn f g (ball u (gaussOrdinaryRadius a b c u) ∩
      ball v (gaussOrdinaryRadius a b c v)) := by
  let U := ball u (gaussOrdinaryRadius a b c u) ∩
    ball v (gaussOrdinaryRadius a b c v)
  have hUo : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_ball u _).inter (convex_ball v _)).isPreconnected
  refine linODE2_eqOn_of_jet_eq'
    (P := fun z : ℂ => z * (1 - z))
    (Q := fun z : ℂ => c - (a + b + 1) * z)
    (R := fun _ : ℂ => -(a * b))
    hUo hUc ?_ ?_ ?_ ?_ (hf.mono Set.inter_subset_left)
      (hg.mono Set.inter_subset_right) ?_ ?_ hz₀ hval hder
  · exact fun _ _ => analyticAt_id.mul (analyticAt_const.sub analyticAt_id)
  · exact fun _ _ => analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  · exact fun _ _ => analyticAt_const
  · intro z hz
    have havoid := gaussOrdinaryBall_subset a b c u hz.1
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at havoid
    exact mul_ne_zero havoid.1 (sub_ne_zero.mpr (Ne.symm havoid.2))
  · intro z hz
    have h := hfode z hz.1
    linear_combination h
  · intro z hz
    have h := hgode z hz.2
    linear_combination h

-- no-dlmf: continuation certificate for DLMF 15.2(ii), no single equation number
/-- **Continuation certificate for `₂F₁`** (DLMF §15.2(ii) interface): an
analytic solution of the hypergeometric equation (DLMF 15.10.1) on a disc
avoiding the singularities `{0, 1}`, matching the 1-jet of `₂F₁` at one point
of the overlap with the unit disc, agrees with `₂F₁` on the whole overlap —
i.e. it *is* the analytic continuation of `₂F₁` there.  (The overlap of two
discs is convex, hence preconnected, so 1-jet uniqueness applies.) -/
theorem eqOn_ordinaryHypergeometric_of_gaussODE_of_c {a b c : ℂ}
    (hc : ∀ kn : ℕ, (kn : ℂ) ≠ -c)
    {z₀ : ℂ} {R : ℝ} (hsub : ball z₀ R ⊆ {(0 : ℂ), 1}ᶜ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball z₀ R))
    (hode : ∀ z ∈ ball z₀ R,
      z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z
        - a * b * f z = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ ball z₀ R ∩ ball (0 : ℂ) 1)
    (hval : f z₁ = ₂F₁ a b c z₁)
    (hder : deriv f z₁ = deriv (₂F₁ a b c : ℂ → ℂ) z₁) :
    Set.EqOn f (₂F₁ a b c) (ball z₀ R ∩ ball (0 : ℂ) 1) := by
  set U : Set ℂ := ball z₀ R ∩ ball (0 : ℂ) 1 with hU
  have hUo : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected U := ((convex_ball z₀ R).inter (convex_ball 0 1)).isPreconnected
  have hne : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    have := hsub hz.1
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at this
    exact this
  refine linODE2_eqOn_of_jet_eq' (P := fun z => z * (1 - z))
    (Q := fun z => c - (a + b + 1) * z) (R := fun _ => -(a * b)) hUo hUc
    ?_ ?_ ?_ ?_ (hf.mono Set.inter_subset_left)
    ((analyticOnNhd_ordinaryHypergeometric_of_c a b c hc).mono Set.inter_subset_right)
    ?_ ?_ hz₁ hval hder
  · exact fun z hz => analyticAt_id.mul (analyticAt_const.sub analyticAt_id)
  · exact fun z hz => analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  · exact fun z hz => analyticAt_const
  · intro z hz
    exact mul_ne_zero (hne z hz).1 (sub_ne_zero.mpr (Ne.symm (hne z hz).2))
  · intro z hz
    have h := hode z hz.1
    linear_combination h
  · intro z hz
    have hz1 : ‖z‖ < 1 := by
      have := hz.2
      rwa [mem_ball_zero_iff] at this
    have h := ordinaryHypergeometric_ode_of_c a b c hc hz1
    linear_combination h

-- no-dlmf: compatibility wrapper for the older three-parameter hypothesis
/-- Variant of `eqOn_ordinaryHypergeometric_of_gaussODE_of_c` retaining the
legacy hypothesis shape used by existing callers. -/
theorem eqOn_ordinaryHypergeometric_of_gaussODE {a b c : ℂ}
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c)
    {z₀ : ℂ} {R : ℝ} (hsub : ball z₀ R ⊆ {(0 : ℂ), 1}ᶜ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball z₀ R))
    (hode : ∀ z ∈ ball z₀ R,
      z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z
        - a * b * f z = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ ball z₀ R ∩ ball (0 : ℂ) 1)
    (hval : f z₁ = ₂F₁ a b c z₁)
    (hder : deriv f z₁ = deriv (₂F₁ a b c : ℂ → ℂ) z₁) :
    Set.EqOn f (₂F₁ a b c) (ball z₀ R ∩ ball (0 : ℂ) 1) :=
  eqOn_ordinaryHypergeometric_of_gaussODE_of_c
    (fun kn => (habc kn).2.2) hsub hf hode hz₁ hval hder

-- no-dlmf: disc-step continuation of 2F1 (DLMF 15.2(ii)), no single equation number
/-- **Disc-step analytic continuation of `₂F₁`** beyond the unit disc: given a
certified local solution on a disc `D(z₀,R) ⊆ ℂ ∖ {0,1}` overlapping the unit
disc and matching the 1-jet of `₂F₁` at one overlap point, there is a single
analytic function on `D(0,1) ∪ D(z₀,R)` restricting to `₂F₁` on the unit disc
and to the local solution on the new disc. -/
theorem exists_extension_ordinaryHypergeometric {a b c : ℂ}
    (habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c)
    {z₀ : ℂ} {R : ℝ} (hsub : ball z₀ R ⊆ {(0 : ℂ), 1}ᶜ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball z₀ R))
    (hode : ∀ z ∈ ball z₀ R,
      z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z
        - a * b * f z = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ ball z₀ R ∩ ball (0 : ℂ) 1)
    (hval : f z₁ = ₂F₁ a b c z₁)
    (hder : deriv f z₁ = deriv (₂F₁ a b c : ℂ → ℂ) z₁) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball (0 : ℂ) 1 ∪ ball z₀ R) ∧
      Set.EqOn h (₂F₁ a b c) (ball (0 : ℂ) 1) ∧ Set.EqOn h f (ball z₀ R) := by
  have hcert := eqOn_ordinaryHypergeometric_of_gaussODE habc hsub hf hode hz₁ hval hder
  exact exists_analyticOnNhd_extension_union isOpen_ball isOpen_ball
    (analyticOnNhd_ordinaryHypergeometric habc) hf
    (fun z hz => (hcert ⟨hz.2, hz.1⟩).symm)

-- no-dlmf: disc-step continuation under the exact lower-parameter hypothesis
/-- The disc-step continuation theorem with unrestricted upper parameters.
Only the lower parameter must avoid the nonpositive integers. -/
theorem exists_extension_ordinaryHypergeometric_of_c {a b c : ℂ}
    (hc : ∀ kn : ℕ, (kn : ℂ) ≠ -c)
    {z₀ : ℂ} {R : ℝ} (hsub : ball z₀ R ⊆ {(0 : ℂ), 1}ᶜ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball z₀ R))
    (hode : ∀ z ∈ ball z₀ R,
      z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z
        - a * b * f z = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ ball z₀ R ∩ ball (0 : ℂ) 1)
    (hval : f z₁ = ₂F₁ a b c z₁)
    (hder : deriv f z₁ = deriv (₂F₁ a b c : ℂ → ℂ) z₁) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball (0 : ℂ) 1 ∪ ball z₀ R) ∧
      Set.EqOn h (₂F₁ a b c) (ball (0 : ℂ) 1) ∧ Set.EqOn h f (ball z₀ R) := by
  have hcert :=
    eqOn_ordinaryHypergeometric_of_gaussODE_of_c hc hsub hf hode hz₁ hval hder
  exact exists_analyticOnNhd_extension_union isOpen_ball isOpen_ball
    (analyticOnNhd_ordinaryHypergeometric_of_c a b c hc) hf
    (fun z hz => (hcert ⟨hz.2, hz.1⟩).symm)

end FLMF.Hypergeometric
