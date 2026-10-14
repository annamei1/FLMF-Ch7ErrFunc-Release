/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

Integrated into FLMF.Support.Watson on 2026-10-14.
Original declaration names and proofs are retained.
-/

import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Watson's lemma on the positive half-line

Leading-order Watson lemma for the Laplace kernel on `(0, ∞)`.
-/

/-!
# Watson's lemma (method kit — DLMF §2.3)

Leading-order asymptotics of half-line Laplace integrals: for `s > 0` and `g`
measurable, bounded on `(0,∞)` with a limit `a₀` at `0⁺`,

`x^s · ∫_{(0,∞)} e^{−x t} t^{s−1} g(t) dt → a₀ · Γ(s)` as `x → ∞`.

Integrated from the `picard-lefschetz` method spine into
`FLMF.Support.Watson`. The `PicardLefschetz` declaration namespace is retained
for compatibility. Unlocks the leading
asymptotics of the exponential integral `E₁`, the error function, and the
incomplete Gamma function.

Surfaced (namespace `PicardLefschetz`):

* `watson_leading` — the leading-order Watson's lemma above.
* `watson_growth` — the same conclusion under an *exponential-growth* amplitude
  `|g t| ≤ C·e^{c t}` (the integral converges for `x > c`; the leading constant is
  unchanged). Unblocks the incomplete-Γ asymptotic for general order `a`.
* `watson_next_order` — the **second term**: for `g t = a₀ + t·h t`,
  `x·(x^s ∫ e^{−x t} t^{s−1} g − a₀ Γ(s)) → a₁ Γ(s+1)`.
* `watson_series` — the **full N-term asymptotic series**: for
  `g t = Σ_{k<N} aₖ tᵏ + tᴺ h t`,
  `xᴺ·(x^s ∫ e^{−x t} t^{s−1} g − Σ_{k<N} aₖ Γ(s+k) x^{−k}) → aₙ Γ(s+N)`.
  (Polynomial integrated exactly via the moment; remainder reduces to
  `watson_leading` at `s+N`. `watson_next_order` is the `N=1` case.)
* `integral_exp_neg_mul_rpow_Ioi` — the scaled Gamma moment
  `∫_{(0,∞)} e^{−x t} t^{s−1} dt = Γ(s)·x^{−s}`.

The Watson spine is complete: moment · leading · growth · next-order · N-term series.
-/

namespace PicardLefschetz

open MeasureTheory Real Filter Topology Set

/-- Gamma integral after scaling the positive half-line.
Reference: DLMF §2.3 (Watson's lemma), leading term. -/
theorem integral_exp_neg_mul_rpow_Ioi {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (s - 1) = Real.Gamma s * x ^ (-s) := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s - 1) (b := x)
      one_pos (by linarith) hx
  calc
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (s - 1)
        = ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-x * t ^ (1 : ℝ)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          simp [Real.rpow_one, mul_comm]
    _ = x ^ (-((s - 1) + 1) / (1 : ℝ)) * (1 / (1 : ℝ)) *
        Real.Gamma (((s - 1) + 1) / (1 : ℝ)) := h
    _ = Real.Gamma s * x ^ (-s) := by
          ring_nf

private theorem watson_change_variables {s : ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) :
    x ^ s * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t)
      = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * g (u / x)) := by
  set G : ℝ → ℝ := fun u => Real.exp (-u) * (u ^ (s - 1) * g (u / x)) with hG
  have hscale := integral_comp_mul_left_Ioi G 0 hx
  simp only [mul_zero, smul_eq_mul] at hscale
  have hleft :
      (∫ t in Ioi (0 : ℝ), G (x * t))
        = x ^ (s - 1) *
            ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht
    have hdiv : x * t / x = t := by
      exact mul_div_cancel_left₀ t hx.ne'
    have hneg : -(x * t) = -x * t := by ring
    simp only [hG]
    rw [Real.mul_rpow hx.le ht_nonneg, hdiv, hneg]
    ring
  have hbase :
      x ^ (s - 1) * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t)
        = x⁻¹ * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * g (u / x)) := by
    rw [← hleft, hscale]
  calc
    x ^ s * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t)
        = x * (x ^ (s - 1) *
            ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t)) := by
          rw [show s = s - 1 + 1 by ring, Real.rpow_add_one hx.ne']
          ring_nf
    _ = x * (x⁻¹ * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * g (u / x))) := by
          rw [hbase]
    _ = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * g (u / x)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]

/-- Leading-order Watson lemma on `(0, ∞)`.
Reference: DLMF §2.3 (Watson's lemma), leading term. -/
theorem watson_leading {s : ℝ} (hs : 0 < s) {g : ℝ → ℝ} {a₀ C : ℝ}
    (hgm : Measurable g)
    (hC : ∀ t ∈ Ioi (0 : ℝ), |g t| ≤ C)
    (hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 a₀)) :
    Tendsto (fun x : ℝ => x ^ s * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
      atTop (𝓝 (a₀ * Real.Gamma s)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun x u => Real.exp (-u) * (u ^ (s - 1) * g (u / x))
  let f : ℝ → ℝ := fun u => Real.exp (-u) * (u ^ (s - 1) * a₀)
  let bound : ℝ → ℝ := fun u => |C| * (Real.exp (-u) * u ^ (s - 1))
  have hpow_aesm : AEStronglyMeasurable (fun u : ℝ => u ^ (s - 1)) μ := by
    exact (continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu))).aestronglyMeasurable
      measurableSet_Ioi
  have hexp_aesm : AEStronglyMeasurable (fun u : ℝ => Real.exp (-u)) μ := by
    exact (Real.measurable_exp.comp measurable_id.neg).aestronglyMeasurable
  have hg_aesm : ∀ x : ℝ, AEStronglyMeasurable (fun u : ℝ => g (u / x)) μ := by
    intro x
    exact (hgm.comp (measurable_id.div_const x)).aestronglyMeasurable
  have hF_aesm : ∀ x : ℝ, AEStronglyMeasurable (F x) μ := by
    intro x
    simpa [F, mul_assoc] using hexp_aesm.mul (hpow_aesm.mul (hg_aesm x))
  have h_bound_eventually :
      ∀ᶠ x in atTop, ∀ᵐ u ∂μ, ‖F x u‖ ≤ bound u := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := hu
    have hux : u / x ∈ Ioi (0 : ℝ) := by
      exact div_pos hu_pos hx
    have hg_bound : |g (u / x)| ≤ |C| :=
      (hC (u / x) hux).trans (le_abs_self C)
    have hk_nonneg : 0 ≤ Real.exp (-u) * u ^ (s - 1) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg (le_of_lt hu_pos) _)
    calc
      ‖F x u‖ = (Real.exp (-u) * u ^ (s - 1)) * |g (u / x)| := by
        simp [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hu_pos) _), mul_assoc, mul_comm]
      _ ≤ (Real.exp (-u) * u ^ (s - 1)) * |C| :=
        mul_le_mul_of_nonneg_left hg_bound hk_nonneg
      _ = bound u := by
        simp [bound, mul_comm]
  have h_bound_integrable : Integrable bound μ := by
    have hker : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (s - 1)) μ := by
      simpa [μ] using (Real.GammaIntegral_convergent hs).integrable
    simpa [bound] using hker.const_mul |C|
  have h_lim_ae : ∀ᵐ u ∂μ, Tendsto (fun x : ℝ => F x u) atTop (𝓝 (f u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := hu
    have hdiv_nhds : Tendsto (fun x : ℝ => u / x) atTop (𝓝 (0 : ℝ)) :=
      Filter.Tendsto.const_div_atTop (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop) u
    have hdiv_within : Tendsto (fun x : ℝ => u / x) atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hdiv_nhds, by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact div_pos hu_pos hx⟩
    have hg_lim : Tendsto (fun x : ℝ => g (u / x)) atTop (𝓝 a₀) :=
      hlim.comp hdiv_within
    have hmul_lim :
        Tendsto (fun x : ℝ => u ^ (s - 1) * g (u / x)) atTop
          (𝓝 (u ^ (s - 1) * a₀)) :=
      Tendsto.const_mul (u ^ (s - 1)) hg_lim
    simpa [F, f, mul_assoc] using Tendsto.const_mul (Real.exp (-u)) hmul_lim
  have hDCT :
      Tendsto (fun x : ℝ => ∫ u, F x u ∂μ) atTop (𝓝 (∫ u, f u ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_
      h_bound_integrable h_lim_ae
    · filter_upwards with x
      exact hF_aesm x
    · exact h_bound_eventually
  have hlimit_eval :
      (∫ u, f u ∂μ) = a₀ * Real.Gamma s := by
    calc
      (∫ u, f u ∂μ)
          = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * a₀) := by
            rfl
      _ = ∫ u in Ioi (0 : ℝ), a₀ * (Real.exp (-u) * u ^ (s - 1)) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro u hu
            ring
      _ = a₀ * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (s - 1) := by
            rw [integral_const_mul]
      _ = a₀ * Real.Gamma s := by
            rw [← Real.Gamma_eq_integral hs]
  have hrescaled :
      Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * (u ^ (s - 1) * g (u / x))) atTop
        (𝓝 (a₀ * Real.Gamma s)) := by
    simpa [μ, F, f, hlimit_eval] using hDCT
  refine hrescaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (watson_change_variables (s := s) (g := g) hx).symm

/-- Watson lemma on `(0, ∞)` for amplitudes with exponential growth.
Reference: DLMF §2.3 (Watson's lemma), exponential-growth variant. -/
theorem watson_growth {s : ℝ} (hs : 0 < s) {g : ℝ → ℝ} {a₀ C c : ℝ} (hC0 : 0 ≤ C)
    (hgm : Measurable g)
    (hC : ∀ t ∈ Ioi (0 : ℝ), |g t| ≤ C * Real.exp (c * t))
    (hlim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 a₀)) :
    Tendsto (fun x : ℝ => x ^ s * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
      atTop (𝓝 (a₀ * Real.Gamma s)) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let M : ℝ := max c 0
  let X : ℝ := M + 1
  let β : ℝ := M / X
  let F : ℝ → ℝ → ℝ := fun x u => Real.exp (-u) * (u ^ (s - 1) * g (u / x))
  let f : ℝ → ℝ := fun u => Real.exp (-u) * (u ^ (s - 1) * a₀)
  let bound : ℝ → ℝ := fun u => C * (Real.exp (-u) * u ^ (s - 1)) * Real.exp (β * u)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact le_max_right c 0
  have hM_lt_X : M < X := by
    dsimp [X]
    linarith
  have hX_pos : 0 < X := by
    linarith
  have hβ_nonneg : 0 ≤ β := by
    exact div_nonneg hM_nonneg hX_pos.le
  have hβ_lt_one : β < 1 := by
    dsimp [β]
    exact (div_lt_one hX_pos).mpr hM_lt_X
  have hb_pos : 0 < 1 - β := sub_pos.mpr hβ_lt_one
  have hpow_aesm : AEStronglyMeasurable (fun u : ℝ => u ^ (s - 1)) μ := by
    exact (continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu))).aestronglyMeasurable
      measurableSet_Ioi
  have hexp_aesm : AEStronglyMeasurable (fun u : ℝ => Real.exp (-u)) μ := by
    exact (Real.measurable_exp.comp measurable_id.neg).aestronglyMeasurable
  have hg_aesm : ∀ x : ℝ, AEStronglyMeasurable (fun u : ℝ => g (u / x)) μ := by
    intro x
    exact (hgm.comp (measurable_id.div_const x)).aestronglyMeasurable
  have hF_aesm : ∀ x : ℝ, AEStronglyMeasurable (F x) μ := by
    intro x
    simpa [F, mul_assoc] using hexp_aesm.mul (hpow_aesm.mul (hg_aesm x))
  have h_bound_eventually :
      ∀ᶠ x in atTop, ∀ᵐ u ∂μ, ‖F x u‖ ≤ bound u := by
    filter_upwards [eventually_ge_atTop X] with x hxX
    have hx_pos : 0 < x := lt_of_lt_of_le hX_pos hxX
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := hu
    have hux : u / x ∈ Ioi (0 : ℝ) := by
      exact div_pos hu_pos hx_pos
    have hg_bound : |g (u / x)| ≤ C * Real.exp (c * (u / x)) :=
      hC (u / x) hux
    have hexp_le : Real.exp (c * (u / x)) ≤ Real.exp (β * u) := by
      refine Real.exp_le_exp.mpr ?_
      by_cases hc_nonneg : 0 ≤ c
      · have hux_le : u / x ≤ u / X :=
          div_le_div_of_nonneg_left hu_pos.le hX_pos hxX
        have hmul_le : c * (u / x) ≤ c * (u / X) :=
          mul_le_mul_of_nonneg_left hux_le hc_nonneg
        have hM_eq : M = c := by
          dsimp [M]
          exact max_eq_left hc_nonneg
        have hβ_eq : β = c / X := by
          dsimp [β]
          rw [hM_eq]
        calc
          c * (u / x) ≤ c * (u / X) := hmul_le
          _ = β * u := by
            rw [hβ_eq]
            ring
      · have hc_nonpos : c ≤ 0 := le_of_lt (lt_of_not_ge hc_nonneg)
        have hleft_nonpos : c * (u / x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hc_nonpos (div_pos hu_pos hx_pos).le
        have hright_nonneg : 0 ≤ β * u :=
          mul_nonneg hβ_nonneg hu_pos.le
        exact hleft_nonpos.trans hright_nonneg
    have hg_bound_beta : |g (u / x)| ≤ C * Real.exp (β * u) :=
      hg_bound.trans (mul_le_mul_of_nonneg_left hexp_le hC0)
    have hk_nonneg : 0 ≤ Real.exp (-u) * u ^ (s - 1) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg hu_pos.le _)
    calc
      ‖F x u‖ = (Real.exp (-u) * u ^ (s - 1)) * |g (u / x)| := by
        simp [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (Real.rpow_nonneg hu_pos.le _), mul_assoc, mul_comm]
      _ ≤ (Real.exp (-u) * u ^ (s - 1)) * (C * Real.exp (β * u)) :=
        mul_le_mul_of_nonneg_left hg_bound_beta hk_nonneg
      _ = bound u := by
        simp [bound]
        ring
  have h_bound_integrable : Integrable bound μ := by
    have htail_on :
        IntegrableOn
          (fun u : ℝ => u ^ (s - 1) * Real.exp (-(1 - β) * u ^ (1 : ℝ)))
          (Ioi (0 : ℝ)) volume := by
      exact integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := 1 - β)
        (by linarith) (by norm_num) hb_pos
    have htail : Integrable (fun u : ℝ => u ^ (s - 1) * Real.exp (-(1 - β) * u)) μ := by
      rw [show (fun u : ℝ => u ^ (s - 1) * Real.exp (-(1 - β) * u)) =
          (fun u : ℝ => u ^ (s - 1) * Real.exp (-(1 - β) * u ^ (1 : ℝ))) by
            funext u
            rw [Real.rpow_one]]
      simpa [μ, IntegrableOn] using htail_on
    have hmul : Integrable (fun u : ℝ => C * (u ^ (s - 1) * Real.exp (-(1 - β) * u))) μ :=
      htail.const_mul C
    refine hmul.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    calc
      C * (u ^ (s - 1) * Real.exp (-(1 - β) * u))
          = C * (u ^ (s - 1) * (Real.exp (-u) * Real.exp (β * u))) := by
            rw [← Real.exp_add]
            congr 2
            ring_nf
      _ = bound u := by
            simp [bound]
            ring_nf
  have h_lim_ae : ∀ᵐ u ∂μ, Tendsto (fun x : ℝ => F x u) atTop (𝓝 (f u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := hu
    have hdiv_nhds : Tendsto (fun x : ℝ => u / x) atTop (𝓝 (0 : ℝ)) :=
      Filter.Tendsto.const_div_atTop (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop) u
    have hdiv_within : Tendsto (fun x : ℝ => u / x) atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hdiv_nhds, by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact div_pos hu_pos hx⟩
    have hg_lim : Tendsto (fun x : ℝ => g (u / x)) atTop (𝓝 a₀) :=
      hlim.comp hdiv_within
    have hmul_lim :
        Tendsto (fun x : ℝ => u ^ (s - 1) * g (u / x)) atTop
          (𝓝 (u ^ (s - 1) * a₀)) :=
      Tendsto.const_mul (u ^ (s - 1)) hg_lim
    simpa [F, f, mul_assoc] using Tendsto.const_mul (Real.exp (-u)) hmul_lim
  have hDCT :
      Tendsto (fun x : ℝ => ∫ u, F x u ∂μ) atTop (𝓝 (∫ u, f u ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound ?_ ?_
      h_bound_integrable h_lim_ae
    · filter_upwards with x
      exact hF_aesm x
    · exact h_bound_eventually
  have hlimit_eval :
      (∫ u, f u ∂μ) = a₀ * Real.Gamma s := by
    calc
      (∫ u, f u ∂μ)
          = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * (u ^ (s - 1) * a₀) := by
            rfl
      _ = ∫ u in Ioi (0 : ℝ), a₀ * (Real.exp (-u) * u ^ (s - 1)) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro u hu
            ring
      _ = a₀ * ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (s - 1) := by
            rw [integral_const_mul]
      _ = a₀ * Real.Gamma s := by
            rw [← Real.Gamma_eq_integral hs]
  have hrescaled :
      Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * (u ^ (s - 1) * g (u / x))) atTop
        (𝓝 (a₀ * Real.Gamma s)) := by
    simpa [μ, F, f, hlimit_eval] using hDCT
  refine hrescaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (watson_change_variables (s := s) (g := g) hx).symm

/-- Next-order Watson lemma on `(0, ∞)`.
Reference: DLMF §2.3 (Watson's lemma), next-order term. -/
theorem watson_next_order {s : ℝ} (hs : 0 < s) {g h : ℝ → ℝ} {a₀ a₁ C : ℝ}
    (hsplit : ∀ t ∈ Ioi (0:ℝ), g t = a₀ + t * h t)
    (hhm : Measurable h)
    (hhC : ∀ t ∈ Ioi (0:ℝ), |h t| ≤ C)
    (hhlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 a₁)) :
    Tendsto (fun x : ℝ => x * (x ^ s * (∫ t in Ioi (0:ℝ), Real.exp (-x * t) * (t ^ (s-1) * g t))
                                  - a₀ * Real.Gamma s))
      atTop (𝓝 (a₁ * Real.Gamma (s + 1))) := by
  have hs1 : 0 < s + 1 := by linarith
  have hw := watson_leading (s := s + 1) hs1 (g := h) (a₀ := a₁) (C := C) hhm hhC hhlim
  refine hw.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hker0_on :
      IntegrableOn (fun t : ℝ => Real.exp (-x * t) * t ^ (s - 1)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := x)
      (by linarith) (by norm_num) hx
    exact h.congr_fun (fun t ht => by
      rw [Real.rpow_one]
      ring) measurableSet_Ioi
  have hF0 :
      Integrable (fun t : ℝ => a₀ * (Real.exp (-x * t) * t ^ (s - 1)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hker0_on.integrable.const_mul a₀
  have hker1_on :
      IntegrableOn (fun t : ℝ => Real.exp (-x * t) * t ^ s) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s) (b := x)
      (by linarith) (by norm_num) hx
    exact h.congr_fun (fun t ht => by
      rw [Real.rpow_one]
      ring) measurableSet_Ioi
  have hker1 :
      Integrable (fun t : ℝ => Real.exp (-x * t) * t ^ s)
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hker1_on
  have hh_aesm : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) :=
    hhm.aestronglyMeasurable
  have hh_bound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖h t‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (by simpa [Real.norm_eq_abs] using (hhC t ht).trans (le_abs_self C))
  have hFh :
      Integrable (fun t : ℝ => Real.exp (-x * t) * (t ^ s * h t))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [mul_assoc] using hker1.mul_bdd hh_aesm hh_bound
  have hIntegral :
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
        = a₀ * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (s - 1))
          + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t) := by
    calc
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
          = ∫ t in Ioi (0 : ℝ),
              a₀ * (Real.exp (-x * t) * t ^ (s - 1))
                + Real.exp (-x * t) * (t ^ s * h t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t ht
            have ht_pos : 0 < t := ht
            have hpow : t ^ (s - 1) * t = t ^ s := by
              rw [← Real.rpow_add_one ht_pos.ne' (s - 1)]
              ring_nf
            have hpowh : t ^ (s - 1) * (t * h t) = t ^ s * h t := by
              rw [← mul_assoc, hpow]
            calc
              Real.exp (-x * t) * (t ^ (s - 1) * g t)
                  = Real.exp (-x * t) * (t ^ (s - 1) * (a₀ + t * h t)) := by
                    rw [hsplit t ht]
              _ = a₀ * (Real.exp (-x * t) * t ^ (s - 1))
                    + Real.exp (-x * t) * (t ^ s * h t) := by
                    rw [mul_add, hpowh]
                    ring
      _ = (∫ t in Ioi (0 : ℝ), a₀ * (Real.exp (-x * t) * t ^ (s - 1)))
            + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t) := by
            rw [MeasureTheory.integral_add hF0 hFh]
      _ = a₀ * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (s - 1))
            + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t) := by
            rw [integral_const_mul]
  have hmoment := integral_exp_neg_mul_rpow_Ioi (s := s) (x := x) hs hx
  have hxpow : x ^ s * x ^ (-s) = 1 := by
    rw [Real.rpow_neg hx.le s]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hx s))
  have hxs1 : x * x ^ s = x ^ (s + 1) := by
    rw [Real.rpow_add_one hx.ne' s]
    ring
  have hpoint :
      x * (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
          - a₀ * Real.Gamma s)
        = x ^ (s + 1) * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + 1) - 1) * h t)) := by
    calc
      x * (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
            - a₀ * Real.Gamma s)
          = x * (x ^ s * (a₀ * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (s - 1))
              + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))
            - a₀ * Real.Gamma s) := by
            rw [hIntegral]
      _ = x * (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))) := by
            rw [hmoment]
            calc
              x * (x ^ s * (a₀ * (Real.Gamma s * x ^ (-s))
                  + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))
                - a₀ * Real.Gamma s)
                  = x * ((a₀ * Real.Gamma s) * (x ^ s * x ^ (-s))
                      + x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))
                      - a₀ * Real.Gamma s) := by
                    ring
              _ = x * ((a₀ * Real.Gamma s) * 1
                      + x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))
                      - a₀ * Real.Gamma s) := by
                    rw [hxpow]
              _ = x * (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t))) := by
                    ring
      _ = x ^ (s + 1) * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ s * h t)) := by
            rw [← mul_assoc, hxs1]
      _ = x ^ (s + 1) * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + 1) - 1) * h t)) := by
            ring_nf
  exact hpoint.symm

open Finset in
/-- N-term Watson lemma on `(0, ∞)`.
Reference: DLMF §2.3 (Watson's lemma), N-term asymptotic series. -/
theorem watson_series {s : ℝ} (hs : 0 < s) {g h : ℝ → ℝ} {a : ℕ → ℝ} {N : ℕ} {aN C : ℝ}
    (hsplit : ∀ t ∈ Ioi (0:ℝ), g t = (∑ k ∈ range N, a k * t ^ k) + t ^ N * h t)
    (hhm : Measurable h)
    (hhC : ∀ t ∈ Ioi (0:ℝ), |h t| ≤ C)
    (hhlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 aN)) :
    Tendsto (fun x : ℝ => x ^ (N : ℝ) *
        (x ^ s * (∫ t in Ioi (0:ℝ), Real.exp (-x * t) * (t ^ (s-1) * g t))
          - ∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ))))
      atTop (𝓝 (aN * Real.Gamma (s + N))) := by
  have hsN : 0 < s + N := by
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg N)
  have hw := watson_leading (s := s + N) hsN (g := h) (a₀ := aN) (C := C) hhm hhC hhlim
  refine hw.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hpow_nat (t : ℝ) (ht_pos : 0 < t) (k : ℕ) :
      t ^ (s - 1) * t ^ k = t ^ ((s + k) - 1) := by
    calc
      t ^ (s - 1) * t ^ k = t ^ (s - 1) * t ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
      _ = t ^ ((s - 1) + (k : ℝ)) := by
        rw [← Real.rpow_add ht_pos]
      _ = t ^ ((s + k) - 1) := by
        congr 1
        ring
  have hker_on (k : ℕ) :
      IntegrableOn (fun t : ℝ => Real.exp (-x * t) * t ^ ((s + k) - 1)) (Ioi (0 : ℝ)) := by
    have hsk : -1 < (s + k) - 1 := by
      have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (s + k) - 1) (b := x)
      hsk (by norm_num) hx
    exact h.congr_fun (fun t ht => by
      rw [Real.rpow_one]
      ring) measurableSet_Ioi
  have hFpart (k : ℕ) (_hk : k ∈ range N) :
      Integrable (fun t : ℝ => a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using (hker_on k).integrable.const_mul (a k)
  have hFsum :
      Integrable
        (fun t : ℝ => ∑ k ∈ range N, a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact integrable_finsetSum (range N) hFpart
  have hkerN :
      Integrable (fun t : ℝ => Real.exp (-x * t) * t ^ ((s + N) - 1))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn] using hker_on N
  have hh_aesm : AEStronglyMeasurable h (volume.restrict (Ioi (0 : ℝ))) :=
    hhm.aestronglyMeasurable
  have hh_bound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖h t‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (by simpa [Real.norm_eq_abs] using (hhC t ht).trans (le_abs_self C))
  have hFh :
      Integrable (fun t : ℝ => Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t))
        (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [mul_assoc] using hkerN.mul_bdd hh_aesm hh_bound
  have hIntegral :
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
        = (∑ k ∈ range N,
            a k * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ ((s + k) - 1)))
          + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
    calc
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
          = ∫ t in Ioi (0 : ℝ),
              (∑ k ∈ range N, a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
                + Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t ht
            have ht_pos : 0 < t := ht
            have hsum :
                t ^ (s - 1) * (∑ k ∈ range N, a k * t ^ k)
                  = ∑ k ∈ range N, a k * t ^ ((s + k) - 1) := by
              rw [mul_sum]
              refine sum_congr rfl ?_
              intro k hk
              calc
                t ^ (s - 1) * (a k * t ^ k)
                    = a k * (t ^ (s - 1) * t ^ k) := by
                      ring
                _ = a k * t ^ ((s + k) - 1) := by
                      rw [hpow_nat t ht_pos k]
            have hrem :
                t ^ (s - 1) * (t ^ N * h t) = t ^ ((s + N) - 1) * h t := by
              rw [← mul_assoc, hpow_nat t ht_pos N]
            have hsum_exp :
                Real.exp (-x * t) * (∑ k ∈ range N, a k * t ^ ((s + k) - 1))
                  = ∑ k ∈ range N, a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)) := by
              rw [mul_sum]
              refine sum_congr rfl ?_
              intro k hk
              ring
            calc
              Real.exp (-x * t) * (t ^ (s - 1) * g t)
                  = Real.exp (-x * t) *
                      (t ^ (s - 1) *
                        ((∑ k ∈ range N, a k * t ^ k) + t ^ N * h t)) := by
                    rw [hsplit t ht]
              _ = Real.exp (-x * t) *
                    ((∑ k ∈ range N, a k * t ^ ((s + k) - 1))
                      + t ^ ((s + N) - 1) * h t) := by
                    rw [mul_add, hsum, hrem]
              _ = (∑ k ∈ range N, a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
                    + Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
                    rw [mul_add, hsum_exp]
      _ = (∫ t in Ioi (0 : ℝ),
              ∑ k ∈ range N, a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
            + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
            rw [MeasureTheory.integral_add hFsum hFh]
      _ = (∑ k ∈ range N,
              ∫ t in Ioi (0 : ℝ), a k * (Real.exp (-x * t) * t ^ ((s + k) - 1)))
            + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
            rw [MeasureTheory.integral_finsetSum (range N) hFpart]
      _ = (∑ k ∈ range N,
              a k * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ ((s + k) - 1)))
            + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t) := by
            congr 1
            refine sum_congr rfl ?_
            intro k hk
            rw [integral_const_mul]
  have hmoment (k : ℕ) :
      (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ ((s + k) - 1))
        = Real.Gamma (s + k) * x ^ (-(s + k)) := by
    have hsk : 0 < s + k := by
      have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    exact integral_exp_neg_mul_rpow_Ioi (s := s + k) (x := x) hsk hx
  have hxpow (k : ℕ) :
      x ^ s * x ^ (-(s + k)) = x ^ (-(k : ℝ)) := by
    calc
      x ^ s * x ^ (-(s + k)) = x ^ (s + (-(s + k))) := by
        rw [← Real.rpow_add hx]
      _ = x ^ (-(k : ℝ)) := by
        congr 1
        ring
  have hxN : x ^ (N : ℝ) * x ^ s = x ^ (s + N) := by
    calc
      x ^ (N : ℝ) * x ^ s = x ^ ((N : ℝ) + s) := by
        rw [← Real.rpow_add hx]
      _ = x ^ (s + N) := by
        congr 1
        ring
  have hscaled :
      x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
        = (∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)))
          + x ^ s *
            (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t)) := by
    calc
      x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
          = x ^ s *
              ((∑ k ∈ range N,
                  a k * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ ((s + k) - 1)))
                + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) *
                    (t ^ ((s + N) - 1) * h t)) := by
            rw [hIntegral]
      _ = x ^ s *
              ((∑ k ∈ range N, a k * (Real.Gamma (s + k) * x ^ (-(s + k))))
                + ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) *
                    (t ^ ((s + N) - 1) * h t)) := by
            congr 1
            congr 1
            refine sum_congr rfl ?_
            intro k hk
            rw [hmoment k]
      _ = (∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)))
            + x ^ s *
              (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) *
                (t ^ ((s + N) - 1) * h t)) := by
            rw [mul_add, mul_sum]
            congr 1
            refine sum_congr rfl ?_
            intro k hk
            calc
              x ^ s * (a k * (Real.Gamma (s + k) * x ^ (-(s + k))))
                  = a k * Real.Gamma (s + k) * (x ^ s * x ^ (-(s + k))) := by
                    ring
              _ = a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)) := by
                    rw [hxpow k]
  have hpoint :
      x ^ (N : ℝ) *
          (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
            - ∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)))
        = x ^ (s + N) *
            (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t)) := by
    calc
      x ^ (N : ℝ) *
          (x ^ s * (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ (s - 1) * g t))
            - ∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)))
          = x ^ (N : ℝ) *
              (((∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ)))
                  + x ^ s *
                    (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) *
                      (t ^ ((s + N) - 1) * h t)))
                - ∑ k ∈ range N, a k * Real.Gamma (s + k) * x ^ (-(k : ℝ))) := by
            rw [hscaled]
      _ = x ^ (N : ℝ) *
            (x ^ s *
              (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t))) := by
            ring
      _ = x ^ (s + N) *
            (∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (t ^ ((s + N) - 1) * h t)) := by
            rw [← mul_assoc, hxN]
  exact hpoint.symm

end PicardLefschetz
