import FLMF.Frameworks.Hypergeometric.Tricomi
import FLMF.Functions.IncompleteGamma.Def
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Upper incomplete Γ as a Tricomi-`U` instance (bridge — DLMF 8.4.16)

* `upperGamma_eq_tricomiU` — `Γ(a,x) = e^{−x} x^a · U(1; 1+a; x)`, for `a > 0`,
  `x > 0`.

This is the integer-`b` payoff of defining `U` by its integral representation
(here `b = 1+a` is unrestricted): both sides are honest real half-line
integrals, related by the affine substitution `s = x(1+t)`, which sends
`U(1;1+a;x) = ∫₀^∞ e^{−xt}(1+t)^{a−1} dt` (since `Γ(1)=1`, `t⁰=1`) to
`e^x x^{−a} ∫ₓ^∞ e^{−s} s^{a−1} ds = e^x x^{−a} Γ(a,x)`.
-/

noncomputable section

open MeasureTheory Real Set Filter
open FLMF.Hypergeometric

namespace FLMF.IncompleteGamma

/-- The Tricomi `U(1;1+a;·)` integral collapses (the `t^{a−1}` factor has
`a = 1`, so `t⁰ = 1`, and `Γ(1) = 1`): `U(1;1+a;x) = ∫₀^∞ e^{−xt}(1+t)^{a−1} dt`. -/
-- no-dlmf: collapse of the Tricomi-U integrand, helper for upperGamma_eq_tricomiU
theorem tricomiU_one_succ (a x : ℝ) :
    tricomiU 1 (1 + a) x = ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (1 + t) ^ (a - 1) := by
  unfold tricomiU
  rw [Real.Gamma_one, inv_one, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  unfold tricomiIntegrand
  rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one,
    show (1 + a) - 1 - 1 = a - 1 by ring]

-- no-dlmf: chain link 8.5.3 (assembled in upperGamma_eq_tricomiU)
/-- `Γ(a,x) = e^{−x}·U(1−a; 1−a; x)` for `x > 0` and `a < 1` (so that `1 − a > 0`,
needed for `tricomiU (1-a) (1-a) x`'s own defining integral — see `tricomiU` — to
be the genuine value rather than its junk `0`) — the Kummer-reflected Tricomi form
of DLMF 8.5.3. This needs the general `U`-Kummer transformation (DLMF 13.2.41,
`z^{1-b} U(1+a-b,2-b,z) = U(a,b,z)`), not yet in the codebase; the `a = 0`/`a = 1`
route used for the other member (`upperGamma_eq_tricomiU`'s heavy lemma) does not
reach this reflected form. -/
theorem upperGamma_eq_tricomiU_reflected {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    upperGamma a x = Real.exp (-x) * tricomiU (1 - a) (1 - a) x := by
  sorry

/-- **Upper incomplete Γ as a Tricomi `U`** (DLMF 8.5.3): `Γ(a,x) = e^{−x}·U(1−a;
1−a; x) = e^{−x} x^a · U(1; 1+a; x)` for `x > 0` and `a < 1` (the full two-link
chain DLMF gives; the second member alone — `upperGamma_eq_tricomiU_reflected`'s
target — needs no constraint on `a`, but the first requires `a < 1` for
`U(1−a,1−a,x)`'s defining integral to converge).

DAG: E-8.5.3.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem upperGamma_eq_tricomiU {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    upperGamma a x = Real.exp (-x) * tricomiU (1 - a) (1 - a) x ∧
    Real.exp (-x) * tricomiU (1 - a) (1 - a) x = Real.exp (-x) * x ^ a * tricomiU 1 (1 + a) x := by
  have hheavy : upperGamma a x = Real.exp (-x) * x ^ a * tricomiU 1 (1 + a) x := by
    set g : ℝ → ℝ := fun s => Real.exp (-s) * s ^ (a - 1) with hg
    set f : ℝ → ℝ := fun t => x * (1 + t) with hf
    have hxpow : x * x ^ (a - 1) = x ^ a := by
      rw [Real.rpow_sub hx, Real.rpow_one, mul_div_cancel₀ _ hx.ne']
    -- images of the substitution land in the positive axis / above `x`
    have himg_Ioi : f '' Ioi 0 ⊆ Ioi 0 := by
      rintro s ⟨t, ht, rfl⟩
      exact mul_pos hx (by have := mem_Ioi.mp ht; linarith)
    have himg_Ici : f '' Ici 0 ⊆ Ici x := by
      rintro s ⟨t, ht, rfl⟩
      exact le_mul_of_one_le_right hx.le (by have := mem_Ici.mp ht; linarith)
    -- change of variables `s = x(1+t)` on the half-line
    have hsub : (∫ t in Ioi (0 : ℝ), (g ∘ f) t * x) = ∫ s in Ioi x, g s := by
      have hf_cont : ContinuousOn f (Ici 0) :=
        (continuous_const.mul (continuous_const.add continuous_id)).continuousOn
      have hf_top : Tendsto f atTop atTop := by
        refine Filter.Tendsto.const_mul_atTop hx ?_
        exact tendsto_atTop_add_const_left atTop 1 tendsto_id
      have hf_deriv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f x (Ioi t) t := by
        intro t _
        have : HasDerivAt f x t := by
          have h := (((hasDerivAt_id t).const_add (1 : ℝ)).const_mul x)
          simpa using h
        exact this.hasDerivWithinAt
      have hg_cont_Ioi : ContinuousOn g (Ioi 0) := by
        refine ContinuousOn.mul ?_ ?_
        · exact (Real.continuous_exp.comp continuous_neg).continuousOn
        · exact continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (mem_Ioi.mp hs))
      have hg_cont : ContinuousOn g (f '' Ioi 0) := hg_cont_Ioi.mono himg_Ioi
      -- `g` is integrable on `[x, ∞)` for any `a` (no singularity at `0`; exp decay)
      have hg_Icix : IntegrableOn g (Ici x) := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        refine integrable_of_isBigO_exp_neg one_half_pos ?_
          (Real.Gamma_integrand_isLittleO (a - 1)).isBigO
        refine ContinuousOn.mul (Real.continuous_exp.comp continuous_neg).continuousOn ?_
        exact continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt (lt_of_lt_of_le hx hs))
      have hg1 : IntegrableOn g (f '' Ici 0) := hg_Icix.mono_set himg_Ici
      have hg2 : IntegrableOn (fun t => (g ∘ f) t * x) (Ici 0) := by
        have hbase := tricomiU_integrand_integrableOn (a := 1) (b := 1 + a) (z := x) one_pos hx
        have hconst : IntegrableOn
            (fun t => (Real.exp (-x) * x ^ a) * tricomiIntegrand 1 (1 + a) x t) (Ioi 0) :=
          hbase.const_mul _
        rw [← integrableOn_Ici_iff_integrableOn_Ioi] at hconst
        refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ici
        have ht0 : (0 : ℝ) ≤ t := mem_Ici.mp ht
        have h1t : (0 : ℝ) < 1 + t := by linarith
        unfold tricomiIntegrand
        simp only [hg, hf, Function.comp_apply]
        rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one,
          show (1 + a) - 1 - 1 = a - 1 by ring,
          Real.mul_rpow hx.le h1t.le,
          show -(x * (1 + t)) = -x + -x * t by ring, Real.exp_add, ← hxpow]
        ring
      have := integral_comp_mul_deriv_Ioi hf_cont hf_top hf_deriv hg_cont hg1 hg2
      rwa [show f 0 = x by simp [hf]] at this
    -- assemble: rewrite both integrals and cancel `e^{±x} x^{±a}`
    have hUint : Real.exp (-x) * x ^ a * tricomiU 1 (1 + a) x
        = Real.exp (-x) * x ^ a * ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * (1 + t) ^ (a - 1) := by
      rw [tricomiU_one_succ]
    rw [hUint]
    -- the `(g ∘ f) t * x` integrand equals `e^{−x} x^a · (U-integrand)` pointwise on `Ioi 0`
    have hpt : ∀ t ∈ Ioi (0 : ℝ), (g ∘ f) t * x
        = (Real.exp (-x) * x ^ a) * (Real.exp (-x * t) * (1 + t) ^ (a - 1)) := by
      intro t ht
      have h1t : (0 : ℝ) < 1 + t := by have := mem_Ioi.mp ht; linarith
      simp only [hg, hf, Function.comp_apply]
      rw [Real.mul_rpow hx.le h1t.le,
        show -(x * (1 + t)) = -x + -x * t by ring, Real.exp_add, ← hxpow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
    -- `upperGamma a x = ∫_{Ioi x} g`
    rw [upperGamma, ← hsub]
  have hlink1 := upperGamma_eq_tricomiU_reflected ha hx
  exact ⟨hlink1, hlink1.symm.trans hheavy⟩

end FLMF.IncompleteGamma
