import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Identity-theorem transfer from the real axis

Complexifying a real special-function identity is a recurring FLMF move: the
handbook states an identity for a complex variable `z`, the Lean proof is run on
the real axis (where the real-analysis toolkit lives), and the complex statement
is then recovered from the identity theorem — two entire functions that agree on
`ℝ ⊆ ℂ` agree everywhere, because `ℝ` accumulates at interior points of `ℂ`.

That argument was previously re-run by hand at every call site
(`Functions/Gamma/Ch5QGamma`, `Functions/Gamma/DigammaSeries`, …, each with its
own accumulating sequence).  This module proves it once:

* `FLMF.Methods.eqOn_of_entire_of_eqOn_real` — pointwise form.
* `FLMF.Methods.eq_of_entire_of_eqOn_real` — the `funext`-ed form `f = g`.

The accumulation witness is the sequence `1/(n+1) → 0`, which lies in
`𝓝[≠] (0 : ℂ)`; `Set.univ` is preconnected, so
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` propagates the agreement
from that cluster point to all of `ℂ`.
-/

open Filter Topology

namespace FLMF.Methods

-- no-dlmf: reusable identity-theorem meta-lemma, not a DLMF display
/-- **Identity theorem, real-axis form (pointwise).**  Two entire functions
`f, g : ℂ → ℂ` that agree at every real number agree at every complex number.

The reals `1/(n+1)` accumulate at `0` inside `𝓝[≠] (0 : ℂ)`, and `Set.univ` is
preconnected, so the agreement propagates by
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. -/
theorem eqOn_of_entire_of_eqOn_real {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) (z : ℂ) : f z = g z := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hU : IsPreconnected (Set.univ : Set ℂ) := isPreconnected_univ
  -- the real sequence `1/(n+1)` tends to `0` and never equals `0`
  have hseq : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h0
    · refine Eventually.of_forall (fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w :=
    hseq.frequently (Eventually.frequently (Eventually.of_forall fun n => h _))
  exact hfa.eqOn_of_preconnected_of_frequently_eq hga hU (Set.mem_univ 0) hfreq (Set.mem_univ z)

-- no-dlmf: reusable identity-theorem meta-lemma, not a DLMF display
/-- **Identity theorem, real-axis form (functional).**  Two entire functions
agreeing on `ℝ ⊆ ℂ` are equal. -/
theorem eq_of_entire_of_eqOn_real {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) : f = g :=
  funext fun z => eqOn_of_entire_of_eqOn_real hf hg h z

end FLMF.Methods
