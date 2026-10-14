import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Analyticity of parametric integrals

Integral representations are the standard way a special function is continued
off the region where its defining series converges, and the standard way two
representations are identified: prove the identity on a real ray, show both
sides are analytic on a connected open set, invoke the identity theorem.  The
analytic half of that argument is always the same computation — differentiate
under the integral sign with a *locally* uniform integrable majorant for the
parameter derivative — and it was previously being re-run by hand at every
call site (`Functions/Gamma/Ch5Tables`, `Functions/Gamma/Ch5BetaCF`,
`Functions/Zeta/ZetaDerivNegOne`).

This module proves that computation once.  The engine is
`analyticOnNhd_integral_of_locallyDominated`: Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` at each point of an open set
`U ⊆ ℂ`, packaged through `analyticOnNhd_iff_differentiableOn` (holomorphic on
an open set ⟹ analytic, by Cauchy's integral formula).

The domination hypothesis is deliberately **local**: the caller only supplies,
for each parameter `a ∈ U`, *some* ball around `a` on which the parameter
derivative admits an integrable majorant.  A global majorant on `U` normally
does not exist — for `∫₀^∞ e^{-at}g(t) dt` on `{0 < Re a}` the majorant
`t·e^{-σt}|g(t)|` degenerates as `σ ↓ 0` — which is exactly why the local form
is the reusable one.

Three corollaries put the local domination in the shape the integral
representations of DLMF Ch 5–7 actually come in, so that a caller never has to
manipulate balls:

* `analyticOnNhd_integral_Ioi_halfPlane` — on `{a | c < a.re}`, majorants
  indexed by the closed sub-half-planes `{a | σ ≤ a.re}`, `σ > c`.
* `analyticOnNhd_integral_strip` / `analyticOnNhd_integral_Ioi_strip` — on the
  open vertical strip `{a | c₁ < a.re ∧ a.re < c₂}`, majorants indexed by the
  closed substrips `{a | σ₁ ≤ a.re ∧ a.re ≤ σ₂}`, `c₁ < σ₁ ≤ σ₂ < c₂`.  This is
  the two-sided domination a Mellin kernel `t^{a-1}` requires and the half-plane
  form cannot express; the first is stated for an arbitrary measure (take
  `μ = volume` for a whole-real-line integral), the second is its
  `volume.restrict (Ioi d)` packaging.
* `analyticOnNhd_integral_Ioi_sector` — on the open sector
  `{a | a ≠ 0 ∧ |arg a| < θ}` (`θ ≤ π`), majorants indexed by the closed
  truncated subsectors `{a | |arg a| ≤ φ, ρ ≤ ‖a‖ ≤ R}`, `φ < θ`, `ρ > 0`.

The engine is stated for an arbitrary measure `μ`; taking
`μ = volume.restrict (Set.Ioi c)` turns `∫ t, f a t ∂μ` into the half-line
integral `∫ t in Set.Ioi c, f a t` (that is the definition of the set-integral
notation, so the two forms are interchangeable without any rewriting), and
`Integrable · μ` into `IntegrableOn · (Set.Ioi c)`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace FLMF.Methods

-- no-dlmf: reusable differentiation-under-the-integral meta-lemma, not a DLMF display
/-- **Analyticity of a parametric integral under local domination.**

If, on an open set `U ⊆ ℂ`,

* `f a` is a.e.-strongly-measurable and integrable for each parameter `a ∈ U`,
* `f' a` is a.e.-strongly-measurable for each `a ∈ U`,
* for a.e. `t`, the map `z ↦ f z t` has derivative `f' a t` at every `a ∈ U`,
* and every `a ∈ U` has a ball around it on which `‖f' · t‖` admits an
  integrable majorant (uniformly in the parameter, for a.e. `t`),

then the parametric integral `a ↦ ∫ t, f a t ∂μ` is analytic on a neighborhood
of every point of `U`.

Differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) gives complex
differentiability at each point of `U`; Cauchy's integral formula
(`analyticOnNhd_iff_differentiableOn`) upgrades that to analyticity.

Note the quantifier order in `hf_deriv`: the almost-everywhere quantifier is
outside the quantifier over the parameter, since the null set may not be chosen
after the parameter.  In practice the derivative statement holds for *every*
`t` in the domain of integration, so this is discharged by `filter_upwards`. -/
theorem analyticOnNhd_integral_of_locallyDominated
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set ℂ} {f f' : ℂ → α → ℂ}
    (hU : IsOpen U)
    (hf_meas : ∀ a ∈ U, AEStronglyMeasurable (f a) μ)
    (hf_int : ∀ a ∈ U, Integrable (f a) μ)
    (hf'_meas : ∀ a ∈ U, AEStronglyMeasurable (f' a) μ)
    (hf_deriv : ∀ᵐ t ∂μ, ∀ a ∈ U, HasDerivAt (fun z : ℂ => f z t) (f' a t) a)
    (hdom : ∀ a ∈ U, ∃ r > 0, ∃ bound : α → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball a r, ‖f' z t‖ ≤ bound t) :
    AnalyticOnNhd ℂ (fun a => ∫ t, f a t ∂μ) U := by
  rw [Complex.analyticOnNhd_iff_differentiableOn hU]
  intro a₀ ha₀
  obtain ⟨r, hr, bound, hbound_int, hbound⟩ := hdom a₀ ha₀
  have hs : Metric.ball a₀ r ∩ U ∈ 𝓝 a₀ :=
    Filter.inter_mem (Metric.ball_mem_nhds a₀ hr) (hU.mem_nhds ha₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := f') (x₀ := a₀) (s := Metric.ball a₀ r ∩ U) (bound := bound)
    hs
    (by filter_upwards [hU.mem_nhds ha₀] with z hz using hf_meas z hz)
    (hf_int a₀ ha₀)
    (hf'_meas a₀ ha₀)
    (by filter_upwards [hbound] with t ht z hz using ht z hz.1)
    hbound_int
    (by filter_upwards [hf_deriv] with t ht z hz using ht z hz.2)
  exact key.2.differentiableAt.differentiableWithinAt

-- no-dlmf: half-plane packaging of the local-domination engine, support lemma
/-- **Half-plane form.**  The parametric half-line integral
`a ↦ ∫_c^∞ f a t dt` is analytic on the open half-plane `{a | c < a.re}` as
soon as the parameter derivative admits an integrable majorant on each closed
sub-half-plane `{a | σ ≤ a.re}` with `σ > c`.

This is the shape the Laplace-type integral representations come in: a
majorant valid for `σ ≤ Re a` is what an exponential kernel `e^{-at}`
naturally produces, and the ball extraction of
`analyticOnNhd_integral_of_locallyDominated` is done here once and for all
(`Metric.ball a₀ ((a₀.re - c)/2) ⊆ {σ ≤ ·.re}` for `σ = (c + a₀.re)/2`). -/
theorem analyticOnNhd_integral_Ioi_halfPlane {c d : ℝ} {f f' : ℂ → ℝ → ℂ}
    (hf_meas : ∀ a : ℂ, c < a.re → AEStronglyMeasurable (f a) (volume.restrict (Ioi d)))
    (hf_int : ∀ a : ℂ, c < a.re → IntegrableOn (f a) (Ioi d))
    (hf'_meas : ∀ a : ℂ, c < a.re → AEStronglyMeasurable (f' a) (volume.restrict (Ioi d)))
    (hf_deriv : ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, c < a.re →
      HasDerivAt (fun z : ℂ => f z t) (f' a t) a)
    (hdom : ∀ σ : ℝ, c < σ → ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi d) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, σ ≤ a.re → ‖f' a t‖ ≤ bound t) :
    AnalyticOnNhd ℂ (fun a => ∫ t in Ioi d, f a t) {a : ℂ | c < a.re} := by
  have hU : IsOpen {a : ℂ | c < a.re} := isOpen_lt continuous_const Complex.continuous_re
  refine analyticOnNhd_integral_of_locallyDominated hU (fun a ha => hf_meas a ha)
    (fun a ha => hf_int a ha) (fun a ha => hf'_meas a ha) ?_ ?_
  · filter_upwards [hf_deriv] with t ht a ha using ht a ha
  · intro a₀ ha₀
    have ha₀' : c < a₀.re := ha₀
    obtain ⟨bound, hbound_int, hbound⟩ := hdom ((c + a₀.re) / 2) (by linarith)
    refine ⟨(a₀.re - c) / 2, by linarith, bound, hbound_int, ?_⟩
    filter_upwards [hbound] with t ht z hz
    refine ht z ?_
    have h1 : ‖z - a₀‖ < (a₀.re - c) / 2 := by
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : |(z - a₀).re| ≤ ‖z - a₀‖ := Complex.abs_re_le_norm _
    have h3 : |z.re - a₀.re| < (a₀.re - c) / 2 := by
      simpa [Complex.sub_re] using lt_of_le_of_lt h2 h1
    have h4 := (abs_lt.mp h3).1
    linarith

-- no-dlmf: strip packaging of the local-domination engine, support lemma
/-- **Strip form.**  The parametric integral `a ↦ ∫ t, f a t ∂μ` is analytic on the
open vertical strip `{a | c₁ < a.re ∧ a.re < c₂}` as soon as the parameter
derivative admits an integrable majorant on each closed substrip
`{a | σ₁ ≤ a.re ∧ a.re ≤ σ₂}` with `c₁ < σ₁ ≤ σ₂ < c₂`.

This is the shape a Mellin-type kernel `t^{a-1}` comes in.  Such a kernel needs
domination from *both* sides — on `(0, ∞)` the majorant is
`t^{σ₁-1} + t^{σ₂-1}`, small `t` being controlled by the left edge of the
substrip and large `t` by the right edge — which the one-sided
`analyticOnNhd_integral_Ioi_halfPlane` cannot express.

The strip is the intersection of two open half-planes, hence open; the ball
extraction of `analyticOnNhd_integral_of_locallyDominated` is done here once and
for all, with radius `min (a₀.re - c₁) (c₂ - a₀.re) / 2` and substrip
`σ₁ = (c₁ + a₀.re)/2`, `σ₂ = (a₀.re + c₂)/2`.

No hypothesis `c₁ < c₂` is needed: if the strip is empty the conclusion is
vacuous, and at a point of the strip the two edge inequalities are available.

Stated for an arbitrary measure `μ`, so that `μ = volume` gives the whole-line
integral `∫ t, f a t` and `μ = volume.restrict (Ioi d)` the half-line form
packaged as `analyticOnNhd_integral_Ioi_strip`. -/
theorem analyticOnNhd_integral_strip
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {c₁ c₂ : ℝ} {f f' : ℂ → α → ℂ}
    (hf_meas : ∀ a : ℂ, c₁ < a.re → a.re < c₂ → AEStronglyMeasurable (f a) μ)
    (hf_int : ∀ a : ℂ, c₁ < a.re → a.re < c₂ → Integrable (f a) μ)
    (hf'_meas : ∀ a : ℂ, c₁ < a.re → a.re < c₂ → AEStronglyMeasurable (f' a) μ)
    (hf_deriv : ∀ᵐ t ∂μ, ∀ a : ℂ, c₁ < a.re → a.re < c₂ →
      HasDerivAt (fun z : ℂ => f z t) (f' a t) a)
    (hdom : ∀ σ₁ σ₂ : ℝ, c₁ < σ₁ → σ₁ ≤ σ₂ → σ₂ < c₂ →
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ᵐ t ∂μ, ∀ a : ℂ, σ₁ ≤ a.re → a.re ≤ σ₂ → ‖f' a t‖ ≤ bound t) :
    AnalyticOnNhd ℂ (fun a => ∫ t, f a t ∂μ) {a : ℂ | c₁ < a.re ∧ a.re < c₂} := by
  have hU : IsOpen {a : ℂ | c₁ < a.re ∧ a.re < c₂} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  refine analyticOnNhd_integral_of_locallyDominated hU (fun a ha => hf_meas a ha.1 ha.2)
    (fun a ha => hf_int a ha.1 ha.2) (fun a ha => hf'_meas a ha.1 ha.2) ?_ ?_
  · filter_upwards [hf_deriv] with t ht a ha using ht a ha.1 ha.2
  · rintro a₀ ⟨hl, hr⟩
    obtain ⟨bound, hbound_int, hbound⟩ :=
      hdom ((c₁ + a₀.re) / 2) ((a₀.re + c₂) / 2) (by linarith) (by linarith) (by linarith)
    refine ⟨min (a₀.re - c₁) (c₂ - a₀.re) / 2,
      div_pos (lt_min (by linarith) (by linarith)) two_pos, bound, hbound_int, ?_⟩
    filter_upwards [hbound] with t ht z hz
    have h1 : ‖z - a₀‖ < min (a₀.re - c₁) (c₂ - a₀.re) / 2 := by
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : |(z - a₀).re| ≤ ‖z - a₀‖ := Complex.abs_re_le_norm _
    have h3 : |z.re - a₀.re| < min (a₀.re - c₁) (c₂ - a₀.re) / 2 := by
      simpa [Complex.sub_re] using lt_of_le_of_lt h2 h1
    have hml : min (a₀.re - c₁) (c₂ - a₀.re) ≤ a₀.re - c₁ := min_le_left _ _
    have hmr : min (a₀.re - c₁) (c₂ - a₀.re) ≤ c₂ - a₀.re := min_le_right _ _
    obtain ⟨h4, h5⟩ := abs_lt.mp h3
    exact ht z (by linarith) (by linarith)

-- no-dlmf: half-line strip packaging of the local-domination engine, support lemma
/-- **Half-line strip form.**  `analyticOnNhd_integral_strip` at
`μ = volume.restrict (Ioi d)`: the parametric half-line integral
`a ↦ ∫_d^∞ f a t dt` is analytic on the open vertical strip
`{a | c₁ < a.re ∧ a.re < c₂}` as soon as the parameter derivative admits an
integrable majorant on each closed substrip `{a | σ₁ ≤ a.re ∧ a.re ≤ σ₂}` with
`c₁ < σ₁ ≤ σ₂ < c₂`.

This is the shape the Mellin-type integral representations come in, where the
kernel `t^{a-1}` must be dominated at both ends of `(d, ∞)`. -/
theorem analyticOnNhd_integral_Ioi_strip {c₁ c₂ d : ℝ} {f f' : ℂ → ℝ → ℂ}
    (hf_meas : ∀ a : ℂ, c₁ < a.re → a.re < c₂ →
      AEStronglyMeasurable (f a) (volume.restrict (Ioi d)))
    (hf_int : ∀ a : ℂ, c₁ < a.re → a.re < c₂ → IntegrableOn (f a) (Ioi d))
    (hf'_meas : ∀ a : ℂ, c₁ < a.re → a.re < c₂ →
      AEStronglyMeasurable (f' a) (volume.restrict (Ioi d)))
    (hf_deriv : ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, c₁ < a.re → a.re < c₂ →
      HasDerivAt (fun z : ℂ => f z t) (f' a t) a)
    (hdom : ∀ σ₁ σ₂ : ℝ, c₁ < σ₁ → σ₁ ≤ σ₂ → σ₂ < c₂ →
      ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi d) ∧
        ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, σ₁ ≤ a.re → a.re ≤ σ₂ →
          ‖f' a t‖ ≤ bound t) :
    AnalyticOnNhd ℂ (fun a => ∫ t in Ioi d, f a t) {a : ℂ | c₁ < a.re ∧ a.re < c₂} :=
  analyticOnNhd_integral_strip hf_meas hf_int hf'_meas hf_deriv hdom

-- no-dlmf: sector packaging of the local-domination engine, support lemma
/-- **Sector form.**  The parametric half-line integral `a ↦ ∫_d^∞ f a t dt` is
analytic on the open sector `{a | a ≠ 0 ∧ |arg a| < θ}` (for `θ ≤ π`) as soon as
the parameter derivative admits an integrable majorant on each closed truncated
subsector `{a | a ≠ 0, |arg a| ≤ φ, ρ ≤ ‖a‖ ≤ R}` with `φ < θ` and `0 < ρ`.

The point `a = 0` must be excluded: `arg 0 = 0`, so `{a | |arg a| < θ}` contains
`0` but is not a neighborhood of it (every ball around `0` meets the negative
reals, where `arg = π`).  Both truncations are genuine — allowing the caller to
use `ρ ≤ ‖a‖ ≤ R` gives the weakest hypothesis, and either bound may simply be
ignored when the majorant does not need it. -/
theorem analyticOnNhd_integral_Ioi_sector {d θ : ℝ} (hθ : θ ≤ Real.pi) {f f' : ℂ → ℝ → ℂ}
    (hf_meas : ∀ a : ℂ, a ≠ 0 → |Complex.arg a| < θ →
      AEStronglyMeasurable (f a) (volume.restrict (Ioi d)))
    (hf_int : ∀ a : ℂ, a ≠ 0 → |Complex.arg a| < θ → IntegrableOn (f a) (Ioi d))
    (hf'_meas : ∀ a : ℂ, a ≠ 0 → |Complex.arg a| < θ →
      AEStronglyMeasurable (f' a) (volume.restrict (Ioi d)))
    (hf_deriv : ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, a ≠ 0 → |Complex.arg a| < θ →
      HasDerivAt (fun z : ℂ => f z t) (f' a t) a)
    (hdom : ∀ φ ρ R : ℝ, φ < θ → 0 < ρ → ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi d) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi d)), ∀ a : ℂ, a ≠ 0 → |Complex.arg a| ≤ φ →
        ρ ≤ ‖a‖ → ‖a‖ ≤ R → ‖f' a t‖ ≤ bound t) :
    AnalyticOnNhd ℂ (fun a => ∫ t in Ioi d, f a t)
      {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < θ} := by
  set U : Set ℂ := {a : ℂ | a ≠ 0 ∧ |Complex.arg a| < θ} with hU_def
  -- Every point of the sector lies in the slit plane, where `arg` is continuous.
  have hslit : ∀ a ∈ U, a ∈ Complex.slitPlane := by
    rintro a ⟨ha0, haθ⟩
    exact Complex.mem_slitPlane_iff_arg.mpr
      ⟨ne_of_lt (abs_lt.mp (lt_of_lt_of_le haθ hθ)).2, ha0⟩
  -- A neighborhood basis of truncated subsectors.
  have hnhds : ∀ a₀ ∈ U, ∀ φ ρ R : ℝ, |Complex.arg a₀| < φ → 0 < ρ → ρ < ‖a₀‖ → ‖a₀‖ < R →
      ∃ r > 0, ∀ z ∈ Metric.ball a₀ r,
        z ≠ 0 ∧ |Complex.arg z| ≤ φ ∧ ρ ≤ ‖z‖ ∧ ‖z‖ ≤ R := by
    intro a₀ ha₀ φ ρ R hφ hρ0 hρ hR
    have hcarg : ContinuousAt (fun z : ℂ => |Complex.arg z|) a₀ :=
      (Complex.continuousAt_arg (hslit a₀ ha₀)).abs
    have hcnorm : ContinuousAt (fun z : ℂ => ‖z‖) a₀ := continuous_norm.continuousAt
    have e1 : ∀ᶠ z in 𝓝 a₀, |Complex.arg z| < φ := hcarg (Iio_mem_nhds hφ)
    have e2 : ∀ᶠ z in 𝓝 a₀, ρ < ‖z‖ := hcnorm (Ioi_mem_nhds hρ)
    have e3 : ∀ᶠ z in 𝓝 a₀, ‖z‖ < R := hcnorm (Iio_mem_nhds hR)
    have : ∀ᶠ z in 𝓝 a₀, z ≠ 0 ∧ |Complex.arg z| ≤ φ ∧ ρ ≤ ‖z‖ ∧ ‖z‖ ≤ R := by
      filter_upwards [e1, e2, e3] with z h1 h2 h3
      refine ⟨?_, h1.le, h2.le, h3.le⟩
      intro hz0
      rw [hz0, norm_zero] at h2
      linarith
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp this
    exact ⟨r, hr, hsub⟩
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro a₀ ha₀
    obtain ⟨ha₀0, ha₀θ⟩ := ha₀
    have hnorm : (0:ℝ) < ‖a₀‖ := norm_pos_iff.mpr ha₀0
    obtain ⟨r, hr, hsub⟩ := hnhds a₀ ⟨ha₀0, ha₀θ⟩ ((|Complex.arg a₀| + θ) / 2) (‖a₀‖ / 2)
      (‖a₀‖ + 1) (by linarith) (by linarith) (by linarith) (by linarith)
    refine Metric.mem_nhds_iff.mpr ⟨r, hr, fun z hz => ?_⟩
    obtain ⟨hz0, hzarg, -, -⟩ := hsub z hz
    exact ⟨hz0, lt_of_le_of_lt hzarg (by linarith)⟩
  refine analyticOnNhd_integral_of_locallyDominated hUopen
    (fun a ha => hf_meas a ha.1 ha.2) (fun a ha => hf_int a ha.1 ha.2)
    (fun a ha => hf'_meas a ha.1 ha.2) ?_ ?_
  · filter_upwards [hf_deriv] with t ht a ha using ht a ha.1 ha.2
  · intro a₀ ha₀
    obtain ⟨ha₀0, ha₀θ⟩ := ha₀
    have hnorm : (0:ℝ) < ‖a₀‖ := norm_pos_iff.mpr ha₀0
    obtain ⟨bound, hbound_int, hbound⟩ :=
      hdom ((|Complex.arg a₀| + θ) / 2) (‖a₀‖ / 2) (‖a₀‖ + 1) (by linarith) (by linarith)
    obtain ⟨r, hr, hsub⟩ := hnhds a₀ ⟨ha₀0, ha₀θ⟩ ((|Complex.arg a₀| + θ) / 2) (‖a₀‖ / 2)
      (‖a₀‖ + 1) (by linarith) (by linarith) (by linarith) (by linarith)
    refine ⟨r, hr, bound, hbound_int, ?_⟩
    filter_upwards [hbound] with t ht z hz
    obtain ⟨hz0, h1, h2, h3⟩ := hsub z hz
    exact ht z hz0 h1 h2 h3

end FLMF.Methods
