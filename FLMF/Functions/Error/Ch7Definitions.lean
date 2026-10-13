import Mathlib
import FLMF.Functions.Error.Dawson
import FLMF.Functions.Error.GoodwinStaton
import FLMF.Functions.Fresnel.Basic
import FLMF.Functions.Fresnel.Limit
import FLMF.Functions.Fresnel.Complex

/-!
# DLMF §7.2 "Definitions" — statement surfaces (still-uncovered labels)

This module states the remaining DLMF §7.2 defining equations not already
covered elsewhere in FLMF:

* 7.2.9  — Fresnel limits `C(x), S(x) → 1/2` as `x → ∞`        (theorem)
* 7.2.10 — auxiliary function `f(z)` for Fresnel integrals       (theorem; real
  instance `erf_7_2_10` + complex DLMF-domain surface `cfresnel_7_2_10`)
* 7.2.11 — auxiliary function `g(z)` for Fresnel integrals       (theorem; real
  instance `erf_7_2_11` + complex DLMF-domain surface `cfresnel_7_2_11`)
* 7.2.12 — Goodwin–Staton integral `G(z) = ∫₀^∞ e^{-t²}/(t+z)dt` (definition
  `goodwinStaton`; real instance `erf_7_2_12` + complex DLMF-domain surface
  `cfresnel_7_2_12`, bridged to the definition by `cfresnel_7_2_12_goodwinStaton`)

Two further labels in this work-list are **inherently complex**; both were
originally recorded here as deferrals (see the comment block below) since FLMF's
`erf`/`erfc`/`dawson`/`fresnelC`/`fresnelS` are all REAL-valued, and both have
since been resolved elsewhere:

* 7.2.3  — the Faddeeva function `w(z) = e^{-z²} erfc(-iz)`
  (RESOLVED in `Error/Faddeeva.lean` as `faddeeva` + `erf_7_2_3`)
* 7.2.6  — the complex Fresnel integral `ℱ(z) = ∫_z^∞ e^{iπt²/2} dt`
  (RESOLVED in `Fresnel/Complex.lean` as `cfresnelScriptF` + `cfresnel_7_2_6`)

The labels 7.2.1/7.2.2/7.2.4/7.2.5/7.2.7/7.2.8 are defined elsewhere in FLMF
and are intentionally NOT restated here.
-/

/-
================================================================================
DOCUMENTED DEFERRALS (inherently complex; not faked as real theorems)
================================================================================

DLMF 7.2.3  (Faddeeva / Faddeyeva function)  [RESOLVED in Error/Faddeeva.lean as
    `faddeeva` + `erf_7_2_3`, via the complex `cerf`/`cerfc` keystone.]
    w(z) = e^{-z²} ( 1 + (2i/√π) ∫₀ᶻ e^{t²} dt ) = e^{-z²} erfc(-iz)
  (Original deferral note:) `w` is the Faddeeva function, an inherently COMPLEX entire function
  of a complex argument, defined via `erfc(-iz)` (complex error function).  FLMF
  has only the REAL `erfc : ℝ → ℝ`, so there is no honest real specialization of
  the full identity — `erfc(-iz)` evaluates the complex error function off the
  real axis.  (For real x one has w(x) = e^{-x²} + (2i/√π)·dawson(x), but the
  value is still complex.)  Needs complex erf / Faddeeva w(z), not in FLMF.

DLMF 7.2.6  (complex Fresnel integral)  [RESOLVED in Fresnel/Complex.lean as
    `cfresnelScriptF` + `cfresnel_7_2_6`, the hypothesis-free rotated-ray
    representation along `t = z + s·e^{iπ/4}`.]
    ℱ(z) = ∫_z^∞ e^{iπ t²/2} dt
  (Original deferral note:) `ℱ` is a COMPLEX-valued (entire) function defined by a contour
  integral of e^{iπt²/2}; its real/imaginary parts are 1/2 - C and 1/2 - S
  (cf. 7.2.9 below), but ℱ itself is complex.  FLMF has only the real Fresnel
  integrals `fresnelC`/`fresnelS`.  Needs a complex-valued Fresnel integral,
  not in FLMF.
================================================================================
-/

namespace FLMF.Error

open Real
open scoped Topology
open MeasureTheory

-- no-dlmf: duplicate assembly of DLMF 7.2.9; canonical surface is `fresnel_7_2_9` (Fresnel/Limit.lean)
/-- The Fresnel integrals both tend to `1/2` at `+∞`:
`lim_{x→∞} C(x) = 1/2` and `lim_{x→∞} S(x) = 1/2` (DLMF 7.2.9).

-/
theorem erf_7_2_9 :
    Filter.Tendsto FLMF.Fresnel.fresnelC Filter.atTop (𝓝 (1 / 2)) ∧
    Filter.Tendsto FLMF.Fresnel.fresnelS Filter.atTop (𝓝 (1 / 2)) :=
  ⟨FLMF.Fresnel.tendsto_fresnelC, FLMF.Fresnel.tendsto_fresnelS⟩

/-- Auxiliary Fresnel function `f`:
`f(x) = (1/2 - S(x)) cos(π x²/2) - (1/2 - C(x)) sin(π x²/2)` (DLMF 7.2.10). -/
-- no-dlmf: section-local definition of the auxiliary `f`; the identity is `erf_7_2_10`
noncomputable def fresnelAuxF (x : ℝ) : ℝ :=
  (1 / 2 - FLMF.Fresnel.fresnelS x) * Real.cos (Real.pi * x ^ 2 / 2) -
    (1 / 2 - FLMF.Fresnel.fresnelC x) * Real.sin (Real.pi * x ^ 2 / 2)

-- no-dlmf: real/narrowed restriction of DLMF 7.2.10; faithful surface is cfresnel_7_2_10
/-- Defining equation of the auxiliary Fresnel function `f`, real specialization:
`f(x) = (1/2 - S(x)) cos(π x²/2) - (1/2 - C(x)) sin(π x²/2)`.
-/
theorem erf_7_2_10 (x : ℝ) :
    fresnelAuxF x =
      (1 / 2 - FLMF.Fresnel.fresnelS x) * Real.cos (Real.pi * x ^ 2 / 2) -
        (1 / 2 - FLMF.Fresnel.fresnelC x) * Real.sin (Real.pi * x ^ 2 / 2) := by
  rfl

open FLMF.Fresnel in
-- no-dlmf: restates the definitional display DLMF 7.2.10; canonical carrier is the definition `cfresnelAuxF` (Fresnel/Complex.lean)
/-- **DLMF 7.2.10** — the auxiliary Fresnel function `f` for complex `z` (no
constraints): `f(z) = (1/2 - S(z)) cos(π z²/2) - (1/2 - C(z)) sin(π z²/2)`,
with `C`, `S` the complex Fresnel integrals.

-/
theorem cfresnel_7_2_10 (z : ℂ) :
    cfresnelAuxF z =
      (1 / 2 - cfresnelS z) * Complex.cos (Real.pi * z ^ 2 / 2) -
        (1 / 2 - cfresnelC z) * Complex.sin (Real.pi * z ^ 2 / 2) := rfl

/-- Auxiliary Fresnel function `g`:
`g(x) = (1/2 - C(x)) cos(π x²/2) + (1/2 - S(x)) sin(π x²/2)` (DLMF 7.2.11). -/
-- no-dlmf: section-local definition of the auxiliary `g`; the identity is `erf_7_2_11`
noncomputable def fresnelAuxG (x : ℝ) : ℝ :=
  (1 / 2 - FLMF.Fresnel.fresnelC x) * Real.cos (Real.pi * x ^ 2 / 2) +
    (1 / 2 - FLMF.Fresnel.fresnelS x) * Real.sin (Real.pi * x ^ 2 / 2)

-- no-dlmf: real/narrowed restriction of DLMF 7.2.11; faithful surface is cfresnel_7_2_11
/-- Defining equation of the auxiliary Fresnel function `g`, real specialization:
`g(x) = (1/2 - C(x)) cos(π x²/2) + (1/2 - S(x)) sin(π x²/2)`.
-/
theorem erf_7_2_11 (x : ℝ) :
    fresnelAuxG x =
      (1 / 2 - FLMF.Fresnel.fresnelC x) * Real.cos (Real.pi * x ^ 2 / 2) +
        (1 / 2 - FLMF.Fresnel.fresnelS x) * Real.sin (Real.pi * x ^ 2 / 2) := by
  rfl

open FLMF.Fresnel in
-- no-dlmf: restates the definitional display DLMF 7.2.11; canonical carrier is the definition `cfresnelAuxG` (Fresnel/Complex.lean)
/-- **DLMF 7.2.11** — the auxiliary Fresnel function `g` for complex `z` (no
constraints): `g(z) = (1/2 - C(z)) cos(π z²/2) + (1/2 - S(z)) sin(π z²/2)`,
with `C`, `S` the complex Fresnel integrals.

-/
theorem cfresnel_7_2_11 (z : ℂ) :
    cfresnelAuxG z =
      (1 / 2 - cfresnelC z) * Complex.cos (Real.pi * z ^ 2 / 2) +
        (1 / 2 - cfresnelS z) * Complex.sin (Real.pi * z ^ 2 / 2) := rfl

/-- **DLMF 7.2.12** — the Goodwin–Staton integral, for complex `z` with
`|ph z| < π`: `G(z) = ∫₀^∞ e^{-t²}/(t+z) dt`.

DLMF 7.2.12.
DAG: E-7.2.12.
Verified: verified (tier2)
-/
noncomputable def goodwinStaton (z : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0:ℝ), (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z)

-- no-dlmf: real/narrowed restriction of DLMF 7.2.12 (positive real axis only,
-- via convergence of truncations rather than the improper integral directly);
-- faithful surface is cfresnel_7_2_12
/-- The Goodwin–Staton integral on the positive real axis
`G(x) = ∫₀^∞ e^{-t²}/(t+x) dt` is the limit of its truncations
`G_T(x, b) = ∫₀^b e^{-t²}/(t+x) dt` as `b → ∞`, real specialization of the
Goodwin–Staton integral for `x > 0`.
-/
theorem erf_7_2_12 {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun b => FLMF.GoodwinStaton.goodwinStatonTrunc x b)
      Filter.atTop (𝓝 (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2) / (t + x))) := by
  have hcont : ContinuousOn (FLMF.GoodwinStaton.gsIntegrand x) (Set.Ioi (0:ℝ)) :=
    FLMF.GoodwinStaton.continuousOn_gsIntegrand
      (fun t ht => FLMF.GoodwinStaton.denom_pos hx (le_of_lt ht))
  have hmeas : MeasureTheory.AEStronglyMeasurable (FLMF.GoodwinStaton.gsIntegrand x)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / x) (Set.Ioi (0:ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      simpa using this.integrableOn
    exact h1.div_const x
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖FLMF.GoodwinStaton.gsIntegrand x t‖ ≤ Real.exp (-t ^ 2) / x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    have h1 : 0 ≤ FLMF.GoodwinStaton.gsIntegrand x t :=
      FLMF.GoodwinStaton.gsIntegrand_nonneg hx (le_of_lt ht)
    rw [Real.norm_of_nonneg h1]
    unfold FLMF.GoodwinStaton.gsIntegrand
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx (by linarith)
  have hInt : MeasureTheory.IntegrableOn (FLMF.GoodwinStaton.gsIntegrand x) (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.mono' hg hmeas hbound
  have htend := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hInt Filter.tendsto_id
  simpa [FLMF.GoodwinStaton.goodwinStatonTrunc] using htend

-- no-dlmf: DLMF 7.2.12 is the *definition* of the Goodwin–Staton integral
-- `G(z) = ∫₀^∞ e^{-t²}/(t+z) dt`; the proper carrier of the 7.2.12 tag is the
-- `goodwinStaton` definition above. What this lemma records is the convergence of
-- the truncations to the improper integral (the value `goodwinStaton z` unfolds to)
-- — analytic infrastructure, not the display itself. See
-- `cfresnel_7_2_12_goodwinStaton` below for the restatement in terms of `goodwinStaton`.
/-- Convergence of the truncated Goodwin–Staton integrals to the improper integral
`∫₀^∞ e^{-t²}/(t+z) dt` (the object DLMF 7.2.12 names `G(z)`), for complex `z` with
`|ph z| < π`. The domain `|ph z| < π` is encoded as "`z` is not a nonpositive real
number" (`z.im ≠ 0 ∨ 0 < z.re`), which excludes both the branch cut `(-∞,0)` and the
pole at `z = 0`. -/
theorem cfresnel_7_2_12 {z : ℂ} (hz : z.im ≠ 0 ∨ 0 < z.re) :
    Filter.Tendsto (fun b : ℝ => ∫ t in (0:ℝ)..b, (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z))
      Filter.atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z))) := by
  have hd : ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, 0 ≤ t → d ≤ ‖(t : ℂ) + z‖ := by
    rcases hz with h1 | h2
    · refine ⟨|z.im|, abs_pos.mpr h1, fun t _ => ?_⟩
      have him : ((t : ℂ) + z).im = z.im := by simp
      calc |z.im| = |((t : ℂ) + z).im| := by rw [him]
        _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _
    · refine ⟨z.re, h2, fun t ht => ?_⟩
      have hre : ((t : ℂ) + z).re = t + z.re := by simp
      calc z.re ≤ t + z.re := by linarith
        _ = ((t : ℂ) + z).re := hre.symm
        _ ≤ ‖(t : ℂ) + z‖ := Complex.re_le_norm _
  obtain ⟨d, hdpos, hdbound⟩ := hd
  have hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ) + z ≠ 0 := by
    intro t ht hzero
    have hb := hdbound t ht
    rw [hzero] at hb
    simp at hb
    linarith
  have hcont : ContinuousOn (fun t : ℝ => (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z)) (Set.Ioi (0:ℝ)) := by
    apply ContinuousOn.div
    · exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
    · fun_prop
    · intro t ht
      exact hne t (le_of_lt ht)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / d) (Set.Ioi (0:ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
      simpa using this.integrableOn
    exact h1.div_const d
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖(Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z)‖ ≤ Real.exp (-t ^ 2) / d := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    rw [norm_div]
    have h1 : ‖(Real.exp (-t ^ 2) : ℂ)‖ = Real.exp (-t ^ 2) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [h1]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdpos (hdbound t ht'.le)
  have hInt : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z))
      (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.mono' hg hmeas hbound
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hInt Filter.tendsto_id

-- no-dlmf: restates `cfresnel_7_2_12`'s conclusion using the `goodwinStaton` name;
-- `goodwinStaton z` is definitionally the improper integral `cfresnel_7_2_12` already
-- converges to, so this is not a fresh DLMF equation (that would be RFL-circular) but
-- a bridge connecting the analytic-infrastructure lemma to the named definition.
/-- The truncated Goodwin–Staton integrals converge to `goodwinStaton z`, for complex
`z` with `|ph z| < π` (same domain as `cfresnel_7_2_12`). -/
theorem cfresnel_7_2_12_goodwinStaton {z : ℂ} (hz : z.im ≠ 0 ∨ 0 < z.re) :
    Filter.Tendsto (fun b : ℝ => ∫ t in (0:ℝ)..b, (Real.exp (-t ^ 2) : ℂ) / ((t : ℂ) + z))
      Filter.atTop (𝓝 (goodwinStaton z)) :=
  cfresnel_7_2_12 hz

end FLMF.Error
