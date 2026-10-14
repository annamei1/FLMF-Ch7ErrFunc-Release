import Mathlib
import FLMF.Chapter7.FresnelBasic
import FLMF.Chapter7.FresnelComplex
import FLMF.Chapter7.Dawson
import FLMF.Chapter7.ComplexErfExtra
import FLMF.Chapter7.Definitions
import FLMF.Chapter7.Symmetry
import FLMF.Support.ExpIntegralsDefinitions
import FLMF.Support.ExpIntegralsE1Series
import FLMF.Support.ExpIntegralsLiLeading

/-!
# DLMF §7.5 — Interrelations

Statement surfaces (Phase 5) for the §7.5 "Interrelations" identities, which
relate `erf`/`erfc`, Dawson's integral `F`, the Fresnel integrals `C`, `S`, and
their auxiliary functions `f`, `g`.

FLMF's `erf`, `erfc`, `dawson`, and the Fresnel `C`, `S` are all **real-valued**.
Several §7.5 identities are intrinsically complex — they involve the complex
Fresnel function `𝓕(z) = ½(1+i) - (C(z) + iS(z))` (7.5.2), the Faddeeva function
`w(z)`, the complex variable `ζ = ½√π(1∓i)z` (7.5.7), or the complex auxiliary
combination `g(z) ± if(z)`. Those are recorded below as **documented deferrals**
rather than faked.

* 7.5.1  — Dawson's integral against the Faddeeva function and `erf` is proven at DLMF's
  full complex strength as `erf_7_5_1` (the complex `cdawson` from `ComplexErfExtra.lean`,
  `faddeeva`, `cerf`); the display is an equality chain, so the surface is the single
  two-conjunct theorem required by the chain-display convention.

* 7.5.3  — the `C(z)` reconstruction from the auxiliary `f`, `g` is proven at DLMF's
  full complex strength as `cfresnel_7_5_3`, the exact companion of `cfresnel_7_5_4`.

* 7.5.4  — the `S(z)` reconstruction from the auxiliary `f`, `g` is proven at DLMF's
  full complex strength as `cfresnel_7_5_4` (using the complex `cfresnelS`,
  `cfresnelAuxF`, `cfresnelAuxG` from `Fresnel/Complex.lean`); `erf_7_5_4` keeps the
  real specialization as a non-DLMF-tagged convenience lemma.

The remaining identities with honest real specializations are:

* 7.5.11 — `|𝓕(x)|² = f²(x) + g²(x)` for `x ≥ 0`, read as the real identity
  `(½ - C x)² + (½ - S x)² = f(x)² + g(x)²`;
* 7.5.12 — its `x ≤ 0` counterpart.

The auxiliary functions are defined here inline by their DLMF §7.2 formulas
(7.2.10, 7.2.11), which are real-valued in terms of the real `C`, `S`.

* 7.5.13 — the Goodwin–Staton integral `G(x) = √π·F(x) - ½e^{-x²}Ei(x²)` for `x > 0`.

All surfaces stated in this file are proven.
-/

namespace FLMF.Error

open Real
open FLMF.Fresnel

-- The Fresnel auxiliary functions `f`, `g` (DLMF 7.2.10/7.2.11) are the canonical
-- `FLMF.Error.fresnelAuxF`/`fresnelAuxG` from `Ch7Definitions` (imported above). We
-- reuse them here rather than redefining; the former local names `auxF`/`auxG` were
-- renamed to `fresnelAuxF`/`fresnelAuxG` to avoid a fidelity-oracle name collision with
-- the chapter-6 (Si/Ci) auxiliary functions `auxF`/`auxG` (DLMF 6.2.17/6.2.18).

/-- **DLMF 7.5.1** — Dawson's integral in terms of the Faddeeva function and the error
function: `F(z) = ½i√π(e^{-z²} - w(z)) = -½i√π e^{-z²} erf(iz)`.

The display is an equality chain with two links, so it is surfaced as a single theorem
whose conclusion is the conjunction of both links (chain-display convention).

DLMF 7.5.1.
DAG: E-7.5.1.
Numerical: N/A
Verified: verified
-/
theorem erf_7_5_1 (z : ℂ) :
    cdawson z
        = (1 / 2 : ℂ) * Complex.I * (Real.sqrt Real.pi : ℂ)
            * (Complex.exp (-z ^ 2) - faddeeva z) ∧
      cdawson z
        = -(1 / 2 : ℂ) * Complex.I * (Real.sqrt Real.pi : ℂ)
            * Complex.exp (-z ^ 2) * cerf (Complex.I * z) := by
  have hneg : cerf (-(Complex.I * z)) = -cerf (Complex.I * z) := cerf_neg _
  constructor
  · unfold cdawson faddeeva cerfc
    rw [hneg]
    ring
  · unfold cdawson
    ring

-- ---------------------------------------------------------------------------
-- 7.5.2  — DEFERRED.
-- `C(z) + iS(z) = ½(1 + i) - 𝓕(z)`.
-- This is the *definition* of the complex Fresnel function `𝓕(z)`. FLMF has no
-- complex Fresnel function (only the real `C`, `S`), so there is no real
-- specialization to state — for real `x` it merely re-expresses `𝓕(x)` and
-- carries no content about the real `C`, `S` alone. Needs complex `𝓕`, not in FLMF.
-- ---------------------------------------------------------------------------

/-- **DLMF 7.5.3** — reconstruction of the (complex) Fresnel cosine integral from the
complex auxiliary functions: `C(z) = ½ + f(z)·sin(πz²/2) - g(z)·cos(πz²/2)`, for
complex `z`.

DLMF 7.5.3.
DAG: E-7.5.3.
Numerical: N/A
Verified: verified
-/
theorem cfresnel_7_5_3 (z : ℂ) :
    FLMF.Fresnel.cfresnelC z
      = 1 / 2 + FLMF.Fresnel.cfresnelAuxF z * Complex.sin (Real.pi * z ^ 2 / 2)
          - FLMF.Fresnel.cfresnelAuxG z * Complex.cos (Real.pi * z ^ 2 / 2) := by
  unfold FLMF.Fresnel.cfresnelAuxF FLMF.Fresnel.cfresnelAuxG
  linear_combination
    ((1:ℂ)/2 - FLMF.Fresnel.cfresnelC z) * (Complex.sin_sq_add_cos_sq (Real.pi * z ^ 2 / 2))

-- no-dlmf: real/narrowed restriction of DLMF 7.5.4; faithful surface is cfresnel_7_5_4
/-- Reconstruction of the Fresnel sine integral from the auxiliary functions:
`S(x) = ½ - f(x)·cos(πx²/2) - g(x)·sin(πx²/2)`, real specialization of DLMF 7.5.4. -/
theorem erf_7_5_4 (x : ℝ) :
    fresnelS x
      = 1 / 2 - fresnelAuxF x * Real.cos (Real.pi * x ^ 2 / 2)
          - fresnelAuxG x * Real.sin (Real.pi * x ^ 2 / 2) := by
  unfold fresnelAuxF fresnelAuxG
  linear_combination ((1:ℝ)/2 - fresnelS x) * (Real.sin_sq_add_cos_sq (Real.pi * x ^ 2 / 2))

/-- **DLMF 7.5.4** — reconstruction of the (complex) Fresnel sine integral from the
complex auxiliary functions: `S(z) = ½ - f(z)·cos(πz²/2) - g(z)·sin(πz²/2)`, for
complex `z`.

DAG: E-7.5.4.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_4 (z : ℂ) :
    FLMF.Fresnel.cfresnelS z
      = 1 / 2 - FLMF.Fresnel.cfresnelAuxF z * Complex.cos (Real.pi * z ^ 2 / 2)
          - FLMF.Fresnel.cfresnelAuxG z * Complex.sin (Real.pi * z ^ 2 / 2) := by
  unfold FLMF.Fresnel.cfresnelAuxF FLMF.Fresnel.cfresnelAuxG
  linear_combination
    ((1:ℂ)/2 - FLMF.Fresnel.cfresnelS z) * (Complex.sin_sq_add_cos_sq (Real.pi * z ^ 2 / 2))

-- ---------------------------------------------------------------------------
-- 7.5.5  — DEFERRED.
-- `e^{-½πiz²} 𝓕(z) = g(z) + i f(z)`.
-- Intrinsically complex: relates the complex Fresnel `𝓕(z)` to the complex
-- combination `g(z) + i f(z)` via the complex exponential `e^{-½πiz²}`. No real
-- specialization. Needs complex `𝓕` / complex `f, g`, not in FLMF.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 7.5.6  — RESOLVED in Fresnel/Complex.lean as `cfresnel_7_5_6` (complex auxiliaries f,g).
-- `e^{±½πiz²}(g(z) ± i f(z)) = ½(1 ± i) - (C(z) ± iS(z))`.
-- Intrinsically complex (the complex combinations `C ± iS`, `g ± if` and the
-- complex exponential). No real specialization. Needs complex arithmetic, not in FLMF.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 7.5.7  — DEFERRED.
-- `ζ = ½√π(1 ∓ i)z`.
-- A *definition* of the complex variable `ζ` used by 7.5.8–7.5.10. `ζ` is complex
-- for real `z`; FLMF has no complex `ζ`. Needs the complex plane, not in FLMF.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 7.5.8  — RESOLVED in Fresnel/Complex.lean as `cfresnel_7_5_8` (complex Fresnel + cerf).
-- `C(z) ± iS(z) = ½(1 ± i) erf(ζ)`.
-- Requires the complex error function `erf(ζ)` at the complex argument
-- `ζ = ½√π(1∓i)z`. FLMF's `erf` is real-valued. Needs complex `erf`, not in FLMF.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 7.5.9  — RESOLVED in Fresnel/Complex.lean as `cfresnel_7_5_9` (complex Fresnel + faddeeva).
-- `C(z) ± iS(z) = ½(1 ± i)(1 - e^{±½πiz²} w(iζ))`.
-- Requires the Faddeeva function `w` at the complex argument `iζ`. FLMF has no
-- Faddeeva `w`. Needs complex `w(z)`, not in FLMF.
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 7.5.10 — RESOLVED in Fresnel/Complex.lean as `cfresnel_7_5_10` (complex f,g + cerfc).
-- `g(z) ± i f(z) = ½(1 ± i) e^{ζ²} erfc(ζ)`  (for `x ≥ 0`).
-- Requires the complex `erfc(ζ)` at the complex `ζ` and the complex combination
-- `g ± if`. FLMF's `erfc` is real-valued. Needs complex `erfc`, not in FLMF.
-- ---------------------------------------------------------------------------

/-- Modulus identity for the complex Fresnel function, `x ≥ 0`:
`|𝓕(x)|² = f²(x) + g²(x)` (DLMF 7.5.11). With `𝓕(x) = ½(1+i) - (C(x) + iS(x))`
(7.5.2) the left side is the real `(½ - C x)² + (½ - S x)²`, so this is an
honest real identity.

DLMF 7.5.11.
DAG: E-7.5.11.
Numerical: PASS
Verified: verified
-/
theorem erf_7_5_11 {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2 - fresnelC x) ^ 2 + (1 / 2 - fresnelS x) ^ 2
      = fresnelAuxF x ^ 2 + fresnelAuxG x ^ 2 := by
  unfold fresnelAuxF fresnelAuxG
  linear_combination (-((1:ℝ)/2 - fresnelC x)^2 - ((1:ℝ)/2 - fresnelS x)^2) * (Real.sin_sq_add_cos_sq (Real.pi * x ^ 2 / 2))

/-- Modulus identity for the complex Fresnel function, `x ≤ 0`:
`|𝓕(x)|² = 2 + f²(-x) + g²(-x) - 2√2·cos(π/4 + πx²/2)·f(-x)
  - 2√2·cos(π/4 - πx²/2)·g(-x)` (DLMF 7.5.12). With `𝓕(x) = ½(1+i) - (C(x) + iS(x))`
(7.5.2) the left side is the real `(½ - C x)² + (½ - S x)²`, so this is an honest
real identity.

DLMF 7.5.12.
DAG: E-7.5.12.
Numerical: PASS
Verified: verified
-/
theorem erf_7_5_12 {x : ℝ} (hx : x ≤ 0) :
    (1 / 2 - fresnelC x) ^ 2 + (1 / 2 - fresnelS x) ^ 2
      = 2 + fresnelAuxF (-x) ^ 2 + fresnelAuxG (-x) ^ 2
          - 2 * Real.sqrt 2 * Real.cos (Real.pi / 4 + Real.pi * x ^ 2 / 2) * fresnelAuxF (-x)
          - 2 * Real.sqrt 2 * Real.cos (Real.pi / 4 - Real.pi * x ^ 2 / 2) * fresnelAuxG (-x) := by
  obtain ⟨hC, hS⟩ := erf_7_4_5 x
  have h2 : Real.sqrt 2 * Real.cos (Real.pi/4) = 1 := by
    rw [Real.cos_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h3 : Real.sqrt 2 * Real.sin (Real.pi/4) = 1 := by
    rw [Real.sin_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hsq : Real.pi * (-x)^2/2 = Real.pi * x^2/2 := by ring_nf
  unfold fresnelAuxF fresnelAuxG
  rw [Real.cos_add, Real.cos_sub, hsq, hC, hS]
  set c := Real.cos (Real.pi * x ^ 2 / 2)
  set s := Real.sin (Real.pi * x ^ 2 / 2)
  set C := fresnelC x
  set S := fresnelS x
  have hpy : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq _
  linear_combination
    (2*(1+S+C) - ((1/2+S)^2 + (1/2+C)^2)) * hpy
  + (2*(c*((1/2+S)*c-(1/2+C)*s) + c*((1/2+C)*c+(1/2+S)*s))) * h2
  + (2*(s*((1/2+C)*c+(1/2+S)*s) - s*((1/2+S)*c-(1/2+C)*s))) * h3

/-! ### Analytic groundwork for DLMF 7.5.13 (the Goodwin–Staton integral)

The route is the first-order linear ODE satisfied by
`G(x) = ∫₀^∞ e^{-t²}/(t+x) dt`, namely `G'(x) + 2x·G(x) = √π − 1/x` (obtained by
differentiating under the integral sign and one integration by parts), which is also
satisfied by the right-hand side `√π·F(x) − ½e^{-x²}Ei(x²)`.  Hence
`Ψ(x) = e^{x²}G(x) − √π∫₀ˣe^{t²}dt + ½Ei(x²)` is constant on `(0,∞)`; the constant is
pinned to `0` by the `x → 0⁺` limit, where `G(x)` is compared with the shifted integral
`∫₀^∞ e^{-(t+x)²}/(t+x) dt = ½E₁(x²)` (the two differ by at most `√π·x`) and
`e^{x²}E₁(x²) + Ei(x²) → 0`.
-/

open MeasureTheory Set Filter Topology

-- no-dlmf: integrability of the Goodwin–Staton integrand; analytic infrastructure
private lemma gs_int1 {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / (t + x)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / x) (Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
      simpa using this.integrableOn
    exact h1.div_const x
  refine Integrable.mono' hg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht' : (0:ℝ) < t := ht
  have hden : 0 < t + x := by linarith
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx (by linarith)

-- no-dlmf: integrability of the squared-denominator variant; analytic infrastructure
private lemma gs_int2 {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / (t + x) ^ 2) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / x ^ 2) (Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
      simpa using this.integrableOn
    exact h1.div_const _
  refine Integrable.mono' hg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht' : (0:ℝ) < t := ht
  have hden : 0 < (t + x) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
  nlinarith

-- no-dlmf: integrability of the integration-by-parts term; analytic infrastructure
private lemma gs_int3 {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-t ^ 2) / (t + x)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => 2 * (t * Real.exp (-t ^ 2)) / x) (Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
      have := integrable_mul_exp_neg_mul_sq (b := (1:ℝ)) one_pos
      simpa using this.integrableOn
    exact ((h1.const_mul 2).div_const x)
  refine Integrable.mono' hg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht' : (0:ℝ) < t := ht
  have hden : 0 < t + x := by linarith
  have hnum : 0 ≤ 2 * t * Real.exp (-t ^ 2) := by positivity
  rw [Real.norm_of_nonneg (div_nonneg hnum hden.le)]
  rw [show 2 * t * Real.exp (-t ^ 2) = 2 * (t * Real.exp (-t ^ 2)) from by ring]
  exact div_le_div_of_nonneg_left (by positivity) hx (by linarith)

-- no-dlmf: integrability of the shifted Goodwin–Staton integrand; analytic infrastructure
private lemma gs_int_shift {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t + x) ^ 2) / (t + x)) (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2) / x) (Ioi (0:ℝ)) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
      simpa using this.integrableOn
    exact h1.div_const x
  refine Integrable.mono' hg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht' : (0:ℝ) < t := ht
  have hden : 0 < t + x := by linarith
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
  have h1 : Real.exp (-(t + x) ^ 2) ≤ Real.exp (-t ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(t + x) ^ 2) / (t + x) ≤ Real.exp (-t ^ 2) / (t + x) := by gcongr
  have h3 : Real.exp (-t ^ 2) / (t + x) ≤ Real.exp (-t ^ 2) / x :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hx (by linarith)
  linarith

-- no-dlmf: integrability of the `E₁` integrand on a half-line away from the pole
private lemma gs_int_e1 {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) / s) (Ioi c) := by
  have hg : IntegrableOn (fun s : ℝ => Real.exp (-s) / c) (Ioi c) := by
    have h := exp_neg_integrableOn_Ioi c (b := 1) zero_lt_one
    simp only [neg_one_mul] at h
    exact h.div_const c
  refine Integrable.mono' hg (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with s hs
  have hs' : c < s := hs
  have hs0 : 0 < s := lt_trans hc hs'
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hs0.le)]
  gcongr

-- no-dlmf: integration by parts for the Goodwin–Staton integrand; analytic infrastructure
private lemma gs_ibp {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0:ℝ), 2 * t * Real.exp (-t ^ 2) / (t + x))
      + (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x) ^ 2) = 1 / x := by
  have hderiv : ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun t : ℝ => -(Real.exp (-t ^ 2) / (t + x)))
        (2 * t * Real.exp (-t ^ 2) / (t + x) + Real.exp (-t ^ 2) / (t + x) ^ 2) t := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hden : (t + x) ≠ 0 := by intro h; nlinarith
    have hnum : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2)) (Real.exp (-t ^ 2) * (-(2 * t))) t := by
      have h1 : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * t)) t := by
        simpa using (hasDerivAt_pow 2 t).neg
      simpa using (Real.hasDerivAt_exp (-t ^ 2)).comp t h1
    have hd2 : HasDerivAt (fun t : ℝ => t + x) 1 t := by
      simpa using (hasDerivAt_id t).add_const x
    have h := (hnum.div hd2 hden).neg
    convert h using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun t : ℝ => -(Real.exp (-t ^ 2) / (t + x))) (Ici (0:ℝ)) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using hx.ne'
  have hint : IntegrableOn (fun t : ℝ => 2 * t * Real.exp (-t ^ 2) / (t + x)
      + Real.exp (-t ^ 2) / (t + x) ^ 2) (Ioi 0) := (gs_int3 hx).add (gs_int2 hx)
  have htend : Tendsto (fun t : ℝ => -(Real.exp (-t ^ 2) / (t + x))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun t : ℝ => Real.exp (-t ^ 2) / x) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => Real.exp (-t ^ 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun t : ℝ => -t ^ 2) atTop atBot := by
          simp
        exact Real.tendsto_exp_atBot.comp h1
      simpa using h0.div_const x
    refine squeeze_zero_norm' (a := fun t : ℝ => Real.exp (-t ^ 2) / x) ?_ hsq
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hden : 0 < t + x := by linarith
    simp only [norm_neg]
    rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hden.le)]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hx (by linarith)
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [integral_add (gs_int3 hx) (gs_int2 hx)] at key
  rw [key]
  simp

-- no-dlmf: differentiation under the integral sign for the Goodwin–Staton integral
private lemma gs_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + y))
      (-(∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x) ^ 2)) x := by
  have hhalf : 0 < x / 2 := by linarith
  have hbound_int : Integrable (fun t : ℝ => Real.exp (-t ^ 2) / (x / 2) ^ 2)
      (volume.restrict (Ioi (0:ℝ))) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
      have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
      simpa using this.integrableOn
    exact h1.div_const _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (𝕜 := ℝ)
    (F := fun (y : ℝ) (t : ℝ) => Real.exp (-t ^ 2) / (t + y))
    (F' := fun (y : ℝ) (t : ℝ) => -(Real.exp (-t ^ 2) / (t + y) ^ 2))
    (x₀ := x) (s := Metric.ball x (x / 2))
    (bound := fun t : ℝ => Real.exp (-t ^ 2) / (x / 2) ^ 2)
    (Metric.ball_mem_nhds x hhalf)
    (Filter.Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (gs_int1 hx)
    (Measurable.aestronglyMeasurable (by fun_prop))
    ?_ hbound_int ?_
  · rw [← integral_neg]
    exact key.2
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    intro y hy
    have ht' : (0:ℝ) < t := ht
    have hy' : x / 2 < y := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy; linarith [hy.1]
    have hden : (x / 2) ^ 2 ≤ (t + y) ^ 2 := by nlinarith
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    intro y hy
    have ht' : (0:ℝ) < t := ht
    have hy' : x / 2 < y := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy; linarith [hy.1]
    have hne : (t + y) ≠ 0 := by intro h; nlinarith
    have hd2 : HasDerivAt (fun y : ℝ => t + y) 1 y := by
      simpa using (hasDerivAt_id y).const_add t
    have h := ((hasDerivAt_const y (Real.exp (-t ^ 2))).div hd2 hne)
    convert h using 1
    field_simp
    ring

-- no-dlmf: the first-order ODE satisfied by the Goodwin–Staton integral
private lemma gs_ode {x : ℝ} (hx : 0 < x) :
    2 * x * (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x))
      - (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x) ^ 2) = Real.sqrt π - 1 / x := by
  have hgauss : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
    have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
    simpa using this.integrableOn
  have hgval : (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2)) = Real.sqrt π / 2 := by
    rw [show (fun t : ℝ => Real.exp (-t ^ 2)) = (fun t : ℝ => Real.exp (-1 * t ^ 2)) from by
      funext t; ring_nf]
    rw [integral_gaussian_Ioi 1]
    simp
  have hsplit : 2 * x * (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x))
      = Real.sqrt π - (∫ t in Ioi (0:ℝ), 2 * t * Real.exp (-t ^ 2) / (t + x)) := by
    rw [← integral_const_mul]
    have hcongr : (∫ t in Ioi (0:ℝ), 2 * x * (Real.exp (-t ^ 2) / (t + x)))
        = ∫ t in Ioi (0:ℝ), (2 * Real.exp (-t ^ 2) - 2 * t * Real.exp (-t ^ 2) / (t + x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht' : (0:ℝ) < t := ht
      have hden : (t + x) ≠ 0 := by intro h; nlinarith
      field_simp
      ring
    rw [hcongr, integral_sub (hgauss.const_mul 2) (gs_int3 hx), integral_const_mul, hgval]
    ring
  have hibp := gs_ibp hx
  linarith

-- no-dlmf: the shifted Goodwin–Staton integral is `½E₁(x²)` (substitution `s = (t+x)²`)
private lemma gs_shift_eq {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0:ℝ), Real.exp (-(t + x) ^ 2) / (t + x))
      = (1 / 2) * FLMF.ExpIntegrals.Def.E1 (x ^ 2) := by
  have hx2 : (0:ℝ) < x ^ 2 := by positivity
  have hfin : ∀ b : ℝ, 0 < b → (∫ t in (0:ℝ)..b, 2 * (Real.exp (-(t + x) ^ 2) / (t + x)))
      = ∫ s in (x ^ 2)..((b + x) ^ 2), Real.exp (-s) / s := by
    intro b hb
    have hsub := intervalIntegral.integral_deriv_smul_comp' (a := (0:ℝ)) (b := b)
      (f := fun t : ℝ => (t + x) ^ 2) (f' := fun t : ℝ => 2 * (t + x))
      (g := fun s : ℝ => Real.exp (-s) / s)
      (fun t _ => by
        have h1 : HasDerivAt (fun t : ℝ => t + x) 1 t := by
          simpa using (hasDerivAt_id t).add_const x
        simpa using (h1.pow 2))
      (by fun_prop)
      (by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        rintro s ⟨t, ht, rfl⟩
        rw [Set.uIcc_of_le hb.le] at ht
        have : 0 ≤ t := ht.1
        positivity)
    simp only [Function.comp_apply, smul_eq_mul, zero_add] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb.le] at ht
    have ht0 : 0 ≤ t := ht.1
    have hpos : 0 < t + x := by linarith
    field_simp
  have hA : Tendsto (fun b : ℝ => ∫ t in (0:ℝ)..b, 2 * (Real.exp (-(t + x) ^ 2) / (t + x)))
      atTop (𝓝 (∫ t in Ioi (0:ℝ), 2 * (Real.exp (-(t + x) ^ 2) / (t + x)))) :=
    intervalIntegral_tendsto_integral_Ioi 0 ((gs_int_shift hx).const_mul 2) tendsto_id
  have hbtop : Tendsto (fun b : ℝ => (b + x) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) two_ne_zero).comp
      (tendsto_atTop_add_const_right _ x tendsto_id)
  have hB : Tendsto (fun b : ℝ => ∫ s in (x ^ 2)..((b + x) ^ 2), Real.exp (-s) / s)
      atTop (𝓝 (∫ s in Ioi (x ^ 2), Real.exp (-s) / s)) :=
    intervalIntegral_tendsto_integral_Ioi (x ^ 2) (gs_int_e1 hx2) hbtop
  have heq : (fun b : ℝ => ∫ t in (0:ℝ)..b, 2 * (Real.exp (-(t + x) ^ 2) / (t + x)))
      =ᶠ[atTop] (fun b : ℝ => ∫ s in (x ^ 2)..((b + x) ^ 2), Real.exp (-s) / s) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb using hfin b hb
  have hkey := tendsto_nhds_unique (hA.congr' heq) hB
  rw [integral_const_mul] at hkey
  rw [FLMF.ExpIntegrals.Def.E1_def]
  linarith

-- no-dlmf: the Goodwin–Staton integral differs from its shift by at most `√π·x`
private lemma gs_shift_close {x : ℝ} (hx : 0 < x) :
    |(∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x))
      - (∫ t in Ioi (0:ℝ), Real.exp (-(t + x) ^ 2) / (t + x))| ≤ Real.sqrt π * x := by
  have hgauss : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0:ℝ)) := by
    have := integrable_exp_neg_mul_sq (b := (1:ℝ)) one_pos
    simpa using this.integrableOn
  have hbound : Integrable (fun t : ℝ => 2 * x * Real.exp (-t ^ 2))
      (volume.restrict (Ioi (0:ℝ))) := hgauss.const_mul _
  rw [← integral_sub (gs_int1 hx) (gs_int_shift hx)]
  have hle : ‖∫ t in Ioi (0:ℝ), (Real.exp (-t ^ 2) / (t + x) - Real.exp (-(t + x) ^ 2) / (t + x))‖
      ≤ ∫ t in Ioi (0:ℝ), 2 * x * Real.exp (-t ^ 2) := by
    refine norm_integral_le_of_norm_le hbound ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht' : (0:ℝ) < t := ht
    have hden : 0 < t + x := by linarith
    have hmono : Real.exp (-(t + x) ^ 2) ≤ Real.exp (-t ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hdiff : Real.exp (-t ^ 2) - Real.exp (-(t + x) ^ 2)
        ≤ (2 * t * x + x ^ 2) * Real.exp (-t ^ 2) := by
      have hkey : Real.exp (-(t + x) ^ 2)
          = Real.exp (-t ^ 2) * Real.exp (-(2 * t * x + x ^ 2)) := by
        rw [← Real.exp_add]; ring_nf
      have hexp : 1 - (2 * t * x + x ^ 2) ≤ Real.exp (-(2 * t * x + x ^ 2)) := by
        have := Real.add_one_le_exp (-(2 * t * x + x ^ 2))
        linarith
      rw [hkey]
      nlinarith [Real.exp_pos (-t ^ 2)]
    have hstep : Real.exp (-t ^ 2) / (t + x) - Real.exp (-(t + x) ^ 2) / (t + x)
        ≤ 2 * x * Real.exp (-t ^ 2) := by
      rw [div_sub_div_same, div_le_iff₀ hden]
      nlinarith [Real.exp_pos (-t ^ 2)]
    rw [Real.norm_of_nonneg (by rw [div_sub_div_same]; positivity)]
    exact hstep
  calc |(∫ t in Ioi (0:ℝ), (Real.exp (-t ^ 2) / (t + x) - Real.exp (-(t + x) ^ 2) / (t + x)))|
      ≤ ∫ t in Ioi (0:ℝ), 2 * x * Real.exp (-t ^ 2) := hle
    _ = Real.sqrt π * x := by
        rw [integral_const_mul]
        rw [show (fun t : ℝ => Real.exp (-t ^ 2)) = (fun t : ℝ => Real.exp (-1 * t ^ 2)) from by
          funext t; ring_nf]
        rw [integral_gaussian_Ioi 1]
        simp only [div_one]
        ring

-- no-dlmf: elementary bound `|eiSeries y| ≤ e^{|y|} - 1`; analytic infrastructure
private lemma gs_eiSeries_abs_le (y : ℝ) :
    |FLMF.ExpIntegrals.Def.eiSeries y| ≤ Real.exp |y| - 1 := by
  have hsummable : Summable (fun n : ℕ => |y| ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial |y|
  have hpeel : Real.exp |y| - 1 = ∑' k : ℕ, |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    have hexp : Real.exp |y| = ∑' n : ℕ, |y| ^ n / (Nat.factorial n : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp, hsummable.tsum_eq_zero_add]; simp
  have hsucc : Summable (fun k : ℕ => |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) := by
    have := hsummable.comp_injective (Nat.succ_injective)
    simpa [Function.comp] using this
  have hterm : ∀ k : ℕ, ‖y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖
      ≤ |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    intro k
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0:ℝ) < (k : ℝ) + 1),
      abs_of_pos (by positivity : (0:ℝ) < (Nat.factorial (k + 1) : ℝ))]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) k,
      (by positivity : (0:ℝ) < (Nat.factorial (k + 1) : ℝ))]
  have hnormsum : Summable
      (fun k : ℕ => ‖y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsucc
  calc |FLMF.ExpIntegrals.Def.eiSeries y|
      ≤ ∑' k : ℕ, ‖y ^ (k + 1) / (((k : ℝ) + 1) * (Nat.factorial (k + 1) : ℝ))‖ := by
        simpa [FLMF.ExpIntegrals.Def.eiSeries, Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, |y| ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) :=
        hnormsum.tsum_le_tsum hterm hsucc
    _ = Real.exp |y| - 1 := hpeel.symm

-- no-dlmf: continuity of `eiSeries` at the origin; analytic infrastructure
private lemma gs_eiSeries_tendsto_zero :
    Tendsto FLMF.ExpIntegrals.Def.eiSeries (𝓝 0) (𝓝 0) := by
  have hb : Tendsto (fun y : ℝ => Real.exp |y| - 1) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun y : ℝ => Real.exp |y| - 1) := by fun_prop
    simpa using h.tendsto 0
  refine squeeze_zero_norm' (a := fun y : ℝ => Real.exp |y| - 1) ?_ hb
  filter_upwards with y
  simpa [Real.norm_eq_abs] using gs_eiSeries_abs_le y

-- no-dlmf: `e^y E₁(y) + Ei(y) → 0` as `y → 0⁺`; the constant-pinning input
private lemma gs_expE1_add_Ei_tendsto :
    Tendsto (fun y : ℝ => Real.exp y * FLMF.ExpIntegrals.Def.E1 y
      + FLMF.ExpIntegrals.Def.Ei y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hslope : Tendsto (fun y : ℝ => (Real.exp y - 1) / y) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0)
    rw [Real.exp_zero] at h
    have hsub : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx)
    refine (h.mono_left hsub).congr ?_
    intro y
    simp [slope_def_field, div_eq_inv_mul, sub_zero]
  have hylog : Tendsto (fun y : ℝ => y * Real.log y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
    simp only [Real.rpow_one] at h
    simpa [mul_comm] using h
  have hexp : Tendsto (fun y : ℝ => Real.exp y) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h : ContinuousAt Real.exp 0 := Real.continuous_exp.continuousAt
    simpa using (h.tendsto.mono_left nhdsWithin_le_nhds)
  have heiS : Tendsto (fun y : ℝ => FLMF.ExpIntegrals.Def.eiSeries y) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    gs_eiSeries_tendsto_zero.mono_left nhdsWithin_le_nhds
  have heiSneg : Tendsto (fun y : ℝ => FLMF.ExpIntegrals.Def.eiSeries (-y))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine gs_eiSeries_tendsto_zero.comp ?_
    have h : Tendsto (fun y : ℝ => -y) (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ))
    exact h.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun y : ℝ =>
      -Real.eulerMascheroniConstant * (Real.exp y - 1)
        - ((Real.exp y - 1) / y) * (y * Real.log y)
        - Real.exp y * FLMF.ExpIntegrals.Def.eiSeries (-y)
        + FLMF.ExpIntegrals.Def.eiSeries y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have e1 : Tendsto (fun y : ℝ => -Real.eulerMascheroniConstant * (Real.exp y - 1))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := (hexp.sub_const 1).const_mul (-Real.eulerMascheroniConstant)
      simpa using this
    have e2 : Tendsto (fun y : ℝ => ((Real.exp y - 1) / y) * (y * Real.log y))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hslope.mul hylog
    have e3 : Tendsto (fun y : ℝ => Real.exp y * FLMF.ExpIntegrals.Def.eiSeries (-y))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hexp.mul heiSneg
    simpa using ((e1.sub e2).sub e3).add heiS
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : (0:ℝ) < y := hy
  rw [FLMF.ExpIntegrals.Def.E1_series hy', FLMF.ExpIntegrals.Def.Ei_def, abs_of_pos hy']
  field_simp
  ring

-- no-dlmf: the conserved quantity of the Goodwin–Staton ODE; analytic infrastructure
private noncomputable def gsPsi (y : ℝ) : ℝ :=
  Real.exp (y ^ 2) * (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + y))
    - Real.sqrt π * (∫ t in (0:ℝ)..y, Real.exp (t ^ 2))
    + (1 / 2) * FLMF.ExpIntegrals.Def.Ei (y ^ 2)

-- no-dlmf: `gsPsi` has vanishing derivative on `(0,∞)`; analytic infrastructure
private lemma gsPsi_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt gsPsi 0 x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hx2 : (0:ℝ) < x ^ 2 := by positivity
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hE : HasDerivAt (fun y : ℝ => Real.exp (y ^ 2)) (Real.exp (x ^ 2) * (2 * x)) x := by
    simpa using (Real.hasDerivAt_exp (x ^ 2)).comp x hsq
  have hI : HasDerivAt (fun y : ℝ => ∫ t in (0:ℝ)..y, Real.exp (t ^ 2)) (Real.exp (x ^ 2)) x :=
    FLMF.hasDerivAt_integral_exp_sq x
  have hEi : HasDerivAt (fun y : ℝ => FLMF.ExpIntegrals.Def.Ei (y ^ 2))
      (Real.exp (x ^ 2) / x ^ 2 * (2 * x)) x := by
    have h : HasDerivAt (FLMF.ExpIntegrals.Def.Ei ∘ fun y : ℝ => y ^ 2)
        (Real.exp (x ^ 2) / x ^ 2 * (2 * x)) x :=
      HasDerivAt.comp x (FLMF.ExpIntegrals.hasDerivAt_Ei hx2) hsq
    simpa [Function.comp] using h
  have htot := (((hE.mul (gs_hasDerivAt hx)).sub (hI.const_mul (Real.sqrt π))).add
    (hEi.const_mul (1 / 2)))
  have hODEx : x * (2 * x * (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x))
      - (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x) ^ 2)) = x * Real.sqrt π - 1 := by
    rw [gs_ode hx]; field_simp
  show HasDerivAt gsPsi 0 x
  unfold gsPsi
  convert htot using 1
  field_simp
  linear_combination (-Real.exp (x ^ 2)) * hODEx

-- no-dlmf: `gsPsi` is constant on `(0,∞)`; analytic infrastructure
private lemma gsPsi_const {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : gsPsi a = gsPsi b := by
  have hsub : ∀ y ∈ Set.uIcc a b, 0 < y := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.1]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := gsPsi) (f' := fun _ : ℝ => (0:ℝ))
    (fun y hy => gsPsi_hasDerivAt (hsub y hy))
    intervalIntegrable_const
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at h
  linarith

-- no-dlmf: the `x → 0⁺` limit pinning the constant to zero; analytic infrastructure
private lemma gsPsi_tendsto_zero : Tendsto gsPsi (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hT1 : Tendsto (fun y : ℝ => Real.exp (y ^ 2)
      * ((∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + y))
        - (∫ t in Ioi (0:ℝ), Real.exp (-(t + y) ^ 2) / (t + y)))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hb : Tendsto (fun y : ℝ => Real.exp (y ^ 2) * (Real.sqrt π * y)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h : Continuous (fun y : ℝ => Real.exp (y ^ 2) * (Real.sqrt π * y)) := by fun_prop
      have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Ioi 0))
      simpa using this
    refine squeeze_zero_norm' (a := fun y : ℝ => Real.exp (y ^ 2) * (Real.sqrt π * y)) ?_ hb
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (0:ℝ) < y := hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (gs_shift_close hy') (Real.exp_pos _).le
  have hy2 : Tendsto (fun y : ℝ => y ^ 2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Continuous (fun y : ℝ => y ^ 2) := by fun_prop
      have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : (0:ℝ) < y := hy
      exact (by positivity : (0:ℝ) < y ^ 2)
  have hT2 : Tendsto (fun y : ℝ => (1 / 2) * (Real.exp (y ^ 2)
      * FLMF.ExpIntegrals.Def.E1 (y ^ 2) + FLMF.ExpIntegrals.Def.Ei (y ^ 2)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have := (gs_expE1_add_Ei_tendsto.comp hy2).const_mul (1 / 2 : ℝ)
    simpa [Function.comp] using this
  have hT3 : Tendsto (fun y : ℝ => Real.sqrt π * (∫ t in (0:ℝ)..y, Real.exp (t ^ 2)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun y : ℝ => ∫ t in (0:ℝ)..y, Real.exp (t ^ 2)) :=
      intervalIntegral.continuous_primitive (fun a b => FLMF.intervalIntegrable_exp_sq a b) 0
    have h := ((hcont.tendsto 0).const_mul (Real.sqrt π)).mono_left
      (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Ioi 0))
    simpa using h
  have hsum := (hT1.add hT2).sub hT3
  simp only [zero_add, sub_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : (0:ℝ) < y := hy
  rw [gs_shift_eq hy']
  unfold gsPsi
  ring

/-- Goodwin–Staton integral in terms of Dawson's integral and `Ei`:
`G(x) = √π·F(x) - ½ e^{-x²} Ei(x²)` for `x > 0`, where the Goodwin–Staton integral
`G(x) = ∫₀^∞ e^{-t²}/(t+x) dt` is written directly as its improper integral
(DLMF 7.5.13).

DLMF 7.5.13.
DAG: E-7.5.13.
Numerical: PASS
Verified: verified
-/
theorem erf_7_5_13 {x : ℝ} (hx : 0 < x) :
    (∫ t in Set.Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x))
      = Real.sqrt π * FLMF.dawson x - (1 / 2) * Real.exp (-x ^ 2) * FLMF.ExpIntegrals.Def.Ei (x ^ 2) := by
  have hzero : gsPsi x = 0 := by
    have hev : (fun _ : ℝ => gsPsi x) =ᶠ[𝓝[>] (0:ℝ)] gsPsi := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact gsPsi_const hx (by exact hy)
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) gsPsi_tendsto_zero
  have hexp : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  unfold gsPsi at hzero
  rw [FLMF.dawson]
  linear_combination (Real.exp (-x ^ 2)) * hzero
    - (∫ t in Ioi (0:ℝ), Real.exp (-t ^ 2) / (t + x)) * hexp

end FLMF.Error
