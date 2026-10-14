import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Contour rotation (sector / Wick rotation) — method-kit infrastructure

Foundation for **Module 1** of the contour-deformation plan
([`docs/METHODS_ROADMAP.md`](../../docs/METHODS_ROADMAP.md)): rotating a ray
integral `∫_{(0,∞)} f(t) dt` onto a rotated ray `e^{iθ}·(0,∞)`,
`∫_{(0,∞)} f = e^{iθ} ∫_{(0,∞)} f(e^{iθ}·)`, for `f` holomorphic on the sector.
This is the analytic engine behind the Fresnel/stationary-phase contour rotation
and the Mellin transform of cosine (`∫_0^∞ t^{s-1}e^{-it} = e^{-iπs/2}Γ(s)`, the
blocker for `Ci → 0`, issue #7).

## Approach — angle differentiation (not homotopy, not Jordan's lemma)

The textbook proof closes a sector contour and bounds the arc at infinity
(Jordan's lemma). We avoid both the `picard-lefschetz` homotopy machinery *and*
Jordan's lemma with a cleaner route: differentiate the rotated integral in the
**rotation angle**. Writing `g(θ, r) = e^{iθ}·f(e^{iθ}·r)`, the chain rule gives
the key identity
`∂_θ g(θ, r) = i · ∂_r [ r · g(θ, r) ]`  (`rotation_angle_deriv`),
so by the fundamental theorem of calculus on `(0,∞)`
`∂_θ ∫_{(0,∞)} g(θ, ·) = i · [ r·g(θ,r) ]_{r=0}^{∞} = 0`
*provided the boundary term `r·g(θ,r) → 0`* — the "arc estimate" becomes a single
**pointwise** boundary condition (`integral_Ioi_deriv_eq_zero`). With the
`θ`-derivative identically zero, the rotated integral is constant in `θ`, giving
the rotation identity.

## Status

Shipped (this file, sorry-free):
* `rotation_angle_deriv` — the angle-derivative identity (`∂_θ g`);
* `rotation_r_deriv` — the matching `r`-derivative of `r·g`;
* `integral_Ioi_deriv_eq_zero` — the FTC boundary-vanishing lemma;
* `angle_deriv_integral_zero` — **the `θ`-derivative of the rotated integral is
  identically zero** (`∫_{(0,∞)} ∂_θ g = i·[r·g]_0^∞ = 0`), the analytic heart;
* `ray_rotation` — **the full rotation identity** `∫f = e^{iθ₀}∫f(e^{iθ₀}·)`, with
  the differentiation-under-the-integral-sign step taken as a caller-supplied
  hypothesis (`hIderiv`, discharged via
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the specific `f`).

* `ray_rotation_of_dominated` — the convenience form: discharges `hIderiv`/`hIcont`
  from a single uniform domination bound on the angle-derivative (via
  `rotated_integral_hasDerivAt`).

Sector forms `angle_deriv_integral_zero_sector` and `ray_rotation_sector`
generalize the engine to `f` holomorphic only on the open rotated rays, with the
boundary function continuous up to `0` supplied as a hypothesis — this admits an
**integrable singularity at `0`** (the `t^{s-1}` of the Γ/Mellin integrand). The
entire-`f` `angle_deriv_integral_zero` / `ray_rotation` are their corollaries.

Validated end-to-end on the Gaussian wedge in `ContourRotationGaussian`
(`gaussian_ray_rotation`), which also realizes the oscillatory boundary
(`rotated_gaussian_tendsto_fresnel`). Remaining toward #7: discharge the sector
hypotheses for the Γ integrand (its `hf` is confirmed dischargeable — holomorphy
on the rotated ray) and the conditionally-convergent / improper formulation.
Tracked in `docs/METHODS_ROADMAP.md`.
-/

namespace FLMF.Methods.ContourRotation

open MeasureTheory Filter Topology Set Complex

-- no-dlmf: contour-rotation infrastructure
/-- **Angle-derivative of the rotated integrand.** For `f` holomorphic at
`u = e^{iθ}·r`, the `θ`-derivative of `g(θ) = e^{iθ}·f(e^{iθ}·r)` is
`i·e^{iθ}·f(u) + i·r·e^{2iθ}·f'(u)`.

This equals `i · ∂_r[r·g]`, which is what turns the contour arc-at-infinity
estimate into the pointwise boundary condition `r·g → 0`. -/
theorem rotation_angle_deriv (f f' : ℂ → ℂ) (θ r : ℝ)
    (hf : HasDerivAt f (f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Complex.exp (θ * Complex.I) * (r : ℂ))) :
    HasDerivAt
      (fun θ' : ℝ => Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
          * f' (Complex.exp (θ * Complex.I) * (r : ℂ))) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => (θ' : ℂ) * Complex.I) Complex.I θ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I)
  have h2 : HasDerivAt (fun θ' : ℝ => Complex.exp ((θ' : ℂ) * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ := h1.cexp
  have h3 : HasDerivAt (fun θ' : ℝ => Complex.exp ((θ' : ℂ) * Complex.I) * (r : ℂ))
      (Complex.exp (θ * Complex.I) * Complex.I * (r : ℂ)) θ := h2.mul_const (r : ℂ)
  have h4 : HasDerivAt (fun θ' : ℝ => f (Complex.exp ((θ' : ℂ) * Complex.I) * (r : ℂ)))
      (f' (Complex.exp (θ * Complex.I) * (r : ℂ))
        * (Complex.exp (θ * Complex.I) * Complex.I * (r : ℂ))) θ :=
    hf.comp θ h3
  have h5 := h2.mul h4
  convert h5 using 1
  ring

-- no-dlmf: contour-rotation infrastructure (FTC boundary-vanishing)
/-- **FTC boundary-vanishing.** If `G : ℝ → ℂ` is `C¹` on `[0,∞)` with `G 0 = 0`
and `G → 0` at `+∞`, and `G'` is integrable on `(0,∞)`, then `∫_{(0,∞)} G' = 0`.
This is the boundary term `i·[r·g]_0^∞ = 0` of the rotation argument. -/
theorem integral_Ioi_deriv_eq_zero {G G' : ℝ → ℂ}
    (hcont : ContinuousOn G (Ici 0))
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Ioi 0))
    (h0 : G 0 = 0) (htop : Tendsto G atTop (𝓝 0)) :
    ∫ x in Ioi (0 : ℝ), G' x = 0 := by
  have hkey := integral_Ioi_of_hasDerivAt_of_tendsto
    (hcont.continuousWithinAt (self_mem_Ici)) hderiv hint htop
  rw [hkey, h0, sub_zero]

-- no-dlmf: contour-rotation infrastructure (derivative helper)
/-- **r-derivative of `G(r) = r·e^{iθ}·f(e^{iθ}r)`** (the "`r·g`" of the rotation
argument). For `f` holomorphic at `e^{iθ}r`,
`∂_r G = e^{iθ}·f(e^{iθ}r) + r·e^{2iθ}·f'(e^{iθ}r)`. -/
theorem rotation_r_deriv (f f' : ℂ → ℂ) (θ r : ℝ)
    (hf : HasDerivAt f (f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Complex.exp (θ * Complex.I) * (r : ℂ))) :
    HasDerivAt
      (fun r' : ℝ =>
        (r' : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r' : ℂ))))
      (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ))) r := by
  have hr1 : HasDerivAt (fun r' : ℝ => (r' : ℂ)) 1 r := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := r)
  have hr2 : HasDerivAt (fun r' : ℝ => Complex.exp (θ * Complex.I) * (r' : ℂ))
      (Complex.exp (θ * Complex.I) * 1) r := hr1.const_mul _
  have hr3 : HasDerivAt (fun r' : ℝ => f (Complex.exp (θ * Complex.I) * (r' : ℂ)))
      (f' (Complex.exp (θ * Complex.I) * (r : ℂ)) * (Complex.exp (θ * Complex.I) * 1)) r :=
    hf.comp r hr2
  have hr4 : HasDerivAt
      (fun r' : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r' : ℂ)))
      (Complex.exp (θ * Complex.I) * (f' (Complex.exp (θ * Complex.I) * (r : ℂ))
        * (Complex.exp (θ * Complex.I) * 1))) r := hr3.const_mul _
  have hr5 := hr1.mul hr4
  convert hr5 using 1
  ring

-- no-dlmf: contour-rotation infrastructure
/-- **The angle-derivative integrates to zero — sector form.** As
`angle_deriv_integral_zero`, but `f` need only be holomorphic on the *open rotated
ray* `{e^{iθ}r : r > 0}` (not entire), with continuity of the boundary function
`r ↦ r·e^{iθ}f(e^{iθ}r)` up to `r = 0` supplied as `hGcont`. This admits an
integrable singularity of `f` at `0` (e.g. the `t^{s-1}` of the Γ/Mellin
integrand, where the `r` factor kills the boundary term as `r → 0` whenever
`Re s > 0`). -/
theorem angle_deriv_integral_zero_sector (f f' : ℂ → ℂ) (θ : ℝ)
    (hf : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt f (f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
        (Complex.exp (θ * Complex.I) * (r : ℂ)))
    (hGcont : ContinuousOn
      (fun r : ℝ => (r : ℂ) *
        (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ)))) (Ici 0))
    (hint : IntegrableOn
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Ioi 0))
    (hbdry : Tendsto
      (fun r : ℝ =>
        (r : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ))) = 0 := by
  set G : ℝ → ℂ := fun r' => (r' : ℂ) *
    (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r' : ℂ))) with hG
  set G' : ℝ → ℂ := fun r' =>
    Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r' : ℂ))
      + (r' : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r' : ℂ))
    with hG'
  have hGderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt G (G' r) r :=
    fun r hr => rotation_r_deriv f f' θ r (hf r hr)
  have hG0 : G 0 = 0 := by simp [hG]
  have hzero : ∫ r in Ioi (0 : ℝ), G' r = 0 :=
    integral_Ioi_deriv_eq_zero hGcont hGderiv hint hG0 hbdry
  calc ∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      = ∫ r in Ioi (0 : ℝ), Complex.I * G' r := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
          rw [hG']; ring
    _ = Complex.I * ∫ r in Ioi (0 : ℝ), G' r := integral_const_mul _ _
    _ = 0 := by rw [hzero, mul_zero]

-- no-dlmf: contour-rotation infrastructure
/-- **The angle-derivative integrates to zero.** For entire `f`, the integral over
`(0,∞)` of `∂_θ[e^{iθ}f(e^{iθ}r)]` vanishes, provided the boundary term
`r·e^{iθ}f(e^{iθ}r) → 0` at `∞` and `∂_r[r·g]` is integrable. The entire-`f`
specialization of `angle_deriv_integral_zero_sector` (the boundary continuity is
free from `f` continuous). This is the `θ`-derivative of the rotated integral —
identically zero, hence the rotated integral is constant in `θ`. -/
theorem angle_deriv_integral_zero (f f' : ℂ → ℂ) (θ : ℝ)
    (hf : ∀ z, HasDerivAt f (f' z) z)
    (hint : IntegrableOn
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Ioi 0))
    (hbdry : Tendsto
      (fun r : ℝ =>
        (r : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ))) = 0 := by
  refine angle_deriv_integral_zero_sector f f' θ (fun r _ => hf _) ?_ hint hbdry
  exact (continuous_iff_continuousAt.mpr fun r =>
    (rotation_r_deriv f f' θ r (hf _)).continuousAt).continuousOn

-- no-dlmf: contour-rotation infrastructure (Wick rotation, sector form)
/-- **Ray rotation (Wick rotation) — sector form.** As `ray_rotation`, but `f` need
only be holomorphic on the open rotated rays for each `θ ∈ [0,θ₀]` (`hf`
per-point), with the boundary function continuous up to `0` (`hGcont`). Admits an
integrable singularity at `0` (the `t^{s-1}` Γ/Mellin case). -/
theorem ray_rotation_sector (f f' : ℂ → ℂ) (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀)
    (hf : ∀ θ ∈ Icc 0 θ₀, ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt f (f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
        (Complex.exp (θ * Complex.I) * (r : ℂ)))
    (hGcont : ∀ θ ∈ Icc 0 θ₀, ContinuousOn
      (fun r : ℝ => (r : ℂ) *
        (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ)))) (Ici 0))
    (hIcont : ContinuousOn
      (fun θ : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))) (Icc 0 θ₀))
    (hIderiv : ∀ θ ∈ Icc 0 θ₀, HasDerivAt
      (fun θ' : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))) θ)
    (hint : ∀ θ ∈ Icc 0 θ₀, IntegrableOn
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Ioi 0))
    (hbdry : ∀ θ ∈ Icc 0 θ₀, Tendsto
      (fun r : ℝ =>
        (r : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), f (r : ℂ)
      = Complex.exp (θ₀ * Complex.I)
        * ∫ r in Ioi (0 : ℝ), f (Complex.exp (θ₀ * Complex.I) * (r : ℂ)) := by
  set I : ℝ → ℂ := fun θ : ℝ => ∫ r in Ioi (0 : ℝ),
    Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ)) with hI
  have hderiv0 : ∀ θ ∈ Ico 0 θ₀, HasDerivWithinAt I 0 (Ici θ) θ := by
    intro θ hθ
    have hz := angle_deriv_integral_zero_sector f f' θ (hf θ (Ico_subset_Icc_self hθ))
      (hGcont θ (Ico_subset_Icc_self hθ)) (hint θ (Ico_subset_Icc_self hθ))
      (hbdry θ (Ico_subset_Icc_self hθ))
    have hd := hIderiv θ (Ico_subset_Icc_self hθ)
    rw [hz] at hd
    exact hd.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hIcont hderiv0 θ₀ (right_mem_Icc.2 hθ₀)
  have hI0 : I 0 = ∫ r in Ioi (0 : ℝ), f (r : ℂ) := by simp [hI]
  have hIθ₀ : I θ₀ = Complex.exp (θ₀ * Complex.I)
      * ∫ r in Ioi (0 : ℝ), f (Complex.exp (θ₀ * Complex.I) * (r : ℂ)) := by
    rw [hI]; simp only; rw [← integral_const_mul]
  rw [← hI0, ← hIθ₀, hconst]

-- no-dlmf: contour-rotation infrastructure (Wick rotation)
/-- **Ray rotation (Wick rotation).** For entire `f`, the ray integral rotates:
`∫_{(0,∞)} f = e^{iθ₀} ∫_{(0,∞)} f(e^{iθ₀}·)`. The entire-`f` specialization of
`ray_rotation_sector` (boundary continuity free from `f` continuous).

The rotated integral `I(θ) = ∫_{(0,∞)} e^{iθ}f(e^{iθ}r) dr` is shown constant in
`θ`: by `angle_deriv_integral_zero` its `θ`-derivative is the integral of
`∂_θ g`, which is `0`. The differentiation-under-the-integral-sign step is
supplied by the caller as `hIderiv` (the standard domination regularity,
discharged via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the
specific `f`); `hIcont` is the matching continuity, and `hint`/`hbdry` are the
per-angle integrability / boundary-vanishing conditions. -/
-- no-dlmf: contour ray-rotation lemma, analytic infra
theorem ray_rotation (f f' : ℂ → ℂ) (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀)
    (hf : ∀ z, HasDerivAt f (f' z) z)
    (hIcont : ContinuousOn
      (fun θ : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))) (Icc 0 θ₀))
    (hIderiv : ∀ θ ∈ Icc 0 θ₀, HasDerivAt
      (fun θ' : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))) θ)
    (hint : ∀ θ ∈ Icc 0 θ₀, IntegrableOn
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Ioi 0))
    (hbdry : ∀ θ ∈ Icc 0 θ₀, Tendsto
      (fun r : ℝ =>
        (r : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), f (r : ℂ)
      = Complex.exp (θ₀ * Complex.I)
        * ∫ r in Ioi (0 : ℝ), f (Complex.exp (θ₀ * Complex.I) * (r : ℂ)) := by
  refine ray_rotation_sector f f' θ₀ hθ₀ (fun θ _ r _ => hf _) (fun θ _ => ?_)
    hIcont hIderiv hint hbdry
  exact (continuous_iff_continuousAt.mpr fun r =>
    (rotation_r_deriv f f' θ r (hf _)).continuousAt).continuousOn

-- no-dlmf: contour-rotation infrastructure (differentiation-under-integral helper)
/-- Discharge the differentiation-under-the-integral hypothesis of `ray_rotation`
at one angle, from a uniform domination bound on an open `θ`-neighbourhood — via
Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the pointwise
derivative supplied by `rotation_angle_deriv`. -/
theorem rotated_integral_hasDerivAt
    (f f' : ℂ → ℂ) (hf : ∀ z, HasDerivAt f (f' z) z)
    (hf_cont : Continuous f) (hf'_cont : Continuous f')
    (s : Set ℝ) (hs_open : IsOpen s) {θ : ℝ} (hθ : θ ∈ s)
    (hg_int : Integrable
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (volume.restrict (Ioi (0:ℝ))))
    (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (0:ℝ))))
    (hdom : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0:ℝ))), ∀ θ' ∈ s,
      ‖Complex.I * Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ))
        + Complex.I * (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
          * f' (Complex.exp (θ' * Complex.I) * (r : ℂ))‖ ≤ bound r) :
    HasDerivAt
      (fun θ' : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))) θ := by
  set F : ℝ → ℝ → ℂ := fun θ' r =>
    Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)) with hF
  set F' : ℝ → ℝ → ℂ := fun θ' r =>
    Complex.I * Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ))
      + Complex.I * (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
        * f' (Complex.exp (θ' * Complex.I) * (r : ℂ)) with hF'
  have hmeasF : ∀ θ' : ℝ, AEStronglyMeasurable (F θ') (volume.restrict (Ioi (0:ℝ))) :=
    fun θ' => (by fun_prop : Continuous (F θ')).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (F' θ) (volume.restrict (Ioi (0:ℝ))) :=
    (by fun_prop : Continuous (F' θ)).aestronglyMeasurable
  have hdiff : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0:ℝ))), ∀ θ' ∈ s,
      HasDerivAt (fun θ'' => F θ'' r) (F' θ' r) θ' := by
    filter_upwards with r θ' _ using rotation_angle_deriv f f' θ' r (hf _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs := hs_open.mem_nhds hθ)
    (hF_meas := Eventually.of_forall hmeasF) (hF_int := hg_int) (hF'_meas := hmeasF')
    (h_bound := hdom) (bound_integrable := hbound_int) (h_diff := hdiff)).2

-- no-dlmf: contour-rotation infrastructure (Wick rotation convenience form)
/-- **Ray rotation from a domination bound.** The convenience form of
`ray_rotation`: discharges the differentiation-under-the-integral and continuity
hypotheses from a single uniform domination bound on the angle-derivative over an
open `θ`-interval `s ⊇ [0,θ₀]`. -/
theorem ray_rotation_of_dominated
    (f f' : ℂ → ℂ) (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀)
    (hf : ∀ z, HasDerivAt f (f' z) z) (hf_cont : Continuous f) (hf'_cont : Continuous f')
    (s : Set ℝ) (hs_open : IsOpen s) (hsub : Icc 0 θ₀ ⊆ s)
    (hg_int : ∀ θ ∈ s, Integrable
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (volume.restrict (Ioi (0:ℝ))))
    (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (0:ℝ))))
    (hdom : ∀ᵐ (r : ℝ) ∂(volume.restrict (Ioi (0:ℝ))), ∀ θ' ∈ s,
      ‖Complex.I * Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ))
        + Complex.I * (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
          * f' (Complex.exp (θ' * Complex.I) * (r : ℂ))‖ ≤ bound r)
    (hint : ∀ θ ∈ Icc 0 θ₀, IntegrableOn
      (fun r : ℝ => Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2 * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Ioi 0))
    (hbdry : ∀ θ ∈ Icc 0 θ₀, Tendsto
      (fun r : ℝ =>
        (r : ℂ) * (Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0)) :
    ∫ r in Ioi (0 : ℝ), f (r : ℂ)
      = Complex.exp (θ₀ * Complex.I)
        * ∫ r in Ioi (0 : ℝ), f (Complex.exp (θ₀ * Complex.I) * (r : ℂ)) := by
  have hIderiv : ∀ θ ∈ Icc 0 θ₀, HasDerivAt
      (fun θ' : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ' * Complex.I) * f (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * f' (Complex.exp (θ * Complex.I) * (r : ℂ)))) θ :=
    fun θ hθ => rotated_integral_hasDerivAt f f' hf hf_cont hf'_cont s hs_open (hsub hθ)
      (hg_int θ (hsub hθ)) bound hbound_int hdom
  have hIcont : ContinuousOn
      (fun θ : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ * Complex.I) * f (Complex.exp (θ * Complex.I) * (r : ℂ))) (Icc 0 θ₀) :=
    fun θ hθ => (hIderiv θ hθ).continuousAt.continuousWithinAt
  exact ray_rotation f f' θ₀ hθ₀ hf hIcont hIderiv hint hbdry

end FLMF.Methods.ContourRotation
