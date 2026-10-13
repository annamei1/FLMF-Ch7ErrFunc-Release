import FLMF.Methods.MellinBarnes
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Residue calculus: small-circle residues, one-pole circle and rectangle theorems

The first residue-calculus module in FLMF (Mathlib has no residue API; its complex-
analysis backbone stops at the Cauchy–Goursat theorems for discs, annuli and
rectangles in `Mathlib.Analysis.Complex.CauchyIntegral`). This file provides the
minimal residue kit that the Mellin–Barnes pole-shifting method (DLMF §2.5, task A3)
consumes:

* `FLMF.Methods.residue f c` — the residue of `f` at `c`, defined as the normalized
  small-circle integral `(2πi)⁻¹ ∮_{|z-c|=ε} f`. It is well defined (radius-independent)
  by the Cauchy–Goursat theorem for annuli whenever `f` is holomorphic on a punctured
  disc around `c`; outside that regime the definition returns a junk value `0`.

* `FLMF.Methods.residue_simple_pole` — if `(z - c) * f z → r` as `z → c` (a simple pole
  with residue `r`, or a removable singularity for `r = 0`), then `residue f c = r`.

* `FLMF.Methods.circleIntegral_eq_two_pi_I_mul_residue` — for `f` holomorphic on a
  punctured closed disc (an arbitrary isolated singularity at the center),
  `∮_{|z-c|=R} f = 2πi · residue f c`.

* `FLMF.Methods.circle_one_pole` — off-center version for a simple pole: `f` holomorphic
  on a closed disc minus one interior point `p` with `(z-p) f z → r` gives
  `∮ f = 2πi · residue f p`.

* `FLMF.Methods.rectangle_one_pole` / `rectangle_one_pole_residue` — the boundary
  integral of `f` over a rectangle containing exactly one (simple) pole `p` in its
  interior equals `2πi r = 2πi · residue f p`. This is the exact shape the A3
  Mellin–Barnes contour shift needs: moving a vertical contour across one Γ-pole
  produces a rectangle whose boundary integral is the crossed residue.

* `FLMF.Methods.residue_Gamma_neg_nat` — the fidelity anchor: the residue of `Γ` at
  `-n` is `(-1)ⁿ/n!` (DLMF §5.2(i)), tying the analytic `residue` to the arithmetic
  `FLMF.MellinBarnes.gammaResidue` data already used by the Barnes expansion of `e^{-x}`.

## Design notes (excision-route decision)

The rectangle theorem does **not** excise a disc around the pole (neither the
four-subrectangle decomposition nor a homotopy via `picard-lefschetz`'s
`contourDeformation1D` is used). Instead we subtract the singular part:
`g := f - r·(·-p)⁻¹` has a removable singularity at `p` (Riemann,
`Complex.differentiableOn_update_limUnder_of_isLittleO`), so its rectangle boundary
integral vanishes by Mathlib's Cauchy–Goursat for rectangles, while the boundary
integral of `(z - p)⁻¹` is computed **explicitly** as `2πi` from `log`/`arctan`
antiderivatives on the four edges (`rectBoundaryIntegral_inv_sub_pole`); the four
corner angles sum to `2π` via `Real.arctan_inv_of_pos/neg`. This trades the missing
excision domain-lemma for a finite FTC computation. The same removable-singularity
induction now also supplies `circle_finite_simple_poles`, the finite-set circle
theorem used by the logarithmic-derivative argument principle. A general
finite-order-pole rectangle theorem would require principal-part subtraction and is
left to a later phase.
-/

open Complex Metric Set Filter Asymptotics Function
open scoped Real Topology Interval BigOperators

namespace FLMF.Methods

/-! ## The residue as a small-circle integral -/

-- no-dlmf: residue definition, contour-integration infra (DLMF §2.5 area)
open scoped Classical in
/-- The **residue** of `f : ℂ → ℂ` at `c`, defined as the normalized small-circle
integral `(2πi)⁻¹ ∮_{|z-c|=ε} f`, with the radius `ε` extracted (noncanonically) from
a punctured disc of holomorphy. The value does not depend on the choice: see
`residue_eq_circleIntegral`. If `f` is not holomorphic on any punctured disc around
`c`, the definition returns the junk value `0`. -/
noncomputable def residue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  if h : ∃ R, 0 < R ∧ ∀ z ∈ ball c R \ {c}, DifferentiableAt ℂ f z then
    (2 * π * I)⁻¹ * ∮ z in C(c, h.choose / 2), f z
  else 0

/-- Radius independence of small-circle integrals around an isolated singularity:
if `f` is holomorphic on the punctured ball `ball c R \ {c}` and `0 < r ≤ ρ < R`,
the circle integrals at radii `ρ` and `r` agree (Cauchy–Goursat for the annulus). -/
-- no-dlmf: annulus deformation of circle integrals, infra
theorem circleIntegral_congr_radius {f : ℂ → ℂ} {c : ℂ} {r ρ R : ℝ}
    (h0 : 0 < r) (hle : r ≤ ρ) (hρR : ρ < R)
    (hd : ∀ z ∈ ball c R \ {c}, DifferentiableAt ℂ f z) :
    (∮ z in C(c, ρ), f z) = ∮ z in C(c, r), f z := by
  have hsub : closedBall c ρ \ ball c r ⊆ ball c R \ {c} := by
    rintro z ⟨h₁, h₂⟩
    rw [mem_closedBall] at h₁
    rw [mem_ball, not_lt] at h₂
    refine ⟨mem_ball.mpr (h₁.trans_lt hρR), ?_⟩
    simp only [mem_singleton_iff]
    rintro rfl
    rw [dist_self] at h₂
    exact absurd h₂ (not_le.mpr h0)
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 hle countable_empty
    (fun z hz => ((hd z (hsub hz)).continuousAt).continuousWithinAt) fun z hz => ?_
  exact hd z (hsub ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩)

/-- The residue is computed by **any** small circle inside a punctured disc of
holomorphy: if `f` is holomorphic on `ball c R \ {c}` and `0 < r < R`, then
`residue f c = (2πi)⁻¹ ∮_{|z-c|=r} f`. -/
-- no-dlmf: residue well-definedness (radius independence), infra
theorem residue_eq_circleIntegral {f : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (h0 : 0 < r) (hrR : r < R)
    (hd : ∀ z ∈ ball c R \ {c}, DifferentiableAt ℂ f z) :
    residue f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), f z := by
  have hex : ∃ R', 0 < R' ∧ ∀ z ∈ ball c R' \ {c}, DifferentiableAt ℂ f z :=
    ⟨R, h0.trans hrR, hd⟩
  rw [residue, dif_pos hex]
  obtain ⟨hR₀, hd₀⟩ := hex.choose_spec
  have ht0 : 0 < min r (hex.choose / 2) := lt_min h0 (half_pos hR₀)
  have h1 : (∮ z in C(c, hex.choose / 2), f z) = ∮ z in C(c, min r (hex.choose / 2)), f z :=
    circleIntegral_congr_radius ht0 (min_le_right _ _) (half_lt_self hR₀) hd₀
  have h2 : (∮ z in C(c, r), f z) = ∮ z in C(c, min r (hex.choose / 2)), f z :=
    circleIntegral_congr_radius ht0 (min_le_left _ _) hrR hd
  rw [h1, h2]

/-- **Residue at a simple pole.** If `f` is holomorphic on a punctured ball around `c`
and `(z - c) * f z → r` as `z → c` (within `z ≠ c`), then `residue f c = r`.
The case `r = 0` includes removable singularities. -/
-- no-dlmf: simple-pole residue evaluation, contour infra (DLMF §2.5 area)
theorem residue_simple_pole {f : ℂ → ℂ} {c r : ℂ} {R : ℝ} (hR : 0 < R)
    (hd : ∀ z ∈ ball c R \ {c}, DifferentiableAt ℂ f z)
    (hlim : Tendsto (fun z => (z - c) * f z) (𝓝[≠] c) (𝓝 r)) :
    residue f c = r := by
  rw [residue_eq_circleIntegral (half_pos hR) (half_lt_self hR) hd]
  have key : (∮ z in C(c, R / 2), (z - c)⁻¹ • ((z - c) • f z)) = (2 * ↑π * I : ℂ) • r := by
    refine circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      (half_pos hR) countable_empty (fun z hz => ?_) (fun z hz => ?_) ?_
    · have hz' : z ∈ ball c R \ {c} :=
        ⟨mem_ball.mpr ((mem_closedBall.mp hz.1).trans_lt (half_lt_self hR)), hz.2⟩
      exact (((differentiableAt_id.sub_const c).smul (hd z hz')).continuousAt).continuousWithinAt
    · have hz' : z ∈ ball c R \ {c} :=
        ⟨ball_subset_ball (half_le_self hR.le) hz.1.1, hz.1.2⟩
      exact (differentiableAt_id.sub_const c).smul (hd z hz')
    · simpa only [smul_eq_mul] using hlim
  have key2 : (∮ z in C(c, R / 2), f z) = 2 * ↑π * I * r := by
    rw [← circleIntegral.integral_sub_inv_smul_sub_smul f c c (R / 2)]
    simpa only [smul_eq_mul] using key
  rw [key2, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

/-- **Cauchy residue theorem, centered circle version.** If `f` is holomorphic on the
punctured closed disc `closedBall c R \ {c}` (an arbitrary isolated singularity at the
center), then `∮_{|z-c|=R} f = 2πi · residue f c`. -/
-- no-dlmf: one-singularity circle residue theorem, contour infra (DLMF §2.5 area)
theorem circleIntegral_eq_two_pi_I_mul_residue {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hd : ∀ z ∈ closedBall c R \ {c}, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = 2 * π * I * residue f c := by
  have hd' : ∀ z ∈ ball c R \ {c}, DifferentiableAt ℂ f z := fun z hz =>
    hd z ⟨ball_subset_closedBall hz.1, hz.2⟩
  have h1 : residue f c = (2 * π * I)⁻¹ * ∮ z in C(c, R / 2), f z :=
    residue_eq_circleIntegral (half_pos hR) (half_lt_self hR) hd'
  have hzne : ∀ z : ℂ, z ∈ closedBall c R \ ball c (R / 2) → z ≠ c := by
    rintro z ⟨_, h₂⟩ rfl
    exact h₂ (mem_ball_self (half_pos hR))
  have h2 : (∮ z in C(c, R), f z) = ∮ z in C(c, R / 2), f z := by
    refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (half_pos hR)
      (half_le_self hR.le) countable_empty
      (fun z hz => ((hd z ⟨hz.1, hzne z hz⟩).continuousAt).continuousWithinAt)
      fun z hz => ?_
    have hz' : z ∈ closedBall c R \ ball c (R / 2) :=
      ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩
    exact hd z ⟨hz'.1, hzne z hz'⟩
  rw [h2, h1, ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

/-! ## Removable-singularity workhorse for the one-pole theorems -/

/-- If `(q - p) * f q → r` at `p` then `g := f - r·(·-p)⁻¹` satisfies the littleO
hypothesis of Riemann's removable-singularity theorem at `p`. -/
-- no-dlmf: removable-singularity littleO bridge, infra
theorem isLittleO_sub_singular_part {f : ℂ → ℂ} {p r : ℂ}
    (hlim : Tendsto (fun q => (q - p) * f q) (𝓝[≠] p) (𝓝 r)) :
    (fun q => (f q - r * (q - p)⁻¹) - (f p - r * (p - p)⁻¹))
      =o[𝓝[≠] p] fun q => (q - p)⁻¹ := by
  rw [isLittleO_iff_tendsto' (by
    filter_upwards [self_mem_nhdsWithin] with q hq h0
    exact absurd (inv_eq_zero.mp h0) (sub_ne_zero.mpr hq))]
  have hcongr : ∀ᶠ q in 𝓝[≠] p,
      ((f q - r * (q - p)⁻¹) - (f p - r * (p - p)⁻¹)) / (q - p)⁻¹
        = ((q - p) * f q - r) - (q - p) * (f p - r * (p - p)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hne : (q - p) ≠ 0 := sub_ne_zero.mpr hq
    field_simp
  rw [tendsto_congr' hcongr]
  have h1 : Tendsto (fun q : ℂ => (q - p) * f q - r) (𝓝[≠] p) (𝓝 0) := by
    simpa using hlim.sub_const r
  have h2 : Tendsto (fun q : ℂ => (q - p) * (f p - r * (p - p)⁻¹)) (𝓝[≠] p) (𝓝 0) := by
    have hq0 : Tendsto (fun q : ℂ => q - p) (𝓝[≠] p) (𝓝 0) := by
      have h : Tendsto (fun q : ℂ => q - p) (𝓝 p) (𝓝 (p - p)) :=
        (continuous_id.sub continuous_const).tendsto p
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using hq0.mul_const (f p - r * (p - p)⁻¹)
  simpa using h1.sub h2

/-! ## The rectangle boundary integral -/

/-- The boundary integral of `f` over the rectangle with opposite corners `z` and `w`,
in Mathlib's orientation (`Complex.integral_boundary_rect_*`): bottom edge minus top
edge plus `i` times the right edge minus `i` times the left edge. For `z` the
lower-left corner this is the counterclockwise contour integral. -/
-- no-dlmf: rectangle boundary contour integral, infra (DLMF §2.5 area)
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - ∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I * ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

section WindingIntegral

/-- Complex antiderivative along a horizontal edge: for `m ≠ p.im`,
`x ↦ ½ log((x-p.re)² + (m-p.im)²) - i·arctan((x-p.re)/(m-p.im))` differentiates to
`(x + m·i - p)⁻¹`. -/
-- no-dlmf: FTC antiderivative for the rectangle winding integral, infra
theorem hasDerivAt_horiz_antideriv (p : ℂ) {m : ℝ} (hm : m ≠ p.im) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => (↑(Real.log ((t - p.re) ^ 2 + (m - p.im) ^ 2) / 2) : ℂ)
        - I * ↑(Real.arctan ((t - p.re) / (m - p.im))))
      ((↑x + ↑m * I - p)⁻¹) x := by
  have hk0 : m - p.im ≠ 0 := sub_ne_zero.mpr hm
  have hD : 0 < (x - p.re) ^ 2 + (m - p.im) ^ 2 := by positivity
  have h₁ : HasDerivAt (fun t : ℝ => (t - p.re) ^ 2 + (m - p.im) ^ 2) (2 * (x - p.re)) x := by
    have := (((hasDerivAt_id x).sub_const p.re).pow 2).add_const ((m - p.im) ^ 2)
    simpa using this
  have h₂ : HasDerivAt (fun t : ℝ => Real.log ((t - p.re) ^ 2 + (m - p.im) ^ 2) / 2)
      ((x - p.re) / ((x - p.re) ^ 2 + (m - p.im) ^ 2)) x := by
    have := ((Real.hasDerivAt_log hD.ne').comp x h₁).div_const 2
    convert this using 1
    field_simp
  have h₃ : HasDerivAt (fun t : ℝ => Real.arctan ((t - p.re) / (m - p.im)))
      ((m - p.im) / ((x - p.re) ^ 2 + (m - p.im) ^ 2)) x := by
    have hin : HasDerivAt (fun t : ℝ => (t - p.re) / (m - p.im)) (1 / (m - p.im)) x := by
      simpa [div_eq_mul_inv] using ((hasDerivAt_id x).sub_const p.re).div_const (m - p.im)
    have := (Real.hasDerivAt_arctan ((x - p.re) / (m - p.im))).comp x hin
    convert this using 1
    field_simp
    ring
  have hF : HasDerivAt
      (fun t : ℝ => (↑(Real.log ((t - p.re) ^ 2 + (m - p.im) ^ 2) / 2) : ℂ)
        - I * ↑(Real.arctan ((t - p.re) / (m - p.im))))
      (↑((x - p.re) / ((x - p.re) ^ 2 + (m - p.im) ^ 2))
        - I * ↑((m - p.im) / ((x - p.re) ^ 2 + (m - p.im) ^ 2))) x :=
    h₂.ofReal_comp.sub ((h₃.ofReal_comp).const_mul I)
  convert hF using 1
  have hζ : (↑x + ↑m * I - p) = ↑(x - p.re) + ↑(m - p.im) * I := by
    simp [Complex.ext_iff]
  rw [hζ]
  have hDc : (((x - p.re) ^ 2 + (m - p.im) ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD.ne'
  have hrw : (↑((x - p.re) / ((x - p.re) ^ 2 + (m - p.im) ^ 2)) : ℂ)
      - I * ↑((m - p.im) / ((x - p.re) ^ 2 + (m - p.im) ^ 2))
      = (↑(x - p.re) - ↑(m - p.im) * I) / (((x - p.re) ^ 2 + (m - p.im) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hrw]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_div_assoc', div_eq_one_iff_eq hDc]
  push_cast
  linear_combination (-((m : ℂ) - p.im) ^ 2) * Complex.I_sq

/-- Complex antiderivative along a vertical edge: for `h ≠ p.re`,
`y ↦ arctan((y-p.im)/(h-p.re)) - i·½ log((h-p.re)² + (y-p.im)²)` differentiates to
`(h + y·i - p)⁻¹`. -/
-- no-dlmf: FTC antiderivative for the rectangle winding integral, infra
theorem hasDerivAt_vert_antideriv (p : ℂ) {h : ℝ} (hh : h ≠ p.re) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => (↑(Real.arctan ((t - p.im) / (h - p.re))) : ℂ)
        - I * ↑(Real.log ((h - p.re) ^ 2 + (t - p.im) ^ 2) / 2))
      ((↑h + ↑y * I - p)⁻¹) y := by
  have hH0 : h - p.re ≠ 0 := sub_ne_zero.mpr hh
  have hD : 0 < (h - p.re) ^ 2 + (y - p.im) ^ 2 := by positivity
  have h₁ : HasDerivAt (fun t : ℝ => (h - p.re) ^ 2 + (t - p.im) ^ 2) (2 * (y - p.im)) y := by
    have := (((hasDerivAt_id y).sub_const p.im).pow 2).const_add ((h - p.re) ^ 2)
    simpa using this
  have h₂ : HasDerivAt (fun t : ℝ => Real.log ((h - p.re) ^ 2 + (t - p.im) ^ 2) / 2)
      ((y - p.im) / ((h - p.re) ^ 2 + (y - p.im) ^ 2)) y := by
    have := ((Real.hasDerivAt_log hD.ne').comp y h₁).div_const 2
    convert this using 1
    field_simp
  have h₃ : HasDerivAt (fun t : ℝ => Real.arctan ((t - p.im) / (h - p.re)))
      ((h - p.re) / ((h - p.re) ^ 2 + (y - p.im) ^ 2)) y := by
    have hin : HasDerivAt (fun t : ℝ => (t - p.im) / (h - p.re)) (1 / (h - p.re)) y := by
      simpa [div_eq_mul_inv] using ((hasDerivAt_id y).sub_const p.im).div_const (h - p.re)
    have := (Real.hasDerivAt_arctan ((y - p.im) / (h - p.re))).comp y hin
    convert this using 1
    field_simp
  have hF : HasDerivAt
      (fun t : ℝ => (↑(Real.arctan ((t - p.im) / (h - p.re))) : ℂ)
        - I * ↑(Real.log ((h - p.re) ^ 2 + (t - p.im) ^ 2) / 2))
      (↑((h - p.re) / ((h - p.re) ^ 2 + (y - p.im) ^ 2))
        - I * ↑((y - p.im) / ((h - p.re) ^ 2 + (y - p.im) ^ 2))) y :=
    h₃.ofReal_comp.sub ((h₂.ofReal_comp).const_mul I)
  convert hF using 1
  have hζ : (↑h + ↑y * I - p) = ↑(h - p.re) + ↑(y - p.im) * I := by
    simp [Complex.ext_iff]
  rw [hζ]
  have hDc : (((h - p.re) ^ 2 + (y - p.im) ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD.ne'
  have hrw : (↑((h - p.re) / ((h - p.re) ^ 2 + (y - p.im) ^ 2)) : ℂ)
      - I * ↑((y - p.im) / ((h - p.re) ^ 2 + (y - p.im) ^ 2))
      = (↑(h - p.re) - ↑(y - p.im) * I) / (((h - p.re) ^ 2 + (y - p.im) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hrw]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_div_assoc', div_eq_one_iff_eq hDc]
  push_cast
  linear_combination (-((y : ℂ) - p.im) ^ 2) * Complex.I_sq

/-- Horizontal-edge integral of `(· - p)⁻¹` at height `m ≠ p.im`, by FTC. -/
-- no-dlmf: rectangle-edge winding integral, infra
theorem integral_horiz_inv (p : ℂ) {m : ℝ} (a b : ℝ) (hm : m ≠ p.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + m * I - p)⁻¹) =
      ((↑(Real.log ((b - p.re) ^ 2 + (m - p.im) ^ 2) / 2) : ℂ)
        - I * ↑(Real.arctan ((b - p.re) / (m - p.im))))
      - ((↑(Real.log ((a - p.re) ^ 2 + (m - p.im) ^ 2) / 2) : ℂ)
        - I * ↑(Real.arctan ((a - p.re) / (m - p.im)))) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_horiz_antideriv p hm x) ?_
  refine Continuous.intervalIntegrable ?_ a b
  refine ((continuous_ofReal.add continuous_const).sub continuous_const).inv₀ fun x h0 => ?_
  apply hm
  have h1 : m - p.im = 0 := by simpa using congrArg Complex.im h0
  exact sub_eq_zero.mp h1

/-- Vertical-edge integral of `(· - p)⁻¹` at abscissa `h ≠ p.re`, by FTC. -/
-- no-dlmf: rectangle-edge winding integral, infra
theorem integral_vert_inv (p : ℂ) {h : ℝ} (a b : ℝ) (hh : h ≠ p.re) :
    (∫ y : ℝ in a..b, ((h : ℂ) + y * I - p)⁻¹) =
      ((↑(Real.arctan ((b - p.im) / (h - p.re))) : ℂ)
        - I * ↑(Real.log ((h - p.re) ^ 2 + (b - p.im) ^ 2) / 2))
      - ((↑(Real.arctan ((a - p.im) / (h - p.re))) : ℂ)
        - I * ↑(Real.log ((h - p.re) ^ 2 + (a - p.im) ^ 2) / 2)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_vert_antideriv p hh y) ?_
  refine Continuous.intervalIntegrable ?_ a b
  refine ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
    continuous_const).inv₀ fun y h0 => ?_
  apply hh
  have h1 : h - p.re = 0 := by simpa using congrArg Complex.re h0
  exact sub_eq_zero.mp h1

/-- **The rectangle winding integral**: the boundary integral of `(z - p)⁻¹` over a
rectangle containing `p` in its open interior equals `2πi`. The four edges contribute
`log` terms that cancel around the corners and eight `arctan` terms — the angles
subtended by the corners — that sum to `2π` via `arctan t + arctan t⁻¹ = ±π/2`. -/
-- no-dlmf: rectangle winding number 1 (∮ dz/(z-p) = 2πi), infra (DLMF §2.5 area)
theorem rectBoundaryIntegral_inv_sub_pole {z w p : ℂ}
    (h₁ : z.re < p.re) (h₂ : p.re < w.re) (h₃ : z.im < p.im) (h₄ : p.im < w.im) :
    rectBoundaryIntegral (fun q => (q - p)⁻¹) z w = 2 * π * I := by
  unfold rectBoundaryIntegral
  rw [show (∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - p)⁻¹)
        = _ from integral_horiz_inv p z.re w.re h₃.ne,
      show (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - p)⁻¹)
        = _ from integral_horiz_inv p z.re w.re h₄.ne',
      show (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - p)⁻¹)
        = _ from integral_vert_inv p z.im w.im h₂.ne',
      show (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - p)⁻¹)
        = _ from integral_vert_inv p z.im w.im h₁.ne]
  have ha0 : z.re - p.re < 0 := sub_neg.mpr h₁
  have hb0 : 0 < w.re - p.re := sub_pos.mpr h₂
  have hc0 : z.im - p.im < 0 := sub_neg.mpr h₃
  have hd0 : 0 < w.im - p.im := sub_pos.mpr h₄
  -- the four corner-angle identities
  have i₁ : Real.arctan ((w.im - p.im) / (w.re - p.re))
      = π / 2 - Real.arctan ((w.re - p.re) / (w.im - p.im)) := by
    rw [← inv_div (w.re - p.re) (w.im - p.im)]
    exact Real.arctan_inv_of_pos (div_pos hb0 hd0)
  have i₂ : Real.arctan ((z.im - p.im) / (w.re - p.re))
      = -(π / 2) - Real.arctan ((w.re - p.re) / (z.im - p.im)) := by
    rw [← inv_div (w.re - p.re) (z.im - p.im)]
    exact Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hb0 hc0)
  have i₃ : Real.arctan ((z.im - p.im) / (z.re - p.re))
      = π / 2 - Real.arctan ((z.re - p.re) / (z.im - p.im)) := by
    rw [← inv_div (z.re - p.re) (z.im - p.im)]
    exact Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha0 hc0)
  have i₄ : Real.arctan ((w.im - p.im) / (z.re - p.re))
      = -(π / 2) - Real.arctan ((z.re - p.re) / (w.im - p.im)) := by
    rw [← inv_div (z.re - p.re) (w.im - p.im)]
    exact Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha0 hd0)
  apply Complex.ext
  · simp only [add_re, sub_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_im, sub_im,
      re_ofNat, im_ofNat]
    ring
  · simp only [add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_re, sub_re,
      re_ofNat, im_ofNat]
    rw [i₁, i₂, i₃, i₄]
    ring

end WindingIntegral

/-! ## The one-pole rectangle theorem -/

section RectangleOnePole

variable {f : ℂ → ℂ} {z w p r : ℂ}

/-- **Residue theorem for a rectangle with one (simple) interior pole.** Let `f` be
holomorphic on the closed rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]` minus the
single interior point `p`, with `(q - p) * f q → r` as `q → p`. Then the boundary
integral of `f` over the rectangle equals `2πi·r`.

This is the exact contour-shift step of the Mellin–Barnes method (DLMF §2.5): moving
a vertical contour across one Γ-pole picks up `2πi` times the residue. -/
-- no-dlmf: one-pole rectangle residue theorem, contour infra (DLMF §2.5 area)
theorem rectangle_one_pole
    (h₁ : z.re < p.re) (h₂ : p.re < w.re) (h₃ : z.im < p.im) (h₄ : p.im < w.im)
    (hd : ∀ q ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {p}, DifferentiableAt ℂ f q)
    (hlim : Tendsto (fun q => (q - p) * f q) (𝓝[≠] p) (𝓝 r)) :
    rectBoundaryIntegral f z w = 2 * π * I * r := by
  have hzw_re : z.re < w.re := h₁.trans h₂
  have hzw_im : z.im < w.im := h₃.trans h₄
  -- the open rectangle
  set U : Set ℂ := Ioo z.re w.re ×ℂ Ioo z.im w.im with hU
  have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hpU : p ∈ U := ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  have hUsub : U ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := fun q hq =>
    ⟨uIcc_of_le hzw_re.le ▸ Ioo_subset_Icc_self hq.1,
      uIcc_of_le hzw_im.le ▸ Ioo_subset_Icc_self hq.2⟩
  -- the regularized function and its removable extension
  set g : ℂ → ℂ := fun q => f q - r * (q - p)⁻¹ with hg
  have hgd : ∀ q ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {p}, DifferentiableAt ℂ g q := by
    intro q hq
    exact (hd q hq).sub
      (((differentiableAt_id.sub_const p).inv (sub_ne_zero.mpr hq.2)).const_mul r)
  set G : ℂ → ℂ := update g p (limUnder (𝓝[≠] p) g) with hG
  have hGd : DifferentiableOn ℂ G U := by
    refine differentiableOn_update_limUnder_of_isLittleO (hUopen.mem_nhds hpU) ?_ ?_
    · exact fun q hq => (hgd q ⟨hUsub hq.1, hq.2⟩).differentiableWithinAt
    · exact isLittleO_sub_singular_part hlim
  -- G is differentiable at every point of the closed rectangle
  have hGd_all : ∀ q ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], DifferentiableAt ℂ G q := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      exact hGd.differentiableAt (hUopen.mem_nhds hpU)
    · have hev : G =ᶠ[𝓝 q] g := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with x hx
        exact update_of_ne hx _ _
      exact (hgd q ⟨hq, hqp⟩).congr_of_eventuallyEq hev
  -- Cauchy–Goursat for G on the rectangle
  have hG0 := integral_boundary_rect_eq_zero_of_differentiableOn G z w
    (fun q hq => (hGd_all q hq).differentiableWithinAt)
  -- edge points avoid p, so the boundary integrals of G and g agree
  have hbot : ∀ x : ℝ, (↑x + ↑z.im * I : ℂ) ≠ p := fun x h => by
    apply h₃.ne
    simpa using congrArg Complex.im h
  have htop : ∀ x : ℝ, (↑x + ↑w.im * I : ℂ) ≠ p := fun x h => by
    apply h₄.ne'
    simpa using congrArg Complex.im h
  have hright : ∀ y : ℝ, (↑w.re + ↑y * I : ℂ) ≠ p := fun y h => by
    apply h₂.ne'
    simpa using congrArg Complex.re h
  have hleft : ∀ y : ℝ, (↑z.re + ↑y * I : ℂ) ≠ p := fun y h => by
    apply h₁.ne
    simpa using congrArg Complex.re h
  have hg0 : rectBoundaryIntegral g z w = 0 := by
    unfold rectBoundaryIntegral
    have e₁ : (∫ x : ℝ in z.re..w.re, g (↑x + ↑z.im * I))
        = ∫ x : ℝ in z.re..w.re, G (↑x + ↑z.im * I) :=
      intervalIntegral.integral_congr fun x _ => (update_of_ne (hbot x) _ _).symm
    have e₂ : (∫ x : ℝ in z.re..w.re, g (↑x + ↑w.im * I))
        = ∫ x : ℝ in z.re..w.re, G (↑x + ↑w.im * I) :=
      intervalIntegral.integral_congr fun x _ => (update_of_ne (htop x) _ _).symm
    have e₃ : (∫ y : ℝ in z.im..w.im, g (↑w.re + ↑y * I))
        = ∫ y : ℝ in z.im..w.im, G (↑w.re + ↑y * I) :=
      intervalIntegral.integral_congr fun y _ => (update_of_ne (hright y) _ _).symm
    have e₄ : (∫ y : ℝ in z.im..w.im, g (↑z.re + ↑y * I))
        = ∫ y : ℝ in z.im..w.im, G (↑z.re + ↑y * I) :=
      intervalIntegral.integral_congr fun y _ => (update_of_ne (hleft y) _ _).symm
    rw [e₁, e₂, e₃, e₄]
    simpa only [smul_eq_mul] using hG0
  -- split each edge integral: ∫ f = ∫ g + r ∫ (·-p)⁻¹
  have hsplit : ∀ (φ : ℝ → ℂ) (a b : ℝ), Continuous φ → (∀ x, φ x ≠ p) →
      (∀ x ∈ [[a, b]], φ x ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) →
      (∫ x in a..b, f (φ x)) = (∫ x in a..b, g (φ x)) + r * ∫ x in a..b, (φ x - p)⁻¹ := by
    intro φ a b hφ hφp hφmem
    have hinv : ContinuousOn (fun x => (φ x - p)⁻¹) [[a, b]] :=
      ((hφ.sub continuous_const).continuousOn).inv₀ fun x _ => sub_ne_zero.mpr (hφp x)
    have hfc : ContinuousOn (fun x => f (φ x)) [[a, b]] := fun x hx =>
      (((hd (φ x) ⟨hφmem x hx, hφp x⟩).continuousAt).comp hφ.continuousAt).continuousWithinAt
    have hfint : IntervalIntegrable (fun x => f (φ x)) MeasureTheory.volume a b :=
      hfc.intervalIntegrable
    have hinvint : IntervalIntegrable (fun x => r * (φ x - p)⁻¹) MeasureTheory.volume a b :=
      (continuousOn_const.mul hinv).intervalIntegrable
    have hgi : (∫ x in a..b, g (φ x))
        = (∫ x in a..b, f (φ x)) - ∫ x in a..b, r * (φ x - p)⁻¹ :=
      intervalIntegral.integral_sub hfint hinvint
    rw [hgi, intervalIntegral.integral_const_mul]
    ring
  have hb := hsplit (fun x => ↑x + ↑z.im * I) z.re w.re
    (continuous_ofReal.add continuous_const) hbot
    (fun x hx => mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩)
  have ht := hsplit (fun x => ↑x + ↑w.im * I) z.re w.re
    (continuous_ofReal.add continuous_const) htop
    (fun x hx => mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩)
  have hri := hsplit (fun y => ↑w.re + ↑y * I) z.im w.im
    (continuous_const.add (continuous_ofReal.mul continuous_const)) hright
    (fun y hy => mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩)
  have hl := hsplit (fun y => ↑z.re + ↑y * I) z.im w.im
    (continuous_const.add (continuous_ofReal.mul continuous_const)) hleft
    (fun y hy => mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩)
  have hwind := rectBoundaryIntegral_inv_sub_pole h₁ h₂ h₃ h₄
  unfold rectBoundaryIntegral at hg0 hwind ⊢
  simp only at hb ht hri hl hg0 hwind
  rw [hb, ht, hri, hl]
  linear_combination hg0 + r * hwind

/-- One-pole rectangle theorem, residue form:
`∮_{∂rect} f = 2πi · residue f p`. -/
-- no-dlmf: one-pole rectangle residue theorem (residue form), contour infra
theorem rectangle_one_pole_residue
    (h₁ : z.re < p.re) (h₂ : p.re < w.re) (h₃ : z.im < p.im) (h₄ : p.im < w.im)
    (hd : ∀ q ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ {p}, DifferentiableAt ℂ f q)
    (hlim : Tendsto (fun q => (q - p) * f q) (𝓝[≠] p) (𝓝 r)) :
    rectBoundaryIntegral f z w = 2 * π * I * residue f p := by
  rw [rectangle_one_pole h₁ h₂ h₃ h₄ hd hlim]
  congr 1
  symm
  -- a small ball around p sits inside the rectangle
  have hε0 : 0 < min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im)) :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  refine residue_simple_pole hε0 (fun q hq => ?_) hlim
  refine hd q ⟨?_, hq.2⟩
  obtain ⟨hq1, _⟩ := hq
  rw [mem_ball, dist_eq_norm] at hq1
  have hre : |(q - p).re| < min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im)) :=
    lt_of_le_of_lt (abs_re_le_norm _) hq1
  have him : |(q - p).im| < min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im)) :=
    lt_of_le_of_lt (abs_im_le_norm _) hq1
  rw [abs_lt] at hre him
  simp only [sub_re, sub_im] at hre him
  have b₁ : min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im))
      ≤ p.re - z.re := (min_le_left _ _).trans (min_le_left _ _)
  have b₂ : min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im))
      ≤ w.re - p.re := (min_le_left _ _).trans (min_le_right _ _)
  have b₃ : min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im))
      ≤ p.im - z.im := (min_le_right _ _).trans (min_le_left _ _)
  have b₄ : min (min (p.re - z.re) (w.re - p.re)) (min (p.im - z.im) (w.im - p.im))
      ≤ w.im - p.im := (min_le_right _ _).trans (min_le_right _ _)
  refine mem_reProdIm.mpr ⟨?_, ?_⟩
  · rw [uIcc_of_le (h₁.trans h₂).le]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  · rw [uIcc_of_le (h₃.trans h₄).le]
    exact ⟨by linarith [him.1], by linarith [him.2]⟩

end RectangleOnePole

/-! ## The finite-pole rectangle theorem -/

/-- **Residue theorem for a rectangle with finitely many simple poles.** Every
listed pole lies in the open rectangle, `f` is holomorphic on the closed
rectangle away from those poles, and `r p` is its simple-pole coefficient at
`p`. -/
-- no-dlmf: finite-pole rectangle residue theorem, contour infra
theorem rectangle_finite_simple_poles {f : ℂ → ℂ} {z w : ℂ}
    (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hd : ∀ q ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ (P : Set ℂ),
      DifferentiableAt ℂ f q)
    (hlim : ∀ p ∈ P, Tendsto (fun q ↦ (q - p) * f q) (𝓝[≠] p) (𝓝 (r p))) :
    rectBoundaryIntegral f z w = 2 * π * I * ∑ p ∈ P, r p := by
  induction P using Finset.induction_on generalizing f with
  | empty =>
      rw [Finset.sum_empty, mul_zero]
      exact integral_boundary_rect_eq_zero_of_differentiableOn f z w fun q hq ↦
        (hd q ⟨hq, by simp⟩).differentiableWithinAt
  | @insert p P hp ih =>
      have hpopen := hP p (Finset.mem_insert_self p P)
      have hzwre : z.re < w.re := hpopen.1.1.trans hpopen.1.2
      have hzwim : z.im < w.im := hpopen.2.1.trans hpopen.2.2
      have hlimp := hlim p (Finset.mem_insert_self p P)
      set g : ℂ → ℂ := fun q ↦ f q - r p * (q - p)⁻¹ with hg
      set G : ℂ → ℂ := update g p (limUnder (𝓝[≠] p) g) with hG
      have hopen : IsOpen ((Ioo z.re w.re ×ℂ Ioo z.im w.im) \ (P : Set ℂ)) :=
        (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff P.isClosed
      have hpmem : p ∈ (Ioo z.re w.re ×ℂ Ioo z.im w.im) \ (P : Set ℂ) :=
        ⟨hpopen, hp⟩
      have hopen_sub : Ioo z.re w.re ×ℂ Ioo z.im w.im ⊆
          [[z.re, w.re]] ×ℂ [[z.im, w.im]] := fun q hq ↦
        ⟨uIcc_of_le hzwre.le ▸ Ioo_subset_Icc_self hq.1,
          uIcc_of_le hzwim.le ▸ Ioo_subset_Icc_self hq.2⟩
      have hgd : DifferentiableOn ℂ g
          (((Ioo z.re w.re ×ℂ Ioo z.im w.im) \ (P : Set ℂ)) \ {p}) := by
        intro q hq
        have hqnot : q ∉ (insert p P : Finset ℂ) := by
          rw [Finset.mem_insert]
          exact not_or_intro (by simpa using hq.2) hq.1.2
        exact ((hd q ⟨hopen_sub hq.1.1, by simpa using hqnot⟩).sub
          (((differentiableAt_id.sub_const p).inv
            (sub_ne_zero.mpr (by simpa using hq.2))).const_mul (r p))).differentiableWithinAt
      have hGd : DifferentiableOn ℂ G
          ((Ioo z.re w.re ×ℂ Ioo z.im w.im) \ (P : Set ℂ)) := by
        simpa only [hG] using differentiableOn_update_limUnder_of_isLittleO
          (hopen.mem_nhds hpmem) hgd (isLittleO_sub_singular_part hlimp)
      have hGd_closed : ∀ q ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ (P : Set ℂ),
          DifferentiableAt ℂ G q := by
        intro q hq
        by_cases hqp : q = p
        · subst q
          exact hGd.differentiableAt (hopen.mem_nhds hpmem)
        · have hev : G =ᶠ[𝓝 q] g := by
            filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with x hx
            exact update_of_ne hx _ _
          have hqnot : q ∉ (insert p P : Finset ℂ) := by
            rw [Finset.mem_insert]
            exact not_or_intro hqp hq.2
          exact ((hd q ⟨hq.1, by simpa using hqnot⟩).sub
            (((differentiableAt_id.sub_const p).inv (sub_ne_zero.mpr hqp)).const_mul
              (r p))).congr_of_eventuallyEq hev
      have hlimG : ∀ q ∈ P,
          Tendsto (fun x ↦ (x - q) * G x) (𝓝[≠] q) (𝓝 (r q)) := by
        intro q hq
        have hqp : q ≠ p := fun h ↦ hp (h ▸ hq)
        have hev : G =ᶠ[𝓝 q] g := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with x hx
          exact update_of_ne hx _ _
        have hprodEq : (fun x ↦ (x - q) * G x) =ᶠ[𝓝[≠] q]
            (fun x ↦ (x - q) * g x) := by
          filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with x hx
          rw [hx]
        rw [tendsto_congr' hprodEq]
        have hzero : Tendsto (fun x : ℂ ↦ x - q) (𝓝[≠] q) (𝓝 0) := by
          have h : Tendsto (fun x : ℂ ↦ x - q) (𝓝 q) (𝓝 (q - q)) :=
            continuousAt_id.sub_const q
          simpa using h.mono_left nhdsWithin_le_nhds
        have hinv : Tendsto (fun x : ℂ ↦ (x - p)⁻¹) (𝓝[≠] q) (𝓝 ((q - p)⁻¹)) :=
          ((continuousAt_id.sub_const p).inv₀ (sub_ne_zero.mpr hqp)).mono_left
            nhdsWithin_le_nhds
        have hreg : Tendsto (fun x ↦ (x - q) * (r p * (x - p)⁻¹))
            (𝓝[≠] q) (𝓝 0) := by
          simpa using hzero.mul (tendsto_const_nhds.mul hinv)
        simpa only [hg, mul_sub, sub_zero] using
          (hlim q (Finset.mem_insert_of_mem hq)).sub hreg
      have hIh := ih (f := G) (fun q hq ↦ hP q (Finset.mem_insert_of_mem hq))
        hGd_closed hlimG
      have hbot : ∀ x : ℝ, (↑x + ↑z.im * I : ℂ) ≠ p := fun x h ↦ by
        exact hpopen.2.1.ne (by simpa using congrArg Complex.im h)
      have htop : ∀ x : ℝ, (↑x + ↑w.im * I : ℂ) ≠ p := fun x h ↦ by
        exact hpopen.2.2.ne' (by simpa using congrArg Complex.im h)
      have hright : ∀ y : ℝ, (↑w.re + ↑y * I : ℂ) ≠ p := fun y h ↦ by
        exact hpopen.1.2.ne' (by simpa using congrArg Complex.re h)
      have hleft : ∀ y : ℝ, (↑z.re + ↑y * I : ℂ) ≠ p := fun y h ↦ by
        exact hpopen.1.1.ne (by simpa using congrArg Complex.re h)
      have hGg : rectBoundaryIntegral G z w = rectBoundaryIntegral g z w := by
        unfold rectBoundaryIntegral
        have e₁ : (∫ x in z.re..w.re, G (↑x + ↑z.im * I)) =
            ∫ x in z.re..w.re, g (↑x + ↑z.im * I) :=
          intervalIntegral.integral_congr fun x _ ↦ update_of_ne (hbot x) _ _
        have e₂ : (∫ x in z.re..w.re, G (↑x + ↑w.im * I)) =
            ∫ x in z.re..w.re, g (↑x + ↑w.im * I) :=
          intervalIntegral.integral_congr fun x _ ↦ update_of_ne (htop x) _ _
        have e₃ : (∫ y in z.im..w.im, G (↑w.re + ↑y * I)) =
            ∫ y in z.im..w.im, g (↑w.re + ↑y * I) :=
          intervalIntegral.integral_congr fun y _ ↦ update_of_ne (hright y) _ _
        have e₄ : (∫ y in z.im..w.im, G (↑z.re + ↑y * I)) =
            ∫ y in z.im..w.im, g (↑z.re + ↑y * I) :=
          intervalIntegral.integral_congr fun y _ ↦ update_of_ne (hleft y) _ _
        rw [e₁, e₂, e₃, e₄]
      have hsplit : rectBoundaryIntegral g z w = rectBoundaryIntegral f z w -
          r p * rectBoundaryIntegral (fun q ↦ (q - p)⁻¹) z w := by
        have hcont (φ : ℝ → ℂ) (a b : ℝ) (hφ : Continuous φ)
            (hφp : ∀ x, φ x ≠ p)
            (hφnot : ∀ x, φ x ∉ (insert p P : Finset ℂ))
            (hφmem : ∀ x ∈ [[a, b]],
              φ x ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
            (∫ x in a..b, g (φ x)) = (∫ x in a..b, f (φ x)) -
              r p * ∫ x in a..b, (φ x - p)⁻¹ := by
          have hfc : ContinuousOn (fun x ↦ f (φ x)) [[a, b]] := fun x hx ↦
            ((hd (φ x) ⟨hφmem x hx, by simpa using hφnot x⟩).continuousAt.comp
              hφ.continuousAt).continuousWithinAt
          have hfint : IntervalIntegrable (fun x ↦ f (φ x)) MeasureTheory.volume a b :=
            hfc.intervalIntegrable
          have hinvint : IntervalIntegrable (fun x ↦ r p * (φ x - p)⁻¹)
              MeasureTheory.volume a b :=
            (continuousOn_const.mul (((hφ.sub continuous_const).continuousOn).inv₀
              (fun x _ ↦ sub_ne_zero.mpr (hφp x)))).intervalIntegrable
          rw [show (∫ x in a..b, g (φ x)) =
              (∫ x in a..b, f (φ x)) - ∫ x in a..b, r p * (φ x - p)⁻¹ by
            exact intervalIntegral.integral_sub hfint hinvint,
            intervalIntegral.integral_const_mul]
        have hb := hcont (fun x ↦ ↑x + ↑z.im * I) z.re w.re
          (continuous_ofReal.add continuous_const) hbot (fun x hmem ↦
            (hP _ hmem).2.1.ne (by simp))
          (fun x hx ↦ mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩)
        have ht := hcont (fun x ↦ ↑x + ↑w.im * I) z.re w.re
          (continuous_ofReal.add continuous_const) htop (fun x hmem ↦
            (hP _ hmem).2.2.ne' (by simp))
          (fun x hx ↦ mem_reProdIm.mpr ⟨by simpa using hx, by simp⟩)
        have hr := hcont (fun y ↦ ↑w.re + ↑y * I) z.im w.im
          (continuous_const.add (continuous_ofReal.mul continuous_const)) hright
          (fun y hmem ↦ (hP _ hmem).1.2.ne' (by simp))
          (fun y hy ↦ mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩)
        have hl := hcont (fun y ↦ ↑z.re + ↑y * I) z.im w.im
          (continuous_const.add (continuous_ofReal.mul continuous_const)) hleft
          (fun y hmem ↦ (hP _ hmem).1.1.ne (by simp))
          (fun y hy ↦ mem_reProdIm.mpr ⟨by simp, by simpa using hy⟩)
        unfold rectBoundaryIntegral
        rw [hb, ht, hr, hl]
        ring
      have hwind := rectBoundaryIntegral_inv_sub_pole hpopen.1.1 hpopen.1.2
        hpopen.2.1 hpopen.2.2
      rw [hGg, hsplit, hwind] at hIh
      rw [Finset.sum_insert hp]
      linear_combination hIh

/-! ## The one-pole circle theorem (off-center pole) -/

section CircleOnePole

variable {f : ℂ → ℂ} {c p r : ℂ} {R : ℝ}

/-- **Residue theorem for a circle with one (simple) interior pole**, in general
position: `f` holomorphic on the closed disc `closedBall c R` minus the single
interior point `p`, with `(q - p) * f q → r` at `p`, gives
`∮_{|z-c|=R} f = 2πi · residue f p`. -/
-- no-dlmf: one-pole circle residue theorem (off-center pole), contour infra
theorem circle_one_pole (hR : 0 < R) (hp : p ∈ ball c R)
    (hd : ∀ q ∈ closedBall c R \ {p}, DifferentiableAt ℂ f q)
    (hlim : Tendsto (fun q => (q - p) * f q) (𝓝[≠] p) (𝓝 r)) :
    (∮ z in C(c, R), f z) = 2 * π * I * residue f p := by
  -- residue f p = r via a small ball around p inside the disc
  have hres : residue f p = r := by
    refine residue_simple_pole (R := R - dist p c) (by simpa [sub_pos] using mem_ball.mp hp)
      (fun q hq => hd q ⟨?_, hq.2⟩) hlim
    have hq1 := mem_ball.mp hq.1
    rw [mem_closedBall]
    calc dist q c ≤ dist q p + dist p c := dist_triangle q p c
      _ ≤ R := by linarith
  rw [hres]
  -- the regularized function and its removable extension
  set g : ℂ → ℂ := fun q => f q - r * (q - p)⁻¹ with hg
  have hgd : ∀ q ∈ closedBall c R \ {p}, DifferentiableAt ℂ g q := fun q hq =>
    (hd q hq).sub (((differentiableAt_id.sub_const p).inv (sub_ne_zero.mpr hq.2)).const_mul r)
  set G : ℂ → ℂ := update g p (limUnder (𝓝[≠] p) g) with hG
  have hGd : DifferentiableOn ℂ G (ball c R) := by
    refine differentiableOn_update_limUnder_of_isLittleO (isOpen_ball.mem_nhds hp) ?_ ?_
    · exact fun q hq =>
        (hgd q ⟨ball_subset_closedBall hq.1, hq.2⟩).differentiableWithinAt
    · exact isLittleO_sub_singular_part hlim
  have hGd_all : ∀ q ∈ closedBall c R, DifferentiableAt ℂ G q := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp
      exact hGd.differentiableAt (isOpen_ball.mem_nhds hp)
    · have hev : G =ᶠ[𝓝 q] g := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with x hx
        exact update_of_ne hx _ _
      exact (hgd q ⟨hq, hqp⟩).congr_of_eventuallyEq hev
  -- Cauchy–Goursat for G on the disc
  have hG0 : (∮ z in C(c, R), G z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
      (fun q hq => (hGd_all q hq).continuousAt.continuousWithinAt)
      fun q hq => hGd_all q (ball_subset_closedBall hq.1)
  -- G = g on the circle (p is interior, hence off the sphere)
  have hsphere : ∀ q ∈ sphere c R, q ≠ p := by
    rintro q hq rfl
    rw [mem_sphere] at hq
    rw [mem_ball] at hp
    exact absurd hq hp.ne
  have hg0 : (∮ z in C(c, R), g z) = 0 := by
    rw [← hG0]
    refine circleIntegral.integral_congr hR.le fun q hq => ?_
    exact (update_of_ne (hsphere q hq) _ _).symm
  -- split: ∮ f = ∮ g + r ∮ (·-p)⁻¹
  have hfint : CircleIntegrable f c R := by
    refine ContinuousOn.circleIntegrable hR.le fun q hq => ?_
    exact ((hd q ⟨sphere_subset_closedBall hq, hsphere q hq⟩).continuousAt).continuousWithinAt
  have hinvint : CircleIntegrable (fun q => r * (q - p)⁻¹) c R := by
    refine ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul ?_)
    exact ((continuous_id.sub continuous_const).continuousOn).inv₀ fun q hq =>
      sub_ne_zero.mpr (hsphere q hq)
  have hsub : (∮ z in C(c, R), g z)
      = (∮ z in C(c, R), f z) - ∮ z in C(c, R), r * (z - p)⁻¹ :=
    circleIntegral.integral_sub hfint hinvint
  have hwind : (∮ z in C(c, R), r * (z - p)⁻¹) = r * (2 * π * I) := by
    rw [← circleIntegral.integral_sub_inv_of_mem_ball hp]
    exact circleIntegral.integral_const_mul r _ c R ▸ rfl
  rw [hg0, hwind] at hsub
  have hf : (∮ z in C(c, R), f z) = r * (2 * π * I) := sub_eq_zero.mp hsub.symm
  rw [hf]
  ring

end CircleOnePole

/-! ## The finite-pole circle theorem -/

/-- **Residue theorem for a circle with finitely many simple poles.** Every
listed pole lies strictly inside the circle, `f` is holomorphic on the closed
disc away from those poles, and `r p` is the corresponding simple-pole
coefficient. -/
-- no-dlmf: finite-pole circle residue theorem, contour infra
theorem circle_finite_simple_poles {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (P : Finset ℂ) (r : ℂ → ℂ)
    (hP : ∀ p ∈ P, p ∈ ball c R)
    (hd : ∀ q ∈ closedBall c R \ (P : Set ℂ), DifferentiableAt ℂ f q)
    (hlim : ∀ p ∈ P, Tendsto (fun q ↦ (q - p) * f q) (𝓝[≠] p) (𝓝 (r p))) :
    (∮ z in C(c, R), f z) = 2 * π * I * ∑ p ∈ P, r p := by
  induction P using Finset.induction_on generalizing f with
  | empty =>
      rw [Finset.sum_empty, mul_zero]
      exact circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
        (fun q hq ↦ (hd q ⟨hq, by simp⟩).continuousAt.continuousWithinAt)
        (fun q hq ↦ hd q ⟨ball_subset_closedBall hq.1, by simp⟩)
  | @insert p P hp ih =>
      have hpball : p ∈ ball c R := hP p (Finset.mem_insert_self p P)
      have hlimp := hlim p (Finset.mem_insert_self p P)
      set g : ℂ → ℂ := fun q ↦ f q - r p * (q - p)⁻¹ with hg
      set G : ℂ → ℂ := update g p (limUnder (𝓝[≠] p) g) with hG
      have hopen : IsOpen (ball c R \ (P : Set ℂ)) :=
        isOpen_ball.sdiff P.isClosed
      have hpmem : p ∈ ball c R \ (P : Set ℂ) := ⟨hpball, hp⟩
      have hgd : DifferentiableOn ℂ g ((ball c R \ (P : Set ℂ)) \ {p}) := by
        intro q hq
        have hqnot : q ∉ (insert p P : Finset ℂ) := by
          have hqp' : q ≠ p := by simpa using hq.2
          rw [Finset.mem_insert]
          exact not_or_intro hqp' hq.1.2
        exact ((hd q ⟨ball_subset_closedBall hq.1.1, by simpa using hqnot⟩).sub
          (((differentiableAt_id.sub_const p).inv
            (sub_ne_zero.mpr (by simpa using hq.2))).const_mul (r p))).differentiableWithinAt
      have hGd : DifferentiableOn ℂ G (ball c R \ (P : Set ℂ)) := by
        simpa only [hG] using differentiableOn_update_limUnder_of_isLittleO
          (hopen.mem_nhds hpmem) hgd (isLittleO_sub_singular_part hlimp)
      have hGd_closed : ∀ q ∈ closedBall c R \ (P : Set ℂ), DifferentiableAt ℂ G q := by
        intro q hq
        by_cases hqp : q = p
        · subst q
          exact hGd.differentiableAt (hopen.mem_nhds hpmem)
        · have hev : G =ᶠ[𝓝 q] g := by
            filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with w hw
            exact update_of_ne hw _ _
          have hqnot : q ∉ (insert p P : Finset ℂ) := by
            rw [Finset.mem_insert]
            exact not_or_intro hqp hq.2
          have hgq : DifferentiableAt ℂ g q :=
            (hd q ⟨hq.1, by simpa using hqnot⟩).sub
              (((differentiableAt_id.sub_const p).inv (sub_ne_zero.mpr hqp)).const_mul (r p))
          exact hgq.congr_of_eventuallyEq hev
      have hlimG : ∀ q ∈ P,
          Tendsto (fun z ↦ (z - q) * G z) (𝓝[≠] q) (𝓝 (r q)) := by
        intro q hq
        have hqp : q ≠ p := fun h ↦ hp (h ▸ hq)
        have hev : G =ᶠ[𝓝 q] g := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hqp] with w hw
          exact update_of_ne hw _ _
        have hprodEq : (fun z ↦ (z - q) * G z) =ᶠ[𝓝[≠] q]
            (fun z ↦ (z - q) * g z) := by
          filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
          rw [hz]
        rw [tendsto_congr' hprodEq]
        have hreg : Tendsto (fun z ↦ (z - q) * (r p * (z - p)⁻¹))
            (𝓝[≠] q) (𝓝 0) := by
          have hzero : Tendsto (fun z : ℂ ↦ z - q) (𝓝[≠] q) (𝓝 0) := by
            have h : Tendsto (fun z : ℂ ↦ z - q) (𝓝 q) (𝓝 (q - q)) :=
              continuousAt_id.sub_const q
            simpa using h.mono_left nhdsWithin_le_nhds
          have hinv : Tendsto (fun z : ℂ ↦ (z - p)⁻¹) (𝓝[≠] q) (𝓝 ((q - p)⁻¹)) :=
            ((continuousAt_id.sub_const p).inv₀ (sub_ne_zero.mpr hqp)).mono_left nhdsWithin_le_nhds
          simpa using hzero.mul (tendsto_const_nhds.mul hinv)
        simpa only [hg, mul_sub, sub_zero] using
          (hlim q (Finset.mem_insert_of_mem hq)).sub hreg
      have hIh := ih (f := G) (fun q hq ↦ hP q (Finset.mem_insert_of_mem hq))
        hGd_closed hlimG
      have hsphere : ∀ q ∈ sphere c R, q ≠ p := by
        rintro q hq rfl
        exact (mem_ball.mp hpball).ne (mem_sphere.mp hq)
      have hGg : (∮ z in C(c, R), G z) = ∮ z in C(c, R), g z := by
        refine circleIntegral.integral_congr hR.le fun q hq ↦ ?_
        exact update_of_ne (hsphere q hq) _ _
      have hfint : CircleIntegrable f c R := by
        refine ContinuousOn.circleIntegrable hR.le fun q hq ↦ ?_
        have hqnot : q ∉ (insert p P : Finset ℂ) := by
          intro hmem
          exact (mem_ball.mp (hP q hmem)).ne (mem_sphere.mp hq)
        exact (hd q ⟨sphere_subset_closedBall hq, by simpa using hqnot⟩).continuousAt.continuousWithinAt
      have hinvint : CircleIntegrable (fun q ↦ r p * (q - p)⁻¹) c R := by
        refine ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul ?_)
        exact ((continuous_id.sub continuous_const).continuousOn).inv₀ fun q hq ↦
          sub_ne_zero.mpr (hsphere q hq)
      have hsub : (∮ z in C(c, R), g z) =
          (∮ z in C(c, R), f z) - ∮ z in C(c, R), r p * (z - p)⁻¹ :=
        circleIntegral.integral_sub hfint hinvint
      have hwind : (∮ z in C(c, R), r p * (z - p)⁻¹) = r p * (2 * π * I) := by
        rw [← circleIntegral.integral_sub_inv_of_mem_ball hpball]
        exact circleIntegral.integral_const_mul (r p) _ c R ▸ rfl
      rw [hGg, hsub, hwind] at hIh
      rw [Finset.sum_insert hp]
      linear_combination hIh

/-! ## Fidelity anchor: the Γ-pole residues (DLMF §5.2(i)) -/

section GammaResidue

/-- Telescoped Γ-recurrence: `Γ(w - n) · ∏_{k<n} (w - (k+1)) = Γ(w)` whenever no
factor vanishes. -/
-- no-dlmf: telescoped Gamma recurrence helper, infra
theorem Gamma_sub_nat_mul_prod (n : ℕ) :
    ∀ w : ℂ, (∀ k ∈ Finset.range n, w - ((k : ℂ) + 1) ≠ 0) →
      Complex.Gamma (w - n) * ∏ k ∈ Finset.range n, (w - ((k : ℂ) + 1)) = Complex.Gamma w := by
  induction n with
  | zero => intro w _; simp
  | succ n ih =>
    intro w hw
    have hlast : w - ((n : ℂ) + 1) ≠ 0 := by
      have := hw n (Finset.self_mem_range_succ n)
      simpa using this
    have hprev := ih w fun k hk =>
      hw k (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans (Nat.lt_succ_self n)))
    have hrec : Complex.Gamma (w - ((n : ℂ) + 1) + 1)
        = (w - ((n : ℂ) + 1)) * Complex.Gamma (w - ((n : ℂ) + 1)) :=
      Complex.Gamma_add_one _ hlast
    have hsimp : w - ((n : ℂ) + 1) + 1 = w - n := by ring
    rw [hsimp] at hrec
    rw [Finset.prod_range_succ]
    have hcast : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    rw [hcast]
    calc Complex.Gamma (w - ((n : ℂ) + 1))
          * ((∏ k ∈ Finset.range n, (w - ((k : ℂ) + 1))) * (w - ((n : ℂ) + 1)))
        = ((w - ((n : ℂ) + 1)) * Complex.Gamma (w - ((n : ℂ) + 1)))
          * ∏ k ∈ Finset.range n, (w - ((k : ℂ) + 1)) := by ring
      _ = Complex.Gamma (w - n) * ∏ k ∈ Finset.range n, (w - ((k : ℂ) + 1)) := by rw [← hrec]
      _ = Complex.Gamma w := hprev

/-- The simple-pole limit of `Γ` at `-n`:
`(z - (-n)) Γ(z) → (-1)ⁿ/n!` as `z → -n`. -/
-- no-dlmf: Gamma pole limit, infra for the residue anchor
theorem tendsto_sub_neg_nat_mul_Gamma (n : ℕ) :
    Tendsto (fun z : ℂ => (z - (-(n : ℂ))) * Complex.Gamma z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 ((-1) ^ n / n.factorial)) := by
  -- the polynomial denominator and its limit
  have hprodval : (∏ k ∈ Finset.range n, ((0 : ℂ) - ((k : ℂ) + 1)))
      = (-1) ^ n * n.factorial := by
    have hterm : ∀ k ∈ Finset.range n, ((0 : ℂ) - ((k : ℂ) + 1)) = -1 * ((k : ℂ) + 1) := by
      intros; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    congr 1
    have : ∀ k ∈ Finset.range n, ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by
      intros; push_cast; ring
    rw [Finset.prod_congr rfl this, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  have hprod : Tendsto (fun v : ℂ => ∏ k ∈ Finset.range n, (v - ((k : ℂ) + 1))) (𝓝 0)
      (𝓝 ((-1) ^ n * n.factorial)) := by
    have hcont : Continuous fun v : ℂ => ∏ k ∈ Finset.range n, (v - ((k : ℂ) + 1)) :=
      continuous_finsetProd _ fun k _ => continuous_id.sub continuous_const
    have := hcont.tendsto 0
    rwa [hprodval] at this
  have hne : ((-1 : ℂ)) ^ n * n.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  -- eventual identity  v·Γ(v-n) = (v·Γ(v)) / ∏ (v-(k+1))  near 0
  have hev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v * Complex.Gamma (v - n)
      = (v * Complex.Gamma v) / ∏ k ∈ Finset.range n, (v - ((k : ℂ) + 1)) := by
    have hball : ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (ball_mem_nhds _ one_pos)
    filter_upwards [hball] with v hv
    have hfac : ∀ k ∈ Finset.range n, v - ((k : ℂ) + 1) ≠ 0 := by
      intro k _ h0
      have hvk : v = (k : ℂ) + 1 := sub_eq_zero.mp h0
      rw [mem_ball, dist_zero_right, hvk] at hv
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast] at hv
      have : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      linarith
    have hΓ := Gamma_sub_nat_mul_prod n v hfac
    have hprodne : (∏ k ∈ Finset.range n, (v - ((k : ℂ) + 1))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hfac
    rw [eq_div_iff hprodne]
    linear_combination v * hΓ
  -- the limit at 0 in the shifted variable
  have hdiv := Complex.tendsto_self_mul_Gamma_nhds_zero.div
    (hprod.mono_left nhdsWithin_le_nhds) hne
  have hval : (1 : ℂ) / ((-1) ^ n * n.factorial) = (-1) ^ n / n.factorial := by
    have hinv : ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n := by
      rw [← inv_pow, inv_neg, inv_one]
    rw [one_div, mul_inv, hinv, ← div_eq_mul_inv]
  have hmain : Tendsto (fun v : ℂ => v * Complex.Gamma (v - n)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((-1) ^ n / n.factorial)) := by
    have hdiv' : Tendsto
        (fun v : ℂ => v * Complex.Gamma v / ∏ k ∈ Finset.range n, (v - ((k : ℂ) + 1)))
        (𝓝[≠] (0 : ℂ)) (𝓝 ((-1) ^ n / n.factorial)) := by
      rw [← hval]
      exact hdiv
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) hdiv'
  -- transfer along the translation z ↦ z + n
  have hmap : Tendsto (fun z : ℂ => z + n) (𝓝[≠] (-(n : ℂ))) (𝓝[≠] (0 : ℂ)) := by
    have hc : Tendsto (fun z : ℂ => z + (n : ℂ)) (𝓝 (-(n : ℂ))) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => z + (n : ℂ)) (𝓝 (-(n : ℂ))) (𝓝 (-(n : ℂ) + n)) :=
        (continuous_id.add continuous_const).tendsto _
      simpa using h
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz ⊢
    intro h0
    exact hz (by linear_combination h0)
  have hcomp := hmain.comp hmap
  refine hcomp.congr fun z => ?_
  simp only [Function.comp_apply]
  rw [add_sub_cancel_right, sub_neg_eq_add]

/-- **Fidelity anchor** (DLMF §5.2(i)): the residue of `Γ` at the simple pole `-n`
is `(-1)ⁿ/n!`. -/
-- no-dlmf: Gamma residue value at -n, anchor for MellinBarnes.gammaResidue (DLMF §5.2(i))
theorem residue_Gamma_neg_nat (n : ℕ) :
    residue Complex.Gamma (-(n : ℂ)) = (-1) ^ n / n.factorial := by
  refine residue_simple_pole one_pos (fun z hz => ?_) (tendsto_sub_neg_nat_mul_Gamma n)
  refine Complex.differentiableAt_Gamma z fun m => ?_
  intro hzm
  obtain ⟨hz1, hz2⟩ := hz
  by_cases hmn : m = n
  · exact hz2 (by simp [hzm, hmn])
  · rw [hzm, mem_ball] at hz1
    have hdist : dist (-(m : ℂ)) (-(n : ℂ)) = |(m : ℝ) - n| := by
      rw [dist_eq_norm]
      have : (-(m : ℂ)) - (-(n : ℂ)) = (((n : ℝ) - (m : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [hdist] at hz1
    have hge : (1 : ℝ) ≤ |(m : ℝ) - n| := by
      have hne : (m : ℤ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
      have h1 : (1 : ℤ) ≤ |(m : ℤ) - n| := Int.one_le_abs hne
      calc (1 : ℝ) ≤ |((m : ℤ) - n : ℤ)| := by exact_mod_cast h1
        _ = |(m : ℝ) - n| := by push_cast; rfl
    linarith

/-- The anchor equality with the Mellin–Barnes residue datum: the analytic residue of
`Γ` at `-n` is exactly `FLMF.MellinBarnes.gammaResidue n`. -/
-- no-dlmf: bridge to the MellinBarnes residue datum, infra
theorem residue_Gamma_neg_nat_eq_gammaResidue (n : ℕ) :
    residue Complex.Gamma (-(n : ℂ)) = FLMF.MellinBarnes.gammaResidue n :=
  residue_Gamma_neg_nat n

end GammaResidue

end FLMF.Methods
