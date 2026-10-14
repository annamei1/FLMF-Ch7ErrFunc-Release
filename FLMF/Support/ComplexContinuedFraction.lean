import FLMF.Support.ContinuedFraction
import FLMF.Support.VanVleck
import Mathlib.Analysis.PSeries

/-!
# Convergence of complex continued fractions with positive partial numerators

This module supplies the convergence criterion for a continued fraction over `ℂ`

```
  h + a₁/(b₁ + a₂/(b₂ + a₃/(b₃ + ⋯)))
```

whose partial **numerators** `aₙ` are *positive reals* and whose partial
**denominators** `bₙ` lie in a closed sector strictly inside the right
half-plane (`δ‖bₙ‖ ≤ Re bₙ` with `δ > 0`).  This is the shape of the classical
*S-fractions* (Stieltjes fractions) attached to special functions — for instance
the DLMF 7.18.13 fraction for the repeated integrals of `erfc`, whose partial
numerators `1/2, (n+1)/2, (n+2)/2, …` grow linearly while the partial
denominators are the constant `z` with `ℜ z > 0`.

Neither of the two criteria already in the kit covers this shape:

* the Śleszyński–Pringsheim theorem
  (`FLMF.Methods.exists_tendsto_convs_of_pringsheim`) needs
  `‖bₙ‖ ≥ ‖aₙ‖ + 1`, which fails as soon as the `aₙ` grow;
* the real Stieltjes sandwich (`FLMF.Methods.tendsto_convs_of_tails`) is
  intrinsically real (it runs on positivity and monotonicity of the
  convergents).

## The route

An **equivalence transformation** (`FLMF.Methods.equivTransform`) with the
*positive real* factors `cfScale α` normalizes every partial numerator to `1`
while multiplying the partial denominators by positive reals — which moves them
inside the *same* cone `{w : δ‖w‖ ≤ Re w}`.  Van Vleck's theorem
(`FLMF.Methods.VanVleck`, DLMF 1.12.28) then applies to the normalized fraction,
and `equivTransform_convs` transports the conclusion back.

Van Vleck's non-summability hypothesis becomes `∑ ρₙ‖bₙ‖ = ∞` for the scaling
sequence `ρ = cfScale α` (`ρ₀ = 1/α₀`, `ρₙρₙ₊₁ = 1/αₙ₊₁`), and the AM–GM bound
`ρₙ‖bₙ‖ + ρₙ₊₁‖bₙ₊₁‖ ≥ 2√(‖bₙ‖‖bₙ₊₁‖/αₙ₊₁)` turns it into the *checkable*
condition `∑ √(‖bₙ‖‖bₙ₊₁‖/αₙ₊₁) = ∞` (`not_summable_scale_mul`), which for a
constant denominator `b ≡ w ≠ 0` is just `∑ 1/√(αₙ) = ∞`
(`not_summable_scale_mul_const`) — satisfied by any `αₙ = O(n²⁻ᵋ)`, in
particular by linearly growing partial numerators.

Indexing follows `GenContFract` throughout: `g.s.get? n = some ⟨a n, b n⟩` says
that the pair at position `n` is the classical `(aₙ₊₁, bₙ₊₁)`.
-/

namespace FLMF.Methods

namespace PosNumSector

open Filter Topology GenContFract

variable {g : GenContFract ℂ} {α : ℕ → ℝ} {b : ℕ → ℂ} {δ : ℝ}

/-! ### The normalizing scale sequence -/

/-- The positive reals `ρₙ` normalizing the partial numerators `αₙ > 0` to `1`:
`ρ₀ = 1/α₀` and `ρₙ₊₁ = 1/(αₙ₊₁ρₙ)`, i.e. `ρₙρₙ₊₁ = 1/αₙ₊₁`.  These are the
factors of the equivalence transformation `equivTransform (cfScale α)`. -/
-- no-dlmf: method-kit bookkeeping (equivalence-transformation scale sequence)
noncomputable def cfScale (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / α 0
  | (n + 1) => 1 / (α (n + 1) * cfScale α n)

-- no-dlmf: method-kit lemma (positivity of the scale sequence)
theorem cfScale_pos (hα : ∀ n, 0 < α n) : ∀ n, 0 < cfScale α n
  | 0 => by
      rw [cfScale]
      exact div_pos one_pos (hα 0)
  | (n + 1) => by
      have h := cfScale_pos hα n
      rw [cfScale]
      exact div_pos one_pos (mul_pos (hα (n + 1)) h)

-- no-dlmf: method-kit lemma (defining product relation of the scale sequence)
theorem cfScale_mul_succ (hα : ∀ n, 0 < α n) (n : ℕ) :
    cfScale α n * cfScale α (n + 1) = 1 / α (n + 1) := by
  have h := (cfScale_pos hα n).ne'
  have h' := (hα (n + 1)).ne'
  rw [cfScale]
  field_simp

-- no-dlmf: method-kit lemma (the `n = 0` normalization)
theorem cfScale_zero_mul (hα : ∀ n, 0 < α n) : cfScale α 0 * α 0 = 1 := by
  rw [cfScale]
  field_simp
  exact div_self (hα 0).ne'

/-- The complex equivalence factors: the casts of `cfScale α`. -/
-- no-dlmf: method-kit bookkeeping (complex cast of the scale sequence)
noncomputable def cfScaleC (α : ℕ → ℝ) (n : ℕ) : ℂ := (cfScale α n : ℂ)

-- no-dlmf: method-kit lemma (the equivalence factors are nonzero)
theorem cfScaleC_ne_zero (hα : ∀ n, 0 < α n) (n : ℕ) : cfScaleC α n ≠ 0 := by
  simpa [cfScaleC] using (cfScale_pos hα n).ne'

/-- The equivalence transformation normalizes every partial numerator to `1`. -/
-- no-dlmf: method-kit lemma (numerator normalization)
theorem equivFactor_cfScaleC (hα : ∀ n, 0 < α n) (n : ℕ) :
    equivFactor (cfScaleC α) n * (α n : ℂ) = 1 := by
  cases n with
  | zero =>
    rw [equivFactor_zero]
    have h := cfScale_zero_mul hα
    have : ((cfScale α 0 * α 0 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
    push_cast at this
    simpa [cfScaleC] using this
  | succ n =>
    rw [equivFactor_succ]
    have h := cfScale_mul_succ hα n
    have hne := (hα (n + 1)).ne'
    have hmul : (cfScale α n * cfScale α (n + 1)) * α (n + 1) = 1 := by
      rw [h]; field_simp
    have : (((cfScale α n * cfScale α (n + 1)) * α (n + 1) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [hmul]
    push_cast at this
    simpa [cfScaleC, mul_assoc] using this

/-- Partial pairs of the normalized fraction: all numerators `1`, denominators
`ρₙ bₙ`. -/
-- no-dlmf: method-kit lemma (partial pairs after normalization)
theorem equivTransform_s_get? (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), b n⟩) (n : ℕ) :
    (equivTransform (cfScaleC α) g).s.get? n = some ⟨1, b n * (cfScale α n : ℂ)⟩ := by
  have h1 := equivFactor_cfScaleC hα n
  rw [FLMF.Methods.equivTransform_s_get?, hs n, Option.map_some]
  dsimp only
  rw [h1, cfScaleC, mul_comm]

/-! ### The Van Vleck hypotheses for the normalized fraction -/

-- no-dlmf: method-kit lemma (the normalized denominators are nonzero)
theorem scaled_den_ne_zero (hα : ∀ n, 0 < α n) (hb0 : ∀ n, b n ≠ 0) (n : ℕ) :
    b n * (cfScale α n : ℂ) ≠ 0 :=
  mul_ne_zero (hb0 n) (by simpa using (cfScale_pos hα n).ne')

-- no-dlmf: method-kit lemma (the normalized denominators stay in the cone)
theorem scaled_den_cone (hα : ∀ n, 0 < α n) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    δ * ‖b n * (cfScale α n : ℂ)‖ ≤ (b n * (cfScale α n : ℂ)).re :=
  VanVleck.cone_ofReal_mul (cfScale_pos hα n).le (hbc n)

/-- The AM–GM criterion for Van Vleck's non-summability hypothesis: since
`ρₙρₙ₊₁ = 1/αₙ₊₁`, one has `ρₙ‖bₙ‖ + ρₙ₊₁‖bₙ₊₁‖ ≥ 2√(‖bₙ‖‖bₙ₊₁‖/αₙ₊₁)`, so a
divergent `∑√(‖bₙ‖‖bₙ₊₁‖/αₙ₊₁)` forces a divergent `∑ρₙ‖bₙ‖`. -/
-- no-dlmf: method-kit lemma (AM–GM criterion for the Van Vleck hypothesis)
theorem not_summable_scale_mul (hα : ∀ n, 0 < α n)
    (hdiv : ¬ Summable fun n => Real.sqrt (‖b n‖ * ‖b (n + 1)‖ / α (n + 1))) :
    ¬ Summable fun n => cfScale α n * ‖b n‖ := by
  intro hsum
  refine hdiv ?_
  have hshift : Summable fun n => cfScale α (n + 1) * ‖b (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr hsum
  have hadd : Summable fun n => cfScale α n * ‖b n‖ + cfScale α (n + 1) * ‖b (n + 1)‖ :=
    hsum.add hshift
  refine Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) (fun n => ?_) hadd
  set x := cfScale α n * ‖b n‖ with hx
  set y := cfScale α (n + 1) * ‖b (n + 1)‖ with hy
  have hxn : 0 ≤ x := mul_nonneg (cfScale_pos hα n).le (norm_nonneg _)
  have hyn : 0 ≤ y := mul_nonneg (cfScale_pos hα (n + 1)).le (norm_nonneg _)
  have hprod : x * y = ‖b n‖ * ‖b (n + 1)‖ / α (n + 1) := by
    have h := cfScale_mul_succ hα n
    rw [hx, hy]
    calc cfScale α n * ‖b n‖ * (cfScale α (n + 1) * ‖b (n + 1)‖)
        = (cfScale α n * cfScale α (n + 1)) * (‖b n‖ * ‖b (n + 1)‖) := by ring
      _ = (1 / α (n + 1)) * (‖b n‖ * ‖b (n + 1)‖) := by rw [h]
      _ = ‖b n‖ * ‖b (n + 1)‖ / α (n + 1) := by ring
  have hkey : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    have hsq : Real.sqrt (((x + y) / 2) ^ 2) = (x + y) / 2 :=
      Real.sqrt_sq (by positivity)
    rw [← hsq]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - y)])
  rw [← hprod]
  linarith [hkey]

/-- The constant-denominator form of the criterion: for `bₙ ≡ w ≠ 0` the
hypothesis of `not_summable_scale_mul` is exactly `∑ 1/√(αₙ₊₁) = ∞`. -/
-- no-dlmf: method-kit lemma (constant-denominator AM–GM criterion)
theorem not_summable_scale_mul_const {w : ℂ} (hα : ∀ n, 0 < α n) (hw : w ≠ 0)
    (hdiv : ¬ Summable fun n => 1 / Real.sqrt (α (n + 1))) :
    ¬ Summable fun n => cfScale α n * ‖w‖ := by
  refine not_summable_scale_mul (b := fun _ => w) hα ?_
  intro hsum
  refine hdiv ?_
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hcongr : ∀ n : ℕ, Real.sqrt (‖w‖ * ‖w‖ / α (n + 1))
      = ‖w‖ * (1 / Real.sqrt (α (n + 1))) := by
    intro n
    rw [show ‖w‖ * ‖w‖ / α (n + 1) = ‖w‖ ^ 2 * (α (n + 1))⁻¹ by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hwn.le, Real.sqrt_inv]
    ring
  have h : Summable fun n : ℕ => ‖w‖ * (1 / Real.sqrt (α (n + 1))) := hsum.congr hcongr
  have h' := h.mul_left ‖w‖⁻¹
  refine h'.congr fun n => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hwn.ne', one_mul]

/-! ### The convergence criterion -/

/-- **The continuant denominators of a positive-numerator sector fraction never
vanish.**  Van Vleck's continuant lemma applied to the normalization. -/
-- no-dlmf: method-kit lemma (nonvanishing continuant denominators)
theorem dens_ne_zero (hδ : 0 < δ) (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    g.dens n ≠ 0 := by
  have hne := VanVleck.dens_ne_zero hδ (equivTransform_s_get? hα hs)
    (scaled_den_ne_zero hα hb0) (scaled_den_cone hα hbc) n
  intro hzero
  refine hne ?_
  have hnt : ¬ g.TerminatedAt (n - 1) := by
    rw [GenContFract.terminatedAt_iff_s_none, hs (n - 1)]
    simp
  have h := (FLMF.Methods.equivTransform_conts (cfScaleC α) (g := g) n (Or.inr hnt)).2
  rw [GenContFract.den_eq_conts_b, h, ← GenContFract.den_eq_conts_b, hzero, mul_zero]

/-- **The convergent gap of a positive-numerator sector fraction tends to `0`**
whenever `∑ ρₙ‖bₙ‖ = ∞` (Van Vleck, DLMF 1.12.28, transported through the
equivalence transformation). -/
-- no-dlmf: method-kit convergence lemma (vanishing convergent gap)
theorem tendsto_convs_diff_zero (hδ : 0 < δ) (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hns : ¬ Summable fun n => cfScale α n * ‖b n‖) :
    Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0) := by
  have hns' : ¬ Summable fun n => ‖b n * (cfScale α n : ℂ)‖ := by
    intro h
    refine hns (h.congr fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cfScale_pos hα n),
      mul_comm]
  have h := VanVleck.tendsto_convs_diff_zero hδ (equivTransform_s_get? hα hs)
    (scaled_den_ne_zero hα hb0) (scaled_den_cone hα hbc) hns'
  simpa [FLMF.Methods.equivTransform_convs (cfScaleC α) (cfScaleC_ne_zero hα) g] using h

/-- **The convergence criterion for complex S-fractions.**  A continued fraction
over `ℂ` whose partial numerators are positive reals `αₙ` and whose partial
denominators lie in the cone `{w : δ‖w‖ ≤ Re w}` (`δ > 0`) *converges*, provided
`∑ ρₙ‖bₙ‖ = ∞` for the normalizing sequence `ρ = cfScale α`.

This is Van Vleck's theorem (DLMF 1.12.28) for the `aₙ ↦ 1` normalization of the
fraction, transported back by `equivTransform_convs`. -/
-- no-dlmf: method-kit convergence criterion (positive numerators, sector denominators)
theorem exists_tendsto_convs (hδ : 0 < δ) (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hns : ¬ Summable fun n => cfScale α n * ‖b n‖) :
    ∃ L : ℂ, Tendsto g.convs atTop (𝓝 L) := by
  have hns' : ¬ Summable fun n => ‖b n * (cfScale α n : ℂ)‖ := by
    intro h
    refine hns (h.congr fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cfScale_pos hα n),
      mul_comm]
  obtain ⟨L, hL⟩ := VanVleck.exists_tendsto_convs hδ (equivTransform_s_get? hα hs)
    (scaled_den_ne_zero hα hb0) (scaled_den_cone hα hbc) hns'
  refine ⟨L, ?_⟩
  have hfun : (equivTransform (cfScaleC α) g).convs = g.convs :=
    funext (FLMF.Methods.equivTransform_convs (cfScaleC α) (cfScaleC_ne_zero hα) g)
  rwa [hfun] at hL

/-! ### The constant-denominator specialization

The shape that occurs in the special-function fractions: partial numerators
`αₙ > 0`, partial denominators the *constant* `w` with `ℜ w > 0`. -/

/-- **Constant-denominator form.**  For an S-fraction with positive partial
numerators `αₙ` and constant partial denominator `w`, `ℜ w > 0`, the continuant
denominators never vanish. -/
-- no-dlmf: method-kit lemma (constant-denominator specialization)
theorem dens_ne_zero_const {w : ℂ} (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), w⟩) (hw : 0 < w.re) (n : ℕ) :
    g.dens n ≠ 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  refine dens_ne_zero (δ := w.re / ‖w‖) (by positivity) hα hs (fun _ => hw0) (fun _ => ?_) n
  rw [div_mul_cancel₀ _ hwn.ne']

/-- **Constant-denominator convergence criterion.**  An S-fraction with positive
partial numerators `αₙ` and constant partial denominator `w` in the open right
half-plane converges as soon as `∑ 1/√(αₙ) = ∞` — in particular whenever the
`αₙ` grow at most quadratically. -/
-- no-dlmf: method-kit convergence criterion (constant sector denominator)
theorem exists_tendsto_convs_const {w : ℂ} (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), w⟩) (hw : 0 < w.re)
    (hdiv : ¬ Summable fun n => 1 / Real.sqrt (α (n + 1))) :
    ∃ L : ℂ, Tendsto g.convs atTop (𝓝 L) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  refine exists_tendsto_convs (δ := w.re / ‖w‖) (by positivity) hα hs (fun _ => hw0)
    (fun _ => ?_) (not_summable_scale_mul_const hα hw0 hdiv)
  rw [div_mul_cancel₀ _ hwn.ne']

/-- **Constant-denominator gap estimate.**  The convergent gap of a
constant-denominator S-fraction in the right half-plane tends to `0`. -/
-- no-dlmf: method-kit convergence lemma (constant sector denominator)
theorem tendsto_convs_diff_zero_const {w : ℂ} (hα : ∀ n, 0 < α n)
    (hs : ∀ n, g.s.get? n = some ⟨(α n : ℂ), w⟩) (hw : 0 < w.re)
    (hdiv : ¬ Summable fun n => 1 / Real.sqrt (α (n + 1))) :
    Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  refine tendsto_convs_diff_zero (δ := w.re / ‖w‖) (by positivity) hα hs (fun _ => hw0)
    (fun _ => ?_) (not_summable_scale_mul_const hα hw0 hdiv)
  rw [div_mul_cancel₀ _ hwn.ne']

end PosNumSector

end FLMF.Methods
