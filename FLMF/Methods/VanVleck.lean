import FLMF.Methods.ContinuedFraction
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Van Vleck's convergence theorem for complex continued fractions (method kit)

This module supplies the sector (angular) convergence theory for continued
fractions over `ℂ`, the complement to the Śleszyński–Pringsheim (norm) theory in
`FLMF.Methods.ContinuedFraction`.  Everything is stated for Mathlib's
`GenContFract ℂ` and applies to a fraction all of whose partial numerators are
`1`,
```
  h + 1/(b₀ + 1/(b₁ + 1/(b₂ + ⋯))),
```
under the hypothesis that the partial denominators lie in a *closed sector*
strictly inside the right half-plane: `bₙ ≠ 0` and `|ph bₙ| ≤ π/2 − ε` for a
fixed `ε > 0`.  (The nonvanishing hypothesis is not redundant: Lean's
`Complex.arg 0 = 0`, so a pure `|arg bₙ| ≤ π/2 − ε` bound would silently admit
`bₙ = 0`.)

Indexing follows `GenContFract`: `g.s.get? n = some ⟨1, b n⟩` says that the pair
at position `n` is the classical `(aₙ₊₁, bₙ₊₁) = (1, bₙ)`, so `b n` is the
classical `bₙ₊₁`; `g.dens 0 = 1`, `g.dens 1 = b 0`, and
`g.dens (n+2) = b (n+1) * g.dens (n+1) + g.dens n`.

## The mathematical route

Write `Bₙ = g.dens n` and let `Eₙ = Re(Bₙ₊₁ conj Bₙ)` (`denPairingRe`).  Every
estimate below flows from two facts about this single real sequence.

1. **Sector induction** (`dens_ne_zero_and_pairing_cone`).  If
   `δ‖bₙ‖ ≤ Re bₙ` for all `n` (the cone form of the sector hypothesis, with
   `δ = sin ε`), then `Bₙ ≠ 0` and `δ‖Bₙ₊₁‖‖Bₙ‖ ≤ Eₙ` for all `n`.  Proof: the
   pairing satisfies `Bₙ₊₂ conj Bₙ₊₁ = bₙ₊₁‖Bₙ₊₁‖² + conj (Bₙ₊₁ conj Bₙ)`, and
   the closed cone `{z : δ‖z‖ ≤ Re z}` is stable under addition, under
   conjugation, and under multiplication by nonnegative reals (`cone_add`,
   `cone_conj`, `cone_ofReal_mul`).  In particular `Eₙ ≍ ‖Bₙ₊₁‖‖Bₙ‖`: it is
   trapped between `δ‖Bₙ₊₁‖‖Bₙ‖` and `‖Bₙ₊₁‖‖Bₙ‖`.

2. **An exact monotone identity** (`denPairingRe_succ`):
   `Eₙ₊₁ = Eₙ + Re(bₙ₊₁)‖Bₙ₊₁‖²`, so `E` is nondecreasing with
   `E₀ = Re b₀ > 0`.

Combining them with the determinant formula `fₙ₊₂ − fₙ = ±bₙ₊₁/(BₙBₙ₊₂)` gives
the **quantitative telescoping bound** (`norm_convs_add_two_sub_convs_le`)
```
  ‖fₙ₊₂ − fₙ‖ ≤ δ⁻¹ (1/Eₙ − 1/Eₙ₊₁),
```
whose partial sums are bounded by `1/(δ · Re b₀) ≤ 1/(sin²ε ‖b₀‖)`
(`sum_norm_convs_add_two_sub_convs_le`,
`sum_norm_convs_add_two_sub_convs_le_of_arg`) — an explicit bound depending only
on `ε` and `‖b₀‖`, which is what a locally-uniform-in-parameters convergence
argument needs.  Absolute summability of the two-step differences makes the
even- and odd-indexed convergents Cauchy: this is the content of DLMF 1.12.27
(`exists_tendsto_convs_even_odd_of_arg`).

For the *full* sequence one needs `fₙ₊₁ − fₙ = ±1/(BₙBₙ₊₁) → 0`, i.e.
`Eₙ → ∞`.  Since `Eₙ = ∑_{k ≤ n} Re(bₖ)‖Bₖ‖²`, this is proved by contradiction:
if `E` were bounded, then `∑ ‖bₖ‖‖Bₖ‖² < ∞`, the growth estimate
`‖Bₙ₊₂‖ ≤ ‖Bₙ‖(1 + ‖bₙ₊₁‖‖Bₙ₊₁‖²/E₀)` would bound `‖Bₙ‖` above (a convergent
product), hence — via `‖Bₙ‖‖Bₙ₊₁‖ ≥ E₀` — also *below*, and then
`∑ ‖bₖ‖‖Bₖ‖² ≳ ∑ ‖bₖ‖ = ∞`, a contradiction.  This yields the "if" half of
DLMF 1.12.28 (`exists_tendsto_convs_of_arg`): a sector fraction with
`∑ ‖bₙ‖ = ∞` converges.

The converse half (Stern–Stolz) is the reverse implication: if `∑ ‖bₙ‖ < ∞`
then the crude product bound `‖Bₙ‖ ≤ ∏ (1 + ‖bₖ‖) ≤ exp(∑ ‖bₖ‖)`
(`norm_dens_le_prod`) keeps the continuants bounded, so
`‖fₙ₊₁ − fₙ‖ = 1/(‖Bₙ‖‖Bₙ₊₁‖)` stays bounded away from `0` and the fraction
cannot converge (`not_exists_tendsto_convs_of_summable`).  The two halves
together are DLMF 1.12.28 in full (`exists_tendsto_convs_iff`,
`exists_tendsto_convs_iff_of_arg`).

## Scope

* The DLMF-display surfaces for 1.12.26–1.12.28 live in
  `FLMF.Methods.Ch1ContinuedFractions`, which is built on a different (bespoke)
  continued-fraction structure; that module bridges its `ContinuedFraction` to
  `GenContFract ℂ` (`toGCF`) and obtains its Van Vleck displays as wrappers over
  the theorems here, which are the method-kit forms on Mathlib's `GenContFract`
  and are therefore marked `no-dlmf`.
-/

namespace FLMF.Methods

namespace VanVleck

open Filter Topology GenContFract Finset

/-! ### The closed cone `{z : δ‖z‖ ≤ Re z}`

A closed sector of half-angle `π/2 − ε` about the positive real axis is exactly
the set `{z : sin ε · ‖z‖ ≤ Re z}` (`cone_of_abs_arg_le`).  Phrased this way the
sector condition is stable under the three operations the continuant induction
needs, with no `arg` arithmetic at all. -/

section Cone

/-- The closed cone `{z : δ‖z‖ ≤ Re z}` is closed under addition. -/
-- no-dlmf: convex-cone additivity (sector bookkeeping)
theorem cone_add {δ : ℝ} (hδ : 0 ≤ δ) {z w : ℂ} (hz : δ * ‖z‖ ≤ z.re) (hw : δ * ‖w‖ ≤ w.re) :
    δ * ‖z + w‖ ≤ (z + w).re := by
  have h1 : δ * ‖z + w‖ ≤ δ * (‖z‖ + ‖w‖) := mul_le_mul_of_nonneg_left (norm_add_le z w) hδ
  have h2 : (z + w).re = z.re + w.re := Complex.add_re z w
  nlinarith

/-- The closed cone `{z : δ‖z‖ ≤ Re z}` is closed under conjugation. -/
-- no-dlmf: cone stability under conjugation (sector bookkeeping)
theorem cone_conj {δ : ℝ} {z : ℂ} (hz : δ * ‖z‖ ≤ z.re) :
    δ * ‖(starRingEnd ℂ) z‖ ≤ ((starRingEnd ℂ) z).re := by
  rwa [Complex.norm_conj, Complex.conj_re]

/-- The closed cone `{z : δ‖z‖ ≤ Re z}` is closed under scaling by a nonnegative
real. -/
-- no-dlmf: cone stability under nonnegative real scaling (sector bookkeeping)
theorem cone_ofReal_mul {δ t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : δ * ‖z‖ ≤ z.re) :
    δ * ‖z * (t : ℂ)‖ ≤ (z * (t : ℂ)).re := by
  have hn : ‖z * (t : ℂ)‖ = ‖z‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hr : (z * (t : ℂ)).re = z.re * t := by simp [Complex.mul_re]
  rw [hn, hr]
  nlinarith

/-- A nonzero element of the cone has positive real part. -/
-- no-dlmf: cone positivity (sector bookkeeping)
theorem re_pos_of_cone {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz0 : z ≠ 0) (hz : δ * ‖z‖ ≤ z.re) :
    0 < z.re := by
  have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  nlinarith

/-- **The sector hypothesis in cone form.**  A nonzero `z` with
`|ph z| ≤ π/2 − ε` satisfies `sin ε · ‖z‖ ≤ Re z`.  (This is where the
nonvanishing hypothesis matters: `Complex.arg 0 = 0`, so the `arg` bound alone
does not exclude `z = 0`.) -/
-- no-dlmf: sector-to-cone conversion (`Re z = ‖z‖ cos (ph z)`)
theorem cone_of_abs_arg_le {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz0 : z ≠ 0)
    (harg : |Complex.arg z| ≤ Real.pi / 2 - ε) :
    Real.sin ε * ‖z‖ ≤ z.re := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hcos : Real.cos (Complex.arg z) = z.re / ‖z‖ := Complex.cos_arg hz0
  have hle : Real.cos (Real.pi / 2 - ε) ≤ Real.cos |Complex.arg z| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by nlinarith [Real.pi_pos]) harg
  rw [Real.cos_abs, hcos, Real.cos_pi_div_two_sub] at hle
  exact (le_div_iff₀ hnorm).mp hle

end Cone

/-! ### The continuant pairing `Eₙ = Re(Bₙ₊₁ conj Bₙ)` -/

section Fraction

variable {g : GenContFract ℂ} {b : ℕ → ℂ} {δ : ℝ}

/-- The real part of the Hermitian pairing of consecutive continuant
denominators, `Eₙ = Re(Bₙ₊₁ conj Bₙ)`.  Under the sector hypothesis this is a
positive nondecreasing sequence comparable to `‖Bₙ₊₁‖‖Bₙ‖`, and it drives every
estimate in this file. -/
-- no-dlmf: continuant bookkeeping (Hermitian pairing of consecutive denominators)
noncomputable def denPairingRe (g : GenContFract ℂ) (n : ℕ) : ℝ :=
  (g.dens (n + 1) * (starRingEnd ℂ) (g.dens n)).re

-- no-dlmf: continuant bookkeeping (`B₁ = b₀`)
theorem dens_one_eq (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) : g.dens 1 = b 0 :=
  GenContFract.first_den_eq (hs 0)

/-- The Wallis recurrence for a fraction with all partial numerators `1`:
`Bₙ₊₂ = bₙ₊₁ Bₙ₊₁ + Bₙ`. -/
-- no-dlmf: continuant recurrence, all-numerators-one form
theorem dens_two_step (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (n : ℕ) :
    g.dens (n + 2) = b (n + 1) * g.dens (n + 1) + g.dens n := by
  have h := GenContFract.dens_recurrence (g := g) (n := n) (gp := ⟨1, b (n + 1)⟩)
    (hs (n + 1)) rfl rfl
  simpa using h

-- no-dlmf: continuant bookkeeping (`E₀ = Re b₀`)
theorem denPairingRe_zero (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) :
    denPairingRe g 0 = (b 0).re := by
  simp [denPairingRe, dens_one_eq hs]

/-- **The exact pairing identity** `Eₙ₊₁ = Re(bₙ₊₁)‖Bₙ₊₁‖² + Eₙ`.  It is the
engine of the whole file: it makes `E` monotone and identifies it with the
weighted sum `∑_{k ≤ n} Re(bₖ)‖Bₖ‖²`. -/
-- no-dlmf: exact recurrence for the continuant pairing
theorem denPairingRe_succ (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (n : ℕ) :
    denPairingRe g (n + 1) = (b (n + 1)).re * ‖g.dens (n + 1)‖ ^ 2 + denPairingRe g n := by
  simp only [denPairingRe, dens_two_step hs n, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The complex form of the pairing recurrence:
`Bₙ₊₂ conj Bₙ₊₁ = bₙ₊₁‖Bₙ₊₁‖² + conj (Bₙ₊₁ conj Bₙ)`.  Both summands lie in the
sector whenever `bₙ₊₁` and the previous pairing do — this is the inductive step
of `dens_ne_zero_and_pairing_cone`. -/
-- no-dlmf: pairing recurrence, complex form
theorem pairing_succ_eq (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (n : ℕ) :
    g.dens (n + 2) * (starRingEnd ℂ) (g.dens (n + 1)) =
      b (n + 1) * ((‖g.dens (n + 1)‖ ^ 2 : ℝ) : ℂ) +
        (starRingEnd ℂ) (g.dens (n + 1) * (starRingEnd ℂ) (g.dens n)) := by
  rw [dens_two_step hs n]
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [map_mul, Complex.conj_conj]
  ring

/-! ### The sector induction -/

/-- **Van Vleck's continuant lemma.**  If every partial denominator lies in the
closed cone `δ‖z‖ ≤ Re z` (`δ > 0`) and is nonzero, then no continuant
denominator vanishes and the pairing `Eₙ = Re(Bₙ₊₁ conj Bₙ)` stays in the same
cone: `δ‖Bₙ₊₁‖‖Bₙ‖ ≤ Eₙ`.

This is the sector analogue of the Pringsheim growth bound
`FLMF.Methods.norm_dens_add_partNumNormProd_le`, and the reason the theory works
at all: the cone is convex, pointed and conjugation-stable, so the recurrence
`Bₙ₊₂ conj Bₙ₊₁ = bₙ₊₁‖Bₙ₊₁‖² + conj (Bₙ₊₁ conj Bₙ)` never allows the two terms
to cancel. -/
-- no-dlmf: sector continuant induction (method-kit meta-lemma; DLMF §1.12(vi) `Bₙ ≠ 0`)
theorem dens_ne_zero_and_pairing_cone (hδ : 0 < δ)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    ∀ n, g.dens n ≠ 0 ∧ g.dens (n + 1) ≠ 0 ∧
      δ * (‖g.dens (n + 1)‖ * ‖g.dens n‖) ≤ denPairingRe g n := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simp, by simp [dens_one_eq hs, hb0 0], ?_⟩
    simpa [denPairingRe_zero hs, dens_one_eq hs] using hbc 0
  | succ n ih =>
    obtain ⟨h0, h1, hcone⟩ := ih
    set D : ℂ := g.dens (n + 1) * (starRingEnd ℂ) (g.dens n) with hD
    have hDne : D ≠ 0 := mul_ne_zero h1 (by simpa using h0)
    have hDnorm : ‖D‖ = ‖g.dens (n + 1)‖ * ‖g.dens n‖ := by
      rw [hD, norm_mul, Complex.norm_conj]
    have hDcone : δ * ‖D‖ ≤ D.re := by rw [hDnorm]; exact hcone
    have hz : δ * ‖b (n + 1) * ((‖g.dens (n + 1)‖ ^ 2 : ℝ) : ℂ)‖ ≤
        (b (n + 1) * ((‖g.dens (n + 1)‖ ^ 2 : ℝ) : ℂ)).re :=
      cone_ofReal_mul (by positivity) (hbc (n + 1))
    have hw : δ * ‖(starRingEnd ℂ) D‖ ≤ ((starRingEnd ℂ) D).re := cone_conj hDcone
    have hsum := cone_add hδ.le hz hw
    rw [← pairing_succ_eq hs n] at hsum
    have hwpos : 0 < ((starRingEnd ℂ) D).re :=
      re_pos_of_cone hδ (by simpa using hDne) hw
    have hzpos : 0 ≤ (b (n + 1) * ((‖g.dens (n + 1)‖ ^ 2 : ℝ) : ℂ)).re := by
      refine le_trans ?_ hz; positivity
    have hnewpos : 0 < (g.dens (n + 2) * (starRingEnd ℂ) (g.dens (n + 1))).re := by
      rw [pairing_succ_eq hs n, Complex.add_re]; linarith
    have hne2 : g.dens (n + 2) ≠ 0 := by
      intro h
      rw [h, zero_mul, Complex.zero_re] at hnewpos
      exact lt_irrefl 0 hnewpos
    refine ⟨h1, hne2, ?_⟩
    have hnorm : ‖g.dens (n + 2) * (starRingEnd ℂ) (g.dens (n + 1))‖ =
        ‖g.dens (n + 2)‖ * ‖g.dens (n + 1)‖ := by
      rw [norm_mul, Complex.norm_conj]
    rw [denPairingRe, ← hnorm]
    exact hsum

/-- Under the sector hypothesis the continuant denominators never vanish (the
first assertion of DLMF §1.12(vi)). -/
-- no-dlmf: sector continuant nonvanishing
theorem dens_ne_zero (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) : g.dens n ≠ 0 :=
  (dens_ne_zero_and_pairing_cone hδ hs hb0 hbc n).1

-- no-dlmf: sector continuant nonvanishing (norm form)
theorem norm_dens_pos (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) : 0 < ‖g.dens n‖ :=
  norm_pos_iff.mpr (dens_ne_zero hδ hs hb0 hbc n)

/-- The trivial half of the comparison `Eₙ ≍ ‖Bₙ₊₁‖‖Bₙ‖`: a real part never
exceeds the modulus. -/
-- no-dlmf: `Re ≤ ‖·‖` for the continuant pairing
theorem denPairingRe_le (n : ℕ) :
    denPairingRe g n ≤ ‖g.dens (n + 1)‖ * ‖g.dens n‖ := by
  have h := Complex.re_le_norm (g.dens (n + 1) * (starRingEnd ℂ) (g.dens n))
  rwa [norm_mul, Complex.norm_conj] at h

-- no-dlmf: positivity of the continuant pairing under the sector hypothesis
theorem denPairingRe_pos (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    0 < denPairingRe g n := by
  have h := (dens_ne_zero_and_pairing_cone hδ hs hb0 hbc n).2.2
  have h1 := norm_dens_pos hδ hs hb0 hbc n
  have h2 := norm_dens_pos hδ hs hb0 hbc (n + 1)
  have hpos : 0 < δ * (‖g.dens (n + 1)‖ * ‖g.dens n‖) := by positivity
  linarith

/-- `E` is nondecreasing: an immediate consequence of the exact identity
`Eₙ₊₁ = Eₙ + Re(bₙ₊₁)‖Bₙ₊₁‖²` and `Re bₙ₊₁ ≥ δ‖bₙ₊₁‖ ≥ 0`. -/
-- no-dlmf: monotonicity of the continuant pairing
theorem denPairingRe_mono (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) : Monotone (denPairingRe g) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := denPairingRe_succ hs n
  have hb : 0 ≤ (b (n + 1)).re := le_trans (by positivity) (hbc (n + 1))
  nlinarith [sq_nonneg ‖g.dens (n + 1)‖]

/-! ### Convergent differences -/

-- no-dlmf: all partial numerators equal `1`
theorem partNumProd_eq_one (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (m : ℕ) :
    partNumProd g m = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [GenContFract.partNum_eq_s_a (hs i)]
  rfl

/-- Determinant formula for an all-numerators-one fraction:
`fₙ₊₁ − fₙ = (−1)ⁿ/(Bₙ Bₙ₊₁)`. -/
-- no-dlmf: one-step convergent difference, all-numerators-one form
theorem convs_succ_sub_convs_eq (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hne : ∀ n, g.dens n ≠ 0) (n : ℕ) :
    g.convs (n + 1) - g.convs n = (-1) ^ n / (g.dens n * g.dens (n + 1)) := by
  rw [convs_succ_sub_convs (hne n) (hne (n + 1)), partNumProd_eq_one hs, mul_one]

/-- Two-step convergent difference: `fₙ₊₂ − fₙ = (−1)ⁿ bₙ₊₁/(Bₙ Bₙ₊₂)`.  (The
intermediate continuant cancels because `Bₙ₊₂ − Bₙ = bₙ₊₁ Bₙ₊₁`.)  This is the
identity whose absolute summability yields the even/odd convergence. -/
-- no-dlmf: two-step convergent difference, all-numerators-one form
theorem convs_add_two_sub_convs_eq (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hne : ∀ n, g.dens n ≠ 0) (n : ℕ) :
    g.convs (n + 2) - g.convs n = (-1) ^ n * b (n + 1) / (g.dens n * g.dens (n + 2)) := by
  have h1 := convs_succ_sub_convs_eq hs hne n
  have h2 : g.convs (n + 2) - g.convs (n + 1) =
      (-1) ^ (n + 1) / (g.dens (n + 1) * g.dens (n + 2)) := convs_succ_sub_convs_eq hs hne (n + 1)
  have hrec := dens_two_step hs n
  have e0 := hne n
  have e1 := hne (n + 1)
  have e2 := hne (n + 2)
  have hsplit : g.convs (n + 2) - g.convs n =
      (g.convs (n + 2) - g.convs (n + 1)) + (g.convs (n + 1) - g.convs n) := by ring
  rw [hsplit, h1, h2, pow_succ]
  field_simp
  linear_combination hrec

-- no-dlmf: two-step convergent difference, norm form
theorem norm_convs_add_two_sub_convs (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hne : ∀ n, g.dens n ≠ 0) (n : ℕ) :
    ‖g.convs (n + 2) - g.convs n‖ = ‖b (n + 1)‖ / (‖g.dens n‖ * ‖g.dens (n + 2)‖) := by
  rw [convs_add_two_sub_convs_eq hs hne n, norm_div, norm_mul, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul]

/-! ### The quantitative telescoping bound -/

/-- **The quantitative Van Vleck estimate.**  Under the sector hypothesis the
two-step convergent differences are dominated by a telescoping sequence:
```
  ‖fₙ₊₂ − fₙ‖ ≤ δ⁻¹ (1/Eₙ − 1/Eₙ₊₁).
```
Proof: `‖fₙ₊₂ − fₙ‖ = ‖bₙ₊₁‖/(‖Bₙ‖‖Bₙ₊₂‖)`; multiply numerator and denominator
by `‖Bₙ₊₁‖²`, bound `δ‖bₙ₊₁‖‖Bₙ₊₁‖² ≤ Eₙ₊₁ − Eₙ` (the exact pairing identity)
and `Eₙ Eₙ₊₁ ≤ (‖Bₙ₊₁‖‖Bₙ‖)(‖Bₙ₊₂‖‖Bₙ₊₁‖)` (the `Re ≤ ‖·‖` half of the
comparison).

This is the primary quantitative statement of the module: every convergence
result below is a corollary, and the resulting bounds are explicit in `δ = sin ε`
and the partial denominators. -/
-- no-dlmf: quantitative Van Vleck telescoping bound (method-kit meta-lemma)
theorem norm_convs_add_two_sub_convs_le (hδ : 0 < δ)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    ‖g.convs (n + 2) - g.convs n‖ ≤
      1 / δ * (1 / denPairingRe g n - 1 / denPairingRe g (n + 1)) := by
  have hne := dens_ne_zero hδ hs hb0 hbc
  have hA := norm_dens_pos hδ hs hb0 hbc n
  have hB := norm_dens_pos hδ hs hb0 hbc (n + 1)
  have hC := norm_dens_pos hδ hs hb0 hbc (n + 2)
  have hE0 := denPairingRe_pos hδ hs hb0 hbc n
  have hE1 := denPairingRe_pos hδ hs hb0 hbc (n + 1)
  have hE0' := denPairingRe_le (g := g) n
  have hE1' : denPairingRe g (n + 1) ≤ ‖g.dens (n + 2)‖ * ‖g.dens (n + 1)‖ :=
    denPairingRe_le (g := g) (n + 1)
  have hstep : δ * (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2) ≤
      denPairingRe g (n + 1) - denPairingRe g n := by
    have h := denPairingRe_succ hs n
    have hb := hbc (n + 1)
    nlinarith [sq_nonneg ‖g.dens (n + 1)‖]
  have hRHS : 1 / δ * (1 / denPairingRe g n - 1 / denPairingRe g (n + 1)) =
      (denPairingRe g (n + 1) - denPairingRe g n) /
        (δ * (denPairingRe g n * denPairingRe g (n + 1))) := by
    field_simp
  rw [norm_convs_add_two_sub_convs hs hne n, hRHS,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : denPairingRe g n * denPairingRe g (n + 1) ≤
      (‖g.dens (n + 1)‖ * ‖g.dens n‖) * (‖g.dens (n + 2)‖ * ‖g.dens (n + 1)‖) :=
    mul_le_mul hE0' hE1' hE1.le (by positivity)
  have h1 : ‖b (n + 1)‖ * (δ * (denPairingRe g n * denPairingRe g (n + 1))) ≤
      ‖b (n + 1)‖ * (δ * ((‖g.dens (n + 1)‖ * ‖g.dens n‖) *
        (‖g.dens (n + 2)‖ * ‖g.dens (n + 1)‖))) := by
    have hc : (0 : ℝ) ≤ ‖b (n + 1)‖ * δ := by positivity
    nlinarith
  have h2 : ‖b (n + 1)‖ * (δ * ((‖g.dens (n + 1)‖ * ‖g.dens n‖) *
        (‖g.dens (n + 2)‖ * ‖g.dens (n + 1)‖))) ≤
      (denPairingRe g (n + 1) - denPairingRe g n) * (‖g.dens n‖ * ‖g.dens (n + 2)‖) := by
    nlinarith [mul_le_mul_of_nonneg_right hstep (mul_nonneg hA.le hC.le)]
  linarith

/-! ### Even and odd convergence (DLMF 1.12.27) -/

/-- The telescoping majorant `uₙ = δ⁻¹(1/Eₙ − 1/Eₙ₊₁)` of the two-step
convergent differences. -/
-- no-dlmf: telescoping majorant of the two-step convergent differences
noncomputable def stepMajorant (g : GenContFract ℂ) (δ : ℝ) (n : ℕ) : ℝ :=
  1 / δ * (1 / denPairingRe g n - 1 / denPairingRe g (n + 1))

-- no-dlmf: majorant nonnegativity
theorem stepMajorant_nonneg (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    0 ≤ stepMajorant g δ n := by
  have hmono := denPairingRe_mono hδ hs hbc (Nat.le_succ n)
  have h1 := denPairingRe_pos hδ hs hb0 hbc n
  have h2 : 1 / denPairingRe g (n + 1) ≤ 1 / denPairingRe g n :=
    one_div_le_one_div_of_le h1 hmono
  have hδ' : 0 < 1 / δ := by positivity
  rw [stepMajorant]
  nlinarith

/-- The majorant telescopes: all its partial sums are bounded by `δ⁻¹/E₀`. -/
-- no-dlmf: telescoping partial-sum bound
theorem sum_stepMajorant_le (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (N : ℕ) :
    ∑ n ∈ Finset.range N, stepMajorant g δ n ≤ 1 / δ * (1 / denPairingRe g 0) := by
  have hδ' : 0 < 1 / δ := by positivity
  have hEN : 0 < denPairingRe g N := denPairingRe_pos hδ hs hb0 hbc N
  have hsplit : ∑ n ∈ Finset.range N, stepMajorant g δ n =
      1 / δ * ∑ n ∈ Finset.range N,
        (1 / denPairingRe g n - 1 / denPairingRe g (n + 1)) := by
    rw [Finset.mul_sum]
    rfl
  rw [hsplit, Finset.sum_range_sub' fun i => 1 / denPairingRe g i]
  have : (0 : ℝ) ≤ 1 / denPairingRe g N := by positivity
  nlinarith

-- no-dlmf: summability of the telescoping majorant
theorem summable_stepMajorant (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    Summable (stepMajorant g δ) :=
  summable_of_sum_range_le (stepMajorant_nonneg hδ hs hb0 hbc)
    (sum_stepMajorant_le hδ hs hb0 hbc)

-- no-dlmf: Cauchy property of the even-indexed convergents (sector hypothesis)
theorem cauchySeq_convs_even (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    CauchySeq fun k => g.convs (2 * k) := by
  refine cauchySeq_of_dist_le_of_summable (fun k => stepMajorant g δ (2 * k)) (fun k => ?_) ?_
  · show dist (g.convs (2 * k)) (g.convs (2 * (k + 1))) ≤ stepMajorant g δ (2 * k)
    have h2k : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2k, dist_eq_norm, norm_sub_rev]
    exact norm_convs_add_two_sub_convs_le hδ hs hb0 hbc (2 * k)
  · have hi : Function.Injective fun k : ℕ => 2 * k := by
      intro x y h; simp only at h; omega
    exact (summable_stepMajorant hδ hs hb0 hbc).comp_injective hi

-- no-dlmf: Cauchy property of the odd-indexed convergents (sector hypothesis)
theorem cauchySeq_convs_odd (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    CauchySeq fun k => g.convs (2 * k + 1) := by
  refine cauchySeq_of_dist_le_of_summable (fun k => stepMajorant g δ (2 * k + 1))
    (fun k => ?_) ?_
  · show dist (g.convs (2 * k + 1)) (g.convs (2 * (k + 1) + 1)) ≤ stepMajorant g δ (2 * k + 1)
    have h2k : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [h2k, dist_eq_norm, norm_sub_rev]
    exact norm_convs_add_two_sub_convs_le hδ hs hb0 hbc (2 * k + 1)
  · have hi : Function.Injective fun k : ℕ => 2 * k + 1 := by
      intro x y h; simp only at h; omega
    exact (summable_stepMajorant hδ hs hb0 hbc).comp_injective hi

/-- **Van Vleck's theorem, even part** (cone form): the even-indexed convergents
of a sector fraction converge. -/
-- no-dlmf: Van Vleck even-part convergence, cone form (DLMF 1.12.27 is stated
-- in `exists_tendsto_convs_even_odd_of_arg`)
theorem exists_tendsto_convs_even (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    ∃ L : ℂ, Tendsto (fun k => g.convs (2 * k)) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_convs_even hδ hs hb0 hbc)

/-- **Van Vleck's theorem, odd part** (cone form): the odd-indexed convergents of
a sector fraction converge. -/
-- no-dlmf: Van Vleck odd-part convergence, cone form (DLMF 1.12.27 is stated
-- in `exists_tendsto_convs_even_odd_of_arg`)
theorem exists_tendsto_convs_odd (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    ∃ L : ℂ, Tendsto (fun k => g.convs (2 * k + 1)) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (cauchySeq_convs_odd hδ hs hb0 hbc)

/-! ### Growth of the continuants -/

/-- Iterating the exact pairing identity: `Eₙ = ∑_{k ≤ n} Re(bₖ)‖Bₖ‖²`. -/
-- no-dlmf: closed form of the continuant pairing as a weighted sum
theorem denPairingRe_eq_sum (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (n : ℕ) :
    denPairingRe g n = ∑ k ∈ Finset.range (n + 1), (b k).re * ‖g.dens k‖ ^ 2 := by
  induction n with
  | zero => simp [denPairingRe_zero hs]
  | succ n ih =>
    rw [denPairingRe_succ hs n, ih,
      Finset.sum_range_succ (f := fun k => (b k).re * ‖g.dens k‖ ^ 2) (n := n + 1)]
    ring

-- no-dlmf: weighted-sum lower bound for the continuant pairing
theorem sum_weight_le (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    δ * ∑ k ∈ Finset.range (n + 1), ‖b k‖ * ‖g.dens k‖ ^ 2 ≤ denPairingRe g n := by
  rw [denPairingRe_eq_sum hs, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := hbc k
  nlinarith [sq_nonneg ‖g.dens k‖]

/-- Multiplicative growth estimate for the continuants:
`‖Bₙ₊₂‖ ≤ ‖Bₙ‖(1 + ‖bₙ₊₁‖‖Bₙ₊₁‖²/E₀)`.  The triangle inequality gives
`‖Bₙ₊₂‖ ≤ ‖bₙ₊₁‖‖Bₙ₊₁‖ + ‖Bₙ‖`, and `‖Bₙ₊₁‖‖Bₙ‖ ≥ E₀` converts the first term
into a multiple of `‖Bₙ‖`. -/
-- no-dlmf: multiplicative continuant growth estimate
theorem norm_dens_growth (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    ‖g.dens (n + 2)‖ ≤
      ‖g.dens n‖ * (1 + ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0) := by
  have hm0 : 0 < denPairingRe g 0 := denPairingRe_pos hδ hs hb0 hbc 0
  have hlow : denPairingRe g 0 ≤ ‖g.dens (n + 1)‖ * ‖g.dens n‖ :=
    le_trans (denPairingRe_mono hδ hs hbc (Nat.zero_le n)) (denPairingRe_le n)
  have htri : ‖g.dens (n + 2)‖ ≤ ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ + ‖g.dens n‖ := by
    rw [dens_two_step hs n]
    calc ‖b (n + 1) * g.dens (n + 1) + g.dens n‖
        ≤ ‖b (n + 1) * g.dens (n + 1)‖ + ‖g.dens n‖ := norm_add_le _ _
      _ = ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ + ‖g.dens n‖ := by rw [norm_mul]
  have hkey : ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ≤
      ‖g.dens n‖ * (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0) := by
    have hrw : ‖g.dens n‖ * (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0) =
        (‖b (n + 1)‖ * ‖g.dens (n + 1)‖) * (‖g.dens (n + 1)‖ * ‖g.dens n‖) /
          denPairingRe g 0 := by
      field_simp
    rw [hrw, le_div_iff₀ hm0]
    nlinarith [mul_nonneg (norm_nonneg (b (n + 1))) (norm_nonneg (g.dens (n + 1)))]
  nlinarith

/-- Turning the multiplicative growth estimate into a product bound:
`‖Bₙ‖ ≤ max(‖B₀‖, ‖B₁‖) · exp(∑_{k < n} ‖bₖ‖‖Bₖ‖²/E₀)`, by `1 + x ≤ eˣ` and a
two-step induction (the even- and odd-indexed continuants grow separately). -/
-- no-dlmf: exponential continuant growth bound
theorem norm_dens_le_exp (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (n : ℕ) :
    ‖g.dens n‖ ≤ max ‖g.dens 0‖ ‖g.dens 1‖ *
      Real.exp (∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0) := by
  have hm0 : 0 < denPairingRe g 0 := denPairingRe_pos hδ hs hb0 hbc 0
  have hanonneg : ∀ k : ℕ, 0 ≤ ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0 := by
    intro k; positivity
  have hsumnonneg : ∀ m : ℕ,
      0 ≤ ∑ k ∈ Finset.range m, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0 :=
    fun m => Finset.sum_nonneg fun k _ => hanonneg k
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero, mul_one]
    exact le_max_left _ _
  | one =>
    have h1 : (1 : ℝ) ≤ Real.exp (∑ k ∈ Finset.range 1,
        ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0) :=
      Real.one_le_exp (hsumnonneg 1)
    have h2 : ‖g.dens 1‖ ≤ max ‖g.dens 0‖ ‖g.dens 1‖ := le_max_right _ _
    have hK : (0 : ℝ) ≤ max ‖g.dens 0‖ ‖g.dens 1‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    nlinarith [norm_nonneg (g.dens 1)]
  | more n ih _ =>
    have hstep := norm_dens_growth hδ hs hb0 hbc n
    have hexp : 1 + ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0 ≤
        Real.exp (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0) := by
      have := Real.add_one_le_exp (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0)
      linarith
    have hK : (0 : ℝ) ≤ max ‖g.dens 0‖ ‖g.dens 1‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    have hmul : ‖g.dens (n + 2)‖ ≤
        (max ‖g.dens 0‖ ‖g.dens 1‖ *
          Real.exp (∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0)) *
        Real.exp (‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0) := by
      refine le_trans hstep (mul_le_mul ih hexp (by positivity) (by positivity))
    refine le_trans hmul ?_
    rw [mul_assoc, ← Real.exp_add]
    have hle : (∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0) +
        ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ ^ 2 / denPairingRe g 0 ≤
        ∑ k ∈ Finset.range (n + 2), ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (n := n)]
      have := hanonneg n
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hK

/-! ### Full convergence for non-summable partial denominators (DLMF 1.12.28) -/

/-- **The Stern–Stolz alternative under the sector hypothesis.**  If
`∑ ‖bₙ‖ = ∞` then `Eₙ → ∞` (equivalently `‖Bₙ‖‖Bₙ₊₁‖ → ∞`, since
`Eₙ ≤ ‖Bₙ₊₁‖‖Bₙ‖ ≤ Eₙ/δ`).

Proof by contradiction.  `E` is nondecreasing, so a failure means `E ≤ C`;
then `∑ ‖bₖ‖‖Bₖ‖² ≤ C/δ`, so `norm_dens_le_exp` bounds `‖Bₙ‖` above by
`max(‖B₀‖,‖B₁‖)·exp(C/(δE₀))`, and `‖Bₙ₊₁‖‖Bₙ‖ ≥ E₀` then bounds `‖Bₙ‖` below by
a positive constant `Q`.  Hence `Q²∑_{k<n}‖bₖ‖ ≤ ∑‖bₖ‖‖Bₖ‖² ≤ C/δ` for every
`n`, contradicting the divergence of `∑‖bₖ‖`. -/
-- no-dlmf: divergence of the continuant pairing (method-kit meta-lemma)
theorem tendsto_denPairingRe_atTop (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hns : ¬ Summable fun n => ‖b n‖) :
    Tendsto (denPairingRe g) atTop atTop := by
  have hmono := denPairingRe_mono hδ hs hbc
  refine Filter.tendsto_atTop_atTop_of_monotone' hmono ?_
  rintro ⟨C, hC⟩
  have hCle : ∀ n, denPairingRe g n ≤ C := fun n => hC (Set.mem_range_self n)
  have hm0 : 0 < denPairingRe g 0 := denPairingRe_pos hδ hs hb0 hbc 0
  have hKpos : 0 < max ‖g.dens 0‖ ‖g.dens 1‖ :=
    lt_of_lt_of_le (norm_dens_pos hδ hs hb0 hbc 0) (le_max_left _ _)
  -- the weighted partial sums are bounded
  have hWsum : ∀ n, ∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 ≤ C / δ := by
    intro n
    have h := sum_weight_le hs hbc (g := g) n
    have hle : ∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 ≤
        ∑ k ∈ Finset.range (n + 1), ‖b k‖ * ‖g.dens k‖ ^ 2 := by
      rw [Finset.sum_range_succ]
      have : (0 : ℝ) ≤ ‖b n‖ * ‖g.dens n‖ ^ 2 := by positivity
      linarith
    rw [le_div_iff₀ hδ]
    nlinarith [hCle n]
  have hAsum : ∀ n, ∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0 ≤
      C / δ / denPairingRe g 0 := by
    intro n
    have hrw : ∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2 / denPairingRe g 0 =
        (∑ k ∈ Finset.range n, ‖b k‖ * ‖g.dens k‖ ^ 2) / denPairingRe g 0 := by
      simp [div_eq_mul_inv, ← Finset.sum_mul]
    rw [hrw]
    gcongr
    exact hWsum n
  -- hence the continuants are bounded above
  have hBmax : ∀ n, ‖g.dens n‖ ≤
      max ‖g.dens 0‖ ‖g.dens 1‖ * Real.exp (C / δ / denPairingRe g 0) := by
    intro n
    refine le_trans (norm_dens_le_exp hδ hs hb0 hbc n) ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hAsum n)) hKpos.le
  -- and therefore bounded below
  have hQpos : 0 < denPairingRe g 0 /
      (max ‖g.dens 0‖ ‖g.dens 1‖ * Real.exp (C / δ / denPairingRe g 0)) := by positivity
  have hBmin : ∀ n, denPairingRe g 0 /
      (max ‖g.dens 0‖ ‖g.dens 1‖ * Real.exp (C / δ / denPairingRe g 0)) ≤ ‖g.dens n‖ := by
    intro n
    have h1 : denPairingRe g 0 ≤ ‖g.dens (n + 1)‖ * ‖g.dens n‖ :=
      le_trans (hmono (Nat.zero_le n)) (denPairingRe_le n)
    have h2 := hBmax (n + 1)
    have h3 := norm_dens_pos hδ hs hb0 hbc n
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- the partial sums of ‖bₖ‖ are then bounded, contradicting non-summability
  set Q := denPairingRe g 0 /
    (max ‖g.dens 0‖ ‖g.dens 1‖ * Real.exp (C / δ / denPairingRe g 0)) with hQdef
  have hfinal : ∀ n, (∑ k ∈ Finset.range n, ‖b k‖) * Q ^ 2 ≤ C / δ := by
    intro n
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hWsum n)
    have hk := hBmin k
    have : Q ^ 2 ≤ ‖g.dens k‖ ^ 2 := by nlinarith [hQpos]
    nlinarith [norm_nonneg (b k)]
  have htend :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => norm_nonneg (b n)).mp hns
  obtain ⟨N, hN⟩ := (htend.eventually_ge_atTop (C / δ / Q ^ 2 + 1)).exists
  have hcancel : C / δ / Q ^ 2 * Q ^ 2 = C / δ := div_mul_cancel₀ _ (by positivity)
  have hfN := hfinal N
  nlinarith [hQpos, sq_nonneg Q]

/-- With `∑ ‖bₙ‖ = ∞` the consecutive convergents close up:
`‖fₙ₊₁ − fₙ‖ = 1/(‖Bₙ‖‖Bₙ₊₁‖) ≤ 1/Eₙ → 0`. -/
-- no-dlmf: vanishing convergent gap under non-summability
theorem tendsto_convs_diff_zero (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hns : ¬ Summable fun n => ‖b n‖) :
    Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0) := by
  have hE := tendsto_denPairingRe_atTop hδ hs hb0 hbc hns
  have hbound : ∀ n, ‖g.convs (n + 1) - g.convs n‖ ≤ 1 / denPairingRe g n := by
    intro n
    rw [convs_succ_sub_convs_eq hs (dens_ne_zero hδ hs hb0 hbc) n, norm_div, norm_pow, norm_neg,
      norm_one, one_pow, norm_mul]
    have h1 : denPairingRe g n ≤ ‖g.dens n‖ * ‖g.dens (n + 1)‖ := by
      have h := denPairingRe_le (g := g) n
      linarith [mul_comm ‖g.dens (n + 1)‖ ‖g.dens n‖ ▸ h]
    exact one_div_le_one_div_of_le (denPairingRe_pos hδ hs hb0 hbc n) h1
  refine squeeze_zero_norm hbound ?_
  simpa [one_div] using hE.inv_tendsto_atTop

/-- **Van Vleck's convergence theorem** (cone form, the "if" half of
DLMF 1.12.28): a sector fraction whose partial denominators are *not* absolutely
summable converges.  The even and odd parts converge by
`exists_tendsto_convs_even`/`_odd`, and non-summability closes the gap between
them. -/
-- no-dlmf: Van Vleck convergence, cone form ("if" half of DLMF 1.12.28; the
-- converse Stern–Stolz direction is `not_exists_tendsto_convs_of_summable`, and
-- the two together are `exists_tendsto_convs_iff`)
theorem exists_tendsto_convs (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hns : ¬ Summable fun n => ‖b n‖) :
    ∃ L : ℂ, Tendsto g.convs atTop (𝓝 L) := by
  obtain ⟨Le, hLe⟩ := exists_tendsto_convs_even hδ hs hb0 hbc
  obtain ⟨Lo, hLo⟩ := exists_tendsto_convs_odd hδ hs hb0 hbc
  have hgap := tendsto_convs_diff_zero hδ hs hb0 hbc hns
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have hsub0 : Tendsto (fun k => g.convs (2 * k + 1) - g.convs (2 * k)) atTop (𝓝 0) := by
    have := hgap.comp h2k
    simpa [Function.comp] using this
  have hsub : Tendsto (fun k => g.convs (2 * k + 1) - g.convs (2 * k)) atTop (𝓝 (Lo - Le)) :=
    hLo.sub hLe
  have hLoLe : Lo = Le := sub_eq_zero.mp (tendsto_nhds_unique hsub hsub0)
  exact ⟨Le, tendsto_of_even_odd hLe (hLoLe ▸ hLo)⟩

/-! ### Uniform tail bounds -/

/-- **Quantitative Cauchy estimate along a fixed parity.**  For `k ≤ m` and any
offset `r`,
```
  ‖f_{2m+r} − f_{2k+r}‖ ≤ δ⁻¹ (1/E_{2k+r} − 1/E_{2m+r}),
```
by telescoping `norm_convs_add_two_sub_convs_le` (the intermediate odd/even terms
drop out because `E` is monotone). -/
-- no-dlmf: telescoped tail estimate along a fixed parity
theorem norm_convs_tail_le (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (r k m : ℕ) (hkm : k ≤ m) :
    ‖g.convs (2 * m + r) - g.convs (2 * k + r)‖ ≤
      1 / δ * (1 / denPairingRe g (2 * k + r) - 1 / denPairingRe g (2 * m + r)) := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hstep := norm_convs_add_two_sub_convs_le hδ hs hb0 hbc (2 * m + r)
    have hmid : 1 / denPairingRe g (2 * (m + 1) + r) ≤ 1 / denPairingRe g (2 * m + r + 1) :=
      one_div_le_one_div_of_le (denPairingRe_pos hδ hs hb0 hbc (2 * m + r + 1))
        (denPairingRe_mono hδ hs hbc (by omega))
    have hidx : 2 * (m + 1) + r = 2 * m + r + 2 := by ring
    have htri : ‖g.convs (2 * m + r + 2) - g.convs (2 * k + r)‖ ≤
        ‖g.convs (2 * m + r + 2) - g.convs (2 * m + r)‖ +
          ‖g.convs (2 * m + r) - g.convs (2 * k + r)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hδ' : 0 < 1 / δ := by positivity
    rw [hidx]
    rw [hidx] at hmid
    linarith [htri, hstep, ih, mul_le_mul_of_nonneg_left hmid hδ'.le]

/-- The uniform form of the tail estimate: all later same-parity convergents stay
within `δ⁻¹/E_{2k+r}` of `f_{2k+r}`. -/
-- no-dlmf: uniform tail estimate along a fixed parity
theorem norm_convs_tail_bound (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (r k m : ℕ) (hkm : k ≤ m) :
    ‖g.convs (2 * m + r) - g.convs (2 * k + r)‖ ≤
      1 / δ * (1 / denPairingRe g (2 * k + r)) := by
  have h := norm_convs_tail_le hδ hs hb0 hbc r k m hkm
  have hpos : 0 < denPairingRe g (2 * m + r) := denPairingRe_pos hδ hs hb0 hbc _
  have hδ' : 0 < 1 / δ := by positivity
  have : (0 : ℝ) < 1 / denPairingRe g (2 * m + r) := by positivity
  nlinarith

/-- The total two-step variation of a sector fraction is bounded by
`1/(δ · Re b₀)`, uniformly in the number of terms. -/
-- no-dlmf: total two-step variation bound, cone form
theorem sum_norm_convs_add_two_sub_convs_le (hδ : 0 < δ)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖g.convs (n + 2) - g.convs n‖ ≤ 1 / (δ * (b 0).re) := by
  have h1 : ∑ n ∈ Finset.range N, ‖g.convs (n + 2) - g.convs n‖ ≤
      ∑ n ∈ Finset.range N, stepMajorant g δ n :=
    Finset.sum_le_sum fun n _ => norm_convs_add_two_sub_convs_le hδ hs hb0 hbc n
  have h2 := sum_stepMajorant_le hδ hs hb0 hbc N
  have h3 : 1 / δ * (1 / denPairingRe g 0) = 1 / (δ * (b 0).re) := by
    rw [denPairingRe_zero hs, div_mul_eq_div_div_swap]
    ring
  linarith [h3 ▸ h2]

/-! ### The `arg`-form (DLMF) statements -/

/-- **Van Vleck's theorem** (DLMF 1.12.27).  Let `g` be a continued fraction over
`ℂ` all of whose partial numerators are `1` and whose partial denominators
satisfy `bₙ ≠ 0` and `|ph bₙ| ≤ π/2 − ε` for a fixed `ε > 0`.  Then the
even-indexed and the odd-indexed convergents each converge to a finite limit (not
necessarily the same one). -/
-- no-dlmf: Van Vleck even/odd convergence on `GenContFract ℂ` (method-kit form of
-- DLMF 1.12.27; the DLMF display surface lives in Methods.Ch1ContinuedFractions)
theorem exists_tendsto_convs_even_odd_of_arg {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (hb0 : ∀ n, b n ≠ 0)
    (harg : ∀ n, |Complex.arg (b n)| ≤ Real.pi / 2 - ε) :
    (∃ Le : ℂ, Tendsto (fun k => g.convs (2 * k)) atTop (𝓝 Le)) ∧
      (∃ Lo : ℂ, Tendsto (fun k => g.convs (2 * k + 1)) atTop (𝓝 Lo)) := by
  have hεle : ε ≤ Real.pi / 2 := by
    have := abs_nonneg (Complex.arg (b 0))
    linarith [harg 0]
  have hδ : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hbc : ∀ n, Real.sin ε * ‖b n‖ ≤ (b n).re := fun n =>
    cone_of_abs_arg_le hε (hb0 n) (harg n)
  exact ⟨exists_tendsto_convs_even hδ hs hb0 hbc, exists_tendsto_convs_odd hδ hs hb0 hbc⟩

/-- **Van Vleck's convergence theorem** (the "if" half of DLMF 1.12.28): a
sector fraction (`bₙ ≠ 0`, `|ph bₙ| ≤ π/2 − ε`) whose partial denominators are
not absolutely summable converges. -/
-- no-dlmf: Van Vleck convergence on `GenContFract ℂ` ("if" half of DLMF 1.12.28;
-- both halves together are `exists_tendsto_convs_iff_of_arg`)
theorem exists_tendsto_convs_of_arg {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (hb0 : ∀ n, b n ≠ 0)
    (harg : ∀ n, |Complex.arg (b n)| ≤ Real.pi / 2 - ε)
    (hns : ¬ Summable fun n => ‖b n‖) :
    ∃ L : ℂ, Tendsto g.convs atTop (𝓝 L) := by
  have hεle : ε ≤ Real.pi / 2 := by
    have := abs_nonneg (Complex.arg (b 0))
    linarith [harg 0]
  have hδ : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  exact exists_tendsto_convs hδ hs hb0 (fun n => cone_of_abs_arg_le hε (hb0 n) (harg n)) hns

/-- The explicit Van Vleck variation bound: for a sector fraction with
`|ph bₙ| ≤ π/2 − ε`,
```
  ∑_{n < N} ‖fₙ₊₂ − fₙ‖ ≤ 1/(sin²ε · ‖b₀‖)
```
for every `N` — a bound depending only on `ε` and the first partial denominator.
This is what makes the convergence locally uniform in parameters on which the
fraction depends analytically: `ε` and `‖b₀‖` can be chosen uniformly on a
compact parameter set. -/
-- no-dlmf: explicit Van Vleck variation bound in terms of `ε` and `‖b₀‖`
theorem sum_norm_convs_add_two_sub_convs_le_of_arg {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (hb0 : ∀ n, b n ≠ 0)
    (harg : ∀ n, |Complex.arg (b n)| ≤ Real.pi / 2 - ε) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖g.convs (n + 2) - g.convs n‖ ≤
      1 / (Real.sin ε ^ 2 * ‖b 0‖) := by
  have hεle : ε ≤ Real.pi / 2 := by
    have := abs_nonneg (Complex.arg (b 0))
    linarith [harg 0]
  have hδ : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  have hbc : ∀ n, Real.sin ε * ‖b n‖ ≤ (b n).re := fun n =>
    cone_of_abs_arg_le hε (hb0 n) (harg n)
  have hb0pos : 0 < ‖b 0‖ := norm_pos_iff.mpr (hb0 0)
  have hre : 0 < (b 0).re := lt_of_lt_of_le (by positivity) (hbc 0)
  refine le_trans (sum_norm_convs_add_two_sub_convs_le hδ hs hb0 hbc N) ?_
  have h1 : Real.sin ε ^ 2 * ‖b 0‖ ≤ Real.sin ε * (b 0).re := by
    nlinarith [hbc 0]
  have h2 : 0 < Real.sin ε ^ 2 * ‖b 0‖ := by positivity
  exact one_div_le_one_div_of_le h2 h1

/-- The continuant denominators of a sector fraction never vanish
(DLMF §1.12(vi), `Bₙ ≠ 0`), in `arg` form. -/
-- no-dlmf: sector continuant nonvanishing, `arg` form
theorem dens_ne_zero_of_arg {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (hb0 : ∀ n, b n ≠ 0)
    (harg : ∀ n, |Complex.arg (b n)| ≤ Real.pi / 2 - ε) (n : ℕ) : g.dens n ≠ 0 := by
  have hεle : ε ≤ Real.pi / 2 := by
    have := abs_nonneg (Complex.arg (b 0))
    linarith [harg 0]
  have hδ : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  exact dens_ne_zero hδ hs hb0 (fun m => cone_of_abs_arg_le hε (hb0 m) (harg m)) n

/-! ### Stern–Stolz: an absolutely summable sector fraction diverges

The converse half of DLMF 1.12.28.  It needs no sector geometry for the growth
estimate — the Wallis recurrence alone gives `‖Bₙ‖ ≤ ∏_{k<n}(1 + ‖bₖ‖)` — and
uses the sector hypothesis only through `Bₙ ≠ 0`, to write the convergent gap as
`1/(‖Bₙ‖‖Bₙ₊₁‖)`. -/

/-- **The crude continuant product bound** `‖Bₙ‖ ≤ ∏_{k<n}(1 + ‖bₖ‖)`, a direct
two-step induction on the Wallis recurrence `Bₙ₊₂ = bₙ₊₁Bₙ₊₁ + Bₙ`.  Unlike
`norm_dens_le_exp` it is unconditional: no sector hypothesis enters. -/
-- no-dlmf: crude product bound for the continuants (Stern–Stolz support lemma)
theorem norm_dens_le_prod (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (n : ℕ) :
    ‖g.dens n‖ ≤ ∏ k ∈ Finset.range n, (1 + ‖b k‖) := by
  have hPnonneg : ∀ m : ℕ, (0 : ℝ) ≤ ∏ k ∈ Finset.range m, (1 + ‖b k‖) :=
    fun m => Finset.prod_nonneg fun k _ => by positivity
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [dens_one_eq hs]
    have h1 : ∏ k ∈ Finset.range 1, (1 + ‖b k‖) = 1 + ‖b 0‖ := by simp
    rw [h1]
    linarith
  | more n ih ih1 =>
    have hmono : ∏ k ∈ Finset.range n, (1 + ‖b k‖) ≤
        ∏ k ∈ Finset.range (n + 1), (1 + ‖b k‖) := by
      rw [Finset.prod_range_succ]
      nlinarith [hPnonneg n, norm_nonneg (b n)]
    rw [dens_two_step hs n]
    calc ‖b (n + 1) * g.dens (n + 1) + g.dens n‖
        ≤ ‖b (n + 1)‖ * ‖g.dens (n + 1)‖ + ‖g.dens n‖ := by
          simpa [norm_mul] using norm_add_le (b (n + 1) * g.dens (n + 1)) (g.dens n)
      _ ≤ ‖b (n + 1)‖ * (∏ k ∈ Finset.range (n + 1), (1 + ‖b k‖)) +
            ∏ k ∈ Finset.range (n + 1), (1 + ‖b k‖) := by
          have := mul_le_mul_of_nonneg_left ih1 (norm_nonneg (b (n + 1)))
          linarith [ih.trans hmono]
      _ = ∏ k ∈ Finset.range (n + 2), (1 + ‖b k‖) := by
          conv_rhs => rw [show n + 2 = (n + 1) + 1 from rfl, Finset.prod_range_succ]
          ring

/-- **Stern–Stolz** (the "only if" half of DLMF 1.12.28).  If `∑ ‖bₙ‖ < ∞` then
`‖Bₙ‖ ≤ exp(∑ ‖bₖ‖)` for every `n`, so the consecutive convergent gap
`‖fₙ₊₁ − fₙ‖ = 1/(‖Bₙ‖‖Bₙ₊₁‖) ≥ exp(−2∑‖bₖ‖)` stays bounded away from `0`; a
convergent sequence has vanishing consecutive gaps, so the fraction diverges. -/
-- no-dlmf: Stern–Stolz divergence, cone form ("only if" half of DLMF 1.12.28)
theorem not_exists_tendsto_convs_of_summable (hδ : 0 < δ)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re)
    (hsum : Summable fun n => ‖b n‖) :
    ¬ ∃ L : ℂ, Tendsto g.convs atTop (𝓝 L) := by
  set T := ∑' n : ℕ, ‖b n‖ with hT
  have hE : ∀ n : ℕ, ‖g.dens n‖ ≤ Real.exp T := by
    intro n
    refine (norm_dens_le_prod hs n).trans ?_
    calc ∏ k ∈ Finset.range n, (1 + ‖b k‖)
        ≤ ∏ k ∈ Finset.range n, Real.exp ‖b k‖ := by
          refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
          linarith [Real.add_one_le_exp ‖b k‖]
      _ = Real.exp (∑ k ∈ Finset.range n, ‖b k‖) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp T :=
          Real.exp_le_exp.mpr (hsum.sum_le_tsum _ fun i _ => norm_nonneg _)
  rintro ⟨L, hL⟩
  have hgap : Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => g.convs (n + 1)) atTop (𝓝 L) :=
      hL.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using h1.sub hL
  have hnorm : Tendsto (fun n => ‖g.convs (n + 1) - g.convs n‖) atTop (𝓝 0) := by
    simpa using hgap.norm
  have hlow : ∀ n : ℕ, Real.exp (-(2 * T)) ≤ ‖g.convs (n + 1) - g.convs n‖ := by
    intro n
    have hx : 0 < ‖g.dens n‖ := norm_dens_pos hδ hs hb0 hbc n
    have hy : 0 < ‖g.dens (n + 1)‖ := norm_dens_pos hδ hs hb0 hbc (n + 1)
    have heq : ‖g.convs (n + 1) - g.convs n‖ = 1 / (‖g.dens n‖ * ‖g.dens (n + 1)‖) := by
      rw [convs_succ_sub_convs_eq hs (dens_ne_zero hδ hs hb0 hbc) n, norm_div, norm_pow,
        norm_neg, norm_one, one_pow, norm_mul]
    rw [heq, Real.exp_neg, show (2 : ℝ) * T = T + T from by ring, Real.exp_add,
      show (Real.exp T * Real.exp T)⁻¹ = 1 / (Real.exp T * Real.exp T) from by rw [one_div]]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul (hE n) (hE (n + 1)) hy.le (Real.exp_pos T).le)
  have hcon : Real.exp (-(2 * T)) ≤ 0 :=
    ge_of_tendsto hnorm (Filter.Eventually.of_forall hlow)
  linarith [Real.exp_pos (-(2 * T))]

/-- **Van Vleck's convergence criterion in full** (DLMF 1.12.28, cone form): a
sector fraction converges *if and only if* its partial denominators are not
absolutely summable. -/
-- no-dlmf: DLMF 1.12.28 on `GenContFract ℂ`, cone form (both halves; the DLMF
-- display surface lives in Methods.Ch1ContinuedFractions)
theorem exists_tendsto_convs_iff (hδ : 0 < δ) (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩)
    (hb0 : ∀ n, b n ≠ 0) (hbc : ∀ n, δ * ‖b n‖ ≤ (b n).re) :
    (∃ L : ℂ, Tendsto g.convs atTop (𝓝 L)) ↔ ¬ Summable fun n => ‖b n‖ :=
  ⟨fun hconv hsum => not_exists_tendsto_convs_of_summable hδ hs hb0 hbc hsum hconv,
    exists_tendsto_convs hδ hs hb0 hbc⟩

/-- **Van Vleck's convergence criterion in full** (DLMF 1.12.28), `arg` form: a
fraction with all partial numerators `1` and `bₙ ≠ 0`, `|ph bₙ| ≤ π/2 − ε`
converges if and only if `∑ ‖bₙ‖ = ∞`. -/
-- no-dlmf: DLMF 1.12.28 on `GenContFract ℂ`, `arg` form (both halves)
theorem exists_tendsto_convs_iff_of_arg {ε : ℝ} (hε : 0 < ε)
    (hs : ∀ n, g.s.get? n = some ⟨1, b n⟩) (hb0 : ∀ n, b n ≠ 0)
    (harg : ∀ n, |Complex.arg (b n)| ≤ Real.pi / 2 - ε) :
    (∃ L : ℂ, Tendsto g.convs atTop (𝓝 L)) ↔ ¬ Summable fun n => ‖b n‖ := by
  have hεle : ε ≤ Real.pi / 2 := by
    have := abs_nonneg (Complex.arg (b 0))
    linarith [harg 0]
  have hδ : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [Real.pi_pos])
  exact exists_tendsto_convs_iff hδ hs hb0 fun n => cone_of_abs_arg_le hε (hb0 n) (harg n)

end Fraction

end VanVleck

end FLMF.Methods
