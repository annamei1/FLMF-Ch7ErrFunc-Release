import Mathlib.Algebra.ContinuedFractions.Determinant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Analytic continued-fraction theory (method kit, DLMF §1.12 / §3.10)

Mathlib's `Algebra.ContinuedFractions` provides the *algebra* of generalized
continued fractions (`GenContFract`): the Wallis continuant recurrence and the
determinant formula `Aₙ Bₙ₊₁ − Bₙ Aₙ₊₁ = ∏ (−aᵢ)`.  It contains **no**
convergence theory for continued fractions that do not arise from the real
`ContFract.of` expansion.  This file supplies the first analytic layer:

1. **The Śleszyński–Pringsheim theorem** (`cauchySeq_convs_of_pringsheim`,
   `exists_tendsto_convs_of_pringsheim`): over a complete normed field, if every
   partial pair satisfies `‖aₖ‖ + 1 ≤ ‖bₖ‖`, the convergents converge.  Route:
   the determinant formula gives `‖fₙ₊₁ − fₙ‖ = ∏‖aᵢ‖ / (‖Bₙ‖‖Bₙ₊₁‖)`; the
   inductive lower bound `‖Bₙ‖ + ∏‖aᵢ‖ ≤ ‖Bₙ₊₁‖` turns this into the
   telescoping bound `‖fₙ₊₁ − fₙ‖ ≤ 1/‖Bₙ‖ − 1/‖Bₙ₊₁‖`, whose partial sums are
   bounded by `1`; absolute summability of the differences gives Cauchy.

2. **Equivalence transformations** (`equivTransform`, `equivTransform_convs`):
   the classical rescaling `aₙ ↦ cₙ₋₁cₙ aₙ`, `bₙ ↦ cₙ bₙ` (with `c₋₁ = 1`)
   multiplies the continuants `Aₙ, Bₙ` by `c₀ ⋯ cₙ₋₁` and therefore preserves
   **every** convergent — the lever for normalizing a fraction toward a
   Pringsheim-applicable or S-fraction form.

3. **Positive (Stieltjes-type) fractions** (`convGap`, `monotone_convs_even`,
   `antitone_convs_odd`, `convs_even_le_odd`, `exists_tendsto_convs_even`,
   `exists_tendsto_convs_odd`, `exists_tendsto_convs_of_gap_tendsto_zero`):
   for a real fraction with all `aₖ, bₖ > 0` the even convergents increase, the
   odd ones decrease, evens ≤ odds, and both subsequences converge; the whole
   sequence converges as soon as the gap `fₙ₊₁ − fₙ → 0`.  This is the
   even/odd half of the classical Stieltjes convergence theory, covering
   fractions (like DLMF 6.9.1, `aₖ = ⌈k/2⌉` unbounded) that Pringsheim's
   hypothesis cannot reach.

4. **Even contraction** (`wallis_even_contraction`,
   `eq_mul_of_wallis_recurrence`): the division-free two-step recurrence
   obtained by eliminating the odd-index continuants from a Wallis recurrence,
   plus the two-seed uniqueness lemma that identifies the continuants of the
   *even part* of a fraction (DLMF §1.12(v)) with the rescaled even-index
   continuants of the original.

All indexing follows Mathlib's `GenContFract`: the pair at position `n` of
`g.s` holds the classical `(aₙ₊₁, bₙ₊₁)`, `g.dens 0 = 1`, and
`g.convs n = g.nums n / g.dens n`.
-/

namespace FLMF.Methods

open Filter Topology GenContFract Finset

/-! ### Products of partial numerators -/

section PartNumProd

variable {K : Type*} [Field K] (g : GenContFract K)

/-- `∏_{i < n} aᵢ`, the product of the first `n` partial numerators of `g`,
with entries past termination counted as `0`.  This is the numerator of the
convergent difference `fₙ₊₁ − fₙ` (up to sign), via the determinant formula. -/
-- no-dlmf: continued-fraction bookkeeping (partial-numerator product)
noncomputable def partNumProd (n : ℕ) : K :=
  ∏ i ∈ Finset.range n, (g.partNums.get? i).getD 0

-- no-dlmf: continued-fraction bookkeeping
theorem partNumProd_succ (n : ℕ) :
    partNumProd g (n + 1) = partNumProd g n * (g.partNums.get? n).getD 0 :=
  Finset.prod_range_succ _ n

end PartNumProd

section PartNumProdField

variable {K : Type*} [Field K] {g : GenContFract K}

/-- The determinant formula in `partNumProd` form:
`Aₙ Bₙ₊₁ − Bₙ Aₙ₊₁ = (−1)ⁿ⁺¹ ∏_{i ≤ n} aᵢ`. -/
-- no-dlmf: determinant formula, signed-product form
theorem determinant_eq_neg_one_pow_mul_partNumProd (n : ℕ) :
    g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) =
      (-1) ^ (n + 1) * partNumProd g (n + 1) := by
  have h := GenContFract.determinant (g := g) (n := n)
  rwa [Finset.prod_neg, Finset.card_range] at h

/-- Difference of consecutive convergents, in signed-product form:
`fₙ₊₁ − fₙ = (−1)ⁿ ∏_{i ≤ n} aᵢ / (Bₙ Bₙ₊₁)` (valid when the denominators do
not vanish). -/
-- no-dlmf: convergent-difference formula from the determinant identity
theorem convs_succ_sub_convs {n : ℕ} (h0 : g.dens n ≠ 0) (h1 : g.dens (n + 1) ≠ 0) :
    g.convs (n + 1) - g.convs n =
      (-1) ^ n * partNumProd g (n + 1) / (g.dens n * g.dens (n + 1)) := by
  have hdet := determinant_eq_neg_one_pow_mul_partNumProd (g := g) (n := n)
  rw [conv_eq_num_div_den, conv_eq_num_div_den, div_sub_div _ _ h1 h0,
    div_eq_div_iff (mul_ne_zero h1 h0) (mul_ne_zero h0 h1)]
  linear_combination (-(g.dens n * g.dens (n + 1))) * hdet

/-- The determinant formula at the `contsAux` level:
`A_{n-1} Bₙ − B_{n-1} Aₙ = (−1)ⁿ ∏_{i < n} aᵢ` (with `A₋₁ = 1`, `B₋₁ = 0`,
so that the `n = 0` case reads `1 = 1`). -/
-- no-dlmf: determinant formula, `contsAux`-level signed-product form
theorem contsAux_determinant (n : ℕ) :
    (g.contsAux n).a * (g.contsAux (n + 1)).b - (g.contsAux n).b * (g.contsAux (n + 1)).a =
      (-1) ^ n * partNumProd g n := by
  cases n with
  | zero =>
    simp [GenContFract.zeroth_contAux_eq_one_zero, GenContFract.first_contAux_eq_h_one,
      partNumProd]
  | succ m =>
    have h := determinant_eq_neg_one_pow_mul_partNumProd (g := g) (n := m)
    simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] at h
    exact h

end PartNumProdField

/-! ### The Śleszyński–Pringsheim theorem -/

section Pringsheim

variable {K : Type*} [NormedField K] {g : GenContFract K}

/-- `∏_{i < n} ‖aᵢ‖`, with entries past termination counted as `0`. -/
-- no-dlmf: continued-fraction bookkeeping (norm of the numerator product)
noncomputable def partNumNormProd (g : GenContFract K) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ‖(g.partNums.get? i).getD 0‖

-- no-dlmf: continued-fraction bookkeeping
theorem partNumNormProd_nonneg (g : GenContFract K) (n : ℕ) :
    0 ≤ partNumNormProd g n :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

-- no-dlmf: continued-fraction bookkeeping
theorem partNumNormProd_succ (g : GenContFract K) (n : ℕ) :
    partNumNormProd g (n + 1) = partNumNormProd g n * ‖(g.partNums.get? n).getD 0‖ :=
  Finset.prod_range_succ _ n

/-- Norm of the determinant formula: `‖Aₙ Bₙ₊₁ − Bₙ Aₙ₊₁‖ = ∏_{i ≤ n} ‖aᵢ‖`. -/
-- no-dlmf: determinant formula, norm form
theorem norm_determinant (g : GenContFract K) (n : ℕ) :
    ‖g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1)‖ =
      partNumNormProd g (n + 1) := by
  rw [GenContFract.determinant (g := g) (n := n), norm_prod]
  simp [partNumNormProd]

/-- The Pringsheim denominator growth bound: under `‖aₖ‖ + 1 ≤ ‖bₖ‖`,
`‖Bₙ‖ + ∏_{i ≤ n} ‖aᵢ‖ ≤ ‖Bₙ₊₁‖`.  (Entries past termination contribute a zero
product, so no non-termination hypothesis is needed.) -/
-- no-dlmf: Pringsheim continuant growth (Śleszyński–Pringsheim, denominator half)
theorem norm_dens_add_partNumNormProd_le
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) :
    ∀ n, ‖g.dens n‖ + partNumNormProd g (n + 1) ≤ ‖g.dens (n + 1)‖ := by
  intro n
  induction n with
  | zero =>
    cases h0 : g.s.get? 0 with
    | none =>
      have hterm : g.TerminatedAt 0 := terminatedAt_iff_s_none.mpr h0
      rw [dens_stable_of_terminated (Nat.zero_le 1) hterm]
      have : g.partNums.get? 0 = none := partNum_none_iff_s_none.mpr h0
      simp [partNumNormProd, this]
    | some gp =>
      rw [first_den_eq h0]
      have hpn : g.partNums.get? 0 = some gp.a := partNum_eq_s_a h0
      have h1 := hg 0 gp h0
      simp only [zeroth_den_eq_one, norm_one]
      simpa [partNumNormProd, hpn, add_comm] using h1
  | succ n ih =>
    cases h1 : g.s.get? (n + 1) with
    | none =>
      have hterm : g.TerminatedAt (n + 1) := terminatedAt_iff_s_none.mpr h1
      rw [dens_stable_of_terminated (Nat.le_succ (n + 1)) hterm]
      have : g.partNums.get? (n + 1) = none := partNum_none_iff_s_none.mpr h1
      rw [partNumNormProd_succ, this]
      simp
    | some gp =>
      have hrec : g.dens (n + 2) = gp.b * g.dens (n + 1) + gp.a * g.dens n :=
        dens_recurrence h1 rfl rfl
      have hpn : g.partNums.get? (n + 1) = some gp.a := partNum_eq_s_a h1
      have hb := hg (n + 1) gp h1
      -- lower bound ‖u + v‖ ≥ ‖u‖ − ‖v‖
      have hlow : ‖gp.b * g.dens (n + 1)‖ - ‖gp.a * g.dens n‖ ≤
          ‖gp.b * g.dens (n + 1) + gp.a * g.dens n‖ := by
        have h := norm_sub_norm_le (gp.b * g.dens (n + 1)) (-(gp.a * g.dens n))
        simpa [sub_neg_eq_add] using h
      rw [hrec, partNumNormProd_succ, hpn, Option.getD_some]
      have hP : 0 ≤ partNumNormProd g (n + 1) := partNumNormProd_nonneg g (n + 1)
      have ha0 : (0 : ℝ) ≤ ‖gp.a‖ := norm_nonneg _
      have hd1 : (0 : ℝ) ≤ ‖g.dens (n + 1)‖ := norm_nonneg _
      refine le_trans ?_ hlow
      rw [norm_mul, norm_mul]
      nlinarith [mul_le_mul_of_nonneg_right hb hd1,
        mul_le_mul_of_nonneg_left ih ha0]

/-- Under the Pringsheim hypothesis, all continuant denominators satisfy
`1 ≤ ‖Bₙ‖` (in particular they never vanish). -/
-- no-dlmf: Pringsheim continuant lower bound
theorem one_le_norm_dens
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) :
    ∀ n, 1 ≤ ‖g.dens n‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_dens_add_partNumNormProd_le hg n
    have hP := partNumNormProd_nonneg g (n + 1)
    linarith

/-- Under the Pringsheim hypothesis, `‖Bₙ‖` is monotone in `n`. -/
-- no-dlmf: Pringsheim continuant monotonicity
theorem monotone_norm_dens
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) :
    Monotone fun n => ‖g.dens n‖ := by
  apply monotone_nat_of_le_succ
  intro n
  have h := norm_dens_add_partNumNormProd_le hg n
  have hP := partNumNormProd_nonneg g (n + 1)
  linarith

/-- Norm of the convergent difference:
`‖fₙ₊₁ − fₙ‖ = ∏_{i ≤ n} ‖aᵢ‖ / (‖Bₙ‖ ‖Bₙ₊₁‖)`. -/
-- no-dlmf: convergent-difference norm from the determinant formula
theorem norm_convs_succ_sub_convs
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) (n : ℕ) :
    ‖g.convs (n + 1) - g.convs n‖ =
      partNumNormProd g (n + 1) / (‖g.dens n‖ * ‖g.dens (n + 1)‖) := by
  have h0 : g.dens n ≠ 0 := by
    intro h
    have h1 := one_le_norm_dens hg n
    rw [h, norm_zero] at h1
    linarith
  have h1 : g.dens (n + 1) ≠ 0 := by
    intro h
    have h2 := one_le_norm_dens hg (n + 1)
    rw [h, norm_zero] at h2
    linarith
  have hnum : g.nums (n + 1) * g.dens n - g.dens (n + 1) * g.nums n =
      -(g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1)) := by ring
  rw [conv_eq_num_div_den, conv_eq_num_div_den, div_sub_div _ _ h1 h0, norm_div,
    norm_mul, hnum, norm_neg, norm_determinant, mul_comm ‖g.dens (n + 1)‖]

/-- The telescoping Pringsheim bound: `‖fₙ₊₁ − fₙ‖ ≤ 1/‖Bₙ‖ − 1/‖Bₙ₊₁‖`. -/
-- no-dlmf: Pringsheim telescoping bound
theorem norm_convs_succ_sub_convs_le
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) (n : ℕ) :
    ‖g.convs (n + 1) - g.convs n‖ ≤ 1 / ‖g.dens n‖ - 1 / ‖g.dens (n + 1)‖ := by
  have h0 : (0 : ℝ) < ‖g.dens n‖ := lt_of_lt_of_le one_pos (one_le_norm_dens hg n)
  have h1 : (0 : ℝ) < ‖g.dens (n + 1)‖ := lt_of_lt_of_le one_pos (one_le_norm_dens hg (n + 1))
  have hkey : partNumNormProd g (n + 1) ≤ ‖g.dens (n + 1)‖ - ‖g.dens n‖ := by
    have := norm_dens_add_partNumNormProd_le hg n
    linarith
  rw [norm_convs_succ_sub_convs hg n, div_sub_div _ _ h0.ne' h1.ne', one_mul, mul_one]
  gcongr

/-- **The Śleszyński–Pringsheim theorem** (Cauchy form).  If every partial pair
of the generalized continued fraction `g` over a normed field satisfies
`‖aₖ‖ + 1 ≤ ‖bₖ‖`, then the convergents of `g` form a Cauchy sequence.
(DLMF §1.12(v) / §3.10: the classical Pringsheim convergence criterion.) -/
-- no-dlmf: Śleszyński–Pringsheim convergence criterion (method-kit meta-lemma)
theorem cauchySeq_convs_of_pringsheim
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) :
    CauchySeq g.convs := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => 1 / ‖g.dens n‖ - 1 / ‖g.dens (n + 1)‖)
  · intro n
    rw [dist_eq_norm, norm_sub_rev]
    exact norm_convs_succ_sub_convs_le hg n
  · apply summable_of_sum_range_le (c := 1)
    · intro n
      have h0 : (0 : ℝ) < ‖g.dens n‖ := lt_of_lt_of_le one_pos (one_le_norm_dens hg n)
      have hmono := monotone_norm_dens hg (Nat.le_succ n)
      have := one_div_le_one_div_of_le h0 hmono
      linarith
    · intro n
      rw [Finset.sum_range_sub' (f := fun i => 1 / ‖g.dens i‖)]
      have h0 : (0 : ℝ) < ‖g.dens n‖ := lt_of_lt_of_le one_pos (one_le_norm_dens hg n)
      have : (0 : ℝ) ≤ 1 / ‖g.dens n‖ := by positivity
      simp only [zeroth_den_eq_one, norm_one]
      linarith

/-- **The Śleszyński–Pringsheim theorem.**  Over a complete normed field, if
every partial pair of `g` satisfies `‖aₖ‖ + 1 ≤ ‖bₖ‖`, the convergents of `g`
converge. -/
-- no-dlmf: Śleszyński–Pringsheim convergence criterion (method-kit meta-lemma)
theorem exists_tendsto_convs_of_pringsheim [CompleteSpace K]
    (hg : ∀ n gp, g.s.get? n = some gp → ‖gp.a‖ + 1 ≤ ‖gp.b‖) :
    ∃ ℓ : K, Tendsto g.convs atTop (𝓝 ℓ) :=
  cauchySeq_tendsto_of_complete (cauchySeq_convs_of_pringsheim hg)

end Pringsheim

/-! ### Equivalence transformations -/

section EquivTransform

variable {K : Type*} [Field K]

/-- Scale factor for the `n`-th partial numerator in an equivalence
transformation: `cₙ₋₁ cₙ` with the convention `c₋₁ = 1`. -/
-- no-dlmf: equivalence-transformation bookkeeping
def equivFactor (c : ℕ → K) : ℕ → K
  | 0 => c 0
  | n + 1 => c n * c (n + 1)

@[simp]
theorem equivFactor_zero (c : ℕ → K) : equivFactor c 0 = c 0 := rfl

@[simp]
theorem equivFactor_succ (c : ℕ → K) (n : ℕ) :
    equivFactor c (n + 1) = c n * c (n + 1) := rfl

/-- The classical **equivalence transformation** of a generalized continued
fraction: `aₙ ↦ cₙ₋₁ cₙ aₙ`, `bₙ ↦ cₙ bₙ` (with `c₋₁ = 1`).  It preserves all
convergents (`equivTransform_convs`). -/
-- no-dlmf: equivalence transformation of a generalized continued fraction
def equivTransform (c : ℕ → K) (g : GenContFract K) : GenContFract K :=
  ⟨g.h,
    ⟨fun n => (g.s.get? n).map fun gp => ⟨equivFactor c n * gp.a, c n * gp.b⟩,
      fun {n} h => by
        rw [Option.map_eq_none_iff] at h ⊢
        exact g.s.2 h⟩⟩

@[simp]
theorem equivTransform_h (c : ℕ → K) (g : GenContFract K) :
    (equivTransform c g).h = g.h := rfl

@[simp]
theorem equivTransform_s_get? (c : ℕ → K) (g : GenContFract K) (n : ℕ) :
    (equivTransform c g).s.get? n =
      (g.s.get? n).map fun gp => ⟨equivFactor c n * gp.a, c n * gp.b⟩ := rfl

-- no-dlmf: equivalence transformation preserves termination
theorem equivTransform_terminatedAt_iff (c : ℕ → K) (g : GenContFract K) (n : ℕ) :
    (equivTransform c g).TerminatedAt n ↔ g.TerminatedAt n := by
  rw [terminatedAt_iff_s_none, terminatedAt_iff_s_none, equivTransform_s_get?,
    Option.map_eq_none_iff]

/-- Continuants under an equivalence transformation: as long as the fraction has
not terminated before position `n`, the `n`-th continuants of the transformed
fraction are `c₀ ⋯ cₙ₋₁` times those of `g`. -/
-- no-dlmf: equivalence transformation scales the continuants
theorem equivTransform_conts (c : ℕ → K) {g : GenContFract K} :
    ∀ n : ℕ, (n = 0 ∨ ¬g.TerminatedAt (n - 1)) →
      ((equivTransform c g).conts n).a = (∏ k ∈ Finset.range n, c k) * (g.conts n).a ∧
        ((equivTransform c g).conts n).b = (∏ k ∈ Finset.range n, c k) * (g.conts n).b := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; simp
  | one =>
    intro h
    have hnt : ¬g.TerminatedAt 0 := h.resolve_left one_ne_zero
    obtain ⟨gp, hgp⟩ : ∃ gp, g.s.get? 0 = some gp :=
      Option.ne_none_iff_exists'.mp (by rwa [terminatedAt_iff_s_none] at hnt)
    have hgp' : (equivTransform c g).s.get? 0 =
        some ⟨equivFactor c 0 * gp.a, c 0 * gp.b⟩ := by
      rw [equivTransform_s_get?, hgp, Option.map_some]
    rw [first_cont_eq hgp, first_cont_eq hgp']
    constructor
    · simp only [equivFactor_zero, Finset.prod_range_one, equivTransform_h]
      ring
    · simp
  | more n ih ih1 =>
    intro h
    have hnt : ¬g.TerminatedAt (n + 1) := h.resolve_left (Nat.succ_ne_zero _)
    obtain ⟨gp, hgp⟩ : ∃ gp, g.s.get? (n + 1) = some gp :=
      Option.ne_none_iff_exists'.mp (by rwa [terminatedAt_iff_s_none] at hnt)
    have hn : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact Or.inl h0
      · exact Or.inr fun ht => hnt (terminated_stable (by omega) ht)
    have hn1 : n + 1 = 0 ∨ ¬g.TerminatedAt (n + 1 - 1) := by
      refine Or.inr fun ht => hnt (terminated_stable (by omega) ht)
    obtain ⟨ihA, ihB⟩ := ih hn
    obtain ⟨ih1A, ih1B⟩ := ih1 hn1
    have hgp' : (equivTransform c g).s.get? (n + 1) =
        some ⟨equivFactor c (n + 1) * gp.a, c (n + 1) * gp.b⟩ := by
      rw [equivTransform_s_get?, hgp, Option.map_some]
    have hrec := conts_recurrence (g := g) hgp rfl rfl
    have hrec' := conts_recurrence (g := equivTransform c g) hgp' rfl rfl
    rw [hrec, hrec']
    constructor
    · dsimp only
      rw [ihA, ih1A, equivFactor_succ]
      simp only [Finset.prod_range_succ]
      ring
    · dsimp only
      rw [ihB, ih1B, equivFactor_succ]
      simp only [Finset.prod_range_succ]
      ring

/-- **Equivalence transformations preserve all convergents**: for nonvanishing
scale factors `cₖ`, the fraction with `aₙ ↦ cₙ₋₁ cₙ aₙ`, `bₙ ↦ cₙ bₙ`
(`c₋₁ = 1`) has exactly the convergents of `g`.  (DLMF §1.12: equivalent
continued fractions.) -/
-- no-dlmf: equivalence transformation preserves the convergents (method-kit meta-lemma)
theorem equivTransform_convs (c : ℕ → K) (hc : ∀ k, c k ≠ 0) (g : GenContFract K)
    (n : ℕ) : (equivTransform c g).convs n = g.convs n := by
  have hprod : ∀ m : ℕ, (∏ k ∈ Finset.range m, c k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have key : ∀ m : ℕ, (m = 0 ∨ ¬g.TerminatedAt (m - 1)) →
      (equivTransform c g).convs m = g.convs m := by
    intro m hm
    obtain ⟨ha, hb⟩ := equivTransform_conts c m hm
    rw [conv_eq_conts_a_div_conts_b, conv_eq_conts_a_div_conts_b, ha, hb,
      mul_div_mul_left _ _ (hprod m)]
  by_cases hterm : ∃ m, g.TerminatedAt m
  · set N := Nat.find hterm with hN_def
    have hN : g.TerminatedAt N := Nat.find_spec hterm
    have hNmin : N = 0 ∨ ¬g.TerminatedAt (N - 1) := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Nat.find_min hterm (by omega))
    rcases le_or_gt n N with hle | hlt
    · refine key n ?_
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Nat.find_min hterm (by omega))
    · have hN' : (equivTransform c g).TerminatedAt N :=
        (equivTransform_terminatedAt_iff c g N).mpr hN
      rw [convs_stable_of_terminated hlt.le hN, convs_stable_of_terminated hlt.le hN']
      exact key N hNmin
  · push Not at hterm
    exact key n (Or.inr (hterm _))

end EquivTransform

/-! ### Even contraction of a Wallis recurrence

The *even part* of a continued fraction (DLMF §1.12(v)) is the fraction whose
convergents are the even-index convergents of the original.  At the continuant
level this is pure algebra: eliminating the odd-index terms from the Wallis
recurrence `uₖ₊₂ = bₖ₊₂ uₖ₊₁ + aₖ₊₂ uₖ` yields a second-order recurrence in
the even-index terms (`wallis_even_contraction`, stated multiplied-through so
no nonvanishing hypothesis is needed), and a two-seed uniqueness lemma
(`eq_mul_of_wallis_recurrence`) then identifies the continuants of the
contracted fraction with the (rescaled) even-index continuants of the
original.  Together these reduce "the even part converges to the same value"
to a subsequence argument. -/

section EvenContraction

variable {K : Type*} [CommRing K]

/-- **Even-contraction step**: for any solution `u` of the Wallis recurrence
`u (k+2) = b (k+2) * u (k+1) + a (k+2) * u k`, eliminating the odd-index
values gives the second-order recurrence
`b₂ₘ₊₂ u₂ₘ₊₄ = (b₂ₘ₊₄ b₂ₘ₊₃ b₂ₘ₊₂ + b₂ₘ₊₄ a₂ₘ₊₃ + a₂ₘ₊₄ b₂ₘ₊₂) u₂ₘ₊₂
− b₂ₘ₊₄ a₂ₘ₊₃ a₂ₘ₊₂ u₂ₘ` connecting three consecutive even-index terms.
This is the recurrence underlying the classical *even part* of a continued
fraction (DLMF §1.12(v)); stated in multiplied-through, division-free form it
is a pure ring identity. -/
-- no-dlmf: even-contraction two-step recurrence (method-kit meta-lemma)
theorem wallis_even_contraction {a b u : ℕ → K}
    (hrec : ∀ k, u (k + 2) = b (k + 2) * u (k + 1) + a (k + 2) * u k) (m : ℕ) :
    b (2 * m + 2) * u (2 * m + 4) =
      (b (2 * m + 4) * b (2 * m + 3) * b (2 * m + 2)
          + b (2 * m + 4) * a (2 * m + 3) + a (2 * m + 4) * b (2 * m + 2)) * u (2 * m + 2)
        - b (2 * m + 4) * a (2 * m + 3) * a (2 * m + 2) * u (2 * m) := by
  have e1 : 2 * m + 2 + 2 = 2 * m + 4 := by omega
  have e2 : 2 * m + 2 + 1 = 2 * m + 3 := by omega
  have e3 : 2 * m + 1 + 2 = 2 * m + 3 := by omega
  have e4 : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  have h4 := hrec (2 * m + 2); rw [e1, e2] at h4
  have h3 := hrec (2 * m + 1); rw [e3, e4] at h3
  have h2 := hrec (2 * m)
  rw [h4, h3, h2]
  ring

/-- **Two-seed uniqueness for scaled Wallis recurrences**: if `u` satisfies the
second-order recurrence `u (n+2) = p n * u (n+1) + q n * u n`, the rescaled
sequence `c * v` satisfies the same recurrence, and the two agree at the seeds
`0` and `1`, then `u n = c n * v n` for all `n`.  Applied with
`v n = (original continuant at 2n)` and the contraction recurrence from
`wallis_even_contraction`, this identifies the continuants of the even part of
a continued fraction with the rescaled even-index continuants of the
original. -/
-- no-dlmf: two-step recurrence uniqueness up to scaling (method-kit meta-lemma)
theorem eq_mul_of_wallis_recurrence {u v c p q : ℕ → K}
    (h0 : u 0 = c 0 * v 0) (h1 : u 1 = c 1 * v 1)
    (hu : ∀ n, u (n + 2) = p n * u (n + 1) + q n * u n)
    (hv : ∀ n, c (n + 2) * v (n + 2) = p n * (c (n + 1) * v (n + 1)) + q n * (c n * v n)) :
    ∀ n, u n = c n * v n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih ih1 =>
    rw [hu n, ih, ih1]
    exact (hv n).symm

end EvenContraction

/-! ### Positive (Stieltjes-type) continued fractions: the even/odd bracket -/

section Positive

variable {g : GenContFract ℝ}

/-- Positivity of the continuant denominators of a positive fraction. -/
-- no-dlmf: positive-fraction continuant positivity
theorem dens_pos (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    ∀ n, 0 < g.dens n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    cases h0 : g.s.get? 0 with
    | none =>
      rw [dens_stable_of_terminated (Nat.zero_le 1) (terminatedAt_iff_s_none.mpr h0)]
      simp
    | some gp =>
      rw [first_den_eq h0]
      exact (hpos 0 gp h0).2
  | more n ih ih1 =>
    cases h1 : g.s.get? (n + 1) with
    | none =>
      rw [dens_stable_of_terminated (Nat.le_succ (n + 1)) (terminatedAt_iff_s_none.mpr h1)]
      exact ih1
    | some gp =>
      rw [dens_recurrence h1 rfl rfl]
      obtain ⟨ha, hb⟩ := hpos (n + 1) gp h1
      exact add_pos (mul_pos hb ih1) (mul_pos ha ih)

-- no-dlmf: positive-fraction numerator-product nonnegativity
theorem partNumProd_nonneg
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) (n : ℕ) :
    0 ≤ partNumProd g n := by
  refine Finset.prod_nonneg fun i _ => ?_
  cases hi : g.partNums.get? i with
  | none => simp
  | some a =>
    obtain ⟨gp, hgp, rfl⟩ := exists_s_a_of_partNum hi
    exact (hpos i gp hgp).1.le

/-- The signed gap `Dₙ = (−1)ⁿ (fₙ₊₁ − fₙ)` between consecutive convergents.
For a positive fraction `Dₙ = ∏_{i ≤ n} aᵢ / (Bₙ Bₙ₊₁) ≥ 0` and `Dₙ` is
antitone: the convergents oscillate with shrinking amplitude. -/
-- no-dlmf: signed convergent gap (positive-fraction bookkeeping)
noncomputable def convGap (g : GenContFract ℝ) (n : ℕ) : ℝ :=
  (-1) ^ n * (g.convs (n + 1) - g.convs n)

-- no-dlmf: signed-gap formula from the determinant identity
theorem convGap_eq (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (n : ℕ) :
    convGap g n = partNumProd g (n + 1) / (g.dens n * g.dens (n + 1)) := by
  have hsq : ((-1 : ℝ)) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n, rfl⟩
  rw [convGap, convs_succ_sub_convs (dens_pos hpos n).ne' (dens_pos hpos (n + 1)).ne',
    mul_div_assoc, ← mul_assoc, hsq, one_mul]

-- no-dlmf: positive-fraction gap nonnegativity
theorem convGap_nonneg (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (n : ℕ) : 0 ≤ convGap g n := by
  rw [convGap_eq hpos n]
  exact div_nonneg (partNumProd_nonneg hpos (n + 1))
    (mul_pos (dens_pos hpos n) (dens_pos hpos (n + 1))).le

/-- For a positive fraction the gaps shrink: `Dₙ₊₁ ≤ Dₙ`. -/
-- no-dlmf: positive-fraction gap antitonicity (nested-interval half)
theorem convGap_succ_le (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (n : ℕ) : convGap g (n + 1) ≤ convGap g n := by
  rw [convGap_eq hpos n, convGap_eq hpos (n + 1)]
  cases h1 : g.s.get? (n + 1) with
  | none =>
    have hpn : g.partNums.get? (n + 1) = none := partNum_none_iff_s_none.mpr h1
    rw [partNumProd_succ, hpn]
    simp only [Option.getD_none, mul_zero, zero_div]
    exact div_nonneg (partNumProd_nonneg hpos (n + 1))
      (mul_pos (dens_pos hpos n) (dens_pos hpos (n + 1))).le
  | some gp =>
    have hpn : g.partNums.get? (n + 1) = some gp.a := partNum_eq_s_a h1
    have hrec : g.dens (n + 2) = gp.b * g.dens (n + 1) + gp.a * g.dens n :=
      dens_recurrence h1 rfl rfl
    obtain ⟨ha, hb⟩ := hpos (n + 1) gp h1
    have hd0 := dens_pos hpos n
    have hd1 := dens_pos hpos (n + 1)
    have hd2 := dens_pos hpos (n + 2)
    have hP := partNumProd_nonneg hpos (n + 1)
    rw [partNumProd_succ, hpn, Option.getD_some,
      div_le_div_iff₀ (mul_pos hd1 hd2) (mul_pos hd0 hd1), hrec]
    nlinarith [mul_nonneg (mul_nonneg hP hb.le) (mul_pos hd1 hd1).le]

/-- Two-step convergent difference in terms of the gaps:
`fₙ₊₂ − fₙ = (−1)ⁿ (Dₙ − Dₙ₊₁)`. -/
-- no-dlmf: two-step convergent difference (algebraic identity)
theorem convs_add_two_sub_convs (g : GenContFract ℝ) (n : ℕ) :
    g.convs (n + 2) - g.convs n = (-1) ^ n * (convGap g n - convGap g (n + 1)) := by
  have hsq : ((-1 : ℝ)) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n, rfl⟩
  simp only [convGap, pow_succ]
  linear_combination (-(g.convs (n + 2) - g.convs n)) * hsq

/-- Even convergents of a positive fraction increase. -/
-- no-dlmf: positive-fraction even-convergent monotonicity
theorem monotone_convs_even
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    Monotone fun k => g.convs (2 * k) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := convs_add_two_sub_convs g (2 * k)
  have hp : ((-1 : ℝ)) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, two_mul k⟩
  have hgap := convGap_succ_le hpos (2 * k)
  have hk : 2 * (k + 1) = 2 * k + 2 := by ring
  simp only [hk]
  rw [hp] at h
  linarith

/-- Odd convergents of a positive fraction decrease. -/
-- no-dlmf: positive-fraction odd-convergent antitonicity
theorem antitone_convs_odd
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    Antitone fun k => g.convs (2 * k + 1) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := convs_add_two_sub_convs g (2 * k + 1)
  have hp : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  have hgap := convGap_succ_le hpos (2 * k + 1)
  have hnn := convGap_nonneg hpos (2 * k + 1)
  have hk : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
  simp only [hk]
  rw [hp] at h
  linarith

/-- Every even convergent of a positive fraction is ≤ every odd convergent. -/
-- no-dlmf: positive-fraction even/odd bracketing
theorem convs_even_le_odd
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) (k j : ℕ) :
    g.convs (2 * k) ≤ g.convs (2 * j + 1) := by
  set m := max k j with hm
  have h1 : g.convs (2 * k) ≤ g.convs (2 * m) :=
    monotone_convs_even hpos (le_max_left k j)
  have h2 : g.convs (2 * m) ≤ g.convs (2 * m + 1) := by
    have hnn := convGap_nonneg hpos (2 * m)
    have hp : ((-1 : ℝ)) ^ (2 * m) = 1 := Even.neg_one_pow ⟨m, two_mul m⟩
    rw [convGap, hp, one_mul] at hnn
    linarith
  have h3 : g.convs (2 * m + 1) ≤ g.convs (2 * j + 1) :=
    antitone_convs_odd hpos (le_max_right k j)
  linarith

/-- The even convergents of a positive fraction converge (increasing and
bounded above by the first odd convergent). -/
-- no-dlmf: positive-fraction even-convergent convergence (method-kit meta-lemma)
theorem exists_tendsto_convs_even
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    ∃ L : ℝ, Tendsto (fun k => g.convs (2 * k)) atTop (𝓝 L) := by
  refine ⟨⨆ k, g.convs (2 * k), tendsto_atTop_ciSup (monotone_convs_even hpos) ?_⟩
  refine ⟨g.convs 1, ?_⟩
  rintro y ⟨k, rfl⟩
  simpa using convs_even_le_odd hpos k 0

/-- The odd convergents of a positive fraction converge (decreasing and
bounded below by the zeroth convergent). -/
-- no-dlmf: positive-fraction odd-convergent convergence (method-kit meta-lemma)
theorem exists_tendsto_convs_odd
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    ∃ L : ℝ, Tendsto (fun k => g.convs (2 * k + 1)) atTop (𝓝 L) := by
  refine ⟨⨅ k, g.convs (2 * k + 1), tendsto_atTop_ciInf (antitone_convs_odd hpos) ?_⟩
  refine ⟨g.convs 0, ?_⟩
  rintro y ⟨k, rfl⟩
  simpa using convs_even_le_odd hpos 0 k

/-- A sequence whose even- and odd-indexed subsequences tend to the same limit
tends to that limit. -/
-- no-dlmf: even/odd interleaving convergence criterion (general topology helper)
theorem tendsto_of_even_odd {X : Type*} [TopologicalSpace X] {f : ℕ → X} {L : X}
    (he : Tendsto (fun k => f (2 * k)) atTop (𝓝 L))
    (ho : Tendsto (fun k => f (2 * k + 1)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Filter.tendsto_def] at he ho ⊢
  intro s hs
  obtain ⟨N₁, hN₁⟩ := Filter.mem_atTop_sets.mp (he s hs)
  obtain ⟨N₂, hN₂⟩ := Filter.mem_atTop_sets.mp (ho s hs)
  rw [Filter.mem_atTop_sets]
  refine ⟨2 * max N₁ N₂ + 1, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h := hN₁ k (by omega)
    simp only [Set.mem_preimage] at h ⊢
    rwa [two_mul] at h
  · subst hk
    have h := hN₂ k (by omega)
    simp only [Set.mem_preimage] at h ⊢
    exact h

/-- **Convergence criterion for positive fractions** (the even/odd half of the
Stieltjes theory): a positive fraction whose consecutive-convergent gap tends
to `0` has convergent convergents.  The remaining content of the classical
Stieltjes theorem is precisely the gap estimate
`∏_{i ≤ n} aᵢ / (Bₙ Bₙ₊₁) → 0`. -/
-- no-dlmf: positive-fraction convergence criterion (method-kit meta-lemma)
theorem exists_tendsto_convs_of_gap_tendsto_zero
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (hgap : Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto g.convs atTop (𝓝 L) := by
  obtain ⟨Le, hLe⟩ := exists_tendsto_convs_even hpos
  obtain ⟨Lo, hLo⟩ := exists_tendsto_convs_odd hpos
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have hsub0 : Tendsto (fun k => g.convs (2 * k + 1) - g.convs (2 * k)) atTop (𝓝 0) := by
    have := hgap.comp h2k
    simpa [Function.comp] using this
  have hsub : Tendsto (fun k => g.convs (2 * k + 1) - g.convs (2 * k)) atTop
      (𝓝 (Lo - Le)) := hLo.sub hLe
  have hLoLe : Lo = Le := sub_eq_zero.mp (tendsto_nhds_unique hsub hsub0)
  exact ⟨Le, tendsto_of_even_odd hLe (hLoLe ▸ hLo)⟩

/-! ### Exact tails: identification of the limit (Stieltjes sandwich)

A sequence `t : ℕ → ℝ` of **exact tails** for `g` satisfies the backwards
recurrence `t n = aₙ₊₁ / (bₙ₊₁ + t (n+1))`, so that formally
`h + t 0 = h + a₁/(b₁ + a₂/(b₂ + ⋯))` *is* the value of the fraction.  The
classical linear-fractional identity `w (Bₙ + tₙ Bₙ₋₁) = Aₙ + tₙ Aₙ₋₁`
(`tail_linearFractional`) shows that `w = h + t 0` is sandwiched between
consecutive convergents; combined with a vanishing convergent gap this
*identifies* the limit of the convergents as `w`
(`tendsto_convs_of_tails`). -/

/-- The `b`-continuants `(contsAux n).b` of a positive fraction are nonnegative
(`B₋₁ = 0`, and `Bₙ > 0` thereafter). -/
-- no-dlmf: positive-fraction continuant nonnegativity (`contsAux` level)
theorem contsAux_b_nonneg
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b) :
    ∀ n, 0 ≤ (g.contsAux n).b := by
  intro n
  cases n with
  | zero => simp [GenContFract.zeroth_contAux_eq_one_zero]
  | succ m =>
    have h := dens_pos hpos m
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux] at h
    exact h.le

/-- **The exact-tail linear-fractional identity** (the crux of the Stieltjes
sandwich): if `t` is a sequence of positive exact tails for `g` — i.e.
`t n = aₙ₊₁ / (bₙ₊₁ + t (n+1))` for every `n` — then the value `w = h + t 0`
satisfies `w (Bₙ + tₙ Bₙ₋₁) = Aₙ + tₙ Aₙ₋₁` for every `n`.  Proof: induction
on `n` through the Wallis recurrence for `contsAux`. -/
-- no-dlmf: exact-tail linear-fractional identity (method-kit meta-lemma)
theorem tail_linearFractional {t : ℕ → ℝ}
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (htpos : ∀ n, 0 < t n)
    (htail : ∀ n, ∃ gp, g.s.get? n = some gp ∧ t n = gp.a / (gp.b + t (n + 1))) :
    ∀ n, (g.h + t 0) * ((g.contsAux (n + 1)).b + t n * (g.contsAux n).b) =
      (g.contsAux (n + 1)).a + t n * (g.contsAux n).a := by
  intro n
  induction n with
  | zero =>
    simp [GenContFract.zeroth_contAux_eq_one_zero, GenContFract.first_contAux_eq_h_one]
  | succ n ih =>
    obtain ⟨gp, hgp, htn⟩ := htail n
    have hb : 0 < gp.b := (hpos n gp hgp).2
    have hden : (0 : ℝ) < gp.b + t (n + 1) := by linarith [htpos (n + 1)]
    have htn' : t n * (gp.b + t (n + 1)) = gp.a := by
      rw [htn, div_mul_cancel₀ _ hden.ne']
    rw [GenContFract.contsAux_recurrence hgp rfl rfl]
    dsimp only
    linear_combination (gp.b + t (n + 1)) * ih +
      ((g.contsAux n).a - (g.h + t 0) * (g.contsAux n).b) * htn'

/-- Signed distance from the exact-tail value to the `n`-th convergent:
`(w − fₙ) · Bₙ (Bₙ + tₙ Bₙ₋₁) = tₙ (−1)ⁿ ∏_{i < n} aᵢ`.  In particular the
sign of `w − fₙ` is `(−1)ⁿ`: the value is sandwiched between consecutive
convergents. -/
-- no-dlmf: exact-tail sandwich, signed-distance form
theorem sub_convs_mul_of_tails {t : ℕ → ℝ}
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (htpos : ∀ n, 0 < t n)
    (htail : ∀ n, ∃ gp, g.s.get? n = some gp ∧ t n = gp.a / (gp.b + t (n + 1)))
    (n : ℕ) :
    ((g.h + t 0) - g.convs n) * (g.dens n * (g.dens n + t n * (g.contsAux n).b)) =
      t n * ((-1) ^ n * partNumProd g n) := by
  have hcrux := tail_linearFractional hpos htpos htail n
  have hdet := contsAux_determinant (g := g) n
  have hBpos := dens_pos hpos n
  have hc : g.convs n * g.dens n = g.nums n := by
    rw [GenContFract.conv_eq_num_div_den, div_mul_cancel₀ _ hBpos.ne']
  have hden : g.dens n = (g.contsAux (n + 1)).b := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  have hnum : g.nums n = (g.contsAux (n + 1)).a := by
    rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [hden] at hc ⊢
  rw [hnum] at hc
  linear_combination (g.contsAux (n + 1)).b * hcrux + t n * hdet -
    ((g.contsAux (n + 1)).b + t n * (g.contsAux n).b) * hc

/-- Even convergents lie below the exact-tail value. -/
-- no-dlmf: exact-tail sandwich, even half
theorem convs_even_le_of_tails {t : ℕ → ℝ}
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (htpos : ∀ n, 0 < t n)
    (htail : ∀ n, ∃ gp, g.s.get? n = some gp ∧ t n = gp.a / (gp.b + t (n + 1)))
    (k : ℕ) : g.convs (2 * k) ≤ g.h + t 0 := by
  have hsign := sub_convs_mul_of_tails hpos htpos htail (2 * k)
  have hp : ((-1 : ℝ)) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, two_mul k⟩
  rw [hp, one_mul] at hsign
  have hD : 0 < g.dens (2 * k) * (g.dens (2 * k) + t (2 * k) * (g.contsAux (2 * k)).b) := by
    have h1 := dens_pos hpos (2 * k)
    have h2 := contsAux_b_nonneg hpos (2 * k)
    have h3 := htpos (2 * k)
    have : 0 < g.dens (2 * k) + t (2 * k) * (g.contsAux (2 * k)).b := by nlinarith
    exact mul_pos h1 this
  have hRHS : 0 ≤ t (2 * k) * partNumProd g (2 * k) :=
    mul_nonneg (htpos (2 * k)).le (partNumProd_nonneg hpos (2 * k))
  nlinarith [hsign, hD, hRHS]

/-- Odd convergents lie above the exact-tail value. -/
-- no-dlmf: exact-tail sandwich, odd half
theorem le_convs_odd_of_tails {t : ℕ → ℝ}
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (htpos : ∀ n, 0 < t n)
    (htail : ∀ n, ∃ gp, g.s.get? n = some gp ∧ t n = gp.a / (gp.b + t (n + 1)))
    (k : ℕ) : g.h + t 0 ≤ g.convs (2 * k + 1) := by
  have hsign := sub_convs_mul_of_tails hpos htpos htail (2 * k + 1)
  have hp : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  rw [hp] at hsign
  have hD : 0 < g.dens (2 * k + 1) *
      (g.dens (2 * k + 1) + t (2 * k + 1) * (g.contsAux (2 * k + 1)).b) := by
    have h1 := dens_pos hpos (2 * k + 1)
    have h2 := contsAux_b_nonneg hpos (2 * k + 1)
    have h3 := htpos (2 * k + 1)
    have : 0 < g.dens (2 * k + 1) + t (2 * k + 1) * (g.contsAux (2 * k + 1)).b := by nlinarith
    exact mul_pos h1 this
  have hRHS : 0 ≤ t (2 * k + 1) * partNumProd g (2 * k + 1) :=
    mul_nonneg (htpos (2 * k + 1)).le (partNumProd_nonneg hpos (2 * k + 1))
  nlinarith [hsign, hD, hRHS]

/-- **Exact tails identify the limit of a positive continued fraction**
(the Stieltjes sandwich, method-kit meta-lemma): if a positive fraction `g`
admits a sequence of positive exact tails `t` (`t n = aₙ₊₁/(bₙ₊₁ + t (n+1))`)
and its convergent gap tends to `0`, then the convergents converge to
`g.h + t 0`.  This upgrades `exists_tendsto_convs_of_gap_tendsto_zero` from
mere convergence to an identification of the limit. -/
-- no-dlmf: exact-tail limit identification (method-kit meta-lemma)
theorem tendsto_convs_of_tails {t : ℕ → ℝ}
    (hpos : ∀ n gp, g.s.get? n = some gp → 0 < gp.a ∧ 0 < gp.b)
    (htpos : ∀ n, 0 < t n)
    (htail : ∀ n, ∃ gp, g.s.get? n = some gp ∧ t n = gp.a / (gp.b + t (n + 1)))
    (hgap : Tendsto (fun n => g.convs (n + 1) - g.convs n) atTop (𝓝 0)) :
    Tendsto g.convs atTop (𝓝 (g.h + t 0)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_convs_of_gap_tendsto_zero hpos hgap
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have h2k1 : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩
  have heven : Tendsto (fun k => g.convs (2 * k)) atTop (𝓝 L) := hL.comp h2k
  have hodd : Tendsto (fun k => g.convs (2 * k + 1)) atTop (𝓝 L) := hL.comp h2k1
  have h1 : L ≤ g.h + t 0 :=
    le_of_tendsto heven
      (Eventually.of_forall fun k => convs_even_le_of_tails hpos htpos htail k)
  have h2 : g.h + t 0 ≤ L :=
    ge_of_tendsto hodd
      (Eventually.of_forall fun k => le_convs_odd_of_tails hpos htpos htail k)
  exact le_antisymm h1 h2 ▸ hL

end Positive

end FLMF.Methods
