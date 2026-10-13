import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Generalized hypergeometric `pFq` (framework — DLMF §16.2)

`pFq(a₁..aₚ; b₁..b_q; z) = ∑ (a₁)ₙ⋯(aₚ)ₙ / ((b₁)ₙ⋯(b_q)ₙ) · zⁿ/n!`
(DLMF 16.2.1), with parameter tuples `Fin p → 𝕂` / `Fin q → 𝕂`, as an
`ofScalars` series in the style of Mathlib's `OrdinaryHypergeometric` (`₂F₁`)
and FLMF's `Kummer` (`₁F₁`), both of which it generalizes (as does `₀F₁`, the
Bessel/Airy parent, and `₁F₂`, the Struve parent).

Main results — the DLMF 16.2(ii)–(iv) convergence trichotomy:

* `pFqSeries_radius_eq_top` — `p ≤ q`: **entire, for all parameters**
  (ratio test generically; the series terminates at nonpositive-integer
  parameters).
* `pFqSeries_radius_eq_one` — `p = q + 1`: radius of convergence `1`, for
  parameters off the nonpositive integers.
* `pFqSeries_radius_eq_zero` — `p ≥ q + 2`: radius `0` (the series is a
  formal/asymptotic object only), for parameters off the nonpositive integers.

All three reduce to one limit (`tendsto_prod_pad_div`): pad the numerator tuple
with trivial factors to the denominator's length `m`, so the term ratio is a
product of `m` factors `(aᵢ+n)/(bᵢ+n) → 1` or `1/(bᵢ+n) → 0`.

The Mellin–Barnes representation, contiguous relations, and the `p+1 ≤ q+1`
parameter-shift calculus are downstream nodes (`F-pFq-mellin-barnes`, etc.).
-/

open Nat FormalMultilinearSeries

namespace FLMF.Hypergeometric

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸] {p q : ℕ}

/-- The coefficients `(a₁)ₙ⋯(aₚ)ₙ / ((b₁)ₙ⋯(b_q)ₙ n!)` of the generalized
hypergeometric series (DLMF 16.2.1). -/
noncomputable abbrev pFqCoefficient (A : Fin p → 𝕂) (B : Fin q → 𝕂) (n : ℕ) : 𝕂 :=
  (n !⁻¹ : 𝕂) * (∏ i, (ascPochhammer 𝕂 n).eval (A i)) *
    (∏ j, (ascPochhammer 𝕂 n).eval (B j))⁻¹

/-- `pFqSeries 𝔸 A B` is the generalized hypergeometric series as a
`FormalMultilinearSeries` (DLMF 16.2.1). Its sum is `pFq`. -/
noncomputable def pFqSeries (A : Fin p → 𝕂) (B : Fin q → 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (pFqCoefficient A B)

variable {𝔸} (A : Fin p → 𝕂) (B : Fin q → 𝕂)

/-- The generalized hypergeometric function `pFq(a;b;x)` (DLMF 16.2.1), the sum
of `pFqSeries` — junk value `0` outside the radius of convergence
(see the radius trichotomy `pFqSeries_radius_eq_top/_one/_zero`). -/
-- DAG: E-16.2.1.
-- Verified: unverified (tier2 DIVERGES)
noncomputable def pFq (x : 𝔸) : 𝔸 :=
  (pFqSeries 𝔸 A B).sum x

-- no-dlmf: termwise evaluation of the series, no DLMF counterpart
theorem pFqSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (pFqSeries 𝔸 A B n fun _ => x) = pFqCoefficient A B n • x ^ n := by
  rw [pFqSeries, ofScalars_apply_eq]

-- no-dlmf: strictly-more-general form over an abstract `Field` `𝕂` and
-- topological `𝕂`-algebra `𝔸`; DLMF's parameter tuples `a,b` are real or
-- complex and its variable `z` is complex; faithful surface is
-- `pFq_eq_tsum_dlmf`
/-- The generalized hypergeometric function is, by definition, the series
`ₚFq(a;b;z) = ∑ₙ (a₁)ₙ⋯(aₚ)ₙ / ((b₁)ₙ⋯(b_q)ₙ) · zⁿ/n!`: unconditionally on the
parameter tuples `A`, `B` and the variable `x`. -/
theorem pFq_eq_tsum : pFq A B =
    fun (x : 𝔸) => ∑' n : ℕ, pFqCoefficient A B n • x ^ n :=
  funext fun x => tsum_congr fun n => pFqSeries_apply_eq A B x n

-- no-dlmf: unused-proviso restatement over the abstract `Field`/algebra
-- setting, feeding the DLMF-faithful `pFq_eq_tsum_dlmf`
/-- `pFq_eq_tsum`, restated with the §16.2(i) proviso that no bottom
parameter `B j` is a nonpositive integer (`pFq_eq_tsum` needs no such
hypothesis: junk-valued terms vanish harmlessly). -/
theorem pFq_eq_tsum_of_ne_neg_nat (_hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j) :
    pFq A B = fun (x : 𝔸) => ∑' n : ℕ, pFqCoefficient A B n • x ^ n :=
  pFq_eq_tsum A B

/-- **DLMF 16.2.1.** The generalized hypergeometric function is the series
`ₚFq(a;b;z) = ∑ₙ (a₁)ₙ⋯(aₚ)ₙ / ((b₁)ₙ⋯(b_q)ₙ) · zⁿ/n!`, for complex parameter
tuples `a,b` and complex variable `z`, with no bottom parameter `B j` a
nonpositive integer.

DAG: E-16.2.1.
Fidelity: tier1 unable (tier1-pending)
Verified: unverified
-/
theorem pFq_eq_tsum_dlmf {p q : ℕ} (A : Fin p → ℂ) (B : Fin q → ℂ)
    (hB : ∀ j (kn : ℕ), (kn : ℂ) ≠ -B j) :
    pFq (𝔸 := ℂ) A B = fun (x : ℂ) => ∑' n : ℕ, pFqCoefficient A B n • x ^ n :=
  pFq_eq_tsum_of_ne_neg_nat (𝔸 := ℂ) A B hB

-- no-dlmf: evaluation at 0 helper, no DLMF counterpart
theorem pFqSeries_apply_zero (n : ℕ) :
    (pFqSeries 𝔸 A B n fun _ => 0) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [pFqSeries, ofScalars_apply_eq]
  cases n <;> simp [pFqCoefficient]

/-- `pFq(a;b;0) = 1`. -/
-- no-dlmf: trivial base value, no DLMF equation number
@[simp]
theorem pFq_zero : pFq A B (0 : 𝔸) = 1 := by
  simp [pFq_eq_tsum, ← pFqSeries_apply_eq, pFqSeries_apply_zero]

-- no-dlmf: per-term vanishing helper for pFqSeries_radius_eq_top; the termination fact is §16.2(iii)/(iv) prose, no numbered DLMF equation (the B j disjunct is a Lean junk-convention artifact)
/-- If any parameter (numerator or denominator) is the nonpositive integer
`-k`, every series term beyond `k` vanishes: numerator parameters terminate the
series, matching the unnumbered §16.2(iii)/(iv) termination prose ("the series
terminates and the generalized hypergeometric function is a polynomial in z"),
denominator parameters kill the junk-valued tail. -/
lemma pFqSeries_eq_zero_of_neg_nat {n k : ℕ}
    (hab : (∃ i, (k : 𝕂) = -A i) ∨ ∃ j, (k : 𝕂) = -B j) (hk : k < n) :
    pFqSeries 𝔸 A B n = 0 := by
  rw [pFqSeries, ofScalars]
  rcases hab with ⟨i, h⟩ | ⟨j, h⟩
  · ext
    have h0 : (∏ i, (ascPochhammer 𝕂 n).eval (A i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i)
        ((ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩)
    simp [h0]
  · ext
    have h0 : (∏ j, (ascPochhammer 𝕂 n).eval (B j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j)
        ((ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩)
    simp [h0]

end Field

section RCLike

open Asymptotics Filter Real Set Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  {p q : ℕ}

/-- Padding a `Fin p`-indexed product with trivial factors up to length `m`. -/
-- no-dlmf: finite-product padding helper, no DLMF counterpart
private lemma prod_pad {m : ℕ} (hpm : p ≤ m) (f : Fin p → 𝕂) :
    (∏ i, f i) = ∏ i : Fin m, (if h : (i : ℕ) < p then f ⟨i, h⟩ else 1) := by
  have h1 : (∏ i, f i) =
      ∏ i ∈ Finset.range p, (if h : i < p then f ⟨i, h⟩ else 1) := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun i _ => by simp [i.isLt]
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if h : i < p then f ⟨i, h⟩ else 1) m]
  exact Finset.prod_subset
    (fun x hx => Finset.mem_range.2 ((Finset.mem_range.1 hx).trans_le hpm))
    (fun x _ hx => dif_neg (by simpa using hx))

/-- The master ratio limit: for a numerator tuple of length `p ≤ m` and a
denominator tuple of length `m`,
`∏ᵢ(Aᵢ+n) / ∏ᵢ(Gᵢ+n) → 1` if `p = m` and `→ 0` if `p < m`. -/
-- no-dlmf: ratio-limit infrastructure for the radius trichotomy, no DLMF counterpart
private lemma tendsto_prod_pad_div {m : ℕ} (hpm : p ≤ m) (A : Fin p → 𝕂) (G : Fin m → 𝕂) :
    Tendsto (fun n : ℕ => (∏ i, (A i + n)) / ∏ i, (G i + n)) atTop
      (𝓝 (if p = m then 1 else 0)) := by
  have key : ∀ n : ℕ, (∏ i, (A i + (n : 𝕂))) / (∏ i, (G i + n)) =
      ∏ i : Fin m, (if h : (i : ℕ) < p then A ⟨i, h⟩ + n else 1) / (G i + n) := by
    intro n
    rw [prod_pad hpm (fun i => A i + (n : 𝕂)), ← Finset.prod_div_distrib]
  simp_rw [key]
  have lim : ∀ i : Fin m,
      Tendsto (fun n : ℕ => (if h : (i : ℕ) < p then A ⟨i, h⟩ + n else 1) / (G i + n))
        atTop (𝓝 (if (i : ℕ) < p then 1 else 0)) := by
    intro i
    by_cases h : (i : ℕ) < p
    · simpa [h] using tendsto_add_mul_div_add_mul_atTop_nhds (A ⟨i, h⟩) (G i) (1 : 𝕂) one_ne_zero
    · simpa [h] using tendsto_add_mul_div_add_mul_atTop_nhds (1 : 𝕂) (G i) (0 : 𝕂) one_ne_zero
  have hval : (∏ i : Fin m, if (i : ℕ) < p then (1 : 𝕂) else 0) = if p = m then 1 else 0 := by
    by_cases hpm' : p = m
    · subst hpm'
      simp
    · rw [if_neg hpm']
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨p, lt_of_le_of_ne hpm hpm'⟩) (by simp)
  simpa [hval] using tendsto_finsetProd Finset.univ fun i _ => lim i

variable (A : Fin p → 𝕂) (B : Fin q → 𝕂)

/-- The extended denominator tuple `(b₁, …, b_q, 1)`: appending the `n!` slot
as the parameter `1` turns the denominator of the term ratio into a product of
`q+1` uniform factors. -/
-- no-dlmf: denominator-tuple extension helper, no DLMF counterpart
private lemma prod_snoc_one (n : ℕ) :
    (∏ i : Fin (q + 1), ((Fin.snoc B 1 : Fin (q + 1) → 𝕂) i + n)) = (∏ j, (B j + n)) * (1 + n) := by
  rw [Fin.prod_univ_castSucc]
  simp

-- no-dlmf: a derived term-ratio identity for pFqCoefficient, restricted to
-- parameters off the nonpositive integers; not DLMF 16.2.1 itself (which
-- defines ₚFq(a;b;z) as the full series in z, unconditionally on a). The
-- faithful full-strength surface of 16.2.1 is `pFq_eq_tsum`.
/-- The term ratio of the generalized hypergeometric series:
`cₙ₊₁/cₙ = ∏ᵢ(aᵢ+n) / (∏ⱼ(bⱼ+n) · (1+n))`, for parameters off the nonpositive
integers. Internal infrastructure for the convergence trichotomy, not itself
DLMF 16.2.1 (which defines ₚFq as the series `pFq_eq_tsum` states). -/
theorem pFqCoefficient_succ_div (n : ℕ)
    (hA : ∀ i (kn : ℕ), (kn : 𝕂) ≠ -A i) (hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j) :
    pFqCoefficient A B n.succ / pFqCoefficient A B n
      = (∏ i, (A i + n)) / ((∏ j, (B j + n)) * (1 + (n : 𝕂))) := by
  have hPA : (∏ i, (ascPochhammer 𝕂 n).eval (A i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn _ => hA i kn
  have hPB : (∏ j, (ascPochhammer 𝕂 n).eval (B j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn _ => hB j kn
  have hQB : (∏ j, (B j + (n : 𝕂))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => fun h => hB j n (by linear_combination h)
  have hfac : ((n ! : ℕ) : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hn1 : (1 : 𝕂) + (n : 𝕂) ≠ 0 := by
    have := Nat.cast_add_one_ne_zero (R := 𝕂) n
    intro h; exact this (by linear_combination h)
  simp only [pFqCoefficient, factorial_succ, ascPochhammer_succ_eval, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Finset.prod_mul_distrib]
  field_simp
  ring

-- no-dlmf: entire for ALL parameters — a Lean-total superset of §16.2(ii); the
-- degenerate-denominator case (where DLMF leaves ₚFq undefined) holds only by the
-- `1/0 = 0` junk convention. Faithful surface: `pFqSeries_radius_eq_top_of_ne_neg_nat`.
/-- For `p ≤ q` the `ₚFq` formal series is entire (radius `⊤`) for ALL parameters —
ratio test generically, termination in the degenerate cases.  Reused downstream
(`pFq_hasSum`); the DLMF-faithful restriction is
`pFqSeries_radius_eq_top_of_ne_neg_nat`. -/
theorem pFqSeries_radius_eq_top (hpq : p ≤ q) : (pFqSeries 𝔸 A B).radius = ⊤ := by
  by_cases hab : ∃ k : ℕ, (∃ i, (k : 𝕂) = -A i) ∨ ∃ j, (k : 𝕂) = -B j
  · obtain ⟨k, hk⟩ := hab
    refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
    exact pFqSeries_eq_zero_of_neg_nat A B hk (by lia)
  · push Not at hab
    have hA : ∀ i (kn : ℕ), (kn : 𝕂) ≠ -A i := fun i kn => (hab kn).1 i
    have hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j := fun j kn => (hab kn).2 j
    have hne : ∀ n, pFqCoefficient A B n ≠ 0 := fun n =>
      mul_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero))
        (Finset.prod_ne_zero_iff.2 fun i _ => by
          rw [Ne, ascPochhammer_eval_eq_zero_iff]
          push Not
          exact fun kn _ => hA i kn))
        (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => by
          rw [Ne, ascPochhammer_eval_eq_zero_iff]
          push Not
          exact fun kn _ => hB j kn))
    refine ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall hne) ?_
    have hratio : (fun n : ℕ ↦ ‖pFqCoefficient A B n.succ‖ / ‖pFqCoefficient A B n‖)
        = fun n : ℕ ↦ ‖(∏ i, (A i + n)) / ∏ i : Fin (q + 1), ((Fin.snoc B 1 : Fin (q + 1) → 𝕂) i + n)‖ := by
      funext n
      rw [← norm_div, pFqCoefficient_succ_div A B n hA hB, prod_snoc_one]
    rw [hratio]
    have := tendsto_prod_pad_div (Nat.le_succ_of_le hpq) A (Fin.snoc B (1 : 𝕂))
    rw [if_neg (by lia)] at this
    simpa using this.norm

-- no-dlmf: strictly-more-general form over an abstract `RCLike` field `𝕂` and a
-- `NormedDivisionRing`/`NormedAlgebra` target `𝔸`; the faithful DLMF 16.2(ii)
-- surface (complex parameters, complex variable) is
-- `pFqSeries_radius_eq_top_of_ne_neg_nat_dlmf`.
/-- For `p ≤ q` the `ₚFq` series is entire (radius `⊤`), under the §16.2(i)
proviso that no bottom parameter `B j` is a nonpositive integer (so `ₚFq` is
defined; top parameters may be nonpositive, terminating the series to a
polynomial, which is still entire).  Faithful restriction of the unconditional
`pFqSeries_radius_eq_top`. -/
theorem pFqSeries_radius_eq_top_of_ne_neg_nat (hpq : p ≤ q)
    (_hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j) : (pFqSeries 𝔸 A B).radius = ⊤ :=
  pFqSeries_radius_eq_top 𝔸 A B hpq

/-- **DLMF 16.2(ii)**: for complex parameters `a₁,…,aₚ`, `b₁,…,b_q` with `p ≤ q`
and no bottom parameter a nonpositive integer, the `ₚFq` series in the complex
variable `z` is entire (radius `⊤`) (DLMF-faithful restriction of
`pFqSeries_radius_eq_top_of_ne_neg_nat`).

DAG: E-16.2.
Fidelity: tier1 unable (tier1-pending)
Verified: verified (tier2)
-/
theorem pFqSeries_radius_eq_top_of_ne_neg_nat_dlmf {p q : ℕ} (A : Fin p → ℂ) (B : Fin q → ℂ)
    (hpq : p ≤ q) (hB : ∀ j (kn : ℕ), (kn : ℂ) ≠ -B j) :
    (pFqSeries ℂ A B).radius = ⊤ :=
  pFqSeries_radius_eq_top_of_ne_neg_nat (𝔸 := ℂ) (A := A) (B := B) hpq hB

-- no-dlmf: strictly-more-general form over an abstract `RCLike` field `𝕂` and a
-- `NormedDivisionRing`/`NormedAlgebra` target `𝔸`; the faithful DLMF 16.2(iii)
-- surface (complex parameters, complex variable) is `pFqSeries_radius_eq_one_dlmf`.
/-- For `p = q + 1` the radius of convergence of the `ₚFq` series is `1`, for
parameters off the nonpositive integers. -/
theorem pFqSeries_radius_eq_one (A : Fin (q + 1) → 𝕂)
    (hA : ∀ i (kn : ℕ), (kn : 𝕂) ≠ -A i) (hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j) :
    (pFqSeries 𝔸 A B).radius = 1 := by
  convert! ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero ?_
  have hne : ∀ n, pFqCoefficient A B n ≠ 0 := fun n =>
    mul_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero))
      (Finset.prod_ne_zero_iff.2 fun i _ => by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => hA i kn))
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => hB j kn))
  have hratio : (fun n : ℕ ↦ ‖pFqCoefficient A B n‖ / ‖pFqCoefficient A B n.succ‖)
      = fun n : ℕ ↦ ‖(∏ i : Fin (q + 1), ((Fin.snoc B 1 : Fin (q + 1) → 𝕂) i + n)) / ∏ i, (A i + n)‖ := by
    funext n
    rw [← norm_div, ← inv_div (pFqCoefficient A B n.succ) (pFqCoefficient A B n),
      pFqCoefficient_succ_div A B n hA hB, prod_snoc_one, inv_div]
  rw [hratio]
  have := tendsto_prod_pad_div le_rfl (Fin.snoc B (1 : 𝕂)) A
  rw [if_pos rfl] at this
  simpa using this.norm

/-- **DLMF 16.2(iii)**: for complex parameters `a₁,…,a_{q+1}`, `b₁,…,b_q` off
the nonpositive integers, the radius of convergence of the `_{q+1}F_q` series
in the complex variable `z` is `1` (DLMF-faithful restriction of
`pFqSeries_radius_eq_one`).

DAG: E-16.2.
Fidelity: tier1 unable (tier1-pending)
Verified: verified (tier2)
-/
theorem pFqSeries_radius_eq_one_dlmf {q : ℕ} (A : Fin (q + 1) → ℂ) (B : Fin q → ℂ)
    (hA : ∀ i (kn : ℕ), (kn : ℂ) ≠ -A i) (hB : ∀ j (kn : ℕ), (kn : ℂ) ≠ -B j) :
    (pFqSeries ℂ A B).radius = 1 :=
  pFqSeries_radius_eq_one (𝔸 := ℂ) (A := A) (B := B) hA hB

-- no-dlmf: strictly-more-general form over an abstract `RCLike` field `𝕂` and a
-- `NormedDivisionRing`/`NormedAlgebra` target `𝔸`; the faithful DLMF 16.2(iv)
-- surface (complex parameters, complex variable) is `pFqSeries_radius_eq_zero_dlmf`.
/-- For `p ≥ q + 2` the radius of convergence of the `ₚFq` series is `0` (the
series is a formal/asymptotic object only), for parameters off the nonpositive
integers. -/
theorem pFqSeries_radius_eq_zero (hqp : q + 1 < p)
    (hA : ∀ i (kn : ℕ), (kn : 𝕂) ≠ -A i) (hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j) :
    (pFqSeries 𝔸 A B).radius = 0 := by
  refine ofScalars_radius_eq_zero_of_tendsto 𝔸 _ ?_
  have hne : ∀ n, pFqCoefficient A B n ≠ 0 := fun n =>
    mul_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero))
      (Finset.prod_ne_zero_iff.2 fun i _ => by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => hA i kn))
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => hB j kn))
  have hratio : (fun n : ℕ ↦ ‖pFqCoefficient A B n‖ / ‖pFqCoefficient A B n.succ‖)
      = fun n : ℕ ↦ ‖(∏ i : Fin (q + 1), ((Fin.snoc B 1 : Fin (q + 1) → 𝕂) i + n)) / ∏ i, (A i + n)‖ := by
    funext n
    rw [← norm_div, ← inv_div (pFqCoefficient A B n.succ) (pFqCoefficient A B n),
      pFqCoefficient_succ_div A B n hA hB, prod_snoc_one, inv_div]
  have hzero : Tendsto (fun n : ℕ ↦ ‖pFqCoefficient A B n‖ / ‖pFqCoefficient A B n.succ‖)
      atTop (𝓝 0) := by
    rw [hratio]
    have := tendsto_prod_pad_div (le_of_lt hqp) (Fin.snoc B (1 : 𝕂)) A
    rw [if_neg (by lia)] at this
    simpa using this.norm
  have hpos : ∀ n, 0 < ‖pFqCoefficient A B n‖ / ‖pFqCoefficient A B n.succ‖ := fun n =>
    div_pos (norm_pos_iff.2 (hne n)) (norm_pos_iff.2 (hne n.succ))
  have hinv : Tendsto (fun n : ℕ ↦ (‖pFqCoefficient A B n‖ / ‖pFqCoefficient A B n.succ‖)⁻¹)
      atTop atTop :=
    (tendsto_nhdsWithin_iff.2 ⟨hzero, Eventually.of_forall fun n => hpos n⟩).inv_tendsto_nhdsGT_zero
  refine hinv.congr fun n => ?_
  rw [inv_div]

/-- **DLMF 16.2(iv)**: for complex parameters `a₁,…,aₚ`, `b₁,…,b_q` with
`p ≥ q + 2` off the nonpositive integers, the radius of convergence of the
`ₚFq` series in the complex variable `z` is `0` (DLMF-faithful restriction of
`pFqSeries_radius_eq_zero`).

DAG: E-16.2.
Fidelity: tier1 unable (tier1-pending)
Verified: verified (tier2)
-/
theorem pFqSeries_radius_eq_zero_dlmf {p q : ℕ} (A : Fin p → ℂ) (B : Fin q → ℂ)
    (hqp : q + 1 < p) (hA : ∀ i (kn : ℕ), (kn : ℂ) ≠ -A i)
    (hB : ∀ j (kn : ℕ), (kn : ℂ) ≠ -B j) :
    (pFqSeries ℂ A B).radius = 0 :=
  pFqSeries_radius_eq_zero (𝔸 := ℂ) (A := A) (B := B) hqp hA hB

-- no-dlmf: strictly-more-general total form (quantifies over all `B j`, with
-- no pole-avoidance on the bottom parameters); the faithful DLMF 16.2 surface
-- is `pFq_hasSum_dlmf`.
/-- `HasSum` form of the `pFq` series at every point of the scalar field, in
the everywhere-convergent regime `p ≤ q`. -/
theorem pFq_hasSum (hpq : p ≤ q) (x : 𝕂) :
    HasSum (fun n : ℕ => pFqCoefficient A B n * x ^ n) (pFq A B x) := by
  have h := (pFqSeries 𝕂 A B).hasSum (x := x)
    (by rw [pFqSeries_radius_eq_top 𝕂 A B hpq]; simp)
  simpa only [pFq, pFqSeries_apply_eq, smul_eq_mul] using h

-- no-dlmf: strictly-more-general form over an abstract `RCLike` field `𝕂`; the
-- faithful DLMF 16.2(ii) surface (complex parameters, complex variable) is
-- `pFq_hasSum_dlmf_complex`.
/-- `HasSum` form of the `pFq` series at every point of the scalar field, in
the everywhere-convergent regime `p ≤ q`, under the §16.2(i) proviso that no
bottom parameter `B j` is a nonpositive integer. -/
theorem pFq_hasSum_dlmf (hpq : p ≤ q) (_hB : ∀ j (kn : ℕ), (kn : 𝕂) ≠ -B j)
    (x : 𝕂) :
    HasSum (fun n : ℕ => pFqCoefficient A B n * x ^ n) (pFq A B x) :=
  pFq_hasSum A B hpq x

/-- **DLMF §16.2(ii)**: for complex parameters `a₁,…,aₚ`, `b₁,…,b_q` with
`p ≤ q` and no bottom parameter a nonpositive integer, the `HasSum` form of the
`pFq` series holds at every complex point `z` (DLMF-faithful restriction of
`pFq_hasSum_dlmf`).

DAG: E-16.2.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem pFq_hasSum_dlmf_complex {p q : ℕ} (A : Fin p → ℂ) (B : Fin q → ℂ)
    (hpq : p ≤ q) (hB : ∀ j (kn : ℕ), (kn : ℂ) ≠ -B j) (x : ℂ) :
    HasSum (fun n : ℕ => pFqCoefficient A B n * x ^ n) (pFq A B x) :=
  pFq_hasSum_dlmf (A := A) (B := B) hpq hB x

end RCLike

section OfReal

/-! ### `ℝ → ℂ` cast bridge

Scalar-tower cast infrastructure: in the everywhere-convergent regime `p ≤ q`
the `pFq` sum commutes with the `ℝ → ℂ` cast, letting the Functions layer
identify real special-function instances with the complex comparison functions
of the Frameworks layer (e.g. `complexModifiedBesselI`). -/

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart (private copy;
-- the public sibling `ascPochhammer_eval_ofReal` lives downstream in
-- `GaussConnection` and cannot be imported here)
/-- `ascPochhammer` evaluation commutes with the `ℝ → ℂ` cast. -/
private lemma ascPochhammer_eval_ofReal' (x : ℝ) (n : ℕ) :
    (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (x : ℂ) := by
  have h : ((ascPochhammer ℝ n).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) x)
      = (algebraMap ℝ ℂ) ((ascPochhammer ℝ n).eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [ascPochhammer_map] at h
  simpa using h.symm

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart
/-- The `pFq` coefficients commute with the `ℝ → ℂ` cast. -/
theorem pFqCoefficient_ofReal {p q : ℕ} (A : Fin p → ℝ) (B : Fin q → ℝ) (n : ℕ) :
    ((pFqCoefficient A B n : ℝ) : ℂ) = pFqCoefficient ((↑) ∘ A) ((↑) ∘ B) n := by
  simp only [pFqCoefficient, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_prod, ascPochhammer_eval_ofReal',
    Function.comp_apply]

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart
/-- In the everywhere-convergent regime `p ≤ q`, `pFq` at real parameters and a
real argument commutes with the `ℝ → ℂ` cast.  No pole-avoidance hypothesis on
the bottom parameters is needed: both sides are unconditional tsums of
termwise-equal, everywhere-summable series (in the degenerate bottom-parameter
cases both sides follow the same junk convention `0⁻¹ = 0`). -/
theorem pFq_ofReal {p q : ℕ} (hpq : p ≤ q) (A : Fin p → ℝ) (B : Fin q → ℝ) (x : ℝ) :
    ((pFq A B x : ℝ) : ℂ) = pFq ((↑) ∘ A : Fin p → ℂ) ((↑) ∘ B : Fin q → ℂ) (x : ℂ) := by
  have hR := pFq_hasSum A B hpq x
  have hC := pFq_hasSum ((↑) ∘ A : Fin p → ℂ) ((↑) ∘ B) hpq (x : ℂ)
  have hRC := Complex.hasSum_ofReal.mpr hR
  have he : (fun n : ℕ => ((pFqCoefficient A B n * x ^ n : ℝ) : ℂ))
      = fun n : ℕ => pFqCoefficient ((↑) ∘ A : Fin p → ℂ) ((↑) ∘ B) n * (x : ℂ) ^ n := by
    funext n
    rw [Complex.ofReal_mul, pFqCoefficient_ofReal, Complex.ofReal_pow]
  rw [he] at hRC
  exact hRC.unique hC

end OfReal

end FLMF.Hypergeometric
