import FLMF.Support.TsumAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Generating-function proof machinery (method kit, C3 Phase 0)

Shared infrastructure for generating-function arguments (DLMF §1.10, §18.12),
previously inlined per family.  Two sides:

## Analytic side (`HasSum` assembly)

A generating-function identity `∑ₙ aₙ tⁿ = G(t)` is typically proved by
expanding `G` as a product of elementary series, obtaining a summable family
over `ℕ × ℕ`, and *regrouping* by the total `t`-degree.  Two regroupings occur
in practice:

* **antidiagonal** (`n = k + l`) — the Cauchy-product shape.
  `hasSum_antidiagonal` is the `HasSum`-valued companion of
  `FLMF.Methods.tsum_antidiagonal` (which it does **not** duplicate: the `tsum`
  form needs only `Summable`, while the `HasSum` form is what family files
  consume directly).  `hasSum_cauchy_product` pre-composes it with Mathlib's
  `HasSum.mul` for the product-form family `f k · g l`.
* **strided degree** (`n = k + d·l`, e.g. `d = 2` for the Hermite EGF
  `exp(x t) · exp(-t²/2)`, where the second factor is a series in `t²`) —
  `hasSum_stride`, regrouping along the fibres of `(k, l) ↦ k + d·l` via the
  packaged equivalence `sigEquiv`.

## Formal side (coefficient comparison)

The GF ⇔ coefficient bridge for formal power series is Mathlib's
`PowerSeries.ext_iff`, re-surfaced here as `powerSeries_ext_iff` /
`powerSeries_mk_eq_mk_iff`: a generating-function identity in `R⟦X⟧` is
*the same thing* as the family of per-coefficient identities.  The working
pattern (cf. Mathlib's `Combinatorics.Enumerative.Catalan` and the Bernoulli
EGF in `NumberTheory.Bernoulli`):

1. package the sequence as `PowerSeries.mk a`;
2. prove the GF-level identity algebraically — a functional equation, an ODE
   in coefficient form (cf. `FLMF.OP.hermiteGF_recurrence`), or a product
   identity via `PowerSeries.coeff_mul` (whose right-hand side is exactly an
   antidiagonal sum, the formal twin of `hasSum_antidiagonal`);
3. transport back per-coefficient through `powerSeries_mk_eq_mk_iff`.

The formal↔analytic transport lemma (formal identity + radius ⟹ pointwise
`HasSum`) is **out of scope** here — it is C3 Phase 1.
-/

namespace FLMF.Methods

open Finset

/-! ### Strided-degree regrouping (`n = k + d·l`) -/

-- no-dlmf: index-regrouping equivalence, summation infra
/-- The strided-degree regrouping equivalence: for a stride `d > 0`, the pairs
`(k, l) : ℕ × ℕ` are re-indexed by the total degree `n = k + d·l` together with
the fibre coordinate `l ≤ n/d`, packaged as `Fin (n/d + 1)` so each fibre is a
`Fintype`.  Forward map: `⟨n, l⟩ ↦ (n - d·l, l)`.

`d = 2` is the Hermite-EGF case (`exp(x t) · exp(-t²/2)`, second factor a
series in `t²`); `d = 1` recovers the antidiagonal. -/
def sigEquiv (d : ℕ) (hd : 0 < d) : (Σ n : ℕ, Fin (n / d + 1)) ≃ ℕ × ℕ where
  toFun := fun ⟨n, l⟩ => (n - d * l.1, l.1)
  invFun := fun kl => ⟨kl.1 + d * kl.2,
    ⟨kl.2, Nat.lt_succ_of_le
      (le_trans (le_of_eq (Nat.mul_div_cancel_left kl.2 hd).symm)
        (Nat.div_le_div_right (Nat.le_add_left _ _)))⟩⟩
  left_inv := by
    rintro ⟨n, l, hl⟩
    have hdl : d * l ≤ n := by
      have h1 : l * d ≤ n := (Nat.le_div_iff_mul_le hd).mp (Nat.lt_succ_iff.mp hl)
      rwa [mul_comm] at h1
    have hn : n - d * l + d * l = n := Nat.sub_add_cancel hdl
    have hbound : (n - d * l + d * l) / d + 1 = n / d + 1 := by rw [hn]
    simp only
    exact Sigma.ext hn ((Fin.heq_ext_iff hbound).mpr rfl)
  right_inv := by
    rintro ⟨k, l⟩
    simp only [Prod.mk.injEq, and_true]
    exact Nat.add_sub_cancel _ _

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T3Space M] [ContinuousAdd M]

-- no-dlmf: HasSum regrouping by strided degree, summation infra
/-- **Strided-degree regrouping of a `HasSum` family.**  If the two-index family
`f : ℕ × ℕ → M` sums to `S`, then so does the one-index family obtained by
summing each (finite) fibre of the degree map `(k, l) ↦ k + d·l`:

    ∑ₙ ( ∑_{l ≤ n/d} f (n - d·l, l) ) = S.

This is the assembly step of generating-function proofs where one factor is a
series in `t^d` (Hermite EGF: `d = 2`). -/
theorem hasSum_stride (d : ℕ) (hd : 0 < d) {f : ℕ × ℕ → M} {S : M} (hf : HasSum f S) :
    HasSum (fun n : ℕ => ∑ l ∈ Finset.range (n / d + 1), f (n - d * l, l)) S := by
  have hsig : HasSum (fun p : Σ n : ℕ, Fin (n / d + 1) => f (sigEquiv d hd p)) S :=
    (sigEquiv d hd).hasSum_iff.mpr hf
  refine hsig.sigma fun n => ?_
  have h : (∑ l : Fin (n / d + 1), f (sigEquiv d hd ⟨n, l⟩))
      = ∑ l ∈ Finset.range (n / d + 1), f (n - d * l, l) := by
    rw [show (∑ l : Fin (n / d + 1), f (sigEquiv d hd ⟨n, l⟩))
          = ∑ l : Fin (n / d + 1), f (n - d * (l : ℕ), (l : ℕ)) from rfl,
      Fin.sum_univ_eq_sum_range (fun l => f (n - d * l, l))]
  rw [← h]
  exact hasSum_fintype _

/-! ### Antidiagonal regrouping (`n = k + l`, the Cauchy-product shape) -/

-- no-dlmf: HasSum-over-antidiagonal rearrangement, summation infra
/-- **Antidiagonal regrouping of a `HasSum` family** (the `HasSum` companion of
`FLMF.Methods.tsum_antidiagonal`).  If `F : ℕ × ℕ → M` sums to `S`, then the
antidiagonal sums `∑_{k+l=n} F (k, l)` sum (over `n`) to `S`.  Unlike Mathlib's
Cauchy-product lemmas this applies to *any* `HasSum` family, not only those of
product form `f k · g l` — the indices may be coupled. -/
theorem hasSum_antidiagonal {F : ℕ × ℕ → M} {S : M} (hF : HasSum F S) :
    HasSum (fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, F kl) S := by
  have hsig : HasSum (fun c : (n : ℕ) × ↥(Finset.antidiagonal n) =>
      F (Finset.sigmaAntidiagonalEquivProd c)) S :=
    (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr hF
  refine hsig.sigma fun n => ?_
  have h : ∑ c : ↥(Finset.antidiagonal n), F (c : ℕ × ℕ)
      = ∑ kl ∈ Finset.antidiagonal n, F kl :=
    Finset.sum_finset_coe F (Finset.antidiagonal n)
  rw [← h]
  exact hasSum_fintype _

-- no-dlmf: Cauchy-product HasSum assembly, summation infra
/-- **Cauchy product in generating-function shape.**  For absolutely convergent
series `∑ f = A` and `∑ g = B` in a complete normed ring, the coefficient
convolution sums to the product:

    ∑ₙ ( ∑_{k+l=n} f k · g l ) = A · B.

This is `HasSum.mul` followed by `hasSum_antidiagonal` — the standard step
turning a product of two GFs into the GF of the convolved coefficients. -/
theorem hasSum_cauchy_product {R : Type*} [NormedRing R] [CompleteSpace R]
    {f g : ℕ → R} {A B : R} (hf : HasSum f A) (hg : HasSum g B)
    (hf' : Summable fun n => ‖f n‖) (hg' : Summable fun n => ‖g n‖) :
    HasSum (fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) (A * B) :=
  hasSum_antidiagonal (hf.mul hg (summable_mul_of_summable_norm hf' hg'))

/-! ### Formal side: the GF ⇔ coefficient comparison bridge -/

-- no-dlmf: formal coefficient-comparison bridge (re-surfaces `PowerSeries.ext_iff`)
/-- **GF ⇔ coefficient comparison** (re-surfaced `PowerSeries.ext_iff`).
Two formal power series are equal iff all their coefficients agree: a
generating-function identity in `R⟦X⟧` *is* the family of per-coefficient
identities.  Prove the GF-level identity by algebra (functional equation,
coefficient-form ODE, `PowerSeries.coeff_mul` convolution — cf. Mathlib's
Catalan GF and `FLMF.OP.hermiteGF_recurrence`) and read the coefficient
identity off with this lemma. -/
theorem powerSeries_ext_iff {R : Type*} [Semiring R] {f g : PowerSeries R} :
    f = g ↔ ∀ n : ℕ, PowerSeries.coeff n f = PowerSeries.coeff n g :=
  PowerSeries.ext_iff

-- no-dlmf: formal coefficient-comparison bridge for mk-packaged sequences
/-- The coefficient-comparison bridge for sequences packaged with
`PowerSeries.mk`: `mk a = mk b ↔ ∀ n, a n = b n`.  This is the working form of
`powerSeries_ext_iff` when both sides of a GF identity are given by explicit
coefficient sequences. -/
theorem powerSeries_mk_eq_mk_iff {R : Type*} [Semiring R] {a b : ℕ → R} :
    PowerSeries.mk a = PowerSeries.mk b ↔ ∀ n : ℕ, a n = b n := by
  rw [powerSeries_ext_iff]
  exact forall_congr' fun n => by rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

end FLMF.Methods
