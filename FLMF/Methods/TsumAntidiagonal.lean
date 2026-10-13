import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Antidiagonal grouping of a summable `ℕ × ℕ` family (method kit)

`tsum_antidiagonal` re-sums an absolutely convergent doubly-indexed series over `ℕ × ℕ`
by its antidiagonals `n = k + j`:

$$ \sum_{(k,j)} F(k,j) \;=\; \sum_{n} \sum_{k+j=n} F(k,j). $$

This is the engine behind Cauchy products and the classical addition/multiplication
theorems for power-series–defined special functions (e.g. the Bessel multiplication
theorem, DLMF 10.23.4).  Unlike Mathlib's
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`, it applies to *any* summable family,
not only those of product form `f k · g j` — useful when the two indices are coupled
(e.g. through a `Γ(ν+k+j+1)` denominator).

The proof transports the sum along `Finset.sigmaAntidiagonalEquivProd` and applies
`Summable.tsum_sigma'`, the inner antidiagonal fibres being finite.
-/

namespace FLMF.Methods

open Finset

/-- Sum a summable family over `ℕ × ℕ` by antidiagonals. -/
-- no-dlmf: tsum-over-antidiagonal rearrangement, summation infra
theorem tsum_antidiagonal {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T3Space α]
    [ContinuousAdd α] {F : ℕ × ℕ → α} (hF : Summable F) :
    ∑' p : ℕ × ℕ, F p = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, F kl := by
  have hsig : Summable (fun c : (n : ℕ) × ↥(Finset.antidiagonal n) =>
      F (Finset.sigmaAntidiagonalEquivProd c)) :=
    (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hF
  rw [← (Finset.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq F,
    hsig.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
  exact tsum_congr fun n => by rw [tsum_fintype]; exact Finset.sum_coe_sort _ F

end FLMF.Methods
