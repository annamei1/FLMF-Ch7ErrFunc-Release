import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Linear recurrences and series coefficient matching (method kit)

The recurrence toolkit behind contiguous relations and three-term recurrences
proved by **coefficient matching**: combine the `HasSum` forms of several
series with scalar weights, check that every coefficient of `zⁿ` vanishes by
(Pochhammer) algebra, and conclude the linear relation between the sums.
Abstracted from the DLMF 13.3.1–3 proofs in
`FLMF.Frameworks.Hypergeometric.KummerContiguous`, which now run through this
file.

Contents:

* `IsPRecursive` — the P-recursive predicate: an order-`d` linear recurrence
  with *index-dependent* coefficient functions, the holonomic-sequence case
  Mathlib's constant-coefficient `LinearRecurrence` cannot express.
* `hasSum_eq_zero` — a series whose terms all vanish sums to `0`: the
  coefficient-matching engine (apply to a `HasSum.add`/`.sub`/`.mul_left`
  combination of series; the pointwise hypothesis is the termwise identity).
* `hasSum_linComb` — the packaged termwise linear combination: pointwise
  `∑ₖ λₖ • fₖ n = 0` with `HasSum (fₖ) (Sₖ)` gives `∑ₖ λₖ • Sₖ = 0`.
* `hasSum_zero_cons` — the shift/reindex helper: prepending a zero term keeps
  the sum (the `z·f(z)` degree shift of a power series).
* Pochhammer/factorial normalizers (`ascPochhammer_shift_bridge`,
  `ascPochhammer_succ_eval_sub_one`, `ascPochhammer_eval_ne_zero`,
  `cast_factorial_succ`) — the simp/`linear_combination` inputs that reduce
  contiguous coefficients to `ring`-equal atoms.

Everything is `HasSum`-hypothesis-only: no analyticity or radius hypotheses
appear anywhere.
-/

namespace FLMF.Methods

/-! ### P-recursive sequences -/

/-- `a` satisfies a linear recurrence of order `d` whose coefficients are
*functions* `c i : ℕ → R` of the index — the P-recursive (holonomic-sequence)
case that Mathlib's constant-coefficient `LinearRecurrence` cannot express:
`∀ n, ∑ i ≤ d, c i n · a (n + i) = 0`. Hypergeometric series coefficients
(e.g. `(n+1)(b+n)·cₙ₊₁ − (a+n)·cₙ = 0` behind Kummer's equation) are the
`d = 1` case. -/
-- no-dlmf: structural predicate, no DLMF counterpart
def IsPRecursive {R : Type*} [NonUnitalNonAssocSemiring R] (d : ℕ)
    (c : Fin (d + 1) → ℕ → R) (a : ℕ → R) : Prop :=
  ∀ n, ∑ i, c i n * a (n + i) = 0

/-! ### `HasSum` coefficient-matching combinators -/

section HasSum

variable {β E : Type*} [AddCommMonoid E] [TopologicalSpace E]

/-- A series whose terms all vanish sums to `0` — the coefficient-matching
engine. Apply with `h` a `HasSum.add`/`.sub`/`.mul_left` combination of
series: the hypothesis `h0` is then the termwise coefficient identity, and the
conclusion is the linear relation between the sums. -/
-- no-dlmf: summation infrastructure, no DLMF counterpart
theorem hasSum_eq_zero [T2Space E] {f : β → E} {S : E}
    (h : HasSum f S) (h0 : ∀ b, f b = 0) : S = 0 :=
  h.unique (by rw [funext h0]; exact hasSum_zero)

/-- **Termwise linear combination of series.** If each `f k` sums to `S k` and
the weighted terms cancel pointwise, `∑ₖ λₖ • fₖ n = 0`, then the sums satisfy
the same linear relation `∑ₖ λₖ • Sₖ = 0`. The `Fin`/`Fintype`-indexed
packaging of `hasSum_eq_zero` for an `m`-term contiguous relation or
recurrence. -/
-- no-dlmf: summation infrastructure, no DLMF counterpart
theorem hasSum_linComb {ι 𝕜 : Type*} [Fintype ι] [DistribSMul 𝕜 E]
    [ContinuousConstSMul 𝕜 E] [ContinuousAdd E] [T2Space E]
    {f : ι → β → E} {S : ι → E} (h : ∀ k, HasSum (f k) (S k)) (lam : ι → 𝕜)
    (hpt : ∀ n, ∑ k, lam k • f k n = 0) : ∑ k, lam k • S k = 0 :=
  hasSum_eq_zero (hasSum_sum fun k _ => (h k).const_smul (lam k)) hpt

/-- **Shift/reindex helper**: prepending a zero term keeps the sum. If
`HasSum f S` and `g` is `f` shifted up one index with `g 0 = 0`, then
`HasSum g S`. This is the alignment step for the `z·f(z)` term of a
contiguous relation: from `HasSum (cₙ zⁿ) S`, the family
`g = (0, c₀z¹, c₁z², …)` has sum `z·S` (apply to `(h.mul_left z)`). -/
-- no-dlmf: summation infrastructure, no DLMF counterpart
theorem hasSum_zero_cons {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {f g : ℕ → E} {S : E} (h : HasSum f S)
    (hg0 : g 0 = 0) (hg : ∀ m, g (m + 1) = f m) : HasSum g S := by
  have h1 : HasSum (fun n => g (n + 1)) S := by simpa [hg] using h
  simpa [hg0] using (hasSum_nat_add_iff (f := g) 1).mp h1

end HasSum

/-! ### Pochhammer and factorial normalizers

The `simp only`/`linear_combination` inputs of a coefficient-matching proof:
the last-factor and first-factor recursions `(x)ₘ₊₁ = (x)ₘ·(x+m) = x·(x+1)ₘ`
reduce shifted-parameter Pochhammer symbols to the atoms `(x)ₘ`, `(x+1)ₘ`, and
the bridge `x·(x+1)ₘ = (x)ₘ·(x+m)` makes the resulting coefficients
`ring`-equal. -/

section Pochhammer

open Polynomial

/-- Nonvanishing of `(x)ₘ` when `x` avoids the nonpositive integers
(`∀ k : ℕ, k ≠ -x`) — the denominator condition of every hypergeometric
contiguous relation, packaged from `ascPochhammer_eval_eq_zero_iff`. -/
-- no-dlmf: Pochhammer nonvanishing infrastructure, no DLMF counterpart
theorem ascPochhammer_eval_ne_zero {R : Type*} [Ring R] [IsDomain R] {x : R}
    (hx : ∀ k : ℕ, (k : R) ≠ -x) (m : ℕ) : (ascPochhammer R m).eval x ≠ 0 := by
  rw [Ne, ascPochhammer_eval_eq_zero_iff]
  push Not
  exact fun k _ => hx k

/-- The Pochhammer **bridge identity** `x·(x+1)ₘ = (x)ₘ·(x+m)`, equating the
first-factor and last-factor peelings of `(x)ₘ₊₁`. This is the single algebraic
fact that makes shifted-parameter contiguous coefficients `ring`-equal. -/
-- no-dlmf: Pochhammer recursion algebra, no distinct DLMF equation number
theorem ascPochhammer_shift_bridge {R : Type*} [CommSemiring R] (x : R) (m : ℕ) :
    x * (ascPochhammer R m).eval (x + 1) = (ascPochhammer R m).eval x * (x + m) := by
  rw [← ascPochhammer_succ_eval, ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_add, eval_X, eval_one]

/-- First-factor peeling at a downshifted argument:
`(x−1)ₘ₊₁ = (x−1)·(x)ₘ` — the normalizer for `a ↦ a−1` parameter shifts. -/
-- no-dlmf: Pochhammer recursion algebra, no distinct DLMF equation number
theorem ascPochhammer_succ_eval_sub_one {R : Type*} [CommRing R] (x : R) (m : ℕ) :
    (ascPochhammer R (m + 1)).eval (x - 1) = (x - 1) * (ascPochhammer R m).eval x := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one,
    sub_add_cancel]

/-- Cast form of `(m+1)! = (m+1)·m!` — the factorial step of a coefficient
recurrence, in the shape `field_simp`/`linear_combination` consume. -/
-- no-dlmf: factorial cast normalizer, no DLMF counterpart
theorem cast_factorial_succ {R : Type*} [CommSemiring R] (m : ℕ) :
    ((Nat.factorial (m + 1) : ℕ) : R) = ((m : R) + 1) * ((Nat.factorial m : ℕ) : R) := by
  push_cast [Nat.factorial_succ]
  ring

end Pochhammer

end FLMF.Methods
