import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FLMF.Functions.OrthogonalPolynomials.Jacobi

/-!
# Gegenbauer (ultraspherical) polynomials `C_n^{(λ)}` (DLMF 18.5.9)

The Gegenbauer polynomials are the symmetric (`α = β = λ − 1/2`) members of the
Jacobi family, written as the terminating Gauss hypergeometric series
(DLMF 18.5.9, <https://dlmf.nist.gov/18.5#E9>)

$$ C_n^{(λ)}(x) = \frac{(2λ)_n}{n!}\; {}_2F_1\!\Big({-n},\,n+2λ;\,λ+\tfrac12;\,\tfrac{1-x}{2}\Big), $$

with `(2λ)_n / n!` the leading normalization. The `₂F₁` terminates because
`(-n)_k = 0` for `k > n`, so this is a genuine polynomial of degree `n`.

## Main results

* `FLMF.Gegenbauer.gegenbauer λ n x` — `C_n^{(λ)}(x)`.
* `gegenbauer_zero` — `C_0^{(λ)} = 1`.
* `gegenbauer_eval_one` — **DLMF §18.6, Table 18.6.1**: `C_n^{(λ)}(1) = (2λ)_n / n!`.

## References

- DLMF §18.5.9: https://dlmf.nist.gov/18.5#E9
- DLMF §18.6, Table 18.6.1: https://dlmf.nist.gov/18.6
-/

open scoped Nat

namespace FLMF.Gegenbauer

noncomputable section

/-- **DLMF 18.5.9.** The Gegenbauer (ultraspherical) polynomial `C_n^{(λ)}(x)`, as
`(2λ)_n/n!` times the terminating `₂F₁(-n, n+2λ; λ+1/2; (1-x)/2)`. Here
`(r)_k = (ascPochhammer ℝ k).eval r` is the rising factorial. -/
-- DAG: E-18.5.9.
-- Verified: verified (tier2)
def gegenbauer (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (2 * lam) / n ! *
    ∑ k ∈ Finset.range (n + 1),
      ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + 2 * lam))
        / ((ascPochhammer ℝ k).eval (lam + 1 / 2) * k !) * ((1 - x) / 2) ^ k

-- no-dlmf: P_0 normalization (C_0^{(λ)} = 1)
/-- `C_0^{(λ)} = 1`. -/
@[simp] theorem gegenbauer_zero (lam : ℝ) (x : ℝ) : gegenbauer lam 0 x = 1 := by
  simp [gegenbauer]

/-- **DLMF §18.6 (Table 18.6.1, Gegenbauer `p_n(1)` column).** `C_n^{(λ)}(1) =
(2λ)_n / n!`. (At `x = 1` the argument `(1-x)/2 = 0`, so only the `k = 0` term
of the `₂F₁` survives, giving `1`.)

DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem gegenbauer_eval_one (lam : ℝ) (n : ℕ) :
    gegenbauer lam n 1 = (ascPochhammer ℝ n).eval (2 * lam) / n ! := by
  rw [gegenbauer]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + 2 * lam))
        / ((ascPochhammer ℝ k).eval (lam + 1 / 2) * k !) * ((1 - (1 : ℝ)) / 2) ^ k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [show ((1 - (1 : ℝ)) / 2) = 0 by norm_num, zero_pow hk, mul_zero]
    · intro h; simp at h
  rw [hsum, mul_one]

/-- **Gegenbauer as a Jacobi special case (DLMF 18.7.1).** The Gegenbauer
polynomials are the symmetric Jacobi family with `α = β = λ − 1/2`:
`(λ+1/2)_n · C_n^{(λ)}(x) = (2λ)_n · P_n^{(λ-1/2, λ-1/2)}(x)`.
(Stated multiplicatively to avoid any nonvanishing hypothesis: the two terminating
`₂F₁` sums are identical — `α+1 = λ+1/2` and `n+α+β+1 = n+2λ` — so the families
agree up to the leading prefactors `(2λ)_n/n!` vs `(λ+1/2)_n/n!`.)

DAG: E-18.7.1.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem gegenbauer_eq_jacobi (lam : ℝ) (n : ℕ) (x : ℝ) :
    (ascPochhammer ℝ n).eval (lam + 1 / 2) * gegenbauer lam n x
      = (ascPochhammer ℝ n).eval (2 * lam) * FLMF.Jacobi.jacobiP (lam - 1 / 2) (lam - 1 / 2) n x := by
  rw [gegenbauer, FLMF.Jacobi.jacobiP]
  simp only [show (n : ℝ) + (lam - 1 / 2) + (lam - 1 / 2) + 1 = (n : ℝ) + 2 * lam from by ring,
    show lam - 1 / 2 + 1 = lam + 1 / 2 from by ring]
  ring

open FLMF.Combinatorics in
-- no-dlmf: proof-internal generalization of `FLMF.Jacobi.jacobiP_eval_neg_one` to the natural
-- nonvanishing hypothesis (rather than the sufficient-but-narrower `-1 < α` used there); kept
-- local to this file since `Jacobi.lean` is not touched.
/-- `P_n^{(α,β)}(-1) = (-1)^n (β+1)_n / n!` whenever `(α+1)_n ≠ 0` (the natural domain where
the Jacobi polynomial's defining sum has no zero denominators), generalizing
`FLMF.Jacobi.jacobiP_eval_neg_one`'s `-1 < α` hypothesis. -/
theorem jacobiP_eval_neg_one_of_ne_zero (α β : ℝ) (n : ℕ)
    (hne : (ascPochhammer ℝ n).eval (α + 1) ≠ 0) :
    FLMF.Jacobi.jacobiP α β n (-1) = (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) / n ! := by
  rw [FLMF.Jacobi.jacobiP]
  simp only [show (1 - (-1 : ℝ)) / 2 = 1 by norm_num, one_pow, mul_one]
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (ascPochhammer ℝ n).eval (α + 1)
        * (((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1))
          / ((ascPochhammer ℝ k).eval (α + 1) * k !))
      = (-1 : ℝ) ^ k * (n.choose k : ℝ)
          * ((ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1)
            * (ascPochhammer ℝ (n - k)).eval ((α + 1) + k)) := by
    intro k hk; rw [Finset.mem_range] at hk
    have hkfac : (k ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hsplit : (ascPochhammer ℝ n).eval (α + 1)
        = (ascPochhammer ℝ k).eval (α + 1) * (ascPochhammer ℝ (n - k)).eval ((α + 1) + k) := by
      conv_lhs => rw [show n = k + (n - k) by omega, ← ascPochhammer_mul]
      rw [Polynomial.eval_mul, Polynomial.eval_comp]
      simp
    have hαk : (ascPochhammer ℝ k).eval (α + 1) ≠ 0 := by
      intro h0; exact hne (by rw [hsplit, h0, zero_mul])
    rw [hsplit, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  have hkey : (ascPochhammer ℝ n).eval (α + 1)
      * (∑ k ∈ Finset.range (n + 1),
          ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1))
            / ((ascPochhammer ℝ k).eval (α + 1) * k !))
      = (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, chu_vandermonde n ((n : ℝ) + α + β + 1) (α + 1),
      show (α + 1) - ((n : ℝ) + α + β + 1) = -((n : ℝ) + β) by ring,
      FLMF.Jacobi.ascPochhammer_neg_reflect]
  rw [div_mul_eq_mul_div, hkey]

/-- **DLMF §18.6 (Table 18.6.1: the `p_n(1)` value combined with the `p_n(-x) =
(-1)^n p_n(x)` symmetry row).** `C_n^{(λ)}(-1) = (-1)^n (2λ)_n / n!`, for any `λ` at which
the Gegenbauer polynomial's defining sum has no zero denominators (`(λ+1/2)_n ≠ 0`) — DLMF's
table entry carries no further `λ`-constraint. From `jacobiP_eval_neg_one_of_ne_zero` and
`gegenbauer_eq_jacobi`.

DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem gegenbauer_eval_neg_one (lam : ℝ) (n : ℕ)
    (hne : (ascPochhammer ℝ n).eval (lam + 1 / 2) ≠ 0) :
    gegenbauer lam n (-1) = (-1) ^ n * (ascPochhammer ℝ n).eval (2 * lam) / n ! := by
  have h := gegenbauer_eq_jacobi lam n (-1)
  rw [jacobiP_eval_neg_one_of_ne_zero (lam - 1 / 2) (lam - 1 / 2) n
      (by rw [show lam - 1 / 2 + 1 = lam + 1 / 2 by ring]; exact hne),
    show lam - 1 / 2 + 1 = lam + 1 / 2 by ring] at h
  have h2 : (ascPochhammer ℝ n).eval (lam + 1 / 2) * gegenbauer lam n (-1)
      = (ascPochhammer ℝ n).eval (lam + 1 / 2)
        * ((-1) ^ n * (ascPochhammer ℝ n).eval (2 * lam) / n !) := by
    rw [h]; ring
  exact mul_left_cancel₀ hne h2

end

end FLMF.Gegenbauer
