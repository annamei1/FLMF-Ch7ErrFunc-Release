import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import FLMF.Support.CombinatoricsVandermonde

/-!
# Jacobi polynomials `P_n^{(α,β)}` (DLMF 18.5.7) — the apex of the Askey scheme

The Jacobi polynomials sit at the top of the continuous Askey scheme. They are the
terminating Gauss hypergeometric series (DLMF 18.5.7)

$$ P_n^{(α,β)}(x) = \binom{n+α}{n}\; {}_2F_1\!\Big({-n},\,n+α+β+1;\,α+1;\,\tfrac{1-x}{2}\Big), $$

with `\binom{n+α}{n} = (α+1)_n/n!`. The `₂F₁` terminates because `(-n)_k = 0` for
`k > n`, so this is a genuine polynomial of degree `n` in `x`.

## Main results

* `FLMF.Jacobi.jacobiP α β n x` — `P_n^{(α,β)}(x)`.
* `jacobiP_zero` — `P_0^{(α,β)} = 1`.
* `jacobiP_eval_one` — **DLMF §18.6, Table 18.6.1**: `P_n^{(α,β)}(1) = (α+1)_n / n!`.

## References

- DLMF §18.5.7: https://dlmf.nist.gov/18.5#E7
- DLMF §18.6, Table 18.6.1: https://dlmf.nist.gov/18.6
-/

open scoped Nat

namespace FLMF.Jacobi

noncomputable section

/-- **DLMF 18.5.7.** The Jacobi polynomial `P_n^{(α,β)}(x)`, as `(α+1)_n/n!` times the
terminating `₂F₁(-n, n+α+β+1; α+1; (1-x)/2)`. Here `(r)_k = (ascPochhammer ℝ k).eval r`
is the rising factorial. -/
-- DAG: E-18.5.7.
-- Verified: unverified
def jacobiP (α β : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (ascPochhammer ℝ n).eval (α + 1) / n ! *
    ∑ k ∈ Finset.range (n + 1),
      ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1))
        / ((ascPochhammer ℝ k).eval (α + 1) * k !) * ((1 - x) / 2) ^ k

-- no-dlmf: `n = 0` normalization (P₀ = 1), not a numbered DLMF identity
/-- `P_0^{(α,β)} = 1`. -/
@[simp] theorem jacobiP_zero (α β : ℝ) (x : ℝ) : jacobiP α β 0 x = 1 := by
  simp [jacobiP]

/-- **DLMF §18.6 (Table 18.6.1, Jacobi `p_n(1)` column).** `P_n^{(α,β)}(1) =
(α+1)_n / n!`. (At `x = 1` the argument `(1-x)/2 = 0`, so only the `k = 0`
term of the `₂F₁` survives, giving `1`.)

DAG: E-18.6.
Numerical: PASS
Verified: verified
-/
theorem jacobiP_eval_one (α β : ℝ) (n : ℕ) :
    jacobiP α β n 1 = (ascPochhammer ℝ n).eval (α + 1) / n ! := by
  rw [jacobiP]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      ((ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1))
        / ((ascPochhammer ℝ k).eval (α + 1) * k !) * ((1 - (1 : ℝ)) / 2) ^ k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [show ((1 - (1 : ℝ)) / 2) = 0 by norm_num, zero_pow hk, mul_zero]
    · intro h; simp at h
  rw [hsum, mul_one]

open FLMF.Combinatorics in
-- no-dlmf: proof-internal Pochhammer reflection helper
/-- Reflection of the rising factorial: `(-(n+β))_n = (-1)^n (β+1)_n`. -/
theorem ascPochhammer_neg_reflect (β : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval (-((n : ℝ) + β)) = (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer,
    show ((n : ℝ) + β) - n + 1 = β + 1 by ring]

-- no-dlmf: technical nonvanishing bound used in proofs
/-- `(α+1)_k ≠ 0` for `α > -1` (the rising factorial of a positive base is positive). -/
theorem ascPochhammer_eval_succ_ne_zero {α : ℝ} (hα : -1 < α) (k : ℕ) :
    (ascPochhammer ℝ k).eval (α + 1) ≠ 0 :=
  (ascPochhammer_pos k (α + 1) (by linarith)).ne'

open FLMF.Combinatorics in
/-- **DLMF §18.6 (Table 18.6.1: the `p_n(-x) = (-1)^n p_n(x)` symmetry row
combined with the Jacobi `p_n(1)` value).** `P_n^{(α,β)}(-1) = (-1)^n (β+1)_n / n!`,
whenever `(α+1)_n ≠ 0` — the natural domain where the Jacobi polynomial's defining
sum has no zero denominators; DLMF's table entry carries no further `α`-constraint,
and this is the minimal hypothesis under which the real-valued `jacobiP` (a finite
sum of quotients, not a Gamma-function extension) can equal that value. At `x = -1`
the argument `(1-x)/2 = 1`, so the `₂F₁` becomes a Chu–Vandermonde sum
(`chu_vandermonde`), which evaluates to `(-(n+β))_n = (-1)^n (β+1)_n` after the
`(α+1)_n` prefactor is absorbed via `ascPochhammer_mul`.

DAG: E-18.6.
Numerical: PASS
Verified: unverified
-/
theorem jacobiP_eval_neg_one (α β : ℝ) (n : ℕ)
    (hne : (ascPochhammer ℝ n).eval (α + 1) ≠ 0) :
    jacobiP α β n (-1) = (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) / n ! := by
  rw [jacobiP]
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
      show (α + 1) - ((n : ℝ) + α + β + 1) = -((n : ℝ) + β) by ring, ascPochhammer_neg_reflect]
  rw [div_mul_eq_mul_div, hkey]

end

end FLMF.Jacobi
