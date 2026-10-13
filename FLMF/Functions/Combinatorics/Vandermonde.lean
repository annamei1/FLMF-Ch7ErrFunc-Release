import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The Vandermonde–Chu identity for rising factorials (DLMF 15.4.24)

The **Vandermonde–Chu (Gould) identity** in its rising-factorial convolution form:

$$ (a+b)_n \;=\; \sum_{k=0}^{n} \binom{n}{k}\, (a)_k\, (b)_{n-k}, $$

where `(r)_k = (ascPochhammer ℝ k).eval r` is the rising factorial (Pochhammer
symbol). This is the additive law for the Pochhammer symbol and the terminating
case of Gauss's `₂F₁(a, -n; c; 1)` summation (DLMF 15.4.24); Mathlib has the
multiplicative split `ascPochhammer_mul` but not this convolution.

Proof: induction on `n` via the rising-factorial recurrence
`(r)_{n+1} = (r)_n (r+n)` (`ascPochhammer_succ_eval`) and Pascal's rule, splitting
`a+b+n = (a+k) + (b+(n-k))` to push each factor into the next rising factorial.
-/

open scoped Nat

namespace FLMF.Combinatorics

-- no-dlmf: pure Pochhammer-symbol convolution identity (the classical
-- Vandermonde additive law), proof-infrastructure toward the DLMF 15.4.24
-- hypergeometric evaluation `chu_vandermonde` below; DLMF 15.4.24 itself states
-- only the ratio form `F(-n,b;c;1) = (c-b)_n/(c)_n`, not this convolution.
/-- **Vandermonde–Chu identity (DLMF 15.4.24), convolution form.**
`(a+b)_n = ∑_{k=0}^n C(n,k) (a)_k (b)_{n-k}`, with `(r)_k = (ascPochhammer ℝ k).eval r`.

DLMF 15.4.24.
-/
theorem ascPochhammer_eval_add (a b : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval (a + b)
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)
          * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n - k)).eval b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Finset.sum_mul]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n - k)).eval b)
            * (a + b + (n : ℝ))
          = (n.choose k : ℝ) * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b)
            + (n.choose k : ℝ)
                * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n + 1 - k)).eval b) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
      rw [ascPochhammer_succ_eval]
      have hb : (ascPochhammer ℝ (n + 1 - k)).eval b
          = (ascPochhammer ℝ (n - k)).eval b * (b + (n - k : ℕ)) := by
        rw [show n + 1 - k = (n - k) + 1 by omega, ascPochhammer_succ_eval]
      rw [hb, Nat.cast_sub hkn]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun k => ((n + 1).choose k : ℝ)
        * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n + 1 - k)).eval b)) (n + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one,
      Nat.sub_zero, one_mul, Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ]
    rw [show (∑ k ∈ Finset.range (n + 1), (((n.choose k : ℝ) + (n.choose (k + 1) : ℝ))
            * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b)))
          = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)
              * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b))
            + (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ)
              * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b)) from by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
    have hB : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)
              * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n + 1 - k)).eval b))
          = (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ)
              * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b))
            + (ascPochhammer ℝ (n + 1)).eval b := by
      rw [Finset.sum_range_succ' (fun k => (n.choose k : ℝ)
          * ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n + 1 - k)).eval b)) n,
        Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℝ)
          * ((ascPochhammer ℝ (k + 1)).eval a * (ascPochhammer ℝ (n - k)).eval b)) n]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
        Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one, one_mul, Nat.succ_sub_succ,
        Nat.sub_zero]
    rw [hB]; ring

-- no-dlmf: real restriction of DLMF 15.4.24; faithful surface is chu_vandermonde_complex
/-- **Chu–Vandermonde summation, `₂F₁`-at-`1` form, real parameters.**
`∑_{k=0}^n (-1)^k C(n,k) (b)_k (c+k)_{n-k} = (c-b)_n`, with `(r)_k = (ascPochhammer ℝ k).eval r`.
This is the terminating Gauss sum `₂F₁(-n, b; c; 1) = (c-b)_n/(c)_n` cleared of the
`(c)_k` denominators (so it holds for all real `b, c`). Proof by induction on `n`,
using the inductive hypothesis at the *shifted* parameters `(b+1, c+1)` for one half
and `(b, c)` for the other.
-/
theorem chu_vandermonde (n : ℕ) (b c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ)
        * ((ascPochhammer ℝ k).eval b * (ascPochhammer ℝ (n - k)).eval (c + k))
      = (ascPochhammer ℝ n).eval (c - b) := by
  induction n generalizing b c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ' (fun k => (-1 : ℝ) ^ k * ((n + 1).choose k : ℝ)
        * ((ascPochhammer ℝ k).eval b * (ascPochhammer ℝ (n + 1 - k)).eval (c + k))) (n + 1)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ, pow_succ,
      Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one, one_mul,
      Nat.sub_zero, pow_zero, Nat.cast_zero, add_zero]
    conv_rhs => rw [ascPochhammer_succ_eval]
    rw [show (∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ x * -1 * ((n.choose x : ℝ) + (n.choose (x + 1) : ℝ))
            * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1))))
          = (∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ x * -1 * (n.choose x : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1))))
            + (∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ x * -1 * (n.choose (x + 1) : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1)))) from by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _; ring]
    have hSa : (∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ x * -1 * (n.choose x : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1))))
          = -b * (ascPochhammer ℝ n).eval (c - b) := by
      have hib := ih (b + 1) (c + 1)
      rw [show (c + 1) - (b + 1) = c - b from by ring] at hib
      rw [← hib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      have hbl : (ascPochhammer ℝ (x + 1)).eval b = b * (ascPochhammer ℝ x).eval (b + 1) := by
        rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_comp]; simp
      rw [hbl, show c + (↑x + 1) = (c + 1) + (x : ℝ) from by ring]
      ring
    have hSb : (∑ x ∈ Finset.range (n + 1), (-1 : ℝ) ^ x * -1 * (n.choose (x + 1) : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1))))
            + (ascPochhammer ℝ (n + 1)).eval c
          = ((c : ℝ) + n) * (ascPochhammer ℝ n).eval (c - b) := by
      rw [Finset.sum_range_succ (fun x => (-1 : ℝ) ^ x * -1 * (n.choose (x + 1) : ℝ)
          * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1)))) n]
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      rw [show (∑ x ∈ Finset.range n, (-1 : ℝ) ^ x * -1 * (n.choose (x + 1) : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b * (ascPochhammer ℝ (n - x)).eval (c + (↑x + 1))))
            = ∑ x ∈ Finset.range n, ((c : ℝ) + n) * ((-1 : ℝ) ^ (x + 1) * (n.choose (x + 1) : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b
                * (ascPochhammer ℝ (n - (x + 1))).eval (c + (↑(x + 1) : ℝ)))) from by
          apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_range] at hx
          rw [show n - x = (n - (x + 1)) + 1 by omega,
            ascPochhammer_succ_eval (n - (x + 1)) (c + (↑x + 1)),
            Nat.cast_sub (show x + 1 ≤ n by omega)]
          push_cast; ring]
      rw [← Finset.mul_sum]
      have hrel : (∑ x ∈ Finset.range n, (-1 : ℝ) ^ (x + 1) * (n.choose (x + 1) : ℝ)
              * ((ascPochhammer ℝ (x + 1)).eval b
                * (ascPochhammer ℝ (n - (x + 1))).eval (c + (↑(x + 1) : ℝ))))
            = (ascPochhammer ℝ n).eval (c - b) - (ascPochhammer ℝ n).eval c := by
        have h0 := ih b c
        rw [Finset.sum_range_succ' (fun x => (-1 : ℝ) ^ x * (n.choose x : ℝ)
          * ((ascPochhammer ℝ x).eval b * (ascPochhammer ℝ (n - x)).eval (c + x))) n] at h0
        simp only [Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one,
          one_mul, Nat.sub_zero, pow_zero, Nat.cast_zero, add_zero] at h0
        linarith [h0]
      rw [hrel, show (ascPochhammer ℝ (n + 1)).eval c
            = ((c : ℝ) + n) * (ascPochhammer ℝ n).eval c from by rw [ascPochhammer_succ_eval]; ring]
      ring
    linear_combination hSa + hSb

/-- **Chu–Vandermonde summation (DLMF 15.4.24), `₂F₁`-at-`1` form.**
`∑_{k=0}^n (-1)^k C(n,k) (b)_k (c+k)_{n-k} = (c-b)_n`, with `(r)_k = (ascPochhammer ℂ k).eval r`
and `b, c : ℂ` (DLMF's real-or-complex parameters). This is the terminating Gauss sum
`₂F₁(-n, b; c; 1) = (c-b)_n/(c)_n` cleared of the `(c)_k` denominators, at DLMF's full
stated domain (`n = 0, 1, 2, …`, `b, c` real or complex).

DLMF 15.4.24.
Fidelity: tier1 PASS
Verified: unverified
DAG: E-15.4.24.
-/
theorem chu_vandermonde_complex (n : ℕ) (b c : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k : ℂ)
        * ((ascPochhammer ℂ k).eval b * (ascPochhammer ℂ (n - k)).eval (c + k))
      = (ascPochhammer ℂ n).eval (c - b) := by
  induction n generalizing b c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ' (fun k => (-1 : ℂ) ^ k * ((n + 1).choose k : ℂ)
        * ((ascPochhammer ℂ k).eval b * (ascPochhammer ℂ (n + 1 - k)).eval (c + k))) (n + 1)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ, pow_succ,
      Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one, one_mul,
      Nat.sub_zero, pow_zero, Nat.cast_zero, add_zero]
    conv_rhs => rw [ascPochhammer_succ_eval]
    rw [show (∑ x ∈ Finset.range (n + 1), (-1 : ℂ) ^ x * -1 * ((n.choose x : ℂ) + (n.choose (x + 1) : ℂ))
            * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1))))
          = (∑ x ∈ Finset.range (n + 1), (-1 : ℂ) ^ x * -1 * (n.choose x : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1))))
            + (∑ x ∈ Finset.range (n + 1), (-1 : ℂ) ^ x * -1 * (n.choose (x + 1) : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1)))) from by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _; ring]
    have hSa : (∑ x ∈ Finset.range (n + 1), (-1 : ℂ) ^ x * -1 * (n.choose x : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1))))
          = -b * (ascPochhammer ℂ n).eval (c - b) := by
      have hib := ih (b + 1) (c + 1)
      rw [show (c + 1) - (b + 1) = c - b from by ring] at hib
      rw [← hib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      have hbl : (ascPochhammer ℂ (x + 1)).eval b = b * (ascPochhammer ℂ x).eval (b + 1) := by
        rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_comp]; simp
      rw [hbl, show c + (↑x + 1) = (c + 1) + (x : ℂ) from by ring]; ring
    have hSb : (∑ x ∈ Finset.range (n + 1), (-1 : ℂ) ^ x * -1 * (n.choose (x + 1) : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1))))
            + (ascPochhammer ℂ (n + 1)).eval c
          = ((c : ℂ) + n) * (ascPochhammer ℂ n).eval (c - b) := by
      rw [Finset.sum_range_succ (fun x => (-1 : ℂ) ^ x * -1 * (n.choose (x + 1) : ℂ)
          * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1)))) n]
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      rw [show (∑ x ∈ Finset.range n, (-1 : ℂ) ^ x * -1 * (n.choose (x + 1) : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b * (ascPochhammer ℂ (n - x)).eval (c + (↑x + 1))))
            = ∑ x ∈ Finset.range n, ((c : ℂ) + n) * ((-1 : ℂ) ^ (x + 1) * (n.choose (x + 1) : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b
                * (ascPochhammer ℂ (n - (x + 1))).eval (c + (↑(x + 1) : ℂ)))) from by
          apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_range] at hx
          rw [show n - x = (n - (x + 1)) + 1 by omega,
            ascPochhammer_succ_eval (n - (x + 1)) (c + (↑x + 1)),
            Nat.cast_sub (show x + 1 ≤ n by omega)]
          push_cast; ring]
      rw [← Finset.mul_sum]
      have hrel : (∑ x ∈ Finset.range n, (-1 : ℂ) ^ (x + 1) * (n.choose (x + 1) : ℂ)
              * ((ascPochhammer ℂ (x + 1)).eval b
                * (ascPochhammer ℂ (n - (x + 1))).eval (c + (↑(x + 1) : ℂ))))
            = (ascPochhammer ℂ n).eval (c - b) - (ascPochhammer ℂ n).eval c := by
        have h0 := ih b c
        rw [Finset.sum_range_succ' (fun x => (-1 : ℂ) ^ x * (n.choose x : ℂ)
          * ((ascPochhammer ℂ x).eval b * (ascPochhammer ℂ (n - x)).eval (c + x))) n] at h0
        simp only [Nat.choose_zero_right, Nat.cast_one, ascPochhammer_zero, Polynomial.eval_one,
          one_mul, Nat.sub_zero, pow_zero, Nat.cast_zero, add_zero] at h0
        linear_combination h0
      rw [hrel, show (ascPochhammer ℂ (n + 1)).eval c
            = ((c : ℂ) + n) * (ascPochhammer ℂ n).eval c from by rw [ascPochhammer_succ_eval]; ring]
      ring
    linear_combination hSa + hSb

end FLMF.Combinatorics
