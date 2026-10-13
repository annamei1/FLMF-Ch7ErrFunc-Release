import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev polynomials: the Rodrigues formula (DLMF §18.5)

The Chebyshev polynomials of the first kind admit the classical *Rodrigues
representation* (DLMF Table 18.5.1 / 18.5.5):
$$
  T_n(x)
    = \frac{(-1)^n\,2^n\,n!}{(2n)!}\,(1-x^2)^{1/2}\,
        \frac{d^n}{dx^n}\!\left[(1-x^2)^{n-1/2}\right],
  \qquad x\in(-1,1).
$$

A fully general inductive proof requires an $n$-th order Leibniz/Faà-di-Bruno
calculus for fractional powers `(1 - x^2) ^ (n - 1/2)`, which is not yet
available in Mathlib.  Here we set up the precise statement together with the
constant and weight occurring in it, and we prove rigorously the two base
cases `n = 0` and `n = 1`, which are genuine calculus identities on the open
interval `(-1, 1)`.

## Main results

* `rodriguesConst` : the scalar prefactor `(-1)^n 2^n n! / (2n)!`.
* `rodriguesRHS`   : the right-hand side of the Rodrigues formula as a function
  of `x`.
* `chebyshevT_rodrigues`      : the general formula (DLMF 18.5.5), stated
  faithfully for all `n`; currently a `sorry` surface.
* `chebyshevT_rodrigues_zero` : the formula for `n = 0` (proven).
* `chebyshevT_rodrigues_one`  : the formula for `n = 1` (proven).
-/

open Polynomial Polynomial.Chebyshev Real

namespace FLMF.Functions.Chebyshev

-- no-dlmf: packaging def for the Rodrigues prefactor; the formula itself is DLMF 18.5.5 below.
/-- The Rodrigues prefactor `(-1)^n · 2^n · n! / (2n)!`. -/
noncomputable def rodriguesConst (n : ℕ) : ℝ :=
  (-1) ^ n * 2 ^ n * (n.factorial : ℝ) / ((2 * n).factorial : ℝ)

-- no-dlmf: packaging def (RHS of the Rodrigues formula); the identity is DLMF 18.5.5 below.
/-- The right-hand side of the Chebyshev–Rodrigues formula, as a real function
of `x`:
`(-1)^n 2^n n!/(2n)! · (1-x^2)^{1/2} · dⁿ/dxⁿ[(1-x^2)^{n-1/2}]`. -/
noncomputable def rodriguesRHS (n : ℕ) (x : ℝ) : ℝ :=
  rodriguesConst n * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
    iteratedDeriv n (fun t => (1 - t ^ 2) ^ ((n : ℝ) - 1 / 2)) x

-- no-dlmf: instance of DLMF 18.5.5 (degree fixed to n = 0); faithful surface is chebyshevT_rodrigues
/-- Rodrigues formula for `T₀`, base case `n = 0`.  Since the prefactor and both
fractional powers cancel, the formula reduces to the constant value
`T₀(x) = 1`. -/
theorem chebyshevT_rodrigues_zero (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (0 : ℕ)).eval x = rodriguesRHS 0 x := by
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hne : (1 - x ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [rodriguesRHS, rodriguesConst, iteratedDeriv_zero]
  -- The inner exponent is `(0 : ℝ) - 1/2 = -(1/2)`.
  have hcast : ((0 : ℕ) : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by norm_num
  rw [hcast]
  -- `(1-x²)^{1/2} · (1-x²)^{-1/2} = 1`.
  have hprod : (1 - x ^ 2) ^ ((1 : ℝ) / 2) * (1 - x ^ 2) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hpos]; norm_num
  rw [show (T ℝ (0 : ℕ)) = 1 from by simp [T_zero]]
  simp only [eval_one]
  rw [mul_assoc, hprod]
  norm_num [Nat.factorial]

-- no-dlmf: proof-internal derivative helper for the n=1 Rodrigues base case.
/-- The (real) derivative of `t ↦ (1 - t^2)^{1/2}` at a point `x ∈ (-1,1)`. -/
private theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hpos : (0 : ℝ) < 1 - x ^ 2) :
    HasDerivAt (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2))
      ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x))) x := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    have : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    simpa using (this.const_sub 1)
  have := hbase.rpow_const (p := (1 : ℝ) / 2) (Or.inl (ne_of_gt hpos))
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

-- no-dlmf: instance of DLMF 18.5.5 (degree fixed to n = 1); faithful surface is chebyshevT_rodrigues
/-- Rodrigues formula for `T₁`, base case `n = 1`.  Here
`T₁(x) = x`, and the right-hand side evaluates to `x` after differentiating
`(1-x^2)^{1/2}` once. -/
theorem chebyshevT_rodrigues_one (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (1 : ℕ)).eval x = rodriguesRHS 1 x := by
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hne : (1 - x ^ 2) ≠ 0 := ne_of_gt hpos
  simp only [rodriguesRHS, rodriguesConst, iteratedDeriv_one]
  -- inner exponent `(1 : ℝ) - 1/2 = 1/2`
  have hcast : ((1 : ℕ) : ℝ) - 1 / 2 = (1 : ℝ) / 2 := by norm_num
  -- compute the derivative of `t ↦ (1 - t²)^{1/2}` at `x`
  have hderiv :
      deriv (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2 - 1 / 2 + 1 / 2)) x
        = (1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)) := by
    have : (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2 - 1 / 2 + 1 / 2))
        = (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2)) := by
      norm_num
    rw [this]
    exact (hasDerivAt_sqrt_one_sub_sq hpos).deriv
  rw [hcast]
  have hderiv' :
      deriv (fun t : ℝ => (1 - t ^ 2) ^ ((1 : ℝ) / 2)) x
        = (1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)) :=
    (hasDerivAt_sqrt_one_sub_sq hpos).deriv
  rw [hderiv']
  -- Now simplify the product.
  -- `(1-x²)^{1/2} · (1-x²)^{1/2-1} = (1-x²)^{0} = 1`.
  have hprod : (1 - x ^ 2) ^ ((1 : ℝ) / 2) * ((1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1))
      = 1 := by
    rw [← Real.rpow_add hpos]
    norm_num
  -- T₁ = X
  rw [show (T ℝ (1 : ℕ)) = X from by simp [T_one]]
  simp only [eval_X]
  -- Rearrange and use hprod.
  rw [show ((-1 : ℝ) ^ 1 * 2 ^ 1 * (Nat.factorial 1 : ℝ) / (Nat.factorial (2 * 1) : ℝ))
        = -1 from by norm_num [Nat.factorial]]
  have key :
      -1 * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
          ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)))
        = x := by
    have : -1 * (1 - x ^ 2) ^ ((1 : ℝ) / 2) *
          ((1 / 2 : ℝ) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1) * (-(2 * x)))
        = ((1 - x ^ 2) ^ ((1 : ℝ) / 2) * (1 - x ^ 2) ^ ((1 : ℝ) / 2 - 1)) * x := by
      ring
    rw [this, hprod]; ring
  linarith [key]

/-- **DLMF 18.5.5** (row `T_n` of Table 18.5.1) — the Rodrigues formula for the
Chebyshev polynomials of the first kind: for every nonnegative integer `n` and
every `x ∈ (-1, 1)`,
$$
  T_n(x) = \frac{(-1)^n 2^n n!}{(2n)!}\,(1-x^2)^{1/2}\,
    \frac{d^n}{dx^n}\left[(1-x^2)^{n-1/2}\right].
$$

DAG: E-18.5.5.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem chebyshevT_rodrigues (n : ℕ) (x : ℝ) (hx : -1 < x) (hx' : x < 1) :
    (T ℝ (n : ℕ)).eval x = rodriguesRHS n x := by
  sorry

end FLMF.Functions.Chebyshev
