import FLMF.Functions.OrthogonalPolynomials.GegenbauerGenerating
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev generating function (DLMF §18.12)

The classical generating function for the Chebyshev polynomials of the second kind is

$$\sum_{n=0}^{\infty} U_n(x)\, t^n = \frac{1}{1 - 2 x t + t^2}.$$

Since Mathlib's `Polynomial.Chebyshev.U` is indexed over `ℤ`, and infinite power-series
convergence is delicate, we record the precise *finite* (telescoping) form of this
generating identity, which is the algebraic heart of DLMF 18.12: for every `N`,

$$(1 - 2 x t + t^2) \sum_{n=0}^{N} U_n(x)\, t^n
    = 1 - U_{N+1}(x)\, t^{N+1} + U_N(x)\, t^{N+2}.$$

Dividing by `1 - 2xt + t²` and letting `N → ∞` (for `|t|` small) recovers the stated
power-series identity, since the remainder terms vanish.
-/

open Polynomial
open Polynomial.Chebyshev
open scoped BigOperators

namespace FLMF.Functions.Chebyshev

-- no-dlmf: packaging abbreviation for `(U ℝ n).eval x`, used by the generating-function proof.
/-- Abbreviation for the value `Uₙ(x)` of the second-kind Chebyshev polynomial. -/
noncomputable def Uval (x : ℝ) (n : ℕ) : ℝ := (U ℝ (n : ℤ)).eval x

-- no-dlmf: base-case simp helper (`U₀ = 1`) for the generating-function induction.
@[simp] theorem Uval_zero (x : ℝ) : Uval x 0 = 1 := by
  simp [Uval, U_zero]

-- no-dlmf: base-case simp helper (`U₁ = 2x`) for the generating-function induction.
@[simp] theorem Uval_one (x : ℝ) : Uval x 1 = 2 * x := by
  simp [Uval, U_one]

theorem Uval_add_two (x : ℝ) (n : ℕ) :
    Uval x (n + 2) = 2 * x * Uval x (n + 1) - Uval x n := by
  have h := U_add_two ℝ (n : ℤ)
  have := congrArg (Polynomial.eval x) h
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at this
  simp only [Uval]
  push_cast
  linear_combination this

end FLMF.Functions.Chebyshev

namespace FLMF.Chebyshev

open FLMF.Functions.Chebyshev

-- no-dlmf: packaging abbreviation for `(T ℝ n).eval x`, used by the generating-function proofs.
/-- Abbreviation for the value `Tₙ(x)` of the first-kind Chebyshev polynomial. -/
noncomputable def Tval (x : ℝ) (n : ℕ) : ℝ := (T ℝ (n : ℤ)).eval x

-- no-dlmf: base-case simp helper (`T₀ = 1`) for the generating-function proofs.
@[simp] theorem Tval_zero (x : ℝ) : Tval x 0 = 1 := by
  simp [Tval, T_zero]

private theorem Tval_succ (x : ℝ) (n : ℕ) :
    Tval x (n + 1) = Uval x (n + 1) - x * Uval x n := by
  have h := congrArg (Polynomial.eval x)
    (T_eq_U_sub_X_mul_U ℝ ((n + 1 : ℕ) : ℤ))
  simpa [Tval, Uval] using h

lemma gegenbauer_one_eq_chebyshevU (n : ℕ) (x : ℝ) :
    FLMF.Gegenbauer.gegenbauer 1 n x = Uval x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [FLMF.Gegenbauer.gegenbauer_one]
      · norm_num
      · norm_num
  | more n h0 h1 =>
      have hg := FLMF.Gegenbauer.gegenbauer_recurrence 1 (by norm_num) x n
      have hu := Uval_add_two x n
      rw [h0, h1] at hg
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      linear_combination hg - ((n : ℝ) + 2) * hu

-- no-dlmf: real-`z` restriction of DLMF 18.12.10; faithful surface is
-- chebyshevU_generating_function_complex.
/-- The Chebyshev second-kind generating function (real `z`)
`1 / (1 - 2xz + z²) = ∑ n, Uₙ(x) zⁿ`. -/
theorem chebyshevU_generating_function {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => Uval x n * z ^ n) ((1 - 2 * x * z + z ^ 2)⁻¹) := by
  simpa only [gegenbauer_one_eq_chebyshevU, neg_one_mul, Real.rpow_neg_one] using
    (FLMF.Gegenbauer.gegenbauer_generating_function (lam := (1 : ℝ)) (x := x) (z := z)
      (by norm_num) hx hz)

/-- **DLMF 18.12.10** — the Chebyshev second-kind generating function at DLMF's stated
strength: real `x`, complex `z` with `‖z‖ < 1`,
`1 / (1 - 2xz + z²) = ∑ n, Uₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`): for real `x` with `|x| > 1` the roots of `1 - 2xz + z² = 0` are real
with product `1`, so one root lies strictly inside the open unit disc and the series
diverges there (e.g. `x = 2` has a pole at `z = 2 - √3 ≈ 0.268 < 1`). The
unconstrained-`x` reading of 18.12.10 is therefore false; `|x| ≤ 1` is the
correctness-preserving domain, and `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.10.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem chebyshevU_generating_function_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Uval x n : ℂ) * z ^ n) ((1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

-- no-dlmf: real-`z` restriction of DLMF 18.12.8; faithful surface is
-- chebyshevT_generating_function_complex.
/-- The Chebyshev first-kind generating function (real `z`)
`(1 - xz) / (1 - 2xz + z²) = ∑ n, Tₙ(x) zⁿ`. -/
theorem chebyshevT_generating_function {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => Tval x n * z ^ n)
      ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) := by
  let SU := (1 - 2 * x * z + z ^ 2)⁻¹
  have hU : HasSum (fun n : ℕ => Uval x n * z ^ n) SU :=
    chebyshevU_generating_function hx hz
  have hshift :
      HasSum (fun n : ℕ => (if n = 0 then 0 else Uval x (n - 1)) * z ^ n) (z * SU) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hU.mul_left z
  have h := hU.sub (hshift.mul_left x)
  convert h using 1
  · funext n
    cases n with
    | zero => simp
    | succ n =>
        rw [show n + 1 = Nat.succ n from rfl]
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
        rw [Tval_succ]
        ring
  · dsimp [SU]
    ring

/-- **DLMF 18.12.8** — the Chebyshev first-kind generating function at DLMF's stated
strength: real `x`, complex `z` with `‖z‖ < 1`,
`(1 - xz) / (1 - 2xz + z²) = ∑ n, Tₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`); see `chebyshevU_generating_function_complex` for why the
unconstrained-`x` reading is false. `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.8.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem chebyshevT_generating_function_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Tval x n : ℂ) * z ^ n)
      ((1 - (x : ℂ) * z) * (1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

-- no-dlmf: real-`z` restriction of DLMF 18.12.7; faithful surface is
-- chebyshevT_generating_function_symm_complex.
/-- The symmetric Chebyshev first-kind generating function (real `z`)
`(1 - z²) / (1 - 2xz + z²) = 1 + 2 ∑ n ≥ 1, Tₙ(x) zⁿ`. -/
theorem chebyshevT_generating_function_symm {x z : ℝ} (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2 * Tval x n) * z ^ n)
      ((1 - z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹) := by
  let d := 1 - 2 * x * z + z ^ 2
  have hx_sq : x ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := x) (b := 1)).mpr (by simpa using hx)
  have hz_sq : z ^ 2 < 1 := by
    simpa using (sq_lt_sq (a := z) (b := 1)).mpr (by simpa using hz)
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith [sq_nonneg (z - x)]
  have hT := (chebyshevT_generating_function hx hz).mul_left 2
  have hdelta : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have h := hT.sub hdelta
  convert h using 1
  · funext n
    cases n with
    | zero => norm_num
    | succ n => simp [mul_assoc]
  · dsimp [d] at hd_pos ⊢
    have hd : 1 - 2 * x * z + z ^ 2 ≠ 0 := ne_of_gt hd_pos
    calc
      (1 - z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹ =
          2 * ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) -
            (1 - 2 * x * z + z ^ 2) * (1 - 2 * x * z + z ^ 2)⁻¹ := by ring
      _ = 2 * ((1 - x * z) * (1 - 2 * x * z + z ^ 2)⁻¹) - 1 := by
        rw [mul_inv_cancel₀ hd]

/-- **DLMF 18.12.7** — the symmetric Chebyshev first-kind generating function at
DLMF's stated strength: real `x`, complex `z` with `‖z‖ < 1`,
`(1 - z²) / (1 - 2xz + z²) = 1 + 2 ∑ n ≥ 1, Tₙ(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`); see `chebyshevU_generating_function_complex` for why the
unconstrained-`x` reading is false. `z : ℝ → z : ℂ` is the genuine relaxation DLMF's
`z : complex variable` glossary calls for.

DAG: E-18.12.7.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem chebyshevT_generating_function_symm_complex {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 2 * (Tval x n : ℂ)) * z ^ n)
      ((1 - z ^ 2) * (1 - 2 * (x : ℂ) * z + z ^ 2)⁻¹) := by
  sorry

/-- **DLMF 18.9.9** — `T_n(x) = ½(U_n(x) - U_{n-2}(x))` for `n` a nonnegative integer
and `x` real, using Mathlib's `ℤ`-indexed `Polynomial.Chebyshev.U` (via its standard
backward extension `U_{-1} = 0`, `U_{-2} = -1`) to make sense of `U_{n-2}` at `n = 0, 1`. -/
theorem chebyshevT_eq_half_U_sub (x : ℝ) (n : ℕ) :
    Tval x n = (1 / 2) * (Uval x n - (U ℝ ((n : ℤ) - 2)).eval x) := by
  have h := congrArg (Polynomial.eval x) (two_mul_T_eq_U_sub_U ℝ ((n : ℤ) - 2))
  have hn2 : (n : ℤ) - 2 + 2 = (n : ℤ) := by ring
  rw [hn2] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
  simp only [Tval, Uval]
  linarith [h]

/-- **DLMF 18.9.10**: `(1 - x²) U_n(x) = -½(T_{n+2}(x) - T_n(x))`. -/
theorem one_sub_sq_mul_U (x : ℝ) (n : ℕ) :
    (1 - x ^ 2) * Uval x n = -(1 / 2) * (Tval x (n + 2) - Tval x n) := by
  have hpol := congrArg (Polynomial.eval x) (one_sub_X_sq_mul_U_eq_pol_in_T ℝ (n : ℤ))
  have hrec := congrArg (Polynomial.eval x) (T_eq ℝ ((n : ℤ) + 2))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_ofNat] at hpol hrec
  simp only [Tval, Uval]
  push_cast at hpol hrec ⊢
  ring_nf at hpol hrec ⊢
  linarith [hpol, hrec]

end FLMF.Chebyshev

namespace FLMF.Functions.Chebyshev

-- no-dlmf: finite/telescoping partial-sum identity used as an induction stepping
-- stone toward the DLMF 18.12.10 generating function (proved separately below as
-- chebyshevU_generating_function); not itself a displayed DLMF equation.
/-- **(DLMF 18.12, second kind, finite/telescoping form).**
For every `N`, the partial generating sum of the second-kind Chebyshev polynomials
satisfies
`(1 - 2 x t + t²) · Σ_{n=0}^{N} Uₙ(x) tⁿ = 1 - U_{N+1}(x) t^{N+1} + U_N(x) t^{N+2}`.

-/
theorem secondKind_generating_partial (x t : ℝ) (N : ℕ) :
    (1 - 2 * x * t + t ^ 2) * (∑ n ∈ Finset.range (N + 1), Uval x n * t ^ n)
      = 1 - Uval x (N + 1) * t ^ (N + 1) + Uval x N * t ^ (N + 2) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one, show (0:ℕ)+1 = 1 from rfl,
        Uval_zero, Uval_one]
      ring
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hN2 : Uval x (N + 1 + 1) = 2 * x * Uval x (N + 1) - Uval x N := by
        simpa using Uval_add_two x N
      rw [hN2]
      ring

end FLMF.Functions.Chebyshev
