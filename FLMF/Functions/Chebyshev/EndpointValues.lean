import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Real.Basic

/-!
# Chebyshev polynomials: special values at the endpoints (DLMF §18.6)

DLMF §18.6 records the values of the Chebyshev polynomials of the first kind
`Tₙ` and second kind `Uₙ` at the endpoints `x = 1` and `x = -1` of the
orthogonality interval `[-1, 1]`:

* `Tₙ(1) = 1`, `Tₙ(-1) = (-1)ⁿ`;
* `Uₙ(1) = n + 1`, `Uₙ(-1) = (-1)ⁿ (n + 1)`.

Mathlib indexes the Chebyshev polynomials by `ℤ`; here we phrase the results for
the classical natural-number index `n : ℕ` (so that `(-1)ⁿ` is a genuine
ring power) and over an arbitrary commutative ring `R`.  These are thin wrappers
around the Mathlib lemmas `T_eval_one`, `T_eval_neg_one`, `U_eval_one`,
`U_eval_neg_one`.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

variable (R : Type*) [CommRing R]

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is `T_table_18_6_1` (FLMF/Functions/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the right endpoint:
`Tₙ(1) = 1` (Table 18.6.1, p_n(1) column), over an arbitrary commutative ring
`R`. -/
theorem T_eval_one_nat (n : ℕ) : (T R (n : ℤ)).eval 1 = 1 :=
  T_eval_one R (n : ℤ)

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, p_n(1) column;
-- duplicate of `T_at_one_nat` in FLMF/Functions/Chebyshev.lean); conjunction
-- carrier is `T_table_18_6_1` (FLMF/Functions/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the right endpoint:
`Tₙ(1) = 1` (Table 18.6.1, p_n(1) column), for the classical real-variable
Chebyshev polynomial (DLMF-faithful restriction of `T_eval_one_nat` to `R = ℝ`). -/
theorem T_eval_one_nat_dlmf (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 :=
  T_eval_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is `T_table_18_6_1` (FLMF/Functions/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the left endpoint:
`Tₙ(-1) = (-1)ⁿ` (Table 18.6.1: p_n(-x) row combined with p_n(1) = 1), over an
arbitrary commutative ring `R`. -/
theorem T_eval_neg_one_nat (n : ℕ) : (T R (n : ℤ)).eval (-1) = (-1 : R) ^ n := by
  have h := T_eval_neg_one R (n : ℤ)
  rw [h]
  rw [Int.coe_negOnePow]
  simp

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's T row: the parity
-- p_n(-x) = (-1)^n p_n(x) combined with p_n(1) = 1 at x = 1), not itself a table
-- entry (duplicate of `T_at_neg_one_nat` in FLMF/Functions/Chebyshev.lean);
-- conjunction carrier is `T_table_18_6_1` (FLMF/Functions/Chebyshev.lean)
/-- First-kind Chebyshev polynomial at the left endpoint:
`Tₙ(-1) = (-1)ⁿ` (Table 18.6.1: p_n(-x) row combined with p_n(1) = 1), for the
classical real-variable Chebyshev polynomial (DLMF-faithful restriction of
`T_eval_neg_one_nat` to `R = ℝ`). -/
theorem T_eval_neg_one_nat_dlmf (n : ℕ) : (T ℝ (n : ℤ)).eval (-1) = (-1 : ℝ) ^ n :=
  T_eval_neg_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is U_eval_one_nat_dlmf
/-- Second-kind Chebyshev polynomial at the right endpoint:
`Uₙ(1) = n + 1` (Table 18.6.1, p_n(1) column), over an arbitrary commutative
ring `R`. -/
theorem U_eval_one_nat (n : ℕ) : (U R (n : ℤ)).eval 1 = (n : R) + 1 := by
  have h := U_eval_one R (n : ℤ)
  rw [h]
  push_cast
  ring

/-- **(DLMF 18.6)** Second-kind Chebyshev polynomial at the right endpoint:
`Uₙ(1) = n + 1` (Table 18.6.1, p_n(1) column), for the classical real-variable
Chebyshev polynomial (DLMF-faithful restriction of `U_eval_one_nat` to `R = ℝ`).

DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_eval_one_nat_dlmf (n : ℕ) : (U ℝ (n : ℤ)).eval 1 = (n : ℝ) + 1 :=
  U_eval_one_nat ℝ n

-- no-dlmf: strictly-more-general form (arbitrary commutative ring `R`); the
-- faithful DLMF 18.6 surface is U_eval_neg_one_nat_dlmf
/-- Second-kind Chebyshev polynomial at the left endpoint:
`Uₙ(-1) = (-1)ⁿ (n + 1)` (Table 18.6.1: p_n(-x) row combined with
p_n(1) = n+1), over an arbitrary commutative ring `R`. -/
theorem U_eval_neg_one_nat (n : ℕ) :
    (U R (n : ℤ)).eval (-1) = (-1 : R) ^ n * ((n : R) + 1) := by
  have h := U_eval_neg_one R (n : ℤ)
  rw [h]
  rw [Int.coe_negOnePow]
  push_cast
  simp

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's U row: the parity
-- column p_n(-x) = (-1)^n p_n(x) evaluated at x = 1, combined with the p_n(1) = n+1
-- column), not itself a table entry — Table 18.6.1 has no p_n(-1) column. Mirrors the
-- treatment of `T_at_neg_one_nat` in FLMF/Functions/Chebyshev.lean.
/-- Second-kind Chebyshev polynomial at the left endpoint:
`Uₙ(-1) = (-1)ⁿ (n + 1)` (DLMF Table 18.6.1: p_n(-x) row combined with
p_n(1) = n+1), for the classical real-variable Chebyshev polynomial
(restriction of `U_eval_neg_one_nat` to `R = ℝ`). -/
theorem U_eval_neg_one_nat_dlmf (n : ℕ) :
    (U ℝ (n : ℤ)).eval (-1) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) :=
  U_eval_neg_one_nat ℝ n

end FLMF.Functions.Chebyshev
