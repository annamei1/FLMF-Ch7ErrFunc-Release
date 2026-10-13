import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev special values (DLMF §18.6)

We record the classical endpoint evaluations for the Chebyshev polynomials of the
first (`Tₙ`) and second (`Uₙ`) kinds.  All statements are wrappers around Mathlib
lemmas.
-/

open Polynomial
open Polynomial.Chebyshev

namespace FLMF.Functions.Chebyshev

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is firstKind_eval_one_nat
/-- the first-kind Chebyshev polynomial satisfies `Tₙ(1) = 1`
(Table 18.6.1, p_n(1) column). -/
@[simp] theorem firstKind_eval_one (n : ℤ) : (T ℝ n).eval 1 = 1 :=
  T_eval_one ℝ n

/-- **DLMF 18.6** (Table 18.6.1, p_n(1) column) — `Tₙ(1) = 1` (DLMF-faithful
restriction of `firstKind_eval_one`: `n : ℕ`).
DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem firstKind_eval_one_nat (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 :=
  firstKind_eval_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.3
-- surface is secondKind_eval_one_nat
/-- the second-kind Chebyshev polynomial satisfies `Uₙ(1) = n + 1`. -/
@[simp] theorem secondKind_eval_one (n : ℤ) : (U ℝ n).eval 1 = (n : ℝ) + 1 :=
  U_eval_one ℝ n

-- no-dlmf: duplicate of `FLMF.Functions.Chebyshev.U_at_one_nat`
-- (`FLMF/Functions/Chebyshev.lean`, tagged DLMF 18.6, tier2-verified). The
-- previous tag `18.6.3` names the Jacobi-polynomial limiting relation
-- `lim_{β→∞} P_n^{(α,β)}(x)/P_n^{(α,β)}(-1) = ((1-x)/2)ⁿ`, an unrelated
-- identity — `Uₙ(1) = n+1` is Table 18.6.1's `p_n(1)` column, already the
-- carrier's tag.
/-- `Uₙ(1) = n + 1`, `n : ℕ`. -/
theorem secondKind_eval_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval 1 = ((n : ℤ) : ℝ) + 1 :=
  secondKind_eval_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.2
-- surface is firstKind_eval_neg_one_nat
/-- the first-kind Chebyshev polynomial satisfies `Tₙ(-1) = (-1)ⁿ`. -/
@[simp] theorem firstKind_eval_neg_one (n : ℤ) : (T ℝ n).eval (-1) = n.negOnePow :=
  T_eval_neg_one ℝ n

-- no-dlmf: duplicate of `FLMF.Functions.Chebyshev.T_at_neg_one_nat`
-- (`FLMF/Functions/Chebyshev.lean`, tagged DLMF 18.6, tier2-verified). The
-- previous tag `18.6.2` names the Jacobi-polynomial limiting relation
-- `lim_{α→∞} P_n^{(α,β)}(x)/P_n^{(α,β)}(1) = ((1+x)/2)ⁿ`, an unrelated
-- identity — `Tₙ(-1) = (-1)ⁿ` is Table 18.6.1's parity column, already the
-- carrier's tag.
/-- `Tₙ(-1) = (-1)ⁿ`, `n : ℕ`. -/
theorem firstKind_eval_neg_one_nat (n : ℕ) :
    (T ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow :=
  firstKind_eval_neg_one (n : ℤ)

end FLMF.Functions.Chebyshev
