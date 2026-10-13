/-
Chebyshev minimax / equioscillation property.

Among all monic real polynomials of degree `n ≥ 1`, the scaled Chebyshev
polynomial `2^{-(n-1)} • T_n` minimizes the supremum norm on `[-1, 1]`,
and that minimal sup-norm equals `2^{-(n-1)}`.

This is the classical "minimax" property of Chebyshev polynomials,
DLMF §18.14 / approximation theory.  The key extremal input is Mathlib's
`Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one`, which says
that a polynomial of degree `≤ n` bounded by `1` on `[-1, 1]` has leading
coefficient at most `2^{n-1}`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Polynomial Real

namespace FLMF.Chebyshev

open Polynomial.Chebyshev

-- no-dlmf: packaging def (scaled monic Chebyshev polynomial) for the minimax statement.
/-- The monic Chebyshev polynomial of degree `n` (for `n ≥ 1`):
`2^{-(n-1)} • T_n`, which has leading coefficient `1`. -/
noncomputable def monicT (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ (n - 1))⁻¹ * T ℝ n

-- no-dlmf: technical degree fact about `T ℝ n`; infrastructure for the minimax proof.
lemma natDegree_T_nat (n : ℕ) : (T ℝ (n : ℤ)).natDegree = n := by
  rw [natDegree_T]; simp

-- no-dlmf: technical leading-coefficient fact; infrastructure for the minimax proof.
lemma leadingCoeff_T_nat (n : ℕ) : (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  rw [leadingCoeff_T]; simp

-- no-dlmf: technical nonvanishing fact; infrastructure for the minimax proof.
lemma T_nat_ne_zero (n : ℕ) : (T ℝ (n : ℤ)) ≠ 0 := by
  intro h
  have : (T ℝ (n : ℤ)).leadingCoeff = 0 := by rw [h]; simp
  rw [leadingCoeff_T_nat] at this
  exact (by positivity : (0:ℝ) < 2 ^ (n-1)).ne' this

-- no-dlmf: technical degree fact; infrastructure for the minimax proof.
lemma degree_T_nat (n : ℕ) : (T ℝ (n : ℤ)).degree = (n : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (T_nat_ne_zero n), natDegree_T_nat]

-- no-dlmf: structural property of the packaging def `monicT`; not a DLMF identity.
/-- `monicT n` is monic. -/
theorem monic_monicT (n : ℕ) : (monicT n).Monic := by
  unfold monicT Polynomial.Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T_nat]
  field_simp

-- no-dlmf: structural property of the packaging def `monicT`; not a DLMF identity.
/-- `monicT n` has degree `n`. -/
theorem natDegree_monicT (n : ℕ) : (monicT n).natDegree = n := by
  unfold monicT
  have hc : ((2 : ℝ) ^ (n - 1))⁻¹ ≠ 0 := by positivity
  rw [natDegree_C_mul hc, natDegree_T_nat]

-- no-dlmf: technical sup-norm bound for `monicT`; one half of the minimax proof, not a DLMF eqn.
/-- The supremum-norm bound: `|monicT n (x)| ≤ 2^{-(n-1)}` for `x ∈ [-1,1]`. -/
theorem abs_eval_monicT_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(monicT n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹ := by
  unfold monicT
  rw [eval_mul, eval_C, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2:ℝ)^(n-1))⁻¹)]
  have hT : |(T ℝ (n:ℤ)).eval x| ≤ 1 := by
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨θ, hθ⟩ : ∃ θ, Real.cos θ = x := ⟨Real.arccos x, Real.cos_arccos hx1 hx2⟩
    rw [← hθ, T_real_cos]
    exact Real.abs_cos_le_one _
  calc ((2:ℝ)^(n-1))⁻¹ * |(T ℝ (n:ℤ)).eval x|
      ≤ ((2:ℝ)^(n-1))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left hT (by positivity)
    _ = ((2:ℝ)^(n-1))⁻¹ := by ring

/-- **Chebyshev minimax (lower bound).**  Any monic real polynomial `P` of degree `n ≥ 1`
attains absolute value at least `2^{-(n-1)}` somewhere on `[-1, 1]`. -/
theorem exists_abs_eval_ge_of_monic {n : ℕ} (hn : 1 ≤ n) {P : ℝ[X]}
    (hPmonic : P.Monic) (hPdeg : P.natDegree = n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |P.eval x| := by
  by_contra h
  push_neg at h
  set Q : ℝ[X] := C ((2 : ℝ) ^ (n - 1)) * P with hQ
  have hQdeg : Q.degree ≤ n := by
    have hc : ((2:ℝ)^(n-1)) ≠ 0 := by positivity
    rw [hQ, degree_C_mul hc]
    rw [Polynomial.degree_eq_natDegree hPmonic.ne_zero, hPdeg]
  have hQbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1 := by
    intro x hx
    rw [hQ, eval_mul, eval_C, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^(n-1))]
    have := h x hx
    have hlt : (2:ℝ)^(n-1) * |P.eval x| < (2:ℝ)^(n-1) * ((2:ℝ)^(n-1))⁻¹ :=
      mul_lt_mul_of_pos_left this (by positivity)
    rw [mul_inv_cancel₀ (by positivity : ((2:ℝ)^(n-1)) ≠ 0)] at hlt
    exact le_of_lt hlt
  have hQlc : Q.leadingCoeff = (2:ℝ)^(n-1) := by
    rw [hQ, leadingCoeff_mul, leadingCoeff_C, hPmonic.leadingCoeff, mul_one]
  by_cases hn2 : 2 ≤ n
  · -- equality case via `leadingCoeff_eq_iff`
    have hQT : Q = T ℝ (n : ℤ) :=
      (leadingCoeff_eq_iff_of_forall_abs_le_one hn2 hQdeg hQbnd).mp (by rw [hQlc])
    have hnode0 : node n 0 ∈ Set.Icc (-1:ℝ) 1 := node_mem_Icc
    have horig := h (node n 0) hnode0
    have hPval : P.eval (node n 0) = ((2:ℝ)^(n-1))⁻¹ := by
      have hQe : Q.eval (node n 0) = (2:ℝ)^(n-1) * P.eval (node n 0) := by
        rw [hQ, eval_mul, eval_C]
      rw [hQT, eval_T_real_node (by simp)] at hQe
      simp only [pow_zero] at hQe
      have hc : ((2:ℝ)^(n-1)) ≠ 0 := by positivity
      field_simp at hQe ⊢
      linarith [hQe]
    rw [hPval, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2:ℝ)^(n-1))⁻¹)] at horig
    exact (lt_irrefl _ horig)
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    simp only [Nat.sub_self, pow_zero, inv_one] at h
    have hPeq : P = X + C (P.coeff 0) := by
      ext k
      rcases k with _ | _ | k
      · simp [coeff_X, coeff_C]
      · have hc1 : P.coeff 1 = 1 := by
          have := hPmonic.leadingCoeff
          rw [leadingCoeff, hPdeg] at this; simpa using this
        simp [coeff_X, hc1]
      · have hck : P.coeff (k+2) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hPdeg]; omega
        simp [coeff_X, hck]
    have hP1 : P.eval 1 - P.eval (-1) = 2 := by
      rw [hPeq]; simp; ring
    have h1 := h 1 (by constructor <;> norm_num)
    have h2 := h (-1) (by constructor <;> norm_num)
    have htri : |P.eval 1 - P.eval (-1)| ≤ |P.eval 1| + |P.eval (-1)| := abs_sub _ _
    rw [hP1] at htri; rw [abs_of_pos (by norm_num : (0:ℝ) < 2)] at htri
    linarith

/-- **Chebyshev minimax / equioscillation theorem.**

For `n ≥ 1`, the scaled Chebyshev polynomial `monicT n = 2^{-(n-1)} T_n` is a monic
polynomial of degree `n` whose supremum norm on `[-1, 1]` is `2^{-(n-1)}`, and no monic
polynomial of degree `n` has a strictly smaller maximal absolute value on `[-1, 1]`:
every such polynomial attains absolute value at least `2^{-(n-1)}` somewhere on `[-1, 1]`,
while `monicT n` never exceeds it.  Thus `monicT n` is the minimax monic polynomial. -/
theorem isMinimax {n : ℕ} (hn : 1 ≤ n) :
    (monicT n).Monic ∧ (monicT n).natDegree = n ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(monicT n).eval x| ≤ ((2 : ℝ) ^ (n - 1))⁻¹) ∧
    (∀ P : ℝ[X], P.Monic → P.natDegree = n →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1, ((2 : ℝ) ^ (n - 1))⁻¹ ≤ |P.eval x|) := by
  refine ⟨monic_monicT n, natDegree_monicT n, ?_, ?_⟩
  · intro x hx; exact abs_eval_monicT_le hx
  · intro P hPm hPd; exact exists_abs_eval_ge_of_monic hn hPm hPd

end FLMF.Chebyshev
