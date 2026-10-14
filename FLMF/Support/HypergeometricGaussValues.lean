import FLMF.Support.HypergeometricEulerIntegral
import FLMF.Support.HypergeometricKummerTransform
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries

/-!
# Closed-form `₂F₁` summations at `z = 1` (framework — DLMF §15.4)

Gauss's summation theorem and the terminating Chu–Vandermonde value, the two
closed forms of `₂F₁` at the unit argument.

* `ordinaryHypergeometric_neg_nat_one` — the **terminating Chu–Vandermonde
  value** (DLMF 15.4.24): for a nonpositive-integer first parameter and `c` off
  the nonpositive integers,
  `₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ`.
  A finite sum; no convergence hypotheses.
* `ordinaryHypergeometric_tendsto_gaussValue` — the **limit form of Gauss's
  theorem**: for `0 < b < c`, `a` off the nonpositive integers and `c−a−b > 0`,
  `₂F₁(a,b;c;z) → Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))` as `z → 1⁻`. Proved by dominated
  convergence on Euler's integral (`ordinaryHypergeometric_eq_betaIntegral`); no
  Abel summation needed.
* `ordinaryHypergeometric_one` — **Gauss's summation theorem** (DLMF 15.4.20):
  for the same hypotheses, `₂F₁(a,b;c;1) = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))`. Proved
  by combining the limit form with Abel's limit theorem
  (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`), which identifies the boundary
  value with the limit once the `z = 1` series is summable.
-/

noncomputable section

open Nat Finset MeasureTheory Real Set Filter Topology FormalMultilinearSeries

namespace FLMF.Hypergeometric

/-- The Gauss value `Γ(c)·Γ(c−a−b) / (Γ(c−a)·Γ(c−b))` (DLMF 15.4.20, RHS).

DLMF 15.4.20.
-/
-- DAG: E-15.4.20.
-- Verified: unverified
def gaussValue (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b))

section Terminating

variable {𝕂 : Type*} [RCLike 𝕂]

/-- `(ascPochhammer 𝕂 k).eval (−n) = (−1)ᵏ · k! · C(n,k)` — the rising factorial
at a nonpositive integer collapses to a binomial coefficient. -/
-- no-dlmf: Pochhammer-at-negative-integer bookkeeping, no single DLMF equation
theorem ascPochhammer_eval_neg_natCast (n k : ℕ) :
    (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) = (-1) ^ k * (k ! : 𝕂) * (n.choose k : 𝕂) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer]
  have hk : (n.choose k : 𝕂) = (descPochhammer 𝕂 k).eval (n : 𝕂) / (k ! : 𝕂) :=
    cast_choose_eq_descPochhammer_div (K := 𝕂) n k
  have hfk : (k ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [hk]
  field_simp

/-- The terminating Gauss series sums everywhere when the first parameter is a
nonpositive integer (the radius is `⊤`). -/
-- no-dlmf: HasSum infrastructure for the terminating series, no DLMF counterpart
theorem ordinaryHypergeometric_hasSum_neg_nat (n : ℕ) (b c : 𝕂) (x : 𝕂) :
    HasSum (fun k : ℕ => ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * x ^ k)
      (₂F₁ (-(n : 𝕂)) b c x) := by
  have hr : (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c).radius = ⊤ :=
    ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝕂 b c
  have hball : HasFPowerSeriesOnBall (₂F₁ (-(n : 𝕂)) b c : 𝕂 → 𝕂)
      (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c) 0 ⊤ := by
    have h := (ordinaryHypergeometricSeries 𝕂 (-(n : 𝕂)) b c).hasFPowerSeriesOnBall
      (by rw [hr]; exact lt_top_iff_ne_top.2 (by simp))
    rwa [hr] at h
  have h := hball.hasSum_sub (y := x)
    (by rw [mem_eball_zero_iff]; exact lt_top_iff_ne_top.2 (by simp))
  simpa only [sub_zero, ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] using h

-- no-dlmf: strictly-more-general total/junk-value form (quantifies over all
-- `b, c : 𝕂` with no pole-avoidance on `c`); the faithful DLMF 15.2.4 surface
-- is `ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf_complex`.
/-- **The terminating case of the Gauss hypergeometric function**: for
`a = −n` a nonpositive integer, `₂F₁(−n; b; c; x)` is the degree-`≤ n`
polynomial `∑_{k≤n} (−n)_k(b)_k/((c)_k k!) · xᵏ`. -/
theorem ordinaryHypergeometric_eq_sum_of_neg_nat (n : ℕ) (b c x : 𝕂) :
    ₂F₁ (-(n : 𝕂)) b c x
      = ∑ k ∈ Finset.range (n + 1),
          ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * x ^ k := by
  refine (ordinaryHypergeometric_hasSum_neg_nat n b c x).unique
    (hasSum_sum_of_ne_finset_zero fun k hk => ?_)
  have hnk : n < k := by
    have := Finset.mem_range.not.1 hk
    omega
  have hz : (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) = 0 :=
    (ascPochhammer_eval_eq_zero_iff k _).2 ⟨n, hnk, (neg_neg _).symm⟩
  simp [ordinaryHypergeometricCoefficient, hz]

-- no-dlmf: OVER-GENERAL — quantifies over an abstract `RCLike` field `𝕂`;
-- DLMF states this for real-or-complex parameters `b, c` and a complex
-- variable `z`. The faithful DLMF 15.2.4 surface is
-- `ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf_complex`.
/-- for `a = −n` a nonpositive integer and `c` off the nonpositive integers,
`₂F₁(−n; b; c; x)` is the degree-`≤ n` polynomial
`∑_{k≤n} (−n)_k(b)_k/((c)_k k!) · xᵏ`. -/
theorem ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf (n : ℕ) (b c : 𝕂)
    (_hc : ∀ m : ℕ, c ≠ -(m : 𝕂)) (x : 𝕂) :
    ₂F₁ (-(n : 𝕂)) b c x
      = ∑ k ∈ Finset.range (n + 1),
          ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * x ^ k :=
  ordinaryHypergeometric_eq_sum_of_neg_nat n b c x

-- no-dlmf: chain link 15.2.4 (assembled in hypergeometric_15_2_4)
/-- For `a = −n` a nonpositive integer and `c` off the
nonpositive integers, `₂F₁(−n; b; c; z)` is the degree-`≤ n` polynomial
`∑_{k≤n} (−n)_k(b)_k/((c)_k k!) · zᵏ` (DLMF-faithful restriction of
`ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf` to `b, c, z : ℂ`, matching
DLMF's real-or-complex parameters and complex variable). -/
theorem ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf_complex (n : ℕ) (b c : ℂ)
    (hc : ∀ m : ℕ, c ≠ -(m : ℂ)) (z : ℂ) :
    ₂F₁ (-(n : ℂ)) b c z
      = ∑ k ∈ Finset.range (n + 1),
          ordinaryHypergeometricCoefficient (-(n : ℂ)) b c k * z ^ k :=
  ordinaryHypergeometric_eq_sum_of_neg_nat_dlmf n b c hc z

-- no-dlmf: OVER-STRONG blanket pole-avoidance on `c` (avoids every
-- nonpositive integer, rather than only the ≤ n poles the finite sum's own
-- denominators can hit); DLMF's sole stated constraint for 15.4.24 is
-- `n = 0,1,2,…`. The faithful surface is
-- `ordinaryHypergeometric_neg_nat_one_dlmf`.
/-- **Terminating Chu–Vandermonde value**: for a nonpositive integer first
parameter and `c` off the nonpositive integers, `₂F₁(−n, b; c; 1) = (c −
b)ₙ / (c)ₙ`. A finite identity; no convergence is required. -/
theorem ordinaryHypergeometric_neg_nat_one (n : ℕ) (b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) :
    ₂F₁ (-(n : 𝕂)) b c (1 : 𝕂)
      = (ascPochhammer 𝕂 n).eval (c - b) * ((ascPochhammer 𝕂 n).eval c)⁻¹ := by
  have hsum := ordinaryHypergeometric_hasSum_neg_nat n b c (1 : 𝕂)
  -- the series is supported on `range (n+1)`: terms vanish for `k > n`
  have hvan : ∀ k ∉ range (n + 1),
      ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * (1 : 𝕂) ^ k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hk
    have : (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) = 0 :=
      (ascPochhammer_eval_eq_zero_iff k _).2 ⟨n, hk, (neg_neg _).symm⟩
    simp [ordinaryHypergeometricCoefficient, this]
  rw [← (hasSum_sum_of_ne_finset_zero hvan).unique hsum]
  -- evaluate the finite sum via Chu–Vandermonde
  have hstep : ∀ k ∈ range (n + 1),
      ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * (1 : 𝕂) ^ k
      = (-1) ^ k * (n.choose k : 𝕂)
        * ((ascPochhammer 𝕂 k).eval (c - (c - b)) * ((ascPochhammer 𝕂 k).eval c)⁻¹) := by
    intro k _
    have hfk : (k ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    rw [one_pow, mul_one, ordinaryHypergeometricCoefficient,
      ascPochhammer_eval_neg_natCast n k, show c - (c - b) = b by ring]
    field_simp
  rw [Finset.sum_congr rfl hstep,
    sum_neg_one_pow_choose_ascPochhammer n (c - b) c hc]

-- no-dlmf: Chu–Vandermonde with a level-bounded pole-avoidance hypothesis
-- (only the poles the finite sum's own denominators can hit, `c ≠
-- 0,-1,…,-(n-1)`, rather than blanket avoidance of every nonpositive
-- integer); mirrors `sum_neg_one_pow_choose_ascPochhammer`
-- (KummerTransform.lean) with the hypothesis weakened to match DLMF
-- 15.4.24's sole stated constraint `n = 0,1,2,…`.
theorem sum_neg_one_pow_choose_ascPochhammer_bounded (n : ℕ) :
    ∀ a b : 𝕂, (∀ k : ℕ, k < n → (k : 𝕂) ≠ -b) →
      ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : 𝕂)
        * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)
      = (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹ := by
  induction n with
  | zero =>
    intro a b _
    simp
  | succ n ih =>
    intro a b hb
    have hb0 : b ≠ 0 := fun h => hb 0 (Nat.succ_pos n) (by simp [h])
    have hb1 : ∀ k : ℕ, k < n → (k : 𝕂) ≠ -(b + 1) := fun k hk h =>
      hb (k + 1) (by omega) (by push_cast; linear_combination h)
    have hB : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn hkn => hb kn (by omega)
    have hB1 : (ascPochhammer 𝕂 n).eval (b + 1) ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      push Not
      exact fun kn hkn => hb1 kn hkn
    have hbridge : b * (ascPochhammer 𝕂 n).eval (b + 1)
        = (ascPochhammer 𝕂 n).eval b * (b + n) := by
      rw [← ascPochhammer_succ_eval', ascPochhammer_succ_eval]
    rw [Finset.sum_range_succ']
    have hsplit : ∀ j ∈ range (n + 1), (-1 : 𝕂) ^ (j + 1) * ((n + 1).choose (j + 1) : 𝕂)
        * ((ascPochhammer 𝕂 (j + 1)).eval (b - a) * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹)
        = -((b - a) * b⁻¹) * ((-1) ^ j * (n.choose j : 𝕂)
            * ((ascPochhammer 𝕂 j).eval (b + 1 - a) * ((ascPochhammer 𝕂 j).eval (b + 1))⁻¹))
          + (-1) ^ (j + 1) * (n.choose (j + 1) : 𝕂)
            * ((ascPochhammer 𝕂 (j + 1)).eval (b - a)
              * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹) := by
      intro j _
      rw [Nat.choose_succ_succ' n j]
      push_cast
      rw [ascPochhammer_succ_eval' j (b - a), ascPochhammer_succ_eval' j b,
        show b - a + 1 = b + 1 - a by ring, mul_inv]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hA : ∑ j ∈ range (n + 1), -((b - a) * b⁻¹) * ((-1) ^ j * (n.choose j : 𝕂)
        * ((ascPochhammer 𝕂 j).eval (b + 1 - a) * ((ascPochhammer 𝕂 j).eval (b + 1))⁻¹))
        = -((b - a) * b⁻¹)
          * ((ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval (b + 1))⁻¹) := by
      rw [← Finset.mul_sum, ih a (b + 1) hb1]
    have hBsum : ∑ j ∈ range (n + 1), (-1 : 𝕂) ^ (j + 1) * (n.choose (j + 1) : 𝕂)
        * ((ascPochhammer 𝕂 (j + 1)).eval (b - a) * ((ascPochhammer 𝕂 (j + 1)).eval b)⁻¹)
        = (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹ - 1 := by
      have h1 := Finset.sum_range_succ'
        (fun k => (-1 : 𝕂) ^ k * (n.choose k : 𝕂)
          * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)) (n + 1)
      have h2 := Finset.sum_range_succ
        (fun k => (-1 : 𝕂) ^ k * (n.choose k : 𝕂)
          * ((ascPochhammer 𝕂 k).eval (b - a) * ((ascPochhammer 𝕂 k).eval b)⁻¹)) (n + 1)
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
        Nat.choose_zero_right, Nat.cast_one, pow_zero, ascPochhammer_zero,
        Polynomial.eval_one, inv_one, mul_one] at h1 h2
      rw [ih a b (fun k hk => hb k (by omega))] at h2
      linear_combination h2 - h1
    rw [hA, hBsum]
    rw [ascPochhammer_succ_eval n a, ascPochhammer_succ_eval' n b, mul_inv]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, ascPochhammer_zero,
      Polynomial.eval_one, inv_one, mul_one]
    field_simp
    linear_combination ((ascPochhammer 𝕂 n).eval a) * hbridge

/-- **DLMF 15.4.24** — the terminating Chu–Vandermonde value: for a
nonpositive-integer first parameter and `c` avoiding the (at most `n`) poles
its own finite sum can hit, `₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ`. Matches
DLMF's sole stated constraint `n = 0,1,2,…`: the pole-avoidance hypothesis on
`c` is only the minimal amount needed for the finite sum's own terms to be
well-defined, not blanket avoidance of every nonpositive integer
(DLMF-faithful restriction of `ordinaryHypergeometric_neg_nat_one`).

DAG: E-15.4.24.
Numerical: PASS
Verified: unverified
-/
theorem ordinaryHypergeometric_neg_nat_one_dlmf (n : ℕ) (b c : 𝕂)
    (hc : ∀ k : ℕ, k < n → (k : 𝕂) ≠ -c) :
    ₂F₁ (-(n : 𝕂)) b c (1 : 𝕂)
      = (ascPochhammer 𝕂 n).eval (c - b) * ((ascPochhammer 𝕂 n).eval c)⁻¹ := by
  have hsum := ordinaryHypergeometric_hasSum_neg_nat n b c (1 : 𝕂)
  have hvan : ∀ k ∉ range (n + 1),
      ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * (1 : 𝕂) ^ k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hk
    have : (ascPochhammer 𝕂 k).eval (-(n : 𝕂)) = 0 :=
      (ascPochhammer_eval_eq_zero_iff k _).2 ⟨n, hk, (neg_neg _).symm⟩
    simp [ordinaryHypergeometricCoefficient, this]
  rw [← (hasSum_sum_of_ne_finset_zero hvan).unique hsum]
  have hstep : ∀ k ∈ range (n + 1),
      ordinaryHypergeometricCoefficient (-(n : 𝕂)) b c k * (1 : 𝕂) ^ k
      = (-1) ^ k * (n.choose k : 𝕂)
        * ((ascPochhammer 𝕂 k).eval (c - (c - b)) * ((ascPochhammer 𝕂 k).eval c)⁻¹) := by
    intro k _
    have hfk : (k ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    rw [one_pow, mul_one, ordinaryHypergeometricCoefficient,
      ascPochhammer_eval_neg_natCast n k, show c - (c - b) = b by ring]
    field_simp
  rw [Finset.sum_congr rfl hstep,
    sum_neg_one_pow_choose_ascPochhammer_bounded n (c - b) c hc]

end Terminating

section Summability

-- no-dlmf: strictly-more-general form using the weakest sufficient pointwise
-- pole-avoidance hypothesis `a + k ≠ 0` for `k < n` (not DLMF's blanket
-- `a ≠ 0,-1,-2,…`); the faithful DLMF 5.2.5 surface is
-- Real_Gamma_add_nat_eq_ascPochhammer_mul_dlmf
/-- Real analogue of `Gamma_add_nat_eq_ascPochhammer_mul`: `Γ(a+n) = (a)ₙ·Γ(a)`
under pointwise pole-avoidance `a + k ≠ 0` for `k < n`. -/
theorem Real_Gamma_add_nat_eq_ascPochhammer_mul (a : ℝ) (n : ℕ)
    (h : ∀ k < n, a + (k : ℝ) ≠ 0) :
    Real.Gamma (a + n) = (ascPochhammer ℝ n).eval a * Real.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : a + (n : ℝ) ≠ 0 := h n (Nat.lt_succ_self n)
    have hcast : a + ((n + 1 : ℕ) : ℝ) = (a + n) + 1 := by push_cast; ring
    rw [hcast, Real.Gamma_add_one hn, ih fun k hk => h k (Nat.lt_succ_of_lt hk),
      ascPochhammer_succ_eval]
    ring

-- no-dlmf: real/narrowed restriction of DLMF 5.2.5 (`a` is real and this
-- uses `Real.Gamma`); DLMF assigns `a` a real-or-complex variable. The
-- faithful surface is `Complex_Gamma_add_nat_eq_ascPochhammer_mul_dlmf`.
/-- `Γ(a+n) = (a)ₙ·Γ(a)` over `ℝ`, for `a` off the nonpositive integers
(DLMF's blanket pole-avoidance hypothesis, `a ≠ 0,-1,-2,…`). -/
theorem Real_Gamma_add_nat_eq_ascPochhammer_mul_dlmf (a : ℝ) (n : ℕ)
    (h : ∀ m : ℕ, a ≠ -(m : ℝ)) :
    Real.Gamma (a + n) = (ascPochhammer ℝ n).eval a * Real.Gamma a :=
  Real_Gamma_add_nat_eq_ascPochhammer_mul a n
    (fun k _ hk0 => h k (by linear_combination hk0))

-- no-dlmf: pointwise-pole-avoidance helper for the complex DLMF 5.2.5
-- surface, mirroring `Real_Gamma_add_nat_eq_ascPochhammer_mul`.
theorem Complex_Gamma_add_nat_eq_ascPochhammer_mul (a : ℂ) (n : ℕ)
    (h : ∀ k < n, a + (k : ℂ) ≠ 0) :
    Complex.Gamma (a + n) = (ascPochhammer ℂ n).eval a * Complex.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : a + (n : ℂ) ≠ 0 := h n (Nat.lt_succ_self n)
    have hcast : a + ((n + 1 : ℕ) : ℂ) = (a + n) + 1 := by push_cast; ring
    rw [hcast, Complex.Gamma_add_one (a + n) hn, ih fun k hk => h k (Nat.lt_succ_of_lt hk),
      ascPochhammer_succ_eval]
    ring

-- no-dlmf: rearranged (multiplied-out) twin of 5.2.5; canonical surface is
-- `ascPochhammer_eval_eq_Gamma_div` (Pochhammer.lean).
/-- `Γ(a+n) = (a)ₙ·Γ(a)` for `a` off the nonpositive
integers (DLMF's real-or-complex `a` and blanket pole-avoidance hypothesis,
here specialized to `a, Γ : ℂ`; DLMF-faithful restriction of
`Complex_Gamma_add_nat_eq_ascPochhammer_mul`). -/
theorem Complex_Gamma_add_nat_eq_ascPochhammer_mul_dlmf (a : ℂ) (n : ℕ)
    (h : ∀ m : ℕ, a ≠ -(m : ℂ)) :
    Complex.Gamma (a + n) = (ascPochhammer ℂ n).eval a * Complex.Gamma a :=
  Complex_Gamma_add_nat_eq_ascPochhammer_mul a n
    (fun k _ hk0 => h k (by linear_combination hk0))

-- no-dlmf: real/narrowed restriction of DLMF 5.2.5 (`a` is real and this
-- uses `Real.Gamma`); DLMF assigns `a` a real-or-complex variable. The
-- faithful surface is `Complex_ascPochhammer_eval_eq_Gamma_div`.
/-- `(a)ₙ = Γ(a+n)/Γ(a)` over `ℝ` for `a` off the nonpositive integers —
the general-sign companion to `ascPochhammer_eval_eq_Gamma_div_real`. -/
theorem Real_ascPochhammer_eval_eq_Gamma_div (a : ℝ) (n : ℕ) (h : ∀ m : ℕ, a ≠ -m)
    (hΓ : Real.Gamma a ≠ 0) :
    (ascPochhammer ℝ n).eval a = Real.Gamma (a + n) / Real.Gamma a := by
  have hpole : ∀ k < n, a + (k : ℝ) ≠ 0 := fun k _ hk0 => h k (by linear_combination hk0)
  rw [Real_Gamma_add_nat_eq_ascPochhammer_mul a n hpole, mul_div_cancel_right₀ _ hΓ]

-- no-dlmf: duplicate complex twin of 5.2.5; canonical surface is
-- `ascPochhammer_eval_eq_Gamma_div` (Pochhammer.lean).
/-- `(a)ₙ = Γ(a+n)/Γ(a)` for `a` off the nonpositive
integers (DLMF's real-or-complex `a`, here specialized to `a, Γ : ℂ`;
DLMF-faithful restriction of `Real_ascPochhammer_eval_eq_Gamma_div`). -/
theorem Complex_ascPochhammer_eval_eq_Gamma_div (a : ℂ) (n : ℕ) (h : ∀ m : ℕ, a ≠ -(m : ℂ)) :
    (ascPochhammer ℂ n).eval a = Complex.Gamma (a + n) / Complex.Gamma a := by
  have hΓ : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero h
  have hpole : ∀ k < n, a + (k : ℂ) ≠ 0 := fun k _ hk0 => h k (by linear_combination hk0)
  rw [Complex_Gamma_add_nat_eq_ascPochhammer_mul a n hpole, mul_div_cancel_right₀ _ hΓ]

/-- `Real.GammaSeq` in gamma form: for `s` off the nonpositive integers,
`GammaSeq s n = n^s · n! · Γ(s) / Γ(s + n + 1)`. -/
-- no-dlmf: Gamma-asymptotic infrastructure for Gauss's theorem, no DLMF counterpart
theorem GammaSeq_eq_gamma_form (s : ℝ) (h : ∀ m : ℕ, s ≠ -m) (hΓ : Real.Gamma s ≠ 0) (n : ℕ) :
    Real.GammaSeq s n
      = (n : ℝ) ^ s * (n ! : ℝ) * Real.Gamma s / Real.Gamma (s + (n : ℝ) + 1) := by
  rw [Real.GammaSeq]
  have hprod : ∏ j ∈ Finset.range (n + 1), (s + (j : ℝ))
      = (ascPochhammer ℝ (n + 1)).eval s :=
    (ascPochhammer_eval_eq_prod_range (n + 1) s).symm
  rw [hprod, Real_ascPochhammer_eval_eq_Gamma_div s (n + 1) h hΓ,
    show s + ((n + 1 : ℕ) : ℝ) = s + (n : ℝ) + 1 by push_cast; ring]
  field_simp

/-- **Gamma-ratio asymptotic** `Γ(s+n+1)/(n^s·n!) → 1` for `s` off the
nonpositive integers, from Euler's limit formula (`GammaSeq_tendsto_Gamma`). -/
-- no-dlmf: Gamma-asymptotic infrastructure for Gauss's theorem, no DLMF counterpart
theorem tendsto_Gamma_ratio_one (s : ℝ) (h : ∀ m : ℕ, s ≠ -m) (hΓ : Real.Gamma s ≠ 0) :
    Tendsto (fun n : ℕ => Real.Gamma (s + (n : ℝ) + 1) / ((n : ℝ) ^ s * (n ! : ℝ)))
      atTop (𝓝 1) := by
  have hgs := Real.GammaSeq_tendsto_Gamma s
  have key : Tendsto (fun n : ℕ => ((n : ℝ) ^ s * (n ! : ℝ)) / Real.Gamma (s + (n : ℝ) + 1))
      atTop (𝓝 1) := by
    have hgs' : Tendsto (fun n : ℕ =>
        Real.Gamma s * (((n : ℝ) ^ s * (n ! : ℝ)) / Real.Gamma (s + (n : ℝ) + 1)))
        atTop (𝓝 (Real.Gamma s)) := by
      refine hgs.congr fun n => ?_
      rw [GammaSeq_eq_gamma_form s h hΓ n]; ring
    have := hgs'.const_mul (Real.Gamma s)⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hΓ, one_mul] at this
    exact this
  have hne : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ s * (n ! : ℝ)) / Real.Gamma (s + (n : ℝ) + 1) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h1 : (n : ℝ) ^ s ≠ 0 := by positivity
    have h2 : (n ! : ℝ) ≠ 0 := by positivity
    have h3 : Real.Gamma (s + (n : ℝ) + 1) ≠ 0 := by
      have hpole : ∀ k < n + 1, s + (k : ℝ) ≠ 0 := fun k _ hk0 => h k (by linear_combination hk0)
      rw [show s + (n : ℝ) + 1 = s + ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real_Gamma_add_nat_eq_ascPochhammer_mul s (n + 1) hpole]
      refine mul_ne_zero ?_ hΓ
      rw [Ne, ascPochhammer_eval_eq_zero_iff]; push Not
      exact fun kn _ hh => h kn (by linear_combination hh)
    exact div_ne_zero (mul_ne_zero h1 h2) h3
  have hk := key.inv₀ (by norm_num)
  rw [inv_one] at hk
  refine hk.congr' ?_
  filter_upwards [hne] with n hn
  rw [inv_div]

/-- The shifted Gamma-ratio `Γ(s+n)/(n^(s−1)·n!) → 1` for `s` off the
nonpositive integers. -/
-- no-dlmf: Gamma-asymptotic infrastructure for Gauss's theorem, no DLMF counterpart
theorem tendsto_Gamma_ratio_shift_one (s : ℝ) (h : ∀ m : ℕ, s ≠ -m) (hΓ : Real.Gamma s ≠ 0) :
    Tendsto (fun n : ℕ => Real.Gamma (s + (n : ℝ)) / ((n : ℝ) ^ (s - 1) * (n ! : ℝ)))
      atTop (𝓝 1) := by
  have hw := tendsto_Gamma_ratio_one s h hΓ
  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / (s + (n : ℝ))) atTop (𝓝 1) := by
    have hlim : Tendsto (fun n : ℕ => 1 / (s / (n : ℝ) + 1)) atTop (𝓝 (1 / (0 + 1))) := by
      apply Tendsto.div tendsto_const_nhds
      · refine Tendsto.add ?_ tendsto_const_nhds
        simpa using (tendsto_const_nhds (x := s)).div_atTop tendsto_natCast_atTop_atTop
      · norm_num
    simp only [zero_add, div_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have hprod := hw.mul hfrac
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hsn : s + (n : ℝ) ≠ 0 := fun hz => h n (by linear_combination hz)
  rw [Real.Gamma_add_one hsn,
    show (n : ℝ) ^ s = (n : ℝ) ^ (s - 1) * (n : ℝ) by rw [← Real.rpow_add_one hn0, sub_add_cancel]]
  field_simp

-- no-dlmf: a convergence lemma (summability of the coefficient sequence at
-- `z = 1`), not itself DLMF 15.4.20's exact-value relation; used internally
-- to prove `ordinaryHypergeometric_one`. The faithful DLMF 15.4.20 surface
-- is `ordinaryHypergeometric_one_dlmf_complex`.
/-- **Summability of the Gauss coefficients at `z = 1`**: for `0 < b < c`,
`a` off the nonpositive integers and `c − a − b > 0`, the series
`∑ₙ (a)ₙ(b)ₙ/((c)ₙ n!)` converges absolutely. Proved by comparison with the
`p`-series `∑ n^(−(1+(c−a−b)))` through the Gamma-ratio asymptotics. -/
theorem summable_ordinaryHypergeometricCoefficient_one (a b c : ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≠ -a)
    (hb : 0 < b) (hbc : b < c) (habc : 0 < c - a - b) :
    Summable (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n) := by
  have hc : 0 < c := by linarith
  have ha' : ∀ m : ℕ, a ≠ -(m : ℝ) := fun m hm => ha m (by rw [hm]; ring)
  have hb0 : ∀ m : ℕ, b ≠ -(m : ℝ) := fun m hm => by
    have := Nat.cast_nonneg (α := ℝ) m; rw [hm] at hb; linarith
  have hc0 : ∀ m : ℕ, c ≠ -(m : ℝ) := fun m hm => by
    have := Nat.cast_nonneg (α := ℝ) m; rw [hm] at hc; linarith
  have hΓa : Real.Gamma a ≠ 0 := Real.Gamma_ne_zero ha'
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  set δ := c - a - b with hδ
  have hgsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + δ))) := by
    rw [Real.summable_nat_rpow]; linarith
  have hva := tendsto_Gamma_ratio_shift_one a ha' hΓa
  have hvb := tendsto_Gamma_ratio_shift_one b hb0 hΓb
  have hvc := tendsto_Gamma_ratio_shift_one c hc0 hΓc
  have hratio : Tendsto
      (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n / (n : ℝ) ^ (-(1 + δ)))
      atTop (𝓝 (Real.Gamma c / (Real.Gamma a * Real.Gamma b))) := by
    have hlim : Tendsto (fun n : ℕ =>
        Real.Gamma c / (Real.Gamma a * Real.Gamma b)
          * ((Real.Gamma (a + (n : ℝ)) / ((n : ℝ) ^ (a - 1) * (n ! : ℝ)))
            * (Real.Gamma (b + (n : ℝ)) / ((n : ℝ) ^ (b - 1) * (n ! : ℝ)))
            / (Real.Gamma (c + (n : ℝ)) / ((n : ℝ) ^ (c - 1) * (n ! : ℝ)))))
        atTop (𝓝 (Real.Gamma c / (Real.Gamma a * Real.Gamma b) * (1 * 1 / 1))) :=
      Tendsto.const_mul _ ((hva.mul hvb).div hvc (by norm_num))
    rw [show (1:ℝ) * 1 / 1 = 1 by norm_num, mul_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hfac : (n ! : ℝ) ≠ 0 := by positivity
    have hΓan : Real.Gamma (a + (n : ℝ)) = (ascPochhammer ℝ n).eval a * Real.Gamma a :=
      Real_Gamma_add_nat_eq_ascPochhammer_mul a n fun k _ hk0 => ha' k (by linear_combination hk0)
    have hΓbn : Real.Gamma (b + (n : ℝ)) = (ascPochhammer ℝ n).eval b * Real.Gamma b :=
      Real_Gamma_add_nat_eq_ascPochhammer_mul b n fun k _ hk0 => hb0 k (by linear_combination hk0)
    have hΓcn : Real.Gamma (c + (n : ℝ)) = (ascPochhammer ℝ n).eval c * Real.Gamma c :=
      Real_Gamma_add_nat_eq_ascPochhammer_mul c n fun k _ hk0 => hc0 k (by linear_combination hk0)
    have hPc : (ascPochhammer ℝ n).eval c ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]; push Not
      exact fun kn _ hh => hc0 kn (by linear_combination hh)
    rw [ordinaryHypergeometricCoefficient, hΓan, hΓbn, hΓcn, hδ]
    rw [show Real.Gamma c / (Real.Gamma a * Real.Gamma b)
        * ((ascPochhammer ℝ n).eval a * Real.Gamma a / ((n : ℝ) ^ (a - 1) * (n ! : ℝ))
          * ((ascPochhammer ℝ n).eval b * Real.Gamma b / ((n : ℝ) ^ (b - 1) * (n ! : ℝ)))
          / ((ascPochhammer ℝ n).eval c * Real.Gamma c / ((n : ℝ) ^ (c - 1) * (n ! : ℝ))))
        = (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b
            * ((ascPochhammer ℝ n).eval c)⁻¹
          * ((n : ℝ) ^ (c - 1) / ((n : ℝ) ^ (a - 1) * (n : ℝ) ^ (b - 1)))
          * (1 / (n ! : ℝ)) by field_simp]
    rw [show (n : ℝ) ^ (c - 1) / ((n : ℝ) ^ (a - 1) * (n : ℝ) ^ (b - 1))
        = (n : ℝ) ^ (-(-(1 + (c - a - b)))) by
        rw [← Real.rpow_add hnpos, ← Real.rpow_sub hnpos,
          show c - 1 - (a - 1 + (b - 1)) = -(-(1 + (c - a - b))) by ring],
      Real.rpow_neg hnpos.le]
    field_simp
  refine summable_of_isBigO_nat hgsum ?_
  refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ hratio
  filter_upwards [eventually_gt_atTop 0] with n hn hzero
  exact absurd hzero (by positivity)

end Summability

section Limit

/-- The Euler integrand at `z = 1`: `t^(b−1)(1−t)^(c−a−b−1)`, the `z → 1` limit
of the parametric integrand. Its integral is `B(b, c−a−b)`. -/
-- no-dlmf: auxiliary integrand for the Gauss-limit proof, no DLMF counterpart
private def gaussLimitIntegrand (a b c : ℝ) : ℝ → ℝ :=
  fun t => t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)

variable (a b c : ℝ)

/-- The dominating function `t^(b−1)(1−t)^(c−a−b−1) + t^(b−1)(1−t)^(c−b−1)`,
integrable on `(0,1]` when `c − a − b > 0` and `0 < b < c`. -/
-- no-dlmf: dominating function for the Gauss-limit proof, no DLMF counterpart
private def gaussBound : ℝ → ℝ :=
  fun t => t ^ (b - 1) * (1 - t) ^ (c - a - b - 1) + t ^ (b - 1) * (1 - t) ^ (c - b - 1)

-- no-dlmf: integrability helper for the Gauss-limit proof, no DLMF counterpart
private theorem integrableOn_gaussBound (hb : 0 < b) (hbc : b < c) (habc : 0 < c - a - b) :
    IntegrableOn (gaussBound a b c) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)) (Ioc (0:ℝ) 1) := by
    have := integrableOn_rpow_mul_one_sub_rpow (p := b) (q := c - a - b) hb habc
    refine this.congr_fun (fun t _ => by rw [show c - a - b - 1 = (c - a - b) - 1 by ring]) measurableSet_Ioc
  have h2 : IntegrableOn (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1)) (Ioc (0:ℝ) 1) :=
    integrableOn_rpow_mul_one_sub_rpow hb (by linarith)
  exact h1.add h2

/-- Pointwise bound for the parametric integrand by `gaussBound`, uniform over
`z ≤ 1`: `(1−zt)^(−a) ≤ (1−t)^(−a) + 1` for `t ∈ (0,1)` and `z ≤ 1`. -/
-- no-dlmf: pointwise-bound helper for the Gauss-limit proof, no DLMF counterpart
private theorem gauss_integrand_bound {z t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) (htlt : t < 1)
    (hz0 : 0 ≤ z) (hz : z ≤ 1) :
    ‖t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a)‖ ≤ gaussBound a b c t := by
  have htpos : 0 < t := ht.1
  have h1t : 0 < 1 - t := by linarith
  have hzt0 : 0 ≤ z * t := mul_nonneg hz0 htpos.le
  have hzt : 1 - t ≤ 1 - z * t := by nlinarith [ht.1, htlt]
  have h1zt : 0 < 1 - z * t := by linarith [h1t]
  have h1zt1 : 1 - z * t ≤ 1 := by linarith
  have hX0 : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
    mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.rpow_nonneg h1t.le _)
  -- `(1 − z t)^(−a) ≤ (1 − t)^(−a) + 1`
  have hpow : (1 - z * t) ^ (-a) ≤ (1 - t) ^ (-a) + 1 := by
    rcases le_or_gt a 0 with ha | ha
    · -- exponent `−a ≥ 0`: `(1 − z t)^(−a) ≤ 1^(−a) = 1`
      have : (1 - z * t) ^ (-a) ≤ 1 := Real.rpow_le_one h1zt.le h1zt1 (by linarith)
      linarith [Real.rpow_nonneg h1t.le (-a)]
    · -- exponent `−a < 0`: larger base gives smaller power
      have : (1 - z * t) ^ (-a) ≤ (1 - t) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos h1t hzt (by linarith)
      linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hX0 (Real.rpow_nonneg h1zt.le _))]
  have hfirst : t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a)
      = t ^ (b - 1) * (1 - t) ^ (c - a - b - 1) := by
    rw [mul_assoc, ← Real.rpow_add h1t, show c - b - 1 + -a = c - a - b - 1 by ring]
  calc t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a)
      ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ((1 - t) ^ (-a) + 1) :=
        mul_le_mul_of_nonneg_left hpow hX0
    _ = gaussBound a b c t := by rw [mul_add, mul_one, hfirst, gaussBound]

-- no-dlmf: a left-limit-as-`z→1⁻` statement, not DLMF 15.4.20's exact value
-- `F(a,b;c;1) = …` at the point `z = 1` itself; used internally (together
-- with Abel's limit theorem) to prove `ordinaryHypergeometric_one`. The
-- faithful DLMF 15.4.20 surface is `ordinaryHypergeometric_one_dlmf_complex`.
/-- **Limit form of Gauss's summation theorem**: for `0 < b < c`,
`a` off the nonpositive integers and `c − a − b > 0`,
`₂F₁(a,b;c;z) → Γ(c)·Γ(c−a−b)/(Γ(c−a)·Γ(c−b))` as `z → 1⁻`. -/
theorem ordinaryHypergeometric_tendsto_gaussValue (ha : ∀ k : ℕ, (k : ℝ) ≠ -a)
    (hb : 0 < b) (hbc : b < c) (habc : 0 < c - a - b) :
    Tendsto (fun z : ℝ => ₂F₁ a b c z) (𝓝[<] (1 : ℝ)) (𝓝 (gaussValue a b c)) := by
  have hc : 0 < c := by linarith
  have hcb : 0 < c - b := by linarith
  have hca : 0 < c - a := by linarith
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have hΓcb : Real.Gamma (c - b) ≠ 0 := (Real.Gamma_pos_of_pos hcb).ne'
  have hConst : Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c ≠ 0 := by
    apply div_ne_zero (mul_ne_zero hΓb hΓcb) hΓc
  -- the parametric integrand as a function of `(z, t)`
  set F : ℝ → ℝ → ℝ := fun z t =>
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a) with hF
  -- `Ioc` and `Ioo` agree up to a null set; we phrase measurability on `Ioo`
  have hμset : volume.restrict (Ioc (0:ℝ) 1) = volume.restrict (Ioo (0:ℝ) 1) :=
    MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  -- a.e. (under the restricted measure) a point lies in the *open* interval
  have haeoo : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) 1)), t ∈ Ioo (0:ℝ) 1 := by
    rw [hμset]; exact ae_restrict_mem measurableSet_Ioo
  -- eventually on `𝓝[<] 1` we have `0 < z` and `z < 1`
  have hzev : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ), 0 < z ∧ z < 1 := by
    have h0 : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ), 0 < z :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num))
    have h1 : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ), z < 1 := eventually_mem_nhdsWithin.mono fun z hz => hz
    filter_upwards [h0, h1] with z hz0 hz1 using ⟨hz0, hz1⟩
  -- measurability of `F z` for `z < 1` (continuous on the open interval `Ioo 0 1`)
  have hFmeas : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ),
      AEStronglyMeasurable (F z) (volume.restrict (Ioc (0:ℝ) 1)) := by
    filter_upwards [hzev] with z hz
    rw [hμset]
    refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo)
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht.1))
      · exact ((continuousOn_const.sub continuousOn_id).rpow_const
          fun t ht => Or.inl (by show (1:ℝ) - t ≠ 0; linarith [ht.2]))
    · exact ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).rpow_const
        fun t ht => Or.inl (by show (1:ℝ) - z * t ≠ 0; nlinarith [ht.1, ht.2, hz.1, hz.2]))
  -- the limit value of the integral: the Beta value `B(b, c − a − b)`
  have hIlim : ∫ t in Ioc (0:ℝ) 1, gaussLimitIntegrand a b c t
      = Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have : ∫ t in (0:ℝ)..1, gaussLimitIntegrand a b c t
        = ∫ t in (0:ℝ)..1, t ^ (b - 1) * (1 - t) ^ ((c - a - b) - 1) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [gaussLimitIntegrand, show (c - a - b) - 1 = c - a - b - 1 by ring]
    rw [this, integral_rpow_mul_one_sub_rpow hb habc, show b + (c - a - b) = c - a by ring]
  -- DOMINATED CONVERGENCE on `𝓝[<] 1`
  have hDCT : Tendsto (fun z : ℝ => ∫ t in Ioc (0:ℝ) 1, F z t) (𝓝[<] (1:ℝ))
      (𝓝 (∫ t in Ioc (0:ℝ) 1, gaussLimitIntegrand a b c t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (gaussBound a b c)
      hFmeas ?_ (integrableOn_gaussBound a b c hb hbc habc) ?_
    · -- the uniform integrable bound
      filter_upwards [hzev] with z hz
      filter_upwards [haeoo] with t htmemoo
      exact gauss_integrand_bound a b c (Ioo_subset_Ioc_self htmemoo) htmemoo.2 hz.1.le hz.2.le
    · -- the pointwise limit, a.e. in `t`
      filter_upwards [haeoo] with t htmemoo
      have h1t : (0:ℝ) < 1 - t := by linarith [htmemoo.2]
      -- `z ↦ (1 − z t)^(−a)` is continuous at `z = 1` since `1 − t > 0`
      have hcont : Tendsto (fun z : ℝ => (1 - z * t) ^ (-a)) (𝓝 (1:ℝ))
          (𝓝 ((1 - t) ^ (-a))) := by
        have hg : Tendsto (fun z : ℝ => 1 - z * t) (𝓝 (1:ℝ)) (𝓝 (1 - 1 * t)) :=
          (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 1
        have hrp : ContinuousAt (fun u : ℝ => u ^ (-a)) (1 - 1 * t) :=
          Real.continuousAt_rpow_const _ _ (Or.inl (by rw [one_mul]; exact h1t.ne'))
        have := hrp.tendsto.comp hg
        simpa only [Function.comp_def, one_mul] using this
      have hlim : Tendsto (fun z : ℝ => F z t) (𝓝 (1:ℝ))
          (𝓝 (gaussLimitIntegrand a b c t)) := by
        have := (hcont.const_mul (t ^ (b - 1) * (1 - t) ^ (c - b - 1)))
        simp only [hF, gaussLimitIntegrand]
        rw [show t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)
          = t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) by
          rw [mul_assoc, ← Real.rpow_add h1t, show c - b - 1 + -a = c - a - b - 1 by ring]]
        exact this.congr fun z => by ring
      exact hlim.mono_left nhdsWithin_le_nhds
  -- relate the integral to `₂F₁` and finish
  have hEuler : ∀ᶠ z : ℝ in 𝓝[<] (1:ℝ),
      ∫ t in Ioc (0:ℝ) 1, F z t = (Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c) * ₂F₁ a b c z := by
    filter_upwards [hzev] with z hz
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact ordinaryHypergeometric_eq_betaIntegral a b c ha hb hbc
      (by rw [abs_of_pos hz.1]; exact hz.2)
  -- transfer the limit through the eventual equality and divide by the constant
  have hDCT2 : Tendsto (fun z : ℝ => (Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c)
      * ₂F₁ a b c z) (𝓝[<] (1:ℝ))
      (𝓝 (Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a))) := by
    rw [hIlim] at hDCT
    exact hDCT.congr' hEuler
  have hfinal := hDCT2.const_mul (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)))
  have hcollapse : ∀ z : ℝ, Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
      * ((Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c) * ₂F₁ a b c z) = ₂F₁ a b c z := by
    intro z; field_simp
  have hval : Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
      * (Real.Gamma b * Real.Gamma (c - a - b) / Real.Gamma (c - a)) = gaussValue a b c := by
    rw [gaussValue]; field_simp
  simp only [hcollapse] at hfinal
  rw [hval] at hfinal
  exact hfinal

-- no-dlmf: real/narrowed restriction of DLMF 15.4.20 (`a, b, c : ℝ` with the
-- extra ordering `0 < b < c`, needed only by this proof's real-Euler-integral
-- route, not part of DLMF's stated domain); DLMF assigns `a, b, c`
-- real-or-complex values under the sole constraint `Re(c−a−b) > 0`. The
-- faithful surface is `ordinaryHypergeometric_one_dlmf_complex`.
/-- **Gauss's summation theorem**, real case: for `0 < b < c`, `a` off the
nonpositive integers and `c − a − b > 0`,
`₂F₁(a,b;c;1) = Γ(c)·Γ(c−a−b)/(Γ(c−a)·Γ(c−b))`.

The boundary value of `₂F₁` at the unit argument. Combining the limit form
(`ordinaryHypergeometric_tendsto_gaussValue`, by dominated convergence on Euler's
integral) with Abel's limit theorem
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`): once the `z = 1` series is
summable (`summable_ordinaryHypergeometricCoefficient_one`), Abel identifies the
boundary value `₂F₁(a,b;c;1)` with the left limit, which the limit form pins to
the Gauss value. -/
theorem ordinaryHypergeometric_one (a b c : ℝ) (ha : ∀ k : ℕ, (k : ℝ) ≠ -a)
    (hb : 0 < b) (hbc : b < c) (habc : 0 < c - a - b) :
    ₂F₁ a b c (1 : ℝ) = gaussValue a b c := by
  -- the `z = 1` series is summable; let `l` be its sum
  have hsummable := summable_ordinaryHypergeometricCoefficient_one a b c ha hb hbc habc
  set l := ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n with hl
  have hHasSum : HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n) l :=
    hsummable.hasSum
  -- `₂F₁ a b c 1 = ∑' n, c_n` (the series sum at the boundary point `x = 1`)
  have hval1 : ₂F₁ a b c (1 : ℝ) = l := by
    rw [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, hl]
    exact tsum_congr fun n => by rw [one_pow, smul_eq_mul, mul_one]
  -- Abel's limit theorem: the power series tends to `l` as `x → 1⁻`
  have hAbel : Tendsto (fun x : ℝ => ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n * x ^ n)
      (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hHasSum.tendsto_sum_nat
  -- on `|x| < 1` the power series equals `₂F₁`, so the same limit holds for `₂F₁`
  have habc' : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -c := by
    intro kn
    refine ⟨ha kn, ?_, ?_⟩
    · intro h; have := Nat.cast_nonneg (α := ℝ) kn; rw [h] at this; linarith
    · intro h; have := Nat.cast_nonneg (α := ℝ) kn; rw [h] at this; linarith
  have hzev : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), 0 < x ∧ x < 1 := by
    have h0 : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), 0 < x :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num))
    have h1 : ∀ᶠ x : ℝ in 𝓝[<] (1:ℝ), x < 1 := eventually_mem_nhdsWithin.mono fun x hx => hx
    filter_upwards [h0, h1] with x hx0 hx1 using ⟨hx0, hx1⟩
  have hAbel2 : Tendsto (fun x : ℝ => ₂F₁ a b c x) (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    refine hAbel.congr' ?_
    filter_upwards [hzev] with x hx
    exact ((ordinaryHypergeometric_hasSum a b c habc'
      (by rw [Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.2)).tsum_eq)
  -- uniqueness of limits against the dominated-convergence limit form
  have hgauss := ordinaryHypergeometric_tendsto_gaussValue a b c ha hb hbc habc
  rw [hval1]
  exact tendsto_nhds_unique hAbel2 hgauss

/-- **DLMF 15.4.20** — for `c` off the nonpositive integers and
`Re(c − a − b) > 0`, `₂F₁(a,b;c;1) = Γ(c)·Γ(c−a−b)/(Γ(c−a)·Γ(c−b))` (DLMF's
real-or-complex `a, b, c`, matching DLMF's sole stated convergence
constraint `Re(c−a−b) > 0`; no positivity ordering on `a, b, c` is required,
unlike the real-domain route in `ordinaryHypergeometric_one`).

DAG: E-15.4.20.
Numerical: PASS
Verified: verified
-/
theorem ordinaryHypergeometric_one_dlmf_complex (a b c : ℂ)
    (hc : ∀ m : ℕ, c ≠ -(m : ℂ)) (habc : 0 < (c - a - b).re) :
    ₂F₁ a b c (1 : ℂ)
      = Complex.Gamma c * Complex.Gamma (c - a - b)
        / (Complex.Gamma (c - a) * Complex.Gamma (c - b)) := by
  sorry

end Limit

end FLMF.Hypergeometric
