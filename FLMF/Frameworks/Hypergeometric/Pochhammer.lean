import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Pochhammer symbol `(a)ₙ` (framework — DLMF §5.2(iii))

The rising factorial `(a)ₙ = a (a+1) ⋯ (a+n−1)`, the coefficient engine of the
hypergeometric tower (`₁F₁`, `₂F₁`, `pFq` — DLMF §13, §15, §16). Root of
`frameworks-hyper`: everything downstream consumes `(a)ₙ` through this module.

**Provenance:** Mathlib carries the polynomial `ascPochhammer S n : S[X]`; FLMF's
`(a)ₙ` is its evaluation `(ascPochhammer 𝕂 n).eval a` — the same binding already
used by `FLMF.Functions.OrthogonalPolynomials.Laguerre`.

Surfaced (Mathlib, `RingTheory.Polynomial.Pochhammer` unless noted):

* `ascPochhammer_zero`, `ascPochhammer_one` — `(a)₀ = 1`, `(a)₁ = a`.
* `ascPochhammer_succ_eval` — the coefficient ratio `(a)ₙ₊₁ = (a)ₙ · (a + n)`,
  the recurrence every hypergeometric series term satisfies.
* `ascPochhammer_mul` — the splitting `(a)ₙ₊ₘ = (a)ₙ · (a+n)ₘ`.
* `ascPochhammer_eval_one` — `(1)ₙ = n!`.
* `ascPochhammer_eval_eq_zero_iff` — over a domain, `(a)ₙ = 0` iff `a` is one of
  `0, −1, …, −(n−1)`: the exact nonvanishing criterion for `pFq` denominators.
* `ascPochhammer_pos`, `ascPochhammer_nat_eq_ascFactorial`,
  `descPochhammer_eval_eq_ascPochhammer` — positivity, ℕ-specialization, the
  falling-factorial bridge.
* `Polynomial.continuous_aeval`-style facts are free: `(·)ₙ` is a polynomial, so
  continuity/differentiability in `a` need no bespoke lemmas
  (`Analysis.SpecialFunctions.Pochhammer` adds the `descPochhammer` calculus).
* `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` already consumes
  this API: `₂F₁` with `ordinaryHypergeometricSeries_radius_eq_one` — the
  intended Mathlib anchor for `F-2F1-def`.

Added here (the pieces Mathlib lacks):

* `ascPochhammer_eval_eq_prod_range` — `(a)ₙ = ∏_{k<n} (a + k)` (Mathlib has
  only the `descPochhammer` product form).
* `ascPochhammer_succ_eval'` — the first-factor recursion `(a)ₙ₊₁ = a·(a+1)ₙ`
  in evaluated form (Mathlib's `ascPochhammer_succ_eval` peels the last factor),
  the step behind the hypergeometric derivative shifts `a ↦ a+1`.
* `Gamma_add_nat_eq_ascPochhammer_mul` / `ascPochhammer_eval_eq_Gamma_div` —
  the gamma-quotient identity `(a)ₙ = Γ(a+n)/Γ(a)` (DLMF 5.2.5), the form the
  asymptotic and Mellin–Barnes machinery binds to.
-/

namespace FLMF.Hypergeometric

open Polynomial

-- no-dlmf: strictly-more-general form over an arbitrary commutative semiring
-- `R`, not DLMF's real-or-complex variable `a`; the faithful DLMF 5.2.4
-- surfaces are `ascPochhammer_eval_eq_prod_range_real_dlmf` and
-- `ascPochhammer_eval_eq_prod_range_complex_dlmf`
/-- `(a)ₙ = ∏_{k<n} (a + k)` — the ascending product form. -/
theorem ascPochhammer_eval_eq_prod_range {R : Type*} [CommSemiring R] (n : ℕ) (r : R) :
    (ascPochhammer R n).eval r = ∏ k ∈ Finset.range n, (r + k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

-- no-dlmf: chain link 5.2.4 (assembled in `ascPochhammer_5_2_4` below)
/-- (real) `(a)ₙ = ∏_{k<n} (a + k)` (DLMF-faithful restriction
of `ascPochhammer_eval_eq_prod_range` to DLMF's real variable `a`). -/
theorem ascPochhammer_eval_eq_prod_range_real_dlmf (n : ℕ) (r : ℝ) :
    (ascPochhammer ℝ n).eval r = ∏ k ∈ Finset.range n, (r + k) :=
  ascPochhammer_eval_eq_prod_range n r

-- no-dlmf: chain link 5.2.4 (assembled in `ascPochhammer_5_2_4` below)
/-- (complex) `(a)ₙ = ∏_{k<n} (a + k)` (DLMF-faithful
restriction of `ascPochhammer_eval_eq_prod_range` to DLMF's complex
variable `a`). -/
theorem ascPochhammer_eval_eq_prod_range_complex_dlmf (n : ℕ) (r : ℂ) :
    (ascPochhammer ℂ n).eval r = ∏ k ∈ Finset.range n, (r + k) :=
  ascPochhammer_eval_eq_prod_range n r

-- no-dlmf: chain link 5.2.4 (assembled in `ascPochhammer_5_2_4` below); base case
-- `(a)₀ = 1` for a real variable `a`, an instance of `ascPochhammer_eval_eq_prod_range`
-- at `n = 0` (the empty product).
theorem ascPochhammer_eval_zero_real (r : ℝ) : (ascPochhammer ℝ 0).eval r = 1 := by
  simpa using ascPochhammer_eval_eq_prod_range 0 r

-- no-dlmf: chain link 5.2.4 (assembled in `ascPochhammer_5_2_4` below); base case
-- `(a)₀ = 1` for a complex variable `a`, an instance of `ascPochhammer_eval_eq_prod_range`
-- at `n = 0` (the empty product).
theorem ascPochhammer_eval_zero_complex (r : ℂ) : (ascPochhammer ℂ 0).eval r = 1 := by
  simpa using ascPochhammer_eval_eq_prod_range 0 r

/-- **DLMF 5.2.4** — the Pochhammer symbol `(a)ₙ`'s defining base case and closed
form, `(a)₀ = 1` and `(a)ₙ = a(a+1)(a+2)⋯(a+n-1) = ∏_{k<n} (a+k)`, over both real
and complex `a` (DLMF's `a` is "real or complex").

DLMF 5.2.4.
DAG: E-5.2.4.
Fidelity: tier1 unable (tier1-pending)
Verified: verified (tier2)
-/
theorem ascPochhammer_5_2_4 (n : ℕ) (r : ℝ) (z : ℂ) :
    ((ascPochhammer ℝ 0).eval r = 1 ∧
        (ascPochhammer ℝ n).eval r = ∏ k ∈ Finset.range n, (r + k)) ∧
      ((ascPochhammer ℂ 0).eval z = 1 ∧
        (ascPochhammer ℂ n).eval z = ∏ k ∈ Finset.range n, (z + k)) :=
  ⟨⟨ascPochhammer_eval_zero_real r, ascPochhammer_eval_eq_prod_range_real_dlmf n r⟩,
    ascPochhammer_eval_zero_complex z, ascPochhammer_eval_eq_prod_range_complex_dlmf n z⟩

/-- `(x)ₙ₊₁ = x · (x+1)ₙ` — the "first factor" recursion for the rising
factorial, in evaluated form (companion to `ascPochhammer_succ_eval`, which
peels the last factor). -/
-- no-dlmf: first-factor Pochhammer recursion, no distinct DLMF equation number
theorem ascPochhammer_succ_eval' {S : Type*} [CommSemiring S] (n : ℕ) (x : S) :
    (ascPochhammer S (n + 1)).eval x = x * (ascPochhammer S n).eval (x + 1) := by
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

-- no-dlmf: strictly-more-general form using the weakest sufficient pointwise
-- pole-avoidance hypothesis `a + k ≠ 0` for `k < n` (not DLMF's blanket
-- `a ≠ 0,-1,-2,…`); the faithful DLMF 5.2.5 surface is
-- Gamma_add_nat_eq_ascPochhammer_mul_dlmf
/-- `Γ(a + n) = (a)ₙ · Γ(a)`, under the pointwise pole-avoidance
hypothesis `a + k ≠ 0` for `k < n` — the weakest condition letting the
`Γ(s+1) = s·Γ(s)` recurrence iterate. -/
theorem Gamma_add_nat_eq_ascPochhammer_mul (a : ℂ) (n : ℕ) (h : ∀ k < n, a + (k : ℂ) ≠ 0) :
    Complex.Gamma (a + n) = (ascPochhammer ℂ n).eval a * Complex.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : a + (n : ℂ) ≠ 0 := h n (Nat.lt_succ_self n)
    have hcast : a + ((n + 1 : ℕ) : ℂ) = (a + n) + 1 := by push_cast; ring
    rw [hcast, Complex.Gamma_add_one _ hn, ih fun k hk => h k (Nat.lt_succ_of_lt hk),
      ascPochhammer_succ_eval]
    ring

-- no-dlmf: rearranged (multiplied-out) twin of 5.2.5; canonical surface is
-- `ascPochhammer_eval_eq_Gamma_div` below.
/-- `Γ(a+n) = (a)ₙ·Γ(a)` (DLMF-faithful restriction of
`Gamma_add_nat_eq_ascPochhammer_mul`: `a ≠ 0,-1,-2,…`, DLMF's blanket
pole-avoidance hypothesis). -/
theorem Gamma_add_nat_eq_ascPochhammer_mul_dlmf (a : ℂ) (n : ℕ)
    (h : ∀ m : ℕ, a ≠ -(m : ℂ)) :
    Complex.Gamma (a + n) = (ascPochhammer ℂ n).eval a * Complex.Gamma a :=
  Gamma_add_nat_eq_ascPochhammer_mul a n
    (fun k _ hk0 => h k (by linear_combination hk0))

/-- `(a)ₙ = Γ(a+n)/Γ(a)` (DLMF 5.2.5) for `a` off the gamma poles.

DLMF 5.2.5.
Fidelity: tier1 PASS
Verified: verified (tier2)
DAG: E-5.2.5.
-/
theorem ascPochhammer_eval_eq_Gamma_div (a : ℂ) (n : ℕ) (h : ∀ m : ℕ, a ≠ -m) :
    (ascPochhammer ℂ n).eval a = Complex.Gamma (a + n) / Complex.Gamma a := by
  have hΓ : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero h
  rw [Gamma_add_nat_eq_ascPochhammer_mul a n fun k _ hk0 =>
      h k (add_eq_zero_iff_eq_neg.mp hk0), mul_div_cancel_right₀ _ hΓ]

-- no-dlmf: finite Pochhammer/rising-factorial identity, a true corollary of
-- Legendre's gamma duplication formula (DLMF 5.5.5) via gamma ratios, but not
-- the same relation as that equation (which is stated for Γ(2z), not for
-- Pochhammer symbols). The faithful DLMF 5.5.5 surface lives in
-- `FLMF/Functions/Gamma/Multiplication.lean` and siblings.
/-- **Legendre duplication for Pochhammer symbols**: `(2a)₂ₙ = 4ⁿ (a)ₙ (a + 1/2)ₙ`
(the rising-factorial shadow of DLMF 5.5.5, by induction via
`ascPochhammer_succ_eval`) — the coefficient engine for every even/odd binomial
split among the quadratic-argument special cases 15.4.7–15.4.18. -/
theorem ascPochhammer_eval_duplication {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a : 𝕂) (n : ℕ) :
    (ascPochhammer 𝕂 (2 * n)).eval (2 * a) =
      4 ^ n * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval (a + 1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h2, ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      ascPochhammer_succ_eval, ih]
    push_cast
    ring

end FLMF.Hypergeometric
