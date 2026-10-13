import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Confluent hypergeometric `₁F₁` — Kummer's `M(a;b;z)` (framework — DLMF §13.2)

`M(a;b;z) = ∑ (a)ₙ/(b)ₙ · zⁿ/n!` (DLMF 13.2.2), the parent of Airy, Bessel,
Hermite, Laguerre, error and incomplete-gamma instances. Modeled directly on
Mathlib's `Analysis.SpecialFunctions.OrdinaryHypergeometric` (`₂F₁`): the series
is a `FormalMultilinearSeries.ofScalars`, the function its sum.

Main results:

* `kummerM` (notation `₁F₁`, scoped to `FLMF.Hypergeometric`) — the sum of the
  series, over any normed algebra.
* `kummerSeries_eq_zero_of_neg_nat` — terminating cases: parameter a nonpositive
  integer kills the tail (`a = -k` gives a degree-`k` polynomial; `b = -k` makes
  the junk-value tail vanish).
* `kummerSeries_radius_eq_top_of_b_ne_neg_nat` — **`M(a;b;·)` is entire in `z`
  when `b` is not a nonpositive integer** (DLMF 13.2.2): ratio test
  `(a+n)/((b+n)(1+n)) → 0` generically, termination in the `a`-terminating case.
  The unconditional `kummerSeries_radius_eq_top` also holds in Lean, but for
  `b ∈ {0,-1,-2,…}` only by the junk convention `(0)⁻¹ = 0` (no DLMF content:
  there `M` is undefined).
* `kummerM_hasFPowerSeriesOnBall` — the sum is globally analytic.

The Kummer ODE `z M'' + (b−z) M' − a M = 0` (DLMF 13.2.1) and the contiguous
relations are downstream framework work (`hypergeometric_ode`, F-pFq-def).
-/

open Nat FormalMultilinearSeries

namespace FLMF.Hypergeometric

section Field

variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The coefficients `(a)ₙ/(b)ₙ · 1/n!` of Kummer's confluent hypergeometric
series (DLMF 13.2.2). -/
noncomputable abbrev kummerCoefficient (a b : 𝕂) (n : ℕ) : 𝕂 :=
  (n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹

/-- `kummerSeries 𝔸 (a b : 𝕂)` is the confluent hypergeometric series as a
`FormalMultilinearSeries` (DLMF 13.2.2). Its sum is `kummerM`. -/
noncomputable def kummerSeries (a b : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (kummerCoefficient a b)

variable {𝔸} (a b : 𝕂)

/-- Kummer's confluent hypergeometric function `M(a;b;x)` (DLMF 13.2.2), the sum
of `kummerSeries`. Junk value `0` outside the radius — but the radius is `⊤`
(`kummerSeries_radius_eq_top`), so over a complete algebra the sum is global. -/
-- DAG: E-13.2.2.
-- Verified: unverified (tier2 DIVERGES)
noncomputable def kummerM (x : 𝔸) : 𝔸 :=
  (kummerSeries 𝔸 a b).sum x

@[inherit_doc]
scoped notation "₁F₁" => kummerM

-- no-dlmf: termwise evaluation of the series, no DLMF counterpart
theorem kummerSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (kummerSeries 𝔸 a b n fun _ => x) =
      ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * ((ascPochhammer 𝕂 n).eval b)⁻¹) • x ^ n := by
  rw [kummerSeries, ofScalars_apply_eq]

-- no-dlmf: tsum form of the series sum, no DLMF counterpart
theorem kummerM_sum_eq (x : 𝔸) : (kummerSeries 𝔸 a b).sum x =
    ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
      ((ascPochhammer 𝕂 n).eval b)⁻¹) • x ^ n :=
  tsum_congr fun n => kummerSeries_apply_eq a b x n

-- no-dlmf: general-normed-algebra series form of `₁F₁`; the ℂ-specialized faithful
-- DLMF 13.2.2 surface is `kummerM_eq_tsum_complex`
/-- The confluent hypergeometric function as its displayed power series, over any
normed algebra: `₁F₁ a b = fun x => ∑ₙ (n!⁻¹ (a)ₙ (b)ₙ⁻¹) • xⁿ`.  The faithful
DLMF 13.2.2 (over ℂ) surface is `kummerM_eq_tsum_complex`. -/
theorem kummerM_eq_tsum : ₁F₁ a b =
    fun (x : 𝔸) => ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
      ((ascPochhammer 𝕂 n).eval b)⁻¹) • x ^ n :=
  funext (kummerM_sum_eq a b)

/-- **DLMF 13.2.2** (over ℂ): `M(a,b,z) = ∑ₛ (a)ₛ/((b)ₛ s!) zˢ`, for `b` off the
nonpositive integers.  The ℂ-specialized faithful surface of the confluent
hypergeometric series definition; the general-algebra form is `kummerM_eq_tsum`
and the convergence/entire consequence is `kummerSeries_radius_eq_top_of_b_ne_neg_nat`.
DAG: E-13.2.2.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem kummerM_eq_tsum_complex (a b z : ℂ) (_hb : ∀ k : ℕ, (k : ℂ) ≠ -b) :
    kummerM a b z = ∑' s : ℕ, ((s ! : ℂ)⁻¹ * (ascPochhammer ℂ s).eval a *
      ((ascPochhammer ℂ s).eval b)⁻¹) * z ^ s := by
  simpa [smul_eq_mul] using congrFun (kummerM_eq_tsum (𝔸 := ℂ) a b) z

-- no-dlmf: evaluation at 0 helper, no DLMF counterpart
theorem kummerSeries_apply_zero (n : ℕ) :
    (kummerSeries 𝔸 a b n fun _ => 0) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [kummerSeries, ofScalars_apply_eq]
  cases n <;> simp [kummerCoefficient]

-- no-dlmf: general-normed-algebra `z = 0` corollary, quantified over arbitrary
-- `a, b : 𝕂` (no `b`-regularity hypothesis needed since every higher-order term
-- vanishes at `z = 0`); not itself a numbered DLMF equation, matching the
-- no-dlmf treatment of the sibling general-algebra series lemmas above
-- (`kummerM_eq_tsum` etc.). The faithful DLMF 13.2.2 surface is
-- `kummerM_eq_tsum_complex`.
/-- `M(a;b;0) = 1` (DLMF 13.2.2 at `z = 0`).

-/
@[simp]
theorem kummerM_zero : ₁F₁ a b (0 : 𝔸) = 1 := by
  simp [kummerM_eq_tsum, ← kummerSeries_apply_eq, kummerSeries_apply_zero]

-- no-dlmf: per-term vanishing helper (terminating cases) for kummerSeries_radius_eq_top; the termination fact is §13.2 prose, no numbered DLMF equation
/-- If `a` or `b` is the nonpositive integer `-k`, every series term beyond `k`
vanishes: the `a` case terminates the series, matching the unnumbered §13.2
prose describing the terminating case (`M(a,b,z)` becomes a polynomial when
`a` is a nonpositive integer); the `b` case kills the junk-valued tail. -/
lemma kummerSeries_eq_zero_of_neg_nat {n k : ℕ} (hab : (k : 𝕂) = -a ∨ (k : 𝕂) = -b)
    (hk : k < n) : kummerSeries 𝔸 a b n = 0 := by
  rw [kummerSeries, ofScalars]
  rcases hab with h | h
  all_goals
    ext
    simp [(ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]

end Field

section RCLike

open Asymptotics Filter Real Set Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b : 𝕂)

/-- The coefficient ratio of the Kummer series: `cₙ₊₁/cₙ = (a+n)/((b+n)(1+n))`,
for parameters off the nonpositive integers. -/
-- no-dlmf: coefficient-ratio infrastructure for the radius proof, no DLMF counterpart
theorem kummerCoefficient_succ_div (n : ℕ)
    (hab : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b) :
    kummerCoefficient a b n.succ / kummerCoefficient a b n
      = (a + n) / ((b + n) * (1 + (n : 𝕂))) := by
  have hA : (ascPochhammer 𝕂 n).eval a ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun kn _ => (hab kn).1
  have hB : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun kn _ => (hab kn).2
  have hBn : b + (n : 𝕂) ≠ 0 := fun h => (hab n).2 (by linear_combination h)
  have hfac : ((n ! : ℕ) : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hn1 : (1 : 𝕂) + (n : 𝕂) ≠ 0 := by
    have := Nat.cast_add_one_ne_zero (R := 𝕂) n
    intro h; exact this (by linear_combination h)
  simp only [kummerCoefficient, factorial_succ, ascPochhammer_succ_eval, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The Kummer series has infinite radius of convergence for **all** parameters
`a, b`.  For `b` off the nonpositive integers this is the honest entirety of
`M(a,b,·)` — see `kummerSeries_radius_eq_top_of_b_ne_neg_nat`; in the remaining
case `b ∈ {0,-1,-2,…}` it holds only by Mathlib's junk convention `(0)⁻¹ = 0`,
which terminates the series.  That degenerate case has no DLMF counterpart
(there `M(a,b,z)` is undefined), so this unconditional fact is untagged. -/
-- no-dlmf: radius ⊤ for all parameters; the `b`-degenerate case is a junk-convention
-- artifact (`(0)⁻¹ = 0` terminates the series), not DLMF entirety. The faithful
-- DLMF 13.2.2 statement is `kummerSeries_radius_eq_top_of_b_ne_neg_nat`.
theorem kummerSeries_radius_eq_top : (kummerSeries 𝔸 a b).radius = ⊤ := by
  by_cases hab : ∃ k : ℕ, (k : 𝕂) = -a ∨ (k : 𝕂) = -b
  · obtain ⟨k, hk⟩ := hab
    refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
    exact kummerSeries_eq_zero_of_neg_nat a b hk (by lia)
  · push Not at hab
    have hne : ∀ n, kummerCoefficient a b n ≠ 0 := by
      intro n
      have hA : (ascPochhammer 𝕂 n).eval a ≠ 0 := by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => (hab kn).1
      have hB : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
        rw [Ne, ascPochhammer_eval_eq_zero_iff]
        push Not
        exact fun kn _ => (hab kn).2
      exact mul_ne_zero (mul_ne_zero
        (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero)) hA) (inv_ne_zero hB)
    refine ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall hne) ?_
    have hratio : (fun n : ℕ ↦ ‖kummerCoefficient a b n.succ‖ / ‖kummerCoefficient a b n‖)
        = fun n : ℕ ↦ ‖(a + n) / ((b + n) * (1 + (n : 𝕂)))‖ := by
      funext n
      rw [← norm_div, kummerCoefficient_succ_div a b n hab]
    rw [hratio]
    have h1 : Tendsto (fun n : ℕ ↦ (a + n) / (b + n)) atTop (𝓝 1) := by
      have := tendsto_add_mul_div_add_mul_atTop_nhds a b (1 : 𝕂) one_ne_zero
      simpa using this
    have h2 : Tendsto (fun n : ℕ ↦ ((1 : 𝕂) + n)⁻¹) atTop (𝓝 0) := by
      have := tendsto_add_mul_div_add_mul_atTop_nhds (1 : 𝕂) 1 0 one_ne_zero
      simp only [zero_mul, add_zero, one_mul, zero_div] at this
      simpa [one_div] using this
    have hkey : Tendsto (fun n : ℕ ↦ (a + n) / ((b + n) * (1 + (n : 𝕂)))) atTop (𝓝 0) := by
      have h3 := h1.mul h2
      rw [one_mul] at h3
      refine h3.congr fun n ↦ ?_
      rw [← div_eq_mul_inv, div_div]
    simpa using hkey.norm

-- no-dlmf: entireness of `M` is DLMF §13.2 prose ("M(a,b,z) is entire in z"), not a
-- numbered equation; the displayed-equation 13.2.2 surface is `kummerM_eq_tsum_complex`
/-- **`M(a;b;·)` is entire in `z`** when `b` is not a nonpositive integer (DLMF
§13.2 prose adjacent to 13.2.2): the confluent hypergeometric function defined by
the power series is entire in `z` provided `b ∉ {0,-1,-2,…}`.  Generic parameters
give this by the ratio test `(a+n)/((b+n)(1+n)) → 0`; the `a`-terminating case
(`a ∈ {0,-1,-2,…}`, `b` off the nonpositive integers) is a polynomial.  The
excluded case `b ∈ {0,-1,-2,…}`, where `M(a,b,z)` is undefined in DLMF, is not
asserted here. -/
theorem kummerSeries_radius_eq_top_of_b_ne_neg_nat
    (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) : (kummerSeries 𝔸 a b).radius = ⊤ := by
  exact kummerSeries_radius_eq_top 𝔸 a b

/-- `₁F₁ a b` is globally analytic: it is the sum of its power series on all of
`𝔸` (radius `⊤`). -/
-- no-dlmf: global-analyticity packaging, no DLMF counterpart
theorem kummerM_hasFPowerSeriesOnBall [CompleteSpace 𝔸] :
    HasFPowerSeriesOnBall (₁F₁ a b : 𝔸 → 𝔸) (kummerSeries 𝔸 a b) 0 ⊤ := by
  have h := (kummerSeries 𝔸 a b).hasFPowerSeriesOnBall
    (by rw [kummerSeries_radius_eq_top]; exact ENNReal.zero_lt_top)
  rwa [kummerSeries_radius_eq_top] at h

-- no-dlmf: scalar-field HasSum packaging of the entire series, no DLMF counterpart
/-- `HasSum` form of the Kummer series at every point of the scalar field
(radius `⊤`, `kummerSeries_radius_eq_top`). -/
theorem kummerM_hasSum (x : 𝕂) :
    HasSum (fun n : ℕ => kummerCoefficient a b n * x ^ n) (₁F₁ a b x) := by
  have h := (kummerSeries 𝕂 a b).hasSum (x := x)
    (by rw [kummerSeries_radius_eq_top]; simp)
  simpa only [kummerM, kummerSeries_apply_eq, smul_eq_mul] using h

end RCLike

section OfReal

/-! ### `ℝ → ℂ` cast bridge

Scalar-tower cast infrastructure: the entire sum `₁F₁ a b` commutes with the
`ℝ → ℂ` cast, letting the Functions layer identify real special-function
instances with the complex comparison functions of the Frameworks layer
(e.g. `complexParabolicCylinderU`). -/

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart (private copy;
-- the public sibling `ascPochhammer_eval_ofReal` lives downstream in
-- `GaussConnection` and cannot be imported here)
/-- `ascPochhammer` evaluation commutes with the `ℝ → ℂ` cast. -/
private lemma ascPochhammer_eval_ofReal' (x : ℝ) (n : ℕ) :
    (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (x : ℂ) := by
  have h : ((ascPochhammer ℝ n).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) x)
      = (algebraMap ℝ ℂ) ((ascPochhammer ℝ n).eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [ascPochhammer_map] at h
  simpa using h.symm

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart
/-- The Kummer coefficients commute with the `ℝ → ℂ` cast. -/
theorem kummerCoefficient_ofReal (a b : ℝ) (n : ℕ) :
    ((kummerCoefficient a b n : ℝ) : ℂ) = kummerCoefficient (a : ℂ) (b : ℂ) n := by
  simp only [kummerCoefficient, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, ascPochhammer_eval_ofReal']

-- no-dlmf: scalar-tower cast infrastructure, no DLMF counterpart
/-- `M(a;b;x)` at real parameters and a real argument commutes with the
`ℝ → ℂ` cast.  No pole-avoidance hypothesis on `b` is needed: both sides are
unconditional tsums of termwise-equal, everywhere-summable series (in the
degenerate case `b ∈ {0,-1,-2,…}` both sides follow the same junk convention
`0⁻¹ = 0`). -/
theorem kummerM_ofReal (a b x : ℝ) :
    ((kummerM a b x : ℝ) : ℂ) = kummerM (a : ℂ) (b : ℂ) (x : ℂ) := by
  have hR := kummerM_hasSum a b x
  have hC := kummerM_hasSum (a : ℂ) (b : ℂ) (x : ℂ)
  have hRC := Complex.hasSum_ofReal.mpr hR
  have he : (fun n : ℕ => ((kummerCoefficient a b n * x ^ n : ℝ) : ℂ))
      = fun n : ℕ => kummerCoefficient (a : ℂ) (b : ℂ) n * (x : ℂ) ^ n := by
    funext n
    rw [Complex.ofReal_mul, kummerCoefficient_ofReal, Complex.ofReal_pow]
  rw [he] at hRC
  exact hRC.unique hC

end OfReal

end FLMF.Hypergeometric
