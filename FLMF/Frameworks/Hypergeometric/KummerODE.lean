import FLMF.Frameworks.Hypergeometric.Kummer
import FLMF.Frameworks.Hypergeometric.Pochhammer
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-!
# Kummer's differential equation for `₁F₁` (framework — DLMF §13.2, §13.3)

The derivative of Kummer's confluent hypergeometric function, and Kummer's
equation:

* `kummerM_hasDerivAt_dlmf` / `kummerM_deriv_dlmf` — the faithful, unconstrained
  DLMF 13.3.15: `d/dz M(a;b;z) = (a/b) M(a+1;b+1;z)`, for every `a`, `b`
  (`b = 0`, or any nonpositive-integer `b`, collapses both sides to `0` through
  the junk-value convention). `kummerM_hasDerivAt` / `kummerM_deriv` are the
  `b ≠ 0` restricted instances feeding it.
* `IsKummerSolution` — **Kummer's equation** (DLMF 13.2.1) as a predicate on an
  unknown function `w`: `z w'' + (b − z) w' − a w = 0`.
* `kummerM_ode` — `M(a;b;·)` solves Kummer's equation, for `b` not a
  nonpositive integer.

The series is entire (`kummerSeries_radius_eq_top`), so termwise
differentiation goes through Mathlib's `HasFPowerSeriesOnBall.fderiv`; the
resulting coefficients are identified by Pochhammer algebra: the shift
`(n+1)·cₙ₊₁(a,b) = (a/b)·cₙ(a+1,b+1)` gives the derivative, and the three-term
recurrence `(n+1)(b+n)·cₙ₊₁ = (a+n)·cₙ` makes the ODE vanish termwise.
-/

open Nat FormalMultilinearSeries

namespace FLMF.Hypergeometric

section Coefficients

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂)

-- no-dlmf: coefficient-level shift lemma, not the function-level DLMF 13.3.15
-- derivative identity (that faithful surface is `kummerM_deriv` below);
-- infrastructure feeding the termwise-derivative argument.
/-- Coefficient form of DLMF 13.3.15: `(n+1)·cₙ₊₁(a,b) = (a/b)·cₙ(a+1,b+1)`.
Holds for every `a` (including terminating cases) as long as `b ≠ 0`.

-/
theorem kummerCoefficient_succ_eq (n : ℕ) (hb : b ≠ 0) :
    ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) =
      a / b * kummerCoefficient (a + 1) (b + 1) n := by
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfac : (((n + 1)! : ℕ) : 𝕂) = ((n : 𝕂) + 1) * ((n ! : ℕ) : 𝕂) := by
    push_cast [Nat.factorial_succ]
    ring
  simp only [kummerCoefficient, hfac, ascPochhammer_succ_eval' n a, ascPochhammer_succ_eval' n b,
    mul_inv]
  field_simp

-- no-dlmf: coefficient-level shift lemma at DLMF's unconstrained strength (no
-- hypothesis on `b` at all); the junk-value convention (`x / 0 = 0`) makes
-- both sides vanish together whenever `b` (or `b+1`) is a nonpositive
-- integer, so the identity is provable for every `a`, `b`. Feeds
-- `kummerM_hasSum_deriv_total`, infrastructure behind the faithful DLMF
-- 13.3.15 surface `kummerM_hasDerivAt_dlmf` in the `ODE` section below.
/-- Coefficient form of DLMF 13.3.15, with no hypothesis on `b`:
`(n+1)·cₙ₊₁(a,b) = (a/b)·cₙ(a+1,b+1)`. -/
theorem kummerCoefficient_succ_eq_total (n : ℕ) :
    ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) =
      a / b * kummerCoefficient (a + 1) (b + 1) n := by
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfac : (((n + 1)! : ℕ) : 𝕂) = ((n : 𝕂) + 1) * ((n ! : ℕ) : 𝕂) := by
    push_cast [Nat.factorial_succ]
    ring
  simp only [kummerCoefficient, hfac, ascPochhammer_succ_eval' n a, ascPochhammer_succ_eval' n b,
    mul_inv]
  rw [div_eq_mul_inv,
    show ((n : 𝕂) + 1) *
        ((((n : 𝕂) + 1))⁻¹ * ((n ! : ℕ) : 𝕂)⁻¹ * (a * Polynomial.eval (a + 1) (ascPochhammer 𝕂 n)) *
          (b⁻¹ * (Polynomial.eval (b + 1) (ascPochhammer 𝕂 n))⁻¹))
      = (((n : 𝕂) + 1) * (((n : 𝕂) + 1))⁻¹) *
        (((n ! : ℕ) : 𝕂)⁻¹ * Polynomial.eval (a + 1) (ascPochhammer 𝕂 n) *
          (a * b⁻¹) * (Polynomial.eval (b + 1) (ascPochhammer 𝕂 n))⁻¹) by ring]
  rw [mul_inv_cancel₀ hn1, one_mul]
  ring

-- no-dlmf: pure coefficient/Pochhammer-ratio identity, no function, `z`, or
-- incomplete-gamma content; infrastructure for the incomplete-gamma/erf/Fresnel
-- bridges. The faithful DLMF 8.5.1 surface lives in `FLMF/Functions/IncompleteGamma`.
/-- For `a` off the nonpositive integers, the `M(a;a+1;·)` coefficients
collapse: `cₙ(a,a+1) = a/((a+n)·n!)` — the incomplete-gamma/erf/Fresnel
family (DLMF 8.5.1, 7.6.1).

-/
theorem kummerCoefficient_self_succ (n : ℕ) (ha : ∀ k : ℕ, (k : 𝕂) ≠ -a) :
    kummerCoefficient a (a + 1) n = a / ((a + n) * n !) := by
  have hbridge : a * (ascPochhammer 𝕂 n).eval (a + 1)
      = (ascPochhammer 𝕂 n).eval a * (a + n) := by
    rw [← ascPochhammer_succ_eval', ascPochhammer_succ_eval]
  have hP : (ascPochhammer 𝕂 n).eval a ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun k _ => ha k
  have hP1 : (ascPochhammer 𝕂 n).eval (a + 1) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun k _ h => ha (k + 1) (by push_cast; linear_combination h)
  have han : a + (n : 𝕂) ≠ 0 := fun h => ha n (by linear_combination h)
  have hfn : (n ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  simp only [kummerCoefficient]
  field_simp
  linear_combination -hbridge

-- no-dlmf: pure coefficient/Pochhammer identity, no erf function, `z`, sign
-- alternation, or `2/√π` prefactor; infrastructure for the erf/Fresnel bridge.
-- The faithful DLMF 7.6.1 surface lives in `FLMF/Functions/Error`.
/-- `cₙ(1/2, 3/2) = 1/((2n+1)·n!)` — the erf/Fresnel coefficient
(DLMF 7.6.1, 7.11.4).

DLMF 7.6.1.
-/
theorem kummerCoefficient_one_half (n : ℕ) :
    kummerCoefficient ((1 : 𝕂) / 2) (3 / 2) n = 1 / ((2 * n + 1) * n !) := by
  have ha : ∀ k : ℕ, (k : 𝕂) ≠ -((1 : 𝕂) / 2) := by
    intro k hk
    have h2 : ((2 * k + 1 : ℕ) : 𝕂) = 0 := by push_cast; linear_combination 2 * hk
    exact Nat.cast_ne_zero.2 (by lia) h2
  have h := kummerCoefficient_self_succ ((1 : 𝕂) / 2) n ha
  rw [show ((1 : 𝕂) / 2 + 1) = 3 / 2 by norm_num] at h
  have hd1 : ((1 : 𝕂) / 2 + n) ≠ 0 := by
    intro hk
    have h2 : ((2 * n + 1 : ℕ) : 𝕂) = 0 := by push_cast; linear_combination 2 * hk
    exact Nat.cast_ne_zero.2 (by lia) h2
  have hd2 : (2 * (n : 𝕂) + 1) ≠ 0 := by
    intro hk
    have h2 : ((2 * n + 1 : ℕ) : 𝕂) = 0 := by push_cast; linear_combination hk
    exact Nat.cast_ne_zero.2 (by lia) h2
  have hfn : (n ! : 𝕂) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [h, div_eq_div_iff (mul_ne_zero hd1 hfn) (mul_ne_zero hd2 hfn)]
  ring

/-- The three-term coefficient recurrence behind Kummer's equation:
`(n+1)(b+n)·cₙ₊₁ = (a+n)·cₙ`, for `b` not a nonpositive integer. -/
-- no-dlmf: series-coefficient recurrence, no single DLMF equation number
theorem kummerCoefficient_succ_mul (n : ℕ) (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) :
    ((n : 𝕂) + 1) * (b + n) * kummerCoefficient a b (n + 1) =
      (a + n) * kummerCoefficient a b n := by
  have hB : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun kn _ => hb kn
  have hbn : b + (n : 𝕂) ≠ 0 := fun h => hb n (by linear_combination h)
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfac : (((n + 1)! : ℕ) : 𝕂) = ((n : 𝕂) + 1) * ((n ! : ℕ) : 𝕂) := by
    push_cast [Nat.factorial_succ]
    ring
  simp only [kummerCoefficient, hfac, ascPochhammer_succ_eval, mul_inv]
  field_simp

end Coefficients

section Equation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **Kummer's differential equation** (DLMF 13.2.1) as a predicate on an
unknown function: `w` is a solution at the point `z` iff
`z w'' + (b − z) w' − a w = 0`.  This is the bare equation of the DLMF entry,
with no constraint on the parameters `a`, `b` or the variable `z`;
`kummerM_ode` below establishes that Kummer's function `M(a;b;·) = ₁F₁(a;b;·)`
solves it (for `b` not a nonpositive integer), and `tricomiU_kummerODE`
(in `TricomiKummerEq`) does the same for the second standard solution
`U(a,b,·)`. -/
-- DAG: E-13.2.1.
-- Verified: unverified (tier2 DIVERGES)
def IsKummerSolution (a b : 𝕜) (w : 𝕜 → 𝕜) (z : 𝕜) : Prop :=
  z * deriv (deriv w) z + (b - z) * deriv w z - a * w z = 0

end Equation

section ODE

variable {𝕂 : Type*} [RCLike 𝕂] (a b : 𝕂)

/-- The termwise-differentiated Kummer series sums to `(a/b)·M(a+1;b+1;x)`. -/
-- no-dlmf: termwise-derivative infrastructure (the derivative identity is DLMF 13.3.15 elsewhere)
theorem kummerM_hasSum_deriv (hb : b ≠ 0) (x : 𝕂) :
    HasSum (fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      (a / b * ₁F₁ (a + 1) (b + 1) x) := by
  have h := (kummerM_hasSum (a + 1) (b + 1) x).mul_left (a / b)
  have he : (fun n : ℕ => a / b * (kummerCoefficient (a + 1) (b + 1) n * x ^ n)) =
      fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n := by
    funext n
    rw [← mul_assoc, ← kummerCoefficient_succ_eq a b n hb]
  rwa [he] at h

-- no-dlmf: termwise-derivative infrastructure at DLMF's unconstrained strength
-- (no hypothesis on `b`); the derivative identity itself is DLMF 13.3.15,
-- surfaced faithfully as `kummerM_hasDerivAt_dlmf` below.
/-- The termwise-differentiated Kummer series sums to `(a/b)·M(a+1;b+1;x)`, for
every `a`, `b` (no constraint on `b`). -/
theorem kummerM_hasSum_deriv_total (x : 𝕂) :
    HasSum (fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      (a / b * ₁F₁ (a + 1) (b + 1) x) := by
  have h := (kummerM_hasSum (a + 1) (b + 1) x).mul_left (a / b)
  have he : (fun n : ℕ => a / b * (kummerCoefficient (a + 1) (b + 1) n * x ^ n)) =
      fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n := by
    funext n
    rw [← mul_assoc, ← kummerCoefficient_succ_eq_total a b n]
  rwa [he] at h

-- no-dlmf: `b ≠ 0` restricted instance of DLMF 13.3.15; the faithful
-- unconstrained surface (DLMF states no constraint on `a`, `b`, or `z`) is
-- `kummerM_hasDerivAt_dlmf` below.
/-- Derivative of Kummer's function, `HasDerivAt` form, for `b ≠ 0`:
`d/dx M(a;b;x) = (a/b) M(a+1;b+1;x)`. -/
theorem kummerM_hasDerivAt (hb : b ≠ 0) (x : 𝕂) :
    HasDerivAt (₁F₁ a b : 𝕂 → 𝕂) (a / b * ₁F₁ (a + 1) (b + 1) x) x := by
  have h : HasFPowerSeriesOnBall (₁F₁ a b : 𝕂 → 𝕂) (kummerSeries 𝕂 a b) 0 ⊤ :=
    kummerM_hasFPowerSeriesOnBall (𝔸 := 𝕂) a b
  -- the derivative series sums to the Fréchet derivative at `x`
  have hsum : HasSum (fun n : ℕ => (kummerSeries 𝕂 a b).derivSeries n fun _ => x)
      (fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x) := by
    simpa using h.fderiv.hasSum_sub (y := x) (by simp)
  -- evaluate at `1` and identify the coefficients
  have h1 : HasSum (fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      (fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x 1) := by
    have happ := hsum.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
    have he : (fun n : ℕ => ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)
        ((kummerSeries 𝕂 a b).derivSeries n fun _ => x)) =
        fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n := by
      funext n
      rw [ContinuousLinearMap.apply_apply,
        apply_eq_pow_smul_coeff (p := (kummerSeries 𝕂 a b).derivSeries) (n := n) (z := x),
        ContinuousLinearMap.smul_apply, derivSeries_coeff_one,
        show (kummerSeries 𝕂 a b).coeff (n + 1) = kummerCoefficient a b (n + 1) from by
          rw [kummerSeries, coeff_ofScalars]]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rwa [he] at happ
  have hfd : fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x 1 = a / b * ₁F₁ (a + 1) (b + 1) x :=
    h1.unique (kummerM_hasSum_deriv a b hb x)
  have hdiff : DifferentiableAt 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x :=
    (h.analyticOnNhd x (by simp)).differentiableAt
  have hda := hdiff.hasDerivAt
  rwa [← fderiv_apply_one_eq_deriv, hfd] at hda

-- no-dlmf: `RCLike`-general form; DLMF's `a,b,z` are complex parameters, not
-- elements of an abstract `RCLike` field; faithful surface is
-- `kummerM_hasDerivAt_dlmf_complex`
/-- `HasDerivAt` form of Kummer's derivative identity, with no constraint on
`a`, `b`, or `x`: `d/dx M(a;b;x) = (a/b) M(a+1;b+1;x)`. The `b = 0` case (and
more generally `b` a nonpositive integer) holds through the junk-value
convention `_/0 = 0`: it collapses the coefficient prefactor `a/b` and the
`b`-indexed Pochhammer denominators to `0` in lockstep, so the identity is
`0 = 0` there.
-/
theorem kummerM_hasDerivAt_dlmf (x : 𝕂) :
    HasDerivAt (₁F₁ a b : 𝕂 → 𝕂) (a / b * ₁F₁ (a + 1) (b + 1) x) x := by
  have h : HasFPowerSeriesOnBall (₁F₁ a b : 𝕂 → 𝕂) (kummerSeries 𝕂 a b) 0 ⊤ :=
    kummerM_hasFPowerSeriesOnBall (𝔸 := 𝕂) a b
  -- the derivative series sums to the Fréchet derivative at `x`
  have hsum : HasSum (fun n : ℕ => (kummerSeries 𝕂 a b).derivSeries n fun _ => x)
      (fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x) := by
    simpa using h.fderiv.hasSum_sub (y := x) (by simp)
  -- evaluate at `1` and identify the coefficients
  have h1 : HasSum (fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      (fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x 1) := by
    have happ := hsum.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
    have he : (fun n : ℕ => ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)
        ((kummerSeries 𝕂 a b).derivSeries n fun _ => x)) =
        fun n : ℕ => ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n := by
      funext n
      rw [ContinuousLinearMap.apply_apply,
        apply_eq_pow_smul_coeff (p := (kummerSeries 𝕂 a b).derivSeries) (n := n) (z := x),
        ContinuousLinearMap.smul_apply, derivSeries_coeff_one,
        show (kummerSeries 𝕂 a b).coeff (n + 1) = kummerCoefficient a b (n + 1) from by
          rw [kummerSeries, coeff_ofScalars]]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rwa [he] at happ
  have hfd : fderiv 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x 1 = a / b * ₁F₁ (a + 1) (b + 1) x :=
    h1.unique (kummerM_hasSum_deriv_total a b x)
  have hdiff : DifferentiableAt 𝕂 (₁F₁ a b : 𝕂 → 𝕂) x :=
    (h.analyticOnNhd x (by simp)).differentiableAt
  have hda := hdiff.hasDerivAt
  rwa [← fderiv_apply_one_eq_deriv, hfd] at hda

/-- **DLMF 13.3.15.** `d/dx M(a;b;x) = (a/b) M(a+1;b+1;x)`, for complex
`a`, `b`, `x`, with no constraint on `a`, `b`, or `x` (DLMF states none).

DAG: E-13.3.15.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem kummerM_hasDerivAt_dlmf_complex (a b x : ℂ) :
    HasDerivAt (₁F₁ a b : ℂ → ℂ) (a / b * ₁F₁ (a + 1) (b + 1) x) x :=
  kummerM_hasDerivAt_dlmf a b x

-- no-dlmf: strictly-more-general total form (`b ≠ 0` only); DLMF's full
-- unconstrained strength is carried by the faithful surface
-- `kummerM_deriv_dlmf` below.
/-- `deriv` form of Kummer's derivative identity, for `b ≠ 0`. -/
theorem kummerM_deriv (hb : b ≠ 0) (x : 𝕂) :
    deriv (₁F₁ a b : 𝕂 → 𝕂) x = a / b * ₁F₁ (a + 1) (b + 1) x :=
  (kummerM_hasDerivAt a b hb x).deriv

/-- **DLMF 13.3.15**, `deriv` form, with no constraint on `a`, `b`, or `x` (DLMF
states none): `d/dx M(a;b;x) = (a/b) M(a+1;b+1;x)`.

DAG: E-13.3.15.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem kummerM_deriv_dlmf (x : 𝕂) :
    deriv (₁F₁ a b : 𝕂 → 𝕂) x = a / b * ₁F₁ (a + 1) (b + 1) x :=
  (kummerM_hasDerivAt_dlmf a b x).deriv

-- no-dlmf: instance of DLMF 13.2.1 (the unknown `w` fixed to `₁F₁ a b`, plus a
-- pole-avoidance hypothesis on `b`); the faithful surface of the bare equation
-- is the `IsKummerSolution` definition above.
/-- **Kummer's equation for `M`**: `M(a;b;·)` solves
`z w'' + (b − z) w' − a w = 0`, for `b` not a nonpositive integer. -/
theorem kummerM_ode (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) (x : 𝕂) :
    x * deriv (deriv (₁F₁ a b : 𝕂 → 𝕂)) x
      + (b - x) * deriv (₁F₁ a b : 𝕂 → 𝕂) x - a * ₁F₁ a b x = 0 := by
  have hb0 : b ≠ 0 := by
    intro h
    exact hb 0 (by simp [h])
  have hb1 : b + 1 ≠ 0 := by
    intro h
    exact hb 1 (by push_cast; linear_combination h)
  -- the first and second derivatives, through DLMF 13.3.15
  have hM' : deriv (₁F₁ a b : 𝕂 → 𝕂) = fun y => a / b * ₁F₁ (a + 1) (b + 1) y :=
    funext fun y => kummerM_deriv a b hb0 y
  have hM'' : deriv (deriv (₁F₁ a b : 𝕂 → 𝕂)) x
      = a / b * ((a + 1) / (b + 1) * ₁F₁ (a + 1 + 1) (b + 1 + 1) x) := by
    rw [hM',
      deriv_const_mul _ ((kummerM_hasDerivAt (a + 1) (b + 1) hb1 x).differentiableAt),
      kummerM_deriv (a + 1) (b + 1) hb1 x]
  -- the four constituent series, all aligned to exponent `n`
  have hA := kummerM_hasSum_deriv a b hb0 x
  have hC : HasSum (fun n : ℕ => ((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
      * kummerCoefficient a b (n + 1 + 1) * x ^ n)
      (a / b * ((a + 1) / (b + 1) * ₁F₁ (a + 1 + 1) (b + 1 + 1) x)) := by
    have h := (kummerM_hasSum_deriv (a + 1) (b + 1) hb1 x).mul_left (a / b)
    have he : (fun n : ℕ => a / b * (((n : 𝕂) + 1) * kummerCoefficient (a + 1) (b + 1) (n + 1)
        * x ^ n)) = fun n : ℕ => ((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
        * kummerCoefficient a b (n + 1 + 1) * x ^ n := by
      funext n
      have hshift := kummerCoefficient_succ_eq a b (n + 1) hb0
      push_cast at hshift
      linear_combination (((n : 𝕂) + 1) * x ^ n) * hshift.symm
    rwa [he] at h
  -- reindex `x·M''` and `x·M'` down by one exponent
  have hF : HasSum (fun n : ℕ => (n : 𝕂) * ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      (x * (a / b * ((a + 1) / (b + 1) * ₁F₁ (a + 1 + 1) (b + 1 + 1) x))) := by
    have h := hC.mul_left x
    have he : (fun n : ℕ => x * (((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
        * kummerCoefficient a b (n + 1 + 1) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : 𝕂)) * (((n + 1 : ℕ) : 𝕂) + 1)
          * kummerCoefficient a b (n + 1 + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff
      (f := fun n : ℕ => (n : 𝕂) * ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n) 1).mp h
    simpa using h2
  have hG : HasSum (fun n : ℕ => (n : 𝕂) * kummerCoefficient a b n * x ^ n)
      (x * (a / b * ₁F₁ (a + 1) (b + 1) x)) := by
    have h := hA.mul_left x
    have he : (fun n : ℕ => x * (((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : 𝕂)) * kummerCoefficient a b (n + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff
      (f := fun n : ℕ => (n : 𝕂) * kummerCoefficient a b n * x ^ n) 1).mp h
    simpa using h2
  -- combine: the termwise recurrence kills every coefficient
  have hT := ((hF.add (hA.mul_left b)).sub hG).sub ((kummerM_hasSum a b x).mul_left a)
  have hzero : (fun n : ℕ => (n : 𝕂) * ((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n
      + b * (((n : 𝕂) + 1) * kummerCoefficient a b (n + 1) * x ^ n)
      - (n : 𝕂) * kummerCoefficient a b n * x ^ n
      - a * (kummerCoefficient a b n * x ^ n)) = fun _ => (0 : 𝕂) := by
    funext n
    linear_combination x ^ n * kummerCoefficient_succ_mul a b n hb
  rw [hzero] at hT
  have hT0 := hT.unique hasSum_zero
  rw [hM'']
  simp only [hM']
  linear_combination hT0

end ODE

end FLMF.Hypergeometric
