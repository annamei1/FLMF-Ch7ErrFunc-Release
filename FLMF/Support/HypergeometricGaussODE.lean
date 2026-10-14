import FLMF.Support.HypergeometricGauss
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The hypergeometric differential equation for `₂F₁` (framework — DLMF §15.5, §15.10)

The derivative of the Gauss hypergeometric function and the hypergeometric
equation, on the unit disc and for parameters off the nonpositive integers:

* `ordinaryHypergeometric_hasDerivAt_of_c` / `ordinaryHypergeometric_deriv_of_c`
  — `d/dz ₂F₁(a,b;c;z) = (ab/c) ₂F₁(a+1,b+1;c+1;z)` (DLMF 15.5.1), for `c` off
  the nonpositive integers (`a`, `b` unrestricted, matching DLMF); the older
  `ordinaryHypergeometric_hasDerivAt` / `ordinaryHypergeometric_deriv` also
  exclude `a`, `b` and remain as narrower instances.
* `ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c` — the same `c`-only
  relaxation of DLMF 15.2.1.
* `ordinaryHypergeometric_ode` — `z(1−z) w'' + (c − (a+b+1)z) w' − ab w = 0`
  (DLMF 15.10.1).

The series has radius `1` (`ordinaryHypergeometricSeries_radius_eq_one`), so on
`‖z‖ < 1` termwise differentiation goes through Mathlib's
`HasFPowerSeriesOnBall.fderiv`, exactly as in `KummerODE`; the coefficients are
identified by the shift `(n+1)·γₙ₊₁(a,b,c) = (ab/c)·γₙ(a+1,b+1,c+1)` and the ODE
vanishes termwise by the recurrence `(n+1)(c+n)·γₙ₊₁ = (a+n)(b+n)·γₙ`.
-/

open Nat FormalMultilinearSeries

namespace FLMF.Hypergeometric

section Coefficients

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b c : 𝕂)

-- no-dlmf: coefficient-level shift lemma, not the function-level DLMF 15.5.1
-- derivative identity (that faithful surface is `ordinaryHypergeometric_hasDerivAt`
-- below); infrastructure feeding the termwise-derivative argument.
/-- Coefficient form of DLMF 15.5.1: `(n+1)·γₙ₊₁(a,b,c) = (ab/c)·γₙ(a+1,b+1,c+1)`.
Holds for all `a`, `b` (including terminating cases) as long as `c ≠ 0`.

DLMF 15.5.1.
-/
theorem ordinaryHypergeometricCoefficient_succ_eq (n : ℕ) (hc : c ≠ 0) :
    ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      a * b / c * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfac : (((n + 1)! : ℕ) : 𝕂) = ((n : 𝕂) + 1) * ((n ! : ℕ) : 𝕂) := by
    push_cast [Nat.factorial_succ]
    ring
  simp only [ordinaryHypergeometricCoefficient, hfac, ascPochhammer_succ_eval' n a,
    ascPochhammer_succ_eval' n b, ascPochhammer_succ_eval' n c, mul_inv]
  field_simp

/-- The three-term coefficient recurrence behind the hypergeometric equation:
`(n+1)(c+n)·γₙ₊₁ = (a+n)(b+n)·γₙ`, for `c` not a nonpositive integer. -/
-- no-dlmf: series-coefficient recurrence, no single DLMF equation number
theorem ordinaryHypergeometricCoefficient_succ_mul (n : ℕ) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) :
    ((n : 𝕂) + 1) * (c + n) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      (a + n) * (b + n) * ordinaryHypergeometricCoefficient a b c n := by
  have hC : (ascPochhammer 𝕂 n).eval c ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    push Not
    exact fun kn _ => hc kn
  have hcn : c + (n : 𝕂) ≠ 0 := fun h => hc n (by linear_combination h)
  have hn1 : ((n : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hfac : (((n + 1)! : ℕ) : 𝕂) = ((n : 𝕂) + 1) * ((n ! : ℕ) : 𝕂) := by
    push_cast [Nat.factorial_succ]
    ring
  simp only [ordinaryHypergeometricCoefficient, hfac, ascPochhammer_succ_eval, mul_inv]
  field_simp

end Coefficients

section ODE

variable {𝕂 : Type*} [RCLike 𝕂] (a b c : 𝕂)

/-- Shifting all parameters up by one preserves "no parameter is a nonpositive
integer". -/
-- no-dlmf: parameter-shift bookkeeping helper, no DLMF counterpart
theorem ordinaryHypergeometric_param_succ_ne
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) (kn : ℕ) :
    (kn : 𝕂) ≠ -(a + 1) ∧ (kn : 𝕂) ≠ -(b + 1) ∧ (kn : 𝕂) ≠ -(c + 1) :=
  ⟨fun h => (habc (kn + 1)).1 (by push_cast; linear_combination h),
   fun h => (habc (kn + 1)).2.1 (by push_cast; linear_combination h),
   fun h => (habc (kn + 1)).2.2 (by push_cast; linear_combination h)⟩

-- no-dlmf: real/narrowed restriction of DLMF 15.2.1 (excludes `a`, `b` off the
-- nonpositive integers beyond DLMF's own c-only restriction); faithful surface
-- is `ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c`
/-- For parameters off the nonpositive integers, `₂F₁(a,b;c;·)` is the sum of
its power series on the unit ball.  The §15.1 notation display DLMF 15.1.1,
which introduces the symbol `F(a,b;c;z) = ₂F₁(a,b;c;z)` for precisely this
function, is surfaced by this declaration.
-/
theorem ordinaryHypergeometric_hasFPowerSeriesOnBall
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c) :
    HasFPowerSeriesOnBall (₂F₁ a b c : 𝕂 → 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c) 0 1 := by
  have h := (ordinaryHypergeometricSeries 𝕂 a b c).hasFPowerSeriesOnBall
    (by rw [ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc]; norm_num)
  rwa [ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc] at h

-- no-dlmf: chain link 15.2.1 (assembled in hypergeometric_15_2_1)
/-- **DLMF 15.2.1**, `c`-hypothesis alone: for any `a`, `b`, and `c` off the
nonpositive integers, `₂F₁(a,b;c;·)` is the sum of its power series on the
unit ball.  Unlike `ordinaryHypergeometric_hasFPowerSeriesOnBall`, `a` and `b`
are unrestricted: DLMF only asserts that `F(a,b;c;z)` fails to exist in
general at `c = 0,-1,-2,…`; terminating cases with `a` or `b` a nonpositive
integer are included (the series is then a polynomial, of radius `⊤ ≥ 1`,
still valid on the unit ball).
-/
theorem ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) :
    HasFPowerSeriesOnBall (₂F₁ a b c : 𝕂 → 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c) 0 1 := by
  have hrad : 1 ≤ (ordinaryHypergeometricSeries 𝕂 a b c).radius := by
    by_cases ha : ∃ k : ℕ, (k : 𝕂) = -a
    · obtain ⟨k, hk⟩ := ha
      have hae : a = -(k : 𝕂) := by linear_combination hk
      rw [hae, ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    · by_cases hb : ∃ k : ℕ, (k : 𝕂) = -b
      · obtain ⟨k, hk⟩ := hb
        have hbe : b = -(k : 𝕂) := by linear_combination hk
        rw [hbe, ordinaryHypergeometric_radius_top_of_neg_nat₂]
        exact le_top
      · push Not at ha hb
        rw [ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c
          (fun kn => ⟨ha kn, hb kn, hc kn⟩)]
  exact ((ordinaryHypergeometricSeries 𝕂 a b c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le zero_lt_one hrad)).mono zero_lt_one hrad

/-- `HasSum` form of the Gauss series on the unit ball. -/
-- no-dlmf: HasSum repackaging of the series (the series is DLMF 15.2.1 above)
theorem ordinaryHypergeometric_hasSum
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n * x ^ n) (₂F₁ a b c x) := by
  have h := (ordinaryHypergeometric_hasFPowerSeriesOnBall a b c habc).hasSum_sub
    (y := x) (by rw [mem_eball_zero_iff, ← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hx)
  simpa only [sub_zero, ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] using h

/-- The termwise-differentiated Gauss series sums to `(ab/c)·₂F₁(a+1,b+1;c+1;x)`
on the unit ball. -/
-- no-dlmf: termwise-derivative infrastructure (the derivative identity is DLMF 15.5.1 below)
theorem ordinaryHypergeometric_hasSum_deriv
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x) := by
  have hc0 : c ≠ 0 := fun h => (habc 0).2.2 (by simp [h])
  have h := (ordinaryHypergeometric_hasSum (a + 1) (b + 1) (c + 1)
    (ordinaryHypergeometric_param_succ_ne a b c habc) hx).mul_left (a * b / c)
  have he : (fun n : ℕ => a * b / c
      * (ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n * x ^ n)) =
      fun n : ℕ => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n := by
    funext n
    rw [← mul_assoc, ← ordinaryHypergeometricCoefficient_succ_eq a b c n hc0]
  rwa [he] at h

-- no-dlmf: real/narrowed restriction of DLMF 15.5.1 (excludes `a`, `b` off the
-- nonpositive integers beyond DLMF's own c-only restriction); faithful surface
-- is `ordinaryHypergeometric_hasDerivAt_of_c`
/-- **Derivative of the Gauss hypergeometric function**:
`d/dx ₂F₁(a,b;c;x) = (ab/c) ₂F₁(a+1,b+1;c+1;x)` on the unit ball, for
parameters off the nonpositive integers.
-/
theorem ordinaryHypergeometric_hasDerivAt
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    HasDerivAt (₂F₁ a b c : 𝕂 → 𝕂) (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x) x := by
  have hxe : x ∈ Metric.eball (0 : 𝕂) 1 := by
    rw [mem_eball_zero_iff, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hx
  have h := ordinaryHypergeometric_hasFPowerSeriesOnBall a b c habc
  -- the derivative series sums to the Fréchet derivative at `x`
  have hsum : HasSum (fun n : ℕ => (ordinaryHypergeometricSeries 𝕂 a b c).derivSeries n
      fun _ => x) (fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x) := by
    simpa using h.fderiv.hasSum_sub (y := x) hxe
  -- evaluate at `1` and identify the coefficients
  have h1 : HasSum (fun n : ℕ => ((n : 𝕂) + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x 1) := by
    have happ := hsum.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
    have he : (fun n : ℕ => ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)
        ((ordinaryHypergeometricSeries 𝕂 a b c).derivSeries n fun _ => x)) =
        fun n : ℕ => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n := by
      funext n
      rw [ContinuousLinearMap.apply_apply,
        apply_eq_pow_smul_coeff (p := (ordinaryHypergeometricSeries 𝕂 a b c).derivSeries)
          (n := n) (z := x),
        ContinuousLinearMap.smul_apply, derivSeries_coeff_one,
        show (ordinaryHypergeometricSeries 𝕂 a b c).coeff (n + 1)
            = ordinaryHypergeometricCoefficient a b c (n + 1) from by
          rw [ordinaryHypergeometricSeries, coeff_ofScalars]]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rwa [he] at happ
  have hfd : fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x 1 = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x :=
    h1.unique (ordinaryHypergeometric_hasSum_deriv a b c habc hx)
  have hdiff : DifferentiableAt 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x :=
    (h.analyticOnNhd x hxe).differentiableAt
  have hda := hdiff.hasDerivAt
  rwa [← fderiv_apply_one_eq_deriv, hfd] at hda

-- no-dlmf: real/narrowed restriction of DLMF 15.5.1 (excludes `a`, `b` off the
-- nonpositive integers beyond DLMF's own c-only restriction); faithful surface
-- is `ordinaryHypergeometric_deriv_of_c`
/-- `deriv` form of the derivative of the Gauss hypergeometric function, for
parameters off the nonpositive integers. -/
theorem ordinaryHypergeometric_deriv
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    deriv (₂F₁ a b c : 𝕂 → 𝕂) x = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x :=
  (ordinaryHypergeometric_hasDerivAt a b c habc hx).deriv

-- no-dlmf: instance of DLMF 15.10.1 (the unspecified solution `w` fixed to
-- `₂F₁(a,b;c;·)`); faithful surfaces are `SolvesGaussODEOn`
-- (Ch15LogarithmicSolutions) and `gaussEquationSolutionsOn`
-- (Ch15RiemannSDifferential)
/-- **The hypergeometric equation for `₂F₁`**: `₂F₁(a,b;c;·)` solves
`z(1−z) w'' + (c − (a+b+1)z) w' − ab w = 0` (DLMF 15.10.1 with `w = ₂F₁`) on
the unit ball, for parameters off the nonpositive integers. -/
theorem ordinaryHypergeometric_ode
    (habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c)
    {x : 𝕂} (hx : ‖x‖ < 1) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c : 𝕂 → 𝕂)) x
      + (c - (a + b + 1) * x) * deriv (₂F₁ a b c : 𝕂 → 𝕂) x
      - a * b * ₂F₁ a b c x = 0 := by
  have habc' := ordinaryHypergeometric_param_succ_ne a b c habc
  have hc0 : c ≠ 0 := fun h => (habc 0).2.2 (by simp [h])
  -- the second derivative at `x`, through the local first-derivative identity
  have hEv : deriv (₂F₁ a b c : 𝕂 → 𝕂) =ᶠ[nhds x]
      fun y => a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) y := by
    have hball : Metric.ball (0 : 𝕂) 1 ∈ nhds x :=
      Metric.isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [hball] with y hy
    exact ordinaryHypergeometric_deriv a b c habc (by simpa using hy)
  have hM'' : deriv (deriv (₂F₁ a b c : 𝕂 → 𝕂)) x
      = a * b / c * ((a + 1) * (b + 1) / (c + 1)
        * ₂F₁ (a + 1 + 1) (b + 1 + 1) (c + 1 + 1) x) := by
    rw [hEv.deriv_eq,
      deriv_const_mul _ ((ordinaryHypergeometric_hasDerivAt (a + 1) (b + 1) (c + 1)
        habc' hx).differentiableAt),
      ordinaryHypergeometric_deriv (a + 1) (b + 1) (c + 1) habc' hx]
  -- the constituent series, all aligned to exponent `n`
  have h0 := ordinaryHypergeometric_hasSum a b c habc hx
  have hA := ordinaryHypergeometric_hasSum_deriv a b c habc hx
  have hC : HasSum (fun n : ℕ => ((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ n)
      (a * b / c * ((a + 1) * (b + 1) / (c + 1)
        * ₂F₁ (a + 1 + 1) (b + 1 + 1) (c + 1 + 1) x)) := by
    have h := (ordinaryHypergeometric_hasSum_deriv (a + 1) (b + 1) (c + 1)
      habc' hx).mul_left (a * b / c)
    have he : (fun n : ℕ => a * b / c * (((n : 𝕂) + 1)
        * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) (n + 1) * x ^ n)) =
        fun n : ℕ => ((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
          * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ n := by
      funext n
      have hshift := ordinaryHypergeometricCoefficient_succ_eq a b c (n + 1) hc0
      push_cast at hshift
      linear_combination (((n : 𝕂) + 1) * x ^ n) * hshift.symm
    rwa [he] at h
  -- reindex `x·w''`, `x²·w''` and `x·w'` down to exponent `n`
  have hF : HasSum (fun n : ℕ => (n : 𝕂) * ((n : 𝕂) + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (x * (a * b / c * ((a + 1) * (b + 1) / (c + 1)
        * ₂F₁ (a + 1 + 1) (b + 1 + 1) (c + 1 + 1) x))) := by
    have h := hC.mul_left x
    have he : (fun n : ℕ => x * (((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
        * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : 𝕂)) * (((n + 1 : ℕ) : 𝕂) + 1)
          * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => (n : 𝕂) * ((n : 𝕂) + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n) 1).mp h
    simpa using h2
  have hF2 : HasSum (fun n : ℕ => ((n : 𝕂) - 1) * (n : 𝕂)
      * ordinaryHypergeometricCoefficient a b c n * x ^ n)
      (x * (x * (a * b / c * ((a + 1) * (b + 1) / (c + 1)
        * ₂F₁ (a + 1 + 1) (b + 1 + 1) (c + 1 + 1) x)))) := by
    have h := (hC.mul_left x).mul_left x
    have he : (fun n : ℕ => x * (x * (((n : 𝕂) + 1) * ((n : 𝕂) + 1 + 1)
        * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ n))) =
        fun n : ℕ => (((n + 1 + 1 : ℕ) : 𝕂) - 1) * ((n + 1 + 1 : ℕ) : 𝕂)
          * ordinaryHypergeometricCoefficient a b c (n + 1 + 1) * x ^ (n + 1 + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => ((n : 𝕂) - 1) * (n : 𝕂)
      * ordinaryHypergeometricCoefficient a b c n * x ^ n) 2).mp h
    simpa [Finset.sum_range_succ] using h2
  have hG : HasSum (fun n : ℕ => (n : 𝕂) * ordinaryHypergeometricCoefficient a b c n * x ^ n)
      (x * (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x)) := by
    have h := hA.mul_left x
    have he : (fun n : ℕ => x * (((n : 𝕂) + 1)
        * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : 𝕂))
          * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ =>
      (n : 𝕂) * ordinaryHypergeometricCoefficient a b c n * x ^ n) 1).mp h
    simpa using h2
  -- combine: the termwise recurrence kills every coefficient
  have hT := (((hF.sub hF2).add (hA.mul_left c)).sub (hG.mul_left (a + b + 1))).sub
    (h0.mul_left (a * b))
  have hzero : (fun n : ℕ => ((n : 𝕂) * ((n : 𝕂) + 1)
        * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n
      - ((n : 𝕂) - 1) * (n : 𝕂) * ordinaryHypergeometricCoefficient a b c n * x ^ n)
      + c * (((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      - (a + b + 1) * ((n : 𝕂) * ordinaryHypergeometricCoefficient a b c n * x ^ n)
      - a * b * (ordinaryHypergeometricCoefficient a b c n * x ^ n)) = fun _ => (0 : 𝕂) := by
    funext n
    linear_combination x ^ n * ordinaryHypergeometricCoefficient_succ_mul a b c n
      (fun kn => (habc kn).2.2)
  rw [hzero] at hT
  have hT0 := hT.unique hasSum_zero
  rw [hM'']
  rw [show deriv (₂F₁ a b c : 𝕂 → 𝕂) x = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x from
    ordinaryHypergeometric_deriv a b c habc hx]
  linear_combination hT0

end ODE

section HcOnly

variable {𝕂 : Type*} [RCLike 𝕂]

/-- **DLMF 15.5.1**, `c`-hypothesis alone: `d/dx ₂F₁(a,b;c;x) = (ab/c)
₂F₁(a+1,b+1;c+1;x)` on the unit ball, assuming only that `c` is off the
nonpositive integers.  Unlike `ordinaryHypergeometric_hasDerivAt`, the
parameters `a`, `b` are unrestricted: if either is a nonpositive integer the
series terminates and has radius `⊤`, otherwise all three parameters are off
the nonpositive integers and the radius is `1`; either way the radius is `≥ 1`
and termwise differentiation on `‖x‖ < 1` goes through.

DAG: E-15.5.1.
Numerical: PASS
Verified: unverified
-/
theorem ordinaryHypergeometric_hasDerivAt_of_c (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasDerivAt (₂F₁ a b c : 𝕂 → 𝕂) (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x) x := by
  have hc0 : c ≠ 0 := fun h => hc 0 (by simp [h])
  -- the series has radius `≥ 1` under the `c`-hypothesis alone, hence is a power
  -- series for `₂F₁` on the unit ball (for any parameters `a'`, `b'`)
  have hball : ∀ a' b' c' : 𝕂, (∀ k : ℕ, (k : 𝕂) ≠ -c') →
      HasFPowerSeriesOnBall (₂F₁ a' b' c' : 𝕂 → 𝕂)
        (ordinaryHypergeometricSeries 𝕂 a' b' c') 0 1 := by
    intro a' b' c' hc'
    have hrad : 1 ≤ (ordinaryHypergeometricSeries 𝕂 a' b' c').radius := by
      by_cases ha : ∃ k : ℕ, (k : 𝕂) = -a'
      · obtain ⟨k, hk⟩ := ha
        have hae : a' = -(k : 𝕂) := by linear_combination hk
        rw [hae, ordinaryHypergeometric_radius_top_of_neg_nat₁]
        exact le_top
      · by_cases hb : ∃ k : ℕ, (k : 𝕂) = -b'
        · obtain ⟨k, hk⟩ := hb
          have hbe : b' = -(k : 𝕂) := by linear_combination hk
          rw [hbe, ordinaryHypergeometric_radius_top_of_neg_nat₂]
          exact le_top
        · push Not at ha hb
          rw [ordinaryHypergeometricSeries_radius_eq_one 𝕂 a' b' c'
            (fun kn => ⟨ha kn, hb kn, hc' kn⟩)]
    exact ((ordinaryHypergeometricSeries 𝕂 a' b' c').hasFPowerSeriesOnBall
      (lt_of_lt_of_le zero_lt_one hrad)).mono zero_lt_one hrad
  -- `HasSum` form of the Gauss series on the unit ball, `c`-hypothesis only
  have hsum : ∀ a' b' c' : 𝕂, (∀ k : ℕ, (k : 𝕂) ≠ -c') → ∀ {y : 𝕂}, ‖y‖ < 1 →
      HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a' b' c' n * y ^ n)
        (₂F₁ a' b' c' y) := by
    intro a' b' c' hc' y hy
    have h := (hball a' b' c' hc').hasSum_sub
      (y := y) (by rw [mem_eball_zero_iff, ← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hy)
    simpa only [sub_zero, ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] using h
  -- the termwise-differentiated series sums to `(ab/c)·₂F₁(a+1,b+1;c+1;x)`
  have hc1 : ∀ k : ℕ, (k : 𝕂) ≠ -(c + 1) := fun k h =>
    hc (k + 1) (by push_cast; linear_combination h)
  have hA : HasSum (fun n : ℕ => ((n : 𝕂) + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x) := by
    have h := (hsum (a + 1) (b + 1) (c + 1) hc1 hx).mul_left (a * b / c)
    have he : (fun n : ℕ => a * b / c
        * (ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n * x ^ n)) =
        fun n : ℕ => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n := by
      funext n
      rw [← mul_assoc, ← ordinaryHypergeometricCoefficient_succ_eq a b c n hc0]
    rwa [he] at h
  -- termwise differentiation through Mathlib's power-series derivative
  have hxe : x ∈ Metric.eball (0 : 𝕂) 1 := by
    rw [mem_eball_zero_iff, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr hx
  have h := hball a b c hc
  have hsumd : HasSum (fun n : ℕ => (ordinaryHypergeometricSeries 𝕂 a b c).derivSeries n
      fun _ => x) (fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x) := by
    simpa using h.fderiv.hasSum_sub (y := x) hxe
  have h1 : HasSum (fun n : ℕ => ((n : 𝕂) + 1)
      * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x 1) := by
    have happ := hsumd.mapL (ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂))
    have he : (fun n : ℕ => ContinuousLinearMap.apply 𝕂 𝕂 (1 : 𝕂)
        ((ordinaryHypergeometricSeries 𝕂 a b c).derivSeries n fun _ => x)) =
        fun n : ℕ => ((n : 𝕂) + 1) * ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n := by
      funext n
      rw [ContinuousLinearMap.apply_apply,
        apply_eq_pow_smul_coeff (p := (ordinaryHypergeometricSeries 𝕂 a b c).derivSeries)
          (n := n) (z := x),
        ContinuousLinearMap.smul_apply, derivSeries_coeff_one,
        show (ordinaryHypergeometricSeries 𝕂 a b c).coeff (n + 1)
            = ordinaryHypergeometricCoefficient a b c (n + 1) from by
          rw [ordinaryHypergeometricSeries, coeff_ofScalars]]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rwa [he] at happ
  have hfd : fderiv 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x 1 = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x :=
    h1.unique hA
  have hdiff : DifferentiableAt 𝕂 (₂F₁ a b c : 𝕂 → 𝕂) x :=
    (h.analyticOnNhd x hxe).differentiableAt
  have hda := hdiff.hasDerivAt
  rwa [← fderiv_apply_one_eq_deriv, hfd] at hda

/-- **DLMF 15.5.1**, `deriv` form, `c`-hypothesis alone: `d/dx ₂F₁(a,b;c;x) =
(ab/c) ₂F₁(a+1,b+1;c+1;x)` on the unit ball, for any `a`, `b` and `c` off the
nonpositive integers.

DAG: E-15.5.1.
Numerical: PASS
Verified: unverified
-/
theorem ordinaryHypergeometric_deriv_of_c (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    deriv (₂F₁ a b c : 𝕂 → 𝕂) x = a * b / c * ₂F₁ (a + 1) (b + 1) (c + 1) x :=
  (ordinaryHypergeometric_hasDerivAt_of_c a b c hc hx).deriv

open Filter Topology Set Metric ENNReal NNReal in
-- no-dlmf: hc-only strengthening of `ordinaryHypergeometric_ode` (DLMF 15.10.1)
/-- **The hypergeometric equation under the `c`-hypothesis alone**:
`₂F₁(a,b;c;·)` solves the Gauss equation on the unit ball whenever only the
lower parameter is off the nonpositive integers.  This includes terminating
upper parameters, which the older three-parameter regularity theorem excludes. -/
theorem ordinaryHypergeometric_ode_of_c (a b c : ℂ)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) {x : ℂ} (hx : ‖x‖ < 1) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c : ℂ → ℂ)) x
      + (c - (a + b + 1) * x) * deriv (₂F₁ a b c : ℂ → ℂ) x
      - a * b * ₂F₁ a b c x = 0 := by
  have hrad : 1 ≤ (ordinaryHypergeometricSeries ℂ a b c).radius := by
    by_cases ha : ∃ k : ℕ, (k : ℂ) = -a
    · obtain ⟨k, hk⟩ := ha
      have hae : a = -(k : ℂ) := by linear_combination hk
      rw [hae, ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    · by_cases hb : ∃ k : ℕ, (k : ℂ) = -b
      · obtain ⟨k, hk⟩ := hb
        have hbe : b = -(k : ℂ) := by linear_combination hk
        rw [hbe, ordinaryHypergeometric_radius_top_of_neg_nat₂]
        exact le_top
      · push Not at ha hb
        rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b c
          (fun kn => ⟨ha kn, hb kn, hc kn⟩)]
  have hB : HasFPowerSeriesOnBall (₂F₁ a b c : ℂ → ℂ)
      (ordinaryHypergeometricSeries ℂ a b c) 0 1 :=
    ((ordinaryHypergeometricSeries ℂ a b c).hasFPowerSeriesOnBall
      (lt_of_lt_of_le zero_lt_one hrad)).mono zero_lt_one hrad
  have hderiv_scalar : ∀ {f : ℂ → ℂ}
      {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞},
      HasFPowerSeriesOnBall f p 0 r →
      ∃ q : FormalMultilinearSeries ℂ ℂ ℂ,
        HasFPowerSeriesOnBall (deriv f) q 0 r ∧
        ∀ n : ℕ, q.coeff n = ((n : ℂ) + 1) * p.coeff (n + 1) := by
    intro f p r h
    refine ⟨(ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      p.derivSeries, ?_, ?_⟩
    · have hf := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall
        h.fderiv
      have he : (⇑(ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) ∘ fderiv ℂ f) =
          deriv f := by
        funext z
        exact fderiv_apply_one_eq_deriv
      rwa [he] at hf
    · intro n
      have h1 : ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
          p.derivSeries).coeff n =
          (p.derivSeries.coeff n) 1 := by
        simp only [FormalMultilinearSeries.coeff,
          ContinuousLinearMap.compFormalMultilinearSeries_apply,
          ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
          ContinuousLinearMap.apply_apply]
      rw [h1, FormalMultilinearSeries.derivSeries_coeff_one]
      push_cast [nsmul_eq_mul]
      ring
  have hsum_coeff : ∀ {f : ℂ → ℂ}
      {q : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞},
      HasFPowerSeriesOnBall f q 0 r → ∀ {y : ℂ},
      (‖y‖₊ : ℝ≥0∞) < r →
      HasSum (fun n : ℕ => q.coeff n * y ^ n) (f y) := by
    intro f q r h y hy
    have hmem : y ∈ Metric.eball (0 : ℂ) r := by
      rwa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    have hs := h.hasSum_sub hmem
    simp only [sub_zero] at hs
    refine hs.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
    ring
  obtain ⟨q₁, hq₁ball, hq₁c⟩ := hderiv_scalar hB
  obtain ⟨q₂, hq₂ball, hq₂c⟩ := hderiv_scalar hq₁ball
  have hxe : (‖x‖₊ : ℝ≥0∞) < 1 := by
    exact_mod_cast hx
  have hpc : ∀ n : ℕ, (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      ordinaryHypergeometricCoefficient a b c n := fun n => by
    rw [ordinaryHypergeometricSeries, FormalMultilinearSeries.coeff_ofScalars]
  set F := (₂F₁ a b c : ℂ → ℂ) with hF
  set γ := ordinaryHypergeometricCoefficient a b c with hγ
  have S0 : HasSum (fun n : ℕ => γ n * x ^ n) (F x) := by
    have h := hsum_coeff hB hxe
    exact h.congr_fun fun n => by rw [hpc n]
  have S1 : HasSum (fun n : ℕ =>
      ((n : ℂ) + 1) * γ (n + 1) * x ^ n) (deriv F x) := by
    have h := hsum_coeff hq₁ball hxe
    exact h.congr_fun fun n => by rw [hq₁c n, hpc (n + 1)]
  have S2 : HasSum (fun n : ℕ =>
      ((n : ℂ) + 1) * ((n : ℂ) + 2) * γ (n + 2) * x ^ n)
      (deriv (deriv F) x) := by
    have h := hsum_coeff hq₂ball hxe
    refine h.congr_fun fun n => ?_
    rw [hq₂c n, hq₁c (n + 1), hpc (n + 2)]
    push_cast
    ring
  have hxw2 : HasSum (fun n : ℕ =>
      (n : ℂ) * ((n : ℂ) + 1) * γ (n + 1) * x ^ n)
      (x * deriv (deriv F) x) := by
    have h := S2.mul_left x
    have he : (fun n : ℕ =>
        x * (((n : ℂ) + 1) * ((n : ℂ) + 2) * γ (n + 2) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : ℂ)) * (((n + 1 : ℕ) : ℂ) + 1) *
          γ ((n + 1) + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ =>
      (n : ℂ) * ((n : ℂ) + 1) * γ (n + 1) * x ^ n) 1).mp h
    simpa using h2
  have hx2w2 : HasSum (fun n : ℕ =>
      ((n : ℂ) - 1) * (n : ℂ) * γ n * x ^ n)
      (x * (x * deriv (deriv F) x)) := by
    have h := (S2.mul_left x).mul_left x
    have he : (fun n : ℕ =>
        x * (x * (((n : ℂ) + 1) * ((n : ℂ) + 2) * γ (n + 2) * x ^ n))) =
        fun n : ℕ => (((n + 2 : ℕ) : ℂ) - 1) * ((n + 2 : ℕ) : ℂ) *
          γ (n + 2) * x ^ (n + 2) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ =>
      ((n : ℂ) - 1) * (n : ℂ) * γ n * x ^ n) 2).mp h
    simpa [Finset.sum_range_succ] using h2
  have hxw1 : HasSum (fun n : ℕ =>
      (n : ℂ) * γ n * x ^ n) (x * deriv F x) := by
    have h := S1.mul_left x
    have he : (fun n : ℕ =>
        x * (((n : ℂ) + 1) * γ (n + 1) * x ^ n)) =
        fun n : ℕ => (((n + 1 : ℕ) : ℂ)) * γ (n + 1) * x ^ (n + 1) := by
      funext n
      push_cast
      ring
    rw [he] at h
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ =>
      (n : ℂ) * γ n * x ^ n) 1).mp h
    simpa using h2
  have hT := (((hxw2.sub hx2w2).add (S1.mul_left c)).sub
    (hxw1.mul_left (a + b + 1))).sub (S0.mul_left (a * b))
  have hzero : (fun n : ℕ =>
      ((n : ℂ) * ((n : ℂ) + 1) * γ (n + 1) * x ^ n
        - ((n : ℂ) - 1) * (n : ℂ) * γ n * x ^ n)
      + c * (((n : ℂ) + 1) * γ (n + 1) * x ^ n)
      - (a + b + 1) * ((n : ℂ) * γ n * x ^ n)
      - a * b * (γ n * x ^ n)) = fun _ => (0 : ℂ) := by
    funext n
    have hrec := ordinaryHypergeometricCoefficient_succ_mul a b c n hc
    rw [hγ]
    linear_combination x ^ n * hrec
  rw [hzero] at hT
  have hT0 := hT.unique hasSum_zero
  linear_combination hT0

end HcOnly

end FLMF.Hypergeometric
