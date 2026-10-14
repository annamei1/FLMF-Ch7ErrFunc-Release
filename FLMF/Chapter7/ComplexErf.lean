import FLMF.Chapter7.Erf
import FLMF.Support.HermiteNormalization
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Complex error function `cerf` and `cerfc` (DLMF §7.2)

We define the complex error function
`erf(z) = (2/√π) ∫_0^z e^{-u²} du = (2/√π) z ∫_0^1 e^{-(t z)²} dt`
and the complex complementary error function `erfc(z) = 1 - erf(z)`, as the
holomorphic extensions of the real `FLMF.Error.erf`/`FLMF.Error.erfc`.

Main results:

* `FLMF.Error.cerf_ofReal` : `cerf ↑x = ↑(erf x)` (agreement with the real `erf`).
* `FLMF.Error.cerfc_ofReal` : `cerfc ↑x = ↑(erfc x)`.
* `FLMF.Error.cerf_neg` : `cerf (-z) = - cerf z` (odd parity, DLMF 7.4.1).
* `FLMF.Error.cerf_zero` : `cerf 0 = 0`.
* `FLMF.Error.hasDerivAt_cerf` : `cerf' z = (2/√π) e^{-z²}` (the `n = 0` instance of
  DLMF 7.10.1; the faithful general surface is `FLMF.Error.cerf_7_10_1`).
* `FLMF.Error.cerf_7_10_1` : `cerf^{(n+1)} z = (-1)ⁿ (2/√π) Hₙ(z) e^{-z²}` (DLMF 7.10.1,
  surfaced).
* `FLMF.Error.differentiable_cerf` : `cerf` is entire (surfaced).
-/

namespace FLMF.Error

open Complex intervalIntegral in
/-- Complex error function `erf z = (2/√π) ∫₀¹ z·e^{-(t z)²} dt = (2/√π)∫₀ᶻ e^{-u²} du`
(complex extension of `FLMF.Error.erf`; DLMF 7.2.1).

DLMF 7.2.1.
-/
-- DAG: E-7.2.1.
-- Verified: verified
noncomputable def cerf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * z * ∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2)

/-- Complex complementary error function `erfc z = 1 - erf z` (DLMF 7.2.2).

DLMF 7.2.2.
-/
-- DAG: E-7.2.2.
-- Verified: verified
noncomputable def cerfc (z : ℂ) : ℂ := 1 - cerf z

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- The complex Gaussian integrand over the real segment to `x` is the cast of the
real integrand: `exp(-(↑t·↑x)²) = ↑(exp(-(t·x)²))`. -/
theorem cerf_integrand_ofReal (x t : ℝ) :
    Complex.exp (-((t : ℂ) * (x : ℂ)) ^ 2) = ((Real.exp (-(t * x) ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- **Agreement with the real `erf`.** `cerf ↑x = ↑(erf x)` for real `x`. -/
theorem cerf_ofReal (x : ℝ) : cerf (x : ℂ) = ((FLMF.Error.erf x : ℝ) : ℂ) := by
  unfold cerf
  -- Replace the complex integrand by the cast of the real integrand, then pull the cast out.
  have hint : (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * (x : ℂ)) ^ 2))
      = ((∫ t in (0:ℝ)..1, Real.exp (-(t * x) ^ 2) : ℝ) : ℂ) := by
    rw [show (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * (x : ℂ)) ^ 2))
          = ∫ t in (0:ℝ)..1, ((Real.exp (-(t * x) ^ 2) : ℝ) : ℂ) from
        intervalIntegral.integral_congr (fun t _ => cerf_integrand_ofReal x t)]
    exact intervalIntegral.integral_ofReal
  rw [hint]
  -- Now reduce to the real change of variables `s = t·x`.
  unfold FLMF.Error.erf
  -- `x * ∫ t in 0..1, exp(-(t·x)²) = ∫ s in 0..x, exp(-s²)`.
  have hcov : x * (∫ t in (0:ℝ)..1, Real.exp (-(t * x) ^ 2))
      = ∫ s in (0:ℝ)..x, Real.exp (-s ^ 2) := by
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := (0:ℝ)) (b := (1:ℝ))
      (f := fun t : ℝ => t * x) (f' := fun _ : ℝ => x)
      (g := fun s : ℝ => Real.exp (-s ^ 2))
      (fun t _ => by simpa using (hasDerivAt_id t).mul_const x)
      (by fun_prop)
      (FLMF.Error.continuous_gaussian)
    simp only [Function.comp] at h
    rw [show (0:ℝ) * x = 0 by ring, show (1:ℝ) * x = x by ring] at h
    -- `h : ∫ t in 0..1, exp(-(t·x)²) * x = ∫ s in 0..x, exp(-s²)`
    rw [← h, intervalIntegral.integral_mul_const]
    ring
  -- Assemble: `(2/√π) * ↑x * ↑(∫ ...) = ↑((2/√π) * ∫ s in 0..x, exp(-s²))`.
  have hgoal : (2 / Real.sqrt Real.pi : ℂ) * (x : ℂ)
        * ((∫ t in (0:ℝ)..1, Real.exp (-(t * x) ^ 2) : ℝ) : ℂ)
      = ((2 / Real.sqrt Real.pi : ℝ) : ℂ)
        * ((x * (∫ t in (0:ℝ)..1, Real.exp (-(t * x) ^ 2)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hgoal, hcov, ← Complex.ofReal_mul]

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- **Agreement with the real `erfc`.** `cerfc ↑x = ↑(erfc x)` for real `x`. -/
theorem cerfc_ofReal (x : ℝ) : cerfc (x : ℂ) = ((FLMF.Error.erfc x : ℝ) : ℂ) := by
  unfold cerfc FLMF.Error.erfc
  rw [cerf_ofReal]
  push_cast
  ring

/-- **DLMF 7.4.1.** `cerf` is odd: `cerf (-z) = - cerf z`.

DLMF 7.4.1.
Numerical: PASS
Verified: verified
DAG: E-7.4.1.
-/
theorem cerf_neg (z : ℂ) : cerf (-z) = - cerf z := by
  unfold cerf
  have : (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * (-z)) ^ 2))
      = ∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    congr 1
    ring
  rw [this]
  ring

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- `cerf 0 = 0`. -/
@[simp]
theorem cerf_zero : cerf 0 = 0 := by
  unfold cerf
  simp

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- `cerfc 0 = 1`. -/
@[simp]
theorem cerfc_zero : cerfc 0 = 1 := by
  unfold cerfc
  simp

-- no-dlmf: instance of DLMF 7.10.1 (n = 0, first derivative); faithful surface is cerf_7_10_1
/-- The derivative of the complex error function: `cerf' z = (2/√π) e^{-z²}`. -/
theorem hasDerivAt_cerf (z : ℂ) :
    HasDerivAt cerf ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2)) z := by
  -- Pointwise ℂ-derivative of the integrand in the parameter `w`.
  have hFderiv : ∀ (t : ℝ) (x : ℂ),
      HasDerivAt (fun w : ℂ => Complex.exp (-((t : ℂ) * w) ^ 2))
        ((-2 * (t : ℂ) ^ 2 * x) * Complex.exp (-((t : ℂ) * x) ^ 2)) x := by
    intro t x
    have hinner : HasDerivAt (fun w : ℂ => -((t : ℂ) * w) ^ 2) (-2 * (t : ℂ) ^ 2 * x) x := by
      have h := (((hasDerivAt_id x).const_mul (t : ℂ)).pow 2).neg
      convert h using 1
      simp only [id_eq]
      ring
    have h := hinner.cexp
    convert h using 1
    ring
  have hcont : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (-((t : ℂ) * w) ^ 2) := by
    intro w; fun_prop
  have hcont' : Continuous fun t : ℝ =>
      (-2 * (t : ℂ) ^ 2 * z) * Complex.exp (-((t : ℂ) * z) ^ 2) := by
    fun_prop
  -- Uniform bound for the `w`-derivative over the unit ball around `z`.
  have hbound : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Metric.ball z 1,
        ‖(-2 * (t : ℂ) ^ 2 * x) * Complex.exp (-((t : ℂ) * x) ^ 2)‖
          ≤ 2 * (‖z‖ + 1) * Real.exp ((‖z‖ + 1) ^ 2) := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hxz : ‖x‖ < ‖z‖ + 1 := by
      have h := mem_ball_iff_norm.mp hx
      calc ‖x‖ = ‖z + (x - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
        _ < ‖z‖ + 1 := by linarith
    have ht0 : (0:ℝ) < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    rw [norm_mul]
    have h1 : ‖-2 * (t : ℂ) ^ 2 * x‖ = 2 * t ^ 2 * ‖x‖ := by
      simp [abs_of_pos ht0]
    have h2 : ‖Complex.exp (-((t : ℂ) * x) ^ 2)‖ ≤ Real.exp ((‖z‖ + 1) ^ 2) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (-((t : ℂ) * x) ^ 2).re ≤ ‖((t : ℂ) * x) ^ 2‖ := by
        rw [Complex.neg_re]
        exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      refine hre.trans ?_
      rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
      have hm : |t| * ‖x‖ ≤ ‖z‖ + 1 := by
        have h := mul_le_mul htabs hxz.le (norm_nonneg x) zero_le_one
        simpa using h
      nlinarith [hm, mul_nonneg (abs_nonneg t) (norm_nonneg x)]
    rw [h1]
    calc 2 * t ^ 2 * ‖x‖ * ‖Complex.exp (-((t : ℂ) * x) ^ 2)‖
        ≤ 2 * 1 * (‖z‖ + 1) * Real.exp ((‖z‖ + 1) ^ 2) := by
          gcongr
          nlinarith [h2, hxz, ht0, ht1]
      _ = 2 * (‖z‖ + 1) * Real.exp ((‖z‖ + 1) ^ 2) := by ring
  -- Differentiate under the integral sign.
  have hG := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (t : ℝ) => Complex.exp (-((t : ℂ) * w) ^ 2))
    (F' := fun (w : ℂ) (t : ℝ) => (-2 * (t : ℂ) ^ 2 * w) * Complex.exp (-((t : ℂ) * w) ^ 2))
    (bound := fun _ => 2 * (‖z‖ + 1) * Real.exp ((‖z‖ + 1) ^ 2))
    (Metric.ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall fun w => (hcont w).aestronglyMeasurable)
    ((hcont z).intervalIntegrable 0 1)
    hcont'.aestronglyMeasurable
    hbound
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => hFderiv t x)).2
  -- FTC in `t`: `∫₀¹ e^{-(tz)²} dt + z·∫₀¹ (-2t²z)e^{-(tz)²} dt = e^{-z²}`,
  -- from `d/dt [t·e^{-(tz)²}] = e^{-(tz)²} + t·(-2tz²)·e^{-(tz)²}`.
  have hkey : (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2))
      + z * ∫ t in (0:ℝ)..1, (-2 * (t : ℂ) ^ 2 * z) * Complex.exp (-((t : ℂ) * z) ^ 2)
      = Complex.exp (-z ^ 2) := by
    have hH : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp (-((s : ℂ) * z) ^ 2))
        (Complex.exp (-((t : ℂ) * z) ^ 2)
          + (t : ℂ) * ((-2 * (t : ℂ) * z ^ 2) * Complex.exp (-((t : ℂ) * z) ^ 2))) t := by
      intro t
      have hinner : HasDerivAt (fun w : ℂ => -(w * z) ^ 2) (-2 * ((t : ℝ) : ℂ) * z ^ 2)
          ((t : ℝ) : ℂ) := by
        have h := (((hasDerivAt_id ((t : ℝ) : ℂ)).mul_const z).pow 2).neg
        convert h using 1
        simp only [id_eq]
        ring
      have hc := (hasDerivAt_id ((t : ℝ) : ℂ)).mul hinner.cexp
      have hc' : HasDerivAt (fun w : ℂ => w * Complex.exp (-(w * z) ^ 2))
          (Complex.exp (-(((t : ℝ) : ℂ) * z) ^ 2)
            + ((t : ℝ) : ℂ) * ((-2 * ((t : ℝ) : ℂ) * z ^ 2)
                * Complex.exp (-(((t : ℝ) : ℂ) * z) ^ 2))) ((t : ℝ) : ℂ) := by
        convert hc using 1
        simp only [id_eq]
        ring
      exact hc'.comp_ofReal
    have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (-((t : ℂ) * z) ^ 2)
        + (t : ℂ) * ((-2 * (t : ℂ) * z ^ 2) * Complex.exp (-((t : ℂ) * z) ^ 2)))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hH t) hint
    have hsplit : (∫ t in (0:ℝ)..1, (Complex.exp (-((t : ℂ) * z) ^ 2)
          + (t : ℂ) * ((-2 * (t : ℂ) * z ^ 2) * Complex.exp (-((t : ℂ) * z) ^ 2))))
        = (∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2))
          + z * ∫ t in (0:ℝ)..1, (-2 * (t : ℂ) ^ 2 * z) * Complex.exp (-((t : ℂ) * z) ^ 2) := by
      rw [intervalIntegral.integral_add ((hcont z).intervalIntegrable 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)]
      congr 1
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [hsplit] at hftc
    rw [hftc]
    norm_num
  -- Assemble via the product rule.
  have hzG := (hasDerivAt_id z).mul hG
  have hfinal := hzG.const_mul ((2 : ℂ) / (Real.sqrt Real.pi : ℂ))
  have hcerf_eq : cerf = fun w : ℂ => ((2 : ℂ) / (Real.sqrt Real.pi : ℂ))
      * (w * ∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * w) ^ 2)) := by
    funext w
    unfold cerf
    ring
  rw [hcerf_eq]
  convert hfinal using 1
  simp only [id_eq, one_mul]
  rw [← hkey]

/-- **DLMF 7.10.1** — the `(n+1)`-th derivative of the complex error function:
`d^{n+1} erf(z) / dz^{n+1} = (-1)ⁿ (2/√π) Hₙ(z) e^{-z²}` for `n = 0, 1, 2, …` and
complex `z`, where `Hₙ` is the physicists' Hermite polynomial
(`FLMF.Functions.Hermite.physicistsHermite`, evaluated at `z` over `ℂ`).

Proved by induction on `n`: the base case is `hasDerivAt_cerf`
(`cerf′ z = (2/√π) e^{-z²}`), and the step is the Hermite–Gaussian differentiation
rule `d/dz (Hₙ(z) e^{-z²}) = -H_{n+1}(z) e^{-z²}`
(`FLMF.Functions.Hermite.hasDerivAt_aeval_physicistsHermite_mul_cexp`), which
supplies exactly the extra factor `-1` per differentiation.
DAG: E-7.10.1.
Numerical: PASS
Verified: verified
-/
theorem cerf_7_10_1 (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 1) cerf z =
      (-1) ^ n * (2 / Real.sqrt Real.pi : ℂ) *
        (Polynomial.aeval z (FLMF.Functions.Hermite.physicistsHermite n)) *
          Complex.exp (-z ^ 2) := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_one, (hasDerivAt_cerf z).deriv]
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv (n + 1) cerf
        = fun w : ℂ => (-1 : ℂ) ^ n * (2 / Real.sqrt Real.pi : ℂ)
            * (Polynomial.aeval w (FLMF.Functions.Hermite.physicistsHermite n))
            * Complex.exp (-w ^ 2) := funext ih
    rw [hfun]
    have hd := (FLMF.Functions.Hermite.hasDerivAt_aeval_physicistsHermite_mul_cexp n z).const_mul
      ((-1 : ℂ) ^ n * (2 / Real.sqrt Real.pi : ℂ))
    have hshape : (fun w : ℂ => (-1 : ℂ) ^ n * (2 / Real.sqrt Real.pi : ℂ)
          * (Polynomial.aeval w (FLMF.Functions.Hermite.physicistsHermite n)
              * Complex.exp (-w ^ 2)))
        = fun w : ℂ => (-1 : ℂ) ^ n * (2 / Real.sqrt Real.pi : ℂ)
            * (Polynomial.aeval w (FLMF.Functions.Hermite.physicistsHermite n))
            * Complex.exp (-w ^ 2) := funext fun w => by ring
    rw [hshape] at hd
    rw [hd.deriv]
    ring

-- no-dlmf: qualitative support lemma (entirety of cerf) — not a numbered DLMF display,
-- so it carries no Fidelity/Verified block (disposition approved by user 2026-07-28).
/-- `cerf` is entire (holomorphic on all of `ℂ`). -/
theorem differentiable_cerf : Differentiable ℂ cerf :=
  fun z => (hasDerivAt_cerf z).differentiableAt

end FLMF.Error
