import FLMF.Support.HypergeometricKummerODE
import FLMF.Support.HypergeometricKummerTransform
import FLMF.Chapter7.Erf
import FLMF.Chapter7.ComplexErf
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The error function as a `₁F₁` instance (bridge — DLMF 7.6.1, 7.11.4)

* `cerf_eq_tsum` — **DLMF 7.6.1** at its stated strength: the Maclaurin series
  `erf z = (2/√π) ∑ (−1)ⁿ z^(2n+1) / (n!(2n+1))`, for all complex `z`.
  `erf_eq_tsum` is the real specialization (real `x`), kept as proven
  infrastructure; `integral_gaussian_eq_tsum` is the raw real gaussian-primitive
  computation underneath it.
* `erf_7_11_4` — **DLMF 7.11.4** at its stated strength: the two-member chain
  `erf z = (2z/√π) M(1/2, 3/2, −z²) = (2z/√π) e^{−z²} M(1, 3/2, z²)`, for all
  complex `z`. `cerf_eq_kummerM` / `cerf_eq_kummerM_transform` are its links and
  `erf_eq_kummerM` is the real specialization, kept as proven infrastructure.
  (This identity is DLMF 7.11.4, NOT 7.6.2: 7.6.2 is the *series*
  `erf z = (2/√π) e^{−z²} ∑ 2ⁿ z^{2n+1}/(1·3⋯(2n+1))`, which FLMF does not
  currently state.)

The gaussian `e^{−t²}` is expanded into its exponential series inside the
defining integral; the termwise pieces are polynomials `t^{2n}`, so the
sum–integral interchange (norm-integrals dominated by `(d−c)·(R²)ⁿ/n!` on
`Ioc c d`) and the termwise integration work on both orientations of the
interval. The Kummer series is matched through the coefficient collapse
`cₙ(1/2, 3/2) = 1/((2n+1)·n!)`. The complex surfaces run the same expansion
along `cerf`'s defining ray integral `∫₀¹ z·e^{−(tz)²} dt` (real `t ∈ [0,1]`,
complex constant `z`).
-/

noncomputable section

open Nat MeasureTheory Real Set FLMF.Hypergeometric

namespace FLMF.Error

-- no-dlmf: termwise gaussian-series integrands; proof infrastructure, no DLMF identity
/-- The termwise gaussian-series integrands. -/
private def gaussTerm (n : ℕ) (t : ℝ) : ℝ := (-1) ^ n / n ! * t ^ (2 * n)

-- no-dlmf: summability bound powering the sum–integral interchange; proof infrastructure, no DLMF identity
private theorem gaussTerm_summable_integral {c d : ℝ} (hcd : c ≤ d) :
    Summable fun n : ℕ => ∫ t in Ioc c d, ‖gaussTerm n t‖ := by
  set R : ℝ := max |c| |d| with hR
  have hbound : ∀ n : ℕ, ∫ t in Ioc c d, ‖gaussTerm n t‖
      ≤ (d - c) * ((R ^ 2) ^ n / n !) := by
    intro n
    have hle : ∀ t ∈ Ioc c d, ‖gaussTerm n t‖ ≤ (R ^ 2) ^ n / n ! := by
      intro t ht
      have htR : |t| ≤ R := by
        rw [abs_le]
        constructor
        · calc -R ≤ -|c| := by simp [hR]
            _ ≤ c := neg_abs_le c
            _ ≤ t := ht.1.le
        · calc t ≤ d := ht.2
            _ ≤ |d| := le_abs_self d
            _ ≤ R := le_max_right _ _
      have habs : ‖gaussTerm n t‖ = |t| ^ (2 * n) / n ! := by
        simp only [gaussTerm]
        rw [norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
          Nat.abs_cast, abs_pow]
        ring
      rw [habs, ← pow_mul]
      gcongr
    calc ∫ t in Ioc c d, ‖gaussTerm n t‖
        ≤ ∫ _ in Ioc c d, (R ^ 2) ^ n / n ! := by
          refine setIntegral_mono_on ?_ (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc hle
          exact ((continuous_const.mul (continuous_pow _)).integrableOn_Ioc).norm
      _ = (d - c) * ((R ^ 2) ^ n / n !) := by
          rw [setIntegral_const, smul_eq_mul, volume_real_Ioc_of_le hcd]
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun t => norm_nonneg _) hbound
    ((Real.summable_pow_div_factorial (R ^ 2)).mul_left _)

-- no-dlmf: real specialization of DLMF 7.6.1 (the raw gaussian primitive, not
-- `erf` itself); faithful complex-`z` surface is `cerf_eq_tsum`
/-- The gaussian primitive as a power series (the core of DLMF 7.6.1), for all
real `x`: `∫₀ˣ e^{−t²} dt = ∑ (−1)ⁿ x^(2n+1)/(n!(2n+1))`. -/
theorem integral_gaussian_eq_tsum (x : ℝ) :
    ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)
      = ∑' n : ℕ, (-1) ^ n / n ! * (x ^ (2 * n + 1) / (2 * n + 1)) := by
  -- pointwise, the gaussian is the sum of its series
  have hpt : ∀ t : ℝ, Real.exp (-t ^ 2) = ∑' n : ℕ, gaussTerm n t := by
    intro t
    rw [show -t ^ 2 = -(t ^ 2) by ring, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    refine tsum_congr fun n => ?_
    rw [gaussTerm, neg_pow, pow_mul]
    ring
  -- interchange on `Ioc c d`
  have hswap : ∀ {c d : ℝ}, c ≤ d →
      ∫ t in Ioc c d, Real.exp (-t ^ 2) = ∑' n : ℕ, ∫ t in Ioc c d, gaussTerm n t := by
    intro c d hcd
    have hFint : ∀ n : ℕ, IntegrableOn (gaussTerm n) (Ioc c d) :=
      fun n => (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
    rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => hpt t]
    exact (integral_tsum_of_summable_integral_norm hFint
      (gaussTerm_summable_integral hcd)).symm
  -- the termwise interval integral
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..x, gaussTerm n t
      = (-1) ^ n / n ! * (x ^ (2 * n + 1) / (2 * n + 1)) := by
    intro n
    simp only [gaussTerm]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  -- assemble, by orientation of the interval
  rcases le_total 0 x with hx | hx
  · rw [intervalIntegral.integral_of_le hx, hswap hx]
    refine tsum_congr fun n => ?_
    rw [← hterm n, intervalIntegral.integral_of_le hx]
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx, hswap hx,
      ← tsum_neg]
    refine tsum_congr fun n => ?_
    rw [← hterm n, intervalIntegral.integral_symm x 0, intervalIntegral.integral_of_le hx]

-- no-dlmf: real specialization of DLMF 7.6.1; faithful complex-`z` surface is
-- `cerf_eq_tsum`
/-- **The Maclaurin series of the error function**, real specialization of
DLMF 7.6.1: `erf x = (2/√π) ∑ (−1)ⁿ x^(2n+1)/(n!(2n+1))`, for all real `x`. -/
theorem erf_eq_tsum (x : ℝ) :
    erf x = 2 / Real.sqrt Real.pi
      * ∑' n : ℕ, (-1) ^ n / n ! * (x ^ (2 * n + 1) / (2 * n + 1)) := by
  rw [erf, integral_gaussian_eq_tsum]

-- no-dlmf: infrastructure for `cerf_eq_tsum`; the pointwise exponential-series
-- expansion of the gaussian integrand along the ray to `z`, no DLMF identity
private theorem cerf_exp_hasSum (z : ℂ) (t : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n))
      (Complex.exp (-((t : ℂ) * z) ^ 2)) := by
  have h : HasSum (fun n : ℕ => (-((t : ℂ) * z) ^ 2) ^ n / n !)
      (Complex.exp (-((t : ℂ) * z) ^ 2)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (-((t : ℂ) * z) ^ 2)
  refine h.congr_fun fun n => ?_
  rw [neg_pow, mul_pow]
  ring

/-- **DLMF 7.6.1** (full strength, complex `z`) — the Maclaurin series of the
complex error function: `erf z = (2/√π) ∑ (−1)ⁿ z^(2n+1)/(n!(2n+1))`, for all
complex `z`.

DLMF 7.6.1.
Numerical: PASS
Verified: verified
DAG: E-7.6.1.
-/
theorem cerf_eq_tsum (z : ℂ) :
    cerf z = 2 / (Real.sqrt Real.pi : ℂ)
      * ∑' n : ℕ, (-1) ^ n / n ! * (z ^ (2 * n + 1) / (2 * n + 1)) := by
  have hpt : ∀ t : ℝ, Complex.exp (-((t : ℂ) * z) ^ 2)
      = ∑' n : ℕ, (-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n) :=
    fun t => (cerf_exp_hasSum z t).tsum_eq.symm
  have hbound : ∀ n : ℕ,
      ∫ t in Set.Ioc (0 : ℝ) 1, ‖(-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)‖
        ≤ ‖z‖ ^ (2 * n) / n ! := by
    intro n
    have hle : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        ‖(-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)‖ ≤ ‖z‖ ^ (2 * n) / n ! := by
      intro t ht
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have habs : ‖(-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)‖
          = ‖z‖ ^ (2 * n) / n ! * |t| ^ (2 * n) := by
        rw [norm_mul, norm_mul, norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
          Complex.norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        ring
      rw [habs]
      have hp : |t| ^ (2 * n) ≤ 1 := by
        calc |t| ^ (2 * n) ≤ (1 : ℝ) ^ (2 * n) := by gcongr
          _ = 1 := one_pow _
      calc ‖z‖ ^ (2 * n) / n ! * |t| ^ (2 * n) ≤ ‖z‖ ^ (2 * n) / n ! * 1 := by
            gcongr
        _ = ‖z‖ ^ (2 * n) / n ! := by ring
    calc ∫ t in Set.Ioc (0 : ℝ) 1, ‖(-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)‖
        ≤ ∫ _ in Set.Ioc (0 : ℝ) 1, ‖z‖ ^ (2 * n) / n ! := by
          refine setIntegral_mono_on ?_ (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc hle
          exact ((continuous_const.mul (Complex.continuous_ofReal.pow _))).integrableOn_Ioc.norm
      _ = ‖z‖ ^ (2 * n) / n ! := by
          rw [setIntegral_const, smul_eq_mul, volume_real_Ioc_of_le zero_le_one, sub_zero,
            one_mul]
  have hsum : Summable fun n : ℕ =>
      ∫ t in Set.Ioc (0 : ℝ) 1, ‖(-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)‖ := by
    have hb : Summable fun n : ℕ => ‖z‖ ^ (2 * n) / n ! := by
      simpa [pow_mul] using Real.summable_pow_div_factorial (‖z‖ ^ 2)
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hbound hb
  have hFint : ∀ n : ℕ,
      IntegrableOn (fun t : ℝ => (-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n))
        (Set.Ioc (0 : ℝ) 1) :=
    fun n => (continuous_const.mul (Complex.continuous_ofReal.pow _)).integrableOn_Ioc
  have hswap : ∫ t in Set.Ioc (0 : ℝ) 1, Complex.exp (-((t : ℂ) * z) ^ 2)
      = ∑' n : ℕ, ∫ t in Set.Ioc (0 : ℝ) 1,
          (-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n) := by
    rw [setIntegral_congr_fun measurableSet_Ioc fun t _ => hpt t]
    exact (integral_tsum_of_summable_integral_norm hFint hsum).symm
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..1,
      (-1 : ℂ) ^ n / n ! * z ^ (2 * n) * (t : ℂ) ^ (2 * n)
        = (-1) ^ n / n ! * (z ^ (2 * n) / (2 * n + 1)) := by
    intro n
    rw [intervalIntegral.integral_const_mul]
    have hcongr : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (2 * n))
        = ∫ t in (0 : ℝ)..1, ((t ^ (2 * n) : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      push_cast; ring
    rw [hcongr, intervalIntegral.integral_ofReal, integral_pow]
    push_cast
    ring
  have hkey : (∫ t in (0 : ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2))
      = ∑' n : ℕ, (-1) ^ n / n ! * (z ^ (2 * n) / (2 * n + 1)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, hswap]
    refine tsum_congr fun n => ?_
    rw [← hterm n, intervalIntegral.integral_of_le zero_le_one]
  unfold cerf
  rw [hkey, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [pow_succ' z (2 * n)]
  ring

-- no-dlmf: real specialization of DLMF 7.11.4 (first member); faithful complex-`z`
-- surface is `erf_7_11_4`
/-- **The error function as a `₁F₁` instance**, real specialization of DLMF
7.11.4: `erf x = (2x/√π) · M(1/2; 3/2; −x²)`, for all real `x`. -/
theorem erf_eq_kummerM (x : ℝ) :
    erf x = 2 / Real.sqrt Real.pi * x * ₁F₁ ((1 : ℝ) / 2) (3 / 2) (-x ^ 2) := by
  have hM := (kummerM_hasSum ((1 : ℝ) / 2) (3 / 2) (-x ^ 2)).mul_left x
  have hterm : (fun n : ℕ => x * (kummerCoefficient ((1 : ℝ) / 2) (3 / 2) n * (-x ^ 2) ^ n)) =
      fun n : ℕ => (-1) ^ n / n ! * (x ^ (2 * n + 1) / (2 * n + 1)) := by
    funext n
    rw [kummerCoefficient_one_half n, neg_pow, ← pow_mul]
    have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hfn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    field_simp
    ring
  rw [hterm] at hM
  rw [erf_eq_tsum, hM.tsum_eq]
  ring

-- no-dlmf: chain link 7.11.4 (assembled in `erf_7_11_4` below) — the first member
-- `erf z = (2z/√π) M(1/2, 3/2, −z²)`. Previously mistagged 7.6.2, which is the
-- *series* representation `erf z = (2/√π) e^{−z²} ∑ 2ⁿ z^{2n+1}/(1·3⋯(2n+1))`,
-- a different display (Semantic adjudication 2026-08-11).
/-- The error function as a `₁F₁` instance (first member of DLMF 7.11.4):
`erf z = (2z/√π) · M(1/2; 3/2; −z²)`, for all complex `z`. -/
theorem cerf_eq_kummerM (z : ℂ) :
    cerf z = 2 / (Real.sqrt Real.pi : ℂ) * z * ₁F₁ ((1 : ℂ) / 2) (3 / 2) (-z ^ 2) := by
  have hM := (kummerM_hasSum ((1 : ℂ) / 2) (3 / 2) (-z ^ 2)).mul_left z
  have hterm : (fun n : ℕ => z * (kummerCoefficient ((1 : ℂ) / 2) (3 / 2) n * (-z ^ 2) ^ n)) =
      fun n : ℕ => (-1) ^ n / n ! * (z ^ (2 * n + 1) / (2 * n + 1)) := by
    funext n
    rw [kummerCoefficient_one_half n, neg_pow, ← pow_mul]
    have h2n : (2 * (n : ℂ) + 1) ≠ 0 := by
      have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    field_simp
    ring
  rw [hterm] at hM
  rw [cerf_eq_tsum, hM.tsum_eq]
  ring

-- no-dlmf: chain link 7.11.4 (assembled in `erf_7_11_4` below) — the second member,
-- obtained from `cerf_eq_kummerM` by Kummer's transformation `M(a,b,w) = eʷ·M(b−a,b,−w)`
-- (`kummerM_kummer_transform`, DLMF 13.2.39) at `a = 1/2`, `b = 3/2`, `w = −z²`
private theorem cerf_eq_kummerM_transform (z : ℂ) :
    cerf z = 2 / (Real.sqrt Real.pi : ℂ) * z * Complex.exp (-z ^ 2) *
      ₁F₁ (1 : ℂ) (3 / 2) (z ^ 2) := by
  have hb : ∀ k : ℕ, (k : ℂ) ≠ -(3 / 2 : ℂ) := by
    intro k h
    have h2 : (k : ℂ) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) := by rw [h]; norm_num
    have h3 : (k : ℝ) = -(3 / 2 : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have ht := FLMF.Hypergeometric.kummerM_kummer_transform (𝕂 := ℂ) (a := (1 / 2 : ℂ))
    (b := (3 / 2 : ℂ)) hb (-z ^ 2)
  rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by ring, ← Complex.exp_eq_exp_ℂ, neg_neg] at ht
  rw [cerf_eq_kummerM z, ht]
  ring

/-- **DLMF 7.11.4**, at DLMF's full complex-variable strength — the error function as
a Kummer confluent hypergeometric value in two equivalent forms,
`erf z = (2z/√π) M(1/2, 3/2, −z²) = (2z/√π) e^{−z²} M(1, 3/2, z²)`, for every `z ∈ ℂ`.

DLMF 7.11.4.
DAG: E-7.11.4.
Numerical: PASS
Verified: verified
-/
theorem erf_7_11_4 (z : ℂ) :
    cerf z = 2 / (Real.sqrt Real.pi : ℂ) * z * ₁F₁ ((1 : ℂ) / 2) (3 / 2) (-z ^ 2) ∧
      cerf z = 2 / (Real.sqrt Real.pi : ℂ) * z * Complex.exp (-z ^ 2) *
        ₁F₁ (1 : ℂ) (3 / 2) (z ^ 2) :=
  ⟨cerf_eq_kummerM z, cerf_eq_kummerM_transform z⟩

end FLMF.Error
