import Mathlib
import FLMF.Functions.Error.Erf

/-!
# DLMF §7.20 "Mathematical Applications" — statement surfaces

This module surfaces the normal-distribution / complementary-error-function
identity from DLMF §7.20.

* 7.20.1 — the distribution function of the normal distribution expressed
  through `erfc`, and through the standard-normal tail `Q` (`gaussQ`) and
  distribution function `P` (`gaussP`); all three links of the display's
  four-member chain are carried by the single theorem `erf_7_20_1`.

The `erf`/`erfc` groundwork lives in `FLMF.Functions.Error.Erf`; the key
analytic input is the tail Gaussian integral `integral_Ioi_gaussian_scaled_erfc`
recorded there.
-/

namespace FLMF.Error

open Real MeasureTheory Set

-- no-dlmf: the standard-normal tail function `Q` of DLMF §7.20(iii) (notation
-- introduced by the display 7.20.1, not itself a numbered DLMF definition);
-- support definition for the chain members of `erf_7_20_1`.
/-- The standard-normal **tail** function
`Q(x) = (2π)^{-1/2} ∫_x^∞ e^{-t²/2} dt`, i.e. the upper-tail probability of the
standard normal distribution.  This is the `Q` of §7.20(iii), the third member
of the display carried by `erf_7_20_1`. -/
noncomputable def gaussQ (x : ℝ) : ℝ :=
    (∫ t in Set.Ioi x, Real.exp (-t ^ 2 / 2)) / Real.sqrt (2 * Real.pi)

-- no-dlmf: the standard-normal distribution function `P` of DLMF §7.20(iii)
-- (notation introduced by the display 7.20.1, not itself a numbered DLMF
-- definition); support definition for the chain members of `erf_7_20_1`.
/-- The standard-normal **cumulative distribution function**
`P(x) = (2π)^{-1/2} ∫_{-∞}^x e^{-t²/2} dt`.  This is the `P` of §7.20(iii), the
fourth member of the display carried by `erf_7_20_1`. -/
noncomputable def gaussP (x : ℝ) : ℝ :=
    (∫ t in Set.Iio x, Real.exp (-t ^ 2 / 2)) / Real.sqrt (2 * Real.pi)

-- no-dlmf: support lemma for 7.20.1 (link `½ erfc(y/√2) = Q(y)`), no DLMF number
/-- The standard-normal tail in terms of `erfc`: `Q(y) = ½ erfc(y/√2)`.

The substitution `t = s√2` is packaged by the scaled tail-Gaussian identity
`integral_Ioi_gaussian_scaled_erfc` with `a = 1/2`. -/
theorem gaussQ_eq_erfc (y : ℝ) : gaussQ y = erfc (y / Real.sqrt 2) / 2 := by
  have ha : (0:ℝ) < 1 / 2 := by norm_num
  have hint : (∫ t in Set.Ioi y, Real.exp (-t ^ 2 / 2))
      = ∫ t in Set.Ioi y, Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    congr 1; ring
  have hs : Real.sqrt ((1:ℝ) / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div' 1 (by norm_num)]
    simp [Real.sqrt_one]
  have hp : Real.sqrt (Real.pi / (1 / 2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    norm_num [mul_comm]
  unfold gaussQ
  rw [hint, integral_Ioi_gaussian_scaled_erfc ha y, hs, hp]
  have hden : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [show 1 / Real.sqrt 2 * y = y / Real.sqrt 2 by ring]
  field_simp

-- no-dlmf: support lemma for 7.20.1 (link `Q(-y) = P(y)`), no DLMF number
/-- Reflection symmetry of the standard normal density: `P(y) = Q(-y)`.

Proved by the measure-preserving reflection `t ↦ -t`, which sends `Iio y` onto
`Ioi (-y)` and fixes the even integrand `e^{-t²/2}`. -/
theorem gaussP_eq_gaussQ_neg (y : ℝ) : gaussP y = gaussQ (-y) := by
  have hrefl : (∫ s in Set.Ioi (-y), Real.exp (-s ^ 2 / 2))
      = ∫ t in Set.Iio y, Real.exp (-t ^ 2 / 2) := by
    have A : MeasurableEmbedding (fun t : ℝ => (0:ℝ) - t) := measurableEmbedding_subLeft 0
    have key := A.setIntegral_map (μ := (volume : Measure ℝ))
        (fun s => Real.exp (-s ^ 2 / 2)) (Set.Ioi (-y))
    rw [((volume : Measure ℝ).measurePreserving_sub_left 0).map_eq] at key
    rw [key]
    have hpre : (fun t : ℝ => (0:ℝ) - t) ⁻¹' Set.Ioi (-y) = Set.Iio y := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
      constructor <;> intro h <;> linarith
    rw [hpre]
    refine setIntegral_congr_fun measurableSet_Iio (fun t _ => ?_)
    congr 1; ring
  unfold gaussP gaussQ
  rw [hrefl]

/-- **DLMF 7.20.1.**  For the normal (Gaussian) distribution with mean `m` and
standard deviation `σ > 0`, the distribution function is given by the four-member
chain
`(1/(σ√(2π))) ∫_{-∞}^x e^{-(t-m)²/(2σ²)} dt = ½ erfc((m-x)/(σ√2))
   = Q((m-x)/σ) = P((x-m)/σ)`,
all three equalities of which are asserted here:

* the normal distribution function equals `½ erfc((m-x)/(σ√2))`;
* that complementary error function equals the standard-normal tail
  `Q((m-x)/σ)` (`gaussQ`, `Q(y) = (2π)^{-1/2}∫_y^∞ e^{-t²/2} dt`);
* which in turn equals the standard-normal distribution function `P((x-m)/σ)`
  (`gaussP`, `P(y) = (2π)^{-1/2}∫_{-∞}^y e^{-t²/2} dt`), by reflection.

Proof route.  First equality: the reflection `s = m - t` sends `Iio x` to
`Ioi (m-x)` and turns the integrand into the centred Gaussian `e^{-s²/(2σ²)}`,
after which the scaled tail-Gaussian identity
`integral_Ioi_gaussian_scaled_erfc` (with `a = 1/(2σ²)`) evaluates it as
`(σ√(2π)/2)·erfc((m-x)/(σ√2))`.  Second equality: `gaussQ_eq_erfc` at
`y = (m-x)/σ`, with `((m-x)/σ)/√2 = (m-x)/(σ√2)`.  Third equality:
`gaussP_eq_gaussQ_neg` at `y = (x-m)/σ`, whose negative is `(m-x)/σ`.

The first equality is numerically pinned (4/4) in
`docs/verification/ch7/apps_pin.py`.

DLMF 7.20.1.
DAG: E-7.20.1.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem erf_7_20_1 (m x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in Set.Iio x, Real.exp (-(t - m) ^ 2 / (2 * σ ^ 2))) /
        (σ * Real.sqrt (2 * Real.pi))
      = erfc ((m - x) / (σ * Real.sqrt 2)) / 2 ∧
    erfc ((m - x) / (σ * Real.sqrt 2)) / 2 = gaussQ ((m - x) / σ) ∧
    gaussQ ((m - x) / σ) = gaussP ((x - m) / σ) := by
  -- Link 2: `½ erfc((m-x)/(σ√2)) = Q((m-x)/σ)`, since `((m-x)/σ)/√2 = (m-x)/(σ√2)`.
  have link2 : erfc ((m - x) / (σ * Real.sqrt 2)) / 2 = gaussQ ((m - x) / σ) := by
    rw [gaussQ_eq_erfc, div_div]
  -- Link 3: `Q((m-x)/σ) = P((x-m)/σ)`, by reflection, since `-((x-m)/σ) = (m-x)/σ`.
  have link3 : gaussQ ((m - x) / σ) = gaussP ((x - m) / σ) := by
    rw [gaussP_eq_gaussQ_neg, neg_div', neg_sub]
  refine ⟨?_, link2, link3⟩
  set a : ℝ := (2 * σ ^ 2)⁻¹ with ha
  have ha0 : 0 < a := by
    rw [ha]; exact inv_pos.mpr (mul_pos (by norm_num) (pow_pos hσ 2))
  -- Reflection `s = m - t`: `Iio x → Ioi (m - x)`, integrand `→ e^{-a s²}`.
  have hrefl : (∫ t in Set.Iio x, Real.exp (-(t - m) ^ 2 / (2 * σ ^ 2)))
      = ∫ s in Set.Ioi (m - x), Real.exp (-a * s ^ 2) := by
    have A : MeasurableEmbedding (fun t : ℝ => m - t) := measurableEmbedding_subLeft m
    have key := A.setIntegral_map (μ := (volume : Measure ℝ))
        (fun s => Real.exp (-a * s ^ 2)) (Set.Ioi (m - x))
    rw [((volume : Measure ℝ).measurePreserving_sub_left m).map_eq] at key
    rw [key]
    have hpre : (fun t : ℝ => m - t) ⁻¹' Set.Ioi (m - x) = Set.Iio x := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
      constructor <;> intro h <;> linarith
    rw [hpre]
    refine setIntegral_congr_fun measurableSet_Iio (fun t _ => ?_)
    rw [ha]; congr 1; ring
  -- `√a = 1/(σ√2)` and `√(π/a) = σ√(2π)`.
  have hsa : Real.sqrt a = 1 / (σ * Real.sqrt 2) := by
    have hval : a = (1 / (σ * Real.sqrt 2)) ^ 2 := by
      rw [ha]; rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    rw [hval, Real.sqrt_sq (div_nonneg zero_le_one (mul_nonneg hσ.le (Real.sqrt_nonneg 2)))]
  have hpia : Real.sqrt (Real.pi / a) = σ * Real.sqrt (2 * Real.pi) := by
    have hval2 : Real.pi / a = (σ * Real.sqrt (2 * Real.pi)) ^ 2 := by
      rw [ha]; rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
      field_simp
    rw [hval2, Real.sqrt_sq (mul_nonneg hσ.le (Real.sqrt_nonneg _))]
  have hden : σ * Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (mul_pos hσ (Real.sqrt_pos.mpr (by positivity)))
  rw [hrefl, integral_Ioi_gaussian_scaled_erfc ha0 (m - x), hsa, hpia]
  have harg : 1 / (σ * Real.sqrt 2) * (m - x) = (m - x) / (σ * Real.sqrt 2) := by
    ring
  rw [harg]
  field_simp

end FLMF.Error
