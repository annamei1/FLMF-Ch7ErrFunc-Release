import FLMF.Chapter7.InverseErf
import FLMF.Chapter7.ErfcSeries

/-!
# The four-term asymptotic expansion of `inverfc` (DLMF 7.17.3)

`FLMF/Chapter7/InverseErf.lean` proves only the **leading term** of DLMF
7.17.3 (`inverfc x · √u → 1`, i.e. `inverfc x - u^{-1/2} = o(u^{-1/2})`).  This file
carries the faithful, four-term display

`inverfc x ∼ u^{-1/2} + a₂ u^{3/2} + a₃ u^{5/2} + a₄ u^{7/2}`  (`x → 0⁺`),

with `u = asymU x` (DLMF 7.17.5) and `a_k = asymA x k` (DLMF 7.17.4), as the Poincaré
truncation `erf_7_17_3_full`.

## The route: log-log asymptotic inversion

Put `y = inverfc x`, so `erfc y = x` and `y → ∞` as `x → 0⁺`.  Everything is driven by
one **exact** identity.  Write

* `M y = √π · y · e^{y²} · erfc y`  (`erfcMills`, the normalized Mills factor; `M → 1`),
* `L y = ln (1 / erfc y)`  (`= ln(1/x)`),
* `A y = ln y + ½ ln π - ln (M y)`  (`inverfcAuxA`), so that `L y = y² + A y` exactly,
* `W y = ln (L y) - 2 ln y = ln (L y / y²)`  (`inverfcAuxW`), so `W y = ln (1 + A y / y²)`,
* `S y = y² - (asymU (erfc y))⁻¹`  (`inverfcAuxS`), the *inversion gap*.

Unfolding `asymU` (7.17.5) and `asymV` (7.17.6) along `x = erfc y` gives

* `(asymU (erfc y))⁻¹ = L y - ½ ln π - ½ ln (L y)`   (`asymU_erfc_inv_eq`), hence
* `S y = ln (M y) + ½ W y`                            (`inverfcAuxS_eq`),
* `asymV (erfc y) = W y + 2 ln y - 2 + ln π`          (`asymV_erfc_eq`).

The second-order `erfc` expansion (`erfc_7_12_1 1`, i.e. `M y = 1 - 1/(2y²) + o(y^{-2})`)
gives `y² ln (M y) → -½`; combined with `y² W y - A y → 0` this yields the **first
bootstrap step**

`y² · S y - asymV (erfc y) / 4 → 0`   (`tendsto_sq_mul_inverfcAuxS_sub`),

which is exactly `S = (v/4) u + o(u)`, the second order of the inversion.  (The `-2` in
DLMF's `v = ln ln(1/x) - 2 + ln π` is precisely the `-1/(2y²)` term of the `erfc`
expansion; that is the sense in which 7.17.6 is the *second* term of the inversion.)

The passage from the gap `S` to the display is the exact algebraic identity
`P - 1 = ½(P² - 1) - ½(P - 1)²` for `P = y √u` (see `normalized_gap_identity`).

## Higher-order inversion

The cubic logarithmic Mills expansion has coefficients `-1/2`, `5/8`, and `-37/24`.
The exact relation `A = 1 + v/2 - S` turns the inversion into the scalar equation
`S = log M + log (1 + y⁻² (1 + v/2 - S))/2`.  A polynomial trial approximation
has equation residual `o(y⁻⁶)`: the quartic logarithmic remainder and every polynomial
in `v` multiplied by `y⁻²` tend to zero at the required scale.  Monotonicity of the
scalar equation bounds its solution error by that residual.  An algebraic change
from `y⁻²` to `u` then gives `inverfc_gap_expansion`; the proved square-root transfer
identities give the faithful four-term display `erf_7_17_3_full`.
-/

namespace FLMF.Error

open Filter Topology Asymptotics Real Set

section LogTaylor

-- no-dlmf: reusable cubic logarithmic remainder for asymptotic inversion
/-- The cubic Taylor remainder of `log (1 + t)` is little-o of `t³`,
including at `t = 0` with Lean's totalized division. -/
theorem tendsto_log_cubic_remainder :
    Tendsto (fun t : ℝ =>
      (Real.log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3) / t ^ 3)
      (𝓝 0) (𝓝 0) := by
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  have hbound : Tendsto (fun t : ℝ => |t| / (1 - |t|)) (𝓝 0) (𝓝 0) := by
    simpa using habs.div (tendsto_const_nhds.sub habs) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [habs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with t ht
  rw [Real.norm_eq_abs]
  by_cases ht0 : t = 0
  · simp [ht0]
  have hR := Real.abs_log_sub_add_sum_range_le (x := -t) (by simpa using ht) 3
  norm_num [Finset.sum_range_succ] at hR
  have heq : (-t + t ^ 2 / 2 + (-t) ^ 3 / 3) + Real.log (1 + t) =
      Real.log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3 := by ring
  rw [heq] at hR
  calc
    |(Real.log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3) / t ^ 3|
        = |Real.log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3| / |t| ^ 3 := by
          rw [abs_div, abs_pow]
    _ ≤ (|t| ^ 4 / (1 - |t|)) / |t| ^ 3 :=
      div_le_div_of_nonneg_right hR (by positivity)
    _ = |t| / (1 - |t|) := by
      field_simp

-- no-dlmf: quartic Taylor control for coefficients growing logarithmically
/-- The cubic logarithmic remainder at argument `c/y²` is little-o of `y⁻⁶`
when `c⁴/y²` tends to zero. -/
lemma tendsto_scaled_log_cubic {c : ℝ → ℝ}
    (ht : Tendsto (fun y => c y / y ^ 2) atTop (𝓝 0))
    (hc : Tendsto (fun y => (c y)^4 / y^2) atTop (𝓝 0)) :
    Tendsto (fun y => y^6 * (Real.log (1 + c y / y^2) - c y / y^2
      + (c y / y^2)^2 / 2 - (c y / y^2)^3 / 3)) atTop (𝓝 0) := by
  have ha : Tendsto (fun y => |c y / y^2|) atTop (𝓝 0) := by
    simpa using ht.abs
  have hb : Tendsto (fun y => ((c y)^4 / y^2) / (1 - |c y / y^2|)) atTop (𝓝 0) := by
    simpa using hc.div (tendsto_const_nhds.sub ha) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    ha.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with y hy hsmall
  set t := c y / y^2 with hteq
  have hR := Real.abs_log_sub_add_sum_range_le (x := -t) (by simpa using hsmall) 3
  norm_num [Finset.sum_range_succ] at hR
  have heq : (-t + t^2/2 + (-t)^3/3) + Real.log (1+t) =
      Real.log (1+t) - t + t^2/2 - t^3/3 := by ring
  rw [heq] at hR
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ y^6)]
  calc
    y^6 * |Real.log (1+t) - t + t^2/2 - t^3/3|
        ≤ y^6 * (|t|^4 / (1-|t|)) := mul_le_mul_of_nonneg_left hR (by positivity)
    _ = ((c y)^4 / y^2) / (1 - |c y / y^2|) := by
      rw [hteq, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (c y / y^2)^4)]
      field_simp

end LogTaylor

section MillsFactor

-- no-dlmf: normalization of `erfc` used to run the asymptotic inversion of 7.17.3
/-- The normalized Mills factor `M y = √π · y · e^{y²} · erfc y`.  DLMF 7.12.1 says
`M y ∼ 1 - 1/(2y²) + 3/(4y⁴) - ⋯` as `y → +∞`. -/
noncomputable def erfcMills (y : ℝ) : ℝ := y * Real.sqrt Real.pi * Real.exp (y ^ 2) * erfc y

-- no-dlmf: support lemma for 7.17.3 — positivity of the Mills factor
/-- `erfcMills y > 0` for `y > 0`. -/
theorem erfcMills_pos {y : ℝ} (hy : 0 < y) : 0 < erfcMills y := by
  have h1 : (0:ℝ) < erfc y := erfc_pos y
  have h2 : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h3 : (0:ℝ) < Real.exp (y ^ 2) := Real.exp_pos _
  unfold erfcMills
  positivity

-- no-dlmf: support limit for 7.17.3 — leading `erfc` asymptotics, restated
/-- `erfcMills y → 1` as `y → ∞` (DLMF 7.12.1, leading order). -/
theorem tendsto_erfcMills : Tendsto erfcMills atTop (𝓝 1) := erfc_asymptotic

-- no-dlmf: support limit for 7.17.3 — the *second* order of DLMF 7.12.1 on the real axis
/-- `y² · (erfcMills y - 1) → -1/2` as `y → ∞`: the second term `-1/(2y²)` of the `erfc`
asymptotic expansion (DLMF 7.12.1 at truncation order `N = 1`). -/
theorem tendsto_sq_mul_erfcMills_sub_one :
    Tendsto (fun y : ℝ => y ^ 2 * (erfcMills y - 1)) atTop (𝓝 (-(1/2))) := by
  have h := erfc_7_12_1 1
  simp only [Finset.sum_range_one, ascPochhammer_zero, ascPochhammer_one] at h
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  unfold erfcMills
  field_simp

-- no-dlmf: cubic Mills-factor input for the higher-order inversion
/-- The normalized Mills factor through its `y⁻⁶` term. -/
theorem tendsto_six_mul_erfcMills_cubic_remainder :
    Tendsto (fun y : ℝ => y ^ 6 *
      (erfcMills y - 1 + 1 / (2 * y ^ 2) - 3 / (4 * y ^ 4)
        + 15 / (8 * y ^ 6))) atTop (𝓝 0) := by
  have h := (erfc_7_12_1 3).add_const (15 / 8 : ℝ)
  norm_num [Finset.sum_range_succ, ascPochhammer_succ_eval,
    ascPochhammer_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  unfold erfcMills
  field_simp
  ring

-- no-dlmf: quadratic Mills-factor coefficient used in logarithmic inversion
theorem tendsto_four_mul_erfcMills_quadratic_remainder :
    Tendsto (fun y : ℝ => y ^ 4 *
      (erfcMills y - 1 + 1 / (2 * y ^ 2))) atTop (𝓝 (3 / 4)) := by
  have h := erfc_7_12_1 2
  norm_num [Finset.sum_range_succ, ascPochhammer_succ_eval,
    ascPochhammer_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  unfold erfcMills
  field_simp
  ring

-- no-dlmf: support limit for 7.17.3
/-- `y² · ln (erfcMills y) → -1/2` as `y → ∞` (squeeze `(M-1)/M ≤ ln M ≤ M-1`). -/
theorem tendsto_sq_mul_log_erfcMills :
    Tendsto (fun y : ℝ => y ^ 2 * Real.log (erfcMills y)) atTop (𝓝 (-(1/2))) := by
  have hM := tendsto_erfcMills
  have hS := tendsto_sq_mul_erfcMills_sub_one
  have hlow : Tendsto (fun y : ℝ => y ^ 2 * (erfcMills y - 1) / erfcMills y)
      atTop (𝓝 (-(1/2))) := by
    have := hS.div hM one_ne_zero
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hS ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hMp : 0 < erfcMills y := erfcMills_pos hy
    have hb : (erfcMills y - 1) / erfcMills y ≤ Real.log (erfcMills y) := by
      have h := Real.log_le_sub_one_of_pos (x := (erfcMills y)⁻¹) (by positivity)
      rw [Real.log_inv] at h
      have hinv : (erfcMills y)⁻¹ - 1 = -((erfcMills y - 1) / erfcMills y) := by
        field_simp
        ring
      rw [hinv] at h
      linarith
    have hy2 : (0:ℝ) < y ^ 2 := by positivity
    calc y ^ 2 * (erfcMills y - 1) / erfcMills y
        = y ^ 2 * ((erfcMills y - 1) / erfcMills y) := by ring
      _ ≤ y ^ 2 * Real.log (erfcMills y) := by nlinarith
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hMp : 0 < erfcMills y := erfcMills_pos hy
    have hb : Real.log (erfcMills y) ≤ erfcMills y - 1 := Real.log_le_sub_one_of_pos hMp
    have hy2 : (0:ℝ) < y ^ 2 := by positivity
    nlinarith

-- no-dlmf: support limit for 7.17.3
/-- `ln (erfcMills y) → 0` as `y → ∞`. -/
theorem tendsto_log_erfcMills_zero :
    Tendsto (fun y : ℝ => Real.log (erfcMills y)) atTop (𝓝 0) := by
  have h := (Real.continuousAt_log (one_ne_zero)).tendsto.comp tendsto_erfcMills
  simpa using h

-- no-dlmf: logarithmic Taylor control at the scale needed for cubic inversion
/-- Taylor expansion of `log M` through the cubic term in `M - 1`, with
remainder little-o of `y⁻⁶`. -/
theorem tendsto_six_mul_log_erfcMills_taylor_remainder :
    Tendsto (fun y : ℝ => y ^ 6 *
      (Real.log (erfcMills y) - (erfcMills y - 1)
        + (erfcMills y - 1) ^ 2 / 2 - (erfcMills y - 1) ^ 3 / 3))
      atTop (𝓝 0) := by
  have hM : Tendsto (fun y : ℝ => erfcMills y - 1) atTop (𝓝 0) := by
    simpa using tendsto_erfcMills.sub_const 1
  have hQ := tendsto_log_cubic_remainder.comp hM
  have h := hQ.mul (tendsto_sq_mul_erfcMills_sub_one.pow 3)
  simp only [zero_mul] at h
  refine h.congr fun y => ?_
  have hsum : 1 + (erfcMills y - 1) = erfcMills y := by ring
  dsimp only [Function.comp_apply]
  rw [hsum]
  by_cases hzero : erfcMills y - 1 = 0
  · have hMone : erfcMills y = 1 := sub_eq_zero.mp hzero
    simp [hMone]
  · field_simp

-- no-dlmf: cubic logarithmic Mills-factor input for higher-order inversion
/-- The logarithmic Mills factor has coefficients `-1/2`, `5/8`, and
`-37/24` at powers `y⁻²`, `y⁻⁴`, and `y⁻⁶`. -/
theorem tendsto_six_mul_log_erfcMills_cubic_remainder :
    Tendsto (fun y : ℝ => y ^ 6 *
      (Real.log (erfcMills y) + 1 / (2 * y ^ 2) - 5 / (8 * y ^ 4)
        + 37 / (24 * y ^ 6))) atTop (𝓝 0) := by
  have hminus : Tendsto (fun y : ℝ =>
      y ^ 2 * (erfcMills y - 1 - 1 / (2 * y ^ 2))) atTop (𝓝 (-1)) := by
    have h := tendsto_sq_mul_erfcMills_sub_one.sub_const (1 / 2 : ℝ)
    norm_num at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    field_simp
  have hsq := tendsto_four_mul_erfcMills_quadratic_remainder.mul hminus
  have hc := tendsto_sq_mul_erfcMills_sub_one.pow 3
  have h := (((tendsto_six_mul_log_erfcMills_taylor_remainder.add
    tendsto_six_mul_erfcMills_cubic_remainder).sub (hsq.div_const 2)).add
    (hc.div_const 3)).sub_const (1 / 3 : ℝ)
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp
  ring

end MillsFactor

section LogVariables

-- no-dlmf: auxiliary quantity for the 7.17.3 inversion
/-- `A y = ln y + ½ ln π - ln (erfcMills y)`, the exact gap in `ln(1/erfc y) = y² + A y`. -/
noncomputable def inverfcAuxA (y : ℝ) : ℝ :=
  Real.log y + (1/2) * Real.log Real.pi - Real.log (erfcMills y)

-- no-dlmf: auxiliary quantity for the 7.17.3 inversion
/-- `W y = ln (ln (1/erfc y)) - 2 ln y = ln (ln(1/erfc y) / y²)`. -/
noncomputable def inverfcAuxW (y : ℝ) : ℝ :=
  Real.log (Real.log (1 / erfc y)) - 2 * Real.log y

-- no-dlmf: support lemma for 7.17.3
/-- `erfc y < 1` for `y > 0`. -/
theorem erfc_lt_one_of_pos {y : ℝ} (hy : 0 < y) : erfc y < 1 := by
  have h := strictAnti_erfc hy
  rwa [erfc_zero] at h

-- no-dlmf: support lemma for 7.17.3
/-- `ln (1 / erfc y) > 0` for `y > 0`. -/
theorem log_inv_erfc_pos {y : ℝ} (hy : 0 < y) : 0 < Real.log (1 / erfc y) := by
  rw [one_div, Real.log_inv, neg_pos]
  exact Real.log_neg (erfc_pos y) (erfc_lt_one_of_pos hy)

-- no-dlmf: support lemma for 7.17.3 — the exact logarithmic form of `erfc y = x`
/-- `ln (1 / erfc y) = y² + ln y + ½ ln π - ln (erfcMills y)` for `y > 0`. -/
theorem log_inv_erfc_eq {y : ℝ} (hy : 0 < y) :
    Real.log (1 / erfc y)
      = y ^ 2 + Real.log y + (1/2) * Real.log Real.pi - Real.log (erfcMills y) := by
  have h0 : (0:ℝ) < erfc y := erfc_pos y
  have hs : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlogM : Real.log (erfcMills y)
      = Real.log y + Real.log (Real.sqrt Real.pi) + y ^ 2 + Real.log (erfc y) := by
    unfold erfcMills
    rw [Real.log_mul (by positivity) h0.ne', Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul hy.ne' hs.ne', Real.log_exp]
  rw [hlogM, Real.log_sqrt Real.pi_pos.le, one_div, Real.log_inv]
  ring

-- no-dlmf: support lemma for 7.17.3
/-- `ln (1 / erfc y) = y² + A y` for `y > 0`. -/
theorem log_inv_erfc_eq_add_auxA {y : ℝ} (hy : 0 < y) :
    Real.log (1 / erfc y) = y ^ 2 + inverfcAuxA y := by
  rw [log_inv_erfc_eq hy]
  unfold inverfcAuxA
  ring

-- no-dlmf: support lemma for 7.17.3
/-- `W y = ln (1 + A y / y²)` for `y > 0`. -/
theorem inverfcAuxW_eq {y : ℝ} (hy : 0 < y) :
    inverfcAuxW y = Real.log (1 + inverfcAuxA y / y ^ 2) := by
  have hL : 0 < Real.log (1 / erfc y) := log_inv_erfc_pos hy
  have hy2 : (0:ℝ) < y ^ 2 := by positivity
  have hz : 1 + inverfcAuxA y / y ^ 2 = Real.log (1 / erfc y) / y ^ 2 := by
    rw [log_inv_erfc_eq_add_auxA hy]; field_simp
  unfold inverfcAuxW
  rw [hz, Real.log_div hL.ne' hy2.ne', Real.log_pow]
  push_cast
  ring

-- no-dlmf: support limit for 7.17.3
/-- `A y / y → 0` as `y → ∞`. -/
theorem tendsto_auxA_div_id : Tendsto (fun y : ℝ => inverfcAuxA y / y) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun y : ℝ => (1/2) * Real.log Real.pi / y) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id _
  have h3 : Tendsto (fun y : ℝ => Real.log (erfcMills y) / y) atTop (𝓝 0) := by
    have := tendsto_log_erfcMills_zero.mul tendsto_inv_atTop_zero
    rw [mul_zero] at this
    exact this.congr (fun y => by rw [div_eq_mul_inv])
  have h := (h1.add h2).sub h3
  simp only [add_zero, sub_zero] at h
  refine h.congr fun y => ?_
  unfold inverfcAuxA
  ring

-- no-dlmf: support limit for 7.17.3
/-- `A y / y² → 0` as `y → ∞`. -/
theorem tendsto_auxA_div_sq : Tendsto (fun y : ℝ => inverfcAuxA y / y ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => ((1/2) * Real.log Real.pi + 1 * Real.log y) / y ^ 2)
      atTop (𝓝 0) := tendsto_affine_log_div_sq _ _
  have h3 : Tendsto (fun y : ℝ => Real.log (erfcMills y) / y ^ 2) atTop (𝓝 0) := by
    have := tendsto_log_erfcMills_zero.mul
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero))
    rw [mul_zero] at this
    exact this.congr (fun y => by simp [div_eq_mul_inv])
  have h := h1.sub h3
  rw [sub_zero] at h
  refine h.congr fun y => ?_
  unfold inverfcAuxA
  ring

-- no-dlmf: support limit for 7.17.3
/-- `W y → 0` as `y → ∞`. -/
theorem tendsto_auxW_zero : Tendsto inverfcAuxW atTop (𝓝 0) := by
  have hc : Tendsto (fun y : ℝ => 1 + inverfcAuxA y / y ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add tendsto_auxA_div_sq
  have h : Tendsto (fun y : ℝ => Real.log (1 + inverfcAuxA y / y ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hc
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  exact (inverfcAuxW_eq hy).symm

-- no-dlmf: support lemma for 7.17.3
/-- `A y ≥ 0` for all large `y`. -/
theorem eventually_auxA_nonneg : ∀ᶠ y : ℝ in atTop, 0 ≤ inverfcAuxA y := by
  have h1 : ∀ᶠ y : ℝ in atTop, Real.log (erfcMills y) < 1 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) tendsto_log_erfcMills_zero
  have h2 : ∀ᶠ y : ℝ in atTop, 1 + |(1/2) * Real.log Real.pi| ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [h1, h2] with y hy1 hy2
  unfold inverfcAuxA
  have h3 := neg_abs_le ((1/2) * Real.log Real.pi)
  linarith

-- no-dlmf: support limit for 7.17.3 — the second-order expansion of the inner logarithm
/-- `y² · W y - A y → 0` as `y → ∞` (from `0 ≤ z - ln(1+z) ≤ z²` for `z ≥ 0`). -/
theorem tendsto_sq_mul_auxW_sub_auxA :
    Tendsto (fun y : ℝ => y ^ 2 * inverfcAuxW y - inverfcAuxA y) atTop (𝓝 0) := by
  have hsq : Tendsto (fun y : ℝ => -(inverfcAuxA y / y) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_auxA_div_id.pow 2).neg
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq tendsto_const_nhds ?_ ?_ <;>
    filter_upwards [eventually_gt_atTop (0:ℝ), eventually_auxA_nonneg] with y hy hA
  · have hy2 : (0:ℝ) < y ^ 2 := by positivity
    set z := inverfcAuxA y / y ^ 2 with hzdef
    have hz0 : 0 ≤ z := div_nonneg hA (by positivity)
    have hkey : y ^ 2 * inverfcAuxW y - inverfcAuxA y = y ^ 2 * (Real.log (1 + z) - z) := by
      rw [inverfcAuxW_eq hy, hzdef]; field_simp
    have hlow : z - z ^ 2 ≤ Real.log (1 + z) := by
      have h := Real.log_le_sub_one_of_pos (x := (1 + z)⁻¹) (by positivity)
      rw [Real.log_inv] at h
      have hinv : (1 + z)⁻¹ - 1 = -(z / (1 + z)) := by field_simp; ring
      rw [hinv] at h
      have h2 : z - z ^ 2 ≤ z / (1 + z) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      linarith
    have hAz : inverfcAuxA y / y = y * z := by rw [hzdef]; field_simp
    rw [hkey, hAz]
    nlinarith [mul_le_mul_of_nonneg_left hlow hy2.le]
  · have hy2 : (0:ℝ) < y ^ 2 := by positivity
    set z := inverfcAuxA y / y ^ 2 with hzdef
    have hz0 : 0 ≤ z := div_nonneg hA (by positivity)
    have hkey : y ^ 2 * inverfcAuxW y - inverfcAuxA y = y ^ 2 * (Real.log (1 + z) - z) := by
      rw [inverfcAuxW_eq hy, hzdef]; field_simp
    have hup : Real.log (1 + z) ≤ z := by
      have := Real.log_le_sub_one_of_pos (x := 1 + z) (by linarith)
      linarith
    rw [hkey]
    nlinarith

end LogVariables

section InversionGap

-- no-dlmf: the inversion gap driving the 7.17.3 expansion
/-- The **inversion gap** `S y = y² - u⁻¹` along `x = erfc y`, `u = asymU x` (DLMF 7.17.5).
The whole expansion 7.17.3 is the statement that `S` has an asymptotic expansion in `u`
whose coefficients are polynomials in `v = asymV x` (DLMF 7.17.6). -/
noncomputable def inverfcAuxS (y : ℝ) : ℝ := y ^ 2 - (asymU (erfc y))⁻¹

-- no-dlmf: support lemma for 7.17.3 — `asymU` (7.17.5) unfolded along `x = erfc y`
/-- `(asymU (erfc y))⁻¹ = ln(1/erfc y) - ½ ln π - ½ ln (ln (1/erfc y))` for `y > 0`. -/
theorem asymU_erfc_inv_eq {y : ℝ} (hy : 0 < y) :
    (asymU (erfc y))⁻¹
      = Real.log (1 / erfc y) - (1/2) * Real.log Real.pi
        - (1/2) * Real.log (Real.log (1 / erfc y)) := by
  have h0 : (0:ℝ) < erfc y := erfc_pos y
  have h1 : erfc y < 1 := erfc_lt_one_of_pos hy
  have hL : (0:ℝ) < Real.log (1 / erfc y) := log_inv_erfc_pos hy
  rw [asymU_of_mem h0 h1, inv_div]
  have hD : Real.log (Real.pi * erfc y ^ 2 * Real.log (1 / erfc y))
      = Real.log Real.pi + 2 * Real.log (erfc y) + Real.log (Real.log (1 / erfc y)) := by
    rw [Real.log_mul (by positivity) hL.ne', Real.log_mul Real.pi_ne_zero (by positivity),
      Real.log_pow]
    push_cast
    ring
  rw [hD]
  have hlog : Real.log (erfc y) = - Real.log (1 / erfc y) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hlog]
  ring

-- no-dlmf: support lemma for 7.17.3 — `asymV` (7.17.6) unfolded along `x = erfc y`
/-- `asymV (erfc y) = W y + 2 ln y - 2 + ln π` for `y > 0`. -/
theorem asymV_erfc_eq {y : ℝ} (hy : 0 < y) :
    asymV (erfc y) = inverfcAuxW y + 2 * Real.log y - 2 + Real.log Real.pi := by
  rw [asymV_of_mem (erfc_pos y) (erfc_lt_one_of_pos hy)]
  unfold inverfcAuxW
  ring

-- no-dlmf: support lemma for 7.17.3 — the exact form of the inversion gap
/-- **The exact inversion identity**: `S y = ln (erfcMills y) + ½ W y` for `y > 0`.
Everything about 7.17.3 beyond the leading order flows from this. -/
theorem inverfcAuxS_eq {y : ℝ} (hy : 0 < y) :
    inverfcAuxS y = Real.log (erfcMills y) + inverfcAuxW y / 2 := by
  unfold inverfcAuxS inverfcAuxW
  rw [asymU_erfc_inv_eq hy, log_inv_erfc_eq hy]
  ring

-- no-dlmf: exact relation between the two auxiliary inversion variables
/-- The auxiliary logarithmic gap in terms of the DLMF variable `v` and the
inversion gap `S`.  This eliminates `log y` from the higher-order inversion. -/
theorem inverfcAuxA_eq_asymV_sub_auxS {y : ℝ} (hy : 0 < y) :
    inverfcAuxA y = 1 + asymV (erfc y) / 2 - inverfcAuxS y := by
  rw [asymV_erfc_eq hy, inverfcAuxS_eq hy]
  unfold inverfcAuxA
  ring

-- no-dlmf: exact implicit scalar equation used for higher-order inversion
/-- An exact scalar equation for `S`, with all logarithmic coefficients
expressed through the DLMF variable `v`. -/
theorem inverfcAuxS_implicit_eq {y : ℝ} (hy : 0 < y) :
    inverfcAuxS y = Real.log (erfcMills y) +
      Real.log (1 + (1 + asymV (erfc y) / 2 - inverfcAuxS y) / y ^ 2) / 2 := by
  calc
    inverfcAuxS y = Real.log (erfcMills y) + inverfcAuxW y / 2 :=
      inverfcAuxS_eq hy
    _ = Real.log (erfcMills y) +
      Real.log (1 + (1 + asymV (erfc y) / 2 - inverfcAuxS y) / y ^ 2) / 2 := by
        rw [inverfcAuxW_eq hy, inverfcAuxA_eq_asymV_sub_auxS hy]

-- no-dlmf: support limit for 7.17.3
/-- `S y → 0` as `y → ∞`. -/
theorem tendsto_inverfcAuxS_zero : Tendsto inverfcAuxS atTop (𝓝 0) := by
  have h := tendsto_log_erfcMills_zero.add (tendsto_auxW_zero.div_const 2)
  simp only [zero_div, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  exact (inverfcAuxS_eq hy).symm

-- no-dlmf: the *second* order of the 7.17.3 inversion (the `a₂` step), in the `y` variable
/-- **First bootstrap step.**  `y² · S y - v/4 → 0` as `y → ∞`, where `v = asymV (erfc y)`
is the 7.17.6 variable.  Equivalently `S = (v/4)·u + o(u)`, which is the `a₂ = v/8` term
of the 7.17.3 display.  The `-1/2` limit of `y² ln (erfcMills y)` (the `-1/(2y²)` term of
the `erfc` expansion 7.12.1) is exactly what produces the `-2` in DLMF's `v`. -/
theorem tendsto_sq_mul_inverfcAuxS_sub :
    Tendsto (fun y : ℝ => y ^ 2 * inverfcAuxS y - asymV (erfc y) / 4) atTop (𝓝 0) := by
  have h1 := tendsto_sq_mul_log_erfcMills
  have h2 := tendsto_sq_mul_auxW_sub_auxA
  have h3 := tendsto_log_erfcMills_zero
  have h4 := tendsto_auxW_zero
  have h := ((((h1.add (h2.div_const 2)).sub (h3.div_const 2)).sub
    (h4.div_const 4)).add_const (1/2))
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [inverfcAuxS_eq hy, asymV_erfc_eq hy]
  unfold inverfcAuxA
  ring

end InversionGap

section NormalizedForm

-- no-dlmf: the algebraic core of the passage `inversion gap → DLMF 7.17.3 display`
/-- **Normalized gap identity.**  With `P = y √u`, `S = y² - u⁻¹` and any `V`,
`(P - 1 - (V/8) u²)/u² = -S²/(2(P+1)²) + (y² S - S² - V/4)/2`.
This is the exact form of `P - 1 = ½(P²-1) - ½(P-1)²` after `P² - 1 = u S`. -/
theorem normalized_gap_identity {y u s v p : ℝ} (hu : u ≠ 0) (hp : p + 1 ≠ 0)
    (hpsq : p ^ 2 = y ^ 2 * u) (hs : s = y ^ 2 - u⁻¹) :
    (p - 1 - (v / 8) * u ^ 2) / u ^ 2
      = -((s ^ 2) / (2 * (p + 1) ^ 2)) + (y ^ 2 * s - s ^ 2 - v / 4) / 2 := by
  have hs' : u * s = y ^ 2 * u - 1 := by rw [hs]; field_simp
  have hb : u * (y ^ 2 - s) = 1 := by rw [mul_sub, hs']; ring
  have ha : u * s = p ^ 2 - 1 := by rw [hs', hpsq]
  have hys : y ^ 2 * s - s ^ 2 = s / u := by
    field_simp
    linear_combination s * hb
  have hsval : s = (p ^ 2 - 1) / u := by
    field_simp
    linear_combination ha
  rw [hys, hsval]
  field_simp
  ring

-- no-dlmf: normalized two-term form of DLMF 7.17.3, in the `y = inverfc x` variable
/-- `(y √u - 1 - a₂ u²)/u² → 0` as `y → ∞`, along `x = erfc y` (`u = asymU x`,
`a₂ = asymA x 2`). -/
theorem tendsto_normalized_two_term_atTop :
    Tendsto (fun y : ℝ =>
        (y * Real.sqrt (asymU (erfc y)) - 1 - asymA (erfc y) 2 * (asymU (erfc y)) ^ 2)
          / (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have hP : Tendsto (fun y : ℝ => y * Real.sqrt (asymU (erfc y))) atTop (𝓝 1) :=
    tendsto_mul_sqrt_asymU
  have hS := tendsto_inverfcAuxS_zero
  have hnum : Tendsto (fun y : ℝ => (inverfcAuxS y) ^ 2) atTop (𝓝 0) := by
    simpa using hS.pow 2
  have hden : Tendsto (fun y : ℝ => 2 * (y * Real.sqrt (asymU (erfc y)) + 1) ^ 2)
      atTop (𝓝 8) := by
    have h1 : Tendsto (fun y : ℝ => y * Real.sqrt (asymU (erfc y)) + 1) atTop (𝓝 2) := by
      have := hP.add (tendsto_const_nhds (α := ℝ) (x := (1:ℝ)) (f := atTop))
      norm_num at this
      exact this
    have h := (h1.pow 2).const_mul (2:ℝ)
    norm_num at h
    exact h
  have hterm1 : Tendsto (fun y : ℝ =>
      -((inverfcAuxS y) ^ 2 / (2 * (y * Real.sqrt (asymU (erfc y)) + 1) ^ 2)))
      atTop (𝓝 0) := by
    have h := (hnum.div hden (by norm_num)).neg
    simpa using h
  have hterm2 : Tendsto (fun y : ℝ =>
      (y ^ 2 * inverfcAuxS y - (inverfcAuxS y) ^ 2 - asymV (erfc y) / 4) / 2)
      atTop (𝓝 0) := by
    have h := (tendsto_sq_mul_inverfcAuxS_sub.sub hnum).div_const 2
    norm_num at h
    refine h.congr fun y => ?_
    ring
  have h := hterm1.add hterm2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_asymU_pos_atTop] with y hy hU
  have hr : 0 < Real.sqrt (asymU (erfc y)) := Real.sqrt_pos.mpr hU
  have hpsq : (y * Real.sqrt (asymU (erfc y))) ^ 2 = y ^ 2 * asymU (erfc y) := by
    rw [mul_pow, Real.sq_sqrt hU.le]
  have hp1 : y * Real.sqrt (asymU (erfc y)) + 1 ≠ 0 := by positivity
  have ha2 : asymA (erfc y) 2 = asymV (erfc y) / 8 := by
    rw [erf_7_17_4_a2]; ring
  rw [ha2]
  exact (normalized_gap_identity (v := asymV (erfc y)) hU.ne' hp1 hpsq rfl).symm

-- no-dlmf: normalized two-term form of DLMF 7.17.3, pulled back to `x → 0⁺`
/-- `(inverfc x · √u - 1 - a₂ u²)/u² → 0` as `x → 0⁺`. -/
theorem tendsto_normalized_two_term :
    Tendsto (fun x : ℝ =>
        (inverfc x * Real.sqrt (asymU x) - 1 - asymA x 2 * (asymU x) ^ 2)
          / (asymU x) ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hcomp := tendsto_normalized_two_term_atTop.comp tendsto_inverfc_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_mem_Ioo] with x hx
  simp only [Function.comp_apply]
  rw [inverfc_erfc_eq x hx.1 hx.2]

end NormalizedForm

section RpowDictionary

-- no-dlmf: support lemma for 7.17.3 — half-integer powers of `u` in terms of `√u`
/-- `u^{-1/2} = (√u)⁻¹` for `u > 0`. -/
theorem rpow_neg_half {u : ℝ} (hu : 0 < u) : u ^ (-(1:ℝ)/2) = (Real.sqrt u)⁻¹ := by
  rw [show (-(1:ℝ)) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]

-- no-dlmf: support lemma for 7.17.3 — half-integer powers of `u` in terms of `√u`
/-- `u^{(2n+1)/2} = uⁿ · √u` for `u > 0` and `n : ℕ`. -/
theorem rpow_half_odd {u : ℝ} (hu : 0 < u) (n : ℕ) :
    u ^ ((2 * (n : ℝ) + 1) / 2) = u ^ n * Real.sqrt u := by
  rw [show (2 * (n : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 by ring, Real.rpow_add hu,
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]

-- no-dlmf: support lemma for 7.17.3 — the `√u`-form of the two-term truncation ratio
/-- `(y - (r⁻¹ + a·u·r))/(u·r) = (y r - 1 - a u²)/u²` when `u = r²`, `r > 0`. -/
theorem two_term_ratio {u r y a : ℝ} (hr : 0 < r) (hu : u = r ^ 2) :
    (y - (r⁻¹ + a * (u ^ 1 * r))) / (u ^ 1 * r) = (y * r - 1 - a * u ^ 2) / u ^ 2 := by
  subst hu
  field_simp
  ring

-- no-dlmf: support lemma for 7.17.3 — the `√u`-form of the four-term truncation ratio
/-- `(y - (r⁻¹ + a₂ u r + a₃ u² r + a₄ u³ r))/(u³ r) = (y r - 1 - a₂u² - a₃u³ - a₄u⁴)/u⁴`
when `u = r²`, `r > 0`. -/
theorem four_term_ratio {u r y a₂ a₃ a₄ : ℝ} (hr : 0 < r) (hu : u = r ^ 2) :
    (y - (r⁻¹ + a₂ * (u ^ 1 * r) + a₃ * (u ^ 2 * r) + a₄ * (u ^ 3 * r))) / (u ^ 3 * r)
      = (y * r - 1 - (a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4)) / u ^ 4 := by
  subst hu
  field_simp
  ring

end RpowDictionary

section TwoTerm

/-- **Two-term truncation of DLMF 7.17.3** (stepping stone; `sorry`-free).
As `x → 0⁺`, with `u = asymU x` (7.17.5) and `a₂ = asymA x 2 = v/8` (7.17.4),

`inverfc x = u^{-1/2} + a₂ u^{3/2} + o(u^{3/2})`.

This strictly improves on `erf_7_17_3` (which stops at the leading term `u^{-1/2}`); the
faithful full display 7.17.3 carries two further terms and is `erf_7_17_3_full` below.
-/
-- no-dlmf: two-term truncation of DLMF 7.17.3; the faithful full display is `erf_7_17_3_full`
theorem inverfc_two_term_expansion :
    (fun x : ℝ => inverfc x
        - ((asymU x) ^ (-(1:ℝ)/2) + asymA x 2 * (asymU x) ^ ((3:ℝ)/2)))
      =o[𝓝[>] (0:ℝ)] (fun x : ℝ => (asymU x) ^ ((3:ℝ)/2)) := by
  have hzero : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ),
      (asymU x) ^ ((3:ℝ)/2) = 0 →
        inverfc x - ((asymU x) ^ (-(1:ℝ)/2) + asymA x 2 * (asymU x) ^ ((3:ℝ)/2)) = 0 := by
    filter_upwards [eventually_asymU_pos] with x hx hcon
    exact absurd hcon (by positivity)
  rw [Asymptotics.isLittleO_iff_tendsto' hzero]
  refine tendsto_normalized_two_term.congr' ?_
  filter_upwards [eventually_asymU_pos] with x hx
  have hr : 0 < Real.sqrt (asymU x) := Real.sqrt_pos.mpr hx
  have hsq : asymU x = Real.sqrt (asymU x) ^ 2 := (Real.sq_sqrt hx.le).symm
  rw [rpow_neg_half hx, show ((3:ℝ)/2) = (2 * ((1:ℕ) : ℝ) + 1) / 2 by norm_num,
    rpow_half_odd hx 1]
  exact (two_term_ratio hr hsq).symm

end TwoTerm

section Rates

/-! ### Rate lemmas: `v^k u^j → 0`

The transfer from the inversion gap `S` to the DLMF display needs to know that the
`v`-polynomial coefficients are dominated by the powers of `u`: since `v ≍ 2 ln y` and
`u ≍ y^{-2}`, every `v^k u^j` with `k ≤ 3, j ≥ 1` (and `k ≤ 4, j ≥ 2`) tends to `0`.
The root estimate is `(ln y)³/y² → 0`, from `ln y ≤ 2√y`.
-/

-- no-dlmf: elementary rate lemma used by the 7.17.3 transfer
/-- `(ln y)³ / y² → 0` as `y → ∞` (from `ln y ≤ 2√y`). -/
theorem tendsto_log_cube_div_sq :
    Tendsto (fun y : ℝ => (Real.log y) ^ 3 / y ^ 2) atTop (𝓝 0) := by
  have hbnd : Tendsto (fun y : ℝ => 8 / Real.sqrt y) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop Real.tendsto_sqrt_atTop 8
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbnd ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have h : 0 ≤ Real.log y := Real.log_nonneg hy
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have hs : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
    have hlog : Real.log y ≤ 2 * Real.sqrt y := by
      have h := Real.log_le_sub_one_of_pos hs
      rw [Real.log_sqrt hy0.le] at h
      linarith
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
    have hcube : (Real.log y) ^ 3 ≤ 8 * Real.sqrt y ^ 3 := by
      have h1 : (Real.log y) ^ 3 ≤ (2 * Real.sqrt y) ^ 3 := pow_le_pow_left₀ hlogy hlog 3
      nlinarith [h1]
    rw [div_le_div_iff₀ (by positivity) hs]
    calc (Real.log y) ^ 3 * Real.sqrt y ≤ (8 * Real.sqrt y ^ 3) * Real.sqrt y :=
          mul_le_mul_of_nonneg_right hcube hs.le
      _ = 8 * (Real.sqrt y ^ 2) ^ 2 := by ring
      _ = 8 * y ^ 2 := by rw [hsq]

-- no-dlmf: support lemma for 7.17.3 — crude two-sided control of the 7.17.6 variable
/-- `1 ≤ v` and `|v| ≤ 3 ln y` for all large `y`, along `x = erfc y`. -/
theorem eventually_asymV_bounds :
    ∀ᶠ y : ℝ in atTop, 1 ≤ asymV (erfc y) ∧ |asymV (erfc y)| ≤ 3 * Real.log y := by
  set C : ℝ := |(-2 : ℝ) + Real.log Real.pi| with hC
  have hW : ∀ᶠ y : ℝ in atTop, |inverfcAuxW y| ≤ 1 := by
    have h := tendsto_auxW_zero.norm
    rw [norm_zero] at h
    exact h.eventually_le_const (by norm_num)
  have hlog : ∀ᶠ y : ℝ in atTop, 4 + C ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop (0:ℝ), hW, hlog] with y hy hWy hly
  have hV := asymV_erfc_eq hy
  have hC1 : -C ≤ (-2 : ℝ) + Real.log Real.pi := by rw [hC]; exact neg_abs_le _
  have hC2 : (-2 : ℝ) + Real.log Real.pi ≤ C := by rw [hC]; exact le_abs_self _
  have hW1 : -1 ≤ inverfcAuxW y := by have := neg_abs_le (inverfcAuxW y); linarith
  have hW2 : inverfcAuxW y ≤ 1 := by have := le_abs_self (inverfcAuxW y); linarith
  have hC0 : 0 ≤ C := abs_nonneg _
  refine ⟨by rw [hV]; linarith, ?_⟩
  rw [abs_le]
  exact ⟨by rw [hV]; linarith, by rw [hV]; linarith⟩

-- no-dlmf: arbitrary logarithmic coefficient rates for cubic inversion
/-- Every fixed power of `v` is dominated by `y²`. -/
theorem tendsto_asymV_pow_div_sq (n : ℕ) :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ n / y ^ 2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun y : ℝ => Real.log y ^ n / y ^ 2) atTop (𝓝 0) := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero.mul
      (Filter.Tendsto.const_div_atTop tendsto_id (1 : ℝ))
    simp only [mul_zero] at h
    exact h.congr fun y => by simp only [id_eq]; ring
  have hbound := hlog.const_mul ((3 : ℝ) ^ n)
  simp only [mul_zero] at hbound
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_asymV_bounds]
    with y hy hV
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_pow, abs_of_pos hy]
  have hp := pow_le_pow_left₀ (abs_nonneg (asymV (erfc y))) hV.2 n
  calc
    |asymV (erfc y)| ^ n / y ^ 2 ≤ (3 * Real.log y) ^ n / y ^ 2 :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = 3 ^ n * (Real.log y ^ n / y ^ 2) := by rw [mul_pow]; ring

-- no-dlmf: polynomial version of the logarithmic coefficient rate
theorem tendsto_polynomial_asymV_div_sq (p : Polynomial ℝ) :
    Tendsto (fun y : ℝ => p.eval (asymV (erfc y)) / y ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ =>
      ∑ n ∈ p.support, p.coeff n * ((asymV (erfc y)) ^ n / y ^ 2)) atTop
      (𝓝 (∑ n ∈ p.support, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro n hn
    simpa using (tendsto_asymV_pow_div_sq n).const_mul (p.coeff n)
  simp only [Finset.sum_const_zero] at h
  refine h.congr fun y => ?_
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

-- no-dlmf: bivariate polynomial remainder estimate for asymptotic inversion
/-- A polynomial in `v` and `y⁻²`, multiplied by `y⁻²`, tends to zero. -/
theorem tendsto_bivariate_polynomial_asymV_div_sq
    (p : Polynomial (Polynomial ℝ)) :
    Tendsto (fun y : ℝ =>
      p.eval₂ (Polynomial.evalRingHom (asymV (erfc y))) (1 / y ^ 2) / y ^ 2)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun y : ℝ => 1 / y ^ 2) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0)) 1
  have h : Tendsto (fun y : ℝ =>
      ∑ n ∈ p.support,
        ((p.coeff n).eval (asymV (erfc y)) / y ^ 2) * (1 / y ^ 2) ^ n)
      atTop (𝓝 (∑ n ∈ p.support, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro n hn
    simpa using (tendsto_polynomial_asymV_div_sq (p.coeff n)).mul (hx.pow n)
  simp only [Finset.sum_const_zero] at h
  refine h.congr fun y => ?_
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Polynomial.coe_evalRingHom]
  ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v³ u → 0` along `x = erfc y`. -/
theorem tendsto_asymV_cube_mul_asymU :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 3 * asymU (erfc y)) atTop (𝓝 0) := by
  have hf : Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 3 / y ^ 2) atTop (𝓝 0) := by
    have hbound : Tendsto (fun y : ℝ => 27 * ((Real.log y) ^ 3 / y ^ 2)) atTop (𝓝 0) := by
      have h := tendsto_log_cube_div_sq.const_mul (27:ℝ)
      simpa using h
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_asymV_bounds] with y hy hVb
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
    have h1 : |asymV (erfc y)| ≤ 3 * Real.log y := hVb.2
    have h2 : |(asymV (erfc y)) ^ 3| ≤ (3 * Real.log y) ^ 3 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < y ^ 2)]
    calc |(asymV (erfc y)) ^ 3| / y ^ 2 ≤ (3 * Real.log y) ^ 3 / y ^ 2 := by gcongr
      _ = 27 * ((Real.log y) ^ 3 / y ^ 2) := by ring
  have hprod := hf.mul tendsto_sq_mul_asymU
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  field_simp

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `u → 0` along `x = erfc y`. -/
theorem tendsto_asymU_erfc_zero : Tendsto (fun y : ℝ => asymU (erfc y)) atTop (𝓝 0) := by
  have h := tendsto_sq_mul_asymU.mul
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  simp only [Function.comp_apply]
  field_simp

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v u → 0` along `x = erfc y`. -/
theorem tendsto_asymV_mul_asymU :
    Tendsto (fun y : ℝ => asymV (erfc y) * asymU (erfc y)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_asymV_cube_mul_asymU <;>
    filter_upwards [eventually_asymV_bounds, eventually_asymU_pos_atTop] with y hV hU
  · have := hV.1; positivity
  · have h1 : (1:ℝ) ≤ asymV (erfc y) := hV.1
    have h2 : asymV (erfc y) ≤ (asymV (erfc y)) ^ 3 := by
      have := pow_le_pow_right₀ h1 (by norm_num : 1 ≤ 3)
      simpa using this
    exact mul_le_mul_of_nonneg_right h2 hU.le

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v² u → 0` along `x = erfc y`. -/
theorem tendsto_asymV_sq_mul_asymU :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 2 * asymU (erfc y)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_asymV_cube_mul_asymU <;>
    filter_upwards [eventually_asymV_bounds, eventually_asymU_pos_atTop] with y hV hU
  · have := hV.1; positivity
  · have h1 : (1:ℝ) ≤ asymV (erfc y) := hV.1
    have h2 : (asymV (erfc y)) ^ 2 ≤ (asymV (erfc y)) ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 hU.le

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v u² → 0` along `x = erfc y`. -/
theorem tendsto_asymV_mul_asymU_sq :
    Tendsto (fun y : ℝ => asymV (erfc y) * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_mul_asymU.mul tendsto_asymU_erfc_zero
  rw [mul_zero] at h
  exact h.congr fun y => by ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v² u² → 0` along `x = erfc y`. -/
theorem tendsto_asymV_sq_mul_asymU_sq :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 2 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_sq_mul_asymU.mul tendsto_asymU_erfc_zero
  rw [mul_zero] at h
  exact h.congr fun y => by ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v³ u² → 0` along `x = erfc y`. -/
theorem tendsto_asymV_cube_mul_asymU_sq :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 3 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_cube_mul_asymU.mul tendsto_asymU_erfc_zero
  rw [mul_zero] at h
  exact h.congr fun y => by ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `v⁴ u² → 0` along `x = erfc y`. -/
theorem tendsto_asymV_four_mul_asymU_sq :
    Tendsto (fun y : ℝ => (asymV (erfc y)) ^ 4 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_sq_mul_asymU.pow 2
  rw [show ((0:ℝ)) ^ 2 = 0 by norm_num] at h
  exact h.congr fun y => by ring

-- no-dlmf: rate lemma for the 7.17.3 transfer (`a₂a₃` is a cubic in `v`)
/-- `a₂ a₃ u → 0` along `x = erfc y`. -/
theorem tendsto_a2_a3_mul_asymU :
    Tendsto (fun y : ℝ => asymA (erfc y) 2 * asymA (erfc y) 3 * asymU (erfc y))
      atTop (𝓝 0) := by
  have h := ((tendsto_asymV_cube_mul_asymU.const_mul (-(1:ℝ)/256)).add
    (tendsto_asymV_sq_mul_asymU.const_mul (-(6:ℝ)/256))).add
    (tendsto_asymV_mul_asymU.const_mul ((6:ℝ)/256))
  norm_num at h
  refine h.congr fun y => ?_
  rw [erf_7_17_4_a2, erf_7_17_4_a3]
  ring

-- no-dlmf: rate lemma for the 7.17.3 transfer (`a₂(2a₄+a₂²)` is a quartic in `v`)
/-- `a₂ (2a₄ + a₂²) u² → 0` along `x = erfc y`. -/
theorem tendsto_a2_a4_mul_asymU_sq :
    Tendsto (fun y : ℝ =>
      asymA (erfc y) 2 * (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2)
        * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := ((((tendsto_asymV_four_mul_asymU_sq.const_mul ((1:ℝ)/384)).add
    (tendsto_asymV_cube_mul_asymU_sq.const_mul ((5:ℝ)/256))).add
    (tendsto_asymV_sq_mul_asymU_sq.const_mul ((9:ℝ)/128))).add
    (tendsto_asymV_mul_asymU_sq.const_mul (-(25:ℝ)/128)))
  norm_num at h
  refine h.congr fun y => ?_
  rw [erf_7_17_4_a2, erf_7_17_4_a4]
  ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `a₂ u² → 0` along `x = erfc y`. -/
theorem tendsto_a2_mul_asymU_sq :
    Tendsto (fun y : ℝ => asymA (erfc y) 2 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_mul_asymU_sq.const_mul ((1:ℝ)/8)
  norm_num at h
  refine h.congr fun y => ?_
  rw [erf_7_17_4_a2]; ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `a₂² u² → 0` along `x = erfc y`. -/
theorem tendsto_a2_sq_mul_asymU_sq :
    Tendsto (fun y : ℝ => (asymA (erfc y) 2) ^ 2 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_sq_mul_asymU_sq.const_mul ((1:ℝ)/64)
  norm_num at h
  refine h.congr fun y => ?_
  rw [erf_7_17_4_a2]; ring

-- no-dlmf: rate lemma for the 7.17.3 transfer
/-- `a₂³ u² → 0` along `x = erfc y`. -/
theorem tendsto_a2_cube_mul_asymU_sq :
    Tendsto (fun y : ℝ => (asymA (erfc y) 2) ^ 3 * (asymU (erfc y)) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_asymV_cube_mul_asymU_sq.const_mul ((1:ℝ)/512)
  norm_num at h
  refine h.congr fun y => ?_
  rw [erf_7_17_4_a2]; ring

end Rates

section FourTerm

-- no-dlmf: stability bound for the scalar logarithmic inversion equation
/-- Monotonicity bounds inversion error by the trial equation residual. -/
lemma implicit_log_error_bound {s t b x m : ℝ} (hx : 0 ≤ x)
    (hs : 0 < 1 + x * (b - s)) (ht : 0 < 1 + x * (b - t))
    (heq : s = m + Real.log (1 + x * (b - s)) / 2) :
    |s - t| ≤ |t - m - Real.log (1 + x * (b - t)) / 2| := by
  rcases le_total s t with hst | hts
  · have harg : 1 + x * (b - t) ≤ 1 + x * (b - s) := by nlinarith
    have hlog := Real.log_le_log ht harg
    have hd : 0 ≤ t - m - Real.log (1 + x * (b - t)) / 2 := by linarith
    rw [abs_of_nonpos (by linarith : s - t ≤ 0), abs_of_nonneg hd]
    linarith
  · have harg : 1 + x * (b - s) ≤ 1 + x * (b - t) := by nlinarith
    have hlog := Real.log_le_log hs harg
    have hd : t - m - Real.log (1 + x * (b - t)) / 2 ≤ 0 := by linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ s - t), abs_of_nonpos hd]
    linarith


-- no-dlmf: polynomial trial for the cubic logarithmic inversion
private noncomputable def gapTrialB : Polynomial ℝ :=
  1 + Polynomial.C (1 / 2) * Polynomial.X

private noncomputable def gapTrialA : Polynomial ℝ :=
  Polynomial.C (1 / 2) * (gapTrialB - 1)

private noncomputable def gapTrialD : Polynomial ℝ :=
  Polynomial.C (5 / 8) - Polynomial.C (1 / 4) * gapTrialB ^ 2
    - Polynomial.C (1 / 2) * gapTrialA

private noncomputable def gapTrialC : Polynomial ℝ :=
  Polynomial.C (-37 / 24) + Polynomial.C (1 / 6) * gapTrialB ^ 3
    + Polynomial.C (1 / 2) * gapTrialB * gapTrialA
    - Polynomial.C (1 / 2) * gapTrialD

private noncomputable def gapTrialQ : Polynomial (Polynomial ℝ) :=
  Polynomial.C gapTrialA + Polynomial.C gapTrialD * Polynomial.X
    + Polynomial.C gapTrialC * Polynomial.X ^ 2

private noncomputable def gapTrialK : Polynomial (Polynomial ℝ) :=
  Polynomial.C gapTrialB - Polynomial.X * gapTrialQ

private noncomputable def gapTrialH : Polynomial (Polynomial ℝ) :=
  Polynomial.C (Polynomial.C (1 / 2) * (gapTrialC - gapTrialB * gapTrialD))
    - Polynomial.C (Polynomial.C (1 / 2) * gapTrialB * gapTrialC) * Polynomial.X
    + Polynomial.C (Polynomial.C (1 / 4)) * gapTrialQ ^ 2
    + Polynomial.C (Polynomial.C (1 / 2) * gapTrialB ^ 2) * gapTrialQ
    - Polynomial.C (Polynomial.C (1 / 2) * gapTrialB) * Polynomial.X * gapTrialQ ^ 2
    + Polynomial.C (Polynomial.C (1 / 6)) * Polynomial.X ^ 2 * gapTrialQ ^ 3

-- no-dlmf: real form of the trial polynomial for the inversion gap
noncomputable def inverfcGapTrial (y : ℝ) : ℝ :=
  let v := asymV (erfc y)
  v / (4 * y ^ 2) - (v ^ 2 + 6 * v - 6) / (16 * y ^ 4)
    + (v ^ 3 / 48 + 7 * v ^ 2 / 32 + 9 * v / 16 - 25 / 16) / y ^ 6

private theorem gapTrial_eval {y : ℝ} (hy : y ≠ 0) :
    inverfcGapTrial y = (1 / y ^ 2) *
      gapTrialQ.eval₂ (Polynomial.evalRingHom (asymV (erfc y))) (1 / y ^ 2) := by
  simp only [inverfcGapTrial, gapTrialQ, gapTrialA, gapTrialD, gapTrialC, gapTrialB,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  field_simp
  ring

-- no-dlmf: polynomial cancellation in the cubic logarithmic inversion
private theorem tendsto_gapTrial_polynomial_residual :
    Tendsto (fun y : ℝ =>
      let t := (1 + asymV (erfc y) / 2 - inverfcGapTrial y) / y ^ 2
      y ^ 6 * (inverfcGapTrial y
        - (-1 / (2 * y ^ 2) + 5 / (8 * y ^ 4) - 37 / (24 * y ^ 6))
        - (t - t ^ 2 / 2 + t ^ 3 / 3) / 2)) atTop (𝓝 0) := by
  have h := tendsto_bivariate_polynomial_asymV_div_sq gapTrialH
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [gapTrial_eval hy.ne']
  simp only [gapTrialH, gapTrialQ, gapTrialA, gapTrialD, gapTrialC, gapTrialB,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  field_simp
  ring

private theorem gapTrialK_eval {y : ℝ} (hy : y ≠ 0) :
    gapTrialK.eval₂ (Polynomial.evalRingHom (asymV (erfc y))) (1 / y ^ 2) =
      1 + asymV (erfc y) / 2 - inverfcGapTrial y := by
  rw [gapTrial_eval hy]
  simp only [gapTrialK, gapTrialB, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  ring

private theorem tendsto_gapTrial_log_argument :
    Tendsto (fun y : ℝ =>
      (1 + asymV (erfc y) / 2 - inverfcGapTrial y) / y ^ 2) atTop (𝓝 0) := by
  have h := tendsto_bivariate_polynomial_asymV_div_sq gapTrialK
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [gapTrialK_eval hy.ne']

private theorem tendsto_gapTrial_log_cubic_remainder :
    Tendsto (fun y : ℝ =>
      let t := (1 + asymV (erfc y) / 2 - inverfcGapTrial y) / y ^ 2
      y ^ 6 * (Real.log (1 + t) - t + t ^ 2 / 2 - t ^ 3 / 3)) atTop (𝓝 0) := by
  apply tendsto_scaled_log_cubic tendsto_gapTrial_log_argument
  have h := tendsto_bivariate_polynomial_asymV_div_sq (gapTrialK ^ 4)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Polynomial.eval₂_pow, gapTrialK_eval hy.ne']

private theorem tendsto_gapTrial_implicit_residual :
    Tendsto (fun y : ℝ => y ^ 6 * (inverfcGapTrial y - Real.log (erfcMills y)
      - Real.log (1 + (1 + asymV (erfc y) / 2 - inverfcGapTrial y) / y ^ 2) / 2))
      atTop (𝓝 0) := by
  have h := (tendsto_gapTrial_polynomial_residual.sub
    tendsto_six_mul_log_erfcMills_cubic_remainder).sub
      (tendsto_gapTrial_log_cubic_remainder.div_const 2)
  norm_num at h
  exact h.congr fun y => by ring

-- no-dlmf: cubic inversion in the elementary variable `y⁻²`
/-- The cubic trial approximation has error little-o of `y⁻⁶`. -/
theorem tendsto_six_mul_inverfcGapTrial_error :
    Tendsto (fun y : ℝ => y ^ 6 * (inverfcAuxS y - inverfcGapTrial y))
      atTop (𝓝 0) := by
  have h := tendsto_gapTrial_implicit_residual.norm
  simp only [norm_zero] at h
  refine squeeze_zero_norm' ?_ h
  have ht := tendsto_gapTrial_log_argument.eventually
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
  have hs := tendsto_auxA_div_sq.eventually
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht, hs] with y hy hty hsy
  have hargS : 0 < 1 + (1 / y ^ 2) *
      (1 + asymV (erfc y) / 2 - inverfcAuxS y) := by
    rw [← inverfcAuxA_eq_asymV_sub_auxS hy]
    simp only [div_eq_mul_inv, one_mul] at hsy ⊢
    nlinarith [hsy]
  have hargT : 0 < 1 + (1 / y ^ 2) *
      (1 + asymV (erfc y) / 2 - inverfcGapTrial y) := by
    simp only [div_eq_mul_inv, one_mul] at hty ⊢
    nlinarith [hty]
  have heq : inverfcAuxS y = Real.log (erfcMills y) +
      Real.log (1 + (1 / y ^ 2) * (1 + asymV (erfc y) / 2 - inverfcAuxS y)) / 2 := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using inverfcAuxS_implicit_eq hy
  have hb := implicit_log_error_bound (by positivity : (0 : ℝ) ≤ 1 / y ^ 2)
    hargS hargT heq
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ y ^ 6)]
  calc
    y ^ 6 * |inverfcAuxS y - inverfcGapTrial y| ≤
        y ^ 6 * |inverfcGapTrial y - Real.log (erfcMills y) -
          Real.log (1 + (1 / y ^ 2) *
            (1 + asymV (erfc y) / 2 - inverfcGapTrial y)) / 2| :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖y ^ 6 * (inverfcGapTrial y - Real.log (erfcMills y) -
          Real.log (1 + (1 + asymV (erfc y) / 2 - inverfcGapTrial y) / y ^ 2) / 2)‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ y ^ 6)]
      congr 2
      congr 2
      ring

-- no-dlmf: algebraic core of the 7.17.3 transfer (`a₂·G` in closed form)
/-- With `g = (p - 1 - a₂u²)/u²` the two-term normalized error and
`d = (S - 2a₂u - 2a₃u² - (2a₄+a₂²)u³)/u³` the gap remainder (`u S = p² - 1`),

`a₂ g = a₂a₃u + a₂(2a₄+a₂²)u²/2 + a₂u²d/2 - (a₂u²g²/2 + a₂²u²g + a₂³u²/2)`.

Every term on the right is a `v`-polynomial times `u` or `u²`, times something tending to
`0`; this is what makes `a₂ g → 0` even though `a₂ → ∞`. -/
theorem gap_transfer_identity {u p g d a₂ a₃ a₄ : ℝ} (hu : u ≠ 0)
    (hg : g = (p - 1 - a₂ * u ^ 2) / u ^ 2)
    (hd : d = ((p ^ 2 - 1) / u
      - (2 * a₂ * u + 2 * a₃ * u ^ 2 + (2 * a₄ + a₂ ^ 2) * u ^ 3)) / u ^ 3) :
    a₂ * g = a₂ * a₃ * u + a₂ * (2 * a₄ + a₂ ^ 2) * u ^ 2 / 2 + a₂ * u ^ 2 * d / 2
      - (a₂ * u ^ 2 * g ^ 2 / 2 + a₂ ^ 2 * u ^ 2 * g + a₂ ^ 3 * u ^ 2 / 2) := by
  subst hg hd; field_simp; ring

-- no-dlmf: algebraic core of the 7.17.3 transfer (the display in terms of `d`, `g`)
/-- `(p - 1 - a₂u² - a₃u³ - a₄u⁴)/u⁴ = d/2 - g²/2 - a₂g`, the exact form of
`p - 1 = ½(p²-1) - ½(p-1)²`. -/
theorem gap_transfer_identity2 {u p g d a₂ a₃ a₄ : ℝ} (hu : u ≠ 0)
    (hg : g = (p - 1 - a₂ * u ^ 2) / u ^ 2)
    (hd : d = ((p ^ 2 - 1) / u
      - (2 * a₂ * u + 2 * a₃ * u ^ 2 + (2 * a₄ + a₂ ^ 2) * u ^ 3)) / u ^ 3) :
    (p - 1 - (a₂ * u ^ 2 + a₃ * u ^ 3 + a₄ * u ^ 4)) / u ^ 4
      = d / 2 - g ^ 2 / 2 - a₂ * g := by
  subst hg hd; field_simp; ring

-- no-dlmf: support lemma for 7.17.3
/-- `S y = ((y √u)² - 1)/u` for `u = asymU (erfc y) > 0`. -/
theorem inverfcAuxS_eq_div {y : ℝ} (hU : 0 < asymU (erfc y)) :
    inverfcAuxS y = ((y * Real.sqrt (asymU (erfc y))) ^ 2 - 1) / asymU (erfc y) := by
  have hr2 : Real.sqrt (asymU (erfc y)) ^ 2 = asymU (erfc y) := Real.sq_sqrt hU.le
  unfold inverfcAuxS
  rw [mul_pow, hr2]
  field_simp

-- no-dlmf: exact conversion of the cubic inversion residual from y⁻² to u
private lemma gap_u_conversion_algebra {a b c s x u r e : ℝ} (hu : u ≠ 0)
    (hxr : x = u*r) (hrr : (1 + u*s)*r = 1)
    (he : s = a*x+b*x^2+c*x^3+x^3*e) :
    (s - a*u - b*u^2 - (c-a^2)*u^3)/u^3 =
      e*r^3 + (a^2*u*s-b*s)*r*(1+r) - a*b*x*r^2 - a*c*x^2*r^2
        - a*x^2*e*r^2 - c*u*s*r*(r^2+r+1) := by
  subst x
  field_simp
  linear_combination (1 - a*u^2*r) * he +
    (a*u + b*u^2*(r+1) + c*u^3*(r^2+r+1) - a^2*u^3*(r+1)) * hrr
open Filter Topology
-- no-dlmf: asymptotic conversion of the cubic inversion residual from y⁻² to u
private lemma tendsto_gap_u_conversion {a b c s x u r e : ℝ → ℝ}
    (hids : ∀ᶠ y in atTop, u y ≠ 0 ∧ x y = u y * r y ∧
      (1 + u y * s y) * r y = 1 ∧
      s y = a y*x y + b y*(x y)^2+c y*(x y)^3+(x y)^3*e y)
    (hE : Tendsto e atTop (𝓝 0)) (hR : Tendsto r atTop (𝓝 1))
    (hS : Tendsto s atTop (𝓝 0))
    (hA2u : Tendsto (fun y => (a y)^2*u y) atTop (𝓝 0))
    (hBS : Tendsto (fun y => b y*s y) atTop (𝓝 0))
    (hABx : Tendsto (fun y => a y*b y*x y) atTop (𝓝 0))
    (hACx2 : Tendsto (fun y => a y*c y*(x y)^2) atTop (𝓝 0))
    (hAx2 : Tendsto (fun y => a y*(x y)^2) atTop (𝓝 0))
    (hCu : Tendsto (fun y => c y*u y) atTop (𝓝 0)) :
    Tendsto (fun y => (s y-a y*u y-b y*(u y)^2-(c y-(a y)^2)*(u y)^3)/(u y)^3)
      atTop (𝓝 0) := by
  have ht1 := hE.mul (hR.pow 3)
  have ht2 := ((hA2u.mul hS).sub hBS).mul hR |>.mul ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hR)
  have ht3 := hABx.mul (hR.pow 2)
  have ht4 := hACx2.mul (hR.pow 2)
  have ht5 := (hAx2.mul hE).mul (hR.pow 2)
  have ht6 := ((hCu.mul hS).mul hR).mul (((hR.pow 2).add hR).add (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)))
  have hsum := (((((ht1.add ht2).sub ht3).sub ht4).sub ht5).sub ht6)
  norm_num at hsum
  refine hsum.congr' ?_
  filter_upwards [hids] with y hy
  exact (gap_u_conversion_algebra hy.1 hy.2.1 hy.2.2.1 hy.2.2.2).symm

-- no-dlmf: conversion of the cubic trial approximation into the DLMF inversion gap
private theorem inverfc_gap_expansion_of_trial
    (hTrial : Tendsto (fun y : ℝ => y ^ 6 * (inverfcAuxS y - inverfcGapTrial y))
      atTop (𝓝 0)) :
    Tendsto (fun y : ℝ =>
        (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
          / (asymU (erfc y)) ^ 3) atTop (𝓝 0) := by
  let v : ℝ → ℝ := fun y => asymV (erfc y)
  let x : ℝ → ℝ := fun y => 1 / y ^ 2
  let u : ℝ → ℝ := fun y => asymU (erfc y)
  let a : ℝ → ℝ := fun y => gapTrialA.eval (v y)
  let b : ℝ → ℝ := fun y => gapTrialD.eval (v y)
  let c : ℝ → ℝ := fun y => gapTrialC.eval (v y)
  let e : ℝ → ℝ := fun y => y ^ 6 * (inverfcAuxS y - inverfcGapTrial y)
  let r : ℝ → ℝ := fun y => x y / u y
  have hE : Tendsto e atTop (𝓝 0) := hTrial
  have hx : Tendsto x atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (tendsto_pow_atTop two_ne_zero) 1
  have hR : Tendsto r atTop (𝓝 1) := by
    have h := tendsto_sq_mul_asymU.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simp only [inv_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_asymU_pos_atTop] with y hy hu
    dsimp [r, x, u]
    field_simp
  have hp (p : Polynomial ℝ) : Tendsto (fun y => p.eval (v y) * x y) atTop (𝓝 0) := by
    simpa [v, x, div_eq_mul_inv] using tendsto_polynomial_asymV_div_sq p
  have hpU (p : Polynomial ℝ) : Tendsto (fun y => p.eval (v y) * u y) atTop (𝓝 0) := by
    have h := (hp p).mul tendsto_sq_mul_asymU
    simp only [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    dsimp [x, u]
    field_simp
  have hA2u : Tendsto (fun y => (a y)^2*u y) atTop (𝓝 0) := by
    have h := hpU (gapTrialA * gapTrialA)
    exact h.congr fun y => by simp only [Polynomial.eval_mul]; dsimp [a]; ring
  have hABx : Tendsto (fun y => a y*b y*x y) atTop (𝓝 0) := by
    simpa [a, b, Polynomial.eval_mul] using hp (gapTrialA * gapTrialD)
  have hACx2 : Tendsto (fun y => a y*c y*(x y)^2) atTop (𝓝 0) := by
    have h := (hp (gapTrialA * gapTrialC)).mul hx
    norm_num at h
    exact h.congr fun y => by simp [a, c]; ring
  have hAx2 : Tendsto (fun y => a y*(x y)^2) atTop (𝓝 0) := by
    have h := (hp gapTrialA).mul hx
    norm_num at h
    exact h.congr fun y => by dsimp [a]; ring
  have hCu : Tendsto (fun y => c y*u y) atTop (𝓝 0) := hpU gapTrialC
  have hids : ∀ᶠ y in atTop, u y ≠ 0 ∧ x y = u y * r y ∧
      (1 + u y * inverfcAuxS y) * r y = 1 ∧
      inverfcAuxS y = a y*x y+b y*(x y)^2+c y*(x y)^3+(x y)^3*e y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_asymU_pos_atTop] with y hy hu
    refine ⟨hu.ne', ?_, ?_, ?_⟩
    · dsimp [r, u]; field_simp [hu.ne']
    · dsimp [r, x, u, inverfcAuxS]
      field_simp [hu.ne']
      ring
    · dsimp [a, b, c, e, x]
      rw [gapTrial_eval hy.ne']
      simp only [gapTrialQ, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.coe_evalRingHom]
      field_simp
      ring
  have hBS : Tendsto (fun y => b y*inverfcAuxS y) atTop (𝓝 0) := by
    have ht1 := hp (gapTrialA * gapTrialD)
    have ht2 := (hp (gapTrialD ^ 2)).mul hx
    have ht3 := (hp (gapTrialD * gapTrialC)).mul (hx.pow 2)
    have ht4 := ((hp gapTrialD).mul (hx.pow 2)).mul hE
    have h := ((ht1.add ht2).add ht3).add ht4
    norm_num at h
    refine h.congr' ?_
    filter_upwards [hids] with y hy
    rw [hy.2.2.2]
    dsimp [a, b, c]
    ring
  have h := tendsto_gap_u_conversion hids hE hR tendsto_inverfcAuxS_zero hA2u hBS hABx hACx2 hAx2 hCu
  refine h.congr fun y => ?_
  dsimp [a, b, c, u, v]
  rw [erf_7_17_4_a2, erf_7_17_4_a3, erf_7_17_4_a4]
  simp only [gapTrialA, gapTrialD, gapTrialC, gapTrialB, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  ring

/-- The three-term expansion of the inversion gap
`S y = y² - u⁻¹`, with `u = asymU (erfc y)`:

`S = 2a₂ u + 2a₃ u² + (2a₄ + a₂²) u³ + o(u³)` as `y → ∞`.

The cubic Mills-factor and logarithmic Taylor estimates yield a trial expansion
in `y⁻²`.  Stability of the implicit logarithmic equation proves its error bound;
an exact change of variables transfers it to `u`. -/
-- no-dlmf: analytic inversion core of DLMF 7.17.3
theorem inverfc_gap_expansion :
    Tendsto (fun y : ℝ =>
        (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
          / (asymU (erfc y)) ^ 3) atTop (𝓝 0) := by
  exact inverfc_gap_expansion_of_trial tendsto_six_mul_inverfcGapTrial_error

-- no-dlmf: transfer step for 7.17.3 — `a₂ · (two-term error) → 0`
/-- From the gap expansion, `a₂ · (p - 1 - a₂u²)/u² → 0` (note `a₂ → ∞`, so this is a
genuine cancellation, not a product of two limits). -/
theorem tendsto_a2_mul_gapG_of_gap
    (H : Tendsto (fun y : ℝ =>
        (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
          / (asymU (erfc y)) ^ 3) atTop (𝓝 0)) :
    Tendsto (fun y : ℝ => asymA (erfc y) 2 *
        ((y * Real.sqrt (asymU (erfc y)) - 1 - asymA (erfc y) 2 * (asymU (erfc y)) ^ 2)
          / (asymU (erfc y)) ^ 2)) atTop (𝓝 0) := by
  have hG := tendsto_normalized_two_term_atTop
  have hGsq : Tendsto (fun y : ℝ =>
      ((y * Real.sqrt (asymU (erfc y)) - 1 - asymA (erfc y) 2 * (asymU (erfc y)) ^ 2)
        / (asymU (erfc y)) ^ 2) ^ 2) atTop (𝓝 0) := by
    have h := hG.pow 2
    simpa using h
  have t1 := tendsto_a2_a3_mul_asymU
  have t2 := tendsto_a2_a4_mul_asymU_sq.div_const 2
  have t3 := (tendsto_a2_mul_asymU_sq.mul H).div_const 2
  have t4 := (tendsto_a2_mul_asymU_sq.mul hGsq).div_const 2
  have t5 := tendsto_a2_sq_mul_asymU_sq.mul hG
  have t6 := tendsto_a2_cube_mul_asymU_sq.div_const 2
  have h := ((((t1.add t2).add t3).sub t4).sub t5).sub t6
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_asymU_pos_atTop] with y hU
  have hd : (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
        + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
        + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
      / (asymU (erfc y)) ^ 3
      = (((y * Real.sqrt (asymU (erfc y))) ^ 2 - 1) / asymU (erfc y)
        - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
        / (asymU (erfc y)) ^ 3 := by
    rw [inverfcAuxS_eq_div hU]
  have hid := gap_transfer_identity (u := asymU (erfc y))
    (p := y * Real.sqrt (asymU (erfc y))) (a₂ := asymA (erfc y) 2)
    (a₃ := asymA (erfc y) 3) (a₄ := asymA (erfc y) 4) hU.ne' rfl hd
  rw [hid]
  ring

-- no-dlmf: transfer step for 7.17.3 — the normalized display, in the `y` variable
/-- From the gap expansion, `(y√u - 1 - a₂u² - a₃u³ - a₄u⁴)/u⁴ → 0` as `y → ∞`. -/
theorem tendsto_normalized_four_term_atTop_of_gap
    (H : Tendsto (fun y : ℝ =>
        (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
          / (asymU (erfc y)) ^ 3) atTop (𝓝 0)) :
    Tendsto (fun y : ℝ =>
        (y * Real.sqrt (asymU (erfc y)) - 1
          - (asymA (erfc y) 2 * (asymU (erfc y)) ^ 2
              + asymA (erfc y) 3 * (asymU (erfc y)) ^ 3
              + asymA (erfc y) 4 * (asymU (erfc y)) ^ 4))
          / (asymU (erfc y)) ^ 4) atTop (𝓝 0) := by
  have hG := tendsto_normalized_two_term_atTop
  have hGsq : Tendsto (fun y : ℝ =>
      ((y * Real.sqrt (asymU (erfc y)) - 1 - asymA (erfc y) 2 * (asymU (erfc y)) ^ 2)
        / (asymU (erfc y)) ^ 2) ^ 2) atTop (𝓝 0) := by
    have h := hG.pow 2
    simpa using h
  have hA := tendsto_a2_mul_gapG_of_gap H
  have h := ((H.div_const 2).sub (hGsq.div_const 2)).sub hA
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_asymU_pos_atTop] with y hU
  have hd : (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
        + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
        + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
      / (asymU (erfc y)) ^ 3
      = (((y * Real.sqrt (asymU (erfc y))) ^ 2 - 1) / asymU (erfc y)
        - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
        / (asymU (erfc y)) ^ 3 := by
    rw [inverfcAuxS_eq_div hU]
  have hid := gap_transfer_identity2 (u := asymU (erfc y))
    (p := y * Real.sqrt (asymU (erfc y))) (a₂ := asymA (erfc y) 2)
    (a₃ := asymA (erfc y) 3) (a₄ := asymA (erfc y) 4) hU.ne' rfl hd
  rw [hid]

-- no-dlmf: normalized (`P = inverfc x · √u`) form of the full DLMF 7.17.3 display, pulled
-- back to `x → 0⁺`; the faithful surface is `erf_7_17_3_full` below
/-- `(inverfc x · √u - 1 - a₂u² - a₃u³ - a₄u⁴)/u⁴ → 0` as `x → 0⁺`. -/
theorem tendsto_normalized_four_term :
    Tendsto (fun x : ℝ =>
        (inverfc x * Real.sqrt (asymU x) - 1
          - (asymA x 2 * (asymU x) ^ 2 + asymA x 3 * (asymU x) ^ 3
              + asymA x 4 * (asymU x) ^ 4))
          / (asymU x) ^ 4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hcomp := (tendsto_normalized_four_term_atTop_of_gap
    inverfc_gap_expansion).comp tendsto_inverfc_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_mem_Ioo] with x hx
  simp only [Function.comp_apply]
  rw [inverfc_erfc_eq x hx.1 hx.2]

/-- **DLMF 7.17.3.**  Asymptotic expansion of the inverse complementary error function for
small `x`:  as `x → 0⁺`, with `u = asymU x` (7.17.5) and the coefficients
`a_k = asymA x k` (7.17.4, polynomials in `v = asymV x` of 7.17.6),

`inverfc x ∼ u^{-1/2} + a₂ u^{3/2} + a₃ u^{5/2} + a₄ u^{7/2} + ⋯`.

Stated as the Poincaré truncation at the last displayed term: the error after
`u^{-1/2} + a₂u^{3/2} + a₃u^{5/2} + a₄u^{7/2}` is `o(u^{7/2})`, which is exactly what
`∼` (DLMF's Poincaré asymptotic expansion, §2.1(iii)) asserts for a four-term display in
the scale `u^{-1/2}, u^{3/2}, u^{5/2}, u^{7/2}`.  The regime is DLMF §7.17(iii)'s own
(`x` real, `x → 0`), encoded by the filter `𝓝[>] 0`.

DLMF 7.17.3.
DAG: E-7.17.3.
Numerical: N/A
Verified: verified
-/
theorem erf_7_17_3_full :
    (fun x : ℝ => inverfc x
        - ((asymU x) ^ (-(1:ℝ)/2) + asymA x 2 * (asymU x) ^ ((3:ℝ)/2)
            + asymA x 3 * (asymU x) ^ ((5:ℝ)/2) + asymA x 4 * (asymU x) ^ ((7:ℝ)/2)))
      =o[𝓝[>] (0:ℝ)] (fun x : ℝ => (asymU x) ^ ((7:ℝ)/2)) := by
  have hzero : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ),
      (asymU x) ^ ((7:ℝ)/2) = 0 →
        inverfc x - ((asymU x) ^ (-(1:ℝ)/2) + asymA x 2 * (asymU x) ^ ((3:ℝ)/2)
            + asymA x 3 * (asymU x) ^ ((5:ℝ)/2) + asymA x 4 * (asymU x) ^ ((7:ℝ)/2)) = 0 := by
    filter_upwards [eventually_asymU_pos] with x hx hcon
    exact absurd hcon (by positivity)
  rw [Asymptotics.isLittleO_iff_tendsto' hzero]
  refine tendsto_normalized_four_term.congr' ?_
  filter_upwards [eventually_asymU_pos] with x hx
  have hr : 0 < Real.sqrt (asymU x) := Real.sqrt_pos.mpr hx
  have hsq : asymU x = Real.sqrt (asymU x) ^ 2 := (Real.sq_sqrt hx.le).symm
  rw [rpow_neg_half hx,
    show ((3:ℝ)/2) = (2 * ((1:ℕ) : ℝ) + 1) / 2 by norm_num, rpow_half_odd hx 1,
    show ((5:ℝ)/2) = (2 * ((2:ℕ) : ℝ) + 1) / 2 by norm_num, rpow_half_odd hx 2,
    show ((7:ℝ)/2) = (2 * ((3:ℕ) : ℝ) + 1) / 2 by norm_num, rpow_half_odd hx 3]
  exact (four_term_ratio hr hsq).symm

end FourTerm

end FLMF.Error
