import FLMF.Functions.Error.Ch7InverseErf
import FLMF.Functions.Error.ErfcSeries

/-!
# The four-term asymptotic expansion of `inverfc` (DLMF 7.17.3)

`FLMF/Functions/Error/Ch7InverseErf.lean` proves only the **leading term** of DLMF
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

## Status

* `inverfc_two_term_expansion` — **fully proved**: the two-term truncation
  `inverfc x - u^{-1/2} - a₂ u^{3/2} = o(u^{3/2})`.  This is new mathematics beyond
  `erf_7_17_3` (which is the one-term truncation) and is `sorry`-free.
* `erf_7_17_3_full` — the faithful four-term display.  It is derived, by **proved**
  reductions, from the single open lemma `inverfc_gap_expansion`:

  ```
  inverfc_gap_expansion            (open: S = 2a₂u + 2a₃u² + (2a₄+a₂²)u³ + o(u³))
    ↓  tendsto_a2_mul_gapG_of_gap  (proved: a₂·(two-term error) → 0; uses the v^k u^j rates)
    ↓  tendsto_normalized_four_term_atTop_of_gap   (proved: gap_transfer_identity2)
    ↓  tendsto_normalized_four_term                (proved: pull back along y = inverfc x)
    ↓  erf_7_17_3_full                             (proved: rpow ↔ √u dictionary)
  ```

  So the only remaining mathematics is the three further orders of the log-log inversion,
  isolated as a statement about `S` alone (no `√u`, no rpow, no `inverfc`).  The first
  order of that statement is proved here as `tendsto_sq_mul_inverfcAuxS_sub`.
-/

namespace FLMF.Error

open Filter Topology Asymptotics Real Set

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

/-- **The remaining analytic gap of DLMF 7.17.3**: the three-term expansion of the
inversion gap `S y = y² - u⁻¹` (`u = asymU (erfc y)`), namely

`S = 2a₂ u + 2a₃ u² + (2a₄ + a₂²) u³ + o(u³)`  as `y → ∞`,

with `a_k = asymA (erfc y) k` the DLMF 7.17.4 coefficients.  Equivalently: the log-log
asymptotic inversion of `erfc` carried three orders past the leading term.

**Open.**  The *first* order of this statement — `S = 2a₂u + o(u)`, i.e.
`y²·S - v/4 → 0` — is proved above as `tendsto_sq_mul_inverfcAuxS_sub`, from the exact
identity `inverfcAuxS_eq` (`S = ln M + ½W`) together with `y² ln (erfcMills y) → -1/2`
(the second order of the `erfc` expansion, `erfc_7_12_1 1`).  The three further orders need
the same two ingredients pushed further:

* `erfc_7_12_1 4`, giving `ln (erfcMills y)` to `O(y^{-8})`
  (`M = 1 - 1/(2y²) + 3/(4y⁴) - 15/(8y⁶) + 105/(16y⁸) + o(y^{-8})`);
* `W y = ln(1 + A y/y²)` expanded to fourth order in `A y/y²`, with `A y` re-expanded
  through `L y = y² + A y` and `1/u = L y - 1 - v/2`, so that the `y`-side quantities are
  re-expressed in the `(u, v)` variables of 7.17.5/7.17.6.

Once available, `gap_transfer_identity` / `gap_transfer_identity2` (both proved) convert it
into the DLMF display without further analysis. -/
-- no-dlmf: the open analytic core of DLMF 7.17.3 (inversion gap expansion); the faithful
-- display surface is `erf_7_17_3_full` below
theorem inverfc_gap_expansion :
    Tendsto (fun y : ℝ =>
        (inverfcAuxS y - (2 * asymA (erfc y) 2 * asymU (erfc y)
            + 2 * asymA (erfc y) 3 * (asymU (erfc y)) ^ 2
            + (2 * asymA (erfc y) 4 + (asymA (erfc y) 2) ^ 2) * (asymU (erfc y)) ^ 3))
          / (asymU (erfc y)) ^ 3) atTop (𝓝 0) := by
  sorry

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
Fidelity: tier1 n/a
Verified: verified (tier2)
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
