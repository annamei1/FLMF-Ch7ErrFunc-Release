import FLMF.Chapter7.Erf
import FLMF.Chapter7.Dawson
import FLMF.Chapter7.IntegralReps

/-!
# Inequalities for `erf`, `erfc`, and Dawson's integral (DLMF §7.8)

Statement surfaces for the bounds in DLMF §7.8, equations 7.8.1–7.8.8.

DLMF's auxiliary function, Mills' ratio
`𝖬(x) = (∫_x^∞ e^{-t²} dt)/e^{-x²} = e^{x²} ∫_x^∞ e^{-t²} dt`, is introduced here as
the definition `millsRatio` (its defining display is 7.8.1, surfaced as `erf_7_8_1`);
`millsRatio_eq_erfc` bridges it to `(√π/2) · e^{x²} · erfc(x)`, the inline form in which
7.8.2–7.8.5 are still written.
Dawson's integral is `F(x) = FLMF.dawson x = e^{-x²} ∫_0^x e^{t²} dt`, so the
DLMF middle term `e^{x²} F(x) = ∫_0^x e^{t²} dt` is written
`Real.exp (x ^ 2) * FLMF.dawson x`.

These are surfaces only: bodies are `:= by sorry`.
-/

namespace FLMF.Error

open Real

-- no-dlmf: introduces the object DEFINED by DLMF 7.8.1 (Mills' ratio `𝖬`);
-- the display itself is surfaced at `erf_7_8_1` below
/-- Mills' ratio `𝖬(x) = (∫_x^∞ e^{-t²} dt) / e^{-x²}` (DLMF 7.8.1).

DLMF's first member is taken as the definiens; the second member
(`e^{x²} ∫_x^∞ e^{-t²} dt`) is the content of `erf_7_8_1`, and the bridge to
FLMF's `erfc` — used by 7.8.2–7.8.5 — is `millsRatio_eq_erfc`. -/
noncomputable def millsRatio (x : ℝ) : ℝ :=
  (∫ t in Set.Ioi x, Real.exp (-t ^ 2)) / Real.exp (-x ^ 2)

/-- Mills' ratio `𝖬(x) = (∫_x^∞ e^{-t²} dt)/e^{-x²} = e^{x²} ∫_x^∞ e^{-t²} dt`
(DLMF 7.8.1).

DLMF 7.8.1.
DAG: E-7.8.1.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_1 (x : ℝ) :
    millsRatio x = (∫ t in Set.Ioi x, Real.exp (-t ^ 2)) / Real.exp (-x ^ 2) ∧
      millsRatio x = Real.exp (x ^ 2) * ∫ t in Set.Ioi x, Real.exp (-t ^ 2) := by
  refine ⟨rfl, ?_⟩
  unfold millsRatio
  rw [Real.exp_neg, div_inv_eq_mul, mul_comm]

-- no-dlmf: bridge from the §7.8 definition to FLMF's erfc (used by 7.8.2–7.8.5)
/-- `𝖬(x) = (√π/2) e^{x²} erfc(x)` — the bridge from Mills' ratio to FLMF's
complementary error function. -/
theorem millsRatio_eq_erfc (x : ℝ) :
    millsRatio x = (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x := by
  have h := FLMF.Error.integral_Ioi_gaussian_scaled_erfc (a := 1) one_pos x
  simp only [neg_mul, one_mul, Real.sqrt_one, div_one] at h
  unfold millsRatio
  rw [h, Real.exp_neg, div_inv_eq_mul]
  ring

/-- `erf x < 1` for every real `x` (strictly monotone with limit `1`); support for 7.8.2. -/
private lemma _kit_erf_lt_one (x : ℝ) : erf x < 1 := by
  have hmono : StrictMono erf := by
    apply strictMono_of_deriv_pos
    intro y
    rw [(hasDerivAt_erf y).deriv]
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have h1 : erf x < erf (x + 1) := hmono (by linarith)
  exact lt_of_lt_of_le h1 (erf_le_one _)

/-- `erfc x > 0` for every real `x`; support for 7.8.2. -/
private lemma _kit_erfc_pos (x : ℝ) : 0 < erfc x := by
  have := _kit_erf_lt_one x
  simp only [erfc]
  linarith

/-- `erfc` has derivative `-(2/√π) e^{-x²}` (from `hasDerivAt_erf`); support for 7.8.2. -/
private lemma _kit_hasDerivAt_erfc (x : ℝ) :
    HasDerivAt erfc (-((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))) x :=
  (hasDerivAt_erf x).const_sub 1

/-- `e^{-y²} → 0` as `y → ∞`; support for 7.8.2. -/
private lemma _kit_exp_neg_sq_tendsto :
    Filter.Tendsto (fun y : ℝ => Real.exp (-y ^ 2)) Filter.atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h : Filter.Tendsto (fun y : ℝ => y ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (two_ne_zero)
  exact Filter.tendsto_neg_atBot_iff.mpr h

/-- `(√π/2)·erfc y → 0` as `y → ∞`; support for 7.8.2. -/
private lemma _kit_scaled_erfc_tendsto :
    Filter.Tendsto (fun y : ℝ => Real.sqrt Real.pi / 2 * erfc y) Filter.atTop (nhds 0) := by
  have h := erfc_tendsto_zero.const_mul (Real.sqrt Real.pi / 2)
  simpa using h

/-- Comparison core for the Mills-ratio bounds of 7.8.2: a function strictly
increasing on `[x₀,∞)` (via a positive derivative) with limit `0` at `+∞` is
negative at `x₀`. -/
private lemma _kit_neg_of_deriv_pos_tendsto_zero {D D' : ℝ → ℝ} {x₀ : ℝ}
    (hd : ∀ y, x₀ ≤ y → HasDerivAt D (D' y) y)
    (hpos : ∀ y, x₀ ≤ y → 0 < D' y)
    (hlim : Filter.Tendsto D Filter.atTop (nhds 0)) : D x₀ < 0 := by
  have hmono : StrictMonoOn D (Set.Ici x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y hy.le).deriv]
      exact hpos y hy.le
  have h1 : D x₀ < D (x₀ + 1) :=
    hmono Set.self_mem_Ici (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have h2 : D (x₀ + 1) ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop (x₀ + 1)] with y hy
    exact (hmono.monotoneOn (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hy)
  linarith

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- The Komatsu lower bound `1/(x+√(x²+2)) < 𝖬(x)` for `x ≥ 0` (DLMF 7.8.2, first
inequality): with `h(y) = 1/(y+√(y²+2)) = (√(y²+2)−y)/2` one has
`h' − 2yh + 1 = (s(2y²+1) − y(2y²+3))/(2s) > 0` (`s = √(y²+2)`; the two squares
differ by `2`), so `D = e^{-y²}h − (√π/2)erfc` is strictly increasing with limit
`0` at `+∞`, hence `D(x) < 0`, i.e. `h(x) < 𝖬(x)`. -/
private lemma _kit_mills_lower (x : ℝ) (hx : 0 ≤ x) :
    1 / (x + Real.sqrt (x ^ 2 + 2))
      < (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set D : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * ((Real.sqrt (y ^ 2 + 2) - y) / 2) - Real.sqrt Real.pi / 2 * erfc y
    with hDdef
  set D' : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * ((y / Real.sqrt (y ^ 2 + 2) - 1) / 2
      - 2 * y * ((Real.sqrt (y ^ 2 + 2) - y) / 2) + 1) with hD'def
  have hsqrt : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 2))
      (y / Real.sqrt (y ^ 2 + 2)) y := by
    intro y
    have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).add_const 2
    have h := hinner.sqrt (by positivity)
    convert h using 1
    ring
  have hexpD : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have hinner : HasDerivAt (fun y : ℝ => -y ^ 2) (-2 * y) y := by
      have := (hasDerivAt_pow 2 y).neg
      convert this using 1
      ring
    exact hinner.exp
  have hd : ∀ y : ℝ, HasDerivAt D (D' y) y := by
    intro y
    have hh : HasDerivAt (fun y : ℝ => (Real.sqrt (y ^ 2 + 2) - y) / 2)
        ((y / Real.sqrt (y ^ 2 + 2) - 1) / 2) y :=
      ((hsqrt y).sub (hasDerivAt_id' (𝕜 := ℝ) (x := y))).div_const 2
    have h := ((hexpD y).mul hh).sub
      ((_kit_hasDerivAt_erfc y).const_mul (Real.sqrt Real.pi / 2))
    convert h using 1
    simp only [hD'def]
    field_simp
    ring
  have hpos : ∀ y : ℝ, x ≤ y → 0 < D' y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans hx hy
    simp only [hD'def]
    set s := Real.sqrt (y ^ 2 + 2) with hsdef
    have hs2 : s ^ 2 = y ^ 2 + 2 := Real.sq_sqrt (by positivity)
    have hspos : (0:ℝ) < s := Real.sqrt_pos.mpr (by positivity)
    have key : y * (2 * y ^ 2 + 3) < s * (2 * y ^ 2 + 1) := by
      apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
      rw [mul_pow, mul_pow, hs2]
      nlinarith [sq_nonneg y]
    have hEeq : (y / s - 1) / 2 - 2 * y * ((s - y) / 2) + 1
        = (s * (2 * y ^ 2 + 1) - y * (2 * y ^ 2 + 3)) / (2 * s) := by
      field_simp
      ring_nf
      nlinarith [hs2]
    have hEpos : 0 < (y / s - 1) / 2 - 2 * y * ((s - y) / 2) + 1 := by
      rw [hEeq]
      exact div_pos (by linarith) (by linarith)
    exact mul_pos (Real.exp_pos _) hEpos
  have hlim : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun y : ℝ => Real.exp (-y ^ 2) * ((Real.sqrt (y ^ 2 + 2) - y) / 2))
        Filter.atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        _kit_exp_neg_sq_tendsto
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have : y ≤ Real.sqrt (y ^ 2 + 2) := by
          calc y ≤ |y| := le_abs_self y
          _ = Real.sqrt (y ^ 2) := (Real.sqrt_sq_eq_abs y).symm
          _ ≤ Real.sqrt (y ^ 2 + 2) := Real.sqrt_le_sqrt (by linarith)
        positivity
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have hle : Real.sqrt (y ^ 2 + 2) ≤ y + 2 := by
          rw [show y + 2 = Real.sqrt ((y + 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
          apply Real.sqrt_le_sqrt
          nlinarith
        have h2 : (Real.sqrt (y ^ 2 + 2) - y) / 2 ≤ 1 := by linarith
        have h3 : (0:ℝ) < Real.exp (-y ^ 2) := Real.exp_pos _
        nlinarith [h3, h2, Real.exp_pos (-y ^ 2)]
    have := h1.sub _kit_scaled_erfc_tendsto
    simpa [hDdef] using this
  have hD : D x < 0 :=
    _kit_neg_of_deriv_pos_tendsto_zero (fun y _ => hd y) hpos hlim
  simp only [hDdef] at hD
  have hepos : (0:ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
  have hee : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hstep : (Real.sqrt (x ^ 2 + 2) - x) / 2
      < Real.sqrt Real.pi / 2 * Real.exp (x ^ 2) * erfc x := by
    have h4 : Real.exp (x ^ 2) * (Real.exp (-x ^ 2) * ((Real.sqrt (x ^ 2 + 2) - x) / 2))
        < Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x) :=
      mul_lt_mul_of_pos_left (by linarith) hepos
    have h5 : Real.exp (x ^ 2) * (Real.exp (-x ^ 2) * ((Real.sqrt (x ^ 2 + 2) - x) / 2))
        = (Real.sqrt (x ^ 2 + 2) - x) / 2 := by
      rw [← mul_assoc, hee, one_mul]
    have h6 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
        = Real.sqrt Real.pi / 2 * Real.exp (x ^ 2) * erfc x := by ring
    linarith
  have hs2 : Real.sqrt (x ^ 2 + 2) ^ 2 = x ^ 2 + 2 := Real.sq_sqrt (by positivity)
  have hspos : (0:ℝ) < Real.sqrt (x ^ 2 + 2) := Real.sqrt_pos.mpr (by positivity)
  have hxs : (0:ℝ) < x + Real.sqrt (x ^ 2 + 2) := by linarith
  have hLHS : 1 / (x + Real.sqrt (x ^ 2 + 2)) = (Real.sqrt (x ^ 2 + 2) - x) / 2 := by
    rw [div_eq_div_iff hxs.ne' (by norm_num)]
    linear_combination -hs2
  rw [hLHS]
  exact hstep

/-- The 7.8.4-strength bound `𝖬(x) < 2/(3x+√(x²+4))` for `x > -√2/2`, by the same
differential comparison in the opposite direction (`h₄' − 2yh₄ + 1 < 0` from
`y(y²+3) < (y²+1)√(y²+4)`; the two squares differ by `4`, and for `y < 0` the
inequality is trivial); the denominator stays positive on the extended domain
because `y² < 1/2` gives `9y² < y²+4`. Input to the Pollak upper bound of 7.8.2
and the surface of 7.8.4. -/
private lemma _kit_mills_784 (x : ℝ) (hx : -(Real.sqrt 2 / 2) < x) :
    (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      < 2 * (3 * x + Real.sqrt (x ^ 2 + 4))⁻¹ := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hneg : -(Real.sqrt 2 / 2) < (0:ℝ) := neg_lt_zero.mpr (by positivity)
  have hs4pos : ∀ y : ℝ, (0:ℝ) < Real.sqrt (y ^ 2 + 4) :=
    fun y => Real.sqrt_pos.mpr (by positivity)
  have hs4ge2 : ∀ y : ℝ, (2:ℝ) ≤ Real.sqrt (y ^ 2 + 4) := by
    intro y
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hden : ∀ y : ℝ, -(Real.sqrt 2 / 2) < y → (0:ℝ) < 3 * y + Real.sqrt (y ^ 2 + 4) := by
    intro y hy
    rcases le_total 0 y with hy0 | hy0
    · have := hs4ge2 y
      linarith
    · have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hy2 : y ^ 2 < 1 / 2 := by
        have h1 : (0:ℝ) < Real.sqrt 2 / 2 + y := by linarith
        have h2 : (0:ℝ) < Real.sqrt 2 / 2 - y := by
          have h2' : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          nlinarith
        nlinarith [mul_pos h1 h2]
      have h9 : (-(3 * y)) ^ 2 < y ^ 2 + 4 := by nlinarith
      have h3 : -(3 * y) < Real.sqrt (y ^ 2 + 4) :=
        (Real.lt_sqrt (by linarith)).mpr h9
      linarith
  have hsqrt4 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 4))
      (y / Real.sqrt (y ^ 2 + 4)) y := by
    intro y
    have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + 4) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).add_const 4
    have h := hinner.sqrt (by positivity)
    convert h using 1
    ring
  have hexpD : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have hinner : HasDerivAt (fun y : ℝ => -y ^ 2) (-2 * y) y := by
      have := (hasDerivAt_pow 2 y).neg
      convert this using 1
      ring
    exact hinner.exp
  set D : ℝ → ℝ := fun y =>
    Real.sqrt Real.pi / 2 * erfc y
      - Real.exp (-y ^ 2) * (2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹) with hDdef
  set D' : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * (2 * ((3 + y / Real.sqrt (y ^ 2 + 4)) / (3 * y + Real.sqrt (y ^ 2 + 4)) ^ 2)
      + 2 * y * (2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹) - 1) with hD'def
  have hd : ∀ y : ℝ, x ≤ y → HasDerivAt D (D' y) y := by
    intro y hy
    have hy' : -(Real.sqrt 2 / 2) < y := lt_of_lt_of_le hx hy
    have hlin : HasDerivAt (fun y : ℝ => 3 * y + Real.sqrt (y ^ 2 + 4))
        (3 * 1 + y / Real.sqrt (y ^ 2 + 4)) y :=
      ((hasDerivAt_id' (𝕜 := ℝ) (x := y)).const_mul 3).add (hsqrt4 y)
    have hinv := (hlin.inv (hden y hy').ne').const_mul 2
    have h := ((_kit_hasDerivAt_erfc y).const_mul (Real.sqrt Real.pi / 2)).sub
      ((hexpD y).mul hinv)
    convert h using 1
    simp only [hD'def, Pi.inv_apply]
    field_simp
    ring
  have hpos : ∀ y : ℝ, x ≤ y → 0 < D' y := by
    intro y hy
    have hy' : -(Real.sqrt 2 / 2) < y := lt_of_lt_of_le hx hy
    simp only [hD'def]
    set s := Real.sqrt (y ^ 2 + 4) with hsdef
    have hs2 : s ^ 2 = y ^ 2 + 4 := Real.sq_sqrt (by positivity)
    have hspos : (0:ℝ) < s := hs4pos y
    have hdpos : (0:ℝ) < 3 * y + s := hden y hy'
    have key : y * (y ^ 2 + 3) < (y ^ 2 + 1) * s := by
      apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
      rw [mul_pow, mul_pow, hs2]
      nlinarith [sq_nonneg y]
    have hEeq : 2 * ((3 + y / s) / (3 * y + s) ^ 2) + 2 * y * (2 * (3 * y + s)⁻¹) - 1
        = 2 * ((y ^ 2 + 1) * s - y * (y ^ 2 + 3)) / (s * (3 * y + s) ^ 2) := by
      field_simp
      ring_nf
      nlinarith [hs2]
    rw [hEeq]
    have hnum : (0:ℝ) < 2 * ((y ^ 2 + 1) * s - y * (y ^ 2 + 3)) := by linarith
    exact mul_pos (Real.exp_pos _) (div_pos hnum (mul_pos hspos (pow_pos hdpos 2)))
  have hlim : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ =>
        Real.exp (-y ^ 2) * (2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹)) Filter.atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        _kit_exp_neg_sq_tendsto
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have := (hden y (lt_of_lt_of_le hneg hy)).le
        positivity
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have hb : 2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one (hden y (lt_of_lt_of_le hneg hy))]
          have := hs4ge2 y
          linarith
        have h3 : (0:ℝ) < Real.exp (-y ^ 2) := Real.exp_pos _
        have h4 : (0:ℝ) ≤ 2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹ := by
          have := (hden y (lt_of_lt_of_le hneg hy)).le
          positivity
        nlinarith
    have := _kit_scaled_erfc_tendsto.sub h1
    simpa [hDdef] using this
  have hD : D x < 0 := _kit_neg_of_deriv_pos_tendsto_zero hd hpos hlim
  simp only [hDdef] at hD
  have hepos : (0:ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
  have hee : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
      < Real.exp (x ^ 2) * (Real.exp (-x ^ 2) * (2 * (3 * x + Real.sqrt (x ^ 2 + 4))⁻¹)) :=
    mul_lt_mul_of_pos_left (by linarith) hepos
  have h5 : Real.exp (x ^ 2) * (Real.exp (-x ^ 2) * (2 * (3 * x + Real.sqrt (x ^ 2 + 4))⁻¹))
      = 2 * (3 * x + Real.sqrt (x ^ 2 + 4))⁻¹ := by
    rw [← mul_assoc, hee, one_mul]
  have h6 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
      = Real.sqrt Real.pi / 2 * Real.exp (x ^ 2) * erfc x := by ring
  linarith

-- no-dlmf: private kit lemma; DLMF citation is context, not an equation surface
/-- The Pollak upper bound `𝖬(x) ≤ 1/(x+√(x²+4/π))` for `x ≥ 0` (DLMF 7.8.2,
second inequality): `ψ(y) = (1/𝖬(y) − y)² − y²` has
`ψ' = 2((2y²−1)𝖬² − 3y𝖬 + 1)/𝖬³ > 0`, because the quadratic factors as
`(1/4)(2 − 𝖬(3y+s₄))(2 − 𝖬(3y−s₄))` with `s₄ = √(y²+4)` and both factors are
positive by `_kit_mills_784`; with `ψ(0) = 4/π` this gives
`(1/𝖬(x) − x)² ≥ x² + 4/π`, which rearranges to the bound. -/
private lemma _kit_mills_upper (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      ≤ 1 / (x + Real.sqrt (x ^ 2 + 4 / Real.pi)) := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs4pos : ∀ y : ℝ, (0:ℝ) < Real.sqrt (y ^ 2 + 4) :=
    fun y => Real.sqrt_pos.mpr (by positivity)
  have hs4ge2 : ∀ y : ℝ, (2:ℝ) ≤ Real.sqrt (y ^ 2 + 4) := by
    intro y
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hden : ∀ y : ℝ, 0 ≤ y → (0:ℝ) < 3 * y + Real.sqrt (y ^ 2 + 4) := by
    intro y hy
    have := hs4ge2 y
    linarith
  set M : ℝ → ℝ := fun y => Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y with hMdef
  have hMpos : ∀ y : ℝ, 0 < M y := by
    intro y
    have := _kit_erfc_pos y
    have := Real.exp_pos (y ^ 2)
    simp only [hMdef]
    positivity
  have hM : ∀ y : ℝ, HasDerivAt M (2 * y * M y - 1) y := by
    intro y
    have h2y : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have hexp2 : HasDerivAt (fun y : ℝ => Real.exp (y ^ 2)) (Real.exp (y ^ 2) * (2 * y)) y :=
      h2y.exp
    have h := (hexp2.const_mul (Real.sqrt Real.pi / 2)).mul (_kit_hasDerivAt_erfc y)
    convert h using 1
    simp only [hMdef]
    have hee : Real.exp (y ^ 2) * Real.exp (-y ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    field_simp
    ring_nf
    nlinarith [hee, sq_nonneg (Real.sqrt Real.pi)]
  set ψ : ℝ → ℝ := fun y => ((M y)⁻¹ - y) ^ 2 - y ^ 2 with hψdef
  have hψd : ∀ y : ℝ, HasDerivAt ψ
      (2 * ((M y)⁻¹ - y) * (-(2 * y * M y - 1) / (M y) ^ 2 - 1) - 2 * y) y := by
    intro y
    have hQ : HasDerivAt (fun y : ℝ => (M y)⁻¹ - y)
        (-(2 * y * M y - 1) / (M y) ^ 2 - 1) y :=
      ((hM y).inv (hMpos y).ne').sub (hasDerivAt_id' (𝕜 := ℝ) (x := y))
    have h2y' : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h := (hQ.pow 2).sub h2y'
    convert h using 1
    push_cast
    ring
  have hψpos : ∀ y : ℝ, 0 ≤ y →
      0 < 2 * ((M y)⁻¹ - y) * (-(2 * y * M y - 1) / (M y) ^ 2 - 1) - 2 * y := by
    intro y hy
    have hm : 0 < M y := hMpos y
    have hspos := hs4pos y
    have hs2 : Real.sqrt (y ^ 2 + 4) ^ 2 = y ^ 2 + 4 := Real.sq_sqrt (by positivity)
    have hdpos : (0:ℝ) < 3 * y + Real.sqrt (y ^ 2 + 4) := hden y hy
    have h4y : M y < 2 * (3 * y + Real.sqrt (y ^ 2 + 4))⁻¹ :=
      _kit_mills_784 y (lt_of_lt_of_le (neg_lt_zero.mpr (by positivity)) hy)
    have hA : M y * (3 * y + Real.sqrt (y ^ 2 + 4)) < 2 := by
      rw [← div_eq_mul_inv] at h4y
      exact (lt_div_iff₀ hdpos).mp h4y
    have hB2 : (0:ℝ) < 2 - M y * (3 * y + Real.sqrt (y ^ 2 + 4)) := by linarith
    have hms : (0:ℝ) < M y * Real.sqrt (y ^ 2 + 4) := mul_pos hm hspos
    have hB' : (0:ℝ) < 2 - M y * (3 * y + Real.sqrt (y ^ 2 + 4))
        + 2 * (M y * Real.sqrt (y ^ 2 + 4)) := by linarith
    have hq : 0 < (2 * y ^ 2 - 1) * (M y) ^ 2 - 3 * y * (M y) + 1 := by
      nlinarith [mul_pos hB2 hB', hs2, sq_nonneg (M y)]
    have hψeq : 2 * ((M y)⁻¹ - y) * (-(2 * y * M y - 1) / (M y) ^ 2 - 1) - 2 * y
        = 2 * ((2 * y ^ 2 - 1) * (M y) ^ 2 - 3 * y * (M y) + 1) / (M y) ^ 3 := by
      field_simp
      ring
    rw [hψeq]
    exact div_pos (by linarith) (pow_pos hm 3)
  have hψmono : StrictMonoOn ψ (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y hy => (hψd y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hψd y).deriv]
      exact hψpos y hy.le
  have hψ0 : ψ 0 = 4 / Real.pi := by
    have h1 : ψ 0 = ((Real.sqrt Real.pi / 2)⁻¹) ^ 2 := by
      simp [hψdef, hMdef]
    have h2 : (Real.sqrt Real.pi / 2) ^ 2 = Real.pi / 4 := by
      rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
      norm_num
    rw [h1, inv_pow, h2, inv_div]
  have hψx : 4 / Real.pi ≤ ψ x := by
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h, hψ0]
    · have := hψmono Set.self_mem_Ici (Set.mem_Ici.mpr hx) h
      rw [hψ0] at this
      linarith
  have hm : 0 < M x := hMpos x
  have hspos := hs4pos x
  have hdpos : (0:ℝ) < 3 * x + Real.sqrt (x ^ 2 + 4) := hden x hx
  have h4x : M x < 2 * (3 * x + Real.sqrt (x ^ 2 + 4))⁻¹ :=
    _kit_mills_784 x (lt_of_lt_of_le (neg_lt_zero.mpr (by positivity)) hx)
  have hA : M x * (3 * x + Real.sqrt (x ^ 2 + 4)) < 2 := by
    rw [← div_eq_mul_inv] at h4x
    exact (lt_div_iff₀ hdpos).mp h4x
  have hxm : x * M x < 1 := by
    have hs2ge := hs4ge2 x
    nlinarith [mul_pos hm hspos]
  have hQpos : 0 < (M x)⁻¹ - x := by
    have h1 : (M x)⁻¹ - x = (1 - x * M x) / (M x) := by
      field_simp
    rw [h1]
    exact div_pos (by linarith) hm
  have hQ2 : x ^ 2 + 4 / Real.pi ≤ ((M x)⁻¹ - x) ^ 2 := by
    have h5 := hψx
    simp only [hψdef] at h5
    linarith
  have hsqle : Real.sqrt (x ^ 2 + 4 / Real.pi) ≤ (M x)⁻¹ - x := by
    have h2 := Real.sqrt_le_sqrt hQ2
    rwa [Real.sqrt_sq hQpos.le] at h2
  have hden2 : (0:ℝ) < x + Real.sqrt (x ^ 2 + 4 / Real.pi) := by
    have : (0:ℝ) < Real.sqrt (x ^ 2 + 4 / Real.pi) :=
      Real.sqrt_pos.mpr (by positivity)
    linarith
  rw [le_div_iff₀ hden2]
  calc M x * (x + Real.sqrt (x ^ 2 + 4 / Real.pi))
      ≤ M x * ((M x)⁻¹) := by
        apply mul_le_mul_of_nonneg_left (by linarith) hm.le
    _ = 1 := mul_inv_cancel₀ hm.ne'

/-- Two-sided bound on `𝖬(x)` for `x ≥ 0` (DLMF 7.8.2).

DLMF 7.8.2.
DAG: E-7.8.2.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_2 (x : ℝ) (hx : 0 ≤ x) :
    1 / (x + Real.sqrt (x ^ 2 + 2))
        < (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      ∧ (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
        ≤ 1 / (x + Real.sqrt (x ^ 2 + 4 / Real.pi)) := by
  exact ⟨_kit_mills_lower x hx, _kit_mills_upper x hx⟩

-- no-dlmf: private kit lemma; the Mills-ratio derivative 𝖬' = 2y𝖬 − 1 shared by 7.8.3/7.8.5
/-- The DLMF auxiliary function `𝖬(y) = (√π/2)e^{y²}erfc y` satisfies
`𝖬'(y) = 2y·𝖬(y) − 1` (differentiate the product and use `erfc' = −(2/√π)e^{−y²}`). -/
private lemma _kit_M_hasDerivAt (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt Real.pi / 2 * Real.exp (t ^ 2) * erfc t)
      (2 * y * (Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y) - 1) y := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2y : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have hexp2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (Real.exp (y ^ 2) * (2 * y)) y :=
    h2y.exp
  have h := (hexp2.const_mul (Real.sqrt Real.pi / 2)).mul (_kit_hasDerivAt_erfc y)
  convert h using 1
  have hee : Real.exp (y ^ 2) * Real.exp (-y ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  field_simp
  ring_nf
  nlinarith [hee, sq_nonneg (Real.sqrt Real.pi)]

/-- Two-sided bound on `𝖬(x)` for `x ≥ 0` (DLMF 7.8.3):
`√π/(2√π·x + 2) ≤ 𝖬(x) ≤ 1/(x+1)`.  (Lower bound corrected 2026-06-25 from the DLMF
PDF: `√π/(2√π·x + 2)`, not `π/(2√(π x + 2))` — the source mis-placed the √ and used π
for √π.  See ERRATA.)

DLMF 7.8.3.
DAG: E-7.8.3.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_3 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt Real.pi / (2 * Real.sqrt Real.pi * x + 2)
        ≤ (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      ∧ (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
        < 1 / (x + 1) := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  constructor
  · -- lower bound via antitonicity of ψ(y) = 1/𝖬(y) − 2y
    set M : ℝ → ℝ := fun y => Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y with hMdef
    have hMpos : ∀ y : ℝ, 0 < M y := by
      intro y
      have h1 := _kit_erfc_pos y
      have h2 := Real.exp_pos (y ^ 2)
      simp only [hMdef]
      positivity
    have hψd : ∀ y : ℝ, HasDerivAt (fun t : ℝ => (M t)⁻¹ - 2 * t)
        (-(2 * y * M y - 1) / (M y) ^ 2 - 2) y := by
      intro y
      have hMd : HasDerivAt M (2 * y * M y - 1) y := _kit_M_hasDerivAt y
      have hQ := hMd.inv (hMpos y).ne'
      have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 y := by
        simpa using (hasDerivAt_id' (𝕜 := ℝ) (x := y)).const_mul 2
      exact hQ.sub h2
    have hψneg : ∀ y : ℝ, 0 ≤ y → -(2 * y * M y - 1) / (M y) ^ 2 - 2 < 0 := by
      intro y hy
      have hm := hMpos y
      have hml' : (Real.sqrt (y ^ 2 + 2) - y) / 2 < M y := by
        have hml := _kit_mills_lower y hy
        have hs2 : Real.sqrt (y ^ 2 + 2) ^ 2 = y ^ 2 + 2 := Real.sq_sqrt (by positivity)
        have hspos : (0:ℝ) < Real.sqrt (y ^ 2 + 2) := Real.sqrt_pos.mpr (by positivity)
        have hys : (0:ℝ) < y + Real.sqrt (y ^ 2 + 2) := by linarith
        have hLHS : 1 / (y + Real.sqrt (y ^ 2 + 2)) = (Real.sqrt (y ^ 2 + 2) - y) / 2 := by
          rw [div_eq_div_iff hys.ne' (by norm_num)]
          linear_combination -hs2
        rw [hLHS] at hml
        exact hml
      have hs2 : Real.sqrt (y ^ 2 + 2) ^ 2 = y ^ 2 + 2 := Real.sq_sqrt (by positivity)
      have hspos : (0:ℝ) < Real.sqrt (y ^ 2 + 2) := Real.sqrt_pos.mpr (by positivity)
      have hmy : (0:ℝ) ≤ (Real.sqrt (y ^ 2 + 2) - y) / 2 + y := by linarith
      have hkey : 1 < 2 * (M y) ^ 2 + 2 * y * M y := by
        nlinarith [mul_pos (sub_pos.mpr hml') hm,
          mul_nonneg (sub_pos.mpr hml').le hmy, hs2]
      have h2 : -(2 * y * M y - 1) / (M y) ^ 2 - 2
          = (1 - 2 * y * M y - 2 * (M y) ^ 2) / (M y) ^ 2 := by
        field_simp
        ring
      rw [h2]
      apply div_neg_of_neg_of_pos
      · linarith
      · positivity
    have hanti : StrictAntiOn (fun t : ℝ => (M t)⁻¹ - 2 * t) (Set.Ici 0) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      · exact fun y hy => (hψd y).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        rw [(hψd y).deriv]
        exact hψneg y hy.le
    have hM0 : M 0 = Real.sqrt Real.pi / 2 := by
      simp only [hMdef]
      norm_num [erfc, erf_zero]
    have hψx : (M x)⁻¹ - 2 * x ≤ (M 0)⁻¹ - 2 * 0 := by
      rcases eq_or_lt_of_le hx with h | h
      · rw [← h]
      · exact (hanti Set.self_mem_Ici (Set.mem_Ici.mpr hx) h).le
    rw [hM0] at hψx
    have hinv : (M x)⁻¹ ≤ 2 * x + 2 / Real.sqrt Real.pi := by
      have hid : (Real.sqrt Real.pi / 2)⁻¹ = 2 / Real.sqrt Real.pi := by
        rw [inv_div]
      rw [hid] at hψx
      linarith
    have hm := hMpos x
    have hpos2 : (0:ℝ) < 2 * x + 2 / Real.sqrt Real.pi := by
      have h1 : (0:ℝ) < 2 / Real.sqrt Real.pi := by positivity
      linarith
    have heq : Real.sqrt Real.pi / (2 * Real.sqrt Real.pi * x + 2)
        = 1 / (2 * x + 2 / Real.sqrt Real.pi) := by
      rw [div_eq_div_iff (by positivity) hpos2.ne']
      field_simp
    rw [heq, div_le_iff₀ hpos2]
    have h1 : 1 ≤ M x * (2 * x + 2 / Real.sqrt Real.pi) := by
      calc (1:ℝ) = M x * (M x)⁻¹ := (mul_inv_cancel₀ hm.ne').symm
        _ ≤ M x * (2 * x + 2 / Real.sqrt Real.pi) :=
            mul_le_mul_of_nonneg_left hinv hm.le
    exact h1
  · -- upper bound from the Pollak bound, since √(x²+4/π) > 1
    have hup := _kit_mills_upper x hx
    have hgt1 : (1:ℝ) < Real.sqrt (x ^ 2 + 4 / Real.pi) := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      apply Real.sqrt_lt_sqrt (by norm_num)
      have h4 : Real.pi < 4 := Real.pi_lt_four
      have h5 : (1:ℝ) < 4 / Real.pi := (one_lt_div Real.pi_pos).mpr h4
      nlinarith [sq_nonneg x]
    have hx1 : (0:ℝ) < x + 1 := by linarith
    have hlt : 1 / (x + Real.sqrt (x ^ 2 + 4 / Real.pi)) < 1 / (x + 1) := by
      apply one_div_lt_one_div_of_lt hx1
      linarith
    exact lt_of_le_of_lt hup hlt

/-- Upper bound on `𝖬(x)` for `x > -½√2` (DLMF 7.8.4).
(Domain corrected 2026-06-25 from the DLMF PDF: `x > -½√2 = -√2/2`, not `-1/(2√2)`.)

DLMF 7.8.4.
DAG: E-7.8.4.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_4 (x : ℝ) (hx : -(Real.sqrt 2 / 2) < x) :
    (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      < 2 / (3 * x + Real.sqrt (x ^ 2 + 4)) := by
  rw [div_eq_mul_inv]
  exact _kit_mills_784 x hx

-- no-dlmf: private kit lemma; DLMF 7.8.5 context, not an equation surface
/-- Lower 7.8.5-strength bound `y(2y²+5)/(4y⁴+12y²+3) < 𝖬(y)`: with `h = p/q`,
`p = y(2y²+5)`, `q = 4y⁴+12y²+3`, one has `h' − 2yh + 1 = 24/q² > 0` (the
polynomial `p'q − pq' − 2ypq + q²` collapses to the constant `24`), so
`D = e^{-y²}h − (√π/2)erfc` is strictly increasing with limit `0` at `+∞`,
hence `D(x) < 0`, i.e. `h(x) < 𝖬(x)`. -/
private lemma _kit_785_lower (x : ℝ) :
    x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)
      < (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hq : ∀ y : ℝ, (0:ℝ) < 4 * y ^ 4 + 12 * y ^ 2 + 3 := fun y => by positivity
  have hy2d : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hy4d : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t ^ 4) (4 * y ^ 3) y := fun y => by
    simpa using hasDerivAt_pow 4 y
  have hexpD : ∀ y : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have hinner : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * y) y := by
      have := (hasDerivAt_pow 2 y).neg
      convert this using 1
      ring
    exact hinner.exp
  set D : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * (y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3))
      - Real.sqrt Real.pi / 2 * erfc y with hDdef
  set D' : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * (24 / (4 * y ^ 4 + 12 * y ^ 2 + 3) ^ 2) with hD'def
  have hd : ∀ y : ℝ, HasDerivAt D (D' y) y := by
    intro y
    have hq0 : (4 * y ^ 4 + 12 * y ^ 2 + 3 : ℝ) ≠ 0 := (hq y).ne'
    have hpd : HasDerivAt (fun t : ℝ => t * (2 * t ^ 2 + 5))
        (1 * (2 * y ^ 2 + 5) + y * (2 * (2 * y))) y :=
      (hasDerivAt_id' (𝕜 := ℝ) (x := y)).mul (((hy2d y).const_mul 2).add_const 5)
    have hqd : HasDerivAt (fun t : ℝ => 4 * t ^ 4 + 12 * t ^ 2 + 3)
        (4 * (4 * y ^ 3) + 12 * (2 * y)) y :=
      (((hy4d y).const_mul 4).add ((hy2d y).const_mul 12)).add_const 3
    have hh := hpd.div hqd hq0
    have h := ((hexpD y).mul hh).sub
      ((_kit_hasDerivAt_erfc y).const_mul (Real.sqrt Real.pi / 2))
    convert h using 1
    simp only [hD'def, Pi.div_apply]
    field_simp
    ring
  have hpos : ∀ y : ℝ, x ≤ y → 0 < D' y := by
    intro y _
    simp only [hD'def]
    have := hq y
    positivity
  have hlim : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ =>
        Real.exp (-y ^ 2) * (y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3)))
        Filter.atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        _kit_exp_neg_sq_tendsto
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have hnum : (0:ℝ) ≤ y * (2 * y ^ 2 + 5) := mul_nonneg hy (by positivity)
        have := (hq y).le
        positivity
      · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
        have hb : y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3) ≤ 1 := by
          rw [div_le_one (hq y)]
          nlinarith [sq_nonneg (2 * y ^ 2 - y / 2), sq_nonneg (y - 1), sq_nonneg y]
        have h3 : (0:ℝ) < Real.exp (-y ^ 2) := Real.exp_pos _
        have h4 : (0:ℝ) ≤ y * (2 * y ^ 2 + 5) / (4 * y ^ 4 + 12 * y ^ 2 + 3) := by
          have hnum : (0:ℝ) ≤ y * (2 * y ^ 2 + 5) := mul_nonneg hy (by positivity)
          have := (hq y).le
          positivity
        nlinarith
    have := h1.sub _kit_scaled_erfc_tendsto
    simpa [hDdef] using this
  have hD : D x < 0 :=
    _kit_neg_of_deriv_pos_tendsto_zero (fun y _ => hd y) hpos hlim
  simp only [hDdef] at hD
  have hepos : (0:ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
  have hee : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : Real.exp (x ^ 2)
        * (Real.exp (-x ^ 2) * (x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)))
      < Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x) :=
    mul_lt_mul_of_pos_left (by linarith) hepos
  have h5 : Real.exp (x ^ 2)
        * (Real.exp (-x ^ 2) * (x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)))
      = x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3) := by
    rw [← mul_assoc, hee, one_mul]
  have h6 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
      = Real.sqrt Real.pi / 2 * Real.exp (x ^ 2) * erfc x := by ring
  linarith

-- no-dlmf: private kit lemma; DLMF 7.8.5 context, not an equation surface
/-- Upper 7.8.5-strength bound `𝖬(x) < (2x⁴+9x²+4)/(x(4x⁴+20x²+15))` for `x > 0`:
with `h₂ = p₂/(y q₂)`, `p₂ = 2y⁴+9y²+4`, `q₂ = 4y⁴+20y²+15`, one has
`h₂' − 2yh₂ + 1 = −60/(y q₂)² < 0` (the polynomial collapses to `−60`), so
`D = (√π/2)erfc − e^{-y²}h₂` is strictly increasing on `[x,∞)` with limit `0`,
hence `D(x) < 0`, i.e. `𝖬(x) < h₂(x)`. -/
private lemma _kit_785_upper (x : ℝ) (hx : 0 < x) :
    (Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x
      < (2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15)) := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hq2 : ∀ y : ℝ, (0:ℝ) < 4 * y ^ 4 + 20 * y ^ 2 + 15 := fun y => by positivity
  have hden : ∀ y : ℝ, 0 < y → (0:ℝ) < y * (4 * y ^ 4 + 20 * y ^ 2 + 15) :=
    fun y hy => mul_pos hy (hq2 y)
  have hy2d : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hy4d : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t ^ 4) (4 * y ^ 3) y := fun y => by
    simpa using hasDerivAt_pow 4 y
  have hexpD : ∀ y : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2))
      (Real.exp (-y ^ 2) * (-2 * y)) y := by
    intro y
    have hinner : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * y) y := by
      have := (hasDerivAt_pow 2 y).neg
      convert this using 1
      ring
    exact hinner.exp
  set D : ℝ → ℝ := fun y =>
    Real.sqrt Real.pi / 2 * erfc y
      - Real.exp (-y ^ 2)
          * ((2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15))) with hDdef
  set D' : ℝ → ℝ := fun y =>
    Real.exp (-y ^ 2) * (60 / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ^ 2) with hD'def
  have hd : ∀ y : ℝ, x ≤ y → HasDerivAt D (D' y) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hx hy
    have hd0 : (y * (4 * y ^ 4 + 20 * y ^ 2 + 15) : ℝ) ≠ 0 := (hden y hy0).ne'
    have hy0' : (y:ℝ) ≠ 0 := hy0.ne'
    have hq0 : (4 * y ^ 4 + 20 * y ^ 2 + 15 : ℝ) ≠ 0 := (hq2 y).ne'
    have hpd : HasDerivAt (fun t : ℝ => 2 * t ^ 4 + 9 * t ^ 2 + 4)
        (2 * (4 * y ^ 3) + 9 * (2 * y)) y :=
      (((hy4d y).const_mul 2).add ((hy2d y).const_mul 9)).add_const 4
    have hqd : HasDerivAt (fun t : ℝ => t * (4 * t ^ 4 + 20 * t ^ 2 + 15))
        (1 * (4 * y ^ 4 + 20 * y ^ 2 + 15) + y * (4 * (4 * y ^ 3) + 20 * (2 * y))) y :=
      (hasDerivAt_id' (𝕜 := ℝ) (x := y)).mul
        ((((hy4d y).const_mul 4).add ((hy2d y).const_mul 20)).add_const 15)
    have hh := hpd.div hqd hd0
    have h := ((_kit_hasDerivAt_erfc y).const_mul (Real.sqrt Real.pi / 2)).sub
      ((hexpD y).mul hh)
    convert h using 1
    simp only [hD'def, Pi.div_apply]
    field_simp
    ring
  have hpos : ∀ y : ℝ, x ≤ y → 0 < D' y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hx hy
    simp only [hD'def]
    have := hden y hy0
    positivity
  have hlim : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ =>
        Real.exp (-y ^ 2)
          * ((2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15))))
        Filter.atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        _kit_exp_neg_sq_tendsto
      · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with y hy
        have hy0 : (0:ℝ) < y := by linarith
        have := (hden y hy0).le
        positivity
      · filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with y hy
        have hy0 : (0:ℝ) < y := by linarith
        have h1' : (0:ℝ) ≤ y - 1 := by linarith
        have hb : (2 * y ^ 4 + 9 * y ^ 2 + 4) / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) ≤ 1 := by
          rw [div_le_one (hden y hy0)]
          nlinarith [mul_nonneg h1' (mul_nonneg (sq_nonneg y) (sq_nonneg y)),
            mul_nonneg h1' (sq_nonneg y), h1', sq_nonneg y, sq_nonneg (y ^ 2)]
        have h3 : (0:ℝ) < Real.exp (-y ^ 2) := Real.exp_pos _
        have h4 : (0:ℝ) ≤ (2 * y ^ 4 + 9 * y ^ 2 + 4)
            / (y * (4 * y ^ 4 + 20 * y ^ 2 + 15)) := by
          have := (hden y hy0).le
          positivity
        nlinarith
    have := _kit_scaled_erfc_tendsto.sub h1
    simpa [hDdef] using this
  have hD : D x < 0 := _kit_neg_of_deriv_pos_tendsto_zero hd hpos hlim
  simp only [hDdef] at hD
  have hepos : (0:ℝ) < Real.exp (x ^ 2) := Real.exp_pos _
  have hee : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
      < Real.exp (x ^ 2) * (Real.exp (-x ^ 2)
          * ((2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15)))) :=
    mul_lt_mul_of_pos_left (by linarith) hepos
  have h5 : Real.exp (x ^ 2) * (Real.exp (-x ^ 2)
        * ((2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15))))
      = (2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15)) := by
    rw [← mul_assoc, hee, one_mul]
  have h6 : Real.exp (x ^ 2) * (Real.sqrt Real.pi / 2 * erfc x)
      = Real.sqrt Real.pi / 2 * Real.exp (x ^ 2) * erfc x := by ring
  linarith

/-- Chain of bounds on `x·𝖬(x)` for `x ≥ 0`, where `𝖬(x) = (√π/2)e^{x²}erfc(x)` is
the Mills ratio (DLMF 7.8.5):
`x²/(2x²+1) ≤ x²(2x²+5)/(4x⁴+12x²+3) ≤ x·𝖬(x) < (2x⁴+9x²+4)/(4x⁴+20x²+15) < (x²+1)/(2x²+3)`.
(Corrected 2026-06-24 from the DLMF PDF — the first bound is `x²/(2x²+1)` (not
`x²/(2√(x²+1))`) and the last is `(x²+1)/(2x²+3)` (not `x/(2√(x²+3))`). See ERRATA.)

DLMF 7.8.5.
DAG: E-7.8.5.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_5 (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / (2 * x ^ 2 + 1)
        ≤ (x ^ 2 * (2 * x ^ 2 + 5)) / (4 * x ^ 4 + 12 * x ^ 2 + 3)
      ∧ (x ^ 2 * (2 * x ^ 2 + 5)) / (4 * x ^ 4 + 12 * x ^ 2 + 3)
        ≤ x * ((Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x)
      ∧ x * ((Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x)
        < (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15)
      ∧ (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15)
        < (x ^ 2 + 1) / (2 * x ^ 2 + 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- link 1: rational inequality
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg x]
  · -- link 2: from the kit lower bound, multiplied by x ≥ 0
    have hlow := _kit_785_lower x
    calc x ^ 2 * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)
        = x * (x * (2 * x ^ 2 + 5) / (4 * x ^ 4 + 12 * x ^ 2 + 3)) := by
          rw [← mul_div_assoc]
          ring_nf
      _ ≤ x * ((Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x) :=
          mul_le_mul_of_nonneg_left hlow.le hx
  · -- link 3: from the kit upper bound for x > 0; at x = 0 it reads 0 < 4/15
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h]
      norm_num
    · have hup := _kit_785_upper x h
      have hx0 : x ≠ 0 := h.ne'
      calc x * ((Real.sqrt Real.pi / 2) * Real.exp (x ^ 2) * FLMF.Error.erfc x)
          < x * ((2 * x ^ 4 + 9 * x ^ 2 + 4) / (x * (4 * x ^ 4 + 20 * x ^ 2 + 15))) :=
            mul_lt_mul_of_pos_left hup h
        _ = (2 * x ^ 4 + 9 * x ^ 2 + 4) / (4 * x ^ 4 + 20 * x ^ 2 + 15) := by
            rw [← mul_div_assoc]
            rw [mul_div_mul_left _ _ hx0]
  · -- link 4: rational inequality (the cross-difference is the constant 3)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg x]

/-- Upper bound on `∫₀^x e^{a t²} dt` for `a, x > 0` (DLMF 7.8.6):
`∫₀^x e^{a t²} dt < (1/(3 a x))·(2 e^{a x²} + a x² − 2)`.
(Corrected 2026-06-24 from the DLMF PDF — the prefactor is `1/(3 a x)` (x in the
denominator), not `(1/(3a))·x`. See ERRATA.)

DLMF 7.8.6.
DAG: E-7.8.6.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_6 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.exp (a * t ^ 2))
      < (1 / (3 * a * x)) * (2 * Real.exp (a * x ^ 2) + a * x ^ 2 - 2) := by
  have hcont : Continuous (fun t : ℝ => Real.exp (a * t ^ 2)) := by fun_prop
  set F : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..y, Real.exp (a * t ^ 2) with hFdef
  have hF : ∀ y : ℝ, HasDerivAt F (Real.exp (a * y ^ 2)) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 y)
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hexp : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (a * y ^ 2))
      (Real.exp (a * y ^ 2) * (2 * a * y)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => a * y ^ 2) (2 * a * y) y := by
      have := (hasDerivAt_pow 2 y).const_mul a
      convert this using 1
      ring
    exact h1.exp
  set G : ℝ → ℝ := fun y => y * Real.exp (a * y ^ 2) + 2 * y - 3 * F y with hGdef
  have hG : ∀ y : ℝ, HasDerivAt G
      (2 * (a * y ^ 2 * Real.exp (a * y ^ 2) + 1 - Real.exp (a * y ^ 2))) y := by
    intro y
    have h := (((hasDerivAt_id' (𝕜 := ℝ) (x := y)).mul (hexp y)).add
      ((hasDerivAt_id' (𝕜 := ℝ) (x := y)).const_mul 2)).sub ((hF y).const_mul 3)
    convert h using 1
    ring
  have hGpos : ∀ y : ℝ, 0 < y →
      0 < 2 * (a * y ^ 2 * Real.exp (a * y ^ 2) + 1 - Real.exp (a * y ^ 2)) := by
    intro y hy
    have hu : 0 < a * y ^ 2 := by positivity
    have h1 : (1 : ℝ) - a * y ^ 2 < Real.exp (-(a * y ^ 2)) := by
      have := Real.add_one_lt_exp (x := -(a * y ^ 2)) (by simpa using hu.ne')
      linarith
    have hepos : 0 < Real.exp (a * y ^ 2) := Real.exp_pos _
    have h2 : (1 - a * y ^ 2) * Real.exp (a * y ^ 2) < 1 := by
      calc (1 - a * y ^ 2) * Real.exp (a * y ^ 2)
          < Real.exp (-(a * y ^ 2)) * Real.exp (a * y ^ 2) :=
            mul_lt_mul_of_pos_right h1 hepos
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [h2]
  have hGmono : StrictMonoOn G (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y _ => (hG y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hG y).deriv]
      exact hGpos y hy
  have hG0 : G 0 = 0 := by simp [hGdef, hF0]
  have hGy : ∀ y : ℝ, 0 < y → 0 < G y := by
    intro y hy
    have := hGmono Set.self_mem_Ici (Set.mem_Ici.mpr hy.le) hy
    rwa [hG0] at this
  set H : ℝ → ℝ := fun y => 2 * Real.exp (a * y ^ 2) + a * y ^ 2 - 2 - 3 * a * (y * F y)
    with hHdef
  have hH : ∀ y : ℝ, HasDerivAt H (a * G y) y := by
    intro y
    have hyF : HasDerivAt (fun y : ℝ => y * F y) (1 * F y + y * Real.exp (a * y ^ 2)) y :=
      (hasDerivAt_id' (𝕜 := ℝ) (x := y)).mul (hF y)
    have hay2 : HasDerivAt (fun y : ℝ => a * y ^ 2) (2 * a * y) y := by
      have := (hasDerivAt_pow 2 y).const_mul a
      convert this using 1
      ring
    have h := ((((hexp y).const_mul 2).add hay2).sub_const 2).sub (hyF.const_mul (3 * a))
    convert h using 1
    simp only [hGdef]
    ring
  have hHmono : StrictMonoOn H (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y _ => (hH y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hH y).deriv]
      exact mul_pos ha (hGy y hy)
  have hH0 : H 0 = 0 := by simp [hHdef, hF0]
  have hHx : 0 < H x := by
    have := hHmono Set.self_mem_Ici (Set.mem_Ici.mpr hx.le) hx
    rwa [hH0] at this
  have h3ax : 0 < 3 * a * x := by positivity
  rw [one_div, inv_mul_eq_div, lt_div_iff₀ h3ax]
  simp only [hHdef] at hHx
  nlinarith [hHx]


-- no-dlmf: upper-bound member of the three-member chain 7.8.7 (conjunction carrier is
-- `erf_7_8_7_chain` below). DLMF 7.8.7 reads
-- `sinh(x²)/x < e^{x²}F(x) = ∫₀ˣ e^{t²} dt < (e^{x²}−1)/x`, x > 0.
/-- Upper bound on `∫₀^x e^{t²} dt = e^{x²} F(x)` for `x > 0` (upper member of DLMF
7.8.7): `∫₀^x e^{t²} dt < (e^{x²} − 1)/x`.  (The 2026-06-25 revision deleted a
mis-transcribed `sinh x/(2x) <` lower bound — the DLMF lower bound is `sinh(x²)/x`,
with the argument squared; see ERRATA `ch7-7-8-7-lower-bound-dropped`.)
`e^{x²}·F(x) = ∫₀ˣ e^{t²} dt` since `F = dawson`. -/
theorem erf_7_8_7 (x : ℝ) (hx : 0 < x) :
    Real.exp (x ^ 2) * FLMF.dawson x < (Real.exp (x ^ 2) - 1) / x := by
  have hstep1 : Real.exp (x ^ 2) * FLMF.dawson x = ∫ t in (0:ℝ)..x, Real.exp (t ^ 2) := by
    unfold FLMF.dawson
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hstep1]
  have h6 := erf_7_8_6 1 x one_pos hx
  simp only [one_mul] at h6
  have hfin : (1 / (3 * x)) * (2 * Real.exp (x ^ 2) + x ^ 2 - 2) ≤ (Real.exp (x ^ 2) - 1) / x := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hx]
    have hexp : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp (x ^ 2)
    nlinarith
  linarith [h6, hfin]

-- no-dlmf: lower-bound member of the chain 7.8.7 (conjunction carrier is
-- `erf_7_8_7_chain` below); open `sorry`
/-- Lower bound member of DLMF 7.8.7: `sinh(x²)/x < ∫₀ˣ e^{t²} dt` for `x > 0`. -/
theorem sinh_sq_div_lt_integral_exp_sq (x : ℝ) (hx : 0 < x) :
    Real.sinh (x ^ 2) / x < ∫ t in (0:ℝ)..x, Real.exp (t ^ 2) := by
  have hcont : Continuous (fun t : ℝ => Real.exp (t ^ 2)) := by fun_prop
  set F : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..y, Real.exp (t ^ 2) with hFdef
  have hF : ∀ y : ℝ, HasDerivAt F (Real.exp (y ^ 2)) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 y)
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  -- `F y ≥ y` for `y ≥ 0`, via `exp(t²) ≥ 1`.
  have hFge : ∀ y : ℝ, 0 ≤ y → y ≤ F y := by
    intro y hy
    have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 0 y :=
      intervalIntegral.intervalIntegrable_const
    have hib : IntervalIntegrable (fun t : ℝ => Real.exp (t ^ 2)) MeasureTheory.volume 0 y :=
      hcont.intervalIntegrable 0 y
    have hmono := intervalIntegral.integral_mono_on hy hconst hib
      (fun t _ => by
        have : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
        calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
          _ ≤ Real.exp (t ^ 2) := Real.exp_le_exp.mpr this)
    simpa [hFdef] using hmono
  -- `K(y) = 2 y F(y) - exp(y²) + exp(-y²)`, with `K(0) = 0` and `K' > 0` on `(0,∞)`.
  set K : ℝ → ℝ := fun y => 2 * y * F y - Real.exp (y ^ 2) + Real.exp (-(y ^ 2)) with hKdef
  have hexpPos : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (y ^ 2))
      (Real.exp (y ^ 2) * (2 * y)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    exact h1.exp
  have hexpNeg : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
      (Real.exp (-(y ^ 2)) * (-(2 * y))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * y)) y := by
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
        simpa using hasDerivAt_pow 2 y
      simpa using h2.neg
    exact h1.exp
  have hK : ∀ y : ℝ, HasDerivAt K (2 * F y - 2 * y * Real.exp (-(y ^ 2))) y := by
    intro y
    have hyF : HasDerivAt (fun y : ℝ => 2 * y * F y)
        (2 * F y + 2 * y * Real.exp (y ^ 2)) y := by
      have h := ((hasDerivAt_id' (𝕜 := ℝ) (x := y)).const_mul (2 : ℝ)).mul (hF y)
      convert h using 1
      ring
    have h := (hyF.sub (hexpPos y)).add (hexpNeg y)
    convert h using 1
    ring
  have hKpos : ∀ y : ℝ, 0 < y → 0 < 2 * F y - 2 * y * Real.exp (-(y ^ 2)) := by
    intro y hy
    have hFy := hFge y hy.le
    have hlt1 : Real.exp (-(y ^ 2)) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_lt_exp.mpr
      have : 0 < y ^ 2 := by positivity
      linarith
    have hlt : y * Real.exp (-(y ^ 2)) < y := by
      calc y * Real.exp (-(y ^ 2)) < y * 1 := by
            apply mul_lt_mul_of_pos_left hlt1 hy
        _ = y := mul_one y
    nlinarith [hFy, hlt]
  have hKmono : StrictMonoOn K (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun y _ => (hK y).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hK y).deriv]
      exact hKpos y hy
  have hK0 : K 0 = 0 := by simp [hKdef, hF0]
  have hKx : 0 < K x := by
    have := hKmono Set.self_mem_Ici (Set.mem_Ici.mpr hx.le) hx
    rwa [hK0] at this
  have hsinh : Real.sinh (x ^ 2) = (Real.exp (x ^ 2) - Real.exp (-(x ^ 2))) / 2 := by
    rw [Real.sinh_eq]
  rw [hsinh, div_lt_iff₀ hx]
  simp only [hKdef] at hKx
  nlinarith [hKx]

/-- **DLMF 7.8.7**, the full three-member chain: for `x > 0`,
`sinh(x²)/x < e^{x²} F(x) = ∫₀ˣ e^{t²} dt < (e^{x²} − 1)/x`, where `F` is Dawson's
integral. (The middle equality is `e^{x²}·F(x) = ∫₀ˣ e^{t²} dt`, immediate from
`F = dawson`.)

Note the argument of `sinh`: the DLMF lower bound is `sinh(x²)/x`, NOT `sinh x/(2x)`.
An earlier FLMF revision mis-transcribed it that way, correctly deleted the false
statement, but then wrongly concluded the lower bound was absent from DLMF; see
`docs/ERRATA.md`.

DLMF 7.8.7.
DAG: E-7.8.7.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_7_chain (x : ℝ) (hx : 0 < x) :
    Real.sinh (x ^ 2) / x < Real.exp (x ^ 2) * FLMF.dawson x ∧
      Real.exp (x ^ 2) * FLMF.dawson x = ∫ t in (0:ℝ)..x, Real.exp (t ^ 2) ∧
      Real.exp (x ^ 2) * FLMF.dawson x < (Real.exp (x ^ 2) - 1) / x := by
  have hstep1 : Real.exp (x ^ 2) * FLMF.dawson x = ∫ t in (0:ℝ)..x, Real.exp (t ^ 2) := by
    unfold FLMF.dawson
    rw [← mul_assoc, ← Real.exp_add]
    simp
  refine ⟨?_, hstep1, erf_7_8_7 x hx⟩
  rw [hstep1]
  exact sinh_sq_div_lt_integral_exp_sq x hx

/-- **DLMF 7.8.8** (Pólya 1949). `erf x < √(1 − e^{−4x²/π})` for `x > 0`.

Note the square root over the whole right-hand side: the un-rooted form
`erf x < 1 − e^{−4x²/π}` is false (at `x = 1`, `erf 1 = 0.8427 > 0.7201`), and an
earlier FLMF revision mis-transcribed 7.8.8 that way and wrongly withdrew it as a
"phantom" equation — 7.8.8 is a genuine §7.8 entry (added in DLMF v1.0.17). See
`docs/ERRATA.md`.

DLMF 7.8.8.
DAG: E-7.8.8.
Numerical: PASS
Verified: verified
-/
theorem erf_7_8_8 (x : ℝ) (hx : 0 < x) :
    erf x < Real.sqrt (1 - Real.exp (-(4 * x ^ 2) / Real.pi)) := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  set c : ℝ := 4 * x ^ 2 / Real.pi with hcdef
  -- continuity kit
  have hinv_cont : Continuous (fun t : ℝ => 1 / (1 + t ^ 2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    positivity
  have hf_cont : Continuous (fun t : ℝ => Real.exp (-(x ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  have hg_cont : Continuous (fun t : ℝ => Real.exp (-c) * ((1 + c) * (1 / (1 + t ^ 2)) - x ^ 2)) :=
    continuous_const.mul ((continuous_const.mul hinv_cont).sub continuous_const)
  -- ∫₀¹ dt/(1+t²) = π/4
  have hI1 : (∫ t in (0:ℝ)..1, 1 / (1 + t ^ 2)) = Real.pi / 4 := by
    simp [Real.arctan_one, Real.arctan_zero]
  -- the tangent-line comparison integrand integrates to exactly e^{-c}·π/4
  have hIg : (∫ t in (0:ℝ)..1, Real.exp (-c) * ((1 + c) * (1 / (1 + t ^ 2)) - x ^ 2))
      = Real.exp (-c) * (Real.pi / 4) := by
    rw [intervalIntegral.integral_const_mul]
    have h2 : (∫ t in (0:ℝ)..1, ((1 + c) * (1 / (1 + t ^ 2)) - x ^ 2))
        = (1 + c) * (Real.pi / 4) - x ^ 2 := by
      rw [intervalIntegral.integral_sub
        ((hinv_cont.const_mul (1 + c)).intervalIntegrable 0 1) intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul, hI1, intervalIntegral.integral_const]
      simp
    rw [h2]
    have h3 : (1 + c) * (Real.pi / 4) - x ^ 2 = Real.pi / 4 := by
      rw [hcdef]
      field_simp
      ring
    rw [h3]
  -- pointwise tangent-line bound  e^{-c}(1+c-u) ≤ e^{-u}  at u = x²(t²+1)
  have hle : ∀ t : ℝ, Real.exp (-c) * ((1 + c) * (1 / (1 + t ^ 2)) - x ^ 2)
      ≤ Real.exp (-(x ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1) := by
    intro t
    have ht1 : (0:ℝ) < 1 + t ^ 2 := by positivity
    set u : ℝ := x ^ 2 * (t ^ 2 + 1) with hudef
    have htan : Real.exp (-c) * (1 + c - u) ≤ Real.exp (-u) := by
      have h2 := Real.add_one_le_exp (c - u)
      have h3 : Real.exp (-c) * Real.exp (c - u) = Real.exp (-u) := by
        rw [← Real.exp_add]
        ring_nf
      calc Real.exp (-c) * (1 + c - u)
          ≤ Real.exp (-c) * Real.exp (c - u) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp (-u) := h3
    have heq : Real.exp (-c) * ((1 + c) * (1 / (1 + t ^ 2)) - x ^ 2)
        = Real.exp (-c) * (1 + c - u) / (1 + t ^ 2) := by
      rw [hudef]
      field_simp
      ring
    have heq2 : Real.exp (-(x ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1)
        = Real.exp (-u) / (1 + t ^ 2) := by
      rw [show -(x ^ 2) * (t ^ 2 + 1) = -u by rw [hudef]; ring,
        show (t ^ 2 + 1 : ℝ) = 1 + t ^ 2 by ring]
    rw [heq, heq2]
    gcongr
  -- strictness at t = 0 (there u = x² ≠ c since π ≠ 4)
  have hgt : x ^ 2 < c := by
    rw [hcdef, lt_div_iff₀ hπ]
    nlinarith [mul_pos (show (0:ℝ) < x ^ 2 by positivity)
      (show (0:ℝ) < 4 - Real.pi by linarith)]
  have hlt0 : Real.exp (-c) * ((1 + c) * (1 / (1 + (0:ℝ) ^ 2)) - x ^ 2)
      < Real.exp (-(x ^ 2) * ((0:ℝ) ^ 2 + 1)) / ((0:ℝ) ^ 2 + 1) := by
    have hne : c - x ^ 2 ≠ 0 := (sub_pos.mpr hgt).ne'
    have h2 := Real.add_one_lt_exp hne
    have h3 : Real.exp (-c) * Real.exp (c - x ^ 2) = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      ring_nf
    have htan : Real.exp (-c) * (1 + c - x ^ 2) < Real.exp (-x ^ 2) := by
      calc Real.exp (-c) * (1 + c - x ^ 2)
          < Real.exp (-c) * Real.exp (c - x ^ 2) :=
            mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos _)
        _ = Real.exp (-x ^ 2) := h3
    norm_num
    linarith [htan]
  -- strict integral comparison
  have key : Real.exp (-c) * (Real.pi / 4)
      < ∫ t in (0:ℝ)..1, Real.exp (-(x ^ 2) * (t ^ 2 + 1)) / (t ^ 2 + 1) := by
    rw [← hIg]
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      one_pos hg_cont.continuousOn hf_cont.continuousOn
      (fun t _ => hle t)
      ⟨0, Set.mem_Icc.mpr (by norm_num), hlt0⟩
  -- assemble via 7.7.5
  have h775 := erf_7_7_5 x
  rw [h775] at key
  have h4pos : (0:ℝ) < Real.pi / 4 := by linarith
  have h2 : Real.exp (-c) < 1 - erf x ^ 2 := by
    nlinarith [key, h4pos]
  have herf0 : (0:ℝ) ≤ erf x := erf_nonneg hx.le
  have hxeq : -(4 * x ^ 2) / Real.pi = -c := by
    rw [hcdef]
    ring
  rw [hxeq]
  exact (Real.lt_sqrt herf0).mpr (by linarith)

end FLMF.Error
