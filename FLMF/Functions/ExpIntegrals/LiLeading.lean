import Mathlib.Analysis.Calculus.SmoothSeries
import FLMF.Functions.ExpIntegrals.E1Leading
import FLMF.Functions.ExpIntegrals.LogIntegral

/-!
# Leading asymptotics of the logarithmic integral `li(x)` (DLMF §6.12)

The logarithmic integral `li(x) = ⨍₀ˣ dt/ln t` satisfies the prime-counting
envelope
$$\operatorname{li}(x) \sim \frac{x}{\ln x}\sum_{k\ge 0}\frac{k!}{(\ln x)^k},
\qquad x \to \infty$$
(DLMF 6.12.2), whose leading term is `li(x) ~ x / ln x`.

We work with a Watson-ready **proxy** `liW(x) = e^{ln x} ∫_{(0,∞)} e^{-(ln x) u} / (1 + u) du`,
a half-line Laplace integral with amplitude `g(u) = 1/(1+u)`, `g(0⁺) = 1`, so the
leading-order Watson lemma gives `liW(x) ~ x/ln x`.  NB `liW` is `E₁`-based
(`liW(x) = x² E₁(ln x)`) and is **not** equal to `li = Ei ∘ log`; the two share only
this leading asymptotic (`li(x)/liW(x) → 1`).

`liW_asymptotic` proves `liW(x) · (ln x) / x → 1` (the proxy, untagged), and
`li_asymptotic` carries the canonical DLMF 6.12.2 result for `li` itself,
`li(x) · (ln x) / x → 1`, i.e. `li(x) ~ x/ln x`.
-/

namespace FLMF.ExpIntegrals

open MeasureTheory Real Filter Topology Set PicardLefschetz

/-- The logarithmic integral `li`, in its Watson-ready (`t = (ln x)(1+u)`)
form.  For `x > 1` (so `ln x > 0`) this matches the Cauchy principal value
`⨍₀ˣ dt/ln t`; here we package the part of the integral responsible for the
leading large-`x` behaviour, namely `e^{ln x}` times the Watson factor of the
exponential integral. -/
-- no-dlmf: Watson-ready representation used for the asymptotic; canonical li is tagged in LogIntegral
noncomputable def liW (x : ℝ) : ℝ :=
  Real.exp (Real.log x) *
    ∫ u in Ioi (0 : ℝ), Real.exp (-(Real.log x) * u) * (1 / (1 + u))

/-- For `x > 0`, `e^{ln x} = x`, so `liW x = x · (Watson factor at ln x)`. -/
-- no-dlmf: arithmetic unfolding helper for `liW`; no DLMF counterpart
theorem liW_eq (x : ℝ) (hx : 0 < x) :
    liW x = x * ∫ u in Ioi (0 : ℝ), Real.exp (-(Real.log x) * u) * (1 / (1 + u)) := by
  unfold liW
  rw [Real.exp_log hx]

/-- The Watson factor for `li`, evaluated at `ln x` and rescaled by `ln x`,
tends to `1` as `x → ∞` (since `ln x → ∞`). -/
-- no-dlmf: intermediate Watson-factor limit toward the asymptotic theorem below
theorem tendsto_li_watson_factor :
    Tendsto
      (fun x : ℝ =>
        (Real.log x) *
          ∫ u in Ioi (0 : ℝ), Real.exp (-(Real.log x) * u) * (1 / (1 + u)))
      atTop (𝓝 1) := by
  -- Compose the `E₁` Watson factor with `ln : atTop → atTop`.
  have hcomp :=
    tendsto_watson_factor.comp Real.tendsto_log_atTop
  -- `tendsto_watson_factor` is stated with the variable `y`; compose with `y = ln x`.
  simpa [Function.comp] using hcomp

/-- Leading asymptotic of the Watson **proxy** `liW`: `liW(x) · (ln x) / x → 1` as
`x → ∞`.  `liW` is `E₁`-based and equals `li` only asymptotically, so this lemma
carries no DLMF tag; the canonical DLMF 6.12.2 result for `li` is `li_asymptotic`. -/
-- no-dlmf: leading asymptotic of the `liW` proxy; the DLMF 6.12.2 li result is `li_asymptotic`
theorem liW_asymptotic :
    Tendsto (fun x : ℝ => liW x * Real.log x / x) atTop (𝓝 1) := by
  refine tendsto_li_watson_factor.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [liW_eq x hx]
  set I := ∫ u in Ioi (0 : ℝ), Real.exp (-(Real.log x) * u) * (1 / (1 + u)) with hI
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp

/-! ## The canonical `li` asymptotic via the large-argument `Ei` expansion -/

private theorem eiSeries_deriv_sum {y : ℝ} (hy : y ≠ 0) :
    ∑' k : ℕ, y ^ k / (Nat.factorial (k+1) : ℝ) = (Real.exp y - 1) / y := by
  have hexp : Real.exp y = ∑' n : ℕ, y ^ n / (Nat.factorial n : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsummable : Summable (fun n : ℕ => y ^ n / (Nat.factorial n : ℝ)) :=
    Real.summable_pow_div_factorial y
  have hpeel : Real.exp y - 1 = ∑' k : ℕ, y ^ (k+1) / (Nat.factorial (k+1) : ℝ) := by
    rw [hexp, hsummable.tsum_eq_zero_add]; simp
  rw [hpeel, eq_div_iff hy, ← tsum_mul_right]
  congr 1; ext k; rw [pow_succ]; ring

/-- Derivative of `eiSeries` for `y > 0`: `eiSeries'(y) = (e^y - 1)/y`. -/
private theorem hasDerivAt_eiSeries {y : ℝ} (hy : 0 < y) :
    HasDerivAt Def.eiSeries ((Real.exp y - 1) / y) y := by
  set R := y + 1 with hR
  have hyR : y < R := by simp [hR]
  have hR0 : 0 < R := by positivity
  have hbound : Summable (fun k : ℕ => R ^ k / (Nat.factorial (k+1) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (Real.summable_pow_div_factorial R)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hsummable_y : Summable (fun k : ℕ =>
      y ^ (k+1) / (((k:ℝ)+1) * (Nat.factorial (k+1) : ℝ))) := by
    have hbase : Summable (fun k : ℕ => y ^ (k+1) / (Nat.factorial (k+1) : ℝ)) := by
      have := (Real.summable_pow_div_factorial y).comp_injective (Nat.succ_injective)
      simpa [Function.comp] using this
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hbase
    have h1 : (Nat.factorial (k+1) : ℝ) ≤ ((k:ℝ)+1) * (Nat.factorial (k+1) : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, (by positivity : (0:ℝ) ≤ (Nat.factorial (k+1) : ℝ))]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => R ^ k / (Nat.factorial (k+1) : ℝ))
    (g := fun k z => z ^ (k+1) / (((k:ℝ)+1) * (Nat.factorial (k+1) : ℝ)))
    (g' := fun k z => z ^ k / (Nat.factorial (k+1) : ℝ))
    (t := Ioo 0 R) (y₀ := y)
    hbound isOpen_Ioo (convex_Ioo 0 R).isPreconnected
    (fun k z _ => by
      have hd : HasDerivAt (fun z : ℝ => z ^ (k+1)) (((k:ℝ)+1) * z ^ k) z := by
        simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (k+1) z
      have := hd.div_const (((k:ℝ)+1) * (Nat.factorial (k+1) : ℝ))
      convert this using 1
      have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
      field_simp)
    (fun k z hz => by
      have hz0 : 0 < z := hz.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < z ^ k),
        abs_of_pos (by positivity : (0:ℝ) < (Nat.factorial (k+1):ℝ))]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (le_of_lt hz0) (le_of_lt hz.2) k)
    ⟨hy, hyR⟩ hsummable_y ⟨hy, hyR⟩
  have heq : Def.eiSeries = fun z => ∑' k : ℕ, z ^ (k+1) / (((k:ℝ)+1) * (Nat.factorial (k+1) : ℝ)) := rfl
  rw [heq]
  have hval : ∑' k : ℕ, y ^ k / (Nat.factorial (k+1) : ℝ) = (Real.exp y - 1) / y :=
    eiSeries_deriv_sum (ne_of_gt hy)
  rw [← hval]
  exact key

/-- Derivative of `Ei` for `y > 0`: `Ei'(y) = e^y / y`. -/
theorem hasDerivAt_Ei {y : ℝ} (hy : 0 < y) :
    HasDerivAt Def.Ei (Real.exp y / y) y := by
  have heq : Def.Ei = fun z => Real.eulerMascheroniConstant + Real.log |z| + Def.eiSeries z := by
    funext z; exact Def.Ei_def z
  rw [heq]
  have hlog : HasDerivAt (fun z => Real.log |z|) (1 / y) y := by
    have := (Real.hasDerivAt_log (ne_of_gt hy))
    have hcongr : (fun z => Real.log |z|) =ᶠ[nhds y] Real.log := by
      filter_upwards [eventually_gt_nhds hy] with z hz
      rw [abs_of_pos hz]
    rw [one_div]
    exact (this.congr_of_eventuallyEq hcongr)
  have hseries := hasDerivAt_eiSeries hy
  have hconst : HasDerivAt (fun _ : ℝ => Real.eulerMascheroniConstant) 0 y := hasDerivAt_const y _
  have := (hconst.add hlog).add hseries
  convert this using 1
  field_simp
  ring

/-- FTC: for `y ≥ 1`, `Ei y - Ei 1 = ∫ t in 1..y, e^t / t`. -/
private theorem Ei_sub_integral {y : ℝ} (hy : 1 ≤ y) :
    Def.Ei y - Def.Ei 1 = ∫ t in (1:ℝ)..y, Real.exp t / t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Def.Ei)]
  · intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact hasDerivAt_Ei (lt_of_lt_of_le one_pos ht.1)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    apply ContinuousOn.div (Real.continuous_exp.continuousOn) (continuousOn_id)
    intro t ht; exact ne_of_gt (lt_of_lt_of_le one_pos ht.1)

/-- IBP identity: `∫₁^y e^t/t = e^y/y - e + ∫₁^y e^t/t²` for `y ≥ 1`. -/
private theorem ibp_identity {y : ℝ} (hy : 1 ≤ y) :
    (∫ t in (1:ℝ)..y, Real.exp t / t)
      = Real.exp y / y - Real.exp 1 + ∫ t in (1:ℝ)..y, Real.exp t / t^2 := by
  have hderiv : ∫ t in (1:ℝ)..y, (Real.exp t / t - Real.exp t / t^2)
      = Real.exp y / y - Real.exp 1 / 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.exp t / t)]
    · intro t ht
      rw [Set.uIcc_of_le hy] at ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
      have hd : HasDerivAt (fun t => Real.exp t / t)
          ((Real.exp t * t - Real.exp t * 1) / t^2) t := by
        exact (Real.hasDerivAt_exp t).div (hasDerivAt_id t) (ne_of_gt ht0)
      convert hd using 1
      field_simp
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hy]
      apply ContinuousOn.sub
      · apply ContinuousOn.div Real.continuous_exp.continuousOn continuousOn_id
        intro t ht; exact ne_of_gt (lt_of_lt_of_le one_pos ht.1)
      · apply ContinuousOn.div Real.continuous_exp.continuousOn (by fun_prop)
        intro t ht; exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos ht.1))
  have hint1 : IntervalIntegrable (fun t => Real.exp t / t) MeasureTheory.volume 1 y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    apply ContinuousOn.div Real.continuous_exp.continuousOn continuousOn_id
    intro t ht; exact ne_of_gt (lt_of_lt_of_le one_pos ht.1)
  have hint2 : IntervalIntegrable (fun t => Real.exp t / t^2) MeasureTheory.volume 1 y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    apply ContinuousOn.div Real.continuous_exp.continuousOn (by fun_prop)
    intro t ht; exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le one_pos ht.1))
  rw [intervalIntegral.integral_sub hint1 hint2] at hderiv
  rw [div_one] at hderiv
  linarith [hderiv]

/-- Integrability of `e^t/t²` on intervals staying positive. -/
private theorem int_exp_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t => Real.exp t / t^2) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht
    have hmin : min a b ≤ t := by rw [Set.uIcc] at ht; exact ht.1
    exact lt_of_lt_of_le (lt_min ha hb) hmin
  apply ContinuousOn.div Real.continuous_exp.continuousOn (by fun_prop)
  intro t ht; exact pow_ne_zero 2 (ne_of_gt (hpos t ht))

/-- Split-at-`y/2` bound for the IBP remainder `∫₁^y e^t/t²`. -/
private theorem tail_bound {y : ℝ} (hy : 2 ≤ y) :
    (∫ t in (1:ℝ)..y, Real.exp t / t^2)
      ≤ y * Real.exp (y/2) + (4 / y^2) * Real.exp y := by
  have hy0 : (0:ℝ) < y := by linarith
  have hhalf : (1:ℝ) ≤ y/2 := by linarith
  have hhalfy : y/2 ≤ y := by linarith
  have hsplit : (∫ t in (1:ℝ)..y, Real.exp t / t^2)
      = (∫ t in (1:ℝ)..(y/2), Real.exp t / t^2)
        + ∫ t in (y/2)..y, Real.exp t / t^2 := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (int_exp_div_sq one_pos (by linarith : (0:ℝ) < y/2))
      (int_exp_div_sq (by linarith : (0:ℝ) < y/2) hy0)]
  rw [hsplit]
  gcongr
  · have hb1 : (∫ t in (1:ℝ)..(y/2), Real.exp t / t^2)
        ≤ ∫ t in (1:ℝ)..(y/2), Real.exp (y/2) := by
      apply intervalIntegral.integral_mono_on hhalf
        (int_exp_div_sq one_pos (by linarith : (0:ℝ) < y/2))
        (intervalIntegrable_const)
      intro t ht
      have ht1 : 1 ≤ t := ht.1
      have hty : t ≤ y/2 := ht.2
      rw [div_le_iff₀ (by positivity)]
      calc Real.exp t ≤ Real.exp (y/2) := by apply Real.exp_le_exp.mpr hty
        _ = Real.exp (y/2) * 1 := by ring
        _ ≤ Real.exp (y/2) * t^2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [ht1]
    rw [intervalIntegral.integral_const] at hb1
    have : (y/2 - 1) • Real.exp (y/2) ≤ y * Real.exp (y/2) := by
      rw [smul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    linarith [hb1, this]
  · have hb2 : (∫ t in (y/2)..y, Real.exp t / t^2)
        ≤ ∫ t in (y/2)..y, (4/y^2) * Real.exp t := by
      apply intervalIntegral.integral_mono_on hhalfy
        (int_exp_div_sq (by linarith : (0:ℝ) < y/2) hy0)
      · apply ContinuousOn.intervalIntegrable; fun_prop
      · intro t ht
        have ht1 : y/2 ≤ t := ht.1
        rw [div_le_iff₀ (by nlinarith [ht1] : (0:ℝ) < t^2)]
        rw [mul_comm (4/y^2) _, mul_assoc]
        have hge : (1:ℝ) ≤ 4 / y^2 * t^2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith [ht1]
        nlinarith [Real.exp_pos t, hge, mul_le_mul_of_nonneg_left hge (le_of_lt (Real.exp_pos t))]
    rw [intervalIntegral.integral_const_mul] at hb2
    have hb3 : (∫ t in (y/2)..y, Real.exp t) ≤ Real.exp y := by
      rw [integral_exp]
      have : Real.exp (y/2) ≥ 0 := le_of_lt (Real.exp_pos _)
      linarith [this]
    calc (∫ t in (y/2)..y, Real.exp t / t^2)
        ≤ (4/y^2) * ∫ t in (y/2)..y, Real.exp t := hb2
      _ ≤ (4/y^2) * Real.exp y := by
          apply mul_le_mul_of_nonneg_left hb3 (by positivity)

private theorem tail_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ ∫ t in (1:ℝ)..y, Real.exp t / t^2 := by
  apply intervalIntegral.integral_nonneg hy
  intro t ht
  have : 0 < t := by linarith [ht.1]
  positivity

/-- Tail term `(∫₁^y e^t/t²)·y·e^{-y} → 0`. -/
private theorem tail_term_tendsto :
    Tendsto (fun y : ℝ => (∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun y : ℝ => y^2 * Real.exp (-(y/2)) + 4 / y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => y^2 * Real.exp (-(y/2))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/2) (by norm_num)
      refine h.congr' ?_
      filter_upwards with y
      rw [show -(1/2 : ℝ) * y = -(y/2) from by ring, Real.rpow_two, sq]
    have h2 : Tendsto (fun y : ℝ => 4 / y) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (4:ℝ))).div_atTop tendsto_id
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with y hy
    have hy1 : (1:ℝ) ≤ y := by linarith
    have := tail_nonneg hy1
    positivity
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with y hy
    have hy0 : (0:ℝ) < y := by linarith
    have htb := tail_bound hy
    have htn := tail_nonneg (by linarith : (1:ℝ) ≤ y)
    have hey : (0:ℝ) < Real.exp (-y) := Real.exp_pos _
    have hstep : (∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y)
        ≤ (y * Real.exp (y/2) + (4 / y^2) * Real.exp y) * y * Real.exp (-y) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hey)
      apply mul_le_mul_of_nonneg_right htb (le_of_lt hy0)
    refine hstep.trans (le_of_eq ?_)
    have he1 : Real.exp (y/2) * Real.exp (-y) = Real.exp (-(y/2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have he2 : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]; simp
    have hyne : y ≠ 0 := ne_of_gt hy0
    calc (y * Real.exp (y/2) + (4 / y^2) * Real.exp y) * y * Real.exp (-y)
        = y^2 * (Real.exp (y/2) * Real.exp (-y))
          + (4 / y^2) * y * (Real.exp y * Real.exp (-y)) := by ring
      _ = y^2 * Real.exp (-(y/2)) + (4 / y^2) * y * 1 := by rw [he1, he2]
      _ = y^2 * Real.exp (-(y/2)) + 4 / y := by rw [mul_one]; field_simp

/-- Large-argument asymptotic of `Ei`: `Ei y · y · e^{-y} → 1` as `y → ∞`
(the exponential-integral form of DLMF 6.12.2, obtained termwise from the
`Ei = γ + log|·| + eiSeries` definition by FTC + one integration by parts).

DLMF 6.12.2.
Fidelity: tier1 PASS
Verified: unverified
DAG: E-6.12.2.
-/
theorem Ei_large_asymptotic :
    Tendsto (fun y : ℝ => Def.Ei y * y * Real.exp (-y)) atTop (𝓝 1) := by
  have hdecomp : ∀ᶠ y in atTop,
      Def.Ei y * y * Real.exp (-y)
        = 1 + (Def.Ei 1 - Real.exp 1) * y * Real.exp (-y)
          + (∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y) := by
    filter_upwards [eventually_ge_atTop (2:ℝ)] with y hy
    have hy1 : (1:ℝ) ≤ y := by linarith
    have hy0 : (0:ℝ) < y := by linarith
    have hsub := Ei_sub_integral hy1
    have hibp := ibp_identity hy1
    have hEi : Def.Ei y = Def.Ei 1 + Real.exp y / y - Real.exp 1
        + ∫ t in (1:ℝ)..y, Real.exp t / t^2 := by
      have : Def.Ei y = Def.Ei 1 + ∫ t in (1:ℝ)..y, Real.exp t / t := by linarith [hsub]
      rw [this, hibp]; ring
    rw [hEi]
    have hey : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have hyne : y ≠ 0 := ne_of_gt hy0
    have hmid : (Real.exp y / y) * y * Real.exp (-y) = 1 := by
      rw [div_mul_cancel₀ _ hyne, hey]
    calc (Def.Ei 1 + Real.exp y / y - Real.exp 1
            + ∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y)
        = (Real.exp y / y) * y * Real.exp (-y)
          + (Def.Ei 1 - Real.exp 1) * y * Real.exp (-y)
          + (∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y) := by ring
      _ = 1 + (Def.Ei 1 - Real.exp 1) * y * Real.exp (-y)
          + (∫ t in (1:ℝ)..y, Real.exp t / t^2) * y * Real.exp (-y) := by rw [hmid]
  refine Tendsto.congr' (Filter.EventuallyEq.symm hdecomp) ?_
  have hconst : Tendsto (fun y : ℝ => (Def.Ei 1 - Real.exp 1) * y * Real.exp (-y))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have := (tendsto_const_nhds (x := Def.Ei 1 - Real.exp 1)).mul hbase
    simpa [mul_assoc] using this
  have := (tendsto_const_nhds (x := (1:ℝ))).add hconst |>.add tail_term_tendsto
  simpa using this

-- no-dlmf: DLMF has no display for the `li` asymptotics — 6.12.2 is the Poincaré
-- expansion of `Ei(x)`, and §6.12(i) only remarks in prose that "the asymptotic
-- expansion of li(x) as x → ∞ is obtainable from (6.2.8) and (6.12.2)".  This is
-- the leading-order (`li(x) ~ x/ln x`) consequence of that remark.
/-- The prime-counting envelope `li(x) ~ x/ln x`
for the canonical logarithmic integral `li = Ei ∘ log`, in the precise sense that
`li(x) · (ln x) / x → 1` as `x → ∞`.  (Reduces to `liW_asymptotic` together with the
asymptotic equivalence `li(x)/liW(x) → 1` of `li` with its `E₁`-based Watson proxy.)
-/
theorem li_asymptotic :
    Tendsto (fun x : ℝ => Def.li x * Real.log x / x) atTop (𝓝 1) := by
  have hcomp := Ei_large_asymptotic.comp Real.tendsto_log_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  simp only [Function.comp_apply, Def.li_def]
  rw [Real.exp_neg, Real.exp_log hx0, div_eq_mul_inv]
