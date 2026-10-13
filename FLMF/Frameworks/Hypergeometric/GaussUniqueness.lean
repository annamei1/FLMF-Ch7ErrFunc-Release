import FLMF.Frameworks.Hypergeometric.GaussODE
import FLMF.Methods.BranchAlgebra

/-!
# Regular-singular uniqueness at `0` for the Gauss equation (M-2f1-quadratic-cubic core)

The uniqueness half of the Frobenius theory at the regular singular point `z = 0`
of the hypergeometric equation, for `c` off the nonpositive integers: **any**
function analytic on a disc `|z| < r ≤ 1` that solves

`z(1−z)·w'' + (c − (a+b+1)z)·w' − ab·w = 0`

with the normalization `w 0 = 1` **equals** `₂F₁ a b c` on the disc
(`eqOn_ordinaryHypergeometric_of_solvesGaussODE`).  The proof extracts the
hypergeometric coefficient recurrence `(n+1)(n+c)·αₙ₊₁ = (n+a)(n+b)·αₙ` from the
Taylor coefficients of `w` (the ODE forces the combined power series to vanish
identically), identifies them inductively with `ordinaryHypergeometricCoefficient`,
and extends the resulting local identity by the identity theorem.

This is the algebraic-evaluation engine of the `M-2f1-quadratic-cubic` method:
the quadratic/cubic transformations and composition special cases of DLMF
§15.4/§15.8 are proven by checking that the (algebraically explicit) right-hand
side solves the Gauss ODE and is normalized at `0`.

Supporting kit (reusable):

* `ordinaryHypergeometric_hasSum_of_c` / `_hasFPowerSeriesOnBall_of_c` /
  `analyticOnNhd_ordinaryHypergeometric_of_c` — the Gauss series on the unit
  ball assuming only `c ∉ ℤ≤0` (terminating numerator parameters allowed).
* `hasFPowerSeriesOnBall_deriv_scalar` — the one-dimensional derivative power
  series with scalar coefficients `(n+1)·p.coeff (n+1)`.
* `hasSum_coeff_mul_of_hasFPowerSeriesOnBall` — scalar `HasSum` extraction.
* `coeff_eq_zero_of_hasSum_zero` — a scalar power series vanishing on a disc
  has zero coefficients.
-/

open Nat FormalMultilinearSeries
open scoped ENNReal NNReal

namespace FLMF.Hypergeometric

/-- The Gauss series has radius at least `1` as soon as `c` is off the
nonpositive integers: if neither numerator parameter is a nonpositive integer
the radius is exactly `1` (`ordinaryHypergeometricSeries_radius_eq_one`), and
otherwise the series terminates and the radius is `⊤`. -/
-- no-dlmf: radius bookkeeping for the series (the series is DLMF 15.2.1)
theorem one_le_radius_ordinaryHypergeometricSeries_of_c {𝕂 : Type*} [RCLike 𝕂] (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) :
    1 ≤ (ordinaryHypergeometricSeries 𝕂 a b c).radius := by
  by_cases habc : ∀ kn : ℕ, (kn : 𝕂) ≠ -a ∧ (kn : 𝕂) ≠ -b ∧ (kn : 𝕂) ≠ -c
  · exact le_of_eq (ordinaryHypergeometricSeries_radius_eq_one 𝕂 a b c habc).symm
  · simp only [not_forall, not_and_or, not_ne_iff] at habc
    obtain ⟨k, hk⟩ := habc
    rcases hk with h | h | h
    · have ha : a = -(k : 𝕂) := by rw [h, neg_neg]
      rw [ha, ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    · have hb : b = -(k : 𝕂) := by rw [h, neg_neg]
      rw [hb, ordinaryHypergeometric_radius_top_of_neg_nat₂]
      exact le_top
    · exact absurd h (hc k)

-- `ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c` (the c-only power-series
-- statement, DLMF 15.2.1) now lives upstream in GaussODE.lean — the identical
-- local copy that used to sit here was removed when the upstream surface was
-- added (same name; the two collided at import).

/-- `HasSum` form of the Gauss series on the unit ball, assuming only that `c`
is off the nonpositive integers.  Unlike `ordinaryHypergeometric_hasSum`, the
parameters `a`, `b` are unrestricted: if one of them is a nonpositive integer
the series terminates and still converges. -/
-- no-dlmf: HasSum repackaging of the series (the series is DLMF 15.2.1)
theorem ordinaryHypergeometric_hasSum_of_c {𝕂 : Type*} [RCLike 𝕂] (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n * x ^ n) (₂F₁ a b c x) := by
  have h := (ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c a b c hc).hasSum_sub (y := x)
    (by rw [mem_eball_zero_iff, ← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hx)
  simpa only [sub_zero, ordinaryHypergeometricSeries_apply_eq, smul_eq_mul] using h

/-- The Gauss function is analytic on the open unit ball as soon as `c` is off
the nonpositive integers. -/
-- no-dlmf: analyticity repackaging of the series (the series is DLMF 15.2.1)
theorem analyticOnNhd_ordinaryHypergeometric_of_c (a b c : ℂ)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    AnalyticOnNhd ℂ (₂F₁ a b c : ℂ → ℂ) (Metric.ball 0 1) := by
  refine (ordinaryHypergeometric_hasFPowerSeriesOnBall_of_c a b c hc).analyticOnNhd.mono ?_
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact ENNReal.ofReal_lt_one.mpr hx

/-- If `f` is the sum of the power series `p` on a ball centred at `0`, then
`deriv f` is the sum of a power series on the same ball whose scalar
coefficients are `(n+1)·p.coeff (n+1)`. -/
-- no-dlmf: one-dimensional derivative-series infrastructure
theorem hasFPowerSeriesOnBall_deriv_scalar {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p 0 r) :
    ∃ q : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesOnBall (deriv f) q 0 r ∧
      ∀ n : ℕ, q.coeff n = ((n : ℂ) + 1) * p.coeff (n + 1) := by
  refine ⟨(ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries,
    ?_, ?_⟩
  · have hf := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv
    have he : (⇑(ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) ∘ fderiv ℂ f) = deriv f := by
      funext z
      exact fderiv_apply_one_eq_deriv
    rwa [he] at hf
  · intro n
    have h1 : ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        p.derivSeries).coeff n = (p.derivSeries.coeff n) 1 := by
      simp only [FormalMultilinearSeries.coeff,
        ContinuousLinearMap.compFormalMultilinearSeries_apply,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousLinearMap.apply_apply]
    rw [h1, FormalMultilinearSeries.derivSeries_coeff_one]
    push_cast [nsmul_eq_mul]
    ring

/-- Scalar `HasSum` extraction from a power-series representation on a ball at `0`. -/
-- no-dlmf: scalar power-series infrastructure
theorem hasSum_coeff_mul_of_hasFPowerSeriesOnBall {f : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f q 0 r) {x : ℂ} (hx : (‖x‖₊ : ℝ≥0∞) < r) :
    HasSum (fun n : ℕ => q.coeff n * x ^ n) (f x) := by
  have hmem : x ∈ Metric.eball (0 : ℂ) r := by
    rwa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
  have hs := h.hasSum_sub hmem
  simp only [sub_zero] at hs
  refine hs.congr_fun fun n => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
  ring

/-- A scalar power series summing to `0` at every point of a real disc around `0`
has all coefficients zero. -/
-- no-dlmf: scalar power-series uniqueness infrastructure
theorem coeff_eq_zero_of_hasSum_zero {β : ℕ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ x : ℂ, ‖x‖ < ρ → HasSum (fun n : ℕ => β n * x ^ n) 0) :
    ∀ n : ℕ, β n = 0 := by
  have h2 : 0 < ρ / 2 := by linarith
  set σ : ℝ≥0 := ⟨ρ / 2, h2.le⟩ with hσdef
  have hcoe : (σ : ℝ) = ρ / 2 := rfl
  have hnorm : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg h2.le]
    linarith
  have hsum0 : Summable (fun n : ℕ => β n * ((ρ / 2 : ℝ) : ℂ) ^ n) := (h _ hnorm).summable
  have hrad : (σ : ℝ≥0∞) ≤ (ofScalars ℂ β).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    have hs : Summable (fun n : ℕ => ‖β n * ((ρ / 2 : ℝ) : ℂ) ^ n‖) :=
      summable_norm_iff.mpr hsum0
    refine hs.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg h2.le, hcoe]
  have hσ0 : (0 : ℝ≥0∞) < (σ : ℝ≥0∞) := by
    rw [ENNReal.coe_pos]
    exact_mod_cast h2
  have hball : HasFPowerSeriesOnBall (0 : ℂ → ℂ) (ofScalars ℂ β) 0 (σ : ℝ≥0∞) := by
    refine ⟨hrad, hσ0, ?_⟩
    intro y hy
    have hyn : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm] at hy
      have hlt : ‖y‖₊ < σ := by exact_mod_cast hy
      have : ‖y‖ < (σ : ℝ) := hlt
      rw [hcoe] at this
      linarith
    have hsy := h y hyn
    simp only [Pi.zero_apply]
    refine hsy.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  intro n
  have hzero := hball.hasFPowerSeriesAt.eq_zero
  calc β n = (ofScalars ℂ β).coeff n := (FormalMultilinearSeries.coeff_ofScalars).symm
    _ = 0 := by rw [hzero]; simp [FormalMultilinearSeries.coeff]

/-- **Regular-singular uniqueness at `0` for the Gauss equation** (the
`M-2f1-quadratic-cubic` engine): a function analytic on the disc `|z| < r ≤ 1`
solving the hypergeometric equation there with `w 0 = 1`, for `c` off the
nonpositive integers, is `₂F₁ a b c` on the whole disc.  The ODE forces the
Taylor coefficients of `w` into the hypergeometric recurrence
`(n+1)(n+c)·αₙ₊₁ = (n+a)(n+b)·αₙ`, which pins them to
`ordinaryHypergeometricCoefficient`; the identity theorem globalizes. -/
-- no-dlmf: Frobenius-uniqueness engine (method core, DLMF §15.10(i) apparatus)
theorem eqOn_ordinaryHypergeometric_of_solvesGaussODE (a b c : ℂ)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {w : ℂ → ℂ}
    (hw : AnalyticOnNhd ℂ w (Metric.ball 0 r))
    (hw0 : w 0 = 1)
    (hode : ∀ z ∈ Metric.ball (0 : ℂ) r,
      z * (1 - z) * deriv (deriv w) z + (c - (a + b + 1) * z) * deriv w z - a * b * w z = 0) :
    Set.EqOn w (₂F₁ a b c) (Metric.ball 0 r) := by
  classical
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr0
  obtain ⟨p, hp⟩ := hw 0 h0mem
  obtain ⟨r₁, hball₁⟩ := hp
  set ε : ℝ≥0∞ := min (ENNReal.ofReal r) r₁ with hεdef
  have hε0 : 0 < ε := lt_min (by simpa using hr0) hball₁.r_pos
  have hB : HasFPowerSeriesOnBall w p 0 ε := hball₁.mono hε0 (min_le_right _ _)
  obtain ⟨ρ, hρ0', hρ1, hρ2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε0
  have hρ0 : 0 < ρ := ENNReal.ofReal_pos.mp hρ1
  have hmemε : ∀ {x : ℂ}, ‖x‖ < ρ → (‖x‖₊ : ℝ≥0∞) < ε := by
    intro x hx
    have h1 : (‖x‖₊ : ℝ≥0∞) < ENNReal.ofReal ρ := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ0).mpr hx
    exact lt_trans h1 hρ2
  have hρr : ρ ≤ r := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : ENNReal.ofReal r < ENNReal.ofReal ρ :=
      (ENNReal.ofReal_lt_ofReal_iff hρ0).mpr hcon
    have h2 : ENNReal.ofReal ρ ≤ ENNReal.ofReal r := le_trans hρ2.le (min_le_left _ _)
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  -- power series of the first and second derivatives
  obtain ⟨q₁, hq₁ball, hq₁c⟩ := hasFPowerSeriesOnBall_deriv_scalar hB
  obtain ⟨q₂, hq₂ball, hq₂c⟩ := hasFPowerSeriesOnBall_deriv_scalar hq₁ball
  set α : ℕ → ℂ := fun n => p.coeff n with hαdef
  set β : ℕ → ℂ := fun n =>
    ((n : ℂ) + 1) * ((n : ℂ) + c) * α (n + 1) - ((n : ℂ) + a) * ((n : ℂ) + b) * α n with hβdef
  -- the ODE kills the combined series at every point of the small disc
  have hβsum : ∀ x : ℂ, ‖x‖ < ρ → HasSum (fun n : ℕ => β n * x ^ n) 0 := by
    intro x hx
    have hxε := hmemε hx
    have hxr : x ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hx hρr
    have S0 : HasSum (fun n : ℕ => α n * x ^ n) (w x) :=
      hasSum_coeff_mul_of_hasFPowerSeriesOnBall hB hxε
    have S1 : HasSum (fun n : ℕ => ((n : ℂ) + 1) * α (n + 1) * x ^ n) (deriv w x) := by
      have h := hasSum_coeff_mul_of_hasFPowerSeriesOnBall hq₁ball hxε
      refine h.congr_fun fun n => ?_
      rw [hq₁c n]
    have S2 : HasSum (fun n : ℕ => ((n : ℂ) + 1) * ((n : ℂ) + 2) * α (n + 2) * x ^ n)
        (deriv (deriv w) x) := by
      have h := hasSum_coeff_mul_of_hasFPowerSeriesOnBall hq₂ball hxε
      refine h.congr_fun fun n => ?_
      rw [hq₂c n, hq₁c (n + 1)]
      push_cast
      ring
    have hxw2 : HasSum (fun n : ℕ => (n : ℂ) * ((n : ℂ) + 1) * α (n + 1) * x ^ n)
        (x * deriv (deriv w) x) := by
      have h := S2.mul_left x
      have he : (fun n : ℕ => x * (((n : ℂ) + 1) * ((n : ℂ) + 2) * α (n + 2) * x ^ n)) =
          fun n : ℕ => (((n + 1 : ℕ) : ℂ)) * (((n + 1 : ℕ) : ℂ) + 1) * α ((n + 1) + 1)
            * x ^ (n + 1) := by
        funext n
        push_cast
        ring
      rw [he] at h
      have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℂ) * ((n : ℂ) + 1)
        * α (n + 1) * x ^ n) 1).mp h
      simpa using h2
    have hx2w2 : HasSum (fun n : ℕ => ((n : ℂ) - 1) * (n : ℂ) * α n * x ^ n)
        (x * (x * deriv (deriv w) x)) := by
      have h := (S2.mul_left x).mul_left x
      have he : (fun n : ℕ => x * (x * (((n : ℂ) + 1) * ((n : ℂ) + 2) * α (n + 2) * x ^ n))) =
          fun n : ℕ => (((n + 2 : ℕ) : ℂ) - 1) * ((n + 2 : ℕ) : ℂ) * α (n + 2)
            * x ^ (n + 2) := by
        funext n
        push_cast
        ring
      rw [he] at h
      have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => ((n : ℂ) - 1) * (n : ℂ)
        * α n * x ^ n) 2).mp h
      simpa [Finset.sum_range_succ] using h2
    have hxw1 : HasSum (fun n : ℕ => (n : ℂ) * α n * x ^ n) (x * deriv w x) := by
      have h := S1.mul_left x
      have he : (fun n : ℕ => x * (((n : ℂ) + 1) * α (n + 1) * x ^ n)) =
          fun n : ℕ => (((n + 1 : ℕ) : ℂ)) * α (n + 1) * x ^ (n + 1) := by
        funext n
        push_cast
        ring
      rw [he] at h
      have h2 := (hasSum_nat_add_iff (f := fun n : ℕ =>
        (n : ℂ) * α n * x ^ n) 1).mp h
      simpa using h2
    have hT := (((hxw2.sub hx2w2).add (S1.mul_left c)).sub
      (hxw1.mul_left (a + b + 1))).sub (S0.mul_left (a * b))
    have hval : (x * deriv (deriv w) x - x * (x * deriv (deriv w) x)
        + c * deriv w x - (a + b + 1) * (x * deriv w x) - a * b * w x) = 0 := by
      have hox := hode x hxr
      linear_combination hox
    rw [hval] at hT
    refine hT.congr_fun fun n => ?_
    simp only [hβdef]
    ring
  have hβ0 := coeff_eq_zero_of_hasSum_zero hρ0 hβsum
  -- coefficient identification with the hypergeometric coefficients
  have hα0 : α 0 = 1 := by
    have h := hB.coeff_zero (fun _ => (1 : ℂ))
    rw [hw0] at h
    exact h
  have hαγ : ∀ n : ℕ, α n = ordinaryHypergeometricCoefficient a b c n := by
    intro n
    induction n with
    | zero =>
      rw [hα0]
      simp [ordinaryHypergeometricCoefficient]
    | succ n ih =>
      have hrec := hβ0 n
      simp only [hβdef] at hrec
      have hγrec := ordinaryHypergeometricCoefficient_succ_mul a b c n hc
      have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have hnc : ((n : ℂ) + c) ≠ 0 := by
        intro h
        exact hc n (by linear_combination h)
      have hkey : ((n : ℂ) + 1) * ((n : ℂ) + c) * α (n + 1) =
          ((n : ℂ) + 1) * ((n : ℂ) + c) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
        rw [show ((n : ℂ) + 1) * ((n : ℂ) + c) * α (n + 1)
            = ((n : ℂ) + a) * ((n : ℂ) + b) * α n from by linear_combination hrec, ih]
        calc ((n : ℂ) + a) * ((n : ℂ) + b) * ordinaryHypergeometricCoefficient a b c n
            = (a + (n : ℂ)) * (b + (n : ℂ)) * ordinaryHypergeometricCoefficient a b c n := by
              ring
          _ = ((n : ℂ) + 1) * (c + (n : ℂ)) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
              rw [← hγrec]
          _ = ((n : ℂ) + 1) * ((n : ℂ) + c) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
              ring
      exact mul_left_cancel₀ (mul_ne_zero hn1 hnc) hkey
  -- local identity near 0
  have hloc : ∀ x : ℂ, ‖x‖ < ρ → w x = ₂F₁ a b c x := by
    intro x hx
    have S0 : HasSum (fun n : ℕ => α n * x ^ n) (w x) :=
      hasSum_coeff_mul_of_hasFPowerSeriesOnBall hB (hmemε hx)
    have SF : HasSum (fun n : ℕ => α n * x ^ n) (₂F₁ a b c x) := by
      have h := ordinaryHypergeometric_hasSum_of_c a b c hc
        (x := x) (lt_of_lt_of_le hx (le_trans hρr hr1))
      refine h.congr_fun fun n => ?_
      rw [hαγ n]
    exact S0.unique SF
  -- identity theorem on the disc
  have hFA : AnalyticOnNhd ℂ (₂F₁ a b c : ℂ → ℂ) (Metric.ball 0 r) := by
    refine (analyticOnNhd_ordinaryHypergeometric_of_c a b c hc).mono ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    exact lt_of_lt_of_le hx hr1
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) r) := (convex_ball (0 : ℂ) r).isPreconnected
  have hev : w =ᶠ[nhds (0 : ℂ)] (₂F₁ a b c : ℂ → ℂ) := by
    have hmem : Metric.ball (0 : ℂ) ρ ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 hρ0
    filter_upwards [hmem] with x hx
    exact hloc x (by rwa [Metric.mem_ball, dist_zero_right] at hx)
  exact hw.eqOn_of_preconnected_of_eventuallyEq hFA hpre h0mem hev

/-- Pointwise form of the uniqueness engine on the unit disc. -/
-- no-dlmf: convenience instance of the uniqueness engine
theorem ordinaryHypergeometric_eq_of_solvesGaussODE (a b c : ℂ)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) {w : ℂ → ℂ}
    (hw : AnalyticOnNhd ℂ w (Metric.ball 0 1))
    (hw0 : w 0 = 1)
    (hode : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      z * (1 - z) * deriv (deriv w) z + (c - (a + b + 1) * z) * deriv w z - a * b * w z = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a b c z = w z :=
  (eqOn_ordinaryHypergeometric_of_solvesGaussODE a b c hc zero_lt_one le_rfl hw hw0 hode
    (by rwa [Metric.mem_ball, dist_zero_right])).symm

end FLMF.Hypergeometric
