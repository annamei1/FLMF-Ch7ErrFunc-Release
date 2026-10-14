import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Tricomi's confluent hypergeometric function `U(a;b;z)` (framework — DLMF §13.4)

The second (recessive) solution of Kummer's equation, defined by its integral
representation (DLMF 13.4.4):

`U(a;b;z) = 1/Γ(a) · ∫₀^∞ e^{−zt} t^{a−1} (1+t)^{b−a−1} dt`,  for `a > 0`, `z > 0`.

We take the **real, positive-axis** form as primary (the integral is intrinsically
a real half-line object, and it is uniform in `b` — integer `b`, where the named
instances live, is no different from any other value). Junk value `0` outside
`a > 0 ∧ z > 0`. The connection formula DLMF 13.2.42 — valid only off the integer
`b` — is a *derived theorem* downstream, not the definition.

Main results:

* `tricomiU` — the function (real form).
* `tricomiU_integrand_integrableOn` — convergence of the defining integral for
  `a > 0`, `z > 0` (the analytic content): `t^{a−1}` integrable at `0`, the
  `e^{−zt}` factor beats the polynomial `(1+t)^{b−a−1}` growth at `∞`.
* `tricomiU_integrand_nonneg`, `tricomiU_nonneg` — positivity on the domain.
-/

noncomputable section

open MeasureTheory Real Set Filter Asymptotics
open scoped Topology

namespace FLMF.Hypergeometric

/-- The integrand of Tricomi's `U`: `t ↦ e^{−zt} t^{a−1} (1+t)^{b−a−1}`. -/
-- no-dlmf: integrand of the U integral representation (the rep is DLMF 13.4.4 below)
def tricomiIntegrand (a b z t : ℝ) : ℝ :=
  Real.exp (-z * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)

/-- **Tricomi's confluent hypergeometric function** `U(a;b;z)` (DLMF 13.4.4),
real form. Junk value `0` outside `a > 0 ∧ z > 0` (the integral diverges and
`∫` returns `0`). -/
-- DAG: E-13.4.4.
-- Verified: unverified
def tricomiU (a b z : ℝ) : ℝ :=
  (Real.Gamma a)⁻¹ * ∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t

/-- The Tricomi integrand is nonnegative for `t ≥ 0`. -/
-- no-dlmf: integrand nonnegativity, no DLMF counterpart
theorem tricomiIntegrand_nonneg (a b z : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ tricomiIntegrand a b z t := by
  unfold tricomiIntegrand
  have h1 : (0 : ℝ) ≤ Real.exp (-z * t) := (Real.exp_pos _).le
  have h2 : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht _
  have h3 : (0 : ℝ) ≤ (1 + t) ^ (b - a - 1) := Real.rpow_nonneg (by linarith) _
  positivity

/-- On `[1, ∞)` the integrand is bounded by `C · e^{−zt} t^{b−2}`, where
`C = max(2^{b−a−1}, 1)` absorbs the `(1+t)^{b−a−1}` factor (`t ≤ 1+t ≤ 2t`). -/
-- no-dlmf: integrand tail bound, no DLMF counterpart
theorem tricomiIntegrand_le {a b z : ℝ} {t : ℝ} (ht : 1 ≤ t) :
    tricomiIntegrand a b z t
      ≤ max ((2 : ℝ) ^ (b - a - 1)) 1 * (Real.exp (-z * t) * t ^ (b - 2)) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  set C : ℝ := max ((2 : ℝ) ^ (b - a - 1)) 1 with hC
  have hpow : (1 + t) ^ (b - a - 1) ≤ C * t ^ (b - a - 1) := by
    rcases le_or_gt 0 (b - a - 1) with hexp | hexp
    · calc (1 + t) ^ (b - a - 1) ≤ (2 * t) ^ (b - a - 1) :=
            Real.rpow_le_rpow (by linarith) (by linarith) hexp
        _ = (2 : ℝ) ^ (b - a - 1) * t ^ (b - a - 1) :=
            Real.mul_rpow (by norm_num) htpos.le
        _ ≤ C * t ^ (b - a - 1) := by
            gcongr
            exact le_max_left _ _
    · calc (1 + t) ^ (b - a - 1) ≤ t ^ (b - a - 1) :=
            Real.rpow_le_rpow_of_nonpos htpos (by linarith) hexp.le
        _ ≤ C * t ^ (b - a - 1) :=
            le_mul_of_one_le_left (Real.rpow_nonneg htpos.le _) (le_max_right _ _)
  have hsplit : t ^ (b - 2) = t ^ (a - 1) * t ^ (b - a - 1) := by
    rw [← Real.rpow_add htpos]
    ring_nf
  unfold tricomiIntegrand
  rw [hsplit]
  have he : (0 : ℝ) ≤ Real.exp (-z * t) := (Real.exp_pos _).le
  have hta : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg htpos.le _
  calc Real.exp (-z * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)
      ≤ Real.exp (-z * t) * t ^ (a - 1) * (C * t ^ (b - a - 1)) := by
        gcongr
    _ = C * (Real.exp (-z * t) * (t ^ (a - 1) * t ^ (b - a - 1))) := by ring

/-- Asymptotic control of the integrand at `+∞`: it is `O(e^{−(z/2) t})`. The
polynomial factors `t^{a−1}(1+t)^{b−a−1}` are dominated by the spare half of the
exponential decay. -/
-- no-dlmf: integrand decay estimate, no DLMF counterpart
theorem tricomiIntegrand_isBigO_exp {a b z : ℝ} (hz : 0 < z) :
    (fun t => tricomiIntegrand a b z t) =O[atTop] fun t => Real.exp (-(z / 2) * t) := by
  set C : ℝ := max ((2 : ℝ) ^ (b - a - 1)) 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the polynomial-times-exponential majorant is `o` of the slower exponential
  have hlittleO : (fun t : ℝ => C * (Real.exp (-z * t) * t ^ (b - 2)))
      =o[atTop] fun t : ℝ => Real.exp (-(z / 2) * t) := by
    refine Asymptotics.isLittleO_of_tendsto (fun t ht => absurd ht (Real.exp_pos _).ne') ?_
    have hquot : (fun t : ℝ => C * (Real.exp (-z * t) * t ^ (b - 2)) / Real.exp (-(z / 2) * t))
        = fun t : ℝ => C * (t ^ (b - 2) * Real.exp (-(z / 2) * t)) := by
      funext t
      have hh : Real.exp (-z * t) = Real.exp (-(z / 2) * t) * Real.exp (-(z / 2) * t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hh]
      have hne : Real.exp (-(z / 2) * t) ≠ 0 := Real.exp_ne_zero _
      rw [div_eq_iff hne]
      ring
    rw [hquot]
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b - 2) (z / 2)
      (by linarith)).const_mul C
    simpa using this
  -- the integrand is `O` of that majorant by the pointwise bound on `[1, ∞)`
  have hbig : (fun t : ℝ => tricomiIntegrand a b z t)
      =O[atTop] fun t : ℝ => C * (Real.exp (-z * t) * t ^ (b - 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hnn : 0 ≤ C * (Real.exp (-z * t) * t ^ (b - 2)) := by
      have : (0 : ℝ) ≤ t ^ (b - 2) := Real.rpow_nonneg (by linarith) _
      have he : (0 : ℝ) ≤ Real.exp (-z * t) := (Real.exp_pos _).le
      positivity
    rw [Real.norm_of_nonneg (tricomiIntegrand_nonneg a b z (by linarith)),
      Real.norm_of_nonneg hnn, one_mul]
    exact tricomiIntegrand_le ht
  exact hbig.trans hlittleO.isBigO

-- no-dlmf: well-definedness of the tricomiU defining integral; the 13.4.4 surface is the def tricomiU itself
/-- **Well-definedness of `tricomiU`'s defining integral**: for `a > 0` and
`z > 0`, `t ↦ e^{−zt} t^{a−1} (1+t)^{b−a−1}` — the integrand appearing in
`tricomiU`'s transcription of DLMF 13.4.4 — is integrable on `(0, ∞)`. -/
theorem tricomiU_integrand_integrableOn {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (fun t => tricomiIntegrand a b z t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  refine ⟨?_, ?_⟩
  · -- near `0`: the `t^{a−1}` singularity is integrable, the rest continuous
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    have hcont : ContinuousOn (fun t : ℝ => Real.exp (-z * t) * (1 + t) ^ (b - a - 1))
        (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.mul
      · exact (continuous_const.mul continuous_id).rexp.continuousOn
      · apply ContinuousOn.rpow_const
        · exact (continuous_const.add continuous_id).continuousOn
        · intro t ht
          left
          have : (0 : ℝ) ≤ t := ht.1
          positivity
    have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Icc (0 : ℝ) 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have := hint.continuousOn_mul hcont isCompact_Icc
    refine this.congr_fun (fun t ht => ?_) measurableSet_Icc
    unfold tricomiIntegrand
    ring
  · -- near `∞`: exponential decay beats polynomial growth
    refine integrable_of_isBigO_exp_neg (b := z / 2) (by linarith) ?_
      (tricomiIntegrand_isBigO_exp hz)
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    unfold tricomiIntegrand
    apply ContinuousWithinAt.mul
    apply ContinuousWithinAt.mul
    · exact ((continuous_const.mul continuous_id).rexp).continuousWithinAt
    · exact (continuousWithinAt_id.rpow_const (Or.inl htpos.ne'))
    · refine ContinuousWithinAt.rpow_const ?_ (Or.inl (by positivity))
      exact (continuous_const.add continuous_id).continuousWithinAt

-- no-dlmf: strictly-more-general total/junk-value form (real z ≤ 0 gives the
-- totalized junk value `0`, not the DLMF `|ph z| < π/2` domain); the faithful
-- DLMF 13.4.4 surface is tricomiU_nonneg_dlmf
/-- `U(a;b;z) ≥ 0` for `a > 0` (the integral representation has a nonnegative
integrand and `Γ(a) > 0`; off the convergence domain the junk value is `0 ≥ 0`). -/
theorem tricomiU_nonneg {a b z : ℝ} (ha : 0 < a) : 0 ≤ tricomiU a b z := by
  unfold tricomiU
  refine mul_nonneg (inv_nonneg.2 (Real.Gamma_pos_of_pos ha).le) ?_
  exact setIntegral_nonneg measurableSet_Ioi
    fun t ht => tricomiIntegrand_nonneg a b z (le_of_lt ht)

-- no-dlmf: positivity consequence of the DLMF 13.4.4 integral representation
-- (nonnegative integrand, Γ(a) > 0), not itself a numbered DLMF equation;
-- the tagged DLMF 13.4.4 carrier is the definition `tricomiU` above.
/-- `U(a;b;z) ≥ 0` on the real-axis instance of `|ph z| < π/2` (`z > 0`,
`a > 0`), a positivity consequence of the DLMF 13.4.4 integral representation. -/
theorem tricomiU_nonneg_dlmf {a b z : ℝ} (ha : 0 < a) (_hz : 0 < z) :
    0 ≤ tricomiU a b z := tricomiU_nonneg ha

/-- The Tricomi integrand is strictly positive for `t > 0`. -/
-- no-dlmf: integrand positivity, no DLMF counterpart
theorem tricomiIntegrand_pos (a b z : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < tricomiIntegrand a b z t := by
  unfold tricomiIntegrand
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _))
    (Real.rpow_pos_of_pos (by linarith) _)

/-- `U(a;b;z) > 0` on the convergence domain `a > 0`, `z > 0` (the integrand is
strictly positive on `(0,∞)` and `Γ(a) > 0`). -/
-- no-dlmf: positivity of U on its domain, no DLMF counterpart
theorem tricomiU_pos {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) : 0 < tricomiU a b z := by
  unfold tricomiU
  refine mul_pos (inv_pos.2 (Real.Gamma_pos_of_pos ha)) ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi
      fun t ht => (tricomiIntegrand_pos a b z ht).le)
    (tricomiU_integrand_integrableOn ha hz)]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun t => tricomiIntegrand a b z t) ∩ Ioi 0 :=
    fun t ht => ⟨ne_of_gt (tricomiIntegrand_pos a b z ht), ht⟩
  calc (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
    _ ≤ volume (Function.support (fun t => tricomiIntegrand a b z t) ∩ Ioi 0) := measure_mono hsub

end FLMF.Hypergeometric
