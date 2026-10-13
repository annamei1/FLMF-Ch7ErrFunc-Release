import FLMF.Frameworks.Hypergeometric.TricomiODE
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Kummer's equation for Tricomi's `U` (framework — DLMF 13.2.1)

`U(a;b;z)` is the recessive (second) solution of Kummer's confluent
hypergeometric equation:

* `tricomiU_contiguous` — the contiguous relation
  `z(a+1)·U(a+2;b+2;z) = (b−z)·U(a+1;b+1;z) + U(a;b;z)` (DLMF 13.3.x).
* `tricomiU_kummerODE` — **Kummer's equation** (DLMF 13.2.1):
  `z·U''(a;b;z) + (b−z)·U'(a;b;z) − a·U(a;b;z) = 0`, for `a > 0`, `z > 0`.

The contiguous relation is the analytic heart: the combination
`z t^{a+1} − (b−z) t^a − a t^{a−1}`, weighted by `e^{−zt}(1+t)^{b−a−1}`, is
exactly `−g'(t)` for `g(t) = e^{−zt} t^a (1+t)^{b−a}`. Since `g` vanishes at both
ends (`t^a → 0` at `0` as `a > 0`; exponential decay at `∞`), the FTC gives
`∫₀^∞ g' = 0`, and the three pieces reassemble (through `Γ(a+2) = (a+1)aΓ(a)`)
into the contiguous relation. Kummer's equation then follows by applying the
derivative `U'(a;b;z) = −a U(a+1;b+1;z)` (DLMF 13.3.22) twice.
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace FLMF.Hypergeometric

/-- `∫₀^∞ tricomiIntegrand a b z = Γ(a)·U(a;b;z)` for `a > 0` (clearing the
`Γ(a)⁻¹` normalization in the definition of `U`). -/
-- no-dlmf: normalization-clearing helper, no DLMF counterpart
theorem integral_tricomiIntegrand {a b z : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t) = Real.Gamma a * tricomiU a b z := by
  rw [tricomiU, ← mul_assoc, mul_inv_cancel₀ (Real.Gamma_pos_of_pos ha).ne', one_mul]

section Contiguous

variable {a b z : ℝ}

/-- The "potential" `g(t) = e^{−zt} t^a (1+t)^{b−a}` whose derivative drives the
contiguous relation. -/
-- no-dlmf: auxiliary potential for the contiguous-relation proof, no DLMF counterpart
private def gPot (a b z t : ℝ) : ℝ := Real.exp (-z * t) * t ^ a * (1 + t) ^ (b - a)

/-- The derivative combination: `g'(t)` expressed in the Tricomi-integrand
basis. -/
-- no-dlmf: derivative combination for the contiguous-relation proof, no DLMF counterpart
private def gDer (a b z t : ℝ) : ℝ :=
  -z * tricomiIntegrand (a + 2) (b + 2) z t
    + (b - z) * tricomiIntegrand (a + 1) (b + 1) z t
    + a * tricomiIntegrand a b z t

-- no-dlmf: boundary value of the auxiliary potential, no DLMF counterpart
private theorem gPot_zero (a b z : ℝ) (ha : 0 < a) : gPot a b z 0 = 0 := by
  simp [gPot, Real.zero_rpow ha.ne']

-- no-dlmf: derivative of the auxiliary potential, no DLMF counterpart
private theorem gPot_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => gPot a b z t) (gDer a b z t) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * t)) (-z * Real.exp (-z * t)) t := by
    have hinner : HasDerivAt (fun t : ℝ => -z * t) (-z) t := by
      simpa using (hasDerivAt_id t).const_mul (-z)
    simpa [mul_comm] using hinner.exp
  have hta : HasDerivAt (fun t : ℝ => t ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have htb : HasDerivAt (fun t : ℝ => (1 + t) ^ (b - a)) ((b - a) * (1 + t) ^ (b - a - 1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := b - a) (Or.inl h1t.ne')).comp t
      ((hasDerivAt_const t 1).add (hasDerivAt_id t))
    simpa using this
  have hmul := (hexp.mul hta).mul htb
  -- rewrite the product-rule derivative into the integrand basis
  refine hmul.congr_deriv ?_
  -- algebra: factor `e^{−zt} t^{a−1}(1+t)^{b−a−1}` out and match the cubic in `t`
  have hB : t ^ a = t * t ^ (a - 1) := by
    have key : t ^ ((a - 1) + 1) = t * t ^ (a - 1) := by
      rw [Real.rpow_add ht, Real.rpow_one, mul_comm]
    rwa [show (a - 1) + 1 = a by ring] at key
  have hA : (1 + t) ^ (b - a) = (1 + t) * (1 + t) ^ (b - a - 1) := by
    have key : (1 + t) ^ ((b - a - 1) + 1) = (1 + t) * (1 + t) ^ (b - a - 1) := by
      rw [Real.rpow_add h1t, Real.rpow_one, mul_comm]
    rwa [show (b - a - 1) + 1 = b - a by ring] at key
  have hC : t ^ (a + 1) = t * (t * t ^ (a - 1)) := by
    rw [← hB, show a + 1 = 1 + a by ring, Real.rpow_add ht, Real.rpow_one]
  simp only [gDer, tricomiIntegrand, Pi.mul_apply]
  rw [show a + 2 - 1 = a + 1 by ring, show b + 2 - (a + 2) - 1 = b - a - 1 by ring,
    show a + 1 - 1 = a by ring, show b + 1 - (a + 1) - 1 = b - a - 1 by ring,
    hC, hA, hB]
  ring

-- no-dlmf: continuity of the auxiliary potential, no DLMF counterpart
private theorem gPot_continuousWithinAt (ha : 0 < a) :
    ContinuousWithinAt (fun t => gPot a b z t) (Ici 0) 0 := by
  apply ContinuousWithinAt.mul
  apply ContinuousWithinAt.mul
  · exact ((continuous_const.mul continuous_id).rexp).continuousWithinAt
  · exact (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).continuousWithinAt
  · have : ContinuousAt (fun t : ℝ => (1 + t) ^ (b - a)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left; norm_num
    exact this.continuousWithinAt

-- no-dlmf: decay of the auxiliary potential at +∞, no DLMF counterpart
private theorem gPot_tendsto_zero (hz : 0 < z) :
    Tendsto (fun t => gPot a b z t) atTop (𝓝 0) := by
  set C : ℝ := max ((2 : ℝ) ^ (b - a)) 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hub : Tendsto (fun t : ℝ => C * (t ^ b * Real.exp (-z * t))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b z hz).const_mul C
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h1t : (0 : ℝ) < 1 + t := by linarith
    simp only [gPot]
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hpow : (1 + t) ^ (b - a) ≤ C * t ^ (b - a) := by
      rcases le_or_gt 0 (b - a) with hexp | hexp
      · calc (1 + t) ^ (b - a) ≤ (2 * t) ^ (b - a) :=
              Real.rpow_le_rpow (by linarith) (by linarith) hexp
          _ = (2 : ℝ) ^ (b - a) * t ^ (b - a) := Real.mul_rpow (by norm_num) htpos.le
          _ ≤ C * t ^ (b - a) := by gcongr; exact le_max_left _ _
      · calc (1 + t) ^ (b - a) ≤ t ^ (b - a) :=
              Real.rpow_le_rpow_of_nonpos htpos (by linarith) hexp.le
          _ ≤ C * t ^ (b - a) :=
              le_mul_of_one_le_left (Real.rpow_nonneg htpos.le _) (le_max_right _ _)
    have htab : t ^ a * t ^ (b - a) = t ^ b := by rw [← Real.rpow_add htpos]; ring_nf
    calc gPot a b z t
        = Real.exp (-z * t) * t ^ a * (1 + t) ^ (b - a) := rfl
      _ ≤ Real.exp (-z * t) * t ^ a * (C * t ^ (b - a)) := by gcongr
      _ = C * (t ^ b * Real.exp (-z * t)) := by
          rw [show Real.exp (-z * t) * t ^ a * (C * t ^ (b - a))
            = C * ((t ^ a * t ^ (b - a)) * Real.exp (-z * t)) by ring, htab]

-- no-dlmf: integrability of the derivative combination, no DLMF counterpart
private theorem gDer_integrableOn (ha : 0 < a) (hz : 0 < z) :
    IntegrableOn (fun t => gDer a b z t) (Ioi 0) := by
  have h0 := tricomiU_integrand_integrableOn (a := a) (b := b) ha hz
  have h1 := tricomiU_integrand_integrableOn (a := a + 1) (b := b + 1) (by linarith) hz
  have h2 := tricomiU_integrand_integrableOn (a := a + 2) (b := b + 2) (by linarith) hz
  unfold gDer
  exact ((h2.const_mul (-z)).add (h1.const_mul (b - z))).add (h0.const_mul a)

/-- **Contiguous relation** for `U` (DLMF 13.3.x):
`z(a+1)·U(a+2;b+2;z) = (b−z)·U(a+1;b+1;z) + U(a;b;z)`, for `a > 0`, `z > 0`.

DAG: E-13.3.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem tricomiU_contiguous (ha : 0 < a) (hz : 0 < z) :
    z * (a + 1) * tricomiU (a + 2) (b + 2) z
      = (b - z) * tricomiU (a + 1) (b + 1) z + tricomiU a b z := by
  -- the integral of `g'` over `(0,∞)` is `0 − g(0) = 0`
  have hFTC : (∫ t in Ioi (0 : ℝ), gDer a b z t) = 0 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (gPot_continuousWithinAt ha)
      (fun t ht => gPot_hasDerivAt ht) (gDer_integrableOn ha hz) (gPot_tendsto_zero hz),
      gPot_zero a b z ha, sub_zero]
  -- split the integral into the three Tricomi integrals
  have h0 := tricomiU_integrand_integrableOn (a := a) (b := b) ha hz
  have h1 := tricomiU_integrand_integrableOn (a := a + 1) (b := b + 1) (by linarith) hz
  have h2 := tricomiU_integrand_integrableOn (a := a + 2) (b := b + 2) (by linarith) hz
  have hf2 : Integrable (fun t => -z * tricomiIntegrand (a + 2) (b + 2) z t)
      (volume.restrict (Ioi 0)) := h2.const_mul (-z)
  have hf1 : Integrable (fun t => (b - z) * tricomiIntegrand (a + 1) (b + 1) z t)
      (volume.restrict (Ioi 0)) := h1.const_mul (b - z)
  have hf0 : Integrable (fun t => a * tricomiIntegrand a b z t)
      (volume.restrict (Ioi 0)) := h0.const_mul a
  have hf21 : Integrable (fun t => -z * tricomiIntegrand (a + 2) (b + 2) z t
      + (b - z) * tricomiIntegrand (a + 1) (b + 1) z t) (volume.restrict (Ioi 0)) := hf2.add hf1
  have hsplit : (∫ t in Ioi (0 : ℝ), gDer a b z t)
      = -z * (∫ t in Ioi (0 : ℝ), tricomiIntegrand (a + 2) (b + 2) z t)
        + (b - z) * (∫ t in Ioi (0 : ℝ), tricomiIntegrand (a + 1) (b + 1) z t)
        + a * (∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t) := by
    unfold gDer
    rw [integral_add hf21 hf0, integral_add hf2 hf1,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsplit, integral_tricomiIntegrand (by linarith : (0:ℝ) < a + 2),
    integral_tricomiIntegrand (by linarith : (0:ℝ) < a + 1),
    integral_tricomiIntegrand ha] at hFTC
  -- collapse the Γ-factors: Γ(a+2) = (a+1)aΓ(a), Γ(a+1) = aΓ(a)
  have hΓ2 : Real.Gamma (a + 2) = (a + 1) * (a * Real.Gamma a) := by
    rw [show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one (by linarith),
      Real.Gamma_add_one ha.ne']
  have hΓ1 : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha.ne'
  rw [hΓ2, hΓ1] at hFTC
  have hΓa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  -- divide through by `a·Γ(a) > 0`
  have key : a * Real.Gamma a *
      (z * (a + 1) * tricomiU (a + 2) (b + 2) z
        - ((b - z) * tricomiU (a + 1) (b + 1) z + tricomiU a b z)) = 0 := by
    linear_combination -hFTC
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (by positivity)
  · linarith [sub_eq_zero.1 h]

end Contiguous

-- no-dlmf: instance of DLMF 13.2.1 (the unknown `w` fixed to `tricomiU a b`,
-- plus the real-axis restriction `a > 0, z > 0` needed by this file's
-- integral-representation definition of `tricomiU`); the faithful surface of
-- the bare equation is the `IsKummerSolution` definition in
-- `FLMF.Frameworks.Hypergeometric.KummerODE` (the same anchor `kummerM_ode`
-- uses for the `M`-branch instance).
/-- **Kummer's equation for `U`**: the Tricomi function is the
recessive solution of `z·w'' + (b−z)·w' − a·w = 0`, for `a > 0`, `z > 0`. -/
theorem tricomiU_kummerODE {a b z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    z * deriv (deriv (fun z => tricomiU a b z)) z
      + (b - z) * deriv (fun z => tricomiU a b z) z - a * tricomiU a b z = 0 := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  -- first derivative (DLMF 13.3.22)
  have hd1 : deriv (fun z => tricomiU a b z) z = -a * tricomiU (a + 1) (b + 1) z :=
    tricomiU_deriv ha hz
  -- `deriv U` agrees with `z ↦ −a U(a+1;b+1;z)` on a neighbourhood of `z`
  have hd1eq : deriv (fun z => tricomiU a b z)
      =ᶠ[𝓝 z] fun z' => -a * tricomiU (a + 1) (b + 1) z' := by
    filter_upwards [Ioi_mem_nhds hz] with z' hz'
    exact tricomiU_deriv ha hz'
  -- second derivative
  have hd2 : deriv (deriv (fun z => tricomiU a b z)) z
      = a * (a + 1) * tricomiU (a + 1 + 1) (b + 1 + 1) z := by
    rw [hd1eq.deriv_eq,
      deriv_const_mul _ (tricomiU_hasDerivAt ha1 hz).differentiableAt,
      tricomiU_deriv ha1 hz]
    ring
  rw [hd1, hd2, show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring]
  -- substitute the contiguous relation
  linear_combination a * tricomiU_contiguous (a := a) (b := b) ha hz

end FLMF.Hypergeometric
