import FLMF.Support.HypergeometricTricomi
import FLMF.Support.Watson

/-!
# Leading recessive asymptotic of Tricomi's `U(a;b;z)` at infinity (DLMF §13.7.3)

The defining integral representation (DLMF 13.4.4)

`U(a;b;z) = 1/Γ(a) · ∫_{(0,∞)} e^{−z t} t^{a−1} (1+t)^{b−a−1} dt`,  `a > 0`, `z > 0`,

is a half-line Laplace integral of exactly the Watson shape
`∫_{(0,∞)} e^{−z t} (t^{a−1} · g t) dt` with parameter `s = a` and amplitude
`g(t) = (1+t)^{b−a−1}`.  Since `g(0⁺) = 1`, the *exponential-growth* Watson lemma
`PicardLefschetz.watson_growth` gives

`z^a · ∫_{(0,∞)} e^{−z t} t^{a−1}(1+t)^{b−a−1} dt → 1 · Γ(a) = Γ(a)`,

and dividing by `Γ(a)` yields the leading recessive term

`U(a;b;z) ~ z^{−a}`  (DLMF 13.7.3),

stated here as the ratio limit `U(a;b;z) / z^{−a} → 1` as `z → +∞`.

The amplitude `g(t) = (1+t)^{b−a−1}` is unbounded when `b−a−1 > 0`, which is why
the exponential-growth variant of Watson's lemma (rather than the bounded one) is
used: `|(1+t)^{b−a−1}| ≤ e^{|b−a−1|·t}` for `t > 0`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology PicardLefschetz

namespace FLMF.Hypergeometric

/-- `g(t) = (1+t)^{b−a−1}`, the Watson amplitude for `U(a;b;z)`. -/
-- no-dlmf: Watson-amplitude auxiliary, no DLMF counterpart
private noncomputable def gT (a b t : ℝ) : ℝ := (1 + t) ^ (b - a - 1)

-- no-dlmf: measurability of the Watson amplitude, no DLMF counterpart
private theorem gT_measurable (a b : ℝ) : Measurable (gT a b) := by
  unfold gT
  fun_prop

/-- Exponential-growth bound: `|(1+t)^{b−a−1}| ≤ 1 · e^{|b−a−1| · t}` for `t > 0`. -/
-- no-dlmf: Watson-amplitude growth bound, no DLMF counterpart
private theorem gT_growth (a b : ℝ) :
    ∀ t ∈ Ioi (0 : ℝ), |gT a b t| ≤ 1 * Real.exp (|b - a - 1| * t) := by
  intro t ht
  have ht' : 0 < t := ht
  have h1u : (0 : ℝ) < 1 + t := by linarith
  rw [one_mul]
  unfold gT
  rw [abs_of_nonneg (Real.rpow_nonneg h1u.le _)]
  set e : ℝ := b - a - 1 with he
  rcases le_or_gt 0 e with he0 | he0
  · -- e ≥ 0: use 1 + t ≤ e^t
    have hexp : e = |e| := (abs_of_nonneg he0).symm
    have hle : 1 + t ≤ Real.exp t := by
      have := Real.add_one_le_exp t
      linarith
    calc (1 + t) ^ e
        ≤ (Real.exp t) ^ e :=
          Real.rpow_le_rpow h1u.le hle he0
      _ = Real.exp (t * e) := by rw [← Real.exp_mul]
      _ = Real.exp (|e| * t) := by rw [← hexp]; ring_nf
  · -- e < 0: (1+t)^e ≤ 1 ≤ e^{|e| t}
    have hle1 : (1 + t) ^ e ≤ 1 := by
      have h1le : (1 : ℝ) ≤ 1 + t := by linarith
      exact Real.rpow_le_one_of_one_le_of_nonpos h1le (by linarith : e ≤ 0)
    have hge1 : (1 : ℝ) ≤ Real.exp (|e| * t) := by
      apply Real.one_le_exp
      positivity
    linarith

-- no-dlmf: Watson-amplitude limit at 0, no DLMF counterpart
private theorem gT_lim (a b : ℝ) : Tendsto (gT a b) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have : Tendsto (gT a b) (𝓝 (0 : ℝ)) (𝓝 1) := by
    unfold gT
    have hcont : Tendsto (fun t : ℝ => (1 + t) ^ (b - a - 1)) (𝓝 0)
        (𝓝 ((1 + 0) ^ (b - a - 1))) := by
      apply ContinuousAt.tendsto
      apply ContinuousAt.rpow_const
      · exact (continuous_const.add continuous_id).continuousAt
      · left; norm_num
    simpa using hcont
  exact this.mono_left nhdsWithin_le_nhds

/-- The Watson factor `z^a · ∫_{(0,∞)} e^{−z t} t^{a−1}(1+t)^{b−a−1} dt` of the
Tricomi integral tends to `Γ(a)` as `z → +∞`. -/
-- no-dlmf: intermediate Watson-asymptotic factor, no DLMF counterpart
private theorem tendsto_tricomi_watson_factor {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun z : ℝ => z ^ a * ∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t)
      atTop (𝓝 (Real.Gamma a)) := by
  have h := watson_growth (s := a) ha (g := gT a b) (a₀ := 1) (C := 1)
    (c := |b - a - 1|) (zero_le_one) (gT_measurable a b) (gT_growth a b) (gT_lim a b)
  -- rewrite Watson's `1 · Γ a` target and align the integrand shape
  have h' :
      Tendsto (fun z : ℝ => z ^ a * ∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t)
        atTop (𝓝 (1 * Real.Gamma a)) := by
    refine h.congr' ?_
    filter_upwards with z
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    unfold tricomiIntegrand gT
    ring
  simpa using h'

/-- **DLMF 13.7.3 (leading recessive term).**  For real `a > 0`,

`U(a;b;z) ~ z^{−a}` as `z → +∞`,

in the precise ratio sense `U(a;b;z) / z^{−a} → 1`.

DAG: E-13.7.3.
Numerical: PASS
Verified: unverified
-/
theorem tricomiU_asymptotic {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun z : ℝ => tricomiU a b z / z ^ (-a)) atTop (𝓝 1) := by
  have hΓ : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  -- `U / z^{−a} = z^a · U = Γ(a)⁻¹ · (z^a · ∫ …)`, which tends to `Γ(a)⁻¹ · Γ(a) = 1`.
  have hlim : Tendsto
      (fun z : ℝ => (Real.Gamma a)⁻¹ * (z ^ a * ∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t))
      atTop (𝓝 ((Real.Gamma a)⁻¹ * Real.Gamma a)) :=
    (tendsto_tricomi_watson_factor ha b).const_mul _
  rw [inv_mul_cancel₀ hΓ] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  unfold tricomiU
  set I := ∫ t in Ioi (0 : ℝ), tricomiIntegrand a b z t with hI
  have hzne : z ≠ 0 := hz.ne'
  -- `z^{−a} = (z^a)⁻¹` and `z^a ≠ 0`
  have hza_pos : (0 : ℝ) < z ^ a := Real.rpow_pos_of_pos hz a
  have hneg : z ^ (-a) = (z ^ a)⁻¹ := by
    rw [Real.rpow_neg hz.le]
  rw [hneg, div_inv_eq_mul]
  ring

end FLMF.Hypergeometric
