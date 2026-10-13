import FLMF.Methods.Watson

/-!
# Leading asymptotics of the exponential integral `E₁`

We work with the Watson-ready representation
`E₁(x) = e^{-x} ∫_{(0,∞)} e^{-x u} / (1+u) du`,
obtained from `E₁(x) = ∫_x^∞ e^{-t}/t dt` by the substitution `t = x(1+u)`
(DLMF §6.2, §6.12.1).  The leading asymptotic `E₁(x) ~ e^{-x}/x` then follows
from the leading-order Watson lemma `PicardLefschetz.watson_leading` with
`s = 1`, `g(u) = 1/(1+u)` and `a₀ = g(0⁺) = 1`.
-/

namespace FLMF.ExpIntegrals

open MeasureTheory Real Filter Topology Set PicardLefschetz

/-- The exponential integral `E₁`, in its Watson-ready (`t = x(1+u)`) form:
`E₁(x) = e^{-x} ∫_{(0,∞)} e^{-x u} / (1+u) du`. -/
-- no-dlmf: Watson-ready representation used for the asymptotic; canonical E₁ is tagged in Definitions
noncomputable def E₁ (x : ℝ) : ℝ :=
  Real.exp (-x) * ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 / (1 + u))

/-- `g(u) = 1/(1+u)`, the Watson amplitude for `E₁`. -/
-- no-dlmf: Watson amplitude helper; no DLMF counterpart
private noncomputable def gE (u : ℝ) : ℝ := 1 / (1 + u)

-- no-dlmf: measurability of the Watson amplitude; no DLMF counterpart
private theorem gE_measurable : Measurable gE := by
  unfold gE
  fun_prop

-- no-dlmf: boundedness of the Watson amplitude; no DLMF counterpart
private theorem gE_bdd : ∀ t ∈ Ioi (0 : ℝ), |gE t| ≤ 1 := by
  intro t ht
  have ht' : 0 < t := ht
  unfold gE
  have h1 : (0 : ℝ) < 1 + t := by linarith
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_one h1]
  linarith

-- no-dlmf: limit of the Watson amplitude at 0⁺; no DLMF counterpart
private theorem gE_lim : Tendsto gE (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have : Tendsto gE (𝓝 (0 : ℝ)) (𝓝 1) := by
    unfold gE
    have : Tendsto (fun u : ℝ => 1 / (1 + u)) (𝓝 0) (𝓝 (1 / (1 + 0))) := by
      apply Tendsto.div tendsto_const_nhds
      · exact (tendsto_const_nhds.add tendsto_id)
      · norm_num
    simpa using this
  exact this.mono_left nhdsWithin_le_nhds

/-- The Watson factor `∫_{(0,∞)} e^{-x u}/(1+u) du` of `E₁`, rescaled by `x`,
tends to `1` as `x → ∞`. -/
-- no-dlmf: intermediate Watson-factor limit toward the asymptotic theorem below
theorem tendsto_watson_factor :
    Tendsto (fun x : ℝ => x * ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 / (1 + u)))
      atTop (𝓝 1) := by
  have h := watson_leading (s := 1) (one_pos) (g := gE) (a₀ := 1) (C := 1)
    gE_measurable gE_bdd gE_lim
  -- Massage the statement of `watson_leading` (with `s = 1`) into our form.
  have h' :
      Tendsto (fun x : ℝ => x * ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 / (1 + u)))
        atTop (𝓝 (1 * Real.Gamma 1)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_one]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u hu
    simp only [gE, show (1:ℝ) - 1 = 0 from by norm_num, Real.rpow_zero, one_mul]
  simpa [Real.Gamma_one] using h'

/-- **DLMF 6.12.1 (leading term).**  `E₁(x) ~ e^{-x}/x`, in the precise sense
that `x · e^{x} · E₁(x) → 1` as `x → ∞`.

DLMF 6.12.1.
Fidelity: tier1 PASS
Verified: unverified
DAG: E-6.12.1.
-/
theorem E₁_asymptotic :
    Tendsto (fun x : ℝ => x * Real.exp x * E₁ x) atTop (𝓝 1) := by
  refine tendsto_watson_factor.congr' ?_
  filter_upwards with x
  unfold E₁
  set I := ∫ u in Ioi (0 : ℝ), Real.exp (-x * u) * (1 / (1 + u)) with hI
  have hexp : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    x * I = x * (Real.exp (-x) * Real.exp x) * I := by rw [hexp]; ring
    _ = x * Real.exp x * (Real.exp (-x) * I) := by ring
