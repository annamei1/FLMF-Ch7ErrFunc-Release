import FLMF.Support.Residue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Analytic zero counts on open sets

This module packages the multiplicity-weighted zero count used by argument-
principle applications.  The congruence theorem is the key invariant needed
to transport a zero count between analytic representatives that agree on an
open domain.
-/

noncomputable section

open Complex Filter Metric Set Topology
open scoped ENNReal Real Interval BigOperators

namespace FLMF.Methods

/-- The sum of analytic vanishing orders over a set.  For an analytic function
that is not locally zero, this is its number of zeros in `U`, counted with
multiplicity, as an `ENNReal`. -/
def analyticZeroCountOn (f : ℂ → ℂ) (U : Set ℂ) : ℝ≥0∞ := by
  classical
  exact ∑' z : ℂ,
    if z ∈ U then (analyticOrderNatAt f z : ℝ≥0∞) else 0

/-- Analytic zero count depends only on the restriction of the function to an
open counting domain. -/
theorem analyticZeroCountOn_congr_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hfg : EqOn f g U) :
    analyticZeroCountOn f U = analyticZeroCountOn g U := by
  classical
  unfold analyticZeroCountOn
  apply tsum_congr
  intro z
  by_cases hz : z ∈ U
  · simp only [hz, if_true]
    have hev : f =ᶠ[𝓝 z] g := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hfg hw
    rw [analyticOrderNatAt, analyticOrderNatAt,
      analyticOrderAt_congr hev]
  · simp [hz]

/-- Analytic zero count is monotone in the counting set. -/
theorem analyticZeroCountOn_mono (f : ℂ → ℂ) {U V : Set ℂ}
    (hUV : U ⊆ V) :
    analyticZeroCountOn f U ≤ analyticZeroCountOn f V := by
  classical
  unfold analyticZeroCountOn
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hzU : z ∈ U
  · have hzV := hUV hzU
    simp only [hzU, hzV, if_true]
    exact le_rfl
  · simp only [hzU, if_false]
    exact bot_le

/-- A directed family of counting sets computes the zero count on its union
as the supremum of the counts on the individual sets.  This is the monotone
exhaustion principle needed to pass from compact argument-principle contours
to an unbounded analytic domain. -/
theorem analyticZeroCountOn_iUnion_of_directed {f : ℂ → ℂ}
    {ι : Type*} [Nonempty ι] {U : ι → Set ℂ}
    (hU : Directed (· ⊆ ·) U) :
    analyticZeroCountOn f (⋃ i, U i) =
      ⨆ i, analyticZeroCountOn f (U i) := by
  classical
  apply le_antisymm
  · unfold analyticZeroCountOn
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s ↦ ?_
    let t : Finset ℂ := s.filter fun z ↦ z ∈ ⋃ i, U i
    have ht : (t : Set ℂ) ⊆ ⋃ i, U i := by
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    obtain ⟨i, hi⟩ := hU.exists_mem_subset_of_finset_subset_biUnion ht
    calc
      ∑ z ∈ s, (if z ∈ ⋃ i, U i then
          (analyticOrderNatAt f z : ℝ≥0∞) else 0) ≤
          ∑ z ∈ s, (if z ∈ U i then
            (analyticOrderNatAt f z : ℝ≥0∞) else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzUnion : z ∈ ⋃ j, U j
        · have hzt : z ∈ t := Finset.mem_filter.mpr ⟨hz, hzUnion⟩
          simp only [hzUnion, hi hzt, if_true]
          exact le_rfl
        · simp [hzUnion]
      _ ≤ ∑' z : ℂ, (if z ∈ U i then
            (analyticOrderNatAt f z : ℝ≥0∞) else 0) :=
        ENNReal.sum_le_tsum s
      _ ≤ ⨆ i, ∑' z : ℂ, (if z ∈ U i then
            (analyticOrderNatAt f z : ℝ≥0∞) else 0) :=
        le_iSup (fun j : ι ↦ ∑' z : ℂ, (if z ∈ U j then
          (analyticOrderNatAt f z : ℝ≥0∞) else 0)) i
  · refine iSup_le fun i ↦ analyticZeroCountOn_mono f ?_
    exact Set.subset_iUnion U i

/-- Restricting the zero count to a finite set turns the defining `tsum` into
the corresponding finite multiplicity sum. -/
theorem analyticZeroCountOn_finite {f : ℂ → ℂ} {U : Set ℂ}
    (hU : U.Finite) :
    analyticZeroCountOn f U =
      ∑ z ∈ hU.toFinset, (analyticOrderNatAt f z : ℝ≥0∞) := by
  classical
  unfold analyticZeroCountOn
  rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos (hU.mem_toFinset.mp hz)]
  · intro z hz
    rw [if_neg (show z ∉ U by
      intro hmem
      exact hz (hU.mem_toFinset.mpr hmem))]

/-- When a finite set is exactly the zero set in `U`, the global indicator
`tsum` reduces to its finite multiplicity sum.  The ambient set `U` itself
need not be finite. -/
theorem analyticZeroCountOn_eq_sum_zeroFinset {f : ℂ → ℂ} {U : Set ℂ}
    (P : Finset ℂ) (hf : ∀ z ∈ U, AnalyticAt ℂ f z)
    (hP : ∀ z, z ∈ P ↔ z ∈ U ∧ f z = 0) :
    analyticZeroCountOn f U =
      ∑ z ∈ P, (analyticOrderNatAt f z : ℝ≥0∞) := by
  classical
  unfold analyticZeroCountOn
  rw [tsum_eq_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos ((hP z).mp hz).1]
  · intro z hzP
    by_cases hzU : z ∈ U
    · have hfz : f z ≠ 0 := by
        intro hfz
        exact hzP ((hP z).mpr ⟨hzU, hfz⟩)
      have hord : analyticOrderAt f z = 0 :=
        (hf z hzU).analyticOrderAt_eq_zero.mpr hfz
      simp [hzU, analyticOrderNatAt, hord]
    · simp [hzU]

/-- Near a zero of finite order, multiplying the logarithmic derivative by
`z - c` tends to the analytic vanishing order. -/
theorem tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfinite : analyticOrderAt f c ≠ ⊤) :
    Tendsto (fun z ↦ (z - c) * (deriv f z / f z)) (𝓝[≠] c)
      (𝓝 (analyticOrderNatAt f c : ℂ)) := by
  let n := analyticOrderNatAt f c
  obtain ⟨g, hg, hgc, hfg⟩ :=
    (hf.analyticOrderNatAt_eq_iff hfinite).mp (rfl : analyticOrderNatAt f c = n)
  have hgne : ∀ᶠ z in 𝓝 c, g z ≠ 0 := hg.continuousAt.eventually_ne hgc
  obtain ⟨V, hVc, hgV⟩ := hg.exists_mem_nhds_analyticOnNhd
  have hfg' : f =ᶠ[𝓝 c] fun z ↦ (z - c) ^ n * g z := by
    simpa only [smul_eq_mul] using hfg
  have hderiv : deriv f =ᶠ[𝓝 c] deriv (fun z ↦ (z - c) ^ n * g z) := hfg'.deriv
  have hlog : ∀ᶠ z in 𝓝[≠] c,
      (z - c) * (deriv f z / f z) =
        (n : ℂ) + (z - c) * (deriv g z / g z) := by
    filter_upwards [hfg'.filter_mono nhdsWithin_le_nhds,
      hderiv.filter_mono nhdsWithin_le_nhds,
      hgne.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hVc,
      self_mem_nhdsWithin] with z hfgz hderivz hgz hzV hzc
    have hsub : z - c ≠ 0 := sub_ne_zero.mpr hzc
    have hgdiff : DifferentiableAt ℂ g z := (hgV z hzV).differentiableAt
    have hsubdiff : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    have hdprod := deriv_mul (hsubdiff.pow n) hgdiff
    have hdpow : deriv (fun w : ℂ ↦ (w - c) ^ n) z =
        (n : ℂ) * (z - c) ^ (n - 1) * deriv (fun w : ℂ ↦ w - c) z := by
      simpa only [Pi.pow_apply] using deriv_pow hsubdiff n
    have hsubderiv : deriv (fun w : ℂ ↦ w - c) z = 1 := by
      simpa using ((hasDerivAt_id z).sub_const c).deriv
    rw [hfgz, hderivz]
    rw [show deriv (fun w ↦ (w - c) ^ n * g w) z =
        deriv (fun w ↦ (w - c) ^ n) z * g z + (z - c) ^ n * deriv g z by
          simpa only [Pi.mul_apply] using hdprod,
      hdpow, hsubderiv]
    cases n with
    | zero => simp
    | succ n =>
        field_simp
        simp only [Nat.succ_sub_one]
        rw [pow_succ]
        ring
  rw [tendsto_congr' hlog]
  have hgquot : Tendsto (fun z ↦ deriv g z / g z) (𝓝[≠] c) (𝓝 (deriv g c / g c)) :=
    (hg.deriv.continuousAt.div hg.continuousAt hgc).tendsto.mono_left nhdsWithin_le_nhds
  have hsubzero : Tendsto (fun z : ℂ ↦ z - c) (𝓝[≠] c) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ ↦ z - c) (𝓝 c) (𝓝 (c - c)) :=
      continuousAt_id.sub_const c
    simpa using h.mono_left nhdsWithin_le_nhds
  convert tendsto_const_nhds.add (hsubzero.mul hgquot) using 1 <;> simp [n]

/-- The logarithmic derivative of a nonzero analytic germ has residue equal to
its vanishing order. This is the local multiplicity calculation underlying the
argument principle. -/
theorem residue_logDeriv_eq_analyticOrderNatAt {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfinite : analyticOrderAt f c ≠ ⊤) :
    residue (fun z ↦ deriv f z / f z) c = (analyticOrderNatAt f c : ℂ) := by
  obtain ⟨g, hg, hgc, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hgne : ∀ᶠ z in 𝓝 c, g z ≠ 0 := hg.continuousAt.eventually_ne hgc
  obtain ⟨U, hUc, hfU⟩ := hf.exists_mem_nhds_analyticOnNhd
  have hdiff : ∀ᶠ z in 𝓝 c, z ≠ c →
      DifferentiableAt ℂ (fun w ↦ deriv f w / f w) z := by
    filter_upwards [hUc, hfg, hgne] with z hzU hfgz hgz
    have hfz : AnalyticAt ℂ f z := hfU z hzU
    have hsub : z - c ≠ 0 → f z ≠ 0 := by
      intro hzc
      rw [hfgz]
      exact mul_ne_zero (pow_ne_zero _ hzc) hgz
    intro hzc
    exact (hfz.deriv.div hfz (hsub (sub_ne_zero.mpr hzc))).differentiableAt
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hdiff
  exact residue_simple_pole hR (fun z hz ↦ hRsub hz.1 hz.2)
    (tendsto_sub_mul_logDeriv hf hfinite)

/-- A nonzero analytic function on a connected domain has only finitely many
zeros in each compact subset of that domain. -/
theorem finite_zeros_on_compact {f : ℂ → ℂ} {U K : Set ℂ} {x : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U)
    (hx : x ∈ U) (hfx : f x ≠ 0) (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ f ⁻¹' {0}).Finite := by
  have hZclosed : IsClosed (K ∩ f ⁻¹' {0}) :=
    (hf.mono hKU).continuousOn.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  have hZcompact : IsCompact (K ∩ f ⁻¹' {0}) :=
    hK.of_isClosed_subset hZclosed inter_subset_left
  have hcod : f ⁻¹' {0}ᶜ ∈ codiscreteWithin U :=
    hf.preimage_zero_mem_codiscreteWithin hfx hx hU
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hcod
  apply hZcompact.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  rw [← disjoint_iff, Filter.disjoint_principal_right]
  apply Filter.mem_of_superset (hcod z (hKU hz.1))
  intro w hw
  simp only [mem_union, mem_preimage, mem_compl_iff, mem_singleton_iff] at hw
  simp only [mem_compl_iff, mem_inter_iff, mem_preimage, mem_singleton_iff]
  tauto

/-- **Argument principle on a circle.** If `P` is exactly the zero set of an
analytic function on the closed disc, every zero is strictly interior, and no
analytic germ is locally zero, then the logarithmic-derivative integral is
`2πi` times the sum of analytic multiplicities. -/
theorem circleIntegral_logDeriv_eq_sum_orders {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (P : Finset ℂ)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z)
    (hP : ∀ z, z ∈ P ↔ z ∈ closedBall c R ∧ f z = 0)
    (hPball : ∀ p ∈ P, p ∈ ball c R)
    (hfinite : ∀ p ∈ P, analyticOrderAt f p ≠ ⊤) :
    (∮ z in C(c, R), deriv f z / f z) =
      2 * π * I * ∑ p ∈ P, (analyticOrderNatAt f p : ℂ) := by
  apply circle_finite_simple_poles (f := fun z ↦ deriv f z / f z) hR P
    (fun p ↦ (analyticOrderNatAt f p : ℂ)) hPball
  · intro q hq
    have hfq := hf q hq.1
    have hfq_ne : f q ≠ 0 := by
      intro hzero
      exact hq.2 ((hP q).mpr ⟨hq.1, hzero⟩)
    exact (hfq.deriv.div hfq hfq_ne).differentiableAt
  · intro p hp
    exact tendsto_sub_mul_logDeriv (hf p (ball_subset_closedBall (hPball p hp)))
      (hfinite p hp)

/-- **Argument principle on a rectangle.** If `P` is exactly the zero set of
an analytic function on the closed rectangle, every zero is strictly
interior, and no listed analytic germ is locally zero, then the boundary
integral of the logarithmic derivative is `2πi` times the sum of the analytic
multiplicities. -/
theorem rectBoundaryIntegral_logDeriv_eq_sum_orders {f : ℂ → ℂ} {z w : ℂ}
    (P : Finset ℂ)
    (hf : ∀ q ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ f q)
    (hP : ∀ q, q ∈ P ↔ q ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] ∧ f q = 0)
    (hPopen : ∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hfinite : ∀ p ∈ P, analyticOrderAt f p ≠ ⊤) :
    rectBoundaryIntegral (fun q ↦ deriv f q / f q) z w =
      2 * π * I * ∑ p ∈ P, (analyticOrderNatAt f p : ℂ) := by
  apply rectangle_finite_simple_poles P
    (fun p ↦ (analyticOrderNatAt f p : ℂ)) hPopen
  · intro q hq
    have hfq := hf q hq.1
    have hfq_ne : f q ≠ 0 := by
      intro hzero
      exact hq.2 ((hP q).mpr ⟨hq.1, hzero⟩)
    exact (hfq.deriv.div hfq hfq_ne).differentiableAt
  · intro p hp
    exact tendsto_sub_mul_logDeriv (hf p
      ⟨uIcc_of_le ((hPopen p hp).1.1.trans (hPopen p hp).1.2).le ▸
          Ioo_subset_Icc_self (hPopen p hp).1,
        uIcc_of_le ((hPopen p hp).2.1.trans (hPopen p hp).2.2).le ▸
          Ioo_subset_Icc_self (hPopen p hp).2⟩) (hfinite p hp)

/-- Schwarz reflection preserves complex differentiability when conjugation
is applied to both the source and target.  This real-derivative proof is the
local analytic engine for real-parameter continuation identities. -/
theorem differentiableAt_conj_comp_conj {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (starRingEnd ℂ z)) :
    DifferentiableAt ℂ (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z := by
  have hi : HasFDerivAt (starRingEnd ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z :=
    Complex.conjCLE.hasFDerivAt
  have hfR : HasFDerivAt f
      (((ContinuousLinearMap.toSpanSingleton ℂ
        (deriv f ((starRingEnd ℂ) z))).restrictScalars ℝ) : ℂ →L[ℝ] ℂ)
      ((starRingEnd ℂ) z) :=
    hf.hasDerivAt.restrictScalars ℝ
  have ho : HasFDerivAt (starRingEnd ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      (f ((starRingEnd ℂ) z)) := Complex.conjCLE.hasFDerivAt
  have hinner : HasFDerivAt (fun w => f ((starRingEnd ℂ) w))
      ((((ContinuousLinearMap.toSpanSingleton ℂ
        (deriv f ((starRingEnd ℂ) z))).restrictScalars ℝ) : ℂ →L[ℝ] ℂ).comp
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
    simpa [Complex.conjCLE_apply] using hfR.comp z hi
  have hreal : HasFDerivAt
      (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv f ((starRingEnd ℂ) z))).restrictScalars ℝ).comp
            (Complex.conjCLE : ℂ →L[ℝ] ℂ)))) z := by
    simpa [Complex.conjCLE_apply] using ho.comp z hinner
  let D : ℂ →L[ℂ] ℂ :=
    ContinuousLinearMap.toSpanSingleton ℂ
      ((starRingEnd ℂ) (deriv f ((starRingEnd ℂ) z)))
  have hD : D.restrictScalars ℝ =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv f ((starRingEnd ℂ) z))).restrictScalars ℝ) : ℂ →L[ℝ] ℂ).comp
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := by
    ext w
    simp [D]
  exact (hasFDerivAt_of_restrictScalars ℝ hreal hD).differentiableAt

/-! ## Circular arcs

The arc analogue of the horizontal/vertical logarithmic-derivative segment lemmas:
a parametrization `θ ↦ r e^{iθ}` of the circle of radius `r` about the origin, its
elementary properties, and the fundamental theorem of calculus for `f'/f` along an
arc on which `f` stays in the principal logarithm domain.  This is the contour
infrastructure a *sector* zero count needs on its circular edge. -/

-- no-dlmf: generic circular-arc contour parametrization; proof infrastructure
/-- The circular arc of radius `r` about the origin: `θ ↦ r e^{iθ}`. -/
def arcPoint (r θ : ℝ) : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * I)

-- no-dlmf: identification of the arc parametrization with Mathlib's `circleMap`
/-- `arcPoint r` is Mathlib's `circleMap 0 r`. -/
theorem arcPoint_eq_circleMap (r θ : ℝ) : arcPoint r θ = circleMap (0 : ℂ) r θ := by
  simp [arcPoint, circleMap]

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- Every point of the arc of radius `r ≥ 0` has norm exactly `r`. -/
theorem norm_arcPoint {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖arcPoint r θ‖ = r := by
  rw [arcPoint_eq_circleMap, norm_circleMap_zero]
  exact abs_of_nonneg hr

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- A nondegenerate arc misses the origin. -/
theorem arcPoint_ne_zero {r : ℝ} (hr : r ≠ 0) (θ : ℝ) : arcPoint r θ ≠ 0 := by
  rw [arcPoint]
  exact mul_ne_zero (by exact_mod_cast hr) (Complex.exp_ne_zero _)

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The arc parametrization is continuous. -/
theorem continuous_arcPoint (r : ℝ) : Continuous (arcPoint r) := by
  have h : arcPoint r = circleMap (0 : ℂ) r := funext (arcPoint_eq_circleMap r)
  rw [h]
  exact continuous_circleMap 0 r

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The real part of an arc point is `r cos θ`. -/
theorem arcPoint_re (r θ : ℝ) : (arcPoint r θ).re = r * Real.cos θ := by
  rw [arcPoint, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The arc is antipodal under a half turn: `arcPoint r (θ + π) = -arcPoint r θ`. -/
theorem arcPoint_add_pi (r θ : ℝ) : arcPoint r (θ + Real.pi) = -arcPoint r θ := by
  simp only [arcPoint]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The arc reflects to its conjugate under `θ ↦ -θ`. -/
theorem arcPoint_neg (r θ : ℝ) : arcPoint r (-θ) = starRingEnd ℂ (arcPoint r θ) := by
  simp only [arcPoint, map_mul, map_mul]
  rw [show starRingEnd ℂ (r : ℂ) = (r : ℂ) from Complex.conj_ofReal _,
    ← Complex.exp_conj]
  congr 2
  push_cast
  simp

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The arc starts at the positive real point `r`. -/
theorem arcPoint_zero (r : ℝ) : arcPoint r 0 = (r : ℂ) := by
  rw [arcPoint]; norm_num

-- no-dlmf: elementary property of the arc parametrization; proof infrastructure
/-- The quarter-arc endpoint is `i r`. -/
theorem arcPoint_pi_div_two (r : ℝ) : arcPoint r (Real.pi / 2) = (r : ℂ) * I := by
  rw [arcPoint, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

-- no-dlmf: chain-rule input for the arc fundamental theorem of calculus
/-- The complex derivative of `w ↦ r e^{iw}` at a real point. -/
theorem hasDerivAt_arcPoint (r θ : ℝ) :
    HasDerivAt (fun w : ℂ => (r : ℂ) * Complex.exp (w * I))
      ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I) (θ : ℂ) := by
  have h : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
      (Complex.exp ((θ : ℂ) * I) * I) (θ : ℂ) := by
    simpa using (Complex.hasDerivAt_exp ((θ : ℂ) * I)).comp (θ : ℂ)
      ((hasDerivAt_id ((θ : ℂ))).mul_const I)
  simpa [mul_assoc] using h.const_mul ((r : ℂ))

-- no-dlmf: the oriented logarithmic-derivative integral along a circular arc
/-- The oriented logarithmic-derivative integral of `f` along the arc of radius `r`
from angle `a` to angle `b`. -/
def arcLogDerivIntegral (f : ℂ → ℂ) (r a b : ℝ) : ℂ :=
  ∫ θ in a..b, deriv f (arcPoint r θ) / f (arcPoint r θ) * (I * arcPoint r θ)

-- no-dlmf: circular-arc analogue of the segment logarithmic-derivative lemmas
/-- **Fundamental theorem of calculus for `f'/f` on a circular arc.**  On an arc whose
image under `f` stays in the principal logarithm domain, the oriented
logarithmic-derivative integral is the difference of the endpoint logarithms. -/
theorem arc_logDeriv_integral {f : ℂ → ℂ} {r a b : ℝ}
    (hf : ∀ θ ∈ [[a, b]], DifferentiableAt ℂ f (arcPoint r θ))
    (hslit : ∀ θ ∈ [[a, b]], f (arcPoint r θ) ∈ Complex.slitPlane)
    (hint : IntervalIntegrable
      (fun θ : ℝ => deriv f (arcPoint r θ) / f (arcPoint r θ) * (I * arcPoint r θ))
      MeasureTheory.volume a b) :
    arcLogDerivIntegral f r a b
      = Complex.log (f (arcPoint r b)) - Complex.log (f (arcPoint r a)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ : ℝ => Complex.log (f (arcPoint r θ))) (fun θ hθ => ?_) hint
  have hF : HasDerivAt (fun w : ℂ => f ((r : ℂ) * Complex.exp (w * I)))
      (deriv f (arcPoint r θ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I)) (θ : ℂ) := by
    simpa [Function.comp_def, arcPoint] using
      (hf θ hθ).hasDerivAt.comp (θ : ℂ) (hasDerivAt_arcPoint r θ)
  have hlog : HasDerivAt
      (fun w : ℂ => Complex.log (f ((r : ℂ) * Complex.exp (w * I))))
      ((f (arcPoint r θ))⁻¹ * (deriv f (arcPoint r θ)
        * ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I))) (θ : ℂ) := by
    simpa [Function.comp_def, arcPoint] using
      (Complex.hasDerivAt_log (hslit θ hθ)).comp (θ : ℂ) hF
  have hd := hlog.comp_ofReal
  simp only [arcPoint] at hd ⊢
  convert hd using 1
  field_simp

-- no-dlmf: conjugation through an interval integral; contour-symmetry infrastructure
/-- Complex conjugation commutes with the interval integral of an interval-integrable
integrand: `∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x)`. -/
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ x in a..b, starRingEnd ℂ (f x)) = starRingEnd ℂ (∫ x in a..b, f x) := by
  have hL := (RCLike.conjCLE (K := ℂ) : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hf
  simpa [RCLike.conjCLE_apply] using hL

/-- The imaginary part of a logarithmic derivative is the real Wronskian
numerator divided by the squared norm. This is the algebraic core of boundary
argument-monotonicity calculations. -/
theorem im_div_eq_conj_mul_im_div_normSq (F D : ℂ) :
    (D / F).im = ((starRingEnd ℂ) F * D).im / Complex.normSq F := by
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A nonzero Wronskian numerator forces the boundary value itself to be
nonzero. -/
theorem ne_zero_of_conj_mul_im_ne_zero {F D : ℂ}
    (hW : ((starRingEnd ℂ) F * D).im ≠ 0) : F ≠ 0 := by
  intro hF
  simp [hF] at hW

/-- Once the Wronskian numerator is nonzero, it has the same sign as the
imaginary part of the logarithmic derivative. -/
theorem im_div_pos_iff_conj_mul_im_pos {F D : ℂ}
    (hW : ((starRingEnd ℂ) F * D).im ≠ 0) :
    0 < (D / F).im ↔ 0 < ((starRingEnd ℂ) F * D).im := by
  rw [im_div_eq_conj_mul_im_div_normSq]
  exact div_pos_iff_of_pos_right
    (Complex.normSq_pos.mpr (ne_zero_of_conj_mul_im_ne_zero hW))

end FLMF.Methods
