import FLMF.Support.HypergeometricGaussConnection
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The `z = 1` connection formula at complex parameters (framework — DLMF 15.10.21, C2 Phase 2)

`GaussConnection.lean` proves DLMF 15.10.21 for **real** parameters in the
restricted regime `0 < b < c < min(1, a+1)`, `a + b < c`, on the lens
`‖z‖ < 1 ∧ ‖z − 1‖ < 1`.  This file removes the parameter restrictions by
analytic continuation in the *parameters*: for fixed `z` in the lens, both
sides of 15.10.21 are analytic in each parameter separately on the honest DLMF
non-degeneracy domain

  `c ∉ ℤ_{≤0}`  and  `c − a − b ∉ ℤ`,

and the proven real region accumulates in every single-variable slice, so the
identity theorem extends the formula one variable at a time (`a`, then `b`,
then `c`).

* `differentiableOn_ordinaryHypergeometric_param` — **parameter analyticity of
  the Gauss series** along affine parameter paths `t ↦ (a₀+a₁t, b₀+b₁t, c₀+c₁t)`
  for fixed `‖u‖ < 1`: a Weierstrass M-test, with the Pochhammer quotients
  dominated on parameter compacts by a ratio-test-summable sequence.
* `ordinaryHypergeometric_one_sub_connection_complex` — **DLMF 15.10.21** for
  complex `a b c` with `c` off the nonpositive integers and `c − a − b ∉ ℤ`, on
  the lens.  The Γ-coefficients take their limiting values at the removable
  points (`1/Γ` is entire and Mathlib's `Γ` vanishes at the poles, so the
  formula is stated with plain division).

The real-parameter surface `ordinaryHypergeometric_one_sub_connection` in
`GaussConnection.lean` is untouched.

## References

- DLMF §15.10(ii): https://dlmf.nist.gov/15.10#ii (15.10.21)
- DLMF §15.8(i): https://dlmf.nist.gov/15.8#i (15.8.4)
-/

noncomputable section

open Set Metric Filter Topology

namespace FLMF.Hypergeometric

/-! ### Parameter analyticity of the Gauss series along affine paths -/

-- no-dlmf: parameter-analyticity infrastructure for DLMF §15.10(ii), no equation number
/-- **Parameter analyticity of the Gauss series.**  Along any affine path
`t ↦ (a₀+a₁t, b₀+b₁t, c₀+c₁t)` in the parameters, `₂F₁(·,·;·;u)` (fixed
`‖u‖ < 1`) is a differentiable function of `t` on any open set where the
`c`-parameter avoids the nonpositive integers.  Weierstrass M-test: on a
parameter compact the Pochhammer quotient terms are dominated by a
ratio-test-summable sequence. -/
theorem differentiableOn_ordinaryHypergeometric_param {u : ℂ} (hu : ‖u‖ < 1)
    (a₀ a₁ b₀ b₁ c₀ c₁ : ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hγ : ∀ t ∈ Ω, ∀ k : ℕ, (k : ℂ) ≠ -(c₀ + c₁ * t)) :
    DifferentiableOn ℂ
      (fun t : ℂ => ₂F₁ (a₀ + a₁ * t) (b₀ + b₁ * t) (c₀ + c₁ * t) u) Ω := by
  classical
  set g : ℕ → ℂ → ℂ := fun n t =>
    (((n.factorial : ℂ))⁻¹ * (ascPochhammer ℂ n).eval (a₀ + a₁ * t)
        * (ascPochhammer ℂ n).eval (b₀ + b₁ * t)
        * ((ascPochhammer ℂ n).eval (c₀ + c₁ * t))⁻¹) * u ^ n with hgdef
  -- pointwise, the function is the sum of the series
  have hFeq : (fun t : ℂ => ₂F₁ (a₀ + a₁ * t) (b₀ + b₁ * t) (c₀ + c₁ * t) u)
      = fun t => ∑' n, g n t := by
    funext t
    rw [show (₂F₁ (a₀ + a₁ * t) (b₀ + b₁ * t) (c₀ + c₁ * t) u : ℂ)
      = ((fun x : ℂ => ∑' n : ℕ, (((n.factorial : ℂ))⁻¹ * (ascPochhammer ℂ n).eval (a₀ + a₁ * t)
          * (ascPochhammer ℂ n).eval (b₀ + b₁ * t)
          * ((ascPochhammer ℂ n).eval (c₀ + c₁ * t))⁻¹) • x ^ n) u)
      from congrFun (ordinaryHypergeometric_eq_tsum _ _ _) u]
    exact tsum_congr fun n => by rw [hgdef]; simp [smul_eq_mul]
  -- each term is differentiable on Ω
  have haff : ∀ (p q : ℂ) (t : ℂ), DifferentiableAt ℂ (fun s : ℂ => p + q * s) t :=
    fun p q t => (differentiableAt_const p).add ((differentiableAt_const q).mul differentiableAt_id)
  have hP : ∀ (n : ℕ) (p q : ℂ) (t : ℂ),
      DifferentiableAt ℂ (fun s : ℂ => (ascPochhammer ℂ n).eval (p + q * s)) t := by
    intro n p q t
    have h := (Polynomial.differentiableAt (p := ascPochhammer ℂ n)
      (x := p + q * t)).comp t (haff p q t)
    simpa [Function.comp_def] using h
  have hgdAt : ∀ (n : ℕ), ∀ t ∈ Ω, DifferentiableAt ℂ (g n) t := by
    intro n t ht
    have hne : (ascPochhammer ℂ n).eval (c₀ + c₁ * t) ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      rintro ⟨k, -, hk⟩
      exact hγ t ht k hk
    exact ((((differentiableAt_const _).mul (hP n a₀ a₁ t)).mul (hP n b₀ b₁ t)).mul
      ((hP n c₀ c₁ t).inv hne)).mul_const (u ^ n)
  -- locally uniform convergence of the partial sums
  have hTLU : TendstoLocallyUniformlyOn
      (fun N : ℕ => fun t : ℂ => ∑ n ∈ Finset.range N, g n t)
      (fun t => ∑' n, g n t) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ]
    intro K hKΩ hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact tendstoUniformlyOn_tsum_nat (u := fun _ : ℕ => (0 : ℝ)) summable_zero
        (fun n x hx => absurd hx (Set.notMem_empty x))
    -- bound the parameters on K
    obtain ⟨r, hKr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R : ℝ := max r 1 with hRdef
    have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
    have hKR : K ⊆ closedBall (0 : ℂ) R :=
      hKr.trans (closedBall_subset_closedBall (le_max_left _ _))
    set A : ℝ := ‖a₀‖ + ‖a₁‖ * R with hAdef
    set B : ℝ := ‖b₀‖ + ‖b₁‖ * R with hBdef
    set C : ℝ := ‖c₀‖ + ‖c₁‖ * R with hCdef
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ B := by positivity
    have hC0 : 0 ≤ C := by positivity
    set N₀ : ℕ := ⌈C⌉₊ with hN₀def
    have hCN : C ≤ N₀ := Nat.le_ceil C
    -- affine bounds on K
    have hnorm_le : ∀ (p q : ℂ) (t : ℂ), t ∈ K → ‖p + q * t‖ ≤ ‖p‖ + ‖q‖ * R := by
      intro p q t ht
      have htR : ‖t‖ ≤ R := by
        have := hKR ht
        rwa [mem_closedBall, dist_zero_right] at this
      calc ‖p + q * t‖ ≤ ‖p‖ + ‖q * t‖ := norm_add_le _ _
        _ = ‖p‖ + ‖q‖ * ‖t‖ := by rw [norm_mul]
        _ ≤ ‖p‖ + ‖q‖ * R := by
            have := mul_le_mul_of_nonneg_left htR (norm_nonneg q)
            linarith
    -- the uniform lower bound δ for the small-k Pochhammer factors
    set T : Set ℂ :=
      ⋃ k ∈ (Finset.range (N₀ + 1) : Set ℕ), (fun t : ℂ => c₀ + c₁ * t + (k : ℂ)) '' K
      with hTdef
    have hTc : IsCompact T := by
      refine (Finset.range (N₀ + 1)).finite_toSet.isCompact_biUnion fun k _ => hK.image ?_
      fun_prop
    have hTne : T.Nonempty := by
      obtain ⟨t, ht⟩ := hKne
      refine ⟨c₀ + c₁ * t + (0 : ℕ), ?_⟩
      rw [hTdef]
      refine Set.mem_biUnion ?_ ⟨t, ht, rfl⟩
      simp
    have hT0 : (0 : ℂ) ∉ T := by
      rw [hTdef]
      intro h
      simp only [Set.mem_iUnion, Set.mem_image] at h
      obtain ⟨k, -, t, ht, hkt⟩ := h
      exact hγ t (hKΩ ht) k (by linear_combination hkt)
    obtain ⟨z₀, hz₀T, hz₀min⟩ := hTc.exists_isMinOn hTne continuous_norm.continuousOn
    set δ : ℝ := min ‖z₀‖ 1 with hδdef
    have hδ0 : 0 < δ := by
      refine lt_min ?_ one_pos
      rw [norm_pos_iff]
      intro h
      rw [h] at hz₀T
      exact hT0 hz₀T
    have hδ1 : δ ≤ 1 := min_le_right _ _
    -- the per-factor lower bound L
    set L : ℕ → ℝ := fun k => if k ≤ N₀ then δ else (k : ℝ) - N₀ with hLdef
    have hL0 : ∀ k, 0 < L k := by
      intro k
      by_cases hk : k ≤ N₀
      · simp only [hLdef, if_pos hk]
        exact hδ0
      · simp only [hLdef, if_neg hk]
        push Not at hk
        have : (N₀ : ℝ) + 1 ≤ k := by exact_mod_cast hk
        linarith
    have hLle : ∀ (k : ℕ) (t : ℂ), t ∈ K → L k ≤ ‖c₀ + c₁ * t + k‖ := by
      intro k t ht
      by_cases hk : k ≤ N₀
      · simp only [hLdef, if_pos hk]
        have hmem : c₀ + c₁ * t + (k : ℂ) ∈ T := by
          rw [hTdef]
          refine Set.mem_biUnion ?_ ⟨t, ht, rfl⟩
          simpa using Nat.lt_succ_of_le hk
        exact le_trans (min_le_left _ _) (hz₀min hmem)
      · simp only [hLdef, if_neg hk]
        push Not at hk
        have h1 : ‖(k : ℂ)‖ ≤ ‖c₀ + c₁ * t + k‖ + ‖c₀ + c₁ * t‖ := by
          calc ‖(k : ℂ)‖ = ‖(c₀ + c₁ * t + k) - (c₀ + c₁ * t)‖ := by ring_nf
            _ ≤ ‖c₀ + c₁ * t + k‖ + ‖c₀ + c₁ * t‖ := norm_sub_le _ _
        have h2 : ‖c₀ + c₁ * t‖ ≤ C := hnorm_le c₀ c₁ t ht
        have h3 : ‖(k : ℂ)‖ = (k : ℝ) := by
          simp
        linarith
    -- the dominating sequence
    set m : ℕ → ℝ := fun k => (A + k) * (B + k) * ‖u‖ / (L k * ((k : ℝ) + 1)) with hmdef
    have hm0 : ∀ k, 0 ≤ m k := by
      intro k
      rw [hmdef]
      have := hL0 k
      positivity
    set M : ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, m k with hMdef
    have hM0 : ∀ n, 0 ≤ M n := fun n => Finset.prod_nonneg fun k _ => hm0 k
    -- the term norm in single-product form
    have hgnorm : ∀ (n : ℕ) (t : ℂ), ‖g n t‖
        = ∏ k ∈ Finset.range n,
            (‖a₀ + a₁ * t + k‖ * ‖b₀ + b₁ * t + k‖ * ‖u‖
              / (‖c₀ + c₁ * t + k‖ * ((k : ℝ) + 1))) := by
      intro n t
      have hfac : (∏ k ∈ Finset.range n, ((k : ℝ) + 1)) = ((n.factorial : ℝ)) := by
        rw [← Finset.prod_range_add_one_eq_factorial n]
        push_cast
        rfl
      rw [hgdef]
      simp only [norm_mul, norm_inv, norm_pow]
      rw [ascPochhammer_eval_eq_prod_range, ascPochhammer_eval_eq_prod_range,
        ascPochhammer_eval_eq_prod_range, norm_prod, norm_prod, norm_prod]
      have hu_pow : ‖u‖ ^ n = ∏ _k ∈ Finset.range n, ‖u‖ := by
        rw [Finset.prod_const, Finset.card_range]
      have hnorms : ∀ (p q : ℂ) (k : ℕ), ‖p + q * t + (k : ℂ)‖ = ‖p + q * t + k‖ := fun _ _ _ => rfl
      rw [show ‖((n.factorial : ℂ))‖ = ((n.factorial : ℝ)) by simp, ← hfac, hu_pow,
        ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [div_eq_mul_inv, mul_inv]
      ring
    -- the termwise bound on K
    have hbound : ∀ (n : ℕ), ∀ t ∈ K, ‖g n t‖ ≤ M n := by
      intro n t ht
      rw [hgnorm n t, hMdef]
      refine Finset.prod_le_prod (fun k _ => ?_) (fun k _ => ?_)
      · positivity
      · rw [hmdef]
        have hLk := hL0 k
        have hLk' := hLle k t ht
        have hγpos : (0 : ℝ) < ‖c₀ + c₁ * t + k‖ := lt_of_lt_of_le hLk hLk'
        have hak : ‖a₀ + a₁ * t + (k : ℂ)‖ ≤ A + k := by
          calc ‖a₀ + a₁ * t + (k : ℂ)‖ ≤ ‖a₀ + a₁ * t‖ + ‖(k : ℂ)‖ := norm_add_le _ _
            _ ≤ A + k := by
                have h1 := hnorm_le a₀ a₁ t ht
                have h2 : ‖(k : ℂ)‖ = (k : ℝ) := by simp
                rw [h2, hAdef]
                linarith
        have hbk : ‖b₀ + b₁ * t + (k : ℂ)‖ ≤ B + k := by
          calc ‖b₀ + b₁ * t + (k : ℂ)‖ ≤ ‖b₀ + b₁ * t‖ + ‖(k : ℂ)‖ := norm_add_le _ _
            _ ≤ B + k := by
                have h1 := hnorm_le b₀ b₁ t ht
                have h2 : ‖(k : ℂ)‖ = (k : ℝ) := by simp
                rw [h2, hBdef]
                linarith
        have hnum : ‖a₀ + a₁ * t + k‖ * ‖b₀ + b₁ * t + k‖ * ‖u‖
            ≤ (A + k) * (B + k) * ‖u‖ := by
          have h1 : ‖a₀ + a₁ * t + k‖ * ‖b₀ + b₁ * t + k‖ ≤ (A + k) * (B + k) :=
            mul_le_mul hak hbk (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg u)
        have hden : L k * ((k : ℝ) + 1) ≤ ‖c₀ + c₁ * t + k‖ * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hLk' (by positivity)
        exact div_le_div₀ (by positivity) hnum (mul_pos (hL0 k) (by positivity)) hden
    -- summability of M via the ratio test
    have hMsum : Summable M := by
      set r : ℝ := (1 + ‖u‖) / 2 with hrdef
      have hr1 : r < 1 := by rw [hrdef]; linarith
      have hur : ‖u‖ < r := by rw [hrdef]; linarith
      -- the factor sequence tends to ‖u‖
      have hm_tendsto : Tendsto m atTop (𝓝 ‖u‖) := by
        have h1 : Tendsto (fun n : ℕ => (A + n) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          have h0 : Tendsto (fun n : ℕ => (A - 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
            have hb0 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (A - 1)
            have := (tendsto_add_atTop_iff_nat 1).mpr hb0
            refine this.congr fun n => ?_
            push_cast
            ring
          have := h0.add tendsto_const_nhds (b := (1 : ℝ))
          rw [zero_add] at this
          refine this.congr fun n => ?_
          have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp
          ring
        have h2 : Tendsto (fun n : ℕ => (B + n) / ((n : ℝ) - N₀)) atTop (𝓝 1) := by
          have h0 : Tendsto (fun n : ℕ => (B + N₀) / ((n : ℝ) - N₀)) atTop (𝓝 0) := by
            refine (tendsto_add_atTop_iff_nat (N₀ + 1)).mp ?_
            have hb0 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (B + N₀)
            have hb1 := (tendsto_add_atTop_iff_nat 1).mpr hb0
            refine hb1.congr fun n => ?_
            push_cast
            ring_nf
          have := h0.add tendsto_const_nhds (b := (1 : ℝ))
          rw [zero_add] at this
          refine this.congr' ?_
          filter_upwards [eventually_ge_atTop (N₀ + 1)] with n hn
          have hne : ((n : ℝ) - N₀) ≠ 0 := by
            have h : (N₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
            exact ne_of_gt (by linarith)
          field_simp
          ring
        have h3 := (h1.mul h2).mul_const ‖u‖
        rw [one_mul, one_mul] at h3
        refine h3.congr' ?_
        filter_upwards [eventually_ge_atTop (N₀ + 1)] with n hn
        have hn' : ¬ (n ≤ N₀) := by omega
        have hne1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hne2 : ((n : ℝ) - N₀) ≠ 0 := by
          have h : (N₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          exact ne_of_gt (by linarith)
        rw [hmdef]
        simp only [hLdef, if_neg hn']
        field_simp
      have hev : ∀ᶠ n in atTop, m n ≤ r :=
        (hm_tendsto.eventually_lt_const hur).mono fun n hn => hn.le
      refine summable_of_ratio_norm_eventually_le hr1 ?_
      filter_upwards [hev] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hM0 (n + 1)),
        abs_of_nonneg (hM0 n), hMdef]
      calc (∏ k ∈ Finset.range (n + 1), m k) = (∏ k ∈ Finset.range n, m k) * m n :=
            Finset.prod_range_succ _ _
        _ ≤ (∏ k ∈ Finset.range n, m k) * r :=
            mul_le_mul_of_nonneg_left hn (hM0 n)
        _ = r * ∏ k ∈ Finset.range n, m k := mul_comm _ _
    exact tendstoUniformlyOn_tsum_nat hMsum fun n t ht => hbound n t ht
  -- the locally uniform limit of differentiable functions is differentiable
  have hdiff : DifferentiableOn ℂ (fun t => ∑' n, g n t) Ω := by
    refine hTLU.differentiableOn (Eventually.of_forall fun N => ?_) hΩ
    intro t ht
    exact (DifferentiableAt.fun_sum fun n _ => hgdAt n t ht).differentiableWithinAt
  rw [hFeq]
  exact hdiff

/-! ### Domain topology: openness and preconnectedness of the parameter domains -/

-- no-dlmf: domain-topology helper, no DLMF counterpart
/-- `{t | f t ∉ ℤ}` is open for continuous `f` (via `sin (π f) ≠ 0`). -/
theorem isOpen_setOf_forall_int_ne {f : ℂ → ℂ} (hf : Continuous f) :
    IsOpen {t : ℂ | ∀ n : ℤ, f t ≠ (n : ℂ)} := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hset : {t : ℂ | ∀ n : ℤ, f t ≠ (n : ℂ)}
      = (fun t => Complex.sin (f t * (Real.pi : ℂ))) ⁻¹' ({0}ᶜ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h h0
      rw [Complex.sin_eq_zero_iff] at h0
      obtain ⟨k, hk⟩ := h0
      exact h k (mul_right_cancel₀ hπ hk)
    · intro h n hn
      exact h (by rw [Complex.sin_eq_zero_iff]; exact ⟨n, by rw [hn]⟩)
  rw [hset]
  exact isOpen_compl_singleton.preimage (Complex.continuous_sin.comp (hf.mul continuous_const))

-- no-dlmf: domain-topology helper, no DLMF counterpart
/-- `{t | -f t ∉ ℕ}` (a series parameter avoiding the nonpositive integers) is
open for continuous `f`: it is `{f ∉ ℤ} ∪ {re f > 0}`. -/
theorem isOpen_setOf_forall_nat_ne_neg {f : ℂ → ℂ} (hf : Continuous f) :
    IsOpen {t : ℂ | ∀ k : ℕ, (k : ℂ) ≠ -f t} := by
  have hset : {t : ℂ | ∀ k : ℕ, (k : ℂ) ≠ -f t}
      = {t : ℂ | ∀ n : ℤ, f t ≠ (n : ℂ)} ∪ (fun t => (f t).re) ⁻¹' (Set.Ioi 0) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      by_cases hint : ∀ n : ℤ, f t ≠ (n : ℂ)
      · exact Or.inl hint
      · push Not at hint
        obtain ⟨n, hn⟩ := hint
        refine Or.inr ?_
        by_contra hre
        push Not at hre
        have hnre : (f t).re = (n : ℝ) := by rw [hn]; simp
        have hn0 : n ≤ 0 := by
          have : ((n : ℝ)) ≤ 0 := hnre ▸ hre
          exact_mod_cast this
        refine h (-n).toNat ?_
        have h1 : (((-n).toNat : ℤ) : ℂ) = ((-n : ℤ) : ℂ) := by
          rw [Int.toNat_of_nonneg (neg_nonneg.mpr hn0)]
        calc ((((-n).toNat : ℕ)) : ℂ) = (((-n).toNat : ℤ) : ℂ) := by push_cast; rfl
          _ = ((-n : ℤ) : ℂ) := h1
          _ = -f t := by rw [hn]; push_cast; ring
    · rintro (h | h) k hk
      · exact h (-(k : ℤ)) (by push_cast; linear_combination hk)
      · have := congrArg Complex.re hk
        simp only [Complex.natCast_re, Complex.neg_re] at this
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
  rw [hset]
  exact (isOpen_setOf_forall_int_ne hf).union (isOpen_Ioi.preimage (Complex.continuous_re.comp hf))

-- no-dlmf: domain-topology helper, no DLMF counterpart
/-- The complement of a countable subset of `ℂ` is preconnected. -/
theorem isPreconnected_compl_countable {s : Set ℂ} (hs : s.Countable) :
    IsPreconnected sᶜ := by
  have h2 : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  exact (hs.isPathConnected_compl_of_one_lt_rank h2).isConnected.isPreconnected

-- no-dlmf: identity-theorem plumbing, no DLMF counterpart
/-- A function vanishing at every real point within `ε` of `x₀` vanishes
frequently in the punctured complex neighborhood of `x₀`. -/
theorem frequently_zero_of_real_seg {D : ℂ → ℂ} {x₀ ε : ℝ} (hε : 0 < ε)
    (hD : ∀ x : ℝ, |x - x₀| < ε → D (x : ℂ) = 0) :
    ∃ᶠ t in 𝓝[≠] (x₀ : ℂ), D t = 0 := by
  have hseq : Tendsto (fun n : ℕ => ((x₀ + ε / (n + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (x₀ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have hb0 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ε
        have := (tendsto_add_atTop_iff_nat 2).mpr hb0
        refine this.congr fun n => ?_
        push_cast
        ring
      have h1 : Tendsto (fun n : ℕ => x₀ + ε / ((n : ℝ) + 2)) atTop (𝓝 (x₀ + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      have := (Complex.continuous_ofReal.tendsto x₀).comp h1
      simpa [Function.comp_def] using this
    · refine Eventually.of_forall fun n => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hreal : x₀ + ε / ((n : ℝ) + 2) = x₀ := by exact_mod_cast h
      have hpos : (0 : ℝ) < ε / ((n : ℝ) + 2) := by positivity
      linarith
  refine hseq.frequently (Frequently.of_forall fun n => hD _ ?_)
  rw [add_sub_cancel_left, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-! ### The connection defect and its parameter analyticity -/

-- no-dlmf: continuation device for DLMF 15.10.21, no equation number
/-- The defect `LHS − RHS` of the connection formula DLMF 15.10.21; the
continuation argument shows it vanishes on the honest parameter domain. -/
def connDefect (z a b c : ℂ) : ℂ :=
  ₂F₁ a b c z
    - (Complex.Gamma c * Complex.Gamma (c - a - b)
        / (Complex.Gamma (c - a) * Complex.Gamma (c - b)) * ₂F₁ a b (a + b - c + 1) (1 - z)
      + Complex.Gamma c * Complex.Gamma (a + b - c) / (Complex.Gamma a * Complex.Gamma b)
        * ((1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)))

-- no-dlmf: parameter-analyticity of the two sides of DLMF 15.10.21, no equation number
/-- Both sides of DLMF 15.10.21 are differentiable along affine parameter paths
on any open set where the `c`-parameter avoids the nonpositive integers and
`c − a − b` avoids the integers (`z` fixed in the lens). -/
theorem differentiableOn_connDefect_param {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1)
    (a₀ a₁ b₀ b₁ c₀ c₁ : ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hc : ∀ t ∈ Ω, ∀ k : ℕ, (k : ℂ) ≠ -(c₀ + c₁ * t))
    (hs : ∀ t ∈ Ω, ∀ n : ℤ,
      (c₀ + c₁ * t) - (a₀ + a₁ * t) - (b₀ + b₁ * t) ≠ (n : ℂ)) :
    DifferentiableOn ℂ
      (fun t => connDefect z (a₀ + a₁ * t) (b₀ + b₁ * t) (c₀ + c₁ * t)) Ω := by
  have hz1' : ‖1 - z‖ < 1 := by rwa [norm_sub_rev] at hz1
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz : z = 1 := by linear_combination -h
    rw [hz] at hz0
    norm_num at hz0
  -- the three series pieces
  have hF1 : DifferentiableOn ℂ
      (fun t => ₂F₁ (a₀ + a₁ * t) (b₀ + b₁ * t) (c₀ + c₁ * t) z) Ω :=
    differentiableOn_ordinaryHypergeometric_param hz0 a₀ a₁ b₀ b₁ c₀ c₁ hΩ hc
  have hF3 : DifferentiableOn ℂ
      (fun t => ₂F₁ (a₀ + a₁ * t) (b₀ + b₁ * t)
        ((a₀ + a₁ * t) + (b₀ + b₁ * t) - (c₀ + c₁ * t) + 1) (1 - z)) Ω := by
    have h := differentiableOn_ordinaryHypergeometric_param hz1' a₀ a₁ b₀ b₁
      (a₀ + b₀ - c₀ + 1) (a₁ + b₁ - c₁) hΩ ?_
    · refine h.congr fun t ht => ?_
      congr 1
      ring
    · intro t ht k hk
      exact hs t ht ((k : ℤ) + 1) (by push_cast; linear_combination -hk)
  have hF4 : DifferentiableOn ℂ
      (fun t => ₂F₁ ((c₀ + c₁ * t) - (a₀ + a₁ * t)) ((c₀ + c₁ * t) - (b₀ + b₁ * t))
        ((c₀ + c₁ * t) - (a₀ + a₁ * t) - (b₀ + b₁ * t) + 1) (1 - z)) Ω := by
    have h := differentiableOn_ordinaryHypergeometric_param hz1' (c₀ - a₀) (c₁ - a₁)
      (c₀ - b₀) (c₁ - b₁) (c₀ - a₀ - b₀ + 1) (c₁ - a₁ - b₁) hΩ ?_
    · refine h.congr fun t ht => ?_
      congr 1 <;> ring
    · intro t ht k hk
      exact hs t ht (-((k : ℤ) + 1)) (by push_cast; linear_combination hk)
  -- pointwise assembly
  intro t ht
  refine DifferentiableAt.differentiableWithinAt ?_
  have hF1At := (hF1.differentiableAt (hΩ.mem_nhds ht))
  have hF3At := (hF3.differentiableAt (hΩ.mem_nhds ht))
  have hF4At := (hF4.differentiableAt (hΩ.mem_nhds ht))
  -- affine inner functions
  have haffc : DifferentiableAt ℂ (fun s : ℂ => c₀ + c₁ * s) t :=
    (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
  have haffs : DifferentiableAt ℂ
      (fun s : ℂ => (c₀ + c₁ * s) - (a₀ + a₁ * s) - (b₀ + b₁ * s)) t := by
    fun_prop
  have haffs' : DifferentiableAt ℂ
      (fun s : ℂ => (a₀ + a₁ * s) + (b₀ + b₁ * s) - (c₀ + c₁ * s)) t := by
    fun_prop
  have haffca : DifferentiableAt ℂ (fun s : ℂ => (c₀ + c₁ * s) - (a₀ + a₁ * s)) t := by
    fun_prop
  have haffcb : DifferentiableAt ℂ (fun s : ℂ => (c₀ + c₁ * s) - (b₀ + b₁ * s)) t := by
    fun_prop
  have haffa : DifferentiableAt ℂ (fun s : ℂ => a₀ + a₁ * s) t := by fun_prop
  have haffb : DifferentiableAt ℂ (fun s : ℂ => b₀ + b₁ * s) t := by fun_prop
  -- Γ factors
  have hΓc : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (c₀ + c₁ * s)) t := by
    have hpole : ∀ mn : ℕ, (c₀ + c₁ * t) ≠ -(mn : ℂ) := by
      intro mn hmn
      exact hc t ht mn (by linear_combination hmn)
    have h := (Complex.differentiableAt_Gamma _ hpole).comp t haffc
    simpa [Function.comp_def] using h
  have hΓs : DifferentiableAt ℂ
      (fun s : ℂ => Complex.Gamma ((c₀ + c₁ * s) - (a₀ + a₁ * s) - (b₀ + b₁ * s))) t := by
    have hpole : ∀ mn : ℕ,
        ((c₀ + c₁ * t) - (a₀ + a₁ * t) - (b₀ + b₁ * t)) ≠ -(mn : ℂ) := by
      intro mn hmn
      exact hs t ht (-(mn : ℤ)) (by push_cast; linear_combination hmn)
    have h := (Complex.differentiableAt_Gamma _ hpole).comp t haffs
    simpa [Function.comp_def] using h
  have hΓs' : DifferentiableAt ℂ
      (fun s : ℂ => Complex.Gamma ((a₀ + a₁ * s) + (b₀ + b₁ * s) - (c₀ + c₁ * s))) t := by
    have hpole : ∀ mn : ℕ,
        ((a₀ + a₁ * t) + (b₀ + b₁ * t) - (c₀ + c₁ * t)) ≠ -(mn : ℂ) := by
      intro mn hmn
      exact hs t ht (mn : ℤ) (by push_cast; linear_combination -hmn)
    have h := (Complex.differentiableAt_Gamma _ hpole).comp t haffs'
    simpa [Function.comp_def] using h
  -- entire reciprocal Γ factors
  have hΓinv : ∀ {f : ℂ → ℂ}, DifferentiableAt ℂ f t →
      DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma (f s))⁻¹) t := by
    intro f hf
    have h := (Complex.differentiable_one_div_Gamma (f t)).comp t hf
    simpa [Function.comp_def] using h
  -- the power factor
  have hpow : DifferentiableAt ℂ
      (fun s : ℂ => (1 - z) ^ ((c₀ + c₁ * s) - (a₀ + a₁ * s) - (b₀ + b₁ * s))) t :=
    haffs.const_cpow (Or.inl h1z)
  -- assemble
  simp only [connDefect, div_eq_mul_inv, mul_inv]
  refine hF1At.sub (DifferentiableAt.add ?_ ?_)
  · exact ((hΓc.mul hΓs).mul ((hΓinv haffca).mul (hΓinv haffcb))).mul hF3At
  · exact ((hΓc.mul hΓs').mul ((hΓinv haffa).mul (hΓinv haffb))).mul (hpow.mul hF4At)

-- no-dlmf: restatement of the proven real-parameter surface of DLMF 15.10.21
/-- The proven real-parameter regime, as vanishing of the defect. -/
theorem connDefect_eq_zero_of_real {a b c : ℝ} (ha : ∀ k : ℕ, (k : ℝ) ≠ -a) (hb : 0 < b)
    (hbc : b < c) (hs : a + b < c) (hc1 : c < 1) (hac : c < a + 1)
    {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    connDefect z (a : ℂ) (b : ℂ) (c : ℂ) = 0 := by
  unfold connDefect
  rw [sub_eq_zero]
  exact ordinaryHypergeometric_one_sub_connection ha hb hbc hs hc1 hac hz0 hz1

/-! ### The three continuation steps -/

-- no-dlmf: continuation step (complex `a`) toward DLMF 15.10.21, no equation number
/-- Step 1: the connection formula for complex `a`, real `0 < b < c < 1`,
`c − a − b ∉ ℤ`. -/
theorem connDefect_eq_zero_step_a {b c : ℝ} (hb : 0 < b) (hbc : b < c) (hc1 : c < 1)
    {a : ℂ} (hs : ∀ n : ℤ, (c : ℂ) - a - b ≠ (n : ℂ))
    {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    connDefect z a (b : ℂ) (c : ℂ) = 0 := by
  have hc0 : 0 < c := lt_trans hb hbc
  set Ω : Set ℂ := {t : ℂ | ∀ n : ℤ, (c : ℂ) - t - b ≠ (n : ℂ)} with hΩdef
  have hΩo : IsOpen Ω := isOpen_setOf_forall_int_ne (f := fun t : ℂ => (c : ℂ) - t - b)
    (by fun_prop)
  have hΩpre : IsPreconnected Ω := by
    have hcompl : Ω = (Set.range fun n : ℤ => (c : ℂ) - b - n)ᶜ := by
      ext t
      simp only [hΩdef, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      constructor
      · intro h n hn
        exact h n (by linear_combination hn)
      · intro h n hn
        exact h n (by linear_combination hn)
    rw [hcompl]
    exact isPreconnected_compl_countable (Set.countable_range _)
  -- analyticity of the defect in `a`
  have hD : AnalyticOnNhd ℂ (fun t => connDefect z t (b : ℂ) (c : ℂ)) Ω := by
    have h := differentiableOn_connDefect_param hz0 hz1 0 1 (b : ℂ) 0 (c : ℂ) 0 hΩo
      (fun t _ k hk => by
        have : (k : ℂ) = -(c : ℂ) := by linear_combination hk
        have hre := congrArg Complex.re this
        simp only [Complex.natCast_re, Complex.neg_re, Complex.ofReal_re] at hre
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
      (fun t ht n hn => ht n (by linear_combination hn))
    have hfun : (fun t : ℂ => connDefect z (0 + 1 * t) ((b : ℂ) + 0 * t) ((c : ℂ) + 0 * t))
        = fun t => connDefect z t (b : ℂ) (c : ℂ) := by
      funext s
      norm_num
    rw [hfun] at h
    exact h.analyticOnNhd hΩo
  -- the real anchor
  set x₀ : ℝ := (c - b) / 2 with hx₀def
  have hx₀Ω : ((x₀ : ℝ) : ℂ) ∈ Ω := by
    intro n hn
    have hreal : c - x₀ - b = (n : ℝ) := by
      exact_mod_cast (show ((c - x₀ - b : ℝ) : ℂ) = (n : ℂ) by push_cast; linear_combination hn)
    have h1 : 0 < c - x₀ - b := by rw [hx₀def]; linarith
    have h2 : c - x₀ - b < 1 := by rw [hx₀def]; linarith
    have hn0 : (0 : ℤ) < n := by exact_mod_cast hreal ▸ h1
    have hn1 : n < (1 : ℤ) := by exact_mod_cast hreal ▸ h2
    omega
  -- frequent vanishing near the anchor: the proven real regime
  have hfreq : ∃ᶠ t in 𝓝[≠] ((x₀ : ℝ) : ℂ), (fun t => connDefect z t (b : ℂ) (c : ℂ)) t = 0 := by
    refine frequently_zero_of_real_seg (ε := (c - b) / 2) (by linarith) ?_
    intro x hx
    rw [abs_lt] at hx
    have hx1 : 0 < x := by rw [hx₀def] at hx; linarith [hx.1]
    have hx2 : x + b < c := by rw [hx₀def] at hx; linarith [hx.2]
    exact connDefect_eq_zero_of_real
      (fun k => by have := Nat.cast_nonneg (α := ℝ) k; intro h; linarith)
      hb hbc hx2 hc1 (by linarith) hz0 hz1
  have hEq : Set.EqOn (fun t => connDefect z t (b : ℂ) (c : ℂ)) 0 Ω :=
    hD.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩpre hx₀Ω hfreq
  have haΩ : a ∈ Ω := fun n => hs n
  simpa using hEq haΩ

-- no-dlmf: continuation step (complex `a`, `b`) toward DLMF 15.10.21, no equation number
/-- Step 2: the connection formula for complex `a`, `b`, real `0 < c < 1`,
`c − a − b ∉ ℤ`. -/
theorem connDefect_eq_zero_step_b {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {a b : ℂ} (hs : ∀ n : ℤ, (c : ℂ) - a - b ≠ (n : ℂ))
    {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    connDefect z a b (c : ℂ) = 0 := by
  set Ω : Set ℂ := {t : ℂ | ∀ n : ℤ, (c : ℂ) - a - t ≠ (n : ℂ)} with hΩdef
  have hΩo : IsOpen Ω := isOpen_setOf_forall_int_ne (f := fun t : ℂ => (c : ℂ) - a - t)
    (by fun_prop)
  have hΩpre : IsPreconnected Ω := by
    have hcompl : Ω = (Set.range fun n : ℤ => (c : ℂ) - a - n)ᶜ := by
      ext t
      simp only [hΩdef, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      constructor
      · intro h n hn
        exact h n (by linear_combination hn)
      · intro h n hn
        exact h n (by linear_combination hn)
    rw [hcompl]
    exact isPreconnected_compl_countable (Set.countable_range _)
  have hD : AnalyticOnNhd ℂ (fun t => connDefect z a t (c : ℂ)) Ω := by
    have h := differentiableOn_connDefect_param hz0 hz1 a 0 0 1 (c : ℂ) 0 hΩo
      (fun t _ k hk => by
        have : (k : ℂ) = -(c : ℂ) := by linear_combination hk
        have hre := congrArg Complex.re this
        simp only [Complex.natCast_re, Complex.neg_re, Complex.ofReal_re] at hre
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
      (fun t ht n hn => ht n (by linear_combination hn))
    have hfun : (fun t : ℂ => connDefect z (a + 0 * t) (0 + 1 * t) ((c : ℂ) + 0 * t))
        = fun t => connDefect z a t (c : ℂ) := by
      funext s
      norm_num
    rw [hfun] at h
    exact h.analyticOnNhd hΩo
  -- pick a good real anchor `y₀ ∈ (0, c)`: at most one point of `(0,c)` is bad
  have hcand : ∃ y₀ : ℝ, 0 < y₀ ∧ y₀ < c ∧ ((y₀ : ℝ) : ℂ) ∈ Ω := by
    by_cases h1 : ((c / 3 : ℝ) : ℂ) ∈ Ω
    · exact ⟨c / 3, by linarith, by linarith, h1⟩
    · refine ⟨2 * c / 3, by linarith, by linarith, ?_⟩
      simp only [hΩdef, Set.mem_setOf_eq, not_forall, not_not] at h1
      obtain ⟨n₁, hn₁⟩ := h1
      intro n₂ hn₂
      have hint : ((c / 3 : ℝ) : ℂ) = ((n₁ - n₂ : ℤ) : ℂ) := by
        push_cast at hn₁ hn₂ ⊢
        linear_combination hn₁ - hn₂
      have hreal : (c / 3 : ℝ) = ((n₁ - n₂ : ℤ) : ℝ) := by exact_mod_cast hint
      have h1' : (0 : ℤ) < n₁ - n₂ := by
        have : (0 : ℝ) < ((n₁ - n₂ : ℤ) : ℝ) := hreal ▸ (by linarith)
        exact_mod_cast this
      have h2' : (n₁ - n₂ : ℤ) < 1 := by
        have : ((n₁ - n₂ : ℤ) : ℝ) < 1 := hreal ▸ (by linarith)
        exact_mod_cast this
      omega
  obtain ⟨y₀, hy₀0, hy₀c, hy₀Ω⟩ := hcand
  -- frequent vanishing near the anchor, from Step 1
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp hΩo _ hy₀Ω
  have hfreq : ∃ᶠ t in 𝓝[≠] ((y₀ : ℝ) : ℂ), (fun t => connDefect z a t (c : ℂ)) t = 0 := by
    refine frequently_zero_of_real_seg (ε := min ε₁ (min y₀ (c - y₀)))
      (lt_min hε₁ (lt_min hy₀0 (by linarith))) ?_
    intro x hx
    have hx1 : |x - y₀| < ε₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : |x - y₀| < y₀ := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
    have hx3 : |x - y₀| < c - y₀ :=
      lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_right _ _))
    rw [abs_lt] at hx2 hx3
    have hx0 : 0 < x := by linarith [hx2.1]
    have hxc : x < c := by linarith [hx3.2]
    have hxΩ : ((x : ℝ) : ℂ) ∈ Ω := by
      refine hball ?_
      rw [mem_ball, Complex.dist_eq,
        show ((x : ℝ) : ℂ) - ((y₀ : ℝ) : ℂ) = ((x - y₀ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hx1
    exact connDefect_eq_zero_step_a hx0 hxc hc1
      (fun n hn => hxΩ n (by linear_combination hn)) hz0 hz1
  have hEq : Set.EqOn (fun t => connDefect z a t (c : ℂ)) 0 Ω :=
    hD.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩpre hy₀Ω hfreq
  have hbΩ : b ∈ Ω := fun n => hs n
  simpa using hEq hbΩ

-- no-dlmf: continuation step (complex `a`, `b`, `c`) toward DLMF 15.10.21, no equation number
/-- Step 3: the connection formula for complex `a`, `b`, `c` with `c` off the
nonpositive integers and `c − a − b ∉ ℤ`. -/
theorem connDefect_eq_zero_step_c {a b c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ))
    {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    connDefect z a b c = 0 := by
  set Ω : Set ℂ :=
    {t : ℂ | ∀ k : ℕ, (k : ℂ) ≠ -t} ∩ {t : ℂ | ∀ n : ℤ, t - a - b ≠ (n : ℂ)} with hΩdef
  have hΩo : IsOpen Ω :=
    (isOpen_setOf_forall_nat_ne_neg continuous_id).inter
      (isOpen_setOf_forall_int_ne (f := fun t : ℂ => t - a - b) (by fun_prop))
  have hΩpre : IsPreconnected Ω := by
    have hcompl : Ω
        = ((Set.range fun k : ℕ => -(k : ℂ)) ∪ (Set.range fun n : ℤ => a + b + n))ᶜ := by
      ext t
      simp only [hΩdef, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff,
        Set.mem_union, Set.mem_range, not_or, not_exists]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun k hk => h1 k (by linear_combination -hk),
          fun n hn => h2 n (by linear_combination -hn)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun k hk => h1 k (by linear_combination -hk),
          fun n hn => h2 n (by linear_combination -hn)⟩
    rw [hcompl]
    exact isPreconnected_compl_countable
      ((Set.countable_range _).union (Set.countable_range _))
  have hD : AnalyticOnNhd ℂ (fun t => connDefect z a b t) Ω := by
    have h := differentiableOn_connDefect_param hz0 hz1 a 0 b 0 0 1 hΩo
      (fun t ht k hk => ht.1 k (by linear_combination hk))
      (fun t ht n hn => ht.2 n (by linear_combination hn))
    have hfun : (fun t : ℂ => connDefect z (a + 0 * t) (b + 0 * t) (0 + 1 * t))
        = fun t => connDefect z a b t := by
      funext s
      norm_num
    rw [hfun] at h
    exact h.analyticOnNhd hΩo
  -- pick a good real anchor `s₀ ∈ (0, 1)`
  have hcand : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ < 1 ∧ ((s₀ : ℝ) : ℂ) ∈ Ω := by
    have hnat : ∀ s₀ : ℝ, 0 < s₀ → ∀ k : ℕ, (k : ℂ) ≠ -((s₀ : ℝ) : ℂ) := by
      intro s₀ hs₀ k hk
      have hre := congrArg Complex.re hk
      simp only [Complex.natCast_re, Complex.neg_re, Complex.ofReal_re] at hre
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    by_cases h1 : ∀ n : ℤ, ((1 / 3 : ℝ) : ℂ) - a - b ≠ (n : ℂ)
    · exact ⟨1 / 3, by norm_num, by norm_num, ⟨hnat _ (by norm_num), h1⟩⟩
    · refine ⟨2 / 3, by norm_num, by norm_num, ⟨hnat _ (by norm_num), ?_⟩⟩
      push Not at h1
      obtain ⟨n₁, hn₁⟩ := h1
      intro n₂ hn₂
      have hint : ((1 / 3 : ℝ) : ℂ) = ((n₂ - n₁ : ℤ) : ℂ) := by
        push_cast at hn₁ hn₂ ⊢
        linear_combination hn₂ - hn₁
      have hreal : (1 / 3 : ℝ) = ((n₂ - n₁ : ℤ) : ℝ) := by exact_mod_cast hint
      have h1' : (0 : ℤ) < n₂ - n₁ := by
        have : (0 : ℝ) < ((n₂ - n₁ : ℤ) : ℝ) := hreal ▸ (by norm_num)
        exact_mod_cast this
      have h2' : (n₂ - n₁ : ℤ) < 1 := by
        have : ((n₂ - n₁ : ℤ) : ℝ) < 1 := hreal ▸ (by norm_num)
        exact_mod_cast this
      omega
  obtain ⟨s₀, hs₀0, hs₀1, hs₀Ω⟩ := hcand
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp hΩo _ hs₀Ω
  have hfreq : ∃ᶠ t in 𝓝[≠] ((s₀ : ℝ) : ℂ), (fun t => connDefect z a b t) t = 0 := by
    refine frequently_zero_of_real_seg (ε := min ε₁ (min s₀ (1 - s₀)))
      (lt_min hε₁ (lt_min hs₀0 (by linarith))) ?_
    intro x hx
    have hx1 : |x - s₀| < ε₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : |x - s₀| < s₀ := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
    have hx3 : |x - s₀| < 1 - s₀ :=
      lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_right _ _))
    rw [abs_lt] at hx2 hx3
    have hx0 : 0 < x := by linarith [hx2.1]
    have hxc : x < 1 := by linarith [hx3.2]
    have hxΩ : ((x : ℝ) : ℂ) ∈ Ω := by
      refine hball ?_
      rw [mem_ball, Complex.dist_eq,
        show ((x : ℝ) : ℂ) - ((s₀ : ℝ) : ℂ) = ((x - s₀ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hx1
    exact connDefect_eq_zero_step_b hx0 hxc
      (fun n hn => hxΩ.2 n (by linear_combination hn)) hz0 hz1
  have hEq : Set.EqOn (fun t => connDefect z a b t) 0 Ω :=
    hD.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩpre hs₀Ω hfreq
  have hcΩ : c ∈ Ω := ⟨fun k => hc k, fun n => hs n⟩
  simpa using hEq hcΩ

/-! ### The connection formula at complex parameters (DLMF 15.10.21) -/

/-- **Gauss's `z = 1` connection formula at complex parameters** (DLMF
15.10.21; equivalently DLMF 15.8.4 in **F**-normalized form): for complex
`a b c` with `c` off the nonpositive integers and `c − a − b ∉ ℤ` — the honest
DLMF non-degeneracy domain — and `z` in the lens `‖z‖ < 1`, `‖z − 1‖ < 1`,

`₂F₁(a,b;c;z) = [Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))] ₂F₁(a,b;a+b−c+1;1−z)
  + [Γ(c)Γ(a+b−c)/(Γ(a)Γ(b))] (1−z)^{c−a−b} ₂F₁(c−a,c−b;c−a−b+1;1−z)`.

Extends the proven real-parameter instance
(`ordinaryHypergeometric_one_sub_connection`) by analytic continuation in the
parameters, one variable at a time (both sides are analytic in each parameter
separately on the non-degeneracy domain, and the real regime accumulates in
every slice).  At the removable points (`a`, `b`, `c−a`, or `c−b` a nonpositive
integer) the Γ-coefficients take their limiting values, since Mathlib's `Γ`
vanishes at the poles and `1/Γ` is entire.

DLMF 15.10.21.
Numerical: PASS
Verified: unverified
DAG: E-15.10.21.
-/
theorem ordinaryHypergeometric_one_sub_connection_complex {a b c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ))
    {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    ₂F₁ a b c z
      = Complex.Gamma c * Complex.Gamma (c - a - b)
          / (Complex.Gamma (c - a) * Complex.Gamma (c - b))
          * ₂F₁ a b (a + b - c + 1) (1 - z)
        + Complex.Gamma c * Complex.Gamma (a + b - c)
          / (Complex.Gamma a * Complex.Gamma b)
          * ((1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)) := by
  have h := connDefect_eq_zero_step_c hc hs hz0 hz1
  unfold connDefect at h
  exact sub_eq_zero.mp h

end FLMF.Hypergeometric
