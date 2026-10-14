import Mathlib

/-!
# Re-expansion of a power series at a new origin (DLMF 1.10(vii), slice L1–L2)

This file is the first slice of the **series-reversion Methods node** for
DLMF §1.10(vii) (reversion of power series).  It supplies the two purely
analytic ingredients that the reversion node needs and that Mathlib
(v4.30.0) does not provide in scalar form:

* **L1 — scalar binomial re-expansion.**  If `∑ cₙ zⁿ` converges absolutely on
  the disc of radius `r` and `‖x‖ + ‖y‖ < r`, then

  `∑' n, cₙ (x + y)ⁿ = ∑' k, (∑' m, C(m+k, k) c_{m+k} xᵐ) yᵏ`,

  together with the two summability facts that make each side meaningful and
  the corollary that `y ↦ ∑' n, cₙ (x + y)ⁿ` has a power-series expansion on
  the ball of radius `r - ‖x‖` with coefficients
  `d k = ∑' m, C(m+k, k) c_{m+k} xᵐ`.
  (This is the scalar/binomial shadow of
  `FormalMultilinearSeries.changeOrigin`, which Mathlib only develops in
  multilinear/`Sigma` form.)

* **L2 — nonnegative-coefficient radius transfer (real Pringsheim step).**
  If all `cₙ ≥ 0` and the re-expansion at `a ∈ [0, r)` converges at `b ≥ 0`,
  then the *original* series already converges at `a + b`.  Equivalently: for
  nonnegative coefficients the radius of convergence cannot be improved by
  re-expanding at an interior point.  This is the form of Pringsheim's
  theorem needed to push a Taylor radius out to the nearest genuine
  singularity without complex analysis.

Together these feed the blocked entry `FLMF.Error.erf_7_17_2` (DLMF 7.17.2,
the Maclaurin series of `inverf`), whose route needs L1 + L2 to certify that
the Taylor radius of `inverf` at `0` is at least `1`.

Everything here is stated for a general `RCLike` scalar field where that costs
nothing; L2 is genuinely real (it uses the order).

All declarations are analytic support lemmas, not DLMF displays.
-/

namespace FLMF.Methods

open Finset Filter

/-! ## A shape-adapted binomial theorem -/

-- no-dlmf: support lemma — binomial theorem in antidiagonal form with the
-- binomial coefficient indexed by the *second* component, the shape used by
-- every re-expansion computation below
/-- Binomial theorem, antidiagonal form, with the coefficient on the second
index: `∑_{i+j=n} C(n,j) xⁱ yʲ = (x + y)ⁿ`. -/
theorem sum_antidiagonal_choose_snd {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    ∑ p ∈ antidiagonal n, (n.choose p.2 : R) * (x ^ p.1 * y ^ p.2) = (x + y) ^ n := by
  rw [Commute.add_pow' (Commute.all x y) n]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h1 : p.1 ≤ n := hp ▸ Nat.le_add_right p.1 p.2
  have h2 : n - p.1 = p.2 := by omega
  have hsym : n.choose p.2 = n.choose p.1 := by
    rw [← Nat.choose_symm h1, h2]
  rw [nsmul_eq_mul, hsym]

/-! ## L1: absolute summability of the re-expanded double family -/

variable {𝕜 : Type*} [RCLike 𝕜]

-- no-dlmf: L1 step 1 — absolute summability of the re-expansion double family
/-- **L1 (summability core).**  If `∑ ‖cₙ‖ rⁿ < ∞` and `a, b ≥ 0` with
`a + b < r`, the double family `C(m+k, k) ‖c_{m+k}‖ aᵐ bᵏ` is summable over
`ℕ × ℕ`.  (Grouping by `n = m + k` turns it into `∑ ‖cₙ‖ (a+b)ⁿ`.) -/
theorem summable_reexpand_norm {c : ℕ → 𝕜} {r a b : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < r) :
    Summable fun p : ℕ × ℕ =>
      ((p.1 + p.2).choose p.2 : ℝ) * ‖c (p.1 + p.2)‖ * a ^ p.1 * b ^ p.2 := by
  set G : ℕ × ℕ → ℝ := fun p =>
    ((p.1 + p.2).choose p.2 : ℝ) * ‖c (p.1 + p.2)‖ * a ^ p.1 * b ^ p.2 with hG
  have hGnn : ∀ p : ℕ × ℕ, 0 ≤ G p := by
    intro p; rw [hG]; positivity
  have hcs : Summable fun n => ‖c n‖ * (a + b) ^ n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hc
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hab.le n) (norm_nonneg _)
  have hfib : ∀ n : ℕ, ∑ p ∈ antidiagonal n, G p = ‖c n‖ * (a + b) ^ n := by
    intro n
    rw [← sum_antidiagonal_choose_snd a b n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hG]
    simp only [hp]
    ring
  rw [← Finset.sigmaAntidiagonalEquivProd.summable_iff]
  refine (summable_sigma_of_nonneg (fun q => hGnn _)).mpr ⟨fun n => Summable.of_finite, ?_⟩
  refine hcs.congr fun n => ?_
  rw [← hfib n, ← Finset.tsum_subtype (antidiagonal n) G]
  rfl

-- no-dlmf: L1 step 2 — the inner (re-expansion coefficient) series converges
/-- **L1 (i), norm form.**  For every `k`, the series defining the `k`-th
re-expansion coefficient converges absolutely whenever `0 ≤ a < r`. -/
theorem summable_reexpand_inner_norm {c : ℕ → 𝕜} {r a : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) (ha : 0 ≤ a) (har : a < r) (k : ℕ) :
    Summable fun m : ℕ => ((m + k).choose k : ℝ) * ‖c (m + k)‖ * a ^ m := by
  have hb : (0 : ℝ) < (r - a) / 2 := by linarith
  have hab : a + (r - a) / 2 < r := by linarith
  have h := summable_reexpand_norm hc ha hb.le hab
  have h2 : Summable fun m : ℕ =>
      ((m + k).choose k : ℝ) * ‖c (m + k)‖ * a ^ m * ((r - a) / 2) ^ k :=
    h.prod_symm.prod_factor k
  exact (summable_mul_right_iff (pow_ne_zero k hb.ne')).mp h2

-- no-dlmf: L1 step 2' — the same inner series, scalar-valued
/-- **L1 (i).**  For every `k`, the `k`-th re-expansion coefficient
`d k = ∑' m, C(m+k, k) c_{m+k} xᵐ` is a convergent (absolutely convergent)
series whenever `‖x‖ < r`. -/
theorem summable_reexpand_inner {c : ℕ → 𝕜} {r : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) {x : 𝕜} (hx : ‖x‖ < r) (k : ℕ) :
    Summable fun m : ℕ => ((m + k).choose k : 𝕜) * c (m + k) * x ^ m := by
  refine Summable.of_norm ?_
  refine (summable_reexpand_inner_norm hc (norm_nonneg x) hx k).congr fun m => ?_
  simp [norm_mul, norm_pow]

-- no-dlmf: L1 step 3 — the outer series converges geometrically in `b`
/-- **L1 (ii), norm form.**  The outer series `∑ (∑' m, C(m+k,k) ‖c_{m+k}‖ aᵐ) bᵏ`
converges whenever `a, b ≥ 0` and `a + b < r`. -/
theorem summable_reexpand_outer_norm {c : ℕ → 𝕜} {r a b : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < r) :
    Summable fun k : ℕ =>
      (∑' m : ℕ, ((m + k).choose k : ℝ) * ‖c (m + k)‖ * a ^ m) * b ^ k := by
  have har : a < r := by linarith
  have h := (summable_reexpand_norm hc ha hb hab).prod_symm.prod
  refine h.congr fun k => ?_
  exact (summable_reexpand_inner_norm hc ha har k).tsum_mul_right (b ^ k)

-- no-dlmf: L1 step 3' — outer summability for the scalar coefficients
/-- **L1 (ii).**  The outer series `∑ ‖d k‖ bᵏ` converges whenever
`‖x‖ + b < r`, where `d k = ∑' m, C(m+k,k) c_{m+k} xᵐ`. -/
theorem summable_reexpand_outer {c : ℕ → 𝕜} {r b : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) {x : 𝕜} (hb : 0 ≤ b) (hab : ‖x‖ + b < r) :
    Summable fun k : ℕ =>
      ‖∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m‖ * b ^ k := by
  have hx : ‖x‖ < r := by linarith
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_reexpand_outer_norm hc (norm_nonneg x) hb hab)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · exact (summable_reexpand_inner_norm hc (norm_nonneg x) hx k).congr fun m => by
      simp [norm_mul, norm_pow]
  · exact tsum_congr fun m => by simp [norm_mul, norm_pow]

/-! ## L1: the re-expansion identity -/

set_option maxHeartbeats 400000 in
-- no-dlmf: L1 main identity — scalar binomial re-expansion at a new origin
/-- **L1.**  Scalar binomial re-expansion of a power series at a new origin.
If `∑ ‖cₙ‖ rⁿ < ∞` and `‖x‖ + ‖y‖ < r`, then

`∑' n, cₙ (x + y)ⁿ = ∑' k, (∑' m, C(m+k,k) c_{m+k} xᵐ) yᵏ`.

This is the scalar shadow of `FormalMultilinearSeries.changeOrigin`. -/
theorem tsum_reexpand {c : ℕ → 𝕜} {r : ℝ} (hc : Summable fun n => ‖c n‖ * r ^ n)
    {x y : 𝕜} (hxy : ‖x‖ + ‖y‖ < r) :
    ∑' n : ℕ, c n * (x + y) ^ n
      = ∑' k : ℕ, (∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m) * y ^ k := by
  have hx : ‖x‖ < r := by have := norm_nonneg y; linarith
  set F : ℕ × ℕ → 𝕜 := fun p =>
    ((p.1 + p.2).choose p.2 : 𝕜) * c (p.1 + p.2) * x ^ p.1 * y ^ p.2 with hF
  have hFn : ∀ p : ℕ × ℕ, ‖F p‖ =
      ((p.1 + p.2).choose p.2 : ℝ) * ‖c (p.1 + p.2)‖ * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 := by
    intro p
    rw [hF]
    simp [norm_mul, norm_pow]
  have hnorm : Summable fun p : ℕ × ℕ => ‖F p‖ :=
    (summable_reexpand_norm hc (norm_nonneg x) (norm_nonneg y) hxy).congr fun p => (hFn p).symm
  have hsum : Summable F := hnorm.of_norm
  have hsig : Summable fun q : (n : ℕ) × {p : ℕ × ℕ // p ∈ antidiagonal n} =>
      F (Finset.sigmaAntidiagonalEquivProd q) :=
    Finset.sigmaAntidiagonalEquivProd.summable_iff.mpr hsum
  have hleft : ∑' p : ℕ × ℕ, F p = ∑' n : ℕ, c n * (x + y) ^ n := by
    rw [← Finset.sigmaAntidiagonalEquivProd.tsum_eq F, hsig.tsum_sigma]
    refine tsum_congr fun n => ?_
    have hfin : ∑' p : {p : ℕ × ℕ // p ∈ antidiagonal n},
        F (Finset.sigmaAntidiagonalEquivProd ⟨n, p⟩) = ∑ p ∈ antidiagonal n, F p :=
      Finset.tsum_subtype (antidiagonal n) F
    rw [hfin, ← sum_antidiagonal_choose_snd x y n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hF]
    simp only [hp]
    ring
  have hprod : ∑' p : ℕ × ℕ, F p = ∑' m : ℕ, ∑' k : ℕ, F (m, k) := hsum.tsum_prod
  have hcomm : ∑' k : ℕ, ∑' m : ℕ, F (m, k) = ∑' m : ℕ, ∑' k : ℕ, F (m, k) :=
    Summable.tsum_comm (f := fun m k => F (m, k)) hsum
  have hy : ∀ k : ℕ, ∑' m : ℕ, F (m, k)
      = (∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m) * y ^ k := fun k =>
    (summable_reexpand_inner hc hx k).tsum_mul_right (y ^ k)
  rw [← hleft, hprod, ← hcomm]
  exact tsum_congr hy

-- no-dlmf: L1 (iii), HasSum form
/-- **L1 (iii), `HasSum` form.**  Under `‖x‖ + ‖y‖ < r` the re-expanded series
actually *sums* to the original value. -/
theorem hasSum_reexpand {c : ℕ → 𝕜} {r : ℝ} (hc : Summable fun n => ‖c n‖ * r ^ n)
    {x y : 𝕜} (hxy : ‖x‖ + ‖y‖ < r) :
    HasSum (fun k : ℕ => (∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m) * y ^ k)
      (∑' n : ℕ, c n * (x + y) ^ n) := by
  have hsummable :
      Summable fun k : ℕ =>
        (∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m) * y ^ k := by
    refine Summable.of_norm ?_
    refine (summable_reexpand_outer hc (norm_nonneg y) hxy).congr fun k => ?_
    rw [norm_mul, norm_pow]
  rw [tsum_reexpand hc hxy]
  exact hsummable.hasSum

/-! ## L1 (iii): the re-expansion as a power series -/

-- no-dlmf: L1 (iii) — the re-expansion is a power series on the shifted ball
/-- **L1 (iii).**  `y ↦ ∑' n, cₙ (x + y)ⁿ` is given by the power series with
coefficients `d k = ∑' m, C(m+k,k) c_{m+k} xᵐ` on the ball of radius
`r - ‖x‖` centred at `0`. -/
theorem hasFPowerSeriesOnBall_reexpand {c : ℕ → 𝕜} {r : ℝ}
    (hc : Summable fun n => ‖c n‖ * r ^ n) {x : 𝕜} (hx : ‖x‖ < r) :
    HasFPowerSeriesOnBall (fun y : 𝕜 => ∑' n : ℕ, c n * (x + y) ^ n)
      (FormalMultilinearSeries.ofScalars 𝕜
        (fun k => ∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m))
      0 (ENNReal.ofReal (r - ‖x‖)) where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have ht' : (t : ℝ) < r - ‖x‖ := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp ht
      simpa using this
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    refine (summable_reexpand_outer hc t.coe_nonneg (by linarith)).congr fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_norm]
  r_pos := by
    simp only [ENNReal.ofReal_pos]
    linarith
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r - ‖x‖ := by
      rw [mem_eball_zero_iff] at hy
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hy
      simpa using this
    have h := hasSum_reexpand hc (x := x) (y := y) (by linarith)
    have happ : ∀ n : ℕ,
        (FormalMultilinearSeries.ofScalars 𝕜
            (fun k => ∑' m : ℕ, ((m + k).choose k : 𝕜) * c (m + k) * x ^ m) n)
          (fun _ => y)
          = (∑' m : ℕ, ((m + n).choose n : 𝕜) * c (m + n) * x ^ m) * y ^ n := by
      intro n
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    simpa only [happ, zero_add] using h

-- no-dlmf: L1 (iii) corollary
/-- **L1 (iii), analyticity form.**  `y ↦ ∑' n, cₙ (x + y)ⁿ` is analytic at `0`
whenever `‖x‖ < r`. -/
theorem analyticAt_reexpand {c : ℕ → 𝕜} {r : ℝ} (hc : Summable fun n => ‖c n‖ * r ^ n)
    {x : 𝕜} (hx : ‖x‖ < r) :
    AnalyticAt 𝕜 (fun y : 𝕜 => ∑' n : ℕ, c n * (x + y) ^ n) 0 :=
  (hasFPowerSeriesOnBall_reexpand hc hx).analyticAt

/-! ## L2: nonnegative coefficients — radius transfer -/

-- no-dlmf: L2 — real Pringsheim step (nonnegative-coefficient radius transfer)
/-- **L2 (real Pringsheim step).**  Let `cₙ ≥ 0` and suppose `∑ cₙ rⁿ` converges,
`0 ≤ a < r`, `0 ≤ b`.  If the re-expansion of the series at `a` converges at
`b` — i.e. `∑ (∑' m, C(m+k,k) c_{m+k} aᵐ) bᵏ < ∞` — then the *original* series
already converges at `a + b`.

Equivalently: for nonnegative coefficients, re-expanding at an interior point
can never reach further than the original radius of convergence.  This is the
form of Pringsheim's theorem used to push a Taylor radius out to the nearest
genuine singularity, with no complex analysis. -/
theorem summable_of_reexpand_nonneg {c : ℕ → ℝ} {r a b : ℝ}
    (hnn : ∀ n, 0 ≤ c n) (hc : Summable fun n => c n * r ^ n)
    (ha : 0 ≤ a) (har : a < r) (hb : 0 ≤ b)
    (hd : Summable fun k : ℕ =>
      (∑' m : ℕ, ((m + k).choose k : ℝ) * c (m + k) * a ^ m) * b ^ k) :
    Summable fun n : ℕ => c n * (a + b) ^ n := by
  have hcn : ∀ n, ‖c n‖ = c n := fun n => Real.norm_of_nonneg (hnn n)
  have hc' : Summable fun n => ‖c n‖ * r ^ n := by
    refine hc.congr fun n => ?_
    rw [hcn n]
  set G : ℕ × ℕ → ℝ := fun p =>
    ((p.1 + p.2).choose p.2 : ℝ) * c (p.1 + p.2) * a ^ p.1 * b ^ p.2 with hG
  have hGnn : ∀ p : ℕ × ℕ, 0 ≤ G p := by
    intro p; rw [hG]; have := hnn (p.1 + p.2); positivity
  -- the double family is summable
  have h0 : ∀ k : ℕ, Summable fun m : ℕ => ((m + k).choose k : ℝ) * c (m + k) * a ^ m := by
    intro k
    refine (summable_reexpand_inner_norm hc' ha har k).congr fun m => ?_
    rw [hcn (m + k)]
  have hinner : ∀ k : ℕ, Summable fun m : ℕ => G (m, k) := fun k => (h0 k).mul_right (b ^ k)
  have houter : Summable fun k : ℕ => ∑' m : ℕ, G (m, k) := by
    refine hd.congr fun k => ?_
    exact ((h0 k).tsum_mul_right (b ^ k)).symm
  have hGsum : Summable G := by
    have : Summable fun p : ℕ × ℕ => G p.swap := by
      refine (summable_prod_of_nonneg (fun p => hGnn p.swap)).mpr ⟨fun k => ?_, ?_⟩
      · exact hinner k
      · exact houter
    exact this.prod_symm
  -- bound the partial sums of the original series by the total mass
  refine summable_of_sum_range_le (c := ∑' p : ℕ × ℕ, G p)
    (fun n => by have := hnn n; positivity) fun N => ?_
  have hfib : ∀ n : ℕ, ∑ p ∈ antidiagonal n, G p = c n * (a + b) ^ n := by
    intro n
    rw [← sum_antidiagonal_choose_snd a b n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [hG]
    simp only [hp]
    ring
  have hdisj : ((range N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun n => (antidiagonal n : Finset (ℕ × ℕ))) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_antidiagonal] at hp hp'
    exact absurd (hp.symm.trans hp') hij
  have hstep1 : ∑ n ∈ range N, c n * (a + b) ^ n
      = ∑ p ∈ (range N).biUnion (fun n => antidiagonal n), G p := by
    rw [Finset.sum_biUnion hdisj]
    exact (Finset.sum_congr rfl fun n _ => hfib n).symm
  have hsubset : (range N).biUnion (fun n => antidiagonal n) ⊆ range N ×ˢ range N := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    rw [Finset.mem_range] at hn
    rw [Finset.mem_antidiagonal] at hpn
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  calc ∑ n ∈ range N, c n * (a + b) ^ n
      = ∑ p ∈ (range N).biUnion (fun n => antidiagonal n), G p := hstep1
    _ ≤ ∑ p ∈ range N ×ˢ range N, G p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun p _ _ => hGnn p
    _ ≤ ∑' p : ℕ × ℕ, G p := hGsum.sum_le_tsum _ fun p _ => hGnn p

/-! ## L2': the radius of a nonnegative series reaches the first non-analytic point -/

-- no-dlmf: support lemma — the summability interval of a nonnegative-coefficient
-- power series is downward closed
/-- For nonnegative coefficients, convergence at `r` forces convergence at every
`0 ≤ s ≤ r`. -/
theorem summable_mul_pow_of_le {c : ℕ → ℝ} (hnn : ∀ n, 0 ≤ c n) {r s : ℝ}
    (hs : 0 ≤ s) (hsr : s ≤ r) (hc : Summable fun n => c n * r ^ n) :
    Summable fun n => c n * s ^ n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (hnn n) (pow_nonneg hs n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsr n) (hnn n)) hc

set_option maxHeartbeats 1000000 in
-- no-dlmf: L2' — real Pringsheim radius push (L1 + L2 assembled against a
-- real-analytic representative)
/-- **L2' (Pringsheim radius push).**  Let `cₙ ≥ 0`, let `f` be real-analytic at
every point of `[0, L)`, and suppose the series `∑ cₙ zⁿ` sums to `f z` on the
interior of its interval of convergence (`hrep`).  If the series converges at
*some* positive point `≤ L`, then it converges at *every* `0 ≤ s < L`.

In words: for nonnegative coefficients the radius of convergence cannot stop
before the first point at which the represented function fails to be analytic.
This is the real (order-theoretic) form of Pringsheim's theorem; the proof
combines the binomial re-expansion `L1` with the radius transfer `L2`, and uses
no complex analysis. -/
theorem summable_mul_pow_of_analyticAt {c : ℕ → ℝ} (hnn : ∀ n, 0 ≤ c n) {f : ℝ → ℝ} {L : ℝ}
    (hpos : ∃ s : ℝ, 0 < s ∧ s ≤ L ∧ Summable fun n => c n * s ^ n)
    (hana : ∀ x : ℝ, 0 ≤ x → x < L → AnalyticAt ℝ f x)
    (hrep : ∀ r z : ℝ, 0 ≤ r → r ≤ L → (Summable fun n => c n * r ^ n) → |z| < r →
      ∑' n : ℕ, c n * z ^ n = f z)
    {s : ℝ} (hs : 0 ≤ s) (hsL : s < L) :
    Summable fun n : ℕ => c n * s ^ n := by
  classical
  obtain ⟨s₀, hs₀pos, hs₀L, hs₀sum⟩ := hpos
  set T : Set ℝ := {r : ℝ | 0 ≤ r ∧ r ≤ L ∧ Summable fun n : ℕ => c n * r ^ n} with hTdef
  have hs₀T : s₀ ∈ T := ⟨hs₀pos.le, hs₀L, hs₀sum⟩
  have hTne : T.Nonempty := ⟨s₀, hs₀T⟩
  have hTbdd : BddAbove T := ⟨L, fun r hr => hr.2.1⟩
  set σ : ℝ := sSup T with hσdef
  have hσpos : 0 < σ := lt_of_lt_of_le hs₀pos (le_csSup hTbdd hs₀T)
  have hbelow : ∀ z : ℝ, 0 ≤ z → z < σ → Summable fun n : ℕ => c n * z ^ n := by
    intro z hz hzσ
    obtain ⟨r, hrT, hzr⟩ := exists_lt_of_lt_csSup hTne hzσ
    exact summable_mul_pow_of_le hnn hz hzr.le hrT.2.2
  have hsum_eq : ∀ z : ℝ, |z| < σ → ∑' n : ℕ, c n * z ^ n = f z := by
    intro z hz
    obtain ⟨r, hrT, hzr⟩ := exists_lt_of_lt_csSup hTne hz
    exact hrep r z hrT.1 hrT.2.1 hrT.2.2 hzr
  have hmain : L ≤ σ := by
    by_contra hcon
    rw [not_le] at hcon
    -- `f` is analytic at `σ`; shrink its ball to a *real* radius `η ≤ σ`
    obtain ⟨p, δ, hp⟩ := hana σ hσpos.le hcon
    obtain ⟨tδ, htδ0, htδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
    have htδ0' : (0 : ℝ) < (tδ : ℝ) := by exact_mod_cast htδ0
    set η : ℝ := min σ (tδ : ℝ) with hηdef
    have hη0 : 0 < η := lt_min hσpos htδ0'
    have hησ : η ≤ σ := min_le_left _ _
    have hηδ : ENNReal.ofReal η ≤ δ := by
      refine le_trans ?_ htδ.le
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    have hp' : HasFPowerSeriesOnBall f p σ (ENNReal.ofReal η) :=
      hp.mono (by simpa using hη0) hηδ
    set a : ℝ := σ - η / 4 with hadef
    set b : ℝ := η / 2 with hbdef
    have ha0 : 0 < a := by rw [hadef]; linarith
    have haσ : a < σ := by rw [hadef]; linarith
    have hb0 : 0 < b := by rw [hbdef]; linarith
    -- the power series of `f` at `a`, with radius at least `3η/4`
    have hnorm : ‖a - σ‖ = η / 4 := by
      rw [hadef, show σ - η / 4 - σ = -(η / 4) by ring, norm_neg,
        Real.norm_of_nonneg (by linarith)]
    have hnorme : ((‖a - σ‖₊ : NNReal) : ENNReal) = ENNReal.ofReal (η / 4) := by
      rw [ENNReal.ofReal, ← hnorm, Real.toNNReal_of_nonneg (norm_nonneg _)]
      rfl
    have hy : ((‖a - σ‖₊ : NNReal) : ENNReal) < ENNReal.ofReal η := by
      rw [hnorme]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    have hq0 := hp'.changeOrigin hy
    rw [show σ + (a - σ) = a by ring, hnorme, ← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ η / 4)]
      at hq0
    have hq : HasFPowerSeriesOnBall f (p.changeOrigin (a - σ)) a (ENNReal.ofReal (3 * η / 4)) := by
      refine hq0.mono (by simp; linarith) (ENNReal.ofReal_le_ofReal (by linarith))
    -- the re-expansion of the series at `a`, from L1
    obtain ⟨r, hrT, har⟩ := exists_lt_of_lt_csSup hTne haσ
    have hcr : Summable fun n : ℕ => ‖c n‖ * r ^ n := by
      refine hrT.2.2.congr fun n => ?_
      rw [Real.norm_of_nonneg (hnn n)]
    have hxa : ‖a‖ < r := by rw [Real.norm_of_nonneg ha0.le]; exact har
    have hL1 := hasFPowerSeriesOnBall_reexpand (𝕜 := ℝ) hcr hxa
    -- the two expansions at `0` agree, hence the formal series agree
    have hshift : HasFPowerSeriesAt (fun z : ℝ => f (z - -a))
        (p.changeOrigin (a - σ)) 0 := by
      have := (hq.comp_sub (-a)).hasFPowerSeriesAt
      rwa [show a + -a = (0:ℝ) by ring] at this
    have heq : ∀ᶠ z : ℝ in nhds 0,
        (∑' n : ℕ, c n * (a + z) ^ n) = f (z - -a) := by
      have hball : Metric.ball (0:ℝ) (σ - a) ∈ nhds (0:ℝ) :=
        Metric.ball_mem_nhds _ (by linarith)
      filter_upwards [hball] with z hz
      have hz' : |z| < σ - a := by simpa [Real.dist_eq] using hz
      have : |a + z| < σ := by
        rcases abs_lt.mp hz' with ⟨h1, h2⟩
        rw [abs_lt]; constructor <;> linarith
      rw [hsum_eq _ this, sub_neg_eq_add, add_comm z a]
    have hcoeff : FormalMultilinearSeries.ofScalars ℝ
        (fun k => ∑' m : ℕ, ((m + k).choose k : ℝ) * c (m + k) * a ^ m)
        = p.changeOrigin (a - σ) :=
      hL1.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hshift heq
    -- hence the re-expanded coefficients are summable against `bᵏ`
    have hbrad : (ENNReal.ofReal b) < (FormalMultilinearSeries.ofScalars ℝ
        (fun k => ∑' m : ℕ, ((m + k).choose k : ℝ) * c (m + k) * a ^ m)).radius := by
      rw [hcoeff]
      refine lt_of_lt_of_le ?_ hq.r_le
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by rw [hbdef]; linarith)
    have hbnn : (0:ℝ) ≤ b := hb0.le
    have hd : Summable fun k : ℕ =>
        (∑' m : ℕ, ((m + k).choose k : ℝ) * c (m + k) * a ^ m) * b ^ k := by
      have hbb : ((b.toNNReal : NNReal) : ENNReal) < (FormalMultilinearSeries.ofScalars ℝ
          (fun k => ∑' m : ℕ, ((m + k).choose k : ℝ) * c (m + k) * a ^ m)).radius := hbrad
      have hsm := FormalMultilinearSeries.summable_norm_mul_pow _ hbb
      refine hsm.congr fun k => ?_
      rw [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hbnn,
        Real.norm_of_nonneg]
      exact tsum_nonneg fun m => by
        have := hnn (m + k); positivity
    -- L2 now pushes the convergence of the original series past `σ`
    have hfinal : Summable fun n : ℕ => c n * (a + b) ^ n :=
      summable_of_reexpand_nonneg hnn hrT.2.2 ha0.le har hbnn hd
    -- contradiction with `σ = sSup T`
    have hab : σ < a + b := by rw [hadef, hbdef]; linarith
    set s₁ : ℝ := min (a + b) L with hs₁def
    have hs₁σ : σ < s₁ := lt_min hab hcon
    have hs₁0 : 0 ≤ s₁ := (hσpos.trans hs₁σ).le
    have hs₁T : s₁ ∈ T :=
      ⟨hs₁0, min_le_right _ _,
        summable_mul_pow_of_le hnn hs₁0 (min_le_left _ _) hfinal⟩
    exact absurd (le_csSup hTbdd hs₁T) (not_le.mpr hs₁σ)
  exact hbelow s hs (lt_of_lt_of_le hsL hmain)

end FLMF.Methods
