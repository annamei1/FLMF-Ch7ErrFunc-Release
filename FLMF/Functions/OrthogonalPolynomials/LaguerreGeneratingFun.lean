/-
Copyright (c) 2026 aletheai-research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FLMF.Functions.OrthogonalPolynomials.LaguerreGenerating
import FLMF.Methods.GeneratingFunction
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Laguerre generating function (analytic form), DLMF 18.12.13

This file proves the analytic generating-function identity for the generalized
Laguerre polynomials `L_n^α`:

```
∑_{n=0}^∞ L_n^α(x) tⁿ = (1 - t)^{-α-1} · exp(-x t / (1 - t)),          (|t| < 1).
```

The route:

* `Real.hasSum_ascPochhammer_div_factorial_mul_pow` — the generalized negative
  binomial series `(1-t)^{-β} = ∑ₙ (β)ₙ/n! · tⁿ` for real `β` and `|t| < 1`,
  obtained from Mathlib's `binomialSeries` together with the reflection lemma
  `Ring.choose_neg_eq` below.
* `Ring.choose_neg_eq` — `Ring.choose (-β) n = (-1)ⁿ (β)ₙ / n!`.
* The main theorem `laguerre_generating_function`, assembled by expanding each
  Laguerre polynomial via `Polynomial.coeff_laguerre`, reindexing the resulting
  double sum over the antidiagonal `(k, m) ↦ n = k + m` (Fubini, using absolute
  summability; the regrouping step is the method-kit lemma
  `FLMF.Methods.hasSum_antidiagonal`), summing over `m` with the
  negative-binomial series, and finally collapsing the `k`-sum into the
  exponential.
-/

open scoped BigOperators Nat
open Finset

namespace Ring

/-- Reflection of `Ring.choose` at negative argument:
`Ring.choose (-β) n = (-1)ⁿ · (β)ₙ / n!`, where `(β)ₙ = (ascPochhammer ℝ n).eval β`
is the rising factorial. -/
theorem choose_neg_eq (β : ℝ) (n : ℕ) :
    Ring.choose (-β) n = (-1) ^ n * (ascPochhammer ℝ n).eval β / (n.factorial : ℝ) := by
  -- `choose (-β) n = negOnePow n • choose (β + n - 1) n`
  rw [Ring.choose_neg]
  -- pin down `choose (β + n - 1) n` via the descending Pochhammer / factorial relation
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have key : (n.factorial : ℝ) * Ring.choose (β + n - 1) n = (ascPochhammer ℝ n).eval β := by
    have h1 := Ring.descPochhammer_eq_factorial_smul_choose (β + (n : ℝ) - 1) n
    rw [nsmul_eq_mul] at h1
    -- `(descPochhammer ℤ n).smeval (β+n-1) = (ascPochhammer ℕ n).smeval ((β+n-1)-n+1)`
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer] at h1
    have hsub : (β + (n : ℝ) - 1) - (n : ℝ) + 1 = β := by ring
    rw [hsub, Polynomial.ascPochhammer_smeval_eq_eval] at h1
    rw [← h1]
  -- finish: peel off the sign and divide
  have hchoose : Ring.choose (β + (n : ℝ) - 1) n
      = (ascPochhammer ℝ n).eval β / (n.factorial : ℝ) := by
    field_simp
    rw [← key]; ring
  rw [Units.smul_def, hchoose]
  have hsign : ((Int.negOnePow (n : ℤ) : ℤ) : ℝ) = (-1) ^ n := by
    simp [Int.cast_negOnePow ℝ (n : ℤ)]
  rw [zsmul_eq_mul, hsign]
  ring

end Ring

namespace Real

/-- **Generalized negative binomial series.** For real `β` and `|t| < 1`,
`(1 - t)^{-β} = ∑ₙ (β)ₙ / n! · tⁿ`, where `(β)ₙ = (ascPochhammer ℝ n).eval β`. -/
theorem hasSum_ascPochhammer_div_factorial_mul_pow (β : ℝ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ ↦ (ascPochhammer ℝ n).eval β / (n.factorial : ℝ) * t ^ n)
      ((1 - t) ^ (-β)) := by
  -- the binomial power series for `(1 + y)^a` with `a = -β`, evaluated at `y = -t`
  have hball : (-t) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.eball, Set.mem_setOf_eq, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm,
      ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
    simpa [abs_neg] using ht
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -β)).hasSum hball
  -- simplify the value: `(1 + -t)^(-β) = (1 - t)^(-β)` (base `1 - t > 0`)
  have hval : (fun n : ℕ ↦ binomialSeries ℝ (-β) n fun _ : Fin n ↦ (-t : ℝ))
      = fun n : ℕ ↦ (ascPochhammer ℝ n).eval β / (n.factorial : ℝ) * t ^ n := by
    funext n
    rw [binomialSeries_apply]
    -- `(List.ofFn (fun _ => -t)).prod = (-t)^n`
    simp only [List.ofFn_const, List.prod_replicate, smul_eq_mul]
    rw [Ring.choose_neg_eq, neg_pow]
    field_simp
    ring_nf
    rw [show n * 2 = 2 * n by ring, pow_mul]
    norm_num
  rw [hval] at h
  have hbase : (1 : ℝ) + (0 + -t) = 1 - t := by ring
  rw [hbase] at h
  exact h

end Real

namespace Polynomial

open Real

/-- Crude bound on the rising factorial: `|(β)ₘ| ≤ (B)ₘ` whenever `0 < B` and `|β| ≤ B`. -/
private theorem abs_eval_ascPochhammer_le {β B : ℝ} (hB : 0 < B) (hβ : |β| ≤ B) (m : ℕ) :
    |(ascPochhammer ℝ m).eval β| ≤ (ascPochhammer ℝ m).eval B := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, abs_mul]
    have hpos : 0 < (ascPochhammer ℝ m).eval B := ascPochhammer_pos m B hB
    have hfac : |β + (m : ℝ)| ≤ B + (m : ℝ) := by
      calc |β + (m : ℝ)| ≤ |β| + |(m : ℝ)| := abs_add_le _ _
        _ = |β| + (m : ℝ) := by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ))]
        _ ≤ B + (m : ℝ) := by linarith
    exact mul_le_mul ih hfac (abs_nonneg _) (le_of_lt hpos)

/-- The summand of the double sum obtained by expanding `L_n^α(x)` via
`coeff_laguerre` and reindexing `(n, k) ↦ (k, m := n - k)` with `n = k + m`. -/
private noncomputable def lagDouble (α x t : ℝ) (km : ℕ × ℕ) : ℝ :=
  (-1) ^ km.1 * (ascPochhammer ℝ km.2).eval (α + (km.1 : ℝ) + 1)
      / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ)) * x ^ km.1 * t ^ (km.1 + km.2)

/-- A nonnegative dominating family for `lagDouble`, obtained by replacing `α, x, t` with
`|α|, |x|, |t|`. Used to establish absolute summability of the double sum. -/
private noncomputable def lagBound (α x t : ℝ) (km : ℕ × ℕ) : ℝ :=
  |x| ^ km.1 / (km.1.factorial : ℝ)
    * ((ascPochhammer ℝ km.2).eval (|α| + (km.1 : ℝ) + 1) / (km.2.factorial : ℝ))
    * |t| ^ (km.1 + km.2)

private theorem lagBound_nonneg (α x t : ℝ) (km : ℕ × ℕ) : 0 ≤ lagBound α x t km := by
  simp only [lagBound]
  have h1 : 0 < (ascPochhammer ℝ km.2).eval (|α| + (km.1 : ℝ) + 1) :=
    ascPochhammer_pos km.2 _ (by positivity)
  positivity

private theorem abs_lagDouble_le (α x t : ℝ) (km : ℕ × ℕ) :
    |lagDouble α x t km| ≤ lagBound α x t km := by
  -- write `|lagDouble|` as `(|ascPoch(α+k+1)| / (k! m!)) · |x|^k · |t|^(k+m)`
  have hrw : |lagDouble α x t km|
      = |(ascPochhammer ℝ km.2).eval (α + (km.1 : ℝ) + 1)|
          / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ)) * |x| ^ km.1 * |t| ^ (km.1 + km.2) := by
    simp only [lagDouble]
    rw [abs_mul, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_pow]
    have hpow : |(-1 : ℝ)| ^ km.1 = 1 := by simp
    rw [hpow, one_mul]
    have hfac : |(km.1.factorial : ℝ) * (km.2.factorial : ℝ)|
        = (km.1.factorial : ℝ) * (km.2.factorial : ℝ) := abs_of_nonneg (by positivity)
    rw [hfac]
  rw [hrw]
  simp only [lagBound]
  -- bound `|(ascPochhammer).eval (α+k+1)| ≤ (ascPochhammer).eval (|α|+k+1)`
  have hbound := abs_eval_ascPochhammer_le (β := α + (km.1 : ℝ) + 1)
    (B := |α| + (km.1 : ℝ) + 1) (by positivity)
    (by
      rw [abs_le]
      constructor <;> [nlinarith [neg_abs_le α]; nlinarith [le_abs_self α]]) km.2
  have hxnn : (0 : ℝ) ≤ |x| ^ km.1 := by positivity
  have htnn : (0 : ℝ) ≤ |t| ^ (km.1 + km.2) := by positivity
  have hfacnn : (0 : ℝ) < (km.1.factorial : ℝ) * (km.2.factorial : ℝ) := by positivity
  have hstep : |(ascPochhammer ℝ km.2).eval (α + (km.1 : ℝ) + 1)|
      / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ))
      ≤ (ascPochhammer ℝ km.2).eval (|α| + (km.1 : ℝ) + 1)
          / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ)) :=
    div_le_div_of_nonneg_right hbound hfacnn.le
  calc |(ascPochhammer ℝ km.2).eval (α + (km.1 : ℝ) + 1)|
          / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ)) * |x| ^ km.1 * |t| ^ (km.1 + km.2)
      ≤ (ascPochhammer ℝ km.2).eval (|α| + (km.1 : ℝ) + 1)
          / ((km.1.factorial : ℝ) * (km.2.factorial : ℝ)) * |x| ^ km.1 * |t| ^ (km.1 + km.2) := by
        apply mul_le_mul_of_nonneg_right _ htnn
        exact mul_le_mul_of_nonneg_right hstep hxnn
    _ = |x| ^ km.1 / (km.1.factorial : ℝ)
          * ((ascPochhammer ℝ km.2).eval (|α| + (km.1 : ℝ) + 1) / (km.2.factorial : ℝ))
          * |t| ^ (km.1 + km.2) := by ring

/-- For fixed `k`, summing the double-sum summand over `m` gives a closed form via the
negative binomial series (Step 2). -/
private theorem hasSum_lagDouble_fiber (α x : ℝ) {t : ℝ} (ht : |t| < 1) (k : ℕ) :
    HasSum (fun m : ℕ ↦ lagDouble α x t (k, m))
      (((-x) ^ k / (k.factorial : ℝ) * t ^ k) * (1 - t) ^ (-(α + (k : ℝ) + 1))) := by
  -- the inner series is the constant `(-x)^k/k! · t^k` times the negative-binomial sum
  have hbin := Real.hasSum_ascPochhammer_div_factorial_mul_pow (α + (k : ℝ) + 1) ht
  have hc := hbin.mul_left ((-x) ^ k / (k.factorial : ℝ) * t ^ k)
  refine hc.congr_fun ?_
  intro m
  simp only [lagDouble]
  rw [pow_add]
  ring

/-- **Step 4 (k-sum collapse).** For `|s| < 1`, the `k`-sum
`∑ₖ yᵏ/k! · sᵏ · (1-s)^{-(γ+1+k)}` collapses to `(1-s)^{-(γ+1)} · exp(y·s/(1-s))`. -/
private theorem hasSum_kSum_collapse (γ y : ℝ) {s : ℝ} (hs : |s| < 1) :
    HasSum (fun k : ℕ ↦ y ^ k / (k.factorial : ℝ) * s ^ k * (1 - s) ^ (-(γ + 1 + (k : ℝ))))
      ((1 - s) ^ (-(γ + 1)) * Real.exp (y * s / (1 - s))) := by
  have hpos : (0 : ℝ) < 1 - s := by
    rcases abs_lt.mp hs with ⟨_, h2⟩; linarith
  set w : ℝ := y * s / (1 - s) with hw
  -- the exponential series `∑ wᵏ/k! = exp w`
  have hexp : HasSum (fun k : ℕ ↦ w ^ k / (k.factorial : ℝ)) (Real.exp w) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp w
  -- multiply by the constant `(1 - s) ^ (-(γ + 1))`
  have h := hexp.mul_left ((1 - s) ^ (-(γ + 1)))
  refine h.congr_fun ?_
  intro k
  -- `(1-s)^(-(γ+1+k)) = (1-s)^(-(γ+1)) · (1-s)^(-k)`
  have hrpow : (1 - s) ^ (-(γ + 1 + (k : ℝ)))
      = (1 - s) ^ (-(γ + 1)) * (1 - s) ^ (-(k : ℝ)) := by
    rw [← Real.rpow_add hpos]; ring_nf
  -- `wᵏ = (y·s)ᵏ · (1-s)^(-k)`
  have hwk : w ^ k = y ^ k * s ^ k * (1 - s) ^ (-(k : ℝ)) := by
    rw [hw, div_pow, mul_pow, Real.rpow_neg (le_of_lt hpos), Real.rpow_natCast]
    field_simp
  rw [hrpow, hwk]
  ring

/-- Fiber HasSum for the dominating family (Step 2 with positive parameters). -/
private theorem hasSum_lagBound_fiber (α x : ℝ) {t : ℝ} (ht : |t| < 1) (k : ℕ) :
    HasSum (fun m : ℕ ↦ lagBound α x t (k, m))
      ((|x| ^ k / (k.factorial : ℝ) * |t| ^ k) * (1 - |t|) ^ (-(|α| + (k : ℝ) + 1))) := by
  have ht' : |(|t|)| < 1 := by rwa [abs_abs]
  have hbin := Real.hasSum_ascPochhammer_div_factorial_mul_pow (|α| + (k : ℝ) + 1) ht'
  have hc := hbin.mul_left (|x| ^ k / (k.factorial : ℝ) * |t| ^ k)
  refine hc.congr_fun ?_
  intro m
  simp only [lagBound]
  rw [pow_add]
  ring

/-- Absolute summability of the double-sum family for `|t| < 1`. -/
private theorem summable_lagDouble (α x : ℝ) {t : ℝ} (ht : |t| < 1) :
    Summable (lagDouble α x t) := by
  -- it suffices to show `Summable lagBound` and compare
  have hsummB : Summable (lagBound α x t) := by
    rw [summable_prod_of_nonneg (lagBound_nonneg α x t)]
    refine ⟨fun k ↦ (hasSum_lagBound_fiber α x ht k).summable, ?_⟩
    -- the fiber sums are `|x|^k/k! · |t|^k · (1-|t|)^(-(|α|+k+1))`, summable by Step 4
    have hkSum := hasSum_kSum_collapse (|α|) (|x|) (s := |t|) (by rwa [abs_abs])
    refine (hkSum.summable).congr ?_
    intro k
    rw [(hasSum_lagBound_fiber α x ht k).tsum_eq]
    have hexp : (-(|α| + 1 + (k : ℝ))) = (-(|α| + (k : ℝ) + 1)) := by ring
    rw [hexp]
  refine hsummB.of_norm_bounded (fun km ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_lagDouble_le α x t km

/-- Antidiagonal collapse: summing the double-sum summand over the antidiagonal `k + m = n`
recovers `L_n^α(x) · tⁿ`. -/
private theorem sum_antidiagonal_lagDouble (α x t : ℝ) (n : ℕ) :
    ∑ km ∈ Finset.antidiagonal n, lagDouble α x t km
      = (laguerre α n).eval x * t ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- expand the Laguerre evaluation as a sum over `range (n+1)`
  rw [laguerre, eval_finsetSum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [lagDouble, eval_mul, eval_C, eval_pow, eval_X]
  -- `k + (n - k) = n` since `k ≤ n`
  have hkn : k + (n - k) = n := by omega
  rw [hkn]

-- no-dlmf: real/narrowed restriction of DLMF 18.12.13 (real `t`, DLMF's `z` is complex);
-- faithful surface is laguerre_generating_function_complex
/-- **Laguerre generating function**, real instance.  For real `α`, `x` and `|t| < 1`,
```
∑ₙ L_n^α(x) tⁿ = (1 - t)^{-α-1} · exp(-x t / (1 - t)).
```
The right-hand power `(1 - t)^{-α-1}` is the real `rpow` (well-defined since `1 - t > 0`).
Real, open-disk instance of the generating function (DLMF 18.12.13 is stated for
complex `z`, `|z| < 1`).
-/
theorem laguerre_generating_function (α x : ℝ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ ↦ (laguerre α n).eval x * t ^ n)
      ((1 - t) ^ (-α - 1) * Real.exp (-x * t / (1 - t))) := by
  -- absolute summability of the double family
  have hsum := summable_lagDouble α x ht
  -- group the double sum over the first coordinate `k` (Fubini)
  have hK : HasSum (fun k : ℕ ↦
      ((-x) ^ k / (k.factorial : ℝ) * t ^ k) * (1 - t) ^ (-(α + (k : ℝ) + 1)))
      (∑' km : ℕ × ℕ, lagDouble α x t km) :=
    hsum.hasSum.prod_fiberwise (fun k ↦ hasSum_lagDouble_fiber α x ht k)
  -- the `k`-sum collapses to the exponential (Step 4)
  have hKval := hasSum_kSum_collapse α (-x) (s := t) ht
  have hValue : (∑' km : ℕ × ℕ, lagDouble α x t km)
      = (1 - t) ^ (-α - 1) * Real.exp (-x * t / (1 - t)) := by
    have heq : (fun k : ℕ ↦ (-x) ^ k / (k.factorial : ℝ) * t ^ k
          * (1 - t) ^ (-(α + 1 + (k : ℝ))))
        = fun k : ℕ ↦ ((-x) ^ k / (k.factorial : ℝ) * t ^ k) * (1 - t) ^ (-(α + (k : ℝ) + 1)) := by
      funext k
      have h1 : (-(α + 1 + (k : ℝ))) = (-(α + (k : ℝ) + 1)) := by ring
      rw [h1, mul_assoc]
    rw [heq] at hKval
    have huniq := hK.unique hKval
    rw [huniq, show (-α - 1) = (-(α + 1)) by ring, show (-x * t) = ((-x) * t) by ring]
  -- regroup the double sum along antidiagonals `n = k + m` to recover the `n`-series
  -- (method kit: `FLMF.Methods.hasSum_antidiagonal`)
  have hN : HasSum (fun n : ℕ ↦ ∑ km ∈ Finset.antidiagonal n, lagDouble α x t km)
      (∑' km : ℕ × ℕ, lagDouble α x t km) :=
    FLMF.Methods.hasSum_antidiagonal hsum.hasSum
  -- rewrite the antidiagonal sums as `L_n(x) tⁿ` and the value as the target RHS
  rw [hValue] at hN
  refine hN.congr_fun (fun n ↦ ?_)
  exact (sum_antidiagonal_lagDouble α x t n).symm

/-- **DLMF 18.12.13** — the Laguerre generating function, for real `α`, real `x`,
and complex `z` with `|z| < 1`,
```
∑ₙ L_n^α(x) zⁿ = (1 - z)^{-α-1} · exp(x z / (z - 1)).
```
The right-hand power `(1 - z)^{-α-1}` is the complex `cpow`, well-defined since
`|z| < 1` puts `1 - z` in the open right half-plane (away from `cpow`'s branch cut).

DAG: E-18.12.13.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem laguerre_generating_function_complex (α x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (((laguerre α n).eval x : ℝ) : ℂ) * z ^ n)
      ((1 - z) ^ (-(α : ℂ) - 1) * Complex.exp (x * z / (z - 1))) := by
  sorry
