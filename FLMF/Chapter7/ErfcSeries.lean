import FLMF.Chapter7.ErfcLeading
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Full asymptotic series for the complementary error function `erfc`

Continuing from `FLMF.Functions.Error.ErfcLeading`, we use the Watson-ready
representation
`erfc(x) = (2/√π) · e^{-x²} ∫_{(0,∞)} e^{-(2x) u} · e^{-u²} du`
and the full `N`-term Watson series lemma `PicardLefschetz.watson_series`
(with `s = 1` and amplitude `g(u) = e^{-u²}`) to obtain the asymptotic
expansion of `erfc` (DLMF §7.12.1).

The amplitude has the convergent Taylor expansion
`e^{-u²} = Σ_{k} ((-1)^k / k!) u^{2k}`, but for `watson_series` we only need a
finite split with a *bounded* remainder `h`:
`g u = Σ_{k<N} a k · u^k + u^N · h u`.

We package the general engine `erfc_watson_series`, which produces the full
asymptotic series of `erfc` (DLMF §7.12.1) on the real axis.

DLMF's own statement is on the complex sector `|ph z| ≤ 3π/4 − δ`, which no analytic
continuation reaches from the real theorem (a `Tendsto` along a sector-at-infinity
filter is not an analytic identity).  That surface, `erfc_7_12_1_complex_series`, is
proved here from the uniform rotated-ray estimate `cerfc_poincare_bound` of
`ErfcLeading.lean`, applied at truncation order `N + 1`.
-/

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set PicardLefschetz

-- no-dlmf: reusable Watson N-term remainder engine, not itself a numbered-equation surface; the faithful §7.12.1 surface is `erfc_7_12_1` below (which consumes this engine).
/-- **Watson `N`-term remainder engine** — the general machine behind the §7.12.1
asymptotic expansion (reusable infrastructure, *not* itself the DLMF surface; the
faithful surface is `erfc_7_12_1` below).

Suppose the Watson amplitude `g(u) = e^{-u²}` splits on `(0,∞)` as
`g u = Σ_{k<N} a k · u^k + u^N · h u` with `h` measurable, bounded by `C`,
tending to `aN` at `0⁺`.  Then for the Laplace parameter `p = 2x`,
`p^N · (p · ∫_{(0,∞)} e^{-p u} e^{-u²} du - Σ_{k<N} a k Γ(1+k) p^{-k})
   → aN · Γ(1+N)` as `x → ∞`. -/
theorem erfc_watson_series {a : ℕ → ℝ} {h : ℝ → ℝ} {N : ℕ} {aN C : ℝ}
    (hsplit : ∀ u ∈ Ioi (0:ℝ),
      Real.exp (-u ^ 2) = (∑ k ∈ Finset.range N, a k * u ^ k) + u ^ N * h u)
    (hhm : Measurable h)
    (hhC : ∀ u ∈ Ioi (0:ℝ), |h u| ≤ C)
    (hhlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 aN)) :
    Tendsto (fun x : ℝ => (2 * x) ^ (N : ℝ) *
        ((2 * x) * (∫ u in Ioi (0:ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2))
          - ∑ k ∈ Finset.range N, a k * Real.Gamma (1 + k) * (2 * x) ^ (-(k : ℝ))))
      atTop (𝓝 (aN * Real.Gamma (1 + N))) := by
  -- Apply `watson_series` at `s = 1` to `g(u) = e^{-u²}`, then precompose with `x ↦ 2x`.
  have hw := watson_series (s := 1) (one_pos) (g := fun u => Real.exp (-u ^ 2))
    (h := h) (a := a) (N := N) (aN := aN) (C := C)
    (by
      intro u hu
      have := hsplit u hu
      simpa using this)
    hhm hhC hhlim
  -- Rewrite `t ^ (1 - 1) = 1` inside the integral and `p ^ (1:ℝ) = p`.
  have hw' :
      Tendsto (fun p : ℝ => p ^ (N : ℝ) *
          (p * (∫ u in Ioi (0:ℝ), Real.exp (-p * u) * Real.exp (-u ^ 2))
            - ∑ k ∈ Finset.range N, a k * Real.Gamma (1 + k) * p ^ (-(k : ℝ))))
        atTop (𝓝 (aN * Real.Gamma (1 + N))) := by
    refine hw.congr' ?_
    filter_upwards with p
    have hint :
        (∫ t in Ioi (0:ℝ), Real.exp (-p * t) * (t ^ ((1:ℝ) - 1) * Real.exp (-t ^ 2)))
          = ∫ u in Ioi (0:ℝ), Real.exp (-p * u) * Real.exp (-u ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro u hu
      simp only [show (1:ℝ) - 1 = 0 from by norm_num, Real.rpow_zero, one_mul]
    rw [Real.rpow_one, hint]
  -- Compose with `x ↦ 2x → ∞`.
  have hcomp : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop' (by norm_num : (0:ℝ) < 2)
  exact hw'.comp hcomp

-- no-dlmf: Taylor coefficients of the Watson amplitude e^{-u²} (a_{2j} = (-1)^j/j!,
-- odd coefficients zero); proof infrastructure for 7.12.1, no DLMF identity number
/-- Taylor coefficients of the Watson amplitude `e^{-u²}`: `a_{2j} = (-1)^j/j!`,
odd coefficients zero. -/
private noncomputable def erfcCoeff (k : ℕ) : ℝ :=
  if Even k then (-1 : ℝ) ^ (k / 2) / (Nat.factorial (k / 2) : ℝ) else 0

-- no-dlmf: even-index value of erfcCoeff; proof infrastructure, no DLMF identity number
private theorem erfcCoeff_even (n : ℕ) :
    erfcCoeff (2 * n) = (-1 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  have h : Even (2 * n) := ⟨n, (two_mul n)⟩
  simp [erfcCoeff, h, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]

-- no-dlmf: odd-index vanishing of erfcCoeff; proof infrastructure, no DLMF identity number
private theorem erfcCoeff_odd (n : ℕ) : erfcCoeff (2 * n + 1) = 0 := by
  have h : ¬ Even (2 * n + 1) := by simp
  simp [erfcCoeff, h]

-- no-dlmf: even-index reindexing of erfcCoeff sums; proof infrastructure, no DLMF
-- identity number
private theorem sum_erfcCoeff (N : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 * N), erfcCoeff k * F k
      = ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j / (Nat.factorial j : ℝ) * F (2 * j) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [erfcCoeff_even, erfcCoeff_odd]
    ring

-- no-dlmf: closed form (½)_N = (2N)!/(4^N·N!) of the half-integer rising factorial;
-- reusable arithmetic identity, not itself a numbered DLMF equation
/-- `(½)_N = (2N)!/(4^N · N!)`. -/
private theorem ascPochhammer_half_eval (N : ℕ) :
    (ascPochhammer ℝ N).eval (1/2 : ℝ)
      = (Nat.factorial (2 * N) : ℝ) / (4 ^ N * (Nat.factorial N : ℝ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hfn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast, ih]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

-- no-dlmf: closed form (½)_N = (2N)!/(4^N·N!) of the half-integer rising factorial,
-- complex coefficients (the ℂ-analogue of `ascPochhammer_half_eval` above); reusable
-- arithmetic identity, not itself a numbered DLMF equation
/-- `(½)_N = (2N)!/(4^N · N!)`, over `ℂ`. -/
private theorem ascPochhammer_half_eval_complex (N : ℕ) :
    (ascPochhammer ℂ N).eval (1/2 : ℂ)
      = (Nat.factorial (2 * N) : ℂ) / (4 ^ N * (Nat.factorial N : ℂ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hfn : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast, ih]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

-- no-dlmf: quadratic control of the order-2N Watson remainder of e^{-u²} near 0⁺
-- (Taylor-remainder estimate via Real.exp_bound); proof infrastructure, no DLMF
-- identity number
/-- On `(0, 1]` the order-`2N` Watson remainder of `e^{-u²}` differs from its limit
`(-1)^N/N!` by at most `O(u²)`, with the explicit constant from `Real.exp_bound`. -/
private theorem erfcRem_sub_bound (N : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    |(Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k) / u ^ (2 * N)
        - (-1 : ℝ) ^ N / (Nat.factorial N : ℝ)|
      ≤ ((N : ℝ) + 2) / ((Nat.factorial (N + 1) : ℝ) * ((N : ℝ) + 1)) * u ^ 2 := by
  have hP : ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k
      = ∑ j ∈ Finset.range N, (-u ^ 2) ^ j / (Nat.factorial j : ℝ) := by
    rw [sum_erfcCoeff N (fun k => u ^ k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul, neg_pow]
    ring
  have hup : (0:ℝ) < u ^ (2 * N) := by positivity
  have hfN : (Nat.factorial N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have key : (Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k) / u ^ (2 * N)
      - (-1 : ℝ) ^ N / (Nat.factorial N : ℝ)
      = (Real.exp (-u ^ 2) - ∑ j ∈ Finset.range (N + 1), (-u ^ 2) ^ j / (Nat.factorial j : ℝ))
          / u ^ (2 * N) := by
    rw [hP, Finset.sum_range_succ]
    have h1 : ((-u ^ 2) ^ N : ℝ) = (-1) ^ N * u ^ (2 * N) := by
      rw [neg_pow, pow_mul]
    rw [h1]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hup, div_le_iff₀ hup]
  have hx1 : |(-u ^ 2 : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_pos (show (0:ℝ) < u^2 by positivity)]
    nlinarith
  have hb := Real.exp_bound hx1 (Nat.succ_pos N)
  calc |Real.exp (-u ^ 2) - ∑ j ∈ Finset.range (N + 1), (-u ^ 2) ^ j / (Nat.factorial j : ℝ)|
      ≤ |(-u ^ 2 : ℝ)| ^ (N + 1)
          * (((N + 1).succ : ℝ) / ((Nat.factorial (N + 1) : ℝ) * ((N + 1 : ℕ) : ℝ))) := hb
    _ = ((N : ℝ) + 2) / ((Nat.factorial (N + 1) : ℝ) * ((N : ℝ) + 1)) * u ^ 2 * u ^ (2 * N) := by
        rw [abs_neg, abs_of_pos (show (0:ℝ) < u^2 by positivity), ← pow_mul]
        push_cast
        rw [show 2 * (N + 1) = 2 + 2 * N by ring, pow_add]
        ring

-- no-dlmf: real/narrowed restriction of DLMF 7.12.1 (whose stated domain is complex
-- `z → ∞` in the sector `|ph z| ≤ 3π/4 − δ`); the faithful full-strength surface is
-- `erfc_7_12_1_complex_series` below (the leading-order `N = 0` case is already
-- surfaced, with proof, as `erfc_7_12_1_complex` in `ErfcLeading.lean`).
/-- **The complete (Poincaré) asymptotic expansion of `erfc`, real axis.**
`erfc(x) ∼ (e^{-x²}/√π) · Σ_{m≥0} (-1)^m (½)_m / x^{2m+1}` as `x → +∞`, where
`(½)_m = (ascPochhammer ℝ m).eval (1/2)` is the rising factorial.

Stated in remainder form, valid for *every* truncation order `N` (which pins every
coefficient): the `N`-term remainder of `√π · e^{x²} · erfc(x)`, scaled by `x^{2N+1}`,
converges to the next coefficient `(-1)^N (½)_N`.  (For `N = 0` this is the leading-term
statement `erfc_asymptotic`.)

The proof routes through the Watson remainder engine `erfc_watson_series` applied to the
Taylor split of the amplitude `e^{-u²}` (whose even coefficients `(-1)^j / j!` give
`a_{2j} Γ(1+2j) (2x)^{-2j} = (-1)^j (½)_j x^{-2j}`); deferred as a semantic surface.

DLMF 7.12.1 itself is stated for complex `z` in the sector `|ph z| ≤ 3π/4 − δ`; see
`erfc_7_12_1_complex_series`.
-/
theorem erfc_7_12_1 (N : ℕ) :
    Tendsto (fun x : ℝ => x ^ (2 * N + 1) *
        (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x
          - ∑ m ∈ Finset.range N,
              (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m + 1)))
      atTop (𝓝 ((-1 : ℝ) ^ N * (ascPochhammer ℝ N).eval (1 / 2 : ℝ))) := by
  classical
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hfN : (Nat.factorial N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  set c : ℝ := ((N : ℝ) + 2) / ((Nat.factorial (N + 1) : ℝ) * ((N : ℝ) + 1)) with hcdef
  set aN : ℝ := (-1 : ℝ) ^ N / (Nat.factorial N : ℝ) with haNdef
  set S : ℝ := ∑ k ∈ Finset.range (2 * N), |erfcCoeff k| with hSdef
  set C : ℝ := c + 1 / (Nat.factorial N : ℝ) + 1 + S with hCdef
  set h : ℝ → ℝ := fun u =>
    (Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k) / u ^ (2 * N)
    with hhdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => abs_nonneg _
  have haN' : |aN| ≤ 1 / (Nat.factorial N : ℝ) := by
    rw [haNdef, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  -- the engine hypotheses: exact split, measurability, boundedness, boundary limit
  have hsplit : ∀ u ∈ Ioi (0:ℝ), Real.exp (-u ^ 2)
      = (∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k) + u ^ (2 * N) * h u := by
    intro u hu
    have hne : u ^ (2 * N) ≠ 0 := pow_ne_zero _ (ne_of_gt hu)
    rw [hhdef]
    field_simp
    ring
  have hhm : Measurable h := by rw [hhdef]; fun_prop
  have hhC : ∀ u ∈ Ioi (0:ℝ), |h u| ≤ C := by
    intro u hu
    have hu0 : (0:ℝ) < u := hu
    rcases le_or_gt u 1 with hu1 | hu1
    · -- near 0: the quadratic remainder estimate
      have hb : |h u - aN| ≤ c * u ^ 2 := erfcRem_sub_bound N hu0 hu1
      have htri : |h u| ≤ |h u - aN| + |aN| := by
        calc |h u| = |(h u - aN) + aN| := by ring_nf
          _ ≤ |h u - aN| + |aN| := abs_add_le _ _
      have hu2 : u ^ 2 ≤ 1 := by nlinarith
      calc |h u| ≤ |h u - aN| + |aN| := htri
        _ ≤ c * u ^ 2 + 1 / (Nat.factorial N : ℝ) := add_le_add hb haN'
        _ ≤ C := by rw [hCdef]; nlinarith
    · -- away from 0: crude polynomial/exponential domination
      have hu1' : (1:ℝ) ≤ u := le_of_lt hu1
      have hup : (0:ℝ) < u ^ (2 * N) := by positivity
      have hup1 : (1:ℝ) ≤ u ^ (2 * N) := one_le_pow₀ hu1'
      have hexp1 : |Real.exp (-u ^ 2)| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _), show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hpoly : |∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k| ≤ S * u ^ (2 * N) := by
        calc |∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k|
            ≤ ∑ k ∈ Finset.range (2 * N), |erfcCoeff k * u ^ k| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range (2 * N), |erfcCoeff k| * u ^ (2 * N) := by
              refine Finset.sum_le_sum fun k hk => ?_
              rw [abs_mul, abs_of_pos (pow_pos hu0 k)]
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hu1' (le_of_lt (Finset.mem_range.mp hk))) (abs_nonneg _)
          _ = S * u ^ (2 * N) := by rw [hSdef, Finset.sum_mul]
      have hnum : |Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k|
          ≤ (1 + S) * u ^ (2 * N) := by
        calc |Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k|
            ≤ |Real.exp (-u ^ 2)| + |∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k| :=
              abs_sub _ _
          _ ≤ 1 + S * u ^ (2 * N) := add_le_add hexp1 hpoly
          _ ≤ (1 + S) * u ^ (2 * N) := by nlinarith
      have habs : |h u| = |Real.exp (-u ^ 2)
          - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k| / u ^ (2 * N) := by
        rw [hhdef]
        rw [abs_div, abs_of_pos hup]
      rw [habs, div_le_iff₀ hup]
      calc |Real.exp (-u ^ 2) - ∑ k ∈ Finset.range (2 * N), erfcCoeff k * u ^ k|
          ≤ (1 + S) * u ^ (2 * N) := hnum
        _ ≤ C * u ^ (2 * N) := by
            have h1N : 0 ≤ 1 / (Nat.factorial N : ℝ) := by positivity
            nlinarith
  have hhlim : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 aN) := by
    have hbound : ∀ᶠ u in 𝓝[>] (0:ℝ), ‖h u - aN‖ ≤ c * u ^ 2 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 from one_pos)] with u hu
      rw [Real.norm_eq_abs]
      exact erfcRem_sub_bound N hu.1 hu.2.le
    have hg : Tendsto (fun u : ℝ => c * u ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hcont : Tendsto (fun u : ℝ => c * u ^ 2) (𝓝 0) (𝓝 (c * 0 ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).tendsto 0
      simpa using hcont.mono_left nhdsWithin_le_nhds
    have h0 : Tendsto (fun u : ℝ => h u - aN) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      squeeze_zero_norm' hbound hg
    have := h0.add (tendsto_const_nhds (x := aN))
    simpa using this
  -- run the Watson remainder engine at order 2N
  have hw := erfc_watson_series (a := erfcCoeff) (N := 2 * N) (aN := aN) (C := C)
    hsplit hhm hhC hhlim
  have hw4 := hw.const_mul (((4:ℝ) ^ N)⁻¹)
  -- identify the limit value: 4^{-N}·(-1)^N/N!·(2N)! = (-1)^N·(½)_N
  have hlimval : ((4:ℝ) ^ N)⁻¹ * (aN * Real.Gamma (1 + ((2 * N : ℕ) : ℝ)))
      = (-1 : ℝ) ^ N * (ascPochhammer ℝ N).eval (1 / 2 : ℝ) := by
    rw [add_comm (1:ℝ) _, Real.Gamma_nat_eq_factorial, ascPochhammer_half_eval, haNdef]
    have h4 : ((4:ℝ) ^ N) ≠ 0 := by positivity
    field_simp
  rw [← hlimval]
  -- eventual equality with the goal function, for x > 0
  refine hw4.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  have h2x : (0:ℝ) < 2 * x := by linarith
  -- the Watson sum collapses to the Pochhammer sum
  have hsum : (∑ k ∈ Finset.range (2 * N),
        erfcCoeff k * Real.Gamma (1 + (k : ℝ)) * (2 * x) ^ (-(k : ℝ)))
      = ∑ m ∈ Finset.range N,
          (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m) := by
    have hstep : (∑ k ∈ Finset.range (2 * N),
          erfcCoeff k * Real.Gamma (1 + (k : ℝ)) * (2 * x) ^ (-(k : ℝ)))
        = ∑ k ∈ Finset.range (2 * N),
            erfcCoeff k * (Real.Gamma (1 + (k : ℝ)) * (2 * x) ^ (-(k : ℝ))) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hstep, sum_erfcCoeff N (fun k => Real.Gamma (1 + (k : ℝ)) * (2 * x) ^ (-(k : ℝ)))]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hΓ : Real.Gamma (1 + ((2 * m : ℕ) : ℝ)) = (Nat.factorial (2 * m) : ℝ) := by
      rw [add_comm, Real.Gamma_nat_eq_factorial]
    have hrpow : (2 * x) ^ (-((2 * m : ℕ) : ℝ)) = ((2 * x) ^ (2 * m))⁻¹ := by
      rw [Real.rpow_neg h2x.le, Real.rpow_natCast]
    have hpow : ((2:ℝ) * x) ^ (2 * m) = 4 ^ m * x ^ (2 * m) := by
      rw [mul_pow, pow_mul, show ((2:ℝ) ^ 2) = 4 by norm_num]
    rw [hΓ, hrpow, hpow, ascPochhammer_half_eval m]
    have hfm : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have h4m : ((4:ℝ) ^ m) ≠ 0 := by positivity
    field_simp
  -- the Watson-ready form of erfc
  have h2I : Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x
      = 2 * ∫ u in Ioi (0:ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2) := by
    rw [erfc_eq_watson hx]
    set I := ∫ u in Ioi (0:ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2)
    calc Real.sqrt Real.pi * Real.exp (x ^ 2)
          * (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2) * I)
        = (Real.sqrt Real.pi / Real.sqrt Real.pi)
            * (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) * (2 * I) := by ring
      _ = 2 * I := by
          rw [div_self hπ, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
          ring
  -- final algebra: (2x)^{2N}/4^N = x^{2N} and the power bookkeeping
  have hrpN : ((2:ℝ) * x) ^ (((2 * N : ℕ)) : ℝ) = (2 * x) ^ (2 * N) :=
    Real.rpow_natCast _ _
  set I := ∫ u in Ioi (0:ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2) with hIdef
  show ((4:ℝ) ^ N)⁻¹ * ((2 * x) ^ (((2 * N : ℕ)) : ℝ) *
      ((2 * x) * I - ∑ k ∈ Finset.range (2 * N),
          erfcCoeff k * Real.Gamma (1 + (k : ℝ)) * (2 * x) ^ (-(k : ℝ))))
    = x ^ (2 * N + 1) *
        (Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x
          - ∑ m ∈ Finset.range N,
              (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m + 1))
  rw [hrpN, hsum, h2I]
  have hfour : ((4:ℝ) ^ N)⁻¹ * ((2 * x) ^ (2 * N)) = x ^ (2 * N) := by
    have h4 : ((4:ℝ) ^ N) ≠ 0 := by positivity
    rw [mul_pow, pow_mul, show ((2:ℝ) ^ 2) = 4 by norm_num, ← mul_assoc,
      inv_mul_cancel₀ h4, one_mul]
  have hsums : x ^ (2 * N) * (∑ m ∈ Finset.range N,
        (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m))
      = x ^ (2 * N + 1) * (∑ m ∈ Finset.range N,
        (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    field_simp
    ring
  calc ((4:ℝ) ^ N)⁻¹ * ((2 * x) ^ (2 * N) * ((2 * x) * I
        - ∑ m ∈ Finset.range N,
            (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m)))
      = (((4:ℝ) ^ N)⁻¹ * (2 * x) ^ (2 * N)) * ((2 * x) * I)
          - (((4:ℝ) ^ N)⁻¹ * (2 * x) ^ (2 * N)) * (∑ m ∈ Finset.range N,
              (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m)) := by ring
    _ = x ^ (2 * N) * ((2 * x) * I) - x ^ (2 * N + 1) * (∑ m ∈ Finset.range N,
            (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m + 1)) := by
        rw [hfour, hsums]
    _ = x ^ (2 * N + 1) * (2 * I - ∑ m ∈ Finset.range N,
            (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (1 / 2 : ℝ) / x ^ (2 * m + 1)) := by
        ring

/-- **DLMF 7.12.1.** The complete (Poincaré) asymptotic expansion of `erfc` for complex
`z → ∞` in the closed sector `|ph z| ≤ 3π/4 − δ` (any `δ ∈ (0, 3π/4)`):
`z^{2N+1} · (√π · e^{z²} · erfc(z) − Σ_{m<N} (-1)^m (½)_m / z^{2m+1}) → (-1)^N (½)_N`
along the filter "infinity in the sector" (`comap norm atTop ⊓ principal {sector}`, the
standard DLMF-sector-at-infinity idiom, also used for the leading-order `N = 0` case
`erfc_7_12_1_complex` in `ErfcLeading.lean` and in
`Frameworks.Hypergeometric.Ch15AsymptoticApproximations`).  Specializes to the real
surface `erfc_7_12_1` on `ph z = 0`, and to `erfc_7_12_1_complex` at `N = 0`.

DAG: E-7.12.1.
Numerical: N/A (unparsed:char '⊓')
Verified: verified
-/
theorem erfc_7_12_1_complex_series (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 3 * Real.pi / 4) :
    Tendsto (fun z : ℂ => z ^ (2 * N + 1) *
        ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
          - ∑ m ∈ Finset.range N,
              (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (1 / 2 : ℂ) / z ^ (2 * m + 1)))
      (comap norm atTop ⊓
        principal {z : ℂ | |Complex.arg z| ≤ 3 * Real.pi / 4 - δ})
      (𝓝 ((-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval (1 / 2 : ℂ))) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set κ : ℝ := Real.sin (2 * δ / 3) with hκdef
  have hκ : 0 < κ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set F : Filter ℂ := comap norm atTop ⊓
    principal {z : ℂ | |Complex.arg z| ≤ 3 * Real.pi / 4 - δ} with hFdef
  set C : ℝ := 2 * (Nat.factorial (2 * (N + 1)) : ℝ) / (2 * κ) ^ (2 * (N + 1) + 1) with hCdef
  set L : ℂ := (-1 : ℂ) ^ N * (ascPochhammer ℂ N).eval (1 / 2 : ℂ) with hLdef
  have hev : ∀ᶠ z : ℂ in F,
      ‖z ^ (2 * N + 1) * ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
          - ∑ m ∈ Finset.range N,
              (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (1 / 2 : ℂ) / z ^ (2 * m + 1)) - L‖
        ≤ C * (‖z‖ ^ 2)⁻¹ := by
    have h1 : ∀ᶠ z : ℂ in F, (1:ℝ) < ‖z‖ :=
      (tendsto_comap.eventually (eventually_gt_atTop (1:ℝ))).filter_mono inf_le_left
    have h2 : ∀ᶠ z : ℂ in F, |Complex.arg z| ≤ 3 * Real.pi / 4 - δ := by
      rw [hFdef]
      exact eventually_inf_principal.mpr (Eventually.of_forall (fun z hz => hz))
    filter_upwards [h1, h2] with z hz1 hz2
    have hzn : (0:ℝ) < ‖z‖ := by linarith
    have hz : z ≠ 0 := by
      intro h
      rw [h] at hzn
      simp at hzn
    have hb := cerfc_poincare_bound hδ hδ' hz hz2 (N + 1)
    rw [Finset.sum_range_succ, ← hκdef] at hb
    have hsumeq : (∑ m ∈ Finset.range N,
          (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (1 / 2 : ℂ) / z ^ (2 * m + 1))
        = ∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4:ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ascPochhammer_half_eval_complex m]
      ring
    have hzp : z ^ (2 * N + 1) ≠ 0 := pow_ne_zero _ hz
    have hG : z ^ (2 * N + 1) * ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
          - ∑ m ∈ Finset.range N,
              (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (1 / 2 : ℂ) / z ^ (2 * m + 1)) - L
        = z ^ (2 * N + 1) * ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
            - ((∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
                  / ((4:ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1))
              + (-1 : ℂ) ^ N * (Nat.factorial (2 * N) : ℂ)
                  / ((4:ℂ) ^ N * (Nat.factorial N : ℂ)) / z ^ (2 * N + 1))) := by
      rw [hsumeq, hLdef, ascPochhammer_half_eval_complex N]
      field_simp
      ring
    rw [hG, norm_mul, norm_pow]
    calc ‖z‖ ^ (2 * N + 1) * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
            - ((∑ j ∈ Finset.range N, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
                  / ((4:ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1))
              + (-1 : ℂ) ^ N * (Nat.factorial (2 * N) : ℂ)
                  / ((4:ℂ) ^ N * (Nat.factorial N : ℂ)) / z ^ (2 * N + 1))‖
        ≤ ‖z‖ ^ (2 * N + 1) * (2 * (Nat.factorial (2 * (N + 1)) : ℝ)
            / (2 * (κ * ‖z‖)) ^ (2 * (N + 1) + 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * (‖z‖ ^ 2)⁻¹ := by
          rw [hCdef, show (2 * (κ * ‖z‖)) = (2 * κ) * ‖z‖ by ring, mul_pow]
          field_simp
          ring
  have hg : Tendsto (fun z : ℂ => C * (‖z‖ ^ 2)⁻¹) F (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    have h3 : Tendsto (fun r : ℝ => C * (r ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using h1.inv_tendsto_atTop.const_mul C
    have h4 : Tendsto (fun z : ℂ => C * (‖z‖ ^ 2)⁻¹) (comap norm atTop) (𝓝 0) := by
      have := h3.comp (tendsto_comap (f := fun z : ℂ => ‖z‖) (x := atTop))
      simpa [Function.comp] using this
    exact (h4.mono_left inf_le_left)
  have h0 : Tendsto (fun z : ℂ => z ^ (2 * N + 1) *
      ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
        - ∑ m ∈ Finset.range N,
            (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (1 / 2 : ℂ) / z ^ (2 * m + 1)) - L)
      F (𝓝 0) := squeeze_zero_norm' hev hg
  have hfin := h0.add (tendsto_const_nhds (x := L) (f := F))
  simpa using hfin

end FLMF.Error
