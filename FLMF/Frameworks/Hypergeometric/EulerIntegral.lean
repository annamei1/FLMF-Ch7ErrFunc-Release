import FLMF.Frameworks.Hypergeometric.GaussODE
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Euler's integral representation of `₂F₁` (framework — real-variable forms)

The theorems in this file are real-variable instances of DLMF 5.2.5, 5.12.1,
and 15.6.1; the faithful complex-domain surfaces live in
`FLMF.Frameworks.Hypergeometric.EulerPfaffComplex`
(`ascPochhammer_eval_eq_Gamma_div_complex`, `betaIntegral_eq_Gamma_div`,
`ordinaryHypergeometric_eq_betaIntegral_complex`).

* `integral_rpow_mul_one_sub_rpow` — the real Beta integral
  `∫₀¹ t^(p−1)(1−t)^(q−1) dt = Γ(p)Γ(q)/Γ(p+q)`, real `p, q > 0`.
* `ascPochhammer_eval_eq_Gamma_div_real` — `(x)ₙ = Γ(x+n)/Γ(x)` over `ℝ`,
  `x > 0`.
* `ordinaryHypergeometric_eq_betaIntegral` — **Euler's integral**, real form:
  for `0 < b < c`, `a` off the nonpositive integers and `|z| < 1`,
  `∫₀¹ t^(b−1)(1−t)^(c−b−1)(1−zt)^(−a) dt = (Γ(b)Γ(c−b)/Γ(c)) ₂F₁(a,b;c;z)`.

The binomial factor `(1−zt)^(−a)` is expanded by Mathlib's binomial series
(`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`, coefficients
`Ring.choose (a+n−1) n = (a)ₙ/n!`); the sum–integral interchange is dominated
by `|cₙ||z|ⁿ·B(b, c−b)`; the termwise Beta values recombine through
`B(b+n, c−b)/B(b, c−b) = (b)ₙ/(c)ₙ`.
-/

noncomputable section

open Nat MeasureTheory Real Set FormalMultilinearSeries

namespace FLMF.Hypergeometric

section RealBeta

/-- The real Beta integrand is integrable on `(0, 1]` for positive exponents
(the real form of `Complex.betaIntegral_convergent`). -/
-- no-dlmf: Beta-integral convergence helper (the identity itself is DLMF 5.12.1 below)
theorem integrableOn_rpow_mul_one_sub_rpow {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) * (1 - t) ^ (q - 1)) (Ioc (0 : ℝ) 1) := by
  have hC := Complex.betaIntegral_convergent (u := (p : ℂ)) (v := (q : ℂ))
    (by simpa using hp) (by simpa using hq)
  have hC2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hC
  refine (IntegrableOn.congr_fun hC2.re (fun t ht => ?_) measurableSet_Ioc)
  have h0t : (0 : ℝ) ≤ t := ht.1.le
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
  rw [show ((p : ℂ) - 1) = ((p - 1 : ℝ) : ℂ) by push_cast; ring,
    show ((q : ℂ) - 1) = ((q - 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow h0t (p - 1), ← Complex.ofReal_cpow h1t (q - 1),
    ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

-- no-dlmf: real/narrowed instance of DLMF 5.12.1, restricted to real `p, q > 0`
-- rather than DLMF's complex `a, b` with `Re a > 0, Re b > 0`; faithful surface
-- is `betaIntegral_eq_Gamma_div` (FLMF/Frameworks/Hypergeometric/EulerPfaffComplex.lean)
/-- The real Beta integral:
`∫₀¹ t^(p−1)(1−t)^(q−1) dt = Γ(p)Γ(q)/Γ(p+q)`, for `p, q > 0`. -/
theorem integral_rpow_mul_one_sub_rpow {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in (0 : ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1)
      = Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (p : ℂ)) (t := (q : ℂ)) (by simpa using hp) (by simpa using hq)
  have hcast : Complex.betaIntegral p q
      = ((∫ t in (0 : ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have h0t : (0 : ℝ) ≤ t := ht.1
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
    rw [show ((p : ℂ) - 1) = ((p - 1 : ℝ) : ℂ) by push_cast; ring,
      show ((q : ℂ) - 1) = ((q - 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h0t (p - 1), ← Complex.ofReal_cpow h1t (q - 1),
      ← Complex.ofReal_mul]
  have hΓ : Real.Gamma (p + q) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have key : Real.Gamma p * Real.Gamma q
      = Real.Gamma (p + q) * ∫ t in (0 : ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1) := by
    rw [hcast, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      Complex.Gamma_ofReal] at hbeta
    exact_mod_cast hbeta
  rw [eq_div_iff hΓ]
  linarith [key]

-- no-dlmf: real/narrowed instance of DLMF 5.2.5, restricted to real `x > 0`
-- rather than DLMF's complex `a` off the nonpositive integers; faithful surface
-- is `ascPochhammer_eval_eq_Gamma_div_complex` (FLMF/Frameworks/Hypergeometric/EulerPfaffComplex.lean)
/-- `(x)ₙ = Γ(x+n)/Γ(x)` over `ℝ`, for `x > 0`. -/
theorem ascPochhammer_eval_eq_Gamma_div_real {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (ascPochhammer ℝ n).eval x = Real.Gamma (x + n) / Real.Gamma x := by
  have hΓx : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  induction n with
  | zero => simp [hΓx]
  | succ n ih =>
    have hxn : x + (n : ℝ) ≠ 0 := by positivity
    rw [ascPochhammer_succ_eval, ih,
      show x + ((n : ℕ) + 1 : ℕ) = (x + n) + 1 by push_cast; ring,
      Real.Gamma_add_one hxn]
    field_simp

end RealBeta

section EulerIntegral

/-- The generalized binomial coefficient as a Pochhammer quotient:
`Ring.choose (a+n−1) n = (a)ₙ/n!` — the coefficients of `(1−x)^(−a)`. -/
-- no-dlmf: binomial-coefficient/Pochhammer bookkeeping, no single DLMF equation
theorem ringChoose_add_sub_one (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℝ n).eval a / n ! := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    show a + (n : ℝ) - 1 - n + 1 = a by ring,
    Polynomial.ascPochhammer_smeval_eq_eval, smul_eq_mul]
  ring

variable (a b c : ℝ)

-- no-dlmf: real/narrowed instance of DLMF 15.6.1, restricted to real `a, b, c, z`
-- rather than DLMF's complex parameters `a, b, c` and complex variable `z`;
-- faithful surface is `ordinaryHypergeometric_eq_betaIntegral_complex`
-- (FLMF/Frameworks/Hypergeometric/EulerPfaffComplex.lean)
/-- Euler's integral representation of `₂F₁` (real form):
for `0 < b < c`, `a` off the nonpositive integers, and `|z| < 1`,
`∫₀¹ t^(b−1)(1−t)^(c−b−1)(1−zt)^(−a) dt = (Γ(b)Γ(c−b)/Γ(c)) · ₂F₁(a,b;c;z)`. -/
theorem ordinaryHypergeometric_eq_betaIntegral (ha : ∀ k : ℕ, (k : ℝ) ≠ -a)
    (hb : 0 < b) (hbc : b < c) {z : ℝ} (hz : |z| < 1) :
    ∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a)
      = (Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c) * ₂F₁ a b c z := by
  have hcb : 0 < c - b := by linarith
  have hc : 0 < c := by linarith
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  -- the termwise integrands
  set F : ℕ → ℝ → ℝ := fun n t =>
    Ring.choose (a + n - 1) n * z ^ n * (t ^ (b + n - 1) * (1 - t) ^ (c - b - 1)) with hF
  -- pointwise expansion on `(0, 1]`
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
      t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a) = ∑' n : ℕ, F n t := by
    intro t ht
    have htpos : 0 < t := ht.1
    have hzt : ‖z * t‖ < 1 := by
      rw [Real.norm_eq_abs, abs_mul]
      calc |z| * |t| ≤ |z| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg z)
            rw [abs_of_pos htpos]
            exact ht.2
        _ < 1 := by rwa [mul_one]
    have h1zt : 0 < 1 - z * t := by
      have : z * t ≤ |z * t| := le_abs_self _
      rw [Real.norm_eq_abs] at hzt
      linarith
    have hbs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum_sub
      (y := z * t) (by rw [mem_eball_zero_iff, ← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hzt)
    have hpow : (1 - z * t) ^ (-a) = 1 / (1 - z * t) ^ a := by
      rw [Real.rpow_neg h1zt.le, one_div]
    rw [hpow]
    have hsum := (hbs.mul_right (t ^ (b - 1) * (1 - t) ^ (c - b - 1))).tsum_eq.symm
    simp only [sub_zero] at hsum
    rw [mul_comm, hsum]
    refine tsum_congr fun n => ?_
    rw [ofScalars_apply_eq, smul_eq_mul]
    simp only [hF]
    have ht1 : t ^ (b + n - 1) = t ^ (n : ℕ) * t ^ (b - 1) := by
      rw [← Real.rpow_natCast t n, ← Real.rpow_add htpos,
        show (n : ℝ) + (b - 1) = b + n - 1 by ring]
    rw [ht1, mul_pow]
    ring
  -- integrability of each term
  have hFint : ∀ n : ℕ, IntegrableOn (F n) (Ioc (0 : ℝ) 1) := by
    intro n
    have h := integrableOn_rpow_mul_one_sub_rpow (p := b + n) (q := c - b)
      (by positivity) hcb
    exact h.const_mul _
  -- summability of the norm-integrals
  have hFsum : Summable fun n : ℕ => ∫ t in Ioc (0 : ℝ) 1, ‖F n t‖ := by
    have hBint := integrableOn_rpow_mul_one_sub_rpow hb hcb
    have hbound : ∀ n : ℕ, ∫ t in Ioc (0 : ℝ) 1, ‖F n t‖
        ≤ ‖Ring.choose (a + n - 1) n * z ^ n‖
          * ∫ t in Ioc (0 : ℝ) 1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) := by
      intro n
      rw [← integral_const_mul]
      refine setIntegral_mono_on ((hFint n).norm) (hBint.const_mul _) measurableSet_Ioc
        fun t ht => ?_
      have htpos : 0 < t := ht.1
      have h1t : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
      have hX0 : (0 : ℝ) ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
        mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.rpow_nonneg h1t _)
      have ht1 : t ^ (b + n - 1) = t ^ (n : ℕ) * t ^ (b - 1) := by
        rw [← Real.rpow_natCast t n, ← Real.rpow_add htpos,
          show (n : ℝ) + (b - 1) = b + n - 1 by ring]
      have hnorm : ‖F n t‖ = ‖Ring.choose (a + (n : ℝ) - 1) n * z ^ n‖
          * (t ^ (n : ℕ) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))) := by
        simp only [hF]
        rw [norm_mul, Real.norm_eq_abs (t ^ (b + (n : ℝ) - 1) * (1 - t) ^ (c - b - 1)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ (b + (n : ℝ) - 1)
            * (1 - t) ^ (c - b - 1)), ht1]
        ring
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left hX0 (pow_le_one₀ htpos.le ht.2)) (norm_nonneg _)
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) hbound ?_
    refine Summable.mul_right _ ?_
    -- `∑ ‖cₙ zⁿ‖` converges since `|z| < 1 ≤ radius` of the binomial series
    have hrad := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).r_le
    have hmem : (|z| : ℝ) ∈ Metric.eball (0 : ℝ)
        (FormalMultilinearSeries.ofScalars ℝ (fun n => Ring.choose (a + n - 1) n)).radius := by
      rw [mem_eball_zero_iff]
      refine lt_of_lt_of_le ?_ hrad
      rw [← ofReal_norm]
      exact ENNReal.ofReal_lt_one.mpr (by simpa using hz)
    have hsum := (FormalMultilinearSeries.ofScalars ℝ
      (fun n => Ring.choose (a + n - 1) n)).summable_norm_apply hmem
    refine hsum.congr fun n => ?_
    rw [ofScalars_apply_eq, smul_eq_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      Real.norm_eq_abs z, Real.norm_eq_abs |z|, abs_abs]
  -- interchange and integrate termwise
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  have hterm : ∀ n : ℕ, ∫ t in Ioc (0 : ℝ) 1, F n t
      = Ring.choose (a + n - 1) n * z ^ n
        * (Real.Gamma (b + n) * Real.Gamma (c - b) / Real.Gamma (c + n)) := by
    intro n
    simp only [hF]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow_mul_one_sub_rpow (by positivity : (0:ℝ) < b + n) hcb,
      show b + (n : ℝ) + (c - b) = c + n by ring]
  -- match against the Gauss series
  have habc : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -c := by
    intro kn
    refine ⟨ha kn, ?_, ?_⟩
    · intro h
      have := Nat.cast_nonneg (α := ℝ) kn
      rw [h] at this
      linarith
    · intro h
      have := Nat.cast_nonneg (α := ℝ) kn
      rw [h] at this
      linarith
  have hM := (ordinaryHypergeometric_hasSum a b c habc
    (by rwa [Real.norm_eq_abs])).mul_left
    (Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c)
  have hterm2 : (fun n : ℕ => (Real.Gamma b * Real.Gamma (c - b) / Real.Gamma c)
      * (ordinaryHypergeometricCoefficient a b c n * z ^ n)) =
      fun n : ℕ => Ring.choose (a + n - 1) n * z ^ n
        * (Real.Gamma (b + n) * Real.Gamma (c - b) / Real.Gamma (c + n)) := by
    funext n
    have hPb : (ascPochhammer ℝ n).eval b = Real.Gamma (b + n) / Real.Gamma b :=
      ascPochhammer_eval_eq_Gamma_div_real hb n
    have hPc : (ascPochhammer ℝ n).eval c = Real.Gamma (c + n) / Real.Gamma c :=
      ascPochhammer_eval_eq_Gamma_div_real hc n
    have hΓbn : Real.Gamma (b + n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hΓcn : Real.Gamma (c + n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hfn : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    rw [ringChoose_add_sub_one]
    simp only [ordinaryHypergeometricCoefficient, hPb, hPc]
    field_simp
  rw [hterm2] at hM
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_fun measurableSet_Ioc hpt, ← hswap]
  rw [tsum_congr hterm, hM.tsum_eq]

end EulerIntegral

end FLMF.Hypergeometric
