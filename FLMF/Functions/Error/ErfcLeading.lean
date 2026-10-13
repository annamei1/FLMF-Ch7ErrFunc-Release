import FLMF.Methods.Watson
import FLMF.Methods.LaplaceTransform
import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.ComplexErf
import FLMF.Functions.Error.Faddeeva
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Leading asymptotics of the complementary error function `erfc`

We work with the Watson-ready representation
`erfc(x) = (2/√π) · e^{-x²} ∫_{(0,∞)} e^{-(2x) u} · e^{-u²} du`,
obtained from `erfc(x) = (2/√π) ∫_x^∞ e^{-t²} dt` by the substitution
`t = x + u` (DLMF §7.2, §7.12.1).  The leading asymptotic
`erfc(x) ~ e^{-x²}/(x √π)` then follows from the leading-order Watson lemma
`PicardLefschetz.watson_leading` with `s = 1`, parameter `2x`,
`g(u) = e^{-u²}` and `a₀ = g(0⁺) = 1`.

`erfc` itself is the canonical `1 - erf` of `FLMF.Functions.Error.Erf`; the
Watson-ready form is recorded here as the theorem `erfc_eq_watson`.

Main results:

* `FLMF.Error.erfc_eq_watson` — the Watson-ready (`t = x + u`) integral form.
* `FLMF.Error.tendsto_watson_factor` — the Watson factor tends to `1`.
* `FLMF.Error.erfc_asymptotic` — **DLMF 7.12.1 (leading term)**, real axis.
* `FLMF.Error.cerfc_poincare_bound` — the uniform Poincaré remainder estimate on the
  complex sector `|ph z| ≤ 3π/4 − δ`, at every truncation order (obtained by rotating
  the Laplace ray; reused by `ErfcSeries.lean`).
* `FLMF.Error.erfc_7_12_1_complex` — **DLMF 7.12.1 (leading term)**, complex sector.
-/

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set PicardLefschetz

-- no-dlmf: exact Watson-ready integral transformation (change of variables
-- s = x + u on the tail form of erfc); DLMF 7.12.1 itself states the Poincaré
-- *asymptotic* expansion, proved separately below as `erfc_asymptotic`
/-- **The Watson-ready (`t = x + u`) form of `erfc`** (DLMF 7.12.1):
`erfc(x) = (2/√π) · e^{-x²} ∫_{(0,∞)} e^{-(2x) u} · e^{-u²} du`, for `x > 0`.

This follows from the tail form `erfc x = (2/√π) ∫_{(x,∞)} e^{-s²}` by the
shift `s = x + u`, with `e^{-(x+u)²} = e^{-x²} · e^{-(2x) u} · e^{-u²}`.

DLMF 7.12.1.
-/
theorem erfc_eq_watson {x : ℝ} (hx : 0 < x) :
    erfc x = (2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) *
      ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hgi : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
    have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
    simpa [one_mul] using this
  -- tail form: `erfc x = (2/√π) ∫_{Ioi x} e^{−s²}`
  have htail : erfc x = 2 / Real.sqrt Real.pi * ∫ s in Ioi x, Real.exp (-s ^ 2) := by
    have hsplit : (∫ s in Ioi (0 : ℝ), Real.exp (-s ^ 2))
        = (∫ s in Ioc 0 x, Real.exp (-s ^ 2)) + ∫ s in Ioi x, Real.exp (-s ^ 2) := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hgi.integrableOn hgi.integrableOn, Ioc_union_Ioi_eq_Ioi hx.le]
    have hocx : (∫ s in Ioc 0 x, Real.exp (-s ^ 2)) = ∫ s in (0 : ℝ)..x, Real.exp (-s ^ 2) := by
      rw [intervalIntegral.integral_of_le hx.le]
    have hIoix : (∫ s in Ioi x, Real.exp (-s ^ 2))
        = Real.sqrt Real.pi / 2 - ∫ s in (0 : ℝ)..x, Real.exp (-s ^ 2) := by
      have := hsplit
      rw [integral_Ioi_gaussian, hocx] at this
      linarith
    rw [hIoix, erfc, erf]
    field_simp
  -- change of variables `s = x + u`, mapping `Ioi 0 → Ioi x`
  set φ : ℝ → ℝ := fun u => x + u with hφ
  have himg : φ '' Ioi 0 = Ioi x := by
    ext s
    simp only [hφ, mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩; linarith
    · intro hs; exact ⟨s - x, by linarith, by ring⟩
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt φ 1 (Ioi 0) u := by
    intro u _
    have : HasDerivAt φ 1 u := by
      simpa [hφ] using ((hasDerivAt_const u x).add (hasDerivAt_id u))
    exact this.hasDerivWithinAt
  have hinj : InjOn φ (Ioi 0) := by
    intro a _ b _ hab
    simpa [hφ] using hab
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun s => Real.exp (-s ^ 2))
  rw [himg] at hcov
  -- the transformed integrand collapses to `e^{−x²} · e^{−(2x)u} · e^{−u²}`
  have hpt : ∀ u ∈ Ioi (0 : ℝ),
      |(1 : ℝ)| • Real.exp (-φ u ^ 2)
        = Real.exp (-x ^ 2) * (Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2)) := by
    intro u _
    have hE : Real.exp (-φ u ^ 2)
        = Real.exp (-x ^ 2) * (Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [hφ]; ring
    rw [abs_one, one_smul, hE]
  have hInt : (∫ s in Ioi x, Real.exp (-s ^ 2))
      = Real.exp (-x ^ 2) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2) := by
    rw [hcov, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [htail, hInt]
  ring

-- no-dlmf: Watson amplitude g(u)=e^{-u²}; proof infrastructure, no DLMF identity
/-- `g(u) = e^{-u²}`, the Watson amplitude for `erfc`. -/
private noncomputable def gErf (u : ℝ) : ℝ := Real.exp (-u ^ 2)

-- no-dlmf: measurability of the Watson amplitude; proof infrastructure, no DLMF identity
private theorem gErf_measurable : Measurable gErf := by
  unfold gErf
  fun_prop

-- no-dlmf: boundedness of the Watson amplitude; proof infrastructure, no DLMF identity
private theorem gErf_bdd : ∀ t ∈ Ioi (0 : ℝ), |gErf t| ≤ 1 := by
  intro t ht
  unfold gErf
  rw [abs_of_pos (Real.exp_pos _)]
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg t]

-- no-dlmf: boundary limit g(0⁺)=1 of the Watson amplitude; proof infrastructure, no DLMF identity
private theorem gErf_lim : Tendsto gErf (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have : Tendsto gErf (𝓝 (0 : ℝ)) (𝓝 1) := by
    unfold gErf
    have h : Tendsto (fun u : ℝ => Real.exp (-u ^ 2)) (𝓝 0) (𝓝 (Real.exp (-(0:ℝ) ^ 2))) := by
      apply Real.continuous_exp.continuousAt.comp
      fun_prop
    simpa using h
  exact this.mono_left nhdsWithin_le_nhds

-- no-dlmf: intermediate Watson-factor limit toward the 7.12.1 asymptotic; proof infrastructure, no distinct DLMF identity
/-- The Watson factor `(2x) · ∫_{(0,∞)} e^{-(2x) u} · e^{-u²} du` of `erfc`
tends to `1` as `x → ∞`. -/
theorem tendsto_watson_factor :
    Tendsto (fun x : ℝ => (2 * x) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2))
      atTop (𝓝 1) := by
  -- Apply Watson's lemma with parameter `p = 2x`, then precompose with `x ↦ 2x`.
  have h := watson_leading (s := 1) (one_pos) (g := gErf) (a₀ := 1) (C := 1)
    gErf_measurable gErf_bdd gErf_lim
  have h' :
      Tendsto (fun p : ℝ => p *
          ∫ u in Ioi (0 : ℝ), Real.exp (-p * u) * Real.exp (-u ^ 2))
        atTop (𝓝 (1 * Real.Gamma 1)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    rw [Real.rpow_one]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u hu
    simp only [gErf, show (1:ℝ) - 1 = 0 from by norm_num, Real.rpow_zero, one_mul]
  rw [Real.Gamma_one, mul_one] at h'
  -- Compose with `x ↦ 2x → ∞`.
  have hcomp : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop' (by norm_num : (0:ℝ) < 2)
  exact h'.comp hcomp

-- no-dlmf: real/narrowed restriction of DLMF 7.12.1; faithful surface is erfc_7_12_1_complex
/-- **Leading term of the `erfc` asymptotic expansion, real axis.**
`erfc(x) ~ e^{-x²}/(x √π)`, in the precise sense that
`x · √π · e^{x²} · erfc(x) → 1` as `x → ∞`.  DLMF 7.12.1 itself is stated for
complex `z` in the sector `|ph z| ≤ 3π/4 − δ`; see `erfc_7_12_1_complex`.
-/
theorem erfc_asymptotic :
    Tendsto (fun x : ℝ => x * Real.sqrt Real.pi * Real.exp (x ^ 2) * erfc x)
      atTop (𝓝 1) := by
  refine tendsto_watson_factor.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [erfc_eq_watson hx]
  set I := ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2) with hI
  have hsqrt_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pos
  have hexp : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : (Real.sqrt Real.pi)⁻¹ * Real.sqrt Real.pi = 1 :=
    inv_mul_cancel₀ hsqrt_ne
  calc
    (2 * x) * I
        = (2 * x) * ((Real.sqrt Real.pi)⁻¹ * Real.sqrt Real.pi) *
            (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) * I := by
          rw [hexp, hsq]; ring
    _ = x * Real.sqrt Real.pi * Real.exp (x ^ 2) *
            ((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) * I) := by
          rw [div_eq_mul_inv]; ring

/-! ### The complex sector `|ph z| ≤ 3π/4 - δ`

The real asymptotic above rests on Watson's lemma along the positive axis.  That route
does not reach DLMF's sector `|ph z| ≤ 3π/4 - δ`: for `Re z < 0` the Laplace integrand
`e^{-2zu-u²}` on the *real* ray `u ∈ (0,∞)` grows like `e^{(Re z)²}` before it decays, so
the naive absolute bound is useless.  The fix is the classical contour rotation, which we
obtain for free from the already-proven DLMF 7.7.3 Gaussian integral: integrate along the
ray `arg u = θ` with `θ = -(ph z)/3`, so that both `Re(z e^{iθ}) ≥ sin(2δ/3)|z| > 0` and
`Re(e^{2iθ}) > 0`.  Expanding the Gaussian factor with a *uniform* Taylor remainder then
gives the sector estimate `cerfc_poincare_bound`, from which both `erfc_7_12_1_complex`
here and `erfc_7_12_1_complex_series` (in `ErfcSeries.lean`) follow by squeezing.
-/

-- no-dlmf: Taylor-remainder estimate for `exp` on the closed left half-plane;
-- proof infrastructure for the sector form of 7.12.1, no DLMF identity number
/-- **Taylor remainder of `exp` on the closed left half-plane.**  If `Re x ≤ 0` then
`‖e^x - Σ_{i<n} xⁱ/i!‖ ≤ ‖x‖ⁿ`.  (The mean-value estimate along the segment `[0,x]`,
which stays in the half-plane; the bound is *uniform*, unlike the usual
`e^{‖x‖}`-weighted one, and this uniformity is what makes the sector estimate work.) -/
private theorem norm_cexp_sub_taylor_le :
    ∀ (n : ℕ) {x : ℂ}, x.re ≤ 0 →
      ‖Complex.exp x - ∑ i ∈ Finset.range n, x ^ i / (Nat.factorial i : ℂ)‖ ≤ ‖x‖ ^ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Complex.norm_exp]
    calc Real.exp x.re ≤ Real.exp 0 := Real.exp_le_exp.mpr hx
      _ = 1 := Real.exp_zero
  | succ n ih =>
    intro x hx
    -- the segment function `g t = exp (t x) - Σ_{i<n+1} (t x)^i/i!`
    set g : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * x)
      - ∑ i ∈ Finset.range (n + 1), ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ) with hg
    set g' : ℝ → ℂ := fun t => x * (Complex.exp ((t : ℂ) * x)
      - ∑ i ∈ Finset.range n, ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ)) with hg'
    have hderiv : ∀ t : ℝ, HasDerivAt g (g' t) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * x))
          (x * Complex.exp ((t : ℂ) * x)) t := by
        have hu : HasDerivAt (fun u : ℂ => u * x) x (t : ℂ) := by
          simpa using (hasDerivAt_id (t : ℂ)).mul_const x
        have := (hu.cexp).comp_ofReal
        simpa [mul_comm] using this
      have h2 : ∀ i : ℕ, HasDerivAt (fun t : ℝ => ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ))
          ((i : ℂ) * ((t : ℂ) * x) ^ (i - 1) * x / (Nat.factorial i : ℂ)) t := by
        intro i
        have hu : HasDerivAt (fun u : ℂ => u * x) x (t : ℂ) := by
          simpa using (hasDerivAt_id (t : ℂ)).mul_const x
        have hp : HasDerivAt (fun u : ℂ => (u * x) ^ i)
            ((i : ℂ) * ((t : ℂ) * x) ^ (i - 1) * x) (t : ℂ) := by
          simpa using (hu.pow i)
        exact (hp.div_const _).comp_ofReal
      have h3 := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (n + 1)) => h2 i)
      have hsum : (∑ i ∈ Finset.range (n + 1),
            (i : ℂ) * ((t : ℂ) * x) ^ (i - 1) * x / (Nat.factorial i : ℂ))
          = x * ∑ i ∈ Finset.range n, ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hf : ((Nat.factorial (i + 1) : ℂ)) = ((i : ℂ) + 1) * (Nat.factorial i : ℂ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hne : ((i : ℂ) + 1) ≠ 0 := by
          have h : ((i + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)
          simpa using h
        have hfi : ((Nat.factorial i : ℂ)) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
        simp only [Nat.add_sub_cancel]
        rw [hf]
        push_cast
        field_simp
      have h3' : HasDerivAt
          (fun t : ℝ => ∑ i ∈ Finset.range (n + 1), ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ))
          (x * ∑ i ∈ Finset.range n, ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ)) t := by
        rw [← hsum]
        exact h3
      have hfin := h1.fun_sub h3'
      rw [hg]
      convert hfin using 1
      ring
    have hbound : ∀ t ∈ Ico (0:ℝ) 1, ‖g' t‖ ≤ ‖x‖ ^ (n + 1) := by
      intro t ht
      have ht0 : (0:ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have hre : ((t : ℂ) * x).re ≤ 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos ht0 hx
      have hIH := ih hre
      have hnorm : ‖(t : ℂ) * x‖ = t * ‖x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      rw [hg', norm_mul]
      calc ‖x‖ * ‖Complex.exp ((t : ℂ) * x)
              - ∑ i ∈ Finset.range n, ((t : ℂ) * x) ^ i / (Nat.factorial i : ℂ)‖
          ≤ ‖x‖ * ‖(t : ℂ) * x‖ ^ n := by
            exact mul_le_mul_of_nonneg_left hIH (norm_nonneg _)
        _ = ‖x‖ * (t ^ n * ‖x‖ ^ n) := by rw [hnorm, mul_pow]
        _ ≤ ‖x‖ * (1 ^ n * ‖x‖ ^ n) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht1 n) (by positivity)
        _ = ‖x‖ ^ (n + 1) := by rw [one_pow, one_mul]; ring
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := g) (f' := g') (a := 0) (b := 1) (C := ‖x‖ ^ (n + 1))
      (fun t _ => (hderiv t).hasDerivWithinAt) hbound 1 (by simp)
    have hg1 : g 1 = Complex.exp x - ∑ i ∈ Finset.range (n + 1), x ^ i / (Nat.factorial i : ℂ) := by
      simp [hg]
    have hg0 : g 0 = 0 := by
      simp only [hg, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      rw [Finset.sum_range_succ']
      simp
    rw [hg1, hg0, sub_zero] at hseg
    simpa using hseg

-- no-dlmf: integrability of the real Laplace moment integrand; proof infrastructure,
-- no DLMF identity number
/-- Integrability of `sᵏ e^{-a s}` on `(0,∞)` for real `a > 0`. -/
private theorem integrableOn_pow_mul_rexp {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(a * s))) (Ioi (0 : ℝ)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine IntegrableOn.congr_fun
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := a) hk le_rfl ha)
    (fun s _ => ?_) measurableSet_Ioi
  rw [Real.rpow_one, Real.rpow_natCast]
  ring_nf

-- no-dlmf: value of the real Laplace moment (Γ-integral instance); proof
-- infrastructure, no DLMF identity number
/-- The real Laplace moment `∫₀^∞ sᵏ e^{-a s} ds = k!/a^{k+1}`, `a > 0`. -/
private theorem integral_pow_mul_rexp {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(a * s)))
      = (Nat.factorial k : ℝ) / a ^ (k + 1) := by
  have hk : (0:ℝ) < ((k : ℝ) + 1) := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := a) hk ha
  have hlhs : (∫ t in Ioi (0:ℝ), t ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * t)))
      = ∫ s in Ioi (0 : ℝ), s ^ k * Real.exp (-(a * s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [show ((k : ℝ) + 1) - 1 = (k : ℝ) by ring, Real.rpow_natCast]
  rw [hlhs] at h
  rw [h, Real.Gamma_nat_eq_factorial, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  rw [div_pow, one_pow]
  field_simp

-- no-dlmf: integrability of the complex Laplace moment integrand; proof
-- infrastructure, no DLMF identity number
/-- Integrability of `sᵏ e^{-c s}` on `(0,∞)` for complex `c` with `Re c > 0`. -/
private theorem integrableOn_pow_mul_cexp {c : ℂ} (hc : 0 < c.re) (k : ℕ) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ k * Complex.exp (-(c * (s : ℂ)))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_pow_mul_rexp hc k) ?_ ?_
  · exact (Complex.continuous_ofReal.pow k).aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      Complex.norm_exp]
    have : (-(c * (s : ℂ))).re = -(c.re * s) := by
      simp [Complex.mul_re]
    rw [this]

-- no-dlmf: integrability of the rotated Gaussian–Laplace integrand `e^{-cs}e^{-bs²}`
-- (dominated by `e^{-(Re c)s}` since `Re b ≥ 0`); proof infrastructure, no DLMF
-- identity number
/-- Integrability on `(0,∞)` of `e^{-c s}·e^{-b s²}` for `Re c > 0`, `Re b ≥ 0`. -/
private theorem integrableOn_gaussLaplace {c b : ℂ} (hc : 0 < c.re) (hb : 0 ≤ b.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2))
      (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_pow_mul_rexp hc 0) ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp, pow_zero, one_mul]
    have h1 : (-(c * (s : ℂ))).re = -(c.re * s) := by simp [Complex.mul_re]
    have h2 : (-b * (s : ℂ) ^ 2).re = -(b.re * s ^ 2) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    rw [h1, h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg s]

-- no-dlmf: rotated-contour Laplace representation of `erfc`, obtained by specializing
-- the (already proven) DLMF 7.7.3 Gaussian integral `gaussLin_integral_eq_cerfc` to the
-- Gaussian rate `a = e^{2iθ}`; proof infrastructure for 7.12.1, no DLMF identity number
/-- **Rotated Laplace representation of `erfc`.**  For every rotation angle
`|θ| < π/4`, with `ω = e^{iθ}`,
`√π · e^{z²} · erfc z = 2ω ∫_{(0,∞)} e^{-2zω s} e^{-ω² s²} ds`.

This is the `t = z + ω s` form of `erfc z = (2/√π)∫_z^∞ e^{-t²} dt` on the *rotated*
ray `arg u = θ`; the value is independent of `θ` (the contour rotation is already
encoded in DLMF 7.7.3, valid for every Gaussian rate with positive real part).  It is
the rotation that reaches the sector `|ph z| ≤ 3π/4 - δ`: on the unrotated ray
(`θ = 0`) the integrand is only controllable for `Re z > 0`. -/
private theorem cerfc_rotated_rep (z : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 4) :
    (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
      = 2 * Complex.exp ((θ : ℂ) * Complex.I) *
          ∫ s in Ioi (0 : ℝ),
            Complex.exp (-((2 * (z * Complex.exp ((θ : ℂ) * Complex.I))) * (s : ℂ)))
              * Complex.exp (-(Complex.exp ((θ : ℂ) * Complex.I) ^ 2) * (s : ℂ) ^ 2) := by
  obtain ⟨hθ1, hθ2⟩ := abs_lt.mp hθ
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hωne : ω ≠ 0 := Complex.exp_ne_zero _
  have him : (((2 * θ : ℝ) : ℂ) * Complex.I).im = 2 * θ := by
    simp [Complex.mul_im]
  have hω2 : ω ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hωdef, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have ha : 0 < (ω ^ 2).re := by
    rw [hω2, Complex.exp_ofReal_mul_I_re]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hπ : 0 < Real.pi := Real.pi_pos
      linarith
    · linarith
  have hcpow : (ω ^ 2) ^ (-(1 : ℂ) / 2) = ω⁻¹ := by
    rw [hω2, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
    rw [Complex.log_exp (by rw [him]; linarith) (by rw [him]; linarith)]
    rw [hωdef, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hg := gaussLin_integral_eq_cerfc (a := ω ^ 2) (z := Complex.I * (z * ω)) ha
  rw [hcpow] at hg
  -- identify the two exponential factors on the right of `hg`
  have hexp : -(Complex.I * (z * ω)) ^ 2 / ω ^ 2 = z ^ 2 := by
    have : (Complex.I * (z * ω)) ^ 2 = -(z ^ 2 * ω ^ 2) := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [this]
    field_simp
  have harg : -Complex.I * (Complex.I * (z * ω)) * ω⁻¹ = z := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hexp, harg] at hg
  -- rewrite the integrand into product form
  have hint : (∫ t in Ioi (0 : ℝ),
        Complex.exp (-(ω ^ 2) * (t : ℂ) ^ 2 + 2 * Complex.I * (Complex.I * (z * ω)) * (t : ℂ)))
      = ∫ s in Ioi (0 : ℝ), Complex.exp (-((2 * (z * ω)) * (s : ℂ)))
          * Complex.exp (-(ω ^ 2) * (s : ℂ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [← Complex.exp_add]
    congr 1
    have : 2 * Complex.I * (Complex.I * (z * ω)) * (s : ℂ) = -((2 * (z * ω)) * (s : ℂ)) := by
      rw [show (2:ℂ) * Complex.I * (Complex.I * (z * ω)) * (s:ℂ)
            = (Complex.I * Complex.I) * (2 * (z * ω) * (s:ℂ)) by ring, Complex.I_mul_I]
      ring
    rw [this]
    ring
  rw [hint] at hg
  rw [hg]
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  field_simp

-- no-dlmf: the uniform sector remainder estimate behind DLMF 7.12.1 (reusable
-- infrastructure, not itself a numbered-equation surface); the tagged surfaces are
-- `erfc_7_12_1_complex` below and `erfc_7_12_1_complex_series` in `ErfcSeries.lean`
/-- **Uniform Poincaré remainder bound for `erfc` in the sector `|ph z| ≤ 3π/4 - δ`.**
For every truncation order `n`,
`‖√π e^{z²} erfc z - Σ_{j<n} (-1)ʲ (2j)!/(4ʲ j!) z^{-(2j+1)}‖ ≤ 2·(2n)!/(2 sin(2δ/3)‖z‖)^{2n+1}`.

The proof rotates the Laplace ray by `θ = -(ph z)/3` (`cerfc_rotated_rep`), which puts
both `Re(z e^{iθ}) ≥ sin(2δ/3)·|z|` and `Re(e^{2iθ}) > 0`, expands the Gaussian factor
`e^{-ω²s²}` to order `n` with the uniform half-plane remainder bound
`norm_cexp_sub_taylor_le`, and integrates the monomials against `e^{-2ω z s}` with the
Laplace moment `∫₀^∞ sᵏ e^{-cs} ds = k!/c^{k+1}`.  The coefficient
`(2j)!/(4ʲ j!) = (½)_j` is the `ascPochhammer` value of DLMF 7.12.1. -/
theorem cerfc_poincare_bound {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * Real.pi / 4)
    {z : ℂ} (hz : z ≠ 0) (hsec : |Complex.arg z| ≤ 3 * Real.pi / 4 - δ) (n : ℕ) :
    ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
        - ∑ j ∈ Finset.range n, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1)‖
      ≤ 2 * (Nat.factorial (2 * n) : ℝ) / (2 * (Real.sin (2 * δ / 3) * ‖z‖)) ^ (2 * n + 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set φ : ℝ := Complex.arg z with hφdef
  set θ : ℝ := -φ / 3 with hθdef
  have hθabs : |θ| ≤ Real.pi / 4 - δ / 3 := by
    rw [hθdef, abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith [hsec]
  have hθ : |θ| < Real.pi / 4 := by linarith
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  set w : ℂ := z * ω with hwdef
  have hωnorm : ‖ω‖ = 1 := by rw [hωdef]; exact Complex.norm_exp_ofReal_mul_I θ
  have hωne : ω ≠ 0 := by
    intro h; rw [h] at hωnorm; simp at hωnorm
  -- the key sector estimate: `Re w ≥ sin(2δ/3)·‖z‖`
  have hκ : 0 < Real.sin (2 * δ / 3) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hwre : Real.sin (2 * δ / 3) * ‖z‖ ≤ w.re := by
    have hzrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    have hwform : w = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((2 * φ / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hwdef, hωdef]
      nth_rewrite 1 [hzrep]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast [hθdef]
      ring
    have hre : w.re = ‖z‖ * Real.cos (2 * φ / 3) := by
      rw [hwform, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rw [hre]
    have habs : |2 * φ / 3| ≤ Real.pi / 2 - 2 * δ / 3 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3), abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
      nlinarith [hsec]
    have hcos : Real.cos (Real.pi / 2 - 2 * δ / 3) ≤ Real.cos (2 * φ / 3) := by
      rw [← Real.cos_abs (2 * φ / 3)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
    rw [Real.cos_pi_div_two_sub] at hcos
    nlinarith [hcos, hzn.le]
  have hwpos : 0 < w.re := lt_of_lt_of_le (by positivity) hwre
  -- abbreviations for the rotated Laplace data
  set c : ℂ := 2 * w with hcdef
  set b : ℂ := ω ^ 2 with hbdef
  have hcre_eq : c.re = 2 * w.re := by
    rw [hcdef]
    simp [Complex.mul_re]
  have hcre : 0 < c.re := by rw [hcre_eq]; linarith
  have hbnorm : ‖b‖ = 1 := by rw [hbdef, norm_pow, hωnorm, one_pow]
  have hbre : 0 ≤ b.re := by
    rw [hbdef, hωdef]
    have hω2 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 2
        = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hω2, Complex.exp_ofReal_mul_I_re]
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have := abs_le.mp hθabs
      linarith [this.1]
    · have := abs_le.mp hθabs
      linarith [this.2]
  -- the pointwise Taylor split of the integrand
  set rem : ℝ → ℂ := fun s => Complex.exp (-(c * (s : ℂ)))
    * (Complex.exp (-b * (s : ℂ) ^ 2)
      - ∑ j ∈ Finset.range n, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)) with hremdef
  set trm : ℕ → ℝ → ℂ := fun j s => ((-b) ^ j / (Nat.factorial j : ℂ))
    * ((s : ℂ) ^ (2 * j) * Complex.exp (-(c * (s : ℂ)))) with htrmdef
  have hpt : ∀ s : ℝ, Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)
      = (∑ j ∈ Finset.range n, trm j s) + rem s := by
    intro s
    have hsum : (∑ j ∈ Finset.range n, trm j s)
        = Complex.exp (-(c * (s : ℂ)))
          * ∑ j ∈ Finset.range n, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htrmdef, mul_pow, ← pow_mul]
      ring
    rw [hsum, hremdef]
    ring
  -- integrability
  have hint_tot : IntegrableOn
      (fun s : ℝ => Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2))
      (Ioi (0 : ℝ)) := integrableOn_gaussLaplace hcre hbre
  have hint_trm : ∀ j : ℕ, IntegrableOn (trm j) (Ioi (0 : ℝ)) := fun j =>
    (integrableOn_pow_mul_cexp hcre (2 * j)).const_mul _
  have hint_sum : IntegrableOn (fun s : ℝ => ∑ j ∈ Finset.range n, trm j s) (Ioi (0 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => hint_trm j)
  have hint_rem : IntegrableOn rem (Ioi (0 : ℝ)) := by
    have h := hint_tot.sub hint_sum
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    have := hpt s
    simp only [Pi.sub_apply]
    linear_combination this
  -- the truncated expansion of the rotated integral
  have hW : (∫ s in Ioi (0 : ℝ),
        Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2))
      = (∑ j ∈ Finset.range n,
          ((-b) ^ j / (Nat.factorial j : ℂ)) * ((Nat.factorial (2 * j) : ℂ) / c ^ (2 * j + 1)))
        + ∫ s in Ioi (0 : ℝ), rem s := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpt s)]
    rw [integral_add hint_sum hint_rem]
    congr 1
    rw [integral_finsetSum _ (fun j _ => hint_trm j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [htrmdef]
    simp only
    rw [MeasureTheory.integral_const_mul,
      FLMF.Methods.LaplaceTransform.scaled_gamma_pow_two_sided (2 * j) hcre]
  -- the remainder bound
  have hrem_bound : ‖∫ s in Ioi (0 : ℝ), rem s‖
      ≤ (Nat.factorial (2 * n) : ℝ) / c.re ^ (2 * n + 1) := by
    calc ‖∫ s in Ioi (0 : ℝ), rem s‖ ≤ ∫ s in Ioi (0 : ℝ), ‖rem s‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioi (0 : ℝ), s ^ (2 * n) * Real.exp (-(c.re * s)) := by
          refine setIntegral_mono_on hint_rem.norm
            (integrableOn_pow_mul_rexp hcre (2 * n)) measurableSet_Ioi (fun s hs => ?_)
          have hs0 : (0:ℝ) < s := hs
          have hxre : (-b * (s : ℂ) ^ 2).re ≤ 0 := by
            have h2 : (-b * (s : ℂ) ^ 2).re = -(b.re * s ^ 2) := by
              simp [pow_two, Complex.mul_re, Complex.mul_im]
            rw [h2]
            nlinarith [sq_nonneg s]
          have htay := norm_cexp_sub_taylor_le n hxre
          have hxnorm : ‖-b * (s : ℂ) ^ 2‖ = s ^ 2 := by
            rw [norm_mul, norm_neg, hbnorm, one_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hs0]
          rw [hxnorm] at htay
          rw [hremdef]
          simp only
          rw [norm_mul, Complex.norm_exp]
          have hce : (-(c * (s : ℂ))).re = -(c.re * s) := by simp [Complex.mul_re]
          rw [hce]
          have h1 : ‖Complex.exp (-b * (s : ℂ) ^ 2)
              - ∑ j ∈ Finset.range n, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)‖
              ≤ s ^ (2 * n) := by
            rw [pow_mul]
            exact htay
          calc Real.exp (-(c.re * s)) * ‖Complex.exp (-b * (s : ℂ) ^ 2)
                - ∑ j ∈ Finset.range n, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)‖
              ≤ Real.exp (-(c.re * s)) * s ^ (2 * n) :=
                mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
            _ = s ^ (2 * n) * Real.exp (-(c.re * s)) := by ring
      _ = (Nat.factorial (2 * n) : ℝ) / c.re ^ (2 * n + 1) :=
          integral_pow_mul_rexp hcre (2 * n)
  -- assembling
  have hrep := cerfc_rotated_rep z hθ
  rw [← hωdef, ← hwdef] at hrep
  have hkey : (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z
      - ∑ j ∈ Finset.range n, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
          / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1)
      = 2 * ω * ∫ s in Ioi (0 : ℝ), rem s := by
    rw [hrep, ← hcdef, ← hbdef, hW, mul_add, Finset.mul_sum]
    have hterms : ∀ j ∈ Finset.range n,
        2 * ω * (((-b) ^ j / (Nat.factorial j : ℂ)) * ((Nat.factorial (2 * j) : ℂ) / c ^ (2 * j + 1)))
          = (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
              / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1) := by
      intro j _
      have hbj : (-b) ^ j = (-1 : ℂ) ^ j * ω ^ (2 * j) := by
        rw [hbdef, neg_pow, ← pow_mul]
      have h2p : (2 : ℂ) ^ (2 * j + 1) = 2 * (4 : ℂ) ^ j := by
        rw [pow_succ, pow_mul, show ((2:ℂ) ^ 2) = 4 by norm_num]
        ring
      have hcj : c ^ (2 * j + 1) = 2 * (4 : ℂ) ^ j * (z ^ (2 * j + 1) * ω ^ (2 * j + 1)) := by
        rw [hcdef, hwdef, mul_pow, mul_pow, h2p]
      have hfj : ((Nat.factorial j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      have hωj : ω ^ (2 * j + 1) = ω ^ (2 * j) * ω := by rw [pow_succ]
      rw [hbj, hcj, hωj]
      have hωj2 : (ω : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ hωne
      field_simp
    rw [Finset.sum_congr rfl hterms]
    ring
  rw [hkey, norm_mul, norm_mul, hωnorm]
  simp only [Complex.norm_ofNat, mul_one]
  have hfinal : (2 : ℝ) * ‖∫ s in Ioi (0 : ℝ), rem s‖
      ≤ 2 * ((Nat.factorial (2 * n) : ℝ) / c.re ^ (2 * n + 1)) :=
    mul_le_mul_of_nonneg_left hrem_bound (by norm_num)
  refine hfinal.trans ?_
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  rw [hcre_eq]
  linarith [hwre]

-- no-dlmf: leading-term (`N = 0`)-only restriction of DLMF 7.12.1 (whose
-- stated content is the full Poincaré asymptotic series, valid for every
-- truncation order `N`); the faithful full-strength surface is
-- `erfc_7_12_1_complex_series` in `ErfcSeries.lean` (which specializes to this
-- theorem at `N = 0`, per its own docstring).
/-- **DLMF 7.12.1 (leading term).**  For complex `z` in the closed sector
`|ph z| ≤ 3π/4 − δ` (any `δ ∈ (0, 3π/4)`), `erfc(z) ~ e^{-z²}/(z √π)` as
`z → ∞` in that sector, in the precise sense that
`z · √π · e^{z²} · erfc(z) → 1` along the filter "infinity in the sector"
(`comap norm atTop ⊓ principal {sector}`, the standard DLMF-sector-at-infinity
idiom also used in `Frameworks.Hypergeometric.Ch15AsymptoticApproximations`).
This specializes to the real surface `erfc_asymptotic` on `ph z = 0`. -/
theorem erfc_7_12_1_complex (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 3 * Real.pi / 4) :
    Tendsto (fun z : ℂ => z * (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z)
      (comap norm atTop ⊓
        principal {z : ℂ | |Complex.arg z| ≤ 3 * Real.pi / 4 - δ})
      (𝓝 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set κ : ℝ := Real.sin (2 * δ / 3) with hκdef
  have hκ : 0 < κ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set F : Filter ℂ := comap norm atTop ⊓
    principal {z : ℂ | |Complex.arg z| ≤ 3 * Real.pi / 4 - δ} with hFdef
  set C : ℝ := 2 * (Nat.factorial (2 * 1) : ℝ) / (2 * κ) ^ (2 * 1 + 1) with hCdef
  have hev : ∀ᶠ z : ℂ in F,
      ‖z * (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z - 1‖ ≤ C * (‖z‖ ^ 2)⁻¹ := by
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
    have hb := cerfc_poincare_bound hδ hδ' hz hz2 1
    have hcoeff : (∑ j ∈ Finset.range 1, (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
        / ((4:ℂ) ^ j * (Nat.factorial j : ℂ)) / z ^ (2 * j + 1)) = z⁻¹ := by
      simp
    rw [hcoeff, ← hκdef] at hb
    have heq : z * (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z - 1
        = z * ((Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z - z⁻¹) := by
      field_simp
    rw [heq, norm_mul]
    calc ‖z‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z - z⁻¹‖
        ≤ ‖z‖ * (2 * (Nat.factorial (2 * 1) : ℝ) / (2 * (κ * ‖z‖)) ^ (2 * 1 + 1)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg z)
      _ = C * (‖z‖ ^ 2)⁻¹ := by
          rw [hCdef, mul_pow]
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
  have h0 : Tendsto
      (fun z : ℂ => z * (Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z - 1) F (𝓝 0) :=
    squeeze_zero_norm' hev hg
  have hfin := h0.add (tendsto_const_nhds (x := (1:ℂ)) (f := F))
  simpa using hfin

end FLMF.Error
