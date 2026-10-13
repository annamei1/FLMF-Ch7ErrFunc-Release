import FLMF.Methods.LaplaceTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Sector-uniform Poincaré remainder bounds for Laplace-type integrals

DLMF Chapter 2 (§2.3, §2.4) supplies the *method* behind every "Poincaré expansion,
valid as `z → ∞` in `|ph z| ≤ ρ − δ`" display in the handbook: a Laplace-type integral
along a ray whose direction is rotated against `ph z`, together with a *uniform* Taylor
remainder for the non-exponential factor.  This module collects the reusable pieces.

Main results:

* `FLMF.Methods.SectorPoincare.norm_cexp_sub_taylor_le` — the **uniform** Taylor remainder
  `‖e^x − Σ_{i<n} xⁱ/i!‖ ≤ ‖x‖ⁿ` on the closed left half-plane `Re x ≤ 0` (unlike the
  usual `e^{‖x‖}`-weighted estimate, this one is bounded on the whole half-plane, which is
  exactly what makes a sector estimate possible).
* `FLMF.Methods.SectorPoincare.integral_pow_mul_rexp` — the real Laplace moment
  `∫₀^∞ sᵏ e^{−a s} ds = k!/a^{k+1}`.
* `FLMF.Methods.SectorPoincare.norm_gaussLaplace_moment_sub_taylor_le` — the **Watson-type
  sector lemma**: for `Re c > 0`, `Re b ≥ 0`, `‖b‖ ≤ 1`,
  `‖∫₀^∞ sᵏ e^{−cs} e^{−b s²} ds − Σ_{j<N} ((−b)ʲ/j!)·(k+2j)!/c^{k+2j+1}‖
      ≤ (k+2N)!/(Re c)^{k+2N+1}`,
  i.e. the Poincaré expansion of a Gaussian-damped Laplace moment with an explicit
  remainder bound depending on `c` only through `Re c`.
* `FLMF.Methods.SectorPoincare.sector_rotation_bounds` — the geometric input: for
  `|ph z| ≤ 3π/4 − δ`, the rotation `θ = −(ph z)/3` satisfies `|θ| ≤ π/4 − δ/3`,
  `Re(z e^{iθ}) ≥ sin(2δ/3)·‖z‖ > 0` and `Re(e^{2iθ}) ≥ 0`; combining it with the Watson
  lemma turns any `∫₀^∞ sᵏ e^{−2 z e^{iθ} s} e^{−e^{2iθ} s²} ds` representation into a
  sector-uniform power bound.

These are the ingredients of `FLMF.Error.cerfc_poincare_bound` (DLMF 7.12.1), isolated so
that the *general-order* repeated-`erfc` expansion DLMF 7.18.14 and the Fresnel-auxiliary
expansions DLMF 7.12.2/7.12.3 can reuse them verbatim.
-/

namespace FLMF.Methods.SectorPoincare

open MeasureTheory Real Filter Topology Set

/-! ### The uniform half-plane Taylor remainder -/

-- no-dlmf: reusable analytic estimate (DLMF §2.3 method infrastructure), no numbered display
/-- **Taylor remainder of `exp` on the closed left half-plane.**  If `Re x ≤ 0` then
`‖e^x − Σ_{i<n} xⁱ/i!‖ ≤ ‖x‖ⁿ`.  (The mean-value estimate along the segment `[0,x]`,
which stays in the half-plane; the bound is *uniform*, unlike the usual
`e^{‖x‖}`-weighted one, and this uniformity is what makes sector estimates work.) -/
theorem norm_cexp_sub_taylor_le :
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
          ≤ ‖x‖ * ‖(t : ℂ) * x‖ ^ n := mul_le_mul_of_nonneg_left hIH (norm_nonneg _)
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

/-! ### Real and complex Laplace moments -/

-- no-dlmf: integrability of the real Laplace-moment integrand; method infrastructure
/-- Integrability of `sᵏ e^{−a s}` on `(0,∞)` for real `a > 0`. -/
theorem integrableOn_pow_mul_rexp {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(a * s))) (Ioi (0 : ℝ)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine IntegrableOn.congr_fun
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := a) hk le_rfl ha)
    (fun s _ => ?_) measurableSet_Ioi
  rw [Real.rpow_one, Real.rpow_natCast]
  ring_nf

-- no-dlmf: the real Laplace moment (Γ-integral instance); method infrastructure
/-- The real Laplace moment `∫₀^∞ sᵏ e^{−a s} ds = k!/a^{k+1}`, `a > 0`. -/
theorem integral_pow_mul_rexp {a : ℝ} (ha : 0 < a) (k : ℕ) :
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

-- no-dlmf: integrability of the complex Laplace-moment integrand; method infrastructure
/-- Integrability of `sᵏ e^{−c s}` on `(0,∞)` for complex `c` with `Re c > 0`. -/
theorem integrableOn_pow_mul_cexp {c : ℂ} (hc : 0 < c.re) (k : ℕ) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ k * Complex.exp (-(c * (s : ℂ)))) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_pow_mul_rexp hc k) ?_ ?_
  · exact (Complex.continuous_ofReal.pow k).aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      Complex.norm_exp]
    have : (-(c * (s : ℂ))).re = -(c.re * s) := by simp [Complex.mul_re]
    rw [this]

-- no-dlmf: integrability of the Gaussian-damped Laplace integrand; method infrastructure
/-- Integrability on `(0,∞)` of `sᵏ e^{−c s}·e^{−b s²}` for `Re c > 0`, `Re b ≥ 0`
(the Gaussian factor has modulus `≤ 1` on the ray, so the Laplace factor already
dominates). -/
theorem integrableOn_pow_mul_gaussLaplace {c b : ℂ} (hc : 0 < c.re) (hb : 0 ≤ b.re) (k : ℕ) :
    IntegrableOn (fun s : ℝ =>
        (s : ℂ) ^ k * (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)))
      (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (integrableOn_pow_mul_rexp hc k) ?_ ?_
  · exact (Complex.continuous_ofReal.pow k).aestronglyMeasurable.mul
      (((Complex.continuous_exp.comp (by fun_prop)).mul
        (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0:ℝ) < s := hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (-(c * (s : ℂ))).re = -(c.re * s) := by simp [Complex.mul_re]
    have h2 : (-b * (s : ℂ) ^ 2).re = -(b.re * s ^ 2) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    rw [h1, h2, ← Real.exp_add]
    have : Real.exp (-(c.re * s) + -(b.re * s ^ 2)) ≤ Real.exp (-(c.re * s)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg s]
    exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### The Watson-type sector lemma -/

-- no-dlmf: the reusable Poincaré-with-remainder estimate for a Gaussian-damped
-- Laplace moment (DLMF §2.3 method); no numbered display
/-- **Poincaré expansion of a Gaussian-damped Laplace moment, with a remainder bound
depending on the rate only through its real part.**  For `Re c > 0`, `Re b ≥ 0` and
`‖b‖ ≤ 1`,
`‖∫₀^∞ sᵏ e^{−cs} e^{−b s²} ds − Σ_{j<N} ((−b)ʲ/j!)·(k+2j)!/c^{k+2j+1}‖
    ≤ (k+2N)!/(Re c)^{k+2N+1}`.

The proof expands `e^{−b s²}` to order `N` with the *uniform* half-plane Taylor bound
`norm_cexp_sub_taylor_le` (legitimate because `Re(−b s²) ≤ 0` on the ray), integrates the
monomials against `e^{−cs}` with the complex Laplace moment
`∫₀^∞ sᵐ e^{−cs} ds = m!/c^{m+1}`, and bounds the remainder integral by the real Laplace
moment at rate `Re c`.  Because the final bound involves `c` only through `Re c`, feeding
it a *rotated* rate `c = 2 z e^{iθ}` with `Re c ≥ 2 sin(2δ/3)‖z‖` yields a bound uniform
on the sector `|ph z| ≤ 3π/4 − δ`. -/
theorem norm_gaussLaplace_moment_sub_taylor_le {c b : ℂ} (hc : 0 < c.re) (hb : 0 ≤ b.re)
    (hbn : ‖b‖ ≤ 1) (k N : ℕ) :
    ‖(∫ s in Ioi (0 : ℝ),
          (s : ℂ) ^ k * (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)))
        - ∑ j ∈ Finset.range N, ((-b) ^ j / (Nat.factorial j : ℂ))
            * ((Nat.factorial (k + 2 * j) : ℂ) / c ^ (k + 2 * j + 1))‖
      ≤ (Nat.factorial (k + 2 * N) : ℝ) / c.re ^ (k + 2 * N + 1) := by
  -- pointwise Taylor split
  set rem : ℝ → ℂ := fun s => (s : ℂ) ^ k * Complex.exp (-(c * (s : ℂ)))
    * (Complex.exp (-b * (s : ℂ) ^ 2)
      - ∑ j ∈ Finset.range N, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)) with hremdef
  set trm : ℕ → ℝ → ℂ := fun j s => ((-b) ^ j / (Nat.factorial j : ℂ))
    * ((s : ℂ) ^ (k + 2 * j) * Complex.exp (-(c * (s : ℂ)))) with htrmdef
  have hpt : ∀ s : ℝ,
      (s : ℂ) ^ k * (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2))
      = (∑ j ∈ Finset.range N, trm j s) + rem s := by
    intro s
    have hsum : (∑ j ∈ Finset.range N, trm j s)
        = (s : ℂ) ^ k * Complex.exp (-(c * (s : ℂ)))
          * ∑ j ∈ Finset.range N, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htrmdef]
      simp only
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    rw [hsum, hremdef]
    ring
  -- integrability
  have hint_tot : IntegrableOn
      (fun s : ℝ =>
        (s : ℂ) ^ k * (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)))
      (Ioi (0 : ℝ)) := integrableOn_pow_mul_gaussLaplace hc hb k
  have hint_trm : ∀ j : ℕ, IntegrableOn (trm j) (Ioi (0 : ℝ)) := fun j =>
    (integrableOn_pow_mul_cexp hc (k + 2 * j)).const_mul _
  have hint_sum : IntegrableOn (fun s : ℝ => ∑ j ∈ Finset.range N, trm j s) (Ioi (0 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => hint_trm j)
  have hint_rem : IntegrableOn rem (Ioi (0 : ℝ)) := by
    have h := hint_tot.sub hint_sum
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    have := hpt s
    simp only [Pi.sub_apply]
    linear_combination this
  -- the truncated expansion
  have hW : (∫ s in Ioi (0 : ℝ),
        (s : ℂ) ^ k * (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)))
      = (∑ j ∈ Finset.range N, ((-b) ^ j / (Nat.factorial j : ℂ))
          * ((Nat.factorial (k + 2 * j) : ℂ) / c ^ (k + 2 * j + 1)))
        + ∫ s in Ioi (0 : ℝ), rem s := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpt s)]
    rw [integral_add hint_sum hint_rem]
    congr 1
    rw [integral_finsetSum _ (fun j _ => hint_trm j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [htrmdef]
    simp only
    rw [MeasureTheory.integral_const_mul,
      FLMF.Methods.LaplaceTransform.scaled_gamma_pow_two_sided (k + 2 * j) hc]
  -- the remainder bound
  have hrem_bound : ‖∫ s in Ioi (0 : ℝ), rem s‖
      ≤ (Nat.factorial (k + 2 * N) : ℝ) / c.re ^ (k + 2 * N + 1) := by
    calc ‖∫ s in Ioi (0 : ℝ), rem s‖ ≤ ∫ s in Ioi (0 : ℝ), ‖rem s‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioi (0 : ℝ), s ^ (k + 2 * N) * Real.exp (-(c.re * s)) := by
          refine setIntegral_mono_on hint_rem.norm
            (integrableOn_pow_mul_rexp hc (k + 2 * N)) measurableSet_Ioi (fun s hs => ?_)
          have hs0 : (0:ℝ) < s := hs
          have hxre : (-b * (s : ℂ) ^ 2).re ≤ 0 := by
            have h2 : (-b * (s : ℂ) ^ 2).re = -(b.re * s ^ 2) := by
              simp [pow_two, Complex.mul_re, Complex.mul_im]
            rw [h2]
            nlinarith [sq_nonneg s]
          have htay := norm_cexp_sub_taylor_le N hxre
          have hxnorm : ‖-b * (s : ℂ) ^ 2‖ ≤ s ^ 2 := by
            rw [norm_mul, norm_neg, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hs0]
            calc ‖b‖ * s ^ 2 ≤ 1 * s ^ 2 :=
                  mul_le_mul_of_nonneg_right hbn (by positivity)
              _ = s ^ 2 := one_mul _
          have h1 : ‖Complex.exp (-b * (s : ℂ) ^ 2)
              - ∑ j ∈ Finset.range N, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)‖
              ≤ s ^ (2 * N) := by
            refine htay.trans ?_
            rw [pow_mul]
            exact pow_le_pow_left₀ (norm_nonneg _) hxnorm N
          rw [hremdef]
          simp only
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs0, Complex.norm_exp]
          have hce : (-(c * (s : ℂ))).re = -(c.re * s) := by simp [Complex.mul_re]
          rw [hce]
          calc s ^ k * Real.exp (-(c.re * s)) * ‖Complex.exp (-b * (s : ℂ) ^ 2)
                - ∑ j ∈ Finset.range N, (-b * (s : ℂ) ^ 2) ^ j / (Nat.factorial j : ℂ)‖
              ≤ s ^ k * Real.exp (-(c.re * s)) * s ^ (2 * N) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = s ^ (k + 2 * N) * Real.exp (-(c.re * s)) := by
                rw [pow_add]; ring
      _ = (Nat.factorial (k + 2 * N) : ℝ) / c.re ^ (k + 2 * N + 1) :=
          integral_pow_mul_rexp hc (k + 2 * N)
  rw [hW]
  simpa using hrem_bound

/-! ### The sector rotation -/

-- no-dlmf: geometric input for sector estimates (DLMF §2.3 method); no numbered display
/-- **The `θ = −(ph z)/3` rotation for the sector `|ph z| ≤ 3π/4 − δ`.**  With
`ω = e^{iθ}` this gives simultaneously

* `|θ| ≤ π/4 − δ/3` (in particular `|θ| < π/4`, so the rotated ray still lies in the
  half-plane where the Gaussian factor `e^{−ω² s²}` is non-increasing), and
* `Re(z ω) ≥ sin(2δ/3)·‖z‖ > 0` (so the Laplace factor decays at a rate proportional to
  `‖z‖`, uniformly on the sector), and
* `Re(ω²) ≥ 0`.

The constant `2δ/3` is exactly what is left of the sector opening after the rotation:
`ph(zω) = (2/3) ph z` has modulus `≤ π/2 − 2δ/3`. -/
theorem sector_rotation_bounds {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * Real.pi / 4)
    {z : ℂ} (hz : z ≠ 0) (hsec : |Complex.arg z| ≤ 3 * Real.pi / 4 - δ) :
    |(-Complex.arg z / 3 : ℝ)| ≤ Real.pi / 4 - δ / 3 ∧
      Real.sin (2 * δ / 3) * ‖z‖
        ≤ (z * Complex.exp (((-Complex.arg z / 3 : ℝ) : ℂ) * Complex.I)).re ∧
      0 ≤ ((Complex.exp (((-Complex.arg z / 3 : ℝ) : ℂ) * Complex.I)) ^ 2).re := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set φ : ℝ := Complex.arg z with hφdef
  set θ : ℝ := -φ / 3 with hθdef
  have hθabs : |θ| ≤ Real.pi / 4 - δ / 3 := by
    rw [hθdef, abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith [hsec]
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  refine ⟨hθabs, ?_, ?_⟩
  · -- `Re (z ω) ≥ sin(2δ/3) ‖z‖`
    have hzrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    have hwform : z * ω = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((2 * φ / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hωdef]
      nth_rewrite 1 [hzrep]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast [hθdef]
      ring
    have hre : (z * ω).re = ‖z‖ * Real.cos (2 * φ / 3) := by
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
  · -- `Re (ω²) ≥ 0`
    rw [hωdef]
    have hω2 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 2
        = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hω2, Complex.exp_ofReal_mul_I_re]
    apply Real.cos_nonneg_of_mem_Icc
    have h := abs_le.mp hθabs
    constructor
    · linarith [h.1]
    · linarith [h.2]

end FLMF.Methods.SectorPoincare
