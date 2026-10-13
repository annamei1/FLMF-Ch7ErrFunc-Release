import FLMF.Frameworks.Hypergeometric.Tricomi
import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Ch7IntegralReps
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The complementary error function as a Tricomi-`U` instance (bridge — DLMF 7.11.2)

* `erfc_eq_tricomiU` — `erfc(x) = (x/√π) · e^{−x²} · U(1; 3/2; x²)` for `x > 0`.

The companion of `FLMF.Error.erf_eq_kummerM` (erf via `₁F₁`). Writing
`erfc(x) = (2/√π) ∫ₓ^∞ e^{−s²} ds` and substituting `s = x√(1+t)` sends the
Gaussian tail onto the `U`-integral
`U(1;3/2;x²) = ∫₀^∞ e^{−x²t}(1+t)^{−1/2} dt`: the Jacobian `x/(2√(1+t))`
supplies the `(1+t)^{−1/2}` and the `x/2`, and `e^{−s²} = e^{−x²} e^{−x²t}`.
-/

noncomputable section

open MeasureTheory Real Set
open FLMF.Hypergeometric

namespace FLMF.Error

-- no-dlmf: was mis-tagged E-7.11.2 — content is the second limb of DLMF 7.11.5 (surfaced at `erf_7_11_5`); the true 7.11.2 is surfaced at `erf_7_11_2` (Ch7RelationsOther.lean)
/-- **`erfc` as a Tricomi `U`** (DLMF 7.11.2):
`erfc(x) = (x/√π) · e^{−x²} · U(1; 3/2; x²)` for `x > 0`.

-/
theorem erfc_eq_tricomiU {x : ℝ} (hx : 0 < x) :
    erfc x = x / Real.sqrt Real.pi * Real.exp (-x ^ 2) * tricomiU 1 (3 / 2) (x ^ 2) := by
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
  -- change of variables `s = x√(1+t)`
  set φ : ℝ → ℝ := fun t => x * Real.sqrt (1 + t) with hφ
  have himg : φ '' Ioi 0 = Ioi x := by
    ext s
    simp only [hφ, mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h1 : 1 < Real.sqrt (1 + t) := by
        have : Real.sqrt 1 < Real.sqrt (1 + t) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith)
        simpa using this
      nlinarith
    · intro hs
      refine ⟨(s / x) ^ 2 - 1, by
        have : 1 < s / x := (one_lt_div hx).mpr hs
        nlinarith, ?_⟩
      rw [show (1 : ℝ) + ((s / x) ^ 2 - 1) = (s / x) ^ 2 by ring,
        Real.sqrt_sq (div_nonneg (lt_trans hx hs).le hx.le), mul_div_cancel₀ _ hx.ne']
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (x / (2 * Real.sqrt (1 + t))) (Ioi 0) t := by
    intro t ht
    have h1t : (1 : ℝ) + t ≠ 0 := by have := mem_Ioi.mp ht; linarith
    have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t)) (1 / (2 * Real.sqrt (1 + t))) t := by
      have := (Real.hasDerivAt_sqrt h1t).comp t ((hasDerivAt_const t 1).add (hasDerivAt_id t))
      simpa using this
    rw [show x / (2 * Real.sqrt (1 + t)) = x * (1 / (2 * Real.sqrt (1 + t))) by ring]
    exact (hsqrt.const_mul x).hasDerivWithinAt
  have hinj : InjOn φ (Ioi 0) := by
    intro a ha b hb hab
    have h1a : (0 : ℝ) ≤ 1 + a := by have := mem_Ioi.mp ha; linarith
    have h1b : (0 : ℝ) ≤ 1 + b := by have := mem_Ioi.mp hb; linarith
    simp only [hφ, mul_right_inj' hx.ne'] at hab
    have : (1 : ℝ) + a = 1 + b := by
      have := congrArg (· ^ 2) hab
      simpa [Real.sq_sqrt, h1a, h1b] using this
    linarith
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun s => Real.exp (-s ^ 2))
  rw [himg] at hcov
  -- the transformed integrand collapses to `(x/2) e^{−x²} · (U-integrand)`
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      |x / (2 * Real.sqrt (1 + t))| • Real.exp (-φ t ^ 2)
        = x / 2 * Real.exp (-x ^ 2) * tricomiIntegrand 1 (3 / 2) (x ^ 2) t := by
    intro t ht
    have h1t : (0 : ℝ) < 1 + t := by have := mem_Ioi.mp ht; linarith
    have hsq : φ t ^ 2 = x ^ 2 * (1 + t) := by
      rw [hφ, mul_pow, Real.sq_sqrt h1t.le]
    have hroot : ((1 : ℝ) + t) ^ (-1 / 2 : ℝ) = (Real.sqrt (1 + t))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg h1t.le, ← Real.sqrt_eq_rpow]
    have hE : Real.exp (-φ t ^ 2) = Real.exp (-x ^ 2) * Real.exp (-(x ^ 2) * t) := by
      rw [← Real.exp_add]; congr 1; linear_combination -hsq
    unfold tricomiIntegrand
    rw [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero, mul_one,
      show (3 / 2 : ℝ) - 1 - 1 = -1 / 2 by ring, hroot,
      abs_of_pos (by positivity), smul_eq_mul, hE]
    field_simp
  have hInt : (∫ s in Ioi x, Real.exp (-s ^ 2))
      = x / 2 * Real.exp (-x ^ 2) * tricomiU 1 (3 / 2) (x ^ 2) := by
    rw [hcov, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      show tricomiU 1 (3 / 2) (x ^ 2)
        = ∫ t in Ioi (0 : ℝ), tricomiIntegrand 1 (3 / 2) (x ^ 2) t from by
        rw [tricomiU, Real.Gamma_one, inv_one, one_mul]]
  rw [htail, hInt]
  ring

-- no-dlmf: support lemma for `erfc_eq_tricomiU_half` — the `(a,b) = (1/2,1/2)`
-- Tricomi integral is the DLMF 7.7.1 half-line Gaussian integral, doubled
/-- The `U(1/2; 1/2; ·)` integral under the substitution `t = s²`:
`∫₀^∞ e^{−xt} t^{−1/2}(1+t)^{−1} dt = 2 ∫₀^∞ e^{−x s²}/(s²+1) ds`. -/
theorem tricomiIntegral_half_eq {x : ℝ} :
    (∫ t in Ioi (0 : ℝ), tricomiIntegrand (1 / 2) (1 / 2) x t)
      = 2 * ∫ s in Ioi (0 : ℝ), Real.exp (-x * s ^ 2) / (s ^ 2 + 1) := by
  set φ : ℝ → ℝ := fun s => s ^ 2 with hφ
  have himg : φ '' Ioi 0 = Ioi (0 : ℝ) := by
    ext u
    simp only [hφ, mem_image, mem_Ioi]
    constructor
    · rintro ⟨s, hs, rfl⟩; positivity
    · intro hu
      exact ⟨Real.sqrt u, Real.sqrt_pos.mpr hu, Real.sq_sqrt hu.le⟩
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (2 * s) (Ioi 0) s := by
    intro s _
    have h := (hasDerivAt_pow 2 s).hasDerivWithinAt (s := Ioi 0)
    simpa [hφ] using h
  have hinj : InjOn φ (Ioi 0) := by
    intro a ha b hb hab
    have ha' := mem_Ioi.mp ha
    have hb' := mem_Ioi.mp hb
    simp only [hφ] at hab
    nlinarith
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t => tricomiIntegrand (1 / 2) (1 / 2) x t)
  rw [himg] at hcov
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      |2 * s| • tricomiIntegrand (1 / 2) (1 / 2) x (φ s)
        = 2 * (Real.exp (-x * s ^ 2) / (s ^ 2 + 1)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := mem_Ioi.mp hs
    have hroot : ((s ^ 2 : ℝ)) ^ ((1 : ℝ) / 2 - 1) = s⁻¹ := by
      rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by ring, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow, Real.sqrt_sq hs0.le]
    have hden : ((1 + s ^ 2 : ℝ)) ^ ((1 : ℝ) / 2 - 1 / 2 - 1) = (1 + s ^ 2)⁻¹ := by
      rw [show (1 : ℝ) / 2 - 1 / 2 - 1 = -(1 : ℝ) by ring, Real.rpow_neg (by positivity),
        Real.rpow_one]
    unfold tricomiIntegrand
    rw [hφ]
    simp only []
    rw [hroot, hden, abs_of_pos (by positivity), smul_eq_mul]
    have h1 : (1 : ℝ) + s ^ 2 = s ^ 2 + 1 := by ring
    rw [h1]
    field_simp
  rw [hcov, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]

/-- **`erfc` as a Tricomi `U`, first form** (DLMF 7.11.5, first equality):
`erfc(z) = (1/√π) · e^{−z²} · U(1/2; 1/2; z²)` for `z > 0`.

The route: `U(1/2;1/2;z²) = (1/Γ(1/2))∫₀^∞ e^{−z²t} t^{−1/2}(1+t)^{−1} dt`
(DLMF 13.4.4, the defining integral), and the substitution `t = s²` turns that
into `(2/√π)∫₀^∞ e^{−z²s²}/(s²+1) ds` — which is exactly the DLMF 7.7.1
half-line representation `erfc z = (2/π) e^{−z²}∫₀^∞ e^{−z²s²}/(s²+1) ds`
(`erf_7_7_1`) after the `√π·√π = π` bookkeeping.  No contiguous-relation
framework is needed. -/
-- no-dlmf: chain link 7.11.5 (assembled with `erfc_eq_tricomiU` in `erf_7_11_5`,
-- `Error/Ch7RelationsOther.lean`); this is DLMF 7.11.5's *first* form,
-- `erfc(z) = (1/√π)·e^{-z²}·U(1/2;1/2;z²)`, genuinely different Tricomi
-- parameters from `erfc_eq_tricomiU`'s `U(1;3/2;·)`
theorem erfc_eq_tricomiU_half {z : ℝ} (hz : 0 < z) :
    erfc z = 1 / Real.sqrt Real.pi * Real.exp (-z ^ 2) * tricomiU (1 / 2) (1 / 2) (z ^ 2) := by
  have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hππ : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hU : tricomiU (1 / 2) (1 / 2) (z ^ 2)
      = (Real.sqrt Real.pi)⁻¹ * (2 * ∫ s in Ioi (0 : ℝ),
          Real.exp (-z ^ 2 * s ^ 2) / (s ^ 2 + 1)) := by
    rw [tricomiU, tricomiIntegral_half_eq, Real.Gamma_one_half_eq]
  have hinv : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = (Real.pi)⁻¹ := by
    rw [← mul_inv, hππ]
  have harith : ∀ E I : ℝ, 2 / Real.pi * E * I
      = 1 / Real.sqrt Real.pi * E * ((Real.sqrt Real.pi)⁻¹ * (2 * I)) := by
    intro E I
    rw [div_eq_mul_inv, ← hinv]
    ring
  rw [hU, erf_7_7_1 hz.le, harith]

end FLMF.Error
