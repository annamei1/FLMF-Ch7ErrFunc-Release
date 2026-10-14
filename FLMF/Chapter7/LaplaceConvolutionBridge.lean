import FLMF.Chapter7.Erf
import FLMF.Chapter7.ErfcLeading
import FLMF.Chapter7.Definitions
import FLMF.Support.LaplaceTransform
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Laplace transform of `erf(b t)`, through `Methods.LaplaceTransform`'s convolution
# theorem (DLMF 7.14.2)

**Anchor for M-laplace-convolution.** DLMF 7.14.2
(`∫₀^∞ e^{-at} erf(bt) dt = (1/a) e^{a²/(4b²)} erfc(a/(2b))`) is proven here
*through* the Laplace module's causal-convolution theorem
(`FLMF.Methods.LaplaceTransform.laplaceTransform_convolution`, DLMF
1.14.30/1.14.31), not by a direct `Ioi` argument on the original integrand:

* `erf(bt) = ∫_0^t h(u) du` with `h(u) = (2b/√π) e^{-b²u²}` (FTC on the
  defining Gaussian integral of `erf`, composed with the linear rescaling
  `u ↦ bu`) is *exactly* the causal convolution of `h` with the constant
  function `g ≡ 1` in `laplaceTransform_convolution`'s own `Ioc 0 t` shape
  (`erf_scaled_eq_convolution`).
* `laplaceTransform_erf_scaled_eq_convolution` bridges
  `laplaceTransform (fun t => erf(bt)) a` to
  `laplaceTransform (fun t => ∫ u in Ioc 0 t, h(u)·1) a` via this pointwise
  identity.
* `laplaceTransform_convolution` itself (applied to `f = hK b`, `g ≡ 1`) then
  factors this into `L[h](a) · L[1](a)` — the genuine consumption of the
  module's convolution theorem, not a re-derivation of it.
* `L[1](a) = 1/a` is `laplaceTransform_pow 0` (the module's `t^n` pair
  specialized to `n = 0`).
* `L[h](a) = e^{a²/(4b²)} erfc(a/(2b))` (`laplaceTransform_hK_eq`) is computed
  by completing the square in the real Gaussian integral defining `L[h]`
  (`J_eq_erfc`), then identifying the resulting shifted-Gaussian tail with
  `erfc` via the Watson-ready representation already proven in
  `ErfcLeading.lean` (`erfc_eq_watson`, DLMF 7.12.1) — `tail_shifted_gaussian`
  is the reusable form of that identification,
  `∫_{(0,∞)} e^{-(u+x)²} du = (√π/2) erfc(x)` for `x > 0`.
* `laplaceTransform_erf_scaled` assembles all of the above into the closed
  form, and `erf_7_14_2` (in `Ch7Integrals.lean`) is a corollary via the
  bridge `laplaceTransform_erf_scaled_eq_ofReal`.
-/

namespace FLMF.Error

open MeasureTheory Real Set Filter FLMF.Methods.LaplaceTransform
open scoped Real Topology

/-- The convolution kernel `h(u) = (2b/√π) e^{-b²u²}`, cast to `ℂ`: the causal
convolution `h ∗ 1` reproduces `erf(b·)` (`erf_scaled_eq_convolution`). -/
-- no-dlmf: Laplace-module bridging definition for 7.14.2, no independent DLMF number
noncomputable def hK (b : ℝ) : ℝ → ℂ :=
  fun u => (((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2))) : ℝ)

/-- `erf(b·)` has derivative `h` (the convolution kernel `hK`, real part) at
every `t : ℝ` — chain rule on `hasDerivAt_erf` through the rescaling `t ↦ b*t`. -/
-- no-dlmf: derivative helper feeding the FTC identification, no independent DLMF number
theorem hasDerivAt_erf_scaled (b t : ℝ) :
    HasDerivAt (fun t : ℝ => erf (b * t))
      ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2))) t := by
  have hbt : HasDerivAt (fun t : ℝ => b * t) b t := by
    simpa using (hasDerivAt_id t).const_mul b
  have h := (hasDerivAt_erf (b * t)).comp t hbt
  have hrw : (2 / Real.sqrt Real.pi) * Real.exp (-(b * t) ^ 2) * b
      = (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2)) := by
    rw [show (b * t) ^ 2 = b ^ 2 * t ^ 2 by ring]; ring
  rwa [hrw] at h

/-- **FTC form:** `erf(bt) = ∫_0^t h(u) du` (interval-integral form), `h(u) = (2b/√π)e^{-b²u²}`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem erf_scaled_eq_intervalIntegral (b t : ℝ) :
    erf (b * t) = ∫ u in (0:ℝ)..t, (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2)) := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) t, HasDerivAt (fun t : ℝ => erf (b * t))
      ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * x ^ 2))) x :=
    fun x _ => hasDerivAt_erf_scaled b x
  have hcont : Continuous (fun u : ℝ => (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2))) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun u : ℝ => (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2))) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]; simp [erf_zero]

/-- **The convolution identity itself:** `erf(bt) = ∫ u in Ioc 0 t, h(u)·1 du`
(`t ≥ 0`) — exactly `laplaceTransform_convolution`'s causal-convolution shape
with kernel `hK b` and the constant function `g ≡ 1`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem erf_scaled_eq_convolution (b t : ℝ) (ht : 0 ≤ t) :
    (erf (b * t) : ℂ) = ∫ u in Ioc (0:ℝ) t, hK b u * (1:ℂ) := by
  have hreal := erf_scaled_eq_intervalIntegral b t
  rw [intervalIntegral.integral_of_le ht] at hreal
  have key := (integral_ofReal
    (f := fun u : ℝ => 2 * b / Real.sqrt Real.pi * Real.exp (-(b ^ 2 * u ^ 2)))
    (μ := volume.restrict (Ioc (0:ℝ) t)) (𝕜 := ℂ))
  calc (erf (b * t) : ℂ)
      = ((∫ u in Ioc (0:ℝ) t, (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2))) : ℝ) := by
        exact_mod_cast hreal
    _ = ∫ u in Ioc (0:ℝ) t, (((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2)) : ℝ) : ℂ) :=
        key.symm
    _ = ∫ u in Ioc (0:ℝ) t, hK b u * 1 := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
        unfold hK; ring

/-- `hK b` is integrable against the Laplace kernel at `a` (bounded by the
integrable exponential kernel, since `‖h(u)‖ ≤ 2b/√π`). -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem integrableOn_hK (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * hK b t) (Ioi 0) := by
  have hv'_int : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_complex_Ioi (a := -(a:ℂ)) (by simp; linarith) 0
  have hu_meas : AEStronglyMeasurable (hK b) (volume.restrict (Ioi (0:ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold hK; fun_prop
  have hbound : ∀ t ∈ Ioi (0:ℝ),
      ‖Complex.exp (-(a:ℂ) * t) * hK b t‖
        ≤ ‖((2 * b / Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-(a:ℂ) * t)‖ := by
    intro t _
    have hu_le : ‖hK b t‖ ≤ 2 * b / Real.sqrt Real.pi := by
      unfold hK
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hexple : Real.exp (-(b ^ 2 * t ^ 2)) ≤ 1 := by
        rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg t, sq_nonneg b]
      have hpos : 0 ≤ (2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2)) := by positivity
      rw [abs_of_nonneg hpos]
      nlinarith [Real.exp_pos (-(b ^ 2 * t ^ 2)), hexple]
    calc ‖Complex.exp (-(a:ℂ) * t) * hK b t‖
        = ‖Complex.exp (-(a:ℂ) * t)‖ * ‖hK b t‖ := norm_mul _ _
      _ ≤ ‖Complex.exp (-(a:ℂ) * t)‖ * (2 * b / Real.sqrt Real.pi) :=
          mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = ‖((2 * b / Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-(a:ℂ) * t)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * b / Real.sqrt Real.pi)]
          ring
  exact Integrable.mono (hv'_int.const_mul ((2 * b / Real.sqrt Real.pi : ℝ) : ℂ))
    (hv'_int.aestronglyMeasurable.mul hu_meas)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hbound t ht)

/-- **Shifted-Gaussian tail = `erfc`:** `∫_{(0,∞)} e^{-(u+x)²} du = (√π/2) erfc(x)`
for `x > 0`, the reusable form of the identification already implicit in
`ErfcLeading.lean`'s `erfc_eq_watson` (DLMF 7.12.1). -/
-- no-dlmf: Gaussian-tail identity feeding the Laplace-convolution bridge, no independent
-- DLMF number (the underlying `erfc_eq_watson` already carries 7.12.1)
theorem tail_shifted_gaussian {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2) = (Real.sqrt Real.pi / 2) * erfc x := by
  have hint_eq : (∫ u in Ioi (0:ℝ), Real.exp (-(2 * x) * u) * Real.exp (-u ^ 2))
      = Real.exp (x ^ 2) * ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have herfc := erfc_eq_watson hx
  rw [hint_eq] at herfc
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hexp : Real.exp (-x ^ 2) * Real.exp (x ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hcollapse : (2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)
      * (Real.exp (x ^ 2) * ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2))
      = (2 / Real.sqrt Real.pi) * ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2) := by
    rw [show (2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)
        * (Real.exp (x ^ 2) * ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2))
        = (2 / Real.sqrt Real.pi) * (Real.exp (-x ^ 2) * Real.exp (x ^ 2))
          * ∫ u in Ioi (0:ℝ), Real.exp (-(u + x) ^ 2) by ring, hexp]
    ring
  rw [hcollapse] at herfc
  field_simp at herfc
  linarith [herfc]

/-- **`L[h](a) = e^{a²/(4b²)} erfc(a/(2b))`** (real form): completing the square
in `∫_{(0,∞)} e^{-au}·h(u) du`, then a scale substitution (`u = s/b`) and
`tail_shifted_gaussian`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem J_eq_erfc (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Ioi (0:ℝ), Real.exp (-a * u) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2)))
      = Real.exp (a ^ 2 / (4 * b ^ 2)) * erfc (a / (2 * b)) := by
  set x := a / (2 * b) with hx_def
  have hx : 0 < x := by rw [hx_def]; positivity
  have hpt : ∀ u : ℝ, Real.exp (-a * u) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * u ^ 2)))
      = (2 * b / Real.sqrt Real.pi) * Real.exp (a ^ 2 / (4 * b ^ 2)) * Real.exp (-(b * u + x) ^ 2) := by
    intro u
    have key : Real.exp (-a * u) * Real.exp (-(b ^ 2 * u ^ 2))
        = Real.exp (a ^ 2 / (4 * b ^ 2)) * Real.exp (-(b * u + x) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hx_def]; field_simp; ring
    calc Real.exp (-a * u) * (2 * b / Real.sqrt Real.pi * Real.exp (-(b ^ 2 * u ^ 2)))
        = 2 * b / Real.sqrt Real.pi * (Real.exp (-a * u) * Real.exp (-(b ^ 2 * u ^ 2))) := by ring
      _ = 2 * b / Real.sqrt Real.pi * (Real.exp (a ^ 2 / (4 * b ^ 2)) * Real.exp (-(b * u + x) ^ 2)) := by
          rw [key]
      _ = 2 * b / Real.sqrt Real.pi * Real.exp (a ^ 2 / (4 * b ^ 2)) * Real.exp (-(b * u + x) ^ 2) := by
          ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u)]
  rw [integral_const_mul]
  have hscale : (∫ u in Ioi (0:ℝ), Real.exp (-(b * u + x) ^ 2))
      = b⁻¹ * ∫ s in Ioi (0:ℝ), Real.exp (-(s + x) ^ 2) := by
    have h := integral_comp_mul_left_Ioi (fun s : ℝ => Real.exp (-(s + x) ^ 2)) 0 hb
    simpa using h
  rw [hscale, tail_shifted_gaussian hx]
  have hbne : b ≠ 0 := ne_of_gt hb
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

/-- **`laplaceTransform (hK b) a = e^{a²/(4b²)} erfc(a/(2b))`** (complex form,
casting `J_eq_erfc`). -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem laplaceTransform_hK_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    laplaceTransform (hK b) (a:ℂ) = ((Real.exp (a ^ 2 / (4 * b ^ 2)) * erfc (a / (2 * b)) : ℝ) : ℂ) := by
  simp only [laplaceTransform, hK]
  have hcongr : ∀ t : ℝ,
      Complex.exp (-(a:ℂ) * (t:ℂ)) * (((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2)) : ℝ) : ℂ)
      = ((Real.exp (-a * t) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2))) : ℝ) : ℂ) := by
    intro t; push_cast; ring_nf
  have key := (integral_ofReal
    (f := fun t : ℝ => Real.exp (-a * t) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2))))
    (μ := volume.restrict (Ioi (0:ℝ))) (𝕜 := ℂ))
  calc (∫ t in Ioi (0:ℝ), Complex.exp (-(a:ℂ) * (t:ℂ)) *
        (((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2)) : ℝ) : ℂ))
      = ∫ t in Ioi (0:ℝ),
          ((Real.exp (-a * t) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2))) : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)
    _ = ((∫ t in Ioi (0:ℝ),
          Real.exp (-a * t) * ((2 * b / Real.sqrt Real.pi) * Real.exp (-(b ^ 2 * t ^ 2)))) : ℝ) := key
    _ = ((Real.exp (a ^ 2 / (4 * b ^ 2)) * erfc (a / (2 * b)) : ℝ) : ℂ) := by
        exact_mod_cast (J_eq_erfc a b ha hb)

/-- Bridge: `laplaceTransform (fun t => erf(bt)) a` equals the module's own
`laplaceTransform` of the causal convolution `hK b ∗ 1` — the pointwise
identification, feeding directly into `laplaceTransform_convolution`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem laplaceTransform_erf_scaled_eq_convolution (a b : ℝ) :
    laplaceTransform (fun t => (erf (b * t) : ℂ)) (a:ℂ)
      = laplaceTransform (fun t => ∫ u in Ioc (0:ℝ) t, hK b u * (1:ℂ)) (a:ℂ) := by
  simp only [laplaceTransform]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [erf_scaled_eq_convolution b t (le_of_lt ht)]

-- no-dlmf: proof-vocabulary corollary of erf_7_14_2 (DLMF 7.14.2); the 1.14.30/1.14.31 citation is the method used (the Laplace convolution theorem), not the equation formalized. The faithful 7.14.2 surface is `erf_7_14_2` in Ch7Integrals.lean.
/-- **The Laplace-routed derivation of DLMF 7.14.2.**
`laplaceTransform (fun t => erf(bt)) a = (1/a) e^{a²/(4b²)} erfc(a/(2b))`,
derived through
`FLMF.Methods.LaplaceTransform.laplaceTransform_convolution` (the Laplace
convolution theorem, 1.14.30/1.14.31), NOT via a direct `Ioi`-integration
argument on the original integrand. -/
theorem laplaceTransform_erf_scaled (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    laplaceTransform (fun t => (erf (b * t) : ℂ)) (a:ℂ)
      = ((1 / a) * Real.exp (a ^ 2 / (4 * b ^ 2)) * erfc (a / (2 * b)) : ℝ) := by
  have hf := integrableOn_hK a b ha hb
  have hg : IntegrableOn (fun t : ℝ => Complex.exp (-(a:ℂ) * t) * (1:ℂ)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_complex_Ioi (a := -(a:ℂ)) (by simp; linarith) (0:ℝ)
  have hconv := laplaceTransform_convolution (hK b) (fun _ : ℝ => (1:ℂ)) (a:ℂ) hf hg
  rw [laplaceTransform_erf_scaled_eq_convolution a b, hconv, laplaceTransform_hK_eq a b ha hb]
  have hone : laplaceTransform (fun _ : ℝ => (1:ℂ)) (a:ℂ) = 1 / (a:ℂ) := by
    have := laplaceTransform_pow 0 (s := (a:ℂ)) (by exact_mod_cast ha)
    simpa using this
  rw [hone]
  push_cast
  ring

/-- Bridge: `laplaceTransform (fun t => (erf(bt):ℂ)) (a:ℂ)` equals the cast of
the real integral, for real `a`, `b`. -/
-- no-dlmf: Laplace-module bridging lemma for 7.14.2, no independent DLMF number
theorem laplaceTransform_erf_scaled_eq_ofReal (a b : ℝ) :
    laplaceTransform (fun t => (erf (b * t) : ℂ)) (a:ℂ)
      = ((∫ t in Ioi (0:ℝ), Real.exp (-a * t) * erf (b * t)) : ℝ) := by
  simp only [laplaceTransform]
  have hcongr : ∀ t : ℝ, Complex.exp (-(a:ℂ) * (t:ℂ)) * (erf (b * t) : ℂ)
      = ((Real.exp (-a * t) * erf (b * t) : ℝ) : ℂ) := by
    intro t; push_cast; ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t)]
  exact _root_.integral_ofReal

end FLMF.Error
