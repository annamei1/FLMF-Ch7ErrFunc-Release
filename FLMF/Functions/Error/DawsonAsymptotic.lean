import FLMF.Functions.Error.Dawson

/-!
# Leading asymptotic of the Dawson function

We prove `F(x) ~ 1/(2x)` as `x → ∞`, in the precise form

`Tendsto (fun x => 2 * x * dawson x) atTop (𝓝 1)`   (DLMF 7.12).
-/

namespace FLMF

open scoped Real
open intervalIntegral MeasureTheory Filter Topology

-- no-dlmf: abbreviation for the inner primitive; analytic infrastructure, no DLMF identity
/-- Inner integral `I(x) = ∫₀ˣ e^{t²} dt`. -/
noncomputable def dawsonInt (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.exp (t ^ 2)

-- no-dlmf: definitional rewrite of dawson; analytic infrastructure, no DLMF identity
theorem dawson_eq (x : ℝ) : dawson x = Real.exp (-x ^ 2) * dawsonInt x := rfl

-- no-dlmf: derivative helper for the asymptotic proof; analytic infrastructure, no DLMF identity
/-- Derivative of `t ↦ e^{t²}/(2t)` at `t ≠ 0` is `e^{t²}(1 - 1/(2t²))`. -/
theorem hasDerivAt_aux (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2) / (2 * t))
      (Real.exp (t ^ 2) * (1 - 1 / (2 * t ^ 2))) t := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (Real.exp (t ^ 2) * (2 * t)) t := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    simpa [mul_comm] using (Real.hasDerivAt_exp (t ^ 2)).comp t h1
  have hden : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ))
  have hne : (2 * t) ≠ 0 := mul_ne_zero two_ne_zero ht
  have hd := hexp.div hden hne
  convert hd using 1
  field_simp
