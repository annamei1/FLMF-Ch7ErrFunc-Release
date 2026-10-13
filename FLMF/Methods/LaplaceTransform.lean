import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import FLMF.Methods.ContourRotationGamma

/-!
# The Laplace transform (method kit — DLMF §1.14)

**Mathlib has no Laplace transform** (re-verified 2026-07-13: no declaration or
file mentions "laplace" in the transform sense — the two hits are an unrelated
notation class and a bibliography citation). This file is the FLMF entry point:

* `laplaceTransform f s = ∫_{(0,∞)} e^{-st} f(t) dt` (DLMF **1.14.17**), plus a
  convergence lemma `integrableOn_laplaceTransform_of_exponentialOrder`
  (exponential order ⟹ integrable on the half-plane `Re s > σ₀`, DLMF
  1.14.18/1.14.19).
* The operational core: linearity (`laplaceTransform_add`, `_smul`), the shift
  rule (DLMF **1.14.21**), the derivative rule (DLMF **1.14.27**, via IBP on
  `Ioi 0` — Mathlib's `integral_Ioi_deriv_mul_eq_sub`), and `t^n ↦ n!/s^{n+1}`
  built on `FLMF.Methods.ContourRotation.Gamma.scaled_gamma` (the complex-rate
  Laplace–Mellin formula `∫₀^∞ t^{s-1}e^{-ct}dt = c^{-s}Γ(s)`), extended off
  `scaled_gamma`'s upper-half-plane restriction (`Im c ≥ 0`) to the full
  half-plane `Re c > 0` via `Complex.Gamma_conj`/`Complex.conj_cpow`
  (`scaled_gamma_two_sided`).
* Concrete tagged pairs: `laplaceTransform_pow` (`t^n`, no individual DLMF
  number — §1.14 tags only the *properties*, not this table entry),
  `laplaceTransform_exp` (`e^{at}`), and the existing `laplace_cos`/`laplace_sin`
  upgraded to genuine `laplaceTransform` statements
  (`laplaceTransform_cos`, `laplaceTransform_sin`).
* The convolution theorem (DLMF **1.14.30**/**1.14.31**, `L[f∗g] = L[f]·L[g]`
  with `(f∗g)(t) = ∫₀^t f(u)g(t-u)du`), proven via Mathlib's *causal*
  convolution machinery `MeasureTheory.integral_posConvolution` (the `Nonneg`
  section of `Mathlib.Analysis.Convolution` — not the whole-line
  `convolution`): the kernel splitting `e^{-st} = e^{-su}·e^{-s(t-u)}`
  identifies `e^{-st}·(f∗g)(t)` with the causal convolution of the weighted
  integrands `e^{-su}f(u)`, `e^{-sv}g(v)`, which `integral_posConvolution`
  factors into the product of the two transforms
  (`laplaceTransform_convolution`).

Reusable building blocks for the Dirichlet integral
(`FLMF.ExpIntegrals.laplace_sinc`), Coulomb phase shifts, and Bessel/oscillatory
tail evaluations.
-/

namespace FLMF.Methods.LaplaceTransform

open MeasureTheory Filter Topology Set Complex
open scoped Real

/-- Laplace transform of cosine: `∫_{(0,∞)} e^{-εt} cos(s t) dt = ε/(ε²+s²)` (ε>0). -/
-- no-dlmf: Laplace transform of cosine, elementary building block (DLMF §1.14 area)
theorem laplace_cos (ε s : ℝ) (hε : 0 < ε) :
    ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * Real.cos (s * t) = ε / (ε ^ 2 + s ^ 2) := by
  set a : ℂ := (-ε : ℂ) + s * Complex.I with ha_def
  have ha : a.re < 0 := by simp only [ha_def]; simp; linarith
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (a * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hcomplex : ∫ t in Ioi (0:ℝ), Complex.exp (a * t) = -1 / a := by
    rw [integral_exp_mul_complex_Ioi ha 0]; simp
  have hre_int : ∀ t : ℝ, (Complex.exp (a * (t : ℂ))).re = Real.exp (-ε * t) * Real.cos (s * t) := by
    intro t
    have hat : a * (t : ℂ) = ((-ε * t : ℝ) : ℂ) + ((s * t : ℝ) : ℂ) * Complex.I := by
      rw [ha_def]; push_cast; ring
    rw [hat, Complex.exp_re]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hLHS : (∫ t in Ioi (0:ℝ), Complex.exp (a * t)).re
      = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * Real.cos (s * t) := by
    rw [show (∫ t in Ioi (0:ℝ), Complex.exp (a * t)).re
          = ∫ t in Ioi (0:ℝ), (Complex.exp (a * t)).re
        from by simpa using (integral_re hint).symm]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hre_int t)
  rw [← hLHS, hcomplex]
  have hnorm : Complex.normSq a = ε ^ 2 + s ^ 2 := by
    simp only [ha_def, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [Complex.div_re, hnorm]
  simp only [ha_def, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Laplace transform of sine: `∫_{(0,∞)} e^{-εt} sin(s t) dt = s/(ε²+s²)` (ε>0). -/
-- no-dlmf: Laplace transform of sine, elementary building block (DLMF §1.14 area)
theorem laplace_sin (ε s : ℝ) (hε : 0 < ε) :
    ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * Real.sin (s * t) = s / (ε ^ 2 + s ^ 2) := by
  set a : ℂ := (-ε : ℂ) + s * Complex.I with ha_def
  have ha : a.re < 0 := by simp only [ha_def]; simp; linarith
  have hint : IntegrableOn (fun t : ℝ => Complex.exp (a * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hcomplex : ∫ t in Ioi (0:ℝ), Complex.exp (a * t) = -1 / a := by
    rw [integral_exp_mul_complex_Ioi ha 0]; simp
  have him_int : ∀ t : ℝ, (Complex.exp (a * (t : ℂ))).im = Real.exp (-ε * t) * Real.sin (s * t) := by
    intro t
    have hat : a * (t : ℂ) = ((-ε * t : ℝ) : ℂ) + ((s * t : ℝ) : ℂ) * Complex.I := by
      rw [ha_def]; push_cast; ring
    rw [hat, Complex.exp_im]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hLHS : (∫ t in Ioi (0:ℝ), Complex.exp (a * t)).im
      = ∫ t in Ioi (0:ℝ), Real.exp (-ε * t) * Real.sin (s * t) := by
    rw [show (∫ t in Ioi (0:ℝ), Complex.exp (a * t)).im
          = ∫ t in Ioi (0:ℝ), (Complex.exp (a * t)).im
        from by simpa using (integral_im hint).symm]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => him_int t)
  rw [← hLHS, hcomplex]
  have hnorm : Complex.normSq a = ε ^ 2 + s ^ 2 := by
    simp only [ha_def, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [Complex.div_im, hnorm]
  simp only [ha_def, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-! ### The Laplace transform: definition, convergence, and linearity -/

/-- **The Laplace transform.** `laplaceTransform f s = ∫_{(0,∞)} e^{-st} f(t) dt`
(DLMF **1.14.17**). Defined unconditionally as a Bochner integral (it evaluates
to `0` off the region of convergence, per the usual `MeasureTheory` convention
for non-integrable integrands); the honest content is in the convergence
hypotheses attached to each downstream theorem. -/
noncomputable def laplaceTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) * f t

/-- **Convergence region (exponential order).** `f` has exponential order `σ₀`
if `‖f(t)‖ ≤ M·e^{σ₀t}` on `[0,∞)` (DLMF **1.14.18**, with `M` explicit). Under
this bound, `laplaceTransform f s` converges (is given by an integrable
integrand) for every `s` with `Re s > σ₀`. -/
theorem integrableOn_laplaceTransform_of_exponentialOrder {f : ℝ → ℂ} {σ₀ M : ℝ}
    (_hM : 0 ≤ M) (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hbound : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ₀ * t))
    {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * f t) (Ioi 0) := by
  have hdec : 0 < s.re - σ₀ := by linarith
  have hgint : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - σ₀) * t)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(s.re - σ₀) < 0) 0).const_mul M
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-s * t) * f t)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hexp : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
        |>.aestronglyMeasurable
    exact hexp.mul hf
  refine Integrable.mono' hgint hmeas ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hbt : ‖f t‖ ≤ M * Real.exp (σ₀ * t) := hbound t ht
    have hnorm_exp : ‖Complex.exp (-s * (t : ℂ))‖ = Real.exp (-s.re * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, mul_comm]
    calc ‖Complex.exp (-s * (t : ℂ)) * f t‖
        = ‖Complex.exp (-s * (t : ℂ))‖ * ‖f t‖ := norm_mul _ _
      _ ≤ Real.exp (-s.re * t) * (M * Real.exp (σ₀ * t)) := by
          rw [hnorm_exp]; exact mul_le_mul_of_nonneg_left hbt (Real.exp_pos _).le
      _ = M * Real.exp (-(s.re - σ₀) * t) := by
          rw [show Real.exp (-s.re * t) * (M * Real.exp (σ₀ * t))
                = M * (Real.exp (-s.re * t) * Real.exp (σ₀ * t)) by ring,
            ← Real.exp_add]
          congr 2
          ring

/-! ### Linearity -/

/-- **Linearity (sum).** `L[f + g](s) = L[f](s) + L[g](s)`, given integrability
of both transforms at `s`. -/
theorem laplaceTransform_add {f g : ℝ → ℂ} {s : ℂ}
    (hf : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * f t) (Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * g t) (Ioi 0)) :
    laplaceTransform (fun t => f t + g t) s = laplaceTransform f s + laplaceTransform g s := by
  simp only [laplaceTransform, mul_add]
  exact integral_add hf hg

/-- **Linearity (scalar multiple).** `L[c•f](s) = c·L[f](s)` for any `c : ℂ`. -/
theorem laplaceTransform_smul (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    laplaceTransform (fun t => c * f t) s = c * laplaceTransform f s := by
  simp only [laplaceTransform]
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-! ### Shift rule -/

/-- **Shift rule** (DLMF **1.14.21**): `L[e^{at}f](s) = L[f](s-a)`, for `a : ℂ`
and any `s` (both sides are the same integral after regrouping the exponential
factor — no extra convergence hypothesis beyond the definitional integral being
well-posed as a Bochner integral, which holds unconditionally by the `= 0` off
the region of convergence convention). -/
theorem laplaceTransform_shift (a : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    laplaceTransform (fun t => Complex.exp (a * t) * f t) s = laplaceTransform f (s - a) := by
  simp only [laplaceTransform]
  congr 1
  funext t
  rw [show -(s - a) * (t : ℂ) = -s * t + a * t by ring, Complex.exp_add]
  ring

/-! ### Derivative rule -/

/-- Derivative of the Laplace kernel `t ↦ e^{-st}` (real variable, complex
value): `d/dt e^{-st} = -s·e^{-st}`. -/
-- no-dlmf: derivative helper, no DLMF equation
theorem hasDerivAt_laplaceKernel (s : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-s * (t : ℂ))) (-s * Complex.exp (-s * (t : ℂ))) t := by
  have hofR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := t)
  have h1 : HasDerivAt (fun t : ℝ => -s * (t : ℂ)) (-s) t := by
    simpa using hofR.const_mul (-s)
  have h2 := h1.cexp
  simpa [mul_comm] using h2

/-- **Derivative rule** (DLMF **1.14.27**): `L[f'](s) = s·L[f](s) - f(0)`, for
`f : ℝ → ℂ` continuously differentiable on `[0,∞)` with derivative `f'`, given:
(i) `L[f](s)` and `L[f'](s)` both converge (are integrable on `Ioi 0`), and
(ii) `e^{-st}f(t) → 0` as `t → ∞` (the boundary term vanishes — automatic once
`f` has exponential order `< Re s`, but stated directly here as the sharp
hypothesis IBP actually needs). -/
theorem laplaceTransform_deriv {f f' : ℝ → ℂ} {s : ℂ}
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * f t) (Ioi 0))
    (hf' : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * f' t) (Ioi 0))
    (hcont : ContinuousWithinAt f (Ici (0 : ℝ)) 0)
    (hbdry : Tendsto (fun t : ℝ => Complex.exp (-s * t) * f t) atTop (𝓝 0)) :
    laplaceTransform f' s = s * laplaceTransform f s - f 0 := by
  have hu : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => Complex.exp (-s * (t : ℂ))) (-s * Complex.exp (-s * (t : ℂ))) t :=
    fun t _ => hasDerivAt_laplaceKernel s t
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := hderiv
  have hzero : Tendsto (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * f t) (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
    have hexp0 : Tendsto (fun t : ℝ => Complex.exp (-s * (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : ContinuousAt (fun t : ℝ => Complex.exp (-s * (t : ℂ))) 0 :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousAt
      simpa using (this.continuousWithinAt (s := Ioi (0:ℝ))).tendsto
    have hcont' : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have := hexp0.mul hcont'
    simpa using this
  have hu'v : IntegrableOn (fun t : ℝ => -s * Complex.exp (-s * (t : ℂ)) * f t) (Ioi 0) := by
    have hmul := hf.const_mul (-s)
    simpa [mul_assoc] using hmul
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0:ℝ)) hu hv hf' hu'v hzero hbdry
  have hrewrite : ∫ t in Ioi (0:ℝ), -s * Complex.exp (-s * (t:ℂ)) * f t
      = -(s * ∫ t in Ioi (0:ℝ), Complex.exp (-s * (t:ℂ)) * f t) := by
    have hcongr : ∀ t : ℝ, -s * Complex.exp (-s * (t:ℂ)) * f t
        = (-s) * (Complex.exp (-s * (t:ℂ)) * f t) := fun t => by ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t), integral_const_mul]
    ring
  simp only [laplaceTransform]
  rw [key, hrewrite]
  ring

/-! ### `t^n ↦ n!/s^{n+1}` — the power pair, via `scaled_gamma`

`FLMF.Methods.ContourRotation.Gamma.scaled_gamma` gives the complex-rate
Laplace–Mellin formula only for rates `c` with `Im c ≥ 0` (the sector-rotation
route only reaches the upper half-plane). The Laplace variable `s` ranges over
the *full* half-plane `Re s > 0`, so we first extend `scaled_gamma` to
`Im c < 0` by complex conjugation (`Complex.Gamma_conj`, `Complex.conj_cpow`),
then specialize the Γ-exponent to `n + 1` for the tagged pair. -/

/-- **Two-sided scaled Γ integral, natural-power case.** `scaled_gamma`
extended off its `Im c ≥ 0` restriction to the full half-plane `Re c > 0`, for
the natural-number exponent `∫₀^∞ t^n e^{-ct} dt = n!/c^{n+1}` needed for the
Laplace pair. Extended by conjugation: for `t : ℝ`, `t^n` is real, so the
integral, `Γ`, and the natural power `c^{-(n+1)}` are all conjugation-symmetric
in `c` (`Im c < 0` reduces to the known `Im (conj c) ≥ 0` case). -/
theorem scaled_gamma_pow_two_sided (n : ℕ) {c : ℂ} (hre : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(c * (t : ℂ)))
      = (Nat.factorial n : ℂ) / c ^ (n + 1) := by
  have hbase_case : ∀ c : ℂ, 0 < c.re → 0 ≤ c.im →
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(c * (t : ℂ)))
        = (Nat.factorial n : ℂ) / c ^ (n + 1) := by
    intro c hre him
    have hnpos : (0:ℝ) < ((n : ℂ) + 1).re := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity
    have hΓ := FLMF.Methods.ContourRotation.Gamma.scaled_gamma
      ((n : ℂ) + 1) hnpos hre him
    have hcpow : ∀ t : ℝ, (t : ℂ) ^ (((n : ℂ) + 1) - 1) = (t : ℂ) ^ n := by
      intro t
      rw [show ((n : ℂ) + 1) - 1 = (n : ℂ) by ring, Complex.cpow_natCast]
    have hcne : c ≠ 0 := by rintro rfl; simp at hre
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hcpow t])] at hΓ
    rw [hΓ, Complex.Gamma_nat_eq_factorial, Complex.cpow_neg,
      show ((n:ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
    field_simp
  rcases lt_or_ge c.im 0 with him | him
  · have hconjre : (0:ℝ) < (starRingEnd ℂ c).re := by simpa using hre
    have hconjim : 0 ≤ (starRingEnd ℂ c).im := by simp; linarith
    have hbase := hbase_case (starRingEnd ℂ c) hconjre hconjim
    have hlhs : ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ n * Complex.exp (-((starRingEnd ℂ c) * (t : ℂ)))
        = starRingEnd ℂ (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(c * (t : ℂ)))) := by
      rw [← integral_conj]
      congr 1
      funext t
      rw [show starRingEnd ℂ ((t:ℂ) ^ n * Complex.exp (-(c * (t : ℂ))))
            = (starRingEnd ℂ ((t:ℂ)^n)) * starRingEnd ℂ (Complex.exp (-(c * (t : ℂ)))) from
          map_mul _ _ _]
      rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
        show starRingEnd ℂ ((t:ℂ)^n) = (t:ℂ)^n from by
          rw [map_pow, Complex.conj_ofReal]]
    rw [hlhs] at hbase
    have hconj_eq := congrArg (starRingEnd ℂ) hbase
    rw [Complex.conj_conj, map_div₀, map_pow, Complex.conj_conj, map_natCast] at hconj_eq
    exact hconj_eq
  · exact hbase_case c hre him

/-- **Laplace transform pair** `t^n ↦ n!/s^{n+1}` (untagged in DLMF §1.14: the
table entries there are the *properties* (1.14.21–1.14.31), not this base
transform pair; the table of concrete pairs lives in §1.14(vii), not tagged
per-entry). Valid for `Re s > 0` — the full half-plane, via
`scaled_gamma_pow_two_sided`. -/
-- no-dlmf: concrete Laplace pair, §1.14 tags properties not this table entry
theorem laplaceTransform_pow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => (t : ℂ) ^ n) s = (Nat.factorial n : ℂ) / s ^ (n + 1) := by
  simp only [laplaceTransform]
  have heq : ∀ t : ℝ, Complex.exp (-s * (t:ℂ)) * (t:ℂ)^n
      = (t:ℂ)^n * Complex.exp (-(s * (t:ℂ))) := fun t => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
  exact scaled_gamma_pow_two_sided n hs

/-! ### Concrete tagged pairs: `e^{at}`, `cos`, `sin` -/

/-- **Laplace transform pair** `e^{at} ↦ 1/(s-a)` for `Re s > Re a` (§1.14(vii),
untagged individually — the standard exponential pair). -/
-- no-dlmf: concrete Laplace pair, §1.14 tags properties not this table entry
theorem laplaceTransform_exp (a : ℂ) {s : ℂ} (hs : a.re < s.re) :
    laplaceTransform (fun t => Complex.exp (a * t)) s = 1 / (s - a) := by
  simp only [laplaceTransform]
  have hb : (-(s - a)).re < 0 := by simp; linarith
  have heq : ∀ t : ℝ, Complex.exp (-s * (t:ℂ)) * Complex.exp (a * (t:ℂ))
      = Complex.exp (-(s - a) * (t:ℂ)) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t),
    integral_exp_mul_complex_Ioi hb 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_neg, neg_div, neg_neg]

/-- **Laplace transform of cosine**, genuine (not merely regularized) version:
`L[cos(bt)](s) = s/(s²+b²)` for `Re s > 0` (§1.14(vii)). Upgrades `laplace_cos`
(stated only for real `s = ε > 0` and a regularizing `ε` on the LHS kernel) to
the honest complex-`s` Laplace transform. -/
-- no-dlmf: concrete Laplace pair, §1.14 tags properties not this table entry
theorem laplaceTransform_cos (b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => (Real.cos (b * t) : ℂ)) s = s / (s ^ 2 + (b : ℂ) ^ 2) := by
  have hcos : ∀ t : ℝ, (Real.cos (b * t) : ℂ)
      = Complex.exp ((Complex.I * b) * t) / 2 + Complex.exp (-(Complex.I * b) * t) / 2 := by
    intro t
    have h2 := Complex.two_cos (x := ((b : ℂ) * (t:ℂ)))
    have hcast : ((Real.cos (b * t) : ℝ) : ℂ) = Complex.cos ((b:ℂ) * (t:ℂ)) := by
      rw [Complex.ofReal_cos (b * t)]
      congr 1
      push_cast
      ring
    rw [hcast]
    rw [show ((b:ℂ) * t) * Complex.I = (Complex.I * b) * t by ring,
      show -(((b:ℂ) * t)) * Complex.I = -(Complex.I * b) * t by ring] at h2
    linear_combination h2 / 2
  have hIb : (Complex.I * b).re < s.re := by
    simp; linarith
  have hnIb : (-(Complex.I * b)).re < s.re := by
    simp; linarith
  have hL1 := laplaceTransform_exp (Complex.I * b) hIb
  have hL2 := laplaceTransform_exp (-(Complex.I * b)) hnIb
  have hint1 : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * Complex.exp ((Complex.I*b)*t))
      (Ioi 0) := by
    have hbase := integrableOn_exp_mul_complex_Ioi (a := -(s - Complex.I*b))
      (by simp; linarith) (0:ℝ)
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t _
    show Complex.exp (-(s - Complex.I*b) * (t:ℂ))
        = Complex.exp (-s * (t:ℂ)) * Complex.exp ((Complex.I*b) * (t:ℂ))
    rw [← Complex.exp_add]; congr 1; ring
  have hint2 : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * t) * Complex.exp (-(Complex.I*b)*t)) (Ioi 0) := by
    have hbase := integrableOn_exp_mul_complex_Ioi (a := -(s - (-(Complex.I*b))))
      (by simp; linarith) (0:ℝ)
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t _
    show Complex.exp (-(s - (-(Complex.I*b))) * (t:ℂ))
        = Complex.exp (-s * (t:ℂ)) * Complex.exp (-(Complex.I*b) * (t:ℂ))
    rw [← Complex.exp_add]; congr 1; ring
  have hstep : laplaceTransform (fun t => (Real.cos (b * t) : ℂ)) s
      = laplaceTransform (fun t : ℝ => Complex.exp ((Complex.I * b) * t)) s / 2
        + laplaceTransform (fun t : ℝ => Complex.exp (-(Complex.I * b) * t)) s / 2 := by
    have hadded := laplaceTransform_add
      (f := fun t : ℝ => Complex.exp ((Complex.I * b) * t) / 2)
      (g := fun t : ℝ => Complex.exp (-(Complex.I * b) * t) / 2) (s := s)
      (by simpa [mul_div_assoc] using hint1.div_const (2:ℂ))
      (by simpa [mul_div_assoc] using hint2.div_const (2:ℂ))
    rw [show (fun t : ℝ => (Real.cos (b * t) : ℂ))
        = (fun t : ℝ => Complex.exp ((Complex.I * b) * t) / 2
            + Complex.exp (-(Complex.I * b) * t) / 2) from funext hcos]
    rw [hadded]
    have hs1 : laplaceTransform (fun t : ℝ => Complex.exp ((Complex.I * b) * t) / 2) s
        = laplaceTransform (fun t : ℝ => Complex.exp ((Complex.I * b) * t)) s / 2 := by
      rw [show (fun t : ℝ => Complex.exp ((Complex.I * b) * t) / 2)
          = (fun t : ℝ => (2:ℂ)⁻¹ * Complex.exp ((Complex.I * b) * t)) from
          funext (fun t => by ring)]
      rw [laplaceTransform_smul, div_eq_inv_mul]
    have hs2 : laplaceTransform (fun t : ℝ => Complex.exp (-(Complex.I * b) * t) / 2) s
        = laplaceTransform (fun t : ℝ => Complex.exp (-(Complex.I * b) * t)) s / 2 := by
      rw [show (fun t : ℝ => Complex.exp (-(Complex.I * b) * t) / 2)
          = (fun t : ℝ => (2:ℂ)⁻¹ * Complex.exp (-(Complex.I * b) * t)) from
          funext (fun t => by ring)]
      rw [laplaceTransform_smul, div_eq_inv_mul]
    rw [hs1, hs2]
  rw [hstep, hL1, hL2]
  have hsub : s - Complex.I * b ≠ 0 := by
    intro hzero
    have hre0 : s.re = 0 := by
      have := congrArg Complex.re hzero
      simpa using this
    linarith
  have hadd : s - (-(Complex.I * b)) ≠ 0 := by
    intro hzero
    have hre0 : s.re = 0 := by
      have := congrArg Complex.re hzero
      simpa using this
    linarith
  have hne : s ^ 2 + (b:ℂ) ^ 2 ≠ 0 := by
    intro hzero
    apply hsub
    have hfact : (s - Complex.I * b) * (s + Complex.I * b) = 0 := by
      have heq2 : s ^ 2 + (b:ℂ) ^ 2 = (s - Complex.I * b) * (s + Complex.I * b) := by
        have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
        linear_combination (b:ℂ)^2 * hI2
      rw [← heq2, hzero]
    rcases mul_eq_zero.mp hfact with h | h
    · exact h
    · exfalso; apply hadd; rw [show s - (-(Complex.I*b)) = s + Complex.I*b by ring, h]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  linear_combination (s * (b:ℂ)^2 * 2) * hI2

/-- **Laplace transform of sine**, genuine (not merely regularized) version:
`L[sin(bt)](s) = b/(s²+b²)` for `Re s > 0` (§1.14(vii)). Upgrades `laplace_sin`
(stated only for real `s = ε > 0`) to the honest complex-`s` Laplace
transform, by the same `e^{±ibt}` decomposition as `laplaceTransform_cos`. -/
-- no-dlmf: concrete Laplace pair, §1.14 tags properties not this table entry
theorem laplaceTransform_sin (b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    laplaceTransform (fun t => (Real.sin (b * t) : ℂ)) s = (b : ℂ) / (s ^ 2 + (b : ℂ) ^ 2) := by
  have hsin : ∀ t : ℝ, (Real.sin (b * t) : ℂ)
      = Complex.I * Complex.exp (-(Complex.I * b) * t) / 2
        - Complex.I * Complex.exp ((Complex.I * b) * t) / 2 := by
    intro t
    have h2 := Complex.two_sin (x := ((b : ℂ) * (t:ℂ)))
    have hcast : ((Real.sin (b * t) : ℝ) : ℂ) = Complex.sin ((b:ℂ) * (t:ℂ)) := by
      rw [Complex.ofReal_sin (b * t)]
      congr 1
      push_cast; ring
    rw [hcast]
    rw [show (-((b:ℂ) * t)) * Complex.I = -(Complex.I * b) * t by ring,
      show ((b:ℂ) * t) * Complex.I = (Complex.I * b) * t by ring] at h2
    linear_combination h2 / 2
  have hIb : (Complex.I * b).re < s.re := by simp; linarith
  have hnIb : (-(Complex.I * b)).re < s.re := by simp; linarith
  have hL1 := laplaceTransform_exp (Complex.I * b) hIb
  have hL2 := laplaceTransform_exp (-(Complex.I * b)) hnIb
  have hint1 : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * Complex.exp ((Complex.I*b)*t))
      (Ioi 0) := by
    have hbase := integrableOn_exp_mul_complex_Ioi (a := -(s - Complex.I*b))
      (by simp; linarith) (0:ℝ)
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t _
    show Complex.exp (-(s - Complex.I*b) * (t:ℂ))
        = Complex.exp (-s * (t:ℂ)) * Complex.exp ((Complex.I*b) * (t:ℂ))
    rw [← Complex.exp_add]; congr 1; ring
  have hint2 : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * t) * Complex.exp (-(Complex.I*b)*t)) (Ioi 0) := by
    have hbase := integrableOn_exp_mul_complex_Ioi (a := -(s - (-(Complex.I*b))))
      (by simp; linarith) (0:ℝ)
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t _
    show Complex.exp (-(s - (-(Complex.I*b))) * (t:ℂ))
        = Complex.exp (-s * (t:ℂ)) * Complex.exp (-(Complex.I*b) * (t:ℂ))
    rw [← Complex.exp_add]; congr 1; ring
  have hstep : laplaceTransform (fun t => (Real.sin (b * t) : ℂ)) s
      = Complex.I * laplaceTransform (fun t : ℝ => Complex.exp (-(Complex.I * b) * t)) s / 2
        - Complex.I * laplaceTransform (fun t : ℝ => Complex.exp ((Complex.I * b) * t)) s / 2 := by
    have hi1 : IntegrableOn
        (fun t : ℝ => Complex.exp (-s * t) * (Complex.I * Complex.exp (-(Complex.I * b) * t) / 2))
        (Ioi 0) := by
      have hm := hint2.const_mul (Complex.I / 2)
      refine IntegrableOn.congr_fun hm ?_ measurableSet_Ioi
      intro t _
      show (Complex.I / 2) * (Complex.exp (-s * (t:ℂ)) * Complex.exp (-(Complex.I*b) * (t:ℂ)))
          = Complex.exp (-s * (t:ℂ)) * (Complex.I * Complex.exp (-(Complex.I * b) * (t:ℂ)) / 2)
      ring
    have hi2 : IntegrableOn
        (fun t : ℝ => Complex.exp (-s * t)
          * (-(Complex.I * Complex.exp ((Complex.I * b) * t) / 2))) (Ioi 0) := by
      have hm := (hint1.const_mul (Complex.I / 2)).neg
      refine IntegrableOn.congr_fun hm ?_ measurableSet_Ioi
      intro t _
      show -((Complex.I / 2) * (Complex.exp (-s * (t:ℂ)) * Complex.exp ((Complex.I*b) * (t:ℂ))))
          = Complex.exp (-s * (t:ℂ))
            * (-(Complex.I * Complex.exp ((Complex.I * b) * (t:ℂ)) / 2))
      ring
    have hadded := laplaceTransform_add
      (f := fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * b) * t) / 2)
      (g := fun t : ℝ => -(Complex.I * Complex.exp ((Complex.I * b) * t) / 2)) (s := s)
      hi1 hi2
    rw [show (fun t : ℝ => (Real.sin (b * t) : ℂ))
        = (fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * b) * t) / 2
            + -(Complex.I * Complex.exp ((Complex.I * b) * t) / 2)) from
        funext (fun t => by rw [hsin t]; ring)]
    rw [hadded]
    have hs1 : laplaceTransform (fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * b) * t) / 2) s
        = Complex.I * laplaceTransform (fun t : ℝ => Complex.exp (-(Complex.I * b) * t)) s / 2 := by
      rw [show (fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * b) * t) / 2)
          = (fun t : ℝ => (Complex.I / 2) * Complex.exp (-(Complex.I * b) * t)) from
          funext (fun t => by ring)]
      rw [laplaceTransform_smul]
      ring
    have hs2 : laplaceTransform
        (fun t : ℝ => -(Complex.I * Complex.exp ((Complex.I * b) * t) / 2)) s
        = -(Complex.I * laplaceTransform (fun t : ℝ => Complex.exp ((Complex.I * b) * t)) s / 2) := by
      rw [show (fun t : ℝ => -(Complex.I * Complex.exp ((Complex.I * b) * t) / 2))
          = (fun t : ℝ => (-(Complex.I / 2)) * Complex.exp ((Complex.I * b) * t)) from
          funext (fun t => by ring)]
      rw [laplaceTransform_smul]
      ring
    rw [hs1, hs2]
    ring
  rw [hstep, hL1, hL2]
  have hsub : s - Complex.I * b ≠ 0 := by
    intro hzero
    have hre0 : s.re = 0 := by
      have := congrArg Complex.re hzero
      simpa using this
    linarith
  have hadd : s - (-(Complex.I * b)) ≠ 0 := by
    intro hzero
    have hre0 : s.re = 0 := by
      have := congrArg Complex.re hzero
      simpa using this
    linarith
  have hne : s ^ 2 + (b:ℂ) ^ 2 ≠ 0 := by
    intro hzero
    apply hsub
    have hfact : (s - Complex.I * b) * (s + Complex.I * b) = 0 := by
      have heq2 : s ^ 2 + (b:ℂ) ^ 2 = (s - Complex.I * b) * (s + Complex.I * b) := by
        have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
        linear_combination (b:ℂ)^2 * hI2
      rw [← heq2, hzero]
    rcases mul_eq_zero.mp hfact with h | h
    · exact h
    · exfalso; apply hadd; rw [show s - (-(Complex.I*b)) = s + Complex.I*b by ring, h]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  ring_nf
  rw [hI2]
  ring

/-! ### Convolution theorem

Mathlib's whole-line `MeasureTheory.convolution` does not apply directly, but
the `Nonneg` section of `Mathlib.Analysis.Convolution` provides exactly the
*causal* (half-line) convolution: `MeasureTheory.integral_posConvolution`
states `∫₀^∞ ∫₀^x L (F t) (G (x-t)) dt dx = L (∫₀^∞ F) (∫₀^∞ G)` for
`F, G` integrable on `Ioi 0` and `L` a continuous bilinear map — the
triangular-support Fubini is already done upstream. Applying it to the
exponentially weighted integrands `F(t) = e^{-st}f(t)`, `G(t) = e^{-st}g(t)`
with `L` = multiplication, the kernel splitting `e^{-sx} = e^{-st}·e^{-s(x-t)}`
turns `e^{-sx}·(f∗g)(x)` into the causal convolution `(F∗G)(x)`, and the
identity above is precisely `L[f∗g](s) = L[f](s)·L[g](s)`. -/

/-- **Convolution theorem** (DLMF **1.14.31**, with the causal convolution
`(f∗g)(t) = ∫ u in Ioc 0 t, f u * g (t - u)` per DLMF **1.14.30**):
`L[f∗g](s) = L[f](s)·L[g](s)`, given that both transforms converge (their
integrands are integrable on `Ioi 0`) at `s`. Proven by the exponential
splitting `e^{-st} = e^{-su}·e^{-s(t-u)}` plus Mathlib's causal-convolution
integral identity `MeasureTheory.integral_posConvolution`. -/
theorem laplaceTransform_convolution (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * f t) (Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * g t) (Ioi 0)) :
    laplaceTransform (fun t => ∫ u in Ioc (0:ℝ) t, f u * g (t - u)) s
      = laplaceTransform f s * laplaceTransform g s := by
  have key := integral_posConvolution (μ := volume) (ν := volume) hf hg
    (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at key
  simp only [laplaceTransform]
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0:ℝ) ≤ x := le_of_lt (mem_Ioi.mp hx)
  rw [intervalIntegral.integral_of_le hx0, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  have hexp : Complex.exp (-s * (t : ℂ)) * Complex.exp (-s * ((x - t : ℝ) : ℂ))
      = Complex.exp (-s * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc Complex.exp (-s * (x : ℂ)) * (f t * g (x - t))
      = (Complex.exp (-s * (t : ℂ)) * Complex.exp (-s * ((x - t : ℝ) : ℂ)))
          * (f t * g (x - t)) := by rw [hexp]
    _ = Complex.exp (-s * (t : ℂ)) * f t
          * (Complex.exp (-s * ((x - t : ℝ) : ℂ)) * g (x - t)) := by ring

end FLMF.Methods.LaplaceTransform
