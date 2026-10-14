import FLMF.Chapter7.FresnelBasic
import FLMF.Chapter7.FresnelLimit
import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.Faddeeva

/-!
# Complex Fresnel integrals `cfresnelC` and `cfresnelS` (DLMF §7.2)

We define the complex Fresnel cosine and sine integrals
`C(z) = ∫₀ᶻ cos(πu²/2) du = z ∫₀¹ cos(π(t z)²/2) dt` and
`S(z) = ∫₀ᶻ sin(πu²/2) du = z ∫₀¹ sin(π(t z)²/2) dt`, as the entire
extensions of the real `FLMF.Fresnel.fresnelC`/`FLMF.Fresnel.fresnelS`.

Main results:

* `FLMF.Fresnel.cfresnelC_ofReal` : `cfresnelC ↑x = ↑(fresnelC x)` (agreement).
* `FLMF.Fresnel.cfresnelS_ofReal` : `cfresnelS ↑x = ↑(fresnelS x)` (agreement).
* `FLMF.Fresnel.cfresnelC_neg` / `cfresnelS_neg` : odd parity (DLMF 7.4.5).
* `FLMF.Fresnel.cfresnelC_zero` / `cfresnelS_zero` : values at `0`.
-/

namespace FLMF.Fresnel

/-- Complex Fresnel cosine integral `C(z) = ∫₀ᶻ cos(πu²/2) du`, the entire
extension of `FLMF.Fresnel.fresnelC` (DLMF 7.2.7 complex form).

DLMF 7.2.7.
-/
-- DAG: E-7.2.7.
-- Verified: verified
noncomputable def cfresnelC (z : ℂ) : ℂ :=
  z * ∫ t in (0:ℝ)..1, Complex.cos (Real.pi * ((t : ℂ) * z) ^ 2 / 2)

/-- Complex Fresnel sine integral `S(z) = ∫₀ᶻ sin(πu²/2) du` (DLMF 7.2.8 complex form).

DLMF 7.2.8.
-/
-- DAG: E-7.2.8.
-- Verified: verified
noncomputable def cfresnelS (z : ℂ) : ℂ :=
  z * ∫ t in (0:ℝ)..1, Complex.sin (Real.pi * ((t : ℂ) * z) ^ 2 / 2)

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- The complex cosine Fresnel integrand over the real segment to `x` is the cast of
the real integrand: `cos(π(↑t·↑x)²/2) = ↑(cos(π(t·x)²/2))`. -/
theorem cfresnelC_integrand_ofReal (x t : ℝ) :
    Complex.cos (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2)
      = ((Real.cos (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cos]
  push_cast
  ring_nf

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- The complex sine Fresnel integrand over the real segment to `x` is the cast of
the real integrand: `sin(π(↑t·↑x)²/2) = ↑(sin(π(t·x)²/2))`. -/
theorem cfresnelS_integrand_ofReal (x t : ℝ) :
    Complex.sin (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2)
      = ((Real.sin (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sin]
  push_cast
  ring_nf

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- **Agreement with the real `fresnelC`.** `cfresnelC ↑x = ↑(fresnelC x)`. -/
theorem cfresnelC_ofReal (x : ℝ) : cfresnelC (x : ℂ) = ((FLMF.Fresnel.fresnelC x : ℝ) : ℂ) := by
  unfold cfresnelC
  -- Replace the complex integrand by the cast of the real integrand, then pull the cast out.
  have hint : (∫ t in (0:ℝ)..1, Complex.cos (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2))
      = ((∫ t in (0:ℝ)..1, Real.cos (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) := by
    rw [show (∫ t in (0:ℝ)..1, Complex.cos (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2))
          = ∫ t in (0:ℝ)..1, ((Real.cos (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) from
        intervalIntegral.integral_congr (fun t _ => cfresnelC_integrand_ofReal x t)]
    exact intervalIntegral.integral_ofReal
  rw [hint]
  -- Now reduce to the real change of variables `s = t·x`.
  unfold FLMF.Fresnel.fresnelC FLMF.Fresnel.cosArg
  -- `x * ∫ t in 0..1, cos(π(t·x)²/2) = ∫ s in 0..x, cos(πs²/2)`.
  have hcov : x * (∫ t in (0:ℝ)..1, Real.cos (Real.pi * (t * x) ^ 2 / 2))
      = ∫ s in (0:ℝ)..x, Real.cos (Real.pi * s ^ 2 / 2) := by
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := (0:ℝ)) (b := (1:ℝ))
      (f := fun t : ℝ => t * x) (f' := fun _ : ℝ => x)
      (g := fun s : ℝ => Real.cos (Real.pi * s ^ 2 / 2))
      (fun t _ => by simpa using (hasDerivAt_id t).mul_const x)
      (by fun_prop)
      (FLMF.Fresnel.continuous_cosArg)
    simp only [Function.comp] at h
    rw [show (0:ℝ) * x = 0 by ring, show (1:ℝ) * x = x by ring] at h
    rw [← h, intervalIntegral.integral_mul_const]
    ring
  rw [← hcov, Complex.ofReal_mul]

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- **Agreement with the real `fresnelS`.** `cfresnelS ↑x = ↑(fresnelS x)`. -/
theorem cfresnelS_ofReal (x : ℝ) : cfresnelS (x : ℂ) = ((FLMF.Fresnel.fresnelS x : ℝ) : ℂ) := by
  unfold cfresnelS
  have hint : (∫ t in (0:ℝ)..1, Complex.sin (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2))
      = ((∫ t in (0:ℝ)..1, Real.sin (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) := by
    rw [show (∫ t in (0:ℝ)..1, Complex.sin (Real.pi * ((t : ℂ) * (x : ℂ)) ^ 2 / 2))
          = ∫ t in (0:ℝ)..1, ((Real.sin (Real.pi * (t * x) ^ 2 / 2) : ℝ) : ℂ) from
        intervalIntegral.integral_congr (fun t _ => cfresnelS_integrand_ofReal x t)]
    exact intervalIntegral.integral_ofReal
  rw [hint]
  unfold FLMF.Fresnel.fresnelS FLMF.Fresnel.sinArg
  have hcov : x * (∫ t in (0:ℝ)..1, Real.sin (Real.pi * (t * x) ^ 2 / 2))
      = ∫ s in (0:ℝ)..x, Real.sin (Real.pi * s ^ 2 / 2) := by
    have h := intervalIntegral.integral_comp_mul_deriv
      (a := (0:ℝ)) (b := (1:ℝ))
      (f := fun t : ℝ => t * x) (f' := fun _ : ℝ => x)
      (g := fun s : ℝ => Real.sin (Real.pi * s ^ 2 / 2))
      (fun t _ => by simpa using (hasDerivAt_id t).mul_const x)
      (by fun_prop)
      (FLMF.Fresnel.continuous_sinArg)
    simp only [Function.comp] at h
    rw [show (0:ℝ) * x = 0 by ring, show (1:ℝ) * x = x by ring] at h
    rw [← h, intervalIntegral.integral_mul_const]
    ring
  rw [← hcov, Complex.ofReal_mul]

-- no-dlmf: chain link 7.4.5 (assembled in cfresnel_7_4_5)
/-- `cfresnelC` is odd: `cfresnelC (-z) = - cfresnelC z`. -/
theorem cfresnelC_neg (z : ℂ) : cfresnelC (-z) = - cfresnelC z := by
  unfold cfresnelC
  have : (∫ t in (0:ℝ)..1, Complex.cos (Real.pi * ((t : ℂ) * (-z)) ^ 2 / 2))
      = ∫ t in (0:ℝ)..1, Complex.cos (Real.pi * ((t : ℂ) * z) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    congr 2
    ring
  rw [this]
  ring

-- no-dlmf: chain link 7.4.5 (assembled in cfresnel_7_4_5)
/-- `cfresnelS` is odd: `cfresnelS (-z) = - cfresnelS z`. -/
theorem cfresnelS_neg (z : ℂ) : cfresnelS (-z) = - cfresnelS z := by
  unfold cfresnelS
  have : (∫ t in (0:ℝ)..1, Complex.sin (Real.pi * ((t : ℂ) * (-z)) ^ 2 / 2))
      = ∫ t in (0:ℝ)..1, Complex.sin (Real.pi * ((t : ℂ) * z) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    congr 2
    ring
  rw [this]
  ring

/-- **DLMF 7.4.5** (the one-conjunction theorem, complex form). The complex
Fresnel integrals are both odd: `C(-z) = -C(z)` and `S(-z) = -S(z)`.

DLMF 7.4.5.
DAG: E-7.4.5.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_4_5 (z : ℂ) :
    cfresnelC (-z) = - cfresnelC z ∧ cfresnelS (-z) = - cfresnelS z :=
  ⟨cfresnelC_neg z, cfresnelS_neg z⟩

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- `cfresnelC 0 = 0`. -/
@[simp]
theorem cfresnelC_zero : cfresnelC 0 = 0 := by
  unfold cfresnelC
  simp

-- no-dlmf: foundational bridge lemma, no DLMF identity
/-- `cfresnelS 0 = 0`. -/
@[simp]
theorem cfresnelS_zero : cfresnelS 0 = 0 := by
  unfold cfresnelS
  simp

/-! ## R3 bridge identities (complex Fresnel ↔ complex erf / Faddeeva) -/

open FLMF.Error in
/-- Imaginary-argument relations `C(iz) = i·C(z)` and `S(iz) = -i·S(z)`
(DLMF 7.4.6).  Proven: the squared argument turns `i` into `i² = -1`, which the
even cosine (resp. odd sine) absorbs.

DLMF 7.4.6.
DAG: E-7.4.6.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_4_6 (z : ℂ) :
    cfresnelC (Complex.I * z) = Complex.I * cfresnelC z ∧
      cfresnelS (Complex.I * z) = -Complex.I * cfresnelS z := by
  have hsq : ∀ t : ℝ, ((t : ℂ) * (Complex.I * z)) ^ 2 = -((t : ℂ) * z) ^ 2 := fun t => by
    rw [show ((t : ℂ) * (Complex.I * z)) ^ 2 = Complex.I ^ 2 * ((t : ℂ) * z) ^ 2 from by ring,
      Complex.I_sq]; ring
  have harg : ∀ t : ℝ, (Real.pi : ℂ) * (-((t : ℂ) * z) ^ 2) / 2
      = -(Real.pi * ((t : ℂ) * z) ^ 2 / 2) := fun t => by ring
  constructor
  · unfold cfresnelC
    have hcos : ∀ t : ℝ,
        Complex.cos (Real.pi * ((t : ℂ) * (Complex.I * z)) ^ 2 / 2)
          = Complex.cos (Real.pi * ((t : ℂ) * z) ^ 2 / 2) := fun t => by
      rw [hsq t, harg t, Complex.cos_neg]
    rw [intervalIntegral.integral_congr (fun t _ => hcos t)]
    ring
  · unfold cfresnelS
    have hsin : ∀ t : ℝ,
        Complex.sin (Real.pi * ((t : ℂ) * (Complex.I * z)) ^ 2 / 2)
          = -Complex.sin (Real.pi * ((t : ℂ) * z) ^ 2 / 2) := fun t => by
      rw [hsq t, harg t, Complex.sin_neg]
    rw [intervalIntegral.integral_congr (fun t _ => hsin t), intervalIntegral.integral_neg]
    ring

open FLMF.Error in
/-- `C(z) ± iS(z) = ½(1±i)·erf(ζ)` with `ζ = ½√π(1∓i)z` (DLMF 7.5.8, both
signs; the first conjunct is the upper-sign case, the second the lower-sign
case).

DLMF 7.5.8.
DAG: E-7.5.8.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_8 (z : ℂ) :
    (cfresnelC z + Complex.I * cfresnelS z
      = (1 / 2) * (1 + Complex.I) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z)) ∧
    (cfresnelC z - Complex.I * cfresnelS z
      = (1 / 2) * (1 - Complex.I) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)) := by
  have hupper : ∀ w : ℂ, cfresnelC w + Complex.I * cfresnelS w
      = (1 / 2) * (1 + Complex.I) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * w) := by
    intro w
    unfold cfresnelC cfresnelS cerf
    set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * w with hζdef
    have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi:ℂ) := by
      norm_cast; exact Real.sq_sqrt Real.pi_pos.le
    have h1mI2 : (1 - Complex.I) ^ 2 = -2 * Complex.I := by linear_combination Complex.I_sq
    have hsqrtpi_ne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hζsq : ζ ^ 2 = -(Complex.I * (Real.pi * w ^ 2 / 2)) := by
      rw [hζdef]
      have expand : ((1/2) * (Real.sqrt Real.pi:ℂ) * (1-Complex.I) * w)^2
          = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1-Complex.I)^2 * w^2 := by ring
      rw [expand, hpi2, h1mI2]; ring
    have hcoef : (2 / Real.sqrt Real.pi : ℂ) * ζ = (1 - Complex.I) * w := by
      rw [hζdef]; field_simp
    have hintegrand : ∀ t : ℝ, Complex.exp (-((t:ℂ)*ζ)^2)
        = Complex.cos (Real.pi * ((t:ℂ)*w)^2/2) + Complex.I * Complex.sin (Real.pi * ((t:ℂ)*w)^2/2) := by
      intro t
      have h1 : -((t:ℂ)*ζ)^2 = (Real.pi * ((t:ℂ)*w)^2/2) * Complex.I := by
        have heq : ((t:ℂ)*ζ)^2 = (t:ℂ)^2 * ζ^2 := by ring
        rw [heq, hζsq]; ring
      rw [h1, Complex.exp_mul_I]; ring
    have hcont_cos : Continuous (fun t : ℝ => Complex.cos (Real.pi * ((t:ℂ)*w)^2/2)) := by fun_prop
    have hcont_sin : Continuous (fun t : ℝ => Complex.sin (Real.pi * ((t:ℂ)*w)^2/2)) := by fun_prop
    have hint_eq : (∫ t in (0:ℝ)..1, Complex.exp (-((t:ℂ)*ζ)^2))
        = (∫ t in (0:ℝ)..1, Complex.cos (Real.pi*((t:ℂ)*w)^2/2))
          + Complex.I * (∫ t in (0:ℝ)..1, Complex.sin (Real.pi*((t:ℂ)*w)^2/2)) := by
      rw [intervalIntegral.integral_congr (fun t _ => hintegrand t)]
      rw [intervalIntegral.integral_add (hcont_cos.intervalIntegrable 0 1)
          ((hcont_sin.intervalIntegrable 0 1).const_mul Complex.I)]
      rw [intervalIntegral.integral_const_mul]
    rw [hint_eq]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    set A : ℂ := ∫ t in (0:ℝ)..1, Complex.cos (Real.pi*((t:ℂ)*w)^2/2) with hAdef
    set B : ℂ := ∫ t in (0:ℝ)..1, Complex.sin (Real.pi*((t:ℂ)*w)^2/2) with hBdef
    rw [hcoef]
    linear_combination ((1:ℂ)/2 * (w*A + Complex.I*w*B)) * hI2
  refine ⟨hupper z, ?_⟩
  -- Lower sign from the upper sign at `i·z`, via the imaginary-argument
  -- relations `C(iz) = i·C(z)`, `S(iz) = -i·S(z)` (DLMF 7.4.6).
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h746 := cfresnel_7_4_6 z
  have h := hupper (Complex.I * z)
  rw [h746.1, h746.2] at h
  have harg : (1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * (Complex.I * z)
      = (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z := by
    linear_combination (-(1 / 2) * (Real.sqrt Real.pi : ℂ) * z) * hI2
  rw [harg] at h
  linear_combination (-Complex.I) * h + (cfresnelC z - Complex.I * cfresnelS z
      - (1 / 2) * cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)) * hI2

open FLMF.Error in
/-- `C(z) ± iS(z) = ½(1±i)(1 - e^{±½πiz²}·w(iζ))` with `ζ = ½√π(1∓i)z`
(DLMF 7.5.9, both signs; the first conjunct is the upper-sign case, the second
the lower-sign case).

DLMF 7.5.9.
DAG: E-7.5.9.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_9 (z : ℂ) :
    (cfresnelC z + Complex.I * cfresnelS z
      = (1 / 2) * (1 + Complex.I) *
          (1 - Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2) *
            faddeeva (Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z)))) ∧
    (cfresnelC z - Complex.I * cfresnelS z
      = (1 / 2) * (1 - Complex.I) *
          (1 - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2)) *
            faddeeva (Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)))) := by
  constructor
  · rw [(cfresnel_7_5_8 z).1]
    set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z with hζdef
    have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi:ℂ) := by
      norm_cast; exact Real.sq_sqrt Real.pi_pos.le
    have h1mI2 : (1 - Complex.I) ^ 2 = -2 * Complex.I := by linear_combination Complex.I_sq
    have hζsq : ζ ^ 2 = -(Complex.I * (Real.pi * z ^ 2 / 2)) := by
      rw [hζdef]
      have expand : ((1/2) * (Real.sqrt Real.pi:ℂ) * (1-Complex.I) * z)^2
          = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1-Complex.I)^2 * z^2 := by ring
      rw [expand, hpi2, h1mI2]; ring
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hfaddeeva : faddeeva (Complex.I * ζ) = Complex.exp (-(Complex.I*(Real.pi*z^2/2))) * cerfc ζ := by
      unfold faddeeva
      have hnegsq : -(Complex.I*ζ)^2 = ζ^2 := by
        have h : (Complex.I*ζ)^2 = Complex.I^2*ζ^2 := by ring
        rw [h, hI2]; ring
      have hneg : -(Complex.I*(Complex.I*ζ)) = ζ := by
        have h : Complex.I*(Complex.I*ζ) = Complex.I^2*ζ := by ring
        rw [h, hI2]; ring
      rw [hnegsq, hneg, hζsq]
    have hexp_prod : Complex.exp ((1/2)*Real.pi*Complex.I*z^2) * Complex.exp (-(Complex.I*(Real.pi*z^2/2))) = 1 := by
      rw [← Complex.exp_add, show (1/2)*Real.pi*Complex.I*z^2 + -(Complex.I*(Real.pi*z^2/2)) = 0 from by ring,
        Complex.exp_zero]
    rw [hfaddeeva, ← mul_assoc, hexp_prod, one_mul]
    unfold cerfc
    ring
  · rw [(cfresnel_7_5_8 z).2]
    set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z with hζdef
    have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi:ℂ) := by
      norm_cast; exact Real.sq_sqrt Real.pi_pos.le
    have h1pI2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by linear_combination Complex.I_sq
    have hζsq : ζ ^ 2 = Complex.I * (Real.pi * z ^ 2 / 2) := by
      rw [hζdef]
      have expand : ((1/2) * (Real.sqrt Real.pi:ℂ) * (1+Complex.I) * z)^2
          = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1+Complex.I)^2 * z^2 := by ring
      rw [expand, hpi2, h1pI2]; ring
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hfaddeeva : faddeeva (Complex.I * ζ) = Complex.exp (Complex.I*(Real.pi*z^2/2)) * cerfc ζ := by
      unfold faddeeva
      have hnegsq : -(Complex.I*ζ)^2 = ζ^2 := by
        have h : (Complex.I*ζ)^2 = Complex.I^2*ζ^2 := by ring
        rw [h, hI2]; ring
      have hneg : -(Complex.I*(Complex.I*ζ)) = ζ := by
        have h : Complex.I*(Complex.I*ζ) = Complex.I^2*ζ := by ring
        rw [h, hI2]; ring
      rw [hnegsq, hneg, hζsq]
    have hexp_prod : Complex.exp (-((1/2)*Real.pi*Complex.I*z^2)) * Complex.exp (Complex.I*(Real.pi*z^2/2)) = 1 := by
      rw [← Complex.exp_add, show -((1/2)*Real.pi*Complex.I*z^2) + Complex.I*(Real.pi*z^2/2) = 0 from by ring,
        Complex.exp_zero]
    rw [hfaddeeva, ← mul_assoc, hexp_prod, one_mul]
    unfold cerfc
    ring

/-! ## R3b — complex Fresnel auxiliary functions `f`, `g` -/

/-- Complex Fresnel auxiliary `f(z) = (½ - S(z))cos(πz²/2) - (½ - C(z))sin(πz²/2)`
(DLMF 7.2.10 complex form), the entire extension of `FLMF.Error.fresnelAuxF`.

DLMF 7.2.10.
-/
-- DAG: E-7.2.10.
-- Verified: verified
noncomputable def cfresnelAuxF (z : ℂ) : ℂ :=
  (1 / 2 - cfresnelS z) * Complex.cos (Real.pi * z ^ 2 / 2)
    - (1 / 2 - cfresnelC z) * Complex.sin (Real.pi * z ^ 2 / 2)

/-- Complex Fresnel auxiliary `g(z) = (½ - C(z))cos(πz²/2) + (½ - S(z))sin(πz²/2)`
(DLMF 7.2.11 complex form).

DLMF 7.2.11.
-/
-- DAG: E-7.2.11.
-- Verified: verified
noncomputable def cfresnelAuxG (z : ℂ) : ℂ :=
  (1 / 2 - cfresnelC z) * Complex.cos (Real.pi * z ^ 2 / 2)
    + (1 / 2 - cfresnelS z) * Complex.sin (Real.pi * z ^ 2 / 2)

/-- Imaginary-argument relations for the auxiliaries (DLMF 7.4.7):
`f(iz) = ½(1+i)e^{-iπz²/2} - i f(z)` and `g(iz) = ½(1-i)e^{-iπz²/2} + i g(z)`.
(The DLMF `(1/√2)e^{iπ/4-iπz²/2}` prefactor equals `½(1+i)e^{-iπz²/2}`.)

DLMF 7.4.7.
DAG: E-7.4.7.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_4_7 (z : ℂ) :
    cfresnelAuxF (Complex.I * z)
        = (1 / 2) * (1 + Complex.I) * Complex.exp (-(Complex.I * Real.pi * z ^ 2 / 2))
          - Complex.I * cfresnelAuxF z ∧
      cfresnelAuxG (Complex.I * z)
        = (1 / 2) * (1 - Complex.I) * Complex.exp (-(Complex.I * Real.pi * z ^ 2 / 2))
          + Complex.I * cfresnelAuxG z := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  set θ : ℂ := (Real.pi:ℂ) * z^2 / 2 with hθdef
  have hsqarg : Real.pi * (Complex.I * z) ^ 2 / 2 = -θ := by
    rw [hθdef]
    have h : (Complex.I*z)^2 = Complex.I^2*z^2 := by ring
    rw [h, hI2]; ring
  have hcosarg : Complex.cos (Real.pi * (Complex.I * z) ^ 2 / 2) = Complex.cos θ := by
    rw [hsqarg, Complex.cos_neg]
  have hsinarg : Complex.sin (Real.pi * (Complex.I * z) ^ 2 / 2) = -Complex.sin θ := by
    rw [hsqarg, Complex.sin_neg]
  have h746 := cfresnel_7_4_6 z
  have hC : cfresnelC (Complex.I * z) = Complex.I * cfresnelC z := h746.1
  have hS : cfresnelS (Complex.I * z) = -Complex.I * cfresnelS z := h746.2
  have hexpneg : Complex.exp (-(Complex.I * Real.pi * z ^ 2 / 2)) = Complex.cos θ - Complex.I * Complex.sin θ := by
    have harg : -(Complex.I * Real.pi * z ^ 2 / 2) = (-θ) * Complex.I := by rw [hθdef]; ring
    rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have hθeq : (Real.pi : ℂ) * z ^ 2 / 2 = θ := hθdef.symm
  constructor
  · unfold cfresnelAuxF
    rw [hC, hS, hcosarg, hsinarg, hexpneg, hθeq]
    linear_combination (Complex.sin θ / 2) * hI2
  · unfold cfresnelAuxG
    rw [hC, hS, hcosarg, hsinarg, hexpneg, hθeq]
    linear_combination (-Complex.sin θ / 2) * hI2

/-- `e^{±½πiz²}(g(z) ± i f(z)) = ½(1±i) - (C(z) ± iS(z))` (DLMF 7.5.6, both
signs; the first conjunct is the upper-sign case, the second the lower-sign
case).

DLMF 7.5.6.
DAG: E-7.5.6.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_6 (z : ℂ) :
    (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2) * (cfresnelAuxG z + Complex.I * cfresnelAuxF z)
      = (1 / 2) * (1 + Complex.I) - (cfresnelC z + Complex.I * cfresnelS z)) ∧
    (Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2)) * (cfresnelAuxG z - Complex.I * cfresnelAuxF z)
      = (1 / 2) * (1 - Complex.I) - (cfresnelC z - Complex.I * cfresnelS z)) := by
  unfold cfresnelAuxG cfresnelAuxF
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  set θ : ℂ := (Real.pi:ℂ)*z^2/2 with hθdef
  constructor
  · have hexp1 : Complex.exp ((1/2)*Real.pi*Complex.I*z^2) = Complex.exp (θ*Complex.I) := by
      congr 1; rw [hθdef]; ring
    have hexpneg : Complex.cos θ - Complex.I * Complex.sin θ = Complex.exp (-θ*Complex.I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
    have hfactor : (1/2 - cfresnelC z)*Complex.cos θ + (1/2 - cfresnelS z)*Complex.sin θ
        + Complex.I*((1/2 - cfresnelS z)*Complex.cos θ - (1/2 - cfresnelC z)*Complex.sin θ)
        = (Complex.cos θ - Complex.I*Complex.sin θ) * ((1/2 - cfresnelC z) + Complex.I*(1/2 - cfresnelS z)) := by
      linear_combination ((1/2 - cfresnelS z)*Complex.sin θ) * hI2
    rw [hfactor, hexpneg, hexp1, ← mul_assoc, ← Complex.exp_add,
      show θ*Complex.I + (-θ*Complex.I) = 0 from by ring, Complex.exp_zero, one_mul]
    ring
  · have hexp1 : Complex.exp (-((1/2)*Real.pi*Complex.I*z^2)) = Complex.exp (-θ*Complex.I) := by
      congr 1; rw [hθdef]; ring
    have hexppos : Complex.cos θ + Complex.I * Complex.sin θ = Complex.exp (θ*Complex.I) := by
      rw [Complex.exp_mul_I]; ring
    have hfactor : (1/2 - cfresnelC z)*Complex.cos θ + (1/2 - cfresnelS z)*Complex.sin θ
        - Complex.I*((1/2 - cfresnelS z)*Complex.cos θ - (1/2 - cfresnelC z)*Complex.sin θ)
        = (Complex.cos θ + Complex.I*Complex.sin θ) * ((1/2 - cfresnelC z) - Complex.I*(1/2 - cfresnelS z)) := by
      linear_combination ((1/2 - cfresnelS z)*Complex.sin θ) * hI2
    rw [hfactor, hexppos, hexp1, ← mul_assoc, ← Complex.exp_add,
      show -θ*Complex.I + θ*Complex.I = 0 from by ring, Complex.exp_zero, one_mul]
    ring

open FLMF.Error in
/-- `g(z) ± i f(z) = ½(1±i)·e^{ζ²}·erfc(ζ)` with `ζ = ½√π(1∓i)z` (DLMF 7.5.10,
both signs; the first conjunct is the upper-sign case, the second the
lower-sign case).

DLMF 7.5.10.
DAG: E-7.5.10.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_10 (z : ℂ) :
    (cfresnelAuxG z + Complex.I * cfresnelAuxF z
      = (1 / 2) * (1 + Complex.I)
          * Complex.exp (((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z) ^ 2)
          * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z)) ∧
    (cfresnelAuxG z - Complex.I * cfresnelAuxF z
      = (1 / 2) * (1 - Complex.I)
          * Complex.exp (((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ^ 2)
          * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)) := by
  -- Combines `cfresnel_7_5_6` (the `e^{±½πiz²}(g±if) = ½(1±i)-(C±iS)` identity) with
  -- `cfresnel_7_5_8` (`C±iS = ½(1±i)·erf ζ`); note this theorem is declared before
  -- `cfresnelScriptF`/`cfresnel_7_5_5` in the file, so it is proved directly rather
  -- than routed through the later `cfresnel_7_5_5`.
  constructor
  · have h756 := (cfresnel_7_5_6 z).1
    have h758 := (cfresnel_7_5_8 z).1
    set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z with hζdef
    have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi:ℂ) := by
      norm_cast; exact Real.sq_sqrt Real.pi_pos.le
    have h1mI2 : (1 - Complex.I) ^ 2 = -2 * Complex.I := by linear_combination Complex.I_sq
    have hζsq : ζ ^ 2 = -(Complex.I * (Real.pi * z ^ 2 / 2)) := by
      rw [hζdef]
      have expand : ((1/2) * (Real.sqrt Real.pi:ℂ) * (1-Complex.I) * z)^2
          = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1-Complex.I)^2 * z^2 := by ring
      rw [expand, hpi2, h1mI2]; ring
    have hexp_eq : Complex.exp (ζ^2) = Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) := by
      rw [hζsq]; congr 1; ring
    have hexp_prod2 : Complex.exp (ζ^2) * Complex.exp ((1/2)*Real.pi*Complex.I*z^2) = 1 := by
      rw [hexp_eq, ← Complex.exp_add,
        show -(((1:ℂ)/2)*Real.pi*Complex.I*z^2) + (1/2)*Real.pi*Complex.I*z^2 = 0 from by ring, Complex.exp_zero]
    have hgf : cfresnelAuxG z + Complex.I * cfresnelAuxF z
        = Complex.exp (ζ^2) * (Complex.exp ((1/2)*Real.pi*Complex.I*z^2) * (cfresnelAuxG z + Complex.I*cfresnelAuxF z)) := by
      rw [← mul_assoc, hexp_prod2, one_mul]
    rw [hgf, h756, h758]
    unfold cerfc
    ring
  · have h756 := (cfresnel_7_5_6 z).2
    have h758 := (cfresnel_7_5_8 z).2
    set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z with hζdef
    have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi:ℂ) := by
      norm_cast; exact Real.sq_sqrt Real.pi_pos.le
    have h1pI2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by linear_combination Complex.I_sq
    have hζsq : ζ ^ 2 = Complex.I * (Real.pi * z ^ 2 / 2) := by
      rw [hζdef]
      have expand : ((1/2) * (Real.sqrt Real.pi:ℂ) * (1+Complex.I) * z)^2
          = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1+Complex.I)^2 * z^2 := by ring
      rw [expand, hpi2, h1pI2]; ring
    have hexp_prod2 : Complex.exp (ζ^2) * Complex.exp (-((1/2)*Real.pi*Complex.I*z^2)) = 1 := by
      rw [hζsq, ← Complex.exp_add,
        show Complex.I*(Real.pi*z^2/2) + -((1/2)*Real.pi*Complex.I*z^2) = 0 from by ring, Complex.exp_zero]
    have hgf : cfresnelAuxG z - Complex.I * cfresnelAuxF z
        = Complex.exp (ζ^2) * (Complex.exp (-((1/2)*Real.pi*Complex.I*z^2)) * (cfresnelAuxG z - Complex.I*cfresnelAuxF z)) := by
      rw [← mul_assoc, hexp_prod2, one_mul]
    rw [hgf, h756, h758]
    unfold cerfc
    ring

/-! ## R3c — the complex Fresnel integral ℱ and its integral representations -/

-- no-dlmf: support def for the 7.5.7 display; surfaced at `cfresnel_7_5_7`
/-- The auxiliary complex variable `ζ = ½√π(1-i)z` (DLMF 7.5.7, upper sign).

-/
noncomputable def fresnelZeta (z : ℂ) : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z

-- no-dlmf: support def for the 7.5.7 display; surfaced at `cfresnel_7_5_7`
/-- The auxiliary complex variable `ζ = ½√π(1+i)z` (DLMF 7.5.7, lower sign).

-/
noncomputable def fresnelZetaLower (z : ℂ) : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z

-- no-dlmf: encodes ℱ via the 7.5.2 relation (display surfaced at `cfresnel_7_5_2`); DLMF's definition of ℱ is 7.2.6 (`cfresnel_7_2_6`)
/-- The complex Fresnel integral `ℱ(z) = ½(1+i) - (C(z)+iS(z))` (DLMF 7.5.2 / 7.2.6).

-/
noncomputable def cfresnelScriptF (z : ℂ) : ℂ := (1 / 2) * (1 + Complex.I) - (cfresnelC z + Complex.I * cfresnelS z)

/-- The complex Fresnel integral in terms of `C` and `S`:
`C(z)+iS(z) = ½(1+i) - ℱ(z)` (DLMF 7.5.2).

DLMF 7.5.2.
DAG: E-7.5.2.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_2 (z : ℂ) :
    cfresnelC z + Complex.I * cfresnelS z = (1/2)*(1+Complex.I) - cfresnelScriptF z := by
  rw [cfresnelScriptF]; ring

/-- The auxiliary complex variable `ζ = ½√π(1∓i)z` (DLMF 7.5.7, both sign
choices: `fresnelZeta` realizes the upper sign `(1-i)`, `fresnelZetaLower`
the lower sign `(1+i)`).

DLMF 7.5.7.
DAG: E-7.5.7.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_7 (z : ℂ) :
    fresnelZeta z = (1/2)*(Real.sqrt Real.pi : ℂ)*(1 - Complex.I)*z ∧
      fresnelZetaLower z = (1/2)*(Real.sqrt Real.pi : ℂ)*(1 + Complex.I)*z :=
  ⟨rfl, rfl⟩

/-- `e^{-½πiz²}ℱ(z) = g(z) + i f(z)` (DLMF 7.5.5, upper sign).

DLMF 7.5.5.
DAG: E-7.5.5.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_5_5 (z : ℂ) :
    Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) * cfresnelScriptF z
      = cfresnelAuxG z + Complex.I * cfresnelAuxF z := by
  have h756 := (cfresnel_7_5_6 z).1
  unfold cfresnelScriptF
  have hexp_prod : Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) * Complex.exp ((1/2)*Real.pi*Complex.I*z^2) = 1 := by
    rw [← Complex.exp_add, show -(((1:ℂ)/2)*Real.pi*Complex.I*z^2) + (1/2)*Real.pi*Complex.I*z^2 = 0 from by ring,
      Complex.exp_zero]
  calc Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) * ((1/2)*(1+Complex.I) - (cfresnelC z + Complex.I*cfresnelS z))
      = Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) * (Complex.exp ((1/2)*Real.pi*Complex.I*z^2) * (cfresnelAuxG z + Complex.I*cfresnelAuxF z)) := by rw [h756]
    _ = (Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) * Complex.exp ((1/2)*Real.pi*Complex.I*z^2)) * (cfresnelAuxG z + Complex.I*cfresnelAuxF z) := by ring
    _ = cfresnelAuxG z + Complex.I*cfresnelAuxF z := by rw [hexp_prod]; ring

/-! ### Support lemmas for the ray integral `∫₀^∞ e^{½πi(z+s)²} ds` (DLMF 7.2.6)

The route to `cfresnel_7_2_6` is derivative matching on the upper half-plane: both
`ℱ(z)` and the ray integral `F(z) = ∫₀^∞ e^{½πi(z+s)²} ds` are differentiable on
`Im z > 0` with the same derivative `-e^{½πiz²}` (for `ℱ` via the keystone
`cfresnel_7_5_8` and `hasDerivAt_cerf`; for `F` by differentiation under the
integral plus the FTC in `s`), so their difference is constant on the convex upper
half-plane; along the imaginary axis both tend to `0`, pinning the constant to `0`. -/

open MeasureTheory Filter
open scoped Topology

-- no-dlmf: support lemma (norm of the ray integrand), no DLMF identity
/-- `‖e^{½πi(w+s)²}‖ = e^{-π(Re w + s)·Im w}`. -/
theorem norm_exp_fresnelRay (w : ℂ) (s : ℝ) :
    ‖Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2))‖
      = Real.exp (-(Real.pi * (w.re + s) * w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq]
  ring

-- no-dlmf: support lemma (complex derivative of the ray integrand), no DLMF identity
/-- The ray integrand `u ↦ e^{½πi(u+a)²}` has complex derivative
`πi(w+a)·e^{½πi(w+a)²}` at `w`. -/
theorem hasDerivAt_exp_fresnelRay (a w : ℂ) :
    HasDerivAt (fun u : ℂ => Complex.exp ((1/2)*Real.pi*Complex.I*((u + a)^2)))
      (Real.pi*Complex.I*(w + a) * Complex.exp ((1/2)*Real.pi*Complex.I*((w + a)^2))) w := by
  have hinner : HasDerivAt (fun u : ℂ => (1/2)*Real.pi*Complex.I*((u + a)^2))
      (Real.pi*Complex.I*(w + a)) w := by
    have h := (((hasDerivAt_id w).add_const a).pow 2).const_mul ((1/2)*(Real.pi:ℂ)*Complex.I)
    convert h using 1
    simp only [id_eq]
    ring
  have h := hinner.cexp
  convert h using 1
  ring

-- no-dlmf: support lemma (elementary exponential integral), no DLMF identity
/-- `∫₀^∞ e^{-bs} ds = 1/b` for `b > 0`. -/
theorem integral_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) :
    ∫ s in Set.Ioi (0:ℝ), Real.exp (-(b*s)) = 1/b := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hb
  simp only [mul_zero] at h
  calc ∫ s in Set.Ioi (0:ℝ), Real.exp (-(b*s))
      = b⁻¹ • ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) := h
    _ = 1/b := by rw [integral_exp_neg_Ioi_zero]; simp [one_div]

-- no-dlmf: support lemma (integrability of the ray integrand), no DLMF identity
/-- For `Im w > 0` the ray integrand is integrable on `(0,∞)`:
`‖e^{½πi(w+s)²}‖ = e^{-π(Re w)(Im w)}·e^{-π(Im w)s}` decays exponentially. -/
theorem integrableOn_exp_fresnelRay {w : ℂ} (hw : 0 < w.im) :
    IntegrableOn (fun s : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2)))
      (Set.Ioi 0) := by
  have hb : 0 < Real.pi * w.im := by positivity
  refine Integrable.mono' (g := fun s : ℝ =>
      Real.exp (-(Real.pi * w.re * w.im)) * Real.exp (-(Real.pi * w.im) * s))
    ((exp_neg_integrableOn_Ioi 0 hb).const_mul _)
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  rw [norm_exp_fresnelRay]
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply le_of_eq
  ring

-- no-dlmf: support lemma (decay of the ray integrand at `+∞`), no DLMF identity
/-- For `Im w > 0` the ray integrand tends to `0` as `s → ∞`. -/
theorem tendsto_exp_fresnelRay_atTop {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun s : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun s => le_of_eq (norm_exp_fresnelRay w s))
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun s : ℝ => Real.pi * w.im * s) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_id
  have h2 : Tendsto (fun s : ℝ => Real.pi * w.im * s + Real.pi * w.re * w.im) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h1
  have h3 := tendsto_neg_atTop_atBot.comp h2
  refine h3.congr fun s => ?_
  simp only [Function.comp_apply]
  ring

-- no-dlmf: support lemma (differentiation of the ray integral), no DLMF identity
/-- On the upper half-plane, the ray integral `F(w) = ∫₀^∞ e^{½πi(w+s)²} ds`
has derivative `-e^{½πiz²}`: differentiation under the integral sign (with a
locally uniform exponential dominant on a ball where `Im w > Im z / 2`) turns the
`z`-derivative of the integrand into its `s`-derivative, and the FTC on `(0,∞)`
evaluates the resulting integral to `-e^{½πiz²}`. -/
theorem hasDerivAt_fresnelRayIntegral {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2)))
      (-Complex.exp ((1/2)*Real.pi*Complex.I*z^2)) z := by
  set ε : ℝ := z.im / 2 with hε
  have hεpos : 0 < ε := half_pos hz
  set c : ℝ := Real.pi * (z.im / 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  -- facts about points in the ball
  have hball : ∀ w ∈ Metric.ball z ε, z.im / 2 < w.im ∧ w.im < z.im + ε ∧ |w.re| < ‖z‖ + ε := by
    intro w hw
    have hdist : ‖w - z‖ < ε := mem_ball_iff_norm.mp hw
    have him : |w.im - z.im| < ε :=
      lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - z)) hdist
    have him' := abs_lt.mp him
    refine ⟨by linarith [him'.1], by linarith [him'.2], ?_⟩
    have : ‖w‖ < ‖z‖ + ε := by
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ < ‖z‖ + ε := by linarith
    exact lt_of_le_of_lt (Complex.abs_re_le_norm w) this
  set M : ℝ := (‖z‖ + ε) * (z.im + ε) with hM
  set K : ℝ := (Real.pi * (‖z‖ + ε) + 2 * Real.pi / c) * Real.exp (Real.pi * M) with hK
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (s : ℝ) => Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2)))
    (F' := fun (w : ℂ) (s : ℝ) =>
      Real.pi*Complex.I*(w + (s:ℂ)) * Complex.exp ((1/2)*Real.pi*Complex.I*((w + (s:ℂ))^2)))
    (μ := volume.restrict (Set.Ioi 0))
    (x₀ := z)
    (bound := fun s => K * Real.exp (-(c/2) * s))
    (Metric.ball_mem_nhds z hεpos)
    (Filter.Eventually.of_forall fun w => Continuous.aestronglyMeasurable (by fun_prop))
    (integrableOn_exp_fresnelRay hz)
    (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ ?_
    (Filter.Eventually.of_forall fun s w _ => hasDerivAt_exp_fresnelRay (s:ℂ) w)
  · -- rewrite the derivative integral via the FTC on (0,∞)
    obtain ⟨hint, hderiv⟩ := hmain
    have hkey : (∫ s in Set.Ioi (0:ℝ),
        Real.pi*Complex.I*(z + (s:ℂ)) * Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2)))
        = -Complex.exp ((1/2)*Real.pi*Complex.I*z^2) := by
      have hderiv_s : ∀ s : ℝ, s ∈ Set.Ioi (0:ℝ) →
          HasDerivAt (fun t : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*((z + (t:ℂ))^2)))
            (Real.pi*Complex.I*(z + (s:ℂ))
              * Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2))) s := by
        intro s _
        have h := (hasDerivAt_exp_fresnelRay z ((s:ℝ):ℂ)).comp_ofReal
        have hfe : (fun t : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*(((t:ℂ) + z)^2)))
            = fun t : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*((z + (t:ℂ))^2)) := by
          funext t; rw [add_comm]
        rw [hfe] at h
        convert h using 1
        rw [add_comm z ((s:ℝ):ℂ)]
      have hcont : ContinuousWithinAt
          (fun t : ℝ => Complex.exp ((1/2)*Real.pi*Complex.I*((z + (t:ℂ))^2))) (Set.Ici 0) 0 :=
        Continuous.continuousWithinAt (by fun_prop)
      have hres := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv_s hint
        (tendsto_exp_fresnelRay_atTop hz)
      rw [hres]
      norm_num
    rw [hkey] at hderiv
    exact hderiv
  · -- the uniform bound on the ball
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    obtain ⟨him_lo, him_hi, hre⟩ := hball w hw
    have hs0 : (0:ℝ) < s := hs
    have hwim : 0 ≤ w.im := by linarith
    rw [norm_mul, norm_exp_fresnelRay]
    have h1 : ‖Real.pi*Complex.I*(w + (s:ℂ))‖ ≤ Real.pi * (‖z‖ + ε + s) := by
      rw [norm_mul, norm_mul]
      simp only [Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      have : ‖w + (s:ℂ)‖ ≤ ‖w‖ + s := by
        calc ‖w + (s:ℂ)‖ ≤ ‖w‖ + ‖(s:ℂ)‖ := norm_add_le _ _
          _ = ‖w‖ + |s| := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ = ‖w‖ + s := by rw [abs_of_pos hs0]
      have hwn : ‖w‖ < ‖z‖ + ε := by
        have hdist : ‖w - z‖ < ε := mem_ball_iff_norm.mp hw
        calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
          _ < ‖z‖ + ε := by linarith
      nlinarith [Real.pi_pos]
    have h2 : Real.exp (-(Real.pi * (w.re + s) * w.im))
        ≤ Real.exp (Real.pi * M) * Real.exp (-c * s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsplit : -(Real.pi * (w.re + s) * w.im)
          = -(Real.pi * w.re * w.im) + (-(Real.pi * w.im) * s) := by ring
      rw [hsplit]
      have hb1 : -(Real.pi * w.re * w.im) ≤ Real.pi * M := by
        have habs : -(w.re * w.im) ≤ |w.re| * w.im := by
          nlinarith [neg_le_abs w.re, hwim]
        have hM' : |w.re| * w.im ≤ M := by
          rw [hM]
          apply mul_le_mul hre.le him_hi.le hwim (by positivity)
        calc -(Real.pi * w.re * w.im) = Real.pi * (-(w.re * w.im)) := by ring
          _ ≤ Real.pi * (|w.re| * w.im) := by
              apply mul_le_mul_of_nonneg_left habs Real.pi_pos.le
          _ ≤ Real.pi * M := by
              apply mul_le_mul_of_nonneg_left hM' Real.pi_pos.le
      have hb2 : -(Real.pi * w.im) * s ≤ -c * s := by
        apply mul_le_mul_of_nonneg_right _ hs0.le
        rw [hc]
        nlinarith [Real.pi_pos]
      linarith
    calc ‖Real.pi*Complex.I*(w + (s:ℂ))‖ * Real.exp (-(Real.pi * (w.re + s) * w.im))
        ≤ Real.pi * (‖z‖ + ε + s) * (Real.exp (Real.pi * M) * Real.exp (-c * s)) := by
          apply mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ K * Real.exp (-(c/2) * s) := by
          rw [hK]
          have hexp_split : Real.exp (-c * s)
              = Real.exp (-(c/2) * s) * Real.exp (-(c/2) * s) := by
            rw [← Real.exp_add]; ring_nf
          have hs_le : s * Real.exp (-(c/2) * s) ≤ 2 / c := by
            have hx : (c/2) * s ≤ Real.exp ((c/2) * s) :=
              le_trans (by linarith [Real.add_one_le_exp ((c/2)*s)]) (le_refl _)
            rw [show -(c/2) * s = -((c/2) * s) by ring, Real.exp_neg]
            rw [le_div_iff₀ hcpos]
            calc s * (Real.exp ((c/2)*s))⁻¹ * c
                = (s * c) * (Real.exp ((c/2)*s))⁻¹ := by ring
              _ ≤ (Real.exp ((c/2)*s) * 2) * (Real.exp ((c/2)*s))⁻¹ := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  nlinarith
              _ = 2 := by
                  rw [mul_comm (Real.exp ((c/2)*s)) 2, mul_assoc,
                    mul_inv_cancel₀ (Real.exp_pos _).ne']
                  ring
          have hexp_le : Real.exp (-c * s) ≤ Real.exp (-(c/2) * s) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          calc Real.pi * (‖z‖ + ε + s) * (Real.exp (Real.pi * M) * Real.exp (-c * s))
              = (Real.pi * (‖z‖ + ε) * Real.exp (-c * s)
                  + Real.pi * (s * Real.exp (-c * s))) * Real.exp (Real.pi * M) := by ring
            _ ≤ (Real.pi * (‖z‖ + ε) * Real.exp (-(c/2) * s)
                  + Real.pi * (2/c * Real.exp (-(c/2) * s))) * Real.exp (Real.pi * M) := by
                apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
                apply add_le_add
                · apply mul_le_mul_of_nonneg_left hexp_le
                  positivity
                · apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
                  rw [hexp_split]
                  calc s * (Real.exp (-(c/2)*s) * Real.exp (-(c/2)*s))
                      = (s * Real.exp (-(c/2)*s)) * Real.exp (-(c/2)*s) := by ring
                    _ ≤ (2/c) * Real.exp (-(c/2)*s) := by
                        apply mul_le_mul_of_nonneg_right hs_le (Real.exp_pos _).le
            _ = (Real.pi * (‖z‖ + ε) + 2 * Real.pi / c) * Real.exp (Real.pi * M)
                  * Real.exp (-(c/2) * s) := by ring
  · -- integrability of the dominant
    apply Integrable.const_mul
    exact exp_neg_integrableOn_Ioi 0 (by positivity)

open FLMF.Error in
-- no-dlmf: support lemma (derivative of C + iS via the keystone 7.5.8), no DLMF identity
/-- `w ↦ C(w) + iS(w)` has derivative `e^{½πiz²}` at every `z` — the chain rule
applied to `cfresnel_7_5_8` and `hasDerivAt_cerf`, using
`(½√π(1-i))² = -½πi` and `½(1+i)·(2/√π)·½√π(1-i) = 1`. -/
theorem hasDerivAt_cfresnelC_add_I_mul_cfresnelS (z : ℂ) :
    HasDerivAt (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w)
      (Complex.exp ((1/2)*Real.pi*Complex.I*z^2)) z := by
  have hfun : (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w)
      = fun w : ℂ => (1/2)*(1+Complex.I)
          * cerf ((1/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)*w) :=
    funext fun w => (cfresnel_7_5_8 w).1
  rw [hfun]
  have hlin : HasDerivAt (fun w : ℂ => (1/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)*w)
      ((1/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)) z := by
    simpa using (hasDerivAt_id z).const_mul ((1/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I))
  have hcomp := (FLMF.Error.hasDerivAt_cerf
      ((1/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)*z)).comp z hlin
  have hfinal := hcomp.const_mul ((1/2)*(1+Complex.I))
  convert hfinal using 1
  have hpi2 : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi:ℂ) := by
    norm_cast; exact Real.sq_sqrt Real.pi_pos.le
  have hne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1mI2 : (1 - Complex.I)^2 = -2*Complex.I := by linear_combination Complex.I_sq
  have hζsq : -(((1:ℂ)/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)*z)^2
      = (1/2)*Real.pi*Complex.I*z^2 := by
    have expand : (((1:ℂ)/2)*(Real.sqrt Real.pi:ℂ)*(1-Complex.I)*z)^2
        = (1/4) * (Real.sqrt Real.pi:ℂ)^2 * (1-Complex.I)^2 * z^2 := by ring
    rw [expand, hpi2, h1mI2]; ring
  rw [hζsq]
  have hI2 : Complex.I^2 = -1 := Complex.I_sq
  field_simp
  linear_combination hI2

-- no-dlmf: support lemma (derivative of ℱ), no DLMF identity
/-- `ℱ` has derivative `-e^{½πiz²}` at every `z`. -/
theorem hasDerivAt_cfresnelScriptF (z : ℂ) :
    HasDerivAt cfresnelScriptF (-Complex.exp ((1/2)*Real.pi*Complex.I*z^2)) z :=
  (hasDerivAt_cfresnelC_add_I_mul_cfresnelS z).const_sub ((1/2)*(1+Complex.I))

-- no-dlmf: support lemma (constancy on the upper half-plane), no DLMF identity
/-- A function with vanishing derivative on the (convex) upper half-plane takes the
same value at any two points of it (mean value inequality with bound `0`). -/
theorem eq_of_hasDerivAt_zero_upperHalfPlane {f : ℂ → ℂ}
    (hf : ∀ w : ℂ, 0 < w.im → HasDerivAt f 0 w) {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    f x = f y := by
  have hconv : Convex ℝ {c : ℂ | 0 < c.im} := convex_halfSpace_im_gt 0
  have h0 : ∀ w ∈ {c : ℂ | 0 < c.im},
      HasFDerivWithinAt f (0 : ℂ →L[ℂ] ℂ) {c : ℂ | 0 < c.im} w := by
    intro w hw
    have h := ((hf w hw).hasFDerivAt.hasFDerivWithinAt (s := {c : ℂ | 0 < c.im}))
    convert h using 1
    ext
    simp
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) h0
    (fun w _ => by simp) hconv hy hx
  have h1 : ‖f x - f y‖ ≤ 0 := by simpa using key
  have h2 := norm_le_zero_iff.mp h1
  exact sub_eq_zero.mp h2

-- no-dlmf: support lemma (ℱ vanishes along the imaginary axis), no DLMF identity
/-- `ℱ(iy) → 0` as `y → ∞`: by `cfresnel_7_4_6`,
`ℱ(iy) = ½(1+i) - i·C(y) - S(y)` with real `C(y), S(y) → ½`. -/
theorem tendsto_cfresnelScriptF_I_mul_atTop :
    Tendsto (fun y : ℝ => cfresnelScriptF (Complex.I * (y:ℂ))) atTop (𝓝 0) := by
  have hI2 : Complex.I^2 = -1 := Complex.I_sq
  have heq : ∀ y : ℝ, cfresnelScriptF (Complex.I * (y:ℂ))
      = (1/2)*(1+Complex.I) - Complex.I * ((fresnelC y : ℝ):ℂ) - ((fresnelS y : ℝ):ℂ) := by
    intro y
    have h746 := cfresnel_7_4_6 ((y:ℝ):ℂ)
    unfold cfresnelScriptF
    rw [h746.1, h746.2, cfresnelC_ofReal, cfresnelS_ofReal]
    linear_combination (((fresnelS y : ℝ):ℂ)) * hI2
  have hC : Tendsto (fun y : ℝ => ((fresnelC y : ℝ):ℂ)) atTop (𝓝 ((((1:ℝ)/2) : ℝ):ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_fresnelC
  have hS : Tendsto (fun y : ℝ => ((fresnelS y : ℝ):ℂ)) atTop (𝓝 ((((1:ℝ)/2) : ℝ):ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_fresnelS
  have h := (tendsto_const_nhds (x := (1/2)*(1+Complex.I)) (f := atTop)).sub
    (hC.const_mul Complex.I) |>.sub hS
  have hval : (1/2)*(1+Complex.I) - Complex.I * ((((1:ℝ)/2) : ℝ):ℂ) - ((((1:ℝ)/2) : ℝ):ℂ) = 0 := by
    push_cast
    ring
  rw [hval] at h
  exact Tendsto.congr (fun y => (heq y).symm) h

-- no-dlmf: support lemma (the ray integral vanishes along the imaginary axis), no DLMF identity
/-- `∫₀^∞ e^{½πi(iy+s)²} ds → 0` as `y → ∞`: the integrand has norm `e^{-πys}`,
so the integral is bounded by `1/(πy)`. -/
theorem tendsto_fresnelRayIntegral_I_mul_atTop :
    Tendsto (fun y : ℝ => ∫ s in Set.Ioi (0:ℝ),
      Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun y : ℝ => 1/(Real.pi * y))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hb : 0 < Real.pi * y := by positivity
    calc ‖∫ s in Set.Ioi (0:ℝ),
          Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2))‖
        ≤ ∫ s in Set.Ioi (0:ℝ),
            ‖Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ s in Set.Ioi (0:ℝ), Real.exp (-(Real.pi * y * s)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro s _
          show ‖Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2))‖
            = Real.exp (-(Real.pi * y * s))
          rw [norm_exp_fresnelRay (Complex.I*(y:ℂ)) s]
          congr 1
          simp [Complex.mul_re, Complex.mul_im]
          ring
      _ = 1/(Real.pi * y) := integral_exp_neg_mul_Ioi hb
  · have h : Tendsto (fun y : ℝ => Real.pi * y) atTop atTop :=
      Tendsto.const_mul_atTop Real.pi_pos tendsto_id
    have h2 := h.inv_tendsto_atTop
    refine h2.congr fun y => ?_
    simp [one_div]

-- no-dlmf: `Im z > 0` horizontal-ray form of 7.2.6; faithful surface is `cfresnel_7_2_6`
/-- Integral representation of the complex Fresnel integral
`ℱ(z) = ∫_z^∞ e^{½πit²}dt`, written along the *horizontal* ray `t = z+s`.

The horizontal parametrization only converges on `Im z > 0` (the integrand's
modulus is `e^{-π(Re z+s)·Im z}`, cf. `norm_exp_fresnelRay`), so this form is
strictly narrower than DLMF 7.2.6, whose unparametrized `∫_z^∞` runs to `∞` in
the decay sector `0 < ph t < π/2`. The hypothesis-free DLMF surface is
`cfresnel_7_2_6`, along the steepest-descent ray `t = z + s·e^{iπ/4}`.
-/
theorem cfresnel_7_2_6_horizontalRay {z : ℂ} (hz : 0 < z.im) :
    cfresnelScriptF z = ∫ s in Set.Ioi (0:ℝ), Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2)) := by
  -- `Φ(w) := ℱ(w) - ∫₀^∞ e^{½πi(w+s)²} ds` has zero derivative on the upper
  -- half-plane, hence is constant there; along `w = iy`, `y → ∞`, both terms
  -- tend to `0`, so the constant is `0`.
  have hΦderiv : ∀ w : ℂ, 0 < w.im → HasDerivAt (fun u : ℂ => cfresnelScriptF u
      - ∫ s in Set.Ioi (0:ℝ), Complex.exp ((1/2)*Real.pi*Complex.I*((u + (s:ℂ))^2))) 0 w := by
    intro w hw
    have h := (hasDerivAt_cfresnelScriptF w).sub (hasDerivAt_fresnelRayIntegral hw)
    simpa using h
  have hconst : ∀ y : ℝ, 0 < y →
      (cfresnelScriptF (Complex.I*(y:ℂ)) - ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2)))
      = cfresnelScriptF z - ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2)) := by
    intro y hy
    exact eq_of_hasDerivAt_zero_upperHalfPlane hΦderiv (by simpa using hy) hz
  have hlim0 : Tendsto (fun y : ℝ => cfresnelScriptF (Complex.I*(y:ℂ))
      - ∫ s in Set.Ioi (0:ℝ), Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2)))
      atTop (𝓝 0) := by
    simpa using tendsto_cfresnelScriptF_I_mul_atTop.sub tendsto_fresnelRayIntegral_I_mul_atTop
  have hlimc : Tendsto (fun y : ℝ => cfresnelScriptF (Complex.I*(y:ℂ))
      - ∫ s in Set.Ioi (0:ℝ), Complex.exp ((1/2)*Real.pi*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ))^2)))
      atTop (𝓝 (cfresnelScriptF z - ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2)))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    exact (hconst y hy).symm
  have h0 := tendsto_nhds_unique hlimc hlim0
  exact sub_eq_zero.mp h0

-- no-dlmf: `Im z > 0` horizontal-ray form of 7.7.12; faithful surface is `cfresnel_7_7_12`
/-- `g(z) + i f(z) = e^{-½πiz²}∫_z^∞ e^{½πit²}dt` along the *horizontal* ray
`t = z+s`, valid only for `Im z>0` (see `cfresnel_7_2_6_horizontalRay`). The
hypothesis-free DLMF surface is `cfresnel_7_7_12`.
-/
theorem cfresnel_7_7_12_horizontalRay {z : ℂ} (hz : 0 < z.im) :
    cfresnelAuxG z + Complex.I * cfresnelAuxF z
      = Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2))
        * ∫ s in Set.Ioi (0:ℝ), Complex.exp ((1/2)*Real.pi*Complex.I*((z + (s:ℂ))^2)) := by
  rw [← cfresnel_7_2_6_horizontalRay hz, ← cfresnel_7_5_5 z]

/-! ### The rotated ray `t = z + s·e^{iπ/4}` (DLMF 7.2.6 for every `z ∈ ℂ`)

DLMF's `∫_z^∞ e^{½πit²}dt` does not name a path: the integrand is entire and
decays exactly in the sector `0 < ph t < π/2` (writing `t = re^{iθ}`,
`Re(½πit²) = -½πr² sin 2θ`), maximally along `θ = π/4`. Parametrizing the
contour along that steepest-descent ray, `t = z + sω` with `ω = e^{iπ/4}`,
`ω² = i`, gives

`½πi(z+sω)² = ½πiz² + πiωz·s - ½πs²`,

a Gaussian decay valid for **every** `z ∈ ℂ` — so the `Im z > 0` hypothesis of
the horizontal parametrization disappears. The proof below re-runs the
horizontal template with three changes: a Gaussian dominant in place of the
exponential one, whole-plane constancy (`eq_of_hasDerivAt_zero_univ`) in place of
constancy on the upper half-plane, and the same imaginary-axis pinning limit. -/

-- no-dlmf: support lemma (integrability of `e^{-s}` on `(0,∞)`), no DLMF identity
/-- `s ↦ e^{-s}` is integrable on `(0,∞)`. -/
theorem integrableOn_exp_neg_Ioi_zero :
    IntegrableOn (fun s : ℝ => Real.exp (-s)) (Set.Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1)
  simpa using h

section RotatedRay

variable {ω : ℂ}

-- no-dlmf: support lemma (exponent factorization on the rotated ray), no DLMF identity
/-- With `ω² = i`, `½πi(w+sω)² = ½πiw² + πiωw·s - ½πs²`: the `s²` term is real
and negative, which is why the rotated ray converges for every `w`. -/
theorem exp_arg_fresnelRot (hω : ω ^ 2 = Complex.I) (w : ℂ) (s : ℝ) :
    (1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)
      = (1/2)*(Real.pi:ℂ)*Complex.I*w^2
        + ((Real.pi:ℂ)*Complex.I*ω*w)*(s:ℂ) - ((Real.pi:ℂ)/2)*(s:ℂ)^2 := by
  have h : ((s:ℂ)*ω)^2 = (s:ℂ)^2 * Complex.I := by rw [mul_pow, hω]
  linear_combination ((1/2)*(Real.pi:ℂ)*Complex.I) * h
    + ((Real.pi:ℂ)*(s:ℂ)^2/2) * Complex.I_sq

-- no-dlmf: support lemma (norm of the rotated-ray integrand), no DLMF identity
/-- `‖e^{½πi(w+sω)²}‖ = e^{-π·Re w·Im w - π(ω₁·Im w + ω₂·Re w)s - ½πs²}`. -/
theorem norm_exp_fresnelRot (hω : ω ^ 2 = Complex.I) (w : ℂ) (s : ℝ) :
    ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2))‖
      = Real.exp (-(Real.pi * w.re * w.im)
          - Real.pi * (ω.re * w.im + ω.im * w.re) * s - (Real.pi/2) * s^2) := by
  rw [exp_arg_fresnelRot hω, Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  ring

-- no-dlmf: support lemma (elementary quadratic bound), no DLMF identity
/-- `bs - ½πs² ≤ b²/(2π)`, the completed square `(πs-b)² ≥ 0`. -/
theorem fresnelRot_quad_le (b s : ℝ) : b * s - (Real.pi/2) * s^2 ≤ b^2 / (2*Real.pi) := by
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
  nlinarith [sq_nonneg (Real.pi*s - b), Real.pi_pos]

-- no-dlmf: support lemma (Gaussian bound for the rotated-ray integrand), no DLMF identity
/-- Locally uniform Gaussian bound on the rotated-ray integrand: for `‖w‖ ≤ R`
and `s ≥ 0`, `‖e^{½πi(w+sω)²}‖ ≤ e^{πR² + 2πRs - ½πs²}`. -/
theorem norm_exp_fresnelRot_le' (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1)
    {R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2))‖
      ≤ Real.exp (Real.pi*R^2 + 2*Real.pi*R*s - (Real.pi/2)*s^2) := by
  rw [norm_exp_fresnelRot hω]
  apply Real.exp_le_exp.mpr
  have hπ := Real.pi_pos
  have hR : 0 ≤ R := le_trans (norm_nonneg w) hw
  have hre : |w.re| ≤ R := le_trans (Complex.abs_re_le_norm w) hw
  have him : |w.im| ≤ R := le_trans (Complex.abs_im_le_norm w) hw
  have hωre : |ω.re| ≤ 1 := by
    have := Complex.abs_re_le_norm ω; rwa [hωn] at this
  have hωim : |ω.im| ≤ 1 := by
    have := Complex.abs_im_le_norm ω; rwa [hωn] at this
  have h1 : -(w.re * w.im) ≤ R^2 := by
    have hab : |w.re * w.im| ≤ R * R := by
      rw [abs_mul]; exact mul_le_mul hre him (abs_nonneg _) hR
    nlinarith [neg_le_abs (w.re * w.im)]
  have h2 : -(ω.re * w.im + ω.im * w.re) ≤ 2*R := by
    have ha : |ω.re * w.im| ≤ R := by
      rw [abs_mul]
      calc |ω.re| * |w.im| ≤ 1 * R := mul_le_mul hωre him (abs_nonneg _) zero_le_one
        _ = R := one_mul R
    have hb : |ω.im * w.re| ≤ R := by
      rw [abs_mul]
      calc |ω.im| * |w.re| ≤ 1 * R := mul_le_mul hωim hre (abs_nonneg _) zero_le_one
        _ = R := one_mul R
    have h3 := neg_le_abs (ω.re * w.im)
    have h4 := neg_le_abs (ω.im * w.re)
    linarith
  have h1' : Real.pi * (-(w.re * w.im)) ≤ Real.pi * R^2 :=
    mul_le_mul_of_nonneg_left h1 hπ.le
  have h2' : -(ω.re * w.im + ω.im * w.re) * (Real.pi * s) ≤ 2*R * (Real.pi * s) :=
    mul_le_mul_of_nonneg_right h2 (mul_nonneg hπ.le hs)
  nlinarith [h1', h2']

-- no-dlmf: support lemma (exponential dominant for the rotated-ray integrand), no DLMF identity
/-- The Gaussian bound of `norm_exp_fresnelRot_le'` dominated by `C_R·e^{-s}`. -/
theorem norm_exp_fresnelRot_le (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1)
    {R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2))‖
      ≤ Real.exp (Real.pi*R^2 + (2*Real.pi*R+1)^2/(2*Real.pi)) * Real.exp (-s) := by
  refine le_trans (norm_exp_fresnelRot_le' hω hωn hw hs) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := fresnelRot_quad_le (2*Real.pi*R+1) s
  linarith

-- no-dlmf: support lemma (dominant for the differentiated integrand), no DLMF identity
/-- Locally uniform dominant `C_R·e^{-s}` for `πi(w+sω)e^{½πi(w+sω)²}`, the
`w`-derivative of the rotated-ray integrand. -/
theorem norm_deriv_fresnelRot_le (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1)
    {R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    ‖(Real.pi:ℂ)*Complex.I*(w + (s:ℂ)*ω)
        * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2))‖
      ≤ (Real.pi*(R+1)*Real.exp (Real.pi*R^2 + (2*Real.pi*R+2)^2/(2*Real.pi)))
          * Real.exp (-s) := by
  have hR : 0 ≤ R := le_trans (norm_nonneg w) hw
  have hπ := Real.pi_pos
  have hfac : ‖(Real.pi:ℂ)*Complex.I*(w + (s:ℂ)*ω)‖ ≤ Real.pi * (R + s) := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hπ]
    have h1 : ‖w + (s:ℂ)*ω‖ ≤ R + s := by
      calc ‖w + (s:ℂ)*ω‖ ≤ ‖w‖ + ‖(s:ℂ)*ω‖ := norm_add_le _ _
        _ = ‖w‖ + s := by
            rw [norm_mul, hωn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
        _ ≤ R + s := by linarith
    nlinarith
  rw [norm_mul]
  have hnorm := norm_exp_fresnelRot_le' hω hωn hw hs
  have hprod : ‖(Real.pi:ℂ)*Complex.I*(w + (s:ℂ)*ω)‖
      * ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2))‖
      ≤ (Real.pi * (R + s)) * Real.exp (Real.pi*R^2 + 2*Real.pi*R*s - (Real.pi/2)*s^2) :=
    mul_le_mul hfac hnorm (norm_nonneg _) (by positivity)
  refine le_trans hprod ?_
  have hes : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have h4 : (R + 1) * (1 + s) ≤ (R + 1) * Real.exp s :=
    mul_le_mul_of_nonneg_left hes (by linarith)
  have h5 : R + s ≤ (R + 1) * (1 + s) := by nlinarith
  have hstep : Real.pi * (R + s) ≤ Real.pi * (R + 1) * Real.exp s := by
    calc Real.pi * (R + s) ≤ Real.pi * ((R + 1) * Real.exp s) :=
          mul_le_mul_of_nonneg_left (h5.trans h4) hπ.le
      _ = Real.pi * (R + 1) * Real.exp s := by ring
  have hq := fresnelRot_quad_le (2*Real.pi*R+2) s
  calc Real.pi * (R + s) * Real.exp (Real.pi*R^2 + 2*Real.pi*R*s - (Real.pi/2)*s^2)
      ≤ (Real.pi * (R + 1) * Real.exp s)
          * Real.exp (Real.pi*R^2 + 2*Real.pi*R*s - (Real.pi/2)*s^2) :=
        mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le
    _ = Real.pi * (R + 1)
          * Real.exp (Real.pi*R^2 + (2*Real.pi*R+1)*s - (Real.pi/2)*s^2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ Real.pi * (R + 1)
          * (Real.exp (Real.pi*R^2 + (2*Real.pi*R+2)^2/(2*Real.pi)) * Real.exp (-s)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
    _ = (Real.pi*(R+1)*Real.exp (Real.pi*R^2 + (2*Real.pi*R+2)^2/(2*Real.pi)))
          * Real.exp (-s) := by ring

-- no-dlmf: support lemma (integrability on the rotated ray), no DLMF identity
/-- The rotated-ray integrand is integrable on `(0,∞)` for **every** `w`. -/
theorem integrableOn_exp_fresnelRot (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1) (w : ℂ) :
    IntegrableOn
      (fun s : ℝ => Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)))
      (Set.Ioi 0) := by
  refine Integrable.mono' (g := fun s : ℝ =>
      Real.exp (Real.pi*‖w‖^2 + (2*Real.pi*‖w‖+1)^2/(2*Real.pi)) * Real.exp (-s))
    (integrableOn_exp_neg_Ioi_zero.const_mul _)
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact norm_exp_fresnelRot_le hω hωn (le_refl ‖w‖) (le_of_lt hs)

-- no-dlmf: support lemma (decay of the rotated-ray integrand at `+∞`), no DLMF identity
/-- The rotated-ray integrand tends to `0` as `s → ∞`, for every `w`. -/
theorem tendsto_exp_fresnelRot_atTop (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1) (w : ℂ) :
    Tendsto (fun s : ℝ => Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun s : ℝ =>
      Real.exp (Real.pi*‖w‖^2 + (2*Real.pi*‖w‖+1)^2/(2*Real.pi)) * Real.exp (-s)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact norm_exp_fresnelRot_le hω hωn (le_refl ‖w‖) hs
  · have h : Tendsto (fun s : ℝ => Real.exp (-s)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using h.const_mul (Real.exp (Real.pi*‖w‖^2 + (2*Real.pi*‖w‖+1)^2/(2*Real.pi)))

-- no-dlmf: support lemma (derivative in the ray parameter), no DLMF identity
/-- `v ↦ e^{½πi(w+vω)²}` has derivative `ω·πi(w+uω)·e^{½πi(w+uω)²}` at `u`. -/
theorem hasDerivAt_exp_fresnelRot_param (w u ω : ℂ) :
    HasDerivAt (fun v : ℂ => Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + v*ω)^2)))
      (ω * ((Real.pi:ℂ)*Complex.I*(w + u*ω)
        * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + u*ω)^2)))) u := by
  have hinner : HasDerivAt (fun v : ℂ => (1/2)*(Real.pi:ℂ)*Complex.I*((w + v*ω)^2))
      (ω * ((Real.pi:ℂ)*Complex.I*(w + u*ω))) u := by
    have h := ((((hasDerivAt_id u).mul_const ω).const_add w).pow 2).const_mul
      ((1/2)*(Real.pi:ℂ)*Complex.I)
    convert h using 1
    simp only [id_eq]
    ring
  have h := hinner.cexp
  convert h using 1
  ring

-- no-dlmf: support lemma (differentiation of the rotated-ray integral), no DLMF identity
/-- On **all** of `ℂ` the rotated-ray integral `w ↦ ω∫₀^∞ e^{½πi(w+sω)²}ds` has
derivative `-e^{½πiz²}`: differentiation under the integral sign against the
locally uniform dominant of `norm_deriv_fresnelRot_le`, then the FTC in `s`. -/
theorem hasDerivAt_fresnelRotIntegral (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)))
      (-Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*z^2)) z := by
  have hω0 : ω ≠ 0 := by
    intro h; rw [h] at hωn; simp at hωn
  set R : ℝ := ‖z‖ + 1 with hR
  set K : ℝ := Real.pi*(R+1)*Real.exp (Real.pi*R^2 + (2*Real.pi*R+2)^2/(2*Real.pi)) with hK
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (s : ℝ) =>
      Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)))
    (F' := fun (w : ℂ) (s : ℝ) =>
      (Real.pi:ℂ)*Complex.I*(w + (s:ℂ)*ω)
        * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((w + (s:ℂ)*ω)^2)))
    (μ := volume.restrict (Set.Ioi 0))
    (x₀ := z)
    (bound := fun s => K * Real.exp (-s))
    (Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1))
    (Filter.Eventually.of_forall fun w => Continuous.aestronglyMeasurable (by fun_prop))
    (integrableOn_exp_fresnelRot hω hωn z)
    (Continuous.aestronglyMeasurable (by fun_prop))
    ?_ ?_
    (Filter.Eventually.of_forall fun s w _ => hasDerivAt_exp_fresnelRay ((s:ℂ)*ω) w)
  · obtain ⟨hint, hderiv⟩ := hmain
    have hderiv_s : ∀ s : ℝ, s ∈ Set.Ioi (0:ℝ) →
        HasDerivAt (fun t : ℝ => Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (t:ℂ)*ω)^2)))
          (ω * ((Real.pi:ℂ)*Complex.I*(z + (s:ℂ)*ω)
            * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)))) s := by
      intro s _
      exact (hasDerivAt_exp_fresnelRot_param z ((s:ℝ):ℂ) ω).comp_ofReal
    have hcont : ContinuousWithinAt
        (fun t : ℝ => Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (t:ℂ)*ω)^2)))
        (Set.Ici 0) 0 :=
      Continuous.continuousWithinAt (by fun_prop)
    have hint' : IntegrableOn (fun s : ℝ =>
        ω * ((Real.pi:ℂ)*Complex.I*(z + (s:ℂ)*ω)
          * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)))) (Set.Ioi 0) :=
      hint.const_mul ω
    have hres := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv_s hint'
      (tendsto_exp_fresnelRot_atTop hω hωn z)
    rw [integral_const_mul] at hres
    have hres' : ω * (∫ s in Set.Ioi (0:ℝ),
        (Real.pi:ℂ)*Complex.I*(z + (s:ℂ)*ω)
          * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)))
        = -Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*z^2) := by
      rw [hres]
      norm_num
    have hkey : (∫ s in Set.Ioi (0:ℝ),
        (Real.pi:ℂ)*Complex.I*(z + (s:ℂ)*ω)
          * Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)))
        = ω⁻¹ * (-Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*z^2)) := by
      rw [← hres', ← mul_assoc, inv_mul_cancel₀ hω0, one_mul]
    rw [hkey] at hderiv
    have hfin := hderiv.const_mul ω
    convert hfin using 1
    rw [← mul_assoc, mul_inv_cancel₀ hω0, one_mul]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have hs0 : (0:ℝ) < s := hs
    have hwR : ‖w‖ ≤ R := by
      have hdist : ‖w - z‖ < 1 := mem_ball_iff_norm.mp hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    exact norm_deriv_fresnelRot_le hω hωn hwR hs0.le
  · exact integrableOn_exp_neg_Ioi_zero.const_mul _

-- no-dlmf: support lemma (constancy on the whole plane), no DLMF identity
/-- A function with vanishing derivative on all of `ℂ` is constant (mean value
inequality with bound `0` on the convex set `Set.univ`). -/
theorem eq_of_hasDerivAt_zero_univ {f : ℂ → ℂ}
    (hf : ∀ w : ℂ, HasDerivAt f 0 w) (x y : ℂ) : f x = f y := by
  have h0 : ∀ w ∈ (Set.univ : Set ℂ),
      HasFDerivWithinAt f (0 : ℂ →L[ℂ] ℂ) (Set.univ : Set ℂ) w := by
    intro w _
    have h := ((hf w).hasFDerivAt.hasFDerivWithinAt (s := (Set.univ : Set ℂ)))
    convert h using 1
    ext
    simp
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) h0
    (fun w _ => by simp) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have h1 : ‖f x - f y‖ ≤ 0 := by simpa using key
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)

-- no-dlmf: support lemma (the rotated-ray integral vanishes along the imaginary axis), no DLMF identity
/-- `ω∫₀^∞ e^{½πi(iy+sω)²}ds → 0` as `y → ∞`: the integrand has norm at most
`e^{-π(Re ω)ys}`, so the integral is bounded by `1/(π(Re ω)y)`. -/
theorem tendsto_fresnelRotIntegral_I_mul_atTop (hω : ω ^ 2 = Complex.I) (hωn : ‖ω‖ = 1)
    (hωre : 0 < ω.re) :
    Tendsto (fun y : ℝ => ω * ∫ s in Set.Ioi (0:ℝ),
      Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2)))
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun y : ℝ => 1/(Real.pi * ω.re * y)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hb : 0 < Real.pi * ω.re * y := by positivity
    have hbound : ∀ s : ℝ, s ∈ Set.Ioi (0:ℝ) →
        ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2))‖
          ≤ Real.exp (-(Real.pi * ω.re * y * s)) := by
      intro s hs
      rw [norm_exp_fresnelRot hω]
      apply Real.exp_le_exp.mpr
      have hre : (Complex.I*(y:ℂ)).re = 0 := by simp
      have him : (Complex.I*(y:ℂ)).im = y := by simp
      rw [hre, him]
      have hs0 : (0:ℝ) < s := hs
      have hsq : 0 ≤ (Real.pi/2) * s^2 := by positivity
      nlinarith [Real.pi_pos]
    calc ‖ω * ∫ s in Set.Ioi (0:ℝ),
          Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2))‖
        = ‖∫ s in Set.Ioi (0:ℝ),
            Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2))‖ := by
          rw [norm_mul, hωn, one_mul]
      _ ≤ ∫ s in Set.Ioi (0:ℝ),
            ‖Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2))‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ s in Set.Ioi (0:ℝ), Real.exp (-(Real.pi * ω.re * y * s)) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards with s using norm_nonneg _
          · have := exp_neg_integrableOn_Ioi 0 hb
            refine this.congr_fun ?_ measurableSet_Ioi
            intro s _
            ring_nf
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
            exact hbound s hs
      _ = 1/(Real.pi * ω.re * y) := integral_exp_neg_mul_Ioi hb
  · have h : Tendsto (fun y : ℝ => Real.pi * ω.re * y) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_id
    have h2 := h.inv_tendsto_atTop
    refine h2.congr fun y => ?_
    simp [one_div]

end RotatedRay

-- no-dlmf: support lemma (`e^{iπ/4}` squares to `i`), no DLMF identity
/-- `(e^{iπ/4})² = i`. -/
theorem exp_I_pi_div_four_sq : (Complex.exp (Complex.I * Real.pi / 4))^2 = Complex.I := by
  rw [pow_two, ← Complex.exp_add]
  rw [show Complex.I * (Real.pi:ℂ) / 4 + Complex.I * (Real.pi:ℂ) / 4
      = ((Real.pi:ℂ)/2) * Complex.I from by ring]
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

-- no-dlmf: support lemma (`Re e^{iπ/4} = √2/2`), no DLMF identity
/-- `Re(e^{iπ/4}) = √2/2 > 0`. -/
theorem exp_I_pi_div_four_re : (Complex.exp (Complex.I * Real.pi / 4)).re = Real.sqrt 2 / 2 := by
  rw [show Complex.I * (Real.pi:ℂ) / 4 = ((Real.pi/4 : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]

-- no-dlmf: support lemma (`|e^{iπ/4}| = 1`), no DLMF identity
/-- `‖e^{iπ/4}‖ = 1`. -/
theorem exp_I_pi_div_four_norm : ‖Complex.exp (Complex.I * Real.pi / 4)‖ = 1 := by
  have h1 : ‖Complex.exp (Complex.I * Real.pi / 4)‖^2 = 1 := by
    rw [← norm_pow, exp_I_pi_div_four_sq, Complex.norm_I]
  nlinarith [norm_nonneg (Complex.exp (Complex.I * Real.pi / 4))]

/-- Integral representation of the complex Fresnel integral
`ℱ(z) = ∫_z^∞ e^{½πit²}dt`, valid for **every** `z ∈ ℂ` (DLMF 7.2.6).

DLMF's `∫_z^∞` names no path. Here it is read as the ray from `z` to
`∞·e^{iπ/4}` — the direction of steepest descent for `e^{½πit²}`, along which
the integrand decays like `e^{-½πs²}` — so the parametrization `t = z + se^{iπ/4}`,
`dt = e^{iπ/4}ds`, converges absolutely for every `z` and the identity carries no
hypothesis. (The value is independent of the admissible direction
`0 < ph < π/2`; the horizontal reading `t = z+s`, which converges only on
`Im z > 0`, is `cfresnel_7_2_6_horizontalRay`.)

DLMF 7.2.6.
DAG: E-7.2.6.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_2_6 (z : ℂ) :
    cfresnelScriptF z
      = Complex.exp (Complex.I * Real.pi / 4) *
          ∫ s in Set.Ioi (0:ℝ),
            Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*
              ((z + (s:ℂ) * Complex.exp (Complex.I * Real.pi / 4))^2)) := by
  set ω : ℂ := Complex.exp (Complex.I * Real.pi / 4) with hωdef
  have hω : ω ^ 2 = Complex.I := exp_I_pi_div_four_sq
  have hωn : ‖ω‖ = 1 := exp_I_pi_div_four_norm
  have hωre : 0 < ω.re := by
    rw [hωdef, exp_I_pi_div_four_re]
    positivity
  -- `Φ(w) := ℱ(w) - ω∫₀^∞ e^{½πi(w+sω)²}ds` has zero derivative on all of `ℂ`,
  -- hence is constant; along `w = iy`, `y → ∞`, both terms tend to `0`.
  have hΦderiv : ∀ w : ℂ, HasDerivAt (fun u : ℂ => cfresnelScriptF u
      - ω * ∫ s in Set.Ioi (0:ℝ),
          Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((u + (s:ℂ)*ω)^2))) 0 w := by
    intro w
    have h := (hasDerivAt_cfresnelScriptF w).sub (hasDerivAt_fresnelRotIntegral hω hωn w)
    simpa using h
  have hconst : ∀ y : ℝ,
      (cfresnelScriptF (Complex.I*(y:ℂ)) - ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2)))
      = cfresnelScriptF z - ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)) := by
    intro y
    exact eq_of_hasDerivAt_zero_univ hΦderiv _ _
  have hlim0 : Tendsto (fun y : ℝ => cfresnelScriptF (Complex.I*(y:ℂ))
      - ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2)))
      atTop (𝓝 0) := by
    simpa using tendsto_cfresnelScriptF_I_mul_atTop.sub
      (tendsto_fresnelRotIntegral_I_mul_atTop hω hωn hωre)
  have hlimc : Tendsto (fun y : ℝ => cfresnelScriptF (Complex.I*(y:ℂ))
      - ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((Complex.I*(y:ℂ) + (s:ℂ)*ω)^2)))
      atTop (𝓝 (cfresnelScriptF z - ω * ∫ s in Set.Ioi (0:ℝ),
        Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*((z + (s:ℂ)*ω)^2)))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with y
    exact (hconst y).symm
  have h0 := tendsto_nhds_unique hlimc hlim0
  exact sub_eq_zero.mp h0

/-- `g(z) + i f(z) = e^{-½πiz²}∫_z^∞ e^{½πit²}dt` (DLMF 7.7.12), for **every**
`z ∈ ℂ`: the integral representation of the auxiliary functions, with `∫_z^∞`
realized along the steepest-descent ray `t = z + se^{iπ/4}` exactly as in
`cfresnel_7_2_6`.

DLMF 7.7.12.
DAG: E-7.7.12.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_7_12 (z : ℂ) :
    cfresnelAuxG z + Complex.I * cfresnelAuxF z
      = Complex.exp (-(((1:ℂ)/2)*Real.pi*Complex.I*z^2)) *
        (Complex.exp (Complex.I * Real.pi / 4) *
          ∫ s in Set.Ioi (0:ℝ),
            Complex.exp ((1/2)*(Real.pi:ℂ)*Complex.I*
              ((z + (s:ℂ) * Complex.exp (Complex.I * Real.pi / 4))^2))) := by
  rw [← cfresnel_7_2_6 z, ← cfresnel_7_5_5 z]

end FLMF.Fresnel
