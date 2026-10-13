import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Ch7Definitions
import FLMF.Functions.Error.Ch7AsymptoticExpansions
import FLMF.Functions.Hermite.Normalization
import FLMF.Functions.Fresnel.Complex

/-!
# Derivatives of the error function (DLMF §7.10)

DLMF §7.10 records the derivatives of `erf`, the Faddeeva function `w(z)`, and the
Fresnel auxiliary functions `f, g`, all at DLMF's stated complex-`z` strength.

* **7.10.1**: DLMF's complex-`z` statement is `FLMF.Error.cerf_7_10_1`
  (`Error/ComplexErf.lean`), the `(n+1)`-th derivative of the complex `cerf` in
  terms of the physicists' Hermite polynomials `Hₙ`
  (`FLMF.Functions.Hermite.physicistsHermite`, evaluated over `ℂ`). `erf_7_10_1` below
  is its real instance, retained as a `no-dlmf` narrowed surface.
* **7.10.2** and **7.10.3** concern the Faddeeva function `w(z) = e^{-z²} erfc(-iz)`,
  RESOLVED (complex-`z`) in `Error/Faddeeva.lean` as `erf_7_10_2`/`erf_7_10_3`.
* **7.10.4**: DLMF's complex-`z` statement is `cfresnel_7_10_4` below, the
  derivatives of the complex Fresnel auxiliary functions `f(z), g(z)`
  (`FLMF.Fresnel.cfresnelAuxF`/`cfresnelAuxG`). `erf_7_10_4` below is its real
  instance, retained as a `no-dlmf` narrowed surface.
-/

namespace FLMF.Error

open Real

-- no-dlmf: real/narrowed restriction of DLMF 7.10.1; faithful surface is
-- FLMF.Error.cerf_7_10_1
/-- The `(n+1)`-th derivative of `erf` is
`(-1)ⁿ (2/√π) Hₙ(z) e^{-z²}`, where `Hₙ` is the physicists' Hermite polynomial
`FLMF.Functions.Hermite.physicistsHermite` (the real instance of DLMF 7.10.1;
DLMF's `z` is complex, see `cerf_7_10_1` in `Error/ComplexErf.lean` for the
faithful surface).

Same induction as the complex surface, run over `ℝ`: base case `hasDerivAt_erf`,
step case the real Hermite–Gaussian differentiation rule
`d/dx (Hₙ(x) e^{-x²}) = -H_{n+1}(x) e^{-x²}`
(`FLMF.Functions.Hermite.hasDerivAt_aeval_physicistsHermite_mul_exp`).
-/
theorem erf_7_10_1 (n : ℕ) (z : ℝ) :
    iteratedDeriv (n + 1) erf z =
      (-1) ^ n * (2 / Real.sqrt Real.pi) *
        (Polynomial.aeval z (FLMF.Functions.Hermite.physicistsHermite n)) *
          Real.exp (-z ^ 2) := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_one, (hasDerivAt_erf z).deriv]
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv (n + 1) erf
        = fun y : ℝ => (-1 : ℝ) ^ n * (2 / Real.sqrt Real.pi)
            * (Polynomial.aeval y (FLMF.Functions.Hermite.physicistsHermite n))
            * Real.exp (-y ^ 2) := funext ih
    rw [hfun]
    have hd := (FLMF.Functions.Hermite.hasDerivAt_aeval_physicistsHermite_mul_exp n z).const_mul
      ((-1 : ℝ) ^ n * (2 / Real.sqrt Real.pi))
    have hshape : (fun y : ℝ => (-1 : ℝ) ^ n * (2 / Real.sqrt Real.pi)
          * (Polynomial.aeval y (FLMF.Functions.Hermite.physicistsHermite n)
              * Real.exp (-y ^ 2)))
        = fun y : ℝ => (-1 : ℝ) ^ n * (2 / Real.sqrt Real.pi)
            * (Polynomial.aeval y (FLMF.Functions.Hermite.physicistsHermite n))
            * Real.exp (-y ^ 2) := funext fun y => by ring
    rw [hshape] at hd
    rw [hd.deriv]
    ring

/-
**DLMF 7.10.2** — `w′(z) = -2 z w(z) + 2 i / √π`.
[RESOLVED in Error/Faddeeva.lean as `erf_7_10_2`, via the complex Faddeeva keystone.]

(Original deferral note:) this is the derivative identity for the Faddeeva (plasma-dispersion)
function `w(z) = e^{-z²} erfc(-i z)`, which is intrinsically complex-valued
(the `2 i / √π` inhomogeneous term is non-real).  FLMF's error API is REAL-valued
and has no complex `w`, so there is no honest real specialization of this identity.
Requires complex `erf` / Faddeeva `w(z)`, not in FLMF.
-/

/-
**DLMF 7.10.3** — `w^{(n+2)}(z) + 2 z w^{(n+1)}(z) + 2 (n+1) w^{(n)}(z) = 0`.
[RESOLVED in Error/Faddeeva.lean as `erf_7_10_3`, via the complex Faddeeva keystone.]

(Original deferral note:) a recurrence on the higher derivatives of the complex Faddeeva function
`w(z)`.  Same obstruction as 7.10.2 — FLMF has no complex `w(z)`, and the identity
has no real specialization.  Requires complex `erf` / Faddeeva `w(z)`, not in FLMF.
-/

-- no-dlmf: real/narrowed restriction of DLMF 7.10.4; faithful surface is
-- FLMF.Error.cfresnel_7_10_4
/-- Derivatives of the Fresnel auxiliary functions `f, g` (real instance of
DLMF 7.10.4): `f′(z) = -π z g(z)` and `g′(z) = π z f(z) - 1`.
DLMF's `z` is complex, see `cfresnel_7_10_4` below for the faithful surface.
-/
theorem erf_7_10_4 (z : ℝ) :
    deriv fresnelAuxF z = -π * z * fresnelAuxG z
      ∧ deriv fresnelAuxG z = π * z * fresnelAuxF z - 1 := by
  exact ⟨(fresnelAuxF_hasDerivAt z).deriv, (fresnelAuxG_hasDerivAt z).deriv⟩

open FLMF.Fresnel in
-- no-dlmf: support lemma (derivative of the complex Fresnel `C - iS` combination
-- via the lower-sign branch of `cfresnel_7_5_8`, chained through `hasDerivAt_cerf`);
-- no DLMF display of its own.
private lemma _kit_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w)
      (Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) z := by
  have hfun : (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w)
      = fun w : ℂ => (1 / 2) * (1 - Complex.I)
          * FLMF.Error.cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w) :=
    funext fun w => (cfresnel_7_5_8 w).2
  rw [hfun]
  have hlin : HasDerivAt (fun w : ℂ => (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w)
      ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I)) z := by
    simpa using (hasDerivAt_id z).const_mul ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I))
  have hcomp := (FLMF.Error.hasDerivAt_cerf
      ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)).comp z hlin
  have hfinal := hcomp.const_mul ((1 / 2) * (1 - Complex.I))
  convert hfinal using 1
  have hpi2 : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    norm_cast; exact Real.sq_sqrt Real.pi_pos.le
  have hne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1pI2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by linear_combination Complex.I_sq
  have hζsq : -(((1 : ℂ) / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ^ 2
      = -((1 / 2) * Real.pi * Complex.I * z ^ 2) := by
    have expand : (((1 : ℂ) / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ^ 2
        = (1 / 4) * (Real.sqrt Real.pi : ℂ) ^ 2 * (1 + Complex.I) ^ 2 * z ^ 2 := by ring
    rw [expand, hpi2, h1pI2]; ring
  rw [hζsq]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  linear_combination hI2

open FLMF.Fresnel in
-- no-dlmf: support lemma (derivative of the complex Fresnel cosine integral `C`,
-- assembled from the `C+iS`/`C-iS` combined derivatives); no DLMF display of its
-- own.
private lemma _kit_cfresnelC_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelC
      ((Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          + Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / 2) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := _kit_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt z
  have hsum := d1.add d2
  have h2 : HasDerivAt (fun w : ℂ => 2 * cfresnelC w)
      (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
        + Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) z := by
    convert hsum using 1
    funext w
    simp only [Pi.add_apply]
    ring
  have h3 := h2.div_const 2
  have hCeq : (fun w : ℂ => 2 * cfresnelC w / 2) = cfresnelC := by funext w; ring
  rw [hCeq] at h3
  exact h3

open FLMF.Fresnel in
-- no-dlmf: support lemma (derivative of the complex Fresnel sine integral `S`,
-- assembled from the `C+iS`/`C-iS` combined derivatives); no DLMF display of its
-- own.
private lemma _kit_cfresnelS_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelS
      ((Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / (2 * Complex.I)) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := _kit_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt z
  have hsub := d1.sub d2
  have h2 : HasDerivAt (fun w : ℂ => 2 * Complex.I * cfresnelS w)
      (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
        - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) z := by
    convert hsub using 1
    funext w
    simp only [Pi.sub_apply]
    ring
  have h3 := h2.div_const (2 * Complex.I)
  have hne : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hSeq : (fun w : ℂ => 2 * Complex.I * cfresnelS w / (2 * Complex.I)) = cfresnelS := by
    funext w
    field_simp
  rw [hSeq] at h3
  exact h3

open FLMF.Fresnel in
-- no-dlmf: support lemma (`Complex.cos`/`Complex.sin` reformulation of
-- `_kit_cfresnelC_hasDerivAt`/`_kit_cfresnelS_hasDerivAt` via `exp_mul_I`); no
-- DLMF display of its own.
private lemma _kit_cfresnelC_cos_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelC (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have h := _kit_cfresnelC_hasDerivAt z
  have heq : Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)
      = (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          + Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / 2 := by
    unfold Complex.cos
    have harg1 : (Real.pi : ℂ) * z ^ 2 / 2 * Complex.I = (1 / 2) * Real.pi * Complex.I * z ^ 2 := by
      ring
    have harg2 : -((Real.pi : ℂ) * z ^ 2 / 2) * Complex.I
        = -((1 / 2) * Real.pi * Complex.I * z ^ 2) := by ring
    rw [harg1, harg2]
  rw [heq]; exact h

open FLMF.Fresnel in
-- no-dlmf: support lemma (`Complex.cos`/`Complex.sin` reformulation of
-- `_kit_cfresnelC_hasDerivAt`/`_kit_cfresnelS_hasDerivAt` via `exp_mul_I`); no
-- DLMF display of its own.
private lemma _kit_cfresnelS_sin_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelS (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have h := _kit_cfresnelS_hasDerivAt z
  have heq : Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)
      = (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / (2 * Complex.I) := by
    unfold Complex.sin
    have harg1 : -((Real.pi : ℂ) * z ^ 2 / 2) * Complex.I
        = -((1 / 2) * Real.pi * Complex.I * z ^ 2) := by ring
    have harg2 : (Real.pi : ℂ) * z ^ 2 / 2 * Complex.I = (1 / 2) * Real.pi * Complex.I * z ^ 2 := by
      ring
    rw [harg1, harg2]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    rw [eq_div_iff (mul_ne_zero two_ne_zero hne)]
    linear_combination
      (Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))
        - Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)) * hI2
  rw [heq]; exact h

-- no-dlmf: support lemma (derivative of the complex Fresnel phase `w ↦ π w²/2`);
-- no DLMF display of its own.
private lemma _kit_ctheta_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w ^ 2 / 2) ((Real.pi : ℂ) * z) z := by
  have h := ((hasDerivAt_pow 2 z).const_mul (Real.pi : ℂ)).div_const 2
  convert h using 1
  push_cast
  ring

open FLMF.Fresnel Complex in
-- no-dlmf: HasDerivAt support form of the complex 7.10.4, first half (mirrors
-- the real `fresnelAuxF_hasDerivAt`).
private lemma _kit_cfresnelAuxF_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelAuxF (-(Real.pi : ℂ) * z * cfresnelAuxG z) z := by
  have hθ := _kit_ctheta_hasDerivAt z
  have hC : HasDerivAt cfresnelC (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z :=
    _kit_cfresnelC_cos_hasDerivAt z
  have hS : HasDerivAt cfresnelS (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z :=
    _kit_cfresnelS_sin_hasDerivAt z
  have h1 := ((hasDerivAt_const z ((1 : ℂ) / 2)).sub hS).mul hθ.ccos
  have h2 := ((hasDerivAt_const z ((1 : ℂ) / 2)).sub hC).mul hθ.csin
  have h := h1.sub h2
  unfold cfresnelAuxF
  convert h using 1
  unfold cfresnelAuxG
  simp only [Pi.sub_apply]
  ring

open FLMF.Fresnel Complex in
-- no-dlmf: HasDerivAt support form of the complex 7.10.4, second half (mirrors
-- the real `fresnelAuxG_hasDerivAt`).
private lemma _kit_cfresnelAuxG_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelAuxG ((Real.pi : ℂ) * z * cfresnelAuxF z - 1) z := by
  have hθ := _kit_ctheta_hasDerivAt z
  have hC : HasDerivAt cfresnelC (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z :=
    _kit_cfresnelC_cos_hasDerivAt z
  have hS : HasDerivAt cfresnelS (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z :=
    _kit_cfresnelS_sin_hasDerivAt z
  have h1 := ((hasDerivAt_const z ((1 : ℂ) / 2)).sub hC).mul hθ.ccos
  have h2 := ((hasDerivAt_const z ((1 : ℂ) / 2)).sub hS).mul hθ.csin
  have h := h1.add h2
  unfold cfresnelAuxG
  convert h using 1
  unfold cfresnelAuxF
  simp only [Pi.sub_apply]
  linear_combination Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z ^ 2 / 2)

open FLMF.Fresnel in
/-- **DLMF 7.10.4** — derivatives of the complex Fresnel auxiliary functions
`f(z), g(z)` (7.2.10–7.2.11): `f′(z) = -π z g(z)` and `g′(z) = π z f(z) - 1`,
for complex `z`.

DLMF 7.10.4.
DAG: E-7.10.4.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem cfresnel_7_10_4 (z : ℂ) :
    deriv cfresnelAuxF z = -(Real.pi : ℂ) * z * cfresnelAuxG z
      ∧ deriv cfresnelAuxG z = (Real.pi : ℂ) * z * cfresnelAuxF z - 1 := by
  exact ⟨(_kit_cfresnelAuxF_hasDerivAt z).deriv, (_kit_cfresnelAuxG_hasDerivAt z).deriv⟩

end FLMF.Error
