import FLMF.Chapter7.Erf
import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.KummerBridge
import FLMF.Chapter7.FresnelBasic
import FLMF.Chapter7.FresnelComplex
import FLMF.Support.BesselSpherical
import FLMF.Support.BesselModifiedSpherical
import FLMF.Support.Chebyshev
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Error/Fresnel series expansions (DLMF §7.6)

Statement surfaces for the Maclaurin and Bessel-coefficient series expansions of
the error function `erf` and the Fresnel integrals `C`, `S` (DLMF §7.6).

FLMF's `erf`, `fresnelC`, `fresnelS` are the REAL-valued forms, matching the
DLMF normalization (`erf x = (2/√π) ∫₀ˣ e^{-t²}`, `C x = ∫₀ˣ cos(π t²/2)`,
`S x = ∫₀ˣ sin(π t²/2)`). We state the real specializations of the convergent
power series; equations requiring complex `erf` or the Faddeeva function `w(z)`
are recorded as documented deferrals. The Bessel-coefficient expansions
(7.6.8–7.6.11) use FLMF's spherical Bessel functions `FLMF.Bessel.sphericalJ`
and modified spherical Bessel functions `FLMF.Bessel.modSphericalI` (DLMF §10.47).

7.6.1 is covered elsewhere (`Error/KummerBridge.lean`, `cerf_eq_tsum`) and is
skipped here; 7.6.2 — the `e^{−z²}`-factored companion series — is stated below
as `cerf_7_6_2`, proved from the Kummer form of `erf` (DLMF 7.11.4) supplied by
that same bridge.
-/

namespace FLMF.Error

open Real
open scoped Real

/-! ## 7.6.2 — the `e^{−z²}`-factored Maclaurin series

DLMF 7.6.2 reads `erf z = (2/√π) e^{−z²} ∑ₙ 2ⁿ z^{2n+1}/(1·3⋯(2n+1))`.  It is
the Kummer-transformed companion of 7.6.1: by DLMF 7.11.4 (second member,
`erf_7_11_4`) `erf z = (2z/√π) e^{−z²} M(1, 3/2, z²)`, and the `M(1, 3/2, ·)`
coefficients collapse to `cₙ = 1/(3/2)ₙ = 2ⁿ/(1·3⋯(2n+1))`, which is exactly the
series above once the factor `z` is absorbed. -/

-- no-dlmf: the odd product `1·3·5···(2n+1) = ∏_{k<n+1}(2k+1)` against the
-- Pochhammer value `(3/2)ₙ`; support lemma for `cerf_7_6_2`, no DLMF display
/-- `∏_{k<n+1}(2k+1) = 2ⁿ·(3/2)ₙ` (the odd product against `ascPochhammer`). -/
private lemma cser762_prod_eq (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), (2 * (k : ℂ) + 1))
      = 2 ^ n * (ascPochhammer ℂ n).eval (3 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, ascPochhammer_succ_eval]
    push_cast
    ring

-- no-dlmf: nonvanishing of the odd product; support lemma for `cerf_7_6_2`
private lemma cser762_prod_ne_zero (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), (2 * (k : ℂ) + 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  intro h
  have h' : ((2 * k + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  exact Nat.cast_ne_zero.2 (by lia) h'

-- no-dlmf: pure Kummer-coefficient collapse `cₙ(1, 3/2) = 2ⁿ/(1·3⋯(2n+1))`;
-- support lemma for `cerf_7_6_2`, no DLMF display of its own
/-- The `M(1, 3/2, ·)` coefficients: `cₙ(1, 3/2) = 2ⁿ/(1·3⋯(2n+1))`. -/
private lemma cser762_coeff (n : ℕ) :
    FLMF.Hypergeometric.kummerCoefficient (1 : ℂ) (3 / 2) n
      = 2 ^ n / ∏ k ∈ Finset.range (n + 1), (2 * (k : ℂ) + 1) := by
  have hprod := cser762_prod_ne_zero n
  have hP : (ascPochhammer ℂ n).eval (3 / 2) ≠ 0 := by
    intro h
    apply hprod
    rw [cser762_prod_eq n, h, mul_zero]
  have hone : (ascPochhammer ℂ n).eval 1 = ((Nat.factorial n : ℕ) : ℂ) :=
    ascPochhammer_eval_one ℂ n
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  rw [FLMF.Hypergeometric.kummerCoefficient, hone, cser762_prod_eq n]
  field_simp

/-- **DLMF 7.6.2** — the `e^{−z²}`-factored Maclaurin series of the complex error
function,
`erf z = (2/√π)·e^{−z²}·∑ₙ 2ⁿ z^{2n+1}/(1·3⋯(2n+1))`, for `z` complex.

DLMF 7.6.2.
DAG: E-7.6.2.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_6_2 (z : ℂ) :
    FLMF.Error.cerf z =
      2 / (Real.sqrt π : ℂ) * Complex.exp (-z ^ 2) *
        ∑' n : ℕ,
          (2 : ℂ) ^ n * z ^ (2 * n + 1) /
            ∏ k ∈ Finset.range (n + 1), (2 * (k : ℂ) + 1) := by
  have hM := (FLMF.Hypergeometric.kummerM_hasSum (1 : ℂ) (3 / 2) (z ^ 2)).mul_left z
  have hterm : (fun n : ℕ =>
        z * (FLMF.Hypergeometric.kummerCoefficient (1 : ℂ) (3 / 2) n * (z ^ 2) ^ n))
      = fun n : ℕ =>
        (2 : ℂ) ^ n * z ^ (2 * n + 1) / ∏ k ∈ Finset.range (n + 1), (2 * (k : ℂ) + 1) := by
    funext n
    have hprod := cser762_prod_ne_zero n
    rw [cser762_coeff n, ← pow_mul, pow_succ' z (2 * n)]
    field_simp
  rw [hterm] at hM
  rw [(erf_7_11_4 z).2, hM.tsum_eq]
  ring

-- 7.6.3 (RESOLVED in Error/Faddeeva.lean as `erf_7_6_3`, against the complex
-- Faddeeva `faddeeva`/`cerf` keystone). Original deferral kept for context:
-- 7.6.3: the Faddeeva function expansion
--   w(z) = ∑ₙ (iz)ⁿ / Γ(n/2 + 1).
-- `w(z)` is the complex scaled complementary error function (Faddeeva
-- function), which FLMF does not provide (its `erf`/`erfc` are real-valued).
-- No faithful real specialization exists. Deferred: needs complex `w(z)`.

/-! ## Shared complex-derivative infrastructure for 7.6.4–7.6.7

`HasDerivAt cfresnelC (cos(πz²/2))` / `HasDerivAt cfresnelS (sin(πz²/2))` are
already proved in `Error/Ch7Derivatives.lean` (`_kit_cfresnelC_cos_hasDerivAt` /
`_kit_cfresnelS_sin_hasDerivAt`), but those are `private` to that file, so we
reconstruct the same short chain here from the same PUBLIC building blocks
(`cfresnel_7_5_8`, `FLMF.Error.hasDerivAt_cerf`,
`hasDerivAt_cfresnelC_add_I_mul_cfresnelS`) for reuse by the complex 7.6.4–7.6.7
surfaces below. -/

open FLMF.Fresnel in
-- no-dlmf: support lemma (derivative of the complex Fresnel `C - iS` combination
-- via the lower-sign branch of `cfresnel_7_5_8`, chained through `hasDerivAt_cerf`);
-- reconstructed locally (see the block comment above), no DLMF display of its own.
private lemma cser76_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt (z : ℂ) :
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
-- assembled from the `C+iS`/`C-iS` combined derivatives); reconstructed locally,
-- no DLMF display of its own.
private lemma cser76_cfresnelC_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelC
      ((Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          + Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / 2) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := cser76_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt z
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
-- assembled from the `C+iS`/`C-iS` combined derivatives); reconstructed locally,
-- no DLMF display of its own.
private lemma cser76_cfresnelS_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelS
      ((Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / (2 * Complex.I)) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := cser76_cfresnelC_sub_I_mul_cfresnelS_hasDerivAt z
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
-- no-dlmf: support lemma (`Complex.cos` reformulation of
-- `cser76_cfresnelC_hasDerivAt`); reconstructed locally, no DLMF display of its own.
private lemma cser76_cfresnelC_cos_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelC (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have h := cser76_cfresnelC_hasDerivAt z
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
-- no-dlmf: support lemma (`Complex.sin` reformulation of
-- `cser76_cfresnelS_hasDerivAt`); reconstructed locally, no DLMF display of its own.
private lemma cser76_cfresnelS_sin_hasDerivAt (z : ℂ) :
    HasDerivAt cfresnelS (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have h := cser76_cfresnelS_hasDerivAt z
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

-- no-dlmf: series summand helper for 7.6.4, no DLMF counterpart
private noncomputable def erf764f (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)) * x ^ (4 * n + 1)

-- no-dlmf: termwise derivative helper for 7.6.4, no DLMF counterpart
private noncomputable def erf764t (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n) / (2 * n).factorial * x ^ (4 * n)

-- no-dlmf: termwise differentiation helper for 7.6.4, no DLMF counterpart
private lemma erf764_hasDerivAt_f (n : ℕ) (y : ℝ) : HasDerivAt (erf764f n) (erf764t n y) y := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (4 * n + 1)) (((4 * n + 1 : ℕ) : ℝ) * y ^ (4 * n + 1 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1 : ℝ) ^ n * (π / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)))
  have hval : (-1 : ℝ) ^ n * (π / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)) *
      (((4 * n + 1 : ℕ) : ℝ) * y ^ (4 * n + 1 - 1)) = erf764t n y := by
    simp only [erf764t]
    rw [show 4 * n + 1 - 1 = 4 * n from rfl]
    have hfac : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (2 * n).factorial_ne_zero
    have h41 : ((4 : ℝ) * n + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← hval]
  exact h

-- no-dlmf: uniform bound helper for 7.6.4, no DLMF counterpart
private lemma erf764_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℝ) (hy : |y| ≤ R) :
    ‖erf764t n y‖ ≤ ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hfacpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast (2 * n).factorial_pos
  have hnfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n)
  have hy4 : |y| ^ (4 * n) ≤ R ^ (4 * n) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have habs : ‖erf764t n y‖ = (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) * |y| ^ (4 * n) := by
    rw [Real.norm_eq_abs, erf764t, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_pow,
      show |(-1 : ℝ)| = 1 by norm_num, one_pow, one_mul, abs_of_pos hpi2, abs_of_pos hfacpos]
  rw [habs]
  have hcoef : (0 : ℝ) ≤ (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) := by positivity
  have step1 : (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) * |y| ^ (4 * n) ≤
      (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) * R ^ (4 * n) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : ((π / 2) ^ 2 * R ^ 4) ^ n = (π / 2) ^ (2 * n) * R ^ (4 * n) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hnfacpos hnle

-- no-dlmf: cosine-series identification helper for 7.6.4, no DLMF counterpart
private lemma erf764_hasSum_t (x : ℝ) :
    HasSum (fun n => erf764t n x) (Real.cos (π * x ^ 2 / 2)) := by
  have h := Real.hasSum_cos (π * x ^ 2 / 2)
  have heq : (fun n : ℕ => (-1 : ℝ) ^ n * (π * x ^ 2 / 2) ^ (2 * n) / (2 * n).factorial) =
      fun n => erf764t n x := by
    funext n
    simp only [erf764t]
    rw [show π * x ^ 2 / 2 = (π / 2) * x ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  rwa [heq] at h

-- no-dlmf: series differentiability helper for 7.6.4, no DLMF counterpart
private lemma erf764_hasDerivAt_Ser (z : ℝ) :
    HasDerivAt (fun x => ∑' n, erf764f n x) (Real.cos (π * z ^ 2 / 2)) z := by
  set R := |z| + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial) :=
    Real.summable_pow_div_factorial ((π / 2) ^ 2 * R ^ 4)
  have hopen : IsOpen (Set.Ioo (-R) R) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-R) R) := isPreconnected_Ioo
  have hz : z ∈ Set.Ioo (-R) R := by
    constructor
    · nlinarith [neg_abs_le z, abs_nonneg z]
    · nlinarith [le_abs_self z, abs_nonneg z]
  have hzero : (0 : ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> [nlinarith [abs_nonneg z]; nlinarith [abs_nonneg z]]
  have hbound : ∀ n y, y ∈ Set.Ioo (-R) R → ‖erf764t n y‖ ≤ ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply erf764_bound R hR n y
    rw [abs_le]
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hg0 : Summable (fun n => erf764f n (0 : ℝ)) := by
    have : (fun n => erf764f n (0 : ℝ)) = fun _ => 0 := by
      funext n; simp [erf764f]
    rw [this]; exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => erf764_hasDerivAt_f n y) hbound hzero hg0 hz
  rwa [(erf764_hasSum_t z).tsum_eq] at h

-- no-dlmf: real/narrowed restriction of DLMF 7.6.4; faithful surface is cfresnel_7_6_4
/-- Maclaurin series for the Fresnel cosine integral `C`, real specialization
(DLMF 7.6.4 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_4 (z : ℝ) :
    FLMF.Fresnel.fresnelC z =
      ∑' n : ℕ,
        (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n) /
            ((2 * n).factorial * (4 * n + 1)) * z ^ (4 * n + 1) := by
  have hfres : ∀ x : ℝ, HasDerivAt FLMF.Fresnel.fresnelC (Real.cos (π * x ^ 2 / 2)) x := by
    intro x
    have := FLMF.Fresnel.hasDerivAt_fresnelC x
    simpa [FLMF.Fresnel.cosArg] using this
  set G : ℝ → ℝ := fun y => ∑' n, erf764f n y with hGdef
  have hH : ∀ x : ℝ, HasDerivAt (fun y => G y - FLMF.Fresnel.fresnelC y) 0 x := by
    intro x
    have := (erf764_hasDerivAt_Ser x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℝ (fun y => G y - FLMF.Fresnel.fresnelC y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.fresnelC y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have : (fun n => erf764f n (0 : ℝ)) = fun _ => 0 := by funext n; simp [erf764f]
    rw [this]; exact tsum_zero
  rw [hG0, FLMF.Fresnel.fresnelC_zero] at hz
  have hEq : FLMF.Fresnel.fresnelC z = G z := by linarith [hz]
  rw [hEq]
  simp only [hGdef, erf764f]

-- no-dlmf: series summand helper for complex 7.6.4, no DLMF counterpart
private noncomputable def cerf764f (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)) * x ^ (4 * n + 1)

-- no-dlmf: termwise derivative helper for complex 7.6.4, no DLMF counterpart
private noncomputable def cerf764t (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n) / (2 * n).factorial * x ^ (4 * n)

-- no-dlmf: termwise differentiation helper for complex 7.6.4, no DLMF counterpart
private lemma cerf764_hasDerivAt_f (n : ℕ) (y : ℂ) : HasDerivAt (cerf764f n) (cerf764t n y) y := by
  have hpow : HasDerivAt (fun x : ℂ => x ^ (4 * n + 1)) (((4 * n + 1 : ℕ) : ℂ) * y ^ (4 * n + 1 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)))
  have hval : (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n) / ((2 * n).factorial * (4 * n + 1)) *
      (((4 * n + 1 : ℕ) : ℂ) * y ^ (4 * n + 1 - 1)) = cerf764t n y := by
    simp only [cerf764t]
    rw [show 4 * n + 1 - 1 = 4 * n from rfl]
    have hfac : ((2 * n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (2 * n).factorial_ne_zero
    have h41 : ((4 : ℂ) * n + 1) ≠ 0 := by
      have h : (4 * n + 1 : ℕ) ≠ 0 := by omega
      exact_mod_cast h
    push_cast
    field_simp
  rw [← hval]
  exact h

-- no-dlmf: uniform bound helper for complex 7.6.4, no DLMF counterpart
private lemma cerf764_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℂ) (hy : ‖y‖ ≤ R) :
    ‖cerf764t n y‖ ≤ ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hfacpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast (2 * n).factorial_pos
  have hnfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n)
  have hcoeff : cerf764t n y =
      (((-1 : ℝ) ^ n * (π / 2) ^ (2 * n) / (2 * n).factorial : ℝ) : ℂ) * y ^ (4 * n) := by
    simp only [cerf764t]
    push_cast
    ring
  have hcoefabs : |(-1 : ℝ) ^ n * (π / 2) ^ (2 * n) / (2 * n).factorial| =
      (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    rw [abs_div, abs_mul, abs_pow, abs_pow,
      show |(-1 : ℝ)| = 1 by norm_num, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < π / 2), abs_of_pos hfacpos]
  rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcoefabs, norm_pow]
  have hy4 : ‖y‖ ^ (4 * n) ≤ R ^ (4 * n) := pow_le_pow_left₀ (norm_nonneg y) hy _
  have hcoef : (0 : ℝ) ≤ (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) := by positivity
  have step1 : (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) * ‖y‖ ^ (4 * n) ≤
      (π / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) * R ^ (4 * n) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : ((π / 2) ^ 2 * R ^ 4) ^ n = (π / 2) ^ (2 * n) * R ^ (4 * n) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hnfacpos hnle

-- no-dlmf: cosine-series identification helper for complex 7.6.4, no DLMF counterpart
private lemma cerf764_hasSum_t (x : ℂ) :
    HasSum (fun n => cerf764t n x) (Complex.cos ((Real.pi : ℂ) * x ^ 2 / 2)) := by
  have h := Complex.hasSum_cos ((Real.pi : ℂ) * x ^ 2 / 2)
  have heq : (fun n : ℕ => (-1 : ℂ) ^ n * ((Real.pi : ℂ) * x ^ 2 / 2) ^ (2 * n) / (2 * n).factorial) =
      fun n => cerf764t n x := by
    funext n
    simp only [cerf764t]
    rw [show (Real.pi : ℂ) * x ^ 2 / 2 = ((Real.pi : ℂ) / 2) * x ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  rwa [heq] at h

-- no-dlmf: series differentiability helper for complex 7.6.4, no DLMF counterpart
private lemma cerf764_hasDerivAt_Ser (z : ℂ) :
    HasDerivAt (fun x => ∑' n, cerf764f n x) (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  set R := ‖z‖ + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial) :=
    Real.summable_pow_div_factorial ((π / 2) ^ 2 * R ^ 4)
  have hopen : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hRdef]
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_self]
    linarith [norm_nonneg z]
  have hbound : ∀ n y, y ∈ Metric.ball (0 : ℂ) R →
      ‖cerf764t n y‖ ≤ ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply cerf764_bound R hR n y
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  have hg0 : Summable (fun n => cerf764f n (0 : ℂ)) := by
    have : (fun n => cerf764f n (0 : ℂ)) = fun _ => 0 := by
      funext n; simp [cerf764f]
    rw [this]; exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => cerf764_hasDerivAt_f n y) hbound hzero hg0 hz
  rwa [(cerf764_hasSum_t z).tsum_eq] at h

/-- **DLMF 7.6.4** — Maclaurin series for the complex Fresnel cosine integral `C`,
    `C(z) = ∑ₙ (-1)ⁿ(π/2)^{2n}/((2n)!(4n+1)) z^{4n+1}`, for `z` complex.

DAG: E-7.6.4.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_6_4 (z : ℂ) :
    FLMF.Fresnel.cfresnelC z =
      ∑' n : ℕ,
        (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n) /
            ((2 * n).factorial * (4 * n + 1)) * z ^ (4 * n + 1) := by
  have hfres : ∀ x : ℂ, HasDerivAt FLMF.Fresnel.cfresnelC (Complex.cos ((Real.pi : ℂ) * x ^ 2 / 2)) x :=
    cser76_cfresnelC_cos_hasDerivAt
  set G : ℂ → ℂ := fun y => ∑' n, cerf764f n y with hGdef
  have hH : ∀ x : ℂ, HasDerivAt (fun y => G y - FLMF.Fresnel.cfresnelC y) 0 x := by
    intro x
    have := (cerf764_hasDerivAt_Ser x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℂ (fun y => G y - FLMF.Fresnel.cfresnelC y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.cfresnelC y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have : (fun n => cerf764f n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf764f]
    rw [this]; exact tsum_zero
  rw [hG0, FLMF.Fresnel.cfresnelC_zero] at hz
  have hEq : FLMF.Fresnel.cfresnelC z = G z := by linear_combination -hz
  rw [hEq]
  simp only [hGdef, cerf764f]

/-- The odd product `1·3·5···(2m-1) = ∏_{k<m}(2k+1)`. -/
private noncomputable def erf765Pr (m : ℕ) : ℝ := ∏ k ∈ Finset.range m, (2 * k + 1 : ℝ)

private lemma erf765_Pr_succ (m : ℕ) : erf765Pr (m + 1) = erf765Pr m * (2 * m + 1) := Finset.prod_range_succ _ _

private lemma erf765_Pr_pos (m : ℕ) : 0 < erf765Pr m := by
  apply Finset.prod_pos
  intro k _
  positivity

/-- `m! ≤ erf765Pr m` since each factor `2k+1 ≥ k+1`. -/
private lemma erf765_factorial_le_Pr (m : ℕ) : (m.factorial : ℝ) ≤ erf765Pr m := by
  induction m with
  | zero => simp [erf765Pr]
  | succ n ih =>
    rw [erf765_Pr_succ, Nat.factorial_succ]
    have hpr := erf765_Pr_pos n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hfac : (0:ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [ih, hpr, hn, hfac]

/-- Aser summand: `(-1)^n π^{2n}/erf765Pr(2n+1) x^{4n+1}`. -/
private noncomputable def erf765fA (n : ℕ) (x : ℝ) : ℝ := (-1)^n * π^(2*n) / erf765Pr (2*n+1) * x^(4*n+1)

/-- Bser summand: `(-1)^n π^{2n+1}/erf765Pr(2n+2) x^{4n+3}`. -/
private noncomputable def erf765fB (n : ℕ) (x : ℝ) : ℝ := (-1)^n * π^(2*n+1) / erf765Pr (2*n+2) * x^(4*n+3)

/-- Derivative of `erf765fA n`: `(-1)^n π^{2n}/erf765Pr(2n) x^{4n}`. -/
private noncomputable def erf765tA (n : ℕ) (x : ℝ) : ℝ := (-1)^n * π^(2*n) / erf765Pr (2*n) * x^(4*n)

/-- Derivative of `erf765fB n`: `(-1)^n π^{2n+1}/erf765Pr(2n+1) x^{4n+2}`. -/
private noncomputable def erf765tB (n : ℕ) (x : ℝ) : ℝ := (-1)^n * π^(2*n+1) / erf765Pr (2*n+1) * x^(4*n+2)

private lemma erf765_hasDerivAt_fA (n : ℕ) (y : ℝ) : HasDerivAt (erf765fA n) (erf765tA n y) y := by
  have hpow : HasDerivAt (fun x : ℝ => x^(4*n+1)) (((4*n+1 : ℕ) : ℝ) * y^(4*n+1-1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1:ℝ)^n * π^(2*n) / erf765Pr (2*n+1))
  have hval : (-1:ℝ)^n * π^(2*n) / erf765Pr (2*n+1) * (((4*n+1 : ℕ) : ℝ) * y^(4*n+1-1)) = erf765tA n y := by
    simp only [erf765tA]
    rw [show 4*n+1-1 = 4*n from rfl, erf765_Pr_succ (2*n)]
    have hpr := erf765_Pr_pos (2*n)
    push_cast
    field_simp
    ring
  rw [← hval]
  exact h

private lemma erf765_hasDerivAt_fB (n : ℕ) (y : ℝ) : HasDerivAt (erf765fB n) (erf765tB n y) y := by
  have hpow : HasDerivAt (fun x : ℝ => x^(4*n+3)) (((4*n+3 : ℕ) : ℝ) * y^(4*n+3-1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1:ℝ)^n * π^(2*n+1) / erf765Pr (2*n+2))
  have hval : (-1:ℝ)^n * π^(2*n+1) / erf765Pr (2*n+2) * (((4*n+3 : ℕ) : ℝ) * y^(4*n+3-1)) = erf765tB n y := by
    simp only [erf765tB]
    rw [show 4*n+3-1 = 4*n+2 from rfl, show 2*n+2 = (2*n+1)+1 from rfl, erf765_Pr_succ (2*n+1)]
    have hpr := erf765_Pr_pos (2*n+1)
    push_cast
    field_simp
    ring
  rw [← hval]
  exact h

/-- Uniform bound for `erf765tA` on the ball of radius `R`. -/
private lemma erf765_boundA (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℝ) (hy : |y| ≤ R) :
    ‖erf765tA n y‖ ≤ (π^2 * R^4)^n / n.factorial := by
  have hPr := erf765_Pr_pos (2*n)
  have hfacpos : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ erf765Pr (2*n) :=
    le_trans (by exact_mod_cast Nat.factorial_le (by omega : n ≤ 2*n)) (erf765_factorial_le_Pr (2*n))
  have hy4 : |y|^(4*n) ≤ R^(4*n) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have habs : ‖erf765tA n y‖ = π^(2*n) / erf765Pr (2*n) * |y|^(4*n) := by
    rw [Real.norm_eq_abs, erf765tA, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_pow,
      show |(-1:ℝ)| = 1 by norm_num, one_pow, one_mul, abs_of_pos Real.pi_pos, abs_of_pos hPr]
  rw [habs]
  have hcoef : (0:ℝ) ≤ π^(2*n) / erf765Pr (2*n) := by positivity
  have step1 : π^(2*n) / erf765Pr (2*n) * |y|^(4*n) ≤ π^(2*n) / erf765Pr (2*n) * R^(4*n) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : (π^2 * R^4)^n = π^(2*n) * R^(4*n) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hfacpos hnle

/-- Uniform bound for `erf765tB` on the ball of radius `R`. -/
private lemma erf765_boundB (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℝ) (hy : |y| ≤ R) :
    ‖erf765tB n y‖ ≤ π * R^2 * (π^2 * R^4)^n / n.factorial := by
  have hPr := erf765_Pr_pos (2*n+1)
  have hfacpos : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ erf765Pr (2*n+1) :=
    le_trans (by exact_mod_cast Nat.factorial_le (by omega : n ≤ 2*n+1)) (erf765_factorial_le_Pr (2*n+1))
  have hy4 : |y|^(4*n+2) ≤ R^(4*n+2) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have habs : ‖erf765tB n y‖ = π^(2*n+1) / erf765Pr (2*n+1) * |y|^(4*n+2) := by
    rw [Real.norm_eq_abs, erf765tB, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_pow,
      show |(-1:ℝ)| = 1 by norm_num, one_pow, one_mul, abs_of_pos Real.pi_pos, abs_of_pos hPr]
  rw [habs]
  have hcoef : (0:ℝ) ≤ π^(2*n+1) / erf765Pr (2*n+1) := by positivity
  have step1 : π^(2*n+1) / erf765Pr (2*n+1) * |y|^(4*n+2) ≤ π^(2*n+1) / erf765Pr (2*n+1) * R^(4*n+2) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : π * R^2 * (π^2 * R^4)^n = π^(2*n+1) * R^(4*n+2) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hfacpos hnle

/-- Aser is differentiable at every point, with derivative the termwise sum `∑ erf765tA n z`. -/
private lemma erf765_hasDerivAt_Aser (z : ℝ) :
    HasDerivAt (fun x => ∑' n, erf765fA n x) (∑' n, erf765tA n z) z := by
  set R := |z| + 1 with hRdef
  have hR : (0:ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => (π^2 * R^4)^n / n.factorial) :=
    Real.summable_pow_div_factorial (π^2 * R^4)
  have hopen : IsOpen (Set.Ioo (-R) R) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-R) R) := isPreconnected_Ioo
  have hz : z ∈ Set.Ioo (-R) R := by
    constructor
    · have := abs_le.mp (le_refl |z|); nlinarith [abs_nonneg z, neg_abs_le z]
    · have := le_abs_self z; nlinarith [abs_nonneg z]
  have hzero : (0:ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> [nlinarith [abs_nonneg z]; nlinarith [abs_nonneg z]]
  have hderiv : ∀ n y, HasDerivAt (erf765fA n) (erf765tA n y) y := erf765_hasDerivAt_fA
  have hbound : ∀ n y, y ∈ Set.Ioo (-R) R → ‖erf765tA n y‖ ≤ (π^2 * R^4)^n / n.factorial := by
    intro n y hy
    apply erf765_boundA R hR n y
    rw [abs_le]
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hg0 : Summable (fun n => erf765fA n (0:ℝ)) := by
    have : (fun n => erf765fA n (0:ℝ)) = fun _ => 0 := by
      funext n; simp [erf765fA]
    rw [this]; exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => hderiv n y) hbound hzero hg0 hz

/-- Bser is differentiable at every point, with derivative the termwise sum `∑ erf765tB n z`. -/
private lemma erf765_hasDerivAt_Bser (z : ℝ) :
    HasDerivAt (fun x => ∑' n, erf765fB n x) (∑' n, erf765tB n z) z := by
  set R := |z| + 1 with hRdef
  have hR : (0:ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => π * R^2 * (π^2 * R^4)^n / n.factorial) := by
    have := (Real.summable_pow_div_factorial (π^2 * R^4)).mul_left (π * R^2)
    simpa [mul_div_assoc] using this
  have hopen : IsOpen (Set.Ioo (-R) R) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-R) R) := isPreconnected_Ioo
  have hz : z ∈ Set.Ioo (-R) R := by
    constructor
    · nlinarith [neg_abs_le z, abs_nonneg z]
    · nlinarith [le_abs_self z, abs_nonneg z]
  have hzero : (0:ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> [nlinarith [abs_nonneg z]; nlinarith [abs_nonneg z]]
  have hderiv : ∀ n y, HasDerivAt (erf765fB n) (erf765tB n y) y := erf765_hasDerivAt_fB
  have hbound : ∀ n y, y ∈ Set.Ioo (-R) R → ‖erf765tB n y‖ ≤ π * R^2 * (π^2 * R^4)^n / n.factorial := by
    intro n y hy
    apply erf765_boundB R hR n y
    rw [abs_le]
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hg0 : Summable (fun n => erf765fB n (0:ℝ)) := by
    have : (fun n => erf765fB n (0:ℝ)) = fun _ => 0 := by
      funext n; simp [erf765fB]
    rw [this]; exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => hderiv n y) hbound hzero hg0 hz

/-- Summability of the `erf765tA` series at any point. -/
private lemma erf765_summable_tA (z : ℝ) : Summable (fun n => erf765tA n z) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (π^2 * (|z|+1)^4))
  intro n
  exact erf765_boundA (|z|+1) (by positivity) n z (by linarith [le_abs_self z, neg_abs_le z])

/-- B cancellation: `∑ erf765tB n z = (πz)·∑ erf765fA n z`. -/
private lemma erf765_hcancelB (z : ℝ) : (∑' n, erf765tB n z) = (π*z) * (∑' n, erf765fA n z) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [erf765tB, erf765fA]
  ring

/-- A cancellation: `∑ erf765tA n z + (πz)·∑ erf765fB n z = 1`. -/
private lemma erf765_hcancelA (z : ℝ) : (∑' n, erf765tA n z) + (π*z) * (∑' n, erf765fB n z) = 1 := by
  have hsum := erf765_summable_tA z
  have hkey : (π*z) * (∑' n, erf765fB n z) = - ∑' n, erf765tA (n+1) z := by
    rw [← tsum_mul_left, ← tsum_neg]
    apply tsum_congr
    intro n
    simp only [erf765fB, erf765tA]
    rw [show 2*(n+1) = 2*n+2 from by ring, show 4*(n+1) = 4*n+4 from by ring]
    ring
  rw [hkey, Summable.tsum_eq_zero_add hsum]
  have h0 : erf765tA 0 z = 1 := by simp [erf765tA, erf765Pr]
  rw [h0]
  ring

-- no-dlmf: real/narrowed restriction of DLMF 7.6.5; faithful surface is cfresnel_7_6_5
/-- Cosine/sine-modulated series for the Fresnel cosine integral `C`, real
specialization (DLMF 7.6.5 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_5 (z : ℝ) :
    FLMF.Fresnel.fresnelC z =
      Real.cos (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℝ) ^ n * Real.pi ^ (2 * n) /
                (∏ k ∈ Finset.range (2 * n + 1), (2 * k + 1 : ℝ)) *
              z ^ (4 * n + 1)) +
        Real.sin (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℝ) ^ n * Real.pi ^ (2 * n + 1) /
                (∏ k ∈ Finset.range (2 * n + 2), (2 * k + 1 : ℝ)) *
              z ^ (4 * n + 3)) := by
  -- Work with the function G y = cos(πy²/2)·A y + sin(πy²/2)·B y.
  have hGderiv : ∀ x : ℝ,
      HasDerivAt (fun y => Real.cos (π*y^2/2) * (∑' n, erf765fA n y)
          + Real.sin (π*y^2/2) * (∑' n, erf765fB n y)) (Real.cos (π*x^2/2)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => π * y^2/2) (π * x) x := by
      have h1 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 := h1.const_mul (π/2)
      have hfun : (fun y : ℝ => π/2 * y^2) = (fun y : ℝ => π * y^2/2) := by funext y; ring
      rw [hfun, show π/2*(2*x) = π*x from by ring] at h2
      exact h2
    have hcos := hp.cos
    have hsin := hp.sin
    have hAx := erf765_hasDerivAt_Aser x
    have hBx := erf765_hasDerivAt_Bser x
    have hprod := (hcos.mul hAx).add (hsin.mul hBx)
    convert hprod using 1
    have e1 := erf765_hcancelA x
    have e2 := erf765_hcancelB x
    rw [e2]
    linear_combination (-(Real.cos (π * x ^ 2 / 2))) * e1
  -- fresnelC has the same derivative
  have hfres : ∀ x : ℝ, HasDerivAt FLMF.Fresnel.fresnelC (Real.cos (π*x^2/2)) x := by
    intro x
    have := FLMF.Fresnel.hasDerivAt_fresnelC x
    simpa [FLMF.Fresnel.cosArg] using this
  -- H = G - fresnelC has derivative 0 everywhere, hence constant
  set G : ℝ → ℝ := fun y => Real.cos (π*y^2/2) * (∑' n, erf765fA n y)
      + Real.sin (π*y^2/2) * (∑' n, erf765fB n y) with hGdef
  have hH : ∀ x : ℝ, HasDerivAt (fun y => G y - FLMF.Fresnel.fresnelC y) 0 x := by
    intro x
    have := (hGderiv x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℝ (fun y => G y - FLMF.Fresnel.fresnelC y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.fresnelC y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have hA0 : (∑' n, erf765fA n (0:ℝ)) = 0 := by
      have : (fun n => erf765fA n (0:ℝ)) = fun _ => 0 := by funext n; simp [erf765fA]
      rw [this]; exact tsum_zero
    have hB0 : (∑' n, erf765fB n (0:ℝ)) = 0 := by
      have : (fun n => erf765fB n (0:ℝ)) = fun _ => 0 := by funext n; simp [erf765fB]
      rw [this]; exact tsum_zero
    rw [hA0, hB0]; simp
  rw [hG0, FLMF.Fresnel.fresnelC_zero] at hz
  have hEq : FLMF.Fresnel.fresnelC z = G z := by linarith [hz]
  rw [hEq]
  simp only [hGdef, erf765fA, erf765fB, erf765Pr]

-- no-dlmf: the complex odd product `1·3·5···(2m-1) = ∏_{k<m}(2k+1)`, for complex 7.6.5/7.6.7
private noncomputable def cprod765 (m : ℕ) : ℂ := ∏ k ∈ Finset.range m, (2 * (k : ℂ) + 1)

private lemma cprod765_succ (m : ℕ) : cprod765 (m + 1) = cprod765 m * (2 * (m : ℂ) + 1) :=
  Finset.prod_range_succ _ _

-- no-dlmf: `cprod765` agrees with the real `erf765Pr` under the `ℝ → ℂ` cast
private lemma cprod765_ofReal (m : ℕ) : cprod765 m = ((erf765Pr m : ℝ) : ℂ) := by
  induction m with
  | zero => simp [cprod765, erf765Pr]
  | succ n ih => rw [cprod765_succ, ih, erf765_Pr_succ]; push_cast; ring

private lemma cprod765_ne_zero (m : ℕ) : cprod765 m ≠ 0 := by
  rw [cprod765_ofReal]; exact_mod_cast (erf765_Pr_pos m).ne'

private lemma cprod765_norm (m : ℕ) : ‖cprod765 m‖ = erf765Pr m := by
  rw [cprod765_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (erf765_Pr_pos m)]

/-- Complex Aser summand: `(-1)^n π^{2n}/cprod765(2n+1) x^{4n+1}`. -/
private noncomputable def cerf765fA (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) / cprod765 (2 * n + 1) * x ^ (4 * n + 1)

/-- Complex Bser summand: `(-1)^n π^{2n+1}/cprod765(2n+2) x^{4n+3}`. -/
private noncomputable def cerf765fB (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) / cprod765 (2 * n + 2) * x ^ (4 * n + 3)

/-- Derivative of `cerf765fA n`: `(-1)^n π^{2n}/cprod765(2n) x^{4n}`. -/
private noncomputable def cerf765tA (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) / cprod765 (2 * n) * x ^ (4 * n)

/-- Derivative of `cerf765fB n`: `(-1)^n π^{2n+1}/cprod765(2n+1) x^{4n+2}`. -/
private noncomputable def cerf765tB (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) / cprod765 (2 * n + 1) * x ^ (4 * n + 2)

private lemma cerf765_hasDerivAt_fA (n : ℕ) (y : ℂ) : HasDerivAt (cerf765fA n) (cerf765tA n y) y := by
  have hpow : HasDerivAt (fun x : ℂ => x ^ (4 * n + 1)) (((4 * n + 1 : ℕ) : ℂ) * y ^ (4 * n + 1 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) / cprod765 (2 * n + 1))
  have hval : (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) / cprod765 (2 * n + 1) *
      (((4 * n + 1 : ℕ) : ℂ) * y ^ (4 * n + 1 - 1)) = cerf765tA n y := by
    simp only [cerf765tA]
    rw [show 4 * n + 1 - 1 = 4 * n from rfl, cprod765_succ (2 * n)]
    have hcast : (2 * ((2 * n : ℕ) : ℂ) + 1) = ((4 * n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    have hpr : cprod765 (2 * n) ≠ 0 := cprod765_ne_zero (2 * n)
    have h4n1 : ((4 * n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  rw [← hval]
  exact h

private lemma cerf765_hasDerivAt_fB (n : ℕ) (y : ℂ) : HasDerivAt (cerf765fB n) (cerf765tB n y) y := by
  have hpow : HasDerivAt (fun x : ℂ => x ^ (4 * n + 3)) (((4 * n + 3 : ℕ) : ℂ) * y ^ (4 * n + 3 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) / cprod765 (2 * n + 2))
  have hval : (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) / cprod765 (2 * n + 2) *
      (((4 * n + 3 : ℕ) : ℂ) * y ^ (4 * n + 3 - 1)) = cerf765tB n y := by
    simp only [cerf765tB]
    rw [show 4 * n + 3 - 1 = 4 * n + 2 from rfl, show 2 * n + 2 = (2 * n + 1) + 1 from rfl,
      cprod765_succ (2 * n + 1)]
    have hcast : (2 * ((2 * n + 1 : ℕ) : ℂ) + 1) = ((4 * n + 3 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    have hpr : cprod765 (2 * n + 1) ≠ 0 := cprod765_ne_zero (2 * n + 1)
    have h4n3 : ((4 * n + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp
  rw [← hval]
  exact h

/-- Uniform bound for `cerf765tA` on the ball of radius `R`. -/
private lemma cerf765_boundA (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℂ) (hy : ‖y‖ ≤ R) :
    ‖cerf765tA n y‖ ≤ (π ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hPr := erf765_Pr_pos (2 * n)
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ erf765Pr (2 * n) :=
    le_trans (by exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n)) (erf765_factorial_le_Pr (2 * n))
  have habs : ‖cerf765tA n y‖ = π ^ (2 * n) / erf765Pr (2 * n) * ‖y‖ ^ (4 * n) := by
    simp only [cerf765tA]
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_pow,
      show ‖(-1 : ℂ)‖ = 1 by norm_num, one_pow, one_mul,
      show ‖(Real.pi : ℂ)‖ = π by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
      cprod765_norm]
  rw [habs]
  have hy4 : ‖y‖ ^ (4 * n) ≤ R ^ (4 * n) := pow_le_pow_left₀ (norm_nonneg y) hy _
  have hcoef : (0 : ℝ) ≤ π ^ (2 * n) / erf765Pr (2 * n) := by positivity
  have step1 : π ^ (2 * n) / erf765Pr (2 * n) * ‖y‖ ^ (4 * n) ≤
      π ^ (2 * n) / erf765Pr (2 * n) * R ^ (4 * n) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : (π ^ 2 * R ^ 4) ^ n = π ^ (2 * n) * R ^ (4 * n) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hfacpos hnle

/-- Uniform bound for `cerf765tB` on the ball of radius `R`. -/
private lemma cerf765_boundB (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℂ) (hy : ‖y‖ ≤ R) :
    ‖cerf765tB n y‖ ≤ π * R ^ 2 * (π ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hPr := erf765_Pr_pos (2 * n + 1)
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ erf765Pr (2 * n + 1) :=
    le_trans (by exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)) (erf765_factorial_le_Pr (2 * n + 1))
  have habs : ‖cerf765tB n y‖ = π ^ (2 * n + 1) / erf765Pr (2 * n + 1) * ‖y‖ ^ (4 * n + 2) := by
    simp only [cerf765tB]
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_pow, norm_pow,
      show ‖(-1 : ℂ)‖ = 1 by norm_num, one_pow, one_mul,
      show ‖(Real.pi : ℂ)‖ = π by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
      cprod765_norm]
  rw [habs]
  have hy4 : ‖y‖ ^ (4 * n + 2) ≤ R ^ (4 * n + 2) := pow_le_pow_left₀ (norm_nonneg y) hy _
  have hcoef : (0 : ℝ) ≤ π ^ (2 * n + 1) / erf765Pr (2 * n + 1) := by positivity
  have step1 : π ^ (2 * n + 1) / erf765Pr (2 * n + 1) * ‖y‖ ^ (4 * n + 2) ≤
      π ^ (2 * n + 1) / erf765Pr (2 * n + 1) * R ^ (4 * n + 2) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : π * R ^ 2 * (π ^ 2 * R ^ 4) ^ n = π ^ (2 * n + 1) * R ^ (4 * n + 2) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hfacpos hnle

/-- Complex Aser is differentiable at every point, with derivative the termwise sum
`∑ cerf765tA n z`. -/
private lemma cerf765_hasDerivAt_Aser (z : ℂ) :
    HasDerivAt (fun x => ∑' n, cerf765fA n x) (∑' n, cerf765tA n z) z := by
  set R := ‖z‖ + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => (π ^ 2 * R ^ 4) ^ n / n.factorial) :=
    Real.summable_pow_div_factorial (π ^ 2 * R ^ 4)
  have hopen : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith [hRdef]
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_self]; linarith [norm_nonneg z]
  have hderiv : ∀ n y, HasDerivAt (cerf765fA n) (cerf765tA n y) y := cerf765_hasDerivAt_fA
  have hbound : ∀ n y, y ∈ Metric.ball (0 : ℂ) R → ‖cerf765tA n y‖ ≤ (π ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply cerf765_boundA R hR n y
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  have hg0 : Summable (fun n => cerf765fA n (0 : ℂ)) := by
    have : (fun n => cerf765fA n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fA]
    rw [this]; exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => hderiv n y) hbound hzero hg0 hz

/-- Complex Bser is differentiable at every point, with derivative the termwise sum
`∑ cerf765tB n z`. -/
private lemma cerf765_hasDerivAt_Bser (z : ℂ) :
    HasDerivAt (fun x => ∑' n, cerf765fB n x) (∑' n, cerf765tB n z) z := by
  set R := ‖z‖ + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => π * R ^ 2 * (π ^ 2 * R ^ 4) ^ n / n.factorial) := by
    have := (Real.summable_pow_div_factorial (π ^ 2 * R ^ 4)).mul_left (π * R ^ 2)
    simpa [mul_div_assoc] using this
  have hopen : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith [hRdef]
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_self]; linarith [norm_nonneg z]
  have hderiv : ∀ n y, HasDerivAt (cerf765fB n) (cerf765tB n y) y := cerf765_hasDerivAt_fB
  have hbound : ∀ n y, y ∈ Metric.ball (0 : ℂ) R →
      ‖cerf765tB n y‖ ≤ π * R ^ 2 * (π ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply cerf765_boundB R hR n y
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  have hg0 : Summable (fun n => cerf765fB n (0 : ℂ)) := by
    have : (fun n => cerf765fB n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fB]
    rw [this]; exact summable_zero
  exact hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => hderiv n y) hbound hzero hg0 hz

/-- Summability of the complex `cerf765tA` series at any point. -/
private lemma cerf765_summable_tA (z : ℂ) : Summable (fun n => cerf765tA n z) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (π ^ 2 * (‖z‖ + 1) ^ 4))
  intro n
  exact cerf765_boundA (‖z‖ + 1) (by positivity) n z (by linarith)

/-- Complex B cancellation: `∑ cerf765tB n z = (πz)·∑ cerf765fA n z`. -/
private lemma cerf765_hcancelB (z : ℂ) :
    (∑' n, cerf765tB n z) = ((Real.pi : ℂ) * z) * (∑' n, cerf765fA n z) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [cerf765tB, cerf765fA]
  ring

/-- Complex A cancellation: `∑ cerf765tA n z + (πz)·∑ cerf765fB n z = 1`. -/
private lemma cerf765_hcancelA (z : ℂ) :
    (∑' n, cerf765tA n z) + ((Real.pi : ℂ) * z) * (∑' n, cerf765fB n z) = 1 := by
  have hsum := cerf765_summable_tA z
  have hkey : ((Real.pi : ℂ) * z) * (∑' n, cerf765fB n z) = - ∑' n, cerf765tA (n + 1) z := by
    rw [← tsum_mul_left, ← tsum_neg]
    apply tsum_congr
    intro n
    simp only [cerf765fB, cerf765tA]
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, show 4 * (n + 1) = 4 * n + 4 from by ring]
    ring
  rw [hkey, Summable.tsum_eq_zero_add hsum]
  have h0 : cerf765tA 0 z = 1 := by simp [cerf765tA, cprod765]
  rw [h0]
  ring

/-- **DLMF 7.6.5** — Cosine/sine-modulated series for the complex Fresnel
    cosine integral `C`,
    `C(z) = cos(πz²/2)·∑ₙ (-1)ⁿπ^{2n}/(1·3···(4n+1)) z^{4n+1}
      + sin(πz²/2)·∑ₙ (-1)ⁿπ^{2n+1}/(1·3···(4n+3)) z^{4n+3}`, for `z` complex.

DAG: E-7.6.5.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_6_5 (z : ℂ) :
    FLMF.Fresnel.cfresnelC z =
      Complex.cos (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) /
                (∏ k ∈ Finset.range (2 * n + 1), (2 * k + 1 : ℂ)) *
              z ^ (4 * n + 1)) +
        Complex.sin (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) /
                (∏ k ∈ Finset.range (2 * n + 2), (2 * k + 1 : ℂ)) *
              z ^ (4 * n + 3)) := by
  have hGderiv : ∀ x : ℂ,
      HasDerivAt (fun y : ℂ => Complex.cos ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fA n y)
          + Complex.sin ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fB n y))
        (Complex.cos ((Real.pi : ℂ) * x ^ 2 / 2)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) * y ^ 2 / 2) ((Real.pi : ℂ) * x) x := by
      have h1 : HasDerivAt (fun y : ℂ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have h2 := h1.const_mul ((Real.pi : ℂ) / 2)
      have hfun : (fun y : ℂ => (Real.pi : ℂ) / 2 * y ^ 2) = (fun y : ℂ => (Real.pi : ℂ) * y ^ 2 / 2) := by
        funext y; ring
      rw [hfun, show (Real.pi : ℂ) / 2 * (2 * x) = (Real.pi : ℂ) * x from by ring] at h2
      exact h2
    have hcos := hp.ccos
    have hsin := hp.csin
    have hAx := cerf765_hasDerivAt_Aser x
    have hBx := cerf765_hasDerivAt_Bser x
    have hprod := (hcos.mul hAx).add (hsin.mul hBx)
    convert hprod using 1
    have e1 := cerf765_hcancelA x
    have e2 := cerf765_hcancelB x
    rw [e2]
    linear_combination (-(Complex.cos ((Real.pi : ℂ) * x ^ 2 / 2))) * e1
  have hfres : ∀ x : ℂ, HasDerivAt FLMF.Fresnel.cfresnelC (Complex.cos ((Real.pi : ℂ) * x ^ 2 / 2)) x :=
    cser76_cfresnelC_cos_hasDerivAt
  set G : ℂ → ℂ := fun y => Complex.cos ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fA n y)
      + Complex.sin ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fB n y) with hGdef
  have hH : ∀ x : ℂ, HasDerivAt (fun y => G y - FLMF.Fresnel.cfresnelC y) 0 x := by
    intro x
    have := (hGderiv x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℂ (fun y => G y - FLMF.Fresnel.cfresnelC y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.cfresnelC y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have hA0 : (∑' n, cerf765fA n (0 : ℂ)) = 0 := by
      have : (fun n => cerf765fA n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fA]
      rw [this]; exact tsum_zero
    have hB0 : (∑' n, cerf765fB n (0 : ℂ)) = 0 := by
      have : (fun n => cerf765fB n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fB]
      rw [this]; exact tsum_zero
    rw [hA0, hB0]; simp
  rw [hG0, FLMF.Fresnel.cfresnelC_zero] at hz
  have hEq : FLMF.Fresnel.cfresnelC z = G z := by linear_combination -hz
  rw [hEq]
  simp only [hGdef, cerf765fA, cerf765fB, cprod765]

-- no-dlmf: series summand helper for 7.6.6, no DLMF counterpart
private noncomputable def erf766f (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)) * x ^ (4 * n + 3)

-- no-dlmf: termwise derivative helper for 7.6.6, no DLMF counterpart
private noncomputable def erf766t (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n + 1) / (2 * n + 1).factorial * x ^ (4 * n + 2)

-- no-dlmf: termwise differentiation helper for 7.6.6, no DLMF counterpart
private lemma erf766_hasDerivAt_f (n : ℕ) (y : ℝ) : HasDerivAt (erf766f n) (erf766t n y) y := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (4 * n + 3)) (((4 * n + 3 : ℕ) : ℝ) * y ^ (4 * n + 3 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul ((-1 : ℝ) ^ n * (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)))
  have hval : (-1 : ℝ) ^ n * (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)) *
      (((4 * n + 3 : ℕ) : ℝ) * y ^ (4 * n + 3 - 1)) = erf766t n y := by
    simp only [erf766t]
    rw [show 4 * n + 3 - 1 = 4 * n + 2 from rfl]
    have hfac : ((2 * n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (2 * n + 1).factorial_ne_zero
    have h43 : ((4 : ℝ) * n + 3) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← hval]
  exact h

-- no-dlmf: uniform bound helper for 7.6.6, no DLMF counterpart
private lemma erf766_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℝ) (hy : |y| ≤ R) :
    ‖erf766t n y‖ ≤ (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hfacpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast (2 * n + 1).factorial_pos
  have hnfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)
  have hy4 : |y| ^ (4 * n + 2) ≤ R ^ (4 * n + 2) := pow_le_pow_left₀ (abs_nonneg y) hy _
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have habs : ‖erf766t n y‖ = (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * |y| ^ (4 * n + 2) := by
    rw [Real.norm_eq_abs, erf766t, abs_mul, abs_div, abs_mul, abs_pow, abs_pow, abs_pow,
      show |(-1 : ℝ)| = 1 by norm_num, one_pow, one_mul, abs_of_pos hpi2, abs_of_pos hfacpos]
  rw [habs]
  have hcoef : (0 : ℝ) ≤ (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by positivity
  have step1 : (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * |y| ^ (4 * n + 2) ≤
      (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * R ^ (4 * n + 2) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n = (π / 2) ^ (2 * n + 1) * R ^ (4 * n + 2) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hnfacpos hnle

-- no-dlmf: sine-series identification helper for 7.6.6, no DLMF counterpart
private lemma erf766_hasSum_t (x : ℝ) :
    HasSum (fun n => erf766t n x) (Real.sin (π * x ^ 2 / 2)) := by
  have h := Real.hasSum_sin (π * x ^ 2 / 2)
  have heq : (fun n : ℕ => (-1 : ℝ) ^ n * (π * x ^ 2 / 2) ^ (2 * n + 1) / (2 * n + 1).factorial) =
      fun n => erf766t n x := by
    funext n
    simp only [erf766t]
    rw [show π * x ^ 2 / 2 = (π / 2) * x ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  rwa [heq] at h

-- no-dlmf: series differentiability helper for 7.6.6, no DLMF counterpart
private lemma erf766_hasDerivAt_Ser (z : ℝ) :
    HasDerivAt (fun x => ∑' n, erf766f n x) (Real.sin (π * z ^ 2 / 2)) z := by
  set R := |z| + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial) := by
    have := (Real.summable_pow_div_factorial ((π / 2) ^ 2 * R ^ 4)).mul_left ((π / 2) * R ^ 2)
    simpa [mul_div_assoc] using this
  have hopen : IsOpen (Set.Ioo (-R) R) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-R) R) := isPreconnected_Ioo
  have hz : z ∈ Set.Ioo (-R) R := by
    constructor
    · nlinarith [neg_abs_le z, abs_nonneg z]
    · nlinarith [le_abs_self z, abs_nonneg z]
  have hzero : (0 : ℝ) ∈ Set.Ioo (-R) R := by
    constructor <;> [nlinarith [abs_nonneg z]; nlinarith [abs_nonneg z]]
  have hbound : ∀ n y, y ∈ Set.Ioo (-R) R →
      ‖erf766t n y‖ ≤ (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply erf766_bound R hR n y
    rw [abs_le]
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hg0 : Summable (fun n => erf766f n (0 : ℝ)) := by
    have : (fun n => erf766f n (0 : ℝ)) = fun _ => 0 := by
      funext n; simp [erf766f]
    rw [this]; exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => erf766_hasDerivAt_f n y) hbound hzero hg0 hz
  rwa [(erf766_hasSum_t z).tsum_eq] at h

-- no-dlmf: real/narrowed restriction of DLMF 7.6.6; faithful surface is cfresnel_7_6_6
/-- Maclaurin series for the Fresnel sine integral `S`, real specialization
(DLMF 7.6.6 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_6 (z : ℝ) :
    FLMF.Fresnel.fresnelS z =
      ∑' n : ℕ,
        (-1 : ℝ) ^ n * (Real.pi / 2) ^ (2 * n + 1) /
            ((2 * n + 1).factorial * (4 * n + 3)) * z ^ (4 * n + 3) := by
  have hfres : ∀ x : ℝ, HasDerivAt FLMF.Fresnel.fresnelS (Real.sin (π * x ^ 2 / 2)) x := by
    intro x
    have := FLMF.Fresnel.hasDerivAt_fresnelS x
    simpa [FLMF.Fresnel.sinArg] using this
  set G : ℝ → ℝ := fun y => ∑' n, erf766f n y with hGdef
  have hH : ∀ x : ℝ, HasDerivAt (fun y => G y - FLMF.Fresnel.fresnelS y) 0 x := by
    intro x
    have := (erf766_hasDerivAt_Ser x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℝ (fun y => G y - FLMF.Fresnel.fresnelS y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.fresnelS y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have : (fun n => erf766f n (0 : ℝ)) = fun _ => 0 := by funext n; simp [erf766f]
    rw [this]; exact tsum_zero
  rw [hG0, FLMF.Fresnel.fresnelS_zero] at hz
  have hEq : FLMF.Fresnel.fresnelS z = G z := by linarith [hz]
  rw [hEq]
  simp only [hGdef, erf766f]

-- no-dlmf: series summand helper for complex 7.6.6, no DLMF counterpart
private noncomputable def cerf766f (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)) * x ^ (4 * n + 3)

-- no-dlmf: termwise derivative helper for complex 7.6.6, no DLMF counterpart
private noncomputable def cerf766t (n : ℕ) (x : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n + 1) / (2 * n + 1).factorial * x ^ (4 * n + 2)

-- no-dlmf: termwise differentiation helper for complex 7.6.6, no DLMF counterpart
private lemma cerf766_hasDerivAt_f (n : ℕ) (y : ℂ) : HasDerivAt (cerf766f n) (cerf766t n y) y := by
  have hpow : HasDerivAt (fun x : ℂ => x ^ (4 * n + 3)) (((4 * n + 3 : ℕ) : ℂ) * y ^ (4 * n + 3 - 1)) y :=
    hasDerivAt_pow _ y
  have h := hpow.const_mul
    ((-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)))
  have hval : (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial * (4 * n + 3)) *
      (((4 * n + 3 : ℕ) : ℂ) * y ^ (4 * n + 3 - 1)) = cerf766t n y := by
    simp only [cerf766t]
    rw [show 4 * n + 3 - 1 = 4 * n + 2 from rfl]
    have hfac : ((2 * n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (2 * n + 1).factorial_ne_zero
    have h43 : ((4 : ℂ) * n + 3) ≠ 0 := by
      have h : (4 * n + 3 : ℕ) ≠ 0 := by omega
      exact_mod_cast h
    push_cast
    field_simp
  rw [← hval]
  exact h

-- no-dlmf: uniform bound helper for complex 7.6.6, no DLMF counterpart
private lemma cerf766_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℂ) (hy : ‖y‖ ≤ R) :
    ‖cerf766t n y‖ ≤ (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
  have hfacpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast (2 * n + 1).factorial_pos
  have hnfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnle : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)
  have hcoeff : cerf766t n y =
      (((-1 : ℝ) ^ n * (π / 2) ^ (2 * n + 1) / (2 * n + 1).factorial : ℝ) : ℂ) * y ^ (4 * n + 2) := by
    simp only [cerf766t]
    push_cast
    ring
  have hcoefabs : |(-1 : ℝ) ^ n * (π / 2) ^ (2 * n + 1) / (2 * n + 1).factorial| =
      (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
    rw [abs_div, abs_mul, abs_pow, abs_pow,
      show |(-1 : ℝ)| = 1 by norm_num, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < π / 2), abs_of_pos hfacpos]
  rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, hcoefabs, norm_pow]
  have hy4 : ‖y‖ ^ (4 * n + 2) ≤ R ^ (4 * n + 2) := pow_le_pow_left₀ (norm_nonneg y) hy _
  have hcoef : (0 : ℝ) ≤ (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by positivity
  have step1 : (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * ‖y‖ ^ (4 * n + 2) ≤
      (π / 2) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * R ^ (4 * n + 2) :=
    mul_le_mul_of_nonneg_left hy4 hcoef
  refine step1.trans ?_
  have hpow_eq : (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n = (π / 2) ^ (2 * n + 1) * R ^ (4 * n + 2) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring
  rw [hpow_eq, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hnfacpos hnle

-- no-dlmf: sine-series identification helper for complex 7.6.6, no DLMF counterpart
private lemma cerf766_hasSum_t (x : ℂ) :
    HasSum (fun n => cerf766t n x) (Complex.sin ((Real.pi : ℂ) * x ^ 2 / 2)) := by
  have h := Complex.hasSum_sin ((Real.pi : ℂ) * x ^ 2 / 2)
  have heq : (fun n : ℕ => (-1 : ℂ) ^ n * ((Real.pi : ℂ) * x ^ 2 / 2) ^ (2 * n + 1) / (2 * n + 1).factorial) =
      fun n => cerf766t n x := by
    funext n
    simp only [cerf766t]
    rw [show (Real.pi : ℂ) * x ^ 2 / 2 = ((Real.pi : ℂ) / 2) * x ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  rwa [heq] at h

-- no-dlmf: series differentiability helper for complex 7.6.6, no DLMF counterpart
private lemma cerf766_hasDerivAt_Ser (z : ℂ) :
    HasDerivAt (fun x => ∑' n, cerf766f n x) (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  set R := ‖z‖ + 1 with hRdef
  have hR : (0 : ℝ) ≤ R := by positivity
  have hsum : Summable (fun n => (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial) := by
    have := (Real.summable_pow_div_factorial ((π / 2) ^ 2 * R ^ 4)).mul_left ((π / 2) * R ^ 2)
    simpa [mul_div_assoc] using this
  have hopen : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hRdef]
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_self]
    linarith [norm_nonneg z]
  have hbound : ∀ n y, y ∈ Metric.ball (0 : ℂ) R →
      ‖cerf766t n y‖ ≤ (π / 2) * R ^ 2 * ((π / 2) ^ 2 * R ^ 4) ^ n / n.factorial := by
    intro n y hy
    apply cerf766_bound R hR n y
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  have hg0 : Summable (fun n => cerf766f n (0 : ℂ)) := by
    have : (fun n => cerf766f n (0 : ℂ)) = fun _ => 0 := by
      funext n; simp [cerf766f]
    rw [this]; exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected hsum hopen hconn
    (fun n y _ => cerf766_hasDerivAt_f n y) hbound hzero hg0 hz
  rwa [(cerf766_hasSum_t z).tsum_eq] at h

/-- **DLMF 7.6.6** — Maclaurin series for the complex Fresnel sine integral `S`,
    `S(z) = ∑ₙ (-1)ⁿ(π/2)^{2n+1}/((2n+1)!(4n+3)) z^{4n+3}`, for `z` complex.

DAG: E-7.6.6.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_6_6 (z : ℂ) :
    FLMF.Fresnel.cfresnelS z =
      ∑' n : ℕ,
        (-1 : ℂ) ^ n * ((Real.pi : ℂ) / 2) ^ (2 * n + 1) /
            ((2 * n + 1).factorial * (4 * n + 3)) * z ^ (4 * n + 3) := by
  have hfres : ∀ x : ℂ, HasDerivAt FLMF.Fresnel.cfresnelS (Complex.sin ((Real.pi : ℂ) * x ^ 2 / 2)) x :=
    cser76_cfresnelS_sin_hasDerivAt
  set G : ℂ → ℂ := fun y => ∑' n, cerf766f n y with hGdef
  have hH : ∀ x : ℂ, HasDerivAt (fun y => G y - FLMF.Fresnel.cfresnelS y) 0 x := by
    intro x
    have := (cerf766_hasDerivAt_Ser x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℂ (fun y => G y - FLMF.Fresnel.cfresnelS y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.cfresnelS y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have : (fun n => cerf766f n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf766f]
    rw [this]; exact tsum_zero
  rw [hG0, FLMF.Fresnel.cfresnelS_zero] at hz
  have hEq : FLMF.Fresnel.cfresnelS z = G z := by linear_combination -hz
  rw [hEq]
  simp only [hGdef, cerf766f]

-- no-dlmf: real/narrowed restriction of DLMF 7.6.7; faithful surface is cfresnel_7_6_7
/-- Cosine/sine-modulated series for the Fresnel sine integral `S`, real
specialization (DLMF 7.6.7 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_7 (z : ℝ) :
    FLMF.Fresnel.fresnelS z =
      -Real.cos (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℝ) ^ n * Real.pi ^ (2 * n + 1) /
                (∏ k ∈ Finset.range (2 * n + 2), (2 * k + 1 : ℝ)) *
              z ^ (4 * n + 3)) +
        Real.sin (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℝ) ^ n * Real.pi ^ (2 * n) /
                (∏ k ∈ Finset.range (2 * n + 1), (2 * k + 1 : ℝ)) *
              z ^ (4 * n + 1)) := by
  -- Mirrors `erf_7_6_5` with `cos`/`sin` and `A`/`B` roles swapped, using the same
  -- cancellation identities `erf765_hcancelA`/`erf765_hcancelB`.
  have hGderiv : ∀ x : ℝ,
      HasDerivAt (fun y => -Real.cos (π*y^2/2) * (∑' n, erf765fB n y)
          + Real.sin (π*y^2/2) * (∑' n, erf765fA n y)) (Real.sin (π*x^2/2)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => π * y^2/2) (π * x) x := by
      have h1 : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 := h1.const_mul (π/2)
      have hfun : (fun y : ℝ => π/2 * y^2) = (fun y : ℝ => π * y^2/2) := by funext y; ring
      rw [hfun, show π/2*(2*x) = π*x from by ring] at h2
      exact h2
    have hcos := hp.cos
    have hsin := hp.sin
    have hnegcos := hcos.neg
    have hBx := erf765_hasDerivAt_Bser x
    have hAx := erf765_hasDerivAt_Aser x
    have hprod := (hnegcos.mul hBx).add (hsin.mul hAx)
    simp only [Pi.neg_apply] at hprod
    convert hprod using 1
    have e1 := erf765_hcancelA x
    have e2 := erf765_hcancelB x
    rw [e2]
    linear_combination (-(Real.sin (π * x ^ 2 / 2))) * e1
  have hfres : ∀ x : ℝ, HasDerivAt FLMF.Fresnel.fresnelS (Real.sin (π*x^2/2)) x := by
    intro x
    have := FLMF.Fresnel.hasDerivAt_fresnelS x
    simpa [FLMF.Fresnel.sinArg] using this
  set G : ℝ → ℝ := fun y => -Real.cos (π*y^2/2) * (∑' n, erf765fB n y)
      + Real.sin (π*y^2/2) * (∑' n, erf765fA n y) with hGdef
  have hH : ∀ x : ℝ, HasDerivAt (fun y => G y - FLMF.Fresnel.fresnelS y) 0 x := by
    intro x
    have := (hGderiv x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℝ (fun y => G y - FLMF.Fresnel.fresnelS y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.fresnelS y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have hA0 : (∑' n, erf765fA n (0:ℝ)) = 0 := by
      have : (fun n => erf765fA n (0:ℝ)) = fun _ => 0 := by funext n; simp [erf765fA]
      rw [this]; exact tsum_zero
    have hB0 : (∑' n, erf765fB n (0:ℝ)) = 0 := by
      have : (fun n => erf765fB n (0:ℝ)) = fun _ => 0 := by funext n; simp [erf765fB]
      rw [this]; exact tsum_zero
    rw [hA0, hB0]; simp
  rw [hG0, FLMF.Fresnel.fresnelS_zero] at hz
  have hEq : FLMF.Fresnel.fresnelS z = G z := by linarith [hz]
  rw [hEq]
  simp only [hGdef, erf765fA, erf765fB, erf765Pr]

/-- **DLMF 7.6.7** — Cosine/sine-modulated series for the complex Fresnel
    sine integral `S`,
    `S(z) = -cos(πz²/2)·∑ₙ (-1)ⁿπ^{2n+1}/(1·3···(4n+3)) z^{4n+3}
      + sin(πz²/2)·∑ₙ (-1)ⁿπ^{2n}/(1·3···(4n+1)) z^{4n+1}`, for `z` complex.

DAG: E-7.6.7.
Numerical: PASS
Verified: verified
-/
theorem cfresnel_7_6_7 (z : ℂ) :
    FLMF.Fresnel.cfresnelS z =
      -Complex.cos (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n + 1) /
                (∏ k ∈ Finset.range (2 * n + 2), (2 * k + 1 : ℂ)) *
              z ^ (4 * n + 3)) +
        Complex.sin (Real.pi * z ^ 2 / 2) *
          (∑' n : ℕ,
            (-1 : ℂ) ^ n * (Real.pi : ℂ) ^ (2 * n) /
                (∏ k ∈ Finset.range (2 * n + 1), (2 * k + 1 : ℂ)) *
              z ^ (4 * n + 1)) := by
  -- Mirrors `cfresnel_7_6_5` with `cos`/`sin` and `A`/`B` roles swapped, using the same
  -- cancellation identities `cerf765_hcancelA`/`cerf765_hcancelB`.
  have hGderiv : ∀ x : ℂ,
      HasDerivAt (fun y : ℂ => -Complex.cos ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fB n y)
          + Complex.sin ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fA n y))
        (Complex.sin ((Real.pi : ℂ) * x ^ 2 / 2)) x := by
    intro x
    have hp : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) * y ^ 2 / 2) ((Real.pi : ℂ) * x) x := by
      have h1 : HasDerivAt (fun y : ℂ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have h2 := h1.const_mul ((Real.pi : ℂ) / 2)
      have hfun : (fun y : ℂ => (Real.pi : ℂ) / 2 * y ^ 2) = (fun y : ℂ => (Real.pi : ℂ) * y ^ 2 / 2) := by
        funext y; ring
      rw [hfun, show (Real.pi : ℂ) / 2 * (2 * x) = (Real.pi : ℂ) * x from by ring] at h2
      exact h2
    have hcos := hp.ccos
    have hsin := hp.csin
    have hnegcos := hcos.neg
    have hBx := cerf765_hasDerivAt_Bser x
    have hAx := cerf765_hasDerivAt_Aser x
    have hprod := (hnegcos.mul hBx).add (hsin.mul hAx)
    simp only [Pi.neg_apply] at hprod
    convert hprod using 1
    have e1 := cerf765_hcancelA x
    have e2 := cerf765_hcancelB x
    rw [e2]
    linear_combination (-(Complex.sin ((Real.pi : ℂ) * x ^ 2 / 2))) * e1
  have hfres : ∀ x : ℂ, HasDerivAt FLMF.Fresnel.cfresnelS (Complex.sin ((Real.pi : ℂ) * x ^ 2 / 2)) x :=
    cser76_cfresnelS_sin_hasDerivAt
  set G : ℂ → ℂ := fun y => -Complex.cos ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fB n y)
      + Complex.sin ((Real.pi : ℂ) * y ^ 2 / 2) * (∑' n, cerf765fA n y) with hGdef
  have hH : ∀ x : ℂ, HasDerivAt (fun y => G y - FLMF.Fresnel.cfresnelS y) 0 x := by
    intro x
    have := (hGderiv x).sub (hfres x)
    simpa using this
  have hdiff : Differentiable ℂ (fun y => G y - FLMF.Fresnel.cfresnelS y) :=
    fun y => (hH y).differentiableAt
  have hderiv0 : ∀ y, deriv (fun y => G y - FLMF.Fresnel.cfresnelS y) y = 0 :=
    fun y => (hH y).deriv
  have hz := is_const_of_deriv_eq_zero hdiff hderiv0 z 0
  simp only at hz
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have hA0 : (∑' n, cerf765fA n (0 : ℂ)) = 0 := by
      have : (fun n => cerf765fA n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fA]
      rw [this]; exact tsum_zero
    have hB0 : (∑' n, cerf765fB n (0 : ℂ)) = 0 := by
      have : (fun n => cerf765fB n (0 : ℂ)) = fun _ => 0 := by funext n; simp [cerf765fB]
      rw [this]; exact tsum_zero
    rw [hA0, hB0]; simp
  rw [hG0, FLMF.Fresnel.cfresnelS_zero] at hz
  have hEq : FLMF.Fresnel.cfresnelS z = G z := by linear_combination -hz
  rw [hEq]
  simp only [hGdef, cerf765fA, cerf765fB, cprod765]

section ModSphericalSeries

open scoped Nat

-- no-dlmf: support lemma (`Complex.cosh` power series, obtained from
-- `Complex.hasSum_cos` via `cos (w * I) = cosh w`), no DLMF display of its own
private lemma cser768_hasSum_ccosh (w : ℂ) :
    HasSum (fun n : ℕ => w ^ (2 * n) / (2 * n)!) (Complex.cosh w) := by
  have h := Complex.hasSum_cos (w * Complex.I)
  rw [Complex.cos_mul_I] at h
  refine h.congr_fun ?_
  intro n
  have hI : ((w * Complex.I) ^ (2 * n) : ℂ) = (-1) ^ n * w ^ (2 * n) := by
    rw [mul_pow, pow_mul Complex.I 2 n, Complex.I_sq]
    ring
  have hsq : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [hI, ← mul_assoc, hsq, one_mul]

-- no-dlmf: support lemma (`Complex.sinh` power series, obtained from
-- `Complex.hasSum_sin` via `sin (w * I) = sinh w * I`), no DLMF display of its own
private lemma cser768_hasSum_csinh (w : ℂ) :
    HasSum (fun n : ℕ => w ^ (2 * n + 1) / (2 * n + 1)!) (Complex.sinh w) := by
  have hII : Complex.I * -Complex.I = 1 := by simp [Complex.I_mul_I]
  have h := (Complex.hasSum_sin (w * Complex.I)).mul_right (-Complex.I)
  rw [Complex.sin_mul_I] at h
  have he : Complex.sinh w * Complex.I * -Complex.I = Complex.sinh w := by
    calc Complex.sinh w * Complex.I * -Complex.I
        = Complex.sinh w * (Complex.I * -Complex.I) := by ring
      _ = Complex.sinh w := by rw [hII]; ring
  rw [he] at h
  refine h.congr_fun ?_
  intro n
  have hI : ((w * Complex.I) ^ (2 * n + 1) : ℂ) = (-1) ^ n * w ^ (2 * n + 1) * Complex.I := by
    rw [mul_pow, pow_succ Complex.I (2 * n), pow_mul Complex.I 2 n, Complex.I_sq]
    ring
  have hsq : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [hI]
  calc w ^ (2 * n + 1) / ((2 * n + 1)! : ℂ)
      = ((-1 : ℂ) ^ n * (-1) ^ n) * (w ^ (2 * n + 1) / ((2 * n + 1)! : ℂ))
          * (Complex.I * -Complex.I) := by rw [hsq, hII]; ring
    _ = (-1 : ℂ) ^ n * ((-1) ^ n * w ^ (2 * n + 1) * Complex.I) / ((2 * n + 1)! : ℂ)
          * -Complex.I := by ring

-- no-dlmf: coefficient of the Maclaurin series of the modified spherical Bessel
-- function `i_n^{(1)}` (support definition for 7.6.8/7.6.9), no DLMF display of its own
private noncomputable def msC (n k : ℕ) : ℝ :=
  1 / ((((2 * k)‼ : ℕ) : ℝ) * (((2 * n + 2 * k + 1)‼ : ℕ) : ℝ))

-- no-dlmf: positivity of the series coefficient `msC`, no DLMF display of its own
private lemma msC_pos (n k : ℕ) : 0 < msC n k := by
  unfold msC
  have h1 : (0:ℝ) < (((2 * k)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have h2 : (0:ℝ) < (((2 * n + 2 * k + 1)‼ : ℕ) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  positivity

-- no-dlmf: double-factorial identity `(2k)‼ (2k+1)‼ = (2k+1)!`, no DLMF display of its own
private lemma msC_fac_odd (k : ℕ) : ((2 * k)‼) * ((2 * k + 1)‼) = (2 * k + 1)! := by
  rw [Nat.factorial_eq_mul_doubleFactorial (2 * k)]
  ring

-- no-dlmf: double-factorial identity `(2k)‼ (2k+3)‼ (2k+2) = (2k+3)!`, no DLMF display of its own
private lemma msC_fac_odd3 (k : ℕ) :
    ((2 * k)‼) * ((2 * k + 3)‼) * (2 * k + 2) = (2 * k + 3)! := by
  have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * k + 2)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 from by ring] at h1
  have h2 : ((2 * k + 2)‼) = (2 * k + 2) * ((2 * k)‼) := Nat.doubleFactorial_add_two (2 * k)
  rw [h1, h2]
  ring

-- no-dlmf: `n = 0` value of the series coefficient, no DLMF display of its own
private lemma msC_zero (k : ℕ) : msC 0 k = 1 / (((2 * k + 1)! : ℕ) : ℝ) := by
  unfold msC
  rw [show 2 * 0 + 2 * k + 1 = 2 * k + 1 from by ring, ← msC_fac_odd k]
  push_cast
  ring

-- no-dlmf: `n = 1` value of the series coefficient, no DLMF display of its own
private lemma msC_one (k : ℕ) :
    msC 1 k = ((2 * k + 2 : ℕ) : ℝ) / (((2 * k + 3)! : ℕ) : ℝ) := by
  unfold msC
  rw [show 2 * 1 + 2 * k + 1 = 2 * k + 3 from by ring, ← msC_fac_odd3 k]
  have hA : (0:ℝ) < (((2 * k)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hB : (0:ℝ) < (((2 * k + 3)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  push_cast
  field_simp

-- no-dlmf: `k = 0` case of the coefficient recurrence, no DLMF display of its own
private lemma msC_rec_zero (n : ℕ) : msC n 0 - (2 * n + 3) * msC (n + 1) 0 = 0 := by
  unfold msC
  have e1 : 2 * 0 = 0 := by ring
  have e2 : 2 * n + 2 * 0 + 1 = 2 * n + 1 := by ring
  have e3 : 2 * (n + 1) + 2 * 0 + 1 = (2 * n + 1) + 2 := by ring
  rw [e1, e2, e3, Nat.doubleFactorial_add_two]
  have hD : (0:ℝ) < (((2 * n + 1)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  simp only [Nat.doubleFactorial]
  push_cast
  field_simp
  ring

-- no-dlmf: coefficient form of the three-term recurrence
-- `i_{n+2} = i_n - ((2n+3)/z) i_{n+1}`, no DLMF display of its own
private lemma msC_rec (n k : ℕ) :
    msC n (k + 1) - (2 * n + 3) * msC (n + 1) (k + 1) = msC (n + 2) k := by
  have h1 : ((2 * (k + 1))‼ : ℕ) = (2 * k + 2) * ((2 * k)‼) := by
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, Nat.doubleFactorial_add_two]
  have h2 : ((2 * n + 2 * (k + 1) + 1)‼ : ℕ) = (2 * n + 2 * k + 3) * ((2 * n + 2 * k + 1)‼) := by
    rw [show 2 * n + 2 * (k + 1) + 1 = (2 * n + 2 * k + 1) + 2 from by ring,
      Nat.doubleFactorial_add_two]
  have h3 : ((2 * (n + 1) + 2 * (k + 1) + 1)‼ : ℕ)
      = (2 * n + 2 * k + 5) * ((2 * n + 2 * k + 3) * ((2 * n + 2 * k + 1)‼)) := by
    rw [show 2 * (n + 1) + 2 * (k + 1) + 1 = ((2 * n + 2 * k + 1) + 2) + 2 from by ring,
      Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two]
  have h4 : ((2 * (n + 2) + 2 * k + 1)‼ : ℕ)
      = (2 * n + 2 * k + 5) * ((2 * n + 2 * k + 3) * ((2 * n + 2 * k + 1)‼)) := by
    rw [show 2 * (n + 2) + 2 * k + 1 = ((2 * n + 2 * k + 1) + 2) + 2 from by ring,
      Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two]
  unfold msC
  rw [h1, h2, h3, h4]
  have hA : (0:ℝ) < (((2 * k)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hD : (0:ℝ) < (((2 * n + 2 * k + 1)‼ : ℕ) : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  push_cast
  field_simp
  ring

-- no-dlmf: `n = 0` base case of the Maclaurin expansion of `i_n^{(1)}`, no DLMF display of its own
private lemma msHasSum_zero {w : ℂ} (hw : w ≠ 0) :
    HasSum (fun k : ℕ => (msC 0 k : ℂ) * w ^ (0 + 2 * k))
      (FLMF.Bessel.modSphericalIC 0 w) := by
  have h := (cser768_hasSum_csinh w).div_const w
  rw [FLMF.Bessel.modSphericalI_zero_complex]
  refine h.congr_fun ?_
  intro k
  rw [msC_zero k]
  have hfac : (((2 * k + 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

-- no-dlmf: `n = 1` base case of the Maclaurin expansion of `i_n^{(1)}`, no DLMF display of its own
private lemma msHasSum_one {w : ℂ} (hw : w ≠ 0) :
    HasSum (fun k : ℕ => (msC 1 k : ℂ) * w ^ (1 + 2 * k))
      (FLMF.Bessel.modSphericalIC 1 w) := by
  set f : ℕ → ℂ := fun k : ℕ => w ^ (2 * k) / ((2 * k)! : ℂ) / w
      - w ^ (2 * k + 1) / ((2 * k + 1)! : ℂ) / w ^ 2 with hfdef
  have hd : HasSum f (Complex.cosh w / w - Complex.sinh w / w ^ 2) :=
    ((cser768_hasSum_ccosh w).div_const w).sub ((cser768_hasSum_csinh w).div_const (w ^ 2))
  have hf0 : f 0 = 0 := by
    simp only [hfdef]
    norm_num
    field_simp
    ring
  have hshift : HasSum (fun j : ℕ => f (j + 1))
      (Complex.cosh w / w - Complex.sinh w / w ^ 2) := by
    refine (hasSum_nat_add_iff 1).mpr ?_
    rw [Finset.sum_range_one, hf0, add_zero]
    exact hd
  rw [FLMF.Bessel.modSphericalI_one_complex]
  refine hshift.congr_fun ?_
  intro j
  simp only [hfdef]
  rw [msC_one j, show 2 * (j + 1) = 2 * j + 2 from by ring,
    show 2 * j + 2 + 1 = 2 * j + 3 from by ring]
  have hfac : ((2 * j + 3)! : ℕ) = (2 * j + 3) * ((2 * j + 2)! : ℕ) := by
    rw [show 2 * j + 3 = (2 * j + 2) + 1 from by ring, Nat.factorial_succ]
  have h2 : (((2 * j + 2)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (2 * (j : ℂ) + 3) ≠ 0 := by
    have h4 : ((2 * j + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h4
    exact h4
  rw [hfac]
  push_cast
  field_simp
  ring

-- no-dlmf: induction step for the Maclaurin expansion of `i_n^{(1)}`, no DLMF display of its own
private lemma msHasSum_step {w : ℂ} (hw : w ≠ 0) (n : ℕ) {A B : ℂ}
    (h1 : HasSum (fun k : ℕ => (msC n k : ℂ) * w ^ (n + 2 * k)) A)
    (h2 : HasSum (fun k : ℕ => (msC (n + 1) k : ℂ) * w ^ (n + 1 + 2 * k)) B) :
    HasSum (fun k : ℕ => (msC (n + 2) k : ℂ) * w ^ (n + 2 + 2 * k))
      (A - (2 * ((n : ℂ) + 1) + 1) / w * B) := by
  set g : ℕ → ℂ := fun k => ((msC n k : ℂ) - (2 * (n : ℂ) + 3) * (msC (n + 1) k : ℂ))
      * w ^ (n + 2 * k) with hgdef
  have hpow : ∀ k : ℕ, w ^ (n + 1 + 2 * k) = w ^ (n + 2 * k) * w := by
    intro k
    rw [show n + 1 + 2 * k = (n + 2 * k) + 1 from by ring, pow_succ]
  have hsum : HasSum g (A - (2 * ((n : ℂ) + 1) + 1) / w * B) := by
    have h2' := h2.mul_left (-((2 * ((n : ℂ) + 1) + 1) / w))
    have hadd := h1.add h2'
    have hval : A + -((2 * ((n : ℂ) + 1) + 1) / w) * B
        = A - (2 * ((n : ℂ) + 1) + 1) / w * B := by ring
    rw [hval] at hadd
    refine hadd.congr_fun ?_
    intro k
    simp only [hgdef]
    rw [hpow k]
    field_simp
    ring
  have hg0 : g 0 = 0 := by
    have hstep := msC_rec_zero n
    have hcast : ((msC n 0 : ℂ) - (2 * (n : ℂ) + 3) * (msC (n + 1) 0 : ℂ))
        = ((msC n 0 - (2 * (n : ℝ) + 3) * msC (n + 1) 0 : ℝ) : ℂ) := by push_cast; ring
    simp only [hgdef]
    rw [hcast, hstep]
    simp
  have hshift := (hasSum_nat_add_iff (f := g) 1).mpr (by simpa [hg0] using hsum)
  refine hshift.congr_fun ?_
  intro j
  simp only [hgdef]
  have hcast : ((msC n (j + 1) : ℂ) - (2 * (n : ℂ) + 3) * (msC (n + 1) (j + 1) : ℂ))
      = ((msC n (j + 1) - (2 * (n : ℝ) + 3) * msC (n + 1) (j + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, msC_rec n j, show n + 2 * (j + 1) = n + 2 + 2 * j from by ring]

-- no-dlmf: Maclaurin expansion `i_n^{(1)}(w) = ∑_k w^{n+2k}/((2k)‼ (2n+2k+1)‼)` of the
-- modified spherical Bessel function; the analytic content behind 7.6.8/7.6.9.
-- (Belongs with `FLMF/Support/BesselModifiedSpherical.lean`; kept private here.)
private lemma msHasSum {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    HasSum (fun k : ℕ => (msC n k : ℂ) * w ^ (n + 2 * k))
      (FLMF.Bessel.modSphericalIC n w) := by
  suffices h : ∀ m : ℕ,
      HasSum (fun k : ℕ => (msC m k : ℂ) * w ^ (m + 2 * k)) (FLMF.Bessel.modSphericalIC m w) ∧
      HasSum (fun k : ℕ => (msC (m + 1) k : ℂ) * w ^ (m + 1 + 2 * k))
        (FLMF.Bessel.modSphericalIC (m + 1) w) from (h n).1
  intro m
  induction m with
  | zero => exact ⟨msHasSum_zero hw, msHasSum_one hw⟩
  | succ p ih =>
      refine ⟨ih.2, ?_⟩
      have hstep := msHasSum_step hw p ih.1 ih.2
      rw [FLMF.Bessel.modSphericalI_recurrence_complex p w]
      exact hstep

-- no-dlmf: `(2n)‼ ≤ (2n+1)‼`, no DLMF display of its own
private lemma msDfac_even_le_odd : ∀ n : ℕ, (2 * n)‼ ≤ (2 * n + 1)‼
  | 0 => by norm_num
  | (n + 1) => by
      have ih := msDfac_even_le_odd n
      rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show 2 * n + 2 + 1 = (2 * n + 1) + 2 from by ring,
        Nat.doubleFactorial_add_two, Nat.doubleFactorial_add_two]
      calc (2 * n + 2) * (2 * n)‼ ≤ (2 * n + 2) * (2 * n + 1)‼ := Nat.mul_le_mul_left _ ih
        _ ≤ (2 * n + 1 + 2) * (2 * n + 1)‼ := Nat.mul_le_mul_right _ (by omega)

-- no-dlmf: monotonicity `(2n+1)‼ ≤ (2n+2k+1)‼`, no DLMF display of its own
private lemma msDfac_odd_mono (n : ℕ) : ∀ k : ℕ, (2 * n + 1)‼ ≤ (2 * n + 2 * k + 1)‼
  | 0 => by norm_num
  | (k + 1) => by
      have ih := msDfac_odd_mono n k
      rw [show 2 * n + 2 * (k + 1) + 1 = (2 * n + 2 * k + 1) + 2 from by ring,
        Nat.doubleFactorial_add_two]
      calc (2 * n + 1)‼ ≤ (2 * n + 2 * k + 1)‼ := ih
        _ ≤ (2 * n + 2 * k + 1 + 2) * (2 * n + 2 * k + 1)‼ :=
            Nat.le_mul_of_pos_left _ (by omega)

-- no-dlmf: lower bound `2^n n! ≤ (2n+2k+1)‼`, no DLMF display of its own
private lemma msDfac_lower (n k : ℕ) : 2 ^ n * n ! ≤ (2 * n + 2 * k + 1)‼ := by
  calc 2 ^ n * n ! = (2 * n)‼ := (Nat.doubleFactorial_two_mul n).symm
    _ ≤ (2 * n + 1)‼ := msDfac_even_le_odd n
    _ ≤ (2 * n + 2 * k + 1)‼ := msDfac_odd_mono n k

-- no-dlmf: upper bound for the series coefficient, no DLMF display of its own
private lemma msC_le (n k : ℕ) :
    msC n k ≤ ((1:ℝ) / ((2:ℝ) ^ k * (k ! : ℝ))) * ((1:ℝ) / ((2:ℝ) ^ n * (n ! : ℝ))) := by
  unfold msC
  have hk : (((2 * k)‼ : ℕ) : ℝ) = (2:ℝ) ^ k * (k ! : ℝ) := by
    rw [Nat.doubleFactorial_two_mul k]; push_cast; ring
  have hn : ((2:ℝ) ^ n * (n ! : ℝ)) ≤ (((2 * n + 2 * k + 1)‼ : ℕ) : ℝ) := by
    have h2 : (((2 ^ n * n ! : ℕ)) : ℝ) ≤ (((2 * n + 2 * k + 1)‼ : ℕ) : ℝ) := by
      exact_mod_cast msDfac_lower n k
    simpa using h2
  have hkpos : (0:ℝ) < (2:ℝ) ^ k * (k ! : ℝ) := by positivity
  rw [hk, div_mul_div_comm, one_mul]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left hn (le_of_lt hkpos)

-- no-dlmf: growth bound `‖i_n^{(1)}(w)‖ ≤ e^{‖w‖²/2} (‖w‖/2)^n / n!`, the summability
-- input for the Bessel-coefficient series of 7.6.8/7.6.9; no DLMF display of its own
private lemma msNorm_le (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    ‖FLMF.Bessel.modSphericalIC n w‖
      ≤ Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ)) := by
  have hsum := msHasSum hw n
  have hexp : HasSum (fun k : ℕ => (‖w‖ ^ 2 / 2) ^ k / (k ! : ℝ)) (Real.exp (‖w‖ ^ 2 / 2)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hmaj := hexp.mul_right ((‖w‖ / 2) ^ n / (n ! : ℝ))
  have hterm : ∀ k : ℕ, ‖(msC n k : ℂ) * w ^ (n + 2 * k)‖
      ≤ ((‖w‖ ^ 2 / 2) ^ k / (k ! : ℝ)) * ((‖w‖ / 2) ^ n / (n ! : ℝ)) := by
    intro k
    have hr0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
    have hn0 : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hk0 : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hnorm : ‖(msC n k : ℂ) * w ^ (n + 2 * k)‖ = msC n k * ‖w‖ ^ (n + 2 * k) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (msC_pos n k)]
    rw [hnorm]
    have h1 : msC n k * ‖w‖ ^ (n + 2 * k)
        ≤ (((1:ℝ) / ((2:ℝ) ^ k * (k ! : ℝ))) * ((1:ℝ) / ((2:ℝ) ^ n * (n ! : ℝ))))
          * ‖w‖ ^ (n + 2 * k) :=
      mul_le_mul_of_nonneg_right (msC_le n k) (pow_nonneg hr0 _)
    refine h1.trans (le_of_eq ?_)
    rw [pow_add, pow_mul, div_pow, div_pow]
    field_simp
  have habs : Summable (fun k : ℕ => ‖(msC n k : ℂ) * w ^ (n + 2 * k)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm hmaj.summable
  calc ‖FLMF.Bessel.modSphericalIC n w‖
      = ‖∑' k : ℕ, (msC n k : ℂ) * w ^ (n + 2 * k)‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' k : ℕ, ‖(msC n k : ℂ) * w ^ (n + 2 * k)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k : ℕ, ((‖w‖ ^ 2 / 2) ^ k / (k ! : ℝ)) * ((‖w‖ / 2) ^ n / (n ! : ℝ)) :=
        habs.tsum_le_tsum hterm hmaj.summable
    _ = Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ)) := hmaj.tsum_eq


/-! ### Chebyshev helpers for 7.6.9 -/

-- no-dlmf: local notation for the odd Chebyshev polynomials of the first kind
private noncomputable def cser769T (a : ℝ) (n : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 1)).eval a

-- no-dlmf: local notation for the Chebyshev polynomials of the second kind
private noncomputable def cser769U (a : ℝ) (m : ℕ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval a

-- no-dlmf: derivative of the odd Chebyshev polynomial, `T_{2n+1}' = (2n+1) U_{2n}`
private lemma cser769_hasDerivAt_T (n : ℕ) (a : ℝ) :
    HasDerivAt (fun x : ℝ => cser769T x n) ((2 * (n : ℝ) + 1) * cser769U a (2 * n)) a := by
  have h := (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 1)).hasDerivAt a
  rw [Polynomial.Chebyshev.T_derivative_eq_U] at h
  have hidx : 2 * (n : ℤ) + 1 - 1 = ((2 * n : ℕ) : ℤ) := by push_cast; ring
  rw [hidx] at h
  simpa [cser769T, cser769U] using h

-- no-dlmf: `U_{m+4} - U_m = 4 X T_{m+3}` (Chebyshev contiguity)
private lemma cser769_U_diff (a : ℝ) (m : ℕ) :
    cser769U a (m + 4) - cser769U a m
      = 4 * a * (Polynomial.Chebyshev.T ℝ ((m : ℤ) + 3)).eval a := by
  have h1 := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ ((m : ℤ) + 2)
  have h2 := Polynomial.Chebyshev.two_mul_T_eq_U_sub_U ℝ (m : ℤ)
  have h3 := Polynomial.Chebyshev.T_add_two ℝ ((m : ℤ) + 2)
  rw [show (m : ℤ) + 2 + 2 = (m : ℤ) + 4 from by ring] at h1 h3
  rw [show (m : ℤ) + 2 + 1 = (m : ℤ) + 3 from by ring] at h3
  have h1' := congrArg (Polynomial.eval a) h1
  have h2' := congrArg (Polynomial.eval a) h2
  have h3' := congrArg (Polynomial.eval a) h3
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_ofNat] at h1' h2' h3'
  have hi1 : cser769U a (m + 4) = (Polynomial.Chebyshev.U ℝ ((m : ℤ) + 4)).eval a := by
    unfold cser769U
    rw [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 4 from by push_cast; ring]
  have hi2 : cser769U a m = (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval a := rfl
  rw [hi1, hi2]
  linarith

-- no-dlmf: two-step recurrence bound, `|f m| ≤ C^m` for `f (m+2) = 2 b f(m+1) - f m`
private lemma cser769_rec_bound {C b : ℝ} (hC : 1 ≤ C) (hb : 2 * |b| + 1 ≤ C) (f : ℕ → ℝ)
    (h0 : |f 0| ≤ 1) (h1 : |f 1| ≤ C)
    (hrec : ∀ m, f (m + 2) = 2 * b * f (m + 1) - f m) : ∀ m, |f m| ≤ C ^ m := by
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  suffices h : ∀ p : ℕ, |f p| ≤ C ^ p ∧ |f (p + 1)| ≤ C ^ (p + 1) from fun m => (h m).1
  intro p
  induction p with
  | zero => exact ⟨by simpa using h0, by simpa using h1⟩
  | succ q ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec q]
      calc |2 * b * f (q + 1) - f q| ≤ |2 * b * f (q + 1)| + |f q| := abs_sub _ _
        _ = 2 * |b| * |f (q + 1)| + |f q| := by rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * |b| * C ^ (q + 1) + C ^ (q + 1) := by
            have hq1 : C ^ q ≤ C ^ (q + 1) := by
              apply pow_le_pow_right₀ hC; omega
            nlinarith [abs_nonneg b, pow_nonneg hC0 (q + 1), ih.1, ih.2]
        _ = (2 * |b| + 1) * C ^ (q + 1) := by ring
        _ ≤ C * C ^ (q + 1) := mul_le_mul_of_nonneg_right hb (pow_nonneg hC0 _)
        _ = C ^ (q + 1 + 1) := by ring

-- no-dlmf: elementary bound `|T_m(a)| ≤ (2|a|+1)^m`
private lemma cser769_T_bound (a : ℝ) (m : ℕ) :
    |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval a| ≤ (2 * |a| + 1) ^ m := by
  have hC : (1:ℝ) ≤ 2 * |a| + 1 := by have := abs_nonneg a; linarith
  refine cser769_rec_bound hC le_rfl (fun m => (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval a) ?_ ?_ ?_ m
  · simp [Polynomial.Chebyshev.T_zero]
  · show |(Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).eval a| ≤ 2 * |a| + 1
    have h1 : (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).eval a = a := by
      norm_num [Polynomial.Chebyshev.T_one]
    rw [h1]
    have h2 := abs_nonneg a
    linarith
  · intro k
    have h := congrArg (Polynomial.eval a) (Polynomial.Chebyshev.T_add_two ℝ (k : ℤ))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_ofNat] at h
    push_cast
    convert h using 3

-- no-dlmf: elementary bound `|U_m(a)| ≤ (2|a|+1)^m`
private lemma cser769_U_bound (a : ℝ) (m : ℕ) : |cser769U a m| ≤ (2 * |a| + 1) ^ m := by
  have hC : (1:ℝ) ≤ 2 * |a| + 1 := by have := abs_nonneg a; linarith
  refine cser769_rec_bound hC le_rfl (fun m => cser769U a m) ?_ ?_ ?_ m
  · simp [cser769U, Polynomial.Chebyshev.U_zero]
  · simp [cser769U, Polynomial.Chebyshev.U_one]
  · intro k
    have h := congrArg (Polynomial.eval a) (Polynomial.Chebyshev.U_add_two ℝ (k : ℤ))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_ofNat] at h
    simp only [cser769U]
    push_cast
    convert h using 3

-- no-dlmf: `T_{2n+1}(0) = 0`
private lemma cser769_T_zero_odd (n : ℕ) : cser769T 0 n = 0 :=
  Polynomial.Chebyshev.T_eval_zero_of_odd (R := ℝ) (n := 2 * (n : ℤ) + 1) ⟨(n : ℤ), by ring⟩

-- no-dlmf: `(2n+1) ≤ 3·2^n`
private lemma cser769_two_n_add_one_le (n : ℕ) : (2 * (n : ℝ) + 1) ≤ 3 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ p ih =>
      have h2 : (1:ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
      push_cast
      push_cast at ih
      rw [pow_succ]
      nlinarith

-- no-dlmf: summability of `(2n+1) c^n / n!`
private lemma cser769_summable_lin (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) * (c ^ n / (n ! : ℝ))) := by
  have hmaj : Summable (fun n : ℕ => 3 * ((2 * c) ^ n / (n ! : ℝ))) :=
    (Real.summable_pow_div_factorial (2 * c)).mul_left 3
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have h1 := cser769_two_n_add_one_le n
  have hstep : (2 * (n : ℝ) + 1) * (c ^ n / (n ! : ℝ))
      ≤ (3 * 2 ^ n) * (c ^ n / (n ! : ℝ)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow]
  ring


/-! ### The Chebyshev/Bessel series of 7.6.9 -/

-- no-dlmf: summand of the 7.6.9 series
private noncomputable def cser769f (w : ℂ) (n : ℕ) (a : ℝ) : ℂ :=
  (cser769T a n : ℂ) * FLMF.Bessel.modSphericalIC n w

-- no-dlmf: termwise `a`-derivative of the 7.6.9 summand
private noncomputable def cser769t (w : ℂ) (n : ℕ) (a : ℝ) : ℂ :=
  (((2 * (n : ℝ) + 1) * cser769U a (2 * n) : ℝ) : ℂ) * FLMF.Bessel.modSphericalIC n w

-- no-dlmf: termwise differentiation for the 7.6.9 series
private lemma cser769_hasDerivAt_f (w : ℂ) (n : ℕ) (y : ℝ) :
    HasDerivAt (cser769f w n) (cser769t w n y) y := by
  have h := ((cser769_hasDerivAt_T n y).ofReal_comp).mul_const
    (FLMF.Bessel.modSphericalIC n w)
  simpa [cser769f, cser769t] using h

-- no-dlmf: uniform bound for the 7.6.9 summands and their derivatives
private lemma cser769_bound (w : ℂ) (hw : w ≠ 0) (n m : ℕ) (y R : ℝ) (hy : |y| ≤ R)
    (c p : ℝ) (hc : 0 ≤ c) (hp : |p| ≤ c * (2 * |y| + 1) ^ m) :
    ‖(p : ℂ) * FLMF.Bessel.modSphericalIC n w‖
      ≤ c * (2 * R + 1) ^ m * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ))) := by
  have hR0 : (0:ℝ) ≤ R := le_trans (abs_nonneg y) hy
  have hB : (0:ℝ) ≤ Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ)) := by positivity
  have hpow : (2 * |y| + 1) ^ m ≤ (2 * R + 1) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc ‖(p : ℂ) * FLMF.Bessel.modSphericalIC n w‖
      = |p| * ‖FLMF.Bessel.modSphericalIC n w‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (c * (2 * |y| + 1) ^ m)
          * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ))) := by
        apply mul_le_mul hp (msNorm_le n hw) (norm_nonneg _) (by positivity)
    _ ≤ c * (2 * R + 1) ^ m * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hpow hc
        nlinarith [hB]

-- no-dlmf: summable majorant for the derivative series of 7.6.9
private lemma cser769_summable_maj (w : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) * (2 * R + 1) ^ (2 * n)
      * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ)))) := by
  have hq : (0:ℝ) ≤ (2 * R + 1) ^ 2 * (‖w‖ / 2) := by positivity
  have h := (cser769_summable_lin ((2 * R + 1) ^ 2 * (‖w‖ / 2)) hq).mul_left
    (Real.exp (‖w‖ ^ 2 / 2))
  refine h.congr (fun n => ?_)
  rw [mul_pow, ← pow_mul]
  ring

-- no-dlmf: derivative-series bound on a ball, for the M-test
private lemma cser769_bound_t (w : ℂ) (hw : w ≠ 0) (n : ℕ) (y R : ℝ) (hy : |y| ≤ R) :
    ‖cser769t w n y‖ ≤ (2 * (n : ℝ) + 1) * (2 * R + 1) ^ (2 * n)
      * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ n / (n ! : ℝ))) := by
  refine cser769_bound w hw n (2 * n) y R hy (2 * (n : ℝ) + 1) _ (by positivity) ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (n : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_left (cser769_U_bound y (2 * n)) (by positivity)

-- no-dlmf: the 7.6.9 series vanishes termwise at `a = 0`
private lemma cser769_f_zero (w : ℂ) (n : ℕ) : cser769f w n 0 = 0 := by
  simp [cser769f, cser769_T_zero_odd n]

-- no-dlmf: termwise differentiation of the 7.6.9 series (Weierstrass M-test)
private lemma cser769_hasDerivAt_Ser (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, cser769f w n x) (∑' n : ℕ, cser769t w n a) a := by
  set R : ℝ := |a| + 1 with hRdef
  have hR0 : (0:ℝ) ≤ R := by positivity
  have ha : a ∈ Metric.ball (0:ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]
    linarith
  have h0 : (0:ℝ) ∈ Metric.ball (0:ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]
    simp only [abs_zero]
    positivity
  refine hasDerivAt_tsum_of_isPreconnected (cser769_summable_maj w R hR0)
    Metric.isOpen_ball ((convex_ball (0:ℝ) R).isPreconnected)
    (fun n y _ => cser769_hasDerivAt_f w n y) (fun n y hy => ?_) h0 ?_ ha
  · refine cser769_bound_t w hw n y R ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    exact hy.le
  · simp only [cser769_f_zero]
    exact summable_zero

-- no-dlmf: summability of the 7.6.9 series at every real `a`
private lemma cser769_summable_f (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    Summable (fun n : ℕ => cser769f w n a) := by
  set R : ℝ := |a| + 1 with hRdef
  have hR0 : (0:ℝ) ≤ R := by positivity
  have ha : a ∈ Metric.ball (0:ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]; linarith
  have h0 : (0:ℝ) ∈ Metric.ball (0:ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]
    simp only [abs_zero]; positivity
  refine summable_of_summable_hasDerivAt_of_isPreconnected (cser769_summable_maj w R hR0)
    Metric.isOpen_ball ((convex_ball (0:ℝ) R).isPreconnected)
    (fun n y _ => cser769_hasDerivAt_f w n y) (fun n y hy => ?_) h0 ?_ ha
  · refine cser769_bound_t w hw n y R ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    exact hy.le
  · simp only [cser769_f_zero]
    exact summable_zero

-- no-dlmf: summability of the derivative series of 7.6.9
private lemma cser769_summable_t (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    Summable (fun n : ℕ => cser769t w n a) := by
  have hR0 : (0:ℝ) ≤ |a| := abs_nonneg a
  refine Summable.of_norm_bounded (cser769_summable_maj w |a| hR0) (fun n => ?_)
  exact cser769_bound_t w hw n a |a| le_rfl


/-! ### Telescoping identity behind 7.6.9 -/

-- no-dlmf: telescoping partner sequence for the 7.6.9 derivative identity
private noncomputable def cser769B (w : ℂ) (a : ℝ) (m : ℕ) : ℂ :=
  (cser769U a (2 * m + 2) : ℂ) * FLMF.Bessel.modSphericalIC m w
    + (cser769U a (2 * m) : ℂ) * FLMF.Bessel.modSphericalIC (m + 1) w

-- no-dlmf: majorant for the telescoping sequence
private lemma cser769_B_bound (w : ℂ) (hw : w ≠ 0) (a : ℝ) (m : ℕ) :
    ‖cser769B w a m‖ ≤ ((2 * |a| + 1) ^ 2 + ‖w‖ / 2)
      * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
  have hfacm : (0:ℝ) < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hfacm1 : (0:ℝ) < ((m + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
  have hE : (0:ℝ) < Real.exp (‖w‖ ^ 2 / 2) := Real.exp_pos _
  have hr : (0:ℝ) ≤ ‖w‖ / 2 := by positivity
  have h1 : ‖(cser769U a (2 * m + 2) : ℂ) * FLMF.Bessel.modSphericalIC m w‖
      ≤ 1 * (2 * |a| + 1) ^ (2 * m + 2)
        * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ m / (m ! : ℝ))) := by
    refine cser769_bound w hw m (2 * m + 2) a |a| le_rfl 1 _ zero_le_one ?_
    rw [one_mul]
    exact cser769_U_bound a (2 * m + 2)
  have h2 : ‖(cser769U a (2 * m) : ℂ) * FLMF.Bessel.modSphericalIC (m + 1) w‖
      ≤ 1 * (2 * |a| + 1) ^ (2 * m)
        * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ (m + 1) / ((m + 1)! : ℝ))) := by
    refine cser769_bound w hw (m + 1) (2 * m) a |a| le_rfl 1 _ zero_le_one ?_
    rw [one_mul]
    exact cser769_U_bound a (2 * m)
  have hfacle : ((‖w‖ / 2) ^ (m + 1) / (((m + 1)! : ℕ) : ℝ))
      ≤ (‖w‖ / 2) * ((‖w‖ / 2) ^ m / (m ! : ℝ)) := by
    have hcast : ((m ! : ℝ)) ≤ (((m + 1)! : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_succ m)
    have hstep : (‖w‖ / 2) ^ (m + 1) / (((m + 1)! : ℕ) : ℝ)
        ≤ (‖w‖ / 2) ^ (m + 1) / (m ! : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfacm hcast
    refine hstep.trans (le_of_eq ?_)
    rw [pow_succ]
    ring
  have hkey1 : (1:ℝ) * (2 * |a| + 1) ^ (2 * m + 2)
      * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) ^ m / (m ! : ℝ)))
      = (2 * |a| + 1) ^ 2
        * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
    rw [mul_pow, ← pow_mul, pow_add]
    ring
  have hkey2 : (1:ℝ) * (2 * |a| + 1) ^ (2 * m)
      * (Real.exp (‖w‖ ^ 2 / 2) * ((‖w‖ / 2) * ((‖w‖ / 2) ^ m / (m ! : ℝ))))
      = (‖w‖ / 2)
        * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
    rw [mul_pow, ← pow_mul]
    ring
  have h2' : ‖(cser769U a (2 * m) : ℂ) * FLMF.Bessel.modSphericalIC (m + 1) w‖
      ≤ (‖w‖ / 2)
        * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
    refine h2.trans ?_
    rw [← hkey2]
    have hpos : (0:ℝ) ≤ 1 * (2 * |a| + 1) ^ (2 * m) * Real.exp (‖w‖ ^ 2 / 2) := by positivity
    nlinarith [hfacle, hpos]
  have h1' : ‖(cser769U a (2 * m + 2) : ℂ) * FLMF.Bessel.modSphericalIC m w‖
      ≤ (2 * |a| + 1) ^ 2
        * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
    rw [← hkey1]; exact h1
  calc ‖cser769B w a m‖
      ≤ ‖(cser769U a (2 * m + 2) : ℂ) * FLMF.Bessel.modSphericalIC m w‖
        + ‖(cser769U a (2 * m) : ℂ) * FLMF.Bessel.modSphericalIC (m + 1) w‖ :=
        norm_add_le _ _
    _ ≤ (2 * |a| + 1) ^ 2
          * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ)))
        + (‖w‖ / 2)
          * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) :=
        add_le_add h1' h2'
    _ = ((2 * |a| + 1) ^ 2 + ‖w‖ / 2)
          * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ))) := by
        ring

-- no-dlmf: the telescoping sequence tends to zero
private lemma cser769_B_tendsto (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    Filter.Tendsto (fun m : ℕ => cser769B w a m) Filter.atTop (nhds 0) := by
  have hq : (0:ℝ) ≤ (2 * |a| + 1) ^ 2 * (‖w‖ / 2) := by positivity
  have hmaj : Summable (fun m : ℕ => ((2 * |a| + 1) ^ 2 + ‖w‖ / 2)
      * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ)))) :=
    ((Real.summable_pow_div_factorial _).mul_left _).mul_left _
  have hz := hmaj.tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => cser769_B_bound w hw a m) hz

-- no-dlmf: the per-term telescoping identity behind the 7.6.9 derivative relation
private lemma cser769_telescope_term (w : ℂ) (hw : w ≠ 0) (a : ℝ) (m : ℕ) :
    cser769t w (m + 1) a - 4 * (a : ℂ) * w * cser769f w (m + 1) a
      = w * (cser769B w a m - cser769B w a (m + 1)) := by
  have hrec : w * (FLMF.Bessel.modSphericalIC m w - FLMF.Bessel.modSphericalIC (m + 2) w)
      = (2 * (m : ℂ) + 3) * FLMF.Bessel.modSphericalIC (m + 1) w := by
    rw [FLMF.Bessel.modSphericalI_recurrence'_complex m w]
    field_simp
    ring
  have hidx : ((2 * m : ℕ) : ℤ) + 3 = 2 * ((m + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  have hU : cser769U a (2 * m + 4) - cser769U a (2 * m) = 4 * a * cser769T a (m + 1) := by
    rw [cser769_U_diff a (2 * m), hidx]
    rfl
  have hUC : ((cser769U a (2 * m + 4) : ℝ) : ℂ) - ((cser769U a (2 * m) : ℝ) : ℂ)
      = 4 * (a : ℂ) * ((cser769T a (m + 1) : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hU
  simp only [cser769t, cser769f, cser769B,
    show 2 * (m + 1) = 2 * m + 2 from by ring,
    show 2 * m + 2 + 2 = 2 * m + 4 from by ring]
  push_cast
  linear_combination (-(((cser769U a (2 * m + 2) : ℝ) : ℂ))) * hrec
    + w * FLMF.Bessel.modSphericalIC (m + 1) w * hUC


-- no-dlmf: base values feeding the telescoping sum
private lemma cser769_U_val_zero (a : ℝ) : cser769U a 0 = 1 := by
  simp [cser769U, Polynomial.Chebyshev.U_zero]

private lemma cser769_U_val_two (a : ℝ) : cser769U a 2 = 4 * a ^ 2 - 1 := by
  have h : ((2 : ℕ) : ℤ) = 2 := by norm_num
  simp only [cser769U, h, Polynomial.Chebyshev.U_two]
  simp

private lemma cser769_T_val_zero (a : ℝ) : cser769T a 0 = a := by
  have h : 2 * ((0 : ℕ) : ℤ) + 1 = 1 := by norm_num
  simp only [cser769T, h, Polynomial.Chebyshev.T_one]
  simp

-- no-dlmf: the closed value of the telescoping sum
private lemma cser769_telescope_head (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    w * cser769B w a 0 + (cser769t w 0 a - 4 * (a : ℂ) * w * cser769f w 0 a)
      = Complex.exp (-w) := by
  simp only [cser769B, cser769t, cser769f, show 2 * 0 + 2 = 2 from by norm_num,
    show 2 * 0 = 0 from by norm_num, zero_add, cser769_U_val_zero, cser769_U_val_two,
    cser769_T_val_zero, FLMF.Bessel.modSphericalI_zero_complex,
    FLMF.Bessel.modSphericalI_one_complex]
  rw [← Complex.cosh_sub_sinh]
  push_cast
  field_simp
  ring

-- no-dlmf: the derivative relation `G'(a) = 4 a w G(a) + e^{-w}` for the 7.6.9 series
private lemma cser769_deriv_eq (w : ℂ) (hw : w ≠ 0) (a : ℝ) :
    (∑' n : ℕ, cser769t w n a)
      = 4 * (a : ℂ) * w * (∑' n : ℕ, cser769f w n a) + Complex.exp (-w) := by
  have hmaj : Summable (fun m : ℕ => ((2 * |a| + 1) ^ 2 + ‖w‖ / 2)
      * (Real.exp (‖w‖ ^ 2 / 2) * (((2 * |a| + 1) ^ 2 * (‖w‖ / 2)) ^ m / (m ! : ℝ)))) :=
    ((Real.summable_pow_div_factorial _).mul_left _).mul_left _
  have hBsum : Summable (fun m : ℕ => cser769B w a m) :=
    Summable.of_norm_bounded hmaj (fun m => cser769_B_bound w hw a m)
  have hdiff : Summable (fun m : ℕ => cser769B w a m - cser769B w a (m + 1)) :=
    hBsum.sub ((summable_nat_add_iff 1).mpr hBsum)
  have hlim : Filter.Tendsto
      (fun N => ∑ m ∈ Finset.range N, (cser769B w a m - cser769B w a (m + 1)))
      Filter.atTop (nhds (cser769B w a 0)) := by
    have heq : ∀ N : ℕ, ∑ m ∈ Finset.range N, (cser769B w a m - cser769B w a (m + 1))
        = cser769B w a 0 - cser769B w a N := fun N => Finset.sum_range_sub' _ N
    simp only [heq]
    simpa using tendsto_const_nhds.sub (cser769_B_tendsto w hw a)
  have htel : HasSum (fun m : ℕ => cser769B w a m - cser769B w a (m + 1)) (cser769B w a 0) := by
    have h1 := hdiff.hasSum
    have h2 := h1.tendsto_sum_nat
    have h3 := tendsto_nhds_unique h2 hlim
    rwa [h3] at h1
  set P : ℕ → ℂ := fun n => cser769t w n a - 4 * (a : ℂ) * w * cser769f w n a with hPdef
  have hPshift : HasSum (fun m : ℕ => P (m + 1)) (w * cser769B w a 0) := by
    have := htel.mul_left w
    refine this.congr_fun ?_
    intro m
    simp only [hPdef]
    exact cser769_telescope_term w hw a m
  have hPfull : HasSum P (w * cser769B w a 0 + P 0) := by
    have := (hasSum_nat_add_iff (f := P) 1).mp hPshift
    simpa using this
  have hPsum : HasSum P ((∑' n : ℕ, cser769t w n a)
      - 4 * (a : ℂ) * w * (∑' n : ℕ, cser769f w n a)) :=
    (cser769_summable_t w hw a).hasSum.sub
      (((cser769_summable_f w hw a).hasSum).mul_left (4 * (a : ℂ) * w))
  have hEq := hPsum.unique hPfull
  simp only [hPdef] at hEq
  have hhead := cser769_telescope_head w hw a
  linear_combination hEq + hhead


-- no-dlmf: the closed form of the 7.6.9 series, obtained by pinning the first-order
-- linear ODE `G'(a) = 2 a z² G(a) + e^{-z²/2}`, `G(0) = 0`, in the Chebyshev variable `a`
private lemma cser769_main (z : ℂ) (hz : z ≠ 0) (a : ℝ) :
    (∑' n : ℕ, cser769f (z ^ 2 / 2) n a)
      = ((Real.sqrt Real.pi : ℂ) / (2 * z))
        * (Complex.exp (((a : ℂ) ^ 2 - 1 / 2) * z ^ 2) * FLMF.Error.cerf ((a : ℂ) * z)) := by
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    have : Real.sqrt Real.pi ≠ 0 := by
      have := Real.sqrt_pos.mpr Real.pi_pos
      linarith
    exact_mod_cast this
  set w : ℂ := z ^ 2 / 2 with hwdef
  have hw : w ≠ 0 := by
    rw [hwdef]
    exact div_ne_zero (pow_ne_zero 2 hz) two_ne_zero
  set G : ℝ → ℂ := fun x => ∑' n : ℕ, cser769f w n x with hGdef
  set F : ℝ → ℂ := fun x => ((Real.sqrt Real.pi : ℂ) / (2 * z))
      * (Complex.exp (((x : ℂ) ^ 2 - 1 / 2) * z ^ 2) * FLMF.Error.cerf ((x : ℂ) * z)) with hFdef
  have hGderiv : ∀ x : ℝ, HasDerivAt G (2 * (x : ℂ) * z ^ 2 * G x + Complex.exp (-w)) x := by
    intro x
    have h := cser769_hasDerivAt_Ser w hw x
    rw [cser769_deriv_eq w hw x] at h
    have hval : 4 * (x : ℂ) * w * (∑' n : ℕ, cser769f w n x) + Complex.exp (-w)
        = 2 * (x : ℂ) * z ^ 2 * G x + Complex.exp (-w) := by
      simp only [hGdef, hwdef]
      ring
    rw [hval] at h
    exact h
  have hFderiv : ∀ x : ℝ, HasDerivAt F (2 * (x : ℂ) * z ^ 2 * F x + Complex.exp (-w)) x := by
    intro x
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun y : ℝ => ((y : ℂ)) ^ 2) (2 * (x : ℂ)) x := by
      simpa using hx.pow 2
    have hu : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ 2 - 1 / 2) * z ^ 2) (2 * (x : ℂ) * z ^ 2) x := by
      simpa using (h1.sub_const (1 / 2 : ℂ)).mul_const (z ^ 2)
    have hexp := hu.cexp
    have hv : HasDerivAt (fun y : ℝ => (y : ℂ) * z) z x := by
      simpa using hx.mul_const z
    have hcerf : HasDerivAt (fun y : ℝ => FLMF.Error.cerf ((y : ℂ) * z))
        (z * ((2 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-((x : ℂ) * z) ^ 2))) x := by
      have h := (FLMF.Error.hasDerivAt_cerf ((x : ℂ) * z)).scomp x hv
      simpa [Function.comp_def, smul_eq_mul] using h
    have hprod := (hexp.mul hcerf).const_mul ((Real.sqrt Real.pi : ℂ) / (2 * z))
    have hexpprod : Complex.exp (((x : ℂ) ^ 2 - 1 / 2) * z ^ 2)
        * Complex.exp (-((x : ℂ) * z) ^ 2) = Complex.exp (-w) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [hwdef]
      ring
    have hkey : ((Real.sqrt Real.pi : ℂ) / (2 * z))
        * (Complex.exp (((x : ℂ) ^ 2 - 1 / 2) * z ^ 2)
          * (z * ((2 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-((x : ℂ) * z) ^ 2))))
        = Complex.exp (-w) := by
      rw [← hexpprod]
      field_simp
    refine hprod.congr_deriv ?_
    simp only [hFdef]
    rw [← hkey]
    ring
  set H : ℝ → ℂ := fun x => Complex.exp (-((x : ℂ) ^ 2 * z ^ 2)) * (G x - F x) with hHdef
  have hHderiv : ∀ x : ℝ, HasDerivAt H 0 x := by
    intro x
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun y : ℝ => ((y : ℂ)) ^ 2) (2 * (x : ℂ)) x := by
      simpa using hx.pow 2
    have hq : HasDerivAt (fun y : ℝ => -((y : ℂ) ^ 2 * z ^ 2)) (-(2 * (x : ℂ) * z ^ 2)) x := by
      simpa using (h1.mul_const (z ^ 2)).neg
    have he := hq.cexp
    have hd := (hGderiv x).sub (hFderiv x)
    have hmul := he.mul hd
    refine hmul.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hconst := is_const_of_deriv_eq_zero
    (fun x => (hHderiv x).differentiableAt) (fun x => (hHderiv x).deriv) a 0
  have hG0 : G 0 = 0 := by
    simp only [hGdef, cser769_f_zero]
    exact tsum_zero
  have hF0 : F 0 = 0 := by
    simp only [hFdef]
    simp [FLMF.Error.cerf_zero]
  have hH0 : H 0 = 0 := by
    simp only [hHdef, hG0, hF0]
    simp
  have hHa : Complex.exp (-((a : ℂ) ^ 2 * z ^ 2)) * (G a - F a) = 0 := by
    have := hconst.trans hH0
    simpa only [hHdef] using this
  have hsub : G a - F a = 0 := by
    rcases mul_eq_zero.mp hHa with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact h
  have : G a = F a := by linear_combination hsub
  simpa only [hGdef, hFdef] using this


-- no-dlmf: the real and complex modified spherical Bessel functions agree on ℝ
private lemma modSphericalIC_ofReal (n : ℕ) (x : ℝ) :
    FLMF.Bessel.modSphericalIC n (x : ℂ) = ((FLMF.Bessel.modSphericalI n x : ℝ) : ℂ) := by
  suffices h : ∀ m : ℕ,
      (FLMF.Bessel.modSphericalIC m (x : ℂ) = ((FLMF.Bessel.modSphericalI m x : ℝ) : ℂ)) ∧
      (FLMF.Bessel.modSphericalIC (m + 1) (x : ℂ)
        = ((FLMF.Bessel.modSphericalI (m + 1) x : ℝ) : ℂ)) from (h n).1
  intro m
  induction m with
  | zero =>
      constructor
      · rw [FLMF.Bessel.modSphericalI_zero_complex, FLMF.Bessel.modSphericalI_zero]
        push_cast
        ring
      · rw [FLMF.Bessel.modSphericalI_one_complex, FLMF.Bessel.modSphericalI_one]
        push_cast
        ring
  | succ p ih =>
      refine ⟨ih.2, ?_⟩
      rw [FLMF.Bessel.modSphericalI_recurrence_complex p (x : ℂ),
        FLMF.Bessel.modSphericalI_recurrence p x, ih.1, ih.2]
      push_cast
      ring

/-! ### 7.6.8 as the `a = 1/√2` instance of 7.6.9 -/

-- no-dlmf: local notation for the Chebyshev polynomials of the first kind, ℕ-indexed
private noncomputable def cser769Tn (a : ℝ) (k : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval a

private lemma cser769Tn_zero (a : ℝ) : cser769Tn a 0 = 1 := by
  simp [cser769Tn, Polynomial.Chebyshev.T_zero]

private lemma cser769Tn_one (a : ℝ) : cser769Tn a 1 = a := by
  have h : ((1 : ℕ) : ℤ) = 1 := by norm_num
  simp only [cser769Tn, h, Polynomial.Chebyshev.T_one]
  simp

private lemma cser769Tn_rec (a : ℝ) (k : ℕ) :
    cser769Tn a (k + 2) = 2 * a * cser769Tn a (k + 1) - cser769Tn a k := by
  have h := congrArg (Polynomial.eval a) (Polynomial.Chebyshev.T_add_two ℝ (k : ℤ))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_ofNat] at h
  simp only [cser769Tn]
  push_cast
  convert h using 3

private lemma cser769T_eq_Tn (a : ℝ) (n : ℕ) : cser769T a n = cser769Tn a (2 * n + 1) := by
  unfold cser769T cser769Tn
  rw [show ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 1 from by push_cast; ring]

-- no-dlmf: for `4a² = 2` the Chebyshev polynomials have period 4 up to sign
private lemma cser769Tn_period (a : ℝ) (ha : 4 * a ^ 2 = 2) (k : ℕ) :
    cser769Tn a (k + 4) = -cser769Tn a k := by
  have h4 : cser769Tn a (k + 4) = 2 * a * cser769Tn a (k + 3) - cser769Tn a (k + 2) := by
    have := cser769Tn_rec a (k + 2)
    rw [show k + 2 + 2 = k + 4 from by ring, show k + 2 + 1 = k + 3 from by ring] at this
    exact this
  have h3 : cser769Tn a (k + 3) = 2 * a * cser769Tn a (k + 2) - cser769Tn a (k + 1) := by
    have := cser769Tn_rec a (k + 1)
    rw [show k + 1 + 2 = k + 3 from by ring, show k + 1 + 1 = k + 2 from by ring] at this
    exact this
  have h2 := cser769Tn_rec a k
  rw [h4, h3, h2]
  linear_combination (2 * a * cser769Tn a (k + 1) - cser769Tn a k) * ha

-- no-dlmf: the Chebyshev values `T_{2n+1}(1/√2)` driving 7.6.8
private lemma cser768_T_values (a : ℝ) (ha : 4 * a ^ 2 = 2) : ∀ m : ℕ,
    cser769T a (2 * m) = (-1) ^ m * a ∧ cser769T a (2 * m + 1) = -((-1) ^ m * a) := by
  have hstep : ∀ n : ℕ, cser769T a (n + 2) = -cser769T a n := by
    intro n
    rw [cser769T_eq_Tn, cser769T_eq_Tn]
    have := cser769Tn_period a ha (2 * n + 1)
    rw [show 2 * n + 1 + 4 = 2 * (n + 2) + 1 from by ring] at this
    exact this
  have h0 : cser769T a 0 = a := by
    rw [cser769T_eq_Tn]
    norm_num [cser769Tn_one]
  have h1 : cser769T a 1 = -a := by
    rw [cser769T_eq_Tn]
    have hr := cser769Tn_rec a 1
    have hr0 := cser769Tn_rec a 0
    rw [show (1 : ℕ) + 2 = 3 from by norm_num, show (1 : ℕ) + 1 = 2 from by norm_num] at hr
    rw [show (0 : ℕ) + 2 = 2 from by norm_num, show (0 : ℕ) + 1 = 1 from by norm_num] at hr0
    rw [show 2 * 1 + 1 = 3 from by norm_num, hr, hr0, cser769Tn_one, cser769Tn_zero]
    linear_combination a * ha
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ p ih =>
      constructor
      · rw [show 2 * (p + 1) = 2 * p + 2 from by ring, hstep (2 * p), ih.1]
        ring
      · rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 2 from by ring, hstep (2 * p + 1), ih.2]
        ring

-- no-dlmf: the DLMF 7.6.9 identity, established for every real `a` (the display's
-- `-1 ≤ a ≤ 1` restriction is not needed by this route); shared by the four public
-- surfaces below, which must precede one another in the file's fixed order
private lemma cser769_formula (a : ℝ) (z : ℂ) :
    FLMF.Error.cerf ((a : ℂ) * z) =
      (2 * z / (Real.sqrt π : ℂ)) * Complex.exp (((1 / 2 - a ^ 2 : ℝ) : ℂ) * z ^ 2) *
        ∑' n : ℕ,
          (((Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a : ℝ) : ℂ) *
            FLMF.Bessel.modSphericalIC n (z ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [FLMF.Error.cerf_zero]
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := by
    have h : Real.sqrt π ≠ 0 := by
      have := Real.sqrt_pos.mpr Real.pi_pos
      linarith
    exact_mod_cast h
  have hid : (∑' n : ℕ, (((Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a : ℝ) : ℂ) *
      FLMF.Bessel.modSphericalIC n (z ^ 2 / 2)) = ∑' n : ℕ, cser769f (z ^ 2 / 2) n a := rfl
  rw [hid, cser769_main z hz a]
  have he : Complex.exp (((1 / 2 - a ^ 2 : ℝ) : ℂ) * z ^ 2)
      * Complex.exp (((a : ℂ) ^ 2 - 1 / 2) * z ^ 2) = 1 := by
    rw [← Complex.exp_add]
    have hz0 : (((1 / 2 - a ^ 2 : ℝ) : ℂ) * z ^ 2 + ((a : ℂ) ^ 2 - 1 / 2) * z ^ 2) = 0 := by
      push_cast
      ring
    rw [hz0, Complex.exp_zero]
  have h1 : (2 * z / (Real.sqrt π : ℂ)) * ((Real.sqrt π : ℂ) / (2 * z)) = 1 := by
    field_simp
  linear_combination (-(FLMF.Error.cerf ((a : ℂ) * z))
      * ((2 * z / (Real.sqrt π : ℂ)) * ((Real.sqrt π : ℂ) / (2 * z)))) * he
    - (FLMF.Error.cerf ((a : ℂ) * z)) * h1

-- no-dlmf: the pair-regrouped Bessel-coefficient series of 7.6.8, as a `HasSum`
-- (the `a = 1/√2` instance of the 7.6.9 series, summed in consecutive pairs)
private lemma cser768_hasSum (w : ℂ) (hw : w ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n *
        (FLMF.Bessel.modSphericalIC (2 * n) w - FLMF.Bessel.modSphericalIC (2 * n + 1) w))
      (((Real.sqrt 2 : ℝ) : ℂ) * ∑' n : ℕ, cser769f w n (1 / Real.sqrt 2)) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have ha2 : 4 * (1 / Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [div_pow, hs2]
    norm_num
  set g : ℕ → ℂ := fun n => cser769f w n (1 / Real.sqrt 2) with hgdef
  have hgsum : Summable g := cser769_summable_f w hw (1 / Real.sqrt 2)
  have he : HasSum (fun m : ℕ => g (2 * m)) (∑' m : ℕ, g (2 * m)) :=
    (hgsum.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  have ho : HasSum (fun m : ℕ => g (2 * m + 1)) (∑' m : ℕ, g (2 * m + 1)) :=
    (hgsum.comp_injective ((add_left_injective 1).comp
      (mul_right_injective₀ (two_ne_zero' ℕ)))).hasSum
  have hfull : HasSum g ((∑' m : ℕ, g (2 * m)) + ∑' m : ℕ, g (2 * m + 1)) := he.even_add_odd ho
  have hpair := (he.add ho).mul_left ((Real.sqrt 2 : ℝ) : ℂ)
  have hterm : ∀ m : ℕ, ((Real.sqrt 2 : ℝ) : ℂ) * (g (2 * m) + g (2 * m + 1))
      = (-1 : ℂ) ^ m * (FLMF.Bessel.modSphericalIC (2 * m) w
        - FLMF.Bessel.modSphericalIC (2 * m + 1) w) := by
    intro m
    have hv := cser768_T_values (1 / Real.sqrt 2) ha2 m
    simp only [hgdef, cser769f, hv.1, hv.2]
    push_cast
    field_simp
    ring
  have hfinal : HasSum (fun m : ℕ => (-1 : ℂ) ^ m
      * (FLMF.Bessel.modSphericalIC (2 * m) w
        - FLMF.Bessel.modSphericalIC (2 * m + 1) w))
      (((Real.sqrt 2 : ℝ) : ℂ) * ((∑' m : ℕ, g (2 * m)) + ∑' m : ℕ, g (2 * m + 1))) := by
    refine hpair.congr_fun ?_
    intro m
    exact (hterm m).symm
  rw [hfull.tsum_eq]
  exact hfinal

-- no-dlmf: the DLMF 7.6.8 identity; the `a = 1/√2`, `z ↦ z√2` instance of
-- `cser769_formula`, regrouped in consecutive pairs
private lemma cser768_formula (z : ℂ) :
    FLMF.Error.cerf z =
      (2 * z / (Real.sqrt π : ℂ)) *
        ∑' n : ℕ,
          (-1 : ℂ) ^ n *
            (FLMF.Bessel.modSphericalIC (2 * n) (z ^ 2) -
              FLMF.Bessel.modSphericalIC (2 * n + 1) (z ^ 2)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [FLMF.Error.cerf_zero]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have ha2 : 4 * (1 / Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    rw [div_pow, hs2]
    norm_num
  have hw : (z ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hz
  have hsC : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hc := cser769_formula (1 / Real.sqrt 2) (z * ((Real.sqrt 2 : ℝ) : ℂ))
  have harg : ((1 / Real.sqrt 2 : ℝ) : ℂ) * (z * ((Real.sqrt 2 : ℝ) : ℂ)) = z := by
    push_cast
    field_simp
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hs2
  have hbess : (z * ((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 / 2 = z ^ 2 := by
    rw [mul_pow, hsq]
    ring
  have hexp1 : Complex.exp (((1 / 2 - (1 / Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ)
      * (z * ((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) = 1 := by
    have h0 : (1 / 2 - (1 / Real.sqrt 2 : ℝ) ^ 2 : ℝ) = 0 := by nlinarith [ha2]
    rw [h0]
    simp
  rw [harg, hbess, hexp1] at hc
  have hid : (∑' n : ℕ, (((Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval
        (1 / Real.sqrt 2) : ℝ) : ℂ) * FLMF.Bessel.modSphericalIC n (z ^ 2))
      = ∑' n : ℕ, cser769f (z ^ 2) n (1 / Real.sqrt 2) := rfl
  rw [hid] at hc
  rw [(cser768_hasSum (z ^ 2) hw).tsum_eq, hc]
  ring

-- no-dlmf: `j_n(w) = i^n · i_n^{(1)}(-i w)` over ℂ, the bridge between FLMF's complex
-- spherical and modified spherical Bessel functions (DLMF 10.47.12); no DLMF display
-- of its own
private lemma sphericalJC_ofModSpherical (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    FLMF.Bessel.sphericalJC n w
      = Complex.I ^ n * FLMF.Bessel.modSphericalIC n (-Complex.I * w) := by
  have hsinh : Complex.sinh (-Complex.I * w) = -(Complex.sin w * Complex.I) := by
    rw [show (-Complex.I * w) = -(w * Complex.I) from by ring, Complex.sinh_neg,
      Complex.sinh_mul_I]
  have hcosh : Complex.cosh (-Complex.I * w) = Complex.cos w := by
    rw [show (-Complex.I * w) = -(w * Complex.I) from by ring, Complex.cosh_neg,
      Complex.cosh_mul_I]
  suffices h : ∀ m : ℕ,
      (FLMF.Bessel.sphericalJC m w
        = Complex.I ^ m * FLMF.Bessel.modSphericalIC m (-Complex.I * w)) ∧
      (FLMF.Bessel.sphericalJC (m + 1) w
        = Complex.I ^ (m + 1) * FLMF.Bessel.modSphericalIC (m + 1) (-Complex.I * w)) from
    (h n).1
  intro m
  induction m with
  | zero =>
      constructor
      · rw [show FLMF.Bessel.sphericalJC 0 w = Complex.sin w / w from rfl,
          FLMF.Bessel.modSphericalI_zero_complex, hsinh]
        field_simp
      · rw [show FLMF.Bessel.sphericalJC 1 w
              = Complex.sin w / w ^ 2 - Complex.cos w / w from rfl,
          FLMF.Bessel.modSphericalI_one_complex, hsinh, hcosh]
        field_simp
        ring
  | succ p ih =>
      refine ⟨ih.2, ?_⟩
      have hrecJ := FLMF.Bessel.sphericalJC_recurrence p w
      have hrecI := FLMF.Bessel.modSphericalI_recurrence_complex p (-Complex.I * w)
      have hI2 : Complex.I ^ (p + 2) = -Complex.I ^ p := by
        rw [pow_add, Complex.I_sq]
        ring
      rw [hrecJ, hrecI, hI2, ih.1, ih.2]
      have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      ring_nf
      linear_combination (Complex.I ^ p * (2 * (p : ℂ) + 3)
        * FLMF.Bessel.modSphericalIC (1 + p) (-(Complex.I * w))) * Complex.I_sq

-- no-dlmf: real trace of `sphericalJC_ofModSpherical`; no DLMF display of its own
private lemma sphericalJ_ofModSpherical (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ((FLMF.Bessel.sphericalJ n x : ℝ) : ℂ)
      = Complex.I ^ n * FLMF.Bessel.modSphericalIC n (-Complex.I * (x : ℂ)) := by
  have hxC : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [← FLMF.Bessel.sphericalJC_ofReal]
  exact sphericalJC_ofModSpherical n hxC

-- no-dlmf: combined body of 7.6.10/7.6.11 — the spherical-Bessel expansion of
-- `C(z) + i S(z)` at complex `z`, obtained from 7.6.8 at `ζ = ½√π(1-i)z` via DLMF 7.5.8
private lemma cser76_cfresnel_hasSum (z : ℂ) (hz : z ≠ 0) :
    HasSum (fun n : ℕ => FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2)
        + Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2))
      (FLMF.Fresnel.cfresnelC z / z + Complex.I * (FLMF.Fresnel.cfresnelS z / z)) := by
  have hX : ((π : ℂ) * z ^ 2 / 2) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ?_ (pow_ne_zero 2 hz)) two_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hpi : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi2 : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = (π : ℂ) := by
    norm_cast
    exact Real.sq_sqrt Real.pi_pos.le
  have h1I : (1 - Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  set ζ : ℂ := (1 / 2) * ((Real.sqrt π : ℝ) : ℂ) * (1 - Complex.I) * z with hzetadef
  have hzeta0 : ζ ≠ 0 := by
    rw [hzetadef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) h1I) hz
  have hzetasq : ζ ^ 2 = -Complex.I * ((π : ℂ) * z ^ 2 / 2) := by
    rw [hzetadef]
    linear_combination ((1 / 4 : ℂ) * (1 - Complex.I) ^ 2 * z ^ 2) * hpi2
      + ((π : ℂ) * z ^ 2 / 4) * Complex.I_sq
  have hw : ζ ^ 2 ≠ 0 := pow_ne_zero 2 hzeta0
  have hb := cser768_hasSum (ζ ^ 2) hw
  set V : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * ∑' n : ℕ, cser769f (ζ ^ 2) n (1 / Real.sqrt 2) with hVdef
  have hterm : ∀ n : ℕ, (-1 : ℂ) ^ n *
      (FLMF.Bessel.modSphericalIC (2 * n) (ζ ^ 2)
        - FLMF.Bessel.modSphericalIC (2 * n + 1) (ζ ^ 2))
      = FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2)
        + Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2) := by
    intro n
    rw [hzetasq, sphericalJC_ofModSpherical (2 * n) hX,
      sphericalJC_ofModSpherical (2 * n + 1) hX]
    have h1 : Complex.I ^ (2 * n) = (-1) ^ n := by
      rw [pow_mul, Complex.I_sq]
    have h2 : Complex.I ^ (2 * n + 1) = (-1) ^ n * Complex.I := by
      rw [pow_succ, h1]
    rw [h1, h2]
    linear_combination (-((-1 : ℂ) ^ n
      * FLMF.Bessel.modSphericalIC (2 * n + 1) (-Complex.I * ((π : ℂ) * z ^ 2 / 2))))
      * Complex.I_sq
  have hb' : HasSum (fun n : ℕ => FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2)
      + Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2)) V :=
    hb.congr_fun (fun n => (hterm n).symm)
  -- identify `V` through DLMF 7.5.8
  have hcerf : FLMF.Error.cerf ζ = (2 * ζ / ((Real.sqrt π : ℝ) : ℂ)) * V := by
    rw [cser768_formula ζ, hb.tsum_eq]
  have h758 := (FLMF.Fresnel.cfresnel_7_5_8 z).1
  have harg : (1 / 2) * ((Real.sqrt π : ℝ) : ℂ) * (1 - Complex.I) * z = ζ := hzetadef.symm
  rw [harg, hcerf] at h758
  have hkey : FLMF.Fresnel.cfresnelC z + Complex.I * FLMF.Fresnel.cfresnelS z = z * V := by
    rw [h758, hzetadef]
    field_simp
    linear_combination (-V) * Complex.I_sq
  have hval : FLMF.Fresnel.cfresnelC z / z + Complex.I * (FLMF.Fresnel.cfresnelS z / z) = V := by
    have hsplit : FLMF.Fresnel.cfresnelC z / z + Complex.I * (FLMF.Fresnel.cfresnelS z / z)
        = (FLMF.Fresnel.cfresnelC z + Complex.I * FLMF.Fresnel.cfresnelS z) / z := by
      ring
    rw [hsplit, hkey, mul_div_cancel_left₀ _ hz]
  rw [hval]
  exact hb'

-- no-dlmf: the two half-series of 7.6.10/7.6.11 at complex `z`, separated from
-- `cser76_cfresnel_hasSum` by the rotation `z ↦ i z` (which flips the sign of the
-- Bessel argument, hence the parity of the odd terms, and rotates `C`, `S` by
-- DLMF 7.4.6)
private lemma cser76_cfresnel_split (z : ℂ) (hz : z ≠ 0) :
    HasSum (fun n : ℕ => FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2))
        (FLMF.Fresnel.cfresnelC z / z) ∧
      HasSum (fun n : ℕ => FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2))
        (FLMF.Fresnel.cfresnelS z / z) := by
  have hI2ne : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have h1 := cser76_cfresnel_hasSum z hz
  have h2 := cser76_cfresnel_hasSum (Complex.I * z) (mul_ne_zero Complex.I_ne_zero hz)
  have harg : (π : ℂ) * (Complex.I * z) ^ 2 / 2 = -((π : ℂ) * z ^ 2 / 2) := by
    linear_combination ((π : ℂ) * z ^ 2 / 2) * Complex.I_sq
  have h746 := FLMF.Fresnel.cfresnel_7_4_6 z
  rw [harg, h746.1, h746.2] at h2
  have hterm2 : ∀ n : ℕ,
      FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2)
        - Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2)
      = FLMF.Bessel.sphericalJC (2 * n) (-((π : ℂ) * z ^ 2 / 2))
        + Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) (-((π : ℂ) * z ^ 2 / 2)) := by
    intro n
    rw [FLMF.Bessel.sphericalJC_neg, FLMF.Bessel.sphericalJC_neg]
    have he : ((-1 : ℂ)) ^ (2 * n) = 1 := by
      rw [pow_mul]; norm_num
    have ho : ((-1 : ℂ)) ^ (2 * n + 1) = -1 := by
      rw [pow_succ, he]; ring
    rw [he, ho]
    ring
  have h2' : HasSum (fun n : ℕ => FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2)
      - Complex.I * FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2))
      (FLMF.Fresnel.cfresnelC z / z - Complex.I * (FLMF.Fresnel.cfresnelS z / z)) := by
    have h := h2.congr_fun hterm2
    have hvv : Complex.I * FLMF.Fresnel.cfresnelC z / (Complex.I * z)
        + Complex.I * (-Complex.I * FLMF.Fresnel.cfresnelS z / (Complex.I * z))
        = FLMF.Fresnel.cfresnelC z / z - Complex.I * (FLMF.Fresnel.cfresnelS z / z) := by
      have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      ring
    rwa [hvv] at h
  constructor
  · have h := (h1.add h2').div_const 2
    have hv : ((FLMF.Fresnel.cfresnelC z / z + Complex.I * (FLMF.Fresnel.cfresnelS z / z))
        + (FLMF.Fresnel.cfresnelC z / z - Complex.I * (FLMF.Fresnel.cfresnelS z / z))) / 2
        = FLMF.Fresnel.cfresnelC z / z := by ring
    rw [hv] at h
    refine h.congr_fun (fun n => ?_)
    rw [eq_div_iff (two_ne_zero' ℂ)]
    ring
  · have h := (h1.sub h2').div_const (2 * Complex.I)
    have hv : ((FLMF.Fresnel.cfresnelC z / z + Complex.I * (FLMF.Fresnel.cfresnelS z / z))
        - (FLMF.Fresnel.cfresnelC z / z - Complex.I * (FLMF.Fresnel.cfresnelS z / z)))
        / (2 * Complex.I) = FLMF.Fresnel.cfresnelS z / z := by
      rw [div_eq_iff hI2ne]
      ring
    rw [hv] at h
    refine h.congr_fun (fun n => ?_)
    rw [eq_div_iff hI2ne]
    ring

-- no-dlmf: real trace of `cser76_cfresnel_split`; shared body of the real
-- specializations `erf_7_6_10`/`erf_7_6_11`
private lemma cser76_fresnel_hasSum (z : ℝ) (hz : z ≠ 0) :
    HasSum (fun n : ℕ => FLMF.Bessel.sphericalJ (2 * n) (π * z ^ 2 / 2))
        (FLMF.Fresnel.fresnelC z / z) ∧
      HasSum (fun n : ℕ => FLMF.Bessel.sphericalJ (2 * n + 1) (π * z ^ 2 / 2))
        (FLMF.Fresnel.fresnelS z / z) := by
  have hzC : ((z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
  have hcast : ((π : ℂ) * (z : ℂ) ^ 2 / 2) = ((π * z ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have h := cser76_cfresnel_split (z : ℂ) hzC
  rw [hcast, FLMF.Fresnel.cfresnelC_ofReal, FLMF.Fresnel.cfresnelS_ofReal] at h
  have hC : ((FLMF.Fresnel.fresnelC z : ℝ) : ℂ) / (z : ℂ)
      = ((FLMF.Fresnel.fresnelC z / z : ℝ) : ℂ) := by push_cast; ring
  have hS : ((FLMF.Fresnel.fresnelS z : ℝ) : ℂ) / (z : ℂ)
      = ((FLMF.Fresnel.fresnelS z / z : ℝ) : ℂ) := by push_cast; ring
  rw [hC, hS] at h
  constructor
  · rw [← Complex.hasSum_ofReal]
    exact h.1.congr_fun
      (fun n => (FLMF.Bessel.sphericalJC_ofReal (2 * n) (π * z ^ 2 / 2)).symm)
  · rw [← Complex.hasSum_ofReal]
    exact h.2.congr_fun
      (fun n => (FLMF.Bessel.sphericalJC_ofReal (2 * n + 1) (π * z ^ 2 / 2)).symm)

end ModSphericalSeries

-- no-dlmf: real/narrowed restriction of DLMF 7.6.8; faithful surface is cerf_7_6_8
/-- Modified-spherical-Bessel series for the error function `erf`, real
specialization (DLMF 7.6.8 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_8 (z : ℝ) :
    FLMF.Error.erf z =
      (2 * z / Real.sqrt π) *
        ∑' n : ℕ,
          (-1 : ℝ) ^ n *
            (FLMF.Bessel.modSphericalI (2 * n) (z ^ 2) -
              FLMF.Bessel.modSphericalI (2 * n + 1) (z ^ 2)) := by
  have hc := cser768_formula (z : ℂ)
  have hL : FLMF.Error.cerf (z : ℂ) = ((FLMF.Error.erf z : ℝ) : ℂ) := FLMF.Error.cerf_ofReal z
  have hS : (∑' n : ℕ, (-1 : ℂ) ^ n * (FLMF.Bessel.modSphericalIC (2 * n) ((z : ℂ) ^ 2)
        - FLMF.Bessel.modSphericalIC (2 * n + 1) ((z : ℂ) ^ 2)))
      = ((∑' n : ℕ, (-1 : ℝ) ^ n * (FLMF.Bessel.modSphericalI (2 * n) (z ^ 2)
          - FLMF.Bessel.modSphericalI (2 * n + 1) (z ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    have hz2 : ((z : ℂ)) ^ 2 = ((z ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hz2, modSphericalIC_ofReal, modSphericalIC_ofReal]
    push_cast
    ring
  rw [hL, hS] at hc
  apply Complex.ofReal_injective
  rw [hc]
  push_cast
  ring

/-- **DLMF 7.6.8** — Modified-spherical-Bessel series for the complex error
    function `erf`,
    `erf(z) = (2z/√π)·∑ₙ (-1)ⁿ(i_{2n}^{(1)}(z²) - i_{2n+1}^{(1)}(z²))`,
    for `z` complex.

DAG: E-7.6.8.
Numerical: N/A (equality)
Verified: verified
-/
theorem cerf_7_6_8 (z : ℂ) :
    FLMF.Error.cerf z =
      (2 * z / (Real.sqrt π : ℂ)) *
        ∑' n : ℕ,
          (-1 : ℂ) ^ n *
            (FLMF.Bessel.modSphericalIC (2 * n) (z ^ 2) -
              FLMF.Bessel.modSphericalIC (2 * n + 1) (z ^ 2)) := by
  exact cser768_formula z

-- no-dlmf: real/narrowed restriction of DLMF 7.6.9; faithful surface is cerf_7_6_9
/-- Chebyshev/modified-spherical-Bessel series for the scaled error function
`erf (a z)`, for `-1 ≤ a ≤ 1`, real specialization (DLMF 7.6.9 assigns `z` the
domain "complex variable").
-/
theorem erf_7_6_9 (a z : ℝ) (ha : -1 ≤ a) (ha' : a ≤ 1) :
    FLMF.Error.erf (a * z) =
      (2 * z / Real.sqrt π) * Real.exp ((1 / 2 - a ^ 2) * z ^ 2) *
        ∑' n : ℕ,
          (Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a *
            FLMF.Bessel.modSphericalI n (z ^ 2 / 2) := by
  have hc := cser769_formula a (z : ℂ)
  have hL : FLMF.Error.cerf ((a : ℂ) * (z : ℂ)) = ((FLMF.Error.erf (a * z) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, FLMF.Error.cerf_ofReal]
  have hS : (∑' n : ℕ, (((Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a : ℝ) : ℂ) *
        FLMF.Bessel.modSphericalIC n ((z : ℂ) ^ 2 / 2))
      = ((∑' n : ℕ, (Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a *
          FLMF.Bessel.modSphericalI n (z ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    rw [Complex.ofReal_mul, ← modSphericalIC_ofReal]
    congr 2
    push_cast
    ring
  rw [hL, hS] at hc
  apply Complex.ofReal_injective
  rw [hc]
  push_cast
  ring

/-- **DLMF 7.6.9** — Chebyshev/modified-spherical-Bessel series for the scaled
    complex error function `erf (a z)`, for real `a` with `-1 ≤ a ≤ 1` and `z`
    complex,
    `erf(az) = (2z/√π)·e^{(1/2-a²)z²}·∑ₙ T_{2n+1}(a)·i_n^{(1)}(z²/2)`.

DAG: E-7.6.9.
Numerical: N/A (equality)
Verified: verified
-/
theorem cerf_7_6_9 (a : ℝ) (z : ℂ) (ha : -1 ≤ a) (ha' : a ≤ 1) :
    FLMF.Error.cerf ((a : ℂ) * z) =
      (2 * z / (Real.sqrt π : ℂ)) * Complex.exp (((1 / 2 - a ^ 2 : ℝ) : ℂ) * z ^ 2) *
        ∑' n : ℕ,
          (((Polynomial.Chebyshev.T ℝ (2 * n + 1)).eval a : ℝ) : ℂ) *
            FLMF.Bessel.modSphericalIC n (z ^ 2 / 2) := by
  exact cser769_formula a z

-- no-dlmf: real/narrowed restriction of DLMF 7.6.10; faithful surface is cfresnel_7_6_10
/-- Spherical-Bessel series for the Fresnel cosine integral `C`, real
specialization (DLMF 7.6.10 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_10 (z : ℝ) :
    FLMF.Fresnel.fresnelC z =
      z * ∑' n : ℕ, FLMF.Bessel.sphericalJ (2 * n) (π * z ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [(cser76_fresnel_hasSum z hz).1.tsum_eq]
  field_simp

-- no-dlmf: real/narrowed restriction of DLMF 7.6.11; faithful surface is cfresnel_7_6_11
/-- Spherical-Bessel series for the Fresnel sine integral `S`, real
specialization (DLMF 7.6.11 assigns `z` the domain "complex variable").
-/
theorem erf_7_6_11 (z : ℝ) :
    FLMF.Fresnel.fresnelS z =
      z * ∑' n : ℕ, FLMF.Bessel.sphericalJ (2 * n + 1) (π * z ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [(cser76_fresnel_hasSum z hz).2.tsum_eq]
  field_simp

/-- **DLMF 7.6.10** — spherical-Bessel series for the complex Fresnel cosine
    integral `C`,
    `C(z) = z·∑ₙ j_{2n}(π z²/2)`,
    for `z` complex.

DLMF 7.6.10.
DAG: E-7.6.10.
Numerical: N/A
Verified: verified
-/
theorem cfresnel_7_6_10 (z : ℂ) :
    FLMF.Fresnel.cfresnelC z =
      z * ∑' n : ℕ, FLMF.Bessel.sphericalJC (2 * n) ((π : ℂ) * z ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [(cser76_cfresnel_split z hz).1.tsum_eq]
  field_simp

/-- **DLMF 7.6.11** — spherical-Bessel series for the complex Fresnel sine
    integral `S`,
    `S(z) = z·∑ₙ j_{2n+1}(π z²/2)`,
    for `z` complex.

DLMF 7.6.11.
DAG: E-7.6.11.
Numerical: N/A
Verified: verified
-/
theorem cfresnel_7_6_11 (z : ℂ) :
    FLMF.Fresnel.cfresnelS z =
      z * ∑' n : ℕ, FLMF.Bessel.sphericalJC (2 * n + 1) ((π : ℂ) * z ^ 2 / 2) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [(cser76_cfresnel_split z hz).2.tsum_eq]
  field_simp

end FLMF.Error
