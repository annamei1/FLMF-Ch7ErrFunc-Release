import Mathlib
import FLMF.Chapter7.Erf
import FLMF.Chapter7.FresnelBasic
import FLMF.Chapter7.ComplexErf
import FLMF.Chapter7.ErfcLeading
import FLMF.Chapter7.InverseErf
import FLMF.Chapter7.FresnelComplex
import FLMF.Support.AnalyticZeroCount
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Real.Pi.Bounds


/-! Background on the complex zeros (formerly the standalone zeros overview). -/
/-!
# Zeros of the error functions and Fresnel integrals (DLMF §7.13)

**RESOLVED**: every §7.13 equation is now STATED and PROVEN in
`Error/ComplexZeros.lean` (`erf_7_13_1`…`erf_7_13_7` + the `…_S` variant),
against the complex `cerf`/`cerfc` and `cfresnelC`/`cfresnelS` keystones. This
module is kept for the background context below; it contains only the chapter
header and namespace, and elaborates cleanly with no declarations.

DLMF §7.13 "Zeros" describes the location of the zeros of `erf`, `erfc`, and the
Fresnel integrals `C`, `S`. Every numbered equation in this section (7.13.1
through 7.13.7) is intrinsically about the COMPLEX zeros of these functions, and
all are asymptotic (`∼`) expansions or parameter definitions feeding them:

* For `erf z`, the only real zero is the simple zero at `z = 0`; all other zeros
  are genuinely complex, lying (in order of increasing modulus) at
  `z_n = x_n + i y_n` in the first quadrant, together with their reflections
  `-z_n, z̄_n, -z̄_n`.
* For `erfc z` there are no real zeros at all; its zeros `z_n = x_n + i y_n` lie
  in the sector `π/2 < ph z < 3π/4`, together with the conjugates `z̄_n`.
* The Fresnel zeros (7.13.5–7.13.7) are likewise complex.

FLMF's `erf`, `erfc`, `fresnelC`, `fresnelS` (as imported by this module) are
REAL-valued functions (`ℝ → ℝ`); the §7.13 equations are about the zeros of the
COMPLEX error function / complex Fresnel integral, which is exactly why the
proofs live in `ComplexZeros.lean` against the complex `cerf`/`cerfc`/
`cfresnelC`/`cfresnelS` keystones instead of here.
-/

namespace FLMF.Error

open Real

end FLMF.Error

/-!
# Complex zeros of `erf`, `erfc`, and the Fresnel integrals `C`, `S` (DLMF §7.13)

This module faithfully *states* the asymptotic expansions of the complex zeros of
the error function `cerf`, the complementary error function `cerfc`, and the
complex Fresnel integrals `cfresnelC`, `cfresnelS`, following DLMF §7.13.

For each family we provide:

* honest `def`s for the numbered parameter equations (7.13.2 / 7.13.4 / 7.13.6 /
  7.13.7) and a theorem that records each parameter equation by `rfl`;
* honest `def`s for the three-term approximations to the real and imaginary parts
  of the `n`-th zero (the leading content of 7.13.1 / 7.13.3 / 7.13.5);
* asymptotic *surface* theorems (7.13.1 / 7.13.3 / 7.13.5) stating that, for the
  COMPLETE strictly-ordered enumeration `z` of ALL zeros of the relevant function
  in the appropriate sector (a `hall` completeness hypothesis rules out
  skip-subsequences), the real and imaginary parts of `z n` agree with the stated
  approximations up to `o` of the last stated correction order.

Every declaration in this file is fully proven (no `sorry`): the asymptotic
surfaces, the parameter/approximation defs, and the four low-zero-count
theorems (argument-principle sections `Erf713ZeroCount` / `Erfc713ZeroCount` /
`Fresnel713ZeroCount`).

The style mirrors `FLMF.Bessel.mcMahonApprox` (McMahon zeros of `J_ν`).
-/

noncomputable section

namespace FLMF.Error

open Real Filter Topology Asymptotics Metric

/-! ## erf zeros — parameters (DLMF 7.13.2) -/

-- no-dlmf: encodes the 7.13.2 parameter λ; display surfaced at `erf_7_13_2`
/-- DLMF 7.13.2 (parameter `λ` for the `n`-th first-quadrant zero of `erf`):
`λ = √((n − 1/8)·π)`.
* dlmf: 7.13.2
* family: error
* kind: zero-asymptotic-parameter -/
def erfZeroLambda (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) - 1 / 8) * Real.pi)

-- no-dlmf: encodes the 7.13.2 parameter μ; display surfaced at `erf_7_13_2`
/-- DLMF 7.13.2 (parameter `μ` for the `n`-th first-quadrant zero of `erf`):
`μ = log (λ · √(2π))`.
* dlmf: 7.13.2
* family: error
* kind: zero-asymptotic-parameter -/
def erfZeroMu (n : ℕ) : ℝ := Real.log (erfZeroLambda n * Real.sqrt (2 * Real.pi))

/-- DLMF 7.13.2 — records the parameter equations for the `erf` zeros.

DLMF §7.13 indexes these zeros `n = 1, 2, 3, …` (Tables 7.13.1–7.13.4 tabulate
`n = 1..5`), matching `erf_7_13_1`'s 1-based enumeration; the `1 ≤ n` hypothesis
is that index range, not a narrowing. On it every displayed logarithm argument is
a positive real, where `Real.log` coincides with DLMF's principal branch `ln`, and
`Real.sqrt` with the principal square root.

Numerical: PASS
Verified: verified
DAG: E-7.13.2.
-/
theorem erf_7_13_2 (n : ℕ) (_hn : 1 ≤ n) :
    erfZeroLambda n = Real.sqrt (((n : ℝ) - 1 / 8) * Real.pi) ∧
      erfZeroMu n = Real.log (erfZeroLambda n * Real.sqrt (2 * Real.pi)) :=
  ⟨rfl, rfl⟩

/-! ## erf zeros — approximation (DLMF 7.13.1) -/

-- no-dlmf: encodes the 7.13.1 approximant; display surfaced at `erf_7_13_1`
/-- DLMF 7.13.1 — three-term approximation of the real part of the `n`-th
first-quadrant zero of `erf`:
`xₙ = λ − (1/4)·μ·λ⁻¹ + (1/16)·(1 − μ + ½μ²)·λ⁻³`.
* dlmf: 7.13.1
* family: error
* kind: zero-approximation -/
def erfZeroReApprox (n : ℕ) : ℝ :=
  let lam := erfZeroLambda n
  let mu := erfZeroMu n
  lam - (1 / 4) * mu * lam⁻¹ + (1 / 16) * (1 - mu + (1 / 2) * mu ^ 2) * lam⁻¹ ^ 3

-- no-dlmf: encodes the 7.13.1 approximant; display surfaced at `erf_7_13_1`
/-- DLMF 7.13.1 — three-term approximation of the imaginary part of the `n`-th
first-quadrant zero of `erf`:
`yₙ = λ + (1/4)·μ·λ⁻¹ + (1/16)·(1 − μ + ½μ²)·λ⁻³`.
* dlmf: 7.13.1
* family: error
* kind: zero-approximation -/
def erfZeroImApprox (n : ℕ) : ℝ :=
  let lam := erfZeroLambda n
  let mu := erfZeroMu n
  lam + (1 / 4) * mu * lam⁻¹ + (1 / 16) * (1 - mu + (1 / 2) * mu ^ 2) * lam⁻¹ ^ 3

/-! ## erf zeros — the effective zero equation

The analytic input for the 7.13.1/7.13.3 zero asymptotics.  A zero of `erf` in the right
half-plane is a solution of `erfc w = 1`, so the uniform Poincaré remainder estimate
`FLMF.Error.cerfc_poincare_bound` turns it into an *effective* transcendental equation
for `w`, with an explicit constant. -/

-- no-dlmf: the `n = 1` truncation of the Poincaré expansion evaluated at a zero of `erf`;
-- proof infrastructure for the §7.13 zero asymptotics, not itself a numbered DLMF display
/-- **The effective zero equation for `erf`.**  If `Re w > 0` and `erf w = 0` — equivalently
`erfc w = 1` — then

`‖√π · w · e^{w²} − 1‖ ≤ 4 / ‖w‖²`.

This is the `n = 1` instance of the uniform sector bound `FLMF.Error.cerfc_poincare_bound`
with `δ = π/4`, for which the sector condition `|ph w| ≤ 3π/4 − δ = π/2` holds on the whole
open right half-plane and the explicit constant collapses (`sin (2δ/3) = sin (π/6) = 1/2`,
so `2 · 2! / (2 · (½‖w‖))³ = 4/‖w‖³`), multiplied through by `w`.

It says that a zero of `erf` far from the origin satisfies
`e^{w²} = (1 + O(‖w‖⁻²)) / (√π w)`, whose logarithm is what produces the parameters `λ`,
`μ` of 7.13.2 and, after inversion, the approximations `erfZeroReApprox`,
`erfZeroImApprox`. -/
theorem cerf_zero_equation {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re) :
    ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - 1‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hz : w ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hz
  have hsec : |Complex.arg w| ≤ 3 * Real.pi / 4 - Real.pi / 4 := by
    have h : |Complex.arg w| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 4) (by positivity) (by linarith) hz hsec 1
  have hcerfc : cerfc w = 1 := by rw [cerfc, hw]; ring
  have hsin : Real.sin (2 * (Real.pi / 4) / 3) = 1 / 2 := by
    rw [show 2 * (Real.pi / 4) / 3 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hcerfc, hsin] at h
  simp only [Finset.sum_range_one] at h
  norm_num at h
  have hadd : ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - w⁻¹‖ ≤ 4 / ‖w‖ ^ 3 := by
    convert h using 2; ring_nf
  have hfac : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - 1
      = w * ((Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - w⁻¹) := by
    field_simp
  rw [hfac, norm_mul]
  calc ‖w‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - w⁻¹‖
      ≤ ‖w‖ * (4 / ‖w‖ ^ 3) := mul_le_mul_of_nonneg_left hadd hwn.le
    _ = 4 / ‖w‖ ^ 2 := by field_simp

-- no-dlmf: logarithmic form of the effective zero equation `cerf_zero_equation`;
-- proof infrastructure for the §7.13 zero asymptotics, not a numbered DLMF display
/-- **The logarithmic zero equation for `erf`.**  If `Re w > 0`, `erf w = 0` and `‖w‖ ≥ 3`,
then for some integer `k`

`‖w² + log (√π · w) − 2πi·k‖ ≤ 6 / ‖w‖²`.

Taking logarithms in `cerf_zero_equation` converts the multiplicative estimate
`√π · w · e^{w²} = 1 + O(‖w‖⁻²)` into an additive one modulo `2πi`; the constant
`6 = (3/2)·4` comes from `Complex.norm_log_one_add_half_le_self`.  The integer `k` is the
*index* of the zero, and the real and imaginary components of this single equation are the
source of the parameters `λ`, `μ` of DLMF 7.13.2 (see `cerf_zero_re_equation` and
`cerf_zero_im_equation`). -/
theorem cerf_zero_log_equation {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re) (hbig : 3 ≤ ‖w‖) :
    ∃ k : ℤ, ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 6 / ‖w‖ ^ 2 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hz
  have hw2 : (9 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hprod : ((Real.sqrt Real.pi : ℝ) : ℂ) * w ≠ 0 := mul_ne_zero hsp hz
  set u : ℂ := w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) with hu
  have hexpu : Complex.exp u = (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) := by
    rw [hu, Complex.exp_add, Complex.exp_log hprod]; ring
  have hd : ‖Complex.exp u - 1‖ ≤ 4 / ‖w‖ ^ 2 := by
    rw [hexpu]; exact cerf_zero_equation hw hre
  have hhalf : ‖Complex.exp u - 1‖ ≤ 1 / 2 := by
    refine hd.trans ?_
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖w‖ ^ 2)]
    linarith
  have h1δ : (1 : ℂ) + (Complex.exp u - 1) = Complex.exp u := by ring
  have hlogbound : ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := by
    have := Complex.norm_log_one_add_half_le_self hhalf
    rwa [h1δ] at this
  have hone : Complex.exp (u - Complex.log (Complex.exp u)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero u),
      div_self (Complex.exp_ne_zero u)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨k, ?_⟩
  have heq : u - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp u) := by
    linear_combination hk
  rw [heq]
  calc ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := hlogbound
    _ ≤ (3 / 2) * (4 / ‖w‖ ^ 2) := by linarith
    _ = 6 / ‖w‖ ^ 2 := by ring

-- no-dlmf: real component of `cerf_zero_log_equation`; proof infrastructure for §7.13
/-- **The `λ`/`μ` equation for a zero of `erf`.**  Taking real parts in
`cerf_zero_log_equation` (the index term `2πi·k` is purely imaginary, so it drops out):
for a zero `w` of `erf` with `Re w > 0` and `‖w‖ ≥ 3`,

`|x² − y² + log (√π ‖w‖)| ≤ 6 / ‖w‖²`,  `w = x + i y`.

This is the equation behind DLMF 7.13.2's `μ = log (λ√(2π))`: at the `n`-th zero
`‖w‖ ≈ λ√2`, so `log (√π ‖w‖) ≈ log (λ√(2π)) = μ`, while `x² − y² = (x−y)(x+y) ≈ −μ`
matches `xₙ − yₙ ≈ −μ/(2λ)` of 7.13.1. -/
theorem cerf_zero_re_equation {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re) (hbig : 3 ≤ ‖w‖) :
    |w.re ^ 2 - w.im ^ 2 + Real.log (Real.sqrt Real.pi * ‖w‖)| ≤ 6 / ‖w‖ ^ 2 := by
  obtain ⟨k, hk⟩ := cerf_zero_log_equation hw hre hbig
  refine le_trans (le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)) hk
  have hnorm : ‖((Real.sqrt Real.pi : ℝ) : ℂ) * w‖ = Real.sqrt Real.pi * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp [Complex.sub_re, Complex.add_re, Complex.log_re, Complex.mul_re,
    Complex.mul_im, pow_two]
  rw [abs_of_nonneg (Real.sqrt_nonneg Real.pi), mul_comm (Real.sqrt Real.pi) ‖w‖]

-- no-dlmf: imaginary component of `cerf_zero_log_equation`; proof infrastructure for §7.13
/-- **The index equation for a zero of `erf`.**  Taking imaginary parts in
`cerf_zero_log_equation`: for a zero `w = x + i y` of `erf` with `Re w > 0` and `‖w‖ ≥ 3`
there is an integer `k` with

`|2xy + ph w − 2πk| ≤ 6 / ‖w‖²`.

Since `ph w ≈ π/4` and `2xy ≈ 2λ²` at the `n`-th first-quadrant zero, this is the equation
that pins `λ² = (k − 1/8)π`, i.e. DLMF 7.13.2, once `k` is identified with the zero's
DLMF index. -/
theorem cerf_zero_im_equation {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re) (hbig : 3 ≤ ‖w‖) :
    ∃ k : ℤ, |2 * w.re * w.im + Complex.arg w - 2 * Real.pi * k| ≤ 6 / ‖w‖ ^ 2 := by
  obtain ⟨k, hk⟩ := cerf_zero_log_equation hw hre hbig
  refine ⟨k, le_trans (le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)) hk⟩
  have harg : (((Real.sqrt Real.pi : ℝ) : ℂ) * w).arg = w.arg :=
    Complex.arg_real_mul w (Real.sqrt_pos.mpr Real.pi_pos)
  simp [Complex.sub_im, Complex.add_im, Complex.log_im, harg, Complex.mul_re,
    Complex.mul_im, pow_two]
  ring_nf

-- no-dlmf: leading-order localization of a first-quadrant zero of `erf` from the two
-- component equations; proof infrastructure for the §7.13 zero asymptotics
/-- **Leading-order localization of a first-quadrant zero of `erf`.**  For a zero
`w = x + i y` of `erf` in the open first quadrant with `‖w‖ ≥ 3` there is an integer `k`
(the index supplied by `cerf_zero_im_equation`) with

`|‖w‖² − 2πk| ≤ π/2 + 6/‖w‖² + (|log (√π ‖w‖)| + 6/‖w‖²)² / ‖w‖²`.

Since `‖w‖² = x² + y²` and `2xy = 2πk − ph w + O(‖w‖⁻²)`, the gap `‖w‖² − 2xy = (x − y)²`
is controlled by the real component equation `cerf_zero_re_equation` through
`|x − y| = |x² − y²| / (x + y) ≤ (|log (√π‖w‖)| + 6/‖w‖²)/‖w‖`, using `x + y ≥ ‖w‖`.
Hence `‖w‖² = 2πk + O(1 + log²‖w‖ / ‖w‖²)`; comparing with `λ_k² = (k − 1/8)π` this is the
statement that every large first-quadrant zero has `‖w‖ ≈ λ_k√2`, i.e. `x ≈ y ≈ λ_k` —
the leading term of DLMF 7.13.1 for the zero of index `k`. -/
theorem cerf_zero_modulus_localization {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re)
    (him : 0 < w.im) (hbig : 3 ≤ ‖w‖) :
    ∃ k : ℤ, |‖w‖ ^ 2 - 2 * Real.pi * k| ≤ Real.pi / 2 + 6 / ‖w‖ ^ 2
      + (|Real.log (Real.sqrt Real.pi * ‖w‖)| + 6 / ‖w‖ ^ 2) ^ 2 / ‖w‖ ^ 2 := by
  obtain ⟨k, hk⟩ := cerf_zero_im_equation hw hre hbig
  refine ⟨k, ?_⟩
  have hnsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : (0 : ℝ) < ‖w‖ ^ 2 := by nlinarith
  have hxy : 0 < w.re * w.im := mul_pos hre him
  have hsum : ‖w‖ ≤ w.re + w.im := by
    nlinarith [hnsq, hxy, norm_nonneg w, sq_nonneg (w.re + w.im - ‖w‖)]
  have hre_eq := cerf_zero_re_equation hw hre hbig
  set L : ℝ := |Real.log (Real.sqrt Real.pi * ‖w‖)| with hLdef
  set c : ℝ := L + 6 / ‖w‖ ^ 2 with hcdef
  have hL1 : Real.log (Real.sqrt Real.pi * ‖w‖) ≤ L := le_abs_self _
  have hL2 : -L ≤ Real.log (Real.sqrt Real.pi * ‖w‖) := neg_abs_le _
  have habs : |w.re ^ 2 - w.im ^ 2| ≤ c := by
    have h := abs_le.mp hre_eq
    rw [abs_le]
    constructor <;> [linarith [h.1]; linarith [h.2]]
  have habs' := abs_le.mp habs
  have hsq : (w.re ^ 2 - w.im ^ 2) ^ 2 ≤ c ^ 2 := sq_le_sq' habs'.1 habs'.2
  have hprod : (w.re - w.im) ^ 2 * ‖w‖ ^ 2 ≤ (w.re ^ 2 - w.im ^ 2) ^ 2 := by
    have hexp : (w.re ^ 2 - w.im ^ 2) ^ 2 = (w.re - w.im) ^ 2 * (w.re + w.im) ^ 2 := by ring
    rw [hexp]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [hsum, norm_nonneg w]
  have hgap : (w.re - w.im) ^ 2 ≤ c ^ 2 / ‖w‖ ^ 2 := by
    rw [le_div_iff₀ hpos]; exact hprod.trans hsq
  have hgap' : ‖w‖ ^ 2 - 2 * w.re * w.im = (w.re - w.im) ^ 2 := by rw [hnsq]; ring
  have harg : |Complex.arg w| ≤ Real.pi / 2 :=
    (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)).le
  have hkk := abs_le.mp hk
  have hargg := abs_le.mp harg
  have hsq0 : (0 : ℝ) ≤ (w.re - w.im) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor
  · linarith [hgap, hgap']
  · linarith [hgap, hgap']

/-! ## erf zeros — existence and localization of the zeros themselves

`cerf_zero_equation` and its consequences above are one-directional: they say what a zero of
`erf` must satisfy.  The results in this section run the other way — they *produce* zeros.
The route is: (i) the exact model equation `√π w e^{w²} = 1` has a root `vₙ` near `w² = 2πi n`
(Banach fixed point, `exists_model_root`); (ii) the model function and `√π w e^{w²} erf w`
differ by `O(‖w‖⁻²)` (`cerf_scaled_remainder_bound`), which by the minimum-modulus principle
forces a genuine zero of `erf` within `12/‖vₙ‖³` of `vₙ` (`exists_cerf_zero_near_model`);
(iii) a Cauchy estimate on the same remainder shows the zeros of `erf` are `Θ(‖w‖⁻¹)`-separated
in the sector, so that zero is the only one within `1/(24‖vₙ‖)` of `vₙ`
(`cerf_zero_unique_in_small_ball`).  The package is `existsUnique_cerf_zero_near_model_root`. -/

-- no-dlmf: mean value inequality on a convex subset of `ℂ` in `HasDerivAt` form; proof
-- infrastructure for the §7.13 zero asymptotics, not a numbered DLMF display
/-- Mean value inequality on a convex subset of `ℂ`, in `HasDerivAt` form: if `f` has
derivative `f'` at every point of a convex set `s` and `‖f'‖ ≤ C` there, then `f` is
`C`-Lipschitz on `s`.  (A one-dimensional repackaging of
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`.) -/
theorem norm_sub_le_of_hasDerivAt_le {f f' : ℂ → ℂ} {s : Set ℂ} {C : ℝ} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z) (bound : ∀ z ∈ s, ‖f' z‖ ≤ C) {x y : ℂ}
    (hx : x ∈ s) (hy : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (f' z))
    (fun z hz => ((hf z hz).hasFDerivAt).hasFDerivWithinAt)
    (fun z hz => by
      simpa [ContinuousLinearMap.norm_smulRight_apply] using bound z hz) hx hy

-- no-dlmf: minimum-modulus zero-existence criterion (maximum modulus principle applied to
-- `1/f`); proof infrastructure for the §7.13 zero asymptotics
/-- **Minimum-modulus zero-existence criterion.**  If `f` is entire and `‖f c‖ < ‖f z‖` at
every point `z` of the circle of radius `r > 0` about `c`, then `f` vanishes somewhere in the
open disc.

Otherwise `1/f` would be holomorphic on the closed disc, and the maximum modulus principle
applied to it would give `‖f c‖ ≥ min_{∂} ‖f‖`, contradicting the hypothesis at the minimizer
(which exists because the circle is compact). -/
theorem exists_zero_of_norm_lt_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (h : ∀ z ∈ Metric.sphere c r, ‖f c‖ < ‖f z‖) :
    ∃ z ∈ Metric.ball c r, f z = 0 := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ z ∈ Metric.closedBall c r, f z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with h' | h'
    · exact hcon z (Metric.mem_ball.mpr h')
    · have hzs : z ∈ Metric.sphere c r := Metric.mem_sphere.mpr h'
      have := h z hzs
      intro hfz
      rw [hfz] at this
      simp at this
      exact absurd this (not_lt.mpr (norm_nonneg _))
  have hc0 : f c ≠ 0 := hcon c (Metric.mem_ball_self hr)
  have hcpos : 0 < ‖f c‖ := norm_pos_iff.mpr hc0
  -- min of ‖f‖ on the sphere
  obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (continuous_norm.comp hf.continuous).continuousOn
  have hxpos : 0 < ‖f x‖ := lt_of_le_of_lt (norm_nonneg _) (h x hx)
  -- max modulus for 1/f
  have hdcc : DiffContOnCl ℂ (fun z => (f z)⁻¹) (Metric.ball c r) := by
    constructor
    · intro z hz
      exact ((hf z).inv (hne z (Metric.ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball c hr.ne']
      intro z hz
      exact ((hf z).continuousAt.inv₀ (hne z hz)).continuousWithinAt
  have hbdd : ∀ z ∈ frontier (Metric.ball c r), ‖(f z)⁻¹‖ ≤ ‖f x‖⁻¹ := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    rw [norm_inv]
    exact inv_anti₀ hxpos (hxmin hz)
  have := Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball) hdcc hbdd (subset_closure (Metric.mem_ball_self hr))
  rw [norm_inv] at this
  have : ‖f x‖ ≤ ‖f c‖ := by
    rwa [inv_le_inv₀ hcpos hxpos] at this
  exact absurd this (not_le.mpr (h x hx))

-- no-dlmf: the `n = 1` truncation of the Poincaré expansion on the right half-plane;
-- proof infrastructure for the §7.13 zero asymptotics, not a numbered DLMF display
/-- The scaled complementary error function to leading order, valid on the right half-plane. -/
theorem cerfc_scaled_leading_bound {w : ℂ} (hre : 0 < w.re) :
    ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹‖ ≤ 4 / ‖w‖ ^ 3 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hsec : |Complex.arg w| ≤ 3 * Real.pi / 4 - Real.pi / 4 := by
    have h : |Complex.arg w| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 4) (by positivity)
    (by linarith [Real.pi_pos]) hz hsec 1
  have hsin : Real.sin (2 * (Real.pi / 4) / 3) = 1 / 2 := by
    rw [show 2 * (Real.pi / 4) / 3 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hsin] at h
  simp only [Finset.sum_range_one] at h
  norm_num at h
  convert h using 2
  ring_nf

-- no-dlmf: the model-function remainder bound underlying the §7.13 zero asymptotics;
-- proof infrastructure, not a numbered DLMF display
/-- The key remainder identity/bound: `√π w e^{w²} erf w` differs from `√π w e^{w²} − 1` by
at most `4/‖w‖²` on the right half-plane. -/
theorem cerf_scaled_remainder_bound {w : ℂ} (hre : 0 < w.re) :
    ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerf w
        - ((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - 1)‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hz
  have h := cerfc_scaled_leading_bound hre
  have hid : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerf w
      - ((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - 1)
      = -(w * ((Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹)) := by
    rw [cerfc]
    field_simp
    ring
  rw [hid, norm_neg, norm_mul]
  calc ‖w‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹‖
      ≤ ‖w‖ * (4 / ‖w‖ ^ 3) := mul_le_mul_of_nonneg_left h hwn.le
    _ = 4 / ‖w‖ ^ 2 := by field_simp

-- no-dlmf: existence and location of the exact roots of the model equation
-- `√π w e^{w²} = 1`; proof infrastructure for the §7.13 zero asymptotics
/-- **Existence of the model roots.**  For every `n ≥ 134` the *model equation*
`√π · v · e^{v²} = 1` — the exact form of the transcendental equation that a zero of `erf`
satisfies up to `O(‖w‖⁻²)` (`cerf_scaled_remainder_bound`) — has a solution `v` with

`v² + log (√π v) = 2πi·n`,  `‖v² − 2πi·n‖ ≤ π n`,  `‖v‖ ≥ 20`,  `‖v‖ ≤ 6 Re v`,
`‖v‖ ≤ 6 Im v`.

The exact logarithmic equation `v² + log (√π v) = 2πi n` — not merely its exponentiated
form — is what the fixed point delivers.

**Caution: the model root is not accurate to `o(λ⁻³)`.**  Inverting this equation (by the
same route as `erf713_zero_expansion`) gives `Re v = erfZeroReApprox n − 1/(16 λₙ³) + o(λₙ⁻³)`
and likewise for `Im v` — a `Θ(λ⁻³)` miss, numerically `(Re v − erfZeroReApprox n)·λ³ →
−0.0625 = −1/16`.  The missing `+1/(16λ³)` is contributed by the *second* Poincaré term
`−1/(2w²)` of `cerf_zero_log_equation_third`, which the model equation drops.  For DLMF
7.13.1 one must therefore work from the third-order equation at a genuine zero of `erf`
(`cerf_zero_log_equation_third` + `erf713_zero_expansion`), not from `v` alone.

In particular `v` lies in the open first quadrant with `‖v‖ ≍ √(2πn)`, i.e. `Re v ≈ Im v ≈ λₙ`
in the notation of DLMF 7.13.2.

The proof inverts the logarithmic form of the model equation by the Banach fixed point
theorem: in the variable `u = v²` the equation reads `u = 2πi n − log √π − ½ log u`, whose
right-hand side maps the closed ball `‖u − 2πi n‖ ≤ πn` into itself and contracts there with
ratio `1/(2πn)` (the derivative of `½ log` is `1/(2u)`).  The square root `v = exp(½ log u)`
is then taken on the branch supplied by `arg u ∈ (0, π)`. -/
theorem exists_model_root (n : ℕ) (hn : 134 ≤ n) :
    ∃ v : ℂ, 20 ≤ ‖v‖ ∧ ‖v‖ ≤ 6 * v.re ∧ ‖v‖ ≤ 6 * v.im ∧
      ‖v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ Real.pi * n ∧
      v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v)
        = 2 * (Real.pi : ℂ) * Complex.I * n ∧
      (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hn' : (134:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set M : ℝ := 2 * Real.pi * n with hMdef
  have hMbig : (800:ℝ) ≤ M := by
    have h3 := Real.pi_gt_three
    rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  set c : ℂ := (M : ℂ) * Complex.I with hcdef
  have hcim : c.im = M := by simp [hcdef]
  have hcnorm : ‖c‖ = M := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM0]
  set a : ℝ := Real.log (Real.sqrt Real.pi) with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    refine Real.log_nonneg ?_
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have ha1 : a ≤ 1 := by
    have h1 : Real.sqrt Real.pi ≤ 2 := by
      have h4 : Real.sqrt Real.pi ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
      rwa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
    have h2 := Real.log_le_sub_one_of_pos hsppos
    rw [hadef]; linarith
  set T : ℂ → ℂ := fun u => c - (a : ℂ) - (1/2) * Complex.log u with hTdef
  set s : Set ℂ := Metric.closedBall c (M/2) with hsdef
  have hmem : ∀ u ∈ s, M/2 ≤ u.im ∧ M/2 ≤ ‖u‖ ∧ ‖u‖ ≤ 3*M/2 ∧ u ≠ 0 := by
    intro u hu
    have hd : ‖u - c‖ ≤ M/2 := by rwa [hsdef, Metric.mem_closedBall, dist_eq_norm] at hu
    have him : |u.im - c.im| ≤ M/2 := by
      have h := Complex.abs_im_le_norm (u - c)
      simp only [Complex.sub_im] at h; linarith
    rw [hcim] at him
    have h1 := abs_le.mp him
    have h2 := norm_sub_norm_le u c
    have h3 := norm_sub_norm_le c u
    rw [norm_sub_rev c u] at h3
    rw [hcnorm] at h2 h3
    refine ⟨by linarith [h1.1], by linarith, by linarith, ?_⟩
    intro h; rw [h] at h1; simp at h1; linarith [h1.1]
  have hsconv : Convex ℝ s := by rw [hsdef]; exact convex_closedBall c (M/2)
  -- `T` maps `s` into `s`
  have hmaps : Set.MapsTo T s s := by
    intro u hu
    obtain ⟨him, hn1, hn2, hu0⟩ := hmem u hu
    rw [hsdef, Metric.mem_closedBall, dist_eq_norm]
    have hTc : T u - c = -((a:ℂ) + (1/2) * Complex.log u) := by rw [hTdef]; ring
    rw [hTc, norm_neg]
    have h1 : ‖(a:ℂ) + (1/2) * Complex.log u‖ ≤ a + (1/2) * ‖Complex.log u‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
      have : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [this]
    have h2 : ‖Complex.log u‖ ≤ |Real.log ‖u‖| + Real.pi := by
      have h := Complex.norm_le_abs_re_add_abs_im (Complex.log u)
      rw [Complex.log_re, Complex.log_im] at h
      have h4 := Complex.abs_arg_le_pi u
      linarith
    have hu1 : (1:ℝ) ≤ ‖u‖ := by linarith
    have habs : |Real.log ‖u‖| = Real.log ‖u‖ := abs_of_nonneg (Real.log_nonneg hu1)
    have h3 : Real.log ‖u‖ ≤ 2 * (Real.sqrt ‖u‖ - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < ‖u‖))
      rw [Real.log_sqrt (by linarith)] at h
      linarith
    have h5 : Real.sqrt ‖u‖ ≤ Real.sqrt (3*M/2) := Real.sqrt_le_sqrt hn2
    have h6 : Real.sqrt (3*M/2) ≤ M/2 - 2 := by
      have h7 : Real.sqrt (3*M/2) ≤ Real.sqrt ((M/2-2)^2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h7
    rw [habs] at h2
    linarith [Real.pi_lt_four]
  -- `T` is a contraction on `s`
  have hlip : LipschitzOnWith (Real.toNNReal (1/M)) T s := by
    refine LipschitzOnWith.of_dist_le' (fun u hu u' hu' => ?_)
    have hlogd : ‖Complex.log u' - Complex.log u‖ ≤ (2/M) * ‖u' - u‖ := by
      refine norm_sub_le_of_hasDerivAt_le (f := Complex.log) (f' := fun z => z⁻¹)
        hsconv ?_ ?_ hu hu'
      · intro y hy
        obtain ⟨hyim, -, -, hy0⟩ := hmem y hy
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inr (by
          intro h; rw [h] at hyim; linarith)))
      · intro y hy
        obtain ⟨-, hyn, -, hy0⟩ := hmem y hy
        rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hM0]
        linarith
    have hTd : T u - T u' = -((1/2) * (Complex.log u - Complex.log u')) := by rw [hTdef]; ring
    rw [dist_eq_norm, hTd, norm_neg, norm_mul, dist_eq_norm]
    have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
    have h2 : ‖Complex.log u - Complex.log u'‖ = ‖Complex.log u' - Complex.log u‖ :=
      norm_sub_rev _ _
    have h3 : ‖u' - u‖ = ‖u - u'‖ := norm_sub_rev _ _
    rw [h1, h2]
    rw [h3] at hlogd
    have h4 : (1/2:ℝ) * ‖Complex.log u' - Complex.log u‖
        ≤ (1/2) * (2/M * ‖u - u'‖) := by linarith
    have hfin : (1/2 : ℝ) * (2/M * ‖u - u'‖) = 1/M * ‖u - u'‖ := by
      field_simp
    rw [hfin] at h4
    exact h4
  have hK : Real.toNNReal (1/M) < 1 := by
    rw [show (1 : NNReal) = Real.toNNReal 1 by simp]
    exact (Real.toNNReal_lt_toNNReal_iff one_pos).mpr (by rw [div_lt_one hM0]; linarith)
  obtain ⟨u, hus, hufix, -⟩ := ContractingWith.exists_fixedPoint' (f := T)
    (Metric.isClosed_closedBall.isComplete) hmaps ⟨hK, hlip.mapsToRestrict hmaps⟩
    (Metric.mem_closedBall_self (by linarith)) (edist_ne_top _ _)
  obtain ⟨huim, hun1, hun2, hu0⟩ := hmem u hus
  -- the square root
  set v : ℂ := Complex.exp ((1/2) * Complex.log u) with hvdef
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have hvsq : v ^ 2 = u := by
    rw [hvdef, pow_two, ← Complex.exp_add,
      show (1/2:ℂ) * Complex.log u + (1/2:ℂ) * Complex.log u = Complex.log u by ring,
      Complex.exp_log hu0]
  have hargpos : 0 < Complex.arg u := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr (by linarith : 0 ≤ u.im)) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h.symm
      linarith [this.2]
  have harglt : Complex.arg u < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi u) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_pi_iff.mp h
      linarith [this.2]
  have hwim : ((1/2 : ℂ) * Complex.log u).im = Complex.arg u / 2 := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]
    ring
  have hvre : 0 < v.re := by
    rw [hvdef, Complex.exp_re, hwim]
    have := Real.cos_pos_of_mem_Ioo (x := Complex.arg u / 2) ⟨by linarith, by linarith⟩
    positivity
  have hvim : 0 < v.im := by
    rw [hvdef, Complex.exp_im, hwim]
    have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg u / 2) (by linarith) (by linarith)
    positivity
  have hvnormsq : ‖v‖ ^ 2 = ‖u‖ := by rw [← hvsq, ← norm_pow]
  have hvnorm : 20 ≤ ‖v‖ := by nlinarith [norm_nonneg v, hvnormsq, hun1]
  have hvnormub : ‖v‖ ≤ Real.sqrt (3*M/2) := by
    have h1 : ‖v‖ ^ 2 ≤ 3*M/2 := by rw [hvnormsq]; exact hun2
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 3*M/2), Real.sqrt_nonneg (3*M/2),
      norm_nonneg v]
  have hvim_le : v.im ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm v)
  have himid : u.im = 2 * v.re * v.im := by
    rw [← hvsq, pow_two, Complex.mul_im]; ring
  have hvnormpos : (0:ℝ) < ‖v‖ := by linarith
  have hvrenn : (0:ℝ) ≤ v.re := hvre.le
  have hvimnn : (0:ℝ) ≤ v.im := hvim.le
  have hprod : M/2 ≤ 2 * v.re * v.im := by rw [← himid]; exact huim
  have hvsqub : ‖v‖ ^ 2 ≤ 3*M/2 := by rw [hvnormsq]; exact hun2
  have hvre6 : ‖v‖ ≤ 6 * v.re := by
    nlinarith [hprod, hvsqub, hvnormpos, hvim_le, hvrenn]
  have hvre_le : v.re ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm v)
  have hvim6 : ‖v‖ ≤ 6 * v.im := by
    nlinarith [hprod, hvsqub, hvnormpos, hvre_le, hvimnn]
  -- the model equation
  have hlogv : Complex.log v = (1/2) * Complex.log u := by
    rw [hvdef]
    exact Complex.log_exp (by rw [hwim]; linarith) (by rw [hwim]; linarith)
  have hkey : v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v) = c := by
    rw [Complex.log_ofReal_mul hsppos hv0, hlogv, hvsq]
    have : T u = u := hufix
    rw [hTdef] at this
    simp only at this
    rw [← hadef]
    linear_combination -this
  have hmodel : (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = 1 := by
    have h1 : Complex.exp (v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v))
        = (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) := by
      rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hv0)]; ring
    rw [← h1, hkey, hcdef]
    have h2 : ((M : ℝ) : ℂ) * Complex.I = (n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hMdef]; push_cast; ring
    rw [h2]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hceq : c = 2 * (Real.pi : ℂ) * Complex.I * n := by
    rw [hcdef, hMdef]; push_cast; ring
  refine ⟨v, hvnorm, hvre6, hvim6, ?_, by rw [hkey, hceq], hmodel⟩
  have h3 : v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n = u - c := by
    rw [hvsq, hcdef, hMdef]; push_cast; ring
  rw [h3]
  have := Metric.mem_closedBall.mp hus
  rw [dist_eq_norm] at this
  rw [hMdef] at this
  linarith [this]

-- no-dlmf: transfer of an exact model root to an exact zero of `cerf`; proof
-- infrastructure for the §7.13 zero asymptotics
/-- **From a model root to a genuine zero of `erf`.**  If `v` solves the model equation
`√π · v · e^{v²} = 1` exactly, with `Re v ≥ 1` and `‖v‖ ≥ 16`, then `cerf` has an honest zero
within distance `12/‖v‖³` of `v`.

This is the quantitative perturbation step of the §7.13 asymptotics.  Writing
`F(z) = √π z e^{z²} erf z`, whose zeros in `Re z > 0` are exactly the zeros of `erf`,
`cerf_scaled_remainder_bound` says `F = Φ − R` with `Φ(z) = √π z e^{z²} − 1` the model
function and `‖R‖ ≤ 4/‖z‖²`.  On the circle `‖z − v‖ = 12/‖v‖³` the model function satisfies
`‖Φ(z)‖ ≥ 18/‖v‖²` (its logarithm `g(z) = z² + log(√π z)` moves by `≈ 2‖v‖·‖z − v‖`), which
beats the remainder, while `‖F(v)‖ = ‖R(v)‖ ≤ 4/‖v‖²` at the centre.  The minimum-modulus
criterion `exists_zero_of_norm_lt_on_sphere` then produces a zero of `F` inside the disc. -/
theorem exists_cerf_zero_near_model {v : ℂ} (hre : 1 ≤ v.re) (hbig : 16 ≤ ‖v‖)
    (hmodel : (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = 1) :
    ∃ w : ℂ, cerf w = 0 ∧ ‖w - v‖ < 12 / ‖v‖ ^ 3 := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hV2 : (256:ℝ) ≤ V ^ 2 := by nlinarith
  have hV3 : (4096:ℝ) ≤ V ^ 3 := by nlinarith
  have hρsmall : ρ ≤ 1/100 := by
    rw [hρdef]
    have h : (12:ℝ) / V ^ 3 ≤ 12 / 4096 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV3
    linarith
  have hA : ρ * V = 12 / V ^ 2 := by rw [hρdef]; field_simp
  have hAsmall : ρ * V ≤ 3/64 := by
    rw [hA]
    have h : (12:ℝ) / V ^ 2 ≤ 12 / 256 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV2
    linarith
  have hρVpos : (0:ℝ) < ρ * V := mul_pos hρ0 hV0
  have h16ρ : 16 * ρ ≤ ρ * V := by nlinarith
  have hρsq : ρ ^ 2 + ρ / 10 ≤ (ρ * V) / 100 := by nlinarith
  -- membership facts
  have hmem : ∀ z ∈ Metric.closedBall v ρ, 0 < z.re ∧ V - ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + ρ := by
    intro z hz
    have hzv : ‖z - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre' : |z.re - v.re| ≤ ρ := by
      have h := Complex.abs_re_le_norm (z - v)
      simp only [Complex.sub_re] at h
      linarith
    have h1 := abs_le.mp hre'
    refine ⟨by linarith, ?_, ?_⟩
    · have h2 := norm_sub_norm_le v z
      rw [norm_sub_rev v z] at h2
      linarith
    · have h2 := norm_sub_norm_le z v
      linarith
  have hVρ : (10:ℝ) ≤ V - ρ := by linarith
  -- mean value bound for the logarithm term
  have hlogmvt : ∀ z ∈ Metric.closedBall v ρ,
      ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z) - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖
        ≤ (1 / (V - ρ)) * ‖z - v‖ := by
    intro z hz
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
      (convex_closedBall v ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hz
    · intro y hy
      obtain ⟨hy1, hy2, -⟩ := hmem y hy
      have hslit : ((Real.sqrt Real.pi : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
          ((Real.sqrt Real.pi : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt Real.pi : ℂ))
      exact h1.clog hslit
    · intro y hy
      obtain ⟨hy1, hy2, -⟩ := hmem y hy
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hsppos]
  -- the model equation in exponential form
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        = (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hz0)]; ring
  have hvre : 0 < v.re := by linarith
  have hgv : Complex.exp (v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v)) = 1 := by
    rw [hexpg v hvre]; exact hmodel
  -- the sphere estimate
  have hsphere : ∀ z ∈ Metric.sphere v ρ,
      ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * cerf v‖
        < ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z‖ := by
    intro z hz
    have hzv : ‖z - v‖ = ρ := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have hzcb : z ∈ Metric.closedBall v ρ := Metric.sphere_subset_closedBall hz
    obtain ⟨hzre, hzn1, hzn2⟩ := hmem z hzcb
    have hzge : 0.9 * V ≤ ‖z‖ := by linarith
    have hzpos : (0:ℝ) < ‖z‖ := by linarith
    have hz4 : 4 / ‖z‖ ^ 2 ≤ (5/12) * (ρ * V) := by
      rw [hA, show (5:ℝ)/12 * (12 / V ^ 2) = 5 / V ^ 2 by ring,
        div_le_div_iff₀ (pow_pos hzpos 2) (pow_pos hV0 2)]
      nlinarith [hzge, hV0]
    set d : ℂ := (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      - (v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v)) with hd
    have hdsplit : d = (z - v) * (z + v)
        + (Complex.log ((Real.sqrt Real.pi : ℂ) * z)
            - Complex.log ((Real.sqrt Real.pi : ℂ) * v)) := by rw [hd]; ring
    have hlog := hlogmvt z hzcb
    rw [hzv] at hlog
    have hlog' : (1 / (V - ρ)) * ρ ≤ ρ / 10 := by
      rw [div_mul_eq_mul_div, one_mul]
      apply div_le_div_of_nonneg_left hρ0.le (by norm_num) hVρ
    have h2v : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    have hzpv : 2 * V - ρ ≤ ‖z + v‖ := by
      have h1 : ‖(2:ℂ) * v‖ ≤ ‖z + v‖ + ‖z - v‖ := by
        calc ‖(2:ℂ) * v‖ = ‖(z + v) - (z - v)‖ := by congr 1; ring
          _ ≤ ‖z + v‖ + ‖z - v‖ := norm_sub_le _ _
      rw [h2v, hzv] at h1; linarith only [h1]
    have hzpv' : ‖z + v‖ ≤ 2 * V + ρ := by
      have h1 := norm_add_le z v; linarith only [h1, hzn2, hVdef.ge, hVdef.le]
    have hprodnorm : ‖(z - v) * (z + v)‖ = ρ * ‖z + v‖ := by rw [norm_mul, hzv]
    have hdlow : 1.99 * (ρ * V) ≤ ‖d‖ := by
      have h1 : ‖(z - v) * (z + v)‖
          - ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ ≤ ‖d‖ := by
        have h0 : ‖(z - v) * (z + v)‖ ≤ ‖d‖
            + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ := by
          calc ‖(z - v) * (z + v)‖
              = ‖d - (Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                  - Complex.log ((Real.sqrt Real.pi : ℂ) * v))‖ := by
                congr 1; rw [hdsplit]; ring
            _ ≤ ‖d‖ + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                  - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ := norm_sub_le _ _
        linarith only [h0]
      rw [hprodnorm] at h1
      have hmul : ρ * (2 * V - ρ) ≤ ρ * ‖z + v‖ := mul_le_mul_of_nonneg_left hzpv hρ0.le
      linarith only [h1, hmul, hlog, hlog', hρsq]
    have hdhigh : ‖d‖ ≤ 2.01 * (ρ * V) := by
      have h1 : ‖d‖ ≤ ‖(z - v) * (z + v)‖
          + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ := by
        rw [hdsplit]; exact norm_add_le _ _
      rw [hprodnorm] at h1
      have hmul : ρ * ‖z + v‖ ≤ ρ * (2 * V + ρ) := mul_le_mul_of_nonneg_left hzpv' hρ0.le
      linarith only [h1, hmul, hlog, hlog', hρsq]
    have hdle1 : ‖d‖ ≤ 1/10 := by linarith only [hdhigh, hAsmall]
    -- lower bound on the model function on the sphere
    have hmodelow : (3/2 : ℝ) * (ρ * V)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1‖ := by
      have hEq : (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1 = Complex.exp d - 1 := by
        rw [← hexpg z hzre, hd, Complex.exp_sub, hgv, div_one]
      rw [hEq]
      have hb := Complex.norm_exp_sub_one_sub_id_le (x := d) (by linarith only [hdle1])
      have hkey : ‖d‖ - ‖d‖ ^ 2 ≤ ‖Complex.exp d - 1‖ := by
        have h5 := norm_sub_norm_le d (Complex.exp d - 1)
        rw [norm_sub_rev d (Complex.exp d - 1)] at h5
        have h6 : (Complex.exp d - 1) - d = Complex.exp d - 1 - d := by ring
        rw [h6] at h5
        linarith only [h5, hb]
      have h7 : ‖d‖ ^ 2 ≤ ‖d‖ / 10 := by
        calc ‖d‖ ^ 2 = ‖d‖ * ‖d‖ := by ring
          _ ≤ ‖d‖ * (1 / 10) := mul_le_mul_of_nonneg_left hdle1 (norm_nonneg d)
          _ = ‖d‖ / 10 := by ring
      have h9 : (3/2 : ℝ) * (ρ * V) ≤ (9/10) * ‖d‖ := by linarith only [hdlow, hρVpos]
      linarith only [hkey, h7, h9]
    -- remainder bounds
    have hrz := cerf_scaled_remainder_bound hzre
    have hrv := cerf_scaled_remainder_bound hvre
    have hfv : ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * cerf v‖
        ≤ (1/3 : ℝ) * (ρ * V) := by
      rw [← hVdef] at hrv
      rw [hA, show (1:ℝ)/3 * (12 / V ^ 2) = 4 / V ^ 2 by ring]
      rw [hmodel] at hrv ⊢
      simpa using hrv
    have hfz : (13/12 : ℝ) * (ρ * V)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z‖ := by
      have h1 := norm_sub_norm_le ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1)
        ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z)
      have h2 := norm_sub_rev ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1)
        ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z)
      rw [h2] at h1
      linarith only [h1, hmodelow, hrz, hz4]
    linarith only [hfv, hfz, hρVpos]
  obtain ⟨w, hw, hfw⟩ := exists_zero_of_norm_lt_on_sphere
    (f := fun z : ℂ => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z)
    (by
      apply Differentiable.mul _ differentiable_cerf
      exact (differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2)))
    hρ0 hsphere
  have hwb : ‖w - v‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
  obtain ⟨hwre, -, -⟩ := hmem w (Metric.ball_subset_closedBall hw)
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
  refine ⟨w, ?_, hwb⟩
  have := hfw
  simp only [mul_eq_zero] at this
  rcases this with (h | h) | h
  · rcases h with h | h
    · exact absurd h hsp0
    · exact absurd h hw0
  · exact absurd h (Complex.exp_ne_zero _)
  · exact h

-- no-dlmf: existence of a first-quadrant zero of `cerf` attached to each large index `n`;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **Existence of the `n`-th first-quadrant zero of `erf`.**  For every `n ≥ 134` there is an
exact root `v` of the model equation `√π v e^{v²} = 1` with `‖v² − 2πi n‖ ≤ πn`, and an exact
zero `w` of `erf` in the open first quadrant with

`‖w − v‖ < 12/‖v‖³`.

Since `‖v‖ ≍ √(2πn) ≍ λₙ√2`, this places a zero of `erf` within `O(λₙ⁻³)` of the `n`-th model
root — the existence half of DLMF 7.13.1.  (The remaining half is the identification of `v`'s
real and imaginary parts with `erfZeroReApprox n`, `erfZeroImApprox n`, together with the
count that no other zeros occur.) -/
theorem exists_cerf_zero_near_model_root (n : ℕ) (hn : 134 ≤ n) :
    ∃ v w : ℂ, (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = 1 ∧
      ‖v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ Real.pi * n ∧
      cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w - v‖ < 12 / ‖v‖ ^ 3 := by
  obtain ⟨v, hvn, hvre, hvim, hvloc, -, hvmodel⟩ := exists_model_root n hn
  have hre1 : (1:ℝ) ≤ v.re := by linarith
  obtain ⟨w, hw, hwb⟩ := exists_cerf_zero_near_model hre1 (by linarith) hvmodel
  have hv3 : (4096:ℝ) ≤ ‖v‖ ^ 3 := by
    nlinarith [hvn, norm_nonneg v, sq_nonneg (‖v‖ - 16), sq_nonneg ‖v‖]
  have hsmall : (12:ℝ) / ‖v‖ ^ 3 ≤ 12 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv3
  have hrew : |w.re - v.re| ≤ ‖w - v‖ := by
    have h := Complex.abs_re_le_norm (w - v)
    simpa only [Complex.sub_re] using h
  have himw : |w.im - v.im| ≤ ‖w - v‖ := by
    have h := Complex.abs_im_le_norm (w - v)
    simpa only [Complex.sub_im] using h
  have h1 := abs_le.mp hrew
  have h2 := abs_le.mp himw
  refine ⟨v, w, hvmodel, hvloc, hw, ?_, ?_, hwb⟩
  · linarith [h1.1]
  · have : (1:ℝ) ≤ v.im := by linarith
    linarith [h2.1]

-- no-dlmf: local uniqueness (separation) of the zeros of `cerf` in the first-quadrant
-- sector; proof infrastructure for the §7.13 zero asymptotics
/-- **Local uniqueness of the zeros of `erf`.**  In the sector `‖v‖ ≤ 6 Re v` with `‖v‖ ≥ 20`,
`erf` has at most one zero in the disc of radius `1/(24‖v‖)` about `v`.  Equivalently: distinct
zeros of `erf` at distance `‖v‖` from the origin in that sector are at least `1/(12‖v‖)` apart —
the `Θ(λ⁻¹)` separation of DLMF 7.13.1's zero family.

The proof compares the two decompositions of `F(z) = √π z e^{z²} erf z = Φ(z) − R(z)` at the two
zeros.  At a zero `Φ = −R`, so `Φ(w) − Φ(w') = −(R(w) − R(w'))`.  The left-hand side is bounded
*below* by `1.56‖v‖·‖w − w'‖`: writing `Φ = e^{g} − 1` with `g(z) = z² + log(√π z)`, one has
`Φ(w) − Φ(w') = √π w' e^{w'²}(e^{g(w) − g(w')} − 1)` where `g(w) − g(w')` moves by `≈ 2‖v‖`
per unit of `‖w − w'‖`.  The right-hand side is bounded *above* by `(120/‖v‖³)·‖w − w'‖` by the
Cauchy estimate (`Complex.norm_deriv_le_div_of_mapsTo_ball` on the disc of radius `‖v‖/12`,
where `‖R‖ ≤ 5/‖v‖²`).  For `‖v‖ ≥ 20` the first beats the second, forcing `w = w'`.

Note the model equation plays no role here: the statement is a separation result for the zeros
of `erf` themselves. -/
theorem cerf_zero_unique_in_small_ball {v w w' : ℂ} (hre : ‖v‖ ≤ 6 * v.re) (hbig : 20 ≤ ‖v‖)
    (hw : cerf w = 0) (hw' : cerf w' = 0)
    (hwb : ‖w - v‖ ≤ 1 / (24 * ‖v‖)) (hwb' : ‖w' - v‖ ≤ 1 / (24 * ‖v‖)) : w = w' := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  have hV2 : (400:ℝ) ≤ V ^ 2 := by nlinarith
  have hV3 : (8000:ℝ) ≤ V ^ 3 := by nlinarith [sq_nonneg V]
  set ρ : ℝ := 1 / (24 * V) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact div_pos (by norm_num) (by linarith)
  have hρsmall : ρ ≤ 1/100 := by
    rw [hρdef]
    have h : (1:ℝ) / (24 * V) ≤ 1 / 480 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hvre : V / 6 ≤ v.re := by linarith
  -- the remainder function
  set Rem : ℂ → ℂ := fun z => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * cerf z
    - ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1) with hRemdef
  have hRdiff : Differentiable ℂ Rem := by
    rw [hRemdef]
    have h0 : Differentiable ℂ (fun z : ℂ => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)) :=
      (differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2))
    exact (h0.mul differentiable_cerf).sub (h0.sub_const 1)
  have hRbound : ∀ z : ℂ, 0 < z.re → ‖Rem z‖ ≤ 4 / ‖z‖ ^ 2 := by
    intro z hz
    rw [hRemdef]
    exact cerf_scaled_remainder_bound hz
  -- geometry of the small ball
  have hgeo : ∀ z : ℂ, ‖z - v‖ ≤ ρ → V / 6 - ρ ≤ z.re ∧ V - ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + ρ := by
    intro z hz
    have h := Complex.abs_re_le_norm (z - v)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hz)
    have h2 := norm_sub_norm_le v z
    rw [norm_sub_rev v z] at h2
    have h3 := norm_sub_norm_le z v
    exact ⟨by linarith [h1.1], by linarith, by linarith⟩
  -- Cauchy estimate for the derivative of the remainder
  have hderiv : ∀ z₀ : ℂ, ‖z₀ - v‖ ≤ ρ → ‖deriv Rem z₀‖ ≤ 120 / V ^ 3 := by
    intro z₀ hz₀
    have hbig' : ∀ z ∈ Metric.ball z₀ (V/12), 0 < z.re ∧ (9/10) * V ≤ ‖z‖ := by
      intro z hz
      have hd : ‖z - z₀‖ < V/12 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hdv : ‖z - v‖ ≤ ρ + V/12 := by
        have := norm_add_le (z - z₀) (z₀ - v)
        have he : (z - z₀) + (z₀ - v) = z - v := by ring
        rw [he] at this
        linarith
      have h := Complex.abs_re_le_norm (z - v)
      simp only [Complex.sub_re] at h
      have h1 := abs_le.mp (le_trans h hdv)
      have h2 := norm_sub_norm_le v z
      rw [norm_sub_rev v z] at h2
      constructor
      · linarith [h1.1]
      · linarith
    have hmaps : Set.MapsTo Rem (Metric.ball z₀ (V/12)) (Metric.closedBall (Rem z₀) (10/V^2)) := by
      intro z hz
      obtain ⟨hzre, hzn⟩ := hbig' z hz
      have hz0re : 0 < z₀.re := by
        obtain ⟨h1, -, -⟩ := hgeo z₀ hz₀; linarith
      have hz0n : (9/10) * V ≤ ‖z₀‖ := by
        obtain ⟨-, h2, -⟩ := hgeo z₀ hz₀; linarith
      have b1 : ‖Rem z‖ ≤ 5 / V ^ 2 := by
        refine le_trans (hRbound z hzre) ?_
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith [hzn, hV0]
      have b2 : ‖Rem z₀‖ ≤ 5 / V ^ 2 := by
        refine le_trans (hRbound z₀ hz0re) ?_
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith [hz0n, hV0]
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := norm_sub_le (Rem z) (Rem z₀)
      have he : (10:ℝ)/V^2 = 5/V^2 + 5/V^2 := by ring
      rw [he]; linarith
    have h := Complex.norm_deriv_le_div_of_mapsTo_ball (f := Rem) (c := z₀)
      (R₁ := V/12) (R₂ := 10/V^2) hRdiff.differentiableOn hmaps (by linarith)
    refine le_trans h (le_of_eq ?_)
    field_simp
    ring
  -- the two zeros
  obtain ⟨hwre0, hwn1, hwn2⟩ := hgeo w hwb
  obtain ⟨hw're0, hw'n1, hw'n2⟩ := hgeo w' hwb'
  have hwre : 0 < w.re := by linarith
  have hw're : 0 < w'.re := by linarith
  have hmemw : w ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwb
  have hmemw' : w' ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwb'
  have hww' : ‖w - w'‖ ≤ 2 * ρ := by
    have h := norm_sub_le (w - v) (w' - v)
    have he : (w - v) - (w' - v) = w - w' := by ring
    rw [he] at h; linarith
  -- Lipschitz bound on the remainder from the Cauchy estimate
  have hRlip : ‖Rem w - Rem w'‖ ≤ (120 / V ^ 3) * ‖w - w'‖ :=
    norm_sub_le_of_hasDerivAt_le (f := Rem) (f' := deriv Rem) (convex_closedBall v ρ)
      (fun z _ => (hRdiff z).hasDerivAt)
      (fun z hz => hderiv z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
      hmemw' hmemw
  -- the logarithmic model function
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        = (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hz0)]; ring
  have hΦ : ∀ z : ℂ, cerf z = 0 →
      (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - 1 = - Rem z := by
    intro z hz
    rw [hRemdef]; simp only; rw [hz]; ring
  clear_value Rem
  have hRw' : ‖Rem w'‖ ≤ 5 / V ^ 2 := by
    refine le_trans (hRbound w' hw're) ?_
    have hw'pos : (0:ℝ) < ‖w'‖ := by linarith
    rw [div_le_div_iff₀ (pow_pos hw'pos 2) (pow_pos hV0 2)]
    nlinarith [hw'n1, hV0, hρsmall]
  have hexpw' : (98/100 : ℝ) ≤ ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ := by
    have h1 : (Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2) = 1 - Rem w' := by
      have := hΦ w' hw'; linear_combination this
    rw [h1]
    have h2 := norm_sub_norm_le (1 : ℂ) (Rem w')
    have h3 : ‖(1:ℂ)‖ = 1 := norm_one
    have h4 : (5:ℝ) / V ^ 2 ≤ 5 / 400 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV2
    rw [h3] at h2
    linarith
  -- two-sided bound on the logarithmic increment
  set δ : ℂ := (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w))
    - (w' ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w')) with hδdef
  have hlogmvt : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ ≤ (1 / (V - ρ)) * ‖w - w'‖ := by
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
      (convex_closedBall v ρ) ?_ ?_ hmemw' hmemw
    · intro y hy
      have hyb : ‖y - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      obtain ⟨hy1, hy2, -⟩ := hgeo y hyb
      have hy1' : 0 < y.re := by linarith
      have hslit : ((Real.sqrt Real.pi : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
          ((Real.sqrt Real.pi : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt Real.pi : ℂ))
      exact h1.clog hslit
    · intro y hy
      have hyb : ‖y - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      obtain ⟨-, hy2, -⟩ := hgeo y hyb
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hsppos]
  have hlogsmall : (1 / (V - ρ)) * ‖w - w'‖ ≤ (1/10) * ‖w - w'‖ := by
    have h1 : (1:ℝ) / (V - ρ) ≤ 1/10 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hsum1 : ‖w + w'‖ ≤ 2 * V + 2 * ρ := by
    have h1 : ‖w + w'‖ ≤ ‖w - v‖ + ‖w' - v‖ + ‖(2:ℂ) * v‖ := by
      calc ‖w + w'‖ = ‖(w - v) + (w' - v) + 2 * v‖ := by congr 1; ring
        _ ≤ ‖(w - v) + (w' - v)‖ + ‖(2:ℂ) * v‖ := norm_add_le _ _
        _ ≤ ‖w - v‖ + ‖w' - v‖ + ‖(2:ℂ) * v‖ := by linarith [norm_add_le (w - v) (w' - v)]
    have h2 : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    rw [h2] at h1; linarith
  have hsum2 : 2 * V - 2 * ρ ≤ ‖w + w'‖ := by
    have h2 : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    have h1 : ‖(2:ℂ) * v‖ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by
      calc ‖(2:ℂ) * v‖ = ‖(w + w') - ((w - v) + (w' - v))‖ := by congr 1; ring
        _ ≤ ‖w + w'‖ + ‖(w - v) + (w' - v)‖ := norm_sub_le _ _
        _ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by linarith [norm_add_le (w - v) (w' - v)]
    rw [h2] at h1; linarith
  have hδsplit : δ = (w - w') * (w + w')
      + (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
        - Complex.log ((Real.sqrt Real.pi : ℂ) * w')) := by rw [hδdef]; ring
  have hprodn : ‖(w - w') * (w + w')‖ = ‖w - w'‖ * ‖w + w'‖ := norm_mul _ _
  clear_value δ
  have hδlow : (199/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖δ‖ := by
    have h0 : ‖(w - w') * (w + w')‖ ≤ ‖δ‖
        + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := by
      calc ‖(w - w') * (w + w')‖
          = ‖δ - (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * w'))‖ := by
            congr 1; rw [hδsplit]; ring
        _ ≤ ‖δ‖ + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := norm_sub_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * (2 * V - 2 * ρ) ≤ ‖w - w'‖ * ‖w + w'‖ :=
      mul_le_mul_of_nonneg_left hsum2 (norm_nonneg _)
    have hslack0 : 2 * ρ + 1/10 ≤ V/100 := by linarith
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδhigh : ‖δ‖ ≤ (201/100 : ℝ) * (V * ‖w - w'‖) := by
    have h0 : ‖δ‖ ≤ ‖(w - w') * (w + w')‖
        + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := by
      rw [hδsplit]; exact norm_add_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * ‖w + w'‖ ≤ ‖w - w'‖ * (2 * V + 2 * ρ) :=
      mul_le_mul_of_nonneg_left hsum1 (norm_nonneg _)
    have hslack0 : 2 * ρ + 1/10 ≤ V/100 := by linarith
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδle : ‖δ‖ ≤ 1/5 := by
    have h1 : V * ‖w - w'‖ ≤ V * (2 * ρ) := mul_le_mul_of_nonneg_left hww' (by linarith)
    have h2 : V * (2 * ρ) = 1 / 12 := by rw [hρdef]; field_simp; ring
    rw [h2] at h1
    linarith
  clear_value ρ V
  -- lower bound on ‖exp δ - 1‖
  have hexpδ : (8/10 : ℝ) * ‖δ‖ ≤ ‖Complex.exp δ - 1‖ := by
    have hb := Complex.norm_exp_sub_one_sub_id_le (x := δ) (by linarith)
    have h5 := norm_sub_norm_le δ (Complex.exp δ - 1)
    rw [norm_sub_rev δ (Complex.exp δ - 1)] at h5
    have h6 : (Complex.exp δ - 1) - δ = Complex.exp δ - 1 - δ := by ring
    rw [h6] at h5
    have h7 : ‖δ‖ ^ 2 ≤ (1/5) * ‖δ‖ := by
      calc ‖δ‖ ^ 2 = ‖δ‖ * ‖δ‖ := by ring
        _ ≤ ‖δ‖ * (1/5) := mul_le_mul_of_nonneg_left hδle (norm_nonneg _)
        _ = (1/5) * ‖δ‖ := by ring
    linarith
  -- assemble
  have hkey : Rem w - Rem w'
      = -((Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2) * (Complex.exp δ - 1)) := by
    have e1 : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2)
        = (Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2) * Complex.exp δ := by
      rw [← hexpg w hwre, ← hexpg w' hw're, ← Complex.exp_add]
      congr 1
      rw [hδdef]; ring
    have e2 := hΦ w hw
    have e3 := hΦ w' hw'
    linear_combination e2 - e3 - e1
  have hlow : ‖Rem w - Rem w'‖
      = ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ := by
    rw [hkey, norm_neg, norm_mul]
  have hVX : (0:ℝ) ≤ V * ‖w - w'‖ := by positivity
  have hchain : (156/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖Rem w - Rem w'‖ := by
    rw [hlow]
    have h1 : (98/100 : ℝ) * ((8/10) * ‖δ‖)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ :=
      mul_le_mul hexpw' hexpδ (by positivity) (norm_nonneg _)
    linarith only [hδlow, h1, hVX]
  -- conclude
  by_contra hne
  have hpos : 0 < ‖w - w'‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  have hcomb : (156/100 : ℝ) * V * ‖w - w'‖ ≤ (120 / V ^ 3) * ‖w - w'‖ := by
    linarith only [hchain, hRlip]
  have hfin : (156/100 : ℝ) * V ≤ 120 / V ^ 3 :=
    le_of_mul_le_mul_right (by linarith only [hcomb]) hpos
  have h120 : (120:ℝ) / V ^ 3 ≤ 120 / 8000 := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < V ^ 3) (by norm_num : (0:ℝ) < 8000)]
    linarith only [hV3]
  linarith only [hfin, h120, hbig]

-- no-dlmf: existence and local uniqueness of the `n`-th first-quadrant zero of `cerf`;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **The `n`-th first-quadrant zero of `erf`, existence and local uniqueness.**  For every
`n ≥ 134` there is an exact root `v` of the model equation `√π v e^{v²} = 1` with
`v² + log (√π v) = 2πi n` and `‖v² − 2πi n‖ ≤ πn` (so `‖v‖ ≍ √(2πn) ≍ λₙ√2`), such that `erf`
has *exactly one* zero in the closed disc of radius `1/(24‖v‖)` about `v`.

This combines `exists_cerf_zero_near_model` (which places the zero within `12/‖v‖³ ≪ 1/(24‖v‖)`
of `v`) with the separation result `cerf_zero_unique_in_small_ball`.  It is the
existence-and-local-uniqueness half of DLMF 7.13.1: what remains for the full display is the
sharpening of `v` against `erfZeroReApprox`/`erfZeroImApprox` and the global count that the
`vₙ` exhaust the first-quadrant zeros. -/
theorem existsUnique_cerf_zero_near_model_root (n : ℕ) (hn : 134 ≤ n) :
    ∃ v : ℂ, (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = 1 ∧
      v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v)
        = 2 * (Real.pi : ℂ) * Complex.I * n ∧
      ‖v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ Real.pi * n ∧
      ∃! w : ℂ, cerf w = 0 ∧ ‖w - v‖ ≤ 1 / (24 * ‖v‖) := by
  obtain ⟨v, hvn, hvre, hvim, hvloc, hvlog, hvmodel⟩ := exists_model_root n hn
  have hV0 : (0:ℝ) < ‖v‖ := by linarith
  have hre1 : (1:ℝ) ≤ v.re := by linarith
  obtain ⟨w, hw, hwb⟩ := exists_cerf_zero_near_model hre1 (by linarith) hvmodel
  have hcmp : (12:ℝ) / ‖v‖ ^ 3 ≤ 1 / (24 * ‖v‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (400:ℝ) ≤ ‖v‖ ^ 2 := by nlinarith
    have h2 : ‖v‖ * 400 ≤ ‖v‖ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hV0.le
    nlinarith [h2, hV0]
  refine ⟨v, hvmodel, hvlog, hvloc, w, ⟨hw, by linarith⟩, ?_⟩
  rintro y ⟨hy, hyb⟩
  exact cerf_zero_unique_in_small_ball hvre hvn hy hw hyb (by linarith)

/-! ## erf zeros — the third-order inversion (DLMF 7.13.1)

The results above localize a zero of `erf` to `O(λ⁻¹)`; the display 7.13.1 asks for `o(λ⁻³)`.
Two extra ingredients are needed and are supplied here.

* `cerf_zero_equation_third` / `cerf_zero_log_equation_third` push the effective zero equation
  one Poincaré order further, to `w² + log(√π w) + 1/(2w²) = 2πi·k + O(‖w‖⁻⁴)`.  The extra
  term `1/(2w²)` is *not* cosmetic: the exact roots of the model equation `√π w e^{w²} = 1`
  (`exists_model_root`) differ from DLMF's approximation by exactly `1/(16λ³)` in each
  coordinate, and this term is what restores it.
* `erf713_zero_expansion` inverts that transcendental equation to third order, by an explicit
  four-step iteration on its real and imaginary components in the variables `s = x + y`,
  `d = x − y` (`erf713_crude`, `erf713_first_order`, `erf713_diff_expansion`,
  `erf713_sum_expansion`).  The effective error is `(μ + 3)⁴/(20 λ⁵) = O(log⁴ n · n^{-5/2})`,
  comfortably `o(λ⁻³)`.

What is *not* done here is the identification of the integer `k` of
`cerf_zero_log_equation_third` with the DLMF index `n` of a strictly ordered enumeration of the
zeros; that counting step is the remaining gap to `erf_7_13_1` itself.
-/


-- no-dlmf: cubic error bound for the linearization of `arctan`; proof infrastructure for
-- the §7.13 zero asymptotics
/-- **Cubic error bound for `arctan`.**  `|arctan t − t| ≤ |t|³`.

The mean value inequality for `g(t) = arctan t − t`, whose derivative `−t²/(1+t²)` is bounded
by `T²` on `[−T, T]`.  This is the third-order input that turns the *index* equation
`2xy + ph w = 2πn` into the `λ⁻³` term of DLMF 7.13.1. -/
theorem abs_arctan_sub_self_le (t : ℝ) : |Real.arctan t - t| ≤ |t| ^ 3 := by
  have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) t,
      HasDerivWithinAt (fun r : ℝ => Real.arctan r - r) (1 / (1 + r ^ 2) - 1)
        (Set.uIcc (0:ℝ) t) r := by
    intro r _
    exact ((Real.hasDerivAt_arctan r).sub (hasDerivAt_id r)).hasDerivWithinAt
  have hbound : ∀ r ∈ Set.uIcc (0:ℝ) t, ‖1 / (1 + r ^ 2) - 1‖ ≤ t ^ 2 := by
    intro r hr
    have h1 : (0:ℝ) < 1 + r ^ 2 := by positivity
    have hid : 1 / (1 + r ^ 2) - 1 = -(r ^ 2 / (1 + r ^ 2)) := by field_simp; ring
    rw [hid, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hrt : r ^ 2 ≤ t ^ 2 := by
      rcases le_total 0 t with h | h
      · rw [Set.uIcc_of_le h] at hr
        nlinarith [hr.1, hr.2]
      · rw [Set.uIcc_of_ge h] at hr
        nlinarith [hr.1, hr.2]
    calc r ^ 2 / (1 + r ^ 2) ≤ r ^ 2 := by
          rw [div_le_iff₀ h1]; nlinarith [sq_nonneg r]
      _ ≤ t ^ 2 := hrt
  have h := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simp only [Real.arctan_zero, sub_zero, sub_self, Real.norm_eq_abs] at h
  calc |Real.arctan t - t| ≤ t ^ 2 * |t| := h
    _ = |t| ^ 3 := by rw [← sq_abs]; ring

-- no-dlmf: the first-quadrant phase in the `x ± y` variables; proof infrastructure for the
-- §7.13 zero asymptotics
/-- **The phase of a first-quadrant point in the `s = x+y`, `d = x−y` variables.**
For `w = x + iy` with `x, y > 0`,

`ph w = π/4 − arctan ((x − y)/(x + y))`.

This is the exact form of "`ph w ≈ π/4`" behind the `−1/8` of DLMF 7.13.2: it converts the
imaginary part of the zero equation into a closed equation for `s` and `d`. -/
theorem arg_eq_pi_div_four_sub_arctan {w : ℂ} (hx : 0 < w.re) (hy : 0 < w.im) :
    Complex.arg w = Real.pi / 4 - Real.arctan ((w.re - w.im) / (w.re + w.im)) := by
  have hs : 0 < w.re + w.im := by linarith
  have harg : Complex.arg w = Real.arctan (w.im / w.re) := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)
    have h2 := abs_lt.mp h
    rw [← Complex.tan_arg w, Real.arctan_tan h2.1 h2.2]
  have hprod : (w.im / w.re) * ((w.re - w.im) / (w.re + w.im)) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity)]
    nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hadd := Real.arctan_add hprod
  have hone : (w.im / w.re + (w.re - w.im) / (w.re + w.im))
      / (1 - (w.im / w.re) * ((w.re - w.im) / (w.re + w.im))) = 1 := by
    rw [div_eq_one_iff_eq]
    · field_simp; ring
    · rw [sub_ne_zero]
      intro h
      rw [h] at hprod
      linarith
  rw [hone, Real.arctan_one] at hadd
  rw [harg]
  linarith

-- no-dlmf: elementary size bounds for the DLMF 7.13.2 parameter `μ = log (λ√(2π))`; proof
-- infrastructure for the §7.13 zero asymptotics
/-- **Size of the parameter `μ` of DLMF 7.13.2.**  For `λ ≥ 100`, `μ = log (λ√(2π))` satisfies
`5 ≤ μ` and `μ + 3 ≤ λ`.  The upper bound (logarithm beats the square root) is what lets every
`μ`-polynomial error term be absorbed into a power of `λ`. -/
theorem erf713_mu_bounds {lam mu : ℝ} (hlam : 100 ≤ lam)
    (hmu : mu = Real.log (lam * Real.sqrt (2 * Real.pi))) :
    5 ≤ mu ∧ mu + 3 ≤ lam := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hsnn : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hlb : (2:ℝ) ≤ Real.sqrt (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have hub : Real.sqrt (2 * Real.pi) ≤ 2.83 := by nlinarith [Real.pi_lt_four]
  have hpos : (0:ℝ) < lam * Real.sqrt (2 * Real.pi) := by nlinarith
  constructor
  · rw [hmu]
    have h200 : (200:ℝ) ≤ lam * Real.sqrt (2 * Real.pi) := by nlinarith
    have hexp : Real.exp 5 ≤ 200 := by
      have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      have h2 : Real.exp 5 = Real.exp 1 ^ (5:ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have h3 : Real.exp 1 ^ (5:ℕ) ≤ (2.7182818286:ℝ) ^ (5:ℕ) := by gcongr
      refine h3.trans ?_
      norm_num
    rw [Real.le_log_iff_exp_le hpos]
    linarith
  · have hsl : Real.sqrt lam ≤ lam / 10 := by
      rw [show lam / 10 = Real.sqrt ((lam / 10) ^ 2) by
        rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hslnn : (0:ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hu4 : lam * Real.sqrt (2 * Real.pi) ≤ 4 * lam := by nlinarith
    have hsu : Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ 2 * Real.sqrt lam := by
      have h1 : Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ Real.sqrt (4 * lam) :=
        Real.sqrt_le_sqrt hu4
      have h2 : Real.sqrt (4 * lam) = 2 * Real.sqrt lam := by
        rw [show (4:ℝ) * lam = 2 ^ 2 * lam by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      linarith [h1, h2.le, h2.ge]
    have hlogsqrt : Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
        ≤ Real.sqrt (lam * Real.sqrt (2 * Real.pi)) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
    have hhalf : Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
        = Real.log (lam * Real.sqrt (2 * Real.pi)) / 2 :=
      Real.log_sqrt hpos.le
    rw [hmu]
    linarith [hsl, hsu, hlogsqrt, hhalf]

set_option maxHeartbeats 1000000 in
-- no-dlmf: crude localization of a solution of the real form of the §7.13 zero equation;
-- proof infrastructure, not a numbered DLMF display
/-- **Crude localization.**  If the real pair `(s, d) = (x+y, x−y)` of a first-quadrant point
satisfies the two real components of the third-order zero equation — `key1` (real part) and
`key2` (imaginary part) — with index parameter `λ ≥ 100`, then

`s = 2λ + O(1)`, `N = x² + y² = 2λ² + O(1)`, `|d| ≤ 2`, `|L − μ| ≤ 2/λ²`,

together with the two-sided logarithmic sandwich relating `L = ½ log (πN)` to `μ`.
This is the zeroth iteration of the inversion of the transcendental system; the sandwich is
kept because the refined steps need it at full strength. -/
theorem erf713_crude {lam mu s d N L A : ℝ}
    (hlam : 100 ≤ lam) (hmu : 2 * mu = Real.log (2 * Real.pi * lam ^ 2))
    (hL : L = (1 / 2) * Real.log (Real.pi * N))
    (hs : 0 < s) (hd2s : d ^ 2 ≤ s ^ 2) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hQ : N < s ^ 2)
    (hAbd : |A| ≤ 2)
    (key1 : |d * s + L + d * s / (2 * N ^ 2)| ≤ 40 / lam ^ 4)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - (s ^ 2 - N) / N ^ 2 - 4 * lam ^ 2| ≤ 80 / lam ^ 4) :
    2 * lam - 1 ≤ s ∧ s ^ 2 ≤ 4 * lam ^ 2 + 10 ∧ 2 * lam ^ 2 - 3 ≤ N ∧ N ≤ 2 * lam ^ 2 + 7
      ∧ |d| ≤ 2 ∧ |L - mu| ≤ 2 / lam ^ 2
      ∧ 2 * (L - mu) ≤ (N - 2 * lam ^ 2) / (2 * lam ^ 2)
      ∧ -(2 * (L - mu)) ≤ (2 * lam ^ 2 - N) / N := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hlam4 : (100000000:ℝ) ≤ lam ^ 4 := by nlinarith
  have heps1 : 40 / lam ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have heps2 : 80 / lam ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hN0 : (0:ℝ) < N := by nlinarith
  have hk1 := abs_le.mp key1
  have hk2 := abs_le.mp key2
  have hAb := abs_le.mp hAbd
  have hQpos : 0 ≤ (s ^ 2 - N) / N ^ 2 := div_nonneg (by linarith) (by positivity)
  have hs2lb : 4 * lam ^ 2 - 5 ≤ s ^ 2 := by
    linarith only [hk2.1, sq_nonneg d, hQpos, heps2, hAb.1, hAb.2]
  have hslb : 2 * lam - 1 ≤ s := by nlinarith [hs2lb, hs, hlam]
  have hNlb : 2 * lam ^ 2 - 3 ≤ N := by linarith only [hNsd, hs2lb, sq_nonneg d]
  have hN1 : (1:ℝ) ≤ N := by linarith only [hNlb, hlam2]
  have hQub : (s ^ 2 - N) / N ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hNsd, hd2s, hN1]
  have hLpos : 0 < L := by
    have h1 : (1:ℝ) < Real.pi * N := by nlinarith [Real.pi_gt_three, hN1]
    have h2 := Real.log_pos h1
    rw [hL]; linarith only [h2]
  have hLub0 : L ≤ 2 * s - 1 := by
    have hsqrtpiub : Real.sqrt Real.pi ≤ 2 := by
      have h := Real.sqrt_le_sqrt Real.pi_lt_four.le
      rwa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
    have h1 : L = Real.log (Real.sqrt (Real.pi * N)) := by
      rw [Real.log_sqrt (by positivity), hL]; ring
    have h2 : Real.log (Real.sqrt (Real.pi * N)) ≤ Real.sqrt (Real.pi * N) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.sqrt N ≤ s := by
      rw [show s = Real.sqrt (s ^ 2) by rw [Real.sqrt_sq hs.le]]
      exact Real.sqrt_le_sqrt (by linarith only [hNsd, hd2s])
    have h3 : Real.sqrt (Real.pi * N) ≤ 2 * s := by
      rw [Real.sqrt_mul Real.pi_pos.le]
      exact mul_le_mul hsqrtpiub h4 (Real.sqrt_nonneg N) (by norm_num)
    linarith only [h1, h2, h3]
  have hdabs : |d| ≤ 2 := by
    have hc : (0:ℝ) < 1 + 1 / (2 * N ^ 2) := by positivity
    have hfac : d * s + d * s / (2 * N ^ 2) = (d * s) * (1 + 1 / (2 * N ^ 2)) := by
      field_simp
    have habs : |d * s| * (1 + 1 / (2 * N ^ 2)) ≤ 40 / lam ^ 4 + L := by
      have h1 : |(d * s) * (1 + 1 / (2 * N ^ 2))| ≤ 40 / lam ^ 4 + L := by
        rw [abs_le]
        constructor <;>
          [linarith only [hk1.1, hfac, hLpos]; linarith only [hk1.2, hfac, hLpos]]
      rwa [abs_mul, abs_of_pos hc] at h1
    have hcge : (0:ℝ) ≤ 1 / (2 * N ^ 2) := by positivity
    have habs' : |d * s| + |d * s| * (1 / (2 * N ^ 2)) ≤ 40 / lam ^ 4 + L := by
      calc |d * s| + |d * s| * (1 / (2 * N ^ 2))
          = |d * s| * (1 + 1 / (2 * N ^ 2)) := by ring
        _ ≤ 40 / lam ^ 4 + L := habs
    have h2 : |d * s| ≤ 40 / lam ^ 4 + L := by
      linarith only [habs', mul_nonneg (abs_nonneg (d * s)) hcge]
    have habsds : |d * s| = |d| * s := by rw [abs_mul, abs_of_pos hs]
    have h3 : |d| * s ≤ 2 * s := by
      rw [← habsds]
      linarith only [h2, heps1, hLub0]
    have h5 := abs_nonneg d
    nlinarith [h3, hs]
  have hd4 : d ^ 2 ≤ 4 := by nlinarith [sq_abs d, abs_nonneg d, hdabs]
  have hs2ub : s ^ 2 ≤ 4 * lam ^ 2 + 10 := by
    linarith only [hk2.2, hQub, hAb.1, hAb.2, hd4, heps2]
  have hNub : N ≤ 2 * lam ^ 2 + 7 := by linarith only [hNsd, hs2ub, hd4]
  have hLmu : |L - mu| ≤ 2 / lam ^ 2 := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have hlamsq : (0:ℝ) < lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (Real.pi * N) = Real.log Real.pi + Real.log N :=
      Real.log_mul Real.pi_ne_zero hN0.ne'
    have e1 : Real.log (2 * Real.pi * lam ^ 2)
        = Real.log Real.pi + Real.log (2 * lam ^ 2) := by
      rw [show (2:ℝ) * Real.pi * lam ^ 2 = Real.pi * (2 * lam ^ 2) by ring]
      exact Real.log_mul Real.pi_ne_zero hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h1 : Real.log (N / (2 * lam ^ 2)) ≤ N / (2 * lam ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hN0 hlam2pos)
    have h2 : Real.log ((2 * lam ^ 2) / N) ≤ (2 * lam ^ 2) / N - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlam2pos hN0)
    have h3 : Real.log ((2 * lam ^ 2) / N) = - Real.log (N / (2 * lam ^ 2)) := by
      rw [Real.log_div hlam2pos.ne' hN0.ne', e2]; ring
    have g1 : N / (2 * lam ^ 2) - 1 ≤ 4 / lam ^ 2 := by
      rw [div_sub_one hlam2pos.ne', div_le_div_iff₀ hlam2pos hlamsq]
      nlinarith [hNub, hlam2]
    have g2 : (2 * lam ^ 2) / N - 1 ≤ 4 / lam ^ 2 := by
      rw [div_sub_one hN0.ne', div_le_div_iff₀ hN0 hlamsq]
      nlinarith [hNlb, hlam2]
    have hhalf : (4:ℝ) / lam ^ 2 = 2 * (2 / lam ^ 2) := by ring
    rw [abs_le]
    constructor <;> linarith only [h1, h2, h3, g1, g2, hlogeq, hhalf]
  have hLup : 2 * (L - mu) ≤ (N - 2 * lam ^ 2) / (2 * lam ^ 2) := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (Real.pi * N) = Real.log Real.pi + Real.log N :=
      Real.log_mul Real.pi_ne_zero hN0.ne'
    have e1 : Real.log (2 * Real.pi * lam ^ 2)
        = Real.log Real.pi + Real.log (2 * lam ^ 2) := by
      rw [show (2:ℝ) * Real.pi * lam ^ 2 = Real.pi * (2 * lam ^ 2) by ring]
      exact Real.log_mul Real.pi_ne_zero hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h1 : Real.log (N / (2 * lam ^ 2)) ≤ N / (2 * lam ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hN0 hlam2pos)
    have hid : (N - 2 * lam ^ 2) / (2 * lam ^ 2) = N / (2 * lam ^ 2) - 1 := by
      field_simp
    rw [hid]
    linarith [hlogeq, h1]
  have hLlo : -(2 * (L - mu)) ≤ (2 * lam ^ 2 - N) / N := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (Real.pi * N) = Real.log Real.pi + Real.log N :=
      Real.log_mul Real.pi_ne_zero hN0.ne'
    have e1 : Real.log (2 * Real.pi * lam ^ 2)
        = Real.log Real.pi + Real.log (2 * lam ^ 2) := by
      rw [show (2:ℝ) * Real.pi * lam ^ 2 = Real.pi * (2 * lam ^ 2) by ring]
      exact Real.log_mul Real.pi_ne_zero hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have e3 : Real.log ((2 * lam ^ 2) / N) = Real.log (2 * lam ^ 2) - Real.log N :=
      Real.log_div hlam2pos.ne' hN0.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h2 : Real.log ((2 * lam ^ 2) / N) ≤ (2 * lam ^ 2) / N - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlam2pos hN0)
    have hid : (2 * lam ^ 2 - N) / N = (2 * lam ^ 2) / N - 1 := by field_simp
    rw [hid]
    linarith [hlogeq, h2, e2, e3]
  exact ⟨hslb, hs2ub, hNlb, hNub, hdabs, hLmu, hLup, hLlo⟩


-- no-dlmf: triangle inequality in subtraction form; proof infrastructure
/-- `|a − b| ≤ |a| + |b|` for real `a`, `b`. -/
theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

set_option maxHeartbeats 2000000 in
-- no-dlmf: first refinement of the real form of the §7.13 zero equation; proof infrastructure
/-- **First refinement of the zero equation.**  From the crude localization, the same real system
gives the sharp sizes

`|d| ≤ (μ+3)/(2λ)`, `|s² − 4λ²| ≤ (μ+3)²/(2λ²)`, `|N − 2λ²| ≤ (μ+3)²/(2λ²)`,
`|s − 2λ| ≤ (μ+3)²/(6λ³)`, `|L − μ| ≤ (μ+3)²/(6λ⁴)`.

These are the estimates that make the *second* correction term of DLMF 7.13.1 accessible. -/
theorem erf713_first_order {lam mu s d N L A : ℝ}
    (hlam : 100 ≤ lam) (hmulb : 5 ≤ mu) (hmub : mu + 3 ≤ lam)
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hQ : N < s ^ 2)
    (hslb : 2 * lam - 1 ≤ s) (hNlb : 2 * lam ^ 2 - 3 ≤ N) (hNub : N ≤ 2 * lam ^ 2 + 7)
    (hdabs : |d| ≤ 2) (hLmu0 : |L - mu| ≤ 2 / lam ^ 2)
    (hLup : 2 * (L - mu) ≤ (N - 2 * lam ^ 2) / (2 * lam ^ 2))
    (hLlo : -(2 * (L - mu)) ≤ (2 * lam ^ 2 - N) / N)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (key1 : |d * s + L + d * s / (2 * N ^ 2)| ≤ 40 / lam ^ 4)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - (s ^ 2 - N) / N ^ 2 - 4 * lam ^ 2| ≤ 80 / lam ^ 4) :
    |d| * (2 * lam) ≤ mu + 3 ∧ |d / s| * (3 * lam ^ 2) ≤ mu + 3 ∧
      |s ^ 2 - 4 * lam ^ 2| * (2 * lam ^ 2) ≤ (mu + 3) ^ 2 ∧
      |N - 2 * lam ^ 2| * (2 * lam ^ 2) ≤ (mu + 3) ^ 2 ∧
      |s - 2 * lam| * (6 * lam ^ 3) ≤ (mu + 3) ^ 2 ∧
      |L - mu| ≤ (mu + 3) ^ 2 / (6 * lam ^ 4) ∧ |d * s| ≤ mu + 3 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hlam4 : (100000000:ℝ) ≤ lam ^ 4 := by nlinarith
  have hN0 : (0:ℝ) < N := by nlinarith
  set m : ℝ := mu + 3 with hmdef
  have hm8 : (8:ℝ) ≤ m := by rw [hmdef]; linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hmm2 : m * (m - 8) ≥ 0 := mul_nonneg hm0 (by linarith)
  have hmm : m ^ 2 * (m - 8) ≥ 0 := mul_nonneg (sq_nonneg m) (by linarith)
  have hmlam : m ≤ lam := hmub
  have hk1 := abs_le.mp key1
  have hk2 := abs_le.mp key2
  have hLb0 := abs_le.mp hLmu0
  have heps4 : (40:ℝ) / lam ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlam2inv : (2:ℝ) / lam ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- Step 1: the size of `d`
  have hfac : d * s + d * s / (2 * N ^ 2) = (d * s) * (1 + 1 / (2 * N ^ 2)) := by field_simp
  have hcpos : (0:ℝ) < 1 + 1 / (2 * N ^ 2) := by positivity
  have hcge : (0:ℝ) ≤ 1 / (2 * N ^ 2) := by positivity
  have hds1 : |d * s| * (1 + 1 / (2 * N ^ 2)) ≤ mu + 1 / 100 := by
    have h1 : |(d * s) * (1 + 1 / (2 * N ^ 2))| ≤ mu + 1 / 100 := by
      rw [abs_le]
      constructor <;>
        [linarith only [hk1.1, hfac, hLb0.1, hLb0.2, heps4, hlam2inv, hmulb];
         linarith only [hk1.2, hfac, hLb0.1, hLb0.2, heps4, hlam2inv, hmulb]]
    rwa [abs_mul, abs_of_pos hcpos] at h1
  have hdsm : |d * s| ≤ mu + 1 / 100 := by
    nlinarith [hds1, mul_nonneg (abs_nonneg (d * s)) hcge]
  have hdsle : |d * s| ≤ m := by rw [hmdef]; linarith
  have habsds : |d * s| = |d| * s := by rw [abs_mul, abs_of_pos hs]
  have hdm : |d| * (2 * lam) ≤ m := by
    have h1 : |d| * s ≤ mu + 1 / 100 := by rw [← habsds]; exact hdsm
    have h2 : |d| * (2 * lam - 1) ≤ |d| * s := mul_le_mul_of_nonneg_left hslb (abs_nonneg d)
    rw [hmdef]
    nlinarith [h1, h2, hdabs, abs_nonneg d]
  -- Step 2: the size of `d / s` and of `A`
  have hTs : |d / s| * s = |d| := by
    rw [abs_div, abs_of_pos hs, div_mul_cancel₀ _ hs.ne']
  have hT3 : |d / s| * (3 * lam ^ 2) ≤ m := by
    have h2 : |d / s| * (2 * lam - 1) ≤ |d| := by
      rw [← hTs]; exact mul_le_mul_of_nonneg_left hslb (abs_nonneg _)
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ 2 * lam)
    have h4 : (0:ℝ) ≤ |d / s| * lam * (lam - 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) hlam0.le) (by linarith)
    nlinarith [h3, hdm, h4]
  have hTtiny : |d / s| ≤ 1 / 100 := by
    nlinarith [hT3, hmlam, abs_nonneg (d / s),
      mul_nonneg (abs_nonneg (d / s)) (by linarith : (0:ℝ) ≤ lam - 100), hlam0]
  have hTcube : |d / s| ^ 3 ≤ |d / s| := by
    have h := pow_le_pow_of_le_one (abs_nonneg (d / s)) (by linarith : |d / s| ≤ 1)
      (by norm_num : 1 ≤ 3)
    simpa using h
  have hA2T : |A| ≤ 2 * |d / s| := by
    have h2 : |A| ≤ |A - d / s| + |d / s| := by
      calc |A| = |(A - d / s) + d / s| := by ring_nf
        _ ≤ |A - d / s| + |d / s| := abs_add_le _ _
    linarith [hAT, hTcube, h2]
  have hAm : |A| * (4 * lam ^ 2) ≤ 3 * m := by
    have h := mul_le_mul_of_nonneg_right hA2T (by positivity : (0:ℝ) ≤ 4 * lam ^ 2)
    nlinarith [h, hT3]
  -- Step 3: the refined size of `s ^ 2 - 4 lam ^ 2` and `N - 2 lam ^ 2`
  have hQ2pos : 0 ≤ (s ^ 2 - N) / N ^ 2 := div_nonneg (by linarith) (by positivity)
  have hQNle : (s ^ 2 - N) / N ^ 2 ≤ 1 / N := by
    rw [div_le_div_iff₀ (by positivity) hN0]
    nlinarith [hNsd, sq_nonneg d]
  have hQ2 : (2 * lam ^ 2) * ((s ^ 2 - N) / N ^ 2) ≤ 2 := by
    have h2 : (2 * lam ^ 2) * (1 / N) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hN0]; linarith
    have h3 := mul_le_mul_of_nonneg_left hQNle (by positivity : (0:ℝ) ≤ 2 * lam ^ 2)
    linarith
  have hd2m : d ^ 2 * (4 * lam ^ 2) ≤ m ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ |d| * (2 * lam)) hdm
    have he : |d| * (2 * lam) * (|d| * (2 * lam)) = d ^ 2 * (4 * lam ^ 2) := by
      calc |d| * (2 * lam) * (|d| * (2 * lam)) = |d| ^ 2 * (4 * lam ^ 2) := by ring
        _ = d ^ 2 * (4 * lam ^ 2) := by rw [sq_abs]
    have he2 : m * m = m ^ 2 := by ring
    linarith [h, he.le, he.ge, he2.le, he2.ge]
  have h160 : (80 / lam ^ 4) * (2 * lam ^ 2) ≤ 1 / 50 := by
    have he : (80 / lam ^ 4) * (2 * lam ^ 2) = 160 / lam ^ 2 := by field_simp; ring
    rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hs2m : |s ^ 2 - 4 * lam ^ 2| * (2 * lam ^ 2) ≤ m ^ 2 := by
    have hA1 : -|A| ≤ A := neg_abs_le A
    have hA2 : A ≤ |A| := le_abs_self A
    have hb : |s ^ 2 - 4 * lam ^ 2|
        ≤ d ^ 2 + 2 * |A| + (s ^ 2 - N) / N ^ 2 + 80 / lam ^ 4 := by
      rw [abs_le]
      constructor <;>
        [linarith only [hk2.1, hA1, hA2, hQ2pos, sq_nonneg d];
         linarith only [hk2.2, hA1, hA2, hQ2pos, sq_nonneg d]]
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2 * lam ^ 2)
    nlinarith [h, hd2m, hAm, hQ2, h160, hmm2]
  have hNm : |N - 2 * lam ^ 2| * (2 * lam ^ 2) ≤ m ^ 2 := by
    have h1 : -|s ^ 2 - 4 * lam ^ 2| ≤ s ^ 2 - 4 * lam ^ 2 := neg_abs_le _
    have h2 : s ^ 2 - 4 * lam ^ 2 ≤ |s ^ 2 - 4 * lam ^ 2| := le_abs_self _
    have hb : |N - 2 * lam ^ 2| * 2 ≤ |s ^ 2 - 4 * lam ^ 2| + d ^ 2 := by
      rcases abs_cases (N - 2 * lam ^ 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        linarith only [hNsd, sq_nonneg d, h1, h2]
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2 * lam ^ 2)
    nlinarith [h, hs2m, hd2m, hlam2]
  have hsm : |s - 2 * lam| * (6 * lam ^ 3) ≤ m ^ 2 := by
    have hfacs : |s - 2 * lam| * (s + 2 * lam) = |s ^ 2 - 4 * lam ^ 2| := by
      rw [← abs_of_pos (show (0:ℝ) < s + 2 * lam by linarith), ← abs_mul]
      congr 1; ring
    have h1 : |s - 2 * lam| * (39 * lam / 10) ≤ |s ^ 2 - 4 * lam ^ 2| := by
      rw [← hfacs]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 * lam ^ 2)
    linarith [h2, hs2m]
  -- Step 4: the refined size of `L - mu`
  have hLm0 : |L - mu| ≤ m ^ 2 / (6 * lam ^ 4) := by
    have hN1 : (N - 2 * lam ^ 2) * (2 * lam ^ 2) ≤ m ^ 2 := by
      have h := le_abs_self (N - 2 * lam ^ 2)
      nlinarith [hNm, h, hlam2]
    have hN2 : (2 * lam ^ 2 - N) * (2 * lam ^ 2) ≤ m ^ 2 := by
      have h := neg_abs_le (N - 2 * lam ^ 2)
      nlinarith [hNm, h, hlam2]
    have hup : (N - 2 * lam ^ 2) / (2 * lam ^ 2) ≤ m ^ 2 / (3 * lam ^ 4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hN1, hlam2, sq_nonneg m]
    have hlo : (2 * lam ^ 2 - N) / N ≤ m ^ 2 / (3 * lam ^ 4) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]
      nlinarith [hN2, hlam2, sq_nonneg m, hNlb]
    have hhalf : m ^ 2 / (3 * lam ^ 4) = 2 * (m ^ 2 / (6 * lam ^ 4)) := by ring
    rw [abs_le]
    constructor <;> linarith [hLup, hLlo, hup, hlo, hhalf]
  have hLm : |L - mu| * lam ^ 4 ≤ m ^ 2 / 6 := by
    have h := mul_le_mul_of_nonneg_right hLm0 (by positivity : (0:ℝ) ≤ lam ^ 4)
    have he : m ^ 2 / (6 * lam ^ 4) * lam ^ 4 = m ^ 2 / 6 := by field_simp
    linarith [h, he.le, he.ge]
  exact ⟨hdm, hT3, hs2m, hNm, hsm, hLm0, hdsle⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: expansion of `x − y` at a solution of the real form of the §7.13 zero equation;
-- proof infrastructure
/-- **Expansion of `d = x − y`.**  `|d + μ/(2λ)| ≤ (μ+3)³/(8λ⁵)`.

This is the `x − y = −μ/(2λ) + o(λ⁻³)` half of DLMF 7.13.1 (the `λ⁻³` terms of `xₙ` and `yₙ`
are equal, so they cancel in the difference); it comes from the real component equation
`d·s = −log(√π‖w‖) + O(λ⁻⁴)` once `s` is known to `O(μ²λ⁻³)`. -/
theorem erf713_diff_expansion {lam mu s d N L : ℝ}
    (hlam : 100 ≤ lam) (hmulb : 5 ≤ mu) (hmub : mu + 3 ≤ lam)
    (hs : 0 < s) (hslb : 2 * lam - 1 ≤ s) (hNlb : 2 * lam ^ 2 - 3 ≤ N)
    (hdsle : |d * s| ≤ mu + 3)
    (hLm0 : |L - mu| ≤ (mu + 3) ^ 2 / (6 * lam ^ 4))
    (hsm : |s - 2 * lam| * (6 * lam ^ 3) ≤ (mu + 3) ^ 2)
    (key1 : |d * s + L + d * s / (2 * N ^ 2)| ≤ 40 / lam ^ 4) :
    |d + mu / (2 * lam)| * (8 * lam ^ 5) ≤ (mu + 3) ^ 3 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hN0 : (0:ℝ) < N := by nlinarith
  set m : ℝ := mu + 3 with hmdef
  have hm8 : (8:ℝ) ≤ m := by rw [hmdef]; linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hmm2 : m * (m - 8) ≥ 0 := mul_nonneg hm0 (by linarith)
  have hmm : m ^ 2 * (m - 8) ≥ 0 := mul_nonneg (sq_nonneg m) (by linarith)
  have hk1 := abs_le.mp key1
  have hLm : |L - mu| * lam ^ 4 ≤ m ^ 2 / 6 := by
    have h := mul_le_mul_of_nonneg_right hLm0 (by positivity : (0:ℝ) ≤ lam ^ 4)
    have he : m ^ 2 / (6 * lam ^ 4) * lam ^ 4 = m ^ 2 / 6 := by field_simp
    linarith [h, he.le, he.ge]
  -- Step 5: the expansion of `d`
  have h7N : (7:ℝ) * lam ^ 4 ≤ 2 * N ^ 2 := by nlinarith [hNlb, hlam2]
  have hdsN : |d * s| / (2 * N ^ 2) * lam ^ 4 ≤ m / 7 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [mul_le_mul_of_nonneg_right hdsle (by positivity : (0:ℝ) ≤ 7 * lam ^ 4),
      mul_le_mul_of_nonneg_left h7N hm0]
  have habsdiv : |d * s / (2 * N ^ 2)| = |d * s| / (2 * N ^ 2) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2)]
  have hPm : |d * s + mu| * lam ^ 4 ≤ m ^ 2 := by
    have hb1 : -(|d * s| / (2 * N ^ 2)) ≤ d * s / (2 * N ^ 2) := by
      rw [← habsdiv]; exact neg_abs_le _
    have hb2 : d * s / (2 * N ^ 2) ≤ |d * s| / (2 * N ^ 2) := by
      rw [← habsdiv]; exact le_abs_self _
    have hb : |d * s + mu| ≤ 40 / lam ^ 4 + |L - mu| + |d * s| / (2 * N ^ 2) := by
      rw [abs_le]
      have hl1 : -|L - mu| ≤ L - mu := neg_abs_le _
      have hl2 : L - mu ≤ |L - mu| := le_abs_self _
      constructor <;>
        [linarith only [hk1.1, hb1, hb2, hl1, hl2];
         linarith only [hk1.2, hb1, hb2, hl1, hl2]]
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ lam ^ 4)
    have h40 : (40 / lam ^ 4) * lam ^ 4 = 40 := by field_simp
    linarith [h, h40.le, h40.ge, hLm, hdsN, hmm2, hm8]
  have hidd : (d + mu / (2 * lam)) * (2 * lam * s)
      = 2 * lam * (d * s + mu) + mu * (s - 2 * lam) := by field_simp; ring
  have hX : |d + mu / (2 * lam)| * (8 * lam ^ 5) ≤ m ^ 3 := by
    have habs1 : |d + mu / (2 * lam)| * (2 * lam * s)
        = |2 * lam * (d * s + mu) + mu * (s - 2 * lam)| := by
      rw [← hidd, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam * s)]
    have hb : |2 * lam * (d * s + mu) + mu * (s - 2 * lam)|
        ≤ 2 * lam * |d * s + mu| + mu * |s - 2 * lam| := by
      have e1 : |2 * lam * (d * s + mu)| = 2 * lam * |d * s + mu| := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * lam by positivity)]
      have e2 : |mu * (s - 2 * lam)| = mu * |s - 2 * lam| := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < mu by linarith)]
      refine (abs_add_le _ _).trans ?_
      rw [e1, e2]
    have h1 := mul_le_mul_of_nonneg_right (habs1.le.trans hb)
      (by positivity : (0:ℝ) ≤ lam ^ 3)
    have h2 : |d + mu / (2 * lam)| * (39 * lam ^ 5 / 10)
        ≤ |d + mu / (2 * lam)| * (2 * lam * s * lam ^ 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have ha := mul_le_mul_of_nonneg_right hslb (pow_nonneg hlam0.le 4)
      have hb2 := mul_le_mul_of_nonneg_right (show (20:ℝ) ≤ lam by linarith)
        (pow_nonneg hlam0.le 4)
      nlinarith [ha, hb2]
    have h3 : 2 * lam * |d * s + mu| * lam ^ 3 ≤ 2 * m ^ 2 := by linarith [hPm]
    have h4 : mu * |s - 2 * lam| * lam ^ 3 ≤ m ^ 3 / 6 := by
      have h5 : |s - 2 * lam| * (6 * lam ^ 3) * mu ≤ m ^ 2 * mu :=
        mul_le_mul_of_nonneg_right hsm (by linarith)
      nlinarith [h5, hmdef, hm0, abs_nonneg (s - 2 * lam), hlam0]
    linarith [h1, h2, h3, h4, hmm]
  exact hX


set_option maxHeartbeats 2000000 in
-- no-dlmf: expansion of `x + y` at a solution of the real form of the §7.13 zero equation;
-- proof infrastructure
/-- **Expansion of `s = x + y`.**
`|s − (2λ + (μ² − 2μ + 2)/(16λ³))| ≤ (μ+3)⁴/(20λ⁵)`.

This is the `λ⁻³`-accurate half of DLMF 7.13.1.  The three contributions to the constant
`μ² − 2μ + 2` are `d² → μ²/(4λ²)`, `2 arctan(d/s) → −μ/(2λ²)` and the *second-order Poincaré
term* `2xy/‖w‖⁴ → 1/(2λ²)`: the last is exactly the `+2`, and it is invisible to the model
equation `√π w e^{w²} = 1`, whose roots miss DLMF's approximation by `1/(16λ³)` in each
coordinate. -/
theorem erf713_sum_expansion {lam mu s d N A : ℝ}
    (hlam : 100 ≤ lam) (hmulb : 5 ≤ mu) (hmub : mu + 3 ≤ lam)
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hQ : N < s ^ 2)
    (hslb : 2 * lam - 1 ≤ s) (hNlb : 2 * lam ^ 2 - 3 ≤ N) (hNub : N ≤ 2 * lam ^ 2 + 7)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - (s ^ 2 - N) / N ^ 2 - 4 * lam ^ 2| ≤ 80 / lam ^ 4)
    (hdm : |d| * (2 * lam) ≤ mu + 3) (hT3 : |d / s| * (3 * lam ^ 2) ≤ mu + 3)
    (hs2m : |s ^ 2 - 4 * lam ^ 2| * (2 * lam ^ 2) ≤ (mu + 3) ^ 2)
    (hNm : |N - 2 * lam ^ 2| * (2 * lam ^ 2) ≤ (mu + 3) ^ 2)
    (hsm : |s - 2 * lam| * (6 * lam ^ 3) ≤ (mu + 3) ^ 2)
    (hX : |d + mu / (2 * lam)| * (8 * lam ^ 5) ≤ (mu + 3) ^ 3) :
    |s - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))| * (20 * lam ^ 5)
      ≤ (mu + 3) ^ 4 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hN0 : (0:ℝ) < N := by nlinarith
  set m : ℝ := mu + 3 with hmdef
  have hm8 : (8:ℝ) ≤ m := by rw [hmdef]; linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hmm : m ^ 2 * (m - 8) ≥ 0 := mul_nonneg (sq_nonneg m) (by linarith)
  have hmm2 : m * (m - 8) ≥ 0 := mul_nonneg hm0 (by linarith)
  have hmlam : m ≤ lam := hmub
  -- the three second-order pieces
  have hdmu : |d - mu / (2 * lam)| * lam ≤ m := by
    have h1 : |d - mu / (2 * lam)| ≤ |d| + mu / (2 * lam) := by
      have h := abs_sub_le_abs_add_abs d (mu / (2 * lam))
      rwa [abs_of_pos (show (0:ℝ) < mu / (2 * lam) by positivity)] at h
    have h2 := mul_le_mul_of_nonneg_right h1 hlam0.le
    have h3 : mu / (2 * lam) * lam = mu / 2 := by field_simp
    linarith [h2, h3.le, h3.ge, hdm, hmdef]
  have hd2ref : |d ^ 2 - mu ^ 2 / (4 * lam ^ 2)| * (8 * lam ^ 6) ≤ m ^ 4 := by
    have hid : d ^ 2 - mu ^ 2 / (4 * lam ^ 2)
        = (d + mu / (2 * lam)) * (d - mu / (2 * lam)) := by field_simp; ring
    rw [hid, abs_mul]
    linarith [mul_le_mul hX hdmu (by positivity) (by positivity)]
  have hATm : |A - d / s| * (27 * lam ^ 6) ≤ m ^ 3 := by
    have h1 : |d / s| ^ 3 * (27 * lam ^ 6) ≤ m ^ 3 := by
      have h2 : (|d / s| * (3 * lam ^ 2)) ^ 3 ≤ m ^ 3 := by gcongr
      linarith [h2]
    have h3 := mul_le_mul_of_nonneg_right hAT (by positivity : (0:ℝ) ≤ 27 * lam ^ 6)
    linarith [h1, h3]
  have hTref : |d / s + mu / (4 * lam ^ 2)| * (8 * lam ^ 6) ≤ m ^ 3 := by
    have hid : (d / s + mu / (4 * lam ^ 2)) * (4 * lam ^ 2 * s)
        = 4 * lam ^ 2 * (d + mu / (2 * lam)) + mu * (s - 2 * lam) := by
      field_simp; ring
    have habs1 : |d / s + mu / (4 * lam ^ 2)| * (4 * lam ^ 2 * s)
        = |4 * lam ^ 2 * (d + mu / (2 * lam)) + mu * (s - 2 * lam)| := by
      rw [← hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * lam ^ 2 * s)]
    have hb : |4 * lam ^ 2 * (d + mu / (2 * lam)) + mu * (s - 2 * lam)|
        ≤ 4 * lam ^ 2 * |d + mu / (2 * lam)| + mu * |s - 2 * lam| := by
      have e1 : |4 * lam ^ 2 * (d + mu / (2 * lam))|
          = 4 * lam ^ 2 * |d + mu / (2 * lam)| := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < 4 * lam ^ 2 by positivity)]
      have e2 : |mu * (s - 2 * lam)| = mu * |s - 2 * lam| := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < mu by linarith)]
      refine (abs_add_le _ _).trans ?_
      rw [e1, e2]
    have h1 := habs1.le.trans hb
    have h2 : |d / s + mu / (4 * lam ^ 2)| * (79 * lam ^ 3 / 10)
        ≤ |d / s + mu / (4 * lam ^ 2)| * (4 * lam ^ 2 * s) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [hslb, hlam0, hlam]
    have h3 : 4 * lam ^ 2 * |d + mu / (2 * lam)| ≤ m ^ 3 / (2 * lam ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hX, abs_nonneg (d + mu / (2 * lam)), hlam0]
    have h4 : mu * |s - 2 * lam| ≤ m ^ 3 / (6 * lam ^ 3) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hsm, abs_nonneg (s - 2 * lam), hmdef, hm0, hlam0]
    have h5 : m ^ 3 / (2 * lam ^ 3) + m ^ 3 / (6 * lam ^ 3)
        = (2 * m ^ 3) / (3 * lam ^ 3) := by field_simp; ring
    have h6 : |d / s + mu / (4 * lam ^ 2)| * (79 * lam ^ 3 / 10)
        ≤ (2 * m ^ 3) / (3 * lam ^ 3) := by linarith [h1, h2, h3, h4, h5.le, h5.ge]
    have h7 := mul_le_mul_of_nonneg_right h6 (by positivity : (0:ℝ) ≤ lam ^ 3)
    have h8 : (2 * m ^ 3) / (3 * lam ^ 3) * lam ^ 3 = 2 * m ^ 3 / 3 := by field_simp
    nlinarith [h7, h8.le, h8.ge, abs_nonneg (d / s + mu / (4 * lam ^ 2)), hlam0]
  have hAref : |2 * A + mu / (2 * lam ^ 2)| * (2 * lam ^ 6) ≤ m ^ 3 := by
    have hid : 2 * A + mu / (2 * lam ^ 2)
        = 2 * ((A - d / s) + (d / s + mu / (4 * lam ^ 2))) := by ring
    have hb : |2 * A + mu / (2 * lam ^ 2)|
        ≤ 2 * (|A - d / s| + |d / s + mu / (4 * lam ^ 2)|) := by
      rw [hid, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have h := abs_add_le (A - d / s) (d / s + mu / (4 * lam ^ 2))
      linarith
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2 * lam ^ 6)
    nlinarith [h, hATm, hTref, abs_nonneg (A - d / s),
      abs_nonneg (d / s + mu / (4 * lam ^ 2)), hlam0]
  have hQref : |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| * lam ^ 6 ≤ m ^ 2 := by
    have hid : ((s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)) * (2 * lam ^ 2 * N ^ 2)
        = 2 * lam ^ 2 * ((s ^ 2 - N) - 2 * lam ^ 2)
          - (N - 2 * lam ^ 2) * (N + 2 * lam ^ 2) := by field_simp; ring
    have habs1 : |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| * (2 * lam ^ 2 * N ^ 2)
        = |2 * lam ^ 2 * ((s ^ 2 - N) - 2 * lam ^ 2)
          - (N - 2 * lam ^ 2) * (N + 2 * lam ^ 2)| := by
      rw [← hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam ^ 2 * N ^ 2)]
    have hQd : |(s ^ 2 - N) - 2 * lam ^ 2| * lam ^ 2 ≤ m ^ 2 := by
      have h1 : |(s ^ 2 - N) - 2 * lam ^ 2|
          ≤ |s ^ 2 - 4 * lam ^ 2| + |N - 2 * lam ^ 2| := by
        have h := abs_sub_le_abs_add_abs (s ^ 2 - 4 * lam ^ 2) (N - 2 * lam ^ 2)
        have he : (s ^ 2 - 4 * lam ^ 2) - (N - 2 * lam ^ 2) = (s ^ 2 - N) - 2 * lam ^ 2 := by
          ring
        rw [he] at h
        exact h
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ lam ^ 2)
      nlinarith [h2, hs2m, hNm, hlam2, abs_nonneg (s ^ 2 - 4 * lam ^ 2),
        abs_nonneg (N - 2 * lam ^ 2)]
    have hb : |2 * lam ^ 2 * ((s ^ 2 - N) - 2 * lam ^ 2)
          - (N - 2 * lam ^ 2) * (N + 2 * lam ^ 2)|
        ≤ 2 * lam ^ 2 * |(s ^ 2 - N) - 2 * lam ^ 2|
          + |N - 2 * lam ^ 2| * (N + 2 * lam ^ 2) := by
      have e1 : |2 * lam ^ 2 * ((s ^ 2 - N) - 2 * lam ^ 2)|
          = 2 * lam ^ 2 * |(s ^ 2 - N) - 2 * lam ^ 2| := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * lam ^ 2 by positivity)]
      have e2 : |(N - 2 * lam ^ 2) * (N + 2 * lam ^ 2)|
          = |N - 2 * lam ^ 2| * (N + 2 * lam ^ 2) := by
        rw [abs_mul, abs_of_pos (show (0:ℝ) < N + 2 * lam ^ 2 by nlinarith)]
      refine (abs_sub_le_abs_add_abs _ _).trans ?_
      rw [e1, e2]
    have t1 : 2 * lam ^ 2 * |(s ^ 2 - N) - 2 * lam ^ 2| ≤ 2 * m ^ 2 := by
      linarith [hQd]
    have t2 : |N - 2 * lam ^ 2| * (N + 2 * lam ^ 2) ≤ 3 * m ^ 2 := by
      have h1 : |N - 2 * lam ^ 2| * (N + 2 * lam ^ 2)
          ≤ |N - 2 * lam ^ 2| * (41 * lam ^ 2 / 10) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      nlinarith [h1, hNm, abs_nonneg (N - 2 * lam ^ 2), hlam2]
    have hbig : |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| * (2 * lam ^ 2 * N ^ 2)
        ≤ 5 * m ^ 2 := by
      linarith [habs1.le, habs1.ge, hb, t1, t2]
    have hN2big : (39:ℝ) * lam ^ 4 / 10 ≤ N ^ 2 := by nlinarith [hNlb, hlam2]
    have h9 : |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| * (2 * lam ^ 2 * (39 * lam ^ 4 / 10))
        ≤ 5 * m ^ 2 := by
      refine le_trans ?_ hbig
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [hN2big, hlam0]
    linarith [h9]
  -- the refined `s ^ 2` equation
  have hs2ref : |s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)| * lam ^ 4
      ≤ m ^ 4 / 40 := by
    have hid : s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)
        = (d ^ 2 - mu ^ 2 / (4 * lam ^ 2)) + (2 * A + mu / (2 * lam ^ 2))
          + ((s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2))
          + (s ^ 2 - d ^ 2 - 2 * A - (s ^ 2 - N) / N ^ 2 - 4 * lam ^ 2) := by
      field_simp; ring
    have hb : |s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)|
        ≤ |d ^ 2 - mu ^ 2 / (4 * lam ^ 2)| + |2 * A + mu / (2 * lam ^ 2)|
          + |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| + 80 / lam ^ 4 := by
      rw [hid]
      refine le_trans (abs_add_le _ _) ?_
      exact add_le_add (le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)) key2
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ lam ^ 4)
    have e1 : |d ^ 2 - mu ^ 2 / (4 * lam ^ 2)| * lam ^ 4 ≤ m ^ 4 / (8 * lam ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hd2ref]
    have e2 : |2 * A + mu / (2 * lam ^ 2)| * lam ^ 4 ≤ m ^ 3 / (2 * lam ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hAref]
    have e3 : |(s ^ 2 - N) / N ^ 2 - 1 / (2 * lam ^ 2)| * lam ^ 4 ≤ m ^ 2 / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hQref]
    have e4 : (80 / lam ^ 4) * lam ^ 4 = 80 := by field_simp
    have e5 : m ^ 4 / (8 * lam ^ 2) + m ^ 3 / (2 * lam ^ 2) + m ^ 2 / lam ^ 2
        ≤ m ^ 4 / (2 * lam ^ 2) := by
      have hpos : (0:ℝ) < lam ^ 2 := by linarith
      have key : m ^ 4 / 8 + m ^ 3 / 2 + m ^ 2 ≤ m ^ 4 / 2 := by
        nlinarith [hmm, hmm2, hm8, hm0]
      have hid : m ^ 4 / (8 * lam ^ 2) + m ^ 3 / (2 * lam ^ 2) + m ^ 2 / lam ^ 2
          = (m ^ 4 / 8 + m ^ 3 / 2 + m ^ 2) / lam ^ 2 := by ring
      have hid2 : m ^ 4 / (2 * lam ^ 2) = (m ^ 4 / 2) / lam ^ 2 := by ring
      rw [hid, hid2, div_le_div_iff₀ hpos hpos]
      linarith [mul_le_mul_of_nonneg_right key hpos.le]
    have e6 : m ^ 4 / (2 * lam ^ 2) ≤ m ^ 4 / 20000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hm0, sq_nonneg (m ^ 2), hlam2]
    have e7 : (80:ℝ) ≤ m ^ 4 / 40 - m ^ 4 / 20000 := by
      nlinarith [hm8, hm0, sq_nonneg (m ^ 2 - 64), sq_nonneg m, hmm, hmm2]
    linarith [h, e1, e2, e3, e4.le, e4.ge, e5, e6, e7]
  -- and finally the expansion of `s`
  have hT0nn : (0:ℝ) ≤ (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2) :=
    div_nonneg (by nlinarith [sq_nonneg (mu - 1)]) (by positivity)
  have hT0ub : (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2) ≤ m ^ 2 / (4 * lam ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hmdef, hmulb, hlam2]
  have hP0sq : (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2
      = 4 * lam ^ 2 + (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)
        + ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) := by
    field_simp; ring
  have hP0lb : 2 * lam ≤ 2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3) := by
    have : (0:ℝ) ≤ (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3) :=
      div_nonneg (by nlinarith [sq_nonneg (mu - 1)]) (by positivity)
    linarith
  have hfacs : |s - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))|
      * (s + (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
      = |s ^ 2 - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2| := by
    rw [← abs_of_pos (show (0:ℝ) < s + (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) by
      linarith), ← abs_mul]
    congr 1; ring
  have hsq : |s ^ 2 - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2| * lam ^ 4
      ≤ m ^ 4 / 39 := by
    have hid : s ^ 2 - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2
        = (s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2))
          + -(((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2)) := by
      rw [hP0sq]; ring
    have hb : |s ^ 2 - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2|
        ≤ |s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)|
          + ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) := by
      rw [hid]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ)
        ≤ ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2))]
    have h := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ lam ^ 4)
    have hsmallsq : ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) * lam ^ 4
        ≤ m ^ 4 / 2560000 := by
      have hsq1 : ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 ≤ (m ^ 2 / (4 * lam ^ 2)) ^ 2 := by
        nlinarith [hT0nn, hT0ub]
      have he : (m ^ 2 / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) * lam ^ 4
          = m ^ 4 / (256 * lam ^ 2) := by field_simp; ring
      have h1 : ((mu ^ 2 - 2 * mu + 2) / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) * lam ^ 4
          ≤ (m ^ 2 / (4 * lam ^ 2)) ^ 2 / (16 * lam ^ 2) * lam ^ 4 := by
        gcongr
      have h2 : m ^ 4 / (256 * lam ^ 2) ≤ m ^ 4 / 2560000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hm0, sq_nonneg (m ^ 2), hlam2]
      linarith [h1, he.le, he.ge, h2]
    have hslack : m ^ 4 / 40 + m ^ 4 / 2560000 ≤ m ^ 4 / 39 := by
      nlinarith [hm0, sq_nonneg (m ^ 2), hm8]
    linarith [h, hs2ref, hsmallsq, hslack]
  have hlow : |s - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))| * (39 * lam / 10)
      ≤ |s ^ 2 - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) ^ 2| := by
    rw [← hfacs]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hfin := mul_le_mul_of_nonneg_right hlow (by positivity : (0:ℝ) ≤ lam ^ 4)
  nlinarith [hfin, hsq, hm0, hm8, hlam0,
    abs_nonneg (s - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))]

set_option maxHeartbeats 1000000 in
-- no-dlmf: the real-variable inversion of the third-order zero equation at a fixed index;
-- proof infrastructure for DLMF 7.13.1, not itself a numbered display
/-- **Third-order inversion of the `erf`-zero equation.**  Let `n ≥ 3400` and let `w` lie in the
open first quadrant with

`‖w² + log (√π w) + 1/(2w²) − 2πi·n‖ ≤ ε`,  `ε ≤ 40/λₙ⁴`.

Then `Re w` and `Im w` agree with the DLMF 7.13.1 approximations `erfZeroReApprox n`,
`erfZeroImApprox n` to within

`(μₙ + 3)⁴ / (20 λₙ⁵)`,

which is `O(log⁴ n · n^{-5/2}) = o(λₙ⁻³)`.  Together with `cerf_zero_log_equation_third` — which
supplies exactly this hypothesis for every zero of `erf`, with `n` the zero's index — this is
the analytic content of DLMF 7.13.1; what remains for the display is the identification of the
index `k` produced there with the DLMF enumeration index.

The proof takes real and imaginary parts, `w = x + iy`, and inverts the resulting exact system
`d·s = −log(√π‖w‖) − ⋯`, `s² = 4λ² + d² + 2 arctan(d/s) + 2xy/‖w‖⁴ + ⋯` by three explicit
iterations (`erf713_crude`, `erf713_first_order`, `erf713_diff_expansion`,
`erf713_sum_expansion`). -/
theorem erf713_zero_expansion {n : ℕ} (hn : 3400 ≤ n) {w : ℂ} {eps : ℝ}
    (hx : 0 < w.re) (hy : 0 < w.im) (heb : eps ≤ 40 / erfZeroLambda n ^ 4)
    (heq : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ eps) :
    |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ∧
      |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  set lam : ℝ := erfZeroLambda n with hlamdef
  set mu : ℝ := erfZeroMu n with hmudef
  have hlamsq : lam ^ 2 = ((n:ℝ) - 1 / 8) * Real.pi := by
    rw [hlamdef]
    exact Real.sq_sqrt (by nlinarith)
  have hlamnn : (0:ℝ) ≤ lam := by rw [hlamdef]; exact Real.sqrt_nonneg _
  have hlam : (100:ℝ) ≤ lam := by nlinarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hmudef' : mu = Real.log (lam * Real.sqrt (2 * Real.pi)) := by
    rw [hmudef, hlamdef]
    simp only [erfZeroMu]
  obtain ⟨hmulb, hmub⟩ := erf713_mu_bounds hlam hmudef'
  have h2mu : 2 * mu = Real.log (2 * Real.pi * lam ^ 2) := by
    have h1 : Real.log ((lam * Real.sqrt (2 * Real.pi)) ^ 2)
        = 2 * Real.log (lam * Real.sqrt (2 * Real.pi)) := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : (lam * Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi * lam ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [← h2, h1, hmudef']
  -- the real and imaginary components of the hypothesis
  have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hnsq : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hnsq0 : (0:ℝ) < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have hN0 : (0:ℝ) < w.re ^ 2 + w.im ^ 2 := by rw [← hnsq]; exact hnsq0
  have hlogre : (Complex.log ((Real.sqrt Real.pi : ℂ) * w)).re
      = (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2)) := by
    have ht : (Real.sqrt Real.pi * ‖w‖) ^ 2 = Real.pi * (w.re ^ 2 + w.im ^ 2) := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Complex.sq_norm, hnsq]
    have h2 : Real.log ((Real.sqrt Real.pi * ‖w‖) ^ 2)
        = 2 * Real.log (Real.sqrt Real.pi * ‖w‖) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← ht, h2]
    ring
  have hlogim : (Complex.log ((Real.sqrt Real.pi : ℂ) * w)).im = Complex.arg w := by
    rw [Complex.log_im, Complex.arg_real_mul w (Real.sqrt_pos.mpr Real.pi_pos)]
  have hsqre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two, Complex.mul_re]
  have hsqim : (w ^ 2).im = 2 * w.re * w.im := by
    simp only [pow_two, Complex.mul_im]; ring
  have hns2 : Complex.normSq (2 * w ^ 2) = 4 * (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h4 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
    rw [map_mul, map_pow, hnsq, h4]
  have hre2 : (2 * w ^ 2 : ℂ).re = 2 * (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.mul_re, hsqre, hsqim]; simp
  have him2 : (2 * w ^ 2 : ℂ).im = 2 * (2 * w.re * w.im) := by
    rw [Complex.mul_im, hsqre, hsqim]; simp
  have hinvre : ((1 : ℂ) / (2 * w ^ 2)).re
      = (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_re, hre2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hinvim : ((1 : ℂ) / (2 * w ^ 2)).im
      = -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_im, him2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcre : (2 * (Real.pi : ℂ) * Complex.I * n).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hcim : (2 * (Real.pi : ℂ) * Complex.I * n).im = 2 * Real.pi * n := by
    simp [Complex.mul_re, Complex.mul_im]
  have harg : Complex.arg w
      = Real.pi / 4 - Real.arctan ((w.re - w.im) / (w.re + w.im)) :=
    arg_eq_pi_div_four_sub_arctan hx hy
  -- the two real equations
  have hbound : eps ≤ 40 / lam ^ 4 := heb
  have hreeq : |(w.re - w.im) * (w.re + w.im)
      + (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
      + (w.re - w.im) * (w.re + w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)| ≤ 40 / lam ^ 4 := by
    have h := (Complex.abs_re_le_norm (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * n)).trans (heq.trans hbound)
    simp only [Complex.sub_re, Complex.add_re, hsqre, hlogre, hinvre, hcre] at h
    calc |(w.re - w.im) * (w.re + w.im)
          + (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re - w.im) * (w.re + w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        = |w.re ^ 2 - w.im ^ 2 + (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 0| := by
          congr 1; ring
      _ ≤ 40 / lam ^ 4 := h
  have himeq : |(w.re + w.im) ^ 2 - (w.re - w.im) ^ 2
      - 2 * Real.arctan ((w.re - w.im) / (w.re + w.im))
      - ((w.re + w.im) ^ 2 - (w.re ^ 2 + w.im ^ 2)) / (w.re ^ 2 + w.im ^ 2) ^ 2
      - 4 * lam ^ 2| ≤ 80 / lam ^ 4 := by
    have h := (Complex.abs_im_le_norm (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * n)).trans (heq.trans hbound)
    simp only [Complex.sub_im, Complex.add_im, hsqim, hlogim, hinvim, hcim, harg] at h
    have hid : (w.re + w.im) ^ 2 - (w.re - w.im) ^ 2
        - 2 * Real.arctan ((w.re - w.im) / (w.re + w.im))
        - ((w.re + w.im) ^ 2 - (w.re ^ 2 + w.im ^ 2)) / (w.re ^ 2 + w.im ^ 2) ^ 2
        - 4 * lam ^ 2
        = 2 * (2 * w.re * w.im
          + (Real.pi / 4 - Real.arctan ((w.re - w.im) / (w.re + w.im)))
          + -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 2 * Real.pi * n) := by
      rw [hlamsq]; field_simp; ring
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h40 : (40:ℝ) / lam ^ 4 * 2 = 80 / lam ^ 4 := by ring
    linarith [h, h40.le, h40.ge]
  -- the real-variable inversion
  have hs : (0:ℝ) < w.re + w.im := by linarith
  have hNsd : 2 * (w.re ^ 2 + w.im ^ 2) = (w.re + w.im) ^ 2 + (w.re - w.im) ^ 2 := by ring
  have hQlt : w.re ^ 2 + w.im ^ 2 < (w.re + w.im) ^ 2 := by nlinarith
  have hd2s : (w.re - w.im) ^ 2 ≤ (w.re + w.im) ^ 2 := by nlinarith
  have hAbd : |Real.arctan ((w.re - w.im) / (w.re + w.im))| ≤ 2 := by
    have h1 := Real.neg_pi_div_two_lt_arctan ((w.re - w.im) / (w.re + w.im))
    have h2 := Real.arctan_lt_pi_div_two ((w.re - w.im) / (w.re + w.im))
    rw [abs_le]
    constructor <;> linarith [Real.pi_lt_four]
  have hAT := abs_arctan_sub_self_le ((w.re - w.im) / (w.re + w.im))
  have hL : (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
      = (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2)) := rfl
  obtain ⟨hslb, -, hNlb, hNub, hdabs, hLmu0, hLup, hLlo⟩ :=
    erf713_crude hlam h2mu hL hs hd2s hNsd hQlt hAbd hreeq himeq
  obtain ⟨hdm, hT3, hs2m, hNm, hsm, hLm0, hdsle⟩ :=
    erf713_first_order hlam hmulb hmub hs hNsd hQlt hslb hNlb hNub hdabs hLmu0 hLup hLlo hAT
      hreeq himeq
  have hX := erf713_diff_expansion hlam hmulb hmub hs hslb hNlb hdsle hLm0 hsm hreeq
  have hS := erf713_sum_expansion hlam hmulb hmub hs hNsd hQlt hslb hNlb hNub hAT himeq hdm hT3
    hs2m hNm hsm hX
  -- assemble
  have hm0 : (0:ℝ) ≤ mu + 3 := by linarith
  have hm8 : (8:ℝ) ≤ mu + 3 := by linarith
  have hlam5 : (0:ℝ) < 20 * lam ^ 5 := by positivity
  have hSd : |(w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))|
      ≤ (mu + 3) ^ 4 / (20 * lam ^ 5) := by
    rw [le_div_iff₀ hlam5]; exact hS
  have hXd : |(w.re - w.im) + mu / (2 * lam)| ≤ (mu + 3) ^ 4 / (20 * lam ^ 5) := by
    rw [le_div_iff₀ hlam5]
    nlinarith [hX, hm0, hm8, abs_nonneg ((w.re - w.im) + mu / (2 * lam)),
      pow_pos hlam0 5]
  have hApproxRe : erfZeroReApprox n
      = ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) + -(mu / (2 * lam))) / 2 := by
    rw [erfZeroReApprox, ← hlamdef, ← hmudef]
    field_simp
    ring
  have hApproxIm : erfZeroImApprox n
      = ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) - -(mu / (2 * lam))) / 2 := by
    rw [erfZeroImApprox, ← hlamdef, ← hmudef]
    field_simp
    ring
  constructor
  · rw [hApproxRe]
    have hid : w.re - ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))
        + -(mu / (2 * lam))) / 2
        = (((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
          + ((w.re - w.im) + mu / (2 * lam))) / 2 := by ring
    rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h := (abs_add_le ((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
      ((w.re - w.im) + mu / (2 * lam)))
    linarith [h, hSd, hXd]
  · rw [hApproxIm]
    have hid : w.im - ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))
        - -(mu / (2 * lam))) / 2
        = (((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
          - ((w.re - w.im) + mu / (2 * lam))) / 2 := by ring
    rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h := abs_sub_le_abs_add_abs ((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
      ((w.re - w.im) + mu / (2 * lam))
    linarith [h, hSd, hXd]

-- no-dlmf: the `n = 2` truncation of the Poincaré expansion evaluated at a zero of `erf`;
-- proof infrastructure for the §7.13 zero asymptotics, not a numbered DLMF display
/-- **The second-order effective zero equation for `erf`.**  If `Re w > 0`, `erf w = 0` and
`‖w‖ ≥ 4`, then

`‖√π · w · e^{w²} − (1 − 1/(2w²))‖ ≤ 48 / ‖w‖⁴`.

This is `cerf_zero_equation` carried one order further: the `n = 2` instance of
`FLMF.Error.cerfc_poincare_bound` with `δ = π/4` (constant `2·4!/‖w‖⁵ = 48/‖w‖⁵`), multiplied
by `w`.  The extra term `−1/(2w²)` is *not* negligible for DLMF 7.13.1: it is what produces the
`+2` in the numerator `1 − μ + μ²/2` of the `λ⁻³` coefficient. -/
theorem cerf_zero_equation_third {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re) (hbig : 4 ≤ ‖w‖) :
    ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - 1 / (2 * w ^ 2))‖
      ≤ 48 / ‖w‖ ^ 4 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hz
  have hsec : |Complex.arg w| ≤ 3 * Real.pi / 4 - Real.pi / 4 := by
    have h : |Complex.arg w| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 4) (by positivity)
    (by linarith [Real.pi_pos]) hz hsec 2
  have hcerfc : cerfc w = 1 := by rw [cerfc, hw]; ring
  have hsin : Real.sin (2 * (Real.pi / 4) / 3) = 1 / 2 := by
    rw [show 2 * (Real.pi / 4) / 3 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hcerfc, hsin] at h
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  norm_num at h
  have hbd : ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - (w⁻¹ + -(1 / 2) / w ^ 3)‖
      ≤ 48 / ‖w‖ ^ 5 := by
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  have hfac : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - 1 / (2 * w ^ 2))
      = w * ((Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - (w⁻¹ + -(1 / 2) / w ^ 3)) := by
    field_simp
    ring
  rw [hfac, norm_mul]
  calc ‖w‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) - (w⁻¹ + -(1 / 2) / w ^ 3)‖
      ≤ ‖w‖ * (48 / ‖w‖ ^ 5) := mul_le_mul_of_nonneg_left hbd hwn.le
    _ = 48 / ‖w‖ ^ 4 := by field_simp

-- no-dlmf: logarithmic form of the second-order effective zero equation; proof infrastructure
-- for the §7.13 zero asymptotics
/-- **The second-order logarithmic zero equation for `erf`.**  If `Re w > 0`, `erf w = 0` and
`‖w‖ ≥ 4`, then for some integer `k`

`‖w² + log (√π · w) + 1/(2w²) − 2πi·k‖ ≤ 150 / ‖w‖⁴`.

Taking logarithms in `cerf_zero_equation_third`, after multiplying by `e^{1/(2w²)}` so that the
remainder is genuinely `O(‖w‖⁻⁴)`: `(1−q)e^{q} − 1 = O(q²)` with `q = 1/(2w²)`.  This is the
equation that `erf713_zero_expansion` inverts, and the `O(‖w‖⁻⁴)` right-hand side is exactly
what is needed to reach the `λ⁻³` term of DLMF 7.13.1 (the `O(‖w‖⁻²)` of
`cerf_zero_log_equation` only reaches `λ⁻¹`). -/
theorem cerf_zero_log_equation_third {w : ℂ} (hw : cerf w = 0) (hre : 0 < w.re)
    (hbig : 4 ≤ ‖w‖) :
    ∃ k : ℤ, ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 150 / ‖w‖ ^ 4 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hz
  have hw2 : (16 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith
  have hw4 : (256 : ℝ) ≤ ‖w‖ ^ 4 := by nlinarith
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hprod : ((Real.sqrt Real.pi : ℝ) : ℂ) * w ≠ 0 := mul_ne_zero hsp hz
  set q : ℂ := 1 / (2 * w ^ 2) with hqdef
  have hqn : ‖q‖ = 1 / (2 * ‖w‖ ^ 2) := by
    rw [hqdef, norm_div, norm_one, norm_mul, norm_pow]
    norm_num
  have hqsmall : ‖q‖ ≤ 1 / 32 := by
    rw [hqn, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set u : ℂ := w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + q with hu
  have hexpu : Complex.exp u = (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2)
      * Complex.exp q := by
    rw [hu, Complex.exp_add, Complex.exp_add, Complex.exp_log hprod]; ring
  have hr := cerf_zero_equation_third hw hre hbig
  have hexpq1 : ‖Complex.exp q - 1‖ ≤ 2 * ‖q‖ :=
    Complex.norm_exp_sub_one_le (by linarith)
  have hexpqn : ‖Complex.exp q‖ ≤ 2 := by
    have h := norm_sub_norm_le (Complex.exp q) 1
    simp only [norm_one] at h
    linarith
  have hkey : ‖(1 - q) * Complex.exp q - 1‖ ≤ 3 * ‖q‖ ^ 2 := by
    have hid : (1 - q) * Complex.exp q - 1
        = (Complex.exp q - 1 - q) - q * (Complex.exp q - 1) := by ring
    have h1 : ‖Complex.exp q - 1 - q‖ ≤ ‖q‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le (by linarith)
    have h2 : ‖q * (Complex.exp q - 1)‖ ≤ ‖q‖ * (2 * ‖q‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hexpq1 (norm_nonneg q)
    rw [hid]
    calc ‖(Complex.exp q - 1 - q) - q * (Complex.exp q - 1)‖
        ≤ ‖Complex.exp q - 1 - q‖ + ‖q * (Complex.exp q - 1)‖ := norm_sub_le _ _
      _ ≤ ‖q‖ ^ 2 + ‖q‖ * (2 * ‖q‖) := by linarith
      _ = 3 * ‖q‖ ^ 2 := by ring
  have hzeta : ‖Complex.exp u - 1‖ ≤ 100 / ‖w‖ ^ 4 := by
    have hid : Complex.exp u - 1 = ((1 - q) * Complex.exp q - 1)
        + ((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - q)) * Complex.exp q := by
      rw [hexpu]; ring
    have h2 : ‖((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - q))
        * Complex.exp q‖ ≤ (48 / ‖w‖ ^ 4) * 2 := by
      rw [norm_mul]
      exact mul_le_mul hr hexpqn (norm_nonneg _) (by positivity)
    have h3 : 3 * ‖q‖ ^ 2 = 3 / (4 * ‖w‖ ^ 4) := by
      rw [hqn]; field_simp; ring
    have h4 : (3 : ℝ) / (4 * ‖w‖ ^ 4) ≤ 4 / ‖w‖ ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hid]
    calc ‖((1 - q) * Complex.exp q - 1)
          + ((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - q)) * Complex.exp q‖
        ≤ ‖(1 - q) * Complex.exp q - 1‖
          + ‖((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) - (1 - q)) * Complex.exp q‖ :=
          norm_add_le _ _
      _ ≤ 4 / ‖w‖ ^ 4 + (48 / ‖w‖ ^ 4) * 2 := by linarith [hkey, h3, h4]
      _ = 100 / ‖w‖ ^ 4 := by ring
  have hhalf : ‖Complex.exp u - 1‖ ≤ 1 / 2 := by
    refine hzeta.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1δ : (1 : ℂ) + (Complex.exp u - 1) = Complex.exp u := by ring
  have hlogbound : ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := by
    have h := Complex.norm_log_one_add_half_le_self hhalf
    rwa [h1δ] at h
  have hone : Complex.exp (u - Complex.log (Complex.exp u)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero u),
      div_self (Complex.exp_ne_zero u)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨k, ?_⟩
  have heq : u - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp u) := by
    linear_combination hk
  have hgoal : w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp u) := by
    rw [← heq, hu]
  rw [hgoal]
  calc ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := hlogbound
    _ ≤ (3 / 2) * (100 / ‖w‖ ^ 4) := by linarith
    _ = 150 / ‖w‖ ^ 4 := by ring


/-! ## erf zeros — the index correspondence and the enumeration (DLMF 7.13.1)

The final assembly.  `erf713_zero_expansion` pins a zero's coordinates once its *index* — the
integer `k` of `cerf_zero_log_equation_third` — is known.  What follows organizes the zeros by
that index:

* `erf713_param_bounds`, `erf713_approx_norm_sq` — elementary size estimates; in particular a
  point matching the DLMF approximations at index `n` has `|‖w‖² − 2λₙ²| ≤ 1`, while consecutive
  grid values `2λₙ²` are `2π` apart.  Hence the index is *determined* by the modulus.
* `erf713_grid_zero` — for every `n ≥ 3400` there is a zero of `erf` matching the approximations
  at index `n` (the model root of `exists_model_root` pins `k = n`).
* `erf713_zero_has_index` — conversely every first-quadrant zero with `‖w‖² ≥ 21987` matches the
  approximations at some index `n ≥ 3500`.
* `erf713_zero_index_unique` — two zeros matching at the same index coincide.

Together these say: the first-quadrant zeros with `‖w‖² ≥ 21987` are in strictly
modulus-increasing bijection with the indices `n ≥ 3500`.  The only external input left is the
count of the *small* zeros, `erf713_low_zero_count`. -/

-- no-dlmf: elementary size bounds for the DLMF 7.13.2 parameters at a large index; proof
-- infrastructure for the §7.13 zero asymptotics
/-- **Size of the parameters at a large index.**  For `n ≥ 3400` the DLMF 7.13.2 parameters
satisfy `λₙ ≥ 100`, `μₙ ≥ 5`, `μₙ + 3 ≤ λₙ/2`, and the `erf713_zero_expansion` error term obeys
`(μₙ + 3)⁴/(20 λₙ⁵) ≤ 1/(320 λₙ)`.

The bound `μ + 3 ≤ λ/2` sharpens `erf713_mu_bounds` (which only gives `μ + 3 ≤ λ`) by keeping
the constant `μ ≤ 4√λ − 2` from the same `log x ≤ 2(√x − 1)` chain; the extra factor `16` in
the error term is what makes the expansion error smaller than the zero separation `1/(24‖w‖)`,
so that two zeros matching at the same index must coincide. -/
theorem erf713_param_bounds {n : ℕ} (hn : 3400 ≤ n) :
    100 ≤ erfZeroLambda n ∧ 5 ≤ erfZeroMu n ∧ erfZeroMu n + 3 ≤ erfZeroLambda n / 2 ∧
      (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ≤ 1 / (320 * erfZeroLambda n) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  have hlamsq : erfZeroLambda n ^ 2 = ((n:ℝ) - 1/8) * Real.pi := by
    simp only [erfZeroLambda]
    exact Real.sq_sqrt (by nlinarith)
  have hlamnn : (0:ℝ) ≤ erfZeroLambda n := by
    simp only [erfZeroLambda]; exact Real.sqrt_nonneg _
  have hlam : (100:ℝ) ≤ erfZeroLambda n := by nlinarith
  have hmudef : erfZeroMu n = Real.log (erfZeroLambda n * Real.sqrt (2 * Real.pi)) := rfl
  obtain ⟨h5, -⟩ := erf713_mu_bounds hlam hmudef
  have hlam0 : (0:ℝ) < erfZeroLambda n := by linarith
  -- the sharpened upper bound `μ + 3 ≤ λ/2`
  have h3 : erfZeroMu n + 3 ≤ erfZeroLambda n / 2 := by
    set lam : ℝ := erfZeroLambda n with hlamdef
    have hsnn : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have hub : Real.sqrt (2 * Real.pi) ≤ 2.83 := by nlinarith [Real.pi_lt_four]
    have hpos : (0:ℝ) < lam * Real.sqrt (2 * Real.pi) := by nlinarith
    have hsl : Real.sqrt lam ≤ lam / 10 := by
      rw [show lam / 10 = Real.sqrt ((lam / 10) ^ 2) by
        rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hslnn : (0:ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hu4 : lam * Real.sqrt (2 * Real.pi) ≤ 4 * lam := by nlinarith
    have hsu : Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ 2 * Real.sqrt lam := by
      have h1 : Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ Real.sqrt (4 * lam) :=
        Real.sqrt_le_sqrt hu4
      have h2 : Real.sqrt (4 * lam) = 2 * Real.sqrt lam := by
        rw [show (4:ℝ) * lam = 2 ^ 2 * lam by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      linarith [h1, h2.le, h2.ge]
    have hlogsqrt : Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
        ≤ Real.sqrt (lam * Real.sqrt (2 * Real.pi)) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
    have hhalf : Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
        = Real.log (lam * Real.sqrt (2 * Real.pi)) / 2 :=
      Real.log_sqrt hpos.le
    rw [hmudef]
    linarith [hsl, hsu, hlogsqrt, hhalf]
  refine ⟨hlam, h5, h3, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : (erfZeroMu n + 3) ^ 4 ≤ (erfZeroLambda n / 2) ^ 4 := by
    have h0 : (0:ℝ) ≤ erfZeroMu n + 3 := by linarith
    gcongr
  have h5' : (erfZeroLambda n / 2) ^ 4 = erfZeroLambda n ^ 4 / 16 := by ring
  rw [h5'] at h4
  nlinarith [h4, hlam0]

-- no-dlmf: the defining square of the DLMF 7.13.2 parameter `λ`; proof infrastructure
/-- `λₙ² = (n − 1/8)π` for `n ≥ 1`. -/
theorem erf713_lambda_sq {n : ℕ} (hn : 1 ≤ n) :
    erfZeroLambda n ^ 2 = ((n:ℝ) - 1/8) * Real.pi := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  simp only [erfZeroLambda]
  exact Real.sq_sqrt (by nlinarith [Real.pi_pos])

set_option maxHeartbeats 800000 in
-- no-dlmf: real-variable computation behind `erf713_approx_norm_sq`; proof infrastructure
/-- **The modulus of a point matching the DLMF 7.13.1 approximations.**  If `(x, y)` sits within
`d ≤ 1/(20λ)` of the pair `(λ − μ/(4λ) + ⋯, λ + μ/(4λ) + ⋯)` of DLMF 7.13.1, then
`|x² + y² − 2λ²| ≤ 1` and both coordinates exceed `λ − 1/2`.  The `μ/(4λ)` terms cancel in the
sum of squares, leaving only `4λ·(λ⁻³-term) + 2(μ/4λ)² + O(λ d)`, each `O(1)` and in fact
`< 1/2`. -/
theorem erf713_norm_sq_aux {lam mu x y d : ℝ} (hlam : 100 ≤ lam) (hmu5 : 5 ≤ mu)
    (hmu3 : mu + 3 ≤ lam) (hd0 : 0 ≤ d) (hd : d ≤ 1 / (20 * lam))
    (hx : |x - (lam - (1/4) * mu * lam⁻¹ + (1/16) * (1 - mu + (1/2) * mu ^ 2) * lam⁻¹ ^ 3)| ≤ d)
    (hy : |y - (lam + (1/4) * mu * lam⁻¹ + (1/16) * (1 - mu + (1/2) * mu ^ 2) * lam⁻¹ ^ 3)| ≤ d) :
    |x ^ 2 + y ^ 2 - 2 * lam ^ 2| ≤ 1 ∧ lam - 1/2 ≤ x ∧ lam - 1/2 ≤ y := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have ht1 : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam0.ne'
  have hdt : d ≤ lam⁻¹ / 20 := by
    refine hd.trans (le_of_eq ?_)
    field_simp
  set t : ℝ := lam⁻¹ with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have htle : t ≤ 1/100 := by nlinarith
  set P : ℝ := 1 - mu + (1/2) * mu ^ 2 with hPdef
  have hP0 : (0:ℝ) ≤ P := by rw [hPdef]; nlinarith
  have hP1 : P ≤ lam ^ 2 := by rw [hPdef]; nlinarith
  set a : ℝ := (1/4) * mu * t with hadef
  set b : ℝ := (1/16) * P * t ^ 3 with hbdef
  clear_value t P a b
  have hmu0 : (0:ℝ) < mu := by linarith
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have ha4 : a ≤ 1/4 := by
    rw [hadef]
    nlinarith [mul_le_mul_of_nonneg_right hmu3 ht0.le, ht1]
  have hb0 : 0 ≤ b := by
    have h := mul_nonneg hP0 (pow_pos ht0 3).le
    rw [hbdef]; linarith
  have hlt3 : lam ^ 2 * t ^ 3 = t := by linear_combination (lam * t ^ 2 + t) * ht1
  have hlt2 : lam ^ 2 * t ^ 2 = 1 := by linear_combination (lam * t + 1) * ht1
  have hbt : b ≤ t / 16 := by
    have h := mul_le_mul_of_nonneg_right hP1 (pow_pos ht0 3).le
    rw [hlt3] at h
    rw [hbdef]; linarith
  have hbub : b ≤ 1/1600 := by linarith
  have hlamb : lam * b ≤ 1/16 := by
    have h4b : lam * b = (1/16) * (P * t ^ 2) := by
      rw [hbdef]; linear_combination ((1/16) * P * t ^ 2) * ht1
    have h := mul_le_mul_of_nonneg_right hP1 (sq_nonneg t)
    rw [hlt2] at h
    rw [h4b]; linarith
  have hlamb0 : 0 ≤ lam * b := mul_nonneg hlam0.le hb0
  have hlamd : lam * d ≤ 1/20 := by
    have h := mul_le_mul_of_nonneg_left hdt hlam0.le
    have h2 : lam * (t / 20) = 1/20 := by linear_combination ht1 / 20
    linarith [h, h2.le, h2.ge]
  have hdsmall : d ≤ 1/2000 := by linarith
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hxd : |x - lam| ≤ 26/100 := by rw [abs_le]; constructor <;> linarith
  have hyd : |y - lam| ≤ 26/100 := by rw [abs_le]; constructor <;> linarith
  have hxsq : (x - lam) ^ 2 ≤ 7/100 := by
    have h := sq_le_sq' (neg_le_of_abs_le hxd) (le_of_abs_le hxd)
    nlinarith [h]
  have hysq : (y - lam) ^ 2 ≤ 7/100 := by
    have h := sq_le_sq' (neg_le_of_abs_le hyd) (le_of_abs_le hyd)
    nlinarith [h]
  have hsum1 : 2 * lam + 2 * b - 2 * d ≤ x + y := by linarith
  have hsum2 : x + y ≤ 2 * lam + 2 * b + 2 * d := by linarith
  have hls1 : lam * (2 * lam + 2 * b - 2 * d) ≤ lam * (x + y) :=
    mul_le_mul_of_nonneg_left hsum1 hlam0.le
  have hls2 : lam * (x + y) ≤ lam * (2 * lam + 2 * b + 2 * d) :=
    mul_le_mul_of_nonneg_left hsum2 hlam0.le
  have he1 : lam * (2 * lam + 2 * b - 2 * d) = 2 * lam ^ 2 + 2 * (lam * b) - 2 * (lam * d) := by
    ring
  have he2 : lam * (2 * lam + 2 * b + 2 * d) = 2 * lam ^ 2 + 2 * (lam * b) + 2 * (lam * d) := by
    ring
  rw [he1] at hls1
  rw [he2] at hls2
  have key : x ^ 2 + y ^ 2 - 2 * lam ^ 2
      = (x - lam) ^ 2 + (y - lam) ^ 2 + 2 * (lam * (x + y)) - 4 * lam ^ 2 := by ring
  refine ⟨?_, by linarith [neg_le_of_abs_le hxd], by linarith [neg_le_of_abs_le hyd]⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [key]; linarith [sq_nonneg (x - lam), sq_nonneg (y - lam)]
  · rw [key]; linarith [sq_nonneg (x - lam), sq_nonneg (y - lam)]

-- no-dlmf: the modulus of a zero matching the DLMF 7.13.1 approximations; proof infrastructure
/-- **The modulus of a point matching the DLMF 7.13.1 approximations at index `n`.**  For
`n ≥ 3400`, any `w` whose real and imaginary parts lie within the `erf713_zero_expansion` error
`(μₙ + 3)⁴/(20λₙ⁵)` of `erfZeroReApprox n`, `erfZeroImApprox n` satisfies
`|‖w‖² − 2λₙ²| ≤ 1`, together with the sector data `‖w‖ ≥ 20`, `‖w‖ ≤ 6 Re w` required by
`cerf_zero_unique_in_small_ball`.  Since consecutive grid values `2λₙ²` are `2π > 2` apart, the
first estimate *determines* the index `n` from `‖w‖`. -/
theorem erf713_approx_norm_sq {n : ℕ} (hn : 3400 ≤ n) {w : ℂ}
    (hre : |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5))
    (him : |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5)) :
    |‖w‖ ^ 2 - 2 * erfZeroLambda n ^ 2| ≤ 1 ∧ 20 ≤ ‖w‖ ∧ ‖w‖ ≤ 6 * w.re := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erf713_param_bounds hn
  have hlam0 : (0:ℝ) < erfZeroLambda n := by linarith
  have hD0 : (0:ℝ) ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) := by positivity
  have hD' : (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ≤ 1 / (20 * erfZeroLambda n) := by
    refine hD.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hnsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  obtain ⟨h1, h2, -⟩ :=
    erf713_norm_sq_aux hlam hmu5 (by linarith) hD0 hD' hre him
  have hA : |‖w‖ ^ 2 - 2 * erfZeroLambda n ^ 2| ≤ 1 := by rw [hnsq]; exact h1
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hre0 : (0:ℝ) < w.re := by linarith
  have h20 : 20 ≤ ‖w‖ := by nlinarith [norm_nonneg w]
  have hlt : ‖w‖ ^ 2 < (6 * w.re) ^ 2 := by nlinarith
  exact ⟨hA, h20, by nlinarith [norm_nonneg w, hre0.le]⟩

set_option maxHeartbeats 800000 in
-- no-dlmf: crude localization of the modulus of a solution of the third-order zero equation;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **Crude modulus localization from the index equation.**  If a first-quadrant point `w` with
`‖w‖ ≥ 20` satisfies the third-order zero equation at index `k`, then `|‖w‖² − 2πk| ≤ 5`.

Only the two component equations are used: the imaginary part gives `2xy = 2πk + O(1)`, while
the real part bounds `|x² − y²| ≤ ½ log(π‖w‖²) + o(1) ≤ √π‖w‖`, hence
`‖w‖² − 2xy = (x − y)² ≤ π + o(1)`.  The constant `5` is crude — the sharp `±1` comes later from
`erf713_approx_norm_sq` — but it already forces `k ≍ ‖w‖²/2π`, which is what is needed to feed
`erf713_zero_expansion`. -/
theorem erf713_crude_modulus {w : ℂ} (hx : 0 < w.re) (hy : 0 < w.im) (hbig : 20 ≤ ‖w‖)
    {k : ℤ} (heq : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 150 / ‖w‖ ^ 4) :
    |‖w‖ ^ 2 - 2 * Real.pi * k| ≤ 5 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hwn : (0:ℝ) < ‖w‖ := by linarith
  have hN : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN0 : (400:ℝ) ≤ w.re ^ 2 + w.im ^ 2 := by rw [← hN]; nlinarith
  have hw4 : ‖w‖ ^ 4 = (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hN]
  have hsqre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two, Complex.mul_re]
  have hsqim : (w ^ 2).im = 2 * w.re * w.im := by simp only [pow_two, Complex.mul_im]; ring
  have hnsq : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hlogre : (Complex.log ((Real.sqrt Real.pi : ℂ) * w)).re
      = (1 / 2) * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2)) := by
    have ht : (Real.sqrt Real.pi * ‖w‖) ^ 2 = Real.pi * (w.re ^ 2 + w.im ^ 2) := by
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Complex.sq_norm, hnsq]
    have h2 : Real.log ((Real.sqrt Real.pi * ‖w‖) ^ 2)
        = 2 * Real.log (Real.sqrt Real.pi * ‖w‖) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← ht, h2]
    ring
  have hlogim : (Complex.log ((Real.sqrt Real.pi : ℂ) * w)).im = Complex.arg w := by
    rw [Complex.log_im, Complex.arg_real_mul w (Real.sqrt_pos.mpr Real.pi_pos)]
  have hns2 : Complex.normSq (2 * w ^ 2) = 4 * (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h4 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
    rw [map_mul, map_pow, hnsq, h4]
  have hre2 : (2 * w ^ 2 : ℂ).re = 2 * (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.mul_re, hsqre, hsqim]; simp
  have him2 : (2 * w ^ 2 : ℂ).im = 2 * (2 * w.re * w.im) := by
    rw [Complex.mul_im, hsqre, hsqim]; simp
  have hinvre : ((1 : ℂ) / (2 * w ^ 2)).re
      = (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_re, hre2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hinvim : ((1 : ℂ) / (2 * w ^ 2)).im
      = -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_im, him2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcre : (2 * (Real.pi : ℂ) * Complex.I * (k:ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hcim : (2 * (Real.pi : ℂ) * Complex.I * (k:ℂ)).im = 2 * Real.pi * (k:ℝ) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hw4] at heq
  have hrepart : |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
      + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        ≤ 150 / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h := (Complex.abs_re_le_norm (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans heq
    simp only [Complex.sub_re, Complex.add_re, hsqre, hlogre, hinvre, hcre] at h
    calc |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        = |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 0| := by
          congr 1; ring
      _ ≤ _ := h
  have himpart : |2 * w.re * w.im + Complex.arg w
      + -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 2 * Real.pi * (k:ℝ)|
        ≤ 150 / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h := (Complex.abs_im_le_norm (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans heq
    simp only [Complex.sub_im, Complex.add_im, hsqim, hlogim, hinvim, hcim] at h
    exact h
  clear heq hsqre hsqim hlogre hlogim hns2 hre2 him2 hinvre hinvim hcre hcim hnsq hw4
  set N : ℝ := w.re ^ 2 + w.im ^ 2 with hNdef
  have hN0' : (0:ℝ) < N := by linarith
  have hNsq : (160000:ℝ) ≤ N ^ 2 := by nlinarith
  have hsmall : 150 / N ^ 2 ≤ 1/1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hNinv : 1 / (2 * N) ≤ 1/800 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hpiN : (0:ℝ) < Real.pi * N := by nlinarith
  have hL0 : (0:ℝ) ≤ 1 / 2 * Real.log (Real.pi * N) := by
    have h1 : (1:ℝ) ≤ Real.pi * N := by nlinarith
    linarith [Real.log_nonneg h1]
  have hsp : Real.sqrt Real.pi ≤ 1.7725 := by
    have h : Real.sqrt Real.pi ≤ Real.sqrt (1.7725 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.7725)] at h
  have hspnn : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hLub : 1 / 2 * Real.log (Real.pi * N) ≤ Real.sqrt Real.pi * ‖w‖ := by
    have hsq1 : Real.log (Real.sqrt (Real.pi * N)) ≤ Real.sqrt (Real.pi * N) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpiN)
    have hsq2 : Real.log (Real.sqrt (Real.pi * N)) = Real.log (Real.pi * N) / 2 :=
      Real.log_sqrt hpiN.le
    have hsq3 : Real.sqrt (Real.pi * N) = Real.sqrt Real.pi * ‖w‖ := by
      rw [Real.sqrt_mul Real.pi_pos.le, ← hN, Real.sqrt_sq (norm_nonneg w)]
    rw [hsq2, hsq3] at hsq1
    linarith
  have hAle : |w.re ^ 2 - w.im ^ 2| ≤ N := by
    rw [abs_le, hNdef]
    constructor <;> nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hinvA : |(w.re ^ 2 - w.im ^ 2) / (2 * N ^ 2)| ≤ 1 / (2 * N) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hAle, abs_nonneg (w.re ^ 2 - w.im ^ 2)]
  have hA : |w.re ^ 2 - w.im ^ 2| ≤ Real.sqrt Real.pi * ‖w‖ + 1/400 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hrepart
    obtain ⟨h3, h4⟩ := abs_le.mp hinvA
    rw [abs_le]
    constructor <;> linarith
  have hxysum : ‖w‖ ≤ w.re + w.im := by
    nlinarith [hN, mul_pos hx hy, norm_nonneg w, sq_nonneg (w.re + w.im - ‖w‖)]
  have hfac : |w.re ^ 2 - w.im ^ 2| = |w.re - w.im| * (w.re + w.im) := by
    rw [show w.re ^ 2 - w.im ^ 2 = (w.re - w.im) * (w.re + w.im) by ring, abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < w.re + w.im)]
  have hdiffabs : |w.re - w.im| * ‖w‖ ≤ |w.re ^ 2 - w.im ^ 2| := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hxysum (abs_nonneg _)
  have hd1 : |w.re - w.im| ≤ Real.sqrt Real.pi + 1/4000 := by
    nlinarith [hdiffabs, hA, abs_nonneg (w.re - w.im)]
  have hsqd : (w.re - w.im) ^ 2 ≤ 3.15 := by
    have h0 : (0:ℝ) ≤ |w.re - w.im| := abs_nonneg _
    have hsq := mul_self_le_mul_self h0 hd1
    rw [abs_mul_abs_self] at hsq
    have hpisq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
      Real.mul_self_sqrt Real.pi_pos.le
    nlinarith [hsq, hpisq, hsp, hspnn]
  have harg : |Complex.arg w| ≤ Real.pi / 2 :=
    (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)).le
  have hxyt : |-(2 * w.re * w.im) / (2 * N ^ 2)| ≤ 1 / (2 * N) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |-(2 * w.re * w.im)| = 2 * w.re * w.im := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [h1, hNdef]
    nlinarith [sq_nonneg (w.re - w.im), mul_pos hx hy]
  have himb : |2 * w.re * w.im - 2 * Real.pi * (k:ℝ)| ≤ 158/100 := by
    obtain ⟨h1, h2⟩ := abs_le.mp himpart
    obtain ⟨h3, h4⟩ := abs_le.mp hxyt
    obtain ⟨h5, h6⟩ := abs_le.mp harg
    rw [abs_le]
    constructor <;> linarith
  have hNxy : N - 2 * w.re * w.im = (w.re - w.im) ^ 2 := by rw [hNdef]; ring
  obtain ⟨h1, h2⟩ := abs_le.mp himb
  rw [hN, abs_le]
  constructor <;> linarith [hsqd, hNxy, sq_nonneg (w.re - w.im)]

-- no-dlmf: passage from the third-order zero equation at a known index to the DLMF 7.13.1
-- approximations; proof infrastructure for the §7.13 zero asymptotics
/-- **Matching a solution of the index-`n` equation to the DLMF approximations.**  For `n ≥ 3400`
a first-quadrant point `w` with `‖w‖ ≥ 20` satisfying the third-order zero equation *at index `n`*
lies within `(μₙ + 3)⁴/(20 λₙ⁵)` of `(erfZeroReApprox n, erfZeroImApprox n)`.

This is `erf713_zero_expansion` with its hypothesis `ε ≤ 40/λₙ⁴` discharged: the crude modulus
bound `|‖w‖² − 2πn| ≤ 5` of `erf713_crude_modulus` gives `‖w‖² ≥ 1.94 λₙ²`, hence
`‖w‖⁴ ≥ 3.75 λₙ⁴` and `150/‖w‖⁴ ≤ 40/λₙ⁴`. -/
theorem erf713_zero_match {n : ℕ} (hn : 3400 ≤ n) {w : ℂ} (hx : 0 < w.re) (hy : 0 < w.im)
    (hbig : 20 ≤ ‖w‖)
    (heq : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ 150 / ‖w‖ ^ 4) :
    |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ∧
      |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erf713_param_bounds hn
  have hlam0 : (0:ℝ) < erfZeroLambda n := by linarith
  have hn1 : 1 ≤ n := by omega
  have hlamsq := erf713_lambda_sq hn1
  have heq' : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * ((n:ℤ):ℂ)‖ ≤ 150 / ‖w‖ ^ 4 := by
    push_cast
    exact heq
  have hcm := erf713_crude_modulus hx hy hbig heq'
  have hcast : (((n:ℤ)):ℝ) = (n:ℝ) := by push_cast; ring
  rw [hcast] at hcm
  have h2pin : 2 * Real.pi * (n:ℝ) = 2 * erfZeroLambda n ^ 2 + Real.pi / 4 := by
    rw [hlamsq]; ring
  rw [h2pin] at hcm
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcm
  have hlow : 1.94 * erfZeroLambda n ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [Real.pi_pos, hlam]
  have hw4eq : ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 := by ring
  have hquart : 3.75 * erfZeroLambda n ^ 4 ≤ ‖w‖ ^ 4 := by
    rw [hw4eq]; nlinarith [hlow, hlam0]
  have hwpos : (0:ℝ) < ‖w‖ := by linarith
  have hw40 : (0:ℝ) < ‖w‖ ^ 4 := by positivity
  have heb : 150 / ‖w‖ ^ 4 ≤ 40 / erfZeroLambda n ^ 4 := by
    rw [div_le_div_iff₀ hw40 (by positivity)]
    nlinarith [hquart]
  exact erf713_zero_expansion hn hx hy heb heq

set_option maxHeartbeats 1000000 in
-- no-dlmf: existence of a zero of `cerf` matching the DLMF 7.13.1 approximations at each large
-- index; proof infrastructure for the §7.13 zero asymptotics
/-- **The grid zero at index `n`.**  For every `n ≥ 3400` there is a first-quadrant zero of `erf`
whose coordinates match `erfZeroReApprox n`, `erfZeroImApprox n` to within
`(μₙ + 3)⁴/(20 λₙ⁵)`.

The zero is the one produced near the `n`-th model root `v` by `exists_cerf_zero_near_model`.
The only new work is *index pinning*: the integer `k` supplied by
`cerf_zero_log_equation_third` at that zero must be `n`, because `v² + log(√π v) = 2πi n`
exactly while `‖w − v‖ < 12/‖v‖³` moves `z ↦ z² + log(√π z) + 1/(2z²)` by less than `1 ≪ 2π`
(the three contributions `‖w² − v²‖ ≤ ρ(2‖v‖ + ρ)`, the mean-value bound on the logarithm, and
`1/(2‖w‖²)` are each `≤ 1/100` for `‖v‖ ≥ 100`). -/
theorem erf713_grid_zero (n : ℕ) (hn : 3400 ≤ n) :
    ∃ w : ℂ, cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧
      |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ∧
      |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  obtain ⟨v, hvn, hvre6, hvim6, hvloc, hvlog, hvmodel⟩ := exists_model_root n (by omega)
  have h2pin : ‖2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ = 2 * Real.pi * (n:ℝ) := by
    have hid : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n:ℂ)
        = ((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hid, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hVbig : (100:ℝ) ≤ ‖v‖ := by
    have h1 := norm_sub_norm_le (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (v ^ 2)
    rw [h2pin, norm_pow,
      norm_sub_rev (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (v ^ 2)] at h1
    nlinarith [hvloc, h1, norm_nonneg v]
  have hV0 : (0:ℝ) < ‖v‖ := by linarith
  have hre1 : (1:ℝ) ≤ v.re := by linarith
  obtain ⟨w, hw, hwb⟩ := exists_cerf_zero_near_model hre1 (by linarith) hvmodel
  set V : ℝ := ‖v‖ with hVdef
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; positivity
  have hV2 : (10000:ℝ) ≤ V ^ 2 := by nlinarith
  have hV2' : 100 * V ≤ V ^ 2 := by nlinarith
  have hV3 : (1000000:ℝ) ≤ V ^ 3 := by nlinarith
  have hV3' : 100 * V ^ 2 ≤ V ^ 3 := by nlinarith
  have hρsmall : ρ ≤ 1/1000 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hwv : ‖w - v‖ ≤ ρ := le_of_lt hwb
  have hmemball : ∀ z ∈ Metric.closedBall v ρ, 0 < z.re ∧ V - ρ ≤ ‖z‖ := by
    intro z hz
    have hzv : ‖z - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - v)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hzv)
    have h2 := norm_sub_norm_le v z
    rw [norm_sub_rev v z] at h2
    exact ⟨by linarith [h1.1], by linarith⟩
  have hwcb : w ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwv
  obtain ⟨hx, hwlow⟩ := hmemball w hwcb
  have hwim : |w.im - v.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (w - v)
    simp only [Complex.sub_im] at h; linarith
  have hy : 0 < w.im := by
    have h := abs_le.mp hwim; linarith [h.1]
  have hwn2 : ‖w‖ ≤ V + ρ := by
    have h := norm_sub_norm_le w v
    linarith
  have hbigw : (20:ℝ) ≤ ‖w‖ := by linarith
  have hwsq : (400:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hwqu : (160000:ℝ) ≤ ‖w‖ ^ 4 := by nlinarith [hwsq]
  obtain ⟨k, hk⟩ := cerf_zero_log_equation_third hw hx (by linarith : (4:ℝ) ≤ ‖w‖)
  have hkn : k = (n:ℤ) := by
    by_contra hne
    have hlogmvt : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
        - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ ≤ (1 / (V - ρ)) * ‖w - v‖ := by
      refine norm_sub_le_of_hasDerivAt_le
        (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
        (convex_closedBall v ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hwcb
      · intro z hz
        obtain ⟨hz1, hz2⟩ := hmemball z hz
        have hslit : ((Real.sqrt Real.pi : ℂ)) * z ∈ Complex.slitPlane := by
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          positivity
        have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
            ((Real.sqrt Real.pi : ℂ)) z := by
          simpa using (hasDerivAt_id z).const_mul ((Real.sqrt Real.pi : ℂ))
        exact h1.clog hslit
      · intro z hz
        obtain ⟨hz1, hz2⟩ := hmemball z hz
        have hzn : (0:ℝ) < ‖z‖ := by linarith
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
          div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith [hz2, hsppos]
    have hid : 2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))
        = (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
             - 2 * (Real.pi : ℂ) * Complex.I * (k:ℂ))
          - ((w ^ 2 - v ^ 2)
             + (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * v))
             + 1 / (2 * w ^ 2)) := by
      linear_combination -hvlog
    have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
    have hqn : ‖(1:ℂ) / (2 * w ^ 2)‖ = 1 / (2 * ‖w‖ ^ 2) := by
      rw [norm_div, norm_one, norm_mul, norm_pow]; norm_num
    have hp3 : ‖(1:ℂ) / (2 * w ^ 2)‖ ≤ 1/100 := by
      rw [hqn, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hp1 : ‖w ^ 2 - v ^ 2‖ ≤ 1/100 := by
      have hfac : w ^ 2 - v ^ 2 = (w - v) * (w + v) := by ring
      have h1 : ‖w + v‖ ≤ 2 * V + ρ := by
        have h := norm_add_le w v; linarith
      have h2 : ‖w ^ 2 - v ^ 2‖ ≤ ρ * (2 * V + ρ) := by
        rw [hfac, norm_mul]
        exact mul_le_mul hwv h1 (norm_nonneg _) hρ0.le
      have hb1 : ρ * (2 * V + ρ) ≤ ρ * (2 * V + 1) := by nlinarith
      have hb2 : ρ * (2 * V + 1) ≤ 1/100 := by
        rw [hρdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hp2 : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
        - Complex.log ((Real.sqrt Real.pi : ℂ) * v)‖ ≤ 1/100 := by
      have h1 : 1 / (V - ρ) ≤ 1/99 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h2 : (1 / (V - ρ)) * ‖w - v‖ ≤ (1/99) * (1/1000) := by
        refine mul_le_mul h1 (by linarith) (norm_nonneg _) (by norm_num)
      linarith
    have hA1 : 150 / ‖w‖ ^ 4 ≤ 1/1000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hub : ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ ≤ 1 := by
      rw [hid]
      have hsec : ‖(w ^ 2 - v ^ 2)
             + (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * v))
             + 1 / (2 * w ^ 2)‖ ≤ 3/100 := by
        refine (norm_add_le _ _).trans ?_
        have := norm_add_le (w ^ 2 - v ^ 2) (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * v))
        linarith
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hlb : (6:ℝ) ≤ ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ := by
      have hne' : ((n:ℤ) - k) ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
      have habs : (1:ℤ) ≤ |(n:ℤ) - k| := Int.one_le_abs hne'
      have hm : ((n:ℂ) - (k:ℂ)) = (((n:ℤ) - k : ℤ) : ℂ) := by push_cast; ring
      rw [hm, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((((n:ℤ) - k : ℤ)) : ℂ)
          = ((2 * Real.pi * ((((n:ℤ) - k : ℤ)) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hcast1 : (1:ℝ) ≤ |((((n:ℤ) - k : ℤ)) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast habs
      nlinarith [hcast1]
    linarith
  rw [hkn] at hk
  have hk' : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ ≤ 150 / ‖w‖ ^ 4 := by
    push_cast at hk
    exact hk
  obtain ⟨hr, hi⟩ := erf713_zero_match hn hx hy hbigw hk'
  exact ⟨w, hw, hx, hy, hr, hi⟩

-- no-dlmf: a fourth-root bound for the DLMF 7.13.2 parameter `μ`; proof infrastructure
/-- **A fourth-root bound for `μ`.**  For `n ≥ 3400`, `(μₙ + 3)⁴ ≤ 1296 λₙ`.

Iterating `log x ≤ 2(√x − 1)` twice gives `μ ≤ 4(⁴√(λ√(2π)) − 1) ≤ 4√2·⁴√λ`, and `⁴√λ ≥ 3`, so
`μ + 3 ≤ 6·⁴√λ`.  This is the estimate that makes the `erf713_zero_expansion` error
`(μ + 3)⁴/(20λ⁵) ≤ 65/λ⁴` genuinely `o(λ⁻³)`; the cruder `μ + 3 ≤ λ/2` of `erf713_param_bounds`
would only give `O(λ⁻¹)`. -/
theorem erf713_mu_quartic {n : ℕ} (hn : 3400 ≤ n) :
    (erfZeroMu n + 3) ^ 4 ≤ 1296 * erfZeroLambda n := by
  obtain ⟨hlam, hmu5, -, -⟩ := erf713_param_bounds hn
  have hlam0 : (0:ℝ) < erfZeroLambda n := by linarith
  set lam : ℝ := erfZeroLambda n with hlamdef
  set mu : ℝ := erfZeroMu n with hmudef
  have hmuval : mu = Real.log (lam * Real.sqrt (2 * Real.pi)) := rfl
  clear_value lam mu
  set s : ℝ := Real.sqrt (Real.sqrt lam) with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hlam0)
  have hs4 : s ^ 4 = lam := by
    rw [hsdef, show (Real.sqrt (Real.sqrt lam)) ^ 4
      = ((Real.sqrt (Real.sqrt lam)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg lam), Real.sq_sqrt hlam0.le]
  have hs3 : 3 ≤ s := by
    by_contra hcon
    have hlt : s < 3 := not_le.mp hcon
    have h1 : s ^ 2 < 9 := by nlinarith [hs0]
    have hsq : s ^ 4 = (s ^ 2) ^ 2 := by ring
    have h2 : s ^ 4 < 81 := by rw [hsq]; nlinarith [h1, sq_nonneg s]
    linarith [hs4, hlam]
  have hsnn : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hsq2pi : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hub : Real.sqrt (2 * Real.pi) ≤ 4 := by nlinarith [Real.pi_lt_four]
  have hX0 : (0:ℝ) < lam * Real.sqrt (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have h1 : Real.log (Real.sqrt (Real.sqrt (lam * Real.sqrt (2 * Real.pi))))
      ≤ Real.sqrt (Real.sqrt (lam * Real.sqrt (2 * Real.pi))) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX0))
  have h2 : Real.log (Real.sqrt (Real.sqrt (lam * Real.sqrt (2 * Real.pi))))
      = Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi))) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.log (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
      = Real.log (lam * Real.sqrt (2 * Real.pi)) / 2 :=
    Real.log_sqrt hX0.le
  have hb : Real.sqrt (Real.sqrt (lam * Real.sqrt (2 * Real.pi))) ≤ Real.sqrt 2 * s := by
    have hu1 : lam * Real.sqrt (2 * Real.pi) ≤ 4 * lam := by nlinarith
    have hu2 : Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ 2 * Real.sqrt lam := by
      have hq : Real.sqrt (4 * lam) = 2 * Real.sqrt lam := by
        rw [show (4:ℝ) * lam = 2 ^ 2 * lam by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      calc Real.sqrt (lam * Real.sqrt (2 * Real.pi)) ≤ Real.sqrt (4 * lam) :=
            Real.sqrt_le_sqrt hu1
        _ = 2 * Real.sqrt lam := hq
    have hu3 : Real.sqrt (Real.sqrt (lam * Real.sqrt (2 * Real.pi)))
        ≤ Real.sqrt (2 * Real.sqrt lam) := Real.sqrt_le_sqrt hu2
    have hu4 : Real.sqrt (2 * Real.sqrt lam) = Real.sqrt 2 * s := by
      rw [hsdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hu3, hu4.le, hu4.ge]
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.415 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.415)] at h
  have hmub : mu + 3 ≤ 6 * s := by
    rw [hmuval]
    have hs2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [h1, h2, h3, hb, hsqrt2, hs3, hs0]
  have hmu0 : (0:ℝ) ≤ mu + 3 := by linarith
  calc (mu + 3) ^ 4 ≤ (6 * s) ^ 4 := by gcongr
    _ = 1296 * lam := by rw [← hs4]; ring

-- no-dlmf: local uniqueness of the zero attached to an index; proof infrastructure
/-- **At most one zero per index.**  Two zeros of `erf` both matching the DLMF 7.13.1
approximations at the same index `n ≥ 3400` coincide.

Both lie within `2·(μₙ+3)⁴/(20λₙ⁵) ≤ 1/(160λₙ)` of the same point, hence within
`1/(24‖w‖)` of each other (`‖w‖ ≤ 1.5λₙ` by `erf713_approx_norm_sq`), and
`cerf_zero_unique_in_small_ball` applies with centre `w`. -/
theorem erf713_zero_index_unique {n : ℕ} (hn : 3400 ≤ n) {w w' : ℂ}
    (hw : cerf w = 0) (hw' : cerf w' = 0)
    (hre : |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5))
    (him : |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5))
    (hre' : |w'.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5))
    (him' : |w'.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5)) :
    w = w' := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erf713_param_bounds hn
  have hlam0 : (0:ℝ) < erfZeroLambda n := by linarith
  obtain ⟨hA, h20, h6⟩ := erf713_approx_norm_sq hn hre him
  have hw0 : (0:ℝ) < ‖w‖ := by linarith
  set D : ℝ := (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) with hDdef
  have hD0 : (0:ℝ) ≤ D := by rw [hDdef]; positivity
  have hdist : ‖w' - w‖ ≤ 4 * D := by
    have h := Complex.norm_le_abs_re_add_abs_im (w' - w)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |w'.re - w.re| ≤ 2 * D := by
      obtain ⟨a1, a2⟩ := abs_le.mp hre
      obtain ⟨b1, b2⟩ := abs_le.mp hre'
      rw [abs_le]; constructor <;> linarith
    have h2 : |w'.im - w.im| ≤ 2 * D := by
      obtain ⟨a1, a2⟩ := abs_le.mp him
      obtain ⟨b1, b2⟩ := abs_le.mp him'
      rw [abs_le]; constructor <;> linarith
    linarith
  have hwle : ‖w‖ ≤ 1.5 * erfZeroLambda n := by
    obtain ⟨hA1, hA2⟩ := abs_le.mp hA
    nlinarith [norm_nonneg w]
  have hDw : D * ‖w‖ ≤ (1 / (320 * erfZeroLambda n)) * (1.5 * erfZeroLambda n) :=
    mul_le_mul hD hwle (norm_nonneg w) (by positivity)
  have hval : (1 / (320 * erfZeroLambda n)) * (1.5 * erfZeroLambda n) = 1.5 / 320 := by
    field_simp
  rw [hval] at hDw
  have hfin : 4 * D ≤ 1 / (24 * ‖w‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hDw]
  exact cerf_zero_unique_in_small_ball h6 h20 hw hw' (by simp) (by linarith [hdist])

-- no-dlmf: every large first-quadrant zero carries an index; proof infrastructure
/-- **Every large first-quadrant zero has an index.**  A zero of `erf` in the open first
quadrant with `‖w‖² ≥ 21987` matches the DLMF 7.13.1 approximations at some index `n ≥ 3500`.

The integer `k` of `cerf_zero_log_equation_third` satisfies `2πk ≥ ‖w‖² − 5 ≥ 21982`, so
`k ≥ 3499 ≥ 3400` and `erf713_zero_match` applies; the sharp bound `|‖w‖² − 2λₖ²| ≤ 1` of
`erf713_approx_norm_sq` then excludes `k = 3499`, because `2λ₃₄₉₉² + 1 < 21987`. -/
theorem erf713_zero_has_index {w : ℂ} (hw : cerf w = 0) (hx : 0 < w.re) (hy : 0 < w.im)
    (hbig : 21987 ≤ ‖w‖ ^ 2) :
    ∃ n : ℕ, 3500 ≤ n ∧
      |w.re - erfZeroReApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) ∧
      |w.im - erfZeroImApprox n| ≤ (erfZeroMu n + 3) ^ 4 / (20 * erfZeroLambda n ^ 5) := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hw20 : (20:ℝ) ≤ ‖w‖ := by nlinarith [norm_nonneg w]
  obtain ⟨k, hk⟩ := cerf_zero_log_equation_third hw hx (by linarith)
  have hcm := erf713_crude_modulus hx hy hw20 hk
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcm
  have hkbig : (3499:ℤ) ≤ k := by
    have hr : (3498:ℝ) < (k:ℝ) := by nlinarith
    have h : (3498:ℤ) < k := by exact_mod_cast hr
    omega
  have hk0 : (0:ℤ) ≤ k := by omega
  set n : ℕ := k.toNat with hndef
  have hkn : (n:ℤ) = k := Int.toNat_of_nonneg hk0
  have hn3499 : 3499 ≤ n := by omega
  have hcast : ((n:ℕ):ℂ) = ((k:ℤ):ℂ) := by rw [← hkn]; push_cast; ring
  have hk' : ‖w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ ≤ 150 / ‖w‖ ^ 4 := by
    rw [hcast]; exact hk
  obtain ⟨hr, hi⟩ := erf713_zero_match (by omega) hx hy hw20 hk'
  obtain ⟨hA, -, -⟩ := erf713_approx_norm_sq (by omega) hr hi
  refine ⟨n, ?_, hr, hi⟩
  by_contra hlt
  have hnle : (n:ℝ) ≤ 3499 := by
    have h : n ≤ 3499 := by omega
    exact_mod_cast h
  have hlamsq := erf713_lambda_sq (n := n) (by omega)
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hnpos : (0:ℝ) ≤ (n:ℝ) - 1/8 := by
    have h : (3499:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3499
    linarith
  have hprod : ((n:ℝ) - 1/8) * Real.pi ≤ 3498.875 * 3.141593 := by
    nlinarith [hpi2, hnle, hnpos, Real.pi_pos]
  nlinarith [hA2, hlamsq, hprod, hbig]

-- no-dlmf: conjugate reflection of the entire function `cerf`; proof infrastructure for the
-- §7.13 erfc zero asymptotics, not a numbered DLMF display
/-- **Conjugate reflection of `erf`.**  `erf (conj z) = conj (erf z)`.

The defining integral `erf z = (2/√π) z ∫₀¹ e^{−(tz)²} dt` has real coefficients and is taken
over a real segment, so conjugation passes through it. -/
theorem cerf_conj (z : ℂ) : cerf (starRingEnd ℂ z) = starRingEnd ℂ (cerf z) := by
  rw [cerf, cerf, map_mul, map_mul]
  congr 1
  · congr 1
    simp [Complex.ext_iff]
  · rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ← integral_conj]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]

/-! ## The count of the small first-quadrant zeros of `erf`

The argument-principle computation behind `erf713_low_zero_count` below.  The Klein symmetry
group `{1, −1, conj, −conj}` of `cerf` turns the first-quadrant count into a full-disc count on
the circle `‖z‖ = R = √21987`, and folds the circle integral of `cerf'/cerf` back onto the
quarter arc; on that arc `cerf` is compared with the elementary model `M = 1 − u`,
`u(z) = e^{−z²}/(√π z)`, whose logarithmic-derivative integral is closed form.  The only
special-function input is the already-proven remainder bound `cerfc_poincare_bound`, and the
whole computation bottoms out in one explicit real inequality, `erf713_modelPsi_bounds`. -/

section Erf713ZeroCount

open Complex MeasureTheory Set FLMF.Methods

/-! ### The two boundary-ray nonvanishing facts

The two coordinate axes carry no zero of `cerf` other than the origin.  Together with oddness and conjugation symmetry they
are what forces every nonzero zero into an *open* quadrant, hence into a 4-element
Klein orbit. -/

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S3.**  `cerf` does not vanish on the punctured real axis: for real `x ≠ 0`,
`cerf x = erf x ≠ 0` because the real `erf` is strictly monotone with `erf 0 = 0`. -/
theorem cerf_ne_zero_of_ne_zero_real {x : ℝ} (hx : x ≠ 0) : cerf (x : ℂ) ≠ 0 := by
  rw [cerf_ofReal]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro h
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have := FLMF.Error.strictMono_erf hneg
    rw [FLMF.Error.erf_zero, h] at this
    exact lt_irrefl 0 this
  · have := FLMF.Error.strictMono_erf hpos
    rw [FLMF.Error.erf_zero, h] at this
    exact lt_irrefl 0 this

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- The `cerf` integrand at a purely imaginary argument is a positive real cast:
`exp (−(t·(y·I))²) = ↑(exp (t²y²))`. -/
theorem cerf_integrand_imAxis (y t : ℝ) :
    Complex.exp (-((t : ℂ) * ((y : ℂ) * I)) ^ 2) = ((Real.exp (t ^ 2 * y ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  have : ((t : ℂ) * ((y : ℂ) * I)) ^ 2 = -((t : ℂ) ^ 2 * (y : ℂ) ^ 2) := by
    rw [mul_pow, mul_pow, Complex.I_sq]; ring
  rw [this]
  push_cast
  ring

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S4, integral form.**  On the imaginary axis `cerf` is `i` times a positive
real multiple of `y`:  `cerf (y·I) = (2/√π) · (y·I) · ↑(∫₀¹ e^{t²y²} dt)`. -/
theorem cerf_imAxis (y : ℝ) :
    cerf ((y : ℂ) * I)
      = (2 / Real.sqrt Real.pi : ℂ) * ((y : ℂ) * I)
          * ((∫ t in (0:ℝ)..1, Real.exp (t ^ 2 * y ^ 2) : ℝ) : ℂ) := by
  unfold cerf
  congr 1
  rw [intervalIntegral.integral_congr
    (g := fun t : ℝ => ((Real.exp (t ^ 2 * y ^ 2) : ℝ) : ℂ))
    (fun t _ => cerf_integrand_imAxis y t)]
  rw [intervalIntegral.integral_ofReal]

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S4.**  For `y > 0` the value `cerf (y·I)` is purely imaginary with strictly
positive imaginary part; in particular `cerf (y·I) ≠ 0`.  (This is the exact
statement that the imaginary edge carries `arg ≡ π/2`.) -/
theorem cerf_imAxis_im_pos {y : ℝ} (hy : 0 < y) :
    (cerf ((y : ℂ) * I)).re = 0 ∧ 0 < (cerf ((y : ℂ) * I)).im := by
  have hK : 0 < ∫ t in (0:ℝ)..1, Real.exp (t ^ 2 * y ^ 2) := by
    have : (0:ℝ) < ∫ t in (0:ℝ)..1, (1:ℝ) := by norm_num
    refine lt_of_lt_of_le this ?_
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact intervalIntegrable_const
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · intro t _
      have : (0:ℝ) ≤ t ^ 2 * y ^ 2 := by positivity
      simpa using Real.one_le_exp this
  have hsp : 0 < 2 / Real.sqrt Real.pi := by positivity
  rw [cerf_imAxis]
  constructor
  · simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  · have : ((2 / Real.sqrt Real.pi : ℝ) : ℂ) * ((y : ℂ) * I)
        * ((∫ t in (0:ℝ)..1, Real.exp (t ^ 2 * y ^ 2) : ℝ) : ℂ)
        = (((2 / Real.sqrt Real.pi) * y * (∫ t in (0:ℝ)..1, Real.exp (t ^ 2 * y ^ 2)) : ℝ) : ℂ)
            * I := by
      push_cast; ring
    rw [show ((2:ℂ) / (Real.sqrt Real.pi : ℂ)) = ((2 / Real.sqrt Real.pi : ℝ) : ℂ) by
      push_cast; ring, this]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    positivity

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S5.**  Every zero of `cerf` is simple: the derivative `(2/√π)·e^{−z²}` never
vanishes.  (Stated as the nonvanishing of the derivative; the upgrade to
`analyticOrderNatAt cerf w = 1` is `analyticOrderAt_eq_one_iff`-style bookkeeping.) -/
theorem deriv_cerf_ne_zero (z : ℂ) : deriv cerf z ≠ 0 := by
  rw [(hasDerivAt_cerf z).deriv]
  have h1 : (2 / Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, Complex.ofReal_eq_zero]
    push_neg
    refine ⟨by norm_num, ?_⟩
    exact_mod_cast Real.sqrt_ne_zero'.mpr Real.pi_pos
  exact mul_ne_zero h1 (Complex.exp_ne_zero _)

/-! ### The arc contour vocabulary

The counting radius, the arc parametrization, the elementary model `u`, and the
explicit (branch-free!) antiderivative `Λ` of `u'/u` along the arc. -/

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The counting radius for the `erf` family: `R = √21987`. -/
def erf713Rad : ℝ := Real.sqrt 21987

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713Rad_pos : 0 < erf713Rad := Real.sqrt_pos.mpr (by norm_num)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713Rad_sq : erf713Rad ^ 2 = 21987 := Real.sq_sqrt (by norm_num)

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The elementary model factor `u(z) = e^{−z²}/(√π z)`.  `cerfc = (1 + E)·u` with
`‖E‖ ≤ 4/‖z‖²` on the closed right half-plane (`cerfc_scaled_unit_bound`). -/
def erf713ModelU (z : ℂ) : ℂ := Complex.exp (-z ^ 2) / ((Real.sqrt Real.pi : ℂ) * z)

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The model for `cerf` on the arc: `M = 1 − u`. -/
def erf713ModelM (z : ℂ) : ℂ := 1 - erf713ModelU z

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The **branch-free** antiderivative of `θ ↦ (u'/u)(arcPoint erf713Rad θ)·(i·arcPoint erf713Rad θ)`:
`Λ(θ) = −R² e^{2iθ} − log(√π R) − iθ`.  Its imaginary part `−R² sin 2θ − θ` is the
continuous argument of `u` along the arc; because `Λ` is defined directly (not as a
branch of `log u`), the many windings of `u` cost nothing. -/
def erf713BigLambda (θ : ℝ) : ℂ :=
  -((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * I)
    - ((Real.log (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) - ((θ : ℝ) : ℂ) * I

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_bigLambda_im (θ : ℝ) : (erf713BigLambda θ).im = -(erf713Rad ^ 2 * Real.sin (2 * θ)) - θ := by
  have hexp : Complex.exp (((2 * θ : ℝ) : ℂ) * I)
      = ((Real.cos (2 * θ) : ℝ) : ℂ) + ((Real.sin (2 * θ) : ℝ) : ℂ) * I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [erf713BigLambda, hexp]
  simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.neg_im, Complex.neg_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re]
  ring

/-! ### Mechanical support lemmas for `W1` and `S6/S7`

Parity of `deriv cerf` under negation/conjugation, the arc's `circleMap` identity and
its two symmetries, conjugation through an interval integral, and the "no zero on the
counting circle" fact `S7`. -/

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- `cerf` is entire, hence analytic at every point. -/
theorem analyticAt_cerf (z : ℂ) : AnalyticAt ℂ cerf z :=
  differentiable_cerf.differentiableOn.analyticAt Filter.univ_mem

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- `deriv cerf` is even: `cerf'(-z) = cerf'(z)`. Immediate from the explicit closed
form `cerf' z = (2/√π)e^{-z²}` (`hasDerivAt_cerf`), since `(-z)² = z²`. -/
theorem deriv_cerf_neg (z : ℂ) : deriv cerf (-z) = deriv cerf z := by
  rw [(hasDerivAt_cerf (-z)).deriv, (hasDerivAt_cerf z).deriv]
  ring_nf

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- `deriv cerf` is conjugation-equivariant: `cerf'(z̄) = conj(cerf'(z))`. Immediate
from the explicit closed form (real prefactor `2/√π`, and `exp` commutes with `conj`). -/
theorem deriv_cerf_conj (z : ℂ) :
    deriv cerf (starRingEnd ℂ z) = starRingEnd ℂ (deriv cerf z) := by
  rw [(hasDerivAt_cerf (starRingEnd ℂ z)).deriv, (hasDerivAt_cerf z).deriv]
  have hc : starRingEnd ℂ ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2))
      = (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-(starRingEnd ℂ z) ^ 2) := by
    rw [map_mul]
    congr 1
    · rw [show ((2:ℂ) / (Real.sqrt Real.pi : ℂ)) = ((2 / Real.sqrt Real.pi : ℝ) : ℂ) by
        push_cast; ring]
      exact Complex.conj_ofReal _
    · rw [← Complex.exp_conj]
      congr 1
      rw [map_neg, map_pow]
  exact hc.symm

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S3+S4, axis case.** `cerf` does not vanish anywhere on either coordinate axis
except at the origin. -/
theorem cerf_ne_zero_of_on_axis {z : ℂ} (hz0 : z ≠ 0) (hax : z.re = 0 ∨ z.im = 0) :
    cerf z ≠ 0 := by
  rcases hax with hre0 | him0
  · have hyne : z.im ≠ 0 := fun h => hz0 (Complex.ext hre0 h)
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · intro hzero
      have h1 := (cerf_imAxis_im_pos (y := -z.im) (by linarith)).2
      have heq : ((-z.im : ℝ) : ℂ) * I = -z := by
        apply Complex.ext
        · simp [hre0]
        · simp
      rw [heq, cerf_neg, hzero, neg_zero] at h1
      exact lt_irrefl 0 h1
    · intro hzero
      have h1 := (cerf_imAxis_im_pos (y := z.im) hpos).2
      have heq : ((z.im : ℝ) : ℂ) * I = z := by
        apply Complex.ext
        · simp [hre0]
        · simp
      rw [heq, hzero] at h1
      exact lt_irrefl 0 h1
  · have hxz : ((z.re : ℝ) : ℂ) = z := by
      apply Complex.ext
      · simp
      · simp [him0]
    have hre0 : z.re ≠ 0 := fun h => hz0 (Complex.ext h him0)
    intro hzero
    rw [← hxz] at hzero
    exact cerf_ne_zero_of_ne_zero_real hre0 hzero

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S7, first-quadrant case.** No first-quadrant zero of `cerf` sits exactly on the
counting circle `‖w‖ = erf713Rad`.

Content: `erf713_zero_has_index` forces the index `n ≥ 3500`; `erf713_approx_norm_sq`
+ `erf713_lambda_sq` then force `‖w‖² ≥ 2λₙ² − 1 > 21988 > 21987 = Rad²`,
contradicting `‖w‖ = erf713Rad`. -/
theorem cerf_Q1_ne_zero_on_circle {w : ℂ} (hre : 0 < w.re) (him : 0 < w.im)
    (hnorm : ‖w‖ = erf713Rad) : cerf w ≠ 0 := by
  intro hzero
  have hnormsq : ‖w‖ ^ 2 = 21987 := by rw [hnorm]; exact erf713Rad_sq
  obtain ⟨n, hn3500, hr, hi⟩ := erf713_zero_has_index hzero hre him hnormsq.ge
  have hn3400 : 3400 ≤ n := by omega
  obtain ⟨hA, -, -⟩ := erf713_approx_norm_sq hn3400 hr hi
  obtain ⟨hA1, -⟩ := abs_le.mp hA
  have hlam := erf713_lambda_sq (n := n) (by omega)
  have hpi := Real.pi_gt_d6
  have hnR : (3500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3500
  have hlow : (3499.875 : ℝ) * 3.141592 < erfZeroLambda n ^ 2 := by
    rw [hlam]
    calc (3499.875 : ℝ) * 3.141592 < 3499.875 * Real.pi := by
          apply mul_lt_mul_of_pos_left hpi (by norm_num)
      _ ≤ ((n : ℝ) - 1 / 8) * Real.pi := by
          apply mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
  nlinarith [hnormsq, hA1, hlow]

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- **S7.** No zero of `cerf` sits exactly on the counting circle `‖z‖ = erf713Rad`,
anywhere in `ℂ`: reduce the axis cases to `cerf_ne_zero_of_on_axis` and the four
open-quadrant cases to `cerf_Q1_ne_zero_on_circle` via `cerf_neg`/`cerf_conj`. -/
theorem cerf_ne_zero_on_circle {z : ℂ} (hz : ‖z‖ = erf713Rad) : cerf z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact erf713Rad_pos.ne' hz.symm
  rcases eq_or_ne z.re 0 with hre0 | hre0
  · exact cerf_ne_zero_of_on_axis hz0 (Or.inl hre0)
  rcases eq_or_ne z.im 0 with him0 | him0
  · exact cerf_ne_zero_of_on_axis hz0 (Or.inr him0)
  rcases lt_or_gt_of_ne hre0 with hreN | hreP <;> rcases lt_or_gt_of_ne him0 with himN | himP
  · -- re < 0, im < 0 : reduce via w := -z
    have hw := cerf_Q1_ne_zero_on_circle (w := -z)
      (by rw [Complex.neg_re]; exact neg_pos.mpr hreN)
      (by rw [Complex.neg_im]; exact neg_pos.mpr himN)
      (by rw [norm_neg]; exact hz)
    exact fun hzero => hw (by rw [cerf_neg, hzero, neg_zero])
  · -- re < 0, im > 0 : reduce via w := -(conj z)
    have hw := cerf_Q1_ne_zero_on_circle (w := -(starRingEnd ℂ z))
      (by rw [Complex.neg_re, Complex.conj_re]; exact neg_pos.mpr hreN)
      (by rw [Complex.neg_im, Complex.conj_im]; simpa using himP)
      (by rw [norm_neg, Complex.norm_conj]; exact hz)
    exact fun hzero => hw (by rw [cerf_neg, cerf_conj, hzero]; simp)
  · -- re > 0, im < 0 : reduce via w := conj z
    have hw := cerf_Q1_ne_zero_on_circle (w := starRingEnd ℂ z)
      (by rw [Complex.conj_re]; exact hreP)
      (by rw [Complex.conj_im]; exact neg_pos.mpr himN)
      (by rw [Complex.norm_conj]; exact hz)
    exact fun hzero => hw (by rw [cerf_conj, hzero]; simp)
  · exact cerf_Q1_ne_zero_on_circle hreP himP hz

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **W1 — the symmetry reduction.**  The two symmetries `g(−z) = −g(z)` (oddness of `cerf`) and
`g(z̄) = conj (g z)` (conjugation symmetry) reduce the full circle integral of
`g = cerf'/cerf` to four times `i` times the imaginary part of the quarter-arc
integral:  `h(θ) := g(arcPoint erf713Rad θ)·(i·arcPoint erf713Rad θ)` is `π`-periodic and satisfies
`h(−θ) = −conj (h θ)`, so `∮ = 2∫₀^π h = 2(J − conj J) = 4i·Im J`.

Proof: two `intervalIntegral` changes of variable plus `intervalIntegral_conj`. -/
theorem erf713_circle_eq_four_I_arc_im :
    (∮ z in C((0:ℂ), erf713Rad), deriv cerf z / cerf z)
      = 4 * I * (((arcLogDerivIntegral cerf erf713Rad 0 (Real.pi / 2)).im : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun θ => deriv cerf (arcPoint erf713Rad θ) / cerf (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) with hhdef
  have hne : ∀ θ : ℝ, cerf (arcPoint erf713Rad θ) ≠ 0 := fun θ => cerf_ne_zero_on_circle (norm_arcPoint erf713Rad_pos.le θ)
  have hstep1 : (∮ z in C((0:ℂ), erf713Rad), deriv cerf z / cerf z) = arcLogDerivIntegral cerf erf713Rad 0 (2 * Real.pi) := by
    unfold circleIntegral arcLogDerivIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, ← arcPoint_eq_circleMap, smul_eq_mul]
    ring
  rw [hstep1]
  show (∫ θ in (0:ℝ)..(2 * Real.pi), h θ)
      = 4 * I * (((∫ θ in (0:ℝ)..(Real.pi / 2), h θ).im : ℝ) : ℂ)
  have hderiv_eq : deriv cerf = fun z => (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2) :=
    funext (fun z => (hasDerivAt_cerf z).deriv)
  have hcont_dcerf : Continuous (deriv cerf) := by rw [hderiv_eq]; fun_prop
  have hcont_cerf : Continuous cerf := differentiable_cerf.continuous
  have hcont_h : Continuous h := by
    have h1 : Continuous (fun θ => deriv cerf (arcPoint erf713Rad θ)) := hcont_dcerf.comp (continuous_arcPoint erf713Rad)
    have h2 : Continuous (fun θ => cerf (arcPoint erf713Rad θ)) := hcont_cerf.comp (continuous_arcPoint erf713Rad)
    have h3 : Continuous (fun θ => I * arcPoint erf713Rad θ) := continuous_const.mul (continuous_arcPoint erf713Rad)
    exact (h1.div h2 hne).mul h3
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hcont_h.intervalIntegrable a b
  have hper : ∀ θ : ℝ, h (θ + Real.pi) = h θ := by
    intro θ
    have hnz := hne θ
    simp only [hhdef]
    rw [arcPoint_add_pi erf713Rad, deriv_cerf_neg, cerf_neg]
    field_simp
  have hconjrel : ∀ θ : ℝ, h (-θ) = - starRingEnd ℂ (h θ) := by
    intro θ
    simp only [hhdef]
    rw [arcPoint_neg erf713Rad, deriv_cerf_conj, cerf_conj, map_mul, map_mul, map_div₀,
      show starRingEnd ℂ I = -I from Complex.conj_I]
    ring
  have hsplit1 : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ)
      = (∫ θ in (0:ℝ)..Real.pi, h θ) + ∫ θ in Real.pi..(2 * Real.pi), h θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 Real.pi)
      (hint Real.pi (2 * Real.pi))).symm
  have hshift : (∫ θ in Real.pi..(2 * Real.pi), h θ) = ∫ θ in (0:ℝ)..Real.pi, h θ := by
    have hc := intervalIntegral.integral_comp_add_right h Real.pi (a := (0:ℝ)) (b := Real.pi)
    rw [show (0:ℝ) + Real.pi = Real.pi by ring, show Real.pi + Real.pi = 2 * Real.pi by ring] at hc
    rw [← hc]
    exact intervalIntegral.integral_congr (fun x _ => hper x)
  have heq2π : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ) = 2 * ∫ θ in (0:ℝ)..Real.pi, h θ := by
    rw [hsplit1, hshift]; ring
  set J : ℂ := ∫ θ in (0:ℝ)..(Real.pi / 2), h θ with hJdef
  have hsplitπ : (∫ θ in (0:ℝ)..Real.pi, h θ) = J + ∫ θ in (Real.pi / 2)..Real.pi, h θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 (Real.pi / 2))
      (hint (Real.pi / 2) Real.pi)).symm
  have hstep : ∀ x : ℝ, h (Real.pi - x) = - starRingEnd ℂ (h x) := by
    intro x
    rw [show Real.pi - x = -x + Real.pi by ring, hper (-x)]
    exact hconjrel x
  have hhalf : (∫ θ in (Real.pi / 2)..Real.pi, h θ) = - starRingEnd ℂ J := by
    have hsub := intervalIntegral.integral_comp_sub_left h (a := (0:ℝ)) (b := Real.pi / 2)
      (d := Real.pi)
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
      show Real.pi - (0:ℝ) = Real.pi by ring] at hsub
    rw [← hsub, intervalIntegral.integral_congr (fun x _ => hstep x),
      intervalIntegral.integral_neg, intervalIntegral_conj (hint 0 (Real.pi / 2)), hJdef]
  have hπsum : (∫ θ in (0:ℝ)..Real.pi, h θ) = J - starRingEnd ℂ J := by
    rw [hsplitπ, hhalf]; ring
  have hfinal : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ) = 2 * (J - starRingEnd ℂ J) := by
    rw [heq2π, hπsum]
  rw [hfinal]
  have hJIm : J - starRingEnd ℂ J = 2 * I * (((J.im : ℝ) : ℂ)) := by
    rw [Complex.sub_conj]
    push_cast
    ring
  rw [hJIm]
  ring

/-! ### A1 — the polar form of the model on the arc, and `|M| ≥ 1/2`

`u(R e^{iθ}) = t(θ)·e^{−i(R² sin 2θ + θ)}` with `t(θ) = e^{−R² cos 2θ}/(√π R)`.
So `log t = −(R² cos 2θ + L)` and `arg u = −(R² sin 2θ + θ)`, and the two branches of
the sufficient condition of `erf713_modelM_norm_ge` read off directly. -/

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- `L = log (√π R) = ½ log (21987 π)`, the constant appearing in `erf713BigLambda`. -/
def erf713BigL : ℝ := Real.log (Real.sqrt Real.pi * erf713Rad)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_sqrtPi_Rad_pos : 0 < Real.sqrt Real.pi * erf713Rad :=
  mul_pos (Real.sqrt_pos.mpr Real.pi_pos) erf713Rad_pos

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `L = ½ log (21987 π)` — the constant of `erf713_modelPsi_bounds`. -/
theorem erf713_bigL_eq : erf713BigL = Real.log (21987 * Real.pi) / 2 := by
  have h : Real.sqrt Real.pi * erf713Rad = Real.sqrt (Real.pi * 21987) := by
    rw [erf713Rad, ← Real.sqrt_mul Real.pi_pos.le]
  rw [erf713BigL, h, Real.log_sqrt (by positivity), mul_comm Real.pi 21987]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- Crude enclosure `0 < L < 6` (numerically `L = 5.5718`). -/
theorem erf713_bigL_bounds : 0 < erf713BigL ∧ erf713BigL < 6 := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  rw [erf713_bigL_eq]
  constructor
  · have h1 : (1 : ℝ) < 21987 * Real.pi := by nlinarith
    linarith [Real.log_pos h1]
  · have hexp12 : (69075 : ℝ) < Real.exp 12 := by
      have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have h2 : (2.7 : ℝ) ^ (12 : ℕ) < (Real.exp 1) ^ (12 : ℕ) :=
        pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
      have h3 : (Real.exp 1) ^ (12 : ℕ) = Real.exp 12 := by
        rw [← Real.exp_nat_mul]; norm_num
      calc (69075 : ℝ) < (2.7 : ℝ) ^ (12 : ℕ) := by norm_num
        _ < (Real.exp 1) ^ (12 : ℕ) := h2
        _ = Real.exp 12 := h3
    have harg : (0 : ℝ) < 21987 * Real.pi := by nlinarith
    have hlt : 21987 * Real.pi < Real.exp 12 := by nlinarith
    linarith [(Real.log_lt_iff_lt_exp harg).mpr hlt]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **Polar form of the model on the arc.**
`u(R e^{iθ}) = (e^{−R² cos 2θ}/(√π R)) · e^{−i(R² sin 2θ + θ)}`. -/
theorem erf713_modelU_arcPt (θ : ℝ) :
    erf713ModelU (arcPoint erf713Rad θ)
      = ((Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ)
          * Complex.exp (((-(erf713Rad ^ 2 * Real.sin (2 * θ) + θ) : ℝ) : ℂ) * I) := by
  have hsr : ((Real.sqrt Real.pi * erf713Rad : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast erf713_sqrtPi_Rad_pos.ne'
  have hexpne : Complex.exp ((θ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  -- the square of the arc point, in rectangular form
  have hsq : -(arcPoint erf713Rad θ) ^ 2
      = ((-(erf713Rad ^ 2 * Real.cos (2 * θ)) : ℝ) : ℂ)
          + ((-(erf713Rad ^ 2 * Real.sin (2 * θ)) : ℝ) : ℂ) * I := by
    have h2 : Complex.exp ((θ : ℂ) * I) ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [arcPoint, mul_pow, h2, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hsqexp : Complex.exp (-(arcPoint erf713Rad θ) ^ 2)
      = ((Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) : ℝ) : ℂ)
          * Complex.exp (((-(erf713Rad ^ 2 * Real.sin (2 * θ)) : ℝ) : ℂ) * I) := by
    rw [hsq, Complex.exp_add, ← Complex.ofReal_exp]
  -- split the phase factor `e^{-i(B+θ)} = e^{-iB}·(e^{iθ})⁻¹`
  have hsplit : Complex.exp (((-(erf713Rad ^ 2 * Real.sin (2 * θ) + θ) : ℝ) : ℂ) * I)
      = Complex.exp (((-(erf713Rad ^ 2 * Real.sin (2 * θ)) : ℝ) : ℂ) * I)
          * (Complex.exp ((θ : ℂ) * I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [erf713ModelU, hsqexp, hsplit]
  rw [show arcPoint erf713Rad θ = (erf713Rad : ℂ) * Complex.exp ((θ : ℂ) * I) from rfl]
  push_cast
  field_simp

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- The modulus of the model factor on the arc. -/
theorem erf713_modelU_arcPt_norm (θ : ℝ) :
    ‖erf713ModelU (arcPoint erf713Rad θ)‖ = Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) / (Real.sqrt Real.pi * erf713Rad) := by
  have hpos : 0 < Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) / (Real.sqrt Real.pi * erf713Rad) :=
    div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
  rw [erf713_modelU_arcPt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- The real part of the model factor on the arc: `|u|·cos (R² sin 2θ + θ)`. -/
theorem erf713_modelU_arcPt_re (θ : ℝ) :
    (erf713ModelU (arcPoint erf713Rad θ)).re
      = Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) / (Real.sqrt Real.pi * erf713Rad)
          * Real.cos (erf713Rad ^ 2 * Real.sin (2 * θ) + θ) := by
  rw [erf713_modelU_arcPt, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_im, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
  rw [Real.cos_neg]
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **A1 — the one genuine computation.**  `|M| ≥ 1/2` on the closed
quarter arc.

Proof by the sufficient condition, in the two branches
`|R² cos 2θ + L| ≥ log 2` (modulus far from `1`) and `< log 2` (phase in the left
half-plane):

* If `|log |u|| = |R² cos 2θ + L| ≥ log 2` then `|u| ≤ 1/2` or `|u| ≥ 2`, so
  `|1 − u| ≥ | 1 − |u| | ≥ 1/2`.
* Otherwise `R²|cos 2θ| < L + log 2 < 6.7`, hence (with `sin 2θ ≥ 0` on the quarter
  arc) `R² sin 2θ ≥ R²(1 − cos²2θ) ≥ 21987 − 45/21987 > 21986.9979`, so
  `Ψ(θ) = R² sin 2θ + θ ∈ [21986.9979, 21987 + π/2]`, which lies inside
  `[2π·3499 + π/2, 2π·3499 + 3π/2]` — margins `0.56` and `1.00`.  Therefore
  `cos Ψ(θ) ≤ 0`, so `Re u ≤ 0` and `|1 − u| ≥ |1 − Re u| ≥ 1`. -/
theorem erf713_modelM_norm_ge {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    (1 : ℝ) / 2 ≤ ‖erf713ModelM (arcPoint erf713Rad θ)‖ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hLpos, hLlt⟩ := erf713_bigL_bounds
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsr : 0 < Real.sqrt Real.pi * erf713Rad := erf713_sqrtPi_Rad_pos
  have hRsq : erf713Rad ^ 2 = 21987 := erf713Rad_sq
  set c : ℝ := Real.cos (2 * θ) with hc
  set s : ℝ := Real.sin (2 * θ) with hs
  set t : ℝ := Real.exp (-(erf713Rad ^ 2 * c)) / (Real.sqrt Real.pi * erf713Rad) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos (Real.exp_pos _) hsr
  have hnorm : ‖erf713ModelU (arcPoint erf713Rad θ)‖ = t := erf713_modelU_arcPt_norm θ
  have hre : (erf713ModelU (arcPoint erf713Rad θ)).re = t * Real.cos (erf713Rad ^ 2 * s + θ) := erf713_modelU_arcPt_re θ
  by_cases hcase : Real.log 2 ≤ |erf713Rad ^ 2 * c + erf713BigL|
  · -- modulus branch: `|u| ≤ 1/2` or `|u| ≥ 2`
    have hlogt : Real.log t = -(erf713Rad ^ 2 * c + erf713BigL) := by
      rw [htdef, Real.log_div (Real.exp_ne_zero _) hsr.ne', Real.log_exp, erf713BigL]
      ring
    have hsplit : t ≤ 1 / 2 ∨ 2 ≤ t := by
      rcases le_abs.mp hcase with h | h
      · left
        have hle : Real.log t ≤ Real.log (1 / 2) := by
          rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, hlogt]; linarith
        exact (Real.log_le_log_iff htpos (by norm_num)).mp hle
      · right
        have hle : Real.log 2 ≤ Real.log t := by rw [hlogt]; linarith
        exact (Real.log_le_log_iff (by norm_num) htpos).mp hle
    have hkey : (1 : ℝ) / 2 ≤ |1 - t| := by
      rcases hsplit with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    calc (1 : ℝ) / 2 ≤ |1 - t| := hkey
      _ = |‖(1 : ℂ)‖ - ‖erf713ModelU (arcPoint erf713Rad θ)‖| := by rw [hnorm, norm_one]
      _ ≤ ‖(1 : ℂ) - erf713ModelU (arcPoint erf713Rad θ)‖ := abs_norm_sub_norm_le _ _
      _ = ‖erf713ModelM (arcPoint erf713Rad θ)‖ := by rw [erf713ModelM]
  · -- phase branch: `Ψ(θ)` sits in the left half-period, so `Re u ≤ 0`
    push_neg at hcase
    have hlog2 : Real.log 2 < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hb : |erf713Rad ^ 2 * c + erf713BigL| < 0.694 := lt_trans hcase hlog2
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
    have hsq2 : (erf713Rad ^ 2 * c) ^ 2 < 45 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < erf713Rad ^ 2 * c + 6.7)
        (by linarith : (0:ℝ) < 0.7 - erf713Rad ^ 2 * c)]
    have hsnn : 0 ≤ s := by
      rw [hs]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hpy : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq _
    have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
    have hslow : 1 - c ^ 2 ≤ s := by nlinarith
    have hRs : (21986.9979 : ℝ) ≤ erf713Rad ^ 2 * s := by
      have h1 : erf713Rad ^ 2 * (1 - c ^ 2) ≤ erf713Rad ^ 2 * s := by
        apply mul_le_mul_of_nonneg_left hslow
        rw [hRsq]; norm_num
      have h2 : erf713Rad ^ 2 * (1 - c ^ 2) = 21987 - (erf713Rad ^ 2 * c) ^ 2 / 21987 := by
        rw [hRsq]; ring
      rw [h2] at h1
      linarith
    have hΨhi : erf713Rad ^ 2 * s ≤ 21987 := by rw [hRsq]; linarith
    have hcosnp : Real.cos (erf713Rad ^ 2 * s + θ) ≤ 0 := by
      rw [← Real.cos_sub_int_mul_two_pi _ (3499 : ℤ)]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · push_cast; linarith
      · push_cast; linarith
    have hrenp : (erf713ModelU (arcPoint erf713Rad θ)).re ≤ 0 := by
      rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos htpos.le hcosnp
    have hMre : (erf713ModelM (arcPoint erf713Rad θ)).re = 1 - (erf713ModelU (arcPoint erf713Rad θ)).re := by
      rw [erf713ModelM]; simp
    have h1 : |(erf713ModelM (arcPoint erf713Rad θ)).re| ≤ ‖erf713ModelM (arcPoint erf713Rad θ)‖ := Complex.abs_re_le_norm _
    rw [hMre, abs_of_nonneg (by linarith)] at h1
    linarith

/-! The two remainder bounds of `ComplexZeros.lean` are stated there with the *open*
hypothesis `0 < w.re`, but their proof only ever uses `|arg w| ≤ 3π/4 − δ`; the
`δ = π/4` instance therefore holds on the CLOSED right half-plane, which is what the
quarter arc needs at its endpoint `θ = π/2`.  These are verbatim re-runs of the
production proofs with `0 < w.re` weakened to `w ≠ 0 ∧ |arg w| ≤ π/2`. -/

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_cerfc_scaled_leading_bound_closed {w : ℂ} (hw : w ≠ 0)
    (hsec : |Complex.arg w| ≤ Real.pi / 2) :
    ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹‖ ≤ 4 / ‖w‖ ^ 3 := by
  have hsec' : |Complex.arg w| ≤ 3 * Real.pi / 4 - Real.pi / 4 := by linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 4) (by positivity)
    (by linarith [Real.pi_pos]) hw hsec' 1
  have hsin : Real.sin (2 * (Real.pi / 4) / 3) = 1 / 2 := by
    rw [show 2 * (Real.pi / 4) / 3 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hsin] at h
  simp only [Finset.sum_range_one] at h
  norm_num at h
  convert h using 2
  ring_nf

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_cerfc_scaled_unit_bound_closed {w : ℂ} (hw : w ≠ 0)
    (hsec : |Complex.arg w| ≤ Real.pi / 2) :
    ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerfc w - 1‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h := erf713_cerfc_scaled_leading_bound_closed hw hsec
  have hid : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerfc w - 1
      = w * ((Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹) := by
    field_simp
  rw [hid, norm_mul]
  calc ‖w‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹‖
      ≤ ‖w‖ * (4 / ‖w‖ ^ 3) := mul_le_mul_of_nonneg_left h hwn.le
    _ = 4 / ‖w‖ ^ 2 := by field_simp

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **A2.**  `|u| ≤ 4·|M|` on the closed quarter arc. -/
theorem erf713_modelU_le_four_modelM {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    ‖erf713ModelU (arcPoint erf713Rad θ)‖ ≤ 4 * ‖erf713ModelM (arcPoint erf713Rad θ)‖ := by
  have hM : (1 : ℝ) / 2 ≤ ‖erf713ModelM (arcPoint erf713Rad θ)‖ := erf713_modelM_norm_ge hθ
  rcases le_total (‖erf713ModelU (arcPoint erf713Rad θ)‖) 2 with h | h
  · linarith
  · have hge : ‖erf713ModelU (arcPoint erf713Rad θ)‖ - ‖(1 : ℂ)‖ ≤ ‖erf713ModelU (arcPoint erf713Rad θ) - 1‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, ← norm_neg (erf713ModelU (arcPoint erf713Rad θ) - 1)] at hge
    have : -(erf713ModelU (arcPoint erf713Rad θ) - 1) = erf713ModelM (arcPoint erf713Rad θ) := by rw [erf713ModelM]; ring
    rw [this] at hge
    linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **A3.**  On the closed quarter arc the ratio `cerf/M` lies in
`ball 1 (1/2)`: `cerf = M − u·E` with `‖E‖ ≤ 4/R²`, so
`‖cerf/M − 1‖ = ‖u‖‖E‖/‖M‖ ≤ 4·(4/21987) = 16/21987 ≈ 7.3e-4`. -/
theorem erf713_ratio_mem_ball {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) ∈ ball (1 : ℂ) (1 / 2) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hzne : arcPoint erf713Rad θ ≠ 0 := arcPoint_ne_zero erf713Rad_pos.ne' θ
  have hznorm : ‖arcPoint erf713Rad θ‖ = erf713Rad := norm_arcPoint erf713Rad_pos.le θ
  have hRsq : erf713Rad ^ 2 = 21987 := erf713Rad_sq
  have hsec : |Complex.arg (arcPoint erf713Rad θ)| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff, arcPoint_re erf713Rad]
    exact mul_nonneg erf713Rad_pos.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ1⟩)
  have hM : (1 : ℝ) / 2 ≤ ‖erf713ModelM (arcPoint erf713Rad θ)‖ := erf713_modelM_norm_ge ⟨hθ0, hθ1⟩
  have hMpos : 0 < ‖erf713ModelM (arcPoint erf713Rad θ)‖ := by linarith
  have hMne : erf713ModelM (arcPoint erf713Rad θ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hMpos; exact lt_irrefl 0 hMpos
  have hπne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ * Complex.exp (arcPoint erf713Rad θ ^ 2)
      * cerfc (arcPoint erf713Rad θ) - 1 with hEdef
  have hEb : ‖E‖ ≤ 4 / 21987 := by
    have := erf713_cerfc_scaled_unit_bound_closed hzne hsec
    rw [hznorm, hRsq] at this
    exact this
  -- `cerf = M − u·E` (both `u·√π z e^{z²} = 1` and `cerfc = 1 − cerf`)
  have hu : erf713ModelU (arcPoint erf713Rad θ)
      * ((Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ * Complex.exp (arcPoint erf713Rad θ ^ 2)) = 1 := by
    rw [erf713ModelU]
    field_simp
    rw [← Complex.exp_add]
    simp
  have hfac : cerf (arcPoint erf713Rad θ) = erf713ModelM (arcPoint erf713Rad θ) - erf713ModelU (arcPoint erf713Rad θ) * E := by
    have hrw : erf713ModelM (arcPoint erf713Rad θ) - erf713ModelU (arcPoint erf713Rad θ) * E
        = 1 - (erf713ModelU (arcPoint erf713Rad θ)
            * ((Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ * Complex.exp (arcPoint erf713Rad θ ^ 2)))
              * cerfc (arcPoint erf713Rad θ) := by
      rw [erf713ModelM, hEdef]; ring
    rw [hrw, hu, one_mul]
    simp only [cerfc]
    ring
  have hid : cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) - 1
      = -(erf713ModelU (arcPoint erf713Rad θ) * E / erf713ModelM (arcPoint erf713Rad θ)) := by
    rw [hfac]
    field_simp
    ring
  have hU4 : ‖erf713ModelU (arcPoint erf713Rad θ)‖ ≤ 4 * ‖erf713ModelM (arcPoint erf713Rad θ)‖ :=
    erf713_modelU_le_four_modelM ⟨hθ0, hθ1⟩
  rw [Metric.mem_ball, Complex.dist_eq, hid, norm_neg, norm_div, norm_mul,
    div_lt_iff₀ hMpos]
  nlinarith [norm_nonneg E, norm_nonneg (erf713ModelU (arcPoint erf713Rad θ)), hEb, hU4, hMpos]

/-! ### The two arc endpoints

`θ = 0` and `θ = π/2` are the only places where the model and the true function are
compared by *value* rather than by increment, and they are what makes the final
integer come out exactly.  Both endpoints are computed here in closed form. -/

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713Rad_ge : (148 : ℝ) ≤ erf713Rad := by
  rw [erf713Rad, show (148:ℝ) = Real.sqrt (148 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_one_lt_sqrtPi_Rad : (1 : ℝ) < Real.sqrt Real.pi * erf713Rad := by
  have h1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  nlinarith [erf713Rad_ge]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `u` at the real endpoint is a real number in `(0, 1)`. -/
theorem erf713_modelU_zero :
    erf713ModelU (arcPoint erf713Rad 0) = ((Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) := by
  rw [erf713_modelU_arcPt]
  norm_num

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_modelU_zero_lt_one : Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) < 1 := by
  have h1 : Real.exp (-(erf713Rad ^ 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [erf713Rad_ge]
  have h2 : (1 : ℝ) < Real.sqrt Real.pi * erf713Rad := erf713_one_lt_sqrtPi_Rad
  rw [div_lt_one (by linarith)]
  linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `u` at the imaginary endpoint: `u(iR) = −i·e^{R²}/(√π R)`. -/
theorem erf713_modelU_pi_div_two :
    erf713ModelU (arcPoint erf713Rad (Real.pi / 2))
      = -(((Real.exp (erf713Rad ^ 2) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) * I) := by
  rw [erf713_modelU_arcPt, show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, Real.sin_pi,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The tiny cancellation constant `c = √π R e^{−R²} = 1/|u(iR)|` (numerically `1e-9549`). -/
def erf713TinyC : ℝ := Real.sqrt Real.pi * erf713Rad * Real.exp (-(erf713Rad ^ 2))

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_tinyC_pos : 0 < erf713TinyC := by
  rw [erf713TinyC]; exact mul_pos erf713_sqrtPi_Rad_pos (Real.exp_pos _)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `arg (1 − i c) = −arctan c`. -/
theorem erf713_arg_one_sub_mul_I (c : ℝ) :
    Complex.arg (1 - (c : ℂ) * I) = -Real.arctan c := by
  have hr : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hrne : ((Real.sqrt (1 + c ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcos : Real.cos (-Real.arctan c) = 1 / Real.sqrt (1 + c ^ 2) := by
    rw [Real.cos_neg, Real.cos_arctan]
  have hsin : Real.sin (-Real.arctan c) = -(c / Real.sqrt (1 + c ^ 2)) := by
    rw [Real.sin_neg, Real.sin_arctan]
  have hfac : (1 : ℂ) - (c : ℂ) * I
      = ((Real.sqrt (1 + c ^ 2) : ℝ) : ℂ)
          * (((Real.cos (-Real.arctan c) : ℝ) : ℂ)
              + ((Real.sin (-Real.arctan c) : ℝ) : ℂ) * I) := by
    rw [hcos, hsin]
    push_cast
    field_simp
    ring
  have hmem : -Real.arctan c ∈ Set.Ioc (-Real.pi) Real.pi := by
    have h1 := Real.arctan_lt_pi_div_two c
    have h2 := Real.neg_pi_div_two_lt_arctan c
    have h3 := Real.pi_pos
    exact ⟨by linarith, by linarith⟩
  rw [hfac, Complex.arg_real_mul _ hr, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I hmem]

/-! ### The branch-free antiderivative (the crux of the model computation)

`Λ` is *defined* directly, not as a branch of `log u`, so the ~3500 windings of `u`
along the arc cost nothing.  What has to be checked is that it really is an
antiderivative of the arc-pulled-back logarithmic derivative of `u`. -/

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `u' = u·(−2z − 1/z)`, i.e. `u'/u = −2z − 1/z`. -/
theorem erf713_hasDerivAt_modelU {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt erf713ModelU (erf713ModelU z * (-2 * z - z⁻¹)) z := by
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1 : HasDerivAt (fun w : ℂ => -w ^ 2) (-(2 * z)) z := by
    simpa using (hasDerivAt_pow 2 z).neg
  have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-w ^ 2))
      (Complex.exp (-z ^ 2) * -(2 * z)) z :=
    (Complex.hasDerivAt_exp (-z ^ 2)).comp z h1
  have hden : HasDerivAt (fun w : ℂ => (Real.sqrt Real.pi : ℂ) * w)
      ((Real.sqrt Real.pi : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul ((Real.sqrt Real.pi : ℂ))
  have hd := hnum.div hden (mul_ne_zero hπ hz)
  convert hd using 1
  rw [erf713ModelU]
  field_simp

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **`Λ` is an antiderivative of `θ ↦ (u'/u)(R e^{iθ})·(i R e^{iθ})`** — branch-free.
Concretely `(u'/u)(z)·(iz) = i(−2z² − 1) = −2i R² e^{2iθ} − i = Λ'(θ)`. -/
theorem erf713_bigLambda_hasDerivAt (θ : ℝ) :
    HasDerivAt erf713BigLambda
      (deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) θ := by
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hz : arcPoint erf713Rad θ ≠ 0 := arcPoint_ne_zero erf713Rad_pos.ne' θ
  have hune : erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := by
    rw [erf713ModelU]; exact div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hπ hz)
  have hexp2 : Complex.exp ((θ : ℂ) * I) ^ 2 = Complex.exp (2 * (θ : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  -- the target derivative in closed form
  have hz2 : (arcPoint erf713Rad θ) ^ 2 = ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) := by
    rw [show arcPoint erf713Rad θ = (erf713Rad : ℂ) * Complex.exp ((θ : ℂ) * I) from rfl, mul_pow, hexp2]
    push_cast
    rfl
  have htarget : deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
      = -2 * I * ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) - I := by
    rw [(erf713_hasDerivAt_modelU hz).deriv, mul_div_cancel_left₀ _ hune]
    have hexpand : (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹) * (I * arcPoint erf713Rad θ)
        = -2 * I * (arcPoint erf713Rad θ) ^ 2 - I := by
      field_simp
    rw [hexpand, hz2]
    ring
  rw [htarget]
  -- `erf713BigLambda` as the restriction of an entire function to the real line
  have hEq : erf713BigLambda = fun y : ℝ =>
      (-((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (y : ℂ) * I)
        - ((Real.log (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) - (y : ℂ) * I) := by
    funext y
    rw [erf713BigLambda]
    push_cast
    ring_nf
  rw [hEq]
  have h1 : HasDerivAt (fun w : ℂ => 2 * w * I) (2 * I) (θ : ℂ) := by
    simpa using ((hasDerivAt_id ((θ : ℂ))).const_mul (2 : ℂ)).mul_const I
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (2 * w * I))
      (Complex.exp (2 * (θ : ℂ) * I) * (2 * I)) (θ : ℂ) :=
    (Complex.hasDerivAt_exp (2 * (θ : ℂ) * I)).comp (θ : ℂ) h1
  have h3 := (h2.const_mul (-((erf713Rad ^ 2 : ℝ) : ℂ))).sub_const
    ((Real.log (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ)
  have h4 : HasDerivAt (fun w : ℂ => w * I) I (θ : ℂ) := by
    simpa using (hasDerivAt_id ((θ : ℂ))).mul_const I
  have hF := h3.sub h4
  have := hF.comp_ofReal
  convert this using 1
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **The `θ*` endpoint identity:** `arg (1 − e^{iφ}) = φ/2 − π/2` for
`φ ∈ (0, 2π)`.  (`1 − e^{iφ} = 2 sin(φ/2)·e^{i(φ/2 − π/2)}` with `sin(φ/2) > 0`.)
This is what produces both `arg M(θ*)` and `−arg k(θ*)` in the closed form. -/
theorem erf713_arg_one_sub_exp_mul_I {φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2 * Real.pi) :
    Complex.arg (1 - Complex.exp ((φ : ℂ) * I)) = φ / 2 - Real.pi / 2 := by
  have hs : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : Real.cos (φ / 2 - Real.pi / 2) = Real.sin (φ / 2) := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsn : Real.sin (φ / 2 - Real.pi / 2) = -Real.cos (φ / 2) := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcosφ : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    have hpy := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    linarith
  have hsinφ : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have h := Real.sin_two_mul (φ / 2)
    rwa [show 2 * (φ / 2) = φ by ring] at h
  have hfac : (1 : ℂ) - Complex.exp ((φ : ℂ) * I)
      = ((2 * Real.sin (φ / 2) : ℝ) : ℂ)
          * (((Real.cos (φ / 2 - Real.pi / 2) : ℝ) : ℂ)
              + ((Real.sin (φ / 2 - Real.pi / 2) : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn,
      hcosφ, hsinφ]
    push_cast
    ring
  have hmem : φ / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hpi := Real.pi_pos
    exact ⟨by linarith, by linarith⟩
  rw [hfac, Complex.arg_real_mul _ (by linarith), Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I hmem]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **Endpoint `θ = 0`.**  `h(0) = cerf(R)/M(R)` is a *positive real*: `cerf R = erf R > 0`
and `M(R) = 1 − e^{−R²}/(√π R) ∈ (0,1)`.  Hence `arg h(0) = 0`. -/
theorem erf713_ratio_arg_zero : Complex.arg (cerf (arcPoint erf713Rad 0) / erf713ModelM (arcPoint erf713Rad 0)) = 0 := by
  have herf : 0 < FLMF.Error.erf erf713Rad := by
    have h := FLMF.Error.strictMono_erf erf713Rad_pos
    rwa [FLMF.Error.erf_zero] at h
  have hc : cerf (arcPoint erf713Rad 0) = ((FLMF.Error.erf erf713Rad : ℝ) : ℂ) := by
    rw [arcPoint_zero erf713Rad, cerf_ofReal]
  have hM : erf713ModelM (arcPoint erf713Rad 0)
      = ((1 - Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) := by
    rw [erf713ModelM, erf713_modelU_zero]; push_cast; ring
  have hMpos : 0 < 1 - Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) := by
    linarith [erf713_modelU_zero_lt_one]
  rw [hc, hM, ← Complex.ofReal_div]
  exact Complex.arg_ofReal_of_nonneg (div_nonneg herf.le hMpos.le)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **Endpoint `θ = π/2` — the exact cancellation.**
`cerf(iR) = i·a` with `a > 0` (`cerf_imAxis_im_pos`) and `M(iR) = 1 + i b` with
`b = e^{R²}/(√π R)`; since `b·c = 1` for `c = erf713TinyC = √π R e^{−R²}`,
`M(iR) = (i b)·(1 − i c)`, so `h(π/2) = (a/b)·(1 − i c)⁻¹` and
`arg h(π/2) = arctan c` — exactly minus the `arg k(π/2)` that `erf713_modelArc_im` carries. -/
theorem erf713_ratio_arg_pi_div_two :
    Complex.arg (cerf (arcPoint erf713Rad (Real.pi / 2)) / erf713ModelM (arcPoint erf713Rad (Real.pi / 2)))
      = Real.arctan erf713TinyC := by
  obtain ⟨hre, him⟩ := cerf_imAxis_im_pos erf713Rad_pos
  set a : ℝ := (cerf ((erf713Rad : ℂ) * I)).im with ha
  set b : ℝ := Real.exp (erf713Rad ^ 2) / (Real.sqrt Real.pi * erf713Rad) with hb
  have hbpos : 0 < b := div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
  have hRne : erf713Rad ≠ 0 := erf713Rad_pos.ne'
  have hexp1 : Real.exp (erf713Rad ^ 2) * Real.exp (-(erf713Rad ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hbc : b * erf713TinyC = 1 := by
    rw [hb, erf713TinyC]
    field_simp
    linear_combination hexp1
  have hbc' : ((b : ℝ) : ℂ) * ((erf713TinyC : ℝ) : ℂ) = 1 := by exact_mod_cast hbc
  have hcerf : cerf (arcPoint erf713Rad (Real.pi / 2)) = ((a : ℝ) : ℂ) * I := by
    rw [arcPoint_pi_div_two erf713Rad]
    apply Complex.ext <;> simp [ha, hre]
  have hM : erf713ModelM (arcPoint erf713Rad (Real.pi / 2))
      = (((b : ℝ) : ℂ) * I) * (1 - ((erf713TinyC : ℝ) : ℂ) * I) := by
    rw [erf713ModelM, erf713_modelU_pi_div_two]
    linear_combination (-1 : ℂ) * hbc' + (((b : ℝ) : ℂ) * ((erf713TinyC : ℝ) : ℂ)) * Complex.I_sq
  have hkne : (1 : ℂ) - ((erf713TinyC : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have : ((1 : ℂ) - ((erf713TinyC : ℝ) : ℂ) * I).re = 0 := by rw [h]; simp
    simp at this
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hfac : cerf (arcPoint erf713Rad (Real.pi / 2)) / erf713ModelM (arcPoint erf713Rad (Real.pi / 2))
      = ((a / b : ℝ) : ℂ) * (1 - ((erf713TinyC : ℝ) : ℂ) * I)⁻¹ := by
    rw [hcerf, hM]
    push_cast
    field_simp
  have hne : ¬ (-Real.arctan erf713TinyC = Real.pi) := by
    have h1 := Real.arctan_lt_pi_div_two erf713TinyC
    have h2 := Real.neg_pi_div_two_lt_arctan erf713TinyC
    have h3 := Real.pi_pos
    intro h; linarith [h ▸ h2]
  rw [hfac, Complex.arg_real_mul _ (div_pos him hbpos), Complex.arg_inv,
    erf713_arg_one_sub_mul_I, if_neg hne, neg_neg]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **The single arithmetic fact the whole theorem rests on.**
With `Ψ = √(R⁴ − L²) + π/4 + ½·arcsin (L/R²)` and `L = ½ log (21987 π)`:

    2π·3499  <  Ψ  <  2π·3500,     i.e.  21984.8654 < 21987.7848 < 21991.1486.

Margins ≈ 2.92 and ≈ 3.36; crude enclosures `L ∈ (0, 6)` and
`arcsin (L/R²) ∈ [0, π/2]` suffice, closed by `Real.pi_gt_3141592` /
`Real.pi_lt_3141593` and `norm_num`.

STATEMENT CORRECTION (2026-08-14): the `arcsin` term had lost its factor `½`.
From `cos 2θ* = −L/R²` with `2θ* ∈ (π/2, π)` one gets
`2θ* = π/2 + arcsin (L/R²)`, hence `θ* = π/4 + ½·arcsin (L/R²)`; the model
and the numerics (`θ* − π/4 = 1.26699e-4 = ½·2.53399e-4`) both carry the `½`.  The mis-stated version was still true (the two differ by `1.3e-4`,
far inside the `2.9` margin), but `Ψ` must be the real `R² sin 2θ* + θ*`. -/
theorem erf713_modelPsi_bounds :
    2 * Real.pi * 3499
      < Real.sqrt (21987 ^ 2 - (Real.log (21987 * Real.pi) / 2) ^ 2) + Real.pi / 4
          + Real.arcsin (Real.log (21987 * Real.pi) / 2 / 21987) / 2
    ∧ Real.sqrt (21987 ^ 2 - (Real.log (21987 * Real.pi) / 2) ^ 2) + Real.pi / 4
          + Real.arcsin (Real.log (21987 * Real.pi) / 2 / 21987) / 2
      < 2 * Real.pi * 3500 := by
  set L : ℝ := Real.log (21987 * Real.pi) / 2 with hLdef
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  -- `L > 0` : the argument of the log exceeds `1`
  have hLpos : 0 < L := by
    have h1 : (1 : ℝ) < 21987 * Real.pi := by nlinarith
    have := Real.log_pos h1
    rw [hLdef]; linarith
  -- `L < 6` : `21987 π < 69074 < 2.7¹² < e¹²`
  have hexp12 : (69075 : ℝ) < Real.exp 12 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h2 : (2.7 : ℝ) ^ (12 : ℕ) < (Real.exp 1) ^ (12 : ℕ) := by
      exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    have h3 : (Real.exp 1) ^ (12 : ℕ) = Real.exp 12 := by
      rw [← Real.exp_nat_mul]; norm_num
    calc (69075 : ℝ) < (2.7 : ℝ) ^ (12 : ℕ) := by norm_num
      _ < (Real.exp 1) ^ (12 : ℕ) := h2
      _ = Real.exp 12 := h3
  have hLlt : L < 6 := by
    have harg : (0 : ℝ) < 21987 * Real.pi := by nlinarith
    have hlt : 21987 * Real.pi < Real.exp 12 := by nlinarith
    have h := (Real.log_lt_iff_lt_exp harg).mpr hlt
    rw [hLdef]; linarith
  -- the square-root enclosure
  have hsq_nonneg : (0 : ℝ) ≤ 21987 ^ 2 - L ^ 2 := by nlinarith
  have he1 : (21986.99 : ℝ) = Real.sqrt (21986.99 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have he2 : (21987 : ℝ) = Real.sqrt (21987 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have hsqrt_lo : (21986.99 : ℝ) < Real.sqrt (21987 ^ 2 - L ^ 2) := by
    rw [he1]
    apply Real.sqrt_lt_sqrt (by norm_num)
    nlinarith
  have hsqrt_hi : Real.sqrt (21987 ^ 2 - L ^ 2) ≤ 21987 := by
    rw [he2]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- the arcsin enclosure: `0 ≤ arcsin (L/R²) ≤ π/2`
  have harcsin_lo : 0 ≤ Real.arcsin (L / 21987) :=
    Real.arcsin_nonneg.mpr (by positivity)
  have harcsin_hi : Real.arcsin (L / 21987) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  -- `linarith` cannot atomize `√(polynomial in L)`, so abstract the two transcendental
  -- quantities into plain variables and run the (purely linear) endgame on those.
  have key : ∀ S A : ℝ, 21986.99 < S → S ≤ 21987 → 0 ≤ A → A ≤ Real.pi / 2 →
      2 * Real.pi * 3499 < S + Real.pi / 4 + A / 2
        ∧ S + Real.pi / 4 + A / 2 < 2 * Real.pi * 3500 := by
    intro S A h1 h2 h3 h4
    constructor
    · linarith
    · linarith
  exact key _ _ hsqrt_lo hsqrt_hi harcsin_lo harcsin_hi


/-! ### The split point `θ*` and the reciprocal factor `k = 1 − 1/u`

`|u(R e^{iθ})| = e^{−R² cos 2θ}/(√π R)` is strictly increasing in `θ` on `[0, π/2]`
(because `cos 2θ` strictly decreases there), and crosses `1` exactly where
`R² cos 2θ = −L`, i.e. at `2θ* = π/2 + arcsin (L/R²)`.  Left of `θ*` the model
`M = 1 − u` lies in the right half-plane; right of `θ*` the *reciprocal* factor
`k = 1 − 1/u` does, and `M = (−u)·k`. -/

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- The model factor never vanishes on the arc. -/
theorem erf713_modelU_arcPt_ne_zero (θ : ℝ) : erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := by
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [erf713ModelU]
  exact div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hπ (arcPoint_ne_zero erf713Rad_pos.ne' θ))

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `M' = −u'`. -/
theorem erf713_hasDerivAt_modelM {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt erf713ModelM (-(erf713ModelU z * (-2 * z - z⁻¹))) z := by
  simpa [erf713ModelM] using (erf713_hasDerivAt_modelU hz).const_sub (1 : ℂ)

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The reciprocal model factor `k(z) = 1 − 1/u(z)`; on the far half of the arc it
plays for `M` the role `M` itself plays on the near half (`M = (−u)·k`). -/
def erf713KFun (z : ℂ) : ℂ := 1 - (erf713ModelU z)⁻¹

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `k' = u'/u²`. -/
theorem erf713_hasDerivAt_kFun {z : ℂ} (hz : z ≠ 0) (hu : erf713ModelU z ≠ 0) :
    HasDerivAt erf713KFun (erf713ModelU z * (-2 * z - z⁻¹) / (erf713ModelU z) ^ 2) z := by
  have h := ((erf713_hasDerivAt_modelU hz).inv hu).const_sub (1 : ℂ)
  have hfun : erf713KFun = fun x => 1 - (erf713ModelU x)⁻¹ := rfl
  rw [hfun]
  convert h using 1
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_modelU_arcPt : Continuous fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ) := by
  have hπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h1 : Continuous (fun θ : ℝ => Complex.exp (-(arcPoint erf713Rad θ) ^ 2)) :=
    Complex.continuous_exp.comp ((continuous_arcPoint erf713Rad).pow 2).neg
  have h2 : Continuous (fun θ : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ) * arcPoint erf713Rad θ) :=
    continuous_const.mul (continuous_arcPoint erf713Rad)
  simpa [erf713ModelU] using h1.div h2 (fun θ => mul_ne_zero hπ (arcPoint_ne_zero erf713Rad_pos.ne' θ))

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_ratioFactor : Continuous fun θ : ℝ => -2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹ :=
  (continuous_const.mul (continuous_arcPoint erf713Rad)).sub ((continuous_arcPoint erf713Rad).inv₀ (arcPoint_ne_zero erf713Rad_pos.ne'))

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_deriv_modelU_arcPt : Continuous fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ))
      = fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹) :=
    funext fun θ => (erf713_hasDerivAt_modelU (arcPoint_ne_zero erf713Rad_pos.ne' θ)).deriv
  rw [heq]
  exact erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_modelM_arcPt : Continuous fun θ : ℝ => erf713ModelM (arcPoint erf713Rad θ) := by
  have h : Continuous fun θ : ℝ => (1 : ℂ) - erf713ModelU (arcPoint erf713Rad θ) :=
    continuous_const.sub erf713_continuous_modelU_arcPt
  simpa [erf713ModelM] using h

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_deriv_modelM_arcPt : Continuous fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ))
      = fun θ : ℝ => -(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)) :=
    funext fun θ => (erf713_hasDerivAt_modelM (arcPoint_ne_zero erf713Rad_pos.ne' θ)).deriv
  rw [heq]
  exact (erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor).neg

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_kFun_arcPt : Continuous fun θ : ℝ => erf713KFun (arcPoint erf713Rad θ) := by
  have h : Continuous fun θ : ℝ => (1 : ℂ) - (erf713ModelU (arcPoint erf713Rad θ))⁻¹ :=
    continuous_const.sub (erf713_continuous_modelU_arcPt.inv₀ erf713_modelU_arcPt_ne_zero)
  simpa [erf713KFun] using h

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_continuous_deriv_kFun_arcPt : Continuous fun θ : ℝ => deriv erf713KFun (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erf713KFun (arcPoint erf713Rad θ))
      = fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)
          / (erf713ModelU (arcPoint erf713Rad θ)) ^ 2 :=
    funext fun θ => (erf713_hasDerivAt_kFun (arcPoint_ne_zero erf713Rad_pos.ne' θ) (erf713_modelU_arcPt_ne_zero θ)).deriv
  rw [heq]
  exact (erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor).div
    (erf713_continuous_modelU_arcPt.pow 2) (fun θ => pow_ne_zero 2 (erf713_modelU_arcPt_ne_zero θ))

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- The pointwise factorisation `M'/M = u'/u + k'/k` behind `M = (−u)·k`, in purely
algebraic form: with `M = 1 − U`, `k = 1 − U⁻¹`, `M' = −U·g`, `u' = U·g`, `k' = U·g/U²`. -/
theorem erf713_logDeriv_factor_split (U g X : ℂ) (hU : U ≠ 0) (hM : 1 - U ≠ 0) :
    -(U * g) / (1 - U) * X
      = U * g / U * X + U * g / U ^ 2 / (1 - U⁻¹) * X := by
  have hU1 : U - 1 ≠ 0 := fun h => hM (by rw [show (1 : ℂ) - U = -(U - 1) by ring, h, neg_zero])
  have h1 : (1 : ℂ) - U⁻¹ = (U - 1) / U := by field_simp
  rw [h1]
  field_simp
  ring

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- The split point `θ* = π/4 + ½ arcsin (L/R²)`, the unique arc parameter with
`|u| = 1` (equivalently `R² cos 2θ* = −L`). -/
def erf713ThetaStar : ℝ := Real.pi / 4 + Real.arcsin (erf713BigL / 21987) / 2

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- `Ψ = R² sin 2θ* + θ*`, the continuous argument of `u` at the split point. -/
def erf713BigPsi : ℝ := erf713Rad ^ 2 * Real.sin (2 * erf713ThetaStar) + erf713ThetaStar

-- no-dlmf: contour/model vocabulary for the argument-principle count `erf713_low_zero_count`; proof infrastructure
/-- `φ = 2π·3500 − Ψ`, the principal residue of `−Ψ` mod `2π`. -/
def erf713BigPhi : ℝ := 2 * Real.pi * 3500 - erf713BigPsi

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_bigL_div_pos : 0 < erf713BigL / 21987 := by
  have := erf713_bigL_bounds.1; positivity

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_bigL_div_lt_one : erf713BigL / 21987 < 1 := by
  have := erf713_bigL_bounds.2; rw [div_lt_one (by norm_num)]; linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_two_thetaStar : 2 * erf713ThetaStar = Real.pi / 2 + Real.arcsin (erf713BigL / 21987) := by
  rw [erf713ThetaStar]; ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_cos_two_thetaStar : Real.cos (2 * erf713ThetaStar) = -(erf713BigL / 21987) := by
  rw [erf713_two_thetaStar, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.sin_arcsin (by linarith [erf713_bigL_div_pos]) erf713_bigL_div_lt_one.le]
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_sin_two_thetaStar :
    Real.sin (2 * erf713ThetaStar) = Real.sqrt (1 - (erf713BigL / 21987) ^ 2) := by
  rw [erf713_two_thetaStar, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_arcsin]
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_thetaStar_pos : 0 < erf713ThetaStar := by
  have h := Real.arcsin_nonneg.mpr erf713_bigL_div_pos.le
  have := Real.pi_pos
  rw [erf713ThetaStar]; linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_thetaStar_lt_pi_div_two : erf713ThetaStar < Real.pi / 2 := by
  have h : Real.arcsin (erf713BigL / 21987) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr erf713_bigL_div_lt_one
  rw [erf713ThetaStar]; linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `Ψ` in the exact shape of `erf713_modelPsi_bounds`. -/
theorem erf713_bigPsi_eq :
    erf713BigPsi = Real.sqrt (21987 ^ 2 - (Real.log (21987 * Real.pi) / 2) ^ 2) + Real.pi / 4
      + Real.arcsin (Real.log (21987 * Real.pi) / 2 / 21987) / 2 := by
  have hfac : (21987 : ℝ) ^ 2 - erf713BigL ^ 2 = 21987 ^ 2 * (1 - (erf713BigL / 21987) ^ 2) := by
    field_simp
  have hsqrt : Real.sqrt ((21987 : ℝ) ^ 2 - erf713BigL ^ 2)
      = 21987 * Real.sqrt (1 - (erf713BigL / 21987) ^ 2) := by
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [erf713BigPsi, erf713_sin_two_thetaStar, erf713Rad_sq, erf713ThetaStar, ← erf713_bigL_eq, ← hsqrt]
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_bigPhi_bounds : 0 < erf713BigPhi ∧ erf713BigPhi < 2 * Real.pi := by
  obtain ⟨h1, h2⟩ := erf713_modelPsi_bounds
  rw [erf713BigPhi, erf713_bigPsi_eq]
  constructor <;> linarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
theorem erf713_exp_bigL : Real.exp erf713BigL = Real.sqrt Real.pi * erf713Rad := Real.exp_log erf713_sqrtPi_Rad_pos

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- Left of the split point the model factor is a strict contraction. -/
theorem erf713_modelU_arcPt_norm_lt_one {θ : ℝ} (h0 : 0 ≤ θ) (h : θ < erf713ThetaStar) :
    ‖erf713ModelU (arcPoint erf713Rad θ)‖ < 1 := by
  have hπ := Real.pi_pos
  have hcos : Real.cos (2 * erf713ThetaStar) < Real.cos (2 * θ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith)
      (by linarith [erf713_thetaStar_lt_pi_div_two]) (by linarith)
  rw [erf713_cos_two_thetaStar] at hcos
  have hkey : -(erf713Rad ^ 2 * Real.cos (2 * θ)) < erf713BigL := by
    rw [erf713Rad_sq]; linarith
  have hexp : Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) < Real.sqrt Real.pi * erf713Rad := by
    rw [← erf713_exp_bigL]; exact Real.exp_lt_exp.mpr hkey
  rw [erf713_modelU_arcPt_norm, div_lt_one erf713_sqrtPi_Rad_pos]
  exact hexp

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- Right of the split point the *reciprocal* model factor is a strict contraction. -/
theorem erf713_modelU_arcPt_inv_norm_lt_one {θ : ℝ} (h : erf713ThetaStar < θ) (h2 : θ ≤ Real.pi / 2) :
    ‖(erf713ModelU (arcPoint erf713Rad θ))⁻¹‖ < 1 := by
  have hπ := Real.pi_pos
  have hcos : Real.cos (2 * θ) < Real.cos (2 * erf713ThetaStar) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [erf713_thetaStar_pos]) (by linarith)
      (by linarith)
  rw [erf713_cos_two_thetaStar] at hcos
  have hkey : erf713BigL < -(erf713Rad ^ 2 * Real.cos (2 * θ)) := by
    rw [erf713Rad_sq]; linarith
  have hexp : Real.sqrt Real.pi * erf713Rad < Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) := by
    rw [← erf713_exp_bigL]; exact Real.exp_lt_exp.mpr hkey
  rw [norm_inv, erf713_modelU_arcPt_norm, inv_lt_one_iff₀]
  right
  rw [lt_div_iff₀ erf713_sqrtPi_Rad_pos, one_mul]
  exact hexp

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- At the split point `u` is the pure phase `e^{iφ}`. -/
theorem erf713_modelU_thetaStar : erf713ModelU (arcPoint erf713Rad erf713ThetaStar) = Complex.exp ((erf713BigPhi : ℂ) * I) := by
  have hcos : Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * erf713ThetaStar))) = Real.sqrt Real.pi * erf713Rad := by
    rw [erf713_cos_two_thetaStar, erf713Rad_sq, ← erf713_exp_bigL]
    congr 1
    ring
  have hphase : ((-(erf713Rad ^ 2 * Real.sin (2 * erf713ThetaStar) + erf713ThetaStar) : ℝ) : ℂ) * I
      = ((erf713BigPhi : ℝ) : ℂ) * I + ((-3500 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have : (-(erf713Rad ^ 2 * Real.sin (2 * erf713ThetaStar) + erf713ThetaStar) : ℝ)
        = erf713BigPhi - 2 * Real.pi * 3500 := by
      rw [erf713BigPhi, erf713BigPsi]; ring
    rw [this]
    push_cast
    ring
  rw [erf713_modelU_arcPt, hcos, hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, div_self erf713_sqrtPi_Rad_pos.ne']
  norm_num

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- At the split point `1/u` is the pure phase `e^{i(2π−φ)}`. -/
theorem erf713_modelU_thetaStar_inv :
    (erf713ModelU (arcPoint erf713Rad erf713ThetaStar))⁻¹ = Complex.exp (((2 * Real.pi - erf713BigPhi : ℝ) : ℂ) * I) := by
  rw [erf713_modelU_thetaStar, ← Complex.exp_neg]
  have hsplit : ((2 * Real.pi - erf713BigPhi : ℝ) : ℂ) * I
      = -((erf713BigPhi : ℂ) * I) + 2 * (Real.pi : ℂ) * I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- `1 − e^{iφ}` has positive real part for `φ ∈ (0, 2π)`. -/
theorem erf713_one_sub_exp_re_pos {φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2 * Real.pi) :
    0 < (1 - Complex.exp ((φ : ℂ) * I)).re := by
  have hs : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcosφ : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    have hpy := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    linarith
  have hre : (1 - Complex.exp ((φ : ℂ) * I)).re = 1 - Real.cos φ := by
    rw [Complex.exp_mul_I]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re]
  rw [hre, hcosφ]
  nlinarith

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- On `[0, θ*]` the model lies in the open right half-plane. -/
theorem erf713_modelM_re_pos {θ : ℝ} (h0 : 0 ≤ θ) (h : θ ≤ erf713ThetaStar) :
    0 < (erf713ModelM (arcPoint erf713Rad θ)).re := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := erf713_modelU_arcPt_norm_lt_one h0 hlt
    have hre : (erf713ModelU (arcPoint erf713Rad θ)).re ≤ ‖erf713ModelU (arcPoint erf713Rad θ)‖ := Complex.re_le_norm _
    have : (erf713ModelM (arcPoint erf713Rad θ)).re = 1 - (erf713ModelU (arcPoint erf713Rad θ)).re := by
      rw [erf713ModelM]; simp
    rw [this]; linarith
  · obtain ⟨hφ0, hφ2⟩ := erf713_bigPhi_bounds
    rw [heq, erf713ModelM, erf713_modelU_thetaStar]
    exact erf713_one_sub_exp_re_pos hφ0 hφ2

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- On `[θ*, π/2]` the reciprocal factor lies in the open right half-plane. -/
theorem erf713_kFun_re_pos {θ : ℝ} (h : erf713ThetaStar ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    0 < (erf713KFun (arcPoint erf713Rad θ)).re := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := erf713_modelU_arcPt_inv_norm_lt_one hlt h2
    have hre : ((erf713ModelU (arcPoint erf713Rad θ))⁻¹).re ≤ ‖(erf713ModelU (arcPoint erf713Rad θ))⁻¹‖ := Complex.re_le_norm _
    have : (erf713KFun (arcPoint erf713Rad θ)).re = 1 - ((erf713ModelU (arcPoint erf713Rad θ))⁻¹).re := by
      rw [erf713KFun]; simp
    rw [this]; linarith
  · obtain ⟨hφ0, hφ2⟩ := erf713_bigPhi_bounds
    rw [← heq, erf713KFun, erf713_modelU_thetaStar_inv]
    exact erf713_one_sub_exp_re_pos (by linarith) (by linarith)

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **The model integral in closed form.**  `Im` of the quarter-arc
integral of `M'/M`.

Content: split at `θ*` (where `|u|` — strictly increasing, since
`d log|u|/dθ = 2R² sin 2θ ≥ 0` — crosses `1`).  On `[0,θ*]`, `M ∈ ball 1 1 ⊆
slitPlane`, so `ARC` applies directly.  On `[θ*,π/2]`, factor `M = (−u)·(1 − 1/u)`:
the second factor is again in `ball 1 1`, and the first contributes
`Λ(π/2) − Λ(θ*)` via the branch-free antiderivative `erf713BigLambda`.  Explicitly

    Im J_M = arg M(θ*) + (Im Λ(π/2) − Im Λ(θ*)) + arg k(π/2) − arg k(θ*)
           = (φ/2 − π/2) + (−π/2 + Ψ) + arg k(π/2) + (φ/2 − π/2)
           = 2πm − 3π/2 + arg k(π/2),      φ = 2πm − Ψ ∈ (0, 2π),  m = ⌈Ψ/2π⌉ = 3500,

with `m = 3500` justified by `erf713_modelPsi_bounds`.  Two of the four ingredients of that
display are now proven here: `erf713_bigLambda_hasDerivAt` (the `Λ` half, i.e. that the
branch-free antiderivative really differentiates to the pulled-back `u'/u`) and
`erf713_arg_one_sub_exp_mul_I` (the `arg M(θ*)` / `arg k(θ*)` half).  The assembly is now
complete: `θ*` is given in closed form (`erf713ThetaStar`, with `cos 2θ* = −L/R²` — so no
intermediate-value argument is needed, only the strict monotonicity of `cos` on
`[0, π]` for the two contraction estimates `erf713_modelU_arcPt_norm_lt_one` /
`erf713_modelU_arcPt_inv_norm_lt_one`), the two `ARC` applications carry their `slitPlane`
side conditions from `erf713_modelM_re_pos` / `erf713_kFun_re_pos` and their integrability from
continuity on the compact arc, and `φ = 2π·3500 − Ψ ∈ (0, 2π)` is `erf713_bigPhi_bounds`,
read off `erf713_modelPsi_bounds`.

**STATEMENT CORRECTION (2026-08-14).**  The previous form asserted
`= 2π·3500 − 3π/2` exactly.  That is FALSE: the naive display sets
`arg k(π/2) = 0`, but `k(π/2) = 1 − 1/u(iR) = 1 − i·√π R e^{−R²} = 1 − i·erf713TinyC`, whose
argument is `−arctan (erf713TinyC) ≈ −1e−9549`, not `0`.  The correct closed form therefore
carries that term.  It is not a rounding nicety: the *exact* `arctan (erf713TinyC)` is what
cancels against `arg h(π/2)` (`erf713_ratio_arg_pi_div_two`) to make `erf713_arc_cerf_im` land on the
integer `2π·3499 + π/2` — with the old statement the two sides would differ by
`2·arctan (erf713TinyC) ≠ 0` and the assembly would be inconsistent. -/
theorem erf713_modelArc_im :
    (arcLogDerivIntegral erf713ModelM erf713Rad 0 (Real.pi / 2)).im
      = 2 * Real.pi * 3500 - 3 * Real.pi / 2 - Real.arctan erf713TinyC := by
  obtain ⟨hφ0, hφ2⟩ := erf713_bigPhi_bounds
  have hπ := Real.pi_pos
  have hts0 : 0 < erf713ThetaStar := erf713_thetaStar_pos
  have hts2 : erf713ThetaStar < Real.pi / 2 := erf713_thetaStar_lt_pi_div_two
  have huIcc1 : Set.uIcc (0:ℝ) erf713ThetaStar = Set.Icc 0 erf713ThetaStar := Set.uIcc_of_le hts0.le
  have huIcc2 : Set.uIcc erf713ThetaStar (Real.pi / 2) = Set.Icc erf713ThetaStar (Real.pi / 2) :=
    Set.uIcc_of_le hts2.le
  have hsub1 : Set.Icc (0:ℝ) erf713ThetaStar ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Icc_subset_Icc le_rfl hts2.le
  have hsub2 : Set.Icc erf713ThetaStar (Real.pi / 2) ⊆ Set.Icc (0:ℝ) (Real.pi / 2) :=
    Set.Icc_subset_Icc hts0.le le_rfl
  -- nonvanishing of the three factors
  have hune : ∀ θ : ℝ, erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := erf713_modelU_arcPt_ne_zero
  have hMne : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2), erf713ModelM (arcPoint erf713Rad θ) ≠ 0 := by
    intro θ hθ h0
    have h := erf713_modelM_norm_ge hθ
    rw [h0, norm_zero] at h
    linarith
  have hkne : ∀ θ ∈ Set.Icc erf713ThetaStar (Real.pi / 2), erf713KFun (arcPoint erf713Rad θ) ≠ 0 := by
    intro θ hθ h0
    have h := erf713_kFun_re_pos hθ.1 hθ.2
    rw [h0] at h
    simp at h
  -- continuity and interval integrability of the three integrands
  have hrot : Continuous fun θ : ℝ => I * arcPoint erf713Rad θ := continuous_const.mul (continuous_arcPoint erf713Rad)
  have hFMcont : ContinuousOn
      (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0:ℝ) (Real.pi / 2)) :=
    (erf713_continuous_deriv_modelM_arcPt.continuousOn.div
      erf713_continuous_modelM_arcPt.continuousOn hMne).mul hrot.continuousOn
  have hFUcont : Continuous
      (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) :=
    (erf713_continuous_deriv_modelU_arcPt.div erf713_continuous_modelU_arcPt hune).mul hrot
  have hFKcont : ContinuousOn
      (fun θ : ℝ => deriv erf713KFun (arcPoint erf713Rad θ) / erf713KFun (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc erf713ThetaStar (Real.pi / 2)) :=
    (erf713_continuous_deriv_kFun_arcPt.continuousOn.div
      erf713_continuous_kFun_arcPt.continuousOn hkne).mul hrot.continuousOn
  have hFMint1 : IntervalIntegrable
      (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume 0 erf713ThetaStar := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc1]; exact hFMcont.mono hsub1
  have hFMint2 : IntervalIntegrable
      (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erf713ThetaStar (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFMcont.mono hsub2
  have hFUint : IntervalIntegrable
      (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erf713ThetaStar (Real.pi / 2) := hFUcont.intervalIntegrable _ _
  have hFKint : IntervalIntegrable
      (fun θ : ℝ => deriv erf713KFun (arcPoint erf713Rad θ) / erf713KFun (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erf713ThetaStar (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFKcont
  -- split the quarter arc at the crossing point `θ*`
  have hsplit : arcLogDerivIntegral erf713ModelM erf713Rad 0 (Real.pi / 2)
      = (∫ θ in (0:ℝ)..erf713ThetaStar,
          deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
        + ∫ θ in erf713ThetaStar..(Real.pi / 2),
            deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) :=
    (intervalIntegral.integral_add_adjacent_intervals hFMint1 hFMint2).symm
  -- near half: `M` itself lies in the right half-plane
  have hleft : (∫ θ in (0:ℝ)..erf713ThetaStar,
      deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      = Complex.log (erf713ModelM (arcPoint erf713Rad erf713ThetaStar)) - Complex.log (erf713ModelM (arcPoint erf713Rad 0)) := by
    have hdiff : ∀ θ ∈ Set.uIcc (0:ℝ) erf713ThetaStar, DifferentiableAt ℂ erf713ModelM (arcPoint erf713Rad θ) :=
      fun θ _ => (erf713_hasDerivAt_modelM (arcPoint_ne_zero erf713Rad_pos.ne' θ)).differentiableAt
    have hslit : ∀ θ ∈ Set.uIcc (0:ℝ) erf713ThetaStar, erf713ModelM (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
      intro θ hθ
      rw [huIcc1] at hθ
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (erf713_modelM_re_pos hθ.1 hθ.2))
    exact arc_logDeriv_integral hdiff hslit hFMint1
  -- far half: factor `M = (−u)·k`, i.e. `M'/M = u'/u + k'/k`
  have hMeq : ∀ θ ∈ Set.Icc erf713ThetaStar (Real.pi / 2),
      deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        = deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv erf713KFun (arcPoint erf713Rad θ) / erf713KFun (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) := by
    intro θ hθ
    have hU := hune θ
    have hM := hMne θ (hsub2 hθ)
    have hK := hkne θ hθ
    rw [erf713ModelM] at hM
    rw [erf713KFun] at hK
    rw [(erf713_hasDerivAt_modelM (arcPoint_ne_zero erf713Rad_pos.ne' θ)).deriv,
      (erf713_hasDerivAt_modelU (arcPoint_ne_zero erf713Rad_pos.ne' θ)).deriv,
      (erf713_hasDerivAt_kFun (arcPoint_ne_zero erf713Rad_pos.ne' θ) hU).deriv, erf713ModelM, erf713KFun]
    exact erf713_logDeriv_factor_split _ _ _ hU hM
  have hright : (∫ θ in erf713ThetaStar..(Real.pi / 2),
      deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      = (erf713BigLambda (Real.pi / 2) - erf713BigLambda erf713ThetaStar)
        + (Complex.log (erf713KFun (arcPoint erf713Rad (Real.pi / 2)))
            - Complex.log (erf713KFun (arcPoint erf713Rad erf713ThetaStar))) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv erf713KFun (arcPoint erf713Rad θ) / erf713KFun (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (fun θ hθ => hMeq θ (by rwa [huIcc2] at hθ)),
      intervalIntegral.integral_add hFUint hFKint]
    congr 1
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => erf713_bigLambda_hasDerivAt θ) hFUint
    · have hdiff : ∀ θ ∈ Set.uIcc erf713ThetaStar (Real.pi / 2),
          DifferentiableAt ℂ erf713KFun (arcPoint erf713Rad θ) :=
        fun θ _ => (erf713_hasDerivAt_kFun (arcPoint_ne_zero erf713Rad_pos.ne' θ) (hune θ)).differentiableAt
      have hslit : ∀ θ ∈ Set.uIcc erf713ThetaStar (Real.pi / 2),
          erf713KFun (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
        intro θ hθ
        rw [huIcc2] at hθ
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (erf713_kFun_re_pos hθ.1 hθ.2))
      exact arc_logDeriv_integral hdiff hslit hFKint
  -- the four endpoint arguments
  have hargMstar : Complex.arg (erf713ModelM (arcPoint erf713Rad erf713ThetaStar)) = erf713BigPhi / 2 - Real.pi / 2 := by
    rw [erf713ModelM, erf713_modelU_thetaStar]
    exact erf713_arg_one_sub_exp_mul_I hφ0 hφ2
  have hargM0 : Complex.arg (erf713ModelM (arcPoint erf713Rad 0)) = 0 := by
    have hM : erf713ModelM (arcPoint erf713Rad 0)
        = ((1 - Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) := by
      rw [erf713ModelM, erf713_modelU_zero]; push_cast; ring
    rw [hM]
    exact Complex.arg_ofReal_of_nonneg (by linarith [erf713_modelU_zero_lt_one])
  have hargKstar : Complex.arg (erf713KFun (arcPoint erf713Rad erf713ThetaStar))
      = (2 * Real.pi - erf713BigPhi) / 2 - Real.pi / 2 := by
    rw [erf713KFun, erf713_modelU_thetaStar_inv]
    exact erf713_arg_one_sub_exp_mul_I (by linarith) (by linarith)
  have hargKpi : Complex.arg (erf713KFun (arcPoint erf713Rad (Real.pi / 2))) = -Real.arctan erf713TinyC := by
    set b : ℝ := Real.exp (erf713Rad ^ 2) / (Real.sqrt Real.pi * erf713Rad) with hb
    have hbpos : 0 < b := div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
    have hexp1 : Real.exp (erf713Rad ^ 2) * Real.exp (-(erf713Rad ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hRne : erf713Rad ≠ 0 := erf713Rad_pos.ne'
    have hbc : b * erf713TinyC = 1 := by
      rw [hb, erf713TinyC]
      field_simp
      linear_combination hexp1
    have hbc' : ((b : ℝ) : ℂ) * ((erf713TinyC : ℝ) : ℂ) = 1 := by exact_mod_cast hbc
    have hprod : (((erf713TinyC : ℝ) : ℂ) * I) * (-(((b : ℝ) : ℂ) * I)) = 1 := by
      linear_combination (-((erf713TinyC : ℝ) : ℂ) * ((b : ℝ) : ℂ)) * Complex.I_sq + hbc'
    have hinv : (erf713ModelU (arcPoint erf713Rad (Real.pi / 2)))⁻¹ = ((erf713TinyC : ℝ) : ℂ) * I := by
      rw [erf713_modelU_pi_div_two]
      exact inv_eq_of_mul_eq_one_left hprod
    rw [erf713KFun, hinv, erf713_arg_one_sub_mul_I]
  -- assemble
  rw [hsplit, hleft, hright]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [hargMstar, hargM0, hargKstar, hargKpi, erf713_bigLambda_im, erf713_bigLambda_im,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  have hpsi : erf713BigPsi = erf713Rad ^ 2 * Real.sin (2 * erf713ThetaStar) + erf713ThetaStar := rfl
  have hphi : erf713BigPhi = 2 * Real.pi * 3500 - erf713BigPsi := rfl
  rw [hpsi] at hphi
  linarith


-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **Splitting the arc integral along `cerf = M·h`.**

Content (no arithmetic left in it — this is pure contour bookkeeping):

* on the closed quarter arc `‖M‖ ≥ 1/2` (`erf713_modelM_norm_ge`), so `M ≠ 0` there, and
  `h := cerf/M` maps the arc into `ball 1 (1/2) ⊆ slitPlane` (`erf713_ratio_mem_ball`); in
  particular `h ≠ 0`, hence also `cerf ≠ 0`, on the arc;
* `cerf`, `erf713ModelM` and `h` are differentiable at every arc point (`differentiable_cerf`;
  `erf713ModelU` is a quotient of entire functions with nonvanishing denominator `√π z`), so
  pointwise `cerf'/cerf = M'/M + h'/h` and each of the three integrands is continuous on
  `[0, π/2]`, hence interval-integrable;
* `ARC` (`arc_logDeriv_integral`) then evaluates the `h`-piece as
  `log h(π/2) − log h(0)`.

Proof: `intervalIntegral`/`DifferentiableAt` bookkeeping, no new mathematics. -/
theorem erf713_arcIntegral_cerf_split :
    arcLogDerivIntegral cerf erf713Rad 0 (Real.pi / 2)
      = arcLogDerivIntegral erf713ModelM erf713Rad 0 (Real.pi / 2)
        + (Complex.log (cerf (arcPoint erf713Rad (Real.pi / 2)) / erf713ModelM (arcPoint erf713Rad (Real.pi / 2)))
            - Complex.log (cerf (arcPoint erf713Rad 0) / erf713ModelM (arcPoint erf713Rad 0))) := by
  have hπ2 : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have huIcc : Set.uIcc (0:ℝ) (Real.pi / 2) = Set.Icc 0 (Real.pi / 2) := Set.uIcc_of_le hπ2
  have hsqrtπ : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hzne : ∀ θ : ℝ, arcPoint erf713Rad θ ≠ 0 := arcPoint_ne_zero erf713Rad_pos.ne'
  have hcne : ∀ θ : ℝ, cerf (arcPoint erf713Rad θ) ≠ 0 := fun θ => cerf_ne_zero_on_circle (norm_arcPoint erf713Rad_pos.le θ)
  have hMne : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2), erf713ModelM (arcPoint erf713Rad θ) ≠ 0 := by
    intro θ hθ h0
    have h := erf713_modelM_norm_ge hθ
    rw [h0, norm_zero] at h
    linarith
  -- derivative of the model on the arc, and of the ratio
  have hMd : ∀ θ : ℝ, HasDerivAt erf713ModelM
      (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))) (arcPoint erf713Rad θ) := by
    intro θ
    have h := (erf713_hasDerivAt_modelU (hzne θ)).const_sub (1 : ℂ)
    simpa [erf713ModelM] using h
  have hHd : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      HasDerivAt (fun z => cerf z / erf713ModelM z)
        ((deriv cerf (arcPoint erf713Rad θ) * erf713ModelM (arcPoint erf713Rad θ)
            - cerf (arcPoint erf713Rad θ) * deriv erf713ModelM (arcPoint erf713Rad θ)) / (erf713ModelM (arcPoint erf713Rad θ)) ^ 2) (arcPoint erf713Rad θ) :=
    fun θ hθ => ((differentiable_cerf (arcPoint erf713Rad θ)).hasDerivAt).div
      ((hMd θ).differentiableAt.hasDerivAt) (hMne θ hθ)
  -- continuity of all three integrands
  have hderiv_eq : deriv cerf = fun z => (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2) :=
    funext (fun z => (hasDerivAt_cerf z).deriv)
  have hdcerfc : Continuous (fun θ : ℝ => deriv cerf (arcPoint erf713Rad θ)) := by
    rw [hderiv_eq]
    exact (Complex.continuous_exp.comp ((continuous_arcPoint erf713Rad).pow 2).neg).const_mul _
  have hcerfc : Continuous (fun θ : ℝ => cerf (arcPoint erf713Rad θ)) :=
    differentiable_cerf.continuous.comp (continuous_arcPoint erf713Rad)
  have hUc : Continuous (fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ)) := by
    have h1 : Continuous (fun θ : ℝ => Complex.exp (-(arcPoint erf713Rad θ) ^ 2)) :=
      Complex.continuous_exp.comp ((continuous_arcPoint erf713Rad).pow 2).neg
    have h2 : Continuous (fun θ : ℝ => ((Real.sqrt Real.pi : ℝ) : ℂ) * arcPoint erf713Rad θ) :=
      continuous_const.mul (continuous_arcPoint erf713Rad)
    simpa [erf713ModelU] using h1.div h2 (fun θ => mul_ne_zero hsqrtπ (hzne θ))
  have hMc : Continuous (fun θ : ℝ => erf713ModelM (arcPoint erf713Rad θ)) := by
    simpa [erf713ModelM] using (continuous_const (y := (1 : ℂ))).sub hUc
  have hdMc : Continuous (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ)) := by
    have heq : (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ))
        = fun θ : ℝ => -(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)) :=
      funext fun θ => (hMd θ).deriv
    rw [heq]
    exact (hUc.mul ((continuous_const.mul (continuous_arcPoint erf713Rad)).sub
      ((continuous_arcPoint erf713Rad).inv₀ hzne))).neg
  have hrot : Continuous (fun θ : ℝ => I * arcPoint erf713Rad θ) := continuous_const.mul (continuous_arcPoint erf713Rad)
  have hFc : Continuous (fun θ : ℝ => deriv cerf (arcPoint erf713Rad θ) / cerf (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) :=
    (hdcerfc.div hcerfc hcne).mul hrot
  have hFm : ContinuousOn
      (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0:ℝ) (Real.pi / 2)) :=
    (hdMc.continuousOn.div hMc.continuousOn hMne).mul hrot.continuousOn
  -- the pointwise splitting of the logarithmic derivative
  have hEq : ∀ θ ∈ Set.Icc (0:ℝ) (Real.pi / 2),
      deriv cerf (arcPoint erf713Rad θ) / cerf (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        = deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ)
              / (cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ) := by
    intro θ hθ
    rw [(hHd θ hθ).deriv]
    have hM := hMne θ hθ
    have hc := hcne θ
    field_simp
    ring
  have hFh : ContinuousOn
      (fun θ : ℝ => deriv (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ)
        / (cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0:ℝ) (Real.pi / 2)) := by
    refine (hFc.continuousOn.sub hFm).congr ?_
    intro θ hθ
    show deriv (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ) / (cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ))
        * (I * arcPoint erf713Rad θ)
      = deriv cerf (arcPoint erf713Rad θ) / cerf (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        - deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
    rw [hEq θ hθ]
    ring
  have hFmInt : IntervalIntegrable
      (fun θ : ℝ => deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFm
  have hFhInt : IntervalIntegrable
      (fun θ : ℝ => deriv (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ)
        / (cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFh
  -- the ratio stays in `ball 1 (1/2) ⊆ slitPlane`
  have hslit : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
    intro θ hθ
    rw [huIcc] at hθ
    have hb := erf713_ratio_mem_ball hθ
    rw [Metric.mem_ball, Complex.dist_eq] at hb
    have h1 : |(cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) - 1).re|
        ≤ ‖cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) - 1‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_re, Complex.one_re] at h1
    have h2 := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hb))).1
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using by linarith))
  have hdiff : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      DifferentiableAt ℂ (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ) := by
    intro θ hθ
    rw [huIcc] at hθ
    exact (hHd θ hθ).differentiableAt
  have hlog := arc_logDeriv_integral (f := fun z => cerf z / erf713ModelM z) (a := (0:ℝ))
    (b := Real.pi / 2) hdiff hslit hFhInt
  have hmain : arcLogDerivIntegral cerf erf713Rad 0 (Real.pi / 2)
      = arcLogDerivIntegral erf713ModelM erf713Rad 0 (Real.pi / 2)
        + arcLogDerivIntegral (fun z => cerf z / erf713ModelM z) erf713Rad 0 (Real.pi / 2) := by
    show (∫ θ in (0:ℝ)..(Real.pi / 2),
        deriv cerf (arcPoint erf713Rad θ) / cerf (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) = _
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv erf713ModelM (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv (fun z => cerf z / erf713ModelM z) (arcPoint erf713Rad θ)
              / (cerf (arcPoint erf713Rad θ) / erf713ModelM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      (fun θ hθ => hEq θ (by rwa [huIcc] at hθ))]
    exact intervalIntegral.integral_add hFmInt hFhInt
  rw [hmain, hlog]

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- Assembling the two halves: the quarter-arc integral of `cerf'/cerf` has imaginary
part `π/2 + 2π·3499`.

`Im` of the split is `Im J_M + arg h(π/2) − arg h(0)`; by `erf713_modelArc_im` the first term
is `2π·3500 − 3π/2 − arctan (erf713TinyC)`, by `erf713_ratio_arg_pi_div_two` the second is
`arctan (erf713TinyC)`, and by `erf713_ratio_arg_zero` the third is `0`.  The two `arctan (erf713TinyC)`
terms cancel **exactly** (they are the same quantity: `arg k(π/2) = −arg h(π/2)`, both
coming from `1 − 1/u(iR) = 1 − i·erf713TinyC`), leaving

    2π·3500 − 3π/2 = 2π·3499 + π/2

on the nose — which is the quantization the argument principle demands.  (This exact
cancellation is why the route needs no `|ε| ≤ π/3` integer-pinning step at all; the
"pin the integer" bound of the usual argument is a safety net, not a necessity.) -/
theorem erf713_arc_cerf_im :
    (arcLogDerivIntegral cerf erf713Rad 0 (Real.pi / 2)).im = Real.pi / 2 + 2 * Real.pi * 3499 := by
  rw [erf713_arcIntegral_cerf_split]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [erf713_modelArc_im, erf713_ratio_arg_zero, erf713_ratio_arg_pi_div_two]
  ring

-- no-dlmf: step of the argument-principle computation behind `erf713_low_zero_count`; proof infrastructure
/-- **S6/S7.**  The zero set of `cerf` on the closed disc of radius `R`
is finite, contains `0`, contains no point of either axis besides `0`, and is
invariant under the Klein group; hence its multiplicity-weighted total is
`1 + 4·N` with `N` the first-quadrant count below the cut.

`S7` (no zero *on* the circle `‖w‖² = 21987`) comes from the existing asymptotic
machinery: a first-quadrant zero with `‖w‖² ≥ 21987` has index `n ≥ 3500`
(`erf713_zero_has_index`), hence `‖w‖² ≥ 2λ₃₅₀₀² − 1 > 21989`; propagate by
oddness/conjugation to the other three quadrants. -/
theorem erf713_zeros_finset_exists :
    ∃ P : Finset ℂ,
      (∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) erf713Rad ∧ cerf z = 0) ∧
      (∀ p ∈ P, p ∈ ball (0 : ℂ) erf713Rad) ∧
      (∑ p ∈ P, (analyticOrderNatAt cerf p : ℂ))
        = 1 + 4 * (({w : ℂ | cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}.ncard : ℕ) : ℂ) := by
  classical
  set Q1 : Set ℂ := {w : ℂ | cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987} with hQ1def
  -- Finiteness of the zero set on the closed counting disc.
  have hUconn : IsConnected (ball (0 : ℂ) (erf713Rad + 1)) :=
    ⟨Metric.nonempty_ball.mpr (by linarith [erf713Rad_pos]), (convex_ball (0 : ℂ) (erf713Rad + 1)).isPreconnected⟩
  have hx1 : (1 : ℂ) ∈ ball (0 : ℂ) (erf713Rad + 1) := by
    rw [mem_ball_zero_iff, norm_one]
    linarith [erf713Rad_pos]
  have hfx : cerf (1 : ℂ) ≠ 0 := by
    have h := cerf_ne_zero_of_ne_zero_real (show (1 : ℝ) ≠ 0 by norm_num)
    simpa using h
  have hK : IsCompact (closedBall (0 : ℂ) erf713Rad) := isCompact_closedBall 0 erf713Rad
  have hKU : closedBall (0 : ℂ) erf713Rad ⊆ ball (0 : ℂ) (erf713Rad + 1) :=
    Metric.closedBall_subset_ball (by linarith)
  have hZfin : (closedBall (0 : ℂ) erf713Rad ∩ cerf ⁻¹' {0}).Finite :=
    finite_zeros_on_compact (fun z _ => analyticAt_cerf z) hUconn hx1 hfx hK hKU
  set P : Finset ℂ := hZfin.toFinset with hPdef
  have hPmem : ∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) erf713Rad ∧ cerf z = 0 := by
    intro z
    rw [hPdef, Set.Finite.mem_toFinset]
    simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hPball : ∀ p ∈ P, p ∈ ball (0 : ℂ) erf713Rad := by
    intro p hp
    obtain ⟨hpc, hpz⟩ := (hPmem p).mp hp
    have hle : ‖p‖ ≤ erf713Rad := mem_closedBall_zero_iff.mp hpc
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · exact absurd hpz (cerf_ne_zero_on_circle heq)
  refine ⟨P, hPmem, hPball, ?_⟩
  -- Every element of `P` is a simple zero: `analyticOrderNatAt cerf p = 1`.
  have horder1 : ∀ p ∈ P, analyticOrderNatAt cerf p = 1 := by
    intro p hp
    have hcerfp : cerf p = 0 := ((hPmem p).mp hp).2
    have hord := (analyticAt_cerf p).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hcerfp
      (deriv_cerf_ne_zero p)
    unfold analyticOrderNatAt
    rw [hord]
    rfl
  have hsum : (∑ p ∈ P, (analyticOrderNatAt cerf p : ℂ)) = (P.card : ℂ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [horder1 p hp])]
    simp
  rw [hsum]
  -- Klein-orbit bookkeeping: `P` (as a set) is `{0}` together with four disjoint
  -- images of `Q1` under `id`, `neg`, `conj`, `-conj`.
  have hZeq : (closedBall (0 : ℂ) erf713Rad ∩ cerf ⁻¹' {0} : Set ℂ)
      = {0} ∪ Q1 ∪ (fun w => -w) '' Q1 ∪ (fun w => starRingEnd ℂ w) '' Q1
          ∪ (fun w => -(starRingEnd ℂ w)) '' Q1 := by
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨hzc, hzz⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzz
      have hzRad : ‖z‖ ≤ erf713Rad := mem_closedBall_zero_iff.mp hzc
      rcases eq_or_lt_of_le hzRad with heq | hlt
      · exact absurd hzz (cerf_ne_zero_on_circle heq)
      have hzsq : ‖z‖ ^ 2 < 21987 := by
        have h2 : ‖z‖ ^ 2 < erf713Rad ^ 2 := by nlinarith [hlt, norm_nonneg z]
        rwa [erf713Rad_sq] at h2
      by_cases hz0 : z = 0
      · left; left; left; left; exact hz0
      · by_cases hre0 : z.re = 0
        · exact absurd hzz (cerf_ne_zero_of_on_axis hz0 (Or.inl hre0))
        by_cases him0 : z.im = 0
        · exact absurd hzz (cerf_ne_zero_of_on_axis hz0 (Or.inr him0))
        rcases lt_or_gt_of_ne hre0 with hreN | hreP <;> rcases lt_or_gt_of_ne him0 with himN | himP
        · -- re < 0, im < 0 : z = -w, w := -z ∈ Q1
          have hwQ1 : (-z) ∈ Q1 := by
            refine ⟨by rw [cerf_neg, hzz, neg_zero], by rw [Complex.neg_re]; linarith,
              by rw [Complex.neg_im]; linarith, by rwa [norm_neg]⟩
          left; left; right
          exact ⟨-z, hwQ1, by ring⟩
        · -- re < 0, im > 0 : z = -(conj w), w := -(conj z) ∈ Q1
          have hwQ1 : (-(starRingEnd ℂ z)) ∈ Q1 := by
            refine ⟨by rw [cerf_neg, cerf_conj, hzz, map_zero, neg_zero],
              by rw [Complex.neg_re, Complex.conj_re]; linarith,
              by rw [Complex.neg_im, Complex.conj_im]; linarith,
              by rw [norm_neg, Complex.norm_conj]; exact hzsq⟩
          right
          refine ⟨-(starRingEnd ℂ z), hwQ1, ?_⟩
          show -(starRingEnd ℂ (-(starRingEnd ℂ z))) = z
          rw [map_neg, starRingEnd_self_apply, neg_neg]
        · -- re > 0, im < 0 : z = conj w, w := conj z ∈ Q1
          have hwQ1 : (starRingEnd ℂ z) ∈ Q1 := by
            refine ⟨by rw [cerf_conj, hzz, map_zero],
              by rw [Complex.conj_re]; linarith,
              by rw [Complex.conj_im]; linarith,
              by rw [Complex.norm_conj]; exact hzsq⟩
          left; right
          exact ⟨starRingEnd ℂ z, hwQ1, starRingEnd_self_apply z⟩
        · -- re > 0, im > 0 : z ∈ Q1
          left; left; left; right
          exact ⟨hzz, hreP, himP, hzsq⟩
    · rintro z ((((rfl | hzQ1) | ⟨w, hwQ1, rfl⟩) | ⟨w, hwQ1, rfl⟩) | ⟨w, hwQ1, rfl⟩)
      · exact ⟨mem_closedBall_zero_iff.mpr (by simp [erf713Rad_pos.le]), by simp⟩
      · obtain ⟨hzz, _, _, hzsq⟩ := hzQ1
        have hzlt : ‖z‖ < erf713Rad := by
          have h2 : ‖z‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
          nlinarith [norm_nonneg z, erf713Rad_pos]
        exact ⟨mem_closedBall_zero_iff.mpr hzlt.le, hzz⟩
      · obtain ⟨hzz, _, _, hzsq⟩ := hwQ1
        have hzlt : ‖w‖ < erf713Rad := by
          have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
          nlinarith [norm_nonneg w, erf713Rad_pos]
        refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
        · show ‖(-w : ℂ)‖ ≤ erf713Rad
          rw [norm_neg]; exact hzlt.le
        · show cerf (-w) = 0
          rw [cerf_neg, hzz, neg_zero]
      · obtain ⟨hzz, _, _, hzsq⟩ := hwQ1
        have hzlt : ‖w‖ < erf713Rad := by
          have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
          nlinarith [norm_nonneg w, erf713Rad_pos]
        refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
        · show ‖(starRingEnd ℂ w)‖ ≤ erf713Rad
          rw [Complex.norm_conj]; exact hzlt.le
        · show cerf (starRingEnd ℂ w) = 0
          rw [cerf_conj, hzz, map_zero]
      · obtain ⟨hzz, _, _, hzsq⟩ := hwQ1
        have hzlt : ‖w‖ < erf713Rad := by
          have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
          nlinarith [norm_nonneg w, erf713Rad_pos]
        refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
        · show ‖(-(starRingEnd ℂ w))‖ ≤ erf713Rad
          rw [norm_neg, Complex.norm_conj]; exact hzlt.le
        · show cerf (-(starRingEnd ℂ w)) = 0
          rw [cerf_neg, cerf_conj, hzz, map_zero, neg_zero]
  -- Sign facts pinning down each of the five pieces to a distinct region.
  have hsignQ1 : ∀ p ∈ Q1, 0 < p.re ∧ 0 < p.im := fun p hp => ⟨hp.2.1, hp.2.2.1⟩
  have hsignNeg : ∀ p ∈ (fun w => -w) '' Q1, p.re < 0 ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.neg_re]; linarith [(hsignQ1 w hw).1],
      by rw [Complex.neg_im]; linarith [(hsignQ1 w hw).2]⟩
  have hsignConj : ∀ p ∈ (fun w => starRingEnd ℂ w) '' Q1, 0 < p.re ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.conj_re]; exact (hsignQ1 w hw).1,
      by rw [Complex.conj_im]; linarith [(hsignQ1 w hw).2]⟩
  have hsignNegConj : ∀ p ∈ (fun w => -(starRingEnd ℂ w)) '' Q1, p.re < 0 ∧ 0 < p.im := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.neg_re, Complex.conj_re]; linarith [(hsignQ1 w hw).1],
      by rw [Complex.neg_im, Complex.conj_im]; linarith [(hsignQ1 w hw).2]⟩
  -- Pairwise disjointness of the five pieces, from the sign facts.
  have hd1 : Disjoint ({0} : Set ℂ) Q1 := by
    rw [Set.disjoint_left]; rintro p hp hpQ1; rw [Set.mem_singleton_iff] at hp
    have := (hsignQ1 p hpQ1).1; rw [hp] at this; simp at this
  have hd2 : Disjoint ({0} : Set ℂ) ((fun w => -w) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp hpN; rw [Set.mem_singleton_iff] at hp
    have := (hsignNeg p hpN).1; rw [hp] at this; simp at this
  have hd3 : Disjoint ({0} : Set ℂ) ((fun w => starRingEnd ℂ w) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp hpC; rw [Set.mem_singleton_iff] at hp
    have := (hsignConj p hpC).1; rw [hp] at this; simp at this
  have hd4 : Disjoint ({0} : Set ℂ) ((fun w => -(starRingEnd ℂ w)) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp hpNC; rw [Set.mem_singleton_iff] at hp
    have := (hsignNegConj p hpNC).1; rw [hp] at this; simp at this
  have hd5 : Disjoint Q1 ((fun w => -w) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignQ1 p hp1).1, (hsignNeg p hp2).1]
  have hd6 : Disjoint Q1 ((fun w => starRingEnd ℂ w) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignQ1 p hp1).2, (hsignConj p hp2).2]
  have hd7 : Disjoint Q1 ((fun w => -(starRingEnd ℂ w)) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignQ1 p hp1).1, (hsignNegConj p hp2).1]
  have hd8 : Disjoint ((fun w => -w) '' Q1) ((fun w => starRingEnd ℂ w) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignNeg p hp1).1, (hsignConj p hp2).1]
  have hd9 : Disjoint ((fun w => -w) '' Q1) ((fun w => -(starRingEnd ℂ w)) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignNeg p hp1).2, (hsignNegConj p hp2).2]
  have hd10 : Disjoint ((fun w => starRingEnd ℂ w) '' Q1) ((fun w => -(starRingEnd ℂ w)) '' Q1) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignConj p hp1).1, (hsignNegConj p hp2).1]
  -- `Q1` is finite (a subset of the finite `Z`), so are its images.
  have hQ1subZ : Q1 ⊆ closedBall (0 : ℂ) erf713Rad ∩ cerf ⁻¹' {0} := by
    intro w hw
    obtain ⟨hzz, _, _, hzsq⟩ := hw
    have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
    have hwlt : ‖w‖ < erf713Rad := by nlinarith [norm_nonneg w, erf713Rad_pos]
    exact ⟨mem_closedBall_zero_iff.mpr hwlt.le, hzz⟩
  have hQ1fin : Q1.Finite := hZfin.subset hQ1subZ
  have hNegInj : Function.Injective (fun w : ℂ => -w) := neg_injective
  have hConjInj : Function.Injective (fun w : ℂ => starRingEnd ℂ w) :=
    Function.LeftInverse.injective (fun x => starRingEnd_self_apply x)
  have hNegConjInj : Function.Injective (fun w : ℂ => -(starRingEnd ℂ w)) :=
    neg_injective.comp hConjInj
  have hNegImgFin : ((fun w : ℂ => -w) '' Q1).Finite := hQ1fin.image _
  have hConjImgFin : ((fun w : ℂ => starRingEnd ℂ w) '' Q1).Finite := hQ1fin.image _
  have hNegConjImgFin : ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q1).Finite := hQ1fin.image _
  have hNegImgCard : ((fun w : ℂ => -w) '' Q1).ncard = Q1.ncard :=
    Set.ncard_image_of_injective Q1 hNegInj
  have hConjImgCard : ((fun w : ℂ => starRingEnd ℂ w) '' Q1).ncard = Q1.ncard :=
    Set.ncard_image_of_injective Q1 hConjInj
  have hNegConjImgCard : ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q1).ncard = Q1.ncard :=
    Set.ncard_image_of_injective Q1 hNegConjInj
  -- Cardinality assembly, bottom-up through the (left-associated) union.
  have hX1fin : ({0} ∪ Q1 : Set ℂ).Finite := (Set.finite_singleton 0).union hQ1fin
  have hX1card : ({0} ∪ Q1 : Set ℂ).ncard = 1 + Q1.ncard := by
    rw [Set.ncard_union_eq hd1 (Set.finite_singleton 0) hQ1fin, Set.ncard_singleton]
  have hdX1Neg : Disjoint ({0} ∪ Q1 : Set ℂ) ((fun w : ℂ => -w) '' Q1) := by
    rw [Set.disjoint_left]
    rintro p hp hpN
    rcases hp with hp0 | hpQ1
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignNeg p hpN).1; rw [hp0] at this; simp at this
    · linarith [(hsignQ1 p hpQ1).1, (hsignNeg p hpN).1]
  have hX2fin : (({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1 : Set ℂ).Finite := hX1fin.union hNegImgFin
  have hX2card : (({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1 : Set ℂ).ncard = 1 + 2 * Q1.ncard := by
    rw [Set.ncard_union_eq hdX1Neg hX1fin hNegImgFin, hX1card, hNegImgCard]; ring
  have hdX2Conj : Disjoint ((({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1) : Set ℂ)
      ((fun w : ℂ => starRingEnd ℂ w) '' Q1) := by
    rw [Set.disjoint_left]
    rintro p hp hpC
    rcases hp with (hp0 | hpQ1) | hpN
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignConj p hpC).1; rw [hp0] at this; simp at this
    · linarith [(hsignQ1 p hpQ1).2, (hsignConj p hpC).2]
    · linarith [(hsignNeg p hpN).1, (hsignConj p hpC).1]
  have hX3fin : ((({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1) ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q1
      : Set ℂ).Finite := hX2fin.union hConjImgFin
  have hX3card : ((({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1) ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q1
      : Set ℂ).ncard = 1 + 3 * Q1.ncard := by
    rw [Set.ncard_union_eq hdX2Conj hX2fin hConjImgFin, hX2card, hConjImgCard]; ring
  have hdX3NegConj : Disjoint (((({0} ∪ Q1) ∪ (fun w : ℂ => -w) '' Q1)
      ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q1) : Set ℂ)
      ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q1) := by
    rw [Set.disjoint_left]
    rintro p hp hpNC
    rcases hp with ((hp0 | hpQ1) | hpN) | hpC
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignNegConj p hpNC).1; rw [hp0] at this; simp at this
    · linarith [(hsignQ1 p hpQ1).1, (hsignNegConj p hpNC).1]
    · linarith [(hsignNeg p hpN).2, (hsignNegConj p hpNC).2]
    · linarith [(hsignConj p hpC).1, (hsignNegConj p hpNC).1]
  have hcardEq : (closedBall (0 : ℂ) erf713Rad ∩ cerf ⁻¹' {0} : Set ℂ).ncard = 1 + 4 * Q1.ncard := by
    rw [hZeq, Set.ncard_union_eq hdX3NegConj hX3fin hNegConjImgFin, hX3card, hNegConjImgCard]
    ring
  have hPcard : P.card = (closedBall (0 : ℂ) erf713Rad ∩ cerf ⁻¹' {0}).ncard := by
    rw [hPdef]; exact (Set.ncard_eq_toFinset_card _ hZfin).symm
  rw [hPcard, hcardEq]
  push_cast
  ring

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerf`; proof infrastructure for the §7.13 zero count
/-- No zero of `cerf` has infinite analytic order: `cerf` is not locally zero,
because its derivative `(2/√π)e^{−z²}` never vanishes (`deriv_cerf_ne_zero`). -/
theorem cerf_analyticOrder_ne_top (z : ℂ) : analyticOrderAt cerf z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  -- `cerf` vanishes identically near `z`, so its derivative vanishes at `z`
  have hd : deriv cerf z = deriv (fun _ : ℂ => (0 : ℂ)) z :=
    Filter.EventuallyEq.deriv_eq htop
  rw [deriv_const] at hd
  exact deriv_cerf_ne_zero z hd

/-! ### The assembly

The pieces above compose to the zero count itself, with no further mathematics. -/

-- no-dlmf: the count of the small first-quadrant zeros of `erf`; the single arithmetic input
-- to DLMF 7.13.1 that the asymptotic machinery of this file cannot supply
/-- **The number of small first-quadrant zeros of `erf`.**  `erf` has exactly `3499` zeros `w`
in the open first quadrant with `‖w‖² < 21987`.

**Proved** by the argument principle.  Route: the Klein symmetry group `{1, −1, conj, −conj}`
of `cerf` (which is odd and conjugation-symmetric) meets each open quadrant exactly once on every
orbit of a nonzero zero, so the multiplicity-weighted count on the closed disc `‖z‖ ≤ √21987` is
`1 + 4·N` with `N` the count sought here (`erf713_zeros_finset_exists`); the same two symmetries
fold the circle integral of `cerf'/cerf` onto the quarter arc
(`erf713_circle_eq_four_I_arc_im`), and on that arc `cerf` is compared with the elementary model
`M = 1 − e^{−z²}/(√π z)`, whose logarithmic-derivative integral is closed form
(`erf713_modelArc_im`).  The contour value is `2πi·13997 = 2πi·(1 + 4·3499)`.

Its role is to fix the *origin* of the enumeration: the asymptotic analysis
above establishes a strictly modulus-increasing bijection between the first-quadrant zeros with
`‖w‖² ≥ 21987` and the indices `n ≥ 3500` (`erf713_grid_zero`, `erf713_zero_has_index`,
`erf713_zero_index_unique`), which determines DLMF's enumeration only up to a constant index
offset.  The offset vanishes exactly when the number of zeros below the cut equals the number
of grid points below it, i.e. when the count here is `3500 − 1 = 3499`.

The threshold `21987` is chosen strictly between the two neighbouring grid values
`2λ₃₄₉₉² ≈ 21984.08` and `2λ₃₅₀₀² ≈ 21990.36`, with margin larger than the `±1` localization of
`erf713_approx_norm_sq`; so no zero of index `3499` or `3500` sits ambiguously at the cut.

The count itself is a bounded-region zero count, not an asymptotic estimate: it is carried out
on an explicit contour with `FLMF.Methods.AnalyticZeroCount`
(`circleIntegral_logDeriv_eq_sum_orders` on the full disc, `arc_logDeriv_integral` on the
quarter arc). -/
theorem erf713_low_zero_count :
    {w : ℂ | cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}.ncard = 3499 := by
  classical
  obtain ⟨P, hP, hPball, hsum⟩ := erf713_zeros_finset_exists
  set N : ℕ := {w : ℂ | cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}.ncard with hN
  -- the argument principle on the full disc (`FLMF.Methods.AnalyticZeroCount`)
  have hAP := circleIntegral_logDeriv_eq_sum_orders (f := cerf) (c := 0) (R := erf713Rad)
    erf713Rad_pos P (fun z _ => analyticAt_cerf z) hP hPball
    (fun p _ => cerf_analyticOrder_ne_top p)
  -- the contour value, via the symmetry reduction and the arc computation
  have hval : (∮ z in C((0:ℂ), erf713Rad), deriv cerf z / cerf z)
      = 2 * (Real.pi : ℂ) * I * (13997 : ℂ) := by
    rw [erf713_circle_eq_four_I_arc_im, erf713_arc_cerf_im]
    push_cast
    ring
  rw [hval, hsum] at hAP
  -- `2πi·14000 = 2πi·(1 + 4N)`  ⟹  `N = 3499`
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simpa using (Real.pi_ne_zero)
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hcancel : (13997 : ℂ) = 1 + 4 * (N : ℂ) := mul_left_cancel₀ h2 hAP
  have : (13997 : ℝ) = 1 + 4 * (N : ℝ) := by exact_mod_cast congrArg Complex.re hcancel
  have : (N : ℝ) = 3499 := by linarith
  exact_mod_cast this

end Erf713ZeroCount

set_option maxHeartbeats 1000000 in
/-- **DLMF 7.13.1** — asymptotic expansion of the first-quadrant zeros
`zₙ = xₙ + i yₙ` of `erf`. For the complete enumeration `z`, ordered by
increasing absolute value (DLMF §7.13(i)), of ALL zeros of `cerf` in the open first
quadrant (`hall`), the real and imaginary
parts of `z n` agree with the three-term approximations `erfZeroReApprox`,
`erfZeroImApprox` (built from `λ`, `μ` of 7.13.2) up to `o(λ⁻³)`.

**Index origin.** DLMF numbers the first-quadrant zeros from `n = 1`, and the enumeration
here matches that 1-based labelling directly: only `z n` for `1 ≤ n` is constrained
(`z 0` is unconstrained junk, harmless in the `=o[atTop]` conclusions, which ignore any
finite prefix), the hypotheses order `z 1, z 2, …` by increasing absolute value, and
`z n` is DLMF's `zₙ`, compared with the `n`-th approximations. (Comparing DLMF's `zₙ`
with the parameters at any shifted index would be off by a full grid step
`λ_{n+1} − λ_n ≍ √π/(2√n) ≫ λ_n⁻³`.)
* dlmf: 7.13.1
* family: error
* kind: zero-asymptotic

DLMF 7.13.1.
Numerical: N/A (conjunction-partial)
Verified: verified
DAG: E-7.13.1.
-/
theorem erf_7_13_1 (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cerf (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).re ∧ 0 < (z n).im)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cerf w = 0 → 0 < w.re → 0 < w.im → ∃ n, 1 ≤ n ∧ z n = w) :
    (fun n => (z n).re - erfZeroReApprox n) =o[atTop]
        (fun n => (erfZeroLambda n) ^ (-3 : ℤ)) ∧
      (fun n => (z n).im - erfZeroImApprox n) =o[atTop]
        (fun n => (erfZeroLambda n) ^ (-3 : ℤ)) := by
  classical
  -- the grid zeros
  have hex : ∀ m : ℕ, ∃ u : ℂ, 3400 ≤ m → (cerf u = 0 ∧ 0 < u.re ∧ 0 < u.im ∧
      |u.re - erfZeroReApprox m| ≤ (erfZeroMu m + 3) ^ 4 / (20 * erfZeroLambda m ^ 5) ∧
      |u.im - erfZeroImApprox m| ≤ (erfZeroMu m + 3) ^ 4 / (20 * erfZeroLambda m ^ 5)) := by
    intro m
    by_cases h : 3400 ≤ m
    · obtain ⟨u, h1, h2, h3, h4, h5⟩ := erf713_grid_zero m h
      exact ⟨u, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose W hW using hex
  have hWnorm : ∀ m : ℕ, 3400 ≤ m → |‖W m‖ ^ 2 - 2 * erfZeroLambda m ^ 2| ≤ 1 := by
    intro m hm
    obtain ⟨-, -, -, h4, h5⟩ := hW m hm
    exact (erf713_approx_norm_sq hm h4 h5).1
  have hlamgap : ∀ m m' : ℕ, 1 ≤ m → m < m' →
      2 * erfZeroLambda m ^ 2 + 6 ≤ 2 * erfZeroLambda m' ^ 2 := by
    intro m m' hm hlt
    have h1 := erf713_lambda_sq hm
    have h2 := erf713_lambda_sq (n := m') (by omega)
    have h3 : (m:ℝ) + 1 ≤ (m':ℝ) := by exact_mod_cast hlt
    have hpi := Real.pi_gt_three
    rw [h1, h2]; nlinarith
  have hWmono : ∀ m m' : ℕ, 3400 ≤ m → m < m' → ‖W m‖ < ‖W m'‖ := by
    intro m m' hm hlt
    have hm' : 3400 ≤ m' := by omega
    obtain ⟨a1, a2⟩ := abs_le.mp (hWnorm m hm)
    obtain ⟨b1, b2⟩ := abs_le.mp (hWnorm m' hm')
    have hgap := hlamgap m m' (by omega) hlt
    have hsq : ‖W m‖ ^ 2 < ‖W m'‖ ^ 2 := by linarith
    nlinarith [norm_nonneg (W m), norm_nonneg (W m')]
  have hWinj : ∀ m m' : ℕ, 3400 ≤ m → 3400 ≤ m' → ‖W m‖ = ‖W m'‖ → m = m' := by
    intro m m' hm hm' heq
    rcases lt_trichotomy m m' with h | h | h
    · exact absurd heq (ne_of_lt (hWmono m m' hm h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hWmono m' m hm' h))
  have hWbig : ∀ m : ℕ, 3500 ≤ m → 21987 ≤ ‖W m‖ ^ 2 := by
    intro m hm
    obtain ⟨a1, a2⟩ := abs_le.mp (hWnorm m (by omega))
    have hl := erf713_lambda_sq (n := m) (by omega)
    have hmr : (3500:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hpi := Real.pi_gt_d6
    have hprod : (3499.875:ℝ) * 3.141592 ≤ ((m:ℝ) - 1/8) * Real.pi := by nlinarith
    rw [hl] at a1
    nlinarith
  have hzeroW : ∀ u : ℂ, cerf u = 0 → 0 < u.re → 0 < u.im → 21987 ≤ ‖u‖ ^ 2 →
      ∃ n : ℕ, 3500 ≤ n ∧ u = W n := by
    intro u hu hur hui hub
    obtain ⟨n, hn, h1, h2⟩ := erf713_zero_has_index hu hur hui hub
    obtain ⟨g1, -, -, g4, g5⟩ := hW n (by omega)
    exact ⟨n, hn, erf713_zero_index_unique (by omega) hu g1 h1 h2 g4 g5⟩
  -- the smallest enumeration index whose zero is beyond the cut
  have hPne : ∃ m : ℕ, 1 ≤ m ∧ 21987 ≤ ‖z m‖ ^ 2 := by
    obtain ⟨g1, g2, g3, -, -⟩ := hW 3500 (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W 3500) g1 g2 g3
    exact ⟨m, hm1, by rw [hm2]; exact hWbig 3500 (le_refl _)⟩
  set M : ℕ := Nat.find hPne with hMdef
  have hM1 : 1 ≤ M := (Nat.find_spec hPne).1
  have hM2 : 21987 ≤ ‖z M‖ ^ 2 := (Nat.find_spec hPne).2
  have hMmin : ∀ m : ℕ, m < M → ¬(1 ≤ m ∧ 21987 ≤ ‖z m‖ ^ 2) := fun m hm => Nat.find_min hPne hm
  have hzbig : ∀ m : ℕ, M ≤ m → 21987 ≤ ‖z m‖ ^ 2 := by
    intro m hm
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h]; exact hM2
    · have hlt : ‖z M‖ < ‖z m‖ := hmono hM1 (by omega : 1 ≤ m) h
      nlinarith [norm_nonneg (z M), norm_nonneg (z m)]
  -- the index attached to each enumeration entry beyond the cut
  have hfex : ∀ m : ℕ, ∃ n : ℕ, M ≤ m → (3500 ≤ n ∧ z m = W n) := by
    intro m
    by_cases h : M ≤ m
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨q1, q2⟩ := hquad m hm1
      obtain ⟨n, hn, heq⟩ := hzeroW (z m) (hzero m hm1) q1 q2 (hzbig m h)
      exact ⟨n, fun _ => ⟨hn, heq⟩⟩
    · exact ⟨3500, fun h' => absurd h' h⟩
  choose f hf using hfex
  have hfmono : ∀ m m' : ℕ, M ≤ m → m < m' → f m < f m' := by
    intro m m' hm hlt
    obtain ⟨hn1, he1⟩ := hf m hm
    obtain ⟨hn2, he2⟩ := hf m' (by omega)
    have hlt' : ‖z m‖ < ‖z m'‖ := hmono (by omega : 1 ≤ m) (by omega : 1 ≤ m') hlt
    rw [he1, he2] at hlt'
    by_contra hcon
    have hle : f m' ≤ f m := by omega
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at hlt'; exact lt_irrefl _ hlt'
    · exact absurd hlt' (not_lt.mpr (hWmono (f m') (f m) (by omega) h).le)
  have hfsurj : ∀ n : ℕ, f M ≤ n → ∃ m : ℕ, M ≤ m ∧ f m = n := by
    intro n hn
    obtain ⟨hfM1, hfMe⟩ := hf M (le_refl M)
    have hn3500 : 3500 ≤ n := by omega
    obtain ⟨g1, g2, g3, -, -⟩ := hW n (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W n) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig n hn3500⟩
    obtain ⟨hq1, hq2⟩ := hf m hmM
    have heq : ‖W (f m)‖ = ‖W n‖ := by rw [← hq2, hm2]
    exact ⟨m, hmM, hWinj _ _ (by omega) (by omega) heq⟩
  -- a strictly monotone surjection onto a tail of `ℕ` is a shift
  have hfform : ∀ m : ℕ, M ≤ m → f m + M = m + f M := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ k ih =>
      intro hm
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; omega
      · have hk : M ≤ k := by omega
        have ihk := ih hk
        have h1 : f k < f (k+1) := hfmono k (k+1) hk (by omega)
        by_contra hcon
        have h2 : f k + 1 < f (k+1) := by omega
        have h3 : f M ≤ f k + 1 := by omega
        obtain ⟨m', hm'1, hm'2⟩ := hfsurj (f k + 1) h3
        rcases Nat.lt_or_ge k m' with h4 | h4
        · have h4' : k + 1 ≤ m' := h4
          rcases eq_or_lt_of_le h4' with h6 | h6
          · rw [← h6] at hm'2; omega
          · have := hfmono (k+1) m' (by omega) h6; omega
        · rcases eq_or_lt_of_le h4 with h5 | h5
          · rw [h5] at hm'2; omega
          · have := hfmono m' k hm'1 h5; omega
  -- the first index beyond the cut is the grid index `3500`
  have hfM : f M = 3500 := by
    obtain ⟨hfM1, hfMe⟩ := hf M (le_refl M)
    refine le_antisymm ?_ hfM1
    obtain ⟨g1, g2, g3, -, -⟩ := hW 3500 (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W 3500) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig 3500 (le_refl _)⟩
    have hle : ‖z M‖ ≤ ‖z m‖ := by
      rcases eq_or_lt_of_le hmM with h | h
      · rw [h]
      · exact (hmono hM1 (by omega : 1 ≤ m) h).le
    rw [hm2, hfMe] at hle
    by_contra hcon
    have h3500 : 3500 < f M := by omega
    exact absurd hle (not_le.mpr (hWmono 3500 (f M) (by omega) h3500))
  -- the count of the small zeros pins the enumeration origin
  have hzinj : Set.InjOn z {n : ℕ | 1 ≤ n} := by
    intro a ha b hb hab
    exact hmono.injOn ha hb (by show ‖z a‖ = ‖z b‖; rw [hab])
  have hMcount : M = 3500 := by
    have hset : {w : ℂ | cerf w = 0 ∧ 0 < w.re ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}
        = ↑((Finset.Ico 1 M).image z) := by
      ext u
      simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hur, hui, hub⟩
        obtain ⟨m, hm1, hm2⟩ := hall u hu hur hui
        refine ⟨m, ⟨hm1, ?_⟩, hm2⟩
        by_contra hcon
        have hMle : M ≤ m := by omega
        have hb := hzbig m hMle
        rw [hm2] at hb
        linarith
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        obtain ⟨q1, q2⟩ := hquad m hm1
        refine ⟨hzero m hm1, q1, q2, ?_⟩
        by_contra hcon
        exact hMmin m hm2 ⟨hm1, not_lt.mp hcon⟩
    have hcard : ((Finset.Ico 1 M).image z).card = M - 1 := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]
      intro a ha b hb hab
      refine hzinj ?_ ?_ hab
      · simp only [Finset.coe_Ico, Set.mem_Ico] at ha; exact ha.1
      · simp only [Finset.coe_Ico, Set.mem_Ico] at hb; exact hb.1
    have hcount := erf713_low_zero_count
    rw [hset, Set.ncard_coe_finset, hcard] at hcount
    omega
  -- hence the enumeration *is* the grid family from index `3500` on
  have hzW : ∀ m : ℕ, 3500 ≤ m → z m = W m := by
    intro m hm
    obtain ⟨-, he⟩ := hf m (by omega)
    have hfm : f m = m := by have h := hfform m (by omega); omega
    rw [he, hfm]
  -- the expansion error is `O(λ⁻⁴)`
  have hDbound : ∀ m : ℕ, 3400 ≤ m →
      (erfZeroMu m + 3) ^ 4 / (20 * erfZeroLambda m ^ 5) ≤ 65 / erfZeroLambda m ^ 4 := by
    intro m hm
    obtain ⟨hlam, -, -, -⟩ := erf713_param_bounds hm
    have hlam0 : (0:ℝ) < erfZeroLambda m := by linarith
    have hq := erf713_mu_quartic hm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg hlam0.le 4)
    have h2 : 1296 * erfZeroLambda m * erfZeroLambda m ^ 4
        = 1296 * erfZeroLambda m ^ 5 := by ring
    rw [h2] at h1
    linarith [h1, pow_pos hlam0 5]
  have hlamge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ erfZeroLambda m ^ 2 := by
    intro m hm
    rw [erf713_lambda_sq hm]
    have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  have key : ∀ F : ℕ → ℝ, (∀ m : ℕ, 3500 ≤ m → |F m| ≤ 65 / erfZeroLambda m ^ 4) →
      F =o[atTop] (fun m => (erfZeroLambda m) ^ (-3 : ℤ)) := by
    intro F hF
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Filter.eventually_ge_atTop (max 3500 ⌈(65/c)^2⌉₊)] with m hm
    have hm3500 : 3500 ≤ m := le_trans (le_max_left _ _) hm
    have hlam0 : (0:ℝ) < erfZeroLambda m := by
      obtain ⟨hlam, -, -, -⟩ := erf713_param_bounds (show 3400 ≤ m by omega); linarith
    have hceil : ((65/c)^2 : ℝ) ≤ (m:ℝ) := by
      have h1 : (⌈(65/c)^2⌉₊ : ℝ) ≤ (m:ℝ) := by
        exact_mod_cast le_trans (le_max_right 3500 ⌈(65/c)^2⌉₊) hm
      exact le_trans (Nat.le_ceil _) h1
    have hlamge' : (65/c) ≤ erfZeroLambda m := by
      have h := hlamge m (by omega)
      have hpos : (0:ℝ) ≤ 65/c := by positivity
      nlinarith [h, hceil, hlam0]
    have hcl : (65:ℝ) ≤ c * erfZeroLambda m := by
      have h1 : c * (65/c) = 65 := by field_simp
      have h2 := mul_le_mul_of_nonneg_left hlamge' hc.le
      linarith [h1.le, h1.ge]
    have hz : (erfZeroLambda m) ^ (-3 : ℤ) = (erfZeroLambda m ^ 3)⁻¹ := by
      rw [show (-3:ℤ) = -(3:ℕ) by norm_num, zpow_neg, zpow_natCast]
    have hfin : 65 / erfZeroLambda m ^ 4 ≤ c * (erfZeroLambda m ^ 3)⁻¹ := by
      rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcl (pow_nonneg hlam0.le 3), hlam0]
    have h := hF m hm3500
    simp only [Real.norm_eq_abs, hz, abs_of_pos (show (0:ℝ) < (erfZeroLambda m ^ 3)⁻¹ by
      positivity)]
    linarith
  constructor
  · refine key _ ?_
    intro m hm
    obtain ⟨-, -, -, h4, -⟩ := hW m (show 3400 ≤ m by omega)
    rw [hzW m hm]
    exact le_trans h4 (hDbound m (by omega))
  · refine key _ ?_
    intro m hm
    obtain ⟨-, -, -, -, h5⟩ := hW m (show 3400 ≤ m by omega)
    rw [hzW m hm]
    exact le_trans h5 (hDbound m (by omega))

/-! ## erfc zeros — parameters (DLMF 7.13.4) -/

-- no-dlmf: encodes the 7.13.4 parameter λ; display surfaced at `erf_7_13_4`
/-- DLMF 7.13.4 (parameter `λ'` for the `n`-th zero of `erfc`):
`λ' = √((n − 1/8)·π)`.
* dlmf: 7.13.4
* family: error
* kind: zero-asymptotic-parameter -/
def erfcZeroLambda (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) - 1 / 8) * Real.pi)

-- no-dlmf: encodes the 7.13.4 parameter μ; display surfaced at `erf_7_13_4`
/-- DLMF 7.13.4 (parameter `μ'` for the `n`-th zero of `erfc`):
`μ' = log (2·λ' · √(2π))`.
* dlmf: 7.13.4
* family: error
* kind: zero-asymptotic-parameter -/
def erfcZeroMu (n : ℕ) : ℝ := Real.log (2 * erfcZeroLambda n * Real.sqrt (2 * Real.pi))

/-- DLMF 7.13.4 — records the parameter equations for the `erfc` zeros.

DLMF §7.13 indexes these zeros `n = 1, 2, 3, …` (Tables 7.13.1–7.13.4 tabulate
`n = 1..5`), matching `erf_7_13_1`'s 1-based enumeration; the `1 ≤ n` hypothesis
is that index range, not a narrowing. On it every displayed logarithm argument is
a positive real, where `Real.log` coincides with DLMF's principal branch `ln`, and
`Real.sqrt` with the principal square root.

Numerical: PASS
Verified: verified
DAG: E-7.13.4.
-/
theorem erf_7_13_4 (n : ℕ) (_hn : 1 ≤ n) :
    erfcZeroLambda n = Real.sqrt (((n : ℝ) - 1 / 8) * Real.pi) ∧
      erfcZeroMu n = Real.log (2 * erfcZeroLambda n * Real.sqrt (2 * Real.pi)) :=
  ⟨rfl, rfl⟩

/-! ## erfc zeros — approximation (DLMF 7.13.3) -/

-- no-dlmf: encodes the 7.13.3 approximant; display surfaced at `erf_7_13_3`
/-- DLMF 7.13.3 — three-term approximation of the real part of the `n`-th zero of
`erfc` (in the sector `re < 0 < im`):
`xₙ = −λ' + (1/4)·μ'·λ'⁻¹ − (1/16)·(1 − μ' + ½μ'²)·λ'⁻³`.
* dlmf: 7.13.3
* family: error
* kind: zero-approximation -/
def erfcZeroReApprox (n : ℕ) : ℝ :=
  let lam := erfcZeroLambda n
  let mu := erfcZeroMu n
  (-lam) + (1 / 4) * mu * lam⁻¹ - (1 / 16) * (1 - mu + (1 / 2) * mu ^ 2) * lam⁻¹ ^ 3

-- no-dlmf: encodes the 7.13.3 approximant; display surfaced at `erf_7_13_3`
/-- DLMF 7.13.3 — three-term approximation of the imaginary part of the `n`-th
zero of `erfc` (in the sector `re < 0 < im`):
`yₙ = λ' + (1/4)·μ'·λ'⁻¹ + (1/16)·(1 − μ' + ½μ'²)·λ'⁻³`.
* dlmf: 7.13.3
* family: error
* kind: zero-approximation -/
def erfcZeroImApprox (n : ℕ) : ℝ :=
  let lam := erfcZeroLambda n
  let mu := erfcZeroMu n
  lam + (1 / 4) * mu * lam⁻¹ + (1 / 16) * (1 - mu + (1 / 2) * mu ^ 2) * lam⁻¹ ^ 3

/-! ## erfc zeros — the reflected pipeline (DLMF 7.13.3)

The zeros of `erfc` in the sector `re < 0 < im` are folded onto the open first quadrant by the
involution `v = −conj u`: since `cerf` has real Taylor coefficients and is odd,

`erfc u = 0  ⟺  erf u = 1  ⟺  erf (−conj u) = −1  ⟺  erfc (−conj u) = 2`.

At such a `v` the Poincaré bound `cerfc_poincare_bound` (applicable, since `|ph v| < π/2`) reads
`‖√π v e^{v²}·2 − 1‖ ≤ 4/‖v‖²`, i.e. the model equation is `√(4π)·v·e^{v²} = 1` — the same
equation as for `erf`, with `√π` replaced by `2√π = √(4π)`.  That single constant change is
exactly the factor `2` in `μ' = log(2λ√(2π))` of DLMF 7.13.4, and it is the only difference
between this pipeline and the `erf` one above: the real component equation acquires
`L = ½log(4π‖v‖²)` in place of `½log(π‖v‖²)` (`erfc713_crude`), while the imaginary component,
and hence the whole abstract inversion `erf713_first_order` → `erf713_diff_expansion` →
`erf713_sum_expansion`, is reused verbatim. -/

-- no-dlmf: the elementary identity `√(4π) = 2√π` relating the `erfc` model constant to the
-- `erf` one; proof infrastructure for the §7.13 zero asymptotics
/-- `√(4π) = 2√π`.  The `erfc` zero equation carries the constant `2√π`, which is written
throughout as the single square root `√(4π)` so that the `erf` proofs transcribe verbatim. -/
theorem sqrt_four_pi : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
  rw [show (4:ℝ) * Real.pi = 2 ^ 2 * Real.pi by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

-- no-dlmf: the reflection `u ↦ −conj u` folding the `erfc` zeros onto the first quadrant;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **The erfc zeros, folded onto the first quadrant.**  `erfc u = 0 ⟺ erf (−conj u) = −1`.

`erfc u = 0` means `erf u = 1`; `cerf` is odd (`cerf_neg`) and has real Taylor coefficients
(`cerf_conj`), so `erf (−conj u) = −conj (erf u) = −1`.  The involution `u ↦ −conj u` preserves
the modulus, sends the sector `re < 0 < im` of DLMF §7.13(ii) to the open first quadrant, and
turns `erfc u = 0` into `erfc (−conj u) = 2` — the equation whose Poincaré analysis produces the
model equation `√(4π) v e^{v²} = 1`. -/
theorem cerfc_zero_iff {w : ℂ} :
    cerfc w = 0 ↔ cerf (-(starRingEnd ℂ w)) = -1 := by
  rw [cerf_neg, cerf_conj, cerfc, sub_eq_zero]
  constructor
  · intro h; rw [← h]; simp
  · intro h
    have : (starRingEnd ℂ) (cerf w) = 1 := by
      have := congrArg Neg.neg h; simpa using this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2.symm

-- no-dlmf: the `n = 1` truncation of the Poincaré expansion evaluated at a point where
-- `erf = −1`; proof infrastructure for the §7.13 zero asymptotics
/-- **The effective equation for the reflected `erfc` zeros.**  If `Re v > 0` and `erf v = −1` —
equivalently `erfc v = 2` — then

`‖√(4π) · v · e^{v²} − 1‖ ≤ 4 / ‖v‖²`.

This is `cerfc_scaled_leading_bound` (the `n = 1` sector bound, valid on the whole open right
half-plane) evaluated at `erfc v = 2` and multiplied by `v`: the constant `2` of `erfc v = 2` is
what turns the `erf` model constant `√π` into `2√π = √(4π)`, and hence produces the factor `2`
in `μ' = log(2λ√(2π))` of DLMF 7.13.4. -/
theorem cerf_negone_equation {v : ℂ} (hv : cerf v = -1) (hre : 0 < v.re) :
    ‖(Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - 1‖ ≤ 4 / ‖v‖ ^ 2 := by
  have hz : v ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have h := cerfc_scaled_leading_bound hre
  have hcerfc : cerfc v = 2 := by rw [cerfc, hv]; ring
  rw [hcerfc] at h
  have hadd : ‖(Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2) - v⁻¹‖ ≤ 4 / ‖v‖ ^ 3 := by
    refine le_trans (le_of_eq ?_) h
    congr 2
    push_cast [sqrt_four_pi]
    ring
  have hfac : (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - 1
      = v * ((Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2) - v⁻¹) := by
    field_simp
  rw [hfac, norm_mul]
  calc ‖v‖ * ‖(Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2) - v⁻¹‖
      ≤ ‖v‖ * (4 / ‖v‖ ^ 3) := mul_le_mul_of_nonneg_left hadd hvn.le
    _ = 4 / ‖v‖ ^ 2 := by field_simp

-- no-dlmf: the `n = 2` truncation of the Poincaré expansion at a point where `erf = −1`;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **The second-order effective equation for the reflected `erfc` zeros.**  If `Re v > 0`,
`erf v = −1` and `‖v‖ ≥ 4`, then

`‖√(4π) · v · e^{v²} − (1 − 1/(2v²))‖ ≤ 48 / ‖v‖⁴`.

The `erfc` analogue of `cerf_zero_equation_third`; the extra term `−1/(2v²)` is what produces
the `+2` in the numerator `1 − μ' + μ'²/2` of the `λ⁻³` coefficient of DLMF 7.13.3. -/
theorem cerf_negone_equation_third {v : ℂ} (hv : cerf v = -1) (hre : 0 < v.re) (hbig : 4 ≤ ‖v‖) :
    ‖(Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - 1 / (2 * v ^ 2))‖
      ≤ 48 / ‖v‖ ^ 4 := by
  have hz : v ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hsec : |Complex.arg v| ≤ 3 * Real.pi / 4 - Real.pi / 4 := by
    have h : |Complex.arg v| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 4) (by positivity)
    (by linarith [Real.pi_pos]) hz hsec 2
  have hcerfc : cerfc v = 2 := by rw [cerfc, hv]; ring
  have hsin : Real.sin (2 * (Real.pi / 4) / 3) = 1 / 2 := by
    rw [show 2 * (Real.pi / 4) / 3 = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hcerfc, hsin] at h
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  norm_num at h
  rw [show (2 * (1 / 2 * ‖v‖)) ^ 5 = ‖v‖ ^ 5 by ring] at h
  have hbd : ‖(Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2)
      - (v⁻¹ + -(1 / 2) / v ^ 3)‖ ≤ 48 / ‖v‖ ^ 5 := by
    refine le_trans (le_of_eq ?_) h
    congr 2
    push_cast [sqrt_four_pi]
    ring
  have hfac : (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - 1 / (2 * v ^ 2))
      = v * ((Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2)
        - (v⁻¹ + -(1 / 2) / v ^ 3)) := by
    field_simp
    ring
  rw [hfac, norm_mul]
  calc ‖v‖ * ‖(Real.sqrt (4 * Real.pi) : ℂ) * Complex.exp (v ^ 2) - (v⁻¹ + -(1 / 2) / v ^ 3)‖
      ≤ ‖v‖ * (48 / ‖v‖ ^ 5) := mul_le_mul_of_nonneg_left hbd hvn.le
    _ = 48 / ‖v‖ ^ 4 := by field_simp

-- no-dlmf: logarithmic form of the second-order effective equation at a point where
-- `erf = −1`; proof infrastructure for the §7.13 zero asymptotics
/-- **The second-order logarithmic equation for the reflected `erfc` zeros.**  If `Re v > 0`,
`erf v = −1` and `‖v‖ ≥ 4`, then for some integer `k`

`‖v² + log (√(4π) · v) + 1/(2v²) − 2πi·k‖ ≤ 150 / ‖v‖⁴`.

Exactly `cerf_zero_log_equation_third` with the model constant `√(4π)`; this is the equation
that `erfc713_zero_expansion` inverts. -/
theorem cerf_negone_log_equation_third {v : ℂ} (hv : cerf v = -1) (hre : 0 < v.re)
    (hbig : 4 ≤ ‖v‖) :
    ∃ k : ℤ, ‖v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v) + 1 / (2 * v ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 150 / ‖v‖ ^ 4 := by
  have hz : v ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hz
  have hw2 : (16 : ℝ) ≤ ‖v‖ ^ 2 := by nlinarith
  have hw4 : (256 : ℝ) ≤ ‖v‖ ^ 4 := by nlinarith
  have hsp : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have hprod : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) * v ≠ 0 := mul_ne_zero hsp hz
  set q : ℂ := 1 / (2 * v ^ 2) with hqdef
  have hqn : ‖q‖ = 1 / (2 * ‖v‖ ^ 2) := by
    rw [hqdef, norm_div, norm_one, norm_mul, norm_pow]
    norm_num
  have hqsmall : ‖q‖ ≤ 1 / 32 := by
    rw [hqn, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set u : ℂ := v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v) + q with hu
  have hexpu : Complex.exp u = (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2)
      * Complex.exp q := by
    rw [hu, Complex.exp_add, Complex.exp_add, Complex.exp_log hprod]; ring
  have hr := cerf_negone_equation_third hv hre hbig
  have hexpq1 : ‖Complex.exp q - 1‖ ≤ 2 * ‖q‖ :=
    Complex.norm_exp_sub_one_le (by linarith)
  have hexpqn : ‖Complex.exp q‖ ≤ 2 := by
    have h := norm_sub_norm_le (Complex.exp q) 1
    simp only [norm_one] at h
    linarith
  have hkey : ‖(1 - q) * Complex.exp q - 1‖ ≤ 3 * ‖q‖ ^ 2 := by
    have hid : (1 - q) * Complex.exp q - 1
        = (Complex.exp q - 1 - q) - q * (Complex.exp q - 1) := by ring
    have h1 : ‖Complex.exp q - 1 - q‖ ≤ ‖q‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le (by linarith)
    have h2 : ‖q * (Complex.exp q - 1)‖ ≤ ‖q‖ * (2 * ‖q‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hexpq1 (norm_nonneg q)
    rw [hid]
    calc ‖(Complex.exp q - 1 - q) - q * (Complex.exp q - 1)‖
        ≤ ‖Complex.exp q - 1 - q‖ + ‖q * (Complex.exp q - 1)‖ := norm_sub_le _ _
      _ ≤ ‖q‖ ^ 2 + ‖q‖ * (2 * ‖q‖) := by linarith
      _ = 3 * ‖q‖ ^ 2 := by ring
  have hzeta : ‖Complex.exp u - 1‖ ≤ 100 / ‖v‖ ^ 4 := by
    have hid : Complex.exp u - 1 = ((1 - q) * Complex.exp q - 1)
        + ((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - q))
          * Complex.exp q := by
      rw [hexpu]; ring
    have h2 : ‖((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - q))
        * Complex.exp q‖ ≤ (48 / ‖v‖ ^ 4) * 2 := by
      rw [norm_mul]
      exact mul_le_mul hr hexpqn (norm_nonneg _) (by positivity)
    have h3 : 3 * ‖q‖ ^ 2 = 3 / (4 * ‖v‖ ^ 4) := by
      rw [hqn]; field_simp; ring
    have h4 : (3 : ℝ) / (4 * ‖v‖ ^ 4) ≤ 4 / ‖v‖ ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [hid]
    calc ‖((1 - q) * Complex.exp q - 1)
          + ((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - q))
            * Complex.exp q‖
        ≤ ‖(1 - q) * Complex.exp q - 1‖
          + ‖((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - (1 - q))
            * Complex.exp q‖ := norm_add_le _ _
      _ ≤ 4 / ‖v‖ ^ 4 + (48 / ‖v‖ ^ 4) * 2 := by linarith [hkey, h3, h4]
      _ = 100 / ‖v‖ ^ 4 := by ring
  have hhalf : ‖Complex.exp u - 1‖ ≤ 1 / 2 := by
    refine hzeta.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1δ : (1 : ℂ) + (Complex.exp u - 1) = Complex.exp u := by ring
  have hlogbound : ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := by
    have h := Complex.norm_log_one_add_half_le_self hhalf
    rwa [h1δ] at h
  have hone : Complex.exp (u - Complex.log (Complex.exp u)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero u),
      div_self (Complex.exp_ne_zero u)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨k, ?_⟩
  have heq : u - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp u) := by
    linear_combination hk
  have hgoal : v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v) + 1 / (2 * v ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp u) := by
    rw [← heq, hu]
  rw [hgoal]
  calc ‖Complex.log (Complex.exp u)‖ ≤ (3 / 2) * ‖Complex.exp u - 1‖ := hlogbound
    _ ≤ (3 / 2) * (100 / ‖v‖ ^ 4) := by linarith
    _ = 150 / ‖v‖ ^ 4 := by ring

-- no-dlmf: the model-function remainder bound underlying the §7.13 erfc zero asymptotics;
-- proof infrastructure, not a numbered DLMF display
/-- The key remainder bound for the `erfc` pipeline: the entire function
`F(v) = √π v e^{v²}(erf v + 1)` — whose zeros in `Re v > 0` are exactly the reflected zeros of
`erfc` — differs from the model function `Φ(v) = √(4π) v e^{v²} − 1` by at most `4/‖v‖²` on the
right half-plane. -/
theorem cerf_negone_scaled_remainder_bound {v : ℂ} (hre : 0 < v.re) :
    ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * (cerf v + 1)
        - ((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - 1)‖ ≤ 4 / ‖v‖ ^ 2 := by
  have hz : v ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have h := cerfc_scaled_leading_bound hre
  have hid : (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * (cerf v + 1)
      - ((Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) - 1)
      = -(v * ((Real.sqrt Real.pi : ℂ) * Complex.exp (v ^ 2) * cerfc v - v⁻¹)) := by
    rw [cerfc]
    push_cast [sqrt_four_pi]
    field_simp
    ring
  rw [hid, norm_neg, norm_mul]
  calc ‖v‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (v ^ 2) * cerfc v - v⁻¹‖
      ≤ ‖v‖ * (4 / ‖v‖ ^ 3) := mul_le_mul_of_nonneg_left h hvn.le
    _ = 4 / ‖v‖ ^ 2 := by field_simp

set_option maxHeartbeats 1000000 in
-- no-dlmf: existence and location of the exact roots of the erfc model equation
-- `√(4π) v e^{v²} = 1`; proof infrastructure for the §7.13 zero asymptotics
/-- **Existence of the `erfc` model roots.**  For every `n ≥ 134` the model equation
`√(4π) · v · e^{v²} = 1` has a solution `v` with

`v² + log (√(4π) v) = 2πi·n`,  `‖v² − 2πi·n‖ ≤ π n`,  `‖v‖ ≥ 20`,  `‖v‖ ≤ 6 Re v`,
`‖v‖ ≤ 6 Im v`.

The proof is that of `exists_model_root` with `a = log √π` replaced by `a = log √(4π) ≤ 3`
(the contraction estimate has ample room for the larger constant). -/
theorem exists_model_root_erfc (n : ℕ) (hn : 134 ≤ n) :
    ∃ v : ℂ, 20 ≤ ‖v‖ ∧ ‖v‖ ≤ 6 * v.re ∧ ‖v‖ ≤ 6 * v.im ∧
      ‖v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ Real.pi * n ∧
      v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)
        = 2 * (Real.pi : ℂ) * Complex.I * n ∧
      (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) = 1 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hsppos : (0:ℝ) < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsp0 : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hn' : (134:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set M : ℝ := 2 * Real.pi * n with hMdef
  have hMbig : (800:ℝ) ≤ M := by
    have h3 := Real.pi_gt_three
    rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  set c : ℂ := (M : ℂ) * Complex.I with hcdef
  have hcim : c.im = M := by simp [hcdef]
  have hcnorm : ‖c‖ = M := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM0]
  set a : ℝ := Real.log (Real.sqrt (4 * Real.pi)) with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    refine Real.log_nonneg ?_
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (4 * Real.pi) := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have ha1 : a ≤ 3 := by
    have h1 : Real.sqrt (4 * Real.pi) ≤ 4 := by
      have h4 : Real.sqrt (4 * Real.pi) ≤ Real.sqrt 16 :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
      rwa [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h4
    have h2 := Real.log_le_sub_one_of_pos hsppos
    rw [hadef]; linarith
  set T : ℂ → ℂ := fun u => c - (a : ℂ) - (1/2) * Complex.log u with hTdef
  set s : Set ℂ := Metric.closedBall c (M/2) with hsdef
  have hmem : ∀ u ∈ s, M/2 ≤ u.im ∧ M/2 ≤ ‖u‖ ∧ ‖u‖ ≤ 3*M/2 ∧ u ≠ 0 := by
    intro u hu
    have hd : ‖u - c‖ ≤ M/2 := by rwa [hsdef, Metric.mem_closedBall, dist_eq_norm] at hu
    have him : |u.im - c.im| ≤ M/2 := by
      have h := Complex.abs_im_le_norm (u - c)
      simp only [Complex.sub_im] at h; linarith
    rw [hcim] at him
    have h1 := abs_le.mp him
    have h2 := norm_sub_norm_le u c
    have h3 := norm_sub_norm_le c u
    rw [norm_sub_rev c u] at h3
    rw [hcnorm] at h2 h3
    refine ⟨by linarith [h1.1], by linarith, by linarith, ?_⟩
    intro h; rw [h] at h1; simp at h1; linarith [h1.1]
  have hsconv : Convex ℝ s := by rw [hsdef]; exact convex_closedBall c (M/2)
  have hmaps : Set.MapsTo T s s := by
    intro u hu
    obtain ⟨him, hn1, hn2, hu0⟩ := hmem u hu
    rw [hsdef, Metric.mem_closedBall, dist_eq_norm]
    have hTc : T u - c = -((a:ℂ) + (1/2) * Complex.log u) := by rw [hTdef]; ring
    rw [hTc, norm_neg]
    have h1 : ‖(a:ℂ) + (1/2) * Complex.log u‖ ≤ a + (1/2) * ‖Complex.log u‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
      have : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [this]
    have h2 : ‖Complex.log u‖ ≤ |Real.log ‖u‖| + Real.pi := by
      have h := Complex.norm_le_abs_re_add_abs_im (Complex.log u)
      rw [Complex.log_re, Complex.log_im] at h
      have h4 := Complex.abs_arg_le_pi u
      linarith
    have hu1 : (1:ℝ) ≤ ‖u‖ := by linarith
    have habs : |Real.log ‖u‖| = Real.log ‖u‖ := abs_of_nonneg (Real.log_nonneg hu1)
    have h3 : Real.log ‖u‖ ≤ 2 * (Real.sqrt ‖u‖ - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < ‖u‖))
      rw [Real.log_sqrt (by linarith)] at h
      linarith
    have h5 : Real.sqrt ‖u‖ ≤ Real.sqrt (3*M/2) := Real.sqrt_le_sqrt hn2
    have h6 : Real.sqrt (3*M/2) ≤ M/2 - 4 := by
      have h7 : Real.sqrt (3*M/2) ≤ Real.sqrt ((M/2-4)^2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h7
    rw [habs] at h2
    linarith [Real.pi_lt_four]
  have hlip : LipschitzOnWith (Real.toNNReal (1/M)) T s := by
    refine LipschitzOnWith.of_dist_le' (fun u hu u' hu' => ?_)
    have hlogd : ‖Complex.log u' - Complex.log u‖ ≤ (2/M) * ‖u' - u‖ := by
      refine norm_sub_le_of_hasDerivAt_le (f := Complex.log) (f' := fun z => z⁻¹)
        hsconv ?_ ?_ hu hu'
      · intro y hy
        obtain ⟨hyim, -, -, hy0⟩ := hmem y hy
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inr (by
          intro h; rw [h] at hyim; linarith)))
      · intro y hy
        obtain ⟨-, hyn, -, hy0⟩ := hmem y hy
        rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hM0]
        linarith
    have hTd : T u - T u' = -((1/2) * (Complex.log u - Complex.log u')) := by rw [hTdef]; ring
    rw [dist_eq_norm, hTd, norm_neg, norm_mul, dist_eq_norm]
    have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
    have h2 : ‖Complex.log u - Complex.log u'‖ = ‖Complex.log u' - Complex.log u‖ :=
      norm_sub_rev _ _
    have h3 : ‖u' - u‖ = ‖u - u'‖ := norm_sub_rev _ _
    rw [h1, h2]
    rw [h3] at hlogd
    have h4 : (1/2:ℝ) * ‖Complex.log u' - Complex.log u‖
        ≤ (1/2) * (2/M * ‖u - u'‖) := by linarith
    have hfin : (1/2 : ℝ) * (2/M * ‖u - u'‖) = 1/M * ‖u - u'‖ := by
      field_simp
    rw [hfin] at h4
    exact h4
  have hK : Real.toNNReal (1/M) < 1 := by
    rw [show (1 : NNReal) = Real.toNNReal 1 by simp]
    exact (Real.toNNReal_lt_toNNReal_iff one_pos).mpr (by rw [div_lt_one hM0]; linarith)
  obtain ⟨u, hus, hufix, -⟩ := ContractingWith.exists_fixedPoint' (f := T)
    (Metric.isClosed_closedBall.isComplete) hmaps ⟨hK, hlip.mapsToRestrict hmaps⟩
    (Metric.mem_closedBall_self (by linarith)) (edist_ne_top _ _)
  obtain ⟨huim, hun1, hun2, hu0⟩ := hmem u hus
  set v : ℂ := Complex.exp ((1/2) * Complex.log u) with hvdef
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have hvsq : v ^ 2 = u := by
    rw [hvdef, pow_two, ← Complex.exp_add,
      show (1/2:ℂ) * Complex.log u + (1/2:ℂ) * Complex.log u = Complex.log u by ring,
      Complex.exp_log hu0]
  have hargpos : 0 < Complex.arg u := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr (by linarith : 0 ≤ u.im)) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h.symm
      linarith [this.2]
  have harglt : Complex.arg u < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi u) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_pi_iff.mp h
      linarith [this.2]
  have hwim : ((1/2 : ℂ) * Complex.log u).im = Complex.arg u / 2 := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]
    ring
  have hvre : 0 < v.re := by
    rw [hvdef, Complex.exp_re, hwim]
    have := Real.cos_pos_of_mem_Ioo (x := Complex.arg u / 2) ⟨by linarith, by linarith⟩
    positivity
  have hvim : 0 < v.im := by
    rw [hvdef, Complex.exp_im, hwim]
    have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg u / 2) (by linarith) (by linarith)
    positivity
  have hvnormsq : ‖v‖ ^ 2 = ‖u‖ := by rw [← hvsq, ← norm_pow]
  have hvnorm : 20 ≤ ‖v‖ := by nlinarith [norm_nonneg v, hvnormsq, hun1]
  have hvnormub : ‖v‖ ≤ Real.sqrt (3*M/2) := by
    have h1 : ‖v‖ ^ 2 ≤ 3*M/2 := by rw [hvnormsq]; exact hun2
    nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 3*M/2), Real.sqrt_nonneg (3*M/2),
      norm_nonneg v]
  have hvim_le : v.im ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm v)
  have himid : u.im = 2 * v.re * v.im := by
    rw [← hvsq, pow_two, Complex.mul_im]; ring
  have hvnormpos : (0:ℝ) < ‖v‖ := by linarith
  have hvrenn : (0:ℝ) ≤ v.re := hvre.le
  have hvimnn : (0:ℝ) ≤ v.im := hvim.le
  have hprod : M/2 ≤ 2 * v.re * v.im := by rw [← himid]; exact huim
  have hvsqub : ‖v‖ ^ 2 ≤ 3*M/2 := by rw [hvnormsq]; exact hun2
  have hvre6 : ‖v‖ ≤ 6 * v.re := by
    nlinarith [hprod, hvsqub, hvnormpos, hvim_le, hvrenn]
  have hvre_le : v.re ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm v)
  have hvim6 : ‖v‖ ≤ 6 * v.im := by
    nlinarith [hprod, hvsqub, hvnormpos, hvre_le, hvimnn]
  have hlogv : Complex.log v = (1/2) * Complex.log u := by
    rw [hvdef]
    exact Complex.log_exp (by rw [hwim]; linarith) (by rw [hwim]; linarith)
  have hkey : v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v) = c := by
    rw [Complex.log_ofReal_mul hsppos hv0, hlogv, hvsq]
    have : T u = u := hufix
    rw [hTdef] at this
    simp only at this
    rw [← hadef]
    linear_combination -this
  have hmodel : (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) = 1 := by
    have h1 : Complex.exp (v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v))
        = (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) := by
      rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hv0)]; ring
    rw [← h1, hkey, hcdef]
    have h2 : ((M : ℝ) : ℂ) * Complex.I = (n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hMdef]; push_cast; ring
    rw [h2]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hceq : c = 2 * (Real.pi : ℂ) * Complex.I * n := by
    rw [hcdef, hMdef]; push_cast; ring
  refine ⟨v, hvnorm, hvre6, hvim6, ?_, by rw [hkey, hceq], hmodel⟩
  have h3 : v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n = u - c := by
    rw [hvsq, hcdef, hMdef]; push_cast; ring
  rw [h3]
  have := Metric.mem_closedBall.mp hus
  rw [dist_eq_norm] at this
  rw [hMdef] at this
  linarith [this]

-- no-dlmf: transfer of an exact erfc model root to an exact solution of `erf w = −1`;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **From an `erfc` model root to a genuine reflected zero.**  If `v` solves
`√(4π) · v · e^{v²} = 1` exactly, with `Re v ≥ 1` and `‖v‖ ≥ 16`, then `erf w = −1` has an
honest solution within distance `12/‖v‖³` of `v`.

The minimum-modulus argument of `exists_cerf_zero_near_model`, run for
`F(z) = √π z e^{z²}(erf z + 1)` against the model `Φ(z) = √(4π) z e^{z²} − 1`. -/
theorem exists_cerf_negone_near_model {v : ℂ} (hre : 1 ≤ v.re) (hbig : 16 ≤ ‖v‖)
    (hmodel : (Real.sqrt (4 * Real.pi) : ℂ) * v * Complex.exp (v ^ 2) = 1) :
    ∃ w : ℂ, cerf w = -1 ∧ ‖w - v‖ < 12 / ‖v‖ ^ 3 := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hcpos : (0:ℝ) < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc0 : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hV2 : (256:ℝ) ≤ V ^ 2 := by nlinarith
  have hV3 : (4096:ℝ) ≤ V ^ 3 := by nlinarith
  have hρsmall : ρ ≤ 1/100 := by
    rw [hρdef]
    have h : (12:ℝ) / V ^ 3 ≤ 12 / 4096 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV3
    linarith
  have hA : ρ * V = 12 / V ^ 2 := by rw [hρdef]; field_simp
  have hAsmall : ρ * V ≤ 3/64 := by
    rw [hA]
    have h : (12:ℝ) / V ^ 2 ≤ 12 / 256 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV2
    linarith
  have hρVpos : (0:ℝ) < ρ * V := mul_pos hρ0 hV0
  have h16ρ : 16 * ρ ≤ ρ * V := by nlinarith
  have hρsq : ρ ^ 2 + ρ / 10 ≤ (ρ * V) / 100 := by nlinarith
  have hmem : ∀ z ∈ Metric.closedBall v ρ, 0 < z.re ∧ V - ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + ρ := by
    intro z hz
    have hzv : ‖z - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre' : |z.re - v.re| ≤ ρ := by
      have h := Complex.abs_re_le_norm (z - v)
      simp only [Complex.sub_re] at h
      linarith
    have h1 := abs_le.mp hre'
    refine ⟨by linarith, ?_, ?_⟩
    · have h2 := norm_sub_norm_le v z
      rw [norm_sub_rev v z] at h2
      linarith
    · have h2 := norm_sub_norm_le z v
      linarith
  have hVρ : (10:ℝ) ≤ V - ρ := by linarith
  have hlogmvt : ∀ z ∈ Metric.closedBall v ρ,
      ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
          - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖
        ≤ (1 / (V - ρ)) * ‖z - v‖ := by
    intro z hz
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) / ((Real.sqrt (4 * Real.pi) : ℂ) * z))
      (convex_closedBall v ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hz
    · intro y hy
      obtain ⟨hy1, hy2, -⟩ := hmem y hy
      have hslit : ((Real.sqrt (4 * Real.pi) : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) * z)
          ((Real.sqrt (4 * Real.pi) : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt (4 * Real.pi) : ℂ))
      exact h1.clog hslit
    · intro y hy
      obtain ⟨hy1, hy2, -⟩ := hmem y hy
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hcpos]
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
        = (Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hc0 hz0)]; ring
  have hvre : 0 < v.re := by linarith
  have hgv : Complex.exp (v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)) = 1 := by
    rw [hexpg v hvre]; exact hmodel
  have hsphere : ∀ z ∈ Metric.sphere v ρ,
      ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * (cerf v + 1)‖
        < ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1)‖ := by
    intro z hz
    have hzv : ‖z - v‖ = ρ := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have hzcb : z ∈ Metric.closedBall v ρ := Metric.sphere_subset_closedBall hz
    obtain ⟨hzre, hzn1, hzn2⟩ := hmem z hzcb
    have hzge : 0.9 * V ≤ ‖z‖ := by linarith
    have hzpos : (0:ℝ) < ‖z‖ := by linarith
    have hz4 : 4 / ‖z‖ ^ 2 ≤ (5/12) * (ρ * V) := by
      rw [hA, show (5:ℝ)/12 * (12 / V ^ 2) = 5 / V ^ 2 by ring,
        div_le_div_iff₀ (pow_pos hzpos 2) (pow_pos hV0 2)]
      nlinarith [hzge, hV0]
    set d : ℂ := (z ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
      - (v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)) with hd
    have hdsplit : d = (z - v) * (z + v)
        + (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
            - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)) := by rw [hd]; ring
    have hlog := hlogmvt z hzcb
    rw [hzv] at hlog
    have hlog' : (1 / (V - ρ)) * ρ ≤ ρ / 10 := by
      rw [div_mul_eq_mul_div, one_mul]
      apply div_le_div_of_nonneg_left hρ0.le (by norm_num) hVρ
    have h2v : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    have hzpv : 2 * V - ρ ≤ ‖z + v‖ := by
      have h1 : ‖(2:ℂ) * v‖ ≤ ‖z + v‖ + ‖z - v‖ := by
        calc ‖(2:ℂ) * v‖ = ‖(z + v) - (z - v)‖ := by congr 1; ring
          _ ≤ ‖z + v‖ + ‖z - v‖ := norm_sub_le _ _
      rw [h2v, hzv] at h1; linarith only [h1]
    have hzpv' : ‖z + v‖ ≤ 2 * V + ρ := by
      have h1 := norm_add_le z v; linarith only [h1, hzn2, hVdef.ge, hVdef.le]
    have hprodnorm : ‖(z - v) * (z + v)‖ = ρ * ‖z + v‖ := by rw [norm_mul, hzv]
    have hdlow : 1.99 * (ρ * V) ≤ ‖d‖ := by
      have h1 : ‖(z - v) * (z + v)‖
          - ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
              - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ ≤ ‖d‖ := by
        have h0 : ‖(z - v) * (z + v)‖ ≤ ‖d‖
            + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
              - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ := by
          calc ‖(z - v) * (z + v)‖
              = ‖d - (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
                  - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v))‖ := by
                congr 1; rw [hdsplit]; ring
            _ ≤ ‖d‖ + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
                  - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ := norm_sub_le _ _
        linarith only [h0]
      rw [hprodnorm] at h1
      have hmul : ρ * (2 * V - ρ) ≤ ρ * ‖z + v‖ := mul_le_mul_of_nonneg_left hzpv hρ0.le
      linarith only [h1, hmul, hlog, hlog', hρsq]
    have hdhigh : ‖d‖ ≤ 2.01 * (ρ * V) := by
      have h1 : ‖d‖ ≤ ‖(z - v) * (z + v)‖
          + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z)
              - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ := by
        rw [hdsplit]; exact norm_add_le _ _
      rw [hprodnorm] at h1
      have hmul : ρ * ‖z + v‖ ≤ ρ * (2 * V + ρ) := mul_le_mul_of_nonneg_left hzpv' hρ0.le
      linarith only [h1, hmul, hlog, hlog', hρsq]
    have hdle1 : ‖d‖ ≤ 1/10 := by linarith only [hdhigh, hAsmall]
    have hmodelow : (3/2 : ℝ) * (ρ * V)
        ≤ ‖(Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1‖ := by
      have hEq : (Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1
          = Complex.exp d - 1 := by
        rw [← hexpg z hzre, hd, Complex.exp_sub, hgv, div_one]
      rw [hEq]
      have hb := Complex.norm_exp_sub_one_sub_id_le (x := d) (by linarith only [hdle1])
      have hkey : ‖d‖ - ‖d‖ ^ 2 ≤ ‖Complex.exp d - 1‖ := by
        have h5 := norm_sub_norm_le d (Complex.exp d - 1)
        rw [norm_sub_rev d (Complex.exp d - 1)] at h5
        have h6 : (Complex.exp d - 1) - d = Complex.exp d - 1 - d := by ring
        rw [h6] at h5
        linarith only [h5, hb]
      have h7 : ‖d‖ ^ 2 ≤ ‖d‖ / 10 := by
        calc ‖d‖ ^ 2 = ‖d‖ * ‖d‖ := by ring
          _ ≤ ‖d‖ * (1 / 10) := mul_le_mul_of_nonneg_left hdle1 (norm_nonneg d)
          _ = ‖d‖ / 10 := by ring
      have h9 : (3/2 : ℝ) * (ρ * V) ≤ (9/10) * ‖d‖ := by linarith only [hdlow, hρVpos]
      linarith only [hkey, h7, h9]
    have hrz := cerf_negone_scaled_remainder_bound hzre
    have hrv := cerf_negone_scaled_remainder_bound hvre
    have hfv : ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * (cerf v + 1)‖
        ≤ (1/3 : ℝ) * (ρ * V) := by
      rw [← hVdef] at hrv
      rw [hA, show (1:ℝ)/3 * (12 / V ^ 2) = 4 / V ^ 2 by ring]
      rw [hmodel] at hrv
      simpa using hrv
    have hfz : (13/12 : ℝ) * (ρ * V)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1)‖ := by
      have h1 := norm_sub_norm_le ((Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1)
        ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1))
      have h2 := norm_sub_rev ((Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1)
        ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1))
      rw [h2] at h1
      linarith only [h1, hmodelow, hrz, hz4]
    linarith only [hfv, hfz, hρVpos]
  obtain ⟨w, hw, hfw⟩ := exists_zero_of_norm_lt_on_sphere
    (f := fun z : ℂ => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1))
    (by
      refine Differentiable.mul ?_ (differentiable_cerf.add_const 1)
      exact (differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2)))
    hρ0 hsphere
  have hwb : ‖w - v‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
  obtain ⟨hwre, -, -⟩ := hmem w (Metric.ball_subset_closedBall hw)
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
  refine ⟨w, ?_, hwb⟩
  have := hfw
  simp only [mul_eq_zero] at this
  rcases this with (h | h) | h
  · rcases h with h | h
    · exact absurd h hsp0
    · exact absurd h hw0
  · exact absurd h (Complex.exp_ne_zero _)
  · linear_combination h

set_option maxHeartbeats 1000000 in
-- no-dlmf: local uniqueness (separation) of the solutions of `erf = −1` in the first-quadrant
-- sector; proof infrastructure for the §7.13 zero asymptotics
/-- **Local uniqueness of the reflected `erfc` zeros.**  In the sector `‖v‖ ≤ 6 Re v` with
`‖v‖ ≥ 20`, `erf w = −1` has at most one solution in the disc of radius `1/(24‖v‖)` about `v`.

The separation argument of `cerf_zero_unique_in_small_ball`, run for the remainder
`Rem = √π z e^{z²}(erf z + 1) − (√(4π) z e^{z²} − 1)`. -/
theorem cerf_negone_unique_in_small_ball {v w w' : ℂ} (hre : ‖v‖ ≤ 6 * v.re) (hbig : 20 ≤ ‖v‖)
    (hw : cerf w = -1) (hw' : cerf w' = -1)
    (hwb : ‖w - v‖ ≤ 1 / (24 * ‖v‖)) (hwb' : ‖w' - v‖ ≤ 1 / (24 * ‖v‖)) : w = w' := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hcpos : (0:ℝ) < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc0 : ((Real.sqrt (4 * Real.pi) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  have hV2 : (400:ℝ) ≤ V ^ 2 := by nlinarith
  have hV3 : (8000:ℝ) ≤ V ^ 3 := by nlinarith [sq_nonneg V]
  set ρ : ℝ := 1 / (24 * V) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact div_pos (by norm_num) (by linarith)
  have hρsmall : ρ ≤ 1/100 := by
    rw [hρdef]
    have h : (1:ℝ) / (24 * V) ≤ 1 / 480 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hvre : V / 6 ≤ v.re := by linarith
  set Rem : ℂ → ℂ := fun z => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) * (cerf z + 1)
    - ((Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1) with hRemdef
  have hRdiff : Differentiable ℂ Rem := by
    rw [hRemdef]
    have h0 : Differentiable ℂ (fun z : ℂ => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)) :=
      (differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2))
    have h1 : Differentiable ℂ
        (fun z : ℂ => (Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2)) :=
      (differentiable_id.const_mul ((Real.sqrt (4 * Real.pi) : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2))
    exact (h0.mul (differentiable_cerf.add_const 1)).sub (h1.sub_const 1)
  have hRbound : ∀ z : ℂ, 0 < z.re → ‖Rem z‖ ≤ 4 / ‖z‖ ^ 2 := by
    intro z hz
    rw [hRemdef]
    exact cerf_negone_scaled_remainder_bound hz
  have hgeo : ∀ z : ℂ, ‖z - v‖ ≤ ρ → V / 6 - ρ ≤ z.re ∧ V - ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + ρ := by
    intro z hz
    have h := Complex.abs_re_le_norm (z - v)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hz)
    have h2 := norm_sub_norm_le v z
    rw [norm_sub_rev v z] at h2
    have h3 := norm_sub_norm_le z v
    exact ⟨by linarith [h1.1], by linarith, by linarith⟩
  have hderiv : ∀ z₀ : ℂ, ‖z₀ - v‖ ≤ ρ → ‖deriv Rem z₀‖ ≤ 120 / V ^ 3 := by
    intro z₀ hz₀
    have hbig' : ∀ z ∈ Metric.ball z₀ (V/12), 0 < z.re ∧ (9/10) * V ≤ ‖z‖ := by
      intro z hz
      have hd : ‖z - z₀‖ < V/12 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hdv : ‖z - v‖ ≤ ρ + V/12 := by
        have := norm_add_le (z - z₀) (z₀ - v)
        have he : (z - z₀) + (z₀ - v) = z - v := by ring
        rw [he] at this
        linarith
      have h := Complex.abs_re_le_norm (z - v)
      simp only [Complex.sub_re] at h
      have h1 := abs_le.mp (le_trans h hdv)
      have h2 := norm_sub_norm_le v z
      rw [norm_sub_rev v z] at h2
      constructor
      · linarith [h1.1]
      · linarith
    have hmaps : Set.MapsTo Rem (Metric.ball z₀ (V/12))
        (Metric.closedBall (Rem z₀) (10/V^2)) := by
      intro z hz
      obtain ⟨hzre, hzn⟩ := hbig' z hz
      have hz0re : 0 < z₀.re := by
        obtain ⟨h1, -, -⟩ := hgeo z₀ hz₀; linarith
      have hz0n : (9/10) * V ≤ ‖z₀‖ := by
        obtain ⟨-, h2, -⟩ := hgeo z₀ hz₀; linarith
      have b1 : ‖Rem z‖ ≤ 5 / V ^ 2 := by
        refine le_trans (hRbound z hzre) ?_
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith [hzn, hV0]
      have b2 : ‖Rem z₀‖ ≤ 5 / V ^ 2 := by
        refine le_trans (hRbound z₀ hz0re) ?_
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith [hz0n, hV0]
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := norm_sub_le (Rem z) (Rem z₀)
      have he : (10:ℝ)/V^2 = 5/V^2 + 5/V^2 := by ring
      rw [he]; linarith
    have h := Complex.norm_deriv_le_div_of_mapsTo_ball (f := Rem) (c := z₀)
      (R₁ := V/12) (R₂ := 10/V^2) hRdiff.differentiableOn hmaps (by linarith)
    refine le_trans h (le_of_eq ?_)
    field_simp
    ring
  obtain ⟨hwre0, hwn1, hwn2⟩ := hgeo w hwb
  obtain ⟨hw're0, hw'n1, hw'n2⟩ := hgeo w' hwb'
  have hwre : 0 < w.re := by linarith
  have hw're : 0 < w'.re := by linarith
  have hmemw : w ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwb
  have hmemw' : w' ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwb'
  have hww' : ‖w - w'‖ ≤ 2 * ρ := by
    have h := norm_sub_le (w - v) (w' - v)
    have he : (w - v) - (w' - v) = w - w' := by ring
    rw [he] at h; linarith
  have hRlip : ‖Rem w - Rem w'‖ ≤ (120 / V ^ 3) * ‖w - w'‖ :=
    norm_sub_le_of_hasDerivAt_le (f := Rem) (f' := deriv Rem) (convex_closedBall v ρ)
      (fun z _ => (hRdiff z).hasDerivAt)
      (fun z hz => hderiv z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
      hmemw' hmemw
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
        = (Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hc0 hz0)]; ring
  have hΦ : ∀ z : ℂ, cerf z = -1 →
      (Real.sqrt (4 * Real.pi) : ℂ) * z * Complex.exp (z ^ 2) - 1 = - Rem z := by
    intro z hz
    rw [hRemdef]; simp only; rw [hz]; ring
  clear_value Rem
  have hRw' : ‖Rem w'‖ ≤ 5 / V ^ 2 := by
    refine le_trans (hRbound w' hw're) ?_
    have hw'pos : (0:ℝ) < ‖w'‖ := by linarith
    rw [div_le_div_iff₀ (pow_pos hw'pos 2) (pow_pos hV0 2)]
    nlinarith [hw'n1, hV0, hρsmall]
  have hexpw' : (98/100 : ℝ)
      ≤ ‖(Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2)‖ := by
    have h1 : (Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2) = 1 - Rem w' := by
      have := hΦ w' hw'; linear_combination this
    rw [h1]
    have h2 := norm_sub_norm_le (1 : ℂ) (Rem w')
    have h3 : ‖(1:ℂ)‖ = 1 := norm_one
    have h4 : (5:ℝ) / V ^ 2 ≤ 5 / 400 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hV2
    rw [h3] at h2
    linarith
  set δ : ℂ := (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w))
    - (w' ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')) with hδdef
  have hlogmvt : ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
      - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')‖ ≤ (1 / (V - ρ)) * ‖w - w'‖ := by
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) / ((Real.sqrt (4 * Real.pi) : ℂ) * z))
      (convex_closedBall v ρ) ?_ ?_ hmemw' hmemw
    · intro y hy
      have hyb : ‖y - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      obtain ⟨hy1, hy2, -⟩ := hgeo y hyb
      have hy1' : 0 < y.re := by linarith
      have hslit : ((Real.sqrt (4 * Real.pi) : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) * z)
          ((Real.sqrt (4 * Real.pi) : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt (4 * Real.pi) : ℂ))
      exact h1.clog hslit
    · intro y hy
      have hyb : ‖y - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      obtain ⟨-, hy2, -⟩ := hgeo y hyb
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hcpos]
  have hlogsmall : (1 / (V - ρ)) * ‖w - w'‖ ≤ (1/10) * ‖w - w'‖ := by
    have h1 : (1:ℝ) / (V - ρ) ≤ 1/10 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hsum1 : ‖w + w'‖ ≤ 2 * V + 2 * ρ := by
    have h1 : ‖w + w'‖ ≤ ‖w - v‖ + ‖w' - v‖ + ‖(2:ℂ) * v‖ := by
      calc ‖w + w'‖ = ‖(w - v) + (w' - v) + 2 * v‖ := by congr 1; ring
        _ ≤ ‖(w - v) + (w' - v)‖ + ‖(2:ℂ) * v‖ := norm_add_le _ _
        _ ≤ ‖w - v‖ + ‖w' - v‖ + ‖(2:ℂ) * v‖ := by linarith [norm_add_le (w - v) (w' - v)]
    have h2 : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    rw [h2] at h1; linarith
  have hsum2 : 2 * V - 2 * ρ ≤ ‖w + w'‖ := by
    have h2 : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    have h1 : ‖(2:ℂ) * v‖ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by
      calc ‖(2:ℂ) * v‖ = ‖(w + w') - ((w - v) + (w' - v))‖ := by congr 1; ring
        _ ≤ ‖w + w'‖ + ‖(w - v) + (w' - v)‖ := norm_sub_le _ _
        _ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by linarith [norm_add_le (w - v) (w' - v)]
    rw [h2] at h1; linarith
  have hδsplit : δ = (w - w') * (w + w')
      + (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
        - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')) := by rw [hδdef]; ring
  have hprodn : ‖(w - w') * (w + w')‖ = ‖w - w'‖ * ‖w + w'‖ := norm_mul _ _
  clear_value δ
  have hδlow : (199/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖δ‖ := by
    have h0 : ‖(w - w') * (w + w')‖ ≤ ‖δ‖
        + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
          - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')‖ := by
      calc ‖(w - w') * (w + w')‖
          = ‖δ - (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
              - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w'))‖ := by
            congr 1; rw [hδsplit]; ring
        _ ≤ ‖δ‖ + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
              - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')‖ := norm_sub_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * (2 * V - 2 * ρ) ≤ ‖w - w'‖ * ‖w + w'‖ :=
      mul_le_mul_of_nonneg_left hsum2 (norm_nonneg _)
    have hslack0 : 2 * ρ + 1/10 ≤ V/100 := by linarith
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδhigh : ‖δ‖ ≤ (201/100 : ℝ) * (V * ‖w - w'‖) := by
    have h0 : ‖δ‖ ≤ ‖(w - w') * (w + w')‖
        + ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
          - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w')‖ := by
      rw [hδsplit]; exact norm_add_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * ‖w + w'‖ ≤ ‖w - w'‖ * (2 * V + 2 * ρ) :=
      mul_le_mul_of_nonneg_left hsum1 (norm_nonneg _)
    have hslack0 : 2 * ρ + 1/10 ≤ V/100 := by linarith
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδle : ‖δ‖ ≤ 1/5 := by
    have h1 : V * ‖w - w'‖ ≤ V * (2 * ρ) := mul_le_mul_of_nonneg_left hww' (by linarith)
    have h2 : V * (2 * ρ) = 1 / 12 := by rw [hρdef]; field_simp; ring
    rw [h2] at h1
    linarith
  clear_value ρ V
  have hexpδ : (8/10 : ℝ) * ‖δ‖ ≤ ‖Complex.exp δ - 1‖ := by
    have hb := Complex.norm_exp_sub_one_sub_id_le (x := δ) (by linarith)
    have h5 := norm_sub_norm_le δ (Complex.exp δ - 1)
    rw [norm_sub_rev δ (Complex.exp δ - 1)] at h5
    have h6 : (Complex.exp δ - 1) - δ = Complex.exp δ - 1 - δ := by ring
    rw [h6] at h5
    have h7 : ‖δ‖ ^ 2 ≤ (1/5) * ‖δ‖ := by
      calc ‖δ‖ ^ 2 = ‖δ‖ * ‖δ‖ := by ring
        _ ≤ ‖δ‖ * (1/5) := mul_le_mul_of_nonneg_left hδle (norm_nonneg _)
        _ = (1/5) * ‖δ‖ := by ring
    linarith
  have hkey : Rem w - Rem w'
      = -((Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2) * (Complex.exp δ - 1)) := by
    have e1 : (Real.sqrt (4 * Real.pi) : ℂ) * w * Complex.exp (w ^ 2)
        = (Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2) * Complex.exp δ := by
      rw [← hexpg w hwre, ← hexpg w' hw're, ← Complex.exp_add]
      congr 1
      rw [hδdef]; ring
    have e2 := hΦ w hw
    have e3 := hΦ w' hw'
    linear_combination e2 - e3 - e1
  have hlow : ‖Rem w - Rem w'‖
      = ‖(Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ := by
    rw [hkey, norm_neg, norm_mul]
  have hVX : (0:ℝ) ≤ V * ‖w - w'‖ := by positivity
  have hchain : (156/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖Rem w - Rem w'‖ := by
    rw [hlow]
    have h1 : (98/100 : ℝ) * ((8/10) * ‖δ‖)
        ≤ ‖(Real.sqrt (4 * Real.pi) : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ :=
      mul_le_mul hexpw' hexpδ (by positivity) (norm_nonneg _)
    linarith only [hδlow, h1, hVX]
  by_contra hne
  have hpos : 0 < ‖w - w'‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  have hcomb : (156/100 : ℝ) * V * ‖w - w'‖ ≤ (120 / V ^ 3) * ‖w - w'‖ := by
    linarith only [hchain, hRlip]
  have hfin : (156/100 : ℝ) * V ≤ 120 / V ^ 3 :=
    le_of_mul_le_mul_right (by linarith only [hcomb]) hpos
  have h120 : (120:ℝ) / V ^ 3 ≤ 120 / 8000 := by
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < V ^ 3) (by norm_num : (0:ℝ) < 8000)]
    linarith only [hV3]
  linarith only [hfin, h120, hbig]

-- no-dlmf: elementary size bounds for the DLMF 7.13.4 parameter `μ' = log (2λ√(2π))`;
-- proof infrastructure for the §7.13 zero asymptotics
/-- **Size of the parameter `μ'` of DLMF 7.13.4.**  For `λ ≥ 100`, `μ' = log (2λ√(2π))`
satisfies `5 ≤ μ'`, `μ' + 3 ≤ 7·λ^{1/4}` and `μ' + 3 ≤ λ/2`.

Both upper bounds come from the same fourth-root chain `log X = 4 log X^{1/4} ≤ 4(X^{1/4} − 1)`
with `X = 2λ√(2π) ≤ 9λ`; the extra factor `2` inside the logarithm (against `erf713_mu_bounds`)
is why the constant `6` there becomes `7` here. -/
theorem erfc713_mu_bounds {lam mu : ℝ} (hlam : 100 ≤ lam)
    (hmu : mu = Real.log (2 * lam * Real.sqrt (2 * Real.pi))) :
    5 ≤ mu ∧ mu + 3 ≤ 7 * Real.sqrt (Real.sqrt lam) ∧ mu + 3 ≤ lam / 2 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsnn : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hlb : (2:ℝ) ≤ Real.sqrt (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have hub : Real.sqrt (2 * Real.pi) ≤ 4.5 := by nlinarith [Real.pi_lt_four]
  set X : ℝ := 2 * lam * Real.sqrt (2 * Real.pi) with hXdef
  have hX0 : (0:ℝ) < X := by rw [hXdef]; nlinarith
  have hX9 : X ≤ 9 * lam := by rw [hXdef]; nlinarith
  set s : ℝ := Real.sqrt (Real.sqrt lam) with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hlam0)
  have hs4 : s ^ 4 = lam := by
    rw [hsdef, show (Real.sqrt (Real.sqrt lam)) ^ 4
      = ((Real.sqrt (Real.sqrt lam)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg lam), Real.sq_sqrt hlam0.le]
  have hs3 : 3 ≤ s := by
    by_contra hcon
    have hlt : s < 3 := not_le.mp hcon
    have h1 : s ^ 2 < 9 := by nlinarith [hs0]
    have h2 : s ^ 4 < 81 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]; nlinarith [h1, sq_nonneg s]
    linarith [hs4, hlam]
  -- the fourth-root bound on `mu`
  have h1 : Real.log (Real.sqrt (Real.sqrt X)) ≤ Real.sqrt (Real.sqrt X) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX0))
  have h2 : Real.log (Real.sqrt (Real.sqrt X)) = Real.log (Real.sqrt X) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsqrt3 : Real.sqrt 3 ≤ 1.74 := by
    have h : Real.sqrt 3 ≤ Real.sqrt (1.74 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.74)] at h
  have hb : Real.sqrt (Real.sqrt X) ≤ 1.74 * s := by
    have hu2 : Real.sqrt X ≤ 3 * Real.sqrt lam := by
      have hq : Real.sqrt (9 * lam) = 3 * Real.sqrt lam := by
        rw [show (9:ℝ) * lam = 3 ^ 2 * lam by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
      calc Real.sqrt X ≤ Real.sqrt (9 * lam) := Real.sqrt_le_sqrt hX9
        _ = 3 * Real.sqrt lam := hq
    have hu3 : Real.sqrt (Real.sqrt X) ≤ Real.sqrt (3 * Real.sqrt lam) :=
      Real.sqrt_le_sqrt hu2
    have hu4 : Real.sqrt (3 * Real.sqrt lam) = Real.sqrt 3 * s := by
      rw [hsdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hs2nn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    nlinarith [hu3, hu4.le, hu4.ge, hsqrt3, hs0]
  have hmuub : mu ≤ 6.96 * s - 4 := by
    rw [hmu]
    linarith [h1, h2, h3, hb]
  refine ⟨?_, by linarith, ?_⟩
  · rw [hmu]
    have h200 : (200:ℝ) ≤ X := by rw [hXdef]; nlinarith
    have hexp : Real.exp 5 ≤ 200 := by
      have h1' : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      have h2' : Real.exp 5 = Real.exp 1 ^ (5:ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h2']
      have h3' : Real.exp 1 ^ (5:ℕ) ≤ (2.7182818286:ℝ) ^ (5:ℕ) := by gcongr
      refine h3'.trans ?_
      norm_num
    rw [Real.le_log_iff_exp_le hX0]
    linarith
  · have hcube : (27:ℝ) ≤ s ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs3) (sq_nonneg s), hs3, hs0]
    have hs4' : 27 * s ≤ s ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hcube hs0.le]
    rw [← hs4]
    linarith [hmuub, hs4', hs0]

-- no-dlmf: the defining square of the DLMF 7.13.4 parameter `λ`; proof infrastructure
/-- `λₙ² = (n − 1/8)π` for `n ≥ 1`.  (DLMF 7.13.4 and 7.13.2 share the same `λ`.) -/
theorem erfc713_lambda_sq {n : ℕ} (hn : 1 ≤ n) :
    erfcZeroLambda n ^ 2 = ((n:ℝ) - 1/8) * Real.pi := erf713_lambda_sq hn

-- no-dlmf: elementary size bounds for the DLMF 7.13.4 parameters at a large index; proof
-- infrastructure for the §7.13 zero asymptotics
/-- **Size of the erfc parameters at a large index.**  For `n ≥ 3400` the DLMF 7.13.4 parameters
satisfy `λₙ ≥ 100`, `μ'ₙ ≥ 5`, `μ'ₙ + 3 ≤ λₙ/2`, and the `erfc713_zero_expansion` error term
obeys `(μ'ₙ + 3)⁴/(20 λₙ⁵) ≤ 1/(320 λₙ)` — smaller than the zero separation `1/(24‖u‖)`, so that
two zeros matching at the same index must coincide. -/
theorem erfc713_param_bounds {n : ℕ} (hn : 3400 ≤ n) :
    100 ≤ erfcZeroLambda n ∧ 5 ≤ erfcZeroMu n ∧
      erfcZeroMu n + 3 ≤ erfcZeroLambda n / 2 ∧
      (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5)
        ≤ 1 / (320 * erfcZeroLambda n) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  have hlamsq : erfcZeroLambda n ^ 2 = ((n:ℝ) - 1/8) * Real.pi := by
    simp only [erfcZeroLambda]
    exact Real.sq_sqrt (by nlinarith)
  have hlamnn : (0:ℝ) ≤ erfcZeroLambda n := by
    simp only [erfcZeroLambda]; exact Real.sqrt_nonneg _
  have hlam : (100:ℝ) ≤ erfcZeroLambda n := by nlinarith
  have hmudef : erfcZeroMu n = Real.log (2 * erfcZeroLambda n * Real.sqrt (2 * Real.pi)) := rfl
  obtain ⟨h5, -, h3⟩ := erfc713_mu_bounds hlam hmudef
  have hlam0 : (0:ℝ) < erfcZeroLambda n := by linarith
  refine ⟨hlam, h5, h3, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : (erfcZeroMu n + 3) ^ 4 ≤ (erfcZeroLambda n / 2) ^ 4 := by
    have h0 : (0:ℝ) ≤ erfcZeroMu n + 3 := by linarith
    gcongr
  have h5' : (erfcZeroLambda n / 2) ^ 4 = erfcZeroLambda n ^ 4 / 16 := by ring
  rw [h5'] at h4
  nlinarith [h4, hlam0]

-- no-dlmf: a fourth-root bound for the DLMF 7.13.4 parameter `μ'`; proof infrastructure
/-- **A fourth-root bound for `μ'`.**  For `n ≥ 3400`, `(μ'ₙ + 3)⁴ ≤ 2401 λₙ`.

This is the estimate that makes the `erfc713_zero_expansion` error `(μ' + 3)⁴/(20λ⁵) ≤ 121/λ⁴`
genuinely `o(λ⁻³)`; the cruder `μ' + 3 ≤ λ/2` would only give `O(λ⁻¹)`. -/
theorem erfc713_mu_quartic {n : ℕ} (hn : 3400 ≤ n) :
    (erfcZeroMu n + 3) ^ 4 ≤ 2401 * erfcZeroLambda n := by
  obtain ⟨hlam, hmu5, -, -⟩ := erfc713_param_bounds hn
  have hlam0 : (0:ℝ) < erfcZeroLambda n := by linarith
  have hmudef : erfcZeroMu n = Real.log (2 * erfcZeroLambda n * Real.sqrt (2 * Real.pi)) := rfl
  obtain ⟨-, hroot, -⟩ := erfc713_mu_bounds hlam hmudef
  have hs4 : Real.sqrt (Real.sqrt (erfcZeroLambda n)) ^ 4 = erfcZeroLambda n := by
    rw [show (Real.sqrt (Real.sqrt (erfcZeroLambda n))) ^ 4
      = ((Real.sqrt (Real.sqrt (erfcZeroLambda n))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hlam0.le]
  have hm0 : (0:ℝ) ≤ erfcZeroMu n + 3 := by linarith
  calc (erfcZeroMu n + 3) ^ 4
      ≤ (7 * Real.sqrt (Real.sqrt (erfcZeroLambda n))) ^ 4 := by gcongr
    _ = 2401 * erfcZeroLambda n := by rw [mul_pow, hs4]; norm_num

set_option maxHeartbeats 1000000 in
-- no-dlmf: crude localization of a solution of the real form of the §7.13 erfc zero equation;
-- proof infrastructure, not a numbered DLMF display
/-- **Crude localization (erfc form).**  If the real pair `(s, d) = (x+y, x−y)` of a first-quadrant point
satisfies the two real components of the third-order zero equation — `key1` (real part) and
`key2` (imaginary part) — with index parameter `λ ≥ 100`, then

`s = 2λ + O(1)`, `N = x² + y² = 2λ² + O(1)`, `|d| ≤ 2`, `|L − μ| ≤ 2/λ²`,

together with the two-sided logarithmic sandwich relating `L = ½ log (πN)` to `μ`.
This is the zeroth iteration of the inversion of the transcendental system; the sandwich is
kept because the refined steps need it at full strength. -/
theorem erfc713_crude {lam mu s d N L A : ℝ}
    (hlam : 100 ≤ lam) (hmu : 2 * mu = Real.log (8 * Real.pi * lam ^ 2))
    (hL : L = (1 / 2) * Real.log (4 * Real.pi * N))
    (hs : 0 < s) (hd2s : d ^ 2 ≤ s ^ 2) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hQ : N < s ^ 2)
    (hAbd : |A| ≤ 2)
    (key1 : |d * s + L + d * s / (2 * N ^ 2)| ≤ 40 / lam ^ 4)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - (s ^ 2 - N) / N ^ 2 - 4 * lam ^ 2| ≤ 80 / lam ^ 4) :
    2 * lam - 1 ≤ s ∧ s ^ 2 ≤ 4 * lam ^ 2 + 10 ∧ 2 * lam ^ 2 - 3 ≤ N ∧ N ≤ 2 * lam ^ 2 + 7
      ∧ |d| ≤ 2 ∧ |L - mu| ≤ 2 / lam ^ 2
      ∧ 2 * (L - mu) ≤ (N - 2 * lam ^ 2) / (2 * lam ^ 2)
      ∧ -(2 * (L - mu)) ≤ (2 * lam ^ 2 - N) / N := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hlam4 : (100000000:ℝ) ≤ lam ^ 4 := by nlinarith
  have heps1 : 40 / lam ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have heps2 : 80 / lam ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hN0 : (0:ℝ) < N := by nlinarith
  have hk1 := abs_le.mp key1
  have hk2 := abs_le.mp key2
  have hAb := abs_le.mp hAbd
  have hQpos : 0 ≤ (s ^ 2 - N) / N ^ 2 := div_nonneg (by linarith) (by positivity)
  have hs2lb : 4 * lam ^ 2 - 5 ≤ s ^ 2 := by
    linarith only [hk2.1, sq_nonneg d, hQpos, heps2, hAb.1, hAb.2]
  have hslb : 2 * lam - 1 ≤ s := by nlinarith [hs2lb, hs, hlam]
  have hNlb : 2 * lam ^ 2 - 3 ≤ N := by linarith only [hNsd, hs2lb, sq_nonneg d]
  have hN1 : (1:ℝ) ≤ N := by linarith only [hNlb, hlam2]
  have hQub : (s ^ 2 - N) / N ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hNsd, hd2s, hN1]
  have hLpos : 0 < L := by
    have h1 : (1:ℝ) < 4 * Real.pi * N := by nlinarith [Real.pi_gt_three, hN1]
    have h2 := Real.log_pos h1
    rw [hL]; linarith only [h2]
  have hLub0 : L ≤ 2 * s - 1 := by
    have hsqrtpiub : Real.sqrt Real.pi ≤ 1.78 := by
      have h := Real.sqrt_le_sqrt (show Real.pi ≤ 1.78 ^ 2 by nlinarith [Real.pi_lt_d6])
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.78)] at h
    have hlog2 : Real.log 2 ≤ 0.7 := by
      linarith [Real.log_two_lt_d9]
    have h0 : L = Real.log 2 + (1 / 2) * Real.log (Real.pi * N) := by
      rw [hL, show (4:ℝ) * Real.pi * N = 2 ^ 2 * (Real.pi * N) by ring,
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h1 : (1 / 2) * Real.log (Real.pi * N) = Real.log (Real.sqrt (Real.pi * N)) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log (Real.sqrt (Real.pi * N)) ≤ Real.sqrt (Real.pi * N) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.sqrt N ≤ s := by
      rw [show s = Real.sqrt (s ^ 2) by rw [Real.sqrt_sq hs.le]]
      exact Real.sqrt_le_sqrt (by linarith only [hNsd, hd2s])
    have h3 : Real.sqrt (Real.pi * N) ≤ 1.78 * s := by
      rw [Real.sqrt_mul Real.pi_pos.le]
      exact mul_le_mul hsqrtpiub h4 (Real.sqrt_nonneg N) (by norm_num)
    have hs199 : (199:ℝ) ≤ s := by linarith only [hslb, hlam]
    linarith only [h0, h1, h2, h3, hlog2, hs199]
  have hdabs : |d| ≤ 2 := by
    have hc : (0:ℝ) < 1 + 1 / (2 * N ^ 2) := by positivity
    have hfac : d * s + d * s / (2 * N ^ 2) = (d * s) * (1 + 1 / (2 * N ^ 2)) := by
      field_simp
    have habs : |d * s| * (1 + 1 / (2 * N ^ 2)) ≤ 40 / lam ^ 4 + L := by
      have h1 : |(d * s) * (1 + 1 / (2 * N ^ 2))| ≤ 40 / lam ^ 4 + L := by
        rw [abs_le]
        constructor <;>
          [linarith only [hk1.1, hfac, hLpos]; linarith only [hk1.2, hfac, hLpos]]
      rwa [abs_mul, abs_of_pos hc] at h1
    have hcge : (0:ℝ) ≤ 1 / (2 * N ^ 2) := by positivity
    have habs' : |d * s| + |d * s| * (1 / (2 * N ^ 2)) ≤ 40 / lam ^ 4 + L := by
      calc |d * s| + |d * s| * (1 / (2 * N ^ 2))
          = |d * s| * (1 + 1 / (2 * N ^ 2)) := by ring
        _ ≤ 40 / lam ^ 4 + L := habs
    have h2 : |d * s| ≤ 40 / lam ^ 4 + L := by
      linarith only [habs', mul_nonneg (abs_nonneg (d * s)) hcge]
    have habsds : |d * s| = |d| * s := by rw [abs_mul, abs_of_pos hs]
    have h3 : |d| * s ≤ 2 * s := by
      rw [← habsds]
      linarith only [h2, heps1, hLub0]
    have h5 := abs_nonneg d
    nlinarith [h3, hs]
  have hd4 : d ^ 2 ≤ 4 := by nlinarith [sq_abs d, abs_nonneg d, hdabs]
  have hs2ub : s ^ 2 ≤ 4 * lam ^ 2 + 10 := by
    linarith only [hk2.2, hQub, hAb.1, hAb.2, hd4, heps2]
  have hNub : N ≤ 2 * lam ^ 2 + 7 := by linarith only [hNsd, hs2ub, hd4]
  have hLmu : |L - mu| ≤ 2 / lam ^ 2 := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have hlamsq : (0:ℝ) < lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (4 * Real.pi * N) = Real.log (4 * Real.pi) + Real.log N :=
      Real.log_mul (by positivity) hN0.ne'
    have e1 : Real.log (8 * Real.pi * lam ^ 2)
        = Real.log (4 * Real.pi) + Real.log (2 * lam ^ 2) := by
      rw [show (8:ℝ) * Real.pi * lam ^ 2 = (4 * Real.pi) * (2 * lam ^ 2) by ring]
      exact Real.log_mul (by positivity) hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h1 : Real.log (N / (2 * lam ^ 2)) ≤ N / (2 * lam ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hN0 hlam2pos)
    have h2 : Real.log ((2 * lam ^ 2) / N) ≤ (2 * lam ^ 2) / N - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlam2pos hN0)
    have h3 : Real.log ((2 * lam ^ 2) / N) = - Real.log (N / (2 * lam ^ 2)) := by
      rw [Real.log_div hlam2pos.ne' hN0.ne', e2]; ring
    have g1 : N / (2 * lam ^ 2) - 1 ≤ 4 / lam ^ 2 := by
      rw [div_sub_one hlam2pos.ne', div_le_div_iff₀ hlam2pos hlamsq]
      nlinarith [hNub, hlam2]
    have g2 : (2 * lam ^ 2) / N - 1 ≤ 4 / lam ^ 2 := by
      rw [div_sub_one hN0.ne', div_le_div_iff₀ hN0 hlamsq]
      nlinarith [hNlb, hlam2]
    have hhalf : (4:ℝ) / lam ^ 2 = 2 * (2 / lam ^ 2) := by ring
    rw [abs_le]
    constructor <;> linarith only [h1, h2, h3, g1, g2, hlogeq, hhalf]
  have hLup : 2 * (L - mu) ≤ (N - 2 * lam ^ 2) / (2 * lam ^ 2) := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (4 * Real.pi * N) = Real.log (4 * Real.pi) + Real.log N :=
      Real.log_mul (by positivity) hN0.ne'
    have e1 : Real.log (8 * Real.pi * lam ^ 2)
        = Real.log (4 * Real.pi) + Real.log (2 * lam ^ 2) := by
      rw [show (8:ℝ) * Real.pi * lam ^ 2 = (4 * Real.pi) * (2 * lam ^ 2) by ring]
      exact Real.log_mul (by positivity) hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h1 : Real.log (N / (2 * lam ^ 2)) ≤ N / (2 * lam ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hN0 hlam2pos)
    have hid : (N - 2 * lam ^ 2) / (2 * lam ^ 2) = N / (2 * lam ^ 2) - 1 := by
      field_simp
    rw [hid]
    linarith [hlogeq, h1]
  have hLlo : -(2 * (L - mu)) ≤ (2 * lam ^ 2 - N) / N := by
    have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by linarith only [hlam2]
    have e0 : Real.log (4 * Real.pi * N) = Real.log (4 * Real.pi) + Real.log N :=
      Real.log_mul (by positivity) hN0.ne'
    have e1 : Real.log (8 * Real.pi * lam ^ 2)
        = Real.log (4 * Real.pi) + Real.log (2 * lam ^ 2) := by
      rw [show (8:ℝ) * Real.pi * lam ^ 2 = (4 * Real.pi) * (2 * lam ^ 2) by ring]
      exact Real.log_mul (by positivity) hlam2pos.ne'
    have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
      Real.log_div hN0.ne' hlam2pos.ne'
    have e3 : Real.log ((2 * lam ^ 2) / N) = Real.log (2 * lam ^ 2) - Real.log N :=
      Real.log_div hlam2pos.ne' hN0.ne'
    have hlogeq : 2 * L - 2 * mu = Real.log (N / (2 * lam ^ 2)) := by
      rw [e2, hL, hmu, e0, e1]; ring
    have h2 : Real.log ((2 * lam ^ 2) / N) ≤ (2 * lam ^ 2) / N - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hlam2pos hN0)
    have hid : (2 * lam ^ 2 - N) / N = (2 * lam ^ 2) / N - 1 := by field_simp
    rw [hid]
    linarith [hlogeq, h2, e2, e3]
  exact ⟨hslb, hs2ub, hNlb, hNub, hdabs, hLmu, hLup, hLlo⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: the real-variable inversion of the third-order erfc zero equation at a fixed index;
-- proof infrastructure for DLMF 7.13.3, not itself a numbered display
/-- **Third-order inversion of the `erfc`-zero equation.**  Let `n ≥ 3400` and let `v` lie in
the open first quadrant with

`‖v² + log (√(4π) v) + 1/(2v²) − 2πi·n‖ ≤ ε`,  `ε ≤ 40/λₙ⁴`.

Then `Re v` and `Im v` agree with the *reflections* of the DLMF 7.13.3 approximations
`erfcZeroReApprox n`, `erfcZeroImApprox n` — the zeros of `erfc` sit in the sector
`re < 0 < im`, and `v = −conj w` folds them onto the first quadrant — to within

`(μ'ₙ + 3)⁴ / (20 λₙ⁵)`,

which is `O(log⁴ n · n^{-5/2}) = o(λₙ⁻³)`.

The proof is the `erf` inversion run with the model constant `√(4π) = 2√π` in place of `√π`
(this is the factor `2` in `μ' = log(2λ√(2π))` of DLMF 7.13.4): the real component equation
reads `d·s = −½log(4π‖v‖²) − ⋯`, the imaginary one is unchanged, and the four iteration steps
`erfc713_crude`, `erf713_first_order`, `erf713_diff_expansion`, `erf713_sum_expansion` apply
verbatim (the last three are stated abstractly in `(λ, μ, s, d, N, L, A)`). -/
theorem erfc713_zero_expansion {n : ℕ} (hn : 3400 ≤ n) {w : ℂ} {eps : ℝ}
    (hx : 0 < w.re) (hy : 0 < w.im) (heb : eps ≤ 40 / erfcZeroLambda n ^ 4)
    (heq : ‖w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ eps) :
    |w.re + erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) ∧
      |w.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  set lam : ℝ := erfcZeroLambda n with hlamdef
  set mu : ℝ := erfcZeroMu n with hmudef
  have hlamsq : lam ^ 2 = ((n:ℝ) - 1 / 8) * Real.pi := by
    rw [hlamdef]
    exact Real.sq_sqrt (by nlinarith)
  have hlamnn : (0:ℝ) ≤ lam := by rw [hlamdef]; exact Real.sqrt_nonneg _
  have hlam : (100:ℝ) ≤ lam := by nlinarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hmudef' : mu = Real.log (2 * lam * Real.sqrt (2 * Real.pi)) := by
    rw [hmudef, hlamdef]
    simp only [erfcZeroMu]
  obtain ⟨hmulb, -, hmuhalf⟩ := erfc713_mu_bounds hlam hmudef'
  have hmub : mu + 3 ≤ lam := by linarith
  have h2mu : 2 * mu = Real.log (8 * Real.pi * lam ^ 2) := by
    have h1 : Real.log ((2 * lam * Real.sqrt (2 * Real.pi)) ^ 2)
        = 2 * Real.log (2 * lam * Real.sqrt (2 * Real.pi)) := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : (2 * lam * Real.sqrt (2 * Real.pi)) ^ 2 = 8 * Real.pi * lam ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [← h2, h1, hmudef']
  -- the real and imaginary components of the hypothesis
  have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hnsq : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hnsq0 : (0:ℝ) < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have hN0 : (0:ℝ) < w.re ^ 2 + w.im ^ 2 := by rw [← hnsq]; exact hnsq0
  have hlogre : (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)).re
      = (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2)) := by
    have ht : (Real.sqrt (4 * Real.pi) * ‖w‖) ^ 2
        = 4 * Real.pi * (w.re ^ 2 + w.im ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Complex.sq_norm, hnsq]
    have h2 : Real.log ((Real.sqrt (4 * Real.pi) * ‖w‖) ^ 2)
        = 2 * Real.log (Real.sqrt (4 * Real.pi) * ‖w‖) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← ht, h2]
    ring
  have hlogim : (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)).im = Complex.arg w := by
    rw [Complex.log_im,
      Complex.arg_real_mul w (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 4 * Real.pi))]
  have hsqre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two, Complex.mul_re]
  have hsqim : (w ^ 2).im = 2 * w.re * w.im := by
    simp only [pow_two, Complex.mul_im]; ring
  have hns2 : Complex.normSq (2 * w ^ 2) = 4 * (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h4 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
    rw [map_mul, map_pow, hnsq, h4]
  have hre2 : (2 * w ^ 2 : ℂ).re = 2 * (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.mul_re, hsqre, hsqim]; simp
  have him2 : (2 * w ^ 2 : ℂ).im = 2 * (2 * w.re * w.im) := by
    rw [Complex.mul_im, hsqre, hsqim]; simp
  have hinvre : ((1 : ℂ) / (2 * w ^ 2)).re
      = (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_re, hre2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hinvim : ((1 : ℂ) / (2 * w ^ 2)).im
      = -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_im, him2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcre : (2 * (Real.pi : ℂ) * Complex.I * n).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hcim : (2 * (Real.pi : ℂ) * Complex.I * n).im = 2 * Real.pi * n := by
    simp [Complex.mul_re, Complex.mul_im]
  have harg : Complex.arg w
      = Real.pi / 4 - Real.arctan ((w.re - w.im) / (w.re + w.im)) :=
    arg_eq_pi_div_four_sub_arctan hx hy
  -- the two real equations
  have hbound : eps ≤ 40 / lam ^ 4 := heb
  have hreeq : |(w.re - w.im) * (w.re + w.im)
      + (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
      + (w.re - w.im) * (w.re + w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)| ≤ 40 / lam ^ 4 := by
    have h := (Complex.abs_re_le_norm (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * n)).trans (heq.trans hbound)
    simp only [Complex.sub_re, Complex.add_re, hsqre, hlogre, hinvre, hcre] at h
    calc |(w.re - w.im) * (w.re + w.im)
          + (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re - w.im) * (w.re + w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        = |w.re ^ 2 - w.im ^ 2 + (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 0| := by
          congr 1; ring
      _ ≤ 40 / lam ^ 4 := h
  have himeq : |(w.re + w.im) ^ 2 - (w.re - w.im) ^ 2
      - 2 * Real.arctan ((w.re - w.im) / (w.re + w.im))
      - ((w.re + w.im) ^ 2 - (w.re ^ 2 + w.im ^ 2)) / (w.re ^ 2 + w.im ^ 2) ^ 2
      - 4 * lam ^ 2| ≤ 80 / lam ^ 4 := by
    have h := (Complex.abs_im_le_norm (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * n)).trans (heq.trans hbound)
    simp only [Complex.sub_im, Complex.add_im, hsqim, hlogim, hinvim, hcim, harg] at h
    have hid : (w.re + w.im) ^ 2 - (w.re - w.im) ^ 2
        - 2 * Real.arctan ((w.re - w.im) / (w.re + w.im))
        - ((w.re + w.im) ^ 2 - (w.re ^ 2 + w.im ^ 2)) / (w.re ^ 2 + w.im ^ 2) ^ 2
        - 4 * lam ^ 2
        = 2 * (2 * w.re * w.im
          + (Real.pi / 4 - Real.arctan ((w.re - w.im) / (w.re + w.im)))
          + -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 2 * Real.pi * n) := by
      rw [hlamsq]; field_simp; ring
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h40 : (40:ℝ) / lam ^ 4 * 2 = 80 / lam ^ 4 := by ring
    linarith [h, h40.le, h40.ge]
  -- the real-variable inversion
  have hs : (0:ℝ) < w.re + w.im := by linarith
  have hNsd : 2 * (w.re ^ 2 + w.im ^ 2) = (w.re + w.im) ^ 2 + (w.re - w.im) ^ 2 := by ring
  have hQlt : w.re ^ 2 + w.im ^ 2 < (w.re + w.im) ^ 2 := by nlinarith
  have hd2s : (w.re - w.im) ^ 2 ≤ (w.re + w.im) ^ 2 := by nlinarith
  have hAbd : |Real.arctan ((w.re - w.im) / (w.re + w.im))| ≤ 2 := by
    have h1 := Real.neg_pi_div_two_lt_arctan ((w.re - w.im) / (w.re + w.im))
    have h2 := Real.arctan_lt_pi_div_two ((w.re - w.im) / (w.re + w.im))
    rw [abs_le]
    constructor <;> linarith [Real.pi_lt_four]
  have hAT := abs_arctan_sub_self_le ((w.re - w.im) / (w.re + w.im))
  have hL : (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
      = (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2)) := rfl
  obtain ⟨hslb, -, hNlb, hNub, hdabs, hLmu0, hLup, hLlo⟩ :=
    erfc713_crude hlam h2mu hL hs hd2s hNsd hQlt hAbd hreeq himeq
  obtain ⟨hdm, hT3, hs2m, hNm, hsm, hLm0, hdsle⟩ :=
    erf713_first_order hlam hmulb hmub hs hNsd hQlt hslb hNlb hNub hdabs hLmu0 hLup hLlo hAT
      hreeq himeq
  have hX := erf713_diff_expansion hlam hmulb hmub hs hslb hNlb hdsle hLm0 hsm hreeq
  have hS := erf713_sum_expansion hlam hmulb hmub hs hNsd hQlt hslb hNlb hNub hAT himeq hdm hT3
    hs2m hNm hsm hX
  -- assemble
  have hm0 : (0:ℝ) ≤ mu + 3 := by linarith
  have hm8 : (8:ℝ) ≤ mu + 3 := by linarith
  have hlam5 : (0:ℝ) < 20 * lam ^ 5 := by positivity
  have hSd : |(w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))|
      ≤ (mu + 3) ^ 4 / (20 * lam ^ 5) := by
    rw [le_div_iff₀ hlam5]; exact hS
  have hXd : |(w.re - w.im) + mu / (2 * lam)| ≤ (mu + 3) ^ 4 / (20 * lam ^ 5) := by
    rw [le_div_iff₀ hlam5]
    nlinarith [hX, hm0, hm8, abs_nonneg ((w.re - w.im) + mu / (2 * lam)),
      pow_pos hlam0 5]
  have hApproxRe : -erfcZeroReApprox n
      = ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) + -(mu / (2 * lam))) / 2 := by
    rw [erfcZeroReApprox, ← hlamdef, ← hmudef]
    field_simp
    ring
  have hApproxIm : erfcZeroImApprox n
      = ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)) - -(mu / (2 * lam))) / 2 := by
    rw [erfcZeroImApprox, ← hlamdef, ← hmudef]
    field_simp
    ring
  constructor
  · rw [show w.re + erfcZeroReApprox n = w.re - -erfcZeroReApprox n by ring, hApproxRe]
    have hid : w.re - ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))
        + -(mu / (2 * lam))) / 2
        = (((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
          + ((w.re - w.im) + mu / (2 * lam))) / 2 := by ring
    rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h := (abs_add_le ((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
      ((w.re - w.im) + mu / (2 * lam)))
    linarith [h, hSd, hXd]
  · rw [hApproxIm]
    have hid : w.im - ((2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3))
        - -(mu / (2 * lam))) / 2
        = (((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
          - ((w.re - w.im) + mu / (2 * lam))) / 2 := by ring
    rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h := abs_sub_le_abs_add_abs ((w.re + w.im) - (2 * lam + (mu ^ 2 - 2 * mu + 2) / (16 * lam ^ 3)))
      ((w.re - w.im) + mu / (2 * lam))
    linarith [h, hSd, hXd]


set_option maxHeartbeats 800000 in
-- no-dlmf: crude localization of the modulus of a solution of the third-order erfc zero
-- equation; proof infrastructure for the §7.13 zero asymptotics
/-- **Crude modulus localization from the erfc index equation.**  If a first-quadrant point `v`
with `‖v‖ ≥ 20` satisfies the third-order `erfc` zero equation at index `k`, then
`|‖v‖² − 2πk| ≤ 15`.

Only the two component equations are used: the imaginary part gives `2xy = 2πk + O(1)`, while
the real part bounds `|x² − y²| ≤ ½ log(π‖w‖²) + o(1) ≤ √π‖w‖`, hence
`‖w‖² − 2xy = (x − y)² ≤ π + o(1)`.  The constant `15` is crude — the sharp `±1` comes later from
`erfc713_approx_norm_sq` — but it already forces `k ≍ ‖w‖²/2π`, which is what is needed to feed
`erf713_zero_expansion`. -/
theorem erfc713_crude_modulus {w : ℂ} (hx : 0 < w.re) (hy : 0 < w.im) (hbig : 20 ≤ ‖w‖)
    {k : ℤ} (heq : ‖w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 150 / ‖w‖ ^ 4) :
    |‖w‖ ^ 2 - 2 * Real.pi * k| ≤ 15 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hwn : (0:ℝ) < ‖w‖ := by linarith
  have hN : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN0 : (400:ℝ) ≤ w.re ^ 2 + w.im ^ 2 := by rw [← hN]; nlinarith
  have hw4 : ‖w‖ ^ 4 = (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hN]
  have hsqre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two, Complex.mul_re]
  have hsqim : (w ^ 2).im = 2 * w.re * w.im := by simp only [pow_two, Complex.mul_im]; ring
  have hnsq : Complex.normSq w = w.re ^ 2 + w.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hlogre : (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)).re
      = (1 / 2) * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2)) := by
    have ht : (Real.sqrt (4 * Real.pi) * ‖w‖) ^ 2
        = 4 * Real.pi * (w.re ^ 2 + w.im ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Complex.sq_norm, hnsq]
    have h2 : Real.log ((Real.sqrt (4 * Real.pi) * ‖w‖) ^ 2)
        = 2 * Real.log (Real.sqrt (4 * Real.pi) * ‖w‖) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← ht, h2]
    ring
  have hlogim : (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)).im = Complex.arg w := by
    rw [Complex.log_im,
      Complex.arg_real_mul w (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 4 * Real.pi))]
  have hns2 : Complex.normSq (2 * w ^ 2) = 4 * (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h4 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
    rw [map_mul, map_pow, hnsq, h4]
  have hre2 : (2 * w ^ 2 : ℂ).re = 2 * (w.re ^ 2 - w.im ^ 2) := by
    rw [Complex.mul_re, hsqre, hsqim]; simp
  have him2 : (2 * w ^ 2 : ℂ).im = 2 * (2 * w.re * w.im) := by
    rw [Complex.mul_im, hsqre, hsqim]; simp
  have hinvre : ((1 : ℂ) / (2 * w ^ 2)).re
      = (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_re, hre2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hinvim : ((1 : ℂ) / (2 * w ^ 2)).im
      = -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) := by
    rw [one_div, Complex.inv_im, him2, hns2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hcre : (2 * (Real.pi : ℂ) * Complex.I * (k:ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have hcim : (2 * (Real.pi : ℂ) * Complex.I * (k:ℂ)).im = 2 * Real.pi * (k:ℝ) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hw4] at heq
  have hrepart : |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
      + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        ≤ 150 / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h := (Complex.abs_re_le_norm (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans heq
    simp only [Complex.sub_re, Complex.add_re, hsqre, hlogre, hinvre, hcre] at h
    calc |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2)|
        = |w.re ^ 2 - w.im ^ 2 + 1 / 2 * Real.log (4 * Real.pi * (w.re ^ 2 + w.im ^ 2))
          + (w.re ^ 2 - w.im ^ 2) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 0| := by
          congr 1; ring
      _ ≤ _ := h
  have himpart : |2 * w.re * w.im + Complex.arg w
      + -(2 * w.re * w.im) / (2 * (w.re ^ 2 + w.im ^ 2) ^ 2) - 2 * Real.pi * (k:ℝ)|
        ≤ 150 / (w.re ^ 2 + w.im ^ 2) ^ 2 := by
    have h := (Complex.abs_im_le_norm (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
      + 1 / (2 * w ^ 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans heq
    simp only [Complex.sub_im, Complex.add_im, hsqim, hlogim, hinvim, hcim] at h
    exact h
  clear heq hsqre hsqim hlogre hlogim hns2 hre2 him2 hinvre hinvim hcre hcim hnsq hw4
  set N : ℝ := w.re ^ 2 + w.im ^ 2 with hNdef
  have hN0' : (0:ℝ) < N := by linarith
  have hNsq : (160000:ℝ) ≤ N ^ 2 := by nlinarith
  have hsmall : 150 / N ^ 2 ≤ 1/1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hNinv : 1 / (2 * N) ≤ 1/800 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hpiN : (0:ℝ) < 4 * Real.pi * N := by nlinarith
  have hL0 : (0:ℝ) ≤ 1 / 2 * Real.log (4 * Real.pi * N) := by
    have h1 : (1:ℝ) ≤ 4 * Real.pi * N := by nlinarith
    linarith [Real.log_nonneg h1]
  have hsp : Real.sqrt (4 * Real.pi) ≤ 3.545 := by
    have h : Real.sqrt (4 * Real.pi) ≤ Real.sqrt (3.545 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3.545)] at h
  have hspnn : (0:ℝ) ≤ Real.sqrt (4 * Real.pi) := Real.sqrt_nonneg _
  have hLub : 1 / 2 * Real.log (4 * Real.pi * N) ≤ Real.sqrt (4 * Real.pi) * ‖w‖ := by
    have hsq1 : Real.log (Real.sqrt (4 * Real.pi * N)) ≤ Real.sqrt (4 * Real.pi * N) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpiN)
    have hsq2 : Real.log (Real.sqrt (4 * Real.pi * N)) = Real.log (4 * Real.pi * N) / 2 :=
      Real.log_sqrt hpiN.le
    have hsq3 : Real.sqrt (4 * Real.pi * N) = Real.sqrt (4 * Real.pi) * ‖w‖ := by
      rw [Real.sqrt_mul (by positivity), ← hN, Real.sqrt_sq (norm_nonneg w)]
    rw [hsq2, hsq3] at hsq1
    linarith
  have hAle : |w.re ^ 2 - w.im ^ 2| ≤ N := by
    rw [abs_le, hNdef]
    constructor <;> nlinarith [sq_nonneg w.re, sq_nonneg w.im]
  have hinvA : |(w.re ^ 2 - w.im ^ 2) / (2 * N ^ 2)| ≤ 1 / (2 * N) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hAle, abs_nonneg (w.re ^ 2 - w.im ^ 2)]
  have hA : |w.re ^ 2 - w.im ^ 2| ≤ Real.sqrt (4 * Real.pi) * ‖w‖ + 1/400 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hrepart
    obtain ⟨h3, h4⟩ := abs_le.mp hinvA
    rw [abs_le]
    constructor <;> linarith
  have hxysum : ‖w‖ ≤ w.re + w.im := by
    nlinarith [hN, mul_pos hx hy, norm_nonneg w, sq_nonneg (w.re + w.im - ‖w‖)]
  have hfac : |w.re ^ 2 - w.im ^ 2| = |w.re - w.im| * (w.re + w.im) := by
    rw [show w.re ^ 2 - w.im ^ 2 = (w.re - w.im) * (w.re + w.im) by ring, abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < w.re + w.im)]
  have hdiffabs : |w.re - w.im| * ‖w‖ ≤ |w.re ^ 2 - w.im ^ 2| := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hxysum (abs_nonneg _)
  have hd1 : |w.re - w.im| ≤ Real.sqrt (4 * Real.pi) + 1/4000 := by
    nlinarith [hdiffabs, hA, abs_nonneg (w.re - w.im)]
  have hsqd : (w.re - w.im) ^ 2 ≤ 12.6 := by
    have h0 : (0:ℝ) ≤ |w.re - w.im| := abs_nonneg _
    have hsq := mul_self_le_mul_self h0 hd1
    rw [abs_mul_abs_self] at hsq
    have hpisq : Real.sqrt (4 * Real.pi) * Real.sqrt (4 * Real.pi) = 4 * Real.pi :=
      Real.mul_self_sqrt (by positivity)
    nlinarith [hsq, hpisq, hsp, hspnn]
  have harg : |Complex.arg w| ≤ Real.pi / 2 :=
    (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)).le
  have hxyt : |-(2 * w.re * w.im) / (2 * N ^ 2)| ≤ 1 / (2 * N) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |-(2 * w.re * w.im)| = 2 * w.re * w.im := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [h1, hNdef]
    nlinarith [sq_nonneg (w.re - w.im), mul_pos hx hy]
  have himb : |2 * w.re * w.im - 2 * Real.pi * (k:ℝ)| ≤ 158/100 := by
    obtain ⟨h1, h2⟩ := abs_le.mp himpart
    obtain ⟨h3, h4⟩ := abs_le.mp hxyt
    obtain ⟨h5, h6⟩ := abs_le.mp harg
    rw [abs_le]
    constructor <;> linarith
  have hNxy : N - 2 * w.re * w.im = (w.re - w.im) ^ 2 := by rw [hNdef]; ring
  obtain ⟨h1, h2⟩ := abs_le.mp himb
  rw [hN, abs_le]
  constructor <;> linarith [hsqd, hNxy, sq_nonneg (w.re - w.im)]


-- no-dlmf: passage from the third-order erfc zero equation at a known index to the DLMF 7.13.3
-- approximations; proof infrastructure for the §7.13 zero asymptotics
/-- **Matching a solution of the index-`n` erfc equation to the DLMF approximations.**  For
`n ≥ 3400` a first-quadrant point `v` with `‖v‖ ≥ 20` satisfying the third-order `erfc` zero
equation *at index `n`* lies within `(μ'ₙ + 3)⁴/(20 λₙ⁵)` of the reflected DLMF 7.13.3
approximations `(−erfcZeroReApprox n, erfcZeroImApprox n)`.

This is `erfc713_zero_expansion` with its hypothesis `ε ≤ 40/λₙ⁴` discharged: the crude modulus
bound `|‖v‖² − 2πn| ≤ 15` of `erfc713_crude_modulus` gives `‖v‖² ≥ 1.94 λₙ²`, hence
`‖v‖⁴ ≥ 3.75 λₙ⁴` and `150/‖v‖⁴ ≤ 40/λₙ⁴`. -/
theorem erfc713_zero_match {n : ℕ} (hn : 3400 ≤ n) {w : ℂ} (hx : 0 < w.re) (hy : 0 < w.im)
    (hbig : 20 ≤ ‖w‖)
    (heq : ‖w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
        - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ 150 / ‖w‖ ^ 4) :
    |w.re + erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) ∧
      |w.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erfc713_param_bounds hn
  have hlam0 : (0:ℝ) < erfcZeroLambda n := by linarith
  have hn1 : 1 ≤ n := by omega
  have hlamsq := erfc713_lambda_sq hn1
  have heq' : ‖w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * ((n:ℤ):ℂ)‖ ≤ 150 / ‖w‖ ^ 4 := by
    push_cast
    exact heq
  have hcm := erfc713_crude_modulus hx hy hbig heq'
  have hcast : (((n:ℤ)):ℝ) = (n:ℝ) := by push_cast; ring
  rw [hcast] at hcm
  have h2pin : 2 * Real.pi * (n:ℝ) = 2 * erfcZeroLambda n ^ 2 + Real.pi / 4 := by
    rw [hlamsq]; ring
  rw [h2pin] at hcm
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcm
  have hlow : 1.94 * erfcZeroLambda n ^ 2 ≤ ‖w‖ ^ 2 := by
    nlinarith [Real.pi_pos, hlam]
  have hw4eq : ‖w‖ ^ 4 = (‖w‖ ^ 2) ^ 2 := by ring
  have hquart : 3.75 * erfcZeroLambda n ^ 4 ≤ ‖w‖ ^ 4 := by
    rw [hw4eq]; nlinarith [hlow, hlam0]
  have hwpos : (0:ℝ) < ‖w‖ := by linarith
  have hw40 : (0:ℝ) < ‖w‖ ^ 4 := by positivity
  have heb : 150 / ‖w‖ ^ 4 ≤ 40 / erfcZeroLambda n ^ 4 := by
    rw [div_le_div_iff₀ hw40 (by positivity)]
    nlinarith [hquart]
  exact erfc713_zero_expansion hn hx hy heb heq


set_option maxHeartbeats 1000000 in
-- no-dlmf: existence of a zero of `cerfc` matching the DLMF 7.13.3 approximations at each large
-- index; proof infrastructure for the §7.13 zero asymptotics
/-- **The grid zero at index `n` (erfc).**  For every `n ≥ 3400` there is a zero of `erfc` in the
sector `re < 0 < im` whose coordinates match `erfcZeroReApprox n`, `erfcZeroImApprox n` to
within `(μ'ₙ + 3)⁴/(20 λₙ⁵)`.

The work is done in the reflected variable `v = −conj u` (first quadrant, `erf v = −1`): the
zero is the one produced near the `n`-th model root of `2√π v e^{v²} = 1` by
`exists_cerf_negone_near_model`, and the only new step is *index pinning* — the integer `k`
supplied by `cerf_negone_log_equation_third` there must be `n`, because
`v² + log(√(4π) v) = 2πi n` exactly while `‖w − v‖ < 12/‖v‖³` moves
`z ↦ z² + log(√(4π) z) + 1/(2z²)` by less than `1 ≪ 2π`. -/
theorem erfc713_grid_zero (n : ℕ) (hn : 3400 ≤ n) :
    ∃ u : ℂ, cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧
      |u.re - erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) ∧
      |u.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
  have hn' : (3400:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  have hsppos : (0:ℝ) < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨v, hvn, hvre6, hvim6, hvloc, hvlog, hvmodel⟩ := exists_model_root_erfc n (by omega)
  have h2pin : ‖2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ = 2 * Real.pi * (n:ℝ) := by
    have hid : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n:ℂ)
        = ((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hid, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hVbig : (100:ℝ) ≤ ‖v‖ := by
    have h1 := norm_sub_norm_le (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (v ^ 2)
    rw [h2pin, norm_pow,
      norm_sub_rev (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (v ^ 2)] at h1
    nlinarith [hvloc, h1, norm_nonneg v]
  have hV0 : (0:ℝ) < ‖v‖ := by linarith
  have hre1 : (1:ℝ) ≤ v.re := by linarith
  obtain ⟨w, hw, hwb⟩ := exists_cerf_negone_near_model hre1 (by linarith) hvmodel
  set V : ℝ := ‖v‖ with hVdef
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; positivity
  have hV2 : (10000:ℝ) ≤ V ^ 2 := by nlinarith
  have hV2' : 100 * V ≤ V ^ 2 := by nlinarith
  have hV3 : (1000000:ℝ) ≤ V ^ 3 := by nlinarith
  have hV3' : 100 * V ^ 2 ≤ V ^ 3 := by nlinarith
  have hρsmall : ρ ≤ 1/1000 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hwv : ‖w - v‖ ≤ ρ := le_of_lt hwb
  have hmemball : ∀ z ∈ Metric.closedBall v ρ, 0 < z.re ∧ V - ρ ≤ ‖z‖ := by
    intro z hz
    have hzv : ‖z - v‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - v)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hzv)
    have h2 := norm_sub_norm_le v z
    rw [norm_sub_rev v z] at h2
    exact ⟨by linarith [h1.1], by linarith⟩
  have hwcb : w ∈ Metric.closedBall v ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwv
  obtain ⟨hx, hwlow⟩ := hmemball w hwcb
  have hwim : |w.im - v.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (w - v)
    simp only [Complex.sub_im] at h; linarith
  have hy : 0 < w.im := by
    have h := abs_le.mp hwim; linarith [h.1]
  have hwn2 : ‖w‖ ≤ V + ρ := by
    have h := norm_sub_norm_le w v
    linarith
  have hbigw : (20:ℝ) ≤ ‖w‖ := by linarith
  have hwsq : (400:ℝ) ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hwqu : (160000:ℝ) ≤ ‖w‖ ^ 4 := by nlinarith [hwsq]
  obtain ⟨k, hk⟩ := cerf_negone_log_equation_third hw hx (by linarith : (4:ℝ) ≤ ‖w‖)
  have hkn : k = (n:ℤ) := by
    by_contra hne
    have hlogmvt : ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
        - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ ≤ (1 / (V - ρ)) * ‖w - v‖ := by
      refine norm_sub_le_of_hasDerivAt_le
        (f := fun z : ℂ => Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * z))
        (f' := fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) / ((Real.sqrt (4 * Real.pi) : ℂ) * z))
        (convex_closedBall v ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hwcb
      · intro z hz
        obtain ⟨hz1, hz2⟩ := hmemball z hz
        have hslit : ((Real.sqrt (4 * Real.pi) : ℂ)) * z ∈ Complex.slitPlane := by
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          positivity
        have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt (4 * Real.pi) : ℂ)) * z)
            ((Real.sqrt (4 * Real.pi) : ℂ)) z := by
          simpa using (hasDerivAt_id z).const_mul ((Real.sqrt (4 * Real.pi) : ℂ))
        exact h1.clog hslit
      · intro z hz
        obtain ⟨hz1, hz2⟩ := hmemball z hz
        have hzn : (0:ℝ) < ‖z‖ := by linarith
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
          div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith [hz2, hsppos]
    have hid : 2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))
        = (w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
             - 2 * (Real.pi : ℂ) * Complex.I * (k:ℂ))
          - ((w ^ 2 - v ^ 2)
             + (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
                - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v))
             + 1 / (2 * w ^ 2)) := by
      linear_combination -hvlog
    have hw0 : w ≠ 0 := by intro h; rw [h] at hx; simp at hx
    have hqn : ‖(1:ℂ) / (2 * w ^ 2)‖ = 1 / (2 * ‖w‖ ^ 2) := by
      rw [norm_div, norm_one, norm_mul, norm_pow]; norm_num
    have hp3 : ‖(1:ℂ) / (2 * w ^ 2)‖ ≤ 1/100 := by
      rw [hqn, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hp1 : ‖w ^ 2 - v ^ 2‖ ≤ 1/100 := by
      have hfac : w ^ 2 - v ^ 2 = (w - v) * (w + v) := by ring
      have h1 : ‖w + v‖ ≤ 2 * V + ρ := by
        have h := norm_add_le w v; linarith
      have h2 : ‖w ^ 2 - v ^ 2‖ ≤ ρ * (2 * V + ρ) := by
        rw [hfac, norm_mul]
        exact mul_le_mul hwv h1 (norm_nonneg _) hρ0.le
      have hb1 : ρ * (2 * V + ρ) ≤ ρ * (2 * V + 1) := by nlinarith
      have hb2 : ρ * (2 * V + 1) ≤ 1/100 := by
        rw [hρdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hp2 : ‖Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
        - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v)‖ ≤ 1/100 := by
      have h1 : 1 / (V - ρ) ≤ 1/99 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h2 : (1 / (V - ρ)) * ‖w - v‖ ≤ (1/99) * (1/1000) := by
        refine mul_le_mul h1 (by linarith) (norm_nonneg _) (by norm_num)
      linarith
    have hA1 : 150 / ‖w‖ ^ 4 ≤ 1/1000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hub : ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ ≤ 1 := by
      rw [hid]
      have hsec : ‖(w ^ 2 - v ^ 2)
             + (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
                - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v))
             + 1 / (2 * w ^ 2)‖ ≤ 3/100 := by
        refine (norm_add_le _ _).trans ?_
        have := norm_add_le (w ^ 2 - v ^ 2) (Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w)
                - Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v))
        linarith
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hlb : (6:ℝ) ≤ ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ := by
      have hne' : ((n:ℤ) - k) ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
      have habs : (1:ℤ) ≤ |(n:ℤ) - k| := Int.one_le_abs hne'
      have hm : ((n:ℂ) - (k:ℂ)) = (((n:ℤ) - k : ℤ) : ℂ) := by push_cast; ring
      rw [hm, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((((n:ℤ) - k : ℤ)) : ℂ)
          = ((2 * Real.pi * ((((n:ℤ) - k : ℤ)) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hcast1 : (1:ℝ) ≤ |((((n:ℤ) - k : ℤ)) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast habs
      nlinarith [hcast1]
    linarith
  rw [hkn] at hk
  have hk' : ‖w ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * w) + 1 / (2 * w ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ ≤ 150 / ‖w‖ ^ 4 := by
    push_cast at hk
    exact hk
  obtain ⟨hr, hi⟩ := erfc713_zero_match hn hx hy hbigw hk'
  refine ⟨-(starRingEnd ℂ w), cerfc_zero_iff.mpr (by simpa using hw), ?_, ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · have hre' : (-(starRingEnd ℂ w)).re = -w.re := by simp
    rw [hre', show -w.re - erfcZeroReApprox n = -(w.re + erfcZeroReApprox n) by ring, abs_neg]
    exact hr
  · have him' : (-(starRingEnd ℂ w)).im = w.im := by simp
    rw [him']
    exact hi



-- no-dlmf: the modulus of a zero of `cerfc` matching the DLMF 7.13.3 approximations at index
-- `n`; proof infrastructure for the §7.13 zero asymptotics
/-- **The modulus of a point matching the DLMF 7.13.3 approximations at index `n`.**  For
`n ≥ 3400`, any `u` whose real and imaginary parts lie within the `erfc713_zero_expansion` error
`(μ'ₙ + 3)⁴/(20λₙ⁵)` of `erfcZeroReApprox n`, `erfcZeroImApprox n` satisfies
`|‖u‖² − 2λₙ²| ≤ 1`, together with the sector data `‖u‖ ≥ 20`, `‖u‖ ≤ −6 Re u` that the
reflected separation result `cerf_negone_unique_in_small_ball` requires.  Since consecutive grid
values `2λₙ²` are `2π > 2` apart, the first estimate *determines* the index `n` from `‖u‖`. -/
theorem erfc713_approx_norm_sq {n : ℕ} (hn : 3400 ≤ n) {u : ℂ}
    (hre : |u.re - erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5))
    (him : |u.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5)) :
    |‖u‖ ^ 2 - 2 * erfcZeroLambda n ^ 2| ≤ 1 ∧ 20 ≤ ‖u‖ ∧ ‖u‖ ≤ 6 * (-u.re) := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erfc713_param_bounds hn
  have hlam0 : (0:ℝ) < erfcZeroLambda n := by linarith
  have hD0 : (0:ℝ) ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by positivity
  have hD' : (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5)
      ≤ 1 / (20 * erfcZeroLambda n) := by
    refine hD.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hnsq : ‖u‖ ^ 2 = (-u.re) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre' : |(-u.re) - (erfcZeroLambda n - (1/4) * erfcZeroMu n * (erfcZeroLambda n)⁻¹
      + (1/16) * (1 - erfcZeroMu n + (1/2) * erfcZeroMu n ^ 2) * (erfcZeroLambda n)⁻¹ ^ 3)|
      ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
    rw [show (-u.re) - (erfcZeroLambda n - (1/4) * erfcZeroMu n * (erfcZeroLambda n)⁻¹
        + (1/16) * (1 - erfcZeroMu n + (1/2) * erfcZeroMu n ^ 2) * (erfcZeroLambda n)⁻¹ ^ 3)
        = -(u.re - erfcZeroReApprox n) by simp only [erfcZeroReApprox]; ring, abs_neg]
    exact hre
  have him' : |u.im - (erfcZeroLambda n + (1/4) * erfcZeroMu n * (erfcZeroLambda n)⁻¹
      + (1/16) * (1 - erfcZeroMu n + (1/2) * erfcZeroMu n ^ 2) * (erfcZeroLambda n)⁻¹ ^ 3)|
      ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
    rw [show erfcZeroLambda n + (1/4) * erfcZeroMu n * (erfcZeroLambda n)⁻¹
        + (1/16) * (1 - erfcZeroMu n + (1/2) * erfcZeroMu n ^ 2) * (erfcZeroLambda n)⁻¹ ^ 3
        = erfcZeroImApprox n by simp only [erfcZeroImApprox]]
    exact him
  obtain ⟨h1, h2, -⟩ :=
    erf713_norm_sq_aux hlam hmu5 (by linarith) hD0 hD' hre' him'
  have hA : |‖u‖ ^ 2 - 2 * erfcZeroLambda n ^ 2| ≤ 1 := by rw [hnsq]; exact h1
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hre0 : (0:ℝ) < -u.re := by linarith
  have h20 : 20 ≤ ‖u‖ := by nlinarith [norm_nonneg u]
  have hlt : ‖u‖ ^ 2 < (6 * (-u.re)) ^ 2 := by nlinarith
  exact ⟨hA, h20, by nlinarith [norm_nonneg u, hre0.le]⟩

-- no-dlmf: local uniqueness of the `cerfc` zero attached to an index; proof infrastructure
/-- **At most one zero per index (erfc).**  Two zeros of `erfc` both matching the DLMF 7.13.3
approximations at the same index `n ≥ 3400` coincide.

Both lie within `2·(μ'ₙ+3)⁴/(20λₙ⁵) ≤ 1/(160λₙ)` of the same point, hence within `1/(24‖u‖)` of
each other, and the reflected separation result `cerf_negone_unique_in_small_ball` applies with
centre `−conj u`. -/
theorem erfc713_zero_index_unique {n : ℕ} (hn : 3400 ≤ n) {u u' : ℂ}
    (hu : cerfc u = 0) (hu' : cerfc u' = 0)
    (hre : |u.re - erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5))
    (him : |u.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5))
    (hre' : |u'.re - erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5))
    (him' : |u'.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5)) :
    u = u' := by
  obtain ⟨hlam, hmu5, hmu3, hD⟩ := erfc713_param_bounds hn
  have hlam0 : (0:ℝ) < erfcZeroLambda n := by linarith
  obtain ⟨hA, h20, h6⟩ := erfc713_approx_norm_sq hn hre him
  have hu0 : (0:ℝ) < ‖u‖ := by linarith
  set D : ℝ := (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) with hDdef
  have hD0 : (0:ℝ) ≤ D := by rw [hDdef]; positivity
  have hdist : ‖u' - u‖ ≤ 4 * D := by
    have h := Complex.norm_le_abs_re_add_abs_im (u' - u)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |u'.re - u.re| ≤ 2 * D := by
      obtain ⟨a1, a2⟩ := abs_le.mp hre
      obtain ⟨b1, b2⟩ := abs_le.mp hre'
      rw [abs_le]; constructor <;> linarith
    have h2 : |u'.im - u.im| ≤ 2 * D := by
      obtain ⟨a1, a2⟩ := abs_le.mp him
      obtain ⟨b1, b2⟩ := abs_le.mp him'
      rw [abs_le]; constructor <;> linarith
    linarith
  have hule : ‖u‖ ≤ 1.5 * erfcZeroLambda n := by
    obtain ⟨hA1, hA2⟩ := abs_le.mp hA
    nlinarith [norm_nonneg u]
  have hDw : D * ‖u‖ ≤ (1 / (320 * erfcZeroLambda n)) * (1.5 * erfcZeroLambda n) :=
    mul_le_mul hD hule (norm_nonneg u) (by positivity)
  have hval : (1 / (320 * erfcZeroLambda n)) * (1.5 * erfcZeroLambda n) = 1.5 / 320 := by
    field_simp
  rw [hval] at hDw
  have hfin : 4 * D ≤ 1 / (24 * ‖u‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hDw]
  -- transfer to the reflected first-quadrant points
  set v : ℂ := -(starRingEnd ℂ u) with hvdef
  set v' : ℂ := -(starRingEnd ℂ u') with hv'def
  have hvnorm : ‖v‖ = ‖u‖ := by rw [hvdef]; simp
  have hvre : v.re = -u.re := by rw [hvdef]; simp
  have hsector : ‖v‖ ≤ 6 * v.re := by rw [hvnorm, hvre]; exact h6
  have hvv' : ‖v' - v‖ = ‖u' - u‖ := by
    have h : v' - v = -((starRingEnd ℂ) (u' - u)) := by rw [hvdef, hv'def, map_sub]; ring
    rw [h, norm_neg, RCLike.norm_conj]
  have heq : v = v' :=
    cerf_negone_unique_in_small_ball hsector (by rw [hvnorm]; exact h20)
      (cerfc_zero_iff.mp hu) (cerfc_zero_iff.mp hu')
      (by simp) (by rw [hvv', hvnorm]; linarith [hdist])
  have := congrArg (fun z : ℂ => -(starRingEnd ℂ z)) heq
  simpa [hvdef, hv'def] using this



-- no-dlmf: every large sector zero of `cerfc` carries an index; proof infrastructure
/-- **Every large zero of `erfc` in the sector has an index.**  A zero of `erfc` in the open
sector `re < 0 < im` with `‖u‖² ≥ 21987` matches the DLMF 7.13.3 approximations at some index
`n ≥ 3500`.

The integer `k` of `cerf_negone_log_equation_third` at the reflected point `v = −conj u`
satisfies `2πk ≥ ‖u‖² − 15 ≥ 21972`, so `k ≥ 3497 ≥ 3400` and `erfc713_zero_match` applies; the
sharp bound `|‖u‖² − 2λₖ²| ≤ 1` of `erfc713_approx_norm_sq` then excludes every `k ≤ 3499`,
because `2λ₃₄₉₉² + 1 < 21987`. -/
theorem erfc713_zero_has_index {u : ℂ} (hu : cerfc u = 0) (hx : u.re < 0) (hy : 0 < u.im)
    (hbig : 21987 ≤ ‖u‖ ^ 2) :
    ∃ n : ℕ, 3500 ≤ n ∧
      |u.re - erfcZeroReApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) ∧
      |u.im - erfcZeroImApprox n| ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  set v : ℂ := -(starRingEnd ℂ) u with hvdef
  have hvnorm : ‖v‖ = ‖u‖ := by rw [hvdef]; simp
  have hvre : v.re = -u.re := by rw [hvdef]; simp
  have hvim : v.im = u.im := by rw [hvdef]; simp
  have hvx : 0 < v.re := by rw [hvre]; linarith
  have hvy : 0 < v.im := by rw [hvim]; exact hy
  have hv : cerf v = -1 := cerfc_zero_iff.mp hu
  have hv20 : (20:ℝ) ≤ ‖v‖ := by
    rw [hvnorm]; nlinarith [norm_nonneg u]
  obtain ⟨k, hk⟩ := cerf_negone_log_equation_third hv hvx (by linarith)
  have hcm := erfc713_crude_modulus hvx hvy hv20 hk
  rw [hvnorm] at hcm
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcm
  have hkbig : (3497:ℤ) ≤ k := by
    have hr : (3496:ℝ) < (k:ℝ) := by nlinarith
    have h : (3496:ℤ) < k := by exact_mod_cast hr
    omega
  have hk0 : (0:ℤ) ≤ k := by omega
  set n : ℕ := k.toNat with hndef
  have hkn : (n:ℤ) = k := Int.toNat_of_nonneg hk0
  have hn3497 : 3497 ≤ n := by omega
  have hcast : ((n:ℕ):ℂ) = ((k:ℤ):ℂ) := by rw [← hkn]; push_cast; ring
  have hk' : ‖v ^ 2 + Complex.log ((Real.sqrt (4 * Real.pi) : ℂ) * v) + 1 / (2 * v ^ 2)
      - 2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ ≤ 150 / ‖v‖ ^ 4 := by
    rw [hcast]; exact hk
  obtain ⟨hrv, hiv⟩ := erfc713_zero_match (by omega) hvx hvy hv20 hk'
  have hr : |u.re - erfcZeroReApprox n|
      ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
    rw [show u.re - erfcZeroReApprox n = -(v.re + erfcZeroReApprox n) by rw [hvre]; ring, abs_neg]
    exact hrv
  have hi : |u.im - erfcZeroImApprox n|
      ≤ (erfcZeroMu n + 3) ^ 4 / (20 * erfcZeroLambda n ^ 5) := by
    rw [← hvim]; exact hiv
  obtain ⟨hA, -, -⟩ := erfc713_approx_norm_sq (by omega) hr hi
  refine ⟨n, ?_, hr, hi⟩
  by_contra hlt
  have hnle : (n:ℝ) ≤ 3499 := by
    have h : n ≤ 3499 := by omega
    exact_mod_cast h
  have hlamsq := erfc713_lambda_sq (n := n) (by omega)
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hnpos : (0:ℝ) ≤ (n:ℝ) - 1/8 := by
    have h : (3497:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3497
    linarith
  have hprod : ((n:ℝ) - 1/8) * Real.pi ≤ 3498.875 * 3.141593 := by
    nlinarith [hpi2, hnle, hnpos, Real.pi_pos]
  nlinarith [hA2, hlamsq, hprod, hbig]


/-! ## The argument-principle count for `erfc` (`erfc713_low_zero_count`)

`cerfc` has no parity of its own, so the count runs through the *even*,
conjugation-equivariant auxiliary function

    F z := cerf z ^ 2 − 1 = (−cerfc z)·(2 − cerfc z),

whose zero set is `{cerfc = 0} ∪ −{cerfc = 0}`.  `F` has no zero on either coordinate
axis (`F < 0` on ℝ, `Re F ≤ −1` on `iℝ`), so the Klein group `{1, −1, conj, −conj}`
acts freely on its zeros and the disc count is `4·N` with **no** origin term — the one
structural difference from the `erf` branch.  `F` even ⇒ `F'` odd ⇒ `F'/F` odd, exactly
the parity the `erf` symmetry reduction uses, so the circle integral again folds to
`4i·Im J` on the quarter arc.  On that arc `F` is compared with the two-level model
`F_M = (−u)·(2 − u)`, `u(z) = e^{−z²}/(√π z)`: the `(−u)` factor is branch-free
(the antiderivative `erf713BigLambda` of the `erf` branch, contributing `−π/2`), and the
`(2 − u)` factor is the level-`a = 2` instance of the `erf` branch's split-point kit,
with `L₂ = log (2√π R)` in place of `L`.  Everything indexed by the radius
`R = erf713Rad = √21987` and by `u` is *shared verbatim* with `section Erf713ZeroCount`
above; only the level-`2` objects (`erfc713ThetaStar2`, `erfc713BigPsi2`,
`erfc713BigPhi2`, `erfc713ModelM2`, `erfc713KFun2`) are new.

The one genuinely new analytic input is that `cerfc` has **no zero in the closed right
half-plane** (`cerfc_ne_zero_of_re_nonneg`), needed to identify the second-quadrant
zeros of `F` with those of `cerfc` throughout the disc — including `‖z‖ ≤ 2`, where the
Poincaré remainder bound is useless.  It comes from DLMF **7.7.2**
(`faddeeva_eq_cauchyIntegral_real`): the Faddeeva function is the Cauchy transform of
the positive measure `e^{−t²} dt`, hence has positive real part on the upper half-plane
(`faddeeva_re_pos`), and `w(iw) = e^{w²} erfc w`. -/

section Erfc713ZeroCount

open Complex MeasureTheory Set FLMF.Methods

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- `L₂ = log (2 √π R) = L + log 2` — the level-`2` constant of the erfc model. -/
def erfc713BigL2 : ℝ := Real.log (2 * (Real.sqrt Real.pi * erf713Rad))

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_bigL2_eq : erfc713BigL2 = erf713BigL + Real.log 2 := by
  rw [erfc713BigL2, erf713BigL, Real.log_mul (by norm_num) erf713_sqrtPi_Rad_pos.ne']
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- Crude enclosure `0 < L₂ < 6.7` (numerically `L₂ = 6.2649`). -/
theorem erfc713_bigL2_bounds : 0 < erfc713BigL2 ∧ erfc713BigL2 < 6.7 := by
  obtain ⟨h1, h2⟩ := erf713_bigL_bounds
  have hlog2 : Real.log 2 < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [erfc713_bigL2_eq]
  exact ⟨by linarith, by linarith⟩

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- `F z = cerf z ^ 2 − 1`.  The even, conjugation-equivariant function whose zero set
is `{cerfc = 0} ∪ −{cerfc = 0}`. -/
def erfc713BigF (z : ℂ) : ℂ := cerf z ^ 2 - 1

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F = (−cerfc)·(2 − cerfc)`, from `cerf = 1 − cerfc`. -/
theorem erfc713_bigF_eq_cerfc (z : ℂ) : erfc713BigF z = (-cerfc z) * (2 - cerfc z) := by
  rw [erfc713BigF, cerfc]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F 0 = −1`. -/
theorem erfc713_bigF_zero : erfc713BigF 0 = -1 := by
  rw [erfc713BigF, cerf_zero]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Evenness.**  `F(−z) = F z` (because `cerf` is odd). -/
theorem erfc713_bigF_even (z : ℂ) : erfc713BigF (-z) = erfc713BigF z := by
  rw [erfc713BigF, erfc713BigF, cerf_neg]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Conjugation equivariance.**  `F(z̄) = conj (F z)`. -/
theorem erfc713_bigF_conj (z : ℂ) : erfc713BigF (starRingEnd ℂ z) = starRingEnd ℂ (erfc713BigF z) := by
  rw [erfc713BigF, erfc713BigF, cerf_conj, map_sub, map_pow, map_one]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F` is entire. -/
theorem erfc713_differentiable_bigF : Differentiable ℂ erfc713BigF := by
  have : erfc713BigF = fun z => cerf z ^ 2 - 1 := rfl
  rw [this]
  exact (differentiable_cerf.pow 2).sub_const 1

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_analyticAt_bigF (z : ℂ) : AnalyticAt ℂ erfc713BigF z :=
  erfc713_differentiable_bigF.differentiableOn.analyticAt Filter.univ_mem

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F' = 2·cerf·cerf'`, in the explicit closed form `2·cerf z·(2/√π)e^{−z²}`. -/
theorem erfc713_hasDerivAt_bigF (z : ℂ) :
    HasDerivAt erfc713BigF (2 * cerf z * ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2))) z := by
  have h := ((hasDerivAt_cerf z).pow 2).sub_const 1
  have hbigF : erfc713BigF = fun w : ℂ => cerf w ^ 2 - 1 := rfl
  rw [hbigF]
  convert h using 1
  push_cast
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_deriv_bigF (z : ℂ) :
    deriv erfc713BigF z = 2 * cerf z * ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2)) :=
  (erfc713_hasDerivAt_bigF z).deriv

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **`F`'s zeros are simple.**  At a zero `cerf z = ±1 ≠ 0` and `cerf' z ≠ 0`, so
`F' z = 2·cerf z·cerf' z ≠ 0`. -/
theorem erfc713_deriv_bigF_ne_zero_of_zero {z : ℂ} (hz : erfc713BigF z = 0) : deriv erfc713BigF z ≠ 0 := by
  have hcerf : cerf z ≠ 0 := by
    intro h
    rw [erfc713BigF, h] at hz
    norm_num at hz
  have hd : (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2) ≠ 0 := by
    have := deriv_cerf_ne_zero z
    rwa [(hasDerivAt_cerf z).deriv] at this
  rw [erfc713_deriv_bigF]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hcerf) hd

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **The zero set of `F`.**  `F z = 0 ↔ cerfc z = 0 ∨ cerfc (−z) = 0`.
(`cerf z = 1` is `cerfc z = 0`; `cerf z = −1` is `cerfc (−z) = 1 + cerf z = 0`.) -/
theorem erfc713_bigF_zero_iff {z : ℂ} : erfc713BigF z = 0 ↔ cerfc z = 0 ∨ cerfc (-z) = 0 := by
  rw [erfc713_bigF_eq_cerfc, mul_eq_zero, cerfc_neg, neg_eq_zero]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_analyticOrder_bigF_ne_top (z : ℂ) : analyticOrderAt erfc713BigF z ≠ ⊤ := by
  by_cases hz : erfc713BigF z = 0
  · rw [(erfc713_analyticAt_bigF z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
      (erfc713_deriv_bigF_ne_zero_of_zero hz)]
    exact ENat.one_ne_top
  · rw [(erfc713_analyticAt_bigF z).analyticOrderAt_eq_zero.mpr hz]
    exact ENat.zero_ne_top

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- `erf x < 1` for every real `x` (strictly monotone, limit `1`). -/
theorem erf_lt_one (x : ℝ) : FLMF.Error.erf x < 1 := by
  have h1 : FLMF.Error.erf x < FLMF.Error.erf (x + 1) := strictMono_erf (by linarith)
  exact lt_of_lt_of_le h1 (FLMF.Error.erf_le_one _)

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- `−1 < erf x` for every real `x`. -/
theorem neg_one_lt_erf (x : ℝ) : -1 < FLMF.Error.erf x := by
  have h : FLMF.Error.erf (-x) < 1 := erf_lt_one (-x)
  have hodd : FLMF.Error.erf (-x) = -FLMF.Error.erf x := by
    have := cerf_neg ((x : ℝ) : ℂ)
    rw [cerf_ofReal, ← Complex.ofReal_neg, cerf_ofReal] at this
    exact_mod_cast this
  rw [hodd] at h
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Real axis.**  `F x = erf(x)² − 1 < 0` for every real `x` (in particular at
`x = 0`, where `F 0 = −1`). -/
theorem erfc713_bigF_ofReal_neg (x : ℝ) : (erfc713BigF (x : ℂ)).re < 0 ∧ (erfc713BigF (x : ℂ)).im = 0 := by
  have hE : erfc713BigF (x : ℂ) = ((FLMF.Error.erf x ^ 2 - 1 : ℝ) : ℂ) := by
    rw [erfc713BigF, cerf_ofReal]; push_cast; ring
  have hlt : FLMF.Error.erf x ^ 2 - 1 < 0 := by
    have h1 := erf_lt_one x
    have h2 := neg_one_lt_erf x
    nlinarith
  rw [hE]
  refine ⟨?_, ?_⟩
  · rw [Complex.ofReal_re]; exact hlt
  · rw [Complex.ofReal_im]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_bigF_ne_zero_ofReal (x : ℝ) : erfc713BigF (x : ℂ) ≠ 0 := by
  intro h
  have := (erfc713_bigF_ofReal_neg x).1
  rw [h] at this
  simp at this

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- `cerf` is purely imaginary on the imaginary axis. -/
theorem cerf_imAxis_re (y : ℝ) : (cerf ((y : ℂ) * I)).re = 0 := by
  rw [cerf_imAxis]
  simp [Complex.ext_iff, Complex.div_re, Complex.mul_re, Complex.mul_im]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Imaginary axis.**  `cerf (iy)` is purely imaginary, so `cerf(iy)² ≤ 0` is real
and `Re F(iy) ≤ −1 < 0`. -/
theorem erfc713_bigF_imAxis_re_le (y : ℝ) : (erfc713BigF ((y : ℂ) * I)).re ≤ -1 := by
  set a : ℝ := (cerf ((y : ℂ) * I)).im with ha
  have hc : cerf ((y : ℂ) * I) = (a : ℂ) * I := by
    apply Complex.ext
    · simp [ha, cerf_imAxis_re y]
    · simp [ha]
  have hF : erfc713BigF ((y : ℂ) * I) = ((-(a ^ 2) - 1 : ℝ) : ℂ) := by
    rw [erfc713BigF, hc]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hF, Complex.ofReal_re]
  nlinarith [sq_nonneg a]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_bigF_ne_zero_imAxis (y : ℝ) : erfc713BigF ((y : ℂ) * I) ≠ 0 := by
  intro h
  have := erfc713_bigF_imAxis_re_le y
  rw [h] at this
  simp at this
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Axis-freeness (deliverable 2).**  `F` has no zero on either coordinate axis
(origin included). -/
theorem erfc713_bigF_ne_zero_on_axis {z : ℂ} (hax : z.re = 0 ∨ z.im = 0) : erfc713BigF z ≠ 0 := by
  rcases hax with hre0 | him0
  · have hz : ((z.im : ℝ) : ℂ) * I = z := by
      apply Complex.ext <;> simp [hre0]
    rw [← hz]
    exact erfc713_bigF_ne_zero_imAxis z.im
  · have hz : ((z.re : ℝ) : ℂ) = z := by
      apply Complex.ext <;> simp [him0]
    rw [← hz]
    exact erfc713_bigF_ne_zero_ofReal z.re

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The Cauchy kernel's denominator is nonvanishing above the real axis. -/
theorem erfc713_ofReal_sub_ne_zero {z : ℂ} (hz : 0 < z.im) (t : ℝ) : (t : ℂ) - z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.sub_im, Complex.ofReal_im] at him
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The Cauchy kernel `t ↦ e^{−t²}/(t − z)` is integrable on `ℝ` for `Im z > 0`
(dominated by `e^{−t²}/Im z`). -/
theorem erfc713_integrable_cauchyKernel {z : ℂ} (hz : 0 < z.im) :
    MeasureTheory.Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)) := by
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => erfc713_ofReal_sub_ne_zero hz t)
  have hdom : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-t ^ 2) / z.im) := by
    simpa using (integrable_exp_neg_mul_sq one_pos).div_const z.im
  refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => ?_))
  have hE : Complex.exp (-(t : ℂ) ^ 2) = ((Real.exp (-t ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; norm_cast
  have hlow : z.im ≤ ‖(t : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((t : ℂ) - z)
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact (le_abs_self _).trans h
  rw [norm_div, hE, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  gcongr

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The exact imaginary part of the Cauchy kernel. -/
theorem erfc713_cauchyKernel_im (z : ℂ) (t : ℝ) :
    (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)).im
      = Real.exp (-t ^ 2) * z.im / Complex.normSq ((t : ℂ) - z) := by
  have hE : Complex.exp (-(t : ℂ) ^ 2) = ((Real.exp (-t ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; norm_cast
  rw [hE, Complex.div_im]
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.sub_im, zero_sub, zero_mul,
    zero_div]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Positivity of the Cauchy kernel's imaginary part** — the whole content of the
Herglotz argument. -/
theorem erfc713_cauchyKernel_im_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    0 < (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)).im := by
  rw [erfc713_cauchyKernel_im]
  have hns : 0 < Complex.normSq ((t : ℂ) - z) :=
    Complex.normSq_pos.mpr (erfc713_ofReal_sub_ne_zero hz t)
  positivity

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- **The Faddeeva function has positive real part on the open upper half-plane.**
`Re w(z) = (1/π)·Im ∫_ℝ e^{−t²}/(t − z) dt > 0` by DLMF 7.7.2 and the pointwise
positivity of the kernel's imaginary part. -/
theorem faddeeva_re_pos {z : ℂ} (hz : 0 < z.im) : 0 < (faddeeva z).re := by
  have hint := erfc713_integrable_cauchyKernel hz
  have hJim : 0 < (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)).im := by
    have hcomm := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at hcomm
    rw [← hcomm, MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun t => (erfc713_cauchyKernel_im_pos hz t).le) hint.im]
    have hsupp : (Function.support fun t : ℝ =>
        (Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z)).im) = Set.univ :=
      Set.eq_univ_of_forall (fun t => Function.mem_support.mpr (erfc713_cauchyKernel_im_pos hz t).ne')
    rw [hsupp, Real.volume_univ]
    exact ENNReal.zero_lt_top
  have hπc : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hK : (1 : ℂ) / ((Real.pi : ℂ) * I) = ((1 / Real.pi : ℝ) : ℂ) * (-I) := by
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp
    linear_combination Complex.I_sq
  rw [faddeeva_eq_cauchyIntegral_real hz, hK]
  set J : ℂ := ∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) / ((t : ℂ) - z) with hJdef
  have hrw : ((1 / Real.pi : ℝ) : ℂ) * (-I) * J = ((1 / Real.pi : ℝ) : ℂ) * -(J * I) := by
    ring
  rw [hrw, Complex.re_ofReal_mul, Complex.neg_re, Complex.mul_I_re, neg_neg]
  exact mul_pos (by positivity) hJim

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- **`cerfc` has no zero in the OPEN right half-plane** (no restriction on `‖w‖`).
`faddeeva (i w) = e^{w²}·cerfc w` and `Im (i w) = Re w > 0`, so `faddeeva (i w)` has
strictly positive real part, hence is nonzero. -/
theorem cerfc_ne_zero_of_re_pos {w : ℂ} (hre : 0 < w.re) : cerfc w ≠ 0 := by
  have hz : 0 < (I * w).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    exact hre
  have hpos := faddeeva_re_pos hz
  have h1 : -(I * w) ^ 2 = w ^ 2 := by linear_combination (-(w ^ 2)) * Complex.I_sq
  have h2 : -(Complex.I * (I * w)) = w := by linear_combination (-w) * Complex.I_sq
  have hval : faddeeva (I * w) = Complex.exp (w ^ 2) * cerfc w := by
    simp only [faddeeva]
    rw [h1, h2]
  intro h0
  rw [hval, h0, mul_zero] at hpos
  simp at hpos

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- **`cerfc` has no zero in the closed right half-plane** — the analytic input that
identifies the second-quadrant zero set of `F` with that of `cerfc`.

The open half-plane is `cerfc_ne_zero_of_re_pos` (the Herglotz property of the Faddeeva
function, DLMF 7.7.2); the boundary line `Re w = 0` is elementary, since `cerf` is purely
imaginary there (`cerf_imAxis_re`), so `Re cerfc (iy) = 1 ≠ 0`.  No restriction on `‖w‖`
is needed anywhere — in particular the Poincaré remainder bound, useless on `‖w‖ ≤ 2`, is
not used at all. -/
theorem cerfc_ne_zero_of_re_nonneg {w : ℂ} (hre : 0 ≤ w.re) : cerfc w ≠ 0 := by
  rcases lt_or_eq_of_le hre with hpos | hzero
  · exact cerfc_ne_zero_of_re_pos hpos
  · have hre0 : w.re = 0 := hzero.symm
    have hw : ((w.im : ℝ) : ℂ) * I = w := by
      apply Complex.ext <;> simp [hre0]
    intro h
    have hcr : (cerf w).re = 0 := by
      rw [← hw]; exact cerf_imAxis_re w.im
    have h1 : (cerfc w).re = 1 := by
      rw [cerfc, Complex.sub_re, Complex.one_re, hcr]
      ring
    rw [h] at h1
    simp at h1

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
theorem cerfc_conj (z : ℂ) : cerfc (starRingEnd ℂ z) = starRingEnd ℂ (cerfc z) := by
  rw [cerfc, cerfc, cerf_conj, map_sub, map_one]

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- **S7, second-quadrant case.**  No second-quadrant zero of `cerfc` sits exactly on
the counting circle `‖w‖ = erf713Rad`: `erfc713_zero_has_index` forces an index `n ≥ 3500`,
whence `‖w‖² ≥ 2λ₃₅₀₀² − 1 > 21987 = erf713Rad²`. -/
theorem erfc713_cerfc_Q2_ne_zero_on_circle {w : ℂ} (hre : w.re < 0) (him : 0 < w.im)
    (hnorm : ‖w‖ = erf713Rad) : cerfc w ≠ 0 := by
  intro hzero
  have hnormsq : ‖w‖ ^ 2 = 21987 := by rw [hnorm]; exact erf713Rad_sq
  obtain ⟨n, hn3500, hr, hi⟩ := erfc713_zero_has_index hzero hre him hnormsq.ge
  have hn3400 : 3400 ≤ n := by omega
  obtain ⟨hA, -, -⟩ := erfc713_approx_norm_sq hn3400 hr hi
  obtain ⟨hA1, -⟩ := abs_le.mp hA
  have hlam := erfc713_lambda_sq (n := n) (by omega)
  have hpi := Real.pi_gt_d6
  have hnR : (3500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3500
  have hlow : (3499.875 : ℝ) * 3.141592 < erfcZeroLambda n ^ 2 := by
    rw [hlam]
    calc (3499.875 : ℝ) * 3.141592 < 3499.875 * Real.pi := by
          apply mul_lt_mul_of_pos_left hpi (by norm_num)
      _ ≤ ((n : ℝ) - 1 / 8) * Real.pi := by
          apply mul_le_mul_of_nonneg_right (by linarith) Real.pi_pos.le
  nlinarith [hnormsq, hA1, hlow]

-- no-dlmf: elementary symmetry/nonvanishing fact for `cerfc`; proof infrastructure for the §7.13 zero count
/-- **S7 for `cerfc`.**  No zero of `cerfc` sits on the counting circle. -/
theorem cerfc_ne_zero_on_circle {z : ℂ} (hz : ‖z‖ = erf713Rad) : cerfc z ≠ 0 := by
  by_cases hre : 0 ≤ z.re
  · exact cerfc_ne_zero_of_re_nonneg hre
  · push_neg at hre
    rcases lt_trichotomy z.im 0 with him | him | him
    · -- lower left: conjugate into Q2
      intro hzero
      refine erfc713_cerfc_Q2_ne_zero_on_circle (w := starRingEnd ℂ z)
        (by rw [Complex.conj_re]; exact hre)
        (by rw [Complex.conj_im]; linarith)
        (by rw [Complex.norm_conj]; exact hz) ?_
      rw [cerfc_conj, hzero, map_zero]
    · -- negative real axis: `cerf x = erf x < 1`
      have hz' : ((z.re : ℝ) : ℂ) = z := by
        apply Complex.ext <;> simp [him]
      intro hzero
      rw [← hz', cerfc, cerf_ofReal, sub_eq_zero] at hzero
      have : FLMF.Error.erf z.re = 1 := by exact_mod_cast hzero.symm
      linarith [erf_lt_one z.re]
    · exact erfc713_cerfc_Q2_ne_zero_on_circle hre him hz

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Deliverable 6.**  `F` has no zero on the counting circle `‖z‖ = erf713Rad`
(both `cerfc z` and `cerfc (−z)` are nonzero there). -/
theorem erfc713_bigF_ne_zero_on_circle {z : ℂ} (hz : ‖z‖ = erf713Rad) : erfc713BigF z ≠ 0 := by
  intro h
  rcases erfc713_bigF_zero_iff.mp h with h1 | h1
  · exact cerfc_ne_zero_on_circle hz h1
  · exact cerfc_ne_zero_on_circle (z := -z) (by rw [norm_neg]; exact hz) h1

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- In the open second quadrant the zeros of `F` are exactly the zeros of `cerfc`:
`F z = 0` allows `cerfc (−z) = 0`, but `−z` then lies in the open **fourth** quadrant,
where `cerfc` has no zero (`cerfc_ne_zero_of_re_nonneg`).

(The hypothesis `him : 0 < z.im` is *not* consumed by the proof — `Re z < 0` alone
suffices, since the whole closed right half-plane is zero-free.  It is kept because
this is the shape the production region needs.) -/
theorem erfc713_bigF_zero_Q2_iff {z : ℂ} (hre : z.re < 0) (him : 0 < z.im) :
    erfc713BigF z = 0 ↔ cerfc z = 0 := by
  constructor
  · intro h
    rcases erfc713_bigF_zero_iff.mp h with h1 | h1
    · exact h1
    · exact absurd h1 (cerfc_ne_zero_of_re_nonneg
        (by rw [Complex.neg_re]; linarith))
  · intro h
    exact erfc713_bigF_zero_iff.mpr (Or.inl h)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The second-quadrant zero sets of `F` and of `cerfc` below the cut coincide. -/
theorem erfc713_Q2_bigF_eq_Q2_cerfc :
    {w : ℂ | erfc713BigF w = 0 ∧ w.re < 0 ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}
      = {u : ℂ | cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧ ‖u‖ ^ 2 < 21987} := by
  ext w
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(erfc713_bigF_zero_Q2_iff h2 h3).mp h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(erfc713_bigF_zero_Q2_iff h2 h3).mpr h1, h2, h3, h4⟩

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Deliverable 3 — the Klein-orbit `Finset` assembly.**  The zero set of `F` on the
closed counting disc is finite, misses the circle and both axes, and is invariant
under the Klein group `{1, −1, conj, −conj}`; its multiplicity-weighted total is
therefore `4·N`, `N` the second-quadrant count below the cut — with **no** `+1`
origin term (`F 0 = −1 ≠ 0`), the one structural difference from the `erf` branch. -/
theorem erfc713_zeros_finset_exists :
    ∃ P : Finset ℂ,
      (∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) erf713Rad ∧ erfc713BigF z = 0) ∧
      (∀ p ∈ P, p ∈ ball (0 : ℂ) erf713Rad) ∧
      (∑ p ∈ P, (analyticOrderNatAt erfc713BigF p : ℂ))
        = 4 * (({u : ℂ | cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧ ‖u‖ ^ 2 < 21987}.ncard : ℕ) : ℂ) := by
  classical
  set Q2 : Set ℂ := {w : ℂ | erfc713BigF w = 0 ∧ w.re < 0 ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987} with hQ2def
  have hUconn : IsConnected (ball (0 : ℂ) (erf713Rad + 1)) :=
    ⟨Metric.nonempty_ball.mpr (by linarith [erf713Rad_pos]),
      (convex_ball (0 : ℂ) (erf713Rad + 1)).isPreconnected⟩
  have hx0 : (0 : ℂ) ∈ ball (0 : ℂ) (erf713Rad + 1) := by
    rw [mem_ball_zero_iff, norm_zero]
    linarith [erf713Rad_pos]
  have hfx : erfc713BigF (0 : ℂ) ≠ 0 := by rw [erfc713_bigF_zero]; norm_num
  have hK : IsCompact (closedBall (0 : ℂ) erf713Rad) := isCompact_closedBall 0 erf713Rad
  have hKU : closedBall (0 : ℂ) erf713Rad ⊆ ball (0 : ℂ) (erf713Rad + 1) :=
    Metric.closedBall_subset_ball (by linarith)
  have hZfin : (closedBall (0 : ℂ) erf713Rad ∩ erfc713BigF ⁻¹' {0}).Finite :=
    finite_zeros_on_compact (fun z _ => erfc713_analyticAt_bigF z) hUconn hx0 hfx hK hKU
  set P : Finset ℂ := hZfin.toFinset with hPdef
  have hPmem : ∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) erf713Rad ∧ erfc713BigF z = 0 := by
    intro z
    rw [hPdef, Set.Finite.mem_toFinset]
    simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hPball : ∀ p ∈ P, p ∈ ball (0 : ℂ) erf713Rad := by
    intro p hp
    obtain ⟨hpc, hpz⟩ := (hPmem p).mp hp
    have hle : ‖p‖ ≤ erf713Rad := mem_closedBall_zero_iff.mp hpc
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · exact absurd hpz (erfc713_bigF_ne_zero_on_circle heq)
  refine ⟨P, hPmem, hPball, ?_⟩
  have horder1 : ∀ p ∈ P, analyticOrderNatAt erfc713BigF p = 1 := by
    intro p hp
    have hFp : erfc713BigF p = 0 := ((hPmem p).mp hp).2
    have hord := (erfc713_analyticAt_bigF p).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hFp
      (erfc713_deriv_bigF_ne_zero_of_zero hFp)
    unfold analyticOrderNatAt
    rw [hord]
    rfl
  have hsum : (∑ p ∈ P, (analyticOrderNatAt erfc713BigF p : ℂ)) = (P.card : ℂ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [horder1 p hp])]
    simp
  rw [hsum]
  -- the Klein decomposition of the zero set: four disjoint images of `Q2`
  have hZeq : (closedBall (0 : ℂ) erf713Rad ∩ erfc713BigF ⁻¹' {0} : Set ℂ)
      = Q2 ∪ (fun w => -w) '' Q2 ∪ (fun w => starRingEnd ℂ w) '' Q2
          ∪ (fun w => -(starRingEnd ℂ w)) '' Q2 := by
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨hzc, hzz⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzz
      have hzRad : ‖z‖ ≤ erf713Rad := mem_closedBall_zero_iff.mp hzc
      rcases eq_or_lt_of_le hzRad with heq | hlt
      · exact absurd hzz (erfc713_bigF_ne_zero_on_circle heq)
      have hzsq : ‖z‖ ^ 2 < 21987 := by
        have h2 : ‖z‖ ^ 2 < erf713Rad ^ 2 := by nlinarith [hlt, norm_nonneg z]
        rwa [erf713Rad_sq] at h2
      have hre0 : z.re ≠ 0 := fun h => (erfc713_bigF_ne_zero_on_axis (Or.inl h)) hzz
      have him0 : z.im ≠ 0 := fun h => (erfc713_bigF_ne_zero_on_axis (Or.inr h)) hzz
      rcases lt_or_gt_of_ne hre0 with hreN | hreP <;>
        rcases lt_or_gt_of_ne him0 with himN | himP
      · -- re < 0, im < 0 : z = conj w with w := conj z ∈ Q2
        have hwQ2 : (starRingEnd ℂ z) ∈ Q2 := by
          refine ⟨by rw [erfc713_bigF_conj, hzz, map_zero], by rw [Complex.conj_re]; linarith,
            by rw [Complex.conj_im]; linarith, by rw [Complex.norm_conj]; exact hzsq⟩
        left; right
        exact ⟨starRingEnd ℂ z, hwQ2, starRingEnd_self_apply z⟩
      · -- re < 0, im > 0 : z ∈ Q2
        left; left; left
        exact ⟨hzz, hreN, himP, hzsq⟩
      · -- re > 0, im < 0 : z = -w with w := -z ∈ Q2
        have hwQ2 : (-z) ∈ Q2 := by
          refine ⟨by rw [erfc713_bigF_even]; exact hzz, by rw [Complex.neg_re]; linarith,
            by rw [Complex.neg_im]; linarith, by rwa [norm_neg]⟩
        left; left; right
        exact ⟨-z, hwQ2, by ring⟩
      · -- re > 0, im > 0 : z = -(conj w) with w := -(conj z) ∈ Q2
        have hwQ2 : (-(starRingEnd ℂ z)) ∈ Q2 := by
          refine ⟨by rw [erfc713_bigF_even, erfc713_bigF_conj, hzz, map_zero],
            by rw [Complex.neg_re, Complex.conj_re]; linarith,
            by rw [Complex.neg_im, Complex.conj_im]; linarith,
            by rw [norm_neg, Complex.norm_conj]; exact hzsq⟩
        right
        refine ⟨-(starRingEnd ℂ z), hwQ2, ?_⟩
        show -(starRingEnd ℂ (-(starRingEnd ℂ z))) = z
        rw [map_neg, starRingEnd_self_apply, neg_neg]
    · have hmem : ∀ w ∈ Q2, ‖w‖ < erf713Rad := by
        intro w hw
        obtain ⟨-, -, -, hzsq⟩ := hw
        have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
        nlinarith [norm_nonneg w, erf713Rad_pos]
      rintro z (((hzQ2 | ⟨w, hwQ2, rfl⟩) | ⟨w, hwQ2, rfl⟩) | ⟨w, hwQ2, rfl⟩)
      · exact ⟨mem_closedBall_zero_iff.mpr (hmem z hzQ2).le, hzQ2.1⟩
      · exact ⟨mem_closedBall_zero_iff.mpr (by rw [norm_neg]; exact (hmem w hwQ2).le),
          by show erfc713BigF (-w) = 0; rw [erfc713_bigF_even]; exact hwQ2.1⟩
      · exact ⟨mem_closedBall_zero_iff.mpr
          (by rw [Complex.norm_conj]; exact (hmem w hwQ2).le),
          by show erfc713BigF (starRingEnd ℂ w) = 0; rw [erfc713_bigF_conj, hwQ2.1, map_zero]⟩
      · exact ⟨mem_closedBall_zero_iff.mpr
          (by rw [norm_neg, Complex.norm_conj]; exact (hmem w hwQ2).le),
          by show erfc713BigF (-(starRingEnd ℂ w)) = 0
             rw [erfc713_bigF_even, erfc713_bigF_conj, hwQ2.1, map_zero]⟩
  -- sign data pinning each image to its own open quadrant
  have hsignQ2 : ∀ p ∈ Q2, p.re < 0 ∧ 0 < p.im := fun p hp => ⟨hp.2.1, hp.2.2.1⟩
  have hsignNeg : ∀ p ∈ (fun w => -w) '' Q2, 0 < p.re ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.neg_re]; linarith [(hsignQ2 w hw).1],
      by rw [Complex.neg_im]; linarith [(hsignQ2 w hw).2]⟩
  have hsignConj : ∀ p ∈ (fun w => starRingEnd ℂ w) '' Q2, p.re < 0 ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.conj_re]; exact (hsignQ2 w hw).1,
      by rw [Complex.conj_im]; linarith [(hsignQ2 w hw).2]⟩
  have hsignNegConj : ∀ p ∈ (fun w => -(starRingEnd ℂ w)) '' Q2, 0 < p.re ∧ 0 < p.im := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by rw [Complex.neg_re, Complex.conj_re]; linarith [(hsignQ2 w hw).1],
      by rw [Complex.neg_im, Complex.conj_im]; linarith [(hsignQ2 w hw).2]⟩
  have hQ2subZ : Q2 ⊆ closedBall (0 : ℂ) erf713Rad ∩ erfc713BigF ⁻¹' {0} := by
    intro w hw
    obtain ⟨hzz, -, -, hzsq⟩ := hw
    have h2 : ‖w‖ ^ 2 < erf713Rad ^ 2 := by rw [erf713Rad_sq]; exact hzsq
    have hwlt : ‖w‖ < erf713Rad := by nlinarith [norm_nonneg w, erf713Rad_pos]
    exact ⟨mem_closedBall_zero_iff.mpr hwlt.le, hzz⟩
  have hQ2fin : Q2.Finite := hZfin.subset hQ2subZ
  have hNegInj : Function.Injective (fun w : ℂ => -w) := neg_injective
  have hConjInj : Function.Injective (fun w : ℂ => starRingEnd ℂ w) :=
    Function.LeftInverse.injective (fun x => starRingEnd_self_apply x)
  have hNegConjInj : Function.Injective (fun w : ℂ => -(starRingEnd ℂ w)) :=
    neg_injective.comp hConjInj
  have hNegImgFin : ((fun w : ℂ => -w) '' Q2).Finite := hQ2fin.image _
  have hConjImgFin : ((fun w : ℂ => starRingEnd ℂ w) '' Q2).Finite := hQ2fin.image _
  have hNegConjImgFin : ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q2).Finite := hQ2fin.image _
  have hNegImgCard : ((fun w : ℂ => -w) '' Q2).ncard = Q2.ncard :=
    Set.ncard_image_of_injective Q2 hNegInj
  have hConjImgCard : ((fun w : ℂ => starRingEnd ℂ w) '' Q2).ncard = Q2.ncard :=
    Set.ncard_image_of_injective Q2 hConjInj
  have hNegConjImgCard : ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q2).ncard = Q2.ncard :=
    Set.ncard_image_of_injective Q2 hNegConjInj
  have hd1 : Disjoint Q2 ((fun w : ℂ => -w) '' Q2) := by
    rw [Set.disjoint_left]; rintro p hp1 hp2
    linarith [(hsignQ2 p hp1).1, (hsignNeg p hp2).1]
  have hX1fin : (Q2 ∪ (fun w : ℂ => -w) '' Q2 : Set ℂ).Finite := hQ2fin.union hNegImgFin
  have hX1card : (Q2 ∪ (fun w : ℂ => -w) '' Q2 : Set ℂ).ncard = 2 * Q2.ncard := by
    rw [Set.ncard_union_eq hd1 hQ2fin hNegImgFin, hNegImgCard]; ring
  have hd2 : Disjoint (Q2 ∪ (fun w : ℂ => -w) '' Q2 : Set ℂ)
      ((fun w : ℂ => starRingEnd ℂ w) '' Q2) := by
    rw [Set.disjoint_left]
    rintro p (hp1 | hp2) hpC
    · linarith [(hsignQ2 p hp1).2, (hsignConj p hpC).2]
    · linarith [(hsignNeg p hp2).1, (hsignConj p hpC).1]
  have hX2fin : ((Q2 ∪ (fun w : ℂ => -w) '' Q2) ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q2
      : Set ℂ).Finite := hX1fin.union hConjImgFin
  have hX2card : ((Q2 ∪ (fun w : ℂ => -w) '' Q2) ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q2
      : Set ℂ).ncard = 3 * Q2.ncard := by
    rw [Set.ncard_union_eq hd2 hX1fin hConjImgFin, hX1card, hConjImgCard]; ring
  have hd3 : Disjoint (((Q2 ∪ (fun w : ℂ => -w) '' Q2)
      ∪ (fun w : ℂ => starRingEnd ℂ w) '' Q2) : Set ℂ)
      ((fun w : ℂ => -(starRingEnd ℂ w)) '' Q2) := by
    rw [Set.disjoint_left]
    rintro p ((hp1 | hp2) | hpC) hpNC
    · linarith [(hsignQ2 p hp1).1, (hsignNegConj p hpNC).1]
    · linarith [(hsignNeg p hp2).2, (hsignNegConj p hpNC).2]
    · linarith [(hsignConj p hpC).1, (hsignNegConj p hpNC).1]
  have hcardEq : (closedBall (0 : ℂ) erf713Rad ∩ erfc713BigF ⁻¹' {0} : Set ℂ).ncard = 4 * Q2.ncard := by
    rw [hZeq, Set.ncard_union_eq hd3 hX2fin hNegConjImgFin, hX2card, hNegConjImgCard]
    ring
  have hPcard : P.card = (closedBall (0 : ℂ) erf713Rad ∩ erfc713BigF ⁻¹' {0}).ncard := by
    rw [hPdef]; exact (Set.ncard_eq_toFinset_card _ hZfin).symm
  rw [hPcard, hcardEq, hQ2def, erfc713_Q2_bigF_eq_Q2_cerfc]
  push_cast
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F'` is odd. -/
theorem erfc713_deriv_bigF_neg (z : ℂ) : deriv erfc713BigF (-z) = -deriv erfc713BigF z := by
  rw [erfc713_deriv_bigF, erfc713_deriv_bigF, cerf_neg]
  ring_nf

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `F'` is conjugation-equivariant. -/
theorem erfc713_deriv_bigF_conj (z : ℂ) :
    deriv erfc713BigF (starRingEnd ℂ z) = starRingEnd ℂ (deriv erfc713BigF z) := by
  rw [erfc713_deriv_bigF, erfc713_deriv_bigF, cerf_conj]
  rw [map_mul, map_mul, map_mul, map_ofNat]
  congr 2
  · rw [show ((2:ℂ) / (Real.sqrt Real.pi : ℂ)) = ((2 / Real.sqrt Real.pi : ℝ) : ℂ) by
      push_cast; ring]
    exact (Complex.conj_ofReal _).symm
  · rw [← Complex.exp_conj, map_neg, map_pow]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_deriv_bigF : Continuous (deriv erfc713BigF) := by
  have h : deriv erfc713BigF
      = fun z => 2 * cerf z * ((2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2)) :=
    funext erfc713_deriv_bigF
  rw [h]
  exact (continuous_const.mul differentiable_cerf.continuous).mul (by fun_prop)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Deliverable 4 (W1 for `F`).**  `∮ F'/F = 4i·Im J`, `J` the quarter-arc integral.

`h(θ) := (F'/F)(arcPoint erf713Rad θ)·(i·arcPoint erf713Rad θ)` satisfies `h(θ+π) = h(θ)` (from `F` even, `F'`
odd) and `h(−θ) = −conj (h θ)` (from conjugation equivariance), so
`∮ = 2∫₀^π h = 2(J − conj J) = 4i·Im J`. -/
theorem erfc713_circle_eq_four_I_arc_im :
    (∮ z in C((0:ℂ), erf713Rad), deriv erfc713BigF z / erfc713BigF z)
      = 4 * I * (((arcLogDerivIntegral erfc713BigF erf713Rad 0 (Real.pi / 2)).im : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun θ => deriv erfc713BigF (arcPoint erf713Rad θ) / erfc713BigF (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) with hhdef
  have hne : ∀ θ : ℝ, erfc713BigF (arcPoint erf713Rad θ) ≠ 0 := fun θ => erfc713_bigF_ne_zero_on_circle ((norm_arcPoint erf713Rad_pos.le) θ)
  have hstep1 : (∮ z in C((0:ℂ), erf713Rad), deriv erfc713BigF z / erfc713BigF z)
      = arcLogDerivIntegral erfc713BigF erf713Rad 0 (2 * Real.pi) := by
    unfold circleIntegral arcLogDerivIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, ← arcPoint_eq_circleMap, smul_eq_mul]
    ring
  rw [hstep1]
  show (∫ θ in (0:ℝ)..(2 * Real.pi), h θ)
      = 4 * I * (((∫ θ in (0:ℝ)..(Real.pi / 2), h θ).im : ℝ) : ℂ)
  have hcont_h : Continuous h := by
    have h1 : Continuous (fun θ => deriv erfc713BigF (arcPoint erf713Rad θ)) :=
      erfc713_continuous_deriv_bigF.comp (continuous_arcPoint erf713Rad)
    have h2 : Continuous (fun θ => erfc713BigF (arcPoint erf713Rad θ)) :=
      erfc713_differentiable_bigF.continuous.comp (continuous_arcPoint erf713Rad)
    have h3 : Continuous (fun θ => I * arcPoint erf713Rad θ) := continuous_const.mul (continuous_arcPoint erf713Rad)
    exact (h1.div h2 hne).mul h3
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hcont_h.intervalIntegrable a b
  have hper : ∀ θ : ℝ, h (θ + Real.pi) = h θ := by
    intro θ
    have hnz := hne θ
    simp only [hhdef]
    rw [(arcPoint_add_pi erf713Rad), erfc713_deriv_bigF_neg, erfc713_bigF_even]
    field_simp
  have hconjrel : ∀ θ : ℝ, h (-θ) = - starRingEnd ℂ (h θ) := by
    intro θ
    simp only [hhdef]
    rw [(arcPoint_neg erf713Rad), erfc713_deriv_bigF_conj, erfc713_bigF_conj, map_mul, map_mul, map_div₀,
      show starRingEnd ℂ I = -I from Complex.conj_I]
    ring
  have hsplit1 : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ)
      = (∫ θ in (0:ℝ)..Real.pi, h θ) + ∫ θ in Real.pi..(2 * Real.pi), h θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 Real.pi)
      (hint Real.pi (2 * Real.pi))).symm
  have hshift : (∫ θ in Real.pi..(2 * Real.pi), h θ) = ∫ θ in (0:ℝ)..Real.pi, h θ := by
    have hc := intervalIntegral.integral_comp_add_right h Real.pi (a := (0:ℝ)) (b := Real.pi)
    rw [show (0:ℝ) + Real.pi = Real.pi by ring,
      show Real.pi + Real.pi = 2 * Real.pi by ring] at hc
    rw [← hc]
    exact intervalIntegral.integral_congr (fun x _ => hper x)
  have heq2π : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ) = 2 * ∫ θ in (0:ℝ)..Real.pi, h θ := by
    rw [hsplit1, hshift]; ring
  set J : ℂ := ∫ θ in (0:ℝ)..(Real.pi / 2), h θ with hJdef
  have hsplitπ : (∫ θ in (0:ℝ)..Real.pi, h θ) = J + ∫ θ in (Real.pi / 2)..Real.pi, h θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 (Real.pi / 2))
      (hint (Real.pi / 2) Real.pi)).symm
  have hstep : ∀ x : ℝ, h (Real.pi - x) = - starRingEnd ℂ (h x) := by
    intro x
    rw [show Real.pi - x = -x + Real.pi by ring, hper (-x)]
    exact hconjrel x
  have hhalf : (∫ θ in (Real.pi / 2)..Real.pi, h θ) = - starRingEnd ℂ J := by
    have hsub := intervalIntegral.integral_comp_sub_left h (a := (0:ℝ)) (b := Real.pi / 2)
      (d := Real.pi)
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
      show Real.pi - (0:ℝ) = Real.pi by ring] at hsub
    rw [← hsub, intervalIntegral.integral_congr (fun x _ => hstep x),
      intervalIntegral.integral_neg, intervalIntegral_conj (hint 0 (Real.pi / 2)), hJdef]
  have hπsum : (∫ θ in (0:ℝ)..Real.pi, h θ) = J - starRingEnd ℂ J := by
    rw [hsplitπ, hhalf]; ring
  have hfinal : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ) = 2 * (J - starRingEnd ℂ J) := by
    rw [heq2π, hπsum]
  rw [hfinal]
  have hJIm : J - starRingEnd ℂ J = 2 * I * (((J.im : ℝ) : ℂ)) := by
    rw [Complex.sub_conj]
    push_cast
    ring
  rw [hJIm]
  ring

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- The level-`2` model factor `2 − u`. -/
def erfc713ModelM2 (z : ℂ) : ℂ := 2 - erf713ModelU z

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- The full model for `F` on the arc: `F_M = (−u)·(2 − u)`. -/
def erfc713ModelFM (z : ℂ) : ℂ := (-erf713ModelU z) * erfc713ModelM2 z

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **A1 at level `a = 2`.**  `|2 − u| ≥ 1` on the closed quarter arc.

Two branches, exactly as in the level-`1` (erf) case with `L` replaced by
`L₂ = log(2√π R)`:

* if `|log (|u|/2)| = |R² cos 2θ + L₂| ≥ log 2` then `|u| ≤ 1` or `|u| ≥ 4`, so
  `|2 − u| ≥ | 2 − |u| | ≥ 1`;
* otherwise `R²|cos 2θ| < L₂ + log 2 < 7.4`, hence (with `sin 2θ ≥ 0` on the quarter
  arc) `R² sin 2θ ≥ R²(1 − cos²2θ) ≥ 21987 − 55/21987 > 21986.997`, so
  `Ψ(θ) = R² sin 2θ + θ ∈ [21986.997, 21987 + π/2] ⊂ [2π·3499 + π/2, 2π·3499 + 3π/2]`;
  therefore `cos Ψ(θ) ≤ 0`, `Re u ≤ 0`, and `|2 − u| ≥ 2 − Re u ≥ 2`. -/
theorem erfc713_modelM2_norm_ge {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    (1 : ℝ) ≤ ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hLpos, hLlt⟩ := erfc713_bigL2_bounds
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsr : 0 < Real.sqrt Real.pi * erf713Rad := erf713_sqrtPi_Rad_pos
  have hRsq : erf713Rad ^ 2 = 21987 := erf713Rad_sq
  set c : ℝ := Real.cos (2 * θ) with hc
  set s : ℝ := Real.sin (2 * θ) with hs
  set t : ℝ := Real.exp (-(erf713Rad ^ 2 * c)) / (Real.sqrt Real.pi * erf713Rad) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos (Real.exp_pos _) hsr
  have hnorm : ‖erf713ModelU (arcPoint erf713Rad θ)‖ = t := erf713_modelU_arcPt_norm θ
  have hre : (erf713ModelU (arcPoint erf713Rad θ)).re = t * Real.cos (erf713Rad ^ 2 * s + θ) := erf713_modelU_arcPt_re θ
  by_cases hcase : Real.log 2 ≤ |erf713Rad ^ 2 * c + erfc713BigL2|
  · -- modulus branch: `|u| ≤ 1` or `|u| ≥ 4`
    have hlogt : Real.log t = -(erf713Rad ^ 2 * c + erfc713BigL2) + Real.log 2 := by
      rw [htdef, Real.log_div (Real.exp_ne_zero _) hsr.ne', Real.log_exp, erfc713BigL2,
        Real.log_mul (by norm_num) hsr.ne']
      ring
    have hsplit : t ≤ 1 ∨ 4 ≤ t := by
      rcases le_abs.mp hcase with h | h
      · left
        have hle : Real.log t ≤ Real.log 1 := by
          rw [Real.log_one, hlogt]; linarith
        exact (Real.log_le_log_iff htpos (by norm_num)).mp hle
      · right
        have hlog4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        have hle : Real.log 4 ≤ Real.log t := by rw [hlogt, hlog4]; linarith
        exact (Real.log_le_log_iff (by norm_num) htpos).mp hle
    have hkey : (1 : ℝ) ≤ |2 - t| := by
      rcases hsplit with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    calc (1 : ℝ) ≤ |2 - t| := hkey
      _ = |‖(2 : ℂ)‖ - ‖erf713ModelU (arcPoint erf713Rad θ)‖| := by
          rw [hnorm, show ‖(2 : ℂ)‖ = 2 by norm_num]
      _ ≤ ‖(2 : ℂ) - erf713ModelU (arcPoint erf713Rad θ)‖ := abs_norm_sub_norm_le _ _
      _ = ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := by rw [erfc713ModelM2]
  · -- phase branch: `Ψ(θ)` sits in the left half-period, so `Re u ≤ 0`
    push_neg at hcase
    have hlog2 : Real.log 2 < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hb : |erf713Rad ^ 2 * c + erfc713BigL2| < 0.694 := lt_trans hcase hlog2
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
    have hsq2 : (erf713Rad ^ 2 * c) ^ 2 < 55 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < erf713Rad ^ 2 * c + 7.4)
        (by linarith : (0:ℝ) < 0.7 - erf713Rad ^ 2 * c)]
    have hsnn : 0 ≤ s := by
      rw [hs]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hpy : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq _
    have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
    have hslow : 1 - c ^ 2 ≤ s := by nlinarith
    have hRs : (21986.997 : ℝ) ≤ erf713Rad ^ 2 * s := by
      have h1 : erf713Rad ^ 2 * (1 - c ^ 2) ≤ erf713Rad ^ 2 * s := by
        apply mul_le_mul_of_nonneg_left hslow
        rw [hRsq]; norm_num
      have h2 : erf713Rad ^ 2 * (1 - c ^ 2) = 21987 - (erf713Rad ^ 2 * c) ^ 2 / 21987 := by
        rw [hRsq]; ring
      rw [h2] at h1
      linarith
    have hΨhi : erf713Rad ^ 2 * s ≤ 21987 := by rw [hRsq]; linarith
    have hcosnp : Real.cos (erf713Rad ^ 2 * s + θ) ≤ 0 := by
      rw [← Real.cos_sub_int_mul_two_pi _ (3499 : ℤ)]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · push_cast; linarith
      · push_cast; linarith
    have hrenp : (erf713ModelU (arcPoint erf713Rad θ)).re ≤ 0 := by
      rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos htpos.le hcosnp
    have hMre : (erfc713ModelM2 (arcPoint erf713Rad θ)).re = 2 - (erf713ModelU (arcPoint erf713Rad θ)).re := by
      rw [erfc713ModelM2]; simp
    have h1 : |(erfc713ModelM2 (arcPoint erf713Rad θ)).re| ≤ ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := Complex.abs_re_le_norm _
    rw [hMre, abs_of_nonneg (by linarith)] at h1
    linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_modelM2_ne_zero {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) : erfc713ModelM2 (arcPoint erf713Rad θ) ≠ 0 := by
  intro h
  have := erfc713_modelM2_norm_ge hθ
  rw [h, norm_zero] at this
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The pulled-back logarithmic derivative of `u` along the arc, in closed form:
`(u'/u)(z)·(iz) = −2i R² e^{2iθ} − i`. -/
theorem erfc713_arcIntegrand_modelU (θ : ℝ) :
    deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
      = -2 * I * ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) - I := by
  have hz : arcPoint erf713Rad θ ≠ 0 := (arcPoint_ne_zero erf713Rad_pos.ne') θ
  have hune : erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := erf713_modelU_arcPt_ne_zero θ
  have hexp2 : Complex.exp ((θ : ℂ) * I) ^ 2 = Complex.exp (2 * (θ : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have hz2 : (arcPoint erf713Rad θ) ^ 2 = ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) := by
    rw [show arcPoint erf713Rad θ = (erf713Rad : ℂ) * Complex.exp ((θ : ℂ) * I) from rfl, mul_pow, hexp2]
    push_cast
    rfl
  rw [(erf713_hasDerivAt_modelU hz).deriv, mul_div_cancel_left₀ _ hune]
  have hexpand : (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹) * (I * arcPoint erf713Rad θ)
      = -2 * I * (arcPoint erf713Rad θ) ^ 2 - I := by
    field_simp
  rw [hexpand, hz2]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `(−u)' = −u'` at every arc point. -/
theorem erfc713_deriv_negU (θ : ℝ) :
    deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) = -deriv erf713ModelU (arcPoint erf713Rad θ) := by
  have h1 : HasDerivAt (fun z => -erf713ModelU z)
      (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))) (arcPoint erf713Rad θ) :=
    (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).neg
  rw [h1.deriv, (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **The branch-free half of the erfc model (PROVEN).**  The `(−u)` factor of `F_M`
contributes `Im = −π/2` to the quarter-arc integral:
`∫₀^{π/2} (−u)'/(−u)·iz dθ = Λ(π/2) − Λ(0)`, whose imaginary part is
`(−R² sin π − π/2) − (−R² sin 0 − 0) = −π/2`.  No branch of the logarithm is
involved, so the ≈3500 windings of `u` cost nothing. -/
theorem erfc713_modelArc_im_negU :
    (arcLogDerivIntegral (fun z => -erf713ModelU z) erf713Rad 0 (Real.pi / 2)).im = -(Real.pi / 2) := by
  have hderiv : ∀ θ : ℝ, deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) / (-erf713ModelU (arcPoint erf713Rad θ))
      * (I * arcPoint erf713Rad θ) = deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) := by
    intro θ
    rw [erfc713_deriv_negU θ, neg_div_neg_eq]
  have hcont : Continuous (fun θ : ℝ =>
      deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) := by
    have h : (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
        = fun θ : ℝ => -2 * I * ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) - I :=
      funext erfc713_arcIntegrand_modelU
    rw [h]
    fun_prop
  have heval : arcLogDerivIntegral (fun z => -erf713ModelU z) erf713Rad 0 (Real.pi / 2)
      = erf713BigLambda (Real.pi / 2) - erf713BigLambda 0 := by
    unfold arcLogDerivIntegral
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
      deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) (fun θ _ => hderiv θ)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => erf713_bigLambda_hasDerivAt θ)
      (hcont.intervalIntegrable _ _)
  rw [heval, Complex.sub_im, erf713_bigLambda_im, erf713_bigLambda_im]
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  norm_num

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Route §1.5 at level `a = 2` — the single arithmetic fact of the erfc branch.**
With `Ψ₂ = √(R⁴ − L₂²) + π/4 + ½·arcsin (L₂/R²)` and `L₂ = log (2√(21987 π))`:

    2π·3499 < Ψ₂ < 2π·3500,   i.e.  21984.8654 < 21987.7846 < 21991.1486.

Margins ≈ 2.92 and ≈ 3.36; the crude enclosures `L₂ ∈ (0, 7)` and
`arcsin (L₂/R²) ∈ [0, π/2]` suffice.  (Stated with `L₂` abstracted as a variable
constrained to `(0,7)` precisely because only the enclosure matters — the concrete
`erfc713_bigL2_bounds` supplies `0 < L₂ < 6.7`.) -/
theorem erfc713_modelPsi2_bounds {L : ℝ} (hL0 : 0 < L) (hL7 : L < 7) :
    2 * Real.pi * 3499
      < Real.sqrt (21987 ^ 2 - L ^ 2) + Real.pi / 4 + Real.arcsin (L / 21987) / 2
    ∧ Real.sqrt (21987 ^ 2 - L ^ 2) + Real.pi / 4 + Real.arcsin (L / 21987) / 2
      < 2 * Real.pi * 3500 := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  have he1 : (21986.99 : ℝ) = Real.sqrt (21986.99 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have he2 : (21987 : ℝ) = Real.sqrt (21987 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have hsqrt_lo : (21986.99 : ℝ) < Real.sqrt (21987 ^ 2 - L ^ 2) := by
    rw [he1]
    apply Real.sqrt_lt_sqrt (by norm_num)
    nlinarith
  have hsqrt_hi : Real.sqrt (21987 ^ 2 - L ^ 2) ≤ 21987 := by
    rw [he2]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have harcsin_lo : 0 ≤ Real.arcsin (L / 21987) :=
    Real.arcsin_nonneg.mpr (by positivity)
  have harcsin_hi : Real.arcsin (L / 21987) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  -- `linarith` cannot atomize `√(polynomial in L)`, so abstract the two transcendental
  -- quantities into plain variables and run the (purely linear) endgame on those.
  have key : ∀ S A : ℝ, 21986.99 < S → S ≤ 21987 → 0 ≤ A → A ≤ Real.pi / 2 →
      2 * Real.pi * 3499 < S + Real.pi / 4 + A / 2
        ∧ S + Real.pi / 4 + A / 2 < 2 * Real.pi * 3500 := by
    intro S A h1 h2 h3 h4
    exact ⟨by linarith, by linarith⟩
  exact key _ _ hsqrt_lo hsqrt_hi harcsin_lo harcsin_hi

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `(2 − u)' = −u'`. -/
theorem erfc713_hasDerivAt_modelM2 {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt erfc713ModelM2 (-(erf713ModelU z * (-2 * z - z⁻¹))) z := by
  simpa [erfc713ModelM2] using (erf713_hasDerivAt_modelU hz).const_sub (2 : ℂ)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_modelM2_arcPt : Continuous fun θ : ℝ => erfc713ModelM2 (arcPoint erf713Rad θ) := by
  have h : Continuous fun θ : ℝ => (2 : ℂ) - erf713ModelU (arcPoint erf713Rad θ) :=
    continuous_const.sub erf713_continuous_modelU_arcPt
  simpa [erfc713ModelM2] using h

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_deriv_modelM2_arcPt :
    Continuous fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ))
      = fun θ : ℝ => -(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)) :=
    funext fun θ => (erfc713_hasDerivAt_modelM2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv
  rw [heq]
  exact (erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor).neg

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- The level-`2` reciprocal model factor `k₂(z) = 1 − 2/u(z)`; on the far half of the
arc it plays for `2 − u` the role `2 − u` itself plays on the near half, since
`2 − u = (−u)·k₂`. -/
def erfc713KFun2 (z : ℂ) : ℂ := 1 - 2 * (erf713ModelU z)⁻¹

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `k₂' = 2u'/u²`. -/
theorem erfc713_hasDerivAt_kFun2 {z : ℂ} (hz : z ≠ 0) (hu : erf713ModelU z ≠ 0) :
    HasDerivAt erfc713KFun2 (2 * (erf713ModelU z * (-2 * z - z⁻¹)) / (erf713ModelU z) ^ 2) z := by
  have h := (((erf713_hasDerivAt_modelU hz).inv hu).const_mul (2 : ℂ)).const_sub (1 : ℂ)
  have hfun : erfc713KFun2 = fun x => 1 - 2 * (erf713ModelU x)⁻¹ := rfl
  rw [hfun]
  convert h using 1
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_kFun2_arcPt : Continuous fun θ : ℝ => erfc713KFun2 (arcPoint erf713Rad θ) := by
  have h : Continuous fun θ : ℝ => (1 : ℂ) - 2 * (erf713ModelU (arcPoint erf713Rad θ))⁻¹ :=
    continuous_const.sub
      (continuous_const.mul (erf713_continuous_modelU_arcPt.inv₀ erf713_modelU_arcPt_ne_zero))
  simpa [erfc713KFun2] using h

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_deriv_kFun2_arcPt :
    Continuous fun θ : ℝ => deriv erfc713KFun2 (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erfc713KFun2 (arcPoint erf713Rad θ))
      = fun θ : ℝ => 2 * (erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))
          / (erf713ModelU (arcPoint erf713Rad θ)) ^ 2 :=
    funext fun θ =>
      (erfc713_hasDerivAt_kFun2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ) (erf713_modelU_arcPt_ne_zero θ)).deriv
  rw [heq]
  exact (continuous_const.mul (erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor)).div
    (erf713_continuous_modelU_arcPt.pow 2) (fun θ => pow_ne_zero 2 (erf713_modelU_arcPt_ne_zero θ))

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The pointwise factorisation `(2−u)'/(2−u) = u'/u + k₂'/k₂` behind `2 − u = (−u)·k₂`,
in purely algebraic form: with `M₂ = 2 − U`, `k₂ = 1 − 2U⁻¹`, `M₂' = −U·g`, `u' = U·g`,
`k₂' = 2U·g/U²`. -/
theorem erfc713_logDeriv_factor_split2 (U g X : ℂ) (hU : U ≠ 0) (hM : 2 - U ≠ 0) :
    -(U * g) / (2 - U) * X
      = U * g / U * X + 2 * (U * g) / U ^ 2 / (1 - 2 * U⁻¹) * X := by
  have hU2 : U - 2 ≠ 0 := fun h => hM (by rw [show (2 : ℂ) - U = -(U - 2) by ring, h, neg_zero])
  have h1 : (1 : ℂ) - 2 * U⁻¹ = (U - 2) / U := by field_simp
  rw [h1]
  field_simp
  ring

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- The level-`2` split point `θ*₂ = π/4 + ½ arcsin (L₂/R²)`, the unique arc parameter
with `|u| = 2` (equivalently `R² cos 2θ*₂ = −L₂`). -/
def erfc713ThetaStar2 : ℝ := Real.pi / 4 + Real.arcsin (erfc713BigL2 / 21987) / 2

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- `Ψ₂ = R² sin 2θ*₂ + θ*₂`, the continuous argument of `u` at the split point. -/
def erfc713BigPsi2 : ℝ := erf713Rad ^ 2 * Real.sin (2 * erfc713ThetaStar2) + erfc713ThetaStar2

-- no-dlmf: contour/model vocabulary for the argument-principle count `erfc713_low_zero_count`; proof infrastructure
/-- `φ₂ = 2π·3500 − Ψ₂`, the principal residue of `−Ψ₂` mod `2π`. -/
def erfc713BigPhi2 : ℝ := 2 * Real.pi * 3500 - erfc713BigPsi2

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_bigL2_div_pos : 0 < erfc713BigL2 / 21987 := by
  have := erfc713_bigL2_bounds.1; positivity

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_bigL2_div_lt_one : erfc713BigL2 / 21987 < 1 := by
  have := erfc713_bigL2_bounds.2; rw [div_lt_one (by norm_num)]; linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_two_thetaStar2 : 2 * erfc713ThetaStar2 = Real.pi / 2 + Real.arcsin (erfc713BigL2 / 21987) := by
  rw [erfc713ThetaStar2]; ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_cos_two_thetaStar2 : Real.cos (2 * erfc713ThetaStar2) = -(erfc713BigL2 / 21987) := by
  rw [erfc713_two_thetaStar2, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.sin_arcsin (by linarith [erfc713_bigL2_div_pos]) erfc713_bigL2_div_lt_one.le]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_sin_two_thetaStar2 :
    Real.sin (2 * erfc713ThetaStar2) = Real.sqrt (1 - (erfc713BigL2 / 21987) ^ 2) := by
  rw [erfc713_two_thetaStar2, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_arcsin]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_thetaStar2_pos : 0 < erfc713ThetaStar2 := by
  have h := Real.arcsin_nonneg.mpr erfc713_bigL2_div_pos.le
  have := Real.pi_pos
  rw [erfc713ThetaStar2]; linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_thetaStar2_lt_pi_div_two : erfc713ThetaStar2 < Real.pi / 2 := by
  have h : Real.arcsin (erfc713BigL2 / 21987) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr erfc713_bigL2_div_lt_one
  rw [erfc713ThetaStar2]; linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `Ψ₂` in the exact shape of `erfc713_modelPsi2_bounds`. -/
theorem erfc713_bigPsi2_eq :
    erfc713BigPsi2 = Real.sqrt (21987 ^ 2 - erfc713BigL2 ^ 2) + Real.pi / 4
      + Real.arcsin (erfc713BigL2 / 21987) / 2 := by
  have hfac : (21987 : ℝ) ^ 2 - erfc713BigL2 ^ 2 = 21987 ^ 2 * (1 - (erfc713BigL2 / 21987) ^ 2) := by
    field_simp
  have hsqrt : Real.sqrt ((21987 : ℝ) ^ 2 - erfc713BigL2 ^ 2)
      = 21987 * Real.sqrt (1 - (erfc713BigL2 / 21987) ^ 2) := by
    rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [erfc713BigPsi2, erfc713_sin_two_thetaStar2, erf713Rad_sq, erfc713ThetaStar2, ← hsqrt]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- `φ₂ ∈ (0, 2π)` — this is where `erfc713_modelPsi2_bounds` (the single arithmetic fact of
the erfc branch) is consumed, with `L := L₂ ∈ (0, 6.7) ⊆ (0, 7)`. -/
theorem erfc713_bigPhi2_bounds : 0 < erfc713BigPhi2 ∧ erfc713BigPhi2 < 2 * Real.pi := by
  obtain ⟨h1, h2⟩ := erfc713_modelPsi2_bounds erfc713_bigL2_bounds.1 (by linarith [erfc713_bigL2_bounds.2])
  rw [erfc713BigPhi2, erfc713_bigPsi2_eq]
  constructor <;> linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_exp_bigL2 : Real.exp erfc713BigL2 = 2 * (Real.sqrt Real.pi * erf713Rad) := by
  rw [erfc713BigL2]
  exact Real.exp_log (by linarith [erf713_sqrtPi_Rad_pos])

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- Left of the split point `|u| < 2`. -/
theorem erfc713_modelU_arcPt_norm_lt_two {θ : ℝ} (h0 : 0 ≤ θ) (h : θ < erfc713ThetaStar2) :
    ‖erf713ModelU (arcPoint erf713Rad θ)‖ < 2 := by
  have hπ := Real.pi_pos
  have hcos : Real.cos (2 * erfc713ThetaStar2) < Real.cos (2 * θ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith)
      (by linarith [erfc713_thetaStar2_lt_pi_div_two]) (by linarith)
  rw [erfc713_cos_two_thetaStar2] at hcos
  have hkey : -(erf713Rad ^ 2 * Real.cos (2 * θ)) < erfc713BigL2 := by rw [erf713Rad_sq]; linarith
  have hexp : Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) < 2 * (Real.sqrt Real.pi * erf713Rad) := by
    rw [← erfc713_exp_bigL2]; exact Real.exp_lt_exp.mpr hkey
  rw [erf713_modelU_arcPt_norm, div_lt_iff₀ erf713_sqrtPi_Rad_pos]
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- Right of the split point the *reciprocal* level-`2` factor is a strict contraction. -/
theorem erfc713_modelU_arcPt_two_inv_norm_lt_one {θ : ℝ} (h : erfc713ThetaStar2 < θ)
    (h2 : θ ≤ Real.pi / 2) : ‖(2 : ℂ) * (erf713ModelU (arcPoint erf713Rad θ))⁻¹‖ < 1 := by
  have hπ := Real.pi_pos
  have hcos : Real.cos (2 * θ) < Real.cos (2 * erfc713ThetaStar2) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [erfc713_thetaStar2_pos]) (by linarith)
      (by linarith)
  rw [erfc713_cos_two_thetaStar2] at hcos
  have hkey : erfc713BigL2 < -(erf713Rad ^ 2 * Real.cos (2 * θ)) := by rw [erf713Rad_sq]; linarith
  have hexp : 2 * (Real.sqrt Real.pi * erf713Rad) < Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * θ))) := by
    rw [← erfc713_exp_bigL2]; exact Real.exp_lt_exp.mpr hkey
  have hn : (2 : ℝ) < ‖erf713ModelU (arcPoint erf713Rad θ)‖ := by
    rw [erf713_modelU_arcPt_norm, lt_div_iff₀ erf713_sqrtPi_Rad_pos]
    linarith
  have hpos : (0 : ℝ) < ‖erf713ModelU (arcPoint erf713Rad θ)‖ := by linarith
  have hrw : ‖(2 : ℂ) * (erf713ModelU (arcPoint erf713Rad θ))⁻¹‖ = 2 / ‖erf713ModelU (arcPoint erf713Rad θ)‖ := by
    rw [norm_mul, norm_inv, show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_mul_inv]
  rw [hrw, div_lt_one hpos]
  exact hn

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- At the split point `u` is `2` times a pure phase. -/
theorem erfc713_modelU_thetaStar2 :
    erf713ModelU (arcPoint erf713Rad erfc713ThetaStar2) = 2 * Complex.exp ((erfc713BigPhi2 : ℂ) * I) := by
  have hcos : Real.exp (-(erf713Rad ^ 2 * Real.cos (2 * erfc713ThetaStar2)))
      = 2 * (Real.sqrt Real.pi * erf713Rad) := by
    rw [erfc713_cos_two_thetaStar2, erf713Rad_sq, ← erfc713_exp_bigL2]
    congr 1
    ring
  have hphase : ((-(erf713Rad ^ 2 * Real.sin (2 * erfc713ThetaStar2) + erfc713ThetaStar2) : ℝ) : ℂ) * I
      = ((erfc713BigPhi2 : ℝ) : ℂ) * I + ((-3500 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have h : (-(erf713Rad ^ 2 * Real.sin (2 * erfc713ThetaStar2) + erfc713ThetaStar2) : ℝ)
        = erfc713BigPhi2 - 2 * Real.pi * 3500 := by
      rw [erfc713BigPhi2, erfc713BigPsi2]; ring
    rw [h]
    push_cast
    ring
  rw [erf713_modelU_arcPt, hcos, hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, mul_div_assoc, div_self erf713_sqrtPi_Rad_pos.ne']
  norm_num

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- At the split point `2/u` is the pure phase `e^{i(2π−φ₂)}`. -/
theorem erfc713_modelU_thetaStar2_two_inv :
    (2 : ℂ) * (erf713ModelU (arcPoint erf713Rad erfc713ThetaStar2))⁻¹
      = Complex.exp (((2 * Real.pi - erfc713BigPhi2 : ℝ) : ℂ) * I) := by
  have hne : Complex.exp ((erfc713BigPhi2 : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have h1 : ((2 * Real.pi - erfc713BigPhi2 : ℝ) : ℂ) * I
      = -((erfc713BigPhi2 : ℂ) * I) + 2 * (Real.pi : ℂ) * I := by push_cast; ring
  rw [erfc713_modelU_thetaStar2, h1, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
    Complex.exp_neg]
  field_simp

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- On `[0, θ*₂]` the level-`2` model lies in the open right half-plane. -/
theorem erfc713_modelM2_re_pos {θ : ℝ} (h0 : 0 ≤ θ) (h : θ ≤ erfc713ThetaStar2) :
    0 < (erfc713ModelM2 (arcPoint erf713Rad θ)).re := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := erfc713_modelU_arcPt_norm_lt_two h0 hlt
    have hre : (erf713ModelU (arcPoint erf713Rad θ)).re ≤ ‖erf713ModelU (arcPoint erf713Rad θ)‖ := Complex.re_le_norm _
    have hM : (erfc713ModelM2 (arcPoint erf713Rad θ)).re = 2 - (erf713ModelU (arcPoint erf713Rad θ)).re := by rw [erfc713ModelM2]; simp
    rw [hM]; linarith
  · obtain ⟨hφ0, hφ2⟩ := erfc713_bigPhi2_bounds
    have h2 := erf713_one_sub_exp_re_pos hφ0 hφ2
    have hM : erfc713ModelM2 (arcPoint erf713Rad θ)
        = 2 * (1 - Complex.exp ((erfc713BigPhi2 : ℂ) * I)) := by
      rw [heq, erfc713ModelM2, erfc713_modelU_thetaStar2]; ring
    have hre : (erfc713ModelM2 (arcPoint erf713Rad θ)).re
        = 2 * (1 - Complex.exp ((erfc713BigPhi2 : ℂ) * I)).re := by
      rw [hM]; simp [Complex.mul_re]
    rw [hre]; linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- On `[θ*₂, π/2]` the reciprocal factor lies in the open right half-plane. -/
theorem erfc713_kFun2_re_pos {θ : ℝ} (h : erfc713ThetaStar2 ≤ θ) (h2 : θ ≤ Real.pi / 2) :
    0 < (erfc713KFun2 (arcPoint erf713Rad θ)).re := by
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := erfc713_modelU_arcPt_two_inv_norm_lt_one hlt h2
    have hre : ((2 : ℂ) * (erf713ModelU (arcPoint erf713Rad θ))⁻¹).re ≤ ‖(2 : ℂ) * (erf713ModelU (arcPoint erf713Rad θ))⁻¹‖ :=
      Complex.re_le_norm _
    have hk : (erfc713KFun2 (arcPoint erf713Rad θ)).re = 1 - ((2 : ℂ) * (erf713ModelU (arcPoint erf713Rad θ))⁻¹).re := by
      rw [erfc713KFun2]; simp
    rw [hk]; linarith
  · obtain ⟨hφ0, hφ2⟩ := erfc713_bigPhi2_bounds
    rw [← heq, erfc713KFun2, erfc713_modelU_thetaStar2_two_inv]
    exact erf713_one_sub_exp_re_pos (by linarith) (by linarith)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **INTERFACE SORRY 2 — CLOSED.**  The §1.4 model integral at level `a = 2`.

    Im ∫₀^{π/2} (2 − u)'/(2 − u)·iz dθ = 2π·3500 − 3π/2 − arctan (2·erf713TinyC).

This is the exact erfc instance of the level-parametrized §1.4 lemma the route doc
recommends proving once for all four families (`a = 1` for `erf`, `a = 2` here,
`a = 1 ± i` for the two Fresnel families).  Content, spelled out at `a = 2`:

* `|u|` is strictly increasing along the arc (`d log|u|/dθ = 2R² sin 2θ ≥ 0`), from
  `e^{−R²}/(√πR)` to `e^{R²}/(√πR)`, so there is a unique `θ*₂ ∈ (π/4, π/2)` with
  `|u(θ*₂)| = 2`, i.e. `R² cos 2θ*₂ = −L₂`, `L₂ = log(2√π R)`;
* on `[0, θ*₂]`: `2 − u = 2·(1 − u/2)` with `|u/2| ≤ 1`, so the image lies in
  `closedBall 1 1 ⊆ slitPlane` off `0` and `ARC` gives
  `arg (2 − u)(θ*₂) − arg (2 − u)(0) = (φ/2 − π/2) − 0` where `u(θ*₂) = 2e^{iφ}`,
  `φ ∈ (0, 2π)` (endpoint identity `arg (1 − e^{iφ}) = φ/2 − π/2`);
* on `[θ*₂, π/2]`: `2 − u = (−u)·(1 − 2/u)` with `|2/u| ≤ 1`; the first factor
  contributes `Im Λ(π/2) − Im Λ(θ*₂) = −π/2 + Ψ₂` by the **branch-free**
  antiderivative `erf713BigLambda` (PROVEN above), the second contributes
  `arg (1 − 2i·erf713TinyC) − arg (1 − e^{−iφ}) = −arctan (2·erf713TinyC) − (π/2 − φ/2)`;
* summing, `Im = φ + Ψ₂ − 3π/2 − arctan (2 erf713TinyC)`, and `φ = 2π·3500 − Ψ₂` because
  `Ψ₂ ∈ (2π·3499, 2π·3500)` — the arithmetic fact `erfc713_modelPsi2_bounds` (PROVEN above,
  with `L = L₂ ∈ (0,7)` supplied by `erfc713_bigL2_bounds`).

Note the `arctan (2·erf713TinyC)` term: as in the `erf` branch (where the route doc's
display dropped the corresponding `arctan erf713TinyC` and had to be corrected), the
`θ = π/2` endpoint of the second factor is `1 − 2/u(iR) = 1 − 2i·erf713TinyC`, NOT `1`.
Its argument cancels *exactly* against `erfc713_ratio_arg_pi_div_two` below; dropping it
would make the assembly inconsistent by `2·arctan (2 erf713TinyC) ≠ 0`. -/
theorem erfc713_modelArc_im_level_two :
    (arcLogDerivIntegral erfc713ModelM2 erf713Rad 0 (Real.pi / 2)).im
      = 2 * Real.pi * 3500 - 3 * Real.pi / 2 - Real.arctan (2 * erf713TinyC) := by
  obtain ⟨hφ0, hφ2⟩ := erfc713_bigPhi2_bounds
  have hπ := Real.pi_pos
  have hts0 : 0 < erfc713ThetaStar2 := erfc713_thetaStar2_pos
  have hts2 : erfc713ThetaStar2 < Real.pi / 2 := erfc713_thetaStar2_lt_pi_div_two
  have huIcc1 : Set.uIcc (0 : ℝ) erfc713ThetaStar2 = Set.Icc 0 erfc713ThetaStar2 := Set.uIcc_of_le hts0.le
  have huIcc2 : Set.uIcc erfc713ThetaStar2 (Real.pi / 2) = Set.Icc erfc713ThetaStar2 (Real.pi / 2) :=
    Set.uIcc_of_le hts2.le
  have hsub1 : Set.Icc (0 : ℝ) erfc713ThetaStar2 ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Icc_subset_Icc le_rfl hts2.le
  have hsub2 : Set.Icc erfc713ThetaStar2 (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Icc_subset_Icc hts0.le le_rfl
  -- nonvanishing of the three factors
  have hune : ∀ θ : ℝ, erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := erf713_modelU_arcPt_ne_zero
  have hMne : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), erfc713ModelM2 (arcPoint erf713Rad θ) ≠ 0 :=
    fun θ hθ => erfc713_modelM2_ne_zero hθ
  have hkne : ∀ θ ∈ Set.Icc erfc713ThetaStar2 (Real.pi / 2), erfc713KFun2 (arcPoint erf713Rad θ) ≠ 0 := by
    intro θ hθ h0
    have h := erfc713_kFun2_re_pos hθ.1 hθ.2
    rw [h0] at h
    simp at h
  -- continuity and interval integrability of the three integrands
  have hrot : Continuous fun θ : ℝ => I * arcPoint erf713Rad θ := continuous_const.mul (continuous_arcPoint erf713Rad)
  have hFMcont : ContinuousOn
      (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    (erfc713_continuous_deriv_modelM2_arcPt.continuousOn.div
      erfc713_continuous_modelM2_arcPt.continuousOn hMne).mul hrot.continuousOn
  have hFUcont : Continuous
      (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) :=
    (erf713_continuous_deriv_modelU_arcPt.div erf713_continuous_modelU_arcPt hune).mul hrot
  have hFKcont : ContinuousOn
      (fun θ : ℝ => deriv erfc713KFun2 (arcPoint erf713Rad θ) / erfc713KFun2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc erfc713ThetaStar2 (Real.pi / 2)) :=
    (erfc713_continuous_deriv_kFun2_arcPt.continuousOn.div
      erfc713_continuous_kFun2_arcPt.continuousOn hkne).mul hrot.continuousOn
  have hFMint1 : IntervalIntegrable
      (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume 0 erfc713ThetaStar2 := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc1]; exact hFMcont.mono hsub1
  have hFMint2 : IntervalIntegrable
      (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erfc713ThetaStar2 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFMcont.mono hsub2
  have hFUint : IntervalIntegrable
      (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erfc713ThetaStar2 (Real.pi / 2) := hFUcont.intervalIntegrable _ _
  have hFKint : IntervalIntegrable
      (fun θ : ℝ => deriv erfc713KFun2 (arcPoint erf713Rad θ) / erfc713KFun2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume erfc713ThetaStar2 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFKcont
  -- split the quarter arc at the crossing point `θ*₂`
  have hsplit : arcLogDerivIntegral erfc713ModelM2 erf713Rad 0 (Real.pi / 2)
      = (∫ θ in (0 : ℝ)..erfc713ThetaStar2,
          deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
        + ∫ θ in erfc713ThetaStar2..(Real.pi / 2),
            deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) :=
    (intervalIntegral.integral_add_adjacent_intervals hFMint1 hFMint2).symm
  -- near half: `2 − u` itself lies in the right half-plane
  have hleft : (∫ θ in (0 : ℝ)..erfc713ThetaStar2,
      deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      = Complex.log (erfc713ModelM2 (arcPoint erf713Rad erfc713ThetaStar2)) - Complex.log (erfc713ModelM2 (arcPoint erf713Rad 0)) := by
    have hdiff : ∀ θ ∈ Set.uIcc (0 : ℝ) erfc713ThetaStar2, DifferentiableAt ℂ erfc713ModelM2 (arcPoint erf713Rad θ) :=
      fun θ _ => (erfc713_hasDerivAt_modelM2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).differentiableAt
    have hslit : ∀ θ ∈ Set.uIcc (0 : ℝ) erfc713ThetaStar2,
        erfc713ModelM2 (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
      intro θ hθ
      rw [huIcc1] at hθ
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (erfc713_modelM2_re_pos hθ.1 hθ.2))
    exact arc_logDeriv_integral hdiff hslit hFMint1
  -- far half: factor `2 − u = (−u)·k₂`, i.e. `(2−u)'/(2−u) = u'/u + k₂'/k₂`
  have hMeq : ∀ θ ∈ Set.Icc erfc713ThetaStar2 (Real.pi / 2),
      deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        = deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv erfc713KFun2 (arcPoint erf713Rad θ) / erfc713KFun2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) := by
    intro θ hθ
    have hU := hune θ
    have hM := hMne θ (hsub2 hθ)
    rw [erfc713ModelM2] at hM
    rw [(erfc713_hasDerivAt_modelM2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv,
      (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv,
      (erfc713_hasDerivAt_kFun2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ) hU).deriv, erfc713ModelM2, erfc713KFun2]
    exact erfc713_logDeriv_factor_split2 _ _ _ hU hM
  have hright : (∫ θ in erfc713ThetaStar2..(Real.pi / 2),
      deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      = (erf713BigLambda (Real.pi / 2) - erf713BigLambda erfc713ThetaStar2)
        + (Complex.log (erfc713KFun2 (arcPoint erf713Rad (Real.pi / 2)))
            - Complex.log (erfc713KFun2 (arcPoint erf713Rad erfc713ThetaStar2))) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv erf713ModelU (arcPoint erf713Rad θ) / erf713ModelU (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv erfc713KFun2 (arcPoint erf713Rad θ) / erfc713KFun2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (fun θ hθ => hMeq θ (by rwa [huIcc2] at hθ)),
      intervalIntegral.integral_add hFUint hFKint]
    congr 1
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => erf713_bigLambda_hasDerivAt θ) hFUint
    · have hdiff : ∀ θ ∈ Set.uIcc erfc713ThetaStar2 (Real.pi / 2),
          DifferentiableAt ℂ erfc713KFun2 (arcPoint erf713Rad θ) :=
        fun θ _ => (erfc713_hasDerivAt_kFun2 ((arcPoint_ne_zero erf713Rad_pos.ne') θ) (hune θ)).differentiableAt
      have hslit : ∀ θ ∈ Set.uIcc erfc713ThetaStar2 (Real.pi / 2),
          erfc713KFun2 (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
        intro θ hθ
        rw [huIcc2] at hθ
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (erfc713_kFun2_re_pos hθ.1 hθ.2))
      exact arc_logDeriv_integral hdiff hslit hFKint
  -- the four endpoint arguments
  have hargMstar : Complex.arg (erfc713ModelM2 (arcPoint erf713Rad erfc713ThetaStar2)) = erfc713BigPhi2 / 2 - Real.pi / 2 := by
    have hM : erfc713ModelM2 (arcPoint erf713Rad erfc713ThetaStar2)
        = ((2 : ℝ) : ℂ) * (1 - Complex.exp ((erfc713BigPhi2 : ℂ) * I)) := by
      rw [erfc713ModelM2, erfc713_modelU_thetaStar2]; push_cast; ring
    rw [hM, Complex.arg_real_mul _ (by norm_num : (0 : ℝ) < 2)]
    exact erf713_arg_one_sub_exp_mul_I hφ0 hφ2
  have hargM0 : Complex.arg (erfc713ModelM2 (arcPoint erf713Rad 0)) = 0 := by
    have hM : erfc713ModelM2 (arcPoint erf713Rad 0)
        = ((2 - Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) : ℝ) : ℂ) := by
      rw [erfc713ModelM2, erf713_modelU_zero]; push_cast; ring
    rw [hM]
    exact Complex.arg_ofReal_of_nonneg (by linarith [erf713_modelU_zero_lt_one])
  have hargKstar : Complex.arg (erfc713KFun2 (arcPoint erf713Rad erfc713ThetaStar2))
      = (2 * Real.pi - erfc713BigPhi2) / 2 - Real.pi / 2 := by
    rw [erfc713KFun2, erfc713_modelU_thetaStar2_two_inv]
    exact erf713_arg_one_sub_exp_mul_I (by linarith) (by linarith)
  have hargKpi : Complex.arg (erfc713KFun2 (arcPoint erf713Rad (Real.pi / 2))) = -Real.arctan (2 * erf713TinyC) := by
    set b : ℝ := Real.exp (erf713Rad ^ 2) / (Real.sqrt Real.pi * erf713Rad) with hb
    have hbpos : 0 < b := div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
    have hexp1 : Real.exp (erf713Rad ^ 2) * Real.exp (-(erf713Rad ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hRne : erf713Rad ≠ 0 := erf713Rad_pos.ne'
    have hsqπne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hbc : b * erf713TinyC = 1 := by
      rw [hb, erf713TinyC]
      field_simp
      linear_combination hexp1
    have hbc' : ((b : ℝ) : ℂ) * ((erf713TinyC : ℝ) : ℂ) = 1 := by exact_mod_cast hbc
    have hprod : (((erf713TinyC : ℝ) : ℂ) * I) * (-(((b : ℝ) : ℂ) * I)) = 1 := by
      linear_combination (-((erf713TinyC : ℝ) : ℂ) * ((b : ℝ) : ℂ)) * Complex.I_sq + hbc'
    have hinv : (erf713ModelU (arcPoint erf713Rad (Real.pi / 2)))⁻¹ = ((erf713TinyC : ℝ) : ℂ) * I := by
      rw [erf713_modelU_pi_div_two]
      exact inv_eq_of_mul_eq_one_left hprod
    rw [erfc713KFun2, hinv,
      show (2 : ℂ) * (((erf713TinyC : ℝ) : ℂ) * I) = ((2 * erf713TinyC : ℝ) : ℂ) * I by push_cast; ring,
      erf713_arg_one_sub_mul_I]
  -- assemble
  rw [hsplit, hleft, hright]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [hargMstar, hargM0, hargKstar, hargKpi, erf713_bigLambda_im, erf713_bigLambda_im,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  have hpsi : erfc713BigPsi2 = erf713Rad ^ 2 * Real.sin (2 * erfc713ThetaStar2) + erfc713ThetaStar2 := rfl
  have hphi : erfc713BigPhi2 = 2 * Real.pi * 3500 - erfc713BigPsi2 := rfl
  rw [hpsi] at hphi
  linarith

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The two factors of `F_M` split the arc integral additively:
`F_M'/F_M = (−u)'/(−u) + (2−u)'/(2−u)` pointwise on the arc, where both factors are
nonvanishing (`erf713_modelU_arcPt_ne_zero`, `erfc713_modelM2_norm_ge`). -/
theorem erfc713_arcIntegral_modelFM_split :
    arcLogDerivIntegral erfc713ModelFM erf713Rad 0 (Real.pi / 2)
      = arcLogDerivIntegral (fun z => -erf713ModelU z) erf713Rad 0 (Real.pi / 2)
        + arcLogDerivIntegral erfc713ModelM2 erf713Rad 0 (Real.pi / 2) := by
  have hkey : ∀ θ ∈ Set.uIcc (0:ℝ) (Real.pi / 2),
      deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        = deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) / (-erf713ModelU (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ)
          + deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ) := by
    intro θ hθ
    have hθ' : θ ∈ Icc 0 (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by positivity)] at hθ
    have hz : arcPoint erf713Rad θ ≠ 0 := (arcPoint_ne_zero erf713Rad_pos.ne') θ
    have hune : erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := erf713_modelU_arcPt_ne_zero θ
    have hM2ne : erfc713ModelM2 (arcPoint erf713Rad θ) ≠ 0 := erfc713_modelM2_ne_zero hθ'
    have hu := erf713_hasDerivAt_modelU hz
    have hnegu : HasDerivAt (fun z => -erf713ModelU z) (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ
        - (arcPoint erf713Rad θ)⁻¹))) (arcPoint erf713Rad θ) := hu.neg
    have hM2 : HasDerivAt erfc713ModelM2 (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)))
        (arcPoint erf713Rad θ) := by
      have : HasDerivAt (fun z => 2 - erf713ModelU z)
          (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))) (arcPoint erf713Rad θ) := by
        simpa using hu.const_sub 2
      exact this
    have hprod : HasDerivAt erfc713ModelFM
        ((-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))) * erfc713ModelM2 (arcPoint erf713Rad θ)
          + (-erf713ModelU (arcPoint erf713Rad θ)) * (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹))))
        (arcPoint erf713Rad θ) := hnegu.mul hM2
    rw [hprod.deriv, hnegu.deriv, hM2.deriv, erfc713ModelFM]
    field_simp
    ring
  have hcont1 : Continuous (fun θ : ℝ =>
      deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) / (-erf713ModelU (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ)) := by
    have h : (fun θ : ℝ => deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) / (-erf713ModelU (arcPoint erf713Rad θ))
        * (I * arcPoint erf713Rad θ))
        = fun θ : ℝ => -2 * I * ((erf713Rad ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (θ : ℂ) * I) - I := by
      funext θ
      rw [erfc713_deriv_negU θ, neg_div_neg_eq, erfc713_arcIntegrand_modelU]
    rw [h]
    fun_prop
  have hcontU : Continuous (fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ)) := by
    have h : (fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ))
        = fun θ : ℝ => Complex.exp (-(arcPoint erf713Rad θ) ^ 2)
            / ((Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ) := rfl
    rw [h]
    have hnum : Continuous (fun θ : ℝ => Complex.exp (-(arcPoint erf713Rad θ) ^ 2)) :=
      Complex.continuous_exp.comp (((continuous_arcPoint erf713Rad).pow 2).neg)
    have hden : Continuous (fun θ : ℝ => (Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ) :=
      continuous_const.mul (continuous_arcPoint erf713Rad)
    exact hnum.div hden
      (fun θ => mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')
        ((arcPoint_ne_zero erf713Rad_pos.ne') θ))
  have hcontdU : Continuous (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ)) := by
    have h : (fun θ : ℝ => deriv erf713ModelU (arcPoint erf713Rad θ))
        = fun θ : ℝ => erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹) := by
      funext θ
      exact (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv
    rw [h]
    refine hcontU.mul (Continuous.sub ?_ ?_)
    · exact continuous_const.mul (continuous_arcPoint erf713Rad)
    · exact (continuous_arcPoint erf713Rad).inv₀ (arcPoint_ne_zero erf713Rad_pos.ne')
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      deriv (fun z => -erf713ModelU z) (arcPoint erf713Rad θ) / (-erf713ModelU (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      MeasureTheory.volume 0 (Real.pi / 2) := hcont1.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ : ℝ =>
      deriv erfc713ModelM2 (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro θ hθ
    have hθ' : θ ∈ Icc 0 (Real.pi / 2) := by
      rwa [Set.uIcc_of_le (by positivity)] at hθ
    have hcontdM2 : Continuous (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ)) := by
      have hdM2 : (fun θ : ℝ => deriv erfc713ModelM2 (arcPoint erf713Rad θ))
          = fun θ : ℝ => -deriv erf713ModelU (arcPoint erf713Rad θ) := by
        funext θ
        have h1 : HasDerivAt erfc713ModelM2 (-(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)))
            (arcPoint erf713Rad θ) := (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).const_sub 2
        rw [h1.deriv, (erf713_hasDerivAt_modelU ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv]
      rw [hdM2]
      exact hcontdU.neg
    have hcontM2 : Continuous (fun θ : ℝ => erfc713ModelM2 (arcPoint erf713Rad θ)) := by
      have : (fun θ : ℝ => erfc713ModelM2 (arcPoint erf713Rad θ)) = fun θ : ℝ => 2 - erf713ModelU (arcPoint erf713Rad θ) := rfl
      rw [this]
      exact continuous_const.sub hcontU
    refine ContinuousAt.continuousWithinAt ?_
    have hne : erfc713ModelM2 (arcPoint erf713Rad θ) ≠ 0 := erfc713_modelM2_ne_zero hθ'
    exact ((hcontdM2.continuousAt).div (hcontM2.continuousAt) hne).mul
      (continuous_const.mul (continuous_arcPoint erf713Rad)).continuousAt
  unfold arcLogDerivIntegral
  rw [intervalIntegral.integral_congr hkey]
  exact intervalIntegral.integral_add hint1 hint2

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **The model arc integral for `F`.**  `Im J_M = 2π·3499 − arctan (2·erf713TinyC)`:
`−π/2` from the branch-free `(−u)` factor plus `2π·3500 − 3π/2 − arctan (2 erf713TinyC)`
from the level-`2` factor. -/
theorem erfc713_modelArc_im :
    (arcLogDerivIntegral erfc713ModelFM erf713Rad 0 (Real.pi / 2)).im
      = 2 * Real.pi * 3499 - Real.arctan (2 * erf713TinyC) := by
  rw [erfc713_arcIntegral_modelFM_split, Complex.add_im, erfc713_modelArc_im_negU, erfc713_modelArc_im_level_two]
  ring

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **A2/A3 for the erfc branch (PROVEN).**  On the closed quarter arc the ratio
`F/F_M` lies in `ball 1 (1/2)`.

`cerfc = (1 + E)u` with `‖E‖ ≤ 4/R² = 4/21987` (`erf713_cerfc_scaled_unit_bound_closed`, valid on
the CLOSED right half-plane), so

    F/F_M = (cerfc/u)·((2 − cerfc)/(2 − u)) = (1 + E)·(1 − E·u/(2 − u)),

and `‖u‖/‖2 − u‖ ≤ 4` on the arc (if `‖u‖ ≤ 4` use `‖2 − u‖ ≥ 1` from
`erfc713_modelM2_norm_ge`; if `‖u‖ ≥ 4` use `‖2 − u‖ ≥ ‖u‖ − 2 ≥ ‖u‖/2`).  Hence
`‖F/F_M − 1‖ ≤ ‖E‖ + (1 + ‖E‖)·4‖E‖ ≤ 5·(4/21987) < 1/2`. -/
theorem erfc713_ratio_mem_ball {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) ∈ ball (1 : ℂ) (1 / 2) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hzne : arcPoint erf713Rad θ ≠ 0 := (arcPoint_ne_zero erf713Rad_pos.ne') θ
  have hznorm : ‖arcPoint erf713Rad θ‖ = erf713Rad := (norm_arcPoint erf713Rad_pos.le) θ
  have hRsq : erf713Rad ^ 2 = 21987 := erf713Rad_sq
  have hsec : |Complex.arg (arcPoint erf713Rad θ)| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff, (arcPoint_re erf713Rad)]
    exact mul_nonneg erf713Rad_pos.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ1⟩)
  have hM2 : (1 : ℝ) ≤ ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := erfc713_modelM2_norm_ge ⟨hθ0, hθ1⟩
  have hM2ne : erfc713ModelM2 (arcPoint erf713Rad θ) ≠ 0 := erfc713_modelM2_ne_zero ⟨hθ0, hθ1⟩
  have hune : erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := erf713_modelU_arcPt_ne_zero θ
  have hπne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ * Complex.exp (arcPoint erf713Rad θ ^ 2)
      * cerfc (arcPoint erf713Rad θ) - 1 with hEdef
  have hEb : ‖E‖ ≤ 4 / 21987 := by
    have := erf713_cerfc_scaled_unit_bound_closed hzne hsec
    rw [hznorm, hRsq] at this
    exact this
  have hu : erf713ModelU (arcPoint erf713Rad θ)
      * ((Real.sqrt Real.pi : ℂ) * arcPoint erf713Rad θ * Complex.exp (arcPoint erf713Rad θ ^ 2)) = 1 := by
    rw [erf713ModelU]
    field_simp
    rw [← Complex.exp_add]
    simp
  -- `cerfc = (1 + E)·u`
  have hcerfc : cerfc (arcPoint erf713Rad θ) = (1 + E) * erf713ModelU (arcPoint erf713Rad θ) := by
    rw [hEdef]
    field_simp
    linear_combination (cerfc (arcPoint erf713Rad θ)) * hu.symm
  -- the ratio of `u` to `2 − u` is at most `4` on the arc
  have hratio : ‖erf713ModelU (arcPoint erf713Rad θ)‖ ≤ 4 * ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := by
    rcases le_total (‖erf713ModelU (arcPoint erf713Rad θ)‖) 4 with h | h
    · linarith
    · have hge : ‖erf713ModelU (arcPoint erf713Rad θ)‖ - ‖(2 : ℂ)‖ ≤ ‖erf713ModelU (arcPoint erf713Rad θ) - 2‖ :=
        norm_sub_norm_le _ _
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num, ← norm_neg (erf713ModelU (arcPoint erf713Rad θ) - 2)] at hge
      have hrw : -(erf713ModelU (arcPoint erf713Rad θ) - 2) = erfc713ModelM2 (arcPoint erf713Rad θ) := by rw [erfc713ModelM2]; ring
      rw [hrw] at hge
      linarith
  -- the factored form of the ratio
  have hFM : erfc713ModelFM (arcPoint erf713Rad θ) = (-erf713ModelU (arcPoint erf713Rad θ)) * erfc713ModelM2 (arcPoint erf713Rad θ) := rfl
  have hFMne : erfc713ModelFM (arcPoint erf713Rad θ) ≠ 0 := by
    rw [hFM]
    exact mul_ne_zero (neg_ne_zero.mpr hune) hM2ne
  have hM2ne' : (2 : ℂ) - erf713ModelU (arcPoint erf713Rad θ) ≠ 0 := hM2ne
  have hFfac : erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) - 1
      = E - (1 + E) * (E * erf713ModelU (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ)) := by
    rw [erfc713_bigF_eq_cerfc, hFM, hcerfc, erfc713ModelM2]
    field_simp
    ring
  have hMpos : (0:ℝ) < ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ := by linarith
  rw [Metric.mem_ball, Complex.dist_eq, hFfac]
  have hb1 : ‖E - (1 + E) * (E * erf713ModelU (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ))‖
      ≤ ‖E‖ + ‖(1 + E)‖ * (‖E‖ * ‖erf713ModelU (arcPoint erf713Rad θ)‖ / ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖) := by
    calc ‖E - (1 + E) * (E * erf713ModelU (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ))‖
        ≤ ‖E‖ + ‖(1 + E) * (E * erf713ModelU (arcPoint erf713Rad θ) / erfc713ModelM2 (arcPoint erf713Rad θ))‖ := norm_sub_le _ _
      _ = ‖E‖ + ‖(1 + E)‖ * (‖E‖ * ‖erf713ModelU (arcPoint erf713Rad θ)‖ / ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖) := by
          rw [norm_mul, norm_div, norm_mul]
  have hb2 : ‖(1 : ℂ) + E‖ ≤ 1 + ‖E‖ := by
    calc ‖(1 : ℂ) + E‖ ≤ ‖(1 : ℂ)‖ + ‖E‖ := norm_add_le _ _
      _ = 1 + ‖E‖ := by rw [norm_one]
  have hb3 : ‖E‖ * ‖erf713ModelU (arcPoint erf713Rad θ)‖ / ‖erfc713ModelM2 (arcPoint erf713Rad θ)‖ ≤ 4 * ‖E‖ := by
    rw [div_le_iff₀ hMpos]
    nlinarith [norm_nonneg E, hratio, hMpos]
  have hEnn : (0:ℝ) ≤ ‖E‖ := norm_nonneg E
  nlinarith [hb1, hb2, hb3, hEb, hEnn, norm_nonneg ((1:ℂ) + E)]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Endpoint `θ = 0`.**  Both `F(R) = erf(R)² − 1` and `F_M(R) = (−u₀)(2 − u₀)` are
*negative reals* (`u₀ = e^{−R²}/(√πR) ∈ (0,1)`), so the ratio is a positive real and
`arg h(0) = 0`. -/
theorem erfc713_ratio_arg_zero : Complex.arg (erfc713BigF (arcPoint erf713Rad 0) / erfc713ModelFM (arcPoint erf713Rad 0)) = 0 := by
  set u0 : ℝ := Real.exp (-(erf713Rad ^ 2)) / (Real.sqrt Real.pi * erf713Rad) with hu0
  have hu0pos : 0 < u0 := div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
  have hu0lt : u0 < 1 := erf713_modelU_zero_lt_one
  have hF : erfc713BigF (arcPoint erf713Rad 0) = ((FLMF.Error.erf erf713Rad ^ 2 - 1 : ℝ) : ℂ) := by
    rw [(arcPoint_zero erf713Rad), erfc713BigF, cerf_ofReal]; push_cast; ring
  have hFneg : FLMF.Error.erf erf713Rad ^ 2 - 1 < 0 := by
    have h1 := erf_lt_one erf713Rad
    have h2 := neg_one_lt_erf erf713Rad
    nlinarith
  have hFM : erfc713ModelFM (arcPoint erf713Rad 0) = ((-u0 * (2 - u0) : ℝ) : ℂ) := by
    rw [erfc713ModelFM, erfc713ModelM2, erf713_modelU_zero, ← hu0]
    push_cast
    ring
  have hFMneg : -u0 * (2 - u0) < 0 := by nlinarith
  rw [hF, hFM, ← Complex.ofReal_div]
  refine Complex.arg_ofReal_of_nonneg ?_
  exact le_of_lt (div_pos_of_neg_of_neg hFneg hFMneg)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **Endpoint `θ = π/2` — the exact cancellation.**  `F(iR) = −(a² + 1)` with
`a = Im cerf(iR) > 0` is a negative real, and

    F_M(iR) = (i b)·(2 + i b) = −b²·(1 − 2i·c),   b = e^{R²}/(√πR),  c = erf713TinyC = 1/b,

so `h(π/2) = ((a²+1)/b²)·(1 − 2i c)⁻¹` and `arg h(π/2) = arctan (2·erf713TinyC)` — exactly
minus the `arg k(π/2)` carried by `erfc713_modelArc_im_level_two`. -/
theorem erfc713_ratio_arg_pi_div_two :
    Complex.arg (erfc713BigF (arcPoint erf713Rad (Real.pi / 2)) / erfc713ModelFM (arcPoint erf713Rad (Real.pi / 2)))
      = Real.arctan (2 * erf713TinyC) := by
  have him := (cerf_imAxis_im_pos erf713Rad_pos).2
  set a : ℝ := (cerf ((erf713Rad : ℂ) * I)).im with ha
  set b : ℝ := Real.exp (erf713Rad ^ 2) / (Real.sqrt Real.pi * erf713Rad) with hb
  have hbpos : 0 < b := div_pos (Real.exp_pos _) erf713_sqrtPi_Rad_pos
  have hRne : erf713Rad ≠ 0 := erf713Rad_pos.ne'
  have hsqπne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hexp1 : Real.exp (erf713Rad ^ 2) * Real.exp (-(erf713Rad ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hbc : b * erf713TinyC = 1 := by
    rw [hb, erf713TinyC]
    field_simp
    linear_combination hexp1
  have hbc' : ((b : ℝ) : ℂ) * ((erf713TinyC : ℝ) : ℂ) = 1 := by exact_mod_cast hbc
  have hcerf : cerf (arcPoint erf713Rad (Real.pi / 2)) = ((a : ℝ) : ℂ) * I := by
    rw [(arcPoint_pi_div_two erf713Rad)]
    apply Complex.ext
    · simpa [ha] using cerf_imAxis_re erf713Rad
    · simp [ha]
  have hF : erfc713BigF (arcPoint erf713Rad (Real.pi / 2)) = ((-(a ^ 2) - 1 : ℝ) : ℂ) := by
    rw [erfc713BigF, hcerf]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  have hFM : erfc713ModelFM (arcPoint erf713Rad (Real.pi / 2))
      = ((-(b ^ 2) : ℝ) : ℂ) * (1 - ((2 * erf713TinyC : ℝ) : ℂ) * I) := by
    rw [erfc713ModelFM, erfc713ModelM2, erf713_modelU_pi_div_two, ← hb]
    push_cast
    linear_combination (-2 * ((b : ℝ) : ℂ) * I) * hbc' + (((b : ℝ) : ℂ) ^ 2) * Complex.I_sq
  have hkne : (1 : ℂ) - ((2 * erf713TinyC : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have : ((1 : ℂ) - ((2 * erf713TinyC : ℝ) : ℂ) * I).re = 0 := by rw [h]; simp
    simp at this
  have hbne : ((-(b ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have : -(b ^ 2) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hfac : erfc713BigF (arcPoint erf713Rad (Real.pi / 2)) / erfc713ModelFM (arcPoint erf713Rad (Real.pi / 2))
      = (((-(a ^ 2) - 1) / (-(b ^ 2)) : ℝ) : ℂ) * (1 - ((2 * erf713TinyC : ℝ) : ℂ) * I)⁻¹ := by
    rw [hF, hFM]
    push_cast
    field_simp
  have hposr : 0 < (-(a ^ 2) - 1) / (-(b ^ 2)) := by
    apply div_pos_of_neg_of_neg <;> nlinarith [sq_nonneg a]
  have hne : ¬ (-Real.arctan (2 * erf713TinyC) = Real.pi) := by
    have h1 := Real.arctan_lt_pi_div_two (2 * erf713TinyC)
    have h2 := Real.neg_pi_div_two_lt_arctan (2 * erf713TinyC)
    have h3 := Real.pi_pos
    intro h; linarith [h ▸ h2]
  rw [hfac, Complex.arg_real_mul _ hposr, Complex.arg_inv, erf713_arg_one_sub_mul_I,
    if_neg hne, neg_neg]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- **INTERFACE SORRY 3 — CLOSED.**  Splitting the arc integral along `F = F_M·h`.

Content (pure contour bookkeeping; no arithmetic and no new estimate — the analytic
input is `erfc713_ratio_mem_ball`, PROVEN above):

* on the closed quarter arc `‖2 − u‖ ≥ 1` (`erfc713_modelM2_norm_ge`) and `u ≠ 0`, so
  `F_M ≠ 0` there, and `h := F/F_M` maps the arc into `ball 1 (1/2) ⊆ slitPlane`
  (`erfc713_ratio_mem_ball`); in particular `h ≠ 0`, hence also `F ≠ 0`, on the arc
  (independently re-proven by `erfc713_bigF_ne_zero_on_circle`);
* `erfc713BigF`, `erfc713ModelFM` and `h` are differentiable at every arc point
  (`erfc713_differentiable_bigF`; `erf713ModelU` is a quotient of entire functions with
  nonvanishing denominator `√π z`), so pointwise `F'/F = F_M'/F_M + h'/h` and each of
  the three integrands is continuous on `[0, π/2]`, hence interval-integrable;
* the arc FTC lemma `ARC` (`arc_logDeriv_integral`, PROVEN above in this file — the
  single new `Methods` lemma of the route) then evaluates the `h`-piece as
  `log h(π/2) − log h(0)`; the model piece is `erfc713_arcIntegral_modelFM_split` (PROVEN).

What is proven below is therefore only: the pointwise identity
`F'/F = F_M'/F_M + h'/h` on the arc (product rule for `F = F_M·h`), the three
continuity/integrability side conditions, and the `ARC` application — no estimate and
no arithmetic. -/
theorem erfc713_hasDerivAt_modelFM {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt erfc713ModelFM
      (-(erf713ModelU z * (-2 * z - z⁻¹)) * erfc713ModelM2 z
        + (-erf713ModelU z) * -(erf713ModelU z * (-2 * z - z⁻¹))) z :=
  (erf713_hasDerivAt_modelU hz).neg.mul (erfc713_hasDerivAt_modelM2 hz)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_modelFM_arcPt : Continuous fun θ : ℝ => erfc713ModelFM (arcPoint erf713Rad θ) := by
  have h : Continuous fun θ : ℝ => (-erf713ModelU (arcPoint erf713Rad θ)) * erfc713ModelM2 (arcPoint erf713Rad θ) :=
    erf713_continuous_modelU_arcPt.neg.mul erfc713_continuous_modelM2_arcPt
  simpa [erfc713ModelFM] using h

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_continuous_deriv_modelFM_arcPt :
    Continuous fun θ : ℝ => deriv erfc713ModelFM (arcPoint erf713Rad θ) := by
  have heq : (fun θ : ℝ => deriv erfc713ModelFM (arcPoint erf713Rad θ))
      = fun θ : ℝ => -(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)) * erfc713ModelM2 (arcPoint erf713Rad θ)
          + (-erf713ModelU (arcPoint erf713Rad θ)) * -(erf713ModelU (arcPoint erf713Rad θ) * (-2 * arcPoint erf713Rad θ - (arcPoint erf713Rad θ)⁻¹)) :=
    funext fun θ => (erfc713_hasDerivAt_modelFM ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).deriv
  rw [heq]
  exact ((erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor).neg.mul
      erfc713_continuous_modelM2_arcPt).add
    (erf713_continuous_modelU_arcPt.neg.mul
      (erf713_continuous_modelU_arcPt.mul erf713_continuous_ratioFactor).neg)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_modelFM_arcPt_ne_zero {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    erfc713ModelFM (arcPoint erf713Rad θ) ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (erf713_modelU_arcPt_ne_zero θ)) (erfc713_modelM2_ne_zero hθ)

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
theorem erfc713_arcIntegral_bigF_split :
    arcLogDerivIntegral erfc713BigF erf713Rad 0 (Real.pi / 2)
      = arcLogDerivIntegral erfc713ModelFM erf713Rad 0 (Real.pi / 2)
        + (Complex.log (erfc713BigF (arcPoint erf713Rad (Real.pi / 2)) / erfc713ModelFM (arcPoint erf713Rad (Real.pi / 2)))
            - Complex.log (erfc713BigF (arcPoint erf713Rad 0) / erfc713ModelFM (arcPoint erf713Rad 0))) := by
  have hπ2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have huIcc : Set.uIcc (0 : ℝ) (Real.pi / 2) = Set.Icc 0 (Real.pi / 2) := Set.uIcc_of_le hπ2
  have hcne : ∀ θ : ℝ, erfc713BigF (arcPoint erf713Rad θ) ≠ 0 := fun θ => erfc713_bigF_ne_zero_on_circle ((norm_arcPoint erf713Rad_pos.le) θ)
  have hMne : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), erfc713ModelFM (arcPoint erf713Rad θ) ≠ 0 :=
    fun θ hθ => erfc713_modelFM_arcPt_ne_zero hθ
  have hMd : ∀ θ : ℝ, HasDerivAt erfc713ModelFM (deriv erfc713ModelFM (arcPoint erf713Rad θ)) (arcPoint erf713Rad θ) :=
    fun θ => (erfc713_hasDerivAt_modelFM ((arcPoint_ne_zero erf713Rad_pos.ne') θ)).differentiableAt.hasDerivAt
  have hHd : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun z => erfc713BigF z / erfc713ModelFM z)
        ((deriv erfc713BigF (arcPoint erf713Rad θ) * erfc713ModelFM (arcPoint erf713Rad θ)
            - erfc713BigF (arcPoint erf713Rad θ) * deriv erfc713ModelFM (arcPoint erf713Rad θ)) / (erfc713ModelFM (arcPoint erf713Rad θ)) ^ 2) (arcPoint erf713Rad θ) :=
    fun θ hθ => ((erfc713_differentiable_bigF (arcPoint erf713Rad θ)).hasDerivAt).div (hMd θ) (hMne θ hθ)
  -- continuity of all three integrands
  have hdbigF : Continuous (fun θ : ℝ => deriv erfc713BigF (arcPoint erf713Rad θ)) :=
    erfc713_continuous_deriv_bigF.comp (continuous_arcPoint erf713Rad)
  have hbigF : Continuous (fun θ : ℝ => erfc713BigF (arcPoint erf713Rad θ)) :=
    erfc713_differentiable_bigF.continuous.comp (continuous_arcPoint erf713Rad)
  have hrot : Continuous (fun θ : ℝ => I * arcPoint erf713Rad θ) := continuous_const.mul (continuous_arcPoint erf713Rad)
  have hFc : Continuous (fun θ : ℝ => deriv erfc713BigF (arcPoint erf713Rad θ) / erfc713BigF (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) :=
    (hdbigF.div hbigF hcne).mul hrot
  have hFm : ContinuousOn
      (fun θ : ℝ => deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    (erfc713_continuous_deriv_modelFM_arcPt.continuousOn.div
      erfc713_continuous_modelFM_arcPt.continuousOn hMne).mul hrot.continuousOn
  -- the pointwise splitting of the logarithmic derivative
  have hEq : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      deriv erfc713BigF (arcPoint erf713Rad θ) / erfc713BigF (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        = deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ)
              / (erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ) := by
    intro θ hθ
    rw [(hHd θ hθ).deriv]
    have hM := hMne θ hθ
    have hc := hcne θ
    field_simp
    ring
  have hFh : ContinuousOn
      (fun θ : ℝ => deriv (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ)
        / (erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    refine (hFc.continuousOn.sub hFm).congr ?_
    intro θ hθ
    show deriv (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ) / (erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ))
        * (I * arcPoint erf713Rad θ)
      = deriv erfc713BigF (arcPoint erf713Rad θ) / erfc713BigF (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
        - deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
    rw [hEq θ hθ]
    ring
  have hFmInt : IntervalIntegrable
      (fun θ : ℝ => deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ))
      volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFm
  have hFhInt : IntervalIntegrable
      (fun θ : ℝ => deriv (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ)
        / (erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFh
  -- the ratio stays in `ball 1 (1/2) ⊆ slitPlane`
  have hslit : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ) ∈ Complex.slitPlane := by
    intro θ hθ
    rw [huIcc] at hθ
    have hb := erfc713_ratio_mem_ball hθ
    rw [Metric.mem_ball, Complex.dist_eq] at hb
    have h1 : |(erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) - 1).re|
        ≤ ‖erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) - 1‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_re, Complex.one_re] at h1
    have h2 := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hb))).1
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using by linarith))
  have hdiff : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      DifferentiableAt ℂ (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ) := by
    intro θ hθ
    rw [huIcc] at hθ
    exact (hHd θ hθ).differentiableAt
  have hlog := arc_logDeriv_integral (f := fun z => erfc713BigF z / erfc713ModelFM z) (a := (0 : ℝ))
    (b := Real.pi / 2) hdiff hslit hFhInt
  have hmain : arcLogDerivIntegral erfc713BigF erf713Rad 0 (Real.pi / 2)
      = arcLogDerivIntegral erfc713ModelFM erf713Rad 0 (Real.pi / 2)
        + arcLogDerivIntegral (fun z => erfc713BigF z / erfc713ModelFM z) erf713Rad 0 (Real.pi / 2) := by
    show (∫ θ in (0 : ℝ)..(Real.pi / 2),
        deriv erfc713BigF (arcPoint erf713Rad θ) / erfc713BigF (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)) = _
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv erfc713ModelFM (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ) * (I * arcPoint erf713Rad θ)
          + deriv (fun z => erfc713BigF z / erfc713ModelFM z) (arcPoint erf713Rad θ)
              / (erfc713BigF (arcPoint erf713Rad θ) / erfc713ModelFM (arcPoint erf713Rad θ)) * (I * arcPoint erf713Rad θ))
      (fun θ hθ => hEq θ (by rwa [huIcc] at hθ))]
    exact intervalIntegral.integral_add hFmInt hFhInt
  rw [hmain, hlog]

-- no-dlmf: step of the argument-principle computation behind `erfc713_low_zero_count`; proof infrastructure
/-- The quarter-arc integral of `F'/F` has imaginary part exactly `2π·3499`.

`Im J = Im J_M + arg h(π/2) − arg h(0) = (2π·3499 − arctan (2 erf713TinyC)) + arctan (2 erf713TinyC) − 0`:
the two `arctan (2·erf713TinyC)` terms cancel **exactly** (they are the same quantity,
`arg k(π/2) = −arg h(π/2)`, both coming from `1 − 2/u(iR) = 1 − 2i·erf713TinyC`), so the
quantization the argument principle demands comes out on the nose — no `|ε| ≤ π/3`
integer-pinning step is needed. -/
theorem erfc713_arc_bigF_im :
    (arcLogDerivIntegral erfc713BigF erf713Rad 0 (Real.pi / 2)).im = 2 * Real.pi * 3499 := by
  rw [erfc713_arcIntegral_bigF_split]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [erfc713_modelArc_im, erfc713_ratio_arg_zero, erfc713_ratio_arg_pi_div_two]
  ring

-- no-dlmf: the count of the small sector zeros of `cerfc`; the single arithmetic input to
-- DLMF 7.13.3 that the asymptotic machinery of this file cannot supply
/-- **The number of small zeros of `erfc` in the sector `re < 0 < im`.**  `erfc` has exactly
`3499` zeros `u` with `Re u < 0 < Im u` and `‖u‖² < 21987`.

**Proved** by the argument principle applied to the even, conjugation-equivariant auxiliary
function `F = cerf² − 1 = (−cerfc)·(2 − cerfc)`, whose zero set is
`{cerfc = 0} ∪ −{cerfc = 0}` (`erfc713_bigF_zero_iff`) and which vanishes on neither axis
(`erfc713_bigF_ne_zero_on_axis`); the Klein group `{1, −1, conj, −conj}` therefore meets each
orbit once per open quadrant and the multiplicity-weighted count on the closed disc
`‖z‖ ≤ √21987` is `4·N` with `N` the sector count sought here (`erfc713_zeros_finset_exists`);
identifying the second-quadrant zeros of `F` with those of `cerfc` uses that `cerfc` has no zero
in the closed right half-plane (`cerfc_ne_zero_of_re_nonneg`, from DLMF 7.7.2).  The same two
symmetries fold the circle integral of `F'/F` onto the quarter arc
(`erfc713_circle_eq_four_I_arc_im`), where `F` is compared with the elementary model
`F_M = (−u)·(2 − u)`, `u(z) = e^{−z²}/(√π z)`, whose logarithmic-derivative integral is closed
form (`erfc713_modelArc_im`).  The contour value is `2πi·13996 = 2πi·(4·3499)`.

Its role is to fix the *origin* of the enumeration: the asymptotic analysis above establishes a
strictly modulus-increasing bijection between the sector zeros with `‖u‖² ≥ 21987` and the indices
`n ≥ 3500` (`erfc713_grid_zero`, `erfc713_zero_has_index`, `erfc713_zero_index_unique`), which
determines DLMF's enumeration only up to a constant index offset.  The offset vanishes exactly
when the number of zeros below the cut equals the number of grid points below it, i.e. when the
count here is `3500 − 1 = 3499`.

The threshold `21987` is chosen strictly between the two neighbouring grid values
`2λ₃₄₉₉² ≈ 21984.08` and `2λ₃₅₀₀² ≈ 21990.36`, with margin larger than the `±1` localization of
`erfc713_approx_norm_sq`; so no zero of index `3499` or `3500` sits ambiguously at the cut.

The count itself is a bounded-region zero count, not an asymptotic estimate: it is carried out on
an explicit contour with `FLMF.Methods.AnalyticZeroCount`
(`circleIntegral_logDeriv_eq_sum_orders` on the full disc, `arc_logDeriv_integral` on the
quarter arc). -/
theorem erfc713_low_zero_count :
    {u : ℂ | cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧ ‖u‖ ^ 2 < 21987}.ncard = 3499 := by
  classical
  obtain ⟨P, hP, hPball, hsum⟩ := erfc713_zeros_finset_exists
  set N : ℕ := {u : ℂ | cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧ ‖u‖ ^ 2 < 21987}.ncard with hN
  -- the argument principle on the full disc (`FLMF.Methods.AnalyticZeroCount`)
  have hAP := circleIntegral_logDeriv_eq_sum_orders (f := erfc713BigF) (c := 0) (R := erf713Rad)
    erf713Rad_pos P (fun z _ => erfc713_analyticAt_bigF z) hP hPball
    (fun p _ => erfc713_analyticOrder_bigF_ne_top p)
  -- the contour value, via the symmetry reduction and the arc computation
  have hval : (∮ z in C((0:ℂ), erf713Rad), deriv erfc713BigF z / erfc713BigF z)
      = 2 * (Real.pi : ℂ) * I * (13996 : ℂ) := by
    rw [erfc713_circle_eq_four_I_arc_im, erfc713_arc_bigF_im]
    push_cast
    ring
  rw [hval, hsum] at hAP
  -- `2πi·13996 = 2πi·(4N)`  ⟹  `N = 3499`
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simpa using (Real.pi_ne_zero)
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hcancel : (13996 : ℂ) = 4 * (N : ℂ) := mul_left_cancel₀ h2 hAP
  have hre : (13996 : ℝ) = 4 * (N : ℝ) := by exact_mod_cast congrArg Complex.re hcancel
  have : (N : ℝ) = 3499 := by linarith
  exact_mod_cast this

end Erfc713ZeroCount

set_option maxHeartbeats 1000000 in
/-- **DLMF 7.13.3** — asymptotic expansion of the zeros `zₙ = xₙ + i yₙ` of
`erfc` in the sector `re < 0 < im`. For the complete enumeration `z`, ordered by increasing absolute
value (DLMF §7.13(ii)), of ALL zeros of `cerfc` in that sector (`hall`), the real and imaginary
parts of `z n` agree with the three-term approximations `erfcZeroReApprox`,
`erfcZeroImApprox` (built from `λ'`, `μ'` of 7.13.4) up to `o(λ'⁻³)`.

**Index origin.** DLMF numbers these zeros from `n = 1`, and the enumeration here matches
that 1-based labelling directly: only `z n` for `1 ≤ n` is constrained (`z 0` is
unconstrained junk, harmless in the `=o[atTop]` conclusions), the hypotheses order
`z 1, z 2, …` by increasing absolute value, and `z n` is DLMF's `zₙ`, compared with the
`n`-th approximations. Comparing at any shifted index would be off by a full grid step,
`λ'_{n+1} − λ'_n ≍ √π/(2√n) ≫ λ'_n⁻³`.
* dlmf: 7.13.3
* family: error
* kind: zero-asymptotic

DLMF 7.13.3.
Numerical: N/A (conjunction-partial)
Verified: verified
DAG: E-7.13.3.
-/
theorem erf_7_13_3 (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cerfc (z n) = 0)
    (hsector : ∀ n, 1 ≤ n → (z n).re < 0 ∧ 0 < (z n).im)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cerfc w = 0 → w.re < 0 → 0 < w.im → ∃ n, 1 ≤ n ∧ z n = w) :
    (fun n => (z n).re - erfcZeroReApprox n) =o[atTop]
        (fun n => (erfcZeroLambda n) ^ (-3 : ℤ)) ∧
      (fun n => (z n).im - erfcZeroImApprox n) =o[atTop]
        (fun n => (erfcZeroLambda n) ^ (-3 : ℤ)) := by
  classical
  -- the grid zeros
  have hex : ∀ m : ℕ, ∃ u : ℂ, 3400 ≤ m → (cerfc u = 0 ∧ u.re < 0 ∧ 0 < u.im ∧
      |u.re - erfcZeroReApprox m| ≤ (erfcZeroMu m + 3) ^ 4 / (20 * erfcZeroLambda m ^ 5) ∧
      |u.im - erfcZeroImApprox m| ≤ (erfcZeroMu m + 3) ^ 4 / (20 * erfcZeroLambda m ^ 5)) := by
    intro m
    by_cases h : 3400 ≤ m
    · obtain ⟨u, h1, h2, h3, h4, h5⟩ := erfc713_grid_zero m h
      exact ⟨u, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose W hW using hex
  have hWnorm : ∀ m : ℕ, 3400 ≤ m → |‖W m‖ ^ 2 - 2 * erfcZeroLambda m ^ 2| ≤ 1 := by
    intro m hm
    obtain ⟨-, -, -, h4, h5⟩ := hW m hm
    exact (erfc713_approx_norm_sq hm h4 h5).1
  have hlamgap : ∀ m m' : ℕ, 1 ≤ m → m < m' →
      2 * erfcZeroLambda m ^ 2 + 6 ≤ 2 * erfcZeroLambda m' ^ 2 := by
    intro m m' hm hlt
    have h1 := erfc713_lambda_sq hm
    have h2 := erfc713_lambda_sq (n := m') (by omega)
    have h3 : (m:ℝ) + 1 ≤ (m':ℝ) := by exact_mod_cast hlt
    have hpi := Real.pi_gt_three
    rw [h1, h2]; nlinarith
  have hWmono : ∀ m m' : ℕ, 3400 ≤ m → m < m' → ‖W m‖ < ‖W m'‖ := by
    intro m m' hm hlt
    have hm' : 3400 ≤ m' := by omega
    obtain ⟨a1, a2⟩ := abs_le.mp (hWnorm m hm)
    obtain ⟨b1, b2⟩ := abs_le.mp (hWnorm m' hm')
    have hgap := hlamgap m m' (by omega) hlt
    have hsq : ‖W m‖ ^ 2 < ‖W m'‖ ^ 2 := by linarith
    nlinarith [norm_nonneg (W m), norm_nonneg (W m')]
  have hWinj : ∀ m m' : ℕ, 3400 ≤ m → 3400 ≤ m' → ‖W m‖ = ‖W m'‖ → m = m' := by
    intro m m' hm hm' heq
    rcases lt_trichotomy m m' with h | h | h
    · exact absurd heq (ne_of_lt (hWmono m m' hm h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hWmono m' m hm' h))
  have hWbig : ∀ m : ℕ, 3500 ≤ m → 21987 ≤ ‖W m‖ ^ 2 := by
    intro m hm
    obtain ⟨a1, a2⟩ := abs_le.mp (hWnorm m (by omega))
    have hl := erfc713_lambda_sq (n := m) (by omega)
    have hmr : (3500:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hpi := Real.pi_gt_d6
    have hprod : (3499.875:ℝ) * 3.141592 ≤ ((m:ℝ) - 1/8) * Real.pi := by nlinarith
    rw [hl] at a1
    nlinarith
  have hzeroW : ∀ u : ℂ, cerfc u = 0 → u.re < 0 → 0 < u.im → 21987 ≤ ‖u‖ ^ 2 →
      ∃ n : ℕ, 3500 ≤ n ∧ u = W n := by
    intro u hu hur hui hub
    obtain ⟨n, hn, h1, h2⟩ := erfc713_zero_has_index hu hur hui hub
    obtain ⟨g1, -, -, g4, g5⟩ := hW n (by omega)
    exact ⟨n, hn, erfc713_zero_index_unique (by omega) hu g1 h1 h2 g4 g5⟩
  -- the smallest enumeration index whose zero is beyond the cut
  have hPne : ∃ m : ℕ, 1 ≤ m ∧ 21987 ≤ ‖z m‖ ^ 2 := by
    obtain ⟨g1, g2, g3, -, -⟩ := hW 3500 (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W 3500) g1 g2 g3
    exact ⟨m, hm1, by rw [hm2]; exact hWbig 3500 (le_refl _)⟩
  set M : ℕ := Nat.find hPne with hMdef
  have hM1 : 1 ≤ M := (Nat.find_spec hPne).1
  have hM2 : 21987 ≤ ‖z M‖ ^ 2 := (Nat.find_spec hPne).2
  have hMmin : ∀ m : ℕ, m < M → ¬(1 ≤ m ∧ 21987 ≤ ‖z m‖ ^ 2) := fun m hm => Nat.find_min hPne hm
  have hzbig : ∀ m : ℕ, M ≤ m → 21987 ≤ ‖z m‖ ^ 2 := by
    intro m hm
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h]; exact hM2
    · have hlt : ‖z M‖ < ‖z m‖ := hmono hM1 (by omega : 1 ≤ m) h
      nlinarith [norm_nonneg (z M), norm_nonneg (z m)]
  -- the index attached to each enumeration entry beyond the cut
  have hfex : ∀ m : ℕ, ∃ n : ℕ, M ≤ m → (3500 ≤ n ∧ z m = W n) := by
    intro m
    by_cases h : M ≤ m
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨q1, q2⟩ := hsector m hm1
      obtain ⟨n, hn, heq⟩ := hzeroW (z m) (hzero m hm1) q1 q2 (hzbig m h)
      exact ⟨n, fun _ => ⟨hn, heq⟩⟩
    · exact ⟨3500, fun h' => absurd h' h⟩
  choose f hf using hfex
  have hfmono : ∀ m m' : ℕ, M ≤ m → m < m' → f m < f m' := by
    intro m m' hm hlt
    obtain ⟨hn1, he1⟩ := hf m hm
    obtain ⟨hn2, he2⟩ := hf m' (by omega)
    have hlt' : ‖z m‖ < ‖z m'‖ := hmono (by omega : 1 ≤ m) (by omega : 1 ≤ m') hlt
    rw [he1, he2] at hlt'
    by_contra hcon
    have hle : f m' ≤ f m := by omega
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at hlt'; exact lt_irrefl _ hlt'
    · exact absurd hlt' (not_lt.mpr (hWmono (f m') (f m) (by omega) h).le)
  have hfsurj : ∀ n : ℕ, f M ≤ n → ∃ m : ℕ, M ≤ m ∧ f m = n := by
    intro n hn
    obtain ⟨hfM1, hfMe⟩ := hf M (le_refl M)
    have hn3500 : 3500 ≤ n := by omega
    obtain ⟨g1, g2, g3, -, -⟩ := hW n (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W n) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig n hn3500⟩
    obtain ⟨hq1, hq2⟩ := hf m hmM
    have heq : ‖W (f m)‖ = ‖W n‖ := by rw [← hq2, hm2]
    exact ⟨m, hmM, hWinj _ _ (by omega) (by omega) heq⟩
  -- a strictly monotone surjection onto a tail of `ℕ` is a shift
  have hfform : ∀ m : ℕ, M ≤ m → f m + M = m + f M := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ k ih =>
      intro hm
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; omega
      · have hk : M ≤ k := by omega
        have ihk := ih hk
        have h1 : f k < f (k+1) := hfmono k (k+1) hk (by omega)
        by_contra hcon
        have h2 : f k + 1 < f (k+1) := by omega
        have h3 : f M ≤ f k + 1 := by omega
        obtain ⟨m', hm'1, hm'2⟩ := hfsurj (f k + 1) h3
        rcases Nat.lt_or_ge k m' with h4 | h4
        · have h4' : k + 1 ≤ m' := h4
          rcases eq_or_lt_of_le h4' with h6 | h6
          · rw [← h6] at hm'2; omega
          · have := hfmono (k+1) m' (by omega) h6; omega
        · rcases eq_or_lt_of_le h4 with h5 | h5
          · rw [h5] at hm'2; omega
          · have := hfmono m' k hm'1 h5; omega
  -- the first index beyond the cut is the grid index `3500`
  have hfM : f M = 3500 := by
    obtain ⟨hfM1, hfMe⟩ := hf M (le_refl M)
    refine le_antisymm ?_ hfM1
    obtain ⟨g1, g2, g3, -, -⟩ := hW 3500 (by omega)
    obtain ⟨m, hm1, hm2⟩ := hall (W 3500) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig 3500 (le_refl _)⟩
    have hle : ‖z M‖ ≤ ‖z m‖ := by
      rcases eq_or_lt_of_le hmM with h | h
      · rw [h]
      · exact (hmono hM1 (by omega : 1 ≤ m) h).le
    rw [hm2, hfMe] at hle
    by_contra hcon
    have h3500 : 3500 < f M := by omega
    exact absurd hle (not_le.mpr (hWmono 3500 (f M) (by omega) h3500))
  -- the count of the small zeros pins the enumeration origin
  have hzinj : Set.InjOn z {n : ℕ | 1 ≤ n} := by
    intro a ha b hb hab
    exact hmono.injOn ha hb (by show ‖z a‖ = ‖z b‖; rw [hab])
  have hMcount : M = 3500 := by
    have hset : {w : ℂ | cerfc w = 0 ∧ w.re < 0 ∧ 0 < w.im ∧ ‖w‖ ^ 2 < 21987}
        = ↑((Finset.Ico 1 M).image z) := by
      ext u
      simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hur, hui, hub⟩
        obtain ⟨m, hm1, hm2⟩ := hall u hu hur hui
        refine ⟨m, ⟨hm1, ?_⟩, hm2⟩
        by_contra hcon
        have hMle : M ≤ m := by omega
        have hb := hzbig m hMle
        rw [hm2] at hb
        linarith
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        obtain ⟨q1, q2⟩ := hsector m hm1
        refine ⟨hzero m hm1, q1, q2, ?_⟩
        by_contra hcon
        exact hMmin m hm2 ⟨hm1, not_lt.mp hcon⟩
    have hcard : ((Finset.Ico 1 M).image z).card = M - 1 := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]
      intro a ha b hb hab
      refine hzinj ?_ ?_ hab
      · simp only [Finset.coe_Ico, Set.mem_Ico] at ha; exact ha.1
      · simp only [Finset.coe_Ico, Set.mem_Ico] at hb; exact hb.1
    have hcount := erfc713_low_zero_count
    rw [hset, Set.ncard_coe_finset, hcard] at hcount
    omega
  -- hence the enumeration *is* the grid family from index `3500` on
  have hzW : ∀ m : ℕ, 3500 ≤ m → z m = W m := by
    intro m hm
    obtain ⟨-, he⟩ := hf m (by omega)
    have hfm : f m = m := by have h := hfform m (by omega); omega
    rw [he, hfm]
  -- the expansion error is `O(λ⁻⁴)`
  have hDbound : ∀ m : ℕ, 3400 ≤ m →
      (erfcZeroMu m + 3) ^ 4 / (20 * erfcZeroLambda m ^ 5) ≤ 121 / erfcZeroLambda m ^ 4 := by
    intro m hm
    obtain ⟨hlam, -, -, -⟩ := erfc713_param_bounds hm
    have hlam0 : (0:ℝ) < erfcZeroLambda m := by linarith
    have hq := erfc713_mu_quartic hm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg hlam0.le 4)
    have h2 : 2401 * erfcZeroLambda m * erfcZeroLambda m ^ 4
        = 2401 * erfcZeroLambda m ^ 5 := by ring
    rw [h2] at h1
    linarith [h1, pow_pos hlam0 5]
  have hlamge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ erfcZeroLambda m ^ 2 := by
    intro m hm
    rw [erfc713_lambda_sq hm]
    have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_gt_three]
  have key : ∀ F : ℕ → ℝ, (∀ m : ℕ, 3500 ≤ m → |F m| ≤ 121 / erfcZeroLambda m ^ 4) →
      F =o[atTop] (fun m => (erfcZeroLambda m) ^ (-3 : ℤ)) := by
    intro F hF
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Filter.eventually_ge_atTop (max 3500 ⌈(121/c)^2⌉₊)] with m hm
    have hm3500 : 3500 ≤ m := le_trans (le_max_left _ _) hm
    have hlam0 : (0:ℝ) < erfcZeroLambda m := by
      obtain ⟨hlam, -, -, -⟩ := erfc713_param_bounds (show 3400 ≤ m by omega); linarith
    have hceil : ((121/c)^2 : ℝ) ≤ (m:ℝ) := by
      have h1 : (⌈(121/c)^2⌉₊ : ℝ) ≤ (m:ℝ) := by
        exact_mod_cast le_trans (le_max_right 3500 ⌈(121/c)^2⌉₊) hm
      exact le_trans (Nat.le_ceil _) h1
    have hlamge' : (121/c) ≤ erfcZeroLambda m := by
      have h := hlamge m (by omega)
      have hpos : (0:ℝ) ≤ 121/c := by positivity
      nlinarith [h, hceil, hlam0]
    have hcl : (121:ℝ) ≤ c * erfcZeroLambda m := by
      have h1 : c * (121/c) = 121 := by field_simp
      have h2 := mul_le_mul_of_nonneg_left hlamge' hc.le
      linarith [h1.le, h1.ge]
    have hz : (erfcZeroLambda m) ^ (-3 : ℤ) = (erfcZeroLambda m ^ 3)⁻¹ := by
      rw [show (-3:ℤ) = -(3:ℕ) by norm_num, zpow_neg, zpow_natCast]
    have hfin : 121 / erfcZeroLambda m ^ 4 ≤ c * (erfcZeroLambda m ^ 3)⁻¹ := by
      rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcl (pow_nonneg hlam0.le 3), hlam0]
    have h := hF m hm3500
    simp only [Real.norm_eq_abs, hz, abs_of_pos (show (0:ℝ) < (erfcZeroLambda m ^ 3)⁻¹ by
      positivity)]
    linarith
  constructor
  · refine key _ ?_
    intro m hm
    obtain ⟨-, -, -, h4, -⟩ := hW m (show 3400 ≤ m by omega)
    rw [hzW m hm]
    exact le_trans h4 (hDbound m (by omega))
  · refine key _ ?_
    intro m hm
    obtain ⟨-, -, -, -, h5⟩ := hW m (show 3400 ≤ m by omega)
    rw [hzW m hm]
    exact le_trans h5 (hDbound m (by omega))

end FLMF.Error

namespace FLMF.Fresnel

open Real Filter Topology Asymptotics

/-! ## Fresnel `C` zeros — parameters (DLMF 7.13.6) -/

-- no-dlmf: encodes the 7.13.6 parameter λ; display surfaced at `erf_7_13_6`
/-- DLMF 7.13.6 (parameter `λ` for the `n`-th complex zero of the Fresnel
integral `C`): `λ = √(4n − 1)`.
* dlmf: 7.13.6
* family: fresnel
* kind: zero-asymptotic-parameter -/
def fresnelCZeroLambda (n : ℕ) : ℝ := Real.sqrt (4 * (n : ℝ) - 1)

-- no-dlmf: encodes the 7.13.6 parameter α; display surfaced at `erf_7_13_6`
/-- DLMF 7.13.6 (parameter `α` for the `n`-th complex zero of the Fresnel
integral `C`): `α = (2/π)·log (π·λ)`.
* dlmf: 7.13.6
* family: fresnel
* kind: zero-asymptotic-parameter -/
def fresnelCZeroAlpha (n : ℕ) : ℝ := (2 / Real.pi) * Real.log (Real.pi * fresnelCZeroLambda n)

/-- DLMF 7.13.6 — records the parameter equations for the Fresnel `C` zeros.

DLMF §7.13 indexes these zeros `n = 1, 2, 3, …` (Tables 7.13.1–7.13.4 tabulate
`n = 1..5`), matching `erf_7_13_1`'s 1-based enumeration; the `1 ≤ n` hypothesis
is that index range, not a narrowing. On it every displayed logarithm argument is
a positive real, where `Real.log` coincides with DLMF's principal branch `ln`, and
`Real.sqrt` with the principal square root.

Numerical: PASS
Verified: verified
DAG: E-7.13.6.
-/
theorem erf_7_13_6 (n : ℕ) (_hn : 1 ≤ n) :
    fresnelCZeroLambda n = Real.sqrt (4 * (n : ℝ) - 1) ∧
      fresnelCZeroAlpha n = (2 / Real.pi) * Real.log (Real.pi * fresnelCZeroLambda n) :=
  ⟨rfl, rfl⟩

/-! ## Fresnel `S` zeros — parameters (DLMF 7.13.7) -/

-- no-dlmf: encodes the 7.13.7 parameter λ; display surfaced at `erf_7_13_7`
/-- DLMF 7.13.7 (parameter `λ` for the `n`-th complex zero of the Fresnel
integral `S`): `λ = 2√n`.
* dlmf: 7.13.7
* family: fresnel
* kind: zero-asymptotic-parameter -/
def fresnelSZeroLambda (n : ℕ) : ℝ := 2 * Real.sqrt (n : ℝ)

-- no-dlmf: encodes the 7.13.7 parameter α; display surfaced at `erf_7_13_7`
/-- DLMF 7.13.7 (parameter `α` for the `n`-th complex zero of the Fresnel
integral `S`): `α = (2/π)·log (π·λ)`.
* dlmf: 7.13.7
* family: fresnel
* kind: zero-asymptotic-parameter -/
def fresnelSZeroAlpha (n : ℕ) : ℝ := (2 / Real.pi) * Real.log (Real.pi * fresnelSZeroLambda n)

/-- DLMF 7.13.7 — records the parameter equations for the Fresnel `S` zeros,
for the `n`-th zero (`n ≥ 1`); at `n = 0` the parameter `λ = 2√n` vanishes and
`α = (2/π)·log (π·λ)` is not the DLMF-intended quantity.

DLMF §7.13 indexes these zeros `n = 1, 2, 3, …` (Tables 7.13.1–7.13.4 tabulate
`n = 1..5`), matching `erf_7_13_1`'s 1-based enumeration; the `1 ≤ n` hypothesis
is that index range, not a narrowing. On it every displayed logarithm argument is
a positive real, where `Real.log` coincides with DLMF's principal branch `ln`, and
`Real.sqrt` with the principal square root.

Numerical: PASS
Verified: verified
DAG: E-7.13.7.
-/
theorem erf_7_13_7 (n : ℕ) (_hn : 1 ≤ n) :
    fresnelSZeroLambda n = 2 * Real.sqrt (n : ℝ) ∧
      fresnelSZeroAlpha n = (2 / Real.pi) * Real.log (Real.pi * fresnelSZeroLambda n) :=
  ⟨rfl, rfl⟩

/-! ## Fresnel zeros — the diagonal mirror symmetry `z ↦ i·conj z`

Both `C` and `S` satisfy `f (i·conj z) = ±i·conj (f z)` (combine `cfresnel_7_4_6`,
`C(iz) = iC(z)` and `S(iz) = -iS(z)`, with the reflection `f (conj z) = conj (f z)`
proved below).  Since `i·conj (x + iy) = y + ix`, this map is an involution of the OPEN
FIRST QUADRANT which swaps real and imaginary parts, and it carries first-quadrant zeros
to first-quadrant zeros.

Consequently the first-quadrant zero set of `C` (resp. `S`) is symmetric about the
diagonal: alongside the DLMF §7.13(iii) family `zₙ = xₙ + i yₙ` (with `xₙ → ∞`,
`yₙ = α/(2λ) → 0`) it contains the reflected family `yₙ + i xₙ`, whose real parts
decrease to `0`.  This is the analytic content behind the `hall`-completeness hypotheses
of the Fresnel surfaces below. -/

-- no-dlmf: Schwarz reflection for `C` (real Taylor coefficients); proof infrastructure
/-- `C (conj z) = conj (C z)`: `cfresnelC` is real on the real axis, hence commutes with
complex conjugation. -/
theorem cfresnelC_conj (z : ℂ) :
    cfresnelC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cfresnelC z) := by
  unfold cfresnelC
  rw [map_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← _root_.integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  rw [← Complex.cos_conj]
  congr 1
  simp [map_div₀, map_mul, map_pow, map_ofNat]

-- no-dlmf: Schwarz reflection for `S` (real Taylor coefficients); proof infrastructure
/-- `S (conj z) = conj (S z)`: `cfresnelS` is real on the real axis, hence commutes with
complex conjugation. -/
theorem cfresnelS_conj (z : ℂ) :
    cfresnelS ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cfresnelS z) := by
  unfold cfresnelS
  rw [map_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← _root_.integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  rw [← Complex.sin_conj]
  congr 1
  simp [map_div₀, map_mul, map_pow, map_ofNat]

-- no-dlmf: diagonal reflection of the first-quadrant zero set of `C`; proof infrastructure
/-- **Mirror zeros of `C`.**  If `w` is a zero of `C` in the open first quadrant, then so
is `i·conj w`, whose real and imaginary parts are those of `w` interchanged. -/
theorem cfresnelC_zero_mirror {w : ℂ} (hw : cfresnelC w = 0) (hre : 0 < w.re)
    (him : 0 < w.im) :
    ∃ w' : ℂ, cfresnelC w' = 0 ∧ 0 < w'.re ∧ 0 < w'.im ∧ w'.re = w.im ∧ w'.im = w.re := by
  refine ⟨Complex.I * (starRingEnd ℂ) w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(cfresnel_7_4_6 ((starRingEnd ℂ) w)).1, cfresnelC_conj, hw]; simp
  all_goals simp [Complex.mul_re, Complex.mul_im, him, hre]

-- no-dlmf: diagonal reflection of the first-quadrant zero set of `S`; proof infrastructure
/-- **Mirror zeros of `S`.**  If `w` is a zero of `S` in the open first quadrant, then so
is `i·conj w`, whose real and imaginary parts are those of `w` interchanged. -/
theorem cfresnelS_zero_mirror {w : ℂ} (hw : cfresnelS w = 0) (hre : 0 < w.re)
    (him : 0 < w.im) :
    ∃ w' : ℂ, cfresnelS w' = 0 ∧ 0 < w'.re ∧ 0 < w'.im ∧ w'.re = w.im ∧ w'.im = w.re := by
  refine ⟨Complex.I * (starRingEnd ℂ) w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(cfresnel_7_4_6 ((starRingEnd ℂ) w)).2, cfresnelS_conj, hw]; simp
  all_goals simp [Complex.mul_re, Complex.mul_im, him, hre]

/-! ## Fresnel zeros — the effective zero equation and its inversion (DLMF 7.13.5)

The analytic input for the 7.13.5 zero asymptotics.  Writing `ζ = ½√π(1+i)z`, DLMF 7.5.8
turns `4·C(z)` (resp. `4·S(z)`) into `2 − c̄·erfc(−iζ) − c·erfc ζ` with `c = 1 − i` (resp.
`c = 1 + i`), so a *sub-diagonal* first-quadrant zero of `C` or `S` solves an effective
transcendental equation `√π ζ e^{ζ²} = c/2 + O(‖ζ‖⁻²)` (`fresnel_zero_model_bound`).  Its
logarithm (`fresnel_zero_log_equation`) splits into two real equations
(`fresnel_zero_components`) in the variables `s = ξ + η`, `d = ξ − η`, `N = ‖ζ‖²`, which are
inverted to `O(λ⁻³)` by `fresnel713_zero_expansion`, with

  `λ = ½√π·λ_F`,  `μ = log (π·λ_F) = πα/2`,

`λ_F`, `α` being the DLMF 7.13.6 / 7.13.7 parameters.  The inversion yields
`d = −μ/(2λ) + O(λ⁻³)` and `s = 2λ + (μ² − 2μ)/(16λ³) + O(λ⁻³)`, i.e. — after the change of
variables `s = √π·x`, `d = −√π·y` — exactly

  `x = λ_F + (α²/8 − α/(2π) + 1/π²)·λ_F⁻³ + O(λ_F⁻³)`,  `y = α/(2λ_F) + O(λ_F⁻³)`,

which is DLMF 7.13.5 at the `O(λ⁻³)` strength asserted below (see the `erf_7_13_5`
docstring for why the displayed `λ⁻³` coefficient is incomplete by `1/π²`).

What is *not* yet supplied here is the passage from "every large sub-diagonal zero satisfies
the expansion at *its own* index" to "the DLMF-ordered enumeration has index `n`": that needs
the existence of a zero for each large index, their separation, and the count of the small
zeros. -/

section FresnelZeroEquation

open FLMF.Error

-- no-dlmf: scaled Poincaré bound in unit-normalized form; proof infrastructure for §7.13
/-- `‖√π w e^{w²} erfc w − 1‖ ≤ 4/‖w‖²` on the right half-plane. -/
theorem cerfc_scaled_unit_bound {w : ℂ} (hre : 0 < w.re) :
    ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerfc w - 1‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hz : w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hz
  have h := cerfc_scaled_leading_bound hre
  have hid : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2) * cerfc w - 1
      = w * ((Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹) := by
    field_simp
  rw [hid, norm_mul]
  calc ‖w‖ * ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (w ^ 2) * cerfc w - w⁻¹‖
      ≤ ‖w‖ * (4 / ‖w‖ ^ 3) := mul_le_mul_of_nonneg_left h hwn.le
    _ = 4 / ‖w‖ ^ 2 := by field_simp

-- no-dlmf: `erfc`-form of the Fresnel `C` integral (assembled from DLMF 7.5.8); proof infrastructure
/-- The `C`-bridge: `4·C(z) = 2 − (1+i)·erfc(−iζ) − (1−i)·erfc ζ` with `ζ = ½√π(1+i)z`. -/
theorem cfresnelC_erfc_form (z : ℂ) :
    4 * cfresnelC z
      = 2 - (1 + Complex.I) *
            cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
          - (1 - Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have harg : -Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)
      = (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z := by
    linear_combination (-(1 / 2) * (Real.sqrt Real.pi : ℂ) * z) * hI2
  rw [harg]
  have h1 := (cfresnel_7_5_8 z).1
  have h2 := (cfresnel_7_5_8 z).2
  simp only [cerfc]
  linear_combination 2 * h1 + 2 * h2

-- no-dlmf: `erfc`-form of the Fresnel `S` integral (assembled from DLMF 7.5.8); proof infrastructure
/-- The `S`-bridge: `4·S(z) = 2 − (1−i)·erfc(−iζ) − (1+i)·erfc ζ` with `ζ = ½√π(1+i)z`. -/
theorem cfresnelS_erfc_form (z : ℂ) :
    4 * cfresnelS z
      = 2 - (1 - Complex.I) *
            cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
          - (1 + Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have harg : -Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)
      = (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z := by
    linear_combination (-(1 / 2) * (Real.sqrt Real.pi : ℂ) * z) * hI2
  rw [harg]
  have h1 := (cfresnel_7_5_8 z).1
  have h2 := (cfresnel_7_5_8 z).2
  simp only [cerfc]
  linear_combination (-2 * Complex.I) * h1 + (2 * Complex.I) * h2
    + (4 * cfresnelS z - (cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z)
        + cerf ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))) * hI2

set_option maxHeartbeats 1000000 in
-- no-dlmf: the effective zero equation for the Fresnel integrals; proof infrastructure for §7.13
/-- **The effective zero equation for the Fresnel integrals.** -/
theorem fresnel_zero_model_bound {c ζ : ℂ} (hcn2 : ‖c‖ ^ 2 = 2)
    (hx : 0 < ζ.re) (hxy : ζ.re ≤ ζ.im) (hbig : 20 ≤ ‖ζ‖)
    (hz : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) :
    ‖(Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) - c / 2‖ ≤ 3 / ‖ζ‖ ^ 2 := by
  have hpi3 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hspnn : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hspsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsp : (1.77 : ℝ) ≤ Real.sqrt Real.pi := by nlinarith
  have hsp0 : (0:ℝ) < Real.sqrt Real.pi := by linarith
  set Z : ℝ := ‖ζ‖ with hZdef
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ2 : (400:ℝ) ≤ Z ^ 2 := by nlinarith
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hx; simp at hx
  set u : ℂ := -Complex.I * ζ with hudef
  have hure : u.re = ζ.im := by simp [hudef, Complex.mul_re]
  have hun : ‖u‖ = Z := by rw [hudef, norm_mul]; simp [hZdef]
  have huy : 0 < u.re := by rw [hure]; linarith
  have husq : u ^ 2 = -ζ ^ 2 := by rw [hudef]; linear_combination (ζ ^ 2) * Complex.I_sq
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) with hEdef
  set P : ℂ := (Real.sqrt Real.pi : ℂ) * u * Complex.exp (u ^ 2) * cerfc u with hPdef
  have hP : ‖P - 1‖ ≤ 4 / Z ^ 2 := by
    have h := cerfc_scaled_unit_bound huy
    rwa [hun] at h
  have hD : ‖E * cerfc ζ - 1‖ ≤ 4 / Z ^ 2 := cerfc_scaled_unit_bound hx
  have hsmall : (4:ℝ) / Z ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hPn : ‖P‖ ≤ 101 / 100 := by
    have h := norm_sub_norm_le P 1
    simp only [norm_one] at h
    linarith [hP, hsmall]
  have hcnnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hcub : ‖c‖ ≤ 1.4143 := by nlinarith
  have hclb : (1.414:ℝ) ≤ ‖c‖ := by nlinarith
  have hconj : ‖(starRingEnd ℂ) c‖ = ‖c‖ := RCLike.norm_conj c
  have hre2 : (ζ ^ 2).re ≤ 0 := by
    have h : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by simp [pow_two, Complex.mul_re]
    rw [h]; nlinarith
  have hexpu : (1:ℝ) ≤ ‖Complex.exp (u ^ 2)‖ := by
    rw [Complex.norm_exp, husq]
    have h : (-ζ ^ 2).re = -(ζ ^ 2).re := by simp
    rw [h]
    exact Real.one_le_exp (by linarith)
  have hden : ‖(Real.sqrt Real.pi : ℂ) * u * Complex.exp (u ^ 2)‖
      = Real.sqrt Real.pi * Z * ‖Complex.exp (u ^ 2)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp0, hun]
  have hPfac : ‖P‖ = Real.sqrt Real.pi * Z * ‖Complex.exp (u ^ 2)‖ * ‖cerfc u‖ := by
    rw [hPdef, norm_mul, hden]
  have hq : ‖cerfc u‖ ≤ 3 / 100 := by
    have h1 : Real.sqrt Real.pi * Z * ‖Complex.exp (u ^ 2)‖ * ‖cerfc u‖ ≤ 101 / 100 := by
      rw [← hPfac]; exact hPn
    have ha : (35.4:ℝ) ≤ Real.sqrt Real.pi * Z := by
      nlinarith [mul_le_mul_of_nonneg_right hsp hZ0.le]
    have h2 : (35:ℝ) ≤ Real.sqrt Real.pi * Z * ‖Complex.exp (u ^ 2)‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hexpu (by positivity : (0:ℝ) ≤ Real.sqrt Real.pi * Z)]
    nlinarith [norm_nonneg (cerfc u)]
  have hzz : c * cerfc ζ = 2 - (starRingEnd ℂ) c * cerfc u := by linear_combination -hz
  have hcerfz : (138:ℝ) / 100 ≤ ‖cerfc ζ‖ := by
    have h2 : 2 - ‖(starRingEnd ℂ) c * cerfc u‖ ≤ ‖(2 : ℂ) - (starRingEnd ℂ) c * cerfc u‖ := by
      have h := norm_sub_norm_le (2 : ℂ) ((starRingEnd ℂ) c * cerfc u)
      simpa using h
    have h3 : ‖(starRingEnd ℂ) c * cerfc u‖ = ‖c‖ * ‖cerfc u‖ := by rw [norm_mul, hconj]
    have h5 : ‖c * cerfc ζ‖ = ‖c‖ * ‖cerfc ζ‖ := norm_mul _ _
    have h4 : 2 - ‖c‖ * ‖cerfc u‖ ≤ ‖c‖ * ‖cerfc ζ‖ := by
      rw [← h5, hzz, ← h3]; exact h2
    nlinarith [norm_nonneg (cerfc ζ)]
  have hEcz : ‖E‖ * ‖cerfc ζ‖ ≤ 101 / 100 := by
    have h := norm_sub_norm_le (E * cerfc ζ) 1
    simp only [norm_one] at h
    rw [norm_mul] at h
    linarith [hD, hsmall]
  have hEub : ‖E‖ ≤ 74 / 100 := by nlinarith [norm_nonneg E]
  have hEsq : ‖E‖ ^ 2 = Real.pi * Z ^ 2 * ‖Complex.exp (2 * ζ ^ 2)‖ := by
    have h2 : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
      norm_cast
    have h3 : Complex.exp (ζ ^ 2) ^ 2 = Complex.exp (2 * ζ ^ 2) := by
      rw [← Complex.exp_nat_mul]; norm_num
    have h1 : E ^ 2 = (Real.pi : ℂ) * ζ ^ 2 * Complex.exp (2 * ζ ^ 2) := by
      rw [hEdef, ← h3, ← h2]; ring
    rw [← norm_pow, h1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_pow, ← hZdef]
  have hexpid : Complex.exp (2 * ζ ^ 2) * Complex.exp (u ^ 2) = Complex.exp (ζ ^ 2) := by
    rw [← Complex.exp_add, husq]; congr 1; ring
  have hIu : Complex.I * u = ζ := by rw [hudef]; linear_combination (-ζ) * Complex.I_sq
  have hEu : E * cerfc u = Complex.I * Complex.exp (2 * ζ ^ 2) * P := by
    calc E * cerfc u
        = (Complex.I * u) * (Real.sqrt Real.pi : ℂ) * Complex.exp (ζ ^ 2) * cerfc u := by
          rw [hIu, hEdef]; ring
      _ = Complex.I * Complex.exp (2 * ζ ^ 2) * P := by rw [hPdef, ← hexpid]; ring
  have hEunorm : ‖E * cerfc u‖ = ‖Complex.exp (2 * ζ ^ 2)‖ * ‖P‖ := by
    rw [hEu, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hEubound : ‖E * cerfc u‖ * Z ^ 2 ≤ 18 / 100 := by
    have hg : ‖Complex.exp (2 * ζ ^ 2)‖ * (Real.pi * Z ^ 2) = ‖E‖ ^ 2 := by rw [hEsq]; ring
    have hgnn : (0:ℝ) ≤ ‖Complex.exp (2 * ζ ^ 2)‖ := norm_nonneg _
    rw [hEunorm]
    nlinarith [hg, hgnn, norm_nonneg P, hPn, hEub, norm_nonneg E, hZ0]
  have hkey : E - c / 2
      = ((starRingEnd ℂ) c / 2) * (E * cerfc u) + (c / 2) * (E * cerfc ζ - 1) := by
    linear_combination (E / 2) * hz
  have hfin : ‖E - c / 2‖ * Z ^ 2 ≤ 3 := by
    have h1 : ‖E - c / 2‖ ≤ ‖((starRingEnd ℂ) c / 2) * (E * cerfc u)‖
        + ‖(c / 2) * (E * cerfc ζ - 1)‖ := by
      rw [hkey]; exact norm_add_le _ _
    have h2 : ‖((starRingEnd ℂ) c / 2) * (E * cerfc u)‖ = (‖c‖ / 2) * ‖E * cerfc u‖ := by
      rw [norm_mul, norm_div, hconj]; norm_num
    have h3 : ‖(c / 2) * (E * cerfc ζ - 1)‖ = (‖c‖ / 2) * ‖E * cerfc ζ - 1‖ := by
      rw [norm_mul, norm_div]; norm_num
    rw [h2, h3] at h1
    have h4 : ‖E * cerfc ζ - 1‖ * Z ^ 2 ≤ 4 := by
      have h5 := mul_le_mul_of_nonneg_right hD (by positivity : (0:ℝ) ≤ Z ^ 2)
      calc ‖E * cerfc ζ - 1‖ * Z ^ 2 ≤ (4 / Z ^ 2) * Z ^ 2 := h5
        _ = 4 := by field_simp
    nlinarith [h1, h4, hEubound, hcub, hcnnn, norm_nonneg (E * cerfc u),
      norm_nonneg (E * cerfc ζ - 1), norm_nonneg (E - c / 2), hZ0]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < Z ^ 2)]
  exact hfin

set_option maxHeartbeats 1000000 in
-- no-dlmf: logarithmic form of the Fresnel zero equation; proof infrastructure for §7.13
/-- Logarithmic form of the Fresnel zero equation. -/
theorem fresnel_zero_log_equation {c ζ : ℂ} (hcn2 : ‖c‖ ^ 2 = 2)
    (hx : 0 < ζ.re) (hxy : ζ.re ≤ ζ.im) (hbig : 20 ≤ ‖ζ‖)
    (hz : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) :
    ∃ k : ℤ, ‖ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 7 / ‖ζ‖ ^ 2 := by
  have hsp0 : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspC : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsp0.ne'
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hx; simp at hx
  set Z : ℝ := ‖ζ‖ with hZdef
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ2 : (400:ℝ) ≤ Z ^ 2 := by nlinarith
  have hcn : ‖c‖ = Real.sqrt 2 := by rw [← hcn2, Real.sqrt_sq (norm_nonneg c)]
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hcn2; simp at hcn2
  have hc20 : c / 2 ≠ 0 := div_ne_zero hc0 (by norm_num)
  have hcn2' : ‖c / 2‖ = Real.sqrt 2 / 2 := by rw [norm_div, hcn]; norm_num
  have hcnlb : (7:ℝ) / 10 ≤ ‖c / 2‖ := by
    rw [hcn2']
    have h : (1.4:ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) with hEdef
  have hA := fresnel_zero_model_bound hcn2 hx hxy hbig hz
  rw [← hEdef, ← hZdef] at hA
  -- the exponentiated form
  set W : ℂ := ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2) with hW
  have hexpW : Complex.exp W = E / (c / 2) := by
    rw [hW, Complex.exp_sub, Complex.exp_add, Complex.exp_log (mul_ne_zero hspC hζ0),
      Complex.exp_log hc20, hEdef]
    ring
  have hd : ‖Complex.exp W - 1‖ ≤ 4.3 / Z ^ 2 := by
    have hid : Complex.exp W - 1 = (E - c / 2) / (c / 2) := by
      rw [hexpW]; field_simp
    have hAZ : ‖E - c / 2‖ * Z ^ 2 ≤ 3 := by
      have h := mul_le_mul_of_nonneg_right hA (by positivity : (0:ℝ) ≤ Z ^ 2)
      calc ‖E - c / 2‖ * Z ^ 2 ≤ (3 / Z ^ 2) * Z ^ 2 := h
        _ = 3 := by field_simp
    rw [hid, norm_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [hAZ, hcnlb]
  have hhalf : ‖Complex.exp W - 1‖ ≤ 1 / 2 := by
    refine hd.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1δ : (1 : ℂ) + (Complex.exp W - 1) = Complex.exp W := by ring
  have hlogbound : ‖Complex.log (Complex.exp W)‖ ≤ (3 / 2) * ‖Complex.exp W - 1‖ := by
    have h := Complex.norm_log_one_add_half_le_self hhalf
    rwa [h1δ] at h
  have hone : Complex.exp (W - Complex.log (Complex.exp W)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_log (Complex.exp_ne_zero W), div_self (Complex.exp_ne_zero W)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨k, ?_⟩
  have heq : W - 2 * (Real.pi : ℂ) * Complex.I * k = Complex.log (Complex.exp W) := by
    linear_combination hk
  rw [heq]
  calc ‖Complex.log (Complex.exp W)‖ ≤ (3 / 2) * ‖Complex.exp W - 1‖ := hlogbound
    _ ≤ (3 / 2) * (4.3 / Z ^ 2) := by linarith
    _ ≤ 7 / Z ^ 2 := by
          have : (3:ℝ) / 2 * (4.3 / Z ^ 2) = 6.45 / Z ^ 2 := by ring
          rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

-- no-dlmf: phase of the model constant `1 ± i`; proof infrastructure
/-- `arg c = c.im · π/4` for `c = 1 ± i`. -/
theorem fresnel_arg_c {c : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1) :
    Complex.arg c = c.im * (Real.pi / 4) := by
  have hpos : 0 < c.re := by rw [hcre]; norm_num
  have harg : Complex.arg c = Real.arctan (c.im / c.re) := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hpos)
    have h2 := abs_lt.mp h
    rw [← Complex.tan_arg c, Real.arctan_tan h2.1 h2.2]
  rw [harg, hcre, div_one]
  rcases hcim with h | h <;> rw [h]
  · rw [Real.arctan_one]; ring
  · rw [show (-1:ℝ) = -(1:ℝ) by norm_num, Real.arctan_neg, Real.arctan_one]; ring

set_option maxHeartbeats 1000000 in
-- no-dlmf: crude localization for the real form of the Fresnel zero equation; proof infrastructure
/-- Crude localization step for the Fresnel zero equation. -/
theorem fresnel713_crude {lam s d N L A : ℝ}
    (hlam : 100 ≤ lam)
    (hL : L = (1 / 2) * Real.log (2 * Real.pi * N))
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hd2s : d ^ 2 ≤ s ^ 2)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (key1 : |d * s + L| ≤ 4 / lam ^ 2)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 8 / lam ^ 2) :
    2 * lam - 1 ≤ s ∧ 2 * lam ^ 2 - 3 ≤ N ∧ |d| ≤ 1 / 5 ∧ |A| ≤ 1 / 400 ∧
      |s ^ 2 - 4 * lam ^ 2| ≤ 1 / 20 ∧ |N - 2 * lam ^ 2| ≤ 1 / 10 := by
  have hpi := Real.pi_gt_three
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have heps1 : (4:ℝ) / lam ^ 2 ≤ 1 / 2000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have heps2 : (8:ℝ) / lam ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hk1 := abs_le.mp key1
  have hk2 := abs_le.mp key2
  have hds1 : |d / s| ≤ 1 := by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    nlinarith [abs_nonneg d, sq_abs d, hd2s]
  have hAcube : |d / s| ^ 3 ≤ |d / s| := by
    have h := pow_le_pow_of_le_one (abs_nonneg (d / s)) hds1 (by norm_num : 1 ≤ 3)
    simpa using h
  have hAbd : |A| ≤ 2 := by
    have h : |A| ≤ |A - d / s| + |d / s| := by
      calc |A| = |(A - d / s) + d / s| := by ring_nf
        _ ≤ |A - d / s| + |d / s| := abs_add_le _ _
    linarith [hAT, hAcube, hds1]
  have hAb := abs_le.mp hAbd
  have hs2lb : 4 * lam ^ 2 - 5 ≤ s ^ 2 := by
    linarith only [hk2.1, sq_nonneg d, heps2, hAb.1, hAb.2]
  have hslb : 2 * lam - 1 ≤ s := by nlinarith [hs2lb, hs, hlam]
  have hs199 : (199:ℝ) ≤ s := by linarith
  have hNlb : 2 * lam ^ 2 - 3 ≤ N := by linarith only [hNsd, hs2lb, sq_nonneg d]
  have hN0 : (0:ℝ) < N := by linarith
  have hNle : N ≤ s ^ 2 := by linarith only [hNsd, hd2s]
  -- an upper bound for `L`
  have hlog2pi : Real.log (2 * Real.pi) ≤ 3.2 := by
    have h4 : Real.log (Real.sqrt (2 * Real.pi)) ≤ Real.sqrt (2 * Real.pi) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity))
    have h5 : Real.log (Real.sqrt (2 * Real.pi)) = Real.log (2 * Real.pi) / 2 :=
      Real.log_sqrt (by positivity)
    have h3 : Real.sqrt (2 * Real.pi) ≤ 2.6 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Real.sqrt_nonneg (2 * Real.pi), Real.pi_lt_d6]
    linarith
  have hLub : L ≤ s / 7 := by
    have hNs : Real.log N ≤ 2 * Real.log s := by
      have h : Real.log N ≤ Real.log (s ^ 2) := Real.log_le_log hN0 hNle
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hlogs : Real.log s ≤ s / 7 - 2 := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hs)
      rw [Real.log_sqrt hs.le] at h
      have hsq : Real.sqrt s ≤ s / 14 := by
        rw [show s / 14 = Real.sqrt ((s / 14) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      linarith
    have hsplit : Real.log (2 * Real.pi * N) = Real.log (2 * Real.pi) + Real.log N :=
      Real.log_mul (by positivity) hN0.ne'
    rw [hL, hsplit]; linarith
  have hLpos : (0:ℝ) < L := by
    have hNbig : (19997:ℝ) ≤ N := by linarith
    have h1 : (1:ℝ) < 2 * Real.pi * N := by nlinarith
    have h2 := Real.log_pos h1
    rw [hL]; linarith
  have hdabs : |d| ≤ 1 / 5 := by
    have h1 : |d * s| ≤ 4 / lam ^ 2 + L := by
      rw [abs_le]; constructor <;> linarith [hk1.1, hk1.2, hLpos]
    have h2 : |d| * s = |d * s| := by rw [abs_mul, abs_of_pos hs]
    have h3 : |d| * s ≤ s / 7 + 1 / 2000 := by rw [h2]; linarith [h1, hLub, heps1]
    nlinarith [h3, hs199, abs_nonneg d]
  have hdssmall : |d / s| ≤ 1 / 900 := by
    rw [abs_div, abs_of_pos hs, div_le_div_iff₀ hs (by norm_num)]
    nlinarith [hdabs, hs199, abs_nonneg d]
  have hAsmall : |A| ≤ 1 / 400 := by
    have h : |A| ≤ |A - d / s| + |d / s| := by
      calc |A| = |(A - d / s) + d / s| := by ring_nf
        _ ≤ |A - d / s| + |d / s| := abs_add_le _ _
    linarith [hAT, hdssmall, hAcube]
  have hd2small : d ^ 2 ≤ 1 / 25 := by nlinarith [hdabs, abs_nonneg d, sq_abs d]
  have hAs := abs_le.mp hAsmall
  have hs2m : |s ^ 2 - 4 * lam ^ 2| ≤ 1 / 20 := by
    rw [abs_le]
    constructor <;>
      [linarith only [hk2.1, hAs.1, hAs.2, hd2small, heps2, sq_nonneg d];
       linarith only [hk2.2, hAs.1, hAs.2, hd2small, heps2, sq_nonneg d]]
  have hs2 := abs_le.mp hs2m
  have hNm : |N - 2 * lam ^ 2| ≤ 1 / 10 := by
    rw [abs_le]
    constructor <;>
      [linarith only [hNsd, hs2.1, hs2.2, hd2small, sq_nonneg d];
       linarith only [hNsd, hs2.1, hs2.2, hd2small, sq_nonneg d]]
  exact ⟨hslb, hNlb, hdabs, hAsmall, hs2m, hNm⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: first-order sizes for the real form of the Fresnel zero equation; proof infrastructure
/-- The `μ`-comparison and the first-order size of `d`. -/
theorem fresnel713_first {lam mu s d N L : ℝ}
    (hlam : 100 ≤ lam) (hmulb : 5 ≤ mu) (hmub : mu + 3 ≤ lam)
    (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2))
    (hL : L = (1 / 2) * Real.log (2 * Real.pi * N))
    (hs : 0 < s) (hslb : 2 * lam - 1 ≤ s) (hNlb : 2 * lam ^ 2 - 3 ≤ N)
    (hdabs : |d| ≤ 1 / 5) (hNm : |N - 2 * lam ^ 2| ≤ 1 / 10)
    (hs2m : |s ^ 2 - 4 * lam ^ 2| ≤ 1 / 20)
    (key1 : |d * s + L| ≤ 4 / lam ^ 2) :
    |L - mu| ≤ 1 / lam ^ 2 ∧ |s - 2 * lam| ≤ 1 / (50 * lam) ∧
      |d * s + mu| ≤ 5 / lam ^ 2 ∧ |d| * (2 * lam) ≤ mu + 3 ∧
      |d + mu / (2 * lam)| ≤ 1 / lam ^ 2 := by
  have hpi := Real.pi_gt_three
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hN0 : (0:ℝ) < N := by nlinarith
  have hlam2pos : (0:ℝ) < 2 * lam ^ 2 := by positivity
  have hk1 := abs_le.mp key1
  have hNb := abs_le.mp hNm
  have hs2 := abs_le.mp hs2m
  have hs199 : (199:ℝ) ≤ s := by linarith
  -- `|s − 2λ|`
  have hsm : |s - 2 * lam| ≤ 1 / (50 * lam) := by
    have hfacs : |s - 2 * lam| * (s + 2 * lam) = |s ^ 2 - 4 * lam ^ 2| := by
      rw [← abs_of_pos (show (0:ℝ) < s + 2 * lam by linarith), ← abs_mul]
      congr 1; ring
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hfacs, hs2m, abs_nonneg (s - 2 * lam), hslb, hlam0]
  -- `|L − μ|`
  have e0 : Real.log (2 * Real.pi * N) = Real.log (2 * Real.pi) + Real.log N :=
    Real.log_mul (by positivity) hN0.ne'
  have e1 : Real.log (4 * Real.pi * lam ^ 2)
      = Real.log (2 * Real.pi) + Real.log (2 * lam ^ 2) := by
    rw [show (4:ℝ) * Real.pi * lam ^ 2 = (2 * Real.pi) * (2 * lam ^ 2) by ring]
    exact Real.log_mul (by positivity) hlam2pos.ne'
  have e2 : Real.log (N / (2 * lam ^ 2)) = Real.log N - Real.log (2 * lam ^ 2) :=
    Real.log_div hN0.ne' hlam2pos.ne'
  have e3 : Real.log ((2 * lam ^ 2) / N) = Real.log (2 * lam ^ 2) - Real.log N :=
    Real.log_div hlam2pos.ne' hN0.ne'
  have hlogeq : 2 * (L - mu) = Real.log (N / (2 * lam ^ 2)) := by
    rw [e2, hL]; linarith [e0, e1, hmu]
  have hup : Real.log (N / (2 * lam ^ 2)) ≤ N / (2 * lam ^ 2) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlo : Real.log ((2 * lam ^ 2) / N) ≤ (2 * lam ^ 2) / N - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hg1 : N / (2 * lam ^ 2) - 1 ≤ 1 / lam ^ 2 := by
    rw [div_sub_one hlam2pos.ne', div_le_div_iff₀ hlam2pos (by positivity)]
    nlinarith [hNb.2]
  have hg2 : (2 * lam ^ 2) / N - 1 ≤ 1 / lam ^ 2 := by
    rw [div_sub_one hN0.ne', div_le_div_iff₀ hN0 (by positivity)]
    nlinarith [hNb.1, hlam2]
  have hLm : |L - mu| ≤ 1 / lam ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [hlogeq, hup, hlo, hg1, hg2, e2, e3]
  have hLmb := abs_le.mp hLm
  -- `|d·s + μ|`
  have hdsmu : |d * s + mu| ≤ 5 / lam ^ 2 := by
    have h : (4:ℝ) / lam ^ 2 + 1 / lam ^ 2 = 5 / lam ^ 2 := by ring
    rw [abs_le]
    constructor <;>
      [linarith only [hk1.1, hLmb.1, hLmb.2, h]; linarith only [hk1.2, hLmb.1, hLmb.2, h]]
  have hdsmu' := abs_le.mp hdsmu
  have heps5 : (5:ℝ) / lam ^ 2 ≤ 1 / 2000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  -- `|d|·2λ ≤ μ + 3`
  have hdm : |d| * (2 * lam) ≤ mu + 3 := by
    have h2 : |d| * s = |d * s| := by rw [abs_mul, abs_of_pos hs]
    have h1 : |d * s| ≤ mu + 1 / 2000 := by
      rw [abs_le]
      constructor <;> linarith [hdsmu'.1, hdsmu'.2, heps5, hmulb]
    nlinarith [h1, h2, hslb, hdabs, abs_nonneg d]
  -- the crude expansion of `d`
  have hidd : (d + mu / (2 * lam)) * (2 * lam * s)
      = 2 * lam * (d * s + mu) + mu * (s - 2 * lam) := by field_simp; ring
  have habs1 : |d + mu / (2 * lam)| * (2 * lam * s)
      = |2 * lam * (d * s + mu) + mu * (s - 2 * lam)| := by
    rw [← hidd, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam * s)]
  have hb : |2 * lam * (d * s + mu) + mu * (s - 2 * lam)|
      ≤ 2 * lam * |d * s + mu| + mu * |s - 2 * lam| := by
    have e4 : |2 * lam * (d * s + mu)| = 2 * lam * |d * s + mu| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam)]
    have e5 : |mu * (s - 2 * lam)| = mu * |s - 2 * lam| := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < mu)]
    refine (abs_add_le _ _).trans ?_
    rw [e4, e5]
  have hb1 : 2 * lam * |d * s + mu| ≤ 10 / lam := by
    have h := mul_le_mul_of_nonneg_left hdsmu (by positivity : (0:ℝ) ≤ 2 * lam)
    have he : 2 * lam * (5 / lam ^ 2) = 10 / lam := by field_simp; ring
    linarith [h, he.le, he.ge]
  have hb2 : mu * |s - 2 * lam| ≤ 1 / 50 := by
    have h := mul_le_mul_of_nonneg_left hsm (by linarith : (0:ℝ) ≤ mu)
    have he : mu * (1 / (50 * lam)) ≤ 1 / 50 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hfinal : |d + mu / (2 * lam)| * (2 * lam * s) ≤ 10 / lam + 1 / 50 := by
    rw [habs1]; linarith [hb, hb1, hb2]
  have h10 : (10:ℝ) / lam ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hsl : (2:ℝ) * lam * (2 * lam - 1) ≤ 2 * lam * s :=
    mul_le_mul_of_nonneg_left hslb (by positivity)
  have hstep : |d + mu / (2 * lam)| * (4 * lam ^ 2 - 2 * lam) ≤ 12 / 100 := by
    nlinarith [hfinal, hsl, abs_nonneg (d + mu / (2 * lam)), h10]
  have h398 : (398:ℝ) / 100 * lam ^ 2 ≤ 4 * lam ^ 2 - 2 * lam := by nlinarith
  have hdd : |d + mu / (2 * lam)| ≤ 1 / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
    nlinarith [hstep, h398, abs_nonneg (d + mu / (2 * lam))]
  exact ⟨hLm, hsm, hdsmu, hdm, hdd⟩

-- no-dlmf: elementary size facts for `μ + 3` under `(μ+3)⁴ ≤ λ`; proof infrastructure
/-- Elementary size facts for `m = μ + 3` under `m⁴ ≤ λ`. -/
theorem fresnel713_mfacts {lam mu : ℝ} (hmulb : 5 ≤ mu) (hm4 : (mu + 3) ^ 4 ≤ lam) :
    8 ≤ mu + 3 ∧ (mu + 3) ^ 3 ≤ lam / 8 ∧ (mu + 3) ^ 2 ≤ lam / 64 ∧
      mu + 3 ≤ lam / 512 ∧ 4096 ≤ lam := by
  set m : ℝ := mu + 3 with hmdef
  have hm8 : (8:ℝ) ≤ m := by rw [hmdef]; linarith
  have hm0 : (0:ℝ) < m := by linarith
  have hlam : (4096:ℝ) ≤ lam := by
    have h : (8:ℝ) ^ 4 ≤ m ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) hm8 4
      simpa using this
    norm_num at h; linarith
  have hm3 : m ^ 3 ≤ lam / 8 := by
    nlinarith [hm4, mul_nonneg (by linarith : (0:ℝ) ≤ m - 8) (pow_pos hm0 3).le]
  have hm2 : m ^ 2 ≤ lam / 64 := by
    nlinarith [hm3, mul_nonneg (by linarith : (0:ℝ) ≤ m - 8) (pow_pos hm0 2).le]
  have hmlam : m ≤ lam / 512 := by
    nlinarith [hm2, mul_nonneg (by linarith : (0:ℝ) ≤ m - 8) hm0.le]
  exact ⟨hm8, hm3, hm2, hmlam, hlam⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: sharp sizes of `d/s`, `A`, `s²−4λ²`, `s−2λ`; proof infrastructure
/-- Sharp sizes of `d/s`, `A`, `s² − 4λ²`, `s − 2λ`. -/
theorem fresnel713_sizes {lam mu s d A : ℝ}
    (hmulb : 5 ≤ mu) (hm4 : (mu + 3) ^ 4 ≤ lam)
    (hs : 0 < s) (hslb : 2 * lam - 1 ≤ s)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (hdm : |d| * (2 * lam) ≤ mu + 3)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 8 / lam ^ 2) :
    |d / s| * lam ^ 2 ≤ mu + 3 ∧ |A| * lam ^ 2 ≤ mu + 3 ∧
      |s ^ 2 - 4 * lam ^ 2| * lam ^ 2 ≤ (mu + 3) ^ 2 ∧
      |s - 2 * lam| * (7 * lam ^ 3) ≤ 2 * (mu + 3) ^ 2 ∧
      |A - d / s| * lam ^ 5 ≤ 1 := by
  obtain ⟨hm8, hm3, hm2, hmlam, hlam⟩ := fresnel713_mfacts hmulb hm4
  set m : ℝ := mu + 3 with hmdef
  have hm0 : (0:ℝ) < m := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
  have hdnn : (0:ℝ) ≤ |d| := abs_nonneg d
  have hdsnn : (0:ℝ) ≤ |d / s| := abs_nonneg _
  have h398 : (398:ℝ) / 100 * lam ^ 2 ≤ 4 * lam ^ 2 - 2 * lam := by nlinarith
  have hdsabs : |d / s| * s = |d| := by
    rw [abs_div, abs_of_pos hs, div_mul_cancel₀ _ hs.ne']
  have hds3 : |d / s| * (4 * lam ^ 2 - 2 * lam) ≤ m := by
    have h1 : |d / s| * (2 * lam - 1) ≤ |d| := by
      rw [← hdsabs]; exact mul_le_mul_of_nonneg_left hslb (abs_nonneg _)
    nlinarith [h1, hdm, hdsnn, hlam0]
  have hdslam : |d / s| * lam ^ 2 ≤ m := by nlinarith [hds3, hdsnn, h398]
  have hds1 : |d / s| ≤ 1 := by nlinarith [hdslam, hdsnn, hmlam, hlam0, hlam2]
  have hAcube : |d / s| ^ 3 ≤ |d / s| := by
    have h := pow_le_pow_of_le_one hdsnn hds1 (by norm_num : 1 ≤ 3)
    simpa using h
  have hAub : |A| ≤ 2 * |d / s| := by
    have h : |A| ≤ |A - d / s| + |d / s| := by
      calc |A| = |(A - d / s) + d / s| := by ring_nf
        _ ≤ |A - d / s| + |d / s| := abs_add_le _ _
    linarith [hAT, hAcube]
  have hAlam : |A| * lam ^ 2 ≤ m := by
    have h := mul_le_mul_of_nonneg_right hAub (le_of_lt hlam2)
    nlinarith [h, hdslam, hdsnn, hlam2]
  -- `|s² − 4λ²|`
  have hd2 : d ^ 2 * lam ^ 2 ≤ m ^ 2 / 4 := by
    have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ |d| * (2 * lam)) hdm
    nlinarith [h, sq_abs d]
  have hk2 := abs_le.mp key2
  have hAle : A ≤ |A| := le_abs_self A
  have hAge : -|A| ≤ A := neg_abs_le A
  have hs2sharp : |s ^ 2 - 4 * lam ^ 2| * lam ^ 2 ≤ m ^ 2 := by
    have hb : |s ^ 2 - 4 * lam ^ 2| ≤ d ^ 2 + 2 * |A| + 8 / lam ^ 2 := by
      rw [abs_le]
      constructor <;>
        [linarith only [hk2.1, hAle, hAge, sq_nonneg d];
         linarith only [hk2.2, hAle, hAge, sq_nonneg d]]
    have h8 : (8:ℝ) / lam ^ 2 * lam ^ 2 = 8 := by field_simp
    have hprod := mul_le_mul_of_nonneg_right hb (le_of_lt hlam2)
    nlinarith [hprod, hd2, hAlam, h8, hm8]
  have hssharp : |s - 2 * lam| * (7 * lam ^ 3) ≤ 2 * m ^ 2 := by
    have hfacs : |s - 2 * lam| * (s + 2 * lam) = |s ^ 2 - 4 * lam ^ 2| := by
      rw [← abs_of_pos (show (0:ℝ) < s + 2 * lam by linarith), ← abs_mul]
      congr 1; ring
    have h1 : |s - 2 * lam| * (4 * lam - 1) ≤ |s ^ 2 - 4 * lam ^ 2| := by
      rw [← hfacs]
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |s - 2 * lam| * ((4 * lam - 1) * lam ^ 2) ≤ m ^ 2 := by
      have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hlam2)
      nlinarith [h3, hs2sharp]
    have h4 : (7:ℝ) * lam ^ 3 ≤ 2 * ((4 * lam - 1) * lam ^ 2) := by nlinarith
    nlinarith [h2, mul_le_mul_of_nonneg_left h4 (abs_nonneg (s - 2 * lam))]
  -- the cube bound
  have hcube5 : |A - d / s| * lam ^ 5 ≤ 1 := by
    have hc : |d / s| ^ 3 * (lam ^ 2) ^ 3 ≤ m ^ 3 := by
      have h1 : |d / s| * lam ^ 2 ≤ m := hdslam
      have hnn : (0:ℝ) ≤ |d / s| * lam ^ 2 := by positivity
      calc |d / s| ^ 3 * (lam ^ 2) ^ 3 = (|d / s| * lam ^ 2) ^ 3 := by ring
        _ ≤ m ^ 3 := by
              have := pow_le_pow_left₀ hnn h1 3
              simpa using this
    have hc' : |d / s| ^ 3 * lam ^ 6 ≤ lam / 8 := by
      have he : (lam ^ 2) ^ 3 = lam ^ 6 := by ring
      rw [he] at hc; linarith [hc, hm3]
    have hkey : (|A - d / s| * lam ^ 5) * lam ≤ 1 * lam := by
      have h1 : |A - d / s| * lam ^ 6 ≤ |d / s| ^ 3 * lam ^ 6 :=
        mul_le_mul_of_nonneg_right hAT (by positivity)
      nlinarith [h1, hc', hlam0]
    exact le_of_mul_le_mul_right hkey hlam0
  exact ⟨hdslam, hAlam, hs2sharp, hssharp, hcube5⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: sharp expansion of `x − y` at a Fresnel zero; proof infrastructure
/-- `d = −μ/(2λ) + O(λ⁻³)`. -/
theorem fresnel713_dsharp {lam mu s d : ℝ}
    (hmulb : 5 ≤ mu) (hm4 : (mu + 3) ^ 4 ≤ lam)
    (hs : 0 < s) (hslb : 2 * lam - 1 ≤ s)
    (hdsmu : |d * s + mu| ≤ 5 / lam ^ 2)
    (hssharp : |s - 2 * lam| * (7 * lam ^ 3) ≤ 2 * (mu + 3) ^ 2) :
    |d + mu / (2 * lam)| ≤ 3 / lam ^ 3 := by
  obtain ⟨hm8, hm3, hm2, hmlam, hlam⟩ := fresnel713_mfacts hmulb hm4
  set m : ℝ := mu + 3 with hmdef
  have hlam0 : (0:ℝ) < lam := by linarith
  have hidd : (d + mu / (2 * lam)) * (2 * lam * s)
      = 2 * lam * (d * s + mu) + mu * (s - 2 * lam) := by field_simp; ring
  have habs1 : |d + mu / (2 * lam)| * (2 * lam * s)
      = |2 * lam * (d * s + mu) + mu * (s - 2 * lam)| := by
    rw [← hidd, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam * s)]
  have hb : |2 * lam * (d * s + mu) + mu * (s - 2 * lam)|
      ≤ 2 * lam * |d * s + mu| + mu * |s - 2 * lam| := by
    have e4 : |2 * lam * (d * s + mu)| = 2 * lam * |d * s + mu| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * lam)]
    have e5 : |mu * (s - 2 * lam)| = mu * |s - 2 * lam| := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < mu)]
    refine (abs_add_le _ _).trans ?_
    rw [e4, e5]
  have hb1 : 2 * lam * |d * s + mu| ≤ 10 / lam := by
    have h := mul_le_mul_of_nonneg_left hdsmu (by positivity : (0:ℝ) ≤ 2 * lam)
    have he : 2 * lam * (5 / lam ^ 2) = 10 / lam := by field_simp; ring
    linarith [h, he.le, he.ge]
  have hb2 : mu * |s - 2 * lam| ≤ 1 / lam ^ 2 := by
    have h1 : mu * (|s - 2 * lam| * (7 * lam ^ 3)) ≤ mu * (2 * m ^ 2) :=
      mul_le_mul_of_nonneg_left hssharp (by linarith)
    have h2 : mu * (2 * m ^ 2) ≤ 2 * m ^ 3 := by nlinarith [sq_nonneg m, hm8]
    have h3 : mu * (|s - 2 * lam| * (7 * lam ^ 3)) ≤ lam / 4 := by linarith [h1, h2, hm3]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h3, abs_nonneg (s - 2 * lam), hlam0,
      mul_nonneg (by linarith : (0:ℝ) ≤ mu) (abs_nonneg (s - 2 * lam))]
  have hfinal : |d + mu / (2 * lam)| * (2 * lam * s) ≤ 10 / lam + 1 / lam ^ 2 := by
    rw [habs1]; linarith [hb, hb1, hb2]
  have h11 : (10:ℝ) / lam + 1 / lam ^ 2 ≤ 11 / lam := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have hsl : (2:ℝ) * lam * (2 * lam - 1) ≤ 2 * lam * s :=
    mul_le_mul_of_nonneg_left hslb (by positivity)
  have hddabs : (0:ℝ) ≤ |d + mu / (2 * lam)| := abs_nonneg _
  have h398 : (398:ℝ) / 100 * lam ^ 2 ≤ 4 * lam ^ 2 - 2 * lam := by nlinarith
  have hstep : |d + mu / (2 * lam)| * (398 / 100 * lam ^ 2) ≤ 11 / lam := by
    nlinarith [hfinal, hsl, hddabs, h11, mul_le_mul_of_nonneg_left h398 hddabs]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 3)]
  have h11l : (11:ℝ) / lam * lam ^ 2 = 11 * lam := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hstep (sq_nonneg lam)
  rw [h11l] at hmul
  have hkey : (|d + mu / (2 * lam)| * lam ^ 3) * lam ≤ 3 * lam := by nlinarith [hmul]
  exact le_of_mul_le_mul_right hkey hlam0

set_option maxHeartbeats 1200000 in
-- no-dlmf: sharp expansion of `x + y` at a Fresnel zero; proof infrastructure
/-- `s = 2λ + (μ²−2μ)/(16λ³) + O(λ⁻³)`. -/
theorem fresnel713_ssharp {lam mu s d A : ℝ}
    (hmulb : 5 ≤ mu) (hm4 : (mu + 3) ^ 4 ≤ lam)
    (hs : 0 < s) (hslb : 2 * lam - 1 ≤ s)
    (hdm : |d| * (2 * lam) ≤ mu + 3)
    (hdsharp : |d + mu / (2 * lam)| ≤ 3 / lam ^ 3)
    (hssharp : |s - 2 * lam| * (7 * lam ^ 3) ≤ 2 * (mu + 3) ^ 2)
    (hcube5 : |A - d / s| * lam ^ 5 ≤ 1)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 8 / lam ^ 2) :
    |s - (2 * lam + (mu ^ 2 - 2 * mu) / (16 * lam ^ 3))| ≤ 3 / lam ^ 3 := by
  obtain ⟨hm8, hm3, hm2, hmlam, hlam⟩ := fresnel713_mfacts hmulb hm4
  set m : ℝ := mu + 3 with hmdef
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
  have hdlam : |d| ≤ m / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]; linarith [hdm]
  -- `d² − μ²/(4λ²)`
  have hdmid : |d - mu / (2 * lam)| ≤ m / lam := by
    have h1 : |mu / (2 * lam)| ≤ m / (2 * lam) := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ mu / (2 * lam))]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h2 : |d - mu / (2 * lam)| ≤ |d| + |mu / (2 * lam)| := by
      calc |d - mu / (2 * lam)| = |d + -(mu / (2 * lam))| := by ring_nf
        _ ≤ |d| + |-(mu / (2 * lam))| := abs_add_le _ _
        _ = |d| + |mu / (2 * lam)| := by rw [abs_neg]
    have h3 : m / (2 * lam) + m / (2 * lam) = m / lam := by field_simp; ring
    linarith [h1, h2, hdlam, h3.le, h3.ge]
  have hd2diff : |d ^ 2 - mu ^ 2 / (4 * lam ^ 2)| ≤ 1 / lam ^ 2 := by
    have hid : d ^ 2 - mu ^ 2 / (4 * lam ^ 2)
        = (d + mu / (2 * lam)) * (d - mu / (2 * lam)) := by field_simp; ring
    have h := mul_le_mul hdsharp hdmid (abs_nonneg _) (by positivity)
    have he : (3 / lam ^ 3) * (m / lam) = 3 * m / lam ^ 4 := by field_simp
    have hb : (3:ℝ) * m / lam ^ 4 ≤ 1 / lam ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hmlam, hlam0, hlam, pow_pos hlam0 2, pow_pos hlam0 3, pow_pos hlam0 4]
    rw [hid, abs_mul]
    linarith [h, he.le, he.ge, hb]
  -- `2A + μ/(2λ²)`
  have hmusgap : mu * |s - 2 * lam| / (4 * lam ^ 2) ≤ 1 / lam ^ 3 := by
    have h1 : mu * (|s - 2 * lam| * (7 * lam ^ 3)) ≤ 2 * m ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hssharp (by linarith : (0:ℝ) ≤ mu)
      nlinarith [h, sq_nonneg m, hm8]
    have h2 : mu * (|s - 2 * lam| * (7 * lam ^ 3)) ≤ lam / 4 := by linarith [h1, hm3]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h2, abs_nonneg (s - 2 * lam), hlam0,
      mul_nonneg (by linarith : (0:ℝ) ≤ mu) (abs_nonneg (s - 2 * lam)), pow_pos hlam0 3]
  have hl3 : (4:ℝ) ≤ lam ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4096) hlam 3
    norm_num at h; nlinarith [h]
  have hl2 : (12:ℝ) ≤ lam ^ 2 := by nlinarith
  have hdsplus : |d / s + mu / (4 * lam ^ 2)| ≤ 3 / lam ^ 4 := by
    have hid : (d / s + mu / (4 * lam ^ 2)) * s
        = (d + mu / (2 * lam)) + mu * (s - 2 * lam) / (4 * lam ^ 2) := by
      field_simp; ring
    have h1 : |mu * (s - 2 * lam) / (4 * lam ^ 2)| ≤ 1 / lam ^ 3 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * lam ^ 2), abs_mul,
        abs_of_pos (by linarith : (0:ℝ) < mu)]
      exact hmusgap
    have h3 := abs_add_le (d + mu / (2 * lam)) (mu * (s - 2 * lam) / (4 * lam ^ 2))
    have hsub : |d / s + mu / (4 * lam ^ 2)| * s ≤ 3 / lam ^ 3 + 1 / lam ^ 3 := by
      rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs, hid]
      linarith [h1, h3, hdsharp]
    have h4 : (4:ℝ) / lam ^ 3 = 3 / lam ^ 3 + 1 / lam ^ 3 := by ring
    have hnn : (0:ℝ) ≤ |d / s + mu / (4 * lam ^ 2)| := abs_nonneg _
    have hstep : |d / s + mu / (4 * lam ^ 2)| * (2 * lam - 1) ≤ 4 / lam ^ 3 := by
      have hle := mul_le_mul_of_nonneg_left hslb hnn
      linarith [hsub, hle, h4.le, h4.ge]
    have hm3' := mul_le_mul_of_nonneg_right hstep (pow_nonneg hlam0.le 3)
    have h4' : (4:ℝ) / lam ^ 3 * lam ^ 3 = 4 := by field_simp
    rw [h4'] at hm3'
    have hcomp : (199:ℝ) / 100 * lam ^ 4 ≤ (2 * lam - 1) * lam ^ 3 := by
      nlinarith [pow_pos hlam0 3]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 4)]
    nlinarith [hm3', hcomp, hnn]
  have hAdiff : |2 * A + mu / (2 * lam ^ 2)| ≤ 1 / lam ^ 2 := by
    have hid2 : 2 * A + mu / (2 * lam ^ 2)
        = 2 * ((A - d / s) + (d / s + mu / (4 * lam ^ 2))) := by ring
    have hAsub : |A - d / s| ≤ 1 / lam ^ 5 := by
      rw [le_div_iff₀ (by positivity)]; linarith [hcube5]
    have h5 := abs_add_le (A - d / s) (d / s + mu / (4 * lam ^ 2))
    have h6a : (1:ℝ) / lam ^ 5 ≤ 1 / (4 * lam ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hl3, hlam2]
    have h6b : (3:ℝ) / lam ^ 4 ≤ 1 / (4 * lam ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hl2, hlam2]
    have h6c : (1:ℝ) / (4 * lam ^ 2) + 1 / (4 * lam ^ 2) = 1 / (2 * lam ^ 2) := by
      field_simp <;> ring
    have h6 : (1:ℝ) / lam ^ 5 + 3 / lam ^ 4 ≤ 1 / (2 * lam ^ 2) := by
      linarith [h6a, h6b, h6c.le, h6c.ge]
    rw [hid2, abs_mul, show |(2:ℝ)| = 2 by norm_num]
    have h7 : (2:ℝ) * (1 / (2 * lam ^ 2)) = 1 / lam ^ 2 := by field_simp
    linarith [h5, hAsub, hdsplus, h6, h7.le, h7.ge]
  -- assemble
  have hs2exp : |s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2)| ≤ 10 / lam ^ 2 := by
    have hid : s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2)
        = (d ^ 2 - mu ^ 2 / (4 * lam ^ 2)) + (2 * A + mu / (2 * lam ^ 2))
          + (s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2) := by field_simp; ring
    rw [hid]
    have h1 := abs_add_le ((d ^ 2 - mu ^ 2 / (4 * lam ^ 2)) + (2 * A + mu / (2 * lam ^ 2)))
      (s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2)
    have h2 := abs_add_le (d ^ 2 - mu ^ 2 / (4 * lam ^ 2)) (2 * A + mu / (2 * lam ^ 2))
    have h3 : (1:ℝ) / lam ^ 2 + 1 / lam ^ 2 + 8 / lam ^ 2 = 10 / lam ^ 2 := by ring
    linarith [h1, h2, hd2diff, hAdiff, key2, h3.le, h3.ge]
  set T : ℝ := 2 * lam + (mu ^ 2 - 2 * mu) / (16 * lam ^ 3) with hTdef
  have hmu2 : (0:ℝ) ≤ mu ^ 2 - 2 * mu := by nlinarith
  have hmu2m : mu ^ 2 - 2 * mu ≤ m ^ 2 := by nlinarith [hmdef, hmulb]
  have hT2lam : 2 * lam ≤ T := by
    have h : (0:ℝ) ≤ (mu ^ 2 - 2 * mu) / (16 * lam ^ 3) := div_nonneg hmu2 (by positivity)
    rw [hTdef]; linarith
  have hTsq : |T ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2)| ≤ 1 / lam ^ 2 := by
    have hid : T ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2)
        = ((mu ^ 2 - 2 * mu) / (16 * lam ^ 3)) ^ 2 := by rw [hTdef]; field_simp; ring
    rw [hid, abs_of_nonneg (by positivity)]
    have h3 : ((mu ^ 2 - 2 * mu) / (16 * lam ^ 3)) ^ 2 ≤ (m ^ 2 / (16 * lam ^ 3)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right hmu2m (by positivity)
    have h4 : (m ^ 2 / (16 * lam ^ 3)) ^ 2 ≤ 1 / lam ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hm2, hlam0, pow_pos hlam0 6, pow_pos hlam0 2, sq_nonneg m, hm8,
        pow_pos hlam0 4]
    linarith [h3, h4]
  have hsT : |s ^ 2 - T ^ 2| ≤ 11 / lam ^ 2 := by
    have hid : s ^ 2 - T ^ 2
        = (s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2))
          - (T ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2)) := by ring
    rw [hid]
    have h := abs_sub (s ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2))
      (T ^ 2 - 4 * lam ^ 2 - (mu ^ 2 - 2 * mu) / (4 * lam ^ 2))
    have h9 : (10:ℝ) / lam ^ 2 + 1 / lam ^ 2 = 11 / lam ^ 2 := by ring
    linarith [h, hs2exp, hTsq, h9.le, h9.ge]
  have hfacs : |s - T| * (s + T) = |s ^ 2 - T ^ 2| := by
    rw [← abs_of_pos (show (0:ℝ) < s + T by linarith), ← abs_mul]
    congr 1; ring
  have h1 : |s - T| * (4 * lam - 1) ≤ |s ^ 2 - T ^ 2| := by
    rw [← hfacs]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 3)]
  have hnn : (0:ℝ) ≤ |s - T| := abs_nonneg _
  have h2 : |s - T| * ((4 * lam - 1) * lam ^ 2) ≤ 11 := by
    have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hlam2)
    have h4 : (11:ℝ) / lam ^ 2 * lam ^ 2 = 11 := by field_simp
    nlinarith [h3, hsT, h4.le, h4.ge, hlam2]
  have hcomp : (399:ℝ) / 100 * lam ^ 3 ≤ (4 * lam - 1) * lam ^ 2 := by
    nlinarith [pow_pos hlam0 2]
  nlinarith [h2, hnn, hcomp]

set_option maxHeartbeats 1000000 in
-- no-dlmf: real and imaginary components of the Fresnel zero equation; proof infrastructure
/-- The two real component equations at a sub-diagonal Fresnel zero. -/
theorem fresnel_zero_components {c ζ : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    (hx : 0 < ζ.re) (hxy : ζ.re < ζ.im) (hbig : 20 ≤ ‖ζ‖)
    (hz : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) :
    ∃ k : ℤ,
      |(ζ.re - ζ.im) * (ζ.re + ζ.im)
          + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))|
          ≤ 7 / (ζ.re ^ 2 + ζ.im ^ 2) ∧
      |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
          - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))
          - (4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))|
          ≤ 14 / (ζ.re ^ 2 + ζ.im ^ 2) := by
  have hy : 0 < ζ.im := by linarith
  have hcn2 : ‖c‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcre]
    rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcn : ‖c‖ = Real.sqrt 2 := by rw [← hcn2, Real.sqrt_sq (norm_nonneg c)]
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcn2; simp at hcn2
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hN : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN0 : (0:ℝ) < ζ.re ^ 2 + ζ.im ^ 2 := by nlinarith
  obtain ⟨k, hk⟩ := fresnel_zero_log_equation hcn2 hx hxy.le hbig hz
  refine ⟨k, ?_, ?_⟩
  · -- real part
    have hre := (Complex.abs_re_le_norm (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
      - Complex.log (c / 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans hk
    have hsqre : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by simp [pow_two, Complex.mul_re]
    have hlogre : (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)).re
        = Real.log (Real.sqrt Real.pi * ‖ζ‖) := by
      rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have hlogc : (Complex.log (c / 2)).re = Real.log (Real.sqrt 2 / 2) := by
      rw [Complex.log_re, norm_div, hcn]; norm_num
    have hcre0 : (2 * (Real.pi : ℂ) * Complex.I * k).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have hid : Real.log (Real.sqrt Real.pi * ‖ζ‖) - Real.log (Real.sqrt 2 / 2)
        = (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2)) := by
      have hzn : (0:ℝ) < ‖ζ‖ := by linarith
      have e1 : Real.log (Real.sqrt Real.pi * ‖ζ‖)
          = (1 / 2) * Real.log (Real.pi * ‖ζ‖ ^ 2) := by
        rw [show Real.pi * ‖ζ‖ ^ 2 = (Real.sqrt Real.pi * ‖ζ‖) ^ 2 by
              rw [mul_pow, Real.sq_sqrt Real.pi_pos.le],
          Real.log_pow]
        push_cast; ring
      have e2 : Real.log (Real.sqrt 2 / 2) = -((1 / 2) * Real.log 2) := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
        ring
      have e3 : Real.log (2 * Real.pi * ‖ζ‖ ^ 2) = Real.log 2 + Real.log (Real.pi * ‖ζ‖ ^ 2) := by
        rw [show (2:ℝ) * Real.pi * ‖ζ‖ ^ 2 = 2 * (Real.pi * ‖ζ‖ ^ 2) by ring]
        exact Real.log_mul (by norm_num) (by positivity)
      rw [← hN, e1, e2, e3]; ring
    calc |(ζ.re - ζ.im) * (ζ.re + ζ.im)
            + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))|
        = |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
            - 2 * (Real.pi : ℂ) * Complex.I * k).re| := by
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, hsqre, hlogre, hlogc, hcre0, ← hid]
          congr 1; ring
      _ ≤ 7 / ‖ζ‖ ^ 2 := hre
      _ = 7 / (ζ.re ^ 2 + ζ.im ^ 2) := by rw [hN]
  · -- imaginary part
    have him := (Complex.abs_im_le_norm (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
      - Complex.log (c / 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans hk
    have hsqim : (ζ ^ 2).im = 2 * ζ.re * ζ.im := by
      simp only [pow_two, Complex.mul_im]; ring
    have hlogim : (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)).im = Complex.arg ζ := by
      rw [Complex.log_im, Complex.arg_real_mul ζ (Real.sqrt_pos.mpr Real.pi_pos)]
    have hargc : Complex.arg (c / 2) = c.im * (Real.pi / 4) := by
      have h : c / 2 = ((1 / 2 : ℝ) : ℂ) * c := by push_cast; ring
      rw [h, Complex.arg_real_mul c (by norm_num : (0:ℝ) < 1 / 2)]
      exact fresnel_arg_c hcre hcim
    have hlogcim : (Complex.log (c / 2)).im = c.im * (Real.pi / 4) := by
      rw [Complex.log_im, hargc]
    have hcim0 : (2 * (Real.pi : ℂ) * Complex.I * k).im = 2 * Real.pi * (k:ℝ) := by
      simp [Complex.mul_re, Complex.mul_im]
    have harg : Complex.arg ζ
        = Real.pi / 4 - Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) :=
      arg_eq_pi_div_four_sub_arctan hx hy
    have hcomp : (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k).im
        = 2 * ζ.re * ζ.im + (Real.pi / 4 - Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)))
          - c.im * (Real.pi / 4) - 2 * Real.pi * (k:ℝ) := by
      rw [Complex.sub_im, Complex.sub_im, Complex.add_im, hsqim, hlogim, hlogcim, hcim0, harg]
    have h2 : |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
        - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))
        - (4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))|
        = 2 * |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
            - 2 * (Real.pi : ℂ) * Complex.I * k).im| := by
      rw [hcomp, ← abs_of_pos (show (0:ℝ) < 2 by norm_num), ← abs_mul]
      congr 1; ring
    rw [h2]
    have h3 : (2:ℝ) * (7 / ‖ζ‖ ^ 2) = 14 / (ζ.re ^ 2 + ζ.im ^ 2) := by rw [hN]; ring
    calc 2 * |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
          - 2 * (Real.pi : ℂ) * Complex.I * k).im|
        ≤ 2 * (7 / ‖ζ‖ ^ 2) := by linarith [him]
      _ = 14 / (ζ.re ^ 2 + ζ.im ^ 2) := h3

set_option maxHeartbeats 1000000 in
-- no-dlmf: crude modulus localization for the Fresnel zero equation; proof infrastructure
/-- Crude modulus localization `4λ² = 2N + O(1)`: this is what converts the `N`-denominated
component bounds into the `λ`-denominated budgets of the inversion. -/
theorem fresnel713_modulus {lam s d N L A : ℝ}
    (hlam0 : 0 < lam) (hNbig : 400 ≤ N)
    (hL : L = (1 / 2) * Real.log (2 * Real.pi * N))
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hd2s : d ^ 2 ≤ s ^ 2)
    (hAbd : |A| ≤ 2)
    (key1 : |d * s + L| ≤ 7 / N)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 14 / N) :
    2 * N - 7 ≤ 4 * lam ^ 2 ∧ 4 * lam ^ 2 ≤ 2 * N + 5 ∧
      7 / N ≤ 4 / lam ^ 2 ∧ 14 / N ≤ 8 / lam ^ 2 := by
  have hpi := Real.pi_gt_three
  have hN0 : (0:ℝ) < N := by linarith
  have he1 : (7:ℝ) / N ≤ 7 / 400 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
  have he2 : (14:ℝ) / N ≤ 14 / 400 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
  have hk1 := abs_le.mp key1
  have hk2 := abs_le.mp key2
  have hAb := abs_le.mp hAbd
  have hsN : N ≤ s ^ 2 := by linarith only [hNsd, hd2s]
  have hsqrtN : Real.sqrt N ≤ s := by
    rw [show s = Real.sqrt (s ^ 2) by rw [Real.sqrt_sq hs.le]]
    exact Real.sqrt_le_sqrt hsN
  have hsqrtN20 : (20:ℝ) ≤ Real.sqrt N := by
    rw [show (20:ℝ) = Real.sqrt 400 by
      rw [show (400:ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 20)]]
    exact Real.sqrt_le_sqrt hNbig
  have hs20 : (20:ℝ) ≤ s := le_trans hsqrtN20 hsqrtN
  have hlog2pi : Real.log (2 * Real.pi) ≤ 3.2 := by
    have h4 : Real.log (Real.sqrt (2 * Real.pi)) ≤ Real.sqrt (2 * Real.pi) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity))
    have h5 : Real.log (Real.sqrt (2 * Real.pi)) = Real.log (2 * Real.pi) / 2 :=
      Real.log_sqrt (by positivity)
    have h3 : Real.sqrt (2 * Real.pi) ≤ 2.6 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Real.sqrt_nonneg (2 * Real.pi), Real.pi_lt_d6]
    linarith
  have hLub : L ≤ Real.sqrt N + 3 / 5 := by
    have hlogN : Real.log N ≤ 2 * (Real.sqrt N - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hN0)
      rw [Real.log_sqrt hN0.le] at h
      linarith
    have hsplit : Real.log (2 * Real.pi * N) = Real.log (2 * Real.pi) + Real.log N :=
      Real.log_mul (by positivity) hN0.ne'
    rw [hL, hsplit]; linarith
  have hLpos : (0:ℝ) < L := by
    have h1 : (1:ℝ) < 2 * Real.pi * N := by nlinarith
    have h2 := Real.log_pos h1
    rw [hL]; linarith
  have hdabs : |d| ≤ 11 / 10 := by
    have h1 : |d * s| ≤ 7 / N + L := by
      rw [abs_le]; constructor <;> linarith [hk1.1, hk1.2, hLpos]
    have h2 : |d| * s = |d * s| := by rw [abs_mul, abs_of_pos hs]
    have h3 : |d| * s ≤ Real.sqrt N + 3 / 5 + 7 / 400 := by rw [h2]; linarith [h1, hLub, he1]
    nlinarith [h3, hsqrtN, hsqrtN20, abs_nonneg d]
  have hd2small : d ^ 2 ≤ 6 / 5 := by nlinarith [hdabs, abs_nonneg d, sq_abs d]
  have hlow : 2 * N - 7 ≤ 4 * lam ^ 2 := by
    linarith only [hk2.2, hAb.1, hAb.2, hd2small, he2, hNsd, sq_nonneg d]
  have hhigh : 4 * lam ^ 2 ≤ 2 * N + 5 := by
    linarith only [hk2.1, hAb.1, hAb.2, hd2small, he2, hNsd, sq_nonneg d]
  refine ⟨hlow, hhigh, ?_, ?_⟩
  · rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hhigh]
  · rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hhigh]

set_option maxHeartbeats 1000000 in
-- no-dlmf: inversion of the Fresnel zero equation to `O(λ⁻³)`; proof infrastructure
/-- **The Fresnel zero expansion.**  A sub-diagonal solution of the two real component
equations at index parameter `λ` obeys `x − y = −μ/(2λ) + O(λ⁻³)` and
`x + y = 2λ + (μ²−2μ)/(16λ³) + O(λ⁻³)`. -/
theorem fresnel713_zero_expansion {lam mu s d N A : ℝ}
    (hlam : 100 ≤ lam) (hmulb : 5 ≤ mu) (hm4 : (mu + 3) ^ 4 ≤ lam)
    (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2))
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hd2s : d ^ 2 ≤ s ^ 2)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (key1 : |d * s + (1 / 2) * Real.log (2 * Real.pi * N)| ≤ 4 / lam ^ 2)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 8 / lam ^ 2) :
    |d + mu / (2 * lam)| ≤ 3 / lam ^ 3 ∧
      |s - (2 * lam + (mu ^ 2 - 2 * mu) / (16 * lam ^ 3))| ≤ 3 / lam ^ 3 := by
  obtain ⟨hm8, hm3, hm2, hmlam, hlam4096⟩ := fresnel713_mfacts hmulb hm4
  have hmub : mu + 3 ≤ lam := by linarith
  obtain ⟨hslb, hNlb, hdabs, hAsmall, hs2m, hNm⟩ :=
    fresnel713_crude hlam rfl hs hNsd hd2s hAT key1 key2
  obtain ⟨hLm, hsm, hdsmu, hdm, hdd⟩ :=
    fresnel713_first hlam hmulb hmub hmu rfl hs hslb hNlb hdabs hNm hs2m key1
  obtain ⟨-, -, -, hssharp, hcube5⟩ :=
    fresnel713_sizes hmulb hm4 hs hslb hAT hdm key2
  have hd := fresnel713_dsharp hmulb hm4 hs hslb hdsmu hssharp
  exact ⟨hd, fresnel713_ssharp hmulb hm4 hs hslb hdm hd hssharp hcube5 key2⟩

-- no-dlmf: real part of the erf-variable `ζ = ½√π(1+i)z`; proof infrastructure
/-- `Re ζ = ½√π (x − y)` for `ζ = ½√π(1+i)z`, `z = x + iy`. -/
theorem fresnel_zeta_re (w : ℂ) :
    ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w).re
      = (1 / 2) * Real.sqrt Real.pi * (w.re - w.im) := by
  simp [Complex.mul_re, Complex.mul_im]; ring

-- no-dlmf: imaginary part of the erf-variable `ζ = ½√π(1+i)z`; proof infrastructure
/-- `Im ζ = ½√π (x + y)` for `ζ = ½√π(1+i)z`, `z = x + iy`. -/
theorem fresnel_zeta_im (w : ℂ) :
    ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w).im
      = (1 / 2) * Real.sqrt Real.pi * (w.re + w.im) := by
  simp [Complex.mul_re, Complex.mul_im]; ring

-- no-dlmf: modulus of the erf-variable `ζ = ½√π(1+i)z`; proof infrastructure
/-- `‖ζ‖² = (π/2)‖z‖²` for `ζ = ½√π(1+i)z`. -/
theorem fresnel_zeta_norm_sq (w : ℂ) :
    ‖(1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w‖ ^ 2
      = (Real.pi / 2) * ‖w‖ ^ 2 := by
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [Complex.sq_norm, Complex.normSq_apply, fresnel_zeta_re, fresnel_zeta_im,
    Complex.sq_norm, Complex.normSq_apply]
  linear_combination ((w.re ^ 2 + w.im ^ 2) / 2) * hsq

-- no-dlmf: the `erfc`-form of the zero condition for `C`; proof infrastructure
/-- A zero of `C` solves `2 − (1+i)·erfc(−iζ) − (1−i)·erfc ζ = 0` with `ζ = ½√π(1+i)z`. -/
theorem cfresnelC_zero_erfc {w : ℂ} (hw : cfresnelC w = 0) :
    2 - (starRingEnd ℂ) (1 - Complex.I)
        * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
      - (1 - Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w) = 0 := by
  have h := cfresnelC_erfc_form w
  rw [hw] at h
  have hc : (starRingEnd ℂ) (1 - Complex.I) = 1 + Complex.I := by
    rw [map_sub, map_one, Complex.conj_I]; ring
  linear_combination -h
    + (-(cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w)))) * hc

-- no-dlmf: the `erfc`-form of the zero condition for `S`; proof infrastructure
/-- A zero of `S` solves `2 − (1−i)·erfc(−iζ) − (1+i)·erfc ζ = 0` with `ζ = ½√π(1+i)z`. -/
theorem cfresnelS_zero_erfc {w : ℂ} (hw : cfresnelS w = 0) :
    2 - (starRingEnd ℂ) (1 + Complex.I)
        * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
      - (1 + Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w) = 0 := by
  have h := cfresnelS_erfc_form w
  rw [hw] at h
  have hc : (starRingEnd ℂ) (1 + Complex.I) = 1 - Complex.I := by
    rw [map_add, map_one, Complex.conj_I]; ring
  linear_combination -h
    + (-(cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w)))) * hc

/-! ### Fresnel zeros — existence and separation

The model roots of `√π ζ e^{ζ²} = c/2`, their transfer to genuine zeros of the Fresnel
zero equation by the minimum-modulus criterion, and the local uniqueness (separation)
of the sub-diagonal Fresnel zeros. -/

-- no-dlmf: modulus of the model function `E(z) = √π z e^{z²}`; proof infrastructure
/-- `‖√π z e^{z²}‖ = √π ‖z‖ exp (Re z²)`. -/
theorem fresnelE_norm (z : ℂ) :
    ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖
      = Real.sqrt Real.pi * ‖z‖ * Real.exp ((z ^ 2).re) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]

set_option maxHeartbeats 1000000 in
-- no-dlmf: remainder bound for the Fresnel model equation; proof infrastructure
/-- The Fresnel zero function `G = 2 − c̄ erfc(−iζ) − c erfc ζ` satisfies
`½·E·G = (E − c/2) − R` with `‖R‖ ≤ (B²/2 + 3)/‖ζ‖²` whenever `‖E‖ ≤ B`, `E = √π ζ e^{ζ²}`. -/
theorem fresnel_rem_bound {c ζ : ℂ} (hcn2 : ‖c‖ ^ 2 = 2)
    (hx : 0 < ζ.re) (hy : 0 < ζ.im) (hbig : 20 ≤ ‖ζ‖) {B : ℝ}
    (hB : ‖(Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2)‖ ≤ B) :
    ‖((Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) - c / 2)
        - (1 / 2) * ((Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2))
            * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ)‖
      ≤ (B ^ 2 / 2 + 3) / ‖ζ‖ ^ 2 := by
  have hpi3 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hsp0 : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set Z : ℝ := ‖ζ‖ with hZdef
  have hZ0 : (0:ℝ) < Z := by linarith
  have hZ2 : (400:ℝ) ≤ Z ^ 2 := by nlinarith
  set u : ℂ := -Complex.I * ζ with hudef
  have hure : u.re = ζ.im := by simp [hudef, Complex.mul_re]
  have hun : ‖u‖ = Z := by rw [hudef, norm_mul]; simp [hZdef]
  have huy : 0 < u.re := by rw [hure]; exact hy
  have husq : u ^ 2 = -ζ ^ 2 := by rw [hudef]; linear_combination (ζ ^ 2) * Complex.I_sq
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) with hEdef
  set P : ℂ := (Real.sqrt Real.pi : ℂ) * u * Complex.exp (u ^ 2) * cerfc u with hPdef
  have hP : ‖P - 1‖ ≤ 4 / Z ^ 2 := by
    have h := cerfc_scaled_unit_bound huy
    rwa [hun] at h
  have hX : ‖E * cerfc ζ - 1‖ ≤ 4 / Z ^ 2 := cerfc_scaled_unit_bound hx
  have hsmall : (4:ℝ) / Z ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hPn : ‖P‖ ≤ 101 / 100 := by
    have h := norm_sub_norm_le P 1
    simp only [norm_one] at h
    linarith [hP, hsmall]
  have hcnnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hcub : ‖c‖ ≤ 1.4143 := by nlinarith
  have hconj : ‖(starRingEnd ℂ) c‖ = ‖c‖ := RCLike.norm_conj c
  -- the exponential factor
  have hEsq : ‖E‖ ^ 2 = Real.pi * Z ^ 2 * ‖Complex.exp (2 * ζ ^ 2)‖ := by
    have h2 : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
      norm_cast
      exact Real.sq_sqrt Real.pi_pos.le
    have h3 : Complex.exp (ζ ^ 2) ^ 2 = Complex.exp (2 * ζ ^ 2) := by
      rw [← Complex.exp_nat_mul]; norm_num
    have h1 : E ^ 2 = (Real.pi : ℂ) * ζ ^ 2 * Complex.exp (2 * ζ ^ 2) := by
      rw [hEdef, ← h3, ← h2]; ring
    rw [← norm_pow, h1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_pow, ← hZdef]
  have hexpid : Complex.exp (2 * ζ ^ 2) * Complex.exp (u ^ 2) = Complex.exp (ζ ^ 2) := by
    rw [← Complex.exp_add, husq]; congr 1; ring
  have hIu : Complex.I * u = ζ := by rw [hudef]; linear_combination (-ζ) * Complex.I_sq
  have hEu : E * cerfc u = Complex.I * Complex.exp (2 * ζ ^ 2) * P := by
    calc E * cerfc u
        = (Complex.I * u) * (Real.sqrt Real.pi : ℂ) * Complex.exp (ζ ^ 2) * cerfc u := by
          rw [hIu, hEdef]; ring
      _ = Complex.I * Complex.exp (2 * ζ ^ 2) * P := by rw [hPdef, ← hexpid]; ring
  have hEunorm : ‖E * cerfc u‖ = ‖Complex.exp (2 * ζ ^ 2)‖ * ‖P‖ := by
    rw [hEu, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hB0 : (0:ℝ) ≤ B := le_trans (norm_nonneg _) hB
  have hEB : ‖E‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg E]
  have hYb : ‖E * cerfc u‖ * Z ^ 2 ≤ B ^ 2 / 3 := by
    have hgnn : (0:ℝ) ≤ ‖Complex.exp (2 * ζ ^ 2)‖ := norm_nonneg _
    have hg : ‖Complex.exp (2 * ζ ^ 2)‖ * (Real.pi * Z ^ 2) = ‖E‖ ^ 2 := by rw [hEsq]; ring
    rw [hEunorm]
    nlinarith [hg, hgnn, norm_nonneg P, hPn, hEB, hZ0]
  -- the algebraic identity
  have hkey : (E - c / 2) - (1 / 2) * E * (2 - (starRingEnd ℂ) c * cerfc u - c * cerfc ζ)
      = ((starRingEnd ℂ) c / 2) * (E * cerfc u) + (c / 2) * (E * cerfc ζ - 1) := by
    ring
  rw [hkey]
  have hna : ‖((starRingEnd ℂ) c / 2) * (E * cerfc u)‖ = (‖c‖ / 2) * ‖E * cerfc u‖ := by
    rw [norm_mul, norm_div, hconj]; norm_num
  have hnb : ‖(c / 2) * (E * cerfc ζ - 1)‖ = (‖c‖ / 2) * ‖E * cerfc ζ - 1‖ := by
    rw [norm_mul, norm_div]; norm_num
  have h1 := norm_add_le (((starRingEnd ℂ) c / 2) * (E * cerfc u))
    ((c / 2) * (E * cerfc ζ - 1))
  rw [hna, hnb] at h1
  rw [le_div_iff₀ (by positivity : (0:ℝ) < Z ^ 2)]
  have hXZ : ‖E * cerfc ζ - 1‖ * Z ^ 2 ≤ 4 := by
    have h5 := mul_le_mul_of_nonneg_right hX (by positivity : (0:ℝ) ≤ Z ^ 2)
    calc ‖E * cerfc ζ - 1‖ * Z ^ 2 ≤ (4 / Z ^ 2) * Z ^ 2 := h5
      _ = 4 := by field_simp
  nlinarith [h1, hXZ, hYb, hcub, hcnnn, norm_nonneg (E * cerfc u),
    norm_nonneg (E * cerfc ζ - 1), hZ0, sq_nonneg B]

set_option maxHeartbeats 1000000 in
-- no-dlmf: existence of the roots of the shifted model equation `√π ζ e^{ζ²} = e^κ`
/-- **Existence of the Fresnel model roots.**  For `‖κ‖ ≤ 1` and every `n ≥ 134` the model
equation `√π · ζ · e^{ζ²} = e^κ` has a solution `ζ` in the open sub-diagonal sector. -/
theorem exists_model_root_fresnel {κ : ℂ} (hκ : ‖κ‖ ≤ 1) (n : ℕ) (hn : 134 ≤ n) :
    ∃ ζ : ℂ, 20 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 6 * ζ.re ∧ ‖ζ‖ ≤ 6 * ζ.im ∧ ζ.re < ζ.im ∧
      ‖ζ ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n‖ ≤ Real.pi * n ∧
      ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - κ
        = 2 * (Real.pi : ℂ) * Complex.I * n ∧
      (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) = Complex.exp κ := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hn' : (134:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  set M : ℝ := 2 * Real.pi * n with hMdef
  have hMbig : (800:ℝ) ≤ M := by
    have h3 := Real.pi_gt_three
    rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  set c : ℂ := (M : ℂ) * Complex.I with hcdef
  have hcim : c.im = M := by simp [hcdef]
  have hcre : c.re = 0 := by simp [hcdef]
  have hcnorm : ‖c‖ = M := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hM0]
  set a : ℝ := Real.log (Real.sqrt Real.pi) with hadef
  have ha0 : 0 ≤ a := by
    rw [hadef]
    refine Real.log_nonneg ?_
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have ha1 : a ≤ 1 := by
    have h1 : Real.sqrt Real.pi ≤ 2 := by
      have h4 : Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
      rwa [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
    have h2 := Real.log_le_sub_one_of_pos hsppos
    rw [hadef]; linarith
  have hκre : |κ.re| ≤ 1 := le_trans (Complex.abs_re_le_norm κ) hκ
  set T : ℂ → ℂ := fun u => c + κ - (a : ℂ) - (1/2) * Complex.log u with hTdef
  set s : Set ℂ := Metric.closedBall c (M/2) with hsdef
  have hmem : ∀ u ∈ s, M/2 ≤ u.im ∧ M/2 ≤ ‖u‖ ∧ ‖u‖ ≤ 3*M/2 ∧ u ≠ 0 := by
    intro u hu
    have hd : ‖u - c‖ ≤ M/2 := by rwa [hsdef, Metric.mem_closedBall, dist_eq_norm] at hu
    have him : |u.im - c.im| ≤ M/2 := by
      have h := Complex.abs_im_le_norm (u - c)
      simp only [Complex.sub_im] at h; linarith
    rw [hcim] at him
    have h1 := abs_le.mp him
    have h2 := norm_sub_norm_le u c
    have h3 := norm_sub_norm_le c u
    rw [norm_sub_rev c u] at h3
    rw [hcnorm] at h2 h3
    refine ⟨by linarith [h1.1], by linarith, by linarith, ?_⟩
    intro h; rw [h] at h1; simp at h1; linarith [h1.1]
  have hsconv : Convex ℝ s := by rw [hsdef]; exact convex_closedBall c (M/2)
  have hmaps : Set.MapsTo T s s := by
    intro u hu
    obtain ⟨him, hn1, hn2, hu0⟩ := hmem u hu
    rw [hsdef, Metric.mem_closedBall, dist_eq_norm]
    have hTc : T u - c = κ - ((a:ℂ) + (1/2) * Complex.log u) := by rw [hTdef]; ring
    rw [hTc]
    have h0 : ‖κ - ((a:ℂ) + (1/2) * Complex.log u)‖
        ≤ ‖κ‖ + ‖(a:ℂ) + (1/2) * Complex.log u‖ := norm_sub_le _ _
    have h1 : ‖(a:ℂ) + (1/2) * Complex.log u‖ ≤ a + (1/2) * ‖Complex.log u‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
      have : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      rw [this]
    have h2 : ‖Complex.log u‖ ≤ |Real.log ‖u‖| + Real.pi := by
      have h := Complex.norm_le_abs_re_add_abs_im (Complex.log u)
      rw [Complex.log_re, Complex.log_im] at h
      have h4 := Complex.abs_arg_le_pi u
      linarith
    have hu1 : (1:ℝ) ≤ ‖u‖ := by linarith
    have habs : |Real.log ‖u‖| = Real.log ‖u‖ := abs_of_nonneg (Real.log_nonneg hu1)
    have h3 : Real.log ‖u‖ ≤ 2 * (Real.sqrt ‖u‖ - 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < ‖u‖))
      rw [Real.log_sqrt (by linarith)] at h
      linarith
    have h5 : Real.sqrt ‖u‖ ≤ Real.sqrt (3*M/2) := Real.sqrt_le_sqrt hn2
    have h6 : Real.sqrt (3*M/2) ≤ M/2 - 4 := by
      have h7 : Real.sqrt (3*M/2) ≤ Real.sqrt ((M/2-4)^2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h7
    rw [habs] at h2
    linarith [Real.pi_lt_four]
  have hlip : LipschitzOnWith (Real.toNNReal (1/M)) T s := by
    refine LipschitzOnWith.of_dist_le' (fun u hu u' hu' => ?_)
    have hlogd : ‖Complex.log u' - Complex.log u‖ ≤ (2/M) * ‖u' - u‖ := by
      refine norm_sub_le_of_hasDerivAt_le (f := Complex.log) (f' := fun z => z⁻¹)
        hsconv ?_ ?_ hu hu'
      · intro y hy
        obtain ⟨hyim, -, -, hy0⟩ := hmem y hy
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inr (by
          intro h; rw [h] at hyim; linarith)))
      · intro y hy
        obtain ⟨-, hyn, -, hy0⟩ := hmem y hy
        rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hM0]
        linarith
    have hTd : T u - T u' = -((1/2) * (Complex.log u - Complex.log u')) := by rw [hTdef]; ring
    rw [dist_eq_norm, hTd, norm_neg, norm_mul, dist_eq_norm]
    have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
    have h2 : ‖Complex.log u - Complex.log u'‖ = ‖Complex.log u' - Complex.log u‖ :=
      norm_sub_rev _ _
    have h3 : ‖u' - u‖ = ‖u - u'‖ := norm_sub_rev _ _
    rw [h1, h2]
    rw [h3] at hlogd
    have h4 : (1/2:ℝ) * ‖Complex.log u' - Complex.log u‖
        ≤ (1/2) * (2/M * ‖u - u'‖) := by linarith
    have hfin : (1/2 : ℝ) * (2/M * ‖u - u'‖) = 1/M * ‖u - u'‖ := by field_simp
    rw [hfin] at h4
    exact h4
  have hK : Real.toNNReal (1/M) < 1 := by
    rw [show (1 : NNReal) = Real.toNNReal 1 by simp]
    exact (Real.toNNReal_lt_toNNReal_iff one_pos).mpr (by rw [div_lt_one hM0]; linarith)
  obtain ⟨u, hus, hufix, -⟩ := ContractingWith.exists_fixedPoint' (f := T)
    (Metric.isClosed_closedBall.isComplete) hmaps ⟨hK, hlip.mapsToRestrict hmaps⟩
    (Metric.mem_closedBall_self (by linarith)) (edist_ne_top _ _)
  obtain ⟨huim, hun1, hun2, hu0⟩ := hmem u hus
  -- the real part of the fixed point is negative: the model root is sub-diagonal
  have hlogu3 : (3:ℝ) ≤ Real.log ‖u‖ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have hp := Real.exp_pos 1
    nlinarith [h, hp, hMbig, hun1]
  have hwre : ((1/2 : ℂ) * Complex.log u).re = Real.log ‖u‖ / 2 := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im]
    norm_num
    ring
  have hure : u.re = κ.re - a - Real.log ‖u‖ / 2 := by
    have h : c + κ - (a : ℂ) - (1/2) * Complex.log u = u := hufix
    have h2 := congrArg Complex.re h
    rw [Complex.sub_re, Complex.sub_re, Complex.add_re, hcre, hwre,
      Complex.ofReal_re] at h2
    linarith [h2]
  have hureneg : u.re ≤ -1/2 := by
    have := abs_le.mp hκre
    linarith [this.2, ha0, hlogu3]
  set v : ℂ := Complex.exp ((1/2) * Complex.log u) with hvdef
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have hvsq : v ^ 2 = u := by
    rw [hvdef, pow_two, ← Complex.exp_add,
      show (1/2:ℂ) * Complex.log u + (1/2:ℂ) * Complex.log u = Complex.log u by ring,
      Complex.exp_log hu0]
  have hargpos : 0 < Complex.arg u := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr (by linarith : 0 ≤ u.im)) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h.symm
      linarith [this.2]
  have harglt : Complex.arg u < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi u) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_pi_iff.mp h
      linarith [this.2]
  have hwim : ((1/2 : ℂ) * Complex.log u).im = Complex.arg u / 2 := by
    simp [Complex.mul_im, Complex.log_im, Complex.log_re]
    ring
  have hvre : 0 < v.re := by
    rw [hvdef, Complex.exp_re, hwim]
    have := Real.cos_pos_of_mem_Ioo (x := Complex.arg u / 2) ⟨by linarith, by linarith⟩
    positivity
  have hvim : 0 < v.im := by
    rw [hvdef, Complex.exp_im, hwim]
    have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg u / 2) (by linarith) (by linarith)
    positivity
  have hvnormsq : ‖v‖ ^ 2 = ‖u‖ := by rw [← hvsq, ← norm_pow]
  have hvnorm : 20 ≤ ‖v‖ := by nlinarith [norm_nonneg v, hvnormsq, hun1]
  have hvim_le : v.im ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm v)
  have himid : u.im = 2 * v.re * v.im := by
    rw [← hvsq, pow_two, Complex.mul_im]; ring
  have hvnormpos : (0:ℝ) < ‖v‖ := by linarith
  have hprod : M/2 ≤ 2 * v.re * v.im := by rw [← himid]; exact huim
  have hvsqub : ‖v‖ ^ 2 ≤ 3*M/2 := by rw [hvnormsq]; exact hun2
  have hvre6 : ‖v‖ ≤ 6 * v.re := by
    nlinarith [hprod, hvsqub, hvnormpos, hvim_le, hvre.le]
  have hvre_le : v.re ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm v)
  have hvim6 : ‖v‖ ≤ 6 * v.im := by
    nlinarith [hprod, hvsqub, hvnormpos, hvre_le, hvim.le]
  have hsub : v.re < v.im := by
    have hsqre : (v ^ 2).re = v.re ^ 2 - v.im ^ 2 := by simp [pow_two, Complex.mul_re]
    have h : v.re ^ 2 - v.im ^ 2 = u.re := by rw [← hsqre, hvsq]
    nlinarith [hureneg, hvre, hvim]
  have hlogv : Complex.log v = (1/2) * Complex.log u := by
    rw [hvdef]
    exact Complex.log_exp (by rw [hwim]; linarith) (by rw [hwim]; linarith)
  have hkey : v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v) - κ = c := by
    rw [Complex.log_ofReal_mul hsppos hv0, hlogv, hvsq]
    have : T u = u := hufix
    rw [hTdef] at this
    simp only at this
    rw [← hadef]
    linear_combination -this
  have hmodel : (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) = Complex.exp κ := by
    have h1 : Complex.exp (v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v))
        = (Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) := by
      rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hv0)]; ring
    have h3 : v ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * v) = κ + c := by
      linear_combination hkey
    rw [← h1, h3, Complex.exp_add]
    have h2 : c = (n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hcdef, hMdef]; push_cast; ring
    rw [h2, Complex.exp_int_mul_two_pi_mul_I n, mul_one]
  have hceq : c = 2 * (Real.pi : ℂ) * Complex.I * n := by
    rw [hcdef, hMdef]; push_cast; ring
  refine ⟨v, hvnorm, hvre6, hvim6, hsub, ?_, by rw [hkey, hceq], hmodel⟩
  have h3 : v ^ 2 - 2 * (Real.pi : ℂ) * Complex.I * n = u - c := by
    rw [hvsq, hcdef, hMdef]; push_cast; ring
  rw [h3]
  have := Metric.mem_closedBall.mp hus
  rw [dist_eq_norm] at this
  rw [hMdef] at this
  linarith [this]

set_option maxHeartbeats 1600000 in
-- no-dlmf: transfer of an exact Fresnel model root to a genuine zero of the Fresnel
-- zero function; proof infrastructure
/-- **From a Fresnel model root to a genuine zero.**  If `ζ₀` solves `√π ζ e^{ζ²} = c/2`
exactly, with `1 ≤ Re ζ₀`, `1 ≤ Im ζ₀` and `‖ζ₀‖ ≥ 25`, then the Fresnel zero equation
`2 − c̄ erfc(−iζ) − c erfc ζ = 0` has a solution within `12/‖ζ₀‖³` of `ζ₀`. -/
theorem exists_fresnel_zero_near_model {c ζ₀ : ℂ} (hcn2 : ‖c‖ ^ 2 = 2)
    (hre : 1 ≤ ζ₀.re) (him : 1 ≤ ζ₀.im) (hbig : 25 ≤ ‖ζ₀‖)
    (hmodel : (Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2) = c / 2) :
    ∃ ζ : ℂ, 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0 ∧
      ‖ζ - ζ₀‖ < 12 / ‖ζ₀‖ ^ 3 := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hcnnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hcub : ‖c‖ ≤ 1.4143 := by nlinarith
  have hclb : (1.414:ℝ) ≤ ‖c‖ := by nlinarith
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcn2; simp at hcn2
  have hc2 : ‖c / 2‖ = ‖c‖ / 2 := by rw [norm_div]; norm_num
  set V : ℝ := ‖ζ₀‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hV2 : (625:ℝ) ≤ V ^ 2 := by nlinarith
  have hV3 : (15625:ℝ) ≤ V ^ 3 := by nlinarith
  have hρsmall : ρ ≤ 1/1000 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hA : ρ * V = 12 / V ^ 2 := by rw [hρdef]; field_simp
  have hAsmall : ρ * V ≤ 1/50 := by
    rw [hA, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hρVpos : (0:ℝ) < ρ * V := mul_pos hρ0 hV0
  have hmem : ∀ z ∈ Metric.closedBall ζ₀ ρ,
      0 < z.re ∧ 0 < z.im ∧ V - ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + ρ := by
    intro z hz
    have hzv : ‖z - ζ₀‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre' : |z.re - ζ₀.re| ≤ ρ := by
      have h := Complex.abs_re_le_norm (z - ζ₀)
      simp only [Complex.sub_re] at h; linarith
    have him' : |z.im - ζ₀.im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (z - ζ₀)
      simp only [Complex.sub_im] at h; linarith
    have h1 := abs_le.mp hre'
    have h2 := abs_le.mp him'
    refine ⟨by linarith [h1.1], by linarith [h2.1], ?_, ?_⟩
    · have h3 := norm_sub_norm_le ζ₀ z
      rw [norm_sub_rev ζ₀ z] at h3; linarith
    · have h3 := norm_sub_norm_le z ζ₀; linarith
  have hVρ : (24:ℝ) ≤ V - ρ := by linarith
  have hlogmvt : ∀ z ∈ Metric.closedBall ζ₀ ρ,
      ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)‖ ≤ (1 / (V - ρ)) * ‖z - ζ₀‖ := by
    intro z hz
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
      (convex_closedBall ζ₀ ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hz
    · intro y hy
      obtain ⟨hy1, -, hy2, -⟩ := hmem y hy
      have hslit : ((Real.sqrt Real.pi : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
          ((Real.sqrt Real.pi : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt Real.pi : ℂ))
      exact h1.clog hslit
    · intro y hy
      obtain ⟨-, -, hy2, -⟩ := hmem y hy
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hsppos]
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        = (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hz0)]; ring
  have hζ₀re : 0 < ζ₀.re := by linarith
  have hgv : Complex.exp (ζ₀ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)) = c / 2 := by
    rw [hexpg ζ₀ hζ₀re]; exact hmodel
  -- the model/remainder split at a point of the closed ball
  have hEcomp : ∀ z ∈ Metric.closedBall ζ₀ ρ,
      ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2‖ ≥ 0 ∧
      ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
        = (c / 2) * Complex.exp ((z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
            - (ζ₀ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))) := by
    intro z hz
    obtain ⟨hzre, -, -, -⟩ := hmem z hz
    refine ⟨norm_nonneg _, ?_⟩
    rw [Complex.exp_sub, hgv, hexpg z hzre]
    field_simp
  have hdbound : ∀ z ∈ Metric.closedBall ζ₀ ρ,
      ‖(z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        - (ζ₀ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))‖ ≤ 2.01 * (ρ * V) := by
    intro z hz
    have hzv : ‖z - ζ₀‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    obtain ⟨-, -, -, hzn2⟩ := hmem z hz
    have hsplit : (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        - (ζ₀ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))
        = (z - ζ₀) * (z + ζ₀)
          + (Complex.log ((Real.sqrt Real.pi : ℂ) * z)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)) := by ring
    have hlog := hlogmvt z hz
    have hlog' : (1 / (V - ρ)) * ‖z - ζ₀‖ ≤ ρ / 24 := by
      have h1 : (1:ℝ) / (V - ρ) ≤ 1 / 24 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hVρ
      calc (1 / (V - ρ)) * ‖z - ζ₀‖ ≤ (1/24) * ρ :=
            mul_le_mul h1 hzv (norm_nonneg _) (by norm_num)
        _ = ρ / 24 := by ring
    have hzpv : ‖z + ζ₀‖ ≤ 2 * V + ρ := by
      have h1 := norm_add_le z ζ₀; linarith
    have hprodnorm : ‖(z - ζ₀) * (z + ζ₀)‖ ≤ ρ * (2 * V + ρ) := by
      rw [norm_mul]; exact mul_le_mul hzv hzpv (norm_nonneg _) hρ0.le
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hslack : ρ * (2 * V + ρ) + ρ / 24 ≤ 2.01 * (ρ * V) := by nlinarith
    linarith
  have hsphere : ∀ z ∈ Metric.sphere ζ₀ ρ,
      ‖(1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ₀) - c * cerfc ζ₀)‖
        < ‖(1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z)‖ := by
    intro z hz
    have hzv : ‖z - ζ₀‖ = ρ := by rwa [Metric.mem_sphere, dist_eq_norm] at hz
    have hzcb : z ∈ Metric.closedBall ζ₀ ρ := Metric.sphere_subset_closedBall hz
    obtain ⟨hzre, hzim, hzn1, hzn2⟩ := hmem z hzcb
    have hz20 : (20:ℝ) ≤ ‖z‖ := by linarith
    have hdle := hdbound z hzcb
    have hEz := (hEcomp z hzcb).2
    set d : ℂ := (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      - (ζ₀ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)) with hd
    have hdsmall : ‖d‖ ≤ 1/10 := hdle.trans (by linarith [hAsmall, hρVpos])
    -- lower bound for the model, upper bound for `‖E z‖`
    have hexpb := Complex.norm_exp_sub_one_sub_id_le (x := d) (by linarith)
    have hup : ‖Complex.exp d - 1‖ ≤ ‖d‖ + ‖d‖ ^ 2 := by
      have h5 := norm_sub_norm_le (Complex.exp d - 1) d
      linarith [h5, hexpb]
    have hlo : ‖d‖ - ‖d‖ ^ 2 ≤ ‖Complex.exp d - 1‖ := by
      have h5 := norm_sub_norm_le d (Complex.exp d - 1)
      rw [norm_sub_rev d (Complex.exp d - 1)] at h5
      have h6 : (Complex.exp d - 1) - d = Complex.exp d - 1 - d := by ring
      rw [h6] at h5
      linarith [h5, hexpb]
    have hdsq : ‖d‖ ^ 2 ≤ ‖d‖ / 10 := by
      calc ‖d‖ ^ 2 = ‖d‖ * ‖d‖ := by ring
        _ ≤ ‖d‖ * (1/10) := mul_le_mul_of_nonneg_left hdsmall (norm_nonneg d)
        _ = ‖d‖ / 10 := by ring
    have hEnorm : ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖ ≤ 1 := by
      rw [hEz, norm_mul, hc2]
      have h1 : ‖Complex.exp d‖ ≤ 1 + ‖d‖ + ‖d‖ ^ 2 := by
        have h2 := norm_sub_norm_le (Complex.exp d) 1
        simp only [norm_one] at h2
        linarith [hup]
      nlinarith [h1, hcub, hcnnn, norm_nonneg d, hdsmall, hdsq, norm_nonneg (Complex.exp d)]
    have hΦlow : 1.266 * (ρ * V)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2‖ := by
      have hid : (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2
          = (c / 2) * (Complex.exp d - 1) := by rw [hEz]; ring
      rw [hid, norm_mul, hc2]
      have hdlow : 1.99 * (ρ * V) ≤ ‖d‖ := by
        have hsplit : d = (z - ζ₀) * (z + ζ₀)
            + (Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)) := by rw [hd]; ring
        have hlogb := hlogmvt z hzcb
        rw [hzv] at hlogb
        have hlogb' : (1 / (V - ρ)) * ρ ≤ ρ / 24 := by
          rw [div_mul_eq_mul_div, one_mul]
          exact div_le_div_of_nonneg_left hρ0.le (by norm_num) hVρ
        have hzpv : 2 * V - ρ ≤ ‖z + ζ₀‖ := by
          have h1 : ‖(2:ℂ) * ζ₀‖ ≤ ‖z + ζ₀‖ + ‖z - ζ₀‖ := by
            calc ‖(2:ℂ) * ζ₀‖ = ‖(z + ζ₀) - (z - ζ₀)‖ := by congr 1; ring
              _ ≤ ‖z + ζ₀‖ + ‖z - ζ₀‖ := norm_sub_le _ _
          have h2 : ‖(2:ℂ) * ζ₀‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
          rw [h2, hzv] at h1; linarith only [h1]
        have h0 : ‖(z - ζ₀) * (z + ζ₀)‖
            - ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)‖ ≤ ‖d‖ := by
          have hh : ‖(z - ζ₀) * (z + ζ₀)‖ ≤ ‖d‖
              + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)‖ := by
            calc ‖(z - ζ₀) * (z + ζ₀)‖
                = ‖d - (Complex.log ((Real.sqrt Real.pi : ℂ) * z)
                    - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))‖ := by
                  congr 1; rw [hsplit]; ring
              _ ≤ _ := norm_sub_le _ _
          linarith only [hh]
        have hpn : ‖(z - ζ₀) * (z + ζ₀)‖ = ρ * ‖z + ζ₀‖ := by rw [norm_mul, hzv]
        rw [hpn] at h0
        have hmul : ρ * (2 * V - ρ) ≤ ρ * ‖z + ζ₀‖ := mul_le_mul_of_nonneg_left hzpv hρ0.le
        nlinarith [h0, hmul, hlogb, hlogb', hρsmall, hρ0, hV0]
      nlinarith [hlo, hdsq, hclb, hdlow, hρVpos]
    have hRz := fresnel_rem_bound hcn2 hzre hzim hz20 hEnorm
    have hRsmall : ‖((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2)
        - (1 / 2) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
            * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z)‖
        ≤ 0.298 * (ρ * V) := by
      refine hRz.trans ?_
      rw [show ((1:ℝ) ^ 2 / 2 + 3) = 3.5 by norm_num, hA,
        show (0.298:ℝ) * (12 / V ^ 2) = 3.576 / V ^ 2 by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hzn1, hV0, hρsmall, hV2, norm_nonneg z]
    have hFlow : 0.968 * (ρ * V)
        ≤ ‖(1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z)‖ := by
      have h1 := norm_sub_norm_le ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2)
        ((1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z))
      have h2 : ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2)
          - (1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
            * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z)
          = ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2)
        - (1 / 2) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
            * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z) := by ring
      rw [h2] at h1
      linarith [h1, hRsmall, hΦlow]
    -- the value at the model root
    have hE0 : ‖(Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2)‖ ≤ 1 := by
      rw [hmodel, hc2]; linarith
    have hR0 := fresnel_rem_bound hcn2 hζ₀re (by linarith : 0 < ζ₀.im) (by linarith) hE0
    have hFhigh : ‖(1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ₀) - c * cerfc ζ₀)‖
        ≤ 0.292 * (ρ * V) := by
      have hz0 : ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2) - c / 2) = 0 := by
        rw [hmodel]; ring
      have h3 : ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2) - c / 2)
          - (1 / 2) * ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2))
              * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ₀) - c * cerfc ζ₀)
          = -((1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * ζ₀ * Complex.exp (ζ₀ ^ 2))
              * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ₀) - c * cerfc ζ₀)) := by
        rw [hz0]; ring
      rw [h3, norm_neg] at hR0
      refine hR0.trans ?_
      rw [show ((1:ℝ) ^ 2 / 2 + 3) = 3.5 by norm_num, ← hVdef, hA,
        show (0.292:ℝ) * (12 / V ^ 2) = 3.504 / V ^ 2 by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hV0, hV2]
    linarith [hFlow, hFhigh, hρVpos]
  have hdiff : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z
      * Complex.exp (z ^ 2)) * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z)) := by
    have hcerfc : Differentiable ℂ cerfc := by
      unfold cerfc; exact fun z => (differentiable_cerf z).const_sub 1
    have h0 : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) * ((Real.sqrt Real.pi : ℂ) * z
        * Complex.exp (z ^ 2))) :=
      ((differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2))).const_mul _
    have h1 : Differentiable ℂ (fun z : ℂ => cerfc (-Complex.I * z)) :=
      hcerfc.comp (differentiable_id.const_mul _)
    exact h0.mul (((differentiable_const 2).sub (h1.const_mul _)).sub (hcerfc.const_mul _))
  obtain ⟨w, hw, hfw⟩ := exists_zero_of_norm_lt_on_sphere hdiff hρ0 hsphere
  have hwb : ‖w - ζ₀‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
  obtain ⟨hwre, -, -, -⟩ := hmem w (Metric.ball_subset_closedBall hw)
  have hw0 : w ≠ 0 := by intro h; rw [h] at hwre; simp at hwre
  refine ⟨w, ?_, hwb⟩
  have hz := hfw
  simp only [mul_eq_zero] at hz
  rcases hz with (h | ((h | h) | h)) | h
  · norm_num at h
  · exact absurd h hsp0
  · exact absurd h hw0
  · exact absurd h (Complex.exp_ne_zero _)
  · exact h

-- no-dlmf: elementary upper bound `exp t ≤ (1 − b)⁻¹`; proof infrastructure
/-- `exp t ≤ (1 − b)⁻¹` whenever `t ≤ b < 1`. -/
theorem exp_le_inv_one_sub {t b : ℝ} (ht : t ≤ b) (hb : b < 1) :
    Real.exp t ≤ (1 - b)⁻¹ := by
  have h1 : Real.exp t ≤ Real.exp b := Real.exp_le_exp.mpr ht
  have h2 : (1:ℝ) - b ≤ Real.exp (-b) := by
    have := Real.add_one_le_exp (-b); linarith
  rw [Real.exp_neg] at h2
  have h4 : (0:ℝ) < Real.exp b := Real.exp_pos b
  have h5 : Real.exp b ≤ (1 - b)⁻¹ := by
    rw [le_inv_comm₀ h4 (by linarith)]
    exact h2.trans (le_of_eq (by rw [inv_eq_one_div, one_div]))
  linarith

-- no-dlmf: transport of the model-function modulus between two points; proof infrastructure
/-- Comparison of `‖E‖ = ‖√π z e^{z²}‖` at two points. -/
theorem fresnelE_le_of {z z₀ : ℂ} {A B t : ℝ} (hz0 : 0 < ‖z₀‖)
    (hE0 : ‖(Real.sqrt Real.pi : ℂ) * z₀ * Complex.exp (z₀ ^ 2)‖ ≤ A)
    (hratio : ‖z‖ ≤ B * ‖z₀‖) (hB : 0 ≤ B)
    (hre : (z ^ 2).re - (z₀ ^ 2).re ≤ t) :
    ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖ ≤ A * B * Real.exp t := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [fresnelE_norm] at hE0 ⊢
  have hexp : Real.exp ((z ^ 2).re) ≤ Real.exp ((z₀ ^ 2).re) * Real.exp t := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 : Real.sqrt Real.pi * ‖z‖ * Real.exp ((z ^ 2).re)
      ≤ Real.sqrt Real.pi * (B * ‖z₀‖) * (Real.exp ((z₀ ^ 2).re) * Real.exp t) := by
    have hnn : (0:ℝ) ≤ Real.sqrt Real.pi * ‖z‖ := by positivity
    refine mul_le_mul ?_ hexp (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left hratio hsppos.le
  have h2 : Real.sqrt Real.pi * (B * ‖z₀‖) * (Real.exp ((z₀ ^ 2).re) * Real.exp t)
      = B * (Real.sqrt Real.pi * ‖z₀‖ * Real.exp ((z₀ ^ 2).re)) * Real.exp t := by ring
  rw [h2] at h1
  have h3 : B * (Real.sqrt Real.pi * ‖z₀‖ * Real.exp ((z₀ ^ 2).re)) * Real.exp t
      ≤ B * A * Real.exp t := by
    have := mul_le_mul_of_nonneg_left hE0 hB
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos t).le
  have h4 : B * A * Real.exp t = A * B * Real.exp t := by ring
  linarith [h1, h3, h4.le, h4.ge]

-- no-dlmf: `Re(z² − z₀²)` bound; proof infrastructure
/-- `Re(z² − z₀²) ≤ ‖z − z₀‖ · ‖z + z₀‖`. -/
theorem fresnel_re_sq_diff_le (z z₀ : ℂ) :
    (z ^ 2).re - (z₀ ^ 2).re ≤ ‖z - z₀‖ * ‖z + z₀‖ := by
  have h1 : (z ^ 2).re - (z₀ ^ 2).re = ((z - z₀) * (z + z₀)).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      pow_two]
    ring
  rw [h1]
  calc ((z - z₀) * (z + z₀)).re ≤ ‖(z - z₀) * (z + z₀)‖ :=
        le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    _ = ‖z - z₀‖ * ‖z + z₀‖ := norm_mul _ _

set_option maxHeartbeats 2000000 in
-- no-dlmf: local uniqueness (separation) of the sub-diagonal Fresnel zeros; proof infrastructure
/-- **Local uniqueness of the sub-diagonal Fresnel zeros.**  In the sector
`‖v‖ ≤ 6 Re v`, `‖v‖ ≤ 6 Im v` with `‖v‖ ≥ 25`, the Fresnel zero equation has at most one
sub-diagonal solution in the disc of radius `1/(24‖v‖)` about `v`.

The Cauchy estimate for the remainder is taken on a ball of radius `1/(4‖v‖)` — the remainder
`R = (E − c/2) − ½EG` is *not* bounded on a ball of radius `≍ ‖v‖`, because `‖e^{ζ²}‖` varies
by `e^{Θ(‖v‖²)}` there; on the `1/(4‖v‖)` ball it varies by a bounded factor, and the model's
derivative growth `≍ 1.4‖v‖` still dominates the resulting Lipschitz constant `≤ 43/‖v‖`. -/
theorem fresnel_zero_unique_in_small_ball {c v w w' : ℂ} (hcn2 : ‖c‖ ^ 2 = 2)
    (hre : ‖v‖ ≤ 6 * v.re) (him : ‖v‖ ≤ 6 * v.im) (hbig : 25 ≤ ‖v‖)
    (hw : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * w) - c * cerfc w = 0)
    (hw' : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * w') - c * cerfc w' = 0)
    (hwsub : w.re ≤ w.im) (hw'sub : w'.re ≤ w'.im)
    (hwb : ‖w - v‖ ≤ 1 / (24 * ‖v‖)) (hwb' : ‖w' - v‖ ≤ 1 / (24 * ‖v‖)) : w = w' := by
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsp0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsppos.ne'
  have hcnnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hcub : ‖c‖ ≤ 1.4143 := by nlinarith
  have hclb : (1.414:ℝ) ≤ ‖c‖ := by nlinarith
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcn2; simp at hcn2
  have hc2 : ‖c / 2‖ = ‖c‖ / 2 := by rw [norm_div]; norm_num
  set V : ℝ := ‖v‖ with hVdef
  have hV0 : (0:ℝ) < V := by linarith
  have hV2 : (625:ℝ) ≤ V ^ 2 := by nlinarith
  set ρ : ℝ := 1 / (24 * V) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρsmall : ρ ≤ 1/600 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hρle : ρ ≤ V / 15000 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hV2]
  have hρV : ρ * V = 1/24 := by rw [hρdef]; field_simp
  have hvre : V / 6 ≤ v.re := by linarith
  have hvim : V / 6 ≤ v.im := by linarith
  -- geometry of the small ball about `v`
  have hgeo : ∀ z : ℂ, ‖z - v‖ ≤ 3 * ρ →
      V / 6 - 3 * ρ ≤ z.re ∧ V / 6 - 3 * ρ ≤ z.im ∧ V - 3 * ρ ≤ ‖z‖ ∧ ‖z‖ ≤ V + 3 * ρ := by
    intro z hz
    have h := Complex.abs_re_le_norm (z - v)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hz)
    have h' := Complex.abs_im_le_norm (z - v)
    simp only [Complex.sub_im] at h'
    have h1' := abs_le.mp (le_trans h' hz)
    have h2 := norm_sub_norm_le v z
    rw [norm_sub_rev v z] at h2
    have h3 := norm_sub_norm_le z v
    exact ⟨by linarith [h1.1], by linarith [h1'.1], by linarith, by linarith⟩
  set Rem : ℂ → ℂ := fun z => ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2)
      - (1 / 2) * ((Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2))
          * (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z) with hRemdef
  have hRdiff : Differentiable ℂ Rem := by
    rw [hRemdef]
    have hcerfc : Differentiable ℂ cerfc := by
      unfold cerfc; exact fun z => (differentiable_cerf z).const_sub 1
    have hE : Differentiable ℂ
        (fun z : ℂ => (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)) :=
      (differentiable_id.const_mul ((Real.sqrt Real.pi : ℂ))).mul
        (Complex.differentiable_exp.comp (differentiable_pow 2))
    have h1 : Differentiable ℂ (fun z : ℂ => cerfc (-Complex.I * z)) :=
      hcerfc.comp (differentiable_id.const_mul _)
    exact (hE.sub_const _).sub
      ((hE.const_mul _).mul (((differentiable_const 2).sub (h1.const_mul _)).sub
        (hcerfc.const_mul _)))
  have hRbound : ∀ z : ℂ, 0 < z.re → 0 < z.im → 20 ≤ ‖z‖ → ∀ B : ℝ,
      ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖ ≤ B →
      ‖Rem z‖ ≤ (B ^ 2 / 2 + 3) / ‖z‖ ^ 2 := by
    intro z h1 h2 h3 B hB
    rw [hRemdef]
    exact fresnel_rem_bound hcn2 h1 h2 h3 hB
  -- the two zeros: `‖E‖ ≈ ‖c/2‖`
  have hzero : ∀ y : ℂ, ‖y - v‖ ≤ ρ → y.re ≤ y.im →
      (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * y) - c * cerfc y = 0) →
      ‖(Real.sqrt Real.pi : ℂ) * y * Complex.exp (y ^ 2) - c / 2‖ ≤ 3 / ‖y‖ ^ 2 := by
    intro y hy hsub hg
    obtain ⟨hy1, -, hy3, -⟩ := hgeo y (by linarith)
    exact fresnel_zero_model_bound hcn2 (by linarith) hsub (by linarith) hg
  have hEw : ‖(Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2)‖ ≤ 0.72 := by
    have h := hzero w hwb hwsub hw
    obtain ⟨-, -, h3, -⟩ := hgeo w (by linarith)
    have hwn : (0:ℝ) < ‖w‖ := by linarith
    have h5 : (3:ℝ) / ‖w‖ ^ 2 ≤ 3 / 620 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h6 := norm_sub_norm_le ((Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2)) (c / 2)
    rw [hc2] at h6
    linarith
  have hEw' : (70/100 : ℝ) ≤ ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ := by
    have h := hzero w' hwb' hw'sub hw'
    obtain ⟨-, -, h3, -⟩ := hgeo w' (by linarith)
    have hwn : (0:ℝ) < ‖w'‖ := by linarith
    have h5 : (3:ℝ) / ‖w'‖ ^ 2 ≤ 3 / 620 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h6 := norm_sub_norm_le (c / 2) ((Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2))
    rw [norm_sub_rev (c/2)] at h6
    rw [hc2] at h6
    linarith
  obtain ⟨-, -, hwn1, hwn2⟩ := hgeo w (by linarith)
  have hwn0 : (0:ℝ) < ‖w‖ := by linarith
  have hww' : ‖w' - w‖ ≤ 2 * ρ := by
    have h := norm_sub_le (w' - v) (w - v)
    have he : (w' - v) - (w - v) = w' - w := by ring
    rw [he] at h; linarith
  -- `‖E‖ ≤ 1` on the ball of radius `2ρ` about `w`
  have hEball : ∀ z : ℂ, ‖z - w‖ ≤ 2 * ρ →
      0 < z.re ∧ 0 < z.im ∧ 20 ≤ ‖z‖ ∧
        ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖ ≤ 1 := by
    intro z hz
    have hzv : ‖z - v‖ ≤ 3 * ρ := by
      have h := norm_add_le (z - w) (w - v)
      have he : (z - w) + (w - v) = z - v := by ring
      rw [he] at h; linarith
    obtain ⟨g1, g2, g3, g4⟩ := hgeo z hzv
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    have hratio : ‖z‖ ≤ 1.001 * ‖w‖ := by linarith [g4, hwn1, hρle, hV0]
    have hzpw : ‖z + w‖ ≤ 2 * V + 6 * ρ := by
      have h := norm_add_le z w; linarith
    have hred : (z ^ 2).re - (w ^ 2).re ≤ 0.168 := by
      have h := fresnel_re_sq_diff_le z w
      have h2 : ‖z - w‖ * ‖z + w‖ ≤ (2 * ρ) * (2 * V + 6 * ρ) :=
        mul_le_mul hz hzpw (norm_nonneg _) (by linarith)
      have h3 : (2 * ρ) * (2 * V + 6 * ρ) ≤ 0.168 := by nlinarith [hρV, hρsmall, hρ0, hV0]
      linarith
    have hEz := fresnelE_le_of hwn0 hEw hratio (by norm_num) hred
    have hexpb : Real.exp (0.168 : ℝ) ≤ 1.21 := by
      have h := exp_le_inv_one_sub (le_refl (0.168:ℝ)) (by norm_num)
      have h2 : ((1:ℝ) - 0.168)⁻¹ ≤ 1.21 := by
        rw [inv_le_comm₀ (by norm_num) (by norm_num)]; norm_num
      linarith
    nlinarith [hEz, hexpb, Real.exp_pos (0.168:ℝ)]
  -- the Cauchy estimate for the remainder
  have hderiv : ∀ z₀ : ℂ, ‖z₀ - w‖ ≤ 2 * ρ → ‖deriv Rem z₀‖ ≤ 43 / V := by
    intro z₀ hz₀
    obtain ⟨hz₀re, hz₀im, hz₀n, hE₀⟩ := hEball z₀ hz₀
    have hz₀v : ‖z₀ - v‖ ≤ 3 * ρ := by
      have h := norm_add_le (z₀ - w) (w - v)
      have he : (z₀ - w) + (w - v) = z₀ - v := by ring
      rw [he] at h; linarith
    obtain ⟨-, -, hz₀n1, hz₀n2⟩ := hgeo z₀ hz₀v
    set r : ℝ := 1 / (4 * V) with hrdef
    have hr0 : 0 < r := by rw [hrdef]; positivity
    have hrV : r * V = 1/4 := by rw [hrdef]; field_simp
    have hrsmall : r ≤ 1/100 := by
      rw [hrdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hrle : r ≤ V / 2500 := by
      rw [hrdef, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hV2]
    have hinner : ∀ z ∈ Metric.ball z₀ r,
        0 < z.re ∧ 0 < z.im ∧ 20 ≤ ‖z‖ ∧ 0.999 * V ≤ ‖z‖ ∧
          ‖(Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2)‖ ≤ 2.1 := by
      intro z hz
      have hd' : ‖z - z₀‖ ≤ r := by
        rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hz).le
      have hzv : ‖z - v‖ ≤ 3 * ρ + r := by
        have h := norm_add_le (z - z₀) (z₀ - v)
        have he : (z - z₀) + (z₀ - v) = z - v := by ring
        rw [he] at h; linarith
      have hre1 : |z.re - v.re| ≤ 3 * ρ + r := by
        have h := Complex.abs_re_le_norm (z - v)
        simp only [Complex.sub_re] at h; linarith
      have him1 : |z.im - v.im| ≤ 3 * ρ + r := by
        have h := Complex.abs_im_le_norm (z - v)
        simp only [Complex.sub_im] at h; linarith
      have hn1 : V - (3 * ρ + r) ≤ ‖z‖ := by
        have h := norm_sub_norm_le v z
        rw [norm_sub_rev v z] at h; linarith
      have hn2 : ‖z‖ ≤ V + (3 * ρ + r) := by
        have h := norm_sub_norm_le z v; linarith
      have ha := abs_le.mp hre1
      have hb := abs_le.mp him1
      have hz₀0 : (0:ℝ) < ‖z₀‖ := by linarith
      refine ⟨by linarith [ha.1], by linarith [hb.1], by linarith,
        by linarith [hn1, hρle, hrle, hV0], ?_⟩
      have hratio : ‖z‖ ≤ 1.001 * ‖z₀‖ := by
        have h := norm_sub_norm_le z z₀
        linarith [h, hd', hz₀n1, hρle, hrle, hV0]
      have hzpz : ‖z + z₀‖ ≤ 2 * V + 7 * ρ + r := by
        have h := norm_add_le z z₀; linarith [h, hn2, hz₀n2, hρ0]
      have hred : (z ^ 2).re - (z₀ ^ 2).re ≤ 0.51 := by
        have h := fresnel_re_sq_diff_le z z₀
        have h2 : ‖z - z₀‖ * ‖z + z₀‖ ≤ r * (2 * V + 7 * ρ + r) :=
          mul_le_mul hd' hzpz (norm_nonneg _) hr0.le
        have h3 : r * (2 * V + 7 * ρ + r) ≤ 0.51 := by
          nlinarith [hrV, hρV, hrsmall, hρsmall, hr0, hρ0, hV0]
        linarith
      have hEz := fresnelE_le_of hz₀0 hE₀ hratio (by norm_num) hred
      have hexpb : Real.exp (0.51 : ℝ) ≤ 2.05 := by
        have h := exp_le_inv_one_sub (le_refl (0.51:ℝ)) (by norm_num)
        have h2 : ((1:ℝ) - 0.51)⁻¹ ≤ 2.05 := by
          rw [inv_le_comm₀ (by norm_num) (by norm_num)]; norm_num
        linarith
      nlinarith [hEz, hexpb, Real.exp_pos (0.51:ℝ)]
    have hmaps : Set.MapsTo Rem (Metric.ball z₀ r) (Metric.closedBall (Rem z₀) (10.6 / V ^ 2)) := by
      intro z hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hinner z hz
      have b1 : ‖Rem z‖ ≤ 5.3 / V ^ 2 := by
        refine le_trans (hRbound z h1 h2 h3 2.1 h5) ?_
        rw [show ((2.1:ℝ) ^ 2 / 2 + 3) = 5.205 by norm_num,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h4, hV0]
      have b2 : ‖Rem z₀‖ ≤ 5.3 / V ^ 2 := by
        refine le_trans (hRbound z₀ hz₀re hz₀im hz₀n 1 hE₀) ?_
        rw [show ((1:ℝ) ^ 2 / 2 + 3) = 3.5 by norm_num,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hz₀n1, hV0, hρsmall]
      rw [Metric.mem_closedBall, dist_eq_norm]
      have := norm_sub_le (Rem z) (Rem z₀)
      have he : (10.6:ℝ)/V^2 = 5.3/V^2 + 5.3/V^2 := by ring
      rw [he]; linarith
    have h := Complex.norm_deriv_le_div_of_mapsTo_ball (f := Rem) (c := z₀)
      (R₁ := r) (R₂ := 10.6 / V ^ 2) hRdiff.differentiableOn hmaps hr0
    refine h.trans ?_
    have hVne : V ≠ 0 := ne_of_gt hV0
    have hval : (10.6 / V ^ 2) / r = 42.4 / V := by
      rw [hrdef]; field_simp; ring
    rw [hval, div_le_div_iff₀ hV0 hV0]
    linarith
  -- the Lipschitz bound and the model lower bound
  have hmemw : w ∈ Metric.closedBall w (2 * ρ) := by
    rw [Metric.mem_closedBall]; simp; linarith
  have hmemw' : w' ∈ Metric.closedBall w (2 * ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hww'
  have hRlip : ‖Rem w - Rem w'‖ ≤ (43 / V) * ‖w - w'‖ :=
    norm_sub_le_of_hasDerivAt_le (f := Rem) (f' := deriv Rem) (convex_closedBall w (2 * ρ))
      (fun z _ => (hRdiff z).hasDerivAt)
      (fun z hz => hderiv z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz))
      hmemw' hmemw
  obtain ⟨hwre0, hwim0, -, -⟩ := hEball w (by simp; linarith)
  obtain ⟨hw're0, hw'im0, hw'n20, -⟩ := hEball w' hww'
  obtain ⟨-, -, hw'n1, hw'n2⟩ := hgeo w' (by linarith)
  have hexpg : ∀ z : ℂ, 0 < z.re →
      Complex.exp (z ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * z))
        = (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [Complex.exp_add, Complex.exp_log (mul_ne_zero hsp0 hz0)]; ring
  have hΦ : ∀ z : ℂ, (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * z) - c * cerfc z = 0) →
      Rem z = (Real.sqrt Real.pi : ℂ) * z * Complex.exp (z ^ 2) - c / 2 := by
    intro z hz
    rw [hRemdef]; simp only; rw [hz]; ring
  set δ : ℂ := (w ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w))
    - (w' ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * w')) with hδdef
  have hlogmvt : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
      - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ ≤ (1 / (V - 3 * ρ)) * ‖w - w'‖ := by
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
      (convex_closedBall w (2 * ρ)) ?_ ?_ hmemw' hmemw
    · intro y hy
      have hyb : ‖y - w‖ ≤ 2 * ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      obtain ⟨hy1, -, -, -⟩ := hEball y hyb
      have hslit : ((Real.sqrt Real.pi : ℂ)) * y ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
          ((Real.sqrt Real.pi : ℂ)) y := by
        simpa using (hasDerivAt_id y).const_mul ((Real.sqrt Real.pi : ℂ))
      exact h1.clog hslit
    · intro y hy
      have hyb : ‖y - w‖ ≤ 2 * ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
      have hyv : ‖y - v‖ ≤ 3 * ρ := by
        have h := norm_add_le (y - w) (w - v)
        have he : (y - w) + (w - v) = y - v := by ring
        rw [he] at h; linarith
      obtain ⟨-, -, hy2, -⟩ := hgeo y hyv
      have hyn : (0:ℝ) < ‖y‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hy2, hsppos]
  have hlogsmall : (1 / (V - 3 * ρ)) * ‖w - w'‖ ≤ (1/24) * ‖w - w'‖ := by
    have h1 : (1:ℝ) / (V - 3 * ρ) ≤ 1/24 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hsum1 : ‖w + w'‖ ≤ 2 * V + 6 * ρ := by
    have h := norm_add_le w w'; linarith
  have hsum2 : 2 * V - 6 * ρ ≤ ‖w + w'‖ := by
    have h2 : ‖(2:ℂ) * v‖ = 2 * V := by rw [norm_mul]; simp [hVdef]
    have h1 : ‖(2:ℂ) * v‖ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by
      calc ‖(2:ℂ) * v‖ = ‖(w + w') - ((w - v) + (w' - v))‖ := by congr 1; ring
        _ ≤ ‖w + w'‖ + ‖(w - v) + (w' - v)‖ := norm_sub_le _ _
        _ ≤ ‖w + w'‖ + (‖w - v‖ + ‖w' - v‖) := by linarith [norm_add_le (w - v) (w' - v)]
    rw [h2] at h1; linarith
  have hδsplit : δ = (w - w') * (w + w')
      + (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
        - Complex.log ((Real.sqrt Real.pi : ℂ) * w')) := by rw [hδdef]; ring
  have hprodn : ‖(w - w') * (w + w')‖ = ‖w - w'‖ * ‖w + w'‖ := norm_mul _ _
  have hwwsmall : ‖w - w'‖ ≤ 2 * ρ := by
    rw [norm_sub_rev]; exact hww'
  have hδlow : (198/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖δ‖ := by
    have h0 : ‖(w - w') * (w + w')‖ ≤ ‖δ‖
        + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := by
      calc ‖(w - w') * (w + w')‖
          = ‖δ - (Complex.log ((Real.sqrt Real.pi : ℂ) * w)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * w'))‖ := by
            congr 1; rw [hδsplit]; ring
        _ ≤ ‖δ‖ + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
              - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := norm_sub_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * (2 * V - 6 * ρ) ≤ ‖w - w'‖ * ‖w + w'‖ :=
      mul_le_mul_of_nonneg_left hsum2 (norm_nonneg _)
    have hslack0 : 6 * ρ + 1/24 ≤ V/50 := by linarith [hρle, hbig]
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδhigh : ‖δ‖ ≤ (202/100 : ℝ) * (V * ‖w - w'‖) := by
    have h0 : ‖δ‖ ≤ ‖(w - w') * (w + w')‖
        + ‖Complex.log ((Real.sqrt Real.pi : ℂ) * w)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * w')‖ := by
      rw [hδsplit]; exact norm_add_le _ _
    rw [hprodn] at h0
    have hmul : ‖w - w'‖ * ‖w + w'‖ ≤ ‖w - w'‖ * (2 * V + 6 * ρ) :=
      mul_le_mul_of_nonneg_left hsum1 (norm_nonneg _)
    have hslack0 : 6 * ρ + 1/24 ≤ V/50 := by linarith [hρle, hbig]
    have hslack := mul_le_mul_of_nonneg_left hslack0 (norm_nonneg (w - w'))
    linarith only [h0, hmul, hlogmvt, hlogsmall, hslack]
  have hδle : ‖δ‖ ≤ 1/5 := by
    have h1 : V * ‖w - w'‖ ≤ V * (2 * ρ) := mul_le_mul_of_nonneg_left hwwsmall (by linarith)
    have h2 : V * (2 * ρ) = 1 / 12 := by rw [hρdef]; field_simp; ring
    rw [h2] at h1
    linarith
  have hexpδ : (8/10 : ℝ) * ‖δ‖ ≤ ‖Complex.exp δ - 1‖ := by
    have hb := Complex.norm_exp_sub_one_sub_id_le (x := δ) (by linarith)
    have h5 := norm_sub_norm_le δ (Complex.exp δ - 1)
    rw [norm_sub_rev δ (Complex.exp δ - 1)] at h5
    have h6 : (Complex.exp δ - 1) - δ = Complex.exp δ - 1 - δ := by ring
    rw [h6] at h5
    have h7 : ‖δ‖ ^ 2 ≤ (1/5) * ‖δ‖ := by
      calc ‖δ‖ ^ 2 = ‖δ‖ * ‖δ‖ := by ring
        _ ≤ ‖δ‖ * (1/5) := mul_le_mul_of_nonneg_left hδle (norm_nonneg _)
        _ = (1/5) * ‖δ‖ := by ring
    linarith
  have hkey : Rem w - Rem w'
      = (Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2) * (Complex.exp δ - 1) := by
    have e1 : (Real.sqrt Real.pi : ℂ) * w * Complex.exp (w ^ 2)
        = (Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2) * Complex.exp δ := by
      rw [← hexpg w hwre0, ← hexpg w' hw're0, ← Complex.exp_add]
      congr 1
      rw [hδdef]; ring
    rw [hΦ w hw, hΦ w' hw']
    linear_combination e1
  have hlow : ‖Rem w - Rem w'‖
      = ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ := by
    rw [hkey, norm_mul]
  have hVX : (0:ℝ) ≤ V * ‖w - w'‖ := by positivity
  have hchain : (110/100 : ℝ) * (V * ‖w - w'‖) ≤ ‖Rem w - Rem w'‖ := by
    rw [hlow]
    have h1 : (70/100 : ℝ) * ((8/10) * ‖δ‖)
        ≤ ‖(Real.sqrt Real.pi : ℂ) * w' * Complex.exp (w' ^ 2)‖ * ‖Complex.exp δ - 1‖ :=
      mul_le_mul hEw' hexpδ (by positivity) (norm_nonneg _)
    linarith only [hδlow, h1, hVX]
  by_contra hne
  have hpos : 0 < ‖w - w'‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  have hcomb : (110/100 : ℝ) * V * ‖w - w'‖ ≤ (43 / V) * ‖w - w'‖ := by
    linarith only [hchain, hRlip]
  have hfin : (110/100 : ℝ) * V ≤ 43 / V :=
    le_of_mul_le_mul_right (by linarith only [hcomb]) hpos
  have h43 : (43:ℝ) / V ≤ 43 / 25 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith only [hfin, h43, hbig]

/-! ### Fresnel zeros — the index, the count and the enumeration

The index parameter attached to a large sub-diagonal zero, the crude match to the DLMF
7.13.6/7.13.7 parameters, the existence of the zero at each index, the uniqueness of the
zero per index, and the assembly of these into the statement that a complete,
modulus-ordered enumeration *is* the index family from index 3300 on. -/

-- no-dlmf: elementary size bounds for the Fresnel index parameters; proof infrastructure
/-- For `λ ≥ 100` and `2μ = log(4πλ²)`: `5 ≤ μ`, `μ + 3 ≤ 7 λ^{1/4}` and `μ + 3 ≤ λ`. -/
theorem fresnel713_mu_bounds {lam mu : ℝ} (hlam : 100 ≤ lam)
    (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2)) :
    5 ≤ mu ∧ mu + 3 ≤ 7 * Real.sqrt (Real.sqrt lam) ∧ mu + 3 ≤ lam := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsnn : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hlb : (1.7:ℝ) ≤ Real.sqrt Real.pi := by nlinarith [Real.pi_gt_three]
  have hub : Real.sqrt Real.pi ≤ 1.8 := by nlinarith [Real.pi_lt_d6, hsq, hsnn]
  set X : ℝ := 2 * lam * Real.sqrt Real.pi with hXdef
  have hX0 : (0:ℝ) < X := by rw [hXdef]; nlinarith
  have hXsq : X ^ 2 = 4 * Real.pi * lam ^ 2 := by rw [hXdef]; nlinarith [hsq]
  have hmuX : mu = Real.log X := by
    rw [← hXsq, Real.log_pow] at hmu
    push_cast at hmu
    linarith
  have hX4 : X ≤ 4 * lam := by rw [hXdef]; nlinarith
  have hX200 : (200:ℝ) ≤ X := by rw [hXdef]; nlinarith
  set s : ℝ := Real.sqrt (Real.sqrt lam) with hsdef
  have hs0 : 0 < s := by
    rw [hsdef]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hlam0)
  have hs4 : s ^ 4 = lam := by
    rw [hsdef, show (Real.sqrt (Real.sqrt lam)) ^ 4
      = ((Real.sqrt (Real.sqrt lam)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg lam), Real.sq_sqrt hlam0.le]
  have hs3 : 3 ≤ s := by
    by_contra hcon
    have hlt : s < 3 := not_le.mp hcon
    have h1 : s ^ 2 < 9 := by nlinarith [hs0]
    have h2 : s ^ 4 < 81 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]; nlinarith [h1, sq_nonneg s]
    linarith [hs4, hlam]
  -- the fourth-root bound on `mu`
  have h1 : Real.log (Real.sqrt (Real.sqrt X)) ≤ Real.sqrt (Real.sqrt X) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX0))
  have h2 : Real.log (Real.sqrt (Real.sqrt X)) = Real.log (Real.sqrt X) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsqrt2 : Real.sqrt 2 ≤ 1.4143 := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.4143)] at h
  have hb : Real.sqrt (Real.sqrt X) ≤ 1.4143 * s := by
    have hu2 : Real.sqrt X ≤ 2 * Real.sqrt lam := by
      have hq : Real.sqrt (4 * lam) = 2 * Real.sqrt lam := by
        rw [show (4:ℝ) * lam = 2 ^ 2 * lam by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      calc Real.sqrt X ≤ Real.sqrt (4 * lam) := Real.sqrt_le_sqrt hX4
        _ = 2 * Real.sqrt lam := hq
    have hu3 : Real.sqrt (Real.sqrt X) ≤ Real.sqrt (2 * Real.sqrt lam) :=
      Real.sqrt_le_sqrt hu2
    have hu4 : Real.sqrt (2 * Real.sqrt lam) = Real.sqrt 2 * s := by
      rw [hsdef, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hs2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [hu3, hu4.le, hu4.ge, hsqrt2, hs0]
  have hmuub : mu ≤ 5.6572 * s - 4 := by
    rw [hmuX]
    linarith [h1, h2, h3, hb]
  refine ⟨?_, by nlinarith [hmuub, hs3, hs0], ?_⟩
  · rw [hmuX]
    have hexp : Real.exp 5 ≤ 200 := by
      have h1' : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      have h2' : Real.exp 5 = Real.exp 1 ^ (5:ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h2']
      have h3' : Real.exp 1 ^ (5:ℕ) ≤ (2.7182818286:ℝ) ^ (5:ℕ) := by gcongr
      refine h3'.trans ?_
      norm_num
    rw [Real.le_log_iff_exp_le hX0]
    linarith
  · have hcube : (27:ℝ) ≤ s ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs3) (sq_nonneg s), hs3, hs0]
    have hs4' : 27 * s ≤ s ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hcube hs0.le]
    rw [← hs4]
    linarith [hmuub, hs4', hs0]

-- no-dlmf: an eighth-root bound for the Fresnel index parameter `μ`; proof infrastructure
/-- `(μ + 3)⁴ ≤ 8214 √λ` for `λ ≥ 100`, `2μ = log(4πλ²)`.  This is the estimate that makes
the asymptotic-constant threshold `(μ+3)⁴ ≤ λ` of `fresnel713_zero_expansion` hold for all
large `λ` (namely `λ ≥ 8214²`). -/
theorem fresnel713_mu_eighth {lam mu : ℝ} (hlam : 100 ≤ lam)
    (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2)) :
    (mu + 3) ^ 4 ≤ 8214 * Real.sqrt lam := by
  obtain ⟨hmu5, -, -⟩ := fresnel713_mu_bounds hlam hmu
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsnn : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hub : Real.sqrt Real.pi ≤ 1.8 := by nlinarith [Real.pi_lt_d6, hsq, hsnn]
  set X : ℝ := 2 * lam * Real.sqrt Real.pi with hXdef
  have hX0 : (0:ℝ) < X := by rw [hXdef]; nlinarith [Real.pi_gt_three, hsq]
  have hXsq : X ^ 2 = 4 * Real.pi * lam ^ 2 := by rw [hXdef]; nlinarith [hsq]
  have hmuX : mu = Real.log X := by
    rw [← hXsq, Real.log_pow] at hmu
    push_cast at hmu
    linarith
  have hX4 : X ≤ 4 * lam := by rw [hXdef]; nlinarith
  -- the eighth root of `lam`
  set t : ℝ := Real.sqrt (Real.sqrt (Real.sqrt lam)) with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hlam0))
  have ht4 : t ^ 4 = Real.sqrt lam := by
    rw [htdef, show (Real.sqrt (Real.sqrt (Real.sqrt lam))) ^ 4
      = ((Real.sqrt (Real.sqrt (Real.sqrt lam))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
  have ht8 : t ^ 8 = lam := by
    have h : t ^ 8 = (t ^ 4) ^ 2 := by ring
    rw [h, ht4, Real.sq_sqrt hlam0.le]
  -- `X^{1/8} ≤ 1.19 t`
  have hq2 : Real.sqrt 2 ≤ 1.4143 := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.4143 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.4143)] at h
  have hq2nn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hqq2 : Real.sqrt (Real.sqrt 2) ≤ 1.19 := by
    have h : Real.sqrt (Real.sqrt 2) ≤ Real.sqrt (1.19 ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.19)] at h
  have e1 : Real.sqrt (4 * t ^ 8) = 2 * t ^ 4 := by
    rw [show (4:ℝ) * t ^ 8 = (2 * t ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (2 * t ^ 4) = Real.sqrt 2 * t ^ 2 := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have e3 : Real.sqrt (Real.sqrt 2 * t ^ 2) = Real.sqrt (Real.sqrt 2) * t := by
    rw [Real.sqrt_mul hq2nn, Real.sqrt_sq ht0.le]
  have hchain : Real.sqrt (Real.sqrt (Real.sqrt X)) ≤ 1.19 * t := by
    have hA : Real.sqrt X ≤ 2 * t ^ 4 := by
      rw [← e1]; exact Real.sqrt_le_sqrt (by rw [ht8]; linarith)
    have hB : Real.sqrt (Real.sqrt X) ≤ Real.sqrt 2 * t ^ 2 := by
      rw [← e2]; exact Real.sqrt_le_sqrt hA
    have hC : Real.sqrt (Real.sqrt (Real.sqrt X)) ≤ Real.sqrt (Real.sqrt 2) * t := by
      rw [← e3]; exact Real.sqrt_le_sqrt hB
    nlinarith [hC, hqq2, ht0, Real.sqrt_nonneg (Real.sqrt 2)]
  -- `log X ≤ 8 (X^{1/8} − 1)`
  have h1 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt X)))
      ≤ Real.sqrt (Real.sqrt (Real.sqrt X)) - 1 :=
    Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX0)))
  have h2 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt X)))
      = Real.log (Real.sqrt (Real.sqrt X)) / 2 := Real.log_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.log (Real.sqrt (Real.sqrt X)) = Real.log (Real.sqrt X) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  have h4 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hmuub : mu + 3 ≤ 9.52 * t := by
    rw [hmuX]
    nlinarith [h1, h2, h3, h4, hchain, ht0]
  have hm0 : (0:ℝ) ≤ mu + 3 := by linarith
  calc (mu + 3) ^ 4 ≤ (9.52 * t) ^ 4 := by gcongr
    _ = (9.52:ℝ) ^ 4 * t ^ 4 := by ring
    _ ≤ 8214 * Real.sqrt lam := by rw [ht4]; nlinarith [Real.sqrt_nonneg lam, ht4, ht0]

set_option maxHeartbeats 1000000 in
-- no-dlmf: the index parameter attached to a large sub-diagonal Fresnel zero; proof
-- infrastructure
/-- **The index of a large sub-diagonal Fresnel zero.**  A solution of the Fresnel zero
equation in the sub-diagonal sector with `‖ζ‖² ≥ 20004` carries an integer index `k ≥ 1`
and the associated parameter `λ` with `4λ² = 4πk − π/2 + (Im c)·π/2`, for which the two
real component equations hold with the `λ`-denominated budgets of the inversion. -/
theorem fresnel_zero_index_exists {c ζ : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    (hx : 0 < ζ.re) (hxy : ζ.re < ζ.im) (hbig : 20004 ≤ ζ.re ^ 2 + ζ.im ^ 2)
    (hz : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) :
    ∃ (k : ℤ) (lam : ℝ), 0 < k ∧ 100 ≤ lam ∧
      4 * lam ^ 2 = 4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2) ∧
      |(ζ.re - ζ.im) * (ζ.re + ζ.im)
          + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))| ≤ 4 / lam ^ 2 ∧
      |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
          - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) - 4 * lam ^ 2| ≤ 8 / lam ^ 2 := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hy : 0 < ζ.im := lt_trans hx hxy
  have hnorm : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hbig20 : (20:ℝ) ≤ ‖ζ‖ := by nlinarith [norm_nonneg ζ, hnorm, hbig]
  obtain ⟨k, key1, key2⟩ := fresnel_zero_components hcre hcim hx hxy hbig20 hz
  set N : ℝ := ζ.re ^ 2 + ζ.im ^ 2 with hNdef
  set s : ℝ := ζ.re + ζ.im with hsdef
  set d : ℝ := ζ.re - ζ.im with hddef
  set A : ℝ := Real.arctan (d / s) with hAdef
  set L : ℝ := (1 / 2) * Real.log (2 * Real.pi * N) with hLdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hNsd : 2 * N = s ^ 2 + d ^ 2 := by rw [hNdef, hsdef, hddef]; ring
  have hd2s : d ^ 2 ≤ s ^ 2 := by rw [hsdef, hddef]; nlinarith
  have hN0 : (0:ℝ) < N := by linarith
  have hAbd : |A| ≤ 2 := by
    rw [hAdef, abs_le]
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan (d / s)]
    · linarith [Real.arctan_lt_pi_div_two (d / s)]
  -- crude size of `d`
  set r : ℝ := Real.sqrt N with hrdef
  have hr2 : r ^ 2 = N := by rw [hrdef]; exact Real.sq_sqrt hN0.le
  have hr0 : (0:ℝ) < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hN0
  have hr141 : (141:ℝ) ≤ r := by nlinarith [hr2, hbig, hr0]
  have hsr : r ≤ s := by nlinarith [hNsd, hd2s, hs, hr2, hr0]
  have hLub : L ≤ 2.51 * r - 1 := by
    have h1 : Real.log (Real.sqrt (2 * Real.pi * N)) ≤ Real.sqrt (2 * Real.pi * N) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity))
    have h2 : Real.log (Real.sqrt (2 * Real.pi * N)) = L := by
      rw [hLdef, Real.log_sqrt (by positivity)]; ring
    have h3 : Real.sqrt (2 * Real.pi * N) ≤ 2.51 * r := by
      have hEq : Real.sqrt (2.51 ^ 2 * N) = 2.51 * r := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2.51 ^ 2),
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.51), hrdef]
      have h4 : Real.sqrt (2 * Real.pi * N) ≤ Real.sqrt (2.51 ^ 2 * N) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d6])
      linarith [h4, hEq.le, hEq.ge]
    linarith [h1, h2.le, h2.ge, h3]
  have hLpos : (0:ℝ) < L := by
    have h1 : (1:ℝ) < 2 * Real.pi * N := by nlinarith
    have h2 := Real.log_pos h1
    rw [hLdef]; linarith
  have hk1 := abs_le.mp key1
  have hdabs : |d| ≤ 2.51 := by
    have h2 : |d| * s = |d * s| := by rw [abs_mul, abs_of_pos hs]
    have h1 : |d * s| ≤ 7 / N + L := by
      rw [abs_le]; constructor <;> linarith [hk1.1, hk1.2, hLpos]
    have h3 : (7:ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]; linarith
    have h4 : |d| * s ≤ 2.51 * r := by rw [h2]; linarith
    have hprod : |d| * r ≤ |d| * s := mul_le_mul_of_nonneg_left hsr (abs_nonneg d)
    exact le_of_mul_le_mul_right (by linarith) hr0
  have hd2 : d ^ 2 ≤ 6.31 := by nlinarith [hdabs, abs_nonneg d, sq_abs d]
  -- positivity of the index constant
  set Q : ℝ := 4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2) with hQdef
  have hk2 := abs_le.mp key2
  have hQpos : (0:ℝ) < Q := by
    have h1 : (14:ℝ) / N ≤ 1 := by rw [div_le_one hN0]; linarith
    have hAle : A ≤ 2 := le_trans (le_abs_self A) hAbd
    linarith [hk2.2, hNsd, hd2, hAle, h1, hbig]
  have hkpos : (0:ℤ) < k := by
    have hcimle : c.im ≤ 1 := by rcases hcim with h | h <;> rw [h] <;> norm_num
    have hQle : Q ≤ 4 * Real.pi * (k:ℝ) := by
      rw [hQdef]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c.im) (by linarith : (0:ℝ) ≤ Real.pi)]
    by_contra hcon
    push Not at hcon
    have hkr : ((k:ℤ):ℝ) ≤ 0 := by exact_mod_cast hcon
    have h0 := mul_le_mul_of_nonneg_left hkr (show (0:ℝ) ≤ 4 * Real.pi by positivity)
    linarith
  -- the parameter `lam`
  set lam : ℝ := Real.sqrt (Q / 4) with hlamdef
  have hlam0 : (0:ℝ) < lam := by rw [hlamdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hlamQ : 4 * lam ^ 2 = Q := by
    rw [hlamdef, Real.sq_sqrt (by linarith)]; ring
  rw [← hlamQ] at key2
  obtain ⟨hlow, hhigh, he1, he2⟩ :=
    fresnel713_modulus hlam0 (by linarith : (400:ℝ) ≤ N) hLdef hs hNsd hd2s hAbd key1 key2
  have hlam100 : (100:ℝ) ≤ lam := by
    have hsq : (10000:ℝ) ≤ lam ^ 2 := by linarith [hlow, hbig]
    nlinarith [hsq, hlam0]
  exact ⟨k, lam, hkpos, hlam100, hlamQ.trans hQdef, le_trans key1 he1, le_trans key2 he2⟩

-- no-dlmf: the crude match of a Fresnel zero to its index parameters; proof infrastructure
/-- **The crude match at an index.**  From the two `λ`-denominated component bounds, the
sub-diagonal solution obeys `d = −μ/(2λ) + O(λ⁻²)`, `s = 2λ + O(λ⁻¹)/70` and
`N = 2λ² + O(1/10)`. -/
theorem fresnel713_match_of_key {lam mu s d N A : ℝ}
    (hlam : 100 ≤ lam) (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2))
    (hs : 0 < s) (hNsd : 2 * N = s ^ 2 + d ^ 2) (hd2s : d ^ 2 ≤ s ^ 2)
    (hAT : |A - d / s| ≤ |d / s| ^ 3)
    (key1 : |d * s + (1 / 2) * Real.log (2 * Real.pi * N)| ≤ 4 / lam ^ 2)
    (key2 : |s ^ 2 - d ^ 2 - 2 * A - 4 * lam ^ 2| ≤ 8 / lam ^ 2) :
    |d + mu / (2 * lam)| ≤ 1 / lam ^ 2 ∧ |s - 2 * lam| ≤ 1 / (70 * lam) ∧
      |N - 2 * lam ^ 2| ≤ 1 / 10 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  obtain ⟨hmu5, -, hmu3⟩ := fresnel713_mu_bounds hlam hmu
  obtain ⟨hslb, hNlb, hdabs, hAsmall, hs2m, hNm⟩ :=
    fresnel713_crude hlam rfl hs hNsd hd2s hAT key1 key2
  obtain ⟨-, -, -, -, hdd⟩ :=
    fresnel713_first hlam hmu5 hmu3 hmu rfl hs hslb hNlb hdabs hNm hs2m key1
  refine ⟨hdd, ?_, hNm⟩
  have hfacs : |s - 2 * lam| * (s + 2 * lam) = |s ^ 2 - 4 * lam ^ 2| := by
    rw [← abs_of_pos (show (0:ℝ) < s + 2 * lam by linarith), ← abs_mul]
    congr 1; ring
  have h1 : |s - 2 * lam| * (4 * lam - 1) ≤ 1 / 20 := by
    have h2 : |s - 2 * lam| * (4 * lam - 1) ≤ |s - 2 * lam| * (s + 2 * lam) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith [hfacs, hs2m]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h1, abs_nonneg (s - 2 * lam), hlam0]

set_option maxHeartbeats 1000000 in
-- no-dlmf: real components of the Fresnel zero equation at a *given* index; proof infrastructure
/-- The two real component equations at a sub-diagonal Fresnel zero, at the index `k` supplied
by the logarithmic form.  (`fresnel_zero_components` is the existential packaging; the index
must be retained when it is to be pinned against a model root.) -/
theorem fresnel_zero_components_of_log {c ζ : ℂ} {k : ℤ}
    (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    (hx : 0 < ζ.re) (hxy : ζ.re < ζ.im) (hbig : 20 ≤ ‖ζ‖)
    (hk : ‖ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k‖ ≤ 7 / ‖ζ‖ ^ 2) :
      |(ζ.re - ζ.im) * (ζ.re + ζ.im)
          + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))|
          ≤ 7 / (ζ.re ^ 2 + ζ.im ^ 2) ∧
      |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
          - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))
          - (4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))|
          ≤ 14 / (ζ.re ^ 2 + ζ.im ^ 2) := by
  have hy : 0 < ζ.im := by linarith
  have hcn2 : ‖c‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcre]
    rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcn : ‖c‖ = Real.sqrt 2 := by rw [← hcn2, Real.sqrt_sq (norm_nonneg c)]
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcn2; simp at hcn2
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hN : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN0 : (0:ℝ) < ζ.re ^ 2 + ζ.im ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · -- real part
    have hre := (Complex.abs_re_le_norm (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
      - Complex.log (c / 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans hk
    have hsqre : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by simp [pow_two, Complex.mul_re]
    have hlogre : (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)).re
        = Real.log (Real.sqrt Real.pi * ‖ζ‖) := by
      rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have hlogc : (Complex.log (c / 2)).re = Real.log (Real.sqrt 2 / 2) := by
      rw [Complex.log_re, norm_div, hcn]; norm_num
    have hcre0 : (2 * (Real.pi : ℂ) * Complex.I * k).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have hid : Real.log (Real.sqrt Real.pi * ‖ζ‖) - Real.log (Real.sqrt 2 / 2)
        = (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2)) := by
      have hzn : (0:ℝ) < ‖ζ‖ := by linarith
      have e1 : Real.log (Real.sqrt Real.pi * ‖ζ‖)
          = (1 / 2) * Real.log (Real.pi * ‖ζ‖ ^ 2) := by
        rw [show Real.pi * ‖ζ‖ ^ 2 = (Real.sqrt Real.pi * ‖ζ‖) ^ 2 by
              rw [mul_pow, Real.sq_sqrt Real.pi_pos.le],
          Real.log_pow]
        push_cast; ring
      have e2 : Real.log (Real.sqrt 2 / 2) = -((1 / 2) * Real.log 2) := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
        ring
      have e3 : Real.log (2 * Real.pi * ‖ζ‖ ^ 2) = Real.log 2 + Real.log (Real.pi * ‖ζ‖ ^ 2) := by
        rw [show (2:ℝ) * Real.pi * ‖ζ‖ ^ 2 = 2 * (Real.pi * ‖ζ‖ ^ 2) by ring]
        exact Real.log_mul (by norm_num) (by positivity)
      rw [← hN, e1, e2, e3]; ring
    calc |(ζ.re - ζ.im) * (ζ.re + ζ.im)
            + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))|
        = |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
            - 2 * (Real.pi : ℂ) * Complex.I * k).re| := by
          rw [Complex.sub_re, Complex.sub_re, Complex.add_re, hsqre, hlogre, hlogc, hcre0, ← hid]
          congr 1; ring
      _ ≤ 7 / ‖ζ‖ ^ 2 := hre
      _ = 7 / (ζ.re ^ 2 + ζ.im ^ 2) := by rw [hN]
  · -- imaginary part
    have him := (Complex.abs_im_le_norm (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
      - Complex.log (c / 2) - 2 * (Real.pi : ℂ) * Complex.I * k)).trans hk
    have hsqim : (ζ ^ 2).im = 2 * ζ.re * ζ.im := by
      simp only [pow_two, Complex.mul_im]; ring
    have hlogim : (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)).im = Complex.arg ζ := by
      rw [Complex.log_im, Complex.arg_real_mul ζ (Real.sqrt_pos.mpr Real.pi_pos)]
    have hargc : Complex.arg (c / 2) = c.im * (Real.pi / 4) := by
      have h : c / 2 = ((1 / 2 : ℝ) : ℂ) * c := by push_cast; ring
      rw [h, Complex.arg_real_mul c (by norm_num : (0:ℝ) < 1 / 2)]
      exact fresnel_arg_c hcre hcim
    have hlogcim : (Complex.log (c / 2)).im = c.im * (Real.pi / 4) := by
      rw [Complex.log_im, hargc]
    have hcim0 : (2 * (Real.pi : ℂ) * Complex.I * k).im = 2 * Real.pi * (k:ℝ) := by
      simp [Complex.mul_re, Complex.mul_im]
    have harg : Complex.arg ζ
        = Real.pi / 4 - Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) :=
      arg_eq_pi_div_four_sub_arctan hx hy
    have hcomp : (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
        - 2 * (Real.pi : ℂ) * Complex.I * k).im
        = 2 * ζ.re * ζ.im + (Real.pi / 4 - Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)))
          - c.im * (Real.pi / 4) - 2 * Real.pi * (k:ℝ) := by
      rw [Complex.sub_im, Complex.sub_im, Complex.add_im, hsqim, hlogim, hlogcim, hcim0, harg]
    have h2 : |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
        - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))
        - (4 * Real.pi * (k:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))|
        = 2 * |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
            - 2 * (Real.pi : ℂ) * Complex.I * k).im| := by
      rw [hcomp, ← abs_of_pos (show (0:ℝ) < 2 by norm_num), ← abs_mul]
      congr 1; ring
    rw [h2]
    have h3 : (2:ℝ) * (7 / ‖ζ‖ ^ 2) = 14 / (ζ.re ^ 2 + ζ.im ^ 2) := by rw [hN]; ring
    calc 2 * |(ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
          - 2 * (Real.pi : ℂ) * Complex.I * k).im|
        ≤ 2 * (7 / ‖ζ‖ ^ 2) := by linarith [him]
      _ = 14 / (ζ.re ^ 2 + ζ.im ^ 2) := h3


set_option maxHeartbeats 1000000 in
-- no-dlmf: sector data for a Fresnel zero from its crude match; proof infrastructure
/-- **Sector data from the crude match.**  A point matching the index parameters `(λ, μ)` in
the crude sense lies strictly below the diagonal, deep inside the first-quadrant sector, and
has `‖ζ‖² = 2λ² + O(1/5)`. -/
theorem fresnel713_match_sector {lam mu : ℝ} {ζ : ℂ} (hlam : 100 ≤ lam)
    (hmu5 : 5 ≤ mu) (hmu3 : mu + 3 ≤ lam)
    (hM1 : |(ζ.re - ζ.im) + mu / (2 * lam)| ≤ 1 / lam ^ 2)
    (hM2 : |(ζ.re + ζ.im) - 2 * lam| ≤ 1 / (70 * lam)) :
    ζ.re < ζ.im ∧ 25 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 6 * ζ.re ∧ ‖ζ‖ ≤ 6 * ζ.im ∧
      |‖ζ‖ ^ 2 - 2 * lam ^ 2| ≤ 1 / 5 := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  have hnorm : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnn : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg ζ
  set d : ℝ := ζ.re - ζ.im with hddef
  set s : ℝ := ζ.re + ζ.im with hsdef
  have hA1 := abs_le.mp hM1
  have hA2 := abs_le.mp hM2
  have he1 : (1:ℝ) / lam ^ 2 ≤ 1 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have he2 : (1:ℝ) / (70 * lam) ≤ 1 / 7000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hmuub : mu / (2 * lam) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hmulb : (5:ℝ) / (2 * lam) ≤ mu / (2 * lam) := by gcongr
  have hmunn : (0:ℝ) ≤ mu / (2 * lam) := by positivity
  have hcmp : (1:ℝ) / lam ^ 2 < 5 / (2 * lam) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hdneg : d < 0 := by linarith [hA1.2, hmulb, hcmp, he1]
  have hsub : ζ.re < ζ.im := by rw [hddef] at hdneg; linarith
  have hdabs : |d| ≤ 0.51 := by
    rw [abs_le]
    constructor <;> linarith [hA1.1, hA1.2, hmuub, hmunn, he1]
  have hdb := abs_le.mp hdabs
  have hd2 : d ^ 2 ≤ 0.2601 := by nlinarith [hdb.1, hdb.2]
  have hs1 : 2 * lam - 1 / 7000 ≤ s := by linarith [hA2.1, he2]
  have hs2 : s ≤ 2 * lam + 1 / 7000 := by linarith [hA2.2, he2]
  have hspos : (0:ℝ) < s := by linarith
  -- `|s² − 4λ²|`
  have hsq : |s ^ 2 - 4 * lam ^ 2| ≤ 0.058 := by
    have hfac : |s ^ 2 - 4 * lam ^ 2| = |s - 2 * lam| * (s + 2 * lam) := by
      rw [← abs_of_pos (show (0:ℝ) < s + 2 * lam by linarith), ← abs_mul]
      congr 1; ring
    have hb : |s - 2 * lam| * (s + 2 * lam) ≤ (1 / (70 * lam)) * (4 * lam + 1 / 7000) := by
      refine mul_le_mul hM2 (by linarith) (by linarith) (by positivity)
    have hval : (1 / (70 * lam)) * (4 * lam + 1 / 7000) ≤ 0.058 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    linarith [hfac.le, hfac.ge, hb, hval]
  have hsqb := abs_le.mp hsq
  have hNid : 2 * ‖ζ‖ ^ 2 = s ^ 2 + d ^ 2 := by rw [hnorm, hsdef, hddef]; ring
  have hNm : |‖ζ‖ ^ 2 - 2 * lam ^ 2| ≤ 1 / 5 := by
    rw [abs_le]
    constructor <;> linarith [hsqb.1, hsqb.2, hd2, sq_nonneg d, hNid]
  have hNb := abs_le.mp hNm
  have h25 : (25:ℝ) ≤ ‖ζ‖ := by
    have hb : (625:ℝ) ≤ ‖ζ‖ ^ 2 := by linarith [hNb.1, hlam2]
    have h4 := Real.sqrt_le_sqrt hb
    rwa [show Real.sqrt 625 = 25 by
      rw [show (625:ℝ) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 25)],
      Real.sqrt_sq hnn] at h4
  have hrelb : lam - 0.2551 ≤ ζ.re := by
    have : ζ.re = (s + d) / 2 := by rw [hsdef, hddef]; ring
    rw [this]; linarith [hs1, hdb.1]
  have himlb : lam - 0.2551 ≤ ζ.im := by
    have : ζ.im = (s - d) / 2 := by rw [hsdef, hddef]; ring
    rw [this]; linarith [hs1, hdb.2, hdneg]
  have hrepos : (0:ℝ) < ζ.re := by linarith
  have himpos : (0:ℝ) < ζ.im := by linarith
  have hkey : ∀ t : ℝ, lam - 0.2551 ≤ t → ‖ζ‖ ≤ 6 * t := by
    intro t ht
    have htpos : (0:ℝ) < t := by linarith
    have hsq0 : (lam - 0.2551) * (lam - 0.2551) ≤ t * t :=
      mul_self_le_mul_self (by linarith) ht
    have hlin : (0:ℝ) ≤ lam * (34 * lam - 19) := mul_nonneg hlam0.le (by linarith)
    have h1 : 2 * lam ^ 2 + 1 / 5 ≤ (6 * t) ^ 2 := by linarith [hsq0, hlin]
    have h2 : ‖ζ‖ ^ 2 ≤ (6 * t) ^ 2 := by linarith [hNb.2, h1]
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 6 * t)] at h4
  exact ⟨hsub, h25, hkey _ hrelb, hkey _ himlb, hNm⟩

set_option maxHeartbeats 1000000 in
-- no-dlmf: at most one Fresnel zero per index; proof infrastructure
/-- **At most one zero per index.**  Two sub-diagonal solutions of the Fresnel zero equation
matching the same index parameters `(λ, μ)` coincide: their separation `≤ 3/(50λ)` is well
inside the `1/(24‖ζ‖)` radius of `fresnel_zero_unique_in_small_ball`. -/
theorem fresnel713_zero_index_unique {c : ℂ} {lam mu : ℝ} {ζ ζ' : ℂ}
    (hcn2 : ‖c‖ ^ 2 = 2) (hlam : 100 ≤ lam) (hmu5 : 5 ≤ mu) (hmu3 : mu + 3 ≤ lam)
    (hz : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0)
    (hz' : 2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ') - c * cerfc ζ' = 0)
    (hM1 : |(ζ.re - ζ.im) + mu / (2 * lam)| ≤ 1 / lam ^ 2)
    (hM2 : |(ζ.re + ζ.im) - 2 * lam| ≤ 1 / (70 * lam))
    (hM1' : |(ζ'.re - ζ'.im) + mu / (2 * lam)| ≤ 1 / lam ^ 2)
    (hM2' : |(ζ'.re + ζ'.im) - 2 * lam| ≤ 1 / (70 * lam)) :
    ζ = ζ' := by
  have hlam0 : (0:ℝ) < lam := by linarith
  have hlam2 : (10000:ℝ) ≤ lam ^ 2 := by nlinarith
  obtain ⟨hsub, h25, h6re, h6im, hN⟩ := fresnel713_match_sector hlam hmu5 hmu3 hM1 hM2
  obtain ⟨hsub', -, -, -, -⟩ := fresnel713_match_sector hlam hmu5 hmu3 hM1' hM2'
  have hNb := abs_le.mp hN
  -- the separation of the two matches
  have hΔd : |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2 ≤ 2 := by
    have hb : |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| ≤ 1 / lam ^ 2 + 1 / lam ^ 2 := by
      have h := abs_le.mp hM1
      have h' := abs_le.mp hM1'
      rw [abs_le]; constructor <;> linarith [h.1, h.2, h'.1, h'.2]
    have h2 : (1:ℝ) / lam ^ 2 * lam ^ 2 = 1 := by field_simp
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ lam ^ 2)
    nlinarith [h3, h2.le, h2.ge]
  have hΔs : |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam) ≤ 1 := by
    have hb : |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| ≤ 1 / (70 * lam) + 1 / (70 * lam) := by
      have h := abs_le.mp hM2
      have h' := abs_le.mp hM2'
      rw [abs_le]; constructor <;> linarith [h.1, h.2, h'.1, h'.2]
    have h2 : (1:ℝ) / (70 * lam) * (35 * lam) = 1 / 2 := by field_simp; ring
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 35 * lam)
    nlinarith [h3, h2.le, h2.ge]
  -- the distance
  have hdiff : ‖ζ' - ζ‖ ^ 2 = (ζ'.re - ζ.re) ^ 2 + (ζ'.im - ζ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [Complex.sub_re, Complex.sub_im]; ring
  have hH1 : 2 * ‖ζ' - ζ‖ ^ 2 * lam ^ 4 ≤ lam ^ 2 / 1225 + 4 := by
    have hds : ((ζ'.re + ζ'.im) - (ζ.re + ζ.im)) ^ 2 * (1225 * lam ^ 2) ≤ 1 := by
      have h0 : (0:ℝ) ≤ |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam) := by positivity
      have h := mul_self_le_mul_self h0 hΔs
      have he : |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam)
          * (|(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam))
          = ((ζ'.re + ζ'.im) - (ζ.re + ζ.im)) ^ 2 * (1225 * lam ^ 2) := by
        rw [show |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam)
            * (|(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| * (35 * lam))
            = |(ζ'.re + ζ'.im) - (ζ.re + ζ.im)| ^ 2 * (1225 * lam ^ 2) by ring, sq_abs]
      linarith [h, he.le, he.ge]
    have hdd : ((ζ'.re - ζ'.im) - (ζ.re - ζ.im)) ^ 2 * lam ^ 4 ≤ 4 := by
      have h0 : (0:ℝ) ≤ |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2 := by positivity
      have h := mul_self_le_mul_self h0 hΔd
      have he : |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2
          * (|(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2)
          = ((ζ'.re - ζ'.im) - (ζ.re - ζ.im)) ^ 2 * lam ^ 4 := by
        rw [show |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2
            * (|(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| * lam ^ 2)
            = |(ζ'.re - ζ'.im) - (ζ.re - ζ.im)| ^ 2 * lam ^ 4 by ring, sq_abs]
      linarith [h, he.le, he.ge]
    have hid : 2 * ((ζ'.re - ζ.re) ^ 2 + (ζ'.im - ζ.im) ^ 2)
        = ((ζ'.re + ζ'.im) - (ζ.re + ζ.im)) ^ 2 + ((ζ'.re - ζ'.im) - (ζ.re - ζ.im)) ^ 2 := by
      ring
    rw [hdiff]
    nlinarith [hds, hdd, hid, sq_nonneg lam, hlam0, hlam2]
  have hH2 : ‖ζ‖ ^ 2 ≤ 2 * lam ^ 2 + 1 / 5 := by linarith [hNb.2]
  have hpoly : 576 * ((lam ^ 2 / 1225 + 4) * (2 * lam ^ 2 + 1 / 5)) ≤ 2 * lam ^ 4 := by
    have h := mul_nonneg (sq_nonneg lam) (by linarith : (0:ℝ) ≤ lam ^ 2 - 10000)
    nlinarith [h, hlam2]
  have hstep : 2 * ‖ζ' - ζ‖ ^ 2 * lam ^ 4 * ‖ζ‖ ^ 2
      ≤ (lam ^ 2 / 1225 + 4) * (2 * lam ^ 2 + 1 / 5) := by
    have h1 : 2 * ‖ζ' - ζ‖ ^ 2 * lam ^ 4 * ‖ζ‖ ^ 2 ≤ (lam ^ 2 / 1225 + 4) * ‖ζ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hH1 (sq_nonneg _)
    have h2 : (lam ^ 2 / 1225 + 4) * ‖ζ‖ ^ 2 ≤ (lam ^ 2 / 1225 + 4) * (2 * lam ^ 2 + 1 / 5) :=
      mul_le_mul_of_nonneg_left hH2 (by positivity)
    linarith
  have hfin : (576 * (‖ζ' - ζ‖ ^ 2 * ‖ζ‖ ^ 2)) * (2 * lam ^ 4) ≤ 1 * (2 * lam ^ 4) := by
    linarith [hstep, hpoly]
  have hsq1 : 576 * (‖ζ' - ζ‖ ^ 2 * ‖ζ‖ ^ 2) ≤ 1 :=
    le_of_mul_le_mul_right hfin (by positivity)
  have hprodnn : (0:ℝ) ≤ 24 * ‖ζ' - ζ‖ * ‖ζ‖ := by positivity
  have hprod : 24 * ‖ζ' - ζ‖ * ‖ζ‖ ≤ 1 := by nlinarith [hsq1, hprodnn]
  have hdist : ‖ζ' - ζ‖ ≤ 1 / (24 * ‖ζ‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hprod]
  exact fresnel_zero_unique_in_small_ball hcn2 h6re h6im h25 hz hz' (le_of_lt hsub)
    (le_of_lt hsub') (by simp) hdist

set_option maxHeartbeats 4000000 in
-- no-dlmf: existence of the Fresnel zero attached to each large index; proof infrastructure
/-- **The grid zero at index `n`.**  For every index `n` whose parameter `λ = ½√π λ_F(n)` is at
least `100`, the Fresnel zero equation has a sub-diagonal solution matching the index
parameters, together with the two `λ`-denominated component bounds.

The zero is the one produced near the `n`-th model root of `√π ζ e^{ζ²} = c/2` by
`exists_fresnel_zero_near_model`; the only extra step is *index pinning* — the integer `k`
supplied by `fresnel_zero_log_equation` must be `n`, because the model root satisfies
`ζ₀² + log(√π ζ₀) − log(c/2) = 2πi n` exactly while `‖ζ − ζ₀‖ < 12/‖ζ₀‖³` moves
`z ↦ z² + log(√π z)` by far less than `2π`. -/
theorem fresnel713_grid_zero {c : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    {lam mu : ℝ} (n : ℕ) (hlam : 100 ≤ lam)
    (hQ : 4 * lam ^ 2 = 4 * Real.pi * (n:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))
    (hmu : 2 * mu = Real.log (4 * Real.pi * lam ^ 2)) :
    ∃ ζ : ℂ, (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) ∧
      0 < ζ.re ∧ ζ.re < ζ.im ∧
      |(ζ.re - ζ.im) + mu / (2 * lam)| ≤ 1 / lam ^ 2 ∧
      |(ζ.re + ζ.im) - 2 * lam| ≤ 1 / (70 * lam) ∧
      |(ζ.re - ζ.im) * (ζ.re + ζ.im)
          + (1 / 2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))| ≤ 4 / lam ^ 2 ∧
      |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
          - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) - 4 * lam ^ 2| ≤ 8 / lam ^ 2 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsplb : (1.7:ℝ) ≤ Real.sqrt Real.pi := by nlinarith [Real.sqrt_nonneg Real.pi]
  have hcn2 : ‖c‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcre]
    rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcn : ‖c‖ = Real.sqrt 2 := by rw [← hcn2, Real.sqrt_sq (norm_nonneg c)]
  have hc0 : c ≠ 0 := by intro h; rw [h] at hcn2; simp at hcn2
  have hc20 : c / 2 ≠ 0 := div_ne_zero hc0 (by norm_num)
  have hcimabs : |c.im| = 1 := by rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcimle : c.im ≤ 1 := by rcases hcim with h | h <;> rw [h] <;> norm_num
  -- the index is large
  have hn3184 : 3184 ≤ n := by
    have h1 : (40000:ℝ) ≤ 4 * lam ^ 2 := by nlinarith
    have h2 : (40000:ℝ) ≤ 4 * Real.pi * (n:ℝ) := by
      nlinarith [hQ, h1,
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - c.im) (by linarith : (0:ℝ) ≤ Real.pi)]
    have h3 : (3183:ℝ) < (n:ℝ) := by nlinarith
    have h4 : 3183 < n := by exact_mod_cast h3
    omega
  have hn' : (3184:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn3184
  -- the shift `κ = log (c/2)`
  set κ : ℂ := Complex.log (c / 2) with hκdef
  have hexpκ : Complex.exp κ = c / 2 := Complex.exp_log hc20
  have hargc : Complex.arg (c / 2) = c.im * (Real.pi / 4) := by
    have h : c / 2 = ((1 / 2 : ℝ) : ℂ) * c := by push_cast; ring
    rw [h, Complex.arg_real_mul c (by norm_num : (0:ℝ) < 1 / 2)]
    exact fresnel_arg_c hcre hcim
  have hκim : κ.im = c.im * (Real.pi / 4) := by rw [hκdef, Complex.log_im, hargc]
  have hκreval : κ.re = -((1 / 2) * Real.log 2) := by
    rw [hκdef, Complex.log_re, norm_div, hcn]
    rw [show ‖(2:ℂ)‖ = 2 by norm_num, Real.log_div (by positivity) (by norm_num),
      Real.log_sqrt (by norm_num)]
    ring
  have hlog2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hκreneg : κ.re < 0 := by rw [hκreval]; linarith
  have hκreabs : |κ.re| ≤ 0.35 := by rw [hκreval, abs_le]; constructor <;> linarith
  have hκimabs : |κ.im| ≤ 0.79 := by
    rw [hκim, abs_mul, hcimabs, one_mul, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 4)]
    linarith
  have hκ : ‖κ‖ ≤ 1 := by
    have hnsq : ‖κ‖ ^ 2 = κ.re ^ 2 + κ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h1 : κ.re ^ 2 ≤ 0.1225 := by
      have := mul_self_le_mul_self (abs_nonneg κ.re) hκreabs
      nlinarith [this, sq_abs κ.re]
    have h2 : κ.im ^ 2 ≤ 0.6241 := by
      have := mul_self_le_mul_self (abs_nonneg κ.im) hκimabs
      nlinarith [this, sq_abs κ.im]
    nlinarith [hnsq, h1, h2, norm_nonneg κ]
  -- the model root
  obtain ⟨ζ₀, hζ₀n, hζ₀re6, hζ₀im6, hζ₀sub, hζ₀loc, hζ₀log, hζ₀model⟩ :=
    exists_model_root_fresnel hκ n (by omega)
  have h2pin : ‖2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)‖ = 2 * Real.pi * (n:ℝ) := by
    have hid : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n:ℂ)
        = ((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hid, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hVsq : (10000:ℝ) ≤ ‖ζ₀‖ ^ 2 := by
    have h1 := norm_sub_norm_le (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (ζ₀ ^ 2)
    rw [h2pin, norm_pow, norm_sub_rev (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) (ζ₀ ^ 2)] at h1
    nlinarith [hζ₀loc, h1]
  have hV : (100:ℝ) ≤ ‖ζ₀‖ := by
    have h4 := Real.sqrt_le_sqrt hVsq
    rwa [show Real.sqrt 10000 = 100 by
      rw [show (10000:ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 100)],
      Real.sqrt_sq (norm_nonneg ζ₀)] at h4
  have hre1 : (1:ℝ) ≤ ζ₀.re := by linarith
  have him1 : (1:ℝ) ≤ ζ₀.im := by linarith
  obtain ⟨ζ, hzζ, hζb⟩ :=
    exists_fresnel_zero_near_model hcn2 hre1 him1 (by linarith) (hζ₀model.trans hexpκ)
  set V : ℝ := ‖ζ₀‖ with hVdef
  set ρ : ℝ := 12 / V ^ 3 with hρdef
  have hV0 : (0:ℝ) < V := by linarith
  have hV3 : (1000000:ℝ) ≤ V ^ 3 := by nlinarith
  have hρ0 : (0:ℝ) < ρ := by rw [hρdef]; positivity
  have hρsmall : ρ ≤ 1 / 80000 := by
    rw [hρdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hζv : ‖ζ - ζ₀‖ ≤ ρ := hζb.le
  have hrediff : |ζ.re - ζ₀.re| ≤ ρ := by
    have h := Complex.abs_re_le_norm (ζ - ζ₀)
    simp only [Complex.sub_re] at h; linarith
  have himdiff : |ζ.im - ζ₀.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (ζ - ζ₀)
    simp only [Complex.sub_im] at h; linarith
  have hrd := abs_le.mp hrediff
  have hid := abs_le.mp himdiff
  have hζn1 : V - ρ ≤ ‖ζ‖ := by
    have h := norm_sub_norm_le ζ₀ ζ
    rw [norm_sub_rev ζ₀ ζ] at h; linarith
  have hζn2 : ‖ζ‖ ≤ V + ρ := by
    have h := norm_sub_norm_le ζ ζ₀; linarith
  have hζre : (0:ℝ) < ζ.re := by linarith [hrd.1]
  have hζn20 : (20:ℝ) ≤ ‖ζ‖ := by linarith
  -- sub-diagonality
  have hζ₀resq : (ζ₀ ^ 2).re = κ.re - Real.log (Real.sqrt Real.pi * V) := by
    have h := congrArg Complex.re hζ₀log
    have hl : (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)).re
        = Real.log (Real.sqrt Real.pi * V) := by
      rw [Complex.log_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), hVdef]
    have hr : (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.sub_re, Complex.add_re, hl, hr] at h
    linarith
  have hlogbig : (5:ℝ) ≤ Real.log (Real.sqrt Real.pi * V) := by
    have hexp5 : Real.exp 5 ≤ 149 := by
      have h1' : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      have h2' : Real.exp 5 = Real.exp 1 ^ (5:ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2']
      have h3' : Real.exp 1 ^ (5:ℕ) ≤ (2.7182818286:ℝ) ^ (5:ℕ) := by gcongr
      refine h3'.trans ?_
      norm_num
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith
  have hprodneg : (ζ₀.re - ζ₀.im) * (ζ₀.re + ζ₀.im) ≤ -5 := by
    have hsq : (ζ₀ ^ 2).re = ζ₀.re ^ 2 - ζ₀.im ^ 2 := by simp [pow_two, Complex.mul_re]
    nlinarith [hζ₀resq, hsq, hκreneg, hlogbig]
  have hζ₀rele : ζ₀.re ≤ V := by
    rw [hVdef]; exact le_trans (le_abs_self _) (Complex.abs_re_le_norm ζ₀)
  have hζ₀imle : ζ₀.im ≤ V := by
    rw [hVdef]; exact le_trans (le_abs_self _) (Complex.abs_im_le_norm ζ₀)
  have hsumpos : (0:ℝ) < ζ₀.re + ζ₀.im := by linarith
  have hdiffneg : ζ₀.re - ζ₀.im < 0 := by linarith
  have hgap : ζ₀.re - ζ₀.im ≤ -5 / (2 * V) := by
    have h1 : (ζ₀.re - ζ₀.im) * (2 * V) ≤ (ζ₀.re - ζ₀.im) * (ζ₀.re + ζ₀.im) :=
      mul_le_mul_of_nonpos_left (by linarith) (le_of_lt hdiffneg)
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * V)]
    linarith [h1, hprodneg]
  have hsmallgap : (24:ℝ) / V ^ 3 < 5 / (2 * V) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hζsub : ζ.re < ζ.im := by
    have h2ρ : (2:ℝ) * ρ = 24 / V ^ 3 := by rw [hρdef]; ring
    have : ζ.re - ζ.im ≤ (ζ₀.re - ζ₀.im) + 2 * ρ := by linarith [hrd.2, hid.1]
    have hneg : (ζ₀.re - ζ₀.im) + 2 * ρ < 0 := by
      rw [h2ρ]
      have hd : -5 / (2 * V) + 24 / V ^ 3 < 0 := by
        rw [neg_div]; linarith [hsmallgap]
      linarith [hgap]
    linarith
  -- the index equation and its pinning
  obtain ⟨k, hk⟩ := fresnel_zero_log_equation hcn2 hζre hζsub.le hζn20 hzζ
  rw [← hκdef] at hk
  have hmemball : ∀ z ∈ Metric.closedBall ζ₀ ρ, 0 < z.re ∧ V - ρ ≤ ‖z‖ := by
    intro z hz
    have hzv : ‖z - ζ₀‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - ζ₀)
    simp only [Complex.sub_re] at h
    have h1 := abs_le.mp (le_trans h hzv)
    have h2 := norm_sub_norm_le ζ₀ z
    rw [norm_sub_rev ζ₀ z] at h2
    exact ⟨by linarith [h1.1], by linarith⟩
  have hζcb : ζ ∈ Metric.closedBall ζ₀ ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hζv
  have hlogmvt : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
      - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)‖ ≤ (1 / (V - ρ)) * ‖ζ - ζ₀‖ := by
    refine norm_sub_le_of_hasDerivAt_le
      (f := fun z : ℂ => Complex.log ((Real.sqrt Real.pi : ℂ) * z))
      (f' := fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) / ((Real.sqrt Real.pi : ℂ) * z))
      (convex_closedBall ζ₀ ρ) ?_ ?_ (Metric.mem_closedBall_self hρ0.le) hζcb
    · intro z hz
      obtain ⟨hz1, hz2⟩ := hmemball z hz
      have hslit : ((Real.sqrt Real.pi : ℂ)) * z ∈ Complex.slitPlane := by
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        positivity
      have h1 : HasDerivAt (fun z : ℂ => ((Real.sqrt Real.pi : ℂ)) * z)
          ((Real.sqrt Real.pi : ℂ)) z := by
        simpa using (hasDerivAt_id z).const_mul ((Real.sqrt Real.pi : ℂ))
      exact h1.clog hslit
    · intro z hz
      obtain ⟨hz1, hz2⟩ := hmemball z hz
      have hzn : (0:ℝ) < ‖z‖ := by linarith
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsppos,
        div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [hz2, hsppos]
  have hkn : k = (n:ℤ) := by
    by_contra hne
    have hid2 : 2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))
        = (ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - κ
             - 2 * (Real.pi : ℂ) * Complex.I * (k:ℂ))
          - ((ζ ^ 2 - ζ₀ ^ 2)
             + (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
                - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))) := by
      linear_combination -hζ₀log
    have hp1 : ‖ζ ^ 2 - ζ₀ ^ 2‖ ≤ 1 / 100 := by
      have hfac : ζ ^ 2 - ζ₀ ^ 2 = (ζ - ζ₀) * (ζ + ζ₀) := by ring
      have h1 : ‖ζ + ζ₀‖ ≤ 2 * V + ρ := by
        have h := norm_add_le ζ ζ₀; linarith
      have h2 : ‖ζ ^ 2 - ζ₀ ^ 2‖ ≤ ρ * (2 * V + ρ) := by
        rw [hfac, norm_mul]
        exact mul_le_mul hζv h1 (norm_nonneg _) hρ0.le
      have hb2 : ρ * (2 * V + ρ) ≤ 1 / 100 := by
        rw [hρdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hρsmall, hV0, hV3]
      linarith
    have hp2 : ‖Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
        - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀)‖ ≤ 1 / 100 := by
      have h1 : 1 / (V - ρ) ≤ 1 / 99 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h2 : (1 / (V - ρ)) * ‖ζ - ζ₀‖ ≤ (1 / 99) * (1 / 80000) :=
        mul_le_mul h1 (by linarith) (norm_nonneg _) (by norm_num)
      linarith
    have hp0 : (7:ℝ) / ‖ζ‖ ^ 2 ≤ 1 / 100 := by
      have hb : (9000:ℝ) ≤ ‖ζ‖ ^ 2 := by nlinarith [hζn1, hρsmall, hV0]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hub : ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ ≤ 1 := by
      rw [hid2]
      refine (norm_sub_le _ _).trans ?_
      have hsec := norm_add_le (ζ ^ 2 - ζ₀ ^ 2)
        (Complex.log ((Real.sqrt Real.pi : ℂ) * ζ)
          - Complex.log ((Real.sqrt Real.pi : ℂ) * ζ₀))
      linarith [hk, hp0, hp1, hp2, hsec]
    have hlb : (6:ℝ) ≤ ‖2 * (Real.pi:ℂ) * Complex.I * ((n:ℂ) - (k:ℂ))‖ := by
      have hne' : ((n:ℤ) - k) ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
      have habs : (1:ℤ) ≤ |(n:ℤ) - k| := Int.one_le_abs hne'
      have hm : ((n:ℂ) - (k:ℂ)) = (((n:ℤ) - k : ℤ) : ℂ) := by push_cast; ring
      rw [hm, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((((n:ℤ) - k : ℤ)) : ℂ)
          = ((2 * Real.pi * ((((n:ℤ) - k : ℤ)) : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      have hcast1 : (1:ℝ) ≤ |((((n:ℤ) - k : ℤ)) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast habs
      nlinarith [hcast1]
    linarith
  rw [hkn] at hk
  have hk' : ‖ζ ^ 2 + Complex.log ((Real.sqrt Real.pi : ℂ) * ζ) - Complex.log (c / 2)
      - 2 * (Real.pi : ℂ) * Complex.I * ((n:ℤ):ℂ)‖ ≤ 7 / ‖ζ‖ ^ 2 := by
    rw [hκdef] at hk; exact hk
  obtain ⟨key1, key2⟩ :=
    fresnel_zero_components_of_log hcre hcim hζre hζsub hζn20 hk'
  -- convert the `N`-budgets to `λ`-budgets
  have hnormid : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hNbig : (400:ℝ) ≤ ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [← hnormid]; nlinarith [hζn1, hρsmall, hV0]
  have hs : (0:ℝ) < ζ.re + ζ.im := by linarith [hζsub, hζre]
  have hNsd : 2 * (ζ.re ^ 2 + ζ.im ^ 2) = (ζ.re + ζ.im) ^ 2 + (ζ.re - ζ.im) ^ 2 := by ring
  have hd2s : (ζ.re - ζ.im) ^ 2 ≤ (ζ.re + ζ.im) ^ 2 := by nlinarith [hζre, hζsub]
  have hAbd : |Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im))]
    · linarith [Real.arctan_lt_pi_div_two ((ζ.re - ζ.im) / (ζ.re + ζ.im))]
  have hQ' : 4 * Real.pi * (((n:ℤ)):ℝ) - Real.pi / 2 + c.im * (Real.pi / 2) = 4 * lam ^ 2 := by
    push_cast; linarith [hQ]
  rw [hQ'] at key2
  obtain ⟨-, -, he1, he2⟩ :=
    fresnel713_modulus hlam0 hNbig rfl hs hNsd hd2s hAbd key1 key2
  have key1' := le_trans key1 he1
  have key2' := le_trans key2 he2
  obtain ⟨hM1, hM2, -⟩ :=
    fresnel713_match_of_key hlam hmu hs hNsd hd2s
      (abs_arctan_sub_self_le ((ζ.re - ζ.im) / (ζ.re + ζ.im))) key1' key2'
  exact ⟨ζ, hzζ, hζre, hζsub, hM1, hM2, key1', key2'⟩

set_option maxHeartbeats 4000000 in
-- no-dlmf: the DLMF index of the enumeration of sub-diagonal Fresnel zeros; proof infrastructure
/-- **The enumeration is the index family from index 3300 on.**  For a complete, strictly
modulus-increasing, 1-based enumeration `z` of the sub-diagonal first-quadrant zeros of a
Fresnel integral `f` whose small zeros number `3299`, the `m`-th entry satisfies the two real
component equations *at index `m`* for every `m ≥ 3300`.

The proof follows the `erf_7_13_3` template: the grid zeros `W m` (`fresnel713_grid_zero`)
have `‖·‖²` within `1/5` of `2λ_m²`, and consecutive grid values are `2π` apart, so they are
strictly modulus-increasing and injective; every sector zero above the cut carries an index
(`fresnel_zero_index_exists` + `fresnel713_match_of_key`) and is *the* grid zero of that index
(`fresnel713_zero_index_unique`); a strictly monotone surjection onto a tail of `ℕ` is a shift,
and the count of the zeros below the cut pins the shift to zero. -/
theorem fresnel713_enumeration
    {c : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    {f : ℂ → ℂ}
    (hlink : ∀ w : ℂ, 4 * f w
      = 2 - (starRingEnd ℂ) c
            * cerfc (-Complex.I * ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
        - c * cerfc ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
    {Lam Mu : ℕ → ℝ}
    (hLamQ : ∀ m : ℕ, 1 ≤ m → 4 * (Lam m) ^ 2
        = 4 * Real.pi * (m:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))
    (hLampos : ∀ m : ℕ, 1 ≤ m → 0 < Lam m)
    (hLam100 : ∀ m : ℕ, 3300 ≤ m → 100 ≤ Lam m)
    (hMu : ∀ m : ℕ, 1 ≤ m → 2 * Mu m = Real.log (4 * Real.pi * (Lam m) ^ 2))
    (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → f (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, f w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w)
    (hcount : {w : ℂ | f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
        ‖w‖ ^ 2 < 4 * 3300 + (c.im - 1) / 2 - 2}.ncard = 3299) :
    ∀ m : ℕ, 3300 ≤ m → ∀ ζ : ℂ,
      ζ = (1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z m →
      0 < ζ.re ∧ ζ.re < ζ.im ∧
       |(ζ.re - ζ.im) * (ζ.re + ζ.im)
          + (1/2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))| ≤ 4 / (Lam m) ^ 2 ∧
       |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
          - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) - 4 * (Lam m) ^ 2|
          ≤ 8 / (Lam m) ^ 2 := by
  classical
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hcn2 : ‖c‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hcre]
    rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcimle : c.im ≤ 1 := by rcases hcim with h | h <;> rw [h] <;> norm_num
  have hcimge : -1 ≤ c.im := by rcases hcim with h | h <;> rw [h] <;> norm_num
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- the linear change of variable
  set A : ℂ := (1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) with hAdef
  have hAnormsq : ‖A‖ ^ 2 = Real.pi / 2 := by
    have h := fresnel_zeta_norm_sq 1
    simpa [hAdef] using h
  have hAnorm0 : (0:ℝ) < ‖A‖ := by nlinarith [norm_nonneg A, hAnormsq, Real.pi_pos]
  have hA0 : A ≠ 0 := by
    intro h; rw [h] at hAnorm0; simp at hAnorm0
  have hAmul : ∀ w : ℂ, ‖A * w‖ ^ 2 = (Real.pi / 2) * ‖w‖ ^ 2 := by
    intro w; rw [norm_mul, mul_pow, hAnormsq]
  have hAre : ∀ w : ℂ, (A * w).re = (1/2) * Real.sqrt Real.pi * (w.re - w.im) := by
    intro w; rw [hAdef]; exact fresnel_zeta_re w
  have hAim : ∀ w : ℂ, (A * w).im = (1/2) * Real.sqrt Real.pi * (w.re + w.im) := by
    intro w; rw [hAdef]; exact fresnel_zeta_im w
  have hsector : ∀ w : ℂ, (0 < w.im ∧ w.im < w.re) ↔ (0 < (A * w).re ∧ (A * w).re < (A * w).im) := by
    intro w
    rw [hAre, hAim]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  have hzeroiff : ∀ w : ℂ, f w = 0 ↔
      2 - (starRingEnd ℂ) c * cerfc (-Complex.I * (A * w)) - c * cerfc (A * w) = 0 := by
    intro w
    have h := hlink w
    constructor
    · intro hw; rw [← h, hw]; ring
    · intro hw; rw [hw] at h; linear_combination h / 4
  -- the index grid
  set G : ℕ → ℝ := fun m => 4 * (m:ℝ) + (c.im - 1) / 2 with hGdef
  have hLamG : ∀ m : ℕ, 1 ≤ m → 4 * (Lam m) ^ 2 = Real.pi * G m := by
    intro m hm; rw [hGdef]; simp only; rw [hLamQ m hm]; ring
  have hNlam : ∀ m : ℕ, 1 ≤ m → 2 * (Lam m) ^ 2 = (Real.pi / 2) * G m := by
    intro m hm; have := hLamG m hm; linarith
  set Nc : ℝ := (Real.pi / 2) * (4 * 3300 + (c.im - 1) / 2) - Real.pi with hNcdef
  have hcut : ∀ w : ℂ, ‖w‖ ^ 2 < 4 * 3300 + (c.im - 1) / 2 - 2 ↔ ‖A * w‖ ^ 2 < Nc := by
    intro w
    rw [hAmul, hNcdef]
    constructor
    · intro h; nlinarith [Real.pi_pos]
    · intro h; nlinarith [Real.pi_pos]
  -- the grid zeros, in the `ζ` variable
  have hex : ∀ m : ℕ, ∃ ζ : ℂ, 3300 ≤ m →
      ((2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) ∧
        0 < ζ.re ∧ ζ.re < ζ.im ∧
        |(ζ.re - ζ.im) + Mu m / (2 * Lam m)| ≤ 1 / (Lam m) ^ 2 ∧
        |(ζ.re + ζ.im) - 2 * Lam m| ≤ 1 / (70 * Lam m) ∧
        |(ζ.re - ζ.im) * (ζ.re + ζ.im)
            + (1/2) * Real.log (2 * Real.pi * (ζ.re ^ 2 + ζ.im ^ 2))| ≤ 4 / (Lam m) ^ 2 ∧
        |(ζ.re + ζ.im) ^ 2 - (ζ.re - ζ.im) ^ 2
            - 2 * Real.arctan ((ζ.re - ζ.im) / (ζ.re + ζ.im)) - 4 * (Lam m) ^ 2|
            ≤ 8 / (Lam m) ^ 2) := by
    intro m
    by_cases h : 3300 ≤ m
    · obtain ⟨ζ, h1, h2, h3, h4, h5, h6, h7⟩ :=
        fresnel713_grid_zero hcre hcim m (hLam100 m h) (hLamQ m (by omega)) (hMu m (by omega))
      exact ⟨ζ, fun _ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wz hWz using hex
  have hWnorm : ∀ m : ℕ, 3300 ≤ m → |‖Wz m‖ ^ 2 - (Real.pi / 2) * G m| ≤ 1 / 5 := by
    intro m hm
    obtain ⟨-, -, -, h4, h5, -, -⟩ := hWz m hm
    obtain ⟨-, -, -, -, hN⟩ := fresnel713_match_sector (hLam100 m hm)
      (fresnel713_mu_bounds (hLam100 m hm) (hMu m (by omega))).1
      (fresnel713_mu_bounds (hLam100 m hm) (hMu m (by omega))).2.2 h4 h5
    rw [← hNlam m (by omega)]; exact hN
  have hGmono : ∀ m m' : ℕ, m < m' → G m + 4 ≤ G m' := by
    intro m m' hlt
    have h3 : (m:ℝ) + 1 ≤ (m':ℝ) := by exact_mod_cast hlt
    rw [hGdef]; simp only; linarith
  have hWmono : ∀ m m' : ℕ, 3300 ≤ m → m < m' → ‖Wz m‖ < ‖Wz m'‖ := by
    intro m m' hm hlt
    have hm' : 3300 ≤ m' := by omega
    obtain ⟨a1, a2⟩ := abs_le.mp (hWnorm m hm)
    obtain ⟨b1, b2⟩ := abs_le.mp (hWnorm m' hm')
    have hg := hGmono m m' hlt
    have hsq : ‖Wz m‖ ^ 2 < ‖Wz m'‖ ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [norm_nonneg (Wz m), norm_nonneg (Wz m')]
  have hWinj : ∀ m m' : ℕ, 3300 ≤ m → 3300 ≤ m' → ‖Wz m‖ = ‖Wz m'‖ → m = m' := by
    intro m m' hm hm' heq
    rcases lt_trichotomy m m' with h | h | h
    · exact absurd heq (ne_of_lt (hWmono m m' hm h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hWmono m' m hm' h))
  have hWbig : ∀ m : ℕ, 3300 ≤ m → Nc ≤ ‖Wz m‖ ^ 2 := by
    intro m hm
    obtain ⟨a1, -⟩ := abs_le.mp (hWnorm m hm)
    have hg : G 3300 ≤ G m := by
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]
      · linarith [hGmono 3300 m h]
    rw [hNcdef]
    have : G 3300 = 4 * 3300 + (c.im - 1) / 2 := by rw [hGdef]; norm_num
    nlinarith [Real.pi_pos, hg, this.le, this.ge]
  -- every sector zero above the cut is a grid zero
  have hindex : ∀ ζ : ℂ, (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) →
      0 < ζ.re → ζ.re < ζ.im → Nc ≤ ‖ζ‖ ^ 2 → ∃ n : ℕ, 3300 ≤ n ∧ ζ = Wz n := by
    intro ζ hz hx hxy hbig
    have hnormid : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hNc0 : (20004:ℝ) ≤ Nc := by
      rw [hNcdef]; nlinarith [Real.pi_pos]
    have hbig' : (20004:ℝ) ≤ ζ.re ^ 2 + ζ.im ^ 2 := by rw [← hnormid]; linarith
    obtain ⟨k, lam, hk0, hlam, hkQ, key1, key2⟩ :=
      fresnel_zero_index_exists hcre hcim hx hxy hbig' hz
    set n : ℕ := k.toNat with hndef
    have hkn : (n:ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk0)
    have hcast : ((n:ℕ):ℝ) = ((k:ℤ):ℝ) := by rw [← hkn]; push_cast; ring
    have hlamn : lam = Lam n := by
      have hn1 : 1 ≤ n := by omega
      have h1 : 4 * lam ^ 2 = 4 * (Lam n) ^ 2 := by
        rw [hkQ, hLamQ n hn1, hcast]
      have h2 : lam ^ 2 = (Lam n) ^ 2 := by linarith
      nlinarith [h2, hlam, hLampos n hn1]
    rw [hlamn] at hlam key1 key2
    have hs : (0:ℝ) < ζ.re + ζ.im := by linarith
    have hNsd : 2 * (ζ.re ^ 2 + ζ.im ^ 2) = (ζ.re + ζ.im) ^ 2 + (ζ.re - ζ.im) ^ 2 := by ring
    have hd2s : (ζ.re - ζ.im) ^ 2 ≤ (ζ.re + ζ.im) ^ 2 := by nlinarith
    have hn1' : 1 ≤ n := by omega
    obtain ⟨hM1, hM2, hNm⟩ :=
      fresnel713_match_of_key hlam (hMu n hn1') hs hNsd hd2s
        (abs_arctan_sub_self_le ((ζ.re - ζ.im) / (ζ.re + ζ.im))) key1 key2
    rw [← hnormid] at hNm
    -- the index is at least 3300
    have hn3300 : 3300 ≤ n := by
      by_contra hcon
      have hle : n ≤ 3299 := by omega
      have hG : G n ≤ G 3299 := by
        rcases eq_or_lt_of_le hle with h | h
        · rw [h]
        · linarith [hGmono n 3299 h]
      have h3299 : G 3299 = 4 * 3299 + (c.im - 1) / 2 := by rw [hGdef]; norm_num
      obtain ⟨-, a2⟩ := abs_le.mp hNm
      rw [hNlam n hn1'] at a2
      rw [hNcdef] at hbig
      nlinarith [Real.pi_pos, hG, h3299.le, h3299.ge]
    -- and the zero is *the* grid zero of that index
    obtain ⟨g1, -, -, g4, g5, -, -⟩ := hWz n hn3300
    refine ⟨n, hn3300, ?_⟩
    exact fresnel713_zero_index_unique hcn2 hlam
      (fresnel713_mu_bounds hlam (hMu n hn1')).1
      (fresnel713_mu_bounds hlam (hMu n hn1')).2.2
      hz g1 hM1 hM2 g4 g5
  -- transport the enumeration hypotheses to the `ζ` variable
  have hzeroZ : ∀ n : ℕ, 1 ≤ n →
      2 - (starRingEnd ℂ) c * cerfc (-Complex.I * (A * z n)) - c * cerfc (A * z n) = 0 :=
    fun n hn => (hzeroiff (z n)).mp (hzero n hn)
  have hquadZ : ∀ n : ℕ, 1 ≤ n → 0 < (A * z n).re ∧ (A * z n).re < (A * z n).im :=
    fun n hn => (hsector (z n)).mp (hquad n hn)
  have hnormZ : ∀ w : ℂ, ‖A * w‖ = ‖A‖ * ‖w‖ := fun w => norm_mul A w
  have hmonoZ : ∀ m m' : ℕ, 1 ≤ m → 1 ≤ m' → m < m' → ‖A * z m‖ < ‖A * z m'‖ := by
    intro m m' hm hm' hlt
    rw [hnormZ, hnormZ]
    exact mul_lt_mul_of_pos_left (hmono hm hm' hlt) hAnorm0
  have hallZ : ∀ ζ : ℂ, (2 - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) - c * cerfc ζ = 0) →
      0 < ζ.re → ζ.re < ζ.im → ∃ n, 1 ≤ n ∧ A * z n = ζ := by
    intro ζ hz hx hxy
    have hw : A * (ζ / A) = ζ := by field_simp
    have h1 : f (ζ / A) = 0 := by rw [hzeroiff, hw]; exact hz
    have h2 : 0 < (ζ / A).im ∧ (ζ / A).im < (ζ / A).re := by
      rw [hsector, hw]; exact ⟨hx, hxy⟩
    obtain ⟨n, hn1, hn2⟩ := hall (ζ / A) h1 h2.1 h2.2
    exact ⟨n, hn1, by rw [hn2, hw]⟩
  -- the smallest enumeration index beyond the cut
  have hPne : ∃ m : ℕ, 1 ≤ m ∧ Nc ≤ ‖A * z m‖ ^ 2 := by
    obtain ⟨g1, g2, g3, -, -, -, -⟩ := hWz 3300 (le_refl _)
    obtain ⟨m, hm1, hm2⟩ := hallZ (Wz 3300) g1 g2 g3
    exact ⟨m, hm1, by rw [hm2]; exact hWbig 3300 (le_refl _)⟩
  set M : ℕ := Nat.find hPne with hMdef
  have hM1 : 1 ≤ M := (Nat.find_spec hPne).1
  have hM2 : Nc ≤ ‖A * z M‖ ^ 2 := (Nat.find_spec hPne).2
  have hMmin : ∀ m : ℕ, m < M → ¬(1 ≤ m ∧ Nc ≤ ‖A * z m‖ ^ 2) := fun m hm =>
    Nat.find_min hPne hm
  have hzbig : ∀ m : ℕ, M ≤ m → Nc ≤ ‖A * z m‖ ^ 2 := by
    intro m hm
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h]; exact hM2
    · have hlt : ‖A * z M‖ < ‖A * z m‖ := hmonoZ M m hM1 (by omega) h
      nlinarith [norm_nonneg (A * z M), norm_nonneg (A * z m)]
  have hfex : ∀ m : ℕ, ∃ n : ℕ, M ≤ m → (3300 ≤ n ∧ A * z m = Wz n) := by
    intro m
    by_cases h : M ≤ m
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨q1, q2⟩ := hquadZ m hm1
      obtain ⟨n, hn, heq⟩ := hindex (A * z m) (hzeroZ m hm1) q1 q2 (hzbig m h)
      exact ⟨n, fun _ => ⟨hn, heq⟩⟩
    · exact ⟨3300, fun h' => absurd h' h⟩
  choose F hF using hfex
  have hFmono : ∀ m m' : ℕ, M ≤ m → m < m' → F m < F m' := by
    intro m m' hm hlt
    obtain ⟨hn1, he1⟩ := hF m hm
    obtain ⟨hn2, he2⟩ := hF m' (by omega)
    have hlt' : ‖A * z m‖ < ‖A * z m'‖ := hmonoZ m m' (by omega) (by omega) hlt
    rw [he1, he2] at hlt'
    by_contra hcon
    have hle : F m' ≤ F m := by omega
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at hlt'; exact lt_irrefl _ hlt'
    · exact absurd hlt' (not_lt.mpr (hWmono (F m') (F m) (by omega) h).le)
  have hFsurj : ∀ n : ℕ, F M ≤ n → ∃ m : ℕ, M ≤ m ∧ F m = n := by
    intro n hn
    obtain ⟨hFM1, hFMe⟩ := hF M (le_refl M)
    have hn3300 : 3300 ≤ n := by omega
    obtain ⟨g1, g2, g3, -, -, -, -⟩ := hWz n hn3300
    obtain ⟨m, hm1, hm2⟩ := hallZ (Wz n) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig n hn3300⟩
    obtain ⟨hq1, hq2⟩ := hF m hmM
    have heq : ‖Wz (F m)‖ = ‖Wz n‖ := by rw [← hq2, hm2]
    exact ⟨m, hmM, hWinj _ _ (by omega) (by omega) heq⟩
  have hFform : ∀ m : ℕ, M ≤ m → F m + M = m + F M := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ k ih =>
      intro hm
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; omega
      · have hk : M ≤ k := by omega
        have ihk := ih hk
        have h1 : F k < F (k+1) := hFmono k (k+1) hk (by omega)
        by_contra hcon
        have h2 : F k + 1 < F (k+1) := by omega
        have h3 : F M ≤ F k + 1 := by omega
        obtain ⟨m', hm'1, hm'2⟩ := hFsurj (F k + 1) h3
        rcases Nat.lt_or_ge k m' with h4 | h4
        · have h4' : k + 1 ≤ m' := h4
          rcases eq_or_lt_of_le h4' with h6 | h6
          · rw [← h6] at hm'2; omega
          · have := hFmono (k+1) m' (by omega) h6; omega
        · rcases eq_or_lt_of_le h4 with h5 | h5
          · rw [h5] at hm'2; omega
          · have := hFmono m' k hm'1 h5; omega
  have hFM : F M = 3300 := by
    obtain ⟨hFM1, hFMe⟩ := hF M (le_refl M)
    refine le_antisymm ?_ hFM1
    obtain ⟨g1, g2, g3, -, -, -, -⟩ := hWz 3300 (le_refl _)
    obtain ⟨m, hm1, hm2⟩ := hallZ (Wz 3300) g1 g2 g3
    have hmM : M ≤ m := by
      by_contra hcon
      exact hMmin m (by omega) ⟨hm1, by rw [hm2]; exact hWbig 3300 (le_refl _)⟩
    have hle : ‖A * z M‖ ≤ ‖A * z m‖ := by
      rcases eq_or_lt_of_le hmM with h | h
      · rw [h]
      · exact (hmonoZ M m hM1 (by omega) h).le
    rw [hm2, hFMe] at hle
    by_contra hcon
    have h3300 : 3300 < F M := by omega
    exact absurd hle (not_le.mpr (hWmono 3300 (F M) (by omega) h3300))
  -- the count of the small zeros pins the enumeration origin
  have hzinj : Set.InjOn z {n : ℕ | 1 ≤ n} := by
    intro a ha b hb hab
    exact hmono.injOn ha hb (by show ‖z a‖ = ‖z b‖; rw [hab])
  have hMcount : M = 3300 := by
    have hset : {w : ℂ | f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
        ‖w‖ ^ 2 < 4 * 3300 + (c.im - 1) / 2 - 2} = ↑((Finset.Ico 1 M).image z) := by
      ext u
      simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_Ico]
      constructor
      · rintro ⟨hu, hui, hur, hub⟩
        obtain ⟨m, hm1, hm2⟩ := hall u hu hui hur
        refine ⟨m, ⟨hm1, ?_⟩, hm2⟩
        by_contra hcon
        have hMle : M ≤ m := by omega
        have hb := hzbig m hMle
        rw [hm2] at hb
        exact absurd ((hcut u).mp hub) (not_lt.mpr hb)
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        obtain ⟨q1, q2⟩ := hquad m hm1
        refine ⟨hzero m hm1, q1, q2, ?_⟩
        by_contra hcon
        exact hMmin m hm2 ⟨hm1, by
          have := (hcut (z m)).not.mp (by exact fun h => hcon h)
          exact not_lt.mp this⟩
    have hcard : ((Finset.Ico 1 M).image z).card = M - 1 := by
      rw [Finset.card_image_of_injOn, Nat.card_Ico]
      intro a ha b hb hab
      refine hzinj ?_ ?_ hab
      · simp only [Finset.coe_Ico, Set.mem_Ico] at ha; exact ha.1
      · simp only [Finset.coe_Ico, Set.mem_Ico] at hb; exact hb.1
    rw [hset, Set.ncard_coe_finset, hcard] at hcount
    omega
  -- hence the enumeration *is* the grid family from index `3300` on
  have hzW : ∀ m : ℕ, 3300 ≤ m → A * z m = Wz m := by
    intro m hm
    obtain ⟨-, he⟩ := hF m (by omega)
    have hfm : F m = m := by have h := hFform m (by omega); omega
    rw [he, hfm]
  intro m hm ζ hζ
  have hζW : ζ = Wz m := by rw [hζ]; exact hzW m hm
  obtain ⟨-, h2, h3, -, -, h6, h7⟩ := hWz m hm
  rw [hζW]
  exact ⟨h2, h3, h6, h7⟩

set_option maxHeartbeats 2000000 in
-- no-dlmf: the sharp DLMF 7.13.5 bounds at every sufficiently large index; proof infrastructure
/-- **The sharp expansion along the enumeration.**  Eventually in `m`, the `m`-th sub-diagonal
zero agrees with the DLMF 7.13.5 approximations at index `m` to within `3 λ_F⁻³`.

The threshold is the asymptotic-constant one `(μ+3)⁴ ≤ λ` of `fresnel713_zero_expansion`,
which `fresnel713_mu_eighth` reaches for `λ ≥ 8214²`; it is free here because the conclusion
is an `atTop` statement. -/
theorem fresnel713_eventual_bounds
    {c : ℂ} (hcre : c.re = 1) (hcim : c.im = 1 ∨ c.im = -1)
    {f : ℂ → ℂ}
    (hlink : ∀ w : ℂ, 4 * f w
      = 2 - (starRingEnd ℂ) c
            * cerfc (-Complex.I * ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
        - c * cerfc ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
    {Lam Mu LF : ℕ → ℝ}
    (hLamQ : ∀ m : ℕ, 1 ≤ m → 4 * (Lam m) ^ 2
        = 4 * Real.pi * (m:ℝ) - Real.pi / 2 + c.im * (Real.pi / 2))
    (hLampos : ∀ m : ℕ, 1 ≤ m → 0 < Lam m)
    (hLam100 : ∀ m : ℕ, 3300 ≤ m → 100 ≤ Lam m)
    (hMu : ∀ m : ℕ, 1 ≤ m → 2 * Mu m = Real.log (4 * Real.pi * (Lam m) ^ 2))
    (hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < LF m)
    (hLF : ∀ m : ℕ, 1 ≤ m → Lam m = (1/2) * Real.sqrt Real.pi * LF m)
    (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → f (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, f w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w)
    (hcount : {w : ℂ | f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
        ‖w‖ ^ 2 < 4 * 3300 + (c.im - 1) / 2 - 2}.ncard = 3299) :
    ∀ᶠ m : ℕ in atTop,
      |(z m).re - (LF m + (Mu m ^ 2 - 2 * Mu m) / (2 * Real.pi ^ 2 * (LF m) ^ 3))|
          ≤ 3 / (LF m) ^ 3 ∧
      |(z m).im - Mu m / (Real.pi * LF m)| ≤ 3 / (LF m) ^ 3 := by
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hcimge : (-1:ℝ) ≤ c.im := by rcases hcim with h | h <;> rw [h] <;> norm_num
  have henum := fresnel713_enumeration hcre hcim hlink hLamQ hLampos hLam100 hMu z hzero
    hquad hmono hall hcount
  filter_upwards [Filter.eventually_ge_atTop (max 3300 (2 * 8214 ^ 4))] with m hm
  have hm3300 : 3300 ≤ m := le_trans (le_max_left _ _) hm
  have hmbig : 2 * 8214 ^ 4 ≤ m := le_trans (le_max_right _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hmR : ((2 * 8214 ^ 4 : ℕ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast hmbig
  have hmR' : (2:ℝ) * 8214 ^ 4 ≤ (m:ℝ) := by push_cast at hmR; linarith
  have hlam100 := hLam100 m hm3300
  have hlam0 : (0:ℝ) < Lam m := hLampos m hm1
  have hLpos : (0:ℝ) < LF m := hLFpos m hm1
  have hLm := hLF m hm1
  -- the asymptotic-constant threshold
  have hLamsq : (3:ℝ) * (m:ℝ) - 1 ≤ (Lam m) ^ 2 := by
    have h := hLamQ m hm1; nlinarith
  have hLamK : ((8214:ℝ) ^ 2) ^ 2 ≤ (Lam m) ^ 2 := by nlinarith [hLamsq, hmR']
  have hLamK' : (8214:ℝ) ^ 2 ≤ Lam m := by nlinarith [hLamK, hlam0]
  have hsqrtLam : (8214:ℝ) ≤ Real.sqrt (Lam m) := by
    have h := Real.sqrt_le_sqrt hLamK'
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 8214)] at h
  have hm4 : (Mu m + 3) ^ 4 ≤ Lam m := by
    have h1 := fresnel713_mu_eighth hlam100 (hMu m hm1)
    have h2 : (8214:ℝ) * Real.sqrt (Lam m) ≤ Real.sqrt (Lam m) * Real.sqrt (Lam m) :=
      mul_le_mul_of_nonneg_right hsqrtLam (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hlam0.le] at h2
    linarith
  obtain ⟨hmu5, -, hmu3⟩ := fresnel713_mu_bounds hlam100 (hMu m hm1)
  -- the component data at `ζ`
  obtain ⟨hx, hxy, key1, key2⟩ :=
    henum m hm3300 ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z m) rfl
  set ζ : ℂ := (1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z m with hζdef
  have hzre : ζ.re = (1/2) * Real.sqrt Real.pi * ((z m).re - (z m).im) := by
    rw [hζdef]; exact fresnel_zeta_re (z m)
  have hzim : ζ.im = (1/2) * Real.sqrt Real.pi * ((z m).re + (z m).im) := by
    rw [hζdef]; exact fresnel_zeta_im (z m)
  have hd : ζ.re - ζ.im = -(Real.sqrt Real.pi * (z m).im) := by rw [hzre, hzim]; ring
  have hs : ζ.re + ζ.im = Real.sqrt Real.pi * (z m).re := by rw [hzre, hzim]; ring
  have hspos : (0:ℝ) < ζ.re + ζ.im := by linarith
  have hNsd : 2 * (ζ.re ^ 2 + ζ.im ^ 2) = (ζ.re + ζ.im) ^ 2 + (ζ.re - ζ.im) ^ 2 := by ring
  have hd2s : (ζ.re - ζ.im) ^ 2 ≤ (ζ.re + ζ.im) ^ 2 := by nlinarith
  obtain ⟨hdexp, hsexp⟩ :=
    fresnel713_zero_expansion hlam100 hmu5 hm4 (hMu m hm1) hspos hNsd hd2s
      (abs_arctan_sub_self_le ((ζ.re - ζ.im) / (ζ.re + ζ.im))) key1 key2
  -- convert to the Fresnel variable
  have hL0 : LF m ≠ 0 := ne_of_gt hLpos
  have hsp0 : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsppos
  have hlamne : Lam m ≠ 0 := ne_of_gt hlam0
  have hpisq8 : (8:ℝ) ≤ Real.pi ^ 2 := by nlinarith [hpi1]
  have hlam3 : Real.sqrt Real.pi * (Lam m) ^ 3 = Real.pi ^ 2 * (LF m) ^ 3 / 8 := by
    rw [hLm]
    linear_combination ((LF m) ^ 3 / 8 * (Real.sqrt Real.pi ^ 2 + Real.pi)) * hspsq
  have hbnd : (3:ℝ) / (Real.sqrt Real.pi * (Lam m) ^ 3) ≤ 3 / (LF m) ^ 3 := by
    rw [hlam3, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.pi ^ 2 - 8)
      (le_of_lt (pow_pos hLpos 3))]
  have hdiv : ∀ X : ℝ, Real.sqrt Real.pi * |X| ≤ 3 / (Lam m) ^ 3 → |X| ≤ 3 / (LF m) ^ 3 := by
    intro X hX
    refine le_trans ?_ hbnd
    rw [le_div_iff₀ (by positivity)]
    calc |X| * (Real.sqrt Real.pi * (Lam m) ^ 3)
        = (Real.sqrt Real.pi * |X|) * (Lam m) ^ 3 := by ring
      _ ≤ (3 / (Lam m) ^ 3) * (Lam m) ^ 3 :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ = 3 := by field_simp
  constructor
  · -- real part
    have hfac : Real.sqrt Real.pi * (16 * (Lam m) ^ 3) = 2 * Real.pi ^ 2 * (LF m) ^ 3 := by
      rw [hLm]
      linear_combination (2 * (LF m) ^ 3 * (Real.sqrt Real.pi ^ 2 + Real.pi)) * hspsq
    have hid : (ζ.re + ζ.im) - (2 * Lam m + (Mu m ^ 2 - 2 * Mu m) / (16 * (Lam m) ^ 3))
        = Real.sqrt Real.pi
          * ((z m).re - (LF m + (Mu m ^ 2 - 2 * Mu m) / (2 * Real.pi ^ 2 * (LF m) ^ 3))) := by
      rw [hs, ← hfac, hLm]
      field_simp
    rw [hid, abs_mul, abs_of_pos hsppos] at hsexp
    exact hdiv _ hsexp
  · -- imaginary part
    have hfac2 : Real.sqrt Real.pi * (2 * Lam m) = Real.pi * LF m := by
      rw [hLm]; linear_combination (LF m) * hspsq
    have hid : (ζ.re - ζ.im) + Mu m / (2 * Lam m)
        = -(Real.sqrt Real.pi) * ((z m).im - Mu m / (Real.pi * LF m)) := by
      rw [hd, ← hfac2, hLm]
      field_simp
      ring
    rw [hid, abs_mul, abs_neg, abs_of_pos hsppos] at hdexp
    exact hdiv _ hdexp

-- no-dlmf: `O(λ⁻³)` packaging of the eventual DLMF 7.13.5 bound; proof infrastructure
/-- An eventual `3 λ_F⁻³` bound is `O(λ_F⁻³)`. -/
theorem fresnel713_bigO {LF F : ℕ → ℝ} (hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < LF m)
    (hF : ∀ᶠ m in atTop, |F m| ≤ 3 / (LF m) ^ 3) :
    F =O[atTop] (fun m => (LF m) ^ (-3 : ℤ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [hF, Filter.eventually_ge_atTop 1] with m h1 h2
  have hp : 0 < LF m := hLFpos m h2
  have hp3 : (0:ℝ) < (LF m) ^ 3 := pow_pos hp 3
  have hz : ‖(LF m) ^ (-3 : ℤ)‖ = ((LF m) ^ 3)⁻¹ := by
    rw [show (-3:ℤ) = -(3:ℕ) by norm_num, zpow_neg, zpow_natCast, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp3)]
  rw [hz, Real.norm_eq_abs]
  calc |F m| ≤ 3 / (LF m) ^ 3 := h1
    _ = 3 * ((LF m) ^ 3)⁻¹ := by field_simp

-- no-dlmf: `o(λ⁻¹)` packaging of the eventual DLMF 7.13.5 bound; proof infrastructure
/-- An eventual `3 λ_F⁻³` bound with `λ_F² ≥ m` is `o(λ_F⁻¹)`. -/
theorem fresnel713_littleO {LF F : ℕ → ℝ} (hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < LF m)
    (hLFge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ (LF m) ^ 2)
    (hF : ∀ᶠ m in atTop, |F m| ≤ 3 / (LF m) ^ 3) :
    F =o[atTop] (fun m => (LF m) ^ (-1 : ℤ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hF, Filter.eventually_ge_atTop (max 1 ⌈(3 / c : ℝ)⌉₊)] with m h1 h2
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) h2
  have hp : 0 < LF m := hLFpos m hm1
  have hp3 : (0:ℝ) < (LF m) ^ 3 := pow_pos hp 3
  have hceil : ((3 / c : ℝ)) ≤ (m:ℝ) := by
    have h : (⌈(3 / c : ℝ)⌉₊ : ℝ) ≤ (m:ℝ) := by
      exact_mod_cast le_trans (le_max_right 1 ⌈(3 / c : ℝ)⌉₊) h2
    exact le_trans (Nat.le_ceil _) h
  have hLF2 : (3 / c : ℝ) ≤ (LF m) ^ 2 := le_trans hceil (hLFge m hm1)
  have hkey : (3:ℝ) ≤ c * (LF m) ^ 2 := by
    rw [div_le_iff₀ hc] at hLF2; linarith
  have hz : ‖(LF m) ^ (-1 : ℤ)‖ = ((LF m))⁻¹ := by
    rw [show (-1:ℤ) = -(1:ℕ) by norm_num, zpow_neg, zpow_natCast, pow_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp)]
  rw [hz, Real.norm_eq_abs]
  refine le_trans h1 ?_
  rw [div_le_iff₀ hp3]
  have hinv : c * (LF m)⁻¹ * (LF m) ^ 3 = c * (LF m) ^ 2 := by field_simp
  rw [hinv]; exact hkey

end FresnelZeroEquation

/-! ## Fresnel `C` zeros — approximation (DLMF 7.13.5 with 7.13.6 params) -/

-- no-dlmf: encodes the 7.13.5 approximant; display surfaced at `erf_7_13_5_full`
/-- DLMF 7.13.5 (with 7.13.6 parameters) — approximation of the real part of the
`n`-th complex zero of the Fresnel integral `C`:
`xₙ = λ + α·(α·π − 4)/(8π·λ³)`.
* dlmf: 7.13.5
* family: fresnel
* kind: zero-approximation -/
def fresnelCZeroReApprox (n : ℕ) : ℝ :=
  let lam := fresnelCZeroLambda n
  let a := fresnelCZeroAlpha n
  lam + a * (a * Real.pi - 4) / (8 * Real.pi * lam ^ 3)

-- no-dlmf: encodes the 7.13.5 approximant; display surfaced at `erf_7_13_5_full`
/-- DLMF 7.13.5 (with 7.13.6 parameters) — approximation of the imaginary part of
the `n`-th complex zero of the Fresnel integral `C`:
`yₙ = α/(2·λ)`.
* dlmf: 7.13.5
* family: fresnel
* kind: zero-approximation -/
def fresnelCZeroImApprox (n : ℕ) : ℝ :=
  let lam := fresnelCZeroLambda n
  let a := fresnelCZeroAlpha n
  a / (2 * lam)

-- no-dlmf: the square of the DLMF 7.13.6 parameter; proof infrastructure
/-- `λ_C(n)² = 4n − 1` for `n ≥ 1`. -/
theorem fresnelCZeroLambda_sq {n : ℕ} (hn : 1 ≤ n) :
    fresnelCZeroLambda n ^ 2 = 4 * (n:ℝ) - 1 := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  exact Real.sq_sqrt (by linarith)

-- no-dlmf: positivity of the DLMF 7.13.6 parameter; proof infrastructure
/-- `λ_C(n) > 0` for `n ≥ 1`. -/
theorem fresnelCZeroLambda_pos {n : ℕ} (hn : 1 ≤ n) : 0 < fresnelCZeroLambda n := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  exact Real.sqrt_pos.mpr (by linarith)

/-! ## The §7.13 Fresnel zero counts

The argument-principle computation behind `fresnelC713_low_zero_count` and
`fresnelS713_low_zero_count` below.  The dihedral symmetry group `D₄ = ⟨z ↦ i z, z ↦ conj z⟩`
of the zero sets of `C` and `S` turns the sub-diagonal octant count into a full-disc
multiplicity total on the circle `‖z‖² = 13197` (resp. `13198`), and folds the circle integral
of `f'/f` onto the *eighth* arc `θ ∈ [0, π/4]`; on that arc `C` and `S` are compared with the
one elementary model `M = 1 − νW`, `W(w) = e^{−iπw²/2}/(π w)`, whose logarithmic-derivative
integral has a branch-free closed form.  The model analysis is parametrized once by the pair
`(R, τ)` with `13197 ≤ R² ≤ 13198` and `πR²/2 − τ = 6599π`; the `C` and `S` cases are the two
endpoints `(13197, −π/2)` and `(13198, 0)` of that segment.  The only special-function inputs
are the already-proven remainder bound `cerfc_poincare_bound` (through
`erf713_cerfc_scaled_unit_bound_closed`) and the `erfc` forms `cfresnelC_erfc_form` /
`cfresnelS_erfc_form`; the circular-arc contour kit is `FLMF.Methods.arcPoint` /
`arcLogDerivIntegral` / `arc_logDeriv_integral`. -/

section Fresnel713ZeroCount

open Complex MeasureTheory Metric Set FLMF.Methods FLMF.Error

/-! ### Part 1 — derivatives and entireness

`C' = cos(πz²/2)` and `S' = sin(πz²/2)`, hence entireness of both.  `Ch7Derivatives.lean`
and `Ch7RelationsOther.lean` carry these facts only as `private` kit lemmas, so they are
reproved here from **public** inputs (`cfresnel_7_5_8`, `hasDerivAt_cerf`,
`hasDerivAt_cfresnelC_add_I_mul_cfresnelS`) — no new mathematics.  (A later relocation to
`FLMF/Chapter7/FresnelComplex.lean` would make them generally available.) -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The lower-sign branch of DLMF 7.5.8, differentiated: `(C - iS)' = e^{-½πiz²}`. -/
theorem fzc713_hasDerivAt_cfresnelC_sub_I_mul_cfresnelS (z : ℂ) :
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

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **`C` is entire with `C' = cos(πz²/2)`** (the FTC for the complex Fresnel
cosine integral). -/
theorem fzc713_hasDerivAt_cfresnelC (z : ℂ) :
    HasDerivAt cfresnelC (Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := fzc713_hasDerivAt_cfresnelC_sub_I_mul_cfresnelS z
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
  have heq : Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)
      = (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          + Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / 2 := by
    unfold Complex.cos
    have harg1 : (Real.pi : ℂ) * z ^ 2 / 2 * Complex.I
        = (1 / 2) * Real.pi * Complex.I * z ^ 2 := by ring
    have harg2 : -((Real.pi : ℂ) * z ^ 2 / 2) * Complex.I
        = -((1 / 2) * Real.pi * Complex.I * z ^ 2) := by ring
    rw [harg1, harg2]
  rw [heq]
  exact h3

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **`S` is entire with `S' = sin(πz²/2)`.** -/
theorem fzc713_hasDerivAt_cfresnelS (z : ℂ) :
    HasDerivAt cfresnelS (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have d1 := hasDerivAt_cfresnelC_add_I_mul_cfresnelS z
  have d2 := fzc713_hasDerivAt_cfresnelC_sub_I_mul_cfresnelS z
  have hsub := d1.sub d2
  have h2 : HasDerivAt (fun w : ℂ => 2 * Complex.I * cfresnelS w)
      (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
        - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) z := by
    convert hsub using 1
    funext w
    simp only [Pi.sub_apply]
    ring
  have h3 := h2.div_const (2 * Complex.I)
  have hSeq : (fun w : ℂ => 2 * Complex.I * cfresnelS w / (2 * Complex.I)) = cfresnelS := by
    funext w
    have hne : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
    field_simp
  rw [hSeq] at h3
  have heq : Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)
      = (Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)
          - Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))) / (2 * Complex.I) := by
    unfold Complex.sin
    have harg1 : -((Real.pi : ℂ) * z ^ 2 / 2) * Complex.I
        = -((1 / 2) * Real.pi * Complex.I * z ^ 2) := by ring
    have harg2 : (Real.pi : ℂ) * z ^ 2 / 2 * Complex.I
        = (1 / 2) * Real.pi * Complex.I * z ^ 2 := by ring
    rw [harg1, harg2]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have hne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    rw [eq_div_iff (mul_ne_zero two_ne_zero hne)]
    linear_combination
      (Complex.exp (-((1 / 2) * Real.pi * Complex.I * z ^ 2))
        - Complex.exp ((1 / 2) * Real.pi * Complex.I * z ^ 2)) * hI2
  rw [heq]
  exact h3

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C` is entire. -/
theorem fzc713_cfresnelC_differentiable : Differentiable ℂ cfresnelC :=
  fun z => (fzc713_hasDerivAt_cfresnelC z).differentiableAt

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S` is entire. -/
theorem fzc713_cfresnelS_differentiable : Differentiable ℂ cfresnelS :=
  fun z => (fzc713_hasDerivAt_cfresnelS z).differentiableAt

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_deriv_cfresnelC : deriv cfresnelC = fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2) :=
  funext fun z => (fzc713_hasDerivAt_cfresnelC z).deriv

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_deriv_cfresnelS : deriv cfresnelS = fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2) :=
  funext fun z => (fzc713_hasDerivAt_cfresnelS z).deriv

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelC_analyticAt (z : ℂ) : AnalyticAt ℂ cfresnelC z :=
  fzc713_cfresnelC_differentiable.analyticAt z

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelS_analyticAt (z : ℂ) : AnalyticAt ℂ cfresnelS z :=
  fzc713_cfresnelS_differentiable.analyticAt z

/-! ### Part 2 — real-axis positivity

The existing FLMF tail bounds give `C, S > 0` on **all** of `(0, ∞)`, in three
elementary regimes and with no arch-pairing machinery.

* `C`: the integrand `cos(πt²/2)` is `> 0` on `(0,1)`, so `C > 0` on `(0,1]`;
  `C` is antitone on `[1, 1.3]` (integrand `≤ 0` there); and for `x ≥ 1.3` the
  already-proven sharp bound `fresnelC_sub_leading_le`,
  `|C(x) - (½ + sin(πx²/2)/(πx))| ≤ 1/(πx)`, gives `C(x) ≥ ½ - 2/(πx) > 0`
  (`π·1.3 > 4`).
* `S`: the integrand `sin(πt²/2)` is `> 0` on `(0,√2)`, so `S > 0` on `(0,√2]`;
  `S` is antitone on `[√2, 2]`; and for `x ≥ 2` the coarse bound
  `fresnelS_dist_half_le`, `|S(x) - ½| ≤ 3/(πx)`, gives `S(x) ≥ ½ - 3/(2π) > 0`
  (`2π > 6`).  (`S` needs no sharp bound because its first sign change of the
  integrand, at `√2`, sits beyond the coarse bound's break-even `6/π ≈ 1.91`.) -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cosArg_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < cosArg t := by
  have hpi := Real.pi_pos
  have ht2 : t ^ 2 < 1 := by nlinarith
  unfold cosArg
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [sq_nonneg t]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_sinArg_pos {t : ℝ} (ht0 : 0 < t) (ht2 : t ^ 2 < 2) : 0 < sinArg t := by
  have hpi := Real.pi_pos
  unfold sinArg
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C(x) > 0` on `(0,1]`: the integrand is positive throughout. -/
theorem fzc713_fresnelC_pos_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 0 < fresnelC x := by
  rw [fresnelC]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_cosArg 0 x) ?_ hx
  intro t ht
  exact fzc713_cosArg_pos ht.1.le (lt_of_lt_of_le ht.2 hx1)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S(x) > 0` on `(0,√2]`: the integrand is positive throughout. -/
theorem fzc713_fresnelS_pos_of_le_sqrt_two {x : ℝ} (hx : 0 < x) (hx2 : x ≤ Real.sqrt 2) :
    0 < fresnelS x := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [fresnelS]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_sinArg 0 x) ?_ hx
  intro t ht
  refine fzc713_sinArg_pos ht.1 ?_
  have htlt : t < Real.sqrt 2 := lt_of_lt_of_le ht.2 hx2
  nlinarith [ht.1.le]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C(x) > 0` for `x ≥ 1.3`, from the sharp leading-order tail bound. -/
theorem fzc713_fresnelC_pos_of_ge {x : ℝ} (hx : (1.3 : ℝ) ≤ x) : 0 < fresnelC x := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hx0 : 0 < x := by linarith
  have hpx : 0 < Real.pi * x := by positivity
  have h := fresnelC_sub_leading_le x hx0
  have habs := abs_le.mp h
  set u : ℝ := 1 / (Real.pi * x) with hudef
  have hupos : 0 < u := by rw [hudef]; positivity
  have huinv : u * (Real.pi * x) = 1 := by rw [hudef]; field_simp
  have hpx4 : 4 < Real.pi * x := by nlinarith
  have hu4 : u < 1 / 4 := by nlinarith
  have heq : Real.sin (Real.pi * x ^ 2 / 2) / (Real.pi * x)
      = Real.sin (Real.pi * x ^ 2 / 2) * u := by rw [hudef]; ring
  have hsin := Real.neg_one_le_sin (Real.pi * x ^ 2 / 2)
  have hge : -u ≤ Real.sin (Real.pi * x ^ 2 / 2) * u := by nlinarith
  rw [heq] at habs
  linarith [habs.1]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S(x) > 0` for `x ≥ 2`, from the coarse tail bound `|S - ½| ≤ 3/(πx)`. -/
theorem fzc713_fresnelS_pos_of_ge_two {x : ℝ} (hx : (2 : ℝ) ≤ x) : 0 < fresnelS x := by
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hx0 : 0 < x := by linarith
  have hpx : 0 < Real.pi * x := by positivity
  have h := fresnelS_dist_half_le x hx0
  have habs := abs_le.mp h
  set v : ℝ := 3 / (Real.pi * x) with hvdef
  have hvpos : 0 < v := by rw [hvdef]; positivity
  have hvinv : v * (Real.pi * x) = 3 := by rw [hvdef]; field_simp
  have hpx6 : 6 < Real.pi * x := by nlinarith
  have hv : v < 1 / 2 := by nlinarith
  linarith [habs.1]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C` is antitone on `[1, 1.3]` (the integrand is `≤ 0` there). -/
theorem fzc713_fresnelC_antitoneOn : AntitoneOn fresnelC (Icc 1 1.3) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_fresnelC.continuousOn
    differentiable_fresnelC.differentiableOn ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [deriv_fresnelC]
  have ht1 : (1 : ℝ) < t := ht.1
  have ht2 : t < 1.3 := ht.2
  have hsq1 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
  have hsq3 : t ^ 2 ≤ 3 := by nlinarith
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · nlinarith
  · nlinarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S` is antitone on `[√2, 2]` (the integrand is `≤ 0` there). -/
theorem fzc713_fresnelS_antitoneOn : AntitoneOn fresnelS (Icc (Real.sqrt 2) 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_fresnelS.continuousOn
    differentiable_fresnelS.differentiableOn ?_
  intro t ht
  rw [interior_Icc] at ht
  rw [deriv_fresnelS]
  have ht2 : 2 < t ^ 2 := by nlinarith [ht.1, hs2pos]
  have ht4 : t ^ 2 < 4 := by nlinarith [ht.1, ht.2, hs2pos]
  have hsplit : Real.sin (Real.pi * t ^ 2 / 2)
      = -Real.sin (Real.pi * t ^ 2 / 2 - Real.pi) := by
    rw [Real.sin_sub_pi]; ring
  rw [hsplit, neg_nonpos]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · nlinarith
  · nlinarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C(x) > 0` for every real `x > 0` — in particular on all
of `(0, 116]`, the range the octant count needs. -/
theorem fzc713_fresnelC_pos {x : ℝ} (hx : 0 < x) : 0 < fresnelC x := by
  by_cases hc1 : x ≤ 1
  · exact fzc713_fresnelC_pos_of_le_one hx hc1
  have h1 : (1 : ℝ) < x := not_le.mp hc1
  by_cases hc2 : (1.3 : ℝ) ≤ x
  · exact fzc713_fresnelC_pos_of_ge hc2
  · have h2 : x < 1.3 := not_le.mp hc2
    have hmem : x ∈ Icc (1 : ℝ) 1.3 := ⟨h1.le, h2.le⟩
    have hmem' : (1.3 : ℝ) ∈ Icc (1 : ℝ) 1.3 := ⟨by norm_num, le_rfl⟩
    have := fzc713_fresnelC_antitoneOn hmem hmem' h2.le
    exact lt_of_lt_of_le (fzc713_fresnelC_pos_of_ge le_rfl) this

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S(x) > 0` for every real `x > 0`. -/
theorem fzc713_fresnelS_pos {x : ℝ} (hx : 0 < x) : 0 < fresnelS x := by
  by_cases hc1 : x ≤ Real.sqrt 2
  · exact fzc713_fresnelS_pos_of_le_sqrt_two hx hc1
  have h1 : Real.sqrt 2 < x := not_le.mp hc1
  by_cases hc2 : (2 : ℝ) ≤ x
  · exact fzc713_fresnelS_pos_of_ge_two hc2
  · have h2 : x < 2 := not_le.mp hc2
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2le : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2]
    have hmem : x ∈ Icc (Real.sqrt 2) 2 := ⟨h1.le, h2.le⟩
    have hmem' : (2 : ℝ) ∈ Icc (Real.sqrt 2) 2 := ⟨hs2le, le_rfl⟩
    have := fzc713_fresnelS_antitoneOn hmem hmem' h2.le
    exact lt_of_lt_of_le (fzc713_fresnelS_pos_of_ge_two le_rfl) this

/-! ### Part 3 — the two punctured axes carry no zero

The imaginary axis collapses into the real one: `(t·iy)² = -t²y²`
and `cos` is even / `sin` odd, so the imaginary-axis values of `C` and `S` are
`i·C(y)` and `-i·S(y)` with the **same real integrals**.  In FLMF this is already
DLMF 7.4.6 (`cfresnel_7_4_6`), so no new integral computation is needed. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C` has no zero on the punctured real axis (positivity + oddness). -/
theorem fzc713_cfresnelC_ofReal_ne_zero {x : ℝ} (hx : x ≠ 0) : cfresnelC (x : ℂ) ≠ 0 := by
  rw [cfresnelC_ofReal]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hpos' : 0 < fresnelC (-x) := fzc713_fresnelC_pos (by linarith)
    have hodd : fresnelC (-x) = -fresnelC x := by
      have := cfresnelC_neg (x : ℂ)
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, cfresnelC_ofReal,
        cfresnelC_ofReal] at this
      exact_mod_cast this
    intro h; rw [h] at hodd; simp at hodd; linarith [hodd ▸ hpos']
  · exact ne_of_gt (fzc713_fresnelC_pos hpos)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S` has no zero on the punctured real axis. -/
theorem fzc713_cfresnelS_ofReal_ne_zero {x : ℝ} (hx : x ≠ 0) : cfresnelS (x : ℂ) ≠ 0 := by
  rw [cfresnelS_ofReal]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hpos' : 0 < fresnelS (-x) := fzc713_fresnelS_pos (by linarith)
    have hodd : fresnelS (-x) = -fresnelS x := by
      have := cfresnelS_neg (x : ℂ)
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, cfresnelS_ofReal,
        cfresnelS_ofReal] at this
      exact_mod_cast this
    intro h; rw [h] at hodd; simp at hodd; linarith [hodd ▸ hpos']
  · exact ne_of_gt (fzc713_fresnelS_pos hpos)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `C(iy) = i·C(y)`, hence no zero on the punctured
imaginary axis. -/
theorem fzc713_cfresnelC_I_mul_ofReal_ne_zero {y : ℝ} (hy : y ≠ 0) :
    cfresnelC (Complex.I * (y : ℂ)) ≠ 0 := by
  rw [(cfresnel_7_4_6 (y : ℂ)).1]
  exact mul_ne_zero Complex.I_ne_zero (fzc713_cfresnelC_ofReal_ne_zero hy)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `S(iy) = -i·S(y)`, hence no zero on the punctured
imaginary axis. -/
theorem fzc713_cfresnelS_I_mul_ofReal_ne_zero {y : ℝ} (hy : y ≠ 0) :
    cfresnelS (Complex.I * (y : ℂ)) ≠ 0 := by
  rw [(cfresnel_7_4_6 (y : ℂ)).2]
  refine mul_ne_zero ?_ (fzc713_cfresnelS_ofReal_ne_zero hy)
  simp [Complex.I_ne_zero]

/-! ### The two axis edges in `re`/`im` form

These are the exact analogues of `cerf_imAxis_im_pos` in the `erf` count: the boundary-ray
facts a contour/argument-principle walk consumes ("this edge carries a constant
`arg`"). -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The real edge carries `arg C ≡ 0`**: `C(x)` is real and strictly positive
for real `x > 0`. -/
theorem fzc713_cfresnelC_ofReal_re_pos {x : ℝ} (hx : 0 < x) :
    (cfresnelC (x : ℂ)).im = 0 ∧ 0 < (cfresnelC (x : ℂ)).re := by
  rw [cfresnelC_ofReal]
  exact ⟨by simp, by simpa using fzc713_fresnelC_pos hx⟩

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The real edge carries `arg S ≡ 0`.** -/
theorem fzc713_cfresnelS_ofReal_re_pos {x : ℝ} (hx : 0 < x) :
    (cfresnelS (x : ℂ)).im = 0 ∧ 0 < (cfresnelS (x : ℂ)).re := by
  rw [cfresnelS_ofReal]
  exact ⟨by simp, by simpa using fzc713_fresnelS_pos hx⟩

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The imaginary edge carries `arg C ≡ π/2`**: `C(iy) = i·C(y)` is purely
imaginary with strictly positive imaginary part for `y > 0`. -/
theorem fzc713_cfresnelC_I_mul_ofReal_im_pos {y : ℝ} (hy : 0 < y) :
    (cfresnelC (Complex.I * (y : ℂ))).re = 0 ∧ 0 < (cfresnelC (Complex.I * (y : ℂ))).im := by
  rw [(cfresnel_7_4_6 (y : ℂ)).1, cfresnelC_ofReal]
  exact ⟨by simp, by simpa using fzc713_fresnelC_pos hy⟩

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The imaginary edge carries `arg S ≡ -π/2`**: `S(iy) = -i·S(y)` is purely
imaginary with strictly *negative* imaginary part for `y > 0`. -/
theorem fzc713_cfresnelS_I_mul_ofReal_im_neg {y : ℝ} (hy : 0 < y) :
    (cfresnelS (Complex.I * (y : ℂ))).re = 0 ∧ (cfresnelS (Complex.I * (y : ℂ))).im < 0 := by
  rw [(cfresnel_7_4_6 (y : ℂ)).2, cfresnelS_ofReal]
  exact ⟨by simp, by simpa using fzc713_fresnelS_pos hy⟩

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- A complex number with real square is real or purely imaginary
(`(w²).im = 2·(Re w)(Im w)`). -/
theorem fzc713_re_eq_zero_or_im_eq_zero_of_sq_im_zero {w : ℂ} (h : (w ^ 2).im = 0) :
    w.im = 0 ∨ w.re = 0 := by
  have hmul : (w ^ 2).im = 2 * w.re * w.im := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hmul] at h
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · norm_num at h''
    · exact Or.inr h''
  · exact Or.inl h'

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The two-axis nonvanishing, packaged for the simplicity argument: a nonzero `w`
with **real square** is not a zero of `C`. -/
theorem fzc713_cfresnelC_ne_zero_of_sq_im_zero {w : ℂ} (hw : w ≠ 0) (h : (w ^ 2).im = 0) :
    cfresnelC w ≠ 0 := by
  rcases fzc713_re_eq_zero_or_im_eq_zero_of_sq_im_zero h with him | hre
  · have hw' : w = ((w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hre0 : w.re ≠ 0 := by
      intro hc; apply hw; rw [hw', hc]; simp
    rw [hw']; exact fzc713_cfresnelC_ofReal_ne_zero hre0
  · have hw' : w = Complex.I * ((w.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    have him0 : w.im ≠ 0 := by
      intro hc; apply hw; rw [hw', hc]; simp
    rw [hw']; exact fzc713_cfresnelC_I_mul_ofReal_ne_zero him0

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The two-axis nonvanishing for `S`. -/
theorem fzc713_cfresnelS_ne_zero_of_sq_im_zero {w : ℂ} (hw : w ≠ 0) (h : (w ^ 2).im = 0) :
    cfresnelS w ≠ 0 := by
  rcases fzc713_re_eq_zero_or_im_eq_zero_of_sq_im_zero h with him | hre
  · have hw' : w = ((w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hre0 : w.re ≠ 0 := by
      intro hc; apply hw; rw [hw', hc]; simp
    rw [hw']; exact fzc713_cfresnelS_ofReal_ne_zero hre0
  · have hw' : w = Complex.I * ((w.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    have him0 : w.im ≠ 0 := by
      intro hc; apply hw; rw [hw', hc]; simp
    rw [hw']; exact fzc713_cfresnelS_I_mul_ofReal_ne_zero him0

/-! ### Part 4 — zero simplicity

`C'(w) = cos(πw²/2) = 0` forces `πw²/2 = (2k+1)π/2`, i.e. `w² = 2k+1`: a **real**
(odd integer) value.  `S'(w) = sin(πw²/2) = 0` forces `w² = 2k`, again real.  In
both cases Part 3 applies.  Note `w = 0` must be excluded for `S` — the origin
genuinely IS a multiple zero of `S` (order 3, Part 5). -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- If `cos(πw²/2) = 0` then `w²` is real. -/
theorem fzc713_sq_im_eq_zero_of_cos_eq_zero {w : ℂ}
    (h : Complex.cos ((Real.pi : ℂ) * w ^ 2 / 2) = 0) : (w ^ 2).im = 0 := by
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hw2 : w ^ 2 = (2 * (k : ℂ) + 1) := by
    field_simp at hk
    exact hk
  rw [hw2]
  simp

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- If `sin(πw²/2) = 0` then `w²` is real. -/
theorem fzc713_sq_im_eq_zero_of_sin_eq_zero {w : ℂ}
    (h : Complex.sin ((Real.pi : ℂ) * w ^ 2 / 2) = 0) : (w ^ 2).im = 0 := by
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hw2 : w ^ 2 = (2 * (k : ℂ)) := by
    field_simp at hk
    exact hk
  rw [hw2]
  simp

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Every nonzero zero of `C` is simple: `C'(w) ≠ 0`. -/
theorem fzc713_deriv_cfresnelC_ne_zero_of_zero {w : ℂ} (hw : w ≠ 0) (hC : cfresnelC w = 0) :
    deriv cfresnelC w ≠ 0 := by
  rw [fzc713_deriv_cfresnelC]
  intro hcos
  exact fzc713_cfresnelC_ne_zero_of_sq_im_zero hw (fzc713_sq_im_eq_zero_of_cos_eq_zero hcos) hC

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Every nonzero zero of `S` is simple: `S'(w) ≠ 0`.
(The origin is excluded and genuinely exceptional — see Part 5.) -/
theorem fzc713_deriv_cfresnelS_ne_zero_of_zero {w : ℂ} (hw : w ≠ 0) (hS : cfresnelS w = 0) :
    deriv cfresnelS w ≠ 0 := by
  rw [fzc713_deriv_cfresnelS]
  intro hsin
  exact fzc713_cfresnelS_ne_zero_of_sq_im_zero hw (fzc713_sq_im_eq_zero_of_sin_eq_zero hsin) hS

/-! ### Part 5 — vanishing orders

A general order criterion via iterated derivatives, then the two local models at
the origin (`C`: simple; `S`: **triple** — the `3 + 8N` vs `1 + 8N` bookkeeping),
and the simplicity of every nonzero zero in `analyticOrderNatAt` form, which is
what the argument-principle sum consumes. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Order `n` from the iterated derivatives: `f^{(i)}(w) = 0` for `i < n` and
`f^{(n)}(w) ≠ 0`. -/
theorem fzc713_analyticOrderNatAt_eq_of_iteratedDeriv {f : ℂ → ℂ} {w : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f w) (hlt : ∀ i < n, iteratedDeriv i f w = 0)
    (hn : iteratedDeriv n f w ≠ 0) : analyticOrderNatAt f w = n := by
  have hle : (n : ℕ∞) ≤ analyticOrderAt f w :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr hlt
  have hnot : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f w) := by
    intro hc
    exact hn ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp hc n (by omega))
  have hlt' : analyticOrderAt f w < ((n + 1 : ℕ) : ℕ∞) := not_le.mp hnot
  have hle' : analyticOrderAt f w ≤ (n : ℕ∞) := by
    have : ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
    rw [this] at hlt'
    exact Order.le_of_lt_add_one hlt'
  have heq : analyticOrderAt f w = (n : ℕ∞) := le_antisymm hle' hle
  simp [analyticOrderNatAt, heq]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Simple zero from a nonvanishing derivative. -/
theorem fzc713_analyticOrderNatAt_eq_one_of_deriv_ne_zero {f : ℂ → ℂ} {w : ℂ}
    (hf : AnalyticAt ℂ f w) (h0 : f w = 0) (h1 : deriv f w ≠ 0) :
    analyticOrderNatAt f w = 1 := by
  refine fzc713_analyticOrderNatAt_eq_of_iteratedDeriv hf ?_ ?_
  · intro i hi
    interval_cases i
    simpa using h0
  · simpa [iteratedDeriv_one] using h1

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **Simplicity, in the form the argument principle consumes.**  Every nonzero
zero of `C` has vanishing order `1`. -/
theorem fzc713_analyticOrderNatAt_cfresnelC_eq_one {w : ℂ} (hw : w ≠ 0) (hC : cfresnelC w = 0) :
    analyticOrderNatAt cfresnelC w = 1 :=
  fzc713_analyticOrderNatAt_eq_one_of_deriv_ne_zero (fzc713_cfresnelC_analyticAt w) hC
    (fzc713_deriv_cfresnelC_ne_zero_of_zero hw hC)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Every nonzero zero of `S` has vanishing order `1`. -/
theorem fzc713_analyticOrderNatAt_cfresnelS_eq_one {w : ℂ} (hw : w ≠ 0) (hS : cfresnelS w = 0) :
    analyticOrderNatAt cfresnelS w = 1 :=
  fzc713_analyticOrderNatAt_eq_one_of_deriv_ne_zero (fzc713_cfresnelS_analyticAt w) hS
    (fzc713_deriv_cfresnelS_ne_zero_of_zero hw hS)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The origin is a simple zero of `C`** (`C(0) = 0`, `C'(0) = cos 0 = 1`). -/
theorem fzc713_analyticOrderNatAt_cfresnelC_zero : analyticOrderNatAt cfresnelC 0 = 1 := by
  refine fzc713_analyticOrderNatAt_eq_one_of_deriv_ne_zero (fzc713_cfresnelC_analyticAt 0) cfresnelC_zero ?_
  rw [fzc713_deriv_cfresnelC]
  simp

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `d/dz sin(πz²/2) = π z cos(πz²/2)`. -/
theorem fzc713_hasDerivAt_sinPhase (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w ^ 2 / 2))
      ((Real.pi : ℂ) * z * Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have hphase : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w ^ 2 / 2) ((Real.pi : ℂ) * z) z := by
    have := ((hasDerivAt_pow 2 z).const_mul (Real.pi : ℂ)).div_const 2
    convert this using 1
    push_cast
    ring
  have := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z ^ 2 / 2)).comp z hphase
  convert this using 1
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `d/dz (π z cos(πz²/2)) = π cos(πz²/2) - π²z² sin(πz²/2)`. -/
theorem fzc713_hasDerivAt_cosPhaseMul (z : ℂ) :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w * Complex.cos ((Real.pi : ℂ) * w ^ 2 / 2))
      ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)
        - (Real.pi : ℂ) ^ 2 * z ^ 2 * Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) z := by
  have hphase : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w ^ 2 / 2) ((Real.pi : ℂ) * z) z := by
    have := ((hasDerivAt_pow 2 z).const_mul (Real.pi : ℂ)).div_const 2
    convert this using 1
    push_cast
    ring
  have hcos := (Complex.hasDerivAt_cos ((Real.pi : ℂ) * z ^ 2 / 2)).comp z hphase
  have hlin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have := hlin.mul hcos
  convert this using 1
  simp only [Function.comp_apply]
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_iteratedDeriv_one_cfresnelS :
    iteratedDeriv 1 cfresnelS = fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2) := by
  rw [iteratedDeriv_one]
  exact fzc713_deriv_cfresnelS

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_iteratedDeriv_two_cfresnelS :
    iteratedDeriv 2 cfresnelS
      = fun z : ℂ => (Real.pi : ℂ) * z * Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, fzc713_iteratedDeriv_one_cfresnelS]
  funext z
  exact (fzc713_hasDerivAt_sinPhase z).deriv

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The origin is a TRIPLE zero of `S`**: `S(0) = S'(0) = S''(0) = 0` and
`S'''(0) = π ≠ 0`.  This is the `3 + 8N` (rather than `1 + 8N`) input to the
disk-count bookkeeping, matching the numerics' measured origin-indentation
`Δarg = -3π/4` over the `π/4` wedge. -/
theorem fzc713_analyticOrderNatAt_cfresnelS_zero : analyticOrderNatAt cfresnelS 0 = 3 := by
  refine fzc713_analyticOrderNatAt_eq_of_iteratedDeriv (fzc713_cfresnelS_analyticAt 0) ?_ ?_
  · intro i hi
    interval_cases i
    · simp [cfresnelS_zero]
    · rw [fzc713_iteratedDeriv_one_cfresnelS]; simp
    · rw [fzc713_iteratedDeriv_two_cfresnelS]; simp
  · rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, fzc713_iteratedDeriv_two_cfresnelS]
    have h := (fzc713_hasDerivAt_cosPhaseMul 0).deriv
    rw [h]
    simp [Real.pi_ne_zero]

/-! ### Part 6 — the diagonal mirror rays (the last edge fact)

The four mirror lines of the dihedral action are the two axes (Part 3) and the two
diagonals `arg z = ±π/4, ±3π/4`.  The diagonal edge is the one fact the earlier parts
did not supply, and it is *elementary*, strictly easier
than the real axis: on `z = s(1+i)` (`s` real) one has `z² = 2i s²`, so the Fresnel
phase `π z²/2` becomes the purely imaginary `iπ s²`, and

* `cos (i x) = cosh x > 0` for every real `x`, so `C(s(1+i)) = s(1+i)·∫₀¹ cosh(π(ts)²)dt`
  is a nonzero multiple of a *strictly positive real* integral;
* `sin (i x) = i sinh x`, so `S(s(1+i)) = s(1+i)·i·∫₀¹ sinh(π(ts)²)dt`, and the real
  integral is again strictly positive for `s ≠ 0` (the integrand vanishes only at `t = 0`).

No oscillation, no envelope argument, no asymptotics. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `C` integrand on the diagonal ray is a real `cosh`.**
`C(s(1+i)) = s(1+i)·∫₀¹ cosh(π(ts)²) dt`. -/
theorem fzc713_cfresnelC_diag (s : ℝ) :
    cfresnelC ((s : ℂ) * (1 + Complex.I))
      = (s : ℂ) * (1 + Complex.I)
          * ((∫ t in (0:ℝ)..1, Real.cosh (Real.pi * (t * s) ^ 2) : ℝ) : ℂ) := by
  unfold cfresnelC
  congr 1
  rw [intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.cosh (Real.pi * (t * s) ^ 2) : ℝ) : ℂ)) ?_,
    intervalIntegral.integral_ofReal]
  intro t _
  dsimp only
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have harg : (Real.pi : ℂ) * ((t : ℂ) * ((s : ℂ) * (1 + Complex.I))) ^ 2 / 2
      = ((Real.pi * (t * s) ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination ((Real.pi : ℂ) * (t : ℂ) ^ 2 * (s : ℂ) ^ 2 / 2) * hI2
  rw [harg, Complex.cos_mul_I, ← Complex.ofReal_cosh]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `S` integrand on the diagonal ray is `i` times a real `sinh`.**
`S(s(1+i)) = s(1+i)·(∫₀¹ sinh(π(ts)²) dt)·i`. -/
theorem fzc713_cfresnelS_diag (s : ℝ) :
    cfresnelS ((s : ℂ) * (1 + Complex.I))
      = (s : ℂ) * (1 + Complex.I)
          * (((∫ t in (0:ℝ)..1, Real.sinh (Real.pi * (t * s) ^ 2) : ℝ) : ℂ) * Complex.I) := by
  unfold cfresnelS
  congr 1
  rw [intervalIntegral.integral_congr
      (g := fun t : ℝ => ((Real.sinh (Real.pi * (t * s) ^ 2) : ℝ) : ℂ) * Complex.I) ?_]
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  intro t _
  dsimp only
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have harg : (Real.pi : ℂ) * ((t : ℂ) * ((s : ℂ) * (1 + Complex.I))) ^ 2 / 2
      = ((Real.pi * (t * s) ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    linear_combination ((Real.pi : ℂ) * (t : ℂ) ^ 2 * (s : ℂ) ^ 2 / 2) * hI2
  rw [harg, Complex.sin_mul_I, ← Complex.ofReal_sinh]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `∫₀¹ cosh(π(ts)²) dt > 0` — the integrand is `≥ 1` everywhere. -/
theorem fzc713_diag_cosh_integral_pos (s : ℝ) :
    0 < ∫ t in (0:ℝ)..1, Real.cosh (Real.pi * (t * s) ^ 2) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by fun_prop) _ _) ?_ (by norm_num)
  intro t _
  exact Real.cosh_pos _

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `∫₀¹ sinh(π(ts)²) dt > 0` for `s ≠ 0` — the integrand is `> 0` off `t = 0`. -/
theorem fzc713_diag_sinh_integral_pos {s : ℝ} (hs : s ≠ 0) :
    0 < ∫ t in (0:ℝ)..1, Real.sinh (Real.pi * (t * s) ^ 2) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable (by fun_prop) _ _) ?_ (by norm_num)
  intro t ht
  refine Real.sinh_pos_iff.mpr ?_
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have : (0:ℝ) < (t * s) ^ 2 := by positivity
  positivity

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `C` diagonal edge.**  `C` has no zero on the punctured ray `arg z = π/4`. -/
theorem fzc713_cfresnelC_diag_ne_zero {s : ℝ} (hs : s ≠ 0) :
    cfresnelC ((s : ℂ) * (1 + Complex.I)) ≠ 0 := by
  rw [fzc713_cfresnelC_diag]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast hs
  · intro h
    have := congrArg Complex.re h
    simp at this
  · exact_mod_cast (fzc713_diag_cosh_integral_pos s).ne'

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `S` diagonal edge.**  `S` has no zero on the punctured ray `arg z = π/4`. -/
theorem fzc713_cfresnelS_diag_ne_zero {s : ℝ} (hs : s ≠ 0) :
    cfresnelS ((s : ℂ) * (1 + Complex.I)) ≠ 0 := by
  rw [fzc713_cfresnelS_diag]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ Complex.I_ne_zero)
  · exact_mod_cast hs
  · intro h
    have := congrArg Complex.re h
    simp at this
  · exact_mod_cast (fzc713_diag_sinh_integral_pos hs).ne'

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- A nonzero point of the diagonal `im = re` is `s(1+i)` with `s = re ≠ 0`. -/
theorem fzc713_eq_diag_mul {z : ℂ} (hz : z ≠ 0) (h : z.im = z.re) :
    z = ((z.re : ℝ) : ℂ) * (1 + Complex.I) ∧ z.re ≠ 0 := by
  have hzre : z.re ≠ 0 := by
    intro hc
    exact hz (Complex.ext hc (by rw [h, hc]; simp))
  refine ⟨Complex.ext ?_ ?_, hzre⟩ <;> simp [h]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- A nonzero point of the anti-diagonal `im = -re` is `conj (s(1+i))` with `s = re ≠ 0`. -/
theorem fzc713_eq_antidiag_mul {z : ℂ} (hz : z ≠ 0) (h : z.im = -z.re) :
    z = starRingEnd ℂ (((z.re : ℝ) : ℂ) * (1 + Complex.I)) ∧ z.re ≠ 0 := by
  have hzre : z.re ≠ 0 := by
    intro hc
    exact hz (Complex.ext hc (by rw [h, hc]; simp))
  refine ⟨Complex.ext ?_ ?_, hzre⟩ <;> simp [h]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **Mirror-line freeness for `C`.**  `C` has no zero on any of the eight
mirror rays: the two punctured axes and the four punctured diagonals. -/
theorem fzc713_cfresnelC_ne_zero_of_mirror {z : ℂ} (hz : z ≠ 0)
    (h : z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re) : cfresnelC z ≠ 0 := by
  rcases h with hre | him | hdiag | hanti
  · have hw : z = Complex.I * ((z.im : ℝ) : ℂ) := by apply Complex.ext <;> simp [hre]
    have him0 : z.im ≠ 0 := by
      intro hc; exact hz (Complex.ext hre hc)
    rw [hw]; exact fzc713_cfresnelC_I_mul_ofReal_ne_zero him0
  · have hw : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hre0 : z.re ≠ 0 := by
      intro hc; exact hz (Complex.ext hc him)
    rw [hw]; exact fzc713_cfresnelC_ofReal_ne_zero hre0
  · obtain ⟨hw, hre0⟩ := fzc713_eq_diag_mul hz hdiag
    rw [hw]; exact fzc713_cfresnelC_diag_ne_zero hre0
  · obtain ⟨hw, hre0⟩ := fzc713_eq_antidiag_mul hz hanti
    rw [hw, cfresnelC_conj]
    simpa using fzc713_cfresnelC_diag_ne_zero hre0

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **Mirror-line freeness for `S`.** -/
theorem fzc713_cfresnelS_ne_zero_of_mirror {z : ℂ} (hz : z ≠ 0)
    (h : z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re) : cfresnelS z ≠ 0 := by
  rcases h with hre | him | hdiag | hanti
  · have hw : z = Complex.I * ((z.im : ℝ) : ℂ) := by apply Complex.ext <;> simp [hre]
    have him0 : z.im ≠ 0 := by
      intro hc; exact hz (Complex.ext hre hc)
    rw [hw]; exact fzc713_cfresnelS_I_mul_ofReal_ne_zero him0
  · have hw : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hre0 : z.re ≠ 0 := by
      intro hc; exact hz (Complex.ext hc him)
    rw [hw]; exact fzc713_cfresnelS_ofReal_ne_zero hre0
  · obtain ⟨hw, hre0⟩ := fzc713_eq_diag_mul hz hdiag
    rw [hw]; exact fzc713_cfresnelS_diag_ne_zero hre0
  · obtain ⟨hw, hre0⟩ := fzc713_eq_antidiag_mul hz hanti
    rw [hw, cfresnelS_conj]
    simpa using fzc713_cfresnelS_diag_ne_zero hre0

/-! ### Part 7 — the dihedral orbit of an octant zero

The group is `D₄ = ⟨r, c⟩` with `r : z ↦ i z` (order 4) and `c : z ↦ conj z`; its eight
elements act on `ℂ` as `z ↦ i^k z` and `z ↦ i^k conj z`, `k < 4`.  Both `C` and `S`
satisfy `f (i z) = μ f z` with `μ = ±i` and `f (conj z) = conj (f z)`, so the zero set of
either is `D₄`-invariant.

Off the eight mirror rays (`re = 0`, `im = 0`, `im = ±re`) the action is free, and the
open sub-diagonal octant `0 < im w < re w` meets each orbit exactly once.  `fzc713_octant_orbit`
is the *effective* form of that statement: it names the octant representative and the
group element carrying it back.  It is stated for an abstract `f` with the three
zero-set symmetries, so `C` and `S` share it verbatim. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The octant representative of a non-mirror zero.**  For any `f` whose zero set is
closed under `z ↦ -z`, `z ↦ conj z` and `z ↦ i z`, every zero off the eight mirror rays
has a (unique, though uniqueness is not needed) partner in the open octant
`0 < im w < re w` of the same modulus, and is one of the eight `D₄`-images of it. -/
theorem fzc713_octant_orbit {f : ℂ → ℂ}
    (hneg : ∀ z, f z = 0 → f (-z) = 0)
    (hconj : ∀ z, f z = 0 → f (starRingEnd ℂ z) = 0)
    (hrot : ∀ z, f z = 0 → f (Complex.I * z) = 0)
    {z : ℂ} (hfz : f z = 0)
    (hre : z.re ≠ 0) (him : z.im ≠ 0) (hd : z.im ≠ z.re) (ha : z.im ≠ -z.re) :
    ∃ w : ℂ, f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ = ‖z‖ ∧
      (z = w ∨ z = starRingEnd ℂ w ∨ z = Complex.I * w ∨
        z = Complex.I * starRingEnd ℂ w ∨ z = -w ∨ z = -(starRingEnd ℂ w) ∨
        z = -(Complex.I * w) ∨ z = -(Complex.I * starRingEnd ℂ w)) := by
  have hInorm : ∀ v : ℂ, ‖Complex.I * v‖ = ‖v‖ := by
    intro v; rw [norm_mul, Complex.norm_I, one_mul]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  rcases lt_or_gt_of_ne hre with hreN | hreP
  · rcases lt_or_gt_of_ne him with himN | himP
    · -- `re < 0`, `im < 0`
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · -- `im < re < 0` : region 8, `w = -(i·conj z)`
        refine ⟨-(Complex.I * starRingEnd ℂ z), hneg _ (hrot _ (hconj _ hfz)), ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [norm_neg, hInorm, Complex.norm_conj]
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
          simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_conj,
            neg_neg, neg_mul]
          linear_combination z * hI2
      · -- `re < im < 0` : region 5, `w = -z`
        refine ⟨-z, hneg _ hfz, ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [norm_neg]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp)))))
    · -- `re < 0 < im`
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · -- `im < -re` : region 6, `w = -(conj z)`
        refine ⟨-(starRingEnd ℂ z), hneg _ (hconj _ hfz), ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [norm_neg, Complex.norm_conj]
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp))))))
      · -- `-re < im` : region 3, `w = -(i·z)`
        refine ⟨-(Complex.I * z), hneg _ (hrot _ hfz), ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [norm_neg, hInorm]
        · refine Or.inr (Or.inr (Or.inl ?_))
          linear_combination z * hI2
  · rcases lt_or_gt_of_ne him with himN | himP
    · -- `im < 0 < re`
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · -- `im < -re` : region 7, `w = i·z`
        refine ⟨Complex.I * z, hrot _ hfz, ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [hInorm]
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
          linear_combination z * hI2
      · -- `-re < im` : region 2, `w = conj z`
        refine ⟨starRingEnd ℂ z, hconj _ hfz, ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [Complex.norm_conj]
        · exact Or.inr (Or.inl (by simp))
    · -- `0 < re`, `0 < im`
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · -- `im < re` : region 1, `w = z`
        exact ⟨z, hfz, himP, hlt, rfl, Or.inl rfl⟩
      · -- `re < im` : region 4, `w = i·conj z`
        refine ⟨Complex.I * starRingEnd ℂ z, hrot _ (hconj _ hfz), ?_, ?_, ?_, ?_⟩
        · simp; linarith
        · simp; linarith
        · rw [hInorm, Complex.norm_conj]
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [Complex.ext_iff]))))

/-! ### The orbit bookkeeping: `#Z = 1 + 8·N`

The count is assembled in two stages, which halves the disjointness obligations:

* the open **first quadrant** off the diagonal is `Oct ⊎ D`, `D` the image of the octant
  under the diagonal mirror `w ↦ i·conj w` (an involution swapping `re` and `im`);
* the plane off the axes is the four quadrant images of that under `⟨z ↦ i z⟩`.

So `Z = {0} ⊎ Q ⊎ iQ ⊎ (−Q) ⊎ (−i)Q` with `Q = Oct ⊎ D`, giving
`#Z = 1 + 4·#Q = 1 + 8·#Oct`. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The dihedral orbit count.**  For an `f` with the three zero-set symmetries, no
mirror-ray zero and no zero on the counting circle, the zero set on the closed counting
disc has exactly `1 + 8·N` points, `N` the number of octant zeros below the cut.

(Point count, not multiplicity: the multiplicity weighting is put on top of this in
`fzc713_zeros_finset_exists_C/S`, where the origin contributes `1` for `C` and `3` for `S`.) -/
theorem fzc713_zero_set_ncard_eq {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hfin : (closedBall (0:ℂ) R ∩ f ⁻¹' {0}).Finite)
    (hf0 : f 0 = 0)
    (hneg : ∀ z, f z = 0 → f (-z) = 0)
    (hconj : ∀ z, f z = 0 → f (starRingEnd ℂ z) = 0)
    (hrot : ∀ z, f z = 0 → f (Complex.I * z) = 0)
    (hmirror : ∀ z : ℂ, z ≠ 0 → (z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re) →
      f z ≠ 0)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    (closedBall (0:ℂ) R ∩ f ⁻¹' {0}).ncard
      = 1 + 8 * {w : ℂ | f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < R ^ 2}.ncard := by
  classical
  set Oct : Set ℂ := {w : ℂ | f w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < R ^ 2} with hOctdef
  set D : Set ℂ := (fun w : ℂ => Complex.I * starRingEnd ℂ w) '' Oct with hDdef
  set Q : Set ℂ := Oct ∪ D with hQdef
  have hInorm : ∀ v : ℂ, ‖Complex.I * v‖ = ‖v‖ := by
    intro v; rw [norm_mul, Complex.norm_I, one_mul]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  -- membership in the closed disc from the modulus bound
  have hballOf : ∀ w : ℂ, ‖w‖ ^ 2 < R ^ 2 → ‖w‖ < R := by
    intro w hw; nlinarith [norm_nonneg w, hR]
  -- sign data for the four quadrant pieces
  have hsignOct : ∀ p ∈ Oct, 0 < p.re ∧ 0 < p.im := by
    rintro p ⟨-, h1, h2, -⟩; exact ⟨lt_trans h1 h2, h1⟩
  have hsignD : ∀ p ∈ D, 0 < p.re ∧ 0 < p.im ∧ p.re < p.im := by
    rintro p ⟨w, hw, rfl⟩
    obtain ⟨-, h1, h2, -⟩ := hw
    refine ⟨by simp; linarith, by simp; linarith, by simp; linarith⟩
  have hsignQ : ∀ p ∈ Q, 0 < p.re ∧ 0 < p.im := by
    rintro p (hp | hp)
    · exact hsignOct p hp
    · exact ⟨(hsignD p hp).1, (hsignD p hp).2.1⟩
  have hsignRot : ∀ p ∈ (fun w : ℂ => Complex.I * w) '' Q, p.re < 0 ∧ 0 < p.im := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by simp; linarith [(hsignQ w hw).2], by simp; linarith [(hsignQ w hw).1]⟩
  have hsignNeg : ∀ p ∈ (fun w : ℂ => -w) '' Q, p.re < 0 ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by simp; linarith [(hsignQ w hw).1], by simp; linarith [(hsignQ w hw).2]⟩
  have hsignNegRot : ∀ p ∈ (fun w : ℂ => -(Complex.I * w)) '' Q, 0 < p.re ∧ p.im < 0 := by
    rintro p ⟨w, hw, rfl⟩
    exact ⟨by simp; linarith [(hsignQ w hw).2], by simp; linarith [(hsignQ w hw).1]⟩
  -- the five-piece decomposition of the zero set
  have hZeq : (closedBall (0:ℂ) R ∩ f ⁻¹' {0} : Set ℂ)
      = {0} ∪ Q ∪ (fun w : ℂ => Complex.I * w) '' Q ∪ (fun w : ℂ => -w) '' Q
          ∪ (fun w : ℂ => -(Complex.I * w)) '' Q := by
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨hzc, hzz⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hzz
      have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hzc
      have hzlt : ‖z‖ < R := by
        rcases lt_or_eq_of_le hzR with h | h
        · exact h
        · exact absurd hzz (hcircle z h)
      have hzsq : ‖z‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg z, hR]
      by_cases hz0 : z = 0
      · left; left; left; left; exact hz0
      have hmir : ¬ (z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re) :=
        fun h => hmirror z hz0 h hzz
      simp only [not_or] at hmir
      obtain ⟨hre, him, hd, ha⟩ := hmir
      obtain ⟨w, hfw, hw1, hw2, hwn, hcase⟩ := fzc713_octant_orbit hneg hconj hrot hzz hre him hd ha
      have hwOct : w ∈ Oct := ⟨hfw, hw1, hw2, by rw [hwn]; exact hzsq⟩
      have hvD : Complex.I * starRingEnd ℂ w ∈ D := ⟨w, hwOct, rfl⟩
      rcases hcase with h | h | h | h | h | h | h | h
      · left; left; left; right; rw [h]; exact Or.inl hwOct
      · -- `z = conj w = -(i·(i·conj w))`
        right
        refine ⟨Complex.I * starRingEnd ℂ w, Or.inr hvD, ?_⟩
        show -(Complex.I * (Complex.I * starRingEnd ℂ w)) = z
        rw [h]; linear_combination (-(starRingEnd ℂ w)) * hI2
      · left; left; right; exact ⟨w, Or.inl hwOct, h.symm⟩
      · left; left; left; right; rw [h]; exact Or.inr hvD
      · left; right; exact ⟨w, Or.inl hwOct, h.symm⟩
      · -- `z = -(conj w) = i·(i·conj w)`
        left; left; right
        refine ⟨Complex.I * starRingEnd ℂ w, Or.inr hvD, ?_⟩
        show Complex.I * (Complex.I * starRingEnd ℂ w) = z
        rw [h]; linear_combination (starRingEnd ℂ w) * hI2
      · right; exact ⟨w, Or.inl hwOct, h.symm⟩
      · left; right; exact ⟨Complex.I * starRingEnd ℂ w, Or.inr hvD, h.symm⟩
    · have hQsub : ∀ p ∈ Q, f p = 0 ∧ ‖p‖ < R := by
        rintro p (⟨hf, -, -, hn⟩ | ⟨w, ⟨hf, -, -, hn⟩, rfl⟩)
        · exact ⟨hf, hballOf p hn⟩
        · exact ⟨hrot _ (hconj _ hf), by rw [hInorm, Complex.norm_conj]; exact hballOf w hn⟩
      rintro z ((((rfl | hzQ) | ⟨w, hwQ, rfl⟩) | ⟨w, hwQ, rfl⟩) | ⟨w, hwQ, rfl⟩)
      · exact ⟨mem_closedBall_zero_iff.mpr (by simp [hR.le]), by simpa using hf0⟩
      · exact ⟨mem_closedBall_zero_iff.mpr (hQsub z hzQ).2.le, (hQsub z hzQ).1⟩
      · exact ⟨mem_closedBall_zero_iff.mpr (by rw [hInorm]; exact (hQsub w hwQ).2.le),
          hrot _ (hQsub w hwQ).1⟩
      · exact ⟨mem_closedBall_zero_iff.mpr (by rw [norm_neg]; exact (hQsub w hwQ).2.le),
          hneg _ (hQsub w hwQ).1⟩
      · exact ⟨mem_closedBall_zero_iff.mpr (by rw [norm_neg, hInorm]; exact (hQsub w hwQ).2.le),
          hneg _ (hrot _ (hQsub w hwQ).1)⟩
  -- finiteness of all the pieces
  have hOctsub : Oct ⊆ closedBall (0:ℂ) R ∩ f ⁻¹' {0} := by
    rintro w ⟨hf, -, -, hn⟩
    exact ⟨mem_closedBall_zero_iff.mpr (hballOf w hn).le, hf⟩
  have hOctfin : Oct.Finite := hfin.subset hOctsub
  have hDfin : D.Finite := hOctfin.image _
  have hQfin : Q.Finite := hOctfin.union hDfin
  have hMirrorInj : Function.Injective (fun w : ℂ => Complex.I * starRingEnd ℂ w) := by
    intro a b hab
    have := mul_left_cancel₀ Complex.I_ne_zero hab
    simpa using congrArg (starRingEnd ℂ) this
  have hRotInj : Function.Injective (fun w : ℂ => Complex.I * w) :=
    fun a b hab => mul_left_cancel₀ Complex.I_ne_zero hab
  have hNegInj : Function.Injective (fun w : ℂ => -w) := neg_injective
  have hNegRotInj : Function.Injective (fun w : ℂ => -(Complex.I * w)) :=
    neg_injective.comp hRotInj
  -- `#Q = 2·#Oct`
  have hdOctD : Disjoint Oct D := by
    rw [Set.disjoint_left]
    rintro p hp hpD
    obtain ⟨-, -, h2, -⟩ := hp
    linarith [(hsignD p hpD).2.2]
  have hQcard : Q.ncard = 2 * Oct.ncard := by
    rw [hQdef, Set.ncard_union_eq hdOctD hOctfin hDfin, hDdef,
      Set.ncard_image_of_injective Oct hMirrorInj]
    ring
  -- the four-piece quadrant assembly
  have hRotFin : ((fun w : ℂ => Complex.I * w) '' Q).Finite := hQfin.image _
  have hNegFin : ((fun w : ℂ => -w) '' Q).Finite := hQfin.image _
  have hNegRotFin : ((fun w : ℂ => -(Complex.I * w)) '' Q).Finite := hQfin.image _
  have hX1fin : ({0} ∪ Q : Set ℂ).Finite := (Set.finite_singleton 0).union hQfin
  have hd1 : Disjoint ({0} : Set ℂ) Q := by
    rw [Set.disjoint_left]; rintro p hp hpQ
    rw [Set.mem_singleton_iff] at hp
    have := (hsignQ p hpQ).1; rw [hp] at this; simp at this
  have hX1card : ({0} ∪ Q : Set ℂ).ncard = 1 + Q.ncard := by
    rw [Set.ncard_union_eq hd1 (Set.finite_singleton 0) hQfin, Set.ncard_singleton]
  have hdX1 : Disjoint ({0} ∪ Q : Set ℂ) ((fun w : ℂ => Complex.I * w) '' Q) := by
    rw [Set.disjoint_left]; rintro p hp hpR
    rcases hp with hp0 | hpQ
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignRot p hpR).2; rw [hp0] at this; simp at this
    · linarith [(hsignQ p hpQ).1, (hsignRot p hpR).1]
  have hX2fin : (({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q : Set ℂ).Finite :=
    hX1fin.union hRotFin
  have hX2card : (({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q : Set ℂ).ncard
      = 1 + 2 * Q.ncard := by
    rw [Set.ncard_union_eq hdX1 hX1fin hRotFin, hX1card,
      Set.ncard_image_of_injective Q hRotInj]
    ring
  have hdX2 : Disjoint ((({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q) : Set ℂ)
      ((fun w : ℂ => -w) '' Q) := by
    rw [Set.disjoint_left]; rintro p hp hpN
    rcases hp with (hp0 | hpQ) | hpR
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignNeg p hpN).1; rw [hp0] at this; simp at this
    · linarith [(hsignQ p hpQ).1, (hsignNeg p hpN).1]
    · linarith [(hsignRot p hpR).2, (hsignNeg p hpN).2]
  have hX3fin : ((({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q) ∪ (fun w : ℂ => -w) '' Q
      : Set ℂ).Finite := hX2fin.union hNegFin
  have hX3card : ((({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q) ∪ (fun w : ℂ => -w) '' Q
      : Set ℂ).ncard = 1 + 3 * Q.ncard := by
    rw [Set.ncard_union_eq hdX2 hX2fin hNegFin, hX2card,
      Set.ncard_image_of_injective Q hNegInj]
    ring
  have hdX3 : Disjoint (((({0} ∪ Q) ∪ (fun w : ℂ => Complex.I * w) '' Q)
      ∪ (fun w : ℂ => -w) '' Q) : Set ℂ) ((fun w : ℂ => -(Complex.I * w)) '' Q) := by
    rw [Set.disjoint_left]; rintro p hp hpNR
    rcases hp with ((hp0 | hpQ) | hpR) | hpN
    · rw [Set.mem_singleton_iff] at hp0
      have := (hsignNegRot p hpNR).1; rw [hp0] at this; simp at this
    · linarith [(hsignQ p hpQ).2, (hsignNegRot p hpNR).2]
    · linarith [(hsignRot p hpR).1, (hsignNegRot p hpNR).1]
    · linarith [(hsignNeg p hpN).1, (hsignNegRot p hpNR).1]
  rw [hZeq, Set.ncard_union_eq hdX3 hX3fin hNegRotFin, hX3card,
    Set.ncard_image_of_injective Q hNegRotInj, hQcard]
  ring

/-! ### Part 8 — no zero on the counting circle (the exact thresholds)

The two thresholds `13197` (`C`) and `13198` (`S`) are chosen *exactly half-way between
consecutive index values*, and that is what makes the circle zero-free — no asymptotic
slack is needed beyond the localization the production machinery already provides.

Concretely, for an octant zero `w` the erf-variable `ζ = ½√π(1+i)w` has
`‖ζ‖² = (π/2)‖w‖²`, and `fresnel_zero_index_exists` + `fresnel713_match_of_key` give an
integer index `k` with

    | ‖ζ‖² − 2λ² | ≤ 1/10 ,    2λ² = 2πk − π/4 + (Im c)·π/4 .

For `C` (`c = 1−i`) that is `2λ² = 2πk − π/2` and `‖ζ‖² = 6598.5·π`; for `S` (`c = 1+i`)
it is `2λ² = 2πk` and `‖ζ‖² = 6599·π`.  **Both** cases collapse to the same statement

    | π·(6599 − 2k) | ≤ 1/10 ,

and `6599 − 2k` is an *odd* integer, hence of absolute value `≥ 1`, so the left side is
`≥ π > 3`.  Contradiction with room to spare (a factor of 30).  The two thresholds are
therefore not merely "far from the grid": they are exactly at the half-integer index. -/

open FLMF.Error in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The octant half of the circle exclusion for `C`.**  No sub-diagonal zero of `C` has
`‖w‖² = 13197`. -/
theorem fzc713_cfresnelC_octant_ne_zero_on_circle {w : ℂ} (h1 : 0 < w.im) (h2 : w.im < w.re)
    (hn : ‖w‖ ^ 2 = 13197) : cfresnelC w ≠ 0 := by
  intro hz
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w with hζdef
  have hζre : ζ.re = (1 / 2) * Real.sqrt Real.pi * (w.re - w.im) := fresnel_zeta_re w
  have hζim : ζ.im = (1 / 2) * Real.sqrt Real.pi * (w.re + w.im) := fresnel_zeta_im w
  have hζn : ‖ζ‖ ^ 2 = (Real.pi / 2) * 13197 := by
    rw [hζdef, fresnel_zeta_norm_sq, hn]
  have hNid : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN2 : ζ.re ^ 2 + ζ.im ^ 2 = Real.pi / 2 * 13197 := by rw [hNid, hζn]
  have hx : 0 < ζ.re := by rw [hζre]; nlinarith
  have hy : 0 < ζ.im := by rw [hζim]; nlinarith
  have hxy : ζ.re < ζ.im := by rw [hζre, hζim]; nlinarith
  have hbig : (20004 : ℝ) ≤ ζ.re ^ 2 + ζ.im ^ 2 := by rw [hN2]; nlinarith
  obtain ⟨k, lam, hk, hlam, hQ, key1, key2⟩ :=
    fresnel_zero_index_exists (c := 1 - Complex.I) (by simp) (Or.inr (by simp)) hx hxy hbig
      (cfresnelC_zero_erfc hz)
  have hcim : (1 - Complex.I).im = -1 := by simp
  rw [hcim] at hQ
  have hmu : 2 * ((1 / 2) * Real.log (4 * Real.pi * lam ^ 2))
      = Real.log (4 * Real.pi * lam ^ 2) := by ring
  have hs : 0 < ζ.re + ζ.im := by linarith
  have hNsd : 2 * (ζ.re ^ 2 + ζ.im ^ 2) = (ζ.re + ζ.im) ^ 2 + (ζ.re - ζ.im) ^ 2 := by ring
  have hd2s : (ζ.re - ζ.im) ^ 2 ≤ (ζ.re + ζ.im) ^ 2 := by nlinarith
  obtain ⟨-, -, hN⟩ := fresnel713_match_of_key hlam hmu hs hNsd hd2s
    (abs_arctan_sub_self_le ((ζ.re - ζ.im) / (ζ.re + ζ.im))) key1 key2
  -- the half-integer collision
  have heq : (ζ.re ^ 2 + ζ.im ^ 2) - 2 * lam ^ 2 = Real.pi * (6599 - 2 * (k : ℝ)) := by
    linear_combination hN2 - (1 / 2) * hQ
  rw [heq, abs_mul, abs_of_pos Real.pi_pos] at hN
  have hodd : (1 : ℝ) ≤ |6599 - 2 * (k : ℝ)| := by
    have h0 : (6599 - 2 * k : ℤ) ≠ 0 := by omega
    have h1 : (1 : ℤ) ≤ |6599 - 2 * k| := Int.one_le_abs h0
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|6599 - 2 * k| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |6599 - 2 * (k : ℝ)| := by push_cast; ring
  nlinarith [hN, hodd, hpi]

open FLMF.Error in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The octant half of the circle exclusion for `S`.**  No sub-diagonal zero of `S` has
`‖w‖² = 13198`. -/
theorem fzc713_cfresnelS_octant_ne_zero_on_circle {w : ℂ} (h1 : 0 < w.im) (h2 : w.im < w.re)
    (hn : ‖w‖ ^ 2 = 13198) : cfresnelS w ≠ 0 := by
  intro hz
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w with hζdef
  have hζre : ζ.re = (1 / 2) * Real.sqrt Real.pi * (w.re - w.im) := fresnel_zeta_re w
  have hζim : ζ.im = (1 / 2) * Real.sqrt Real.pi * (w.re + w.im) := fresnel_zeta_im w
  have hζn : ‖ζ‖ ^ 2 = (Real.pi / 2) * 13198 := by
    rw [hζdef, fresnel_zeta_norm_sq, hn]
  have hNid : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hN2 : ζ.re ^ 2 + ζ.im ^ 2 = Real.pi / 2 * 13198 := by rw [hNid, hζn]
  have hx : 0 < ζ.re := by rw [hζre]; nlinarith
  have hy : 0 < ζ.im := by rw [hζim]; nlinarith
  have hxy : ζ.re < ζ.im := by rw [hζre, hζim]; nlinarith
  have hbig : (20004 : ℝ) ≤ ζ.re ^ 2 + ζ.im ^ 2 := by rw [hN2]; nlinarith
  obtain ⟨k, lam, hk, hlam, hQ, key1, key2⟩ :=
    fresnel_zero_index_exists (c := 1 + Complex.I) (by simp) (Or.inl (by simp)) hx hxy hbig
      (cfresnelS_zero_erfc hz)
  have hcim : (1 + Complex.I).im = 1 := by simp
  rw [hcim] at hQ
  have hmu : 2 * ((1 / 2) * Real.log (4 * Real.pi * lam ^ 2))
      = Real.log (4 * Real.pi * lam ^ 2) := by ring
  have hs : 0 < ζ.re + ζ.im := by linarith
  have hNsd : 2 * (ζ.re ^ 2 + ζ.im ^ 2) = (ζ.re + ζ.im) ^ 2 + (ζ.re - ζ.im) ^ 2 := by ring
  have hd2s : (ζ.re - ζ.im) ^ 2 ≤ (ζ.re + ζ.im) ^ 2 := by nlinarith
  obtain ⟨-, -, hN⟩ := fresnel713_match_of_key hlam hmu hs hNsd hd2s
    (abs_arctan_sub_self_le ((ζ.re - ζ.im) / (ζ.re + ζ.im))) key1 key2
  have heq : (ζ.re ^ 2 + ζ.im ^ 2) - 2 * lam ^ 2 = Real.pi * (6599 - 2 * (k : ℝ)) := by
    linear_combination hN2 - (1 / 2) * hQ
  rw [heq, abs_mul, abs_of_pos Real.pi_pos] at hN
  have hodd : (1 : ℝ) ≤ |6599 - 2 * (k : ℝ)| := by
    have h0 : (6599 - 2 * k : ℤ) ≠ 0 := by omega
    have h1 : (1 : ℤ) ≤ |6599 - 2 * k| := Int.one_le_abs h0
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|6599 - 2 * k| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |6599 - 2 * (k : ℝ)| := by push_cast; ring
  nlinarith [hN, hodd, hpi]

/-! ### The three zero-set symmetries, packaged -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelC_zero_neg {z : ℂ} (h : cfresnelC z = 0) : cfresnelC (-z) = 0 := by
  rw [cfresnelC_neg, h, neg_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelC_zero_conj {z : ℂ} (h : cfresnelC z = 0) :
    cfresnelC (starRingEnd ℂ z) = 0 := by
  rw [cfresnelC_conj, h, map_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelC_zero_rot {z : ℂ} (h : cfresnelC z = 0) :
    cfresnelC (Complex.I * z) = 0 := by
  rw [(cfresnel_7_4_6 z).1, h, mul_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelS_zero_neg {z : ℂ} (h : cfresnelS z = 0) : cfresnelS (-z) = 0 := by
  rw [cfresnelS_neg, h, neg_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelS_zero_conj {z : ℂ} (h : cfresnelS z = 0) :
    cfresnelS (starRingEnd ℂ z) = 0 := by
  rw [cfresnelS_conj, h, map_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelS_zero_rot {z : ℂ} (h : cfresnelS z = 0) :
    cfresnelS (Complex.I * z) = 0 := by
  rw [(cfresnel_7_4_6 z).2, h, mul_zero]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The full circle exclusion for `C`.**  `C` has no zero anywhere on `‖z‖² = 13197`:
mirror-ray points by Part 6, all others by the octant case through the dihedral orbit. -/
theorem fzc713_cfresnelC_ne_zero_on_circle {z : ℂ} (hz : ‖z‖ ^ 2 = 13197) : cfresnelC z ≠ 0 := by
  intro hzero
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  by_cases hmir : z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re
  · exact fzc713_cfresnelC_ne_zero_of_mirror hz0 hmir hzero
  simp only [not_or] at hmir
  obtain ⟨hre, him, hd, ha⟩ := hmir
  obtain ⟨w, hfw, hw1, hw2, hwn, -⟩ :=
    fzc713_octant_orbit (fun v h => fzc713_cfresnelC_zero_neg h) (fun v h => fzc713_cfresnelC_zero_conj h)
      (fun v h => fzc713_cfresnelC_zero_rot h) hzero hre him hd ha
  exact fzc713_cfresnelC_octant_ne_zero_on_circle hw1 hw2 (by rw [hwn]; exact hz) hfw

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The full circle exclusion for `S`** at `‖z‖² = 13198`. -/
theorem fzc713_cfresnelS_ne_zero_on_circle {z : ℂ} (hz : ‖z‖ ^ 2 = 13198) : cfresnelS z ≠ 0 := by
  intro hzero
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  by_cases hmir : z.re = 0 ∨ z.im = 0 ∨ z.im = z.re ∨ z.im = -z.re
  · exact fzc713_cfresnelS_ne_zero_of_mirror hz0 hmir hzero
  simp only [not_or] at hmir
  obtain ⟨hre, him, hd, ha⟩ := hmir
  obtain ⟨w, hfw, hw1, hw2, hwn, -⟩ :=
    fzc713_octant_orbit (fun v h => fzc713_cfresnelS_zero_neg h) (fun v h => fzc713_cfresnelS_zero_conj h)
      (fun v h => fzc713_cfresnelS_zero_rot h) hzero hre him hd ha
  exact fzc713_cfresnelS_octant_ne_zero_on_circle hw1 hw2 (by rw [hwn]; exact hz) hfw

/-! ### Part 9 — the multiplicity-weighted disc totals

`1 + 8N` for `C` (simple zero at the origin) and `3 + 8N` for `S` (**triple** zero at the
origin, `fzc713_analyticOrderNatAt_cfresnelS_zero`).  This is the only place where the two
families' bookkeeping differs, and it is exactly the difference the arc identity of
Part 10 has to absorb. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The `C` counting radius, `R² = 13197`. -/
def fzc713RadC : ℝ := Real.sqrt 13197

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The `S` counting radius, `R² = 13198`. -/
def fzc713RadS : ℝ := Real.sqrt 13198

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_RadC_pos : 0 < fzc713RadC := Real.sqrt_pos.mpr (by norm_num)
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_RadS_pos : 0 < fzc713RadS := Real.sqrt_pos.mpr (by norm_num)
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_RadC_sq : fzc713RadC ^ 2 = 13197 := Real.sq_sqrt (by norm_num)
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_RadS_sq : fzc713RadS ^ 2 = 13198 := Real.sq_sqrt (by norm_num)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelC_one_ne_zero : cfresnelC (1 : ℂ) ≠ 0 := by
  simpa using fzc713_cfresnelC_ofReal_ne_zero (x := (1 : ℝ)) (by norm_num)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cfresnelS_one_ne_zero : cfresnelS (1 : ℂ) ≠ 0 := by
  simpa using fzc713_cfresnelS_ofReal_ne_zero (x := (1 : ℝ)) (by norm_num)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Finiteness of the zero set on the closed counting disc, for either family. -/
theorem fzc713_fresnel_zeros_finite {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) :
    (closedBall (0 : ℂ) R ∩ f ⁻¹' {0}).Finite := by
  have hUconn : IsConnected (ball (0 : ℂ) (R + 1)) :=
    ⟨Metric.nonempty_ball.mpr (by linarith), (convex_ball (0 : ℂ) (R + 1)).isPreconnected⟩
  have hx1 : (1 : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball_zero_iff, norm_one]; linarith
  exact FLMF.Methods.finite_zeros_on_compact (fun z _ => hf.analyticAt z) hUconn hx1 hf1
    (isCompact_closedBall 0 R) (Metric.closedBall_subset_ball (by linarith))

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `C` disc total.**  `∑ orders = 1 + 8N` on `closedBall 0 fzc713RadC`. -/
theorem fzc713_zeros_finset_exists_C :
    ∃ P : Finset ℂ,
      (∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) fzc713RadC ∧ cfresnelC z = 0) ∧
      (∀ p ∈ P, p ∈ ball (0 : ℂ) fzc713RadC) ∧
      (∑ p ∈ P, (analyticOrderNatAt cfresnelC p : ℂ))
        = 1 + 8 * (({w : ℂ | cfresnelC w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
            ‖w‖ ^ 2 < 13197}.ncard : ℕ) : ℂ) := by
  classical
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadC → cfresnelC z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelC_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadC_sq
  have hZfin : (closedBall (0 : ℂ) fzc713RadC ∩ cfresnelC ⁻¹' {0}).Finite :=
    fzc713_fresnel_zeros_finite fzc713_RadC_pos fzc713_cfresnelC_differentiable fzc713_cfresnelC_one_ne_zero
  set P : Finset ℂ := hZfin.toFinset with hPdef
  have hPmem : ∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) fzc713RadC ∧ cfresnelC z = 0 := by
    intro z
    rw [hPdef, Set.Finite.mem_toFinset]
    simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hPball : ∀ p ∈ P, p ∈ ball (0 : ℂ) fzc713RadC := by
    intro p hp
    obtain ⟨hpc, hpz⟩ := (hPmem p).mp hp
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hpc) with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · exact absurd hpz (hcirc p heq)
  refine ⟨P, hPmem, hPball, ?_⟩
  -- every zero of `C` in the disc is simple (including the origin)
  have horder1 : ∀ p ∈ P, analyticOrderNatAt cfresnelC p = 1 := by
    intro p hp
    have hzero : cfresnelC p = 0 := ((hPmem p).mp hp).2
    by_cases hp0 : p = 0
    · rw [hp0]; exact fzc713_analyticOrderNatAt_cfresnelC_zero
    · exact fzc713_analyticOrderNatAt_cfresnelC_eq_one hp0 hzero
  have hsum : (∑ p ∈ P, (analyticOrderNatAt cfresnelC p : ℂ)) = (P.card : ℂ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [horder1 p hp])]
    simp
  have hcard := fzc713_zero_set_ncard_eq (f := cfresnelC) (R := fzc713RadC) fzc713_RadC_pos hZfin cfresnelC_zero
    (fun v h => fzc713_cfresnelC_zero_neg h) (fun v h => fzc713_cfresnelC_zero_conj h)
    (fun v h => fzc713_cfresnelC_zero_rot h)
    (fun z hz0 h => fzc713_cfresnelC_ne_zero_of_mirror hz0 h) hcirc
  rw [fzc713_RadC_sq] at hcard
  have hPcard : P.card = (closedBall (0 : ℂ) fzc713RadC ∩ cfresnelC ⁻¹' {0}).ncard := by
    rw [hPdef]; exact (Set.ncard_eq_toFinset_card _ hZfin).symm
  rw [hsum, hPcard, hcard]
  push_cast
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `S` disc total.**  `∑ orders = 3 + 8N` — the origin is a *triple* zero. -/
theorem fzc713_zeros_finset_exists_S :
    ∃ P : Finset ℂ,
      (∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) fzc713RadS ∧ cfresnelS z = 0) ∧
      (∀ p ∈ P, p ∈ ball (0 : ℂ) fzc713RadS) ∧
      (∑ p ∈ P, (analyticOrderNatAt cfresnelS p : ℂ))
        = 3 + 8 * (({w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
            ‖w‖ ^ 2 < 13198}.ncard : ℕ) : ℂ) := by
  classical
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadS → cfresnelS z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelS_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadS_sq
  have hZfin : (closedBall (0 : ℂ) fzc713RadS ∩ cfresnelS ⁻¹' {0}).Finite :=
    fzc713_fresnel_zeros_finite fzc713_RadS_pos fzc713_cfresnelS_differentiable fzc713_cfresnelS_one_ne_zero
  set P : Finset ℂ := hZfin.toFinset with hPdef
  have hPmem : ∀ z, z ∈ P ↔ z ∈ closedBall (0 : ℂ) fzc713RadS ∧ cfresnelS z = 0 := by
    intro z
    rw [hPdef, Set.Finite.mem_toFinset]
    simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hPball : ∀ p ∈ P, p ∈ ball (0 : ℂ) fzc713RadS := by
    intro p hp
    obtain ⟨hpc, hpz⟩ := (hPmem p).mp hp
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hpc) with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · exact absurd hpz (hcirc p heq)
  refine ⟨P, hPmem, hPball, ?_⟩
  have h0P : (0 : ℂ) ∈ P :=
    (hPmem 0).mpr ⟨mem_closedBall_self fzc713_RadS_pos.le, cfresnelS_zero⟩
  have horder1 : ∀ p ∈ P.erase 0, analyticOrderNatAt cfresnelS p = 1 := by
    intro p hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    exact fzc713_analyticOrderNatAt_cfresnelS_eq_one hp0 ((hPmem p).mp (Finset.mem_of_mem_erase hp)).2
  have hsum : (∑ p ∈ P, (analyticOrderNatAt cfresnelS p : ℂ))
      = ((P.erase 0).card : ℂ) + 3 := by
    rw [← Finset.add_sum_erase P (fun p => (analyticOrderNatAt cfresnelS p : ℂ)) h0P,
      fzc713_analyticOrderNatAt_cfresnelS_zero,
      Finset.sum_congr rfl (fun p hp => by rw [horder1 p hp])]
    simp
    ring
  have hcard := fzc713_zero_set_ncard_eq (f := cfresnelS) (R := fzc713RadS) fzc713_RadS_pos hZfin cfresnelS_zero
    (fun v h => fzc713_cfresnelS_zero_neg h) (fun v h => fzc713_cfresnelS_zero_conj h)
    (fun v h => fzc713_cfresnelS_zero_rot h)
    (fun z hz0 h => fzc713_cfresnelS_ne_zero_of_mirror hz0 h) hcirc
  rw [fzc713_RadS_sq] at hcard
  have hPcard : P.card = (closedBall (0 : ℂ) fzc713RadS ∩ cfresnelS ⁻¹' {0}).ncard := by
    rw [hPdef]; exact (Set.ncard_eq_toFinset_card _ hZfin).symm
  have herase : (P.erase 0).card + 1 = P.card := Finset.card_erase_add_one h0P
  have hEcard : (P.erase 0).card
      = 8 * {w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13198}.ncard := by
    omega
  rw [hsum, hEcard]
  push_cast
  ring

/-! ### Part 10 — the circle reduces to the **eighth** arc

The algebra, done once and carefully (this is the point where the Fresnel case differs
from `erf`'s quarter-arc `4i·Im J`).

Write `p(θ) = R e^{iθ}`, `g = f'/f`, `h(θ) = g(p θ)·(i·p θ)`, so that
`∮_{|z|=R} f'/f = ∫₀^{2π} h`.

* **Rotation.**  `f (i z) = μ f z` with `μ` a nonzero constant (`μ = i` for `C`,
  `μ = -i` for `S`).  Differentiating, `f'(i z)·i = μ f'(z)`, so
  `g(i z) = f'(iz)/f(iz) = (μ f'(z)/i)/(μ f(z)) = g(z)/i` — **`μ` cancels**, which is why
  `C` and `S` obey the *same* reduction.  Hence
  `h(θ + π/2) = g(i p)·(i·(i p)) = (g(p)/i)·i²·p = g(p)·(i p) = h(θ)`:
  `h` is `π/2`-periodic, so `∫₀^{2π} h = 4∫₀^{π/2} h`.
* **Conjugation.**  `f (z̄) = conj (f z)` gives `g(z̄) = conj (g z)` and
  `h(−θ) = −conj (h θ)`.  Combined with `π/2`-periodicity,
  `h(π/2 − x) = h(−x) = −conj (h x)`, so `∫_{π/4}^{π/2} h = −conj J` with
  `J := ∫₀^{π/4} h`, and `∫₀^{π/2} h = J − conj J = 2i·Im J`.

**Therefore `∮ = 8i·Im J` over the eighth arc `θ ∈ [0, π/4]`** — *not* `4i·Im` of a
quarter arc.  (Both foldings are used: the order-4 rotation folds the circle to a
quarter, and the conjugation folds that quarter to an eighth.  The erf case had only the
order-2 rotation `z ↦ −z`, hence `4i·Im` of a quarter.)

Combined with the argument principle `∮ = 2πi·∑orders` this gives
`Im J = π/4 + 2πN` for `C` (`∑ = 1 + 8N`) and `Im J = 3π/4 + 2πN` for `S`
(`∑ = 3 + 8N`) — the `3π/4` matching the numerics' origin-indentation `Δarg = -3π/4`
over the `π/4` wedge. -/


-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The counting arc misses the origin (`Methods.arcPoint_ne_zero`, in the `0 < R` form the
Fresnel arc analysis uses). -/
theorem fzc713_arcPoint_ne_zero {R : ℝ} (hR : 0 < R) (θ : ℝ) : arcPoint R θ ≠ 0 :=
  arcPoint_ne_zero hR.ne' θ

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- Every point of the counting arc has norm `R` (`Methods.norm_arcPoint`, in the `0 < R`
form the Fresnel arc analysis uses). -/
theorem fzc713_arcPoint_norm {R : ℝ} (hR : 0 < R) (θ : ℝ) : ‖arcPoint R θ‖ = R :=
  norm_arcPoint hR.le θ

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_exp_pi_div_two_mul_I : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]
  have h1 : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [show (((Real.pi / 2 : ℝ)) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.cos_pi_div_two
  have h2 : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [show (((Real.pi / 2 : ℝ)) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
    exact Complex.sin_pi_div_two
  rw [h1, h2]; ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The quarter-turn on the arc: `p(θ + π/2) = i·p(θ)`. -/
theorem fzc713_arcPoint_add_pi_div_two (R θ : ℝ) :
    arcPoint R (θ + Real.pi / 2) = Complex.I * arcPoint R θ := by
  simp only [arcPoint]
  rw [show (((θ + Real.pi / 2 : ℝ)) : ℂ) = ((θ : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
    add_mul, Complex.exp_add, fzc713_exp_pi_div_two_mul_I]
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The rotation identity for the derivative.**  `f (i z) = μ f z` differentiates to
`f'(i z)·i = μ·f'(z)`. -/
theorem fzc713_deriv_rot {f : ℂ → ℂ} {μ : ℂ} (hdiff : Differentiable ℂ f)
    (hrot : ∀ z, f (Complex.I * z) = μ * f z) (z : ℂ) :
    deriv f (Complex.I * z) * Complex.I = μ * deriv f z := by
  have hlin : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I z := by
    simpa using (hasDerivAt_id z).const_mul Complex.I
  have hcomp : HasDerivAt (fun w : ℂ => f (Complex.I * w))
      (deriv f (Complex.I * z) * Complex.I) z :=
    (hdiff (Complex.I * z)).hasDerivAt.comp z hlin
  have hfun : (fun w : ℂ => f (Complex.I * w)) = fun w : ℂ => μ * f w := funext hrot
  rw [hfun] at hcomp
  have hother : HasDerivAt (fun w : ℂ => μ * f w) (μ * deriv f z) z :=
    (hdiff z).hasDerivAt.const_mul μ
  exact hcomp.unique hother

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The conjugation identity for the derivative of `C`**, read off the explicit
derivative `C' = cos(πz²/2)` (real Taylor coefficients). -/
theorem fzc713_deriv_cfresnelC_conj (z : ℂ) :
    deriv cfresnelC (starRingEnd ℂ z) = starRingEnd ℂ (deriv cfresnelC z) := by
  rw [fzc713_deriv_cfresnelC]
  dsimp only
  rw [← Complex.cos_conj]
  congr 1
  rw [map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  norm_num [map_ofNat]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The conjugation identity for the derivative of `S`** (`S' = sin(πz²/2)`). -/
theorem fzc713_deriv_cfresnelS_conj (z : ℂ) :
    deriv cfresnelS (starRingEnd ℂ z) = starRingEnd ℂ (deriv cfresnelS z) := by
  rw [fzc713_deriv_cfresnelS]
  dsimp only
  rw [← Complex.sin_conj]
  congr 1
  rw [map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  norm_num [map_ofNat]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The circle-to-eighth-arc reduction.**  For any entire `f` with
`f(iz) = μ f(z)` (`μ ≠ 0` constant) and `f(z̄) = conj (f z)`, nonvanishing on `‖z‖ = R`,

    ∮_{|z|=R} f'/f  =  8i · Im ∫₀^{π/4} (f'/f)(R e^{iθ})·(i R e^{iθ}) dθ .

The rotation folds the circle onto a quarter (`h` is `π/2`-periodic) and the conjugation
folds the quarter onto an eighth (`h(π/2 − x) = −conj (h x)`). -/
theorem fzc713_circle_eq_eight_I_arc_im {f : ℂ → ℂ} {R : ℝ} {μ : ℂ} (hR : 0 < R)
    (hdiff : Differentiable ℂ f) (hdcont : Continuous (deriv f)) (hμ : μ ≠ 0)
    (hrot : ∀ z, f (Complex.I * z) = μ * f z)
    (hconj : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hdconj : ∀ z, deriv f (starRingEnd ℂ z) = starRingEnd ℂ (deriv f z))
    (hne : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) :
    (∮ z in C((0:ℂ), R), deriv f z / f z)
      = 8 * Complex.I * (((arcLogDerivIntegral f R 0 (Real.pi / 4)).im : ℝ) : ℂ) := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  set h : ℝ → ℂ :=
    fun θ => deriv f (arcPoint R θ) / f (arcPoint R θ) * (Complex.I * arcPoint R θ) with hhdef
  have hnearc : ∀ θ : ℝ, f (arcPoint R θ) ≠ 0 := fun θ => hne _ (fzc713_arcPoint_norm hR θ)
  have hcont_h : Continuous h := by
    have h1 : Continuous fun θ : ℝ => deriv f (arcPoint R θ) := hdcont.comp (continuous_arcPoint R)
    have h2 : Continuous fun θ : ℝ => f (arcPoint R θ) :=
      hdiff.continuous.comp (continuous_arcPoint R)
    exact (h1.div h2 hnearc).mul (continuous_const.mul (continuous_arcPoint R))
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hcont_h.intervalIntegrable a b
  -- the circle integral is the full-period arc integral
  have hstep1 : (∮ z in C((0:ℂ), R), deriv f z / f z)
      = ∫ θ in (0:ℝ)..(2 * Real.pi), h θ := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [deriv_circleMap, ← arcPoint_eq_circleMap, smul_eq_mul, hhdef]
    ring
  -- `π/2`-periodicity (the rotation)
  have hper : Function.Periodic h (Real.pi / 2) := by
    intro θ
    have hnz := hnearc θ
    have hd := fzc713_deriv_rot hdiff hrot (arcPoint R θ)
    have hd' : deriv f (Complex.I * arcPoint R θ)
        = -Complex.I * (μ * deriv f (arcPoint R θ)) := by
      linear_combination (-Complex.I) * hd
        + (deriv f (Complex.I * arcPoint R θ)) * hI2
    simp only [hhdef]
    rw [fzc713_arcPoint_add_pi_div_two, hrot, hd']
    field_simp
    linear_combination (-(deriv f (arcPoint R θ) * arcPoint R θ)) * hI2
  -- the conjugation reflection
  have hconjrel : ∀ θ : ℝ, h (-θ) = - starRingEnd ℂ (h θ) := by
    intro θ
    simp only [hhdef]
    rw [arcPoint_neg, hdconj, hconj, map_mul, map_mul, map_div₀,
      show starRingEnd ℂ Complex.I = -Complex.I from Complex.conj_I]
    ring
  -- fold the circle onto the quarter arc
  have hquarter : ∀ t : ℝ, (∫ θ in t..(t + Real.pi / 2), h θ)
      = ∫ θ in (0:ℝ)..(Real.pi / 2), h θ := by
    intro t
    have := hper.intervalIntegral_add_eq t 0
    simpa using this
  have e2 : (∫ θ in (Real.pi / 2)..Real.pi, h θ) = ∫ θ in (0:ℝ)..(Real.pi / 2), h θ := by
    have := hquarter (Real.pi / 2)
    rwa [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] at this
  have e3 : (∫ θ in Real.pi..(3 * Real.pi / 2), h θ)
      = ∫ θ in (0:ℝ)..(Real.pi / 2), h θ := by
    have := hquarter Real.pi
    rwa [show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring] at this
  have e4 : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), h θ)
      = ∫ θ in (0:ℝ)..(Real.pi / 2), h θ := by
    have := hquarter (3 * Real.pi / 2)
    rwa [show 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi by ring] at this
  have hsum4 : (∫ θ in (0:ℝ)..(2 * Real.pi), h θ)
      = 4 * ∫ θ in (0:ℝ)..(Real.pi / 2), h θ := by
    have s1 := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := Real.pi / 2) (c := Real.pi) (f := h) (hint _ _) (hint _ _)
    have s2 := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := Real.pi) (c := 3 * Real.pi / 2) (f := h) (hint _ _) (hint _ _)
    have s3 := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := 3 * Real.pi / 2) (c := 2 * Real.pi) (f := h) (hint _ _) (hint _ _)
    rw [← s3, ← s2, ← s1, e2, e3, e4]
    ring
  -- fold the quarter arc onto the eighth arc
  set J : ℂ := ∫ θ in (0:ℝ)..(Real.pi / 4), h θ with hJdef
  have hstep : ∀ x : ℝ, h (Real.pi / 2 - x) = - starRingEnd ℂ (h x) := by
    intro x
    rw [show Real.pi / 2 - x = -x + Real.pi / 2 by ring, hper (-x)]
    exact hconjrel x
  have hhalf : (∫ θ in (Real.pi / 4)..(Real.pi / 2), h θ) = - starRingEnd ℂ J := by
    have hsub := intervalIntegral.integral_comp_sub_left h (a := (0:ℝ)) (b := Real.pi / 4)
      (d := Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
      show Real.pi / 2 - (0:ℝ) = Real.pi / 2 by ring] at hsub
    rw [← hsub, intervalIntegral.integral_congr (fun x _ => hstep x),
      intervalIntegral.integral_neg, intervalIntegral_conj (hint 0 (Real.pi / 4)), hJdef]
  have hhalfsum : (∫ θ in (0:ℝ)..(Real.pi / 2), h θ) = J - starRingEnd ℂ J := by
    have s := intervalIntegral.integral_add_adjacent_intervals
      (a := (0:ℝ)) (b := Real.pi / 4) (c := Real.pi / 2) (f := h) (hint _ _) (hint _ _)
    rw [← s, hhalf, hJdef]; ring
  have harc : arcLogDerivIntegral f R 0 (Real.pi / 4) = J := rfl
  rw [hstep1, hsum4, hhalfsum, harc]
  have hJIm : J - starRingEnd ℂ J = 2 * Complex.I * ((J.im : ℝ) : ℂ) := by
    rw [Complex.sub_conj]; push_cast; ring
  rw [hJIm]; ring

/-! ### The two Fresnel instances of the reduction -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_circle_eq_eight_I_arc_im_C {R : ℝ} (hR : 0 < R)
    (hne : ∀ z : ℂ, ‖z‖ = R → cfresnelC z ≠ 0) :
    (∮ z in C((0:ℂ), R), deriv cfresnelC z / cfresnelC z)
      = 8 * Complex.I * (((arcLogDerivIntegral cfresnelC R 0 (Real.pi / 4)).im : ℝ) : ℂ) := by
  have hdcont : Continuous (deriv cfresnelC) := by
    rw [fzc713_deriv_cfresnelC]; fun_prop
  exact fzc713_circle_eq_eight_I_arc_im hR fzc713_cfresnelC_differentiable hdcont Complex.I_ne_zero
    (fun z => (cfresnel_7_4_6 z).1) cfresnelC_conj fzc713_deriv_cfresnelC_conj hne

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_circle_eq_eight_I_arc_im_S {R : ℝ} (hR : 0 < R)
    (hne : ∀ z : ℂ, ‖z‖ = R → cfresnelS z ≠ 0) :
    (∮ z in C((0:ℂ), R), deriv cfresnelS z / cfresnelS z)
      = 8 * Complex.I * (((arcLogDerivIntegral cfresnelS R 0 (Real.pi / 4)).im : ℝ) : ℂ) := by
  have hdcont : Continuous (deriv cfresnelS) := by
    rw [fzc713_deriv_cfresnelS]; fun_prop
  refine fzc713_circle_eq_eight_I_arc_im hR fzc713_cfresnelS_differentiable hdcont ?_
    (fun z => (cfresnel_7_4_6 z).2) cfresnelS_conj fzc713_deriv_cfresnelS_conj hne
  simp [Complex.I_ne_zero]

/-! ### Part 10¾ — the parametrized model arc

The Fresnel analogue of the `erf` model computation (`erf713_modelArc_im`), carried out once for both
families.  On the eighth arc `w = R e^{iθ}`, `θ ∈ [0, π/4]`, the erf-variable
`ζ = ½√π(1+i)w` has `|ζ|² = πR²/2 =: ρ²` and `arg ζ = θ + π/4 ∈ [π/4, π/2]`, and the
`erfc`-form `4f = 2 − c̄·erfc(−iζ) − c·erfc ζ` (`c = 1∓i`) becomes

    4 f(w) = 2·(1 − ν W(w)) − 2 ν W(w) E − c̄·erfc(−iζ),
    W(w) = e^{−iπw²/2}/(π w),   ν = c/(1+i) = e^{iτ},   τ = π(R²−13198)/2,

with `‖E‖ ≤ 4/ρ²`.  Everything below is stated for the pair `(R, τ)` constrained by
`13197 ≤ R² ≤ 13198` and `ρ² − τ = 6599π` — the two families are the endpoints
`(13197, −π/2)` and `(13198, 0)` of that segment.

Closed forms derived here:

* `fzc713BigLam R τ θ = −iρ² e^{2iθ} − log(πR) + iτ − iθ`, the **branch-free** logarithm of
  `ν W` along the arc (`Im = −(ρ² cos 2θ + θ − τ) = −fzc713PsiOf`);
* `fzc713ThetaStar R = ½ arcsin (log(πR)/ρ²)`, the unique `θ ∈ (0, π/4)` with `‖νW‖ = 1`;
* `fzc713BigPsi R τ = ρ² cos 2θ* + θ* − τ ∈ (2π·3299, 2π·3300)` and `fzc713BigPhi = 2π·3300 − fzc713BigPsi`;
* `Im ∫₀^{π/4} M'/M = 2π·3300 − 5π/4 + τ − arg M(0) + arg k(π/4)`  (`fzc713_modelArc_im`).

Note that — unlike the `erf` case — the two endpoint corrections do **not** cancel
exactly (the `θ = π/4` ratio carries the `O(‖E‖) ≈ 2·10⁻⁴` remainder, not an
`arctan(e^{−R²})`), so the integer is pinned by the argument principle instead: all four
residual arguments lie in `(−π/2, π/2)`, hence the total is within `2π` of the model
value, and `Im J ∈ π/4 + 2πℕ` (resp. `3π/4 + 2πℕ`) forces the exact value. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_arcPoint_im (R θ : ℝ) : (arcPoint R θ).im = R * Real.sin θ := by
  rw [arcPoint, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-! ### The model -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The elementary Fresnel model factor `W(w) = e^{-iπw²/2}/(π w)`. -/
def fzc713ModelW (w : ℂ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * w ^ 2) / ((Real.pi : ℂ) * w)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The model for the Fresnel integrals on the arc: `M = 1 - ν W`. -/
def fzc713ModelM (ν : ℂ) (w : ℂ) : ℂ := 1 - ν * fzc713ModelW w

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The reciprocal factor. -/
def fzc713KFun (ν : ℂ) (w : ℂ) : ℂ := 1 - (ν * fzc713ModelW w)⁻¹

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_modelW_ne_zero {w : ℂ} (hw : w ≠ 0) : fzc713ModelW w ≠ 0 := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fzc713ModelW]
  exact div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hπ hw)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_hasDerivAt_modelW {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt fzc713ModelW (fzc713ModelW w * (-(Real.pi : ℂ) * Complex.I * w - w⁻¹)) w := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun v : ℂ => -((Real.pi : ℂ) / 2) * Complex.I * v ^ 2)
      (-((Real.pi : ℂ) / 2) * Complex.I * (2 * w)) w := by
    simpa [mul_assoc] using (hasDerivAt_pow 2 w).const_mul (-((Real.pi : ℂ) / 2) * Complex.I)
  have hnum : HasDerivAt (fun v : ℂ => Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * v ^ 2))
      (Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * w ^ 2)
        * (-((Real.pi : ℂ) / 2) * Complex.I * (2 * w))) w :=
    (Complex.hasDerivAt_exp _).comp w h1
  have hden : HasDerivAt (fun v : ℂ => (Real.pi : ℂ) * v) ((Real.pi : ℂ)) w := by
    simpa using (hasDerivAt_id w).const_mul ((Real.pi : ℂ))
  have hd := hnum.div hden (mul_ne_zero hπ hw)
  convert hd using 1
  rw [fzc713ModelW]
  field_simp

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_hasDerivAt_modelM (ν : ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fzc713ModelM ν) (-(ν * (fzc713ModelW w * (-(Real.pi : ℂ) * Complex.I * w - w⁻¹)))) w := by
  have h := ((fzc713_hasDerivAt_modelW hw).const_mul ν).const_sub (1 : ℂ)
  simpa [fzc713ModelM] using h

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_hasDerivAt_kFun (ν : ℂ) {w : ℂ} (hw : w ≠ 0) (hν : ν ≠ 0) :
    HasDerivAt (fzc713KFun ν)
      (ν * (fzc713ModelW w * (-(Real.pi : ℂ) * Complex.I * w - w⁻¹)) / (ν * fzc713ModelW w) ^ 2) w := by
  have hu : ν * fzc713ModelW w ≠ 0 := mul_ne_zero hν (fzc713_modelW_ne_zero hw)
  have h := (((fzc713_hasDerivAt_modelW hw).const_mul ν).inv hu).const_sub (1 : ℂ)
  have hfun : fzc713KFun ν = fun x => 1 - (ν * fzc713ModelW x)⁻¹ := rfl
  rw [hfun]
  convert h using 1
  ring

/-! ### Polar form on the arc -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `ρ² = π R²/2`, the squared modulus of the erf-variable `ζ = ½√π(1+i)w` on the arc. -/
def fzc713Rho2 (R : ℝ) : ℝ := Real.pi * R ^ 2 / 2

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The continuous argument datum `Ψ(θ) = ρ² cos 2θ + θ − τ`. -/
def fzc713PsiOf (R τ θ : ℝ) : ℝ := fzc713Rho2 R * Real.cos (2 * θ) + θ - τ

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **Polar form of the model factor on the arc.** -/
theorem fzc713_modelW_arcPt {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    fzc713ModelW (arcPoint R θ)
      = ((Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) : ℝ) : ℂ)
          * Complex.exp (((-(fzc713Rho2 R * Real.cos (2 * θ) + θ) : ℝ) : ℂ) * Complex.I) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hexpne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h2 : Complex.exp ((θ : ℂ) * Complex.I) ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  -- the exponent in rectangular form
  have hsq : -((Real.pi : ℂ) / 2) * Complex.I * (arcPoint R θ) ^ 2
      = ((fzc713Rho2 R * Real.sin (2 * θ) : ℝ) : ℂ)
        + ((-(fzc713Rho2 R * Real.cos (2 * θ)) : ℝ) : ℂ) * Complex.I := by
    have hpt : (arcPoint R θ) ^ 2 = ((R : ℝ) : ℂ) ^ 2 *
        (((Real.cos (2 * θ) : ℝ) : ℂ) + ((Real.sin (2 * θ) : ℝ) : ℂ) * Complex.I) := by
      rw [arcPoint, mul_pow, h2, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hpt, fzc713Rho2]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    linear_combination (-((Real.pi : ℂ) / 2) * ((R : ℝ) : ℂ) ^ 2
      * ((Real.sin (2 * θ) : ℝ) : ℂ)) * hI2
  have hsqexp : Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * (arcPoint R θ) ^ 2)
      = ((Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) : ℝ) : ℂ)
          * Complex.exp (((-(fzc713Rho2 R * Real.cos (2 * θ)) : ℝ) : ℂ) * Complex.I) := by
    rw [hsq, Complex.exp_add, ← Complex.ofReal_exp]
  have hsplit : Complex.exp (((-(fzc713Rho2 R * Real.cos (2 * θ) + θ) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-(fzc713Rho2 R * Real.cos (2 * θ)) : ℝ) : ℂ) * Complex.I)
          * (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [fzc713ModelW, hsqexp, hsplit, arcPoint]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_modelW_arcPt_norm {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖fzc713ModelW (arcPoint R θ)‖ = Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) := by
  have hpos : 0 < Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) :=
    div_pos (Real.exp_pos _) (mul_pos Real.pi_pos hR)
  rw [fzc713_modelW_arcPt hR, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The rotated model `ν W` in polar form, `ν = e^{iτ}`. -/
theorem fzc713_nuW_arcPt {R τ : ℝ} (hR : 0 < R) (θ : ℝ) :
    Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)
      = ((Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) : ℝ) : ℂ)
          * Complex.exp (((-(fzc713PsiOf R τ θ) : ℝ) : ℂ) * Complex.I) := by
  rw [fzc713_modelW_arcPt hR]
  rw [show ((-(fzc713PsiOf R τ θ) : ℝ) : ℂ) * Complex.I
      = (τ : ℂ) * Complex.I + ((-(fzc713Rho2 R * Real.cos (2 * θ) + θ) : ℝ) : ℂ) * Complex.I by
    rw [fzc713PsiOf]; push_cast; ring]
  rw [Complex.exp_add]
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_arcPt_norm {R τ : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖
      = Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, fzc713_modelW_arcPt_norm hR]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_arcPt_re {R τ : ℝ} (hR : 0 < R) (θ : ℝ) :
    (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re
      = Real.exp (fzc713Rho2 R * Real.sin (2 * θ)) / (Real.pi * R) * Real.cos (fzc713PsiOf R τ θ) := by
  rw [fzc713_nuW_arcPt hR, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_im, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
  rw [Real.cos_neg]
  ring


/-! ### The branch-free antiderivative -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `Λ(θ) = −iρ² e^{2iθ} − log(πR) + iτ − iθ`, a branch-free logarithm of `ν W` on the arc. -/
def fzc713BigLam (R τ : ℝ) (θ : ℝ) : ℂ :=
  -(Complex.I * ((fzc713Rho2 R : ℝ) : ℂ)) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
    - ((Real.log (Real.pi * R) : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I
      - ((θ : ℝ) : ℂ) * Complex.I

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_bigLam_im (R τ θ : ℝ) : (fzc713BigLam R τ θ).im = -(fzc713PsiOf R τ θ) := by
  have hexp : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (2 * θ) : ℝ) : ℂ) + ((Real.sin (2 * θ) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [fzc713BigLam, hexp, fzc713PsiOf]
  simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.neg_im, Complex.neg_re, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
    Complex.I_re]
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_bigLam_hasDerivAt {R : ℝ} (hR : 0 < R) (τ θ : ℝ) :
    HasDerivAt (fzc713BigLam R τ)
      (deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ)) θ := by
  have hz : arcPoint R θ ≠ 0 := fzc713_arcPoint_ne_zero hR θ
  have hune : fzc713ModelW (arcPoint R θ) ≠ 0 := fzc713_modelW_ne_zero hz
  have hexp2 : Complex.exp ((θ : ℂ) * Complex.I) ^ 2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have hz2 : (arcPoint R θ) ^ 2
      = ((R ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [arcPoint, mul_pow, hexp2]
    push_cast
    ring
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have htarget : deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ)
      = ((Real.pi * R ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
          - Complex.I := by
    rw [(fzc713_hasDerivAt_modelW hz).deriv, mul_div_cancel_left₀ _ hune]
    have hexpand : (-(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹)
        * (Complex.I * arcPoint R θ)
        = -(Real.pi : ℂ) * Complex.I ^ 2 * (arcPoint R θ) ^ 2 - Complex.I := by
      field_simp
    rw [hexpand, hI2, hz2]
    push_cast
    ring
  rw [htarget]
  -- differentiate the closed form
  have h1 : HasDerivAt (fun v : ℂ => 2 * v * Complex.I) (2 * Complex.I) (θ : ℂ) := by
    simpa using ((hasDerivAt_id ((θ : ℂ))).const_mul (2 : ℂ)).mul_const Complex.I
  have h2 : HasDerivAt (fun v : ℂ => Complex.exp (2 * v * Complex.I))
      (Complex.exp (2 * (θ : ℂ) * Complex.I) * (2 * Complex.I)) (θ : ℂ) :=
    (Complex.hasDerivAt_exp (2 * (θ : ℂ) * Complex.I)).comp (θ : ℂ) h1
  have h3 := ((h2.const_mul (-(Complex.I * ((fzc713Rho2 R : ℝ) : ℂ)))).sub_const
    ((Real.log (Real.pi * R) : ℝ) : ℂ)).add_const (((τ : ℝ) : ℂ) * Complex.I)
  have h4 : HasDerivAt (fun v : ℂ => v * Complex.I) Complex.I (θ : ℂ) := by
    simpa using (hasDerivAt_id ((θ : ℂ))).mul_const Complex.I
  have hF := h3.sub h4
  have hEq : fzc713BigLam R τ = fun y : ℝ =>
      (-(Complex.I * ((fzc713Rho2 R : ℝ) : ℂ)) * Complex.exp (2 * (y : ℂ) * Complex.I)
        - ((Real.log (Real.pi * R) : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I - (y : ℂ) * Complex.I) := by
    funext y
    rw [fzc713BigLam]
    push_cast
    ring_nf
  rw [hEq]
  have := hF.comp_ofReal
  convert this using 1
  rw [fzc713Rho2]
  push_cast
  linear_combination ((Real.pi : ℂ) * ((R : ℝ) : ℂ) ^ 2
    * Complex.exp (2 * (θ : ℂ) * Complex.I)) * hI2



/-! ### Numerics -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `L = log(πR)`, the constant of the balance equation `ρ² sin 2θ* = L`. -/
def fzc713BigLc (R : ℝ) : ℝ := Real.log (Real.pi * R)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The split point: the unique `θ ∈ [0, π/4]` with `‖νW‖ = 1`. -/
def fzc713ThetaStar (R : ℝ) : ℝ := Real.arcsin (fzc713BigLc R / fzc713Rho2 R) / 2

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `Ψ = ρ² cos 2θ* + θ* − τ`, minus the continuous argument of `νW` at the split point. -/
def fzc713BigPsi (R τ : ℝ) : ℝ := fzc713PsiOf R τ (fzc713ThetaStar R)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- `φ = 2π·3300 − Ψ ∈ (0, 2π)`, the principal residue. -/
def fzc713BigPhi (R τ : ℝ) : ℝ := 2 * Real.pi * 3300 - fzc713BigPsi R τ

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_R_bounds {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    114.8 ≤ R ∧ R ≤ 114.9 := by
  constructor <;> nlinarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_rho2_bounds {R : ℝ} (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    20729.79 ≤ fzc713Rho2 R ∧ fzc713Rho2 R ≤ 20731.38 := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  rw [fzc713Rho2]
  constructor <;> nlinarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_bigLc_bounds {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    0 < fzc713BigLc R ∧ fzc713BigLc R < 7 := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  obtain ⟨hRlo, hRhi⟩ := fzc713_R_bounds hR hR1 hR2
  have hgt : (1 : ℝ) < Real.pi * R := by nlinarith
  have hlt : Real.pi * R < 361 := by nlinarith
  refine ⟨Real.log_pos hgt, ?_⟩
  have hexp7 : (1046 : ℝ) < Real.exp 7 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h2 : (2.7 : ℝ) ^ (7 : ℕ) < (Real.exp 1) ^ (7 : ℕ) :=
      pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    have h3 : (Real.exp 1) ^ (7 : ℕ) = Real.exp 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    calc (1046 : ℝ) < (2.7 : ℝ) ^ (7 : ℕ) := by norm_num
      _ < (Real.exp 1) ^ (7 : ℕ) := h2
      _ = Real.exp 7 := h3
  have harg : (0 : ℝ) < Real.pi * R := by linarith
  exact (Real.log_lt_iff_lt_exp harg).mpr (by linarith)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_exp_bigLc {R : ℝ} (hR : 0 < R) : Real.exp (fzc713BigLc R) = Real.pi * R :=
  Real.exp_log (mul_pos Real.pi_pos hR)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_xval_bounds {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    0 < fzc713BigLc R / fzc713Rho2 R ∧ fzc713BigLc R / fzc713Rho2 R < 1 := by
  obtain ⟨hL0, hL7⟩ := fzc713_bigLc_bounds hR hR1 hR2
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_thetaStar_pos {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    0 < fzc713ThetaStar R := by
  obtain ⟨h1, h2⟩ := fzc713_xval_bounds hR hR1 hR2
  have := Real.arcsin_pos.mpr h1
  rw [fzc713ThetaStar]; linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_thetaStar_lt {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    fzc713ThetaStar R < Real.pi / 4 := by
  obtain ⟨h1, h2⟩ := fzc713_xval_bounds hR hR1 hR2
  have := Real.arcsin_lt_pi_div_two.mpr h2
  rw [fzc713ThetaStar]; linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_two_thetaStar (R : ℝ) : 2 * fzc713ThetaStar R = Real.arcsin (fzc713BigLc R / fzc713Rho2 R) := by
  rw [fzc713ThetaStar]; ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_sin_two_thetaStar {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    Real.sin (2 * fzc713ThetaStar R) = fzc713BigLc R / fzc713Rho2 R := by
  obtain ⟨h1, h2⟩ := fzc713_xval_bounds hR hR1 hR2
  rw [fzc713_two_thetaStar, Real.sin_arcsin (by linarith) h2.le]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cos_two_thetaStar {R : ℝ} :
    Real.cos (2 * fzc713ThetaStar R) = Real.sqrt (1 - (fzc713BigLc R / fzc713Rho2 R) ^ 2) := by
  rw [fzc713_two_thetaStar, Real.cos_arcsin]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_cos_two_thetaStar_nonneg {R : ℝ} : 0 ≤ Real.cos (2 * fzc713ThetaStar R) := by
  rw [fzc713_cos_two_thetaStar]; exact Real.sqrt_nonneg _

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_rho2_one_sub_cos_thetaStar {R : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2)
    (hR2 : R ^ 2 ≤ 13198) :
    fzc713Rho2 R * (1 - Real.cos (2 * fzc713ThetaStar R)) ≤ 1 := by
  obtain ⟨hL0, hL7⟩ := fzc713_bigLc_bounds hR hR1 hR2
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hs := fzc713_sin_two_thetaStar hR hR1 hR2
  have hc0 := fzc713_cos_two_thetaStar_nonneg (R := R)
  have hpy : Real.sin (2 * fzc713ThetaStar R) ^ 2 + Real.cos (2 * fzc713ThetaStar R) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  set c := Real.cos (2 * fzc713ThetaStar R)
  have hc1 : c ≤ 1 := by nlinarith
  have hkey : 1 - c ≤ Real.sin (2 * fzc713ThetaStar R) ^ 2 := by nlinarith
  have hsv : Real.sin (2 * fzc713ThetaStar R) ^ 2 = (fzc713BigLc R) ^ 2 / (fzc713Rho2 R) ^ 2 := by
    rw [hs]; ring
  have hfin : fzc713Rho2 R * (1 - c) ≤ fzc713Rho2 R * (Real.sin (2 * fzc713ThetaStar R) ^ 2) := by
    apply mul_le_mul_of_nonneg_left hkey (by linarith)
  rw [hsv] at hfin
  have : fzc713Rho2 R * ((fzc713BigLc R) ^ 2 / (fzc713Rho2 R) ^ 2) = (fzc713BigLc R) ^ 2 / fzc713Rho2 R := by
    field_simp
  rw [this] at hfin
  have hdiv : (fzc713BigLc R) ^ 2 / fzc713Rho2 R ≤ 1 := by
    rw [div_le_one (by linarith)]; nlinarith
  linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_bigPhi_bounds {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi) :
    0 < fzc713BigPhi R τ ∧ fzc713BigPhi R τ < 2 * Real.pi := by
  have hπ : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hts0 := fzc713_thetaStar_pos hR hR1 hR2
  have hts1 := fzc713_thetaStar_lt hR hR1 hR2
  have hone := fzc713_rho2_one_sub_cos_thetaStar hR hR1 hR2
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hc1 : Real.cos (2 * fzc713ThetaStar R) ≤ 1 := Real.cos_le_one _
  have hPsi : fzc713BigPsi R τ = 6599 * Real.pi - fzc713Rho2 R * (1 - Real.cos (2 * fzc713ThetaStar R))
      + fzc713ThetaStar R := by
    rw [fzc713BigPsi, fzc713PsiOf]; linarith [hτ]
  have hnn : 0 ≤ fzc713Rho2 R * (1 - Real.cos (2 * fzc713ThetaStar R)) := by
    apply mul_nonneg (by linarith); linarith
  rw [fzc713BigPhi, hPsi]
  constructor <;> linarith

/-! ### Endpoint argument lemmas -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_arg_one_sub_exp_mul_I {φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2 * Real.pi) :
    Complex.arg (1 - Complex.exp ((φ : ℂ) * Complex.I)) = φ / 2 - Real.pi / 2 := by
  have hs : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : Real.cos (φ / 2 - Real.pi / 2) = Real.sin (φ / 2) := by
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsn : Real.sin (φ / 2 - Real.pi / 2) = -Real.cos (φ / 2) := by
    rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hcosφ : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    have hpy := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    linarith
  have hsinφ : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have h := Real.sin_two_mul (φ / 2)
    rwa [show 2 * (φ / 2) = φ by ring] at h
  have hfac : (1 : ℂ) - Complex.exp ((φ : ℂ) * Complex.I)
      = ((2 * Real.sin (φ / 2) : ℝ) : ℂ)
          * (((Real.cos (φ / 2 - Real.pi / 2) : ℝ) : ℂ)
              + ((Real.sin (φ / 2 - Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn,
      hcosφ, hsinφ]
    push_cast
    ring
  have hmem : φ / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hpi := Real.pi_pos
    exact ⟨by linarith, by linarith⟩
  rw [hfac, Complex.arg_real_mul _ (by linarith), Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I hmem]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_one_sub_exp_re_pos {φ : ℝ} (h0 : 0 < φ) (h2 : φ < 2 * Real.pi) :
    0 < (1 - Complex.exp ((φ : ℂ) * Complex.I)).re := by
  have hs : 0 < Real.sin (φ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcosφ : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    have hpy := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    linarith
  have hre : (1 - Complex.exp ((φ : ℂ) * Complex.I)).re = 1 - Real.cos φ := by
    rw [Complex.exp_mul_I]
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re]
  rw [hre, hcosφ]
  nlinarith

/-! ### The contraction estimates -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_sin_lt_sin_of_arc {a b : ℝ} (h0 : 0 ≤ a) (hab : a < b) (hb : b ≤ Real.pi / 2) :
    Real.sin a < Real.sin b := by
  have hπ := Real.pi_pos
  exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, hb⟩ hab

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_norm_lt_one {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    {θ : ℝ} (h0 : 0 ≤ θ) (h : θ < fzc713ThetaStar R) :
    ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖ < 1 := by
  have hπR : 0 < Real.pi * R := mul_pos Real.pi_pos hR
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hts1 := fzc713_thetaStar_lt hR hR1 hR2
  have hπ := Real.pi_pos
  have hsin : Real.sin (2 * θ) < Real.sin (2 * fzc713ThetaStar R) :=
    fzc713_sin_lt_sin_of_arc (by linarith) (by linarith) (by linarith)
  rw [fzc713_sin_two_thetaStar hR hR1 hR2] at hsin
  have hkey : fzc713Rho2 R * Real.sin (2 * θ) < fzc713BigLc R := by
    have := mul_lt_mul_of_pos_left hsin (show (0:ℝ) < fzc713Rho2 R by linarith)
    rwa [mul_div_cancel₀ _ (by linarith : fzc713Rho2 R ≠ 0)] at this
  rw [fzc713_nuW_arcPt_norm hR, div_lt_one hπR, ← fzc713_exp_bigLc hR]
  exact Real.exp_lt_exp.mpr hkey

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_inv_norm_lt_one {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    {θ : ℝ} (h : fzc713ThetaStar R < θ) (h2 : θ ≤ Real.pi / 4) :
    ‖(Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ))⁻¹‖ < 1 := by
  have hπR : 0 < Real.pi * R := mul_pos Real.pi_pos hR
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hts0 := fzc713_thetaStar_pos hR hR1 hR2
  have hπ := Real.pi_pos
  have hsin : Real.sin (2 * fzc713ThetaStar R) < Real.sin (2 * θ) :=
    fzc713_sin_lt_sin_of_arc (by linarith) (by linarith) (by linarith)
  rw [fzc713_sin_two_thetaStar hR hR1 hR2] at hsin
  have hkey : fzc713BigLc R < fzc713Rho2 R * Real.sin (2 * θ) := by
    have := mul_lt_mul_of_pos_left hsin (show (0:ℝ) < fzc713Rho2 R by linarith)
    rwa [mul_div_cancel₀ _ (by linarith : fzc713Rho2 R ≠ 0)] at this
  rw [norm_inv, fzc713_nuW_arcPt_norm hR, inv_lt_one_iff₀]
  right
  rw [lt_div_iff₀ hπR, one_mul, ← fzc713_exp_bigLc hR]
  exact Real.exp_lt_exp.mpr hkey

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_thetaStar {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R (fzc713ThetaStar R))
      = Complex.exp (((fzc713BigPhi R τ : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hπR : 0 < Real.pi * R := mul_pos Real.pi_pos hR
  have hmod : Real.exp (fzc713Rho2 R * Real.sin (2 * fzc713ThetaStar R)) = Real.pi * R := by
    rw [fzc713_sin_two_thetaStar hR hR1 hR2, mul_div_cancel₀ _ (by linarith : fzc713Rho2 R ≠ 0)]
    exact fzc713_exp_bigLc hR
  have hphase : ((-(fzc713PsiOf R τ (fzc713ThetaStar R)) : ℝ) : ℂ) * Complex.I
      = ((fzc713BigPhi R τ : ℝ) : ℂ) * Complex.I + ((-3300 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h : (-(fzc713PsiOf R τ (fzc713ThetaStar R)) : ℝ) = fzc713BigPhi R τ - 2 * Real.pi * 3300 := by
      rw [fzc713BigPhi, fzc713BigPsi]; ring
    rw [h]
    push_cast
    ring
  rw [fzc713_nuW_arcPt hR, hmod, hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one, div_self hπR.ne']
  norm_num

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_thetaStar_inv {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198) :
    (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R (fzc713ThetaStar R)))⁻¹
      = Complex.exp (((2 * Real.pi - fzc713BigPhi R τ : ℝ) : ℂ) * Complex.I) := by
  rw [fzc713_nuW_thetaStar hR hR1 hR2, ← Complex.exp_neg]
  have hsplit : ((2 * Real.pi - fzc713BigPhi R τ : ℝ) : ℂ) * Complex.I
      = -(((fzc713BigPhi R τ : ℝ) : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]



/-! ### `|M| ≥ 1/2` on the eighth arc -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_modelM_norm_ge {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    (1 : ℝ) / 2 ≤ ‖fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖ := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  obtain ⟨hL0, hL7⟩ := fzc713_bigLc_bounds hR hR1 hR2
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  have hπR : 0 < Real.pi * R := mul_pos Real.pi_pos hR
  set s : ℝ := Real.sin (2 * θ) with hs
  set c : ℝ := Real.cos (2 * θ) with hc
  set t : ℝ := Real.exp (fzc713Rho2 R * s) / (Real.pi * R) with ht
  have htpos : 0 < t := div_pos (Real.exp_pos _) hπR
  have hnorm : ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖ = t :=
    fzc713_nuW_arcPt_norm hR θ
  have hre : (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re
      = t * Real.cos (fzc713PsiOf R τ θ) := fzc713_nuW_arcPt_re hR θ
  by_cases hcase : Real.log 2 ≤ |fzc713Rho2 R * s - fzc713BigLc R|
  · have hlogt : Real.log t = fzc713Rho2 R * s - fzc713BigLc R := by
      rw [ht, Real.log_div (Real.exp_ne_zero _) hπR.ne', Real.log_exp, fzc713BigLc]
    have hsplit : t ≤ 1 / 2 ∨ 2 ≤ t := by
      rcases le_abs.mp hcase with h | h
      · right
        have hle : Real.log 2 ≤ Real.log t := by rw [hlogt]; linarith
        exact (Real.log_le_log_iff (by norm_num) htpos).mp hle
      · left
        have hle : Real.log t ≤ Real.log (1 / 2) := by
          rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, hlogt]; linarith
        exact (Real.log_le_log_iff htpos (by norm_num)).mp hle
    have hkey : (1 : ℝ) / 2 ≤ |1 - t| := by
      rcases hsplit with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    calc (1 : ℝ) / 2 ≤ |1 - t| := hkey
      _ = |‖(1 : ℂ)‖ - ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖| := by
            rw [hnorm, norm_one]
      _ ≤ ‖(1 : ℂ) - Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖ :=
            abs_norm_sub_norm_le _ _
      _ = ‖fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖ := by rw [fzc713ModelM]
  · push_neg at hcase
    have hlog2 : Real.log 2 < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hb : |fzc713Rho2 R * s - fzc713BigLc R| < 0.694 := lt_trans hcase hlog2
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
    have hsnn : 0 ≤ s := by
      rw [hs]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hcnn : 0 ≤ c := by
      rw [hc]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hpy : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq _
    have hc1 : c ≤ 1 := by nlinarith
    have hρs : fzc713Rho2 R * s < 7.694 := by linarith
    have hρsnn : 0 ≤ fzc713Rho2 R * s := by
      apply mul_nonneg (by linarith) hsnn
    have hgap : fzc713Rho2 R * (1 - c) ≤ 0.003 := by
      have h1 : 1 - c ≤ s ^ 2 := by nlinarith
      have h2 : fzc713Rho2 R * (1 - c) ≤ fzc713Rho2 R * s ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      nlinarith
    have hgapnn : 0 ≤ fzc713Rho2 R * (1 - c) := mul_nonneg (by linarith) (by linarith)
    have hval : fzc713PsiOf R τ θ - ((3299 : ℤ) : ℝ) * (2 * Real.pi)
        = Real.pi - fzc713Rho2 R * (1 - c) + θ := by
      rw [fzc713PsiOf, ← hc]
      push_cast
      linarith
    have hcosnp : Real.cos (fzc713PsiOf R τ θ) ≤ 0 := by
      rw [← Real.cos_sub_int_mul_two_pi _ (3299 : ℤ), hval]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
    have hrenp : (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re ≤ 0 := by
      rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos htpos.le hcosnp
    have hMre : (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re
        = 1 - (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re := by
      rw [fzc713ModelM]; simp
    have h1 : |(fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re|
        ≤ ‖fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖ := Complex.abs_re_le_norm _
    rw [hMre, abs_of_nonneg (by linarith)] at h1
    linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_modelM_re_pos {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    {θ : ℝ} (h0 : 0 ≤ θ) (h : θ ≤ fzc713ThetaStar R) :
    0 < (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re := by
  have hMre : (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re
      = 1 - (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re := by
    rw [fzc713ModelM]; simp
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := fzc713_nuW_norm_lt_one (τ := τ) hR hR1 hR2 h0 hlt
    have hre : (Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)).re
        ≤ ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖ := Complex.re_le_norm _
    rw [hMre]; linarith
  · obtain ⟨hφ0, hφ2⟩ := fzc713_bigPhi_bounds hR hR1 hR2 hτ
    rw [heq, fzc713ModelM, fzc713_nuW_thetaStar hR hR1 hR2]
    exact fzc713_one_sub_exp_re_pos hφ0 hφ2

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_kFun_re_pos {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    {θ : ℝ} (h : fzc713ThetaStar R ≤ θ) (h2 : θ ≤ Real.pi / 4) :
    0 < (fzc713KFun (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re := by
  have hKre : (fzc713KFun (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re
      = 1 - ((Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ))⁻¹).re := by
    rw [fzc713KFun]; simp
  rcases lt_or_eq_of_le h with hlt | heq
  · have hn := fzc713_nuW_inv_norm_lt_one (τ := τ) hR hR1 hR2 hlt h2
    have hre : ((Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ))⁻¹).re
        ≤ ‖(Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ))⁻¹‖ := Complex.re_le_norm _
    rw [hKre]; linarith
  · obtain ⟨hφ0, hφ2⟩ := fzc713_bigPhi_bounds hR hR1 hR2 hτ
    rw [← heq, fzc713KFun, fzc713_nuW_thetaStar_inv hR hR1 hR2]
    exact fzc713_one_sub_exp_re_pos (by linarith) (by linarith)

/-! ### Continuity on the arc -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_modelW_arcPt {R : ℝ} (hR : 0 < R) :
    Continuous fun θ : ℝ => fzc713ModelW (arcPoint R θ) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : Continuous fun θ : ℝ =>
      Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * (arcPoint R θ) ^ 2) :=
    Complex.continuous_exp.comp (continuous_const.mul ((continuous_arcPoint R).pow 2))
  have h2 : Continuous fun θ : ℝ => (Real.pi : ℂ) * arcPoint R θ :=
    continuous_const.mul (continuous_arcPoint R)
  simpa [fzc713ModelW] using h1.div h2 (fun θ => mul_ne_zero hπ (fzc713_arcPoint_ne_zero hR θ))

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_ratioFactor {R : ℝ} (hR : 0 < R) :
    Continuous fun θ : ℝ => -(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹ :=
  (continuous_const.mul (continuous_arcPoint R)).sub
    ((continuous_arcPoint R).inv₀ (fzc713_arcPoint_ne_zero hR))

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_deriv_modelW_arcPt {R : ℝ} (hR : 0 < R) :
    Continuous fun θ : ℝ => deriv fzc713ModelW (arcPoint R θ) := by
  have heq : (fun θ : ℝ => deriv fzc713ModelW (arcPoint R θ))
      = fun θ : ℝ => fzc713ModelW (arcPoint R θ)
          * (-(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹) :=
    funext fun θ => (fzc713_hasDerivAt_modelW (fzc713_arcPoint_ne_zero hR θ)).deriv
  rw [heq]
  exact (fzc713_continuous_modelW_arcPt hR).mul (fzc713_continuous_ratioFactor hR)

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_modelM_arcPt {R : ℝ} (hR : 0 < R) (ν : ℂ) :
    Continuous fun θ : ℝ => fzc713ModelM ν (arcPoint R θ) := by
  have h : Continuous fun θ : ℝ => (1 : ℂ) - ν * fzc713ModelW (arcPoint R θ) :=
    continuous_const.sub (continuous_const.mul (fzc713_continuous_modelW_arcPt hR))
  simpa [fzc713ModelM] using h

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_deriv_modelM_arcPt {R : ℝ} (hR : 0 < R) (ν : ℂ) :
    Continuous fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) := by
  have heq : (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ))
      = fun θ : ℝ => -(ν * (fzc713ModelW (arcPoint R θ)
          * (-(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹))) :=
    funext fun θ => (fzc713_hasDerivAt_modelM ν (fzc713_arcPoint_ne_zero hR θ)).deriv
  rw [heq]
  exact ((fzc713_continuous_modelW_arcPt hR).mul (fzc713_continuous_ratioFactor hR)).const_mul _ |>.neg

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_arcPt_ne_zero {R : ℝ} (hR : 0 < R) {ν : ℂ} (hν : ν ≠ 0) (θ : ℝ) :
    ν * fzc713ModelW (arcPoint R θ) ≠ 0 :=
  mul_ne_zero hν (fzc713_modelW_ne_zero (fzc713_arcPoint_ne_zero hR θ))

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_kFun_arcPt {R : ℝ} (hR : 0 < R) {ν : ℂ} (hν : ν ≠ 0) :
    Continuous fun θ : ℝ => fzc713KFun ν (arcPoint R θ) := by
  have h : Continuous fun θ : ℝ => (1 : ℂ) - (ν * fzc713ModelW (arcPoint R θ))⁻¹ :=
    continuous_const.sub
      ((continuous_const.mul (fzc713_continuous_modelW_arcPt hR)).inv₀ (fzc713_nuW_arcPt_ne_zero hR hν))
  simpa [fzc713KFun] using h

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_continuous_deriv_kFun_arcPt {R : ℝ} (hR : 0 < R) {ν : ℂ} (hν : ν ≠ 0) :
    Continuous fun θ : ℝ => deriv (fzc713KFun ν) (arcPoint R θ) := by
  have heq : (fun θ : ℝ => deriv (fzc713KFun ν) (arcPoint R θ))
      = fun θ : ℝ => ν * (fzc713ModelW (arcPoint R θ)
          * (-(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹))
            / (ν * fzc713ModelW (arcPoint R θ)) ^ 2 :=
    funext fun θ => (fzc713_hasDerivAt_kFun ν (fzc713_arcPoint_ne_zero hR θ) hν).deriv
  rw [heq]
  exact (((fzc713_continuous_modelW_arcPt hR).mul (fzc713_continuous_ratioFactor hR)).const_mul _).div
    ((continuous_const.mul (fzc713_continuous_modelW_arcPt hR)).pow 2)
    (fun θ => pow_ne_zero 2 (fzc713_nuW_arcPt_ne_zero hR hν θ))

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The pointwise factorisation `M'/M = (νW)'/(νW) + k'/k`. -/
theorem fzc713_logDeriv_factor_split (U g X : ℂ) (hU : U ≠ 0) (hM : 1 - U ≠ 0) :
    -(U * g) / (1 - U) * X
      = U * g / U * X + U * g / U ^ 2 / (1 - U⁻¹) * X := by
  have hU1 : U - 1 ≠ 0 := fun h => hM (by rw [show (1 : ℂ) - U = -(U - 1) by ring, h, neg_zero])
  have h1 : (1 : ℂ) - U⁻¹ = (U - 1) / U := by field_simp
  rw [h1]
  field_simp
  ring



-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- The pointwise splitting `M'/M = (νW)'/(νW) + k'/k` behind `M = (−νW)·k`. -/
theorem fzc713_logDeriv_split (ν W g X : ℂ) (hν : ν ≠ 0) (hW : W ≠ 0) (hM : 1 - ν * W ≠ 0) :
    -(ν * (W * g)) / (1 - ν * W) * X
      = W * g / W * X + ν * (W * g) / (ν * W) ^ 2 / (1 - (ν * W)⁻¹) * X := by
  have hνW : ν * W ≠ 0 := mul_ne_zero hν hW
  have hne : ν * W - 1 ≠ 0 := fun h =>
    hM (by rw [show (1 : ℂ) - ν * W = -(ν * W - 1) by ring, h, neg_zero])
  have h1 : (1 : ℂ) - (ν * W)⁻¹ = (ν * W - 1) / (ν * W) := by field_simp
  rw [h1]
  field_simp
  ring

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The model arc integral in closed form.** -/
theorem fzc713_modelArc_im {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi) :
    (arcLogDerivIntegral (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I))) R 0 (Real.pi / 4)).im
      = 2 * Real.pi * 3300 - 5 * Real.pi / 4 + τ
        - Complex.arg (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R 0))
        + Complex.arg (fzc713KFun (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R (Real.pi / 4))) := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hνne : ν ≠ 0 := by rw [hνdef]; exact Complex.exp_ne_zero _
  obtain ⟨hφ0, hφ2⟩ := fzc713_bigPhi_bounds hR hR1 hR2 hτ
  have hπ := Real.pi_pos
  have hts0 : 0 < fzc713ThetaStar R := fzc713_thetaStar_pos hR hR1 hR2
  have hts2 : fzc713ThetaStar R < Real.pi / 4 := fzc713_thetaStar_lt hR hR1 hR2
  have huIcc1 : Set.uIcc (0 : ℝ) (fzc713ThetaStar R) = Set.Icc 0 (fzc713ThetaStar R) := Set.uIcc_of_le hts0.le
  have huIcc2 : Set.uIcc (fzc713ThetaStar R) (Real.pi / 4) = Set.Icc (fzc713ThetaStar R) (Real.pi / 4) :=
    Set.uIcc_of_le hts2.le
  have hsub1 : Set.Icc (0 : ℝ) (fzc713ThetaStar R) ⊆ Set.Icc 0 (Real.pi / 4) :=
    Set.Icc_subset_Icc le_rfl hts2.le
  have hsub2 : Set.Icc (fzc713ThetaStar R) (Real.pi / 4) ⊆ Set.Icc (0 : ℝ) (Real.pi / 4) :=
    Set.Icc_subset_Icc hts0.le le_rfl
  -- nonvanishing
  have hune : ∀ θ : ℝ, ν * fzc713ModelW (arcPoint R θ) ≠ 0 := fzc713_nuW_arcPt_ne_zero hR hνne
  have hMne : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4), fzc713ModelM ν (arcPoint R θ) ≠ 0 := by
    intro θ hθ h0
    have h := fzc713_modelM_norm_ge hR hR1 hR2 hτ hθ.1 hθ.2
    rw [← hνdef, h0, norm_zero] at h
    linarith
  have hkne : ∀ θ ∈ Set.Icc (fzc713ThetaStar R) (Real.pi / 4), fzc713KFun ν (arcPoint R θ) ≠ 0 := by
    intro θ hθ h0
    have h := fzc713_kFun_re_pos hR hR1 hR2 hτ hθ.1 hθ.2
    rw [← hνdef, h0] at h
    simp at h
  -- continuity / integrability
  have hrot : Continuous fun θ : ℝ => Complex.I * arcPoint R θ :=
    continuous_const.mul (continuous_arcPoint R)
  have hFMcont : ContinuousOn
      (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)
        * (Complex.I * arcPoint R θ)) (Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    ((fzc713_continuous_deriv_modelM_arcPt hR ν).continuousOn.div
      (fzc713_continuous_modelM_arcPt hR ν).continuousOn hMne).mul hrot.continuousOn
  have hFUcont : Continuous
      (fun θ : ℝ => deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ)) :=
    ((fzc713_continuous_deriv_modelW_arcPt hR).div (fzc713_continuous_modelW_arcPt hR)
      (fun θ => fzc713_modelW_ne_zero (fzc713_arcPoint_ne_zero hR θ))).mul hrot
  have hFKcont : ContinuousOn
      (fun θ : ℝ => deriv (fzc713KFun ν) (arcPoint R θ) / fzc713KFun ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
      (Set.Icc (fzc713ThetaStar R) (Real.pi / 4)) :=
    ((fzc713_continuous_deriv_kFun_arcPt hR hνne).continuousOn.div
      (fzc713_continuous_kFun_arcPt hR hνne).continuousOn hkne).mul hrot.continuousOn
  have hFMint1 : IntervalIntegrable
      (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)
        * (Complex.I * arcPoint R θ)) volume 0 (fzc713ThetaStar R) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc1]; exact hFMcont.mono hsub1
  have hFMint2 : IntervalIntegrable
      (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)
        * (Complex.I * arcPoint R θ)) volume (fzc713ThetaStar R) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFMcont.mono hsub2
  have hFUint : IntervalIntegrable
      (fun θ : ℝ => deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ))
      volume (fzc713ThetaStar R) (Real.pi / 4) := hFUcont.intervalIntegrable _ _
  have hFKint : IntervalIntegrable
      (fun θ : ℝ => deriv (fzc713KFun ν) (arcPoint R θ) / fzc713KFun ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
      volume (fzc713ThetaStar R) (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc2]; exact hFKcont
  -- split at the crossing point
  have hsplit : arcLogDerivIntegral (fzc713ModelM ν) R 0 (Real.pi / 4)
      = (∫ θ in (0 : ℝ)..(fzc713ThetaStar R),
          deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
        + ∫ θ in (fzc713ThetaStar R)..(Real.pi / 4),
            deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ) :=
    (intervalIntegral.integral_add_adjacent_intervals hFMint1 hFMint2).symm
  have hleft : (∫ θ in (0 : ℝ)..(fzc713ThetaStar R),
      deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
      = Complex.log (fzc713ModelM ν (arcPoint R (fzc713ThetaStar R)))
        - Complex.log (fzc713ModelM ν (arcPoint R 0)) := by
    have hdiff : ∀ θ ∈ Set.uIcc (0 : ℝ) (fzc713ThetaStar R),
        DifferentiableAt ℂ (fzc713ModelM ν) (arcPoint R θ) :=
      fun θ _ => (fzc713_hasDerivAt_modelM ν (fzc713_arcPoint_ne_zero hR θ)).differentiableAt
    have hslit : ∀ θ ∈ Set.uIcc (0 : ℝ) (fzc713ThetaStar R),
        fzc713ModelM ν (arcPoint R θ) ∈ Complex.slitPlane := by
      intro θ hθ
      rw [huIcc1] at hθ
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (fzc713_modelM_re_pos hR hR1 hR2 hτ hθ.1 hθ.2))
    exact arc_logDeriv_integral hdiff hslit hFMint1
  have hMeq : ∀ θ ∈ Set.Icc (fzc713ThetaStar R) (Real.pi / 4),
      deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ)
        = deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ)
          + deriv (fzc713KFun ν) (arcPoint R θ) / fzc713KFun ν (arcPoint R θ) * (Complex.I * arcPoint R θ) := by
    intro θ hθ
    have hW := fzc713_modelW_ne_zero (fzc713_arcPoint_ne_zero hR θ)
    have hM := hMne θ (hsub2 hθ)
    rw [fzc713ModelM] at hM
    rw [(fzc713_hasDerivAt_modelM ν (fzc713_arcPoint_ne_zero hR θ)).deriv,
      (fzc713_hasDerivAt_modelW (fzc713_arcPoint_ne_zero hR θ)).deriv,
      (fzc713_hasDerivAt_kFun ν (fzc713_arcPoint_ne_zero hR θ) hνne).deriv, fzc713ModelM, fzc713KFun]
    exact fzc713_logDeriv_split _ _ _ _ hνne hW hM
  have hright : (∫ θ in (fzc713ThetaStar R)..(Real.pi / 4),
      deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
      = (fzc713BigLam R τ (Real.pi / 4) - fzc713BigLam R τ (fzc713ThetaStar R))
        + (Complex.log (fzc713KFun ν (arcPoint R (Real.pi / 4)))
            - Complex.log (fzc713KFun ν (arcPoint R (fzc713ThetaStar R)))) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv fzc713ModelW (arcPoint R θ) / fzc713ModelW (arcPoint R θ) * (Complex.I * arcPoint R θ)
          + deriv (fzc713KFun ν) (arcPoint R θ) / fzc713KFun ν (arcPoint R θ) * (Complex.I * arcPoint R θ))
      (fun θ hθ => hMeq θ (by rwa [huIcc2] at hθ)),
      intervalIntegral.integral_add hFUint hFKint]
    congr 1
    · exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ => fzc713_bigLam_hasDerivAt hR τ θ) hFUint
    · have hdiff : ∀ θ ∈ Set.uIcc (fzc713ThetaStar R) (Real.pi / 4),
          DifferentiableAt ℂ (fzc713KFun ν) (arcPoint R θ) :=
        fun θ _ => (fzc713_hasDerivAt_kFun ν (fzc713_arcPoint_ne_zero hR θ) hνne).differentiableAt
      have hslit : ∀ θ ∈ Set.uIcc (fzc713ThetaStar R) (Real.pi / 4),
          fzc713KFun ν (arcPoint R θ) ∈ Complex.slitPlane := by
        intro θ hθ
        rw [huIcc2] at hθ
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (fzc713_kFun_re_pos hR hR1 hR2 hτ hθ.1 hθ.2))
      exact arc_logDeriv_integral hdiff hslit hFKint
  -- the two split-point arguments
  have hargMstar : Complex.arg (fzc713ModelM ν (arcPoint R (fzc713ThetaStar R)))
      = fzc713BigPhi R τ / 2 - Real.pi / 2 := by
    rw [fzc713ModelM, hνdef, fzc713_nuW_thetaStar hR hR1 hR2]
    exact fzc713_arg_one_sub_exp_mul_I hφ0 hφ2
  have hargKstar : Complex.arg (fzc713KFun ν (arcPoint R (fzc713ThetaStar R)))
      = (2 * Real.pi - fzc713BigPhi R τ) / 2 - Real.pi / 2 := by
    rw [fzc713KFun, hνdef, fzc713_nuW_thetaStar_inv hR hR1 hR2]
    exact fzc713_arg_one_sub_exp_mul_I (by linarith) (by linarith)
  have hpsi4 : fzc713PsiOf R τ (Real.pi / 4) = Real.pi / 4 - τ := by
    rw [fzc713PsiOf, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    ring
  have hpsistar : fzc713PsiOf R τ (fzc713ThetaStar R) = fzc713BigPsi R τ := rfl
  have hphi : fzc713BigPhi R τ = 2 * Real.pi * 3300 - fzc713BigPsi R τ := rfl
  rw [hsplit, hleft, hright]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [hargMstar, hargKstar, fzc713_bigLam_im, fzc713_bigLam_im, hpsi4, hpsistar]
  linarith



/-! ### `|νW| ≤ 4|M|` -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_nuW_le_four_modelM {R τ : ℝ} (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    ‖Complex.exp ((τ : ℂ) * Complex.I) * fzc713ModelW (arcPoint R θ)‖
      ≤ 4 * ‖fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖ := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hM : (1 : ℝ) / 2 ≤ ‖fzc713ModelM ν (arcPoint R θ)‖ := fzc713_modelM_norm_ge hR hR1 hR2 hτ hθ0 hθ1
  rcases le_total (‖ν * fzc713ModelW (arcPoint R θ)‖) 2 with h | h
  · linarith
  · have hge : ‖ν * fzc713ModelW (arcPoint R θ)‖ - ‖(1 : ℂ)‖ ≤ ‖ν * fzc713ModelW (arcPoint R θ) - 1‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, ← norm_neg (ν * fzc713ModelW (arcPoint R θ) - 1)] at hge
    have hneg : -(ν * fzc713ModelW (arcPoint R θ) - 1) = fzc713ModelM ν (arcPoint R θ) := by rw [fzc713ModelM]; ring
    rw [hneg] at hge
    linarith

/-! ### The ratio bound -/

set_option maxHeartbeats 1600000 in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_fresnel_ratio_bound {R τ : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    (hcν : Complex.exp ((τ : ℂ) * Complex.I) * (1 + Complex.I) = c)
    (hcn : ‖c‖ ≤ 1.4143)
    (hform : ∀ z : ℂ, 4 * f z
      = 2 - (starRingEnd ℂ) c
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - c * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    ‖4 * f (arcPoint R θ) - 2 * fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖
      ≤ ‖fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)‖ := by
  have hπlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hπhi : Real.pi < 3.141593 := Real.pi_lt_d6
  obtain ⟨hρ0, hρ1⟩ := fzc713_rho2_bounds hR1 hR2
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hνn : ‖ν‖ = 1 := by rw [hνdef]; exact Complex.norm_exp_ofReal_mul_I τ
  set w : ℂ := arcPoint R θ with hwdef
  have hwne : w ≠ 0 := fzc713_arcPoint_ne_zero hR θ
  have hwn : ‖w‖ = R := fzc713_arcPoint_norm hR θ
  set ζ : ℂ := (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w with hζdef
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hsp2 : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    norm_cast; exact Real.sq_sqrt Real.pi_pos.le
  have hsplo : (1.77 : ℝ) ≤ Real.sqrt Real.pi := by
    have h : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi]
  -- modulus of ζ
  have hζn2 : ‖ζ‖ ^ 2 = fzc713Rho2 R := by
    rw [hζdef, fresnel_zeta_norm_sq, hwn, fzc713Rho2]; ring
  have hζnpos : (143 : ℝ) ≤ ‖ζ‖ := by nlinarith [norm_nonneg ζ, hζn2]
  have hζne : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζnpos; linarith
  -- the arc's half-plane facts
  have hwre : w.re = R * Real.cos θ := arcPoint_re R θ
  have hwim : w.im = R * Real.sin θ := fzc713_arcPoint_im R θ
  have hcosge : Real.sin θ ≤ Real.cos θ := by
    have h1 : Real.sin θ = Real.cos (Real.pi / 2 - θ) := (Real.cos_pi_div_two_sub θ).symm
    rw [h1]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsinnn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hζre : 0 ≤ ζ.re := by
    rw [hζdef, fresnel_zeta_re, hwre, hwim]
    have : 0 ≤ R * Real.cos θ - R * Real.sin θ := by nlinarith
    nlinarith [Real.sqrt_nonneg Real.pi]
  have hζim : 0 < ζ.im := by
    rw [hζdef, fresnel_zeta_im, hwre, hwim]
    have h1 : (0:ℝ) < 1 / 2 * Real.sqrt Real.pi := by positivity
    have h2 : (0:ℝ) < R * Real.cos θ + R * Real.sin θ := by nlinarith
    exact mul_pos h1 h2
  -- the exponent
  have hζsq : ζ ^ 2 = ((Real.pi : ℂ) / 2) * Complex.I * w ^ 2 := by
    rw [hζdef]
    linear_combination ((1 / 4) * (1 + Complex.I) ^ 2 * w ^ 2) * hsp2
      + ((1 / 4) * (Real.pi : ℂ) * w ^ 2) * hI2
  have hexpprod : Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * w ^ 2)
      * Complex.exp (ζ ^ 2) = 1 := by
    rw [hζsq, ← Complex.exp_add,
      show -((Real.pi : ℂ) / 2) * Complex.I * w ^ 2 + (Real.pi : ℂ) / 2 * Complex.I * w ^ 2 = 0 by
        ring, Complex.exp_zero]
  have hw2 : w ^ 2 = ((R ^ 2 : ℝ) : ℂ)
      * (((Real.cos (2 * θ) : ℝ) : ℂ) + ((Real.sin (2 * θ) : ℝ) : ℂ) * Complex.I) := by
    have hexp2 : Complex.exp ((θ : ℂ) * Complex.I) ^ 2
        = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hwdef, arcPoint, mul_pow, hexp2, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    push_cast
    ring
  have hw2im : (w ^ 2).im = R ^ 2 * Real.sin (2 * θ) := by
    rw [hw2]
    simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hζsq' : ζ ^ 2 = (((Real.pi / 2 : ℝ)) : ℂ) * Complex.I * w ^ 2 := by
    rw [hζsq]; push_cast; ring
  have hζ2re : (ζ ^ 2).re = -(fzc713Rho2 R * Real.sin (2 * θ)) := by
    rw [hζsq']
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [hw2im, fzc713Rho2]
    ring
  have hsinnn2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  -- the key algebraic identity `c = 2νW·√π ζ e^{ζ²}`
  have hπc : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcw : 2 * (ν * fzc713ModelW w) * ((Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2)) = c := by
    have hstep : 2 * (ν * fzc713ModelW w) * ((Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2))
        = ν * (1 + Complex.I) * ((((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 / (Real.pi : ℂ))
            * (Complex.exp (-((Real.pi : ℂ) / 2) * Complex.I * w ^ 2) * Complex.exp (ζ ^ 2))) := by
      rw [fzc713ModelW, hζdef]
      field_simp
      try ring
    rw [hstep, hsp2, hexpprod, div_self hπc, mul_one, mul_one, hcν]
  -- the two remainder bounds
  set E : ℂ := (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) * cerfc ζ - 1 with hEdef
  have hEb : ‖E‖ ≤ 4 / fzc713Rho2 R := by
    have hsec : |Complex.arg ζ| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr hζre
    have h := erf713_cerfc_scaled_unit_bound_closed hζne hsec
    rwa [hζn2] at h
  have hAb : ‖cerfc (-Complex.I * ζ)‖ ≤ 0.004 := by
    set v : ℂ := -Complex.I * ζ with hvdef
    have hvn : ‖v‖ = ‖ζ‖ := by rw [hvdef, norm_mul]; simp
    have hvre : 0 < v.re := by
      rw [hvdef]
      simpa [Complex.mul_re] using hζim
    have h := cerfc_scaled_unit_bound hvre
    have hv2 : v ^ 2 = -ζ ^ 2 := by rw [hvdef]; linear_combination (ζ ^ 2) * hI2
    have hv2re : (v ^ 2).re = fzc713Rho2 R * Real.sin (2 * θ) := by
      rw [hv2, Complex.neg_re, hζ2re, neg_neg]
    have hexpv : ‖Complex.exp (v ^ 2)‖ = Real.exp ((v ^ 2).re) := Complex.norm_exp _
    have hexpge : (1 : ℝ) ≤ ‖Complex.exp (v ^ 2)‖ := by
      rw [hexpv, hv2re]
      exact Real.one_le_exp (by positivity)
    have hprod : ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * cerfc v‖
        ≤ 1 + 4 / ‖v‖ ^ 2 := by
      have h1 := norm_sub_norm_le ((Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * cerfc v)
        (1 : ℂ)
      rw [norm_one] at h1
      linarith [h1, h]
    have hexpand : ‖(Real.sqrt Real.pi : ℂ) * v * Complex.exp (v ^ 2) * cerfc v‖
        = Real.sqrt Real.pi * ‖v‖ * ‖Complex.exp (v ^ 2)‖ * ‖cerfc v‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hexpand, hvn, hζn2] at hprod
    have hfour : 4 / fzc713Rho2 R ≤ 0.0002 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hcnn : 0 ≤ ‖cerfc v‖ := norm_nonneg _
    have hA1 : (253 : ℝ) ≤ Real.sqrt Real.pi * ‖ζ‖ := by nlinarith [hsplo, hζnpos]
    have hA2 : Real.sqrt Real.pi * ‖ζ‖
        ≤ Real.sqrt Real.pi * ‖ζ‖ * ‖Complex.exp (v ^ 2)‖ :=
      le_mul_of_one_le_right (by positivity) hexpge
    have hA3 : (253 : ℝ) * ‖cerfc v‖
        ≤ Real.sqrt Real.pi * ‖ζ‖ * ‖Complex.exp (v ^ 2)‖ * ‖cerfc v‖ :=
      mul_le_mul_of_nonneg_right (le_trans hA1 hA2) hcnn
    linarith [hA3, hprod, hfour]
  -- the splitting identity
  have hBsplit : c * cerfc ζ = 2 * (ν * fzc713ModelW w) * (1 + E) := by
    rw [hEdef]
    rw [show (1 : ℂ) + ((Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) * cerfc ζ - 1)
        = (Real.sqrt Real.pi : ℂ) * ζ * Complex.exp (ζ ^ 2) * cerfc ζ by ring, ← hcw]
    ring
  have hid : 4 * f w - 2 * fzc713ModelM ν w
      = -(2 * (ν * fzc713ModelW w) * E) - (starRingEnd ℂ) c * cerfc (-Complex.I * ζ) := by
    rw [hform w, ← hζdef, fzc713ModelM, hBsplit]
    ring
  -- the final estimate
  have hM12 : (1 : ℝ) / 2 ≤ ‖fzc713ModelM ν (arcPoint R θ)‖ := fzc713_modelM_norm_ge hR hR1 hR2 hτ hθ0 hθ1
  have hW4 : ‖ν * fzc713ModelW w‖ ≤ 4 * ‖fzc713ModelM ν (arcPoint R θ)‖ :=
    fzc713_nuW_le_four_modelM hR hR1 hR2 hτ hθ0 hθ1
  have hcnorm : ‖(starRingEnd ℂ) c‖ = ‖c‖ := Complex.norm_conj c
  have hbound : ‖4 * f w - 2 * fzc713ModelM ν w‖
      ≤ 2 * ‖ν * fzc713ModelW w‖ * ‖E‖ + ‖c‖ * ‖cerfc (-Complex.I * ζ)‖ := by
    rw [hid]
    refine le_trans (norm_sub_le _ _) ?_
    have e1 : ‖-(2 * (ν * fzc713ModelW w) * E)‖ = 2 * ‖ν * fzc713ModelW w‖ * ‖E‖ := by
      rw [norm_neg, norm_mul, norm_mul]
      norm_num
    have e2 : ‖(starRingEnd ℂ) c * cerfc (-Complex.I * ζ)‖
        = ‖c‖ * ‖cerfc (-Complex.I * ζ)‖ := by rw [norm_mul, hcnorm]
    rw [e1, e2]
  have hEnn : 0 ≤ ‖E‖ := norm_nonneg _
  have hWnn : 0 ≤ ‖ν * fzc713ModelW w‖ := norm_nonneg _
  have hEb' : ‖E‖ ≤ 0.0002 := by
    refine le_trans hEb ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  have hAnn : 0 ≤ ‖cerfc (-Complex.I * ζ)‖ := norm_nonneg _
  have hcnn : 0 ≤ ‖c‖ := norm_nonneg _
  calc ‖4 * f w - 2 * fzc713ModelM ν w‖
      ≤ 2 * ‖ν * fzc713ModelW w‖ * ‖E‖ + ‖c‖ * ‖cerfc (-Complex.I * ζ)‖ := hbound
    _ ≤ ‖fzc713ModelM ν (arcPoint R θ)‖ := by
          have p1 : 2 * ‖ν * fzc713ModelW w‖ * ‖E‖
              ≤ 2 * (4 * ‖fzc713ModelM ν (arcPoint R θ)‖) * 0.0002 := by
            nlinarith [hW4, hEb', hEnn, hWnn]
          have p2 : ‖c‖ * ‖cerfc (-Complex.I * ζ)‖ ≤ 1.4143 * 0.004 := by
            nlinarith [hcn, hAb, hAnn, hcnn]
          have p3 : (1.4143 : ℝ) * 0.004 ≤ 0.0114 * ‖fzc713ModelM ν (arcPoint R θ)‖ := by
            nlinarith [hM12]
          linarith



/-! ### The arc split against the true function -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_ratio_norm_le {R τ : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    (hcν : Complex.exp ((τ : ℂ) * Complex.I) * (1 + Complex.I) = c)
    (hcn : ‖c‖ ≤ 1.4143)
    (hform : ∀ z : ℂ, 4 * f z
      = 2 - (starRingEnd ℂ) c
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - c * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    ‖2 * f (arcPoint R θ) / fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ) - 1‖
      ≤ 1 / 2 := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hM12 : (1 : ℝ) / 2 ≤ ‖fzc713ModelM ν (arcPoint R θ)‖ := fzc713_modelM_norm_ge hR hR1 hR2 hτ hθ0 hθ1
  have hMpos : 0 < ‖fzc713ModelM ν (arcPoint R θ)‖ := by linarith
  have hMne : fzc713ModelM ν (arcPoint R θ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hMpos; exact lt_irrefl 0 hMpos
  have hb := fzc713_fresnel_ratio_bound hR hR1 hR2 hτ hcν hcn hform hθ0 hθ1
  have hid : 2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) - 1
      = (4 * f (arcPoint R θ) - 2 * fzc713ModelM ν (arcPoint R θ)) / (2 * fzc713ModelM ν (arcPoint R θ)) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
  linarith

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_ratio_re_pos {R τ : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    (hcν : Complex.exp ((τ : ℂ) * Complex.I) * (1 + Complex.I) = c)
    (hcn : ‖c‖ ≤ 1.4143)
    (hform : ∀ z : ℂ, 4 * f z
      = 2 - (starRingEnd ℂ) c
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - c * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 4) :
    0 < (2 * f (arcPoint R θ) / fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R θ)).re := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hb := fzc713_ratio_norm_le hR hR1 hR2 hτ hcν hcn hform hθ0 hθ1
  have h1 : |(2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) - 1).re|
      ≤ ‖2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) - 1‖ := Complex.abs_re_le_norm _
  simp only [Complex.sub_re, Complex.one_re] at h1
  have h2 := (abs_le.mp (le_trans h1 hb)).1
  linarith

set_option maxHeartbeats 1600000 in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
theorem fzc713_arcIntegral_split {R τ : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    (hcν : Complex.exp ((τ : ℂ) * Complex.I) * (1 + Complex.I) = c)
    (hcn : ‖c‖ ≤ 1.4143)
    (hform : ∀ z : ℂ, 4 * f z
      = 2 - (starRingEnd ℂ) c
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - c * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
    (hfd : Differentiable ℂ f) (hfdc : Continuous (deriv f)) :
    arcLogDerivIntegral f R 0 (Real.pi / 4)
      = arcLogDerivIntegral (fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I))) R 0 (Real.pi / 4)
        + (Complex.log (2 * f (arcPoint R (Real.pi / 4))
              / fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R (Real.pi / 4)))
            - Complex.log (2 * f (arcPoint R 0)
              / fzc713ModelM (Complex.exp ((τ : ℂ) * Complex.I)) (arcPoint R 0))) := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hνne : ν ≠ 0 := by rw [hνdef]; exact Complex.exp_ne_zero _
  have hπ4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have huIcc : Set.uIcc (0 : ℝ) (Real.pi / 4) = Set.Icc 0 (Real.pi / 4) := Set.uIcc_of_le hπ4
  have hzne : ∀ θ : ℝ, arcPoint R θ ≠ 0 := fzc713_arcPoint_ne_zero hR
  have hMne : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4), fzc713ModelM ν (arcPoint R θ) ≠ 0 := by
    intro θ hθ h0
    have h := fzc713_modelM_norm_ge hR hR1 hR2 hτ hθ.1 hθ.2
    rw [← hνdef, h0, norm_zero] at h
    linarith
  have hratiore : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      0 < (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)).re := by
    intro θ hθ
    exact fzc713_ratio_re_pos hR hR1 hR2 hτ hcν hcn hform hθ.1 hθ.2
  have hfne : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4), f (arcPoint R θ) ≠ 0 := by
    intro θ hθ h0
    have h := hratiore θ hθ
    rw [h0] at h
    simp at h
  -- derivatives
  have hMd : ∀ θ : ℝ, HasDerivAt (fzc713ModelM ν)
      (-(ν * (fzc713ModelW (arcPoint R θ)
        * (-(Real.pi : ℂ) * Complex.I * arcPoint R θ - (arcPoint R θ)⁻¹)))) (arcPoint R θ) :=
    fun θ => fzc713_hasDerivAt_modelM ν (hzne θ)
  have h2fd : ∀ θ : ℝ, HasDerivAt (fun z : ℂ => 2 * f z) (2 * deriv f (arcPoint R θ)) (arcPoint R θ) :=
    fun θ => ((hfd (arcPoint R θ)).hasDerivAt).const_mul 2
  have hHd : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      HasDerivAt (fun z => 2 * f z / fzc713ModelM ν z)
        ((2 * deriv f (arcPoint R θ) * fzc713ModelM ν (arcPoint R θ)
            - 2 * f (arcPoint R θ) * deriv (fzc713ModelM ν) (arcPoint R θ))
          / (fzc713ModelM ν (arcPoint R θ)) ^ 2) (arcPoint R θ) :=
    fun θ hθ => (h2fd θ).div ((hMd θ).differentiableAt.hasDerivAt) (hMne θ hθ)
  -- continuity
  have hdfc : Continuous (fun θ : ℝ => deriv f (arcPoint R θ)) := hfdc.comp (continuous_arcPoint R)
  have hfc : Continuous (fun θ : ℝ => f (arcPoint R θ)) := hfd.continuous.comp (continuous_arcPoint R)
  have hrot : Continuous (fun θ : ℝ => Complex.I * arcPoint R θ) :=
    continuous_const.mul (continuous_arcPoint R)
  have hFc : ContinuousOn
      (fun θ : ℝ => deriv f (arcPoint R θ) / f (arcPoint R θ) * (Complex.I * arcPoint R θ))
      (Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    (hdfc.continuousOn.div hfc.continuousOn hfne).mul hrot.continuousOn
  have hFm : ContinuousOn
      (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)
        * (Complex.I * arcPoint R θ)) (Set.Icc (0 : ℝ) (Real.pi / 4)) :=
    ((fzc713_continuous_deriv_modelM_arcPt hR ν).continuousOn.div
      (fzc713_continuous_modelM_arcPt hR ν).continuousOn hMne).mul hrot.continuousOn
  -- the pointwise splitting
  have hEq : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      deriv f (arcPoint R θ) / f (arcPoint R θ) * (Complex.I * arcPoint R θ)
        = deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ)
          + deriv (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ)
              / (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)) * (Complex.I * arcPoint R θ) := by
    intro θ hθ
    rw [(hHd θ hθ).deriv]
    have hM := hMne θ hθ
    have hfz := hfne θ hθ
    field_simp
    ring
  have hFh : ContinuousOn
      (fun θ : ℝ => deriv (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ)
        / (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)) * (Complex.I * arcPoint R θ))
      (Set.Icc (0 : ℝ) (Real.pi / 4)) := by
    refine (hFc.sub hFm).congr ?_
    intro θ hθ
    show deriv (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ)
        / (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)) * (Complex.I * arcPoint R θ)
      = deriv f (arcPoint R θ) / f (arcPoint R θ) * (Complex.I * arcPoint R θ)
        - deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ)
    rw [hEq θ hθ]
    ring
  have hFmInt : IntervalIntegrable
      (fun θ : ℝ => deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)
        * (Complex.I * arcPoint R θ)) volume 0 (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFm
  have hFhInt : IntervalIntegrable
      (fun θ : ℝ => deriv (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ)
        / (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)) * (Complex.I * arcPoint R θ))
      volume 0 (Real.pi / 4) := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hFh
  have hslit : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4),
      (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ) ∈ Complex.slitPlane := by
    intro θ hθ
    rw [huIcc] at hθ
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (hratiore θ hθ))
  have hdiff : ∀ θ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4),
      DifferentiableAt ℂ (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ) := by
    intro θ hθ
    rw [huIcc] at hθ
    exact (hHd θ hθ).differentiableAt
  have hlog := arc_logDeriv_integral (f := fun z => 2 * f z / fzc713ModelM ν z) (r := R) (a := (0 : ℝ))
    (b := Real.pi / 4) hdiff hslit hFhInt
  have hmain : arcLogDerivIntegral f R 0 (Real.pi / 4)
      = arcLogDerivIntegral (fzc713ModelM ν) R 0 (Real.pi / 4)
        + arcLogDerivIntegral (fun z => 2 * f z / fzc713ModelM ν z) R 0 (Real.pi / 4) := by
    show (∫ θ in (0 : ℝ)..(Real.pi / 4),
        deriv f (arcPoint R θ) / f (arcPoint R θ) * (Complex.I * arcPoint R θ)) = _
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
        deriv (fzc713ModelM ν) (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ) * (Complex.I * arcPoint R θ)
          + deriv (fun z => 2 * f z / fzc713ModelM ν z) (arcPoint R θ)
              / (2 * f (arcPoint R θ) / fzc713ModelM ν (arcPoint R θ)) * (Complex.I * arcPoint R θ))
      (fun θ hθ => hEq θ (by rwa [huIcc] at hθ))]
    exact intervalIntegral.integral_add hFmInt hFhInt
  rw [hmain, hlog]

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The arc integral is within `2π` of the model prediction.** -/
theorem fzc713_arc_im_close {R τ : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hR1 : 13197 ≤ R ^ 2) (hR2 : R ^ 2 ≤ 13198)
    (hτ : fzc713Rho2 R - τ = 6599 * Real.pi)
    (hcν : Complex.exp ((τ : ℂ) * Complex.I) * (1 + Complex.I) = c)
    (hcn : ‖c‖ ≤ 1.4143)
    (hform : ∀ z : ℂ, 4 * f z
      = 2 - (starRingEnd ℂ) c
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - c * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
    (hfd : Differentiable ℂ f) (hfdc : Continuous (deriv f)) :
    |(arcLogDerivIntegral f R 0 (Real.pi / 4)).im - (2 * Real.pi * 3300 - 5 * Real.pi / 4 + τ)|
      < 2 * Real.pi := by
  set ν : ℂ := Complex.exp ((τ : ℂ) * Complex.I) with hνdef
  have hπ := Real.pi_pos
  have hts0 : 0 < fzc713ThetaStar R := fzc713_thetaStar_pos hR hR1 hR2
  have hts1 : fzc713ThetaStar R < Real.pi / 4 := fzc713_thetaStar_lt hR hR1 hR2
  rw [fzc713_arcIntegral_split hR hR1 hR2 hτ hcν hcn hform hfd hfdc]
  simp only [Complex.add_im, Complex.sub_im, Complex.log_im]
  rw [fzc713_modelArc_im hR hR1 hR2 hτ]
  -- the four residual arguments
  have hA1 : |Complex.arg (fzc713ModelM ν (arcPoint R 0))| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (fzc713_modelM_re_pos hR hR1 hR2 hτ le_rfl hts0.le))
  have hA2 : |Complex.arg (fzc713KFun ν (arcPoint R (Real.pi / 4)))| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (fzc713_kFun_re_pos hR hR1 hR2 hτ hts1.le le_rfl))
  have hA3 : |Complex.arg (2 * f (arcPoint R (Real.pi / 4))
      / fzc713ModelM ν (arcPoint R (Real.pi / 4)))| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (fzc713_ratio_re_pos hR hR1 hR2 hτ hcν hcn hform (by positivity) le_rfl))
  have hA4 : |Complex.arg (2 * f (arcPoint R 0) / fzc713ModelM ν (arcPoint R 0))| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (fzc713_ratio_re_pos hR hR1 hR2 hτ hcν hcn hform le_rfl (by positivity)))
  obtain ⟨a1, b1⟩ := abs_lt.mp hA1
  obtain ⟨a2, b2⟩ := abs_lt.mp hA2
  obtain ⟨a3, b3⟩ := abs_lt.mp hA3
  obtain ⟨a4, b4⟩ := abs_lt.mp hA4
  rw [abs_lt]
  constructor <;> linarith




/-! ### Part 11 — the assembly

Everything above composes to the two counts: the argument principle on the counting circle,
folded to the eighth arc, evaluated against the model.  The two eighth-arc values
(`fzc713_arc_cfresnelC_im`, `fzc713_arc_cfresnelS_im`) are the Fresnel analogues of
`erf713_arc_cerf_im`. -/

-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- No zero of an entire, not-identically-zero `f` has infinite analytic order. -/
theorem fzc713_analyticOrder_ne_top {f : ℂ → ℂ} (hdiff : Differentiable ℂ f) (hf1 : f 1 ≠ 0)
    (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hAn : AnalyticOnNhd ℂ f Set.univ := fun w _ => hdiff.analyticAt w
  have heq := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) htop
  exact hf1 (by simpa using heq (Set.mem_univ (1 : ℂ)))

open FLMF.Error in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `C` model-arc value.**  `Im ∫₀^{π/4} (C'/C)(R e^{iθ})·(i R e^{iθ}) dθ = π/4 + 2π·3299`
at `R² = 13197`. -/
theorem fzc713_arc_cfresnelC_im :
    (arcLogDerivIntegral cfresnelC fzc713RadC 0 (Real.pi / 4)).im = Real.pi / 4 + 2 * Real.pi * 3299 := by
  classical
  have hπ := Real.pi_pos
  have hRsq : fzc713RadC ^ 2 = 13197 := fzc713_RadC_sq
  have hτ : fzc713Rho2 fzc713RadC - (-(Real.pi / 2)) = 6599 * Real.pi := by
    rw [fzc713Rho2, hRsq]; ring
  have hexpν : Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast
    ring
  have hcν : Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) * (1 + Complex.I)
      = 1 - Complex.I := by
    rw [hexpν]
    linear_combination -Complex.I_sq
  have hcn : ‖(1 : ℂ) - Complex.I‖ ≤ 1.4143 := by
    have h : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      norm_num
    nlinarith [norm_nonneg ((1 : ℂ) - Complex.I), h]
  have hform : ∀ z : ℂ, 4 * cfresnelC z
      = 2 - (starRingEnd ℂ) (1 - Complex.I)
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - (1 - Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) := by
    intro z
    rw [show (starRingEnd ℂ) (1 - Complex.I) = 1 + Complex.I by simp]
    exact cfresnelC_erfc_form z
  have hdcont : Continuous (deriv cfresnelC) := by rw [fzc713_deriv_cfresnelC]; fun_prop
  have hbound := fzc713_arc_im_close (R := fzc713RadC) (τ := -(Real.pi / 2)) (c := 1 - Complex.I)
    (f := cfresnelC) fzc713_RadC_pos (by rw [hRsq]) (by rw [hRsq]; norm_num) hτ hcν hcn hform
    fzc713_cfresnelC_differentiable hdcont
  -- the argument principle: the arc value is quantized
  obtain ⟨P, hP, hPball, hsum⟩ := fzc713_zeros_finset_exists_C
  set N : ℕ := {w : ℂ | cfresnelC w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13197}.ncard
    with hN
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadC → cfresnelC z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelC_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadC_sq
  have hAP := FLMF.Methods.circleIntegral_logDeriv_eq_sum_orders (f := cfresnelC) (c := 0)
    (R := fzc713RadC) fzc713_RadC_pos P (fun z _ => fzc713_cfresnelC_analyticAt z) hP hPball
    (fun p _ => fzc713_analyticOrder_ne_top fzc713_cfresnelC_differentiable fzc713_cfresnelC_one_ne_zero p)
  rw [fzc713_circle_eq_eight_I_arc_im_C fzc713_RadC_pos hcirc, hsum] at hAP
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hkey : ((8 * (arcLogDerivIntegral cfresnelC fzc713RadC 0 (Real.pi / 4)).im : ℝ) : ℂ)
      = ((2 * Real.pi * (1 + 8 * (N : ℝ)) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast
    linear_combination hAP
  have hreal : 8 * (arcLogDerivIntegral cfresnelC fzc713RadC 0 (Real.pi / 4)).im
      = 2 * Real.pi * (1 + 8 * (N : ℝ)) := Complex.ofReal_inj.mp hkey
  have hq : (arcLogDerivIntegral cfresnelC fzc713RadC 0 (Real.pi / 4)).im
      = Real.pi / 4 + 2 * Real.pi * (N : ℝ) := by linarith
  rw [hq] at hbound
  have hNr : 2 * Real.pi * |(N : ℝ) - 3299| < 2 * Real.pi := by
    have heq : Real.pi / 4 + 2 * Real.pi * (N : ℝ)
        - (2 * Real.pi * 3300 - 5 * Real.pi / 4 + -(Real.pi / 2))
          = 2 * Real.pi * ((N : ℝ) - 3299) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbound
    exact hbound
  have habs : |(N : ℝ) - 3299| < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hNr]
  have h1 : (N : ℝ) < 3300 := by linarith [(abs_lt.mp habs).2]
  have h2 : (3298 : ℝ) < (N : ℝ) := by linarith [(abs_lt.mp habs).1]
  have h1' : N < 3300 := by exact_mod_cast h1
  have h2' : 3298 < N := by exact_mod_cast h2
  have hNv : N = 3299 := by omega
  rw [hq, hNv]
  norm_num

open FLMF.Error in
-- no-dlmf: §7.13 Fresnel zero-count infrastructure
/-- **The `S` model-arc value.**  `Im ∫₀^{π/4} (S'/S)(R e^{iθ})·(i R e^{iθ}) dθ = 3π/4 + 2π·3299`
at `R² = 13198`.  The `3π/4` is the origin's *triple* zero. -/
theorem fzc713_arc_cfresnelS_im :
    (arcLogDerivIntegral cfresnelS fzc713RadS 0 (Real.pi / 4)).im
      = 3 * Real.pi / 4 + 2 * Real.pi * 3299 := by
  classical
  have hπ := Real.pi_pos
  have hRsq : fzc713RadS ^ 2 = 13198 := fzc713_RadS_sq
  have hτ : fzc713Rho2 fzc713RadS - 0 = 6599 * Real.pi := by
    rw [fzc713Rho2, hRsq]; ring
  have hcν : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * (1 + Complex.I) = 1 + Complex.I := by
    simp
  have hcn : ‖(1 : ℂ) + Complex.I‖ ≤ 1.4143 := by
    have h : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      norm_num
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I), h]
  have hform : ∀ z : ℂ, 4 * cfresnelS z
      = 2 - (starRingEnd ℂ) (1 + Complex.I)
          * cerfc (-Complex.I * ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z))
        - (1 + Complex.I) * cerfc ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) := by
    intro z
    rw [show (starRingEnd ℂ) (1 + Complex.I) = 1 - Complex.I by
      rw [map_add, map_one, Complex.conj_I]; ring]
    exact cfresnelS_erfc_form z
  have hdcont : Continuous (deriv cfresnelS) := by rw [fzc713_deriv_cfresnelS]; fun_prop
  have hbound := fzc713_arc_im_close (R := fzc713RadS) (τ := 0) (c := 1 + Complex.I)
    (f := cfresnelS) fzc713_RadS_pos (by rw [hRsq]; norm_num) (by rw [hRsq]) hτ hcν hcn hform
    fzc713_cfresnelS_differentiable hdcont
  obtain ⟨P, hP, hPball, hsum⟩ := fzc713_zeros_finset_exists_S
  set N : ℕ := {w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13198}.ncard
    with hN
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadS → cfresnelS z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelS_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadS_sq
  have hAP := FLMF.Methods.circleIntegral_logDeriv_eq_sum_orders (f := cfresnelS) (c := 0)
    (R := fzc713RadS) fzc713_RadS_pos P (fun z _ => fzc713_cfresnelS_analyticAt z) hP hPball
    (fun p _ => fzc713_analyticOrder_ne_top fzc713_cfresnelS_differentiable fzc713_cfresnelS_one_ne_zero p)
  rw [fzc713_circle_eq_eight_I_arc_im_S fzc713_RadS_pos hcirc, hsum] at hAP
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hkey : ((8 * (arcLogDerivIntegral cfresnelS fzc713RadS 0 (Real.pi / 4)).im : ℝ) : ℂ)
      = ((2 * Real.pi * (3 + 8 * (N : ℝ)) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hI
    push_cast
    linear_combination hAP
  have hreal : 8 * (arcLogDerivIntegral cfresnelS fzc713RadS 0 (Real.pi / 4)).im
      = 2 * Real.pi * (3 + 8 * (N : ℝ)) := Complex.ofReal_inj.mp hkey
  have hq : (arcLogDerivIntegral cfresnelS fzc713RadS 0 (Real.pi / 4)).im
      = 3 * Real.pi / 4 + 2 * Real.pi * (N : ℝ) := by linarith
  rw [hq] at hbound
  have hNr : 2 * Real.pi * |(N : ℝ) - 3299| < 2 * Real.pi := by
    have heq : 3 * Real.pi / 4 + 2 * Real.pi * (N : ℝ)
        - (2 * Real.pi * 3300 - 5 * Real.pi / 4 + 0)
          = 2 * Real.pi * ((N : ℝ) - 3299) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbound
    exact hbound
  have habs : |(N : ℝ) - 3299| < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hNr]
  have h1 : (N : ℝ) < 3300 := by linarith [(abs_lt.mp habs).2]
  have h2 : (3298 : ℝ) < (N : ℝ) := by linarith [(abs_lt.mp habs).1]
  have h1' : N < 3300 := by exact_mod_cast h1
  have h2' : 3298 < N := by exact_mod_cast h2
  have hNv : N = 3299 := by omega
  rw [hq, hNv]
  norm_num

-- no-dlmf: the count of the small sub-diagonal zeros of `C`; the index-origin input to
-- `erf_7_13_5`
/-- **The number of small sub-diagonal zeros of the Fresnel integral `C`.**  `C` has exactly
`3299` zeros `w` with `0 < Im w < Re w` and `‖w‖² < 13197`.

Its role is to fix the *origin* of the enumeration: the analysis above establishes a strictly
modulus-increasing bijection between the sub-diagonal zeros with `‖w‖² ≥ 13197` and the
indices `n ≥ 3300` (`fresnel713_grid_zero`, `fresnel_zero_index_exists`,
`fresnel713_zero_index_unique`), which determines DLMF's enumeration only up to a constant
index offset.  The offset vanishes exactly when the number of zeros below the cut equals the
number of grid points below it, i.e. when the count here is `3300 − 1 = 3299`.

**Route** (section `Fresnel713ZeroCount` above).  The `D₄` symmetry of the zero set
(`z ↦ −z`, `z ↦ conj z`, `z ↦ i z`, together with mirror-ray freeness) turns the octant count
`N` into the full-disc multiplicity total `1 + 8N` on `‖z‖ ≤ √13197`; the argument principle
evaluates that total through the circle integral of `C'/C`, which the order-4 rotation and the
conjugation fold to `8i·Im J` over the eighth arc `θ ∈ [0, π/4]`.  On that arc `C` is pinned
to the level-`ν` elementary model `M = 1 − νW`, `W(w) = e^{−iπw²/2}/(π w)`, by the Poincaré
remainder bound, and `νW` carries a branch-free logarithm with a closed-form arc integral; all
four residual endpoint arguments lie in `(−π/2, π/2)`, so `Im J` is within `2π` of the model
value, which pins the integer.

The threshold `13197` is chosen strictly between the two neighbouring grid values
`λ_C(3299)² = 13195` and `λ_C(3300)² = 13199`, with margin `≈ 1.9` on each side — far larger
than the `0.13` localization that `fresnel713_match_sector` gives for `‖w‖²`; so no zero of
index `3299` or `3300` sits ambiguously at the cut, and the counting circle itself is
zero-free (`fzc713_cfresnelC_ne_zero_on_circle`). -/
theorem fresnelC713_low_zero_count :
    {w : ℂ | cfresnelC w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13197}.ncard = 3299 := by
  classical
  obtain ⟨P, hP, hPball, hsum⟩ := fzc713_zeros_finset_exists_C
  set N : ℕ := {w : ℂ | cfresnelC w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13197}.ncard
    with hN
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadC → cfresnelC z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelC_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadC_sq
  have hAP := FLMF.Methods.circleIntegral_logDeriv_eq_sum_orders (f := cfresnelC) (c := 0)
    (R := fzc713RadC) fzc713_RadC_pos P (fun z _ => fzc713_cfresnelC_analyticAt z) hP hPball
    (fun p _ => fzc713_analyticOrder_ne_top fzc713_cfresnelC_differentiable fzc713_cfresnelC_one_ne_zero p)
  have hval : (∮ z in C((0:ℂ), fzc713RadC), deriv cfresnelC z / cfresnelC z)
      = 2 * (Real.pi : ℂ) * Complex.I * (26393 : ℂ) := by
    rw [fzc713_circle_eq_eight_I_arc_im_C fzc713_RadC_pos hcirc, fzc713_arc_cfresnelC_im]
    push_cast
    ring
  rw [hval, hsum] at hAP
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hcancel : (26393 : ℂ) = 1 + 8 * (N : ℂ) := mul_left_cancel₀ h2 hAP
  have hR : (26393 : ℝ) = 1 + 8 * (N : ℝ) := by exact_mod_cast congrArg Complex.re hcancel
  have : (N : ℝ) = 3299 := by linarith
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
-- no-dlmf: the eventual DLMF 7.13.5 bounds for the `C` enumeration; proof infrastructure
/-- **The `C`-branch eventual bound.**  For a complete, modulus-ordered, 1-based enumeration
`z` of the sub-diagonal first-quadrant zeros of `C`, both coordinates of `z m` agree with the
DLMF 7.13.5 approximations at index `m` to within `3 λ⁻³`, for all large `m`. -/
theorem fresnelC713_eventual (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cfresnelC (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cfresnelC w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w) :
    ∀ᶠ m : ℕ in atTop,
      |(z m).re - fresnelCZeroReApprox m| ≤ 3 / (fresnelCZeroLambda m) ^ 3 ∧
      |(z m).im - fresnelCZeroImApprox m| ≤ 3 / (fresnelCZeroLambda m) ^ 3 := by
  have hpi := Real.pi_gt_d6
  have hspsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hcre : (1 - Complex.I).re = 1 := by simp
  have hcimval : (1 - Complex.I).im = -1 := by simp
  have hcim : (1 - Complex.I).im = 1 ∨ (1 - Complex.I).im = -1 := Or.inr hcimval
  have hlink : ∀ w : ℂ, 4 * cfresnelC w
      = 2 - (starRingEnd ℂ) (1 - Complex.I)
            * FLMF.Error.cerfc
                (-Complex.I * ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
        - (1 - Complex.I)
            * FLMF.Error.cerfc ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w) := by
    intro w
    have hc : (starRingEnd ℂ) (1 - Complex.I) = 1 + Complex.I := by
      rw [map_sub, map_one, Complex.conj_I]; ring
    rw [hc]
    exact cfresnelC_erfc_form w
  have hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < fresnelCZeroLambda m := fun m hm => fresnelCZeroLambda_pos hm
  have hLamsq : ∀ m : ℕ, 1 ≤ m →
      4 * ((1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m) ^ 2
        = Real.pi * (4 * (m:ℝ) - 1) := by
    intro m hm
    rw [← fresnelCZeroLambda_sq hm]; nlinarith [hspsq]
  have hLamQ : ∀ m : ℕ, 1 ≤ m →
      4 * ((1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m) ^ 2
        = 4 * Real.pi * (m:ℝ) - Real.pi / 2 + (1 - Complex.I).im * (Real.pi / 2) := by
    intro m hm; rw [hLamsq m hm, hcimval]; ring
  have hLampos : ∀ m : ℕ, 1 ≤ m →
      0 < (1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m := by
    intro m hm
    exact mul_pos (mul_pos (by norm_num) hsppos) (hLFpos m hm)
  have hLam100 : ∀ m : ℕ, 3300 ≤ m →
      100 ≤ (1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m := by
    intro m hm
    have hm1 : 1 ≤ m := by omega
    have hmR : (3300:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hpos := hLampos m hm1
    have hsq := hLamsq m hm1
    nlinarith [hsq, hmR, hpos, hpi]
  have hMu : ∀ m : ℕ, 1 ≤ m →
      2 * Real.log (Real.pi * fresnelCZeroLambda m)
        = Real.log (4 * Real.pi * ((1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m) ^ 2) := by
    intro m hm
    have hL := hLFpos m hm
    have h1 : 4 * Real.pi * ((1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m) ^ 2
        = (Real.pi * fresnelCZeroLambda m) ^ 2 := by nlinarith [hspsq]
    rw [h1, Real.log_pow]; push_cast; ring
  have hcount : {w : ℂ | cfresnelC w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
      ‖w‖ ^ 2 < 4 * 3300 + ((1 - Complex.I).im - 1) / 2 - 2}.ncard = 3299 := by
    have hval : (4 * 3300 + ((1 - Complex.I).im - 1) / 2 - 2 : ℝ) = 13197 := by
      rw [hcimval]; norm_num
    rw [hval]; exact fresnelC713_low_zero_count
  have hev := fresnel713_eventual_bounds
    (Lam := fun m => (1/2) * Real.sqrt Real.pi * fresnelCZeroLambda m)
    (Mu := fun m => Real.log (Real.pi * fresnelCZeroLambda m))
    (LF := fresnelCZeroLambda)
    hcre hcim hlink hLamQ hLampos hLam100 hMu hLFpos (fun m _ => rfl)
    z hzero hquad hmono hall hcount
  have hReEq : ∀ m : ℕ, 1 ≤ m →
      fresnelCZeroLambda m
        + ((Real.log (Real.pi * fresnelCZeroLambda m)) ^ 2
            - 2 * Real.log (Real.pi * fresnelCZeroLambda m))
          / (2 * Real.pi ^ 2 * (fresnelCZeroLambda m) ^ 3)
        = fresnelCZeroReApprox m := by
    intro m hm
    have hL := hLFpos m hm
    have hL0 : fresnelCZeroLambda m ≠ 0 := ne_of_gt hL
    have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    simp only [fresnelCZeroReApprox, fresnelCZeroAlpha]
    field_simp
    ring
  have hImEq : ∀ m : ℕ, 1 ≤ m →
      Real.log (Real.pi * fresnelCZeroLambda m) / (Real.pi * fresnelCZeroLambda m)
        = fresnelCZeroImApprox m := by
    intro m hm
    have hL := hLFpos m hm
    have hL0 : fresnelCZeroLambda m ≠ 0 := ne_of_gt hL
    have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    simp only [fresnelCZeroImApprox, fresnelCZeroAlpha]
    field_simp
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with m h1 h2
  rw [← hReEq m h2, ← hImEq m h2]
  exact h1

-- no-dlmf: C(z)-only restriction of DLMF 7.13.5; DLMF §7.13(iii) also extends
-- (7.13.5) verbatim, with the 7.13.7 parameters, to zeros of S(z); faithful
-- surface is erf_7_13_5_full
/-- DLMF 7.13.5 (C-branch, with 7.13.6 parameters) — asymptotic expansion of the complex
zeros `zₙ = xₙ + i yₙ` of the Fresnel integral `C`, for the complete enumeration `z`,
ordered by increasing absolute value (DLMF §7.13(iii)), of all *sub-diagonal*
first-quadrant zeros of `cfresnelC` (`hall`): the real part of `z n` agrees with
`fresnelCZeroReApprox` to within `O(λ⁻³)` and the imaginary part with
`fresnelCZeroImApprox` up to `o(λ⁻¹)`.

**Mirror-pair restriction.** The open first quadrant is *not* enumerable in strictly
increasing absolute value: `cfresnelC_zero_mirror` shows `w ↦ i·conj w` is an involution
of the quadrant that swaps real and imaginary parts and preserves zeros, so each zero of
the DLMF family (`xₙ → ∞`, `yₙ = α/(2λ) → 0`) is paired with a mirror zero of *exactly
equal* absolute value — DLMF §7.13(iii)'s "arranged in order of increasing absolute
value", read over the whole quadrant, is unsatisfiable. The enumeration is therefore
restricted to the sub-diagonal representative `0 < im < re` of each mirror pair —
exactly DLMF's family, within which the modulus ordering is strict.

**Index origin.** DLMF numbers the zeros from `n = 1` and the enumeration matches that
1-based labelling directly: only `z n` for `1 ≤ n` is constrained (`z 0` is unconstrained
junk, harmless in the asymptotic conclusions), and `z n` is DLMF's `zₙ`, compared with
the `n`-th approximations.

**Order of the real part.** The displayed `λ⁻³` coefficient of 7.13.5 is incomplete: the
correct expansion is `xₙ = λ + (α²/8 − α/(2π) + 1/π²)·λ⁻³ + ⋯` whereas the display gives
`α(απ − 4)/(8πλ³) = (α²/8 − α/(2π))·λ⁻³`, so the residual is `λ⁻³/π² + o(λ⁻³)`
(numerically `(xₙ − fresnelCZeroReApprox n)·λ³ → 0.10128…`, against `1/π² = 0.101321…`).
The real-part error is thus `Θ(λ⁻³)`, *not* `o(λ⁻³)`, and the sharp true statement at
DLMF's approximant is the `O(λ⁻³)` bound asserted here.
* dlmf: 7.13.5
* family: fresnel
* kind: zero-asymptotic
-/
theorem erf_7_13_5 (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cfresnelC (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cfresnelC w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w) :
    (fun n => (z n).re - fresnelCZeroReApprox n) =O[atTop]
        (fun n => (fresnelCZeroLambda n) ^ (-3 : ℤ)) ∧
      (fun n => (z n).im - fresnelCZeroImApprox n) =o[atTop]
        (fun n => (fresnelCZeroLambda n) ^ (-1 : ℤ)) := by
  have hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < fresnelCZeroLambda m :=
    fun m hm => fresnelCZeroLambda_pos hm
  have hLFge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ (fresnelCZeroLambda m) ^ 2 := by
    intro m hm
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [fresnelCZeroLambda_sq hm]; linarith
  have hev := fresnelC713_eventual z hzero hquad hmono hall
  exact ⟨fresnel713_bigO hLFpos (hev.mono fun m h => h.1),
    fresnel713_littleO hLFpos hLFge (hev.mono fun m h => h.2)⟩

/-! ## Fresnel `S` zeros — approximation (DLMF 7.13.5 with 7.13.7 params) -/

-- no-dlmf: encodes the 7.13.5 approximant; display surfaced at `erf_7_13_5_full`
/-- DLMF 7.13.5 (with 7.13.7 parameters) — approximation of the real part of the
`n`-th complex zero of the Fresnel integral `S`:
`xₙ = λ + α·(α·π − 4)/(8π·λ³)`.
* dlmf: 7.13.5
* family: fresnel
* kind: zero-approximation -/
def fresnelSZeroReApprox (n : ℕ) : ℝ :=
  let lam := fresnelSZeroLambda n
  let a := fresnelSZeroAlpha n
  lam + a * (a * Real.pi - 4) / (8 * Real.pi * lam ^ 3)

-- no-dlmf: encodes the 7.13.5 approximant; display surfaced at `erf_7_13_5_full`
/-- DLMF 7.13.5 (with 7.13.7 parameters) — approximation of the imaginary part of
the `n`-th complex zero of the Fresnel integral `S`:
`yₙ = α/(2·λ)`.
* dlmf: 7.13.5
* family: fresnel
* kind: zero-approximation -/
def fresnelSZeroImApprox (n : ℕ) : ℝ :=
  let lam := fresnelSZeroLambda n
  let a := fresnelSZeroAlpha n
  a / (2 * lam)

-- no-dlmf: the square of the DLMF 7.13.7 parameter; proof infrastructure
/-- `λ_S(n)² = 4n`. -/
theorem fresnelSZeroLambda_sq (n : ℕ) : fresnelSZeroLambda n ^ 2 = 4 * (n:ℝ) := by
  have h : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  simp only [fresnelSZeroLambda]; nlinarith [h]

-- no-dlmf: positivity of the DLMF 7.13.7 parameter; proof infrastructure
/-- `λ_S(n) > 0` for `n ≥ 1`. -/
theorem fresnelSZeroLambda_pos {n : ℕ} (hn : 1 ≤ n) : 0 < fresnelSZeroLambda n := by
  have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by linarith)
  simp only [fresnelSZeroLambda]; linarith

-- no-dlmf: the count of the small sub-diagonal zeros of `S`; the index-origin input to
-- `erf_7_13_5_S` / to the `S` half of `erf_7_13_5_full`
/-- **The number of small sub-diagonal zeros of the Fresnel integral `S`.**  `S` has exactly
`3299` zeros `w` with `0 < Im w < Re w` and `‖w‖² < 13198`.

Exactly as for `fresnelC713_low_zero_count`, its role is to fix the *origin* of the
enumeration: the analysis above gives a strictly modulus-increasing bijection between the
sub-diagonal zeros with `‖w‖² ≥ 13198` and the indices `n ≥ 3300`, determining DLMF's
enumeration up to a constant index offset, and the offset vanishes exactly when the count here
is `3300 − 1 = 3299`.

**Route** (section `Fresnel713ZeroCount` above).  The same `D₄` argument-principle computation
as for `C`, with one difference: the origin is a *triple* zero of `S`
(`fzc713_analyticOrderNatAt_cfresnelS_zero`), so the full-disc multiplicity total on
`‖z‖ ≤ √13198` is `3 + 8N` rather than `1 + 8N`, and the folded eighth-arc value is
`3π/4 + 2πN` rather than `π/4 + 2πN`.  The model half of the argument is shared verbatim: the
level-`ν` model `M = 1 − νW` is parametrized by `(R, τ)` with `πR²/2 − τ = 6599π`, and `S` is
the endpoint `τ = 0` of the same segment whose other endpoint is `C`.

The threshold `13198` lies strictly between the neighbouring grid values `λ_S(3299)² = 13196`
and `λ_S(3300)² = 13200`, with margin `≈ 1.9` on each side — far larger than the `0.13`
localization of `‖w‖²`, and the counting circle itself is zero-free
(`fzc713_cfresnelS_ne_zero_on_circle`). -/
theorem fresnelS713_low_zero_count :
    {w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13198}.ncard = 3299 := by
  classical
  obtain ⟨P, hP, hPball, hsum⟩ := fzc713_zeros_finset_exists_S
  set N : ℕ := {w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧ ‖w‖ ^ 2 < 13198}.ncard
    with hN
  have hcirc : ∀ z : ℂ, ‖z‖ = fzc713RadS → cfresnelS z ≠ 0 := by
    intro z hzn
    refine fzc713_cfresnelS_ne_zero_on_circle ?_
    rw [hzn]; exact fzc713_RadS_sq
  have hAP := FLMF.Methods.circleIntegral_logDeriv_eq_sum_orders (f := cfresnelS) (c := 0)
    (R := fzc713RadS) fzc713_RadS_pos P (fun z _ => fzc713_cfresnelS_analyticAt z) hP hPball
    (fun p _ => fzc713_analyticOrder_ne_top fzc713_cfresnelS_differentiable fzc713_cfresnelS_one_ne_zero p)
  have hval : (∮ z in C((0:ℂ), fzc713RadS), deriv cfresnelS z / cfresnelS z)
      = 2 * (Real.pi : ℂ) * Complex.I * (26395 : ℂ) := by
    rw [fzc713_circle_eq_eight_I_arc_im_S fzc713_RadS_pos hcirc, fzc713_arc_cfresnelS_im]
    push_cast
    ring
  rw [hval, hsum] at hAP
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hcancel : (26395 : ℂ) = 3 + 8 * (N : ℂ) := mul_left_cancel₀ h2 hAP
  have hR : (26395 : ℝ) = 3 + 8 * (N : ℝ) := by exact_mod_cast congrArg Complex.re hcancel
  have : (N : ℝ) = 3299 := by linarith
  exact_mod_cast this

end Fresnel713ZeroCount

set_option maxHeartbeats 1000000 in
-- no-dlmf: the eventual DLMF 7.13.5 bounds for the `S` enumeration; proof infrastructure
-- shared by `erf_7_13_5_S` and the `S` half of `erf_7_13_5_full`
/-- **The `S`-branch eventual bound.**  For a complete, modulus-ordered, 1-based enumeration
`z` of the sub-diagonal first-quadrant zeros of `S`, both coordinates of `z m` agree with the
DLMF 7.13.5 approximations (7.13.7 parameters) at index `m` to within `3 λ⁻³`, for all
large `m`. -/
theorem fresnelS713_eventual (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cfresnelS (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cfresnelS w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w) :
    ∀ᶠ m : ℕ in atTop,
      |(z m).re - fresnelSZeroReApprox m| ≤ 3 / (fresnelSZeroLambda m) ^ 3 ∧
      |(z m).im - fresnelSZeroImApprox m| ≤ 3 / (fresnelSZeroLambda m) ^ 3 := by
  have hpi := Real.pi_gt_d6
  have hspsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsppos : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hcre : (1 + Complex.I).re = 1 := by simp
  have hcimval : (1 + Complex.I).im = 1 := by simp
  have hcim : (1 + Complex.I).im = 1 ∨ (1 + Complex.I).im = -1 := Or.inl hcimval
  have hlink : ∀ w : ℂ, 4 * cfresnelS w
      = 2 - (starRingEnd ℂ) (1 + Complex.I)
            * FLMF.Error.cerfc
                (-Complex.I * ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w))
        - (1 + Complex.I)
            * FLMF.Error.cerfc ((1/2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * w) := by
    intro w
    have hc : (starRingEnd ℂ) (1 + Complex.I) = 1 - Complex.I := by
      rw [map_add, map_one, Complex.conj_I]; ring
    rw [hc]
    exact cfresnelS_erfc_form w
  have hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < fresnelSZeroLambda m := fun m hm => fresnelSZeroLambda_pos hm
  have hLamsq : ∀ m : ℕ, 1 ≤ m →
      4 * ((1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m) ^ 2
        = Real.pi * (4 * (m:ℝ)) := by
    intro m _
    rw [← fresnelSZeroLambda_sq m]; nlinarith [hspsq]
  have hLamQ : ∀ m : ℕ, 1 ≤ m →
      4 * ((1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m) ^ 2
        = 4 * Real.pi * (m:ℝ) - Real.pi / 2 + (1 + Complex.I).im * (Real.pi / 2) := by
    intro m hm; rw [hLamsq m hm, hcimval]; ring
  have hLampos : ∀ m : ℕ, 1 ≤ m →
      0 < (1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m := by
    intro m hm
    exact mul_pos (mul_pos (by norm_num) hsppos) (hLFpos m hm)
  have hLam100 : ∀ m : ℕ, 3300 ≤ m →
      100 ≤ (1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m := by
    intro m hm
    have hm1 : 1 ≤ m := by omega
    have hmR : (3300:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hpos := hLampos m hm1
    have hsq := hLamsq m hm1
    nlinarith [hsq, hmR, hpos, hpi]
  have hMu : ∀ m : ℕ, 1 ≤ m →
      2 * Real.log (Real.pi * fresnelSZeroLambda m)
        = Real.log (4 * Real.pi * ((1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m) ^ 2) := by
    intro m hm
    have hL := hLFpos m hm
    have h1 : 4 * Real.pi * ((1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m) ^ 2
        = (Real.pi * fresnelSZeroLambda m) ^ 2 := by nlinarith [hspsq]
    rw [h1, Real.log_pow]; push_cast; ring
  have hcount : {w : ℂ | cfresnelS w = 0 ∧ 0 < w.im ∧ w.im < w.re ∧
      ‖w‖ ^ 2 < 4 * 3300 + ((1 + Complex.I).im - 1) / 2 - 2}.ncard = 3299 := by
    have hval : (4 * 3300 + ((1 + Complex.I).im - 1) / 2 - 2 : ℝ) = 13198 := by
      rw [hcimval]; norm_num
    rw [hval]; exact fresnelS713_low_zero_count
  have hev := fresnel713_eventual_bounds
    (Lam := fun m => (1/2) * Real.sqrt Real.pi * fresnelSZeroLambda m)
    (Mu := fun m => Real.log (Real.pi * fresnelSZeroLambda m))
    (LF := fresnelSZeroLambda)
    hcre hcim hlink hLamQ hLampos hLam100 hMu hLFpos (fun m _ => rfl)
    z hzero hquad hmono hall hcount
  have hReEq : ∀ m : ℕ, 1 ≤ m →
      fresnelSZeroLambda m
        + ((Real.log (Real.pi * fresnelSZeroLambda m)) ^ 2
            - 2 * Real.log (Real.pi * fresnelSZeroLambda m))
          / (2 * Real.pi ^ 2 * (fresnelSZeroLambda m) ^ 3)
        = fresnelSZeroReApprox m := by
    intro m hm
    have hL := hLFpos m hm
    have hL0 : fresnelSZeroLambda m ≠ 0 := ne_of_gt hL
    have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    simp only [fresnelSZeroReApprox, fresnelSZeroAlpha]
    field_simp
    ring
  have hImEq : ∀ m : ℕ, 1 ≤ m →
      Real.log (Real.pi * fresnelSZeroLambda m) / (Real.pi * fresnelSZeroLambda m)
        = fresnelSZeroImApprox m := by
    intro m hm
    have hL := hLFpos m hm
    have hL0 : fresnelSZeroLambda m ≠ 0 := ne_of_gt hL
    have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    simp only [fresnelSZeroImApprox, fresnelSZeroAlpha]
    field_simp
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with m h1 h2
  rw [← hReEq m h2, ← hImEq m h2]
  exact h1

-- no-dlmf: weaker `S`-only partial of display 7.13.5 — both errors are stated only to
-- `o(λ⁻¹)`, whereas 7.13.5 displays the `λ⁻³` correction term for the real part, and the
-- display covers `C` as well. The carrier at the full true strength is `erf_7_13_5_full`
-- below (real part `O(λ⁻³)`; see its docstring for why `o(λ⁻³)` is false).
/-- `S`-only, `o(λ⁻¹)`-strength form of the asymptotic expansion of the complex
zeros `zₙ = xₙ + i yₙ` of the Fresnel integral `S` (with 7.13.7 parameters). For the
complete enumeration `z`, ordered by increasing absolute value (DLMF §7.13(iii)), of the
*sub-diagonal* first-quadrant zeros of `cfresnelS` (`hall`), the real and imaginary parts
of `z n` agree with the `n`-th approximations `fresnelSZeroReApprox`,
`fresnelSZeroImApprox` up to `o(λ⁻¹)`.

The enumeration is restricted to `0 < im < re`, one representative per mirror pair: by
`cfresnelS_zero_mirror` the map `w ↦ i·conj w` is a zero-preserving involution of the open
first quadrant swapping real and imaginary parts, so each family zero is paired with a
mirror zero of exactly equal absolute value and no strictly-modulus-increasing complete
enumeration of the whole quadrant exists. The enumeration matches DLMF's 1-based
numbering directly: only `z n` for `1 ≤ n` is constrained (`z 0` is unconstrained junk). -/
theorem erf_7_13_5_S (z : ℕ → ℂ) (hzero : ∀ n, 1 ≤ n → cfresnelS (z n) = 0)
    (hquad : ∀ n, 1 ≤ n → 0 < (z n).im ∧ (z n).im < (z n).re)
    (hmono : StrictMonoOn (fun n => ‖z n‖) {n | 1 ≤ n})
    (hall : ∀ w : ℂ, cfresnelS w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ z n = w) :
    (fun n => (z n).re - fresnelSZeroReApprox n) =o[atTop]
        (fun n => (fresnelSZeroLambda n) ^ (-1 : ℤ)) ∧
      (fun n => (z n).im - fresnelSZeroImApprox n) =o[atTop]
        (fun n => (fresnelSZeroLambda n) ^ (-1 : ℤ)) := by
  have hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < fresnelSZeroLambda m :=
    fun m hm => fresnelSZeroLambda_pos hm
  have hLFge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ (fresnelSZeroLambda m) ^ 2 := by
    intro m hm
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [fresnelSZeroLambda_sq m]; linarith
  have hev := fresnelS713_eventual z hzero hquad hmono hall
  exact ⟨fresnel713_littleO hLFpos hLFge (hev.mono fun m h => h.1),
    fresnel713_littleO hLFpos hLFge (hev.mono fun m h => h.2)⟩

/-! ## Fresnel `C`/`S` zeros — DLMF 7.13.5 at full stated strength -/

/-- **DLMF 7.13.5** — asymptotic expansion, as `n → ∞`, of the complex zeros of
BOTH Fresnel integrals from the single displayed equation 7.13.5. For the
complete enumeration `zC`, ordered by increasing absolute value (DLMF §7.13(iii)),
of the sub-diagonal first-quadrant zeros of `cfresnelC` (`λ, α` per 7.13.6)
and, independently, the like-ordered complete enumeration `zS` of the sub-diagonal
first-quadrant zeros of `cfresnelS` (`λ, α` per 7.13.7), the real parts of
`zC n` and of `zS n` agree with `λ + α(απ−4)/(8πλ³)` to within `O(λ⁻³)`, and the
imaginary parts with `α/(2λ)` up to `o(λ⁻¹)`, the parameters being taken at the
same 1-based index `n`. This records DLMF §7.13(iii)'s cross-reference extending (7.13.5) —
stated in the text for `C` — verbatim to `S` with the 7.13.7 parameters.

**Mirror-pair restriction.** `cfresnelC_zero_mirror` / `cfresnelS_zero_mirror`:
`w ↦ i·conj w` is a zero-preserving involution of the open first quadrant that
swaps real and imaginary parts, so the quadrant contains, besides DLMF's family
(`xₙ → ∞`, `yₙ → 0`), its mirror image, with real and imaginary parts swapped and
hence *exactly equal* absolute value. DLMF's "arranged in order of increasing
absolute value", read over the whole quadrant, is therefore unsatisfiable, and the
enumerations are restricted to the sub-diagonal representative `0 < im < re` of
each mirror pair — precisely DLMF's family, within which the modulus ordering is
strict.

**Index origin.** DLMF numbers the zeros from `n = 1` and the enumerations match
that 1-based labelling directly: only indices `1 ≤ n` are constrained (`zC 0`,
`zS 0` are unconstrained junk), and the parameters are evaluated at the same `n`.

**Order of the real parts.** DLMF's displayed `λ⁻³` coefficient is incomplete: the
true expansion is `xₙ = λ + (α²/8 − α/(2π) + 1/π²)·λ⁻³ + ⋯`, while the display gives
`α(απ − 4)/(8πλ³) = (α²/8 − α/(2π))·λ⁻³`. The residual is therefore `λ⁻³/π² + o(λ⁻³)`
— numerically `(xₙ − fresnelCZeroReApprox n)·λ³ → 0.10128…` and likewise for `S`,
against `1/π² = 0.101321…` — so the real-part error is `Θ(λ⁻³)` and `o(λ⁻³)` is
false; the sharp true statement at DLMF's approximant is the `O(λ⁻³)` bound below.

DAG: E-7.13.5.
Numerical: N/A (unparsed:expected ) got ∧)
Verified: unverified
-/
theorem erf_7_13_5_full
    (zC : ℕ → ℂ) (hzeroC : ∀ n, 1 ≤ n → cfresnelC (zC n) = 0)
    (hquadC : ∀ n, 1 ≤ n → 0 < (zC n).im ∧ (zC n).im < (zC n).re)
    (hmonoC : StrictMonoOn (fun n => ‖zC n‖) {n | 1 ≤ n})
    (hallC : ∀ w : ℂ, cfresnelC w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ zC n = w)
    (zS : ℕ → ℂ) (hzeroS : ∀ n, 1 ≤ n → cfresnelS (zS n) = 0)
    (hquadS : ∀ n, 1 ≤ n → 0 < (zS n).im ∧ (zS n).im < (zS n).re)
    (hmonoS : StrictMonoOn (fun n => ‖zS n‖) {n | 1 ≤ n})
    (hallS : ∀ w : ℂ, cfresnelS w = 0 → 0 < w.im → w.im < w.re → ∃ n, 1 ≤ n ∧ zS n = w) :
    ((fun n => (zC n).re - fresnelCZeroReApprox n) =O[atTop]
        (fun n => (fresnelCZeroLambda n) ^ (-3 : ℤ)) ∧
      (fun n => (zC n).im - fresnelCZeroImApprox n) =o[atTop]
        (fun n => (fresnelCZeroLambda n) ^ (-1 : ℤ))) ∧
    ((fun n => (zS n).re - fresnelSZeroReApprox n) =O[atTop]
        (fun n => (fresnelSZeroLambda n) ^ (-3 : ℤ)) ∧
      (fun n => (zS n).im - fresnelSZeroImApprox n) =o[atTop]
        (fun n => (fresnelSZeroLambda n) ^ (-1 : ℤ))) := by
  refine ⟨erf_7_13_5 zC hzeroC hquadC hmonoC hallC, ?_⟩
  have hLFpos : ∀ m : ℕ, 1 ≤ m → 0 < fresnelSZeroLambda m :=
    fun m hm => fresnelSZeroLambda_pos hm
  have hLFge : ∀ m : ℕ, 1 ≤ m → (m:ℝ) ≤ (fresnelSZeroLambda m) ^ 2 := by
    intro m hm
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [fresnelSZeroLambda_sq m]; linarith
  have hev := fresnelS713_eventual zS hzeroS hquadS hmonoS hallS
  exact ⟨fresnel713_bigO hLFpos (hev.mono fun m h => h.1),
    fresnel713_littleO hLFpos hLFge (hev.mono fun m h => h.2)⟩

end FLMF.Fresnel
