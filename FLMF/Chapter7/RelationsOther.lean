import FLMF.Chapter7.Erf
import FLMF.Chapter7.FresnelBasic
import FLMF.Support.IncompleteGammaDef
import FLMF.Support.IncompleteGammaComplexDef
import FLMF.Support.HypergeometricKummer
import FLMF.Support.HypergeometricKummerODE
import FLMF.Support.HypergeometricTricomi
import FLMF.Support.HypergeometricGauss
import FLMF.Support.HypergeometricPFQ
import FLMF.Chapter7.KummerBridge
import FLMF.Support.IncompleteGammaKummerBridge
import FLMF.Chapter7.TricomiBridge
import FLMF.Support.IncompleteGammaTricomiBridge
import FLMF.Chapter7.FresnelKummerBridge
import FLMF.Chapter7.FresnelComplex
import FLMF.Chapter7.Series

/-!
# DLMF §7.11 — Relations to other functions (statement surfaces)

Faithful TRUE statement surfaces (Phase 5) for DLMF §7.11, relating the error
functions `erf`/`erfc` and the Fresnel integrals `C`/`S` to the incomplete gamma
function, the confluent hypergeometric functions (Kummer `M`, Tricomi `U`), and
the Gauss hypergeometric function `₂F₁`.

Work-list: 7.11.1, 7.11.2, 7.11.3, 7.11.5, 7.11.6, 7.11.7, 7.11.8.
(7.11.4 is covered in Error/KummerBridge.lean.)

**7.11.1 / 7.11.2 / 7.11.3** are surfaced at complex-variable strength on the
principal branch (`cerf_7_11_1`, `cerfc_7_11_2`, `cerf_7_11_3`), using the
complex incomplete-gamma module `FLMF.Functions.IncompleteGamma.ComplexDef`
(`clowerGamma`, `cupperGamma`, `cexpIntegralE`); the real-`z` forms below are
demoted to `-- no-dlmf` restrictions.  Each complex surface carries the sector
hypothesis `0 < z.re`: all three displays feed `z²` into a function carrying a
`w^{±1/2}` factor, and principal `(z²)^{1/2} = z` holds exactly on the right
half-plane, so `Re z > 0` is the maximal true principal-branch domain (DLMF
states them unrestricted because its `γ`, `Γ`, `E_p` are the continued,
multivalued objects — the displays are branch-implicit).  See the `ComplexDef`
module docstring for the full branch note.

**7.11.5** is complexified elsewhere: the complex `U` (`tricomiUC`, the
13.2.42 connection formula) lives in `Frameworks/Hypergeometric/
TricomiComplex.lean`, and the canonical 7.11.5 carrier is `cerf_7_11_5`
(`Error/ComplexTricomi.lean`); the real-domain form `erf_7_11_5` below is
demoted to a `-- no-dlmf` restriction.

The Fresnel integrals DO have a complex extension (`FLMF.Fresnel.Complex`,
`cfresnelC`/`cfresnelS`), and `kummerM`/`pFq` are already generic over any
normed algebra, so 7.11.6/7.11.7/7.11.8 are surfaced at DLMF's full complex-`z`
strength (`erf_7_11_6`/`erf_7_11_7_complex`/`erf_7_11_8_complex`,
proven via the analytic-continuation identity theorem from the real-`x`
results below, which are demoted to `-- no-dlmf` real-domain lemmas).
-/

namespace FLMF.Error

open Real
open FLMF.IncompleteGamma
open FLMF.Hypergeometric
open scoped FLMF.Hypergeometric
open FLMF.Fresnel
open scoped Topology
open Filter

-- no-dlmf: real/narrowed restriction of DLMF 7.11.1 (DLMF's `z` is a complex
-- variable); faithful surface is `FLMF.Error.cerf_7_11_1`
/-- `erf z = (1/√π)·γ(½, z²)`: the error function as a lower incomplete gamma
value, real form (`z ≥ 0`, so `z² ≥ 0` lies in the domain of the real lower
incomplete gamma integral).  Real trace of `cerf_7_11_1`.
-/
theorem erf_7_11_1 {z : ℝ} (hz : 0 ≤ z) :
    FLMF.Error.erf z = (1 / Real.sqrt Real.pi) * lowerGamma (1 / 2) (z ^ 2) := by
  have hg' := lowerGamma_eq_kummerM (a := (1/2:ℝ)) (by norm_num) (x := z^2) (by positivity)
  have hg := hg'.1.trans hg'.2
  have hpow : (z^2 : ℝ) ^ (1/2 : ℝ) = z := by
    rw [show (z^2:ℝ) = z*z by ring, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self hz]
  rw [hg, hpow, erf_eq_kummerM z]; ring

-- no-dlmf: real/narrowed restriction of DLMF 7.11.2 (DLMF's `z` is a complex
-- variable); faithful surface is `FLMF.Error.cerfc_7_11_2`
/-- `erfc z = (1/√π)·Γ(½, z²)`: the complementary error function as an upper
incomplete gamma value, real form (`z ≥ 0`, so `z² ≥ 0` lies in the domain of
the real upper incomplete gamma integral). Complement of `erf_7_11_1` via
`γ(½,x) + Γ(½,x) = Γ(½) = √π`.  Real trace of `cerfc_7_11_2`.
-/
theorem erf_7_11_2 {z : ℝ} (hz : 0 ≤ z) :
    FLMF.Error.erfc z = (1 / Real.sqrt Real.pi) * upperGamma (1 / 2) (z ^ 2) := by
  have hsum := lowerGamma_add_upperGamma (a := (1 / 2 : ℝ)) (by norm_num)
    (x := z ^ 2) (by positivity)
  rw [Real.Gamma_one_half_eq] at hsum
  have h1 := erf_7_11_1 hz
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hc : FLMF.Error.erfc z = 1 - FLMF.Error.erf z := rfl
  rw [hc, h1]
  field_simp
  linarith [hsum]

-- no-dlmf: `√π ≠ 0` cast helper for the complex 7.11.x surfaces, no DLMF counterpart
private theorem csqrt_pi_ne_zero : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- **DLMF 7.11.1**, at complex-variable strength on the principal branch:
`erf z = (1/√π)·γ(½, z²)` for every `z` with `Re z > 0`.

**Branch note (why `0 < z.re` is DLMF-honest, not a narrowing).** `γ(a, w)` carries
a `w^a` factor, so it is multivalued in `w`; DLMF states 7.11.1 without a
constraint because its `γ` is the analytically continued (multivalued) object,
i.e. the display is *branch-implicit*.  FLMF's `clowerGamma` fixes the **principal**
branch (`w ^ a = exp (a · Log w)`, `arg ∈ (-π, π]`), and with that fixed choice the
identity holds exactly where principal `(z²)^{1/2} = z`, namely on the right
half-plane `Re z > 0`; off it the principal-branch statement is false (at `z = -1`,
`γ(½, 1) = √π · erf 1 ≠ √π · erf(-1)`).  So `0 < z.re` is the maximal true
principal-branch domain of DLMF 7.11.1, and the real-variable form `erf_7_11_1`
(`z ≥ 0`) is its trace on the positive axis.

DLMF 7.11.1.
DAG: E-7.11.1.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_11_1 {z : ℂ} (hz : 0 < z.re) :
    cerf z = (1 / (Real.sqrt Real.pi : ℂ)) * clowerGamma (1 / 2) (z ^ 2) := by
  have hint : (∫ t in (0:ℝ)..1, Complex.exp (-(t : ℂ) ^ 2 * z ^ 2))
      = ∫ t in (0:ℝ)..1, Complex.exp (-((t : ℂ) * z) ^ 2) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    congr 1
    ring
  rw [clowerGamma, cpow_half_sq hz, segment_integral_half (z ^ 2), hint, cerf]
  field_simp

/-- **DLMF 7.11.2**, at complex-variable strength on the principal branch:
`erfc z = (1/√π)·Γ(½, z²)` for every `z` with `Re z > 0`.

**Branch note.** Identical to `cerf_7_11_1`: `Γ(a,w) = Γ(a) − γ(a,w)` inherits the
`w^a` branch cut of `γ`, DLMF's display is branch-implicit, and the principal-branch
identity is true exactly on `Re z > 0`.  `erf_7_11_2` (`z ≥ 0`) is its real trace.

DLMF 7.11.2.
DAG: E-7.11.2.
Numerical: N/A
Verified: verified
-/
theorem cerfc_7_11_2 {z : ℂ} (hz : 0 < z.re) :
    cerfc z = (1 / (Real.sqrt Real.pi : ℂ)) * cupperGamma (1 / 2) (z ^ 2) := by
  have h1 := cerf_7_11_1 hz
  have hpi := csqrt_pi_ne_zero
  rw [cupperGamma, cGamma_one_half, cerfc, h1]
  field_simp

/-- Generalized exponential integral `E_p(x) = x^{p-1} Γ(1-p, x)` (DLMF 8.19.1). -/
-- DAG: E-8.19.1.
-- Verified: unverified
noncomputable def expIntegralE (p x : ℝ) : ℝ :=
  x ^ (p - 1) * FLMF.IncompleteGamma.upperGamma (1 - p) x

-- no-dlmf: real/narrowed restriction of DLMF 7.11.3 (DLMF's `z` is a complex
-- variable); faithful surface is `FLMF.Error.cerf_7_11_3`
/-- `erfc z = (z/√π)·E_{1/2}(z²)`: the complementary error function as a value of the
generalized exponential integral `E_p` at half-integer order `p = 1/2`, real form
(`z > 0`).  Real trace of `cerf_7_11_3`.
-/
theorem erf_7_11_3 {z : ℝ} (hz : 0 < z) :
    FLMF.Error.erfc z = (z / Real.sqrt π) * expIntegralE (1 / 2) (z ^ 2) := by
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  have hu' := upperGamma_eq_tricomiU (a := (1/2:ℝ)) (by norm_num) hz2
  have hu := hu'.1.trans hu'.2
  have hc := erfc_eq_tricomiU hz
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h2 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  have hpow : ((z:ℝ) ^ 2) ^ ((1:ℝ)/2 - 1) * (z ^ 2) ^ ((1:ℝ)/2) = 1 := by
    rw [← Real.rpow_add hz2]; norm_num
  have hcollapse : (z^2 : ℝ) ^ ((1:ℝ)/2 - 1) * upperGamma (1 - 1/2 : ℝ) (z^2)
      = Real.exp (-(z^2)) * tricomiU 1 (3/2 : ℝ) (z^2) := by
    rw [h1, hu, h2]
    calc (z^2:ℝ)^((1:ℝ)/2 - 1) * (Real.exp (-(z^2)) * (z^2)^((1:ℝ)/2) * tricomiU 1 (3/2:ℝ) (z^2))
        = ((z^2:ℝ)^((1:ℝ)/2 - 1) * (z^2)^((1:ℝ)/2)) * (Real.exp (-(z^2)) * tricomiU 1 (3/2:ℝ) (z^2)) := by
          ring
      _ = 1 * (Real.exp (-(z^2)) * tricomiU 1 (3/2:ℝ) (z^2)) := by rw [hpow]
      _ = Real.exp (-(z^2)) * tricomiU 1 (3/2:ℝ) (z^2) := by ring
  unfold expIntegralE
  rw [hcollapse, hc]
  ring

/-- **DLMF 7.11.3**, at complex-variable strength on the principal branch:
`erfc z = (z/√π)·E_{1/2}(z²)` for every `z` with `Re z > 0`, with the complex
generalized exponential integral `cexpIntegralE p w = w^{p-1} Γ(1-p, w)`
(DLMF 8.19.1).

**Branch note.** `E_{1/2}(z²) = (z²)^{-1/2} Γ(½, z²)`, and principal
`(z²)^{-1/2} = z⁻¹` exactly on `Re z > 0` (`cpow_neg_half_sq`); as in 7.11.1/7.11.2
DLMF's display is branch-implicit (its `E_p` is the continued object), so the right
half-plane is the maximal true principal-branch domain, not a narrowing.
`erf_7_11_3` (`z > 0`) is its real trace.  Unlike that real form, this proof does
not route through `upperGamma_eq_tricomiU` (whose first conjunct is an open `sorry`
in `IncompleteGamma/TricomiBridge.lean`): it goes through `cerfc_7_11_2` only.

DLMF 7.11.3.
DAG: E-7.11.3.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_11_3 {z : ℂ} (hz : 0 < z.re) :
    cerfc z = (z / (Real.sqrt Real.pi : ℂ)) * cexpIntegralE (1 / 2) (z ^ 2) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hpi := csqrt_pi_ne_zero
  have hu : cupperGamma (1 / 2 : ℂ) (z ^ 2) = (Real.sqrt Real.pi : ℂ) * cerfc z := by
    rw [cerfc_7_11_2 hz]
    field_simp
  have hpow : ((z ^ 2 : ℂ)) ^ ((1 / 2 : ℂ) - 1) = z⁻¹ := by
    rw [show ((1 / 2 : ℂ) - 1) = (-(1 / 2) : ℂ) by norm_num]
    exact cpow_neg_half_sq hz
  rw [cexpIntegralE, hpow, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hu]
  field_simp

-- no-dlmf: real-axis restriction of DLMF 7.11.5 over the real `tricomiU`
-- integral rep; the canonical carrier is the complex `cerf_7_11_5`
-- (Error/ComplexTricomi.lean, over `tricomiUC`)
/-- `erfc` as a Tricomi `U` value at two parameter pairs (7.11.5, real form),
`erfc z = (1/√π)·e^{-z²}·U(1/2, 1/2, z²) = (z/√π)·e^{-z²}·U(1, 3/2, z²)`.
Stated for `z > 0` so that `z² > 0` is in the domain of FLMF's real
`tricomiU` integral representation. The faithful complex surface is
`cerf_7_11_5` (Error/ComplexTricomi.lean). -/
theorem erf_7_11_5 {z : ℝ} (hz : 0 < z) :
    FLMF.Error.erfc z =
      (1 / Real.sqrt Real.pi) * Real.exp (-z ^ 2) * tricomiU (1 / 2) (1 / 2) (z ^ 2) ∧
    FLMF.Error.erfc z =
      (z / Real.sqrt Real.pi) * Real.exp (-z ^ 2) * tricomiU 1 (3 / 2) (z ^ 2) :=
  ⟨erfc_eq_tricomiU_half hz, erfc_eq_tricomiU hz⟩

-- no-dlmf: real-argument restriction of DLMF 7.11.6 (DLMF's `z` is an
-- unconstrained complex variable); feeds `cfresnel_kummer_eq_of_real` below,
-- which in turn feeds the faithful complex surface `erf_7_11_6`
/-- `C(x) + i·S(x) = x·M(½, 3/2, ½πi x²)`: the Fresnel integrals as a Kummer
confluent hypergeometric value (DLMF 7.11.6), real-argument specialization. The
identity is intrinsically complex — the LHS is the complex combination
`C(x) + i S(x)` and the Kummer `M` (FLMF's complex `kummerM`, DLMF 13.2.2) is
evaluated at the purely imaginary argument `½πi x²` — so the real Fresnel
integrals `fresnelC`/`fresnelS` are cast up to ℂ.
-/
theorem fresnel_kummerM_real (x : ℝ) :
    (FLMF.Fresnel.fresnelC x : ℂ) + Complex.I * (FLMF.Fresnel.fresnelS x : ℂ) =
      (x : ℂ) * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
        ((Real.pi : ℂ) * Complex.I * (x : ℂ) ^ 2 / 2) := by
  rw [show ((Real.pi:ℂ)*Complex.I*(x:ℂ)^2/2) = Complex.I*(Real.pi:ℂ)*(x:ℂ)^2/2 by ring]
  exact FLMF.Fresnel.fresnel_eq_kummerM x

-- no-dlmf: real-cast bridge feeding `erf_7_11_6`, no DLMF counterpart
/-- `fresnel_kummerM_real` rephrased with the entire complex extensions `cfresnelC`/
`cfresnelS` at a real-embedded argument. -/
private theorem cfresnel_kummer_eq_of_real (x : ℝ) :
    cfresnelC (x : ℂ) + Complex.I * cfresnelS (x : ℂ)
      = (x : ℂ) * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
          (Complex.I * Real.pi * (x : ℂ) ^ 2 / 2) := by
  rw [cfresnelC_ofReal, cfresnelS_ofReal,
    show (Complex.I * Real.pi * (x:ℂ)^2/2) = ((Real.pi:ℂ)*Complex.I*(x:ℂ)^2/2) by ring]
  exact_mod_cast fresnel_kummerM_real x

-- no-dlmf: chain link 7.11.6 (assembled in `erf_7_11_6` below, alongside a
-- Kummer-transformation link); the complex-variable-strength first form,
-- `C(z) + i·S(z) = z·M(½, 3/2, ½πi z²)`. Proved from the real-argument case
-- (`fresnel_kummerM_real`) by the identity theorem for analytic functions:
-- both sides are entire (LHS via `hasDerivAt_cfresnelC_add_I_mul_cfresnelS`,
-- RHS via the unconditional `kummerM_hasDerivAt_dlmf`) and agree on the
-- reals, hence agree everywhere
/-- The Fresnel integrals as a Kummer confluent hypergeometric value,
`C(z) + i·S(z) = z·M(½, 3/2, ½πi z²)`, for every `z ∈ ℂ`. -/
theorem cfresnel_eq_kummerM_complex (z : ℂ) :
    cfresnelC z + Complex.I * cfresnelS z =
      z * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
        (Complex.I * Real.pi * z ^ 2 / 2) := by
  have hlhs_diff : Differentiable ℂ (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w) :=
    fun w => (hasDerivAt_cfresnelC_add_I_mul_cfresnelS w).differentiableAt
  have hM_diff : Differentiable ℂ (FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)) :=
    fun w => (FLMF.Hypergeometric.kummerM_hasDerivAt_dlmf (1 / 2 : ℂ) (3 / 2 : ℂ) w).differentiableAt
  have harg_diff : Differentiable ℂ (fun w : ℂ => Complex.I * Real.pi * w ^ 2 / 2) := by
    fun_prop
  have hrhs_diff : Differentiable ℂ
      (fun w : ℂ => w * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
        (Complex.I * Real.pi * w ^ 2 / 2)) :=
    differentiable_id.mul (hM_diff.comp harg_diff)
  have hfAnalytic : AnalyticOnNhd ℂ (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w)
      Set.univ := fun w _ => hlhs_diff.analyticAt w
  have hgAnalytic : AnalyticOnNhd ℂ
      (fun w : ℂ => w * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
        (Complex.I * Real.pi * w ^ 2 / 2))
      Set.univ := fun w _ => hrhs_diff.analyticAt w
  have htendsto : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall (fun n => div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)))
  have hp : ∀ n : ℕ, (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w) ((1 : ℂ) / ((n : ℂ) + 1))
      = (fun w : ℂ => w * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
          (Complex.I * Real.pi * w ^ 2 / 2)) ((1 : ℂ) / ((n : ℂ) + 1)) := by
    intro n
    have hcast : (1 : ℂ) / ((n : ℂ) + 1) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast; ring
    simp only
    rw [hcast]
    exact cfresnel_kummer_eq_of_real (1 / ((n : ℝ) + 1))
  have hkey : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w) w
      = (fun w : ℂ => w * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
          (Complex.I * Real.pi * w ^ 2 / 2)) w :=
    htendsto.frequently (Eventually.frequently (Eventually.of_forall hp))
  have heq := AnalyticOnNhd.eq_of_frequently_eq hfAnalytic hgAnalytic hkey
  exact congrFun heq z

-- no-dlmf: chain link 7.11.6 (assembled in `erf_7_11_6` below, alongside
-- `cfresnel_eq_kummerM_complex`); the Kummer-transformation form, obtained from
-- `cfresnel_eq_kummerM_complex` via Kummer's transformation `M(a,b,w) = eʷ·M(b-a,b,-w)`
-- (`kummerM_kummer_transform`, DLMF 13.2.39) with `a = 1/2`, `b = 3/2`
private theorem cfresnel_eq_kummerM_transform (z : ℂ) :
    cfresnelC z + Complex.I * cfresnelS z =
      z * Complex.exp (Complex.I * Real.pi * z ^ 2 / 2) *
        FLMF.Hypergeometric.kummerM (1 : ℂ) (3 / 2 : ℂ) (-(Complex.I * Real.pi * z ^ 2 / 2)) := by
  have hb : ∀ k : ℕ, (k : ℂ) ≠ -(3 / 2 : ℂ) := by
    intro k h
    have h2 : (k : ℂ) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) := by rw [h]; norm_num
    have h3 : (k : ℝ) = -(3 / 2 : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have ht := FLMF.Hypergeometric.kummerM_kummer_transform (𝕂 := ℂ) (a := (1 / 2 : ℂ))
    (b := (3 / 2 : ℂ)) hb (Complex.I * Real.pi * z ^ 2 / 2)
  rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by ring, ← Complex.exp_eq_exp_ℂ] at ht
  rw [cfresnel_eq_kummerM_complex z, ht]
  ring

/-- **DLMF 7.11.6**, at DLMF's full complex-variable strength: the Fresnel
integrals as Kummer confluent hypergeometric values in two equivalent forms,
`C(z) + i·S(z) = z·M(½, 3/2, ½πi z²) = z·e^{πiz²/2}·M(1, 3/2, −½πi z²)`, for
every `z ∈ ℂ`.

DLMF 7.11.6.
DAG: E-7.11.6.
Numerical: PASS
Verified: verified
-/
theorem erf_7_11_6 (z : ℂ) :
    cfresnelC z + Complex.I * cfresnelS z =
      z * FLMF.Hypergeometric.kummerM (1 / 2 : ℂ) (3 / 2 : ℂ)
        (Complex.I * Real.pi * z ^ 2 / 2) ∧
    cfresnelC z + Complex.I * cfresnelS z =
      z * Complex.exp (Complex.I * Real.pi * z ^ 2 / 2) *
        FLMF.Hypergeometric.kummerM (1 : ℂ) (3 / 2 : ℂ) (-(Complex.I * Real.pi * z ^ 2 / 2)) :=
  ⟨cfresnel_eq_kummerM_complex z, cfresnel_eq_kummerM_transform z⟩

-- no-dlmf: Pochhammer telescoping helper `(5/4)_k = (1/4)_k (4k+1)` for 7.11.7, no DLMF counterpart
private lemma erf7117_poch54 (k : ℕ) :
    (ascPochhammer ℝ k).eval (5/4 : ℝ) = (ascPochhammer ℝ k).eval (1/4 : ℝ) * (4 * k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
    push_cast
    ring

-- no-dlmf: Pochhammer duplication helper `(1/2)_k 4^k k! = (2k)!` for 7.11.7, no DLMF counterpart
private lemma erf7117_poch12 (k : ℕ) :
    ((2 * k).factorial : ℝ) = (ascPochhammer ℝ k).eval (1/2 : ℝ) * (4 ^ k * k.factorial) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hfac : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * ((2 * n + 1) * ((2 * n).factorial : ℝ)) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, ih, ascPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
    push_cast
    ring

-- no-dlmf: Pochhammer telescoping helper `3·(7/4)_k = (3/4)_k (4k+3)` for 7.11.8, no DLMF counterpart
private lemma erf7118_poch74 (k : ℕ) :
    3 * (ascPochhammer ℝ k).eval (7/4 : ℝ) = (ascPochhammer ℝ k).eval (3/4 : ℝ) * (4 * k + 3) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval,
      show (3:ℝ) * ((ascPochhammer ℝ n).eval (7/4:ℝ) * (7/4 + n)) =
        3 * (ascPochhammer ℝ n).eval (7/4:ℝ) * (7/4 + n) by ring, ih]
    push_cast
    ring

-- no-dlmf: Pochhammer duplication helper `(3/2)_k 4^k k! = (2k+1)!` for 7.11.8, no DLMF counterpart
private lemma erf7118_poch32 (k : ℕ) :
    ((2 * k + 1).factorial : ℝ) = (ascPochhammer ℝ k).eval (3/2 : ℝ) * (4 ^ k * k.factorial) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hfac : ((2 * (n + 1) + 1).factorial : ℝ) = (2 * n + 3) * ((2 * n + 2) * ((2 * n + 1).factorial : ℝ)) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, ih, ascPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
    push_cast
    ring

-- no-dlmf: real-argument restriction of DLMF 7.11.7 (DLMF's `z` is an
-- unconstrained complex variable); faithful surface is `erf_7_11_7_complex`
/-- `C(z) = z·₁F₂(¼; 5/4, ½; −π²z⁴/16)`: the Fresnel cosine integral as a
generalized hypergeometric value (DLMF 7.11.7), real form, via `FLMF.Hypergeometric.pFq`
with one upper and two lower parameters.  (Corrected 2026-06-25 from the DLMF PDF —
this is `₁F₂`, NOT the Gauss `₂F₁`; verified C(0.8) = 0.72284417 = RHS.  See ERRATA.)
-/
theorem erf_7_11_7 (z : ℝ) :
    FLMF.Fresnel.fresnelC z =
      z * FLMF.Hypergeometric.pFq (![(1 / 4 : ℝ)]) (![(5 / 4 : ℝ), (1 / 2 : ℝ)])
        (-(Real.pi ^ 2) * z ^ 4 / 16) := by
  have hp := pFq_hasSum (![(1 / 4 : ℝ)]) (![(5 / 4 : ℝ), (1 / 2 : ℝ)])
    (by norm_num) (-(Real.pi ^ 2) * z ^ 4 / 16)
  have hM := hp.mul_left z
  have hterm : (fun k : ℕ => z *
      (pFqCoefficient (![(1 / 4 : ℝ)]) (![(5 / 4 : ℝ), (1 / 2 : ℝ)]) k *
        (-(Real.pi ^ 2) * z ^ 4 / 16) ^ k)) =
      fun k : ℕ => (-1 : ℝ) ^ k * (Real.pi / 2) ^ (2 * k) /
        ((2 * k).factorial * (4 * k + 1)) * z ^ (4 * k + 1) := by
    funext k
    have hP14 : (0:ℝ) < (ascPochhammer ℝ k).eval (1/4 : ℝ) := ascPochhammer_pos k _ (by norm_num)
    have h54 := erf7117_poch54 k
    have h12 := erf7117_poch12 k
    have hfk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hf2k : ((2 * k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (2 * k).factorial_ne_zero
    have h4k1 : ((4:ℝ) * k + 1) ≠ 0 := by positivity
    have h4pk : ((4:ℝ)) ^ k ≠ 0 := by positivity
    have hP14' : (ascPochhammer ℝ k).eval (1/4 : ℝ) ≠ 0 := ne_of_gt hP14
    have hxpow : (-(Real.pi ^ 2) * z ^ 4 / 16 : ℝ) ^ k =
        (-1 : ℝ) ^ k * Real.pi ^ (2 * k) * z ^ (4 * k) / (4 ^ k * 4 ^ k) := by
      rw [show (-(Real.pi ^ 2) * z ^ 4 / 16 : ℝ) = (-1) * (Real.pi ^ 2 * z ^ 4 / 16) by ring,
        mul_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul, show ((16:ℝ)) ^ k = 4 ^ k * 4 ^ k by
          rw [← mul_pow]; norm_num]
      ring
    have hhalf : ((Real.pi : ℝ) / 2) ^ (2 * k) = Real.pi ^ (2 * k) / 4 ^ k := by
      rw [div_pow, show ((2:ℝ)) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
    simp only [pFqCoefficient, Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hxpow, hhalf, h54, h12]
    field_simp
    ring
  rw [hterm] at hM
  rw [erf_7_6_4 z]
  exact hM.tsum_eq

-- no-dlmf: real-argument restriction of DLMF 7.11.8 (DLMF's `z` is an
-- unconstrained complex variable); faithful surface is `erf_7_11_8_complex`
/-- `S(z) = (π/6)·z³·₁F₂(¾; 7/4, 3/2; −π²z⁴/16)`: the Fresnel sine integral as a
generalized hypergeometric value (DLMF 7.11.8), real form, via `FLMF.Hypergeometric.pFq`.
(Corrected 2026-06-25 from the DLMF PDF — `₁F₂`, NOT the Gauss `₂F₁`; verified
S(0.8) = 0.24934139 = RHS.  See ERRATA.)
-/
theorem erf_7_11_8 (z : ℝ) :
    FLMF.Fresnel.fresnelS z =
      (Real.pi / 6) * z ^ 3 * FLMF.Hypergeometric.pFq (![(3 / 4 : ℝ)]) (![(7 / 4 : ℝ), (3 / 2 : ℝ)])
        (-(Real.pi ^ 2) * z ^ 4 / 16) := by
  have hp := pFq_hasSum (![(3 / 4 : ℝ)]) (![(7 / 4 : ℝ), (3 / 2 : ℝ)])
    (by norm_num) (-(Real.pi ^ 2) * z ^ 4 / 16)
  have hM := hp.mul_left ((Real.pi / 6) * z ^ 3)
  have hterm : (fun k : ℕ => (Real.pi / 6) * z ^ 3 *
      (pFqCoefficient (![(3 / 4 : ℝ)]) (![(7 / 4 : ℝ), (3 / 2 : ℝ)]) k *
        (-(Real.pi ^ 2) * z ^ 4 / 16) ^ k)) =
      fun k : ℕ => (-1 : ℝ) ^ k * (Real.pi / 2) ^ (2 * k + 1) /
        ((2 * k + 1).factorial * (4 * k + 3)) * z ^ (4 * k + 3) := by
    funext k
    have hP34 : (0:ℝ) < (ascPochhammer ℝ k).eval (3/4 : ℝ) := ascPochhammer_pos k _ (by norm_num)
    have h74 := erf7118_poch74 k
    have h32 := erf7118_poch32 k
    have hP74 : (0:ℝ) < (ascPochhammer ℝ k).eval (7/4 : ℝ) := ascPochhammer_pos k _ (by norm_num)
    have hfk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hf2k1 : ((2 * k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (2 * k + 1).factorial_ne_zero
    have h4k3 : ((4:ℝ) * k + 3) ≠ 0 := by positivity
    have h4pk : ((4:ℝ)) ^ k ≠ 0 := by positivity
    have hP34' : (ascPochhammer ℝ k).eval (3/4 : ℝ) ≠ 0 := ne_of_gt hP34
    have hP74' : (ascPochhammer ℝ k).eval (7/4 : ℝ) ≠ 0 := ne_of_gt hP74
    have hxpow : (-(Real.pi ^ 2) * z ^ 4 / 16 : ℝ) ^ k =
        (-1 : ℝ) ^ k * Real.pi ^ (2 * k) * z ^ (4 * k) / (4 ^ k * 4 ^ k) := by
      rw [show (-(Real.pi ^ 2) * z ^ 4 / 16 : ℝ) = (-1) * (Real.pi ^ 2 * z ^ 4 / 16) by ring,
        mul_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul, show ((16:ℝ)) ^ k = 4 ^ k * 4 ^ k by
          rw [← mul_pow]; norm_num]
      ring
    have hhalf : ((Real.pi : ℝ) / 2) ^ (2 * k + 1) = Real.pi ^ (2 * k + 1) / (2 * 4 ^ k) := by
      rw [div_pow, show ((2:ℝ)) ^ (2 * k + 1) = 2 * 4 ^ k by rw [pow_succ, pow_mul]; ring_nf]
    simp only [pFqCoefficient, Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hxpow, hhalf, h32]
    have h74' : (ascPochhammer ℝ k).eval (7/4 : ℝ) = (ascPochhammer ℝ k).eval (3/4 : ℝ) * (4 * k + 3) / 3 := by
      field_simp
      linarith [h74]
    rw [h74']
    field_simp
    ring
  rw [hterm] at hM
  rw [erf_7_6_6 z]
  exact hM.tsum_eq

/-! ## Complex-`z` surfaces for DLMF 7.11.7 / 7.11.8

`cfresnelC`/`cfresnelS` (`FLMF.Fresnel.Complex`) are the entire extensions of
the real Fresnel integrals, and `pFq` (unlike `lowerGamma`/`upperGamma`/
`tricomiU`) is already generic over any normed algebra, so DLMF 7.11.7/7.11.8
can be surfaced at full complex-`z` strength via the same analytic-
continuation identity-theorem route used for `cfresnel_eq_kummerM_complex` above. -/

-- no-dlmf: standalone entirety of `cfresnelC`, no DLMF counterpart (derived from
-- the entirety of `C+iS` and `C-iS` via DLMF 7.5.8, `cfresnel_7_5_8`)
private theorem cfresnelC_differentiable : Differentiable ℂ cfresnelC := by
  have hsum : Differentiable ℂ (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w) :=
    fun w => (hasDerivAt_cfresnelC_add_I_mul_cfresnelS w).differentiableAt
  have hdiff_eq : (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w) =
      fun w : ℂ => (1/2)*(1-Complex.I) * cerf ((1/2)*(Real.sqrt Real.pi:ℂ)*(1+Complex.I)*w) :=
    funext fun w => (cfresnel_7_5_8 w).2
  have hdiff : Differentiable ℂ (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w) := by
    rw [hdiff_eq]
    have hlin : Differentiable ℂ (fun w : ℂ => (1/2)*(Real.sqrt Real.pi:ℂ)*(1+Complex.I)*w) := by
      fun_prop
    exact (differentiable_cerf.comp hlin).const_mul _
  have hC_eq : cfresnelC = fun w : ℂ =>
      ((cfresnelC w + Complex.I * cfresnelS w) + (cfresnelC w - Complex.I * cfresnelS w)) / 2 := by
    funext w; ring
  rw [hC_eq]
  exact (hsum.add hdiff).div_const 2

-- no-dlmf: standalone entirety of `cfresnelS`, no DLMF counterpart (same route
-- as `cfresnelC_differentiable`)
private theorem cfresnelS_differentiable : Differentiable ℂ cfresnelS := by
  have hsum : Differentiable ℂ (fun w : ℂ => cfresnelC w + Complex.I * cfresnelS w) :=
    fun w => (hasDerivAt_cfresnelC_add_I_mul_cfresnelS w).differentiableAt
  have hdiff_eq : (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w) =
      fun w : ℂ => (1/2)*(1-Complex.I) * cerf ((1/2)*(Real.sqrt Real.pi:ℂ)*(1+Complex.I)*w) :=
    funext fun w => (cfresnel_7_5_8 w).2
  have hdiff : Differentiable ℂ (fun w : ℂ => cfresnelC w - Complex.I * cfresnelS w) := by
    rw [hdiff_eq]
    have hlin : Differentiable ℂ (fun w : ℂ => (1/2)*(Real.sqrt Real.pi:ℂ)*(1+Complex.I)*w) := by
      fun_prop
    exact (differentiable_cerf.comp hlin).const_mul _
  have hS_eq : cfresnelS = fun w : ℂ =>
      ((cfresnelC w + Complex.I * cfresnelS w) - (cfresnelC w - Complex.I * cfresnelS w)) /
        (2 * Complex.I) := by
    funext w; field_simp; ring
  rw [hS_eq]
  exact (hsum.sub hdiff).div_const _

-- no-dlmf: entirety of a `₁F₂`-shaped `pFq` instance (`p ≤ q`), no DLMF
-- counterpart (packaging of `pFqSeries_radius_eq_top`)
private theorem pFq_1_2_analyticOnNhd (A : Fin 1 → ℂ) (B : Fin 2 → ℂ) :
    AnalyticOnNhd ℂ (pFq (𝔸 := ℂ) A B) Set.univ := by
  have hrad : (pFqSeries ℂ A B).radius = ⊤ := pFqSeries_radius_eq_top ℂ A B (by norm_num)
  have hball : HasFPowerSeriesOnBall (pFq (𝔸 := ℂ) A B) (pFqSeries ℂ A B) 0 ⊤ := by
    have h := (pFqSeries ℂ A B).hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
    rwa [hrad] at h
  intro z _
  exact hball.analyticAt_of_mem (Metric.mem_eball.2 (edist_lt_top z 0))

-- no-dlmf: real-cast bridge feeding `erf_7_11_7_complex`, no DLMF counterpart
private theorem cfresnelC_kummer_eq_of_real (x : ℝ) :
    cfresnelC (x : ℂ) =
      (x : ℂ) * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)])
        (-(Real.pi:ℂ)^2 * (x:ℂ)^4/16) := by
  rw [cfresnelC_ofReal, erf_7_11_7 x, Complex.ofReal_mul]
  have h2 := pFq_ofReal (p := 1) (q := 2) (by norm_num)
    (![(1/4:ℝ)]) (![(5/4:ℝ), (1/2:ℝ)]) (-(Real.pi ^ 2) * x ^ 4 / 16)
  have hArw : ((↑) ∘ (![(1/4:ℝ)]) : Fin 1 → ℂ) = ![(1/4:ℂ)] := by
    funext i; fin_cases i; simp
  have hBrw : ((↑) ∘ (![(5/4:ℝ), (1/2:ℝ)]) : Fin 2 → ℂ) = ![(5/4:ℂ), (1/2:ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hArw, hBrw] at h2
  rw [h2]
  congr 2
  push_cast
  ring

/-- **DLMF 7.11.7**, at DLMF's full complex-variable strength:
`C(z) = z·₁F₂(¼; 5/4, ½; −π²z⁴/16)`, for every `z ∈ ℂ`. Proved from the
real-argument case (`erf_7_11_7`) by the identity theorem for analytic
functions: both sides are entire (LHS via `cfresnelC_differentiable`, RHS via
`pFq_1_2_analyticOnNhd`, both packaging existing entirety facts) and agree on
the reals, hence agree everywhere.

DAG: E-7.11.7.
Numerical: N/A (unparsed:char '𝔸')
Verified: verified
-/
theorem erf_7_11_7_complex (z : ℂ) :
    cfresnelC z =
      z * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)]) (-(Real.pi:ℂ)^2 * z^4/16) := by
  have hrhs_diff : Differentiable ℂ
      (fun w : ℂ => w * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16)) := by
    have harg : Differentiable ℂ (fun w : ℂ => -(Real.pi:ℂ)^2 * w^4/16) := by fun_prop
    have hpFq_diff : Differentiable ℂ (pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)])) :=
      fun w => (pFq_1_2_analyticOnNhd _ _ w (Set.mem_univ w)).differentiableAt
    exact differentiable_id.mul (hpFq_diff.comp harg)
  have hfAnalytic : AnalyticOnNhd ℂ cfresnelC Set.univ :=
    fun w _ => cfresnelC_differentiable.analyticAt w
  have hgAnalytic : AnalyticOnNhd ℂ
      (fun w : ℂ => w * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16))
      Set.univ :=
    fun w _ => hrhs_diff.analyticAt w
  have htendsto : Tendsto (fun n : ℕ => (1:ℂ)/((n:ℂ)+1)) atTop (𝓝[≠] (0:ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall (fun n => div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)))
  have hp : ∀ n : ℕ, cfresnelC ((1:ℂ)/((n:ℂ)+1))
      = (fun w : ℂ => w * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16))
        ((1:ℂ)/((n:ℂ)+1)) := by
    intro n
    have hcast : (1:ℂ)/((n:ℂ)+1) = (((1:ℝ)/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
    simp only
    rw [hcast]
    exact cfresnelC_kummer_eq_of_real (1/((n:ℝ)+1))
  have hkey : ∃ᶠ w in 𝓝[≠] (0:ℂ),
      cfresnelC w
      = (fun w : ℂ => w * pFq (𝔸 := ℂ) (![(1/4:ℂ)]) (![(5/4:ℂ), (1/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16)) w :=
    htendsto.frequently (Eventually.frequently (Eventually.of_forall hp))
  have heq := AnalyticOnNhd.eq_of_frequently_eq hfAnalytic hgAnalytic hkey
  exact congrFun heq z

-- no-dlmf: real-cast bridge feeding `erf_7_11_8_complex`, no DLMF counterpart
private theorem cfresnelS_kummer_eq_of_real (x : ℝ) :
    cfresnelS (x:ℂ) =
      ((Real.pi:ℂ) / 6) * (x:ℂ) ^ 3 *
        pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * (x:ℂ)^4/16) := by
  rw [cfresnelS_ofReal, erf_7_11_8 x, Complex.ofReal_mul, Complex.ofReal_mul]
  have h2 := pFq_ofReal (p := 1) (q := 2) (by norm_num)
    (![(3/4:ℝ)]) (![(7/4:ℝ), (3/2:ℝ)]) (-(Real.pi ^ 2) * x ^ 4 / 16)
  have hArw : ((↑) ∘ (![(3/4:ℝ)]) : Fin 1 → ℂ) = ![(3/4:ℂ)] := by
    funext i; fin_cases i; simp
  have hBrw : ((↑) ∘ (![(7/4:ℝ), (3/2:ℝ)]) : Fin 2 → ℂ) = ![(7/4:ℂ), (3/2:ℂ)] := by
    funext i; fin_cases i <;> simp
  rw [hArw, hBrw] at h2
  rw [h2]
  congr 2 <;> push_cast <;> ring

/-- **DLMF 7.11.8**, at DLMF's full complex-variable strength:
`S(z) = (π/6)·z³·₁F₂(¾; 7/4, 3/2; −π²z⁴/16)`, for every `z ∈ ℂ`. Proved from
the real-argument case (`erf_7_11_8`) by the identity theorem for analytic
functions, mirroring `erf_7_11_7_complex`.

DAG: E-7.11.8.
Numerical: N/A (unparsed:char '𝔸')
Verified: verified
-/
theorem erf_7_11_8_complex (z : ℂ) :
    cfresnelS z =
      ((Real.pi:ℂ) / 6) * z ^ 3 *
        pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * z^4/16) := by
  have hrhs_diff : Differentiable ℂ
      (fun w : ℂ => ((Real.pi:ℂ)/6) * w ^ 3 *
        pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16)) := by
    have harg : Differentiable ℂ (fun w : ℂ => -(Real.pi:ℂ)^2 * w^4/16) := by fun_prop
    have hpFq_diff : Differentiable ℂ (pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)])) :=
      fun w => (pFq_1_2_analyticOnNhd _ _ w (Set.mem_univ w)).differentiableAt
    have hcube : Differentiable ℂ (fun w : ℂ => ((Real.pi:ℂ)/6) * w ^ 3) := by fun_prop
    exact hcube.mul (hpFq_diff.comp harg)
  have hfAnalytic : AnalyticOnNhd ℂ cfresnelS Set.univ :=
    fun w _ => cfresnelS_differentiable.analyticAt w
  have hgAnalytic : AnalyticOnNhd ℂ
      (fun w : ℂ => ((Real.pi:ℂ)/6) * w ^ 3 *
        pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16))
      Set.univ :=
    fun w _ => hrhs_diff.analyticAt w
  have htendsto : Tendsto (fun n : ℕ => (1:ℂ)/((n:ℂ)+1)) atTop (𝓝[≠] (0:ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall (fun n => div_ne_zero one_ne_zero (Nat.cast_add_one_ne_zero n)))
  have hp : ∀ n : ℕ, cfresnelS ((1:ℂ)/((n:ℂ)+1))
      = (fun w : ℂ => ((Real.pi:ℂ)/6) * w ^ 3 *
          pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16))
        ((1:ℂ)/((n:ℂ)+1)) := by
    intro n
    have hcast : (1:ℂ)/((n:ℂ)+1) = (((1:ℝ)/((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; ring
    simp only
    rw [hcast]
    exact cfresnelS_kummer_eq_of_real (1/((n:ℝ)+1))
  have hkey : ∃ᶠ w in 𝓝[≠] (0:ℂ),
      cfresnelS w
      = (fun w : ℂ => ((Real.pi:ℂ)/6) * w ^ 3 *
          pFq (𝔸 := ℂ) (![(3/4:ℂ)]) (![(7/4:ℂ), (3/2:ℂ)]) (-(Real.pi:ℂ)^2 * w^4/16)) w :=
    htendsto.frequently (Eventually.frequently (Eventually.of_forall hp))
  have heq := AnalyticOnNhd.eq_of_frequently_eq hfAnalytic hgAnalytic hkey
  exact congrFun heq z

end FLMF.Error
