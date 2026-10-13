import Mathlib
import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Dawson
import FLMF.Functions.Error.Ch7Definitions
import FLMF.Functions.Fresnel.Basic
import FLMF.Functions.Fresnel.Complex

/-!
# Symmetry relations for the error functions (DLMF §7.4)

This module states the parity/symmetry relations of DLMF §7.4. FLMF's
`erf`/`erfc`/`dawson`/`fresnelC`/`fresnelS` are real-valued, so the real
specializations of 7.4.1, 7.4.2, 7.4.5, 7.4.8 are recorded here as
`-- no-dlmf` narrowed instances (the DLMF variable `z` is complex with no
stated constraint). Their DLMF-domain-faithful complex surfaces are:

* 7.4.1 — `FLMF.Error.cerf_neg` (`Error/ComplexErf.lean`, pre-existing).
* 7.4.2 — `FLMF.Error.cerfc_neg` (below, new).
* 7.4.4 — `FLMF.Error.cdawson_neg` (`Error/ComplexErfExtra.lean`).
* 7.4.5 — `FLMF.Fresnel.cfresnelC_neg` / `cfresnelS_neg`
  (`Fresnel/Complex.lean`, pre-existing).
* 7.4.8 — `FLMF.Error.cfresnel_7_4_8` (below, new; complex
  `cfresnelAuxF`/`cfresnelAuxG` from `Fresnel/Complex.lean`).

7.4.4 (Dawson's integral, DLMF variable `z` complex) is DEFERRED: the
complex Dawson integral `cdawson` lives in `Error/ComplexErfExtra.lean`,
which transitively imports this file (`ComplexErfExtra → Ch7InverseErf →
Ch7Symmetry`), so a complex surface referencing the canonical `cdawson`
cannot be added here without an import cycle; a duplicate ad hoc definition
would violate the project's anti-duplication policy. The real specialization
`erf_7_4_4` is kept as-is (proven, `-- no-dlmf`).

FLMF's inherently complex entries of §7.4 that have no real specialization
at all — the Faddeeva function `w(z)` (7.4.3), the imaginary-argument
Fresnel relations (7.4.6), and the complex auxiliary functions `f`, `g`
(7.4.7) — remain documented deferrals below (resolved elsewhere, as noted).
-/

namespace FLMF.Error

open Real
open intervalIntegral MeasureTheory

-- no-dlmf: real/narrowed restriction of DLMF 7.4.1; faithful surface is
-- FLMF.Error.cerf_neg (Error/ComplexErf.lean)
/-- The real error function is odd: `erf(-z) = -erf(z)`. Real specialization
of DLMF 7.4.1 (DLMF's `z` is complex); see `cerf_neg` for the full-strength
complex surface. -/
theorem erf_7_4_1 (z : ℝ) : erf (-z) = -erf z := by
  unfold erf
  have heven : (∫ t in (0 : ℝ)..z, Real.exp (-(-t) ^ 2))
      = ∫ t in (0 : ℝ)..z, Real.exp (-t ^ 2) := by
    simp
  have hcn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
      (fun t => Real.exp (-t ^ 2))
  rw [heven] at hcn
  have hsym : (∫ t in (0 : ℝ)..(-z), Real.exp (-t ^ 2))
      = -∫ t in (0 : ℝ)..z, Real.exp (-t ^ 2) := by
    rw [hcn, intervalIntegral.integral_symm]
    simp
  rw [hsym]
  ring

-- no-dlmf: real/narrowed restriction of DLMF 7.4.2; faithful surface is
-- cerfc_neg (below)
/-- Real complementary error function symmetry: `erfc(-z) = 2 - erfc(z)`.
Real specialization of DLMF 7.4.2 (DLMF's `z` is complex); see `cerfc_neg`
for the full-strength complex surface. -/
theorem erf_7_4_2 (z : ℝ) : erfc (-z) = 2 - erfc z := by
  unfold erfc
  rw [erf_7_4_1]
  ring

/-- **DLMF 7.4.2** — the complex complementary error function is symmetric:
`erfc(-z) = 2 - erfc(z)`.

DLMF 7.4.2.
DAG: E-7.4.2.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem cerfc_neg (z : ℂ) : cerfc (-z) = 2 - cerfc z := by
  unfold cerfc
  rw [cerf_neg]
  ring

-- DLMF 7.4.3: `w(-z) = 2 e^{-z²} - w(z)`.
-- RESOLVED (and PROVEN) in Error/Faddeeva.lean as `erf_7_4_3`, via the complex
-- Faddeeva keystone. Original deferral kept for context:
-- the Faddeeva (plasma dispersion) function `w(z) = e^{-z²} erfc(-iz)`
-- is intrinsically complex-valued and is not part of the REAL-valued FLMF
-- error-function surface. Stating this faithfully requires a complex `erf`/`w`
-- (`ℂ → ℂ`), which FLMF does not currently provide. No honest real
-- specialization exists (the right-hand side multiplies by `e^{-z²}` with a
-- genuinely complex `w`), so it is recorded as a deferral rather than a
-- weakened/vacuous theorem.

-- no-dlmf: real/narrowed restriction of DLMF 7.4.4; faithful surface is
-- cdawson_neg (ComplexErfExtra.lean)
/-- The real Dawson integral is odd: `F(-z) = -F(z)`. Real specialization of
DLMF 7.4.4 (DLMF's `z` is complex); see `FLMF.Error.cdawson_neg`
(`Error/ComplexErfExtra.lean`) for the full-strength complex surface. -/
theorem erf_7_4_4 (z : ℝ) : FLMF.dawson (-z) = -FLMF.dawson z :=
  FLMF.dawson_neg z

-- no-dlmf: real/narrowed restriction of DLMF 7.4.5; faithful surface is
-- FLMF.Fresnel.cfresnelC_neg / cfresnelS_neg (Fresnel/Complex.lean)
/-- The real Fresnel integrals are odd: `C(-z) = -C(z)` and `S(-z) = -S(z)`.
Real specialization of DLMF 7.4.5 (DLMF's `z` is complex); see
`cfresnelC_neg`/`cfresnelS_neg` for the full-strength complex surface. -/
theorem erf_7_4_5 (z : ℝ) :
    FLMF.Fresnel.fresnelC (-z) = -FLMF.Fresnel.fresnelC z ∧
      FLMF.Fresnel.fresnelS (-z) = -FLMF.Fresnel.fresnelS z := by
  constructor
  · unfold FLMF.Fresnel.fresnelC FLMF.Fresnel.cosArg
    have heven : (∫ t in (0 : ℝ)..z, Real.cos (Real.pi * (-t) ^ 2 / 2))
        = ∫ t in (0 : ℝ)..z, Real.cos (Real.pi * t ^ 2 / 2) := by
      simp
    have hcn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
        (fun t => Real.cos (Real.pi * t ^ 2 / 2))
    rw [heven] at hcn
    rw [hcn, intervalIntegral.integral_symm]
    simp
  · unfold FLMF.Fresnel.fresnelS FLMF.Fresnel.sinArg
    have heven : (∫ t in (0 : ℝ)..z, Real.sin (Real.pi * (-t) ^ 2 / 2))
        = ∫ t in (0 : ℝ)..z, Real.sin (Real.pi * t ^ 2 / 2) := by
      simp
    have hcn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
        (fun t => Real.sin (Real.pi * t ^ 2 / 2))
    rw [heven] at hcn
    rw [hcn, intervalIntegral.integral_symm]
    simp

-- DLMF 7.4.6: `C(iz) = i C(z)` and `S(iz) = -i S(z)`.
-- RESOLVED (and PROVEN) in Fresnel/Complex.lean as `cfresnel_7_4_6`, via the complex
-- Fresnel keystone. Original deferral kept for context:
-- these relate the Fresnel integrals at the imaginary argument `iz`.
-- FLMF's `fresnelC`/`fresnelS` are REAL functions `ℝ → ℝ`, so the imaginary
-- argument `iz` and the resulting `i·C(z)` / `-i·S(z)` cannot be expressed
-- without a complex Fresnel extension (`ℂ → ℂ`), which FLMF does not provide.
-- No real specialization exists, so this is a deferral.

-- DLMF 7.4.7: `f(iz) = ½ e^{iπ/4 - iπ z²/2} - i f(z)` and
--             `g(iz) = ½ e^{-iπ/4 - iπ z²/2} + i g(z)`.
-- RESOLVED in Fresnel/Complex.lean as `cfresnel_7_4_7` (complex auxiliaries
-- cfresnelAuxF/G; the (1/√2)e^{iπ/4} prefactor = ½(1+i)). Original deferral kept
-- for context: (1) the auxiliary Fresnel functions `f`, `g`
-- (DLMF 7.2.9–7.2.10) are not part of the FLMF surface, and (2) the relation is
-- at the imaginary argument `iz` with complex right-hand sides. Both require
-- complex machinery FLMF does not have; deferred rather than faked.

-- no-dlmf: real/narrowed restriction of DLMF 7.4.8; faithful surface is
-- cfresnel_7_4_8 (below)
/-- Reflection formula for the real Fresnel auxiliary functions `f`, `g` at
the real argument `-z`:
`f(-z) = √2 cos(π/4 + π z²/2) - f(z)` and `g(-z) = √2 sin(π/4 + π z²/2) - g(z)`.
Real specialization of DLMF 7.4.8 (DLMF's `z` is complex); see
`cfresnel_7_4_8` for the full-strength complex surface. -/
theorem erf_7_4_8 (z : ℝ) :
    fresnelAuxF (-z) = Real.sqrt 2 * Real.cos (π / 4 + π * z ^ 2 / 2) - fresnelAuxF z
      ∧ fresnelAuxG (-z) = Real.sqrt 2 * Real.sin (π / 4 + π * z ^ 2 / 2) - fresnelAuxG z := by
  obtain ⟨hC, hS⟩ := erf_7_4_5 z
  have h2 : Real.sqrt 2 * Real.cos (Real.pi/4) = 1 := by
    rw [Real.cos_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h3 : Real.sqrt 2 * Real.sin (Real.pi/4) = 1 := by
    rw [Real.sin_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hsq : Real.pi * (-z)^2/2 = Real.pi * z^2/2 := by ring_nf
  constructor
  · unfold fresnelAuxF; rw [Real.cos_add, hsq, hC, hS]
    linear_combination (-Real.cos (Real.pi*z^2/2))*h2 + (Real.sin (Real.pi*z^2/2))*h3
  · unfold fresnelAuxG; rw [Real.sin_add, hsq, hC, hS]
    linear_combination (-Real.cos (Real.pi*z^2/2))*h3 + (-Real.sin (Real.pi*z^2/2))*h2

/-- **DLMF 7.4.8** — reflection formula for the complex Fresnel auxiliary
functions `f`, `g` at `-z`:
`f(-z) = √2 cos(π/4 + π z²/2) - f(z)` and `g(-z) = √2 sin(π/4 + π z²/2) - g(z)`.

DLMF 7.4.8.
DAG: E-7.4.8.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem cfresnel_7_4_8 (z : ℂ) :
    FLMF.Fresnel.cfresnelAuxF (-z)
        = (Real.sqrt 2 : ℂ) * Complex.cos ((Real.pi : ℂ) / 4 + (Real.pi : ℂ) * z ^ 2 / 2)
            - FLMF.Fresnel.cfresnelAuxF z
      ∧ FLMF.Fresnel.cfresnelAuxG (-z)
        = (Real.sqrt 2 : ℂ) * Complex.sin ((Real.pi : ℂ) / 4 + (Real.pi : ℂ) * z ^ 2 / 2)
            - FLMF.Fresnel.cfresnelAuxG z := by
  have hC := FLMF.Fresnel.cfresnelC_neg z
  have hS := FLMF.Fresnel.cfresnelS_neg z
  have h2 : (Real.sqrt 2 : ℂ) * Complex.cos ((Real.pi : ℂ) / 4) = 1 := by
    have hcast : ((Real.pi : ℂ) / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_cos]
    have hreal : Real.sqrt 2 * Real.cos (Real.pi / 4) = 1 := by
      rw [Real.cos_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    exact_mod_cast hreal
  have h3 : (Real.sqrt 2 : ℂ) * Complex.sin ((Real.pi : ℂ) / 4) = 1 := by
    have hcast : ((Real.pi : ℂ) / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_sin]
    have hreal : Real.sqrt 2 * Real.sin (Real.pi / 4) = 1 := by
      rw [Real.sin_pi_div_four, ← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    exact_mod_cast hreal
  have hsq : (Real.pi : ℂ) * (-z) ^ 2 / 2 = (Real.pi : ℂ) * z ^ 2 / 2 := by ring_nf
  constructor
  · unfold FLMF.Fresnel.cfresnelAuxF; rw [Complex.cos_add, hsq, hC, hS]
    linear_combination (-Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) * h2
      + (Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) * h3
  · unfold FLMF.Fresnel.cfresnelAuxG; rw [Complex.sin_add, hsq, hC, hS]
    linear_combination (-Complex.cos ((Real.pi : ℂ) * z ^ 2 / 2)) * h3
      + (-Complex.sin ((Real.pi : ℂ) * z ^ 2 / 2)) * h2

end FLMF.Error
