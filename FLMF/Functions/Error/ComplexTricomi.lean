import FLMF.Frameworks.Hypergeometric.TricomiComplex
import FLMF.Functions.Error.ComplexRepeatedErfc
import FLMF.Functions.Error.TricomiBridge
import FLMF.Functions.IncompleteGamma.ComplexDef

/-!
# DLMF §7.11 / §7.18 — the Tricomi-`U` representations for a complex variable

DLMF 7.11.5 and 7.18.10 express `erfc` and the repeated integrals `iⁿerfc` through
Tricomi's confluent hypergeometric function `U`, with a **complex** variable `z`.
FLMF's real `FLMF.Hypergeometric.tricomiU` (the DLMF 13.4.4 Laplace integral) could
only carry the real-axis restrictions `erf_7_11_5` / `erf_7_18_10`; this module
states the complex displays over the new
`FLMF.Hypergeometric.tricomiUC` (DLMF 13.2.42, `Frameworks/Hypergeometric/TricomiComplex.lean`).

## The sector

Both displays are stated on `Re z > 0`, i.e. `|ph z| < ½π`, and that is the
**maximal principal-branch domain**, not a narrowing:

* DLMF's own erratum for 7.18.10 records that "the confluent hypergeometric
  function on the right-hand side of (7.18.10) is multivalued and in the sectors
  ½π < |ph z| < π one has to use the analytic continuation formula (13.2.12)".
  So the display as literally written is a `|ph z| < ½π` statement.
* The same branch bound governs 7.11.5: the right-hand sides carry `U(·;·;z²)`,
  and `U(a,b,w)` is principal for `w` off the cut `(−∞,0]`.  Writing `w = z²`,
  the principal `(z²)^{1/2} = z` exactly on `Re z > 0` — off that half-plane the
  displays are *false* for the principal branch (numerically: at `z = −0.8` the
  two sides of 7.18.10 give 1.112 and 0.028), which is precisely why the
  real carriers already carried `0 < z`.  `Re z > 0` is the complex statement of
  that same restriction, and the real hypothesis `0 < z` is its real trace.

## The route

Both proofs are pure algebra on top of the already-verified `cerf_7_18_9`
(the Kummer `M`-pair form of `iⁿerfc`, `ComplexRepeatedErfc.lean`), because
`tricomiUC` is *defined* by the 13.2.42 combination of exactly that `M`-pair:

`U(a,b,w) = Γ(1−b)/Γ(a−b+1)·M(a,b,w) + Γ(b−1)/Γ(a)·w^{1−b}·M(a−b+1,2−b,w)`.

At `a = n/2+1/2`, `b = 1/2`, `w = z²` this reads
`U = √π/Γ(n/2+1)·M(n/2+1/2,1/2,z²) − 2√π/Γ(n/2+1/2)·z·M(n/2+1,3/2,z²)`
(using `(z²)^{1/2} = z` on `Re z > 0`), which is 7.18.9 up to the constant
`e^{−z²}/(2ⁿ√π)`.  7.11.5's two limbs are the `n = 0` instance, read through the
two parameter pairs `(1/2,1/2)` and `(1,3/2)`.

## Consistency with the real `tricomiU`

`TricomiComplex.lean` deliberately does not prove the general agreement
`tricomiUC a b (x:ℝ) = (tricomiU a b x : ℂ)` (that *is* the real case of DLMF
13.2.42, a Frameworks result of its own).  What is proved here — from the two
complex theorems together with their already-proven real counterparts — is
agreement on exactly the slices these displays use:

* `tricomiUC_ofReal_erfc_slice`: `(a,b) = (1/2,1/2)` and `(1,3/2)` at `w = x² > 0`;
* `tricomiUC_ofReal_repErfc_slice`: `(a,b) = (n/2+1/2,1/2)` at `w = x² > 0`, all `n`.

So the complex `U` is pinned to the real `U` wherever these displays live.

Main results:

* `FLMF.Error.cerf_7_11_5` — DLMF 7.11.5 for complex `z`, `Re z > 0`.
* `FLMF.Error.cerf_7_18_10` — DLMF 7.18.10 for complex `z`, `Re z > 0`.
-/

noncomputable section

namespace FLMF.Error

open FLMF.Hypergeometric

open scoped FLMF.Hypergeometric

/-! ## Constants and branch bookkeeping -/

-- no-dlmf: `Γ(1/2) = √π` over ℂ, the complex face of `Real.Gamma_one_half_eq`;
-- proof infrastructure, no DLMF identity number
/-- `Γ(1/2) = √π` over `ℂ`. -/
private theorem cGamma_half : Complex.Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Real.Gamma_one_half_eq]

-- no-dlmf: `Γ(−1/2) = −2√π` over ℂ from the recurrence; proof infrastructure,
-- no DLMF identity number
/-- `Γ(−1/2) = −2√π` over `ℂ` (from `Γ(s+1) = sΓ(s)` at `s = −1/2`). -/
private theorem cGamma_neg_half :
    Complex.Gamma (-(1 / 2) : ℂ) = -2 * (Real.sqrt Real.pi : ℂ) := by
  have h := Complex.Gamma_add_one (-(1 / 2) : ℂ) (by norm_num)
  rw [show (-(1 / 2) : ℂ) + 1 = 1 / 2 by ring, cGamma_half] at h
  linear_combination 2 * h

-- no-dlmf: `√π ≠ 0` cast into ℂ; proof infrastructure, no DLMF identity number
private theorem csqrtPi_ne_zero : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

-- no-dlmf: `z² ∈ ℂ∖(−∞,0]` on the right half-plane; branch bookkeeping, no DLMF
-- identity number
/-- On `Re z > 0` the square `z²` avoids the principal cut `(−∞, 0]`. -/
private theorem sq_mem_slitPlane {z : ℂ} (hz : 0 < z.re) : z ^ 2 ∈ Complex.slitPlane := by
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have him : (z ^ 2).im = 2 * (z.re * z.im) := by
    simp [pow_two, Complex.mul_im]; ring
  rcases eq_or_ne z.im 0 with h0 | h0
  · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hre, h0]
    nlinarith
  · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    rw [him]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hz.ne' h0)

-- no-dlmf: `Γ(n/2+1) ≠ 0`; proof infrastructure, no DLMF identity number
private theorem cGamma_half_succ_ne_zero (n : ℕ) : Complex.Gamma ((n : ℂ) / 2 + 1) ≠ 0 := by
  rw [show (n : ℂ) / 2 + 1 = ((((n : ℝ) / 2 + 1 : ℝ)) : ℂ) by push_cast; ring]
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  rw [Complex.ofReal_re]
  positivity

-- no-dlmf: `Γ(n/2+1/2) ≠ 0`; proof infrastructure, no DLMF identity number
private theorem cGamma_half_half_ne_zero (n : ℕ) :
    Complex.Gamma ((n : ℂ) / 2 + 1 / 2) ≠ 0 := by
  rw [show (n : ℂ) / 2 + 1 / 2 = ((((n : ℝ) / 2 + 1 / 2 : ℝ)) : ℂ) by push_cast; ring]
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  rw [Complex.ofReal_re]
  positivity

-- no-dlmf: real-rpow bookkeeping for the `2^{n−1}` prefactor of 7.18.9; proof
-- infrastructure, no DLMF identity number
/-- `2^{n−1}` as a real `rpow`, cast into `ℂ`: `((2:ℝ)^{(n:ℝ)−1} : ℂ) = 2ⁿ/2`. -/
private theorem two_rpow_sub_one_cast (n : ℕ) :
    ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ)) : ℂ) = (2 : ℂ) ^ n / 2 := by
  have h : ((2 : ℝ) ^ ((n : ℝ) - 1)) = (2 : ℝ) ^ n / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one]
  rw [h]; push_cast; ring

/-! ## Evaluating `tricomiUC` at the §7 parameter slices -/

-- no-dlmf: 13.2.42 evaluated at `(a,b) = (n/2+1/2, 1/2)`, `w = z²`; support
-- lemma for `cerf_7_18_10`, not a display of its own
/-- `U(n/2+1/2; 1/2; z²)` on `Re z > 0`, from the 13.2.42 connection formula:
`U = √π/Γ(n/2+1)·M(n/2+1/2,1/2,z²) − 2√π/Γ(n/2+1/2)·z·M(n/2+1,3/2,z²)`. -/
private theorem tricomiUC_repErfc_eval (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    tricomiUC ((n : ℂ) / 2 + 1 / 2) (1 / 2) (z ^ 2)
      = (Real.sqrt Real.pi : ℂ) / Complex.Gamma ((n : ℂ) / 2 + 1)
            * ₁F₁ ((n : ℂ) / 2 + 1 / 2) (1 / 2 : ℂ) (z ^ 2)
        + (-2 * (Real.sqrt Real.pi : ℂ)) / Complex.Gamma ((n : ℂ) / 2 + 1 / 2)
            * z * ₁F₁ ((n : ℂ) / 2 + 1) (3 / 2 : ℂ) (z ^ 2) := by
  rw [tricomiUC_of_mem (sq_mem_slitPlane hz) half_ne_intCast,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring,
    show ((n : ℂ) / 2 + 1 / 2) - 1 / 2 + 1 = (n : ℂ) / 2 + 1 by ring,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring,
    show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    cGamma_half, cGamma_neg_half, FLMF.IncompleteGamma.cpow_half_sq hz]

-- no-dlmf: 13.2.42 evaluated at `(a,b) = (1/2, 1/2)`, `w = z²`; support lemma
-- for `cerf_7_11_5`, not a display of its own
/-- `U(1/2; 1/2; z²) = √π·M(1/2,1/2,z²) − 2z·M(1,3/2,z²)` on `Re z > 0`
(13.2.42 at `a = b = 1/2`). -/
private theorem tricomiUC_half_half_eval {z : ℂ} (hz : 0 < z.re) :
    tricomiUC (1 / 2 : ℂ) (1 / 2) (z ^ 2)
      = (Real.sqrt Real.pi : ℂ) * ₁F₁ (1 / 2 : ℂ) (1 / 2 : ℂ) (z ^ 2)
        - 2 * z * ₁F₁ (1 : ℂ) (3 / 2 : ℂ) (z ^ 2) := by
  rw [tricomiUC_of_mem (sq_mem_slitPlane hz) half_ne_intCast,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring,
    show (1 / 2 : ℂ) - 1 / 2 + 1 = 1 by ring,
    show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring,
    show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    cGamma_half, cGamma_neg_half, Complex.Gamma_one,
    FLMF.IncompleteGamma.cpow_half_sq hz]
  field_simp
  ring

-- no-dlmf: 13.2.42 evaluated at `(a,b) = (1, 3/2)`, `w = z²`; support lemma for
-- `cerf_7_11_5`, not a display of its own
/-- `U(1; 3/2; z²) = −2·M(1,3/2,z²) + √π·z⁻¹·M(1/2,1/2,z²)` on `Re z > 0`
(13.2.42 at `a = 1`, `b = 3/2`). -/
private theorem tricomiUC_one_three_half_eval {z : ℂ} (hz : 0 < z.re) :
    tricomiUC (1 : ℂ) (3 / 2) (z ^ 2)
      = -2 * ₁F₁ (1 : ℂ) (3 / 2 : ℂ) (z ^ 2)
        + (Real.sqrt Real.pi : ℂ) * z⁻¹ * ₁F₁ (1 / 2 : ℂ) (1 / 2 : ℂ) (z ^ 2) := by
  rw [tricomiUC_of_mem (sq_mem_slitPlane hz) three_half_ne_intCast,
    show (1 : ℂ) - 3 / 2 + 1 = 1 / 2 by ring,
    show (1 : ℂ) - 3 / 2 = -(1 / 2) by ring,
    show (3 / 2 : ℂ) - 1 = 1 / 2 by ring,
    show (2 : ℂ) - 3 / 2 = 1 / 2 by ring,
    cGamma_half, cGamma_neg_half, Complex.Gamma_one,
    FLMF.IncompleteGamma.cpow_neg_half_sq hz]
  field_simp

/-! ## The `n = 0` Kummer pair for `erfc` -/

-- no-dlmf: the `n = 0` instance of DLMF 7.18.9 (surfaced at `cerf_7_18_9`),
-- rewritten with the numerical constants evaluated; support lemma
/-- `erfc(z) = e^{−z²}(M(1/2,1/2,z²) − 2z·M(1,3/2,z²)/√π)` for every complex `z`
(the `n = 0` instance of 7.18.9, since `i⁰erfc = erfc`). -/
private theorem cerfc_eq_kummerPair (z : ℂ) :
    cerfc z = Complex.exp (-z ^ 2) *
      (₁F₁ (1 / 2 : ℂ) (1 / 2 : ℂ) (z ^ 2)
        - 2 * z * ₁F₁ (1 : ℂ) (3 / 2 : ℂ) (z ^ 2) / (Real.sqrt Real.pi : ℂ)) := by
  have h := cerf_7_18_9 0 z
  rw [cRepErfc_zero] at h
  rw [h, two_rpow_sub_one_cast 0]
  have hg1 : Complex.Gamma (((0 : ℕ) : ℂ) / 2 + 1) = 1 := by
    norm_num [Complex.Gamma_one]
  have hg2 : Complex.Gamma (((0 : ℕ) : ℂ) / 2 + 1 / 2) = (Real.sqrt Real.pi : ℂ) := by
    rw [show (((0 : ℕ) : ℂ) / 2 + 1 / 2) = (1 / 2 : ℂ) by norm_num, cGamma_half]
  rw [hg1, hg2, show (((0 : ℕ) : ℂ) / 2 + 1 / 2) = (1 / 2 : ℂ) by norm_num,
    show (((0 : ℕ) : ℂ) / 2 + 1) = (1 : ℂ) by norm_num]
  have hπ := csqrtPi_ne_zero
  field_simp

/-! ## DLMF 7.11.5 -/

/-- **DLMF 7.11.5** — `erfc` as a Tricomi `U` value at two parameter pairs, for a
complex variable:
`erfc z = (1/√π)·e^{−z²}·U(1/2, 1/2, z²) = (z/√π)·e^{−z²}·U(1, 3/2, z²)`.

Stated on the sector `Re z > 0`, i.e. `|ph z| < ½π`.  This is the maximal
principal-branch domain, not a narrowing of DLMF's claim: the right-hand sides
carry `U(·;·;z²)`, whose principal branch requires `z²` off the cut `(−∞,0]`, and
`(z²)^{1/2} = z` (the branch fact behind both limbs) holds for the principal
power exactly on `Re z > 0`.  Off that half-plane the displays are false for the
principal branch and DLMF's own multivaluedness caveat applies.

`U` here is `FLMF.Hypergeometric.tricomiUC`, the complex Tricomi function defined
by Kummer's connection formula 13.2.42; the real-axis restriction of this
statement is `FLMF.Error.erf_7_11_5`, over the real `tricomiU`.

DLMF 7.11.5.
DAG: E-7.11.5.
Fidelity: tier1 n/a
Verified: verified (tier2)
-/
theorem cerf_7_11_5 {z : ℂ} (hz : 0 < z.re) :
    cerfc z = (1 / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-z ^ 2)
        * tricomiUC (1 / 2 : ℂ) (1 / 2) (z ^ 2) ∧
    cerfc z = (z / (Real.sqrt Real.pi : ℂ)) * Complex.exp (-z ^ 2)
        * tricomiUC (1 : ℂ) (3 / 2) (z ^ 2) := by
  have hπ := csqrtPi_ne_zero
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  constructor
  · rw [tricomiUC_half_half_eval hz, cerfc_eq_kummerPair z]
    field_simp
  · rw [tricomiUC_one_three_half_eval hz, cerfc_eq_kummerPair z]
    field_simp
    ring

/-! ## DLMF 7.18.10 -/

/-- **DLMF 7.18.10** — the Tricomi `U` representation of the repeated integrals of
`erfc`, for a complex variable:
`iⁿerfc(z) = e^{−z²}/(2ⁿ√π) · U(n/2+1/2, 1/2, z²)`.

Stated on the sector `Re z > 0`, i.e. `|ph z| < ½π`, which is exactly the domain
of DLMF's display: the DLMF erratum for 7.18.10 records that the confluent
hypergeometric function on the right-hand side is multivalued and that in the
sectors `½π < |ph z| < π` one must use the analytic continuation formula
13.2.12.  The principal branch used here satisfies `(z²)^{1/2} = z` precisely on
`Re z > 0`; the real carrier `FLMF.Error.erf_7_18_10` carries the real trace
`0 < z` of the same restriction.

`U` here is `FLMF.Hypergeometric.tricomiUC` (the 13.2.42 connection formula).

DLMF 7.18.10.
DAG: E-7.18.10.
Fidelity: tier1 n/a
Verified: verified (tier2)
-/
theorem cerf_7_18_10 (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    cRepErfc n z =
      Complex.exp (-z ^ 2) / ((2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ)) *
        tricomiUC ((n : ℂ) / 2 + 1 / 2) (1 / 2) (z ^ 2) := by
  have hπ := csqrtPi_ne_zero
  have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hg1 := cGamma_half_succ_ne_zero n
  have hg2 := cGamma_half_half_ne_zero n
  rw [cerf_7_18_9 n z, tricomiUC_repErfc_eval n hz, two_rpow_sub_one_cast n]
  field_simp
  ring

/-! ## Consistency with the real `tricomiU` on the §7 slices -/

-- no-dlmf: real↔complex agreement of `U` on the two 7.11.5 parameter slices;
-- consistency lemma, no DLMF identity number
/-- The complex `U` agrees with the real `U` on the two slices used by 7.11.5:
for `x > 0`, `U_ℂ(1/2,1/2,x²) = U_ℝ(1/2,1/2,x²)` and `U_ℂ(1,3/2,x²) = U_ℝ(1,3/2,x²)`.
Obtained by comparing `cerf_7_11_5` with its real counterpart
`erfc_eq_tricomiU_half` / `erfc_eq_tricomiU`. -/
theorem tricomiUC_ofReal_erfc_slice {x : ℝ} (hx : 0 < x) :
    tricomiUC (1 / 2 : ℂ) (1 / 2) ((x : ℂ) ^ 2)
        = ((tricomiU (1 / 2) (1 / 2) (x ^ 2) : ℝ) : ℂ) ∧
    tricomiUC (1 : ℂ) (3 / 2) ((x : ℂ) ^ 2)
        = ((tricomiU 1 (3 / 2) (x ^ 2) : ℝ) : ℂ) := by
  have hπ := csqrtPi_ne_zero
  have hxre : 0 < ((x : ℂ)).re := by simpa using hx
  have hx0 : (x : ℂ) ≠ 0 := by simpa using hx.ne'
  have hE : Complex.exp (-(x : ℂ) ^ 2) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨?_, ?_⟩
  · set U : ℝ := tricomiU (1 / 2) (1 / 2) (x ^ 2) with hUdef
    have hcast : ((FLMF.Error.erfc x : ℝ) : ℂ) = cerfc (x : ℂ) := (cerfc_ofReal x).symm
    rw [erfc_eq_tricomiU_half hx, (cerf_7_11_5 hxre).1] at hcast
    have hL : (((1 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) * U : ℝ) : ℂ)
        = 1 / (Real.sqrt Real.pi : ℂ) * Complex.exp (-(x : ℂ) ^ 2) * ((U : ℝ) : ℂ) := by
      push_cast [Complex.ofReal_exp]
      ring
    rw [hL] at hcast
    have hA : 1 / (Real.sqrt Real.pi : ℂ) * Complex.exp (-(x : ℂ) ^ 2) ≠ 0 :=
      mul_ne_zero (one_div_ne_zero hπ) hE
    exact (mul_left_cancel₀ hA hcast).symm
  · set U : ℝ := tricomiU 1 (3 / 2) (x ^ 2) with hUdef
    have hcast : ((FLMF.Error.erfc x : ℝ) : ℂ) = cerfc (x : ℂ) := (cerfc_ofReal x).symm
    rw [erfc_eq_tricomiU hx, (cerf_7_11_5 hxre).2] at hcast
    have hL : (((x / Real.sqrt Real.pi) * Real.exp (-x ^ 2) * U : ℝ) : ℂ)
        = (x : ℂ) / (Real.sqrt Real.pi : ℂ) * Complex.exp (-(x : ℂ) ^ 2) * ((U : ℝ) : ℂ) := by
      push_cast [Complex.ofReal_exp]
      ring
    rw [hL] at hcast
    have hA : (x : ℂ) / (Real.sqrt Real.pi : ℂ) * Complex.exp (-(x : ℂ) ^ 2) ≠ 0 :=
      mul_ne_zero (div_ne_zero hx0 hπ) hE
    exact (mul_left_cancel₀ hA hcast).symm

-- no-dlmf: real↔complex agreement of `U` on the 7.18.10 parameter slice;
-- consistency lemma, no DLMF identity number
/-- The complex `U` agrees with the real `U` on the slice used by 7.18.10: for
`x > 0` and every `n`, `U_ℂ(n/2+1/2,1/2,x²) = U_ℝ(n/2+1/2,1/2,x²)`.  Obtained by
comparing `cerf_7_18_10` with the real `erf_7_18_10`. -/
theorem tricomiUC_ofReal_repErfc_slice (n : ℕ) {x : ℝ} (hx : 0 < x) :
    tricomiUC ((n : ℂ) / 2 + 1 / 2) (1 / 2) ((x : ℂ) ^ 2)
      = ((FLMF.Hypergeometric.tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) (x ^ 2) : ℝ) : ℂ) := by
  have hπ := csqrtPi_ne_zero
  have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hxre : 0 < ((x : ℂ)).re := by simpa using hx
  have hE : Complex.exp (-(x : ℂ) ^ 2) ≠ 0 := Complex.exp_ne_zero _
  set U : ℝ := FLMF.Hypergeometric.tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) (x ^ 2) with hUdef
  have hcast : ((iRepErfc n x : ℝ) : ℂ) = cRepErfc n (x : ℂ) := (cRepErfc_ofReal n x).symm
  rw [erf_7_18_10 n hx, cerf_7_18_10 n hxre] at hcast
  have hL : ((Real.exp (-x ^ 2) / ((2 : ℝ) ^ n * Real.sqrt Real.pi) * U : ℝ) : ℂ)
      = Complex.exp (-(x : ℂ) ^ 2) / ((2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ))
          * ((U : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_exp]
    ring
  rw [hL] at hcast
  have hA : Complex.exp (-(x : ℂ) ^ 2) / ((2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ)) ≠ 0 :=
    div_ne_zero hE (mul_ne_zero h2 hπ)
  exact (mul_left_cancel₀ hA hcast).symm

end FLMF.Error
