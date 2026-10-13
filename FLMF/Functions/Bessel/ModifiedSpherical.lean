/-
  Modified Spherical Bessel Functions  i_n^{(1)}, k_n

  The modified spherical Bessel functions of the first and second kind are
  defined (DLMF 10.47.7, 10.47.9) by
    i_n^{(1)}(z) = sqrt(π/(2z)) I_{n+1/2}(z),   k_n(z) = sqrt(π/(2z)) K_{n+1/2}(z).

  Since Mathlib currently has no API for the cylinder modified Bessel functions
  `I_ν`, `K_ν` of half-integer order, we take the equivalent **closed-form
  definition** (DLMF 10.49.8/10.49.12) as our basic definition and develop the
  standard structural properties from it:

  * base cases  `i₀^{(1)}(z) = sinh z / z`,  `k₀(z) = e^{-z}/z`,
                `i₁^{(1)}(z) = cosh z / z - sinh z / z²`,
                `k₁(z) = e^{-z}/z + e^{-z}/z²`;
  * the three-term recurrence (DLMF 10.51.4/10.51.5):
        i_{n+1}(z) = i_{n-1}(z) - ((2n+1)/z) i_n(z),
        k_{n+1}(z) = k_{n-1}(z) + ((2n+1)/z) k_n(z);
  * closed forms at `n = 2` and the derivatives of the base cases.

  ## References
  - DLMF Chapter 10.47-10.51: https://dlmf.nist.gov/10.47
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace FLMF.Bessel

open Real

/-! ## Definitions via the three-term recurrence

We define the modified spherical Bessel functions of the first and second kind
by their base cases at `n = 0, 1` together with the upward recurrence relations
(DLMF 10.51.4/10.51.5):
  `i_{n+1}(z) = i_{n-1}(z) - ((2n+1)/z) i_n(z)`,
  `k_{n+1}(z) = k_{n-1}(z) + ((2n+1)/z) k_n(z)`.
This is the standard closed-form construction and is equivalent to the
definition `f_n(z) = sqrt(π/(2z)) C_{n+1/2}(z)` whenever `z ≠ 0`. -/

/-- Modified spherical Bessel function of the first kind `i_n^{(1)}(z)`
(DLMF 10.47.7), defined by the upward recurrence with `i₀ = sinh z / z`,
`i₁ = cosh z / z - sinh z / z²`. -/
noncomputable def modSphericalI : ℕ → ℝ → ℝ
  | 0, z => Real.sinh z / z
  | 1, z => Real.cosh z / z - Real.sinh z / z ^ 2
  | (n + 2), z =>
      modSphericalI n z - (2 * (n + 1) + 1) / z * modSphericalI (n + 1) z

/-- Modified spherical Bessel function of the second kind `k_n(z)`
(DLMF 10.47.9), defined by the upward recurrence with `k₀ = e^{-z}/z`,
`k₁ = e^{-z}/z + e^{-z}/z²`. -/
noncomputable def modSphericalK : ℕ → ℝ → ℝ
  | 0, z => Real.exp (-z) / z
  | 1, z => Real.exp (-z) / z + Real.exp (-z) / z ^ 2
  | (n + 2), z =>
      modSphericalK n z + (2 * (n + 1) + 1) / z * modSphericalK (n + 1) z

/-! ## Complex-domain twins (DLMF's stated variable domain)

DLMF's `z` in Chapter 10 is a complex variable; `modSphericalI`/`modSphericalK`
above are restricted to `z : ℝ` (this is the convention consumed by the
real-analytic series in `Functions/Error/Ch7Series.lean`, so that binder type
is kept as-is rather than widened in place). The functions below mirror the
same recursive construction over `ℂ`, matching DLMF's own closed-form
definition (10.49.8/10.49.12) verbatim, and let the base-case/recurrence
identities below be surfaced at DLMF's full stated domain. -/

/-- Complex-domain modified spherical Bessel function of the first kind,
mirroring `modSphericalI` over `ℂ` (DLMF 10.47.7, complex `z`). -/
noncomputable def modSphericalIC : ℕ → ℂ → ℂ
  | 0, z => Complex.sinh z / z
  | 1, z => Complex.cosh z / z - Complex.sinh z / z ^ 2
  | (n + 2), z =>
      modSphericalIC n z - (2 * (n + 1) + 1) / z * modSphericalIC (n + 1) z

/-- Complex-domain modified spherical Bessel function of the second kind,
mirroring `modSphericalK` over `ℂ` (DLMF 10.47.9, complex `z`). -/
noncomputable def modSphericalKC : ℕ → ℂ → ℂ
  | 0, z => Complex.exp (-z) / z
  | 1, z => Complex.exp (-z) / z + Complex.exp (-z) / z ^ 2
  | (n + 2), z =>
      modSphericalKC n z + (2 * (n + 1) + 1) / z * modSphericalKC (n + 1) z

/-! ## Base cases (DLMF 10.49.9, 10.49.13) -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 10.49.9
-- surface is modSphericalI_10_49_9
/-- (base case `n = 0`): `i₀^{(1)}(z) = sinh z / z`. -/
@[simp] theorem modSphericalI_zero (z : ℝ) :
    modSphericalI 0 z = Real.sinh z / z := rfl

-- no-dlmf: chain link 10.49.9 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalI_10_49_9). (Previously tagged 10.49.8, the general-`n`
-- sum formula, of which this is only the `n = 0` instance.)
/-- (`n = 0` line): `i₀^{(1)}(z) = sinh z / z` (DLMF-faithful restriction of
`modSphericalI_zero`: `z ≠ 0`). -/
theorem modSphericalI_zero_dlmf (z : ℝ) (hz : z ≠ 0) :
    modSphericalI 0 z = Real.sinh z / z := modSphericalI_zero z

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 10.49.9
-- surface is modSphericalI_10_49_9
/-- (base case `n = 1`): `i₁^{(1)}(z) = cosh z / z - sinh z / z²`. -/
@[simp] theorem modSphericalI_one (z : ℝ) :
    modSphericalI 1 z = Real.cosh z / z - Real.sinh z / z ^ 2 := rfl

-- no-dlmf: chain link 10.49.9 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalI_10_49_9). (Previously tagged 10.49.8, the general-`n`
-- sum formula, of which this is only the `n = 1` instance.)
/-- (`n = 1` line): `i₁^{(1)}(z) = cosh z / z - sinh z / z²`
(DLMF-faithful restriction of `modSphericalI_one`: `z ≠ 0`). -/
theorem modSphericalI_one_dlmf (z : ℝ) (hz : z ≠ 0) :
    modSphericalI 1 z = Real.cosh z / z - Real.sinh z / z ^ 2 := modSphericalI_one z

-- no-dlmf: complex-domain twin of modSphericalI_zero (definitional; chain link
-- 10.49.9, assembled in modSphericalI_10_49_9)
/-- `i₀^{(1)}(z) = sinh z / z` over `ℂ`. -/
theorem modSphericalI_zero_complex (z : ℂ) :
    modSphericalIC 0 z = Complex.sinh z / z := rfl

-- no-dlmf: complex-domain twin of modSphericalI_one (definitional; chain link
-- 10.49.9, assembled in modSphericalI_10_49_9)
/-- `i₁^{(1)}(z) = cosh z / z - sinh z / z²` over `ℂ`. -/
theorem modSphericalI_one_complex (z : ℂ) :
    modSphericalIC 1 z = Complex.cosh z / z - Complex.sinh z / z ^ 2 := rfl

-- no-dlmf: FLMF's modSphericalK omits DLMF 10.49.13's π/2 prefactor (the
-- DLMF-faithful π/2-scaled identity is modSphericalK_10_49_13)
/-- (base case `n = 0`): `k₀(z) = e^{-z} / z`. -/
@[simp] theorem modSphericalK_zero (z : ℝ) :
    modSphericalK 0 z = Real.exp (-z) / z := rfl

-- no-dlmf: chain link 10.49.13 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalK_10_49_13). (Previously tagged 10.49.12, the general-`n`
-- sum formula, of which this is only the `n = 0` instance.)
/-- (`n = 0` line, π/2-scaled): `(π/2) · k₀(z) = (π/2) · e^{-z}/z`
— i.e. `modSphericalK 0` matches DLMF's `𝗄₀(z) = ½π e^{-z}/z` up to the `π/2`
normalization prefactor that `modSphericalK` omits (DLMF-faithful restriction:
`z ≠ 0`). -/
theorem modSphericalK_zero_dlmf (z : ℝ) (_hz : z ≠ 0) :
    Real.pi / 2 * modSphericalK 0 z = Real.pi / 2 * (Real.exp (-z) / z) := by
  rw [modSphericalK_zero]

-- no-dlmf: FLMF's modSphericalK omits DLMF 10.49.13's π/2 prefactor (the
-- DLMF-faithful π/2-scaled identity is modSphericalK_10_49_13)
/-- (base case `n = 1`): `k₁(z) = e^{-z}/z + e^{-z}/z²`. -/
@[simp] theorem modSphericalK_one (z : ℝ) :
    modSphericalK 1 z = Real.exp (-z) / z + Real.exp (-z) / z ^ 2 := rfl

-- no-dlmf: chain link 10.49.13 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalK_10_49_13). (Previously tagged 10.49.12, the general-`n`
-- sum formula, of which this is only the `n = 1` instance.)
/-- (`n = 1` line, π/2-scaled): `(π/2) · k₁(z) = (π/2) · (e^{-z}/z + e^{-z}/z²)`
— i.e. `modSphericalK 1` matches DLMF's `𝗄₁(z) = ½π e^{-z}(1/z + 1/z²)` up to
the `π/2` normalization prefactor that `modSphericalK` omits (DLMF-faithful
restriction: `z ≠ 0`). -/
theorem modSphericalK_one_dlmf (z : ℝ) (_hz : z ≠ 0) :
    Real.pi / 2 * modSphericalK 1 z
      = Real.pi / 2 * (Real.exp (-z) / z + Real.exp (-z) / z ^ 2) := by
  rw [modSphericalK_one]

-- no-dlmf: complex-domain twin of modSphericalK_zero_dlmf's π/2-scaled base case
-- (definitional; chain link 10.49.13, assembled in modSphericalK_10_49_13)
/-- `(π/2) · k₀(z) = (π/2) · e^{-z}/z` over `ℂ`. -/
theorem modSphericalK_zero_complex (z : ℂ) :
    (Real.pi : ℂ) / 2 * modSphericalKC 0 z = (Real.pi : ℂ) / 2 * (Complex.exp (-z) / z) := by
  simp only [modSphericalKC]

-- no-dlmf: complex-domain twin of modSphericalK_one_dlmf's π/2-scaled base case
-- (definitional; chain link 10.49.13, assembled in modSphericalK_10_49_13)
/-- `(π/2) · k₁(z) = (π/2) · (e^{-z}/z + e^{-z}/z²)` over `ℂ`. -/
theorem modSphericalK_one_complex (z : ℂ) :
    (Real.pi : ℂ) / 2 * modSphericalKC 1 z
      = (Real.pi : ℂ) / 2 * (Complex.exp (-z) / z + Complex.exp (-z) / z ^ 2) := by
  simp only [modSphericalKC]

/-! ## Three-term recurrence (DLMF 10.51.4, 10.51.5)

For the modified spherical Bessel functions the recurrences are
`i_{n-1}(z) - i_{n+1}(z) = ((2n+1)/z) i_n(z)` and
`k_{n-1}(z) - k_{n+1}(z) = -((2n+1)/z) k_n(z)`. -/

-- no-dlmf: chain link 10.51.4 (real/narrowed restriction; assembled, in complex
-- form, in modSpherical_10_51_4)
/-- Three-term recurrence for `i_n^{(1)}`, real `z`. -/
theorem modSphericalI_recurrence (n : ℕ) (z : ℝ) :
    modSphericalI (n + 2) z
      = modSphericalI n z - (2 * (n + 1) + 1) / z * modSphericalI (n + 1) z := rfl

-- no-dlmf: chain link 10.51.4 (algebraic row, specialized to `g_n = i_n^{(1)}`;
-- assembled in modSpherical_10_51_4)
/-- Three-term recurrence for `i_n^{(1)}` at DLMF's stated complex `z` (the `g_n`
display of 10.51.4 is `g_{n-1}(z) - g_{n+1}(z) = ((2n+1)/z) g_n(z)`, specialized
to `g_n = i_n^{(1)}`). -/
theorem modSphericalI_recurrence_complex (n : ℕ) (z : ℂ) :
    modSphericalIC (n + 2) z
      = modSphericalIC n z - (2 * (n + 1) + 1) / z * modSphericalIC (n + 1) z := rfl

-- no-dlmf: chain link 10.51.4 (algebraic row, specialized to `g_n = (-1)^n k_n`;
-- assembled in modSpherical_10_51_4). (Previously mistagged 10.51.5, which states
-- the *derivative* identities `g_n' = g_{n-1} - ((n+1)/z)g_n` etc., a different
-- relation.)
/-- Three-term recurrence for `k_n`: the `g_n` display of 10.51.4 is
`g_{n-1}(z) - g_{n+1}(z) = ((2n+1)/z) g_n(z)`, where `g_n` denotes `𝗂_n^{(1)}`,
`𝗂_n^{(2)}`, or `(-1)^n 𝗄_n(z)`; substituting `g_n = (-1)^n k_n` (the `n-1` and
`n+1` sign factors are equal, since `n-1, n+1` share parity, so they cancel)
gives exactly this `k_n`-only recurrence. -/
theorem modSphericalK_recurrence (n : ℕ) (z : ℝ) :
    modSphericalK (n + 2) z
      = modSphericalK n z + (2 * (n + 1) + 1) / z * modSphericalK (n + 1) z := rfl

-- no-dlmf: complex-domain twin of modSphericalK_recurrence (definitional; chain
-- link 10.51.4, assembled in modSpherical_10_51_4)
/-- Three-term recurrence for `k_n` at DLMF's stated complex `z`. -/
theorem modSphericalK_recurrence_complex (n : ℕ) (z : ℂ) :
    modSphericalKC (n + 2) z
      = modSphericalKC n z + (2 * (n + 1) + 1) / z * modSphericalKC (n + 1) z := rfl

-- no-dlmf: chain link 10.51.4 (real/narrowed restriction; assembled, in complex
-- form, in modSpherical_10_51_4)
/-- The symmetric form of the recurrence, real `z`:
`i_{n-1}(z) - i_{n+1}(z) = ((2n+1)/z) i_n(z)`. -/
theorem modSphericalI_recurrence' (n : ℕ) (z : ℝ) :
    modSphericalI n z - modSphericalI (n + 2) z
      = (2 * (n + 1) + 1) / z * modSphericalI (n + 1) z := by
  rw [modSphericalI_recurrence]; ring

-- no-dlmf: chain link 10.51.4 (algebraic row, specialized to `g_n = i_n^{(1)}`,
-- symmetric form; assembled in modSpherical_10_51_4)
/-- The symmetric form of the three-term recurrence for `i_n^{(1)}` at DLMF's
stated complex `z`: `i_{n-1}(z) - i_{n+1}(z) = ((2n+1)/z) i_n(z)`. -/
theorem modSphericalI_recurrence'_complex (n : ℕ) (z : ℂ) :
    modSphericalIC n z - modSphericalIC (n + 2) z
      = (2 * (n + 1) + 1) / z * modSphericalIC (n + 1) z := by
  rw [modSphericalI_recurrence_complex]; ring

-- no-dlmf: chain link 10.51.4 (algebraic row, specialized to `g_n = (-1)^n k_n`,
-- symmetric form; assembled in modSpherical_10_51_4). (Previously mistagged
-- 10.51.5, which states the derivative identities, a different relation.)
/-- The symmetric form of `g_n`'s three-term recurrence, specialized to `k_n`
via `g_n = (-1)^n k_n` (see `modSphericalK_recurrence`):
`k_{n-1}(z) - k_{n+1}(z) = -((2n+1)/z) k_n(z)`. -/
theorem modSphericalK_recurrence' (n : ℕ) (z : ℝ) :
    modSphericalK n z - modSphericalK (n + 2) z
      = -((2 * (n + 1) + 1) / z * modSphericalK (n + 1) z) := by
  rw [modSphericalK_recurrence]; ring

-- no-dlmf: complex-domain twin of modSphericalK_recurrence' (chain link 10.51.4,
-- assembled in modSpherical_10_51_4)
/-- The symmetric form of the recurrence for `k_n` at DLMF's stated complex `z`:
`k_{n-1}(z) - k_{n+1}(z) = -((2n+1)/z) k_n(z)`. -/
theorem modSphericalK_recurrence'_complex (n : ℕ) (z : ℂ) :
    modSphericalKC n z - modSphericalKC (n + 2) z
      = -((2 * (n + 1) + 1) / z * modSphericalKC (n + 1) z) := by
  rw [modSphericalK_recurrence_complex]; ring

-- no-dlmf: chain link 10.51.4 (derivative row, specialized to `g_n = i_n^{(1)}`;
-- assembled in modSpherical_10_51_4). General-`n` differentiability of
-- `modSphericalIC` beyond the `n = 0` base case (`hasDerivAt_modSphericalI_zero'`,
-- DLMF 10.51.5) is not yet established in this file; verified numerically
-- (symbolic differentiation of the defining recursion) before being recorded here.
/-- `n · i_{n-1}(z) + (n+1) · i_{n+1}(z) = (2n+1) · i_n'(z)`, the derivative row of
DLMF 10.51.4 specialized to `g_n = i_n^{(1)}`, for `n = 1, 2, …` and `z ≠ 0`. -/
theorem modSphericalI_deriv_recurrence (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalIC n)
      (((n : ℂ) * modSphericalIC (n - 1) z + ((n : ℂ) + 1) * modSphericalIC (n + 1) z)
        / (2 * (n : ℂ) + 1)) z := by
  sorry

-- no-dlmf: chain link 10.51.4 (derivative row, specialized to `g_n = (-1)^n k_n`;
-- assembled in modSpherical_10_51_4). General-`n` differentiability of
-- `modSphericalKC` beyond the `n = 0` base case (`hasDerivAt_modSphericalK_zero'`,
-- DLMF 10.51.5) is not yet established in this file; verified numerically
-- (symbolic differentiation of the defining recursion) before being recorded here.
/-- `n · k_{n-1}(z) + (n+1) · k_{n+1}(z) = -(2n+1) · k_n'(z)`, the derivative row
of DLMF 10.51.4 specialized to `g_n = (-1)^n k_n` (the sign flips relative to the
`i_n^{(1)}` case since `g_n = (-1)^n k_n`), for `n = 1, 2, …` and `z ≠ 0`. -/
theorem modSphericalK_deriv_recurrence (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalKC n)
      (-((n : ℂ) * modSphericalKC (n - 1) z + ((n : ℂ) + 1) * modSphericalKC (n + 1) z)
        / (2 * (n : ℂ) + 1)) z := by
  sorry

/-- **DLMF 10.51.4** — both rows of the recurrence relations for `g_n` (DLMF's
`g_n` denotes any of `𝗂_n^{(1)}`, `𝗂_n^{(2)}`, or `(-1)^n 𝗄_n(z)`; only `i_n^{(1)}`
and `k_n` are tracked in this file), at DLMF's stated complex `z`: the algebraic
row `g_{n-1}(z) - g_{n+1}(z) = ((2n+1)/z) g_n(z)` and the derivative row
`n g_{n-1}(z) + (n+1) g_{n+1}(z) = (2n+1) g_n'(z)`, `n = 1, 2, …`.
DAG: E-10.51.4.
Fidelity: tier1 unable (unparsed:forall-body unconsumed)
Verified: unverified
-/
theorem modSpherical_10_51_4 (z : ℂ) (hz : z ≠ 0) :
    (∀ n : ℕ, modSphericalIC n z - modSphericalIC (n + 2) z
        = (2 * (n + 1) + 1) / z * modSphericalIC (n + 1) z) ∧
      (∀ n : ℕ, modSphericalKC n z - modSphericalKC (n + 2) z
        = -((2 * (n + 1) + 1) / z * modSphericalKC (n + 1) z)) ∧
      (∀ n : ℕ, 1 ≤ n → HasDerivAt (modSphericalIC n)
        (((n : ℂ) * modSphericalIC (n - 1) z + ((n : ℂ) + 1) * modSphericalIC (n + 1) z)
          / (2 * (n : ℂ) + 1)) z) ∧
      (∀ n : ℕ, 1 ≤ n → HasDerivAt (modSphericalKC n)
        (-((n : ℂ) * modSphericalKC (n - 1) z + ((n : ℂ) + 1) * modSphericalKC (n + 1) z)
          / (2 * (n : ℂ) + 1)) z) :=
  ⟨fun n => modSphericalI_recurrence'_complex n z,
   fun n => modSphericalK_recurrence'_complex n z,
   fun n hn => modSphericalI_deriv_recurrence n hn z hz,
   fun n hn => modSphericalK_deriv_recurrence n hn z hz⟩

/-! ## Closed forms at `n = 2` (DLMF 10.49.9, 10.49.13) -/

-- no-dlmf: chain link 10.49.9 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalI_10_49_9)
/-- Closed form for `i₂^{(1)}(z)`, real `z`. -/
theorem modSphericalI_two (z : ℝ) (hz : z ≠ 0) :
    modSphericalI 2 z
      = (3 / z ^ 3 + 1 / z) * Real.sinh z - 3 / z ^ 2 * Real.cosh z := by
  have h := modSphericalI_recurrence 0 z
  rw [h, modSphericalI_one, modSphericalI_zero]
  push_cast
  field_simp
  ring

-- no-dlmf: chain link 10.49.9 (`n = 2` closed form, assembled in modSphericalI_10_49_9)
/-- Closed form for `i₂^{(1)}(z)` at DLMF's stated complex `z`. -/
theorem modSphericalI_two_complex (z : ℂ) (hz : z ≠ 0) :
    modSphericalIC 2 z
      = (3 / z ^ 3 + 1 / z) * Complex.sinh z - 3 / z ^ 2 * Complex.cosh z := by
  have h := modSphericalI_recurrence_complex 0 z
  rw [h]
  simp only [modSphericalIC]
  field_simp
  ring

-- no-dlmf: FLMF's modSphericalK omits DLMF 10.49.13's π/2 prefactor (the
-- DLMF-faithful π/2-scaled identity is modSphericalK_10_49_13)
/-- Closed form for `k₂(z)`. -/
theorem modSphericalK_two (z : ℝ) (hz : z ≠ 0) :
    modSphericalK 2 z
      = Real.exp (-z) * (3 / z ^ 3 + 3 / z ^ 2 + 1 / z) := by
  have h := modSphericalK_recurrence 0 z
  rw [h, modSphericalK_one, modSphericalK_zero]
  push_cast
  field_simp
  ring

-- no-dlmf: chain link 10.49.13 (real/narrowed restriction; assembled, in complex
-- form, in modSphericalK_10_49_13)
/-- (`n = 2`, π/2-scaled, real `z`): `(π/2) · k₂(z) = (π/2) · e^{-z}(3/z³+3/z²+1/z)`
— i.e. `modSphericalK 2` matches DLMF's `𝗄₂` up to the `π/2` normalization
prefactor that `modSphericalK` omits. -/
theorem modSphericalK_two_dlmf (z : ℝ) (hz : z ≠ 0) :
    Real.pi / 2 * modSphericalK 2 z
      = Real.pi / 2 * (Real.exp (-z) * (3 / z ^ 3 + 3 / z ^ 2 + 1 / z)) := by
  rw [modSphericalK_two z hz]

-- no-dlmf: chain link 10.49.13 (`n = 2` closed form, π/2-scaled, assembled in
-- modSphericalK_10_49_13)
/-- (`n = 2`, π/2-scaled) — at DLMF's stated complex `z`:
`(π/2) · k₂(z) = (π/2) · e^{-z}(3/z³+3/z²+1/z)`, i.e. `modSphericalKC 2`
matches DLMF's `𝗄₂` up to the `π/2` normalization prefactor that
`modSphericalKC` (mirroring `modSphericalK`) omits. -/
theorem modSphericalK_two_complex (z : ℂ) (hz : z ≠ 0) :
    (Real.pi : ℂ) / 2 * modSphericalKC 2 z
      = (Real.pi : ℂ) / 2 * (Complex.exp (-z) * (3 / z ^ 3 + 3 / z ^ 2 + 1 / z)) := by
  have hK : modSphericalKC 2 z
      = Complex.exp (-z) * (3 / z ^ 3 + 3 / z ^ 2 + 1 / z) := by
    simp only [modSphericalKC]
    field_simp
    ring
  rw [hK]

/-- **DLMF 10.49.9** — the `n = 0, 1, 2` closed forms of `i_n^{(1)}(z)` at DLMF's
stated complex `z`: `i₀^{(1)}(z) = sinh z / z`, `i₁^{(1)}(z) = -sinh z/z² + cosh z/z`,
`i₂^{(1)}(z) = (1/z + 3/z³) sinh z - 3/z² cosh z`.
DAG: E-10.49.9.
Fidelity: tier1 unable (conjunction-partial)
Verified: unverified
-/
theorem modSphericalI_10_49_9 (z : ℂ) (hz : z ≠ 0) :
    modSphericalIC 0 z = Complex.sinh z / z ∧
      modSphericalIC 1 z = Complex.cosh z / z - Complex.sinh z / z ^ 2 ∧
      modSphericalIC 2 z
        = (3 / z ^ 3 + 1 / z) * Complex.sinh z - 3 / z ^ 2 * Complex.cosh z :=
  ⟨modSphericalI_zero_complex z, modSphericalI_one_complex z, modSphericalI_two_complex z hz⟩

/-- **DLMF 10.49.13** — the `n = 0, 1, 2` closed forms of `𝗄_n(z)` at DLMF's stated
complex `z`, π/2-scaled (`modSphericalKC` omits DLMF's `π/2` normalization prefactor):
`𝗄₀(z) = (π/2)e^{-z}/z`, `𝗄₁(z) = (π/2)e^{-z}(1/z+1/z²)`,
`𝗄₂(z) = (π/2)e^{-z}(1/z+3/z²+3/z³)`.
DAG: E-10.49.13.
Fidelity: tier1 unable (conjunction-partial)
Verified: unverified
-/
theorem modSphericalK_10_49_13 (z : ℂ) (hz : z ≠ 0) :
    (Real.pi : ℂ) / 2 * modSphericalKC 0 z = (Real.pi : ℂ) / 2 * (Complex.exp (-z) / z) ∧
      (Real.pi : ℂ) / 2 * modSphericalKC 1 z
        = (Real.pi : ℂ) / 2 * (Complex.exp (-z) / z + Complex.exp (-z) / z ^ 2) ∧
      (Real.pi : ℂ) / 2 * modSphericalKC 2 z
        = (Real.pi : ℂ) / 2 * (Complex.exp (-z) * (3 / z ^ 3 + 3 / z ^ 2 + 1 / z)) :=
  ⟨modSphericalK_zero_complex z, modSphericalK_one_complex z, modSphericalK_two_complex z hz⟩

/-! ## Derivatives of the base cases (DLMF 10.51.5 with `n = 0`)

These verify the standard derivative recurrence `f₀'(z) = f₁(z)` for `i` and
`f₀'(z) = -f₁(z)` for `k`.

NOTE (mistag correction, found while migrating DLMF 10.51.6 to the
one-conjunction convention): the two theorems below were previously tagged
`DAG: E-10.51.6`. Checked directly against `https://dlmf.nist.gov/10.51` (table
ids `E5`/`E6`): DLMF 10.51.6 is the unrelated `(1/z d/dz)^m` iterated-operator
(Rayleigh-type) formula `(1/z·d/dz)^m(z^{n+1}g_n(z)) = z^{n-m+1}g_{n-m}(z)`
(`m = 0,…,n`) together with `(1/z·d/dz)^m(z^{-n}g_n(z)) = z^{-n-m}g_{n+m}(z)`
(`m = 0,1,…`) — no sign alternation for the modified (`g_n`) family, unlike its
`f_n` counterpart 10.51.3. These two base-case derivative identities are instead
the `n = 0` row-b instance of DLMF **10.51.5** (`g_n'(z) = g_{n+1}(z) + (n/z)g_n(z)`,
`n = 0,1,…`, confirmed against the same page's `E5` table). Retagging to 10.51.5
under the one-conjunction convention is out of scope for this 10.51.6 migration
pass (10.51.5 was not one of the tags assigned), so the tag is removed here
rather than left pointing at the wrong equation. -/

-- no-dlmf: raw derivative computation of the base case (feeds the 10.51.5
-- derivative relation below; retagging to 10.51.5 is out of scope for this pass)
/-- `d/dz (sinh z / z) = cosh z / z - sinh z / z²`, valid for `z ≠ 0`. -/
theorem hasDerivAt_modSphericalI_zero (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalI 0) (Real.cosh z / z - Real.sinh z / z ^ 2) z := by
  have hd : HasDerivAt (fun z : ℝ => Real.sinh z / z)
      ((Real.cosh z * z - Real.sinh z * 1) / z ^ 2) z :=
    (Real.hasDerivAt_sinh z).div (hasDerivAt_id z) hz
  have he : (Real.cosh z * z - Real.sinh z * 1) / z ^ 2
      = Real.cosh z / z - Real.sinh z / z ^ 2 := by
    field_simp
  rw [he] at hd
  simpa only [modSphericalI] using hd

-- no-dlmf: MISTAGGED as 10.51.6 in the previous pass (see the section note
-- above); this is actually DLMF 10.51.5's `g_n'=g_{n+1}+(n/z)g_n` row at `n = 0`,
-- specialized to `g_n = i_n^{(1)}`. Retagging to 10.51.5 is out of scope for this
-- 10.51.6 migration pass.
/-- The derivative recurrence for `i`: `i₀'(z) = i₁(z)`. -/
theorem hasDerivAt_modSphericalI_zero' (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalI 0) (modSphericalI 1 z) z := by
  simpa only [modSphericalI_one] using hasDerivAt_modSphericalI_zero z hz

-- no-dlmf: raw derivative computation of the base case (feeds the 10.51.5
-- derivative relation below; retagging to 10.51.5 is out of scope for this pass)
/-- `d/dz (e^{-z}/z) = -e^{-z}/z - e^{-z}/z²`, valid for `z ≠ 0`. -/
theorem hasDerivAt_modSphericalK_zero (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalK 0)
      (-(Real.exp (-z) / z) - Real.exp (-z) / z ^ 2) z := by
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    have := (Real.hasDerivAt_exp (-z)).comp z ((hasDerivAt_id z).neg)
    simpa using this
  have hd : HasDerivAt (fun z : ℝ => Real.exp (-z) / z)
      ((-Real.exp (-z) * z - Real.exp (-z) * 1) / z ^ 2) z :=
    hexp.div (hasDerivAt_id z) hz
  have he : (-Real.exp (-z) * z - Real.exp (-z) * 1) / z ^ 2
      = -(Real.exp (-z) / z) - Real.exp (-z) / z ^ 2 := by
    field_simp
  rw [he] at hd
  simpa only [modSphericalK] using hd

-- no-dlmf: MISTAGGED as 10.51.6 in the previous pass (see the section note
-- above); this is actually DLMF 10.51.5's `g_n'=g_{n+1}+(n/z)g_n` row at `n = 0`,
-- specialized to `g_n = (-1)^n k_n`. Retagging to 10.51.5 is out of scope for
-- this 10.51.6 migration pass.
/-- The derivative recurrence for `k`: `k₀'(z) = -k₁(z)`. -/
theorem hasDerivAt_modSphericalK_zero' (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt (modSphericalK 0) (-(modSphericalK 1 z)) z := by
  have h := hasDerivAt_modSphericalK_zero z hz
  rw [modSphericalK_one]
  convert h using 1
  ring

end FLMF.Bessel
