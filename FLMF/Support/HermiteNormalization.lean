import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hermite polynomials: explicit normalization constants (DLMF §18.3)

DLMF §18.3 (table) records, among the "standardizations" of the classical
orthogonal polynomials, the explicit normalization data of the Hermite family.
For the **physicists' Hermite polynomials** `Hₙ` the table entry is the leading
coefficient

```
kₙ = 2 ^ n,
```

while the **probabilists' Hermite polynomials** `Heₙ` (the version `hermite n`
implemented in Mathlib) are monic,

```
kₙ = 1.
```

The two families are related by the classical scaling
`Hₙ(x) = 2 ^ (n/2) · Heₙ(√2 · x)`.  At the level of polynomials with integer
coefficients we capture this rescaling by the substitution `X ↦ 2 X`, which
turns the monic `hermite n` into a degree-`n` polynomial whose leading coefficient
is exactly the DLMF normalization constant `2 ^ n`.

## Main definitions

* `physHermite n` : the rescaled Hermite polynomial `(hermite n).comp (2 X) = Heₙ(2X)`,
  carrying the physicists' *leading coefficient* `2 ^ n`.  **This is not `Hₙ`** — see
  the caveat on its docstring and `docs/ERRATA.md` (`physhermite-not-physicist`).
* `physicistsHermite n` : the genuine **physicists' Hermite polynomial** `Hₙ`,
  defined by the classical three-term recurrence
  `H₀ = 1`, `H₁ = 2X`, `H_{n+2} = 2X·H_{n+1} − 2(n+1)·Hₙ`.

## Main results

* `leadingCoeff_probHermite` (from Mathlib): `Heₙ` is monic, `kₙ = 1`.
* `natDegree_physHermite` : `physHermite n` has degree `n`.
* `leadingCoeff_physHermite` : the leading coefficient of `physHermite n` is `2 ^ n`
  — the DLMF §18.3 normalization constant for physicists' Hermite polynomials.
* `coeff_physHermite_self` : the top coefficient `coeff (physHermite n) n = 2 ^ n`.
* `derivative_physicistsHermite` : `H′_{n+1} = 2(n+1)·Hₙ`.
* `physicistsHermite_succ` : `H_{n+1} = 2X·Hₙ − H′ₙ`.
* `hasDerivAt_aeval_physicistsHermite_mul_cexp` / `…_mul_exp` : the Rodrigues-type
  differentiation step `d/dz (Hₙ(z) e^{−z²}) = −H_{n+1}(z) e^{−z²}` over `ℂ` and `ℝ`,
  the engine behind DLMF 7.10.1 and 7.18.8.
-/

open Polynomial

namespace FLMF.Functions.Hermite

/-- The **rescaled (physicists'-normalized) Hermite polynomial** obtained from
Mathlib's monic probabilists' Hermite polynomial `hermite n` by the substitution
`X ↦ 2 X`.

This is the polynomial-level shadow of the scaling `Hₙ(x) = 2 ^ (n/2) · Heₙ(√2 · x)`:
the substitution multiplies the (degree-`n`) leading term by `2 ^ n`, producing
the physicists' normalization constant `kₙ = 2 ^ n` of DLMF 18.3.

**Caveat (docs/ERRATA.md, `physhermite-not-physicist`).** `physHermite n` is
`Heₙ(2X)`, **not** DLMF's physicists' Hermite polynomial `Hₙ(X)`: the two share the
leading coefficient `2 ^ n` (which is all this definition is for) but differ in the
lower-order terms from `n = 2` on — `physHermite 2 = 4X² − 1` whereas
`H₂ = 4X² − 2`.  Anything that needs the actual `Hₙ` must use `physicistsHermite`
below. -/
-- no-dlmf: rescaled-Hermite definition (physicists' normalization), not an equation
noncomputable def physHermite (n : ℕ) : Polynomial ℤ :=
  (hermite n).comp (C 2 * X)

/-- `physHermite 0 = 1`. -/
-- no-dlmf: low-order value of the rescaled polynomial, structural
@[simp]
theorem physHermite_zero : physHermite 0 = 1 := by
  simp [physHermite, hermite_zero]

/-- `physHermite 1 = 2 X`, i.e. `H₁(x) = 2x`. -/
-- no-dlmf: low-order value of the rescaled polynomial, structural
theorem physHermite_one : physHermite 1 = C 2 * X := by
  rw [physHermite, hermite_one]; simp

/-- The degree of `physHermite n` is `n`. -/
-- no-dlmf: degree of the rescaled polynomial, structural
@[simp]
theorem natDegree_physHermite (n : ℕ) : (physHermite n).natDegree = n := by
  have h2 : (C (2 : ℤ) * X).natDegree = 1 := by
    rw [natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0), natDegree_X]
  rw [physHermite, natDegree_comp, natDegree_hermite, h2, mul_one]

-- no-dlmf: leading coefficient of the *rescaled* polynomial `Heₙ(2X)`, which is
-- NOT DLMF's physicists' Hermite `Hₙ` (see docs/ERRATA.md,
-- `physhermite-not-physicist`); the numerical value `2ⁿ` coincides with Table
-- 18.3.1's `kₙ` for `Hₙ` only by accident.  The genuine Table 18.3.1 rows carried
-- here are `leadingCoeff_probHermite` (`Heₙ`, `kₙ = 1`).
/-- The leading coefficient of `physHermite n = Heₙ(2X)` equals `2 ^ n`. -/
theorem leadingCoeff_physHermite (n : ℕ) : (physHermite n).leadingCoeff = 2 ^ n := by
  rw [physHermite, leadingCoeff_comp
        (by rw [natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0), natDegree_X]; exact one_ne_zero)]
  rw [leadingCoeff_hermite, one_mul, leadingCoeff_C_mul_X, natDegree_hermite]

-- no-dlmf: degree-`n` coefficient of the rescaled `Heₙ(2X)`; same caveat as
-- `leadingCoeff_physHermite` (docs/ERRATA.md `physhermite-not-physicist`) — this
-- is not Table 18.3.1's `kₙ` for the physicists' `Hₙ`.
/-- The top coefficient `coeff (physHermite n) n` of `physHermite n = Heₙ(2X)`
is `2 ^ n`. -/
theorem coeff_physHermite_self (n : ℕ) : (physHermite n).coeff n = 2 ^ n := by
  have h := leadingCoeff_physHermite n
  rwa [leadingCoeff, natDegree_physHermite] at h

/-! ## The physicists' Hermite polynomials `Hₙ`

The genuine physicists' family, defined by the classical three-term recurrence
(DLMF 18.9.1 with the §18.3 standardization; equivalently Rodrigues'
`Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`):

```
H₀ = 1,   H₁ = 2X,   H_{n+2} = 2X·H_{n+1} − 2(n+1)·Hₙ.
```

This is the family DLMF §7.10 and §7.18 refer to as `Hₙ`; it is **not**
`physHermite` above (see `docs/ERRATA.md`, `physhermite-not-physicist`). -/

/-- The **physicists' Hermite polynomials** `Hₙ ∈ ℤ[X]`, given by the three-term
recurrence `H₀ = 1`, `H₁ = 2X`, `H_{n+2} = 2X·H_{n+1} − 2(n+1)·Hₙ`.

Low-order values: `H₀ = 1`, `H₁ = 2X`, `H₂ = 4X² − 2`, `H₃ = 8X³ − 12X`. -/
-- no-dlmf: definition of the physicists' Hermite family (recurrence form), not a
-- numbered display; the equations it satisfies are surfaced separately
noncomputable def physicistsHermite : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => C 2 * X
  | (n + 2) => C 2 * X * physicistsHermite (n + 1) - C (2 * ((n : ℤ) + 1)) * physicistsHermite n

/-- `H₀ = 1`. -/
-- no-dlmf: low-order value of `physicistsHermite`, structural
@[simp]
theorem physicistsHermite_zero : physicistsHermite 0 = 1 := rfl

/-- `H₁ = 2X`. -/
-- no-dlmf: low-order value of `physicistsHermite`, structural
theorem physicistsHermite_one : physicistsHermite 1 = C 2 * X := rfl

/-- The defining three-term recurrence `H_{n+2} = 2X·H_{n+1} − 2(n+1)·Hₙ`. -/
-- no-dlmf: defining recurrence of `physicistsHermite`, structural (the DLMF display
-- 18.9.1 for the Hermite row is surfaced in the OrthogonalPolynomials lane)
theorem physicistsHermite_add_two (n : ℕ) :
    physicistsHermite (n + 2) =
      C 2 * X * physicistsHermite (n + 1) - C (2 * ((n : ℤ) + 1)) * physicistsHermite n := rfl

-- no-dlmf: two-step induction carrying the derivative identity at consecutive
-- indices (the step needs `H′ₙ` as well as `H′_{n+1}`); support for
-- `derivative_physicistsHermite`
/-- Auxiliary two-step form of the derivative identity: `H′_{n+1} = 2(n+1)Hₙ`
*and* `H′_{n+2} = 2(n+2)H_{n+1}`, proved simultaneously. -/
private theorem derivative_physicistsHermite_aux (n : ℕ) :
    derivative (physicistsHermite (n + 1)) = C (2 * ((n : ℤ) + 1)) * physicistsHermite n ∧
    derivative (physicistsHermite (n + 2)) = C (2 * ((n : ℤ) + 2)) * physicistsHermite (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [physicistsHermite_one, physicistsHermite_zero]
    · rw [physicistsHermite_add_two 0, physicistsHermite_one, physicistsHermite_zero]
      simp
      ring
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hrec2 : physicistsHermite (n + 2) =
        C 2 * X * physicistsHermite (n + 1) - C (2 * ((n : ℤ) + 1)) * physicistsHermite n :=
      physicistsHermite_add_two n
    have hrec3 : physicistsHermite (n + 1 + 2) =
        C 2 * X * physicistsHermite (n + 2)
          - C (2 * ((n : ℤ) + 2)) * physicistsHermite (n + 1) := by
      have h := physicistsHermite_add_two (n + 1)
      push_cast at h
      convert h using 3
    rw [hrec3]
    simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, ih.1, ih.2,
      zero_mul, mul_one, zero_add]
    rw [hrec2]
    simp only [map_mul, map_add, map_one, map_natCast, map_ofNat]
    push_cast
    ring

/-- **Derivative of the physicists' Hermite polynomials**: `H′_{n+1} = 2(n+1)·Hₙ`. -/
-- no-dlmf: derivative identity for `physicistsHermite`; support kit for DLMF 7.10.1
-- and 7.18.8 (the DLMF Hermite display itself lives in the §18 lane)
theorem derivative_physicistsHermite (n : ℕ) :
    derivative (physicistsHermite (n + 1)) = C (2 * ((n : ℤ) + 1)) * physicistsHermite n :=
  (derivative_physicistsHermite_aux n).1

/-- The Rodrigues-type step relation `H_{n+1} = 2X·Hₙ − H′ₙ`, valid for every `n`
(including `n = 0`, where `H′₀ = 0`). -/
-- no-dlmf: equivalent one-step form of the recurrence; support kit
theorem physicistsHermite_succ (n : ℕ) :
    physicistsHermite (n + 1) =
      C 2 * X * physicistsHermite n - derivative (physicistsHermite n) := by
  cases n with
  | zero => simp [physicistsHermite_one, physicistsHermite_zero]
  | succ m => rw [physicistsHermite_add_two m, derivative_physicistsHermite m]

section AEval

variable {R : Type*} [CommRing R]

/-- `H₀(x) = 1` in any commutative ring. -/
-- no-dlmf: evaluated form of `physicistsHermite_zero`, structural
@[simp]
theorem aeval_physicistsHermite_zero (x : R) : aeval x (physicistsHermite 0) = 1 := by
  simp [physicistsHermite_zero]

/-- `H₁(x) = 2x` in any commutative ring. -/
-- no-dlmf: evaluated form of `physicistsHermite_one`, structural
@[simp]
theorem aeval_physicistsHermite_one (x : R) : aeval x (physicistsHermite 1) = 2 * x := by
  simp [physicistsHermite_one, map_ofNat]

/-- The evaluated three-term recurrence
`H_{n+2}(x) = 2x·H_{n+1}(x) − 2(n+1)·Hₙ(x)` in any commutative ring. -/
-- no-dlmf: evaluated form of `physicistsHermite_add_two`, structural
theorem aeval_physicistsHermite_add_two (n : ℕ) (x : R) :
    aeval x (physicistsHermite (n + 2)) =
      2 * x * aeval x (physicistsHermite (n + 1))
        - 2 * ((n : R) + 1) * aeval x (physicistsHermite n) := by
  rw [physicistsHermite_add_two]
  simp only [map_sub, map_add, map_mul, map_one, map_ofNat, map_natCast, aeval_X]

/-- The evaluated derivative identity `H′_{n+1}(x) = 2(n+1)·Hₙ(x)`. -/
-- no-dlmf: evaluated form of `derivative_physicistsHermite`, structural
theorem aeval_derivative_physicistsHermite (n : ℕ) (x : R) :
    aeval x (derivative (physicistsHermite (n + 1))) =
      2 * ((n : R) + 1) * aeval x (physicistsHermite n) := by
  rw [derivative_physicistsHermite]
  simp only [map_add, map_mul, map_one, map_ofNat, map_natCast]

/-- The anchor value `H₂(x) = 4x² − 2` — the first index at which the physicists'
family separates from the rescaled `physHermite 2 = 4x² − 1`. -/
-- no-dlmf: anchor/sanity value distinguishing `physicistsHermite` from `physHermite`
theorem aeval_physicistsHermite_two (x : R) :
    aeval x (physicistsHermite 2) = 4 * x ^ 2 - 2 := by
  have h := aeval_physicistsHermite_add_two 0 x
  simp only [zero_add, Nat.cast_zero, aeval_physicistsHermite_one,
    aeval_physicistsHermite_zero, mul_one] at h
  rw [h]
  ring

end AEval

/-- **The Hermite–Gaussian differentiation step over `ℂ`**:
`d/dz (Hₙ(z)·e^{−z²}) = −H_{n+1}(z)·e^{−z²}`, from `H_{n+1} = 2z·Hₙ − H′ₙ`.
This is the engine of DLMF 7.10.1. -/
-- no-dlmf: analytic support lemma (product rule against the Gaussian); no DLMF display
theorem hasDerivAt_aeval_physicistsHermite_mul_cexp (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => aeval w (physicistsHermite n) * Complex.exp (-w ^ 2))
      (-(aeval z (physicistsHermite (n + 1))) * Complex.exp (-z ^ 2)) z := by
  have hH : HasDerivAt (fun w : ℂ => aeval w (physicistsHermite n))
      (aeval z (derivative (physicistsHermite n))) z :=
    (physicistsHermite n).hasDerivAt_aeval z
  have hg : HasDerivAt (fun w : ℂ => Complex.exp (-w ^ 2))
      (Complex.exp (-z ^ 2) * -(2 * z)) z := by
    have h : HasDerivAt (fun w : ℂ => -w ^ 2) (-(2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).neg
    simpa using h.cexp
  have h := hH.mul hg
  convert h using 1
  have hsucc : aeval z (physicistsHermite (n + 1))
      = 2 * z * aeval z (physicistsHermite n) - aeval z (derivative (physicistsHermite n)) := by
    rw [physicistsHermite_succ]
    simp only [map_sub, map_mul, map_ofNat, aeval_X]
  rw [hsucc]
  ring

/-- **The Hermite–Gaussian differentiation step over `ℝ`**:
`d/dx (Hₙ(x)·e^{−x²}) = −H_{n+1}(x)·e^{−x²}` (real instance of
`hasDerivAt_aeval_physicistsHermite_mul_cexp`). -/
-- no-dlmf: analytic support lemma (product rule against the Gaussian); no DLMF display
theorem hasDerivAt_aeval_physicistsHermite_mul_exp (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => aeval y (physicistsHermite n) * Real.exp (-y ^ 2))
      (-(aeval x (physicistsHermite (n + 1))) * Real.exp (-x ^ 2)) x := by
  have hH : HasDerivAt (fun y : ℝ => aeval y (physicistsHermite n))
      (aeval x (derivative (physicistsHermite n))) x :=
    (physicistsHermite n).hasDerivAt_aeval x
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2))
      (Real.exp (-x ^ 2) * -(2 * x)) x := by
    have h : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    simpa using h.exp
  have h := hH.mul hg
  convert h using 1
  have hsucc : aeval x (physicistsHermite (n + 1))
      = 2 * x * aeval x (physicistsHermite n) - aeval x (derivative (physicistsHermite n)) := by
    rw [physicistsHermite_succ]
    simp only [map_sub, map_mul, map_ofNat, aeval_X]
  rw [hsucc]
  ring

/-- **(DLMF 18.3, probabilists' Hermite normalization)** — the probabilists'
Hermite polynomials `Heₙ = hermite n` are monic, i.e. their leading coefficient
is `1`.

DAG: E-18.3.
Numerical: PASS
Verified: unverified
-/
theorem leadingCoeff_probHermite (n : ℕ) : (hermite n).leadingCoeff = 1 :=
  Polynomial.leadingCoeff_hermite n

end FLMF.Functions.Hermite
