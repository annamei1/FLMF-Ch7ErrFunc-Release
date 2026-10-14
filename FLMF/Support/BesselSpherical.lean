import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-
  Spherical Bessel Functions j_n, y_n

  The spherical Bessel functions of the first and second kind are defined by
    j_n(x) = sqrt(π/(2x)) J_{n+1/2}(x),    y_n(x) = sqrt(π/(2x)) Y_{n+1/2}(x).

  Since Mathlib currently has no API for the cylinder Bessel functions
  `J_ν`, `Y_ν` of half-integer order, we take the equivalent **Rayleigh
  closed-form definition** (DLMF 10.49.2/10.49.3) as our basic definition and
  develop the standard structural properties from it:

  * base cases  `j₀(x) = sin x / x`,  `y₀(x) = - cos x / x`,
                `j₁(x) = sin x / x² - cos x / x`,
                `y₁(x) = - cos x / x² - sin x / x`;
  * the three-term recurrence (DLMF 10.51.1)
        f_{n+1}(x) = ((2n+1)/x) f_n(x) - f_{n-1}(x);
  * the derivative recurrence relations (DLMF 10.51.2).

  ## References
  - DLMF Chapter 10.47-10.51: https://dlmf.nist.gov/10.47
-/

namespace FLMF.Bessel

open Real

/-! ## Definitions via the three-term recurrence

We define the spherical Bessel functions of the first and second kind by their
base cases at `n = 0, 1` together with the upward recurrence relation
`f_{n+1}(x) = ((2n+1)/x) f_n(x) - f_{n-1}(x)` (DLMF 10.51.1).  This is the
standard closed-form construction and is equivalent to the definition
`f_n(x) = sqrt(π/(2x)) C_{n+1/2}(x)` whenever `x ≠ 0`. -/

/-- DLMF 10.49.3 — Spherical Bessel function of the first kind `j_n(x)`, defined by the
upward recurrence with `j₀ = sin x / x`, `j₁ = sin x/x² - cos x/x`. -/
-- DAG: E-10.49.3.
-- Verified: unverified
noncomputable def sphericalJ : ℕ → ℝ → ℝ
  | 0, x => Real.sin x / x
  | 1, x => Real.sin x / x ^ 2 - Real.cos x / x
  | (n + 2), x =>
      (2 * (n + 1) + 1) / x * sphericalJ (n + 1) x - sphericalJ n x

/-- DLMF 10.49.5 — Spherical Bessel function of the second kind `y_n(x)`, defined by the
upward recurrence with `y₀ = - cos x / x`, `y₁ = - cos x/x² - sin x/x`. -/
-- DAG: E-10.49.5.
-- Verified: unverified
noncomputable def sphericalY : ℕ → ℝ → ℝ
  | 0, x => - Real.cos x / x
  | 1, x => - Real.cos x / x ^ 2 - Real.sin x / x
  | (n + 2), x =>
      (2 * (n + 1) + 1) / x * sphericalY (n + 1) x - sphericalY n x

/-! ## Complex-domain twin (DLMF's stated variable domain)

DLMF's `z` in Chapter 10 is a complex variable; `sphericalJ` above is restricted
to `x : ℝ` (this is the convention consumed by the real-analytic series in
`Functions/Error/Ch7Series.lean`, so that binder type is kept as-is rather than
widened in place). The function below mirrors the same recursive construction
over `ℂ`, matching DLMF's own closed-form definition (10.49.3) verbatim, and lets
displays whose DLMF form is complex — notably the Fresnel spherical-Bessel series
DLMF 7.6.10/7.6.11 — be surfaced at DLMF's full stated domain. This mirrors the
"Complex-domain twins" section of `Bessel/ModifiedSpherical.lean`
(`modSphericalIC` / `modSphericalKC`). -/

/-- Complex-domain spherical Bessel function of the first kind, mirroring
`sphericalJ` over `ℂ` (DLMF 10.49.3, complex `z`): defined by the upward
recurrence with `j₀ = sin z / z`, `j₁ = sin z/z² - cos z/z`. -/
noncomputable def sphericalJC : ℕ → ℂ → ℂ
  | 0, z => Complex.sin z / z
  | 1, z => Complex.sin z / z ^ 2 - Complex.cos z / z
  | (n + 2), z =>
      (2 * (n + 1) + 1) / z * sphericalJC (n + 1) z - sphericalJC n z

-- no-dlmf: complex-domain twin of the `sphericalJ` recurrence (definitional)
/-- Three-term recurrence for `sphericalJC` (the defining equation). -/
theorem sphericalJC_recurrence (n : ℕ) (z : ℂ) :
    sphericalJC (n + 2) z = (2 * (n + 1) + 1) / z * sphericalJC (n + 1) z
      - sphericalJC n z := rfl

-- no-dlmf: real-agreement bridge between `sphericalJC` and `sphericalJ`, support lemma
/-- **Agreement with the real `sphericalJ`.** `sphericalJC n ↑x = ↑(sphericalJ n x)`
(the junk values at `x = 0` agree as well, since `w / 0 = 0` on both sides). -/
theorem sphericalJC_ofReal (n : ℕ) (x : ℝ) :
    sphericalJC n (x : ℂ) = ((sphericalJ n x : ℝ) : ℂ) := by
  suffices h : ∀ m : ℕ,
      sphericalJC m (x : ℂ) = ((sphericalJ m x : ℝ) : ℂ) ∧
        sphericalJC (m + 1) (x : ℂ) = ((sphericalJ (m + 1) x : ℝ) : ℂ) from (h n).1
  intro m
  induction m with
  | zero =>
      constructor
      · show Complex.sin (x : ℂ) / (x : ℂ) = ((Real.sin x / x : ℝ) : ℂ)
        push_cast
        ring
      · show Complex.sin (x : ℂ) / (x : ℂ) ^ 2 - Complex.cos (x : ℂ) / (x : ℂ)
          = ((Real.sin x / x ^ 2 - Real.cos x / x : ℝ) : ℂ)
        push_cast
        ring
  | succ p ih =>
      refine ⟨ih.2, ?_⟩
      have hrecR : sphericalJ (p + 2) x
          = (2 * ((p : ℝ) + 1) + 1) / x * sphericalJ (p + 1) x - sphericalJ p x := rfl
      rw [sphericalJC_recurrence, ih.1, ih.2, hrecR]
      push_cast
      ring

-- no-dlmf: parity `j_n(-z) = (-1)^n j_n(z)` of the complex spherical Bessel
-- function; support lemma for the Fresnel series DLMF 7.6.10/7.6.11
/-- **Parity.** `j_n(-z) = (-1)ⁿ j_n(z)`. -/
theorem sphericalJC_neg (n : ℕ) (z : ℂ) :
    sphericalJC n (-z) = (-1) ^ n * sphericalJC n z := by
  suffices h : ∀ m : ℕ,
      sphericalJC m (-z) = (-1) ^ m * sphericalJC m z ∧
        sphericalJC (m + 1) (-z) = (-1) ^ (m + 1) * sphericalJC (m + 1) z from (h n).1
  intro m
  induction m with
  | zero =>
      constructor
      · show Complex.sin (-z) / (-z) = (-1) ^ (0 : ℕ) * (Complex.sin z / z)
        rw [Complex.sin_neg, neg_div_neg_eq]
        ring
      · show Complex.sin (-z) / (-z) ^ 2 - Complex.cos (-z) / (-z)
          = (-1) ^ (1 : ℕ) * (Complex.sin z / z ^ 2 - Complex.cos z / z)
        rw [Complex.sin_neg, Complex.cos_neg, neg_sq, div_neg]
        ring
  | succ p ih =>
      refine ⟨ih.2, ?_⟩
      rw [sphericalJC_recurrence, sphericalJC_recurrence, ih.1, ih.2, div_neg]
      ring

/-! ## Base cases (DLMF 10.49.3, 10.49.5) -/

-- no-dlmf: chain link 10.49.3 (assembled in sphericalJ_10_49_3)
/-- `j₀(x) = sin x / x`. -/
@[simp] theorem sphericalJ_zero (x : ℝ) : sphericalJ 0 x = Real.sin x / x := rfl

-- no-dlmf: chain link 10.49.3 (assembled in sphericalJ_10_49_3)
/-- `j₁(x) = sin x / x² - cos x / x`. -/
@[simp] theorem sphericalJ_one (x : ℝ) :
    sphericalJ 1 x = Real.sin x / x ^ 2 - Real.cos x / x := rfl

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 10.49.5
-- surface is sphericalY_zero_dlmf
/-- `y₀(x) = - cos x / x`. -/
@[simp] theorem sphericalY_zero (x : ℝ) : sphericalY 0 x = - Real.cos x / x := rfl

-- no-dlmf: chain link 10.49.5 (assembled in sphericalY_10_49_5)
/-- `y₀(x) = - cos x / x` (DLMF-faithful restriction of
`sphericalY_zero`: `x ≠ 0`). -/
theorem sphericalY_zero_dlmf (x : ℝ) (hx : x ≠ 0) :
    sphericalY 0 x = - Real.cos x / x := sphericalY_zero x

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 10.49.5
-- surface is sphericalY_one_dlmf
/-- `y₁(x) = - cos x / x² - sin x / x`. -/
@[simp] theorem sphericalY_one (x : ℝ) :
    sphericalY 1 x = - Real.cos x / x ^ 2 - Real.sin x / x := rfl

-- no-dlmf: chain link 10.49.5 (assembled in sphericalY_10_49_5)
/-- `y₁(x) = - cos x / x² - sin x / x` (DLMF-faithful
restriction of `sphericalY_one`: `x ≠ 0`). -/
theorem sphericalY_one_dlmf (x : ℝ) (hx : x ≠ 0) :
    sphericalY 1 x = - Real.cos x / x ^ 2 - Real.sin x / x := sphericalY_one x

/-! ## Three-term recurrence (DLMF 10.51.1)

`f_{n-1}(x) + f_{n+1}(x) = ((2n+1)/x) f_n(x)`, i.e.
`f_{n+1}(x) = ((2n+1)/x) f_n(x) - f_{n-1}(x)`. -/

-- no-dlmf: instance of DLMF 10.51.1 (f = j only, three-term display only); faithful surface is spherical_recurrence
/-- Three-term recurrence for `j_n`:
`j_{n+2}(x) = ((2(n+1)+1)/x) j_{n+1}(x) - j_n(x)`. -/
theorem sphericalJ_recurrence (n : ℕ) (x : ℝ) :
    sphericalJ (n + 2) x = (2 * (n + 1) + 1) / x * sphericalJ (n + 1) x
      - sphericalJ n x := rfl

-- no-dlmf: instance of DLMF 10.51.1 (f = y only, three-term display only); faithful surface is spherical_recurrence
/-- Three-term recurrence for `y_n`:
`y_{n+2}(x) = ((2(n+1)+1)/x) y_{n+1}(x) - y_n(x)`. -/
theorem sphericalY_recurrence (n : ℕ) (x : ℝ) :
    sphericalY (n + 2) x = (2 * (n + 1) + 1) / x * sphericalY (n + 1) x
      - sphericalY n x := rfl

-- no-dlmf: instance of DLMF 10.51.1 (f = j only, symmetric two-term display, real x);
-- faithful surface is spherical_recurrence
/-- The symmetric form of the recurrence for `j_n`:
`j_{n-1}(x) + j_{n+1}(x) = ((2n+1)/x) j_n(x)`. -/
theorem sphericalJ_recurrence' (n : ℕ) (x : ℝ) :
    sphericalJ n x + sphericalJ (n + 2) x
      = (2 * (n + 1) + 1) / x * sphericalJ (n + 1) x := by
  rw [sphericalJ_recurrence]; ring

-- no-dlmf: instance of DLMF 10.51.1 (f = y only, three-term display only); faithful surface is spherical_recurrence
/-- Symmetric form of the recurrence for `y_n`:
`y_{n-1}(x) + y_{n+1}(x) = ((2n+1)/x) y_n(x)`. -/
theorem sphericalY_recurrence' (n : ℕ) (x : ℝ) :
    sphericalY n x + sphericalY (n + 2) x
      = (2 * (n + 1) + 1) / x * sphericalY (n + 1) x := by
  rw [sphericalY_recurrence]; ring

/-- **DLMF 10.51.1** — recurrence relations for a general spherical Bessel
function: for `f_n` any of `j_n`, `y_n`, `h⁽¹⁾_n = j_n + i y_n`,
`h⁽²⁾_n = j_n − i y_n` (DLMF §10.47(ii)) and `n = 1, 2, …`, both displays
`f_{n-1}(x) + f_{n+1}(x) = ((2n+1)/x) f_n(x)` and
`n f_{n-1}(x) − (n+1) f_{n+1}(x) = (2n+1) f_n'(x)` hold (stated at index
`n + 1` so that the DLMF constraint `n ≥ 1` is automatic; stated on the real
line `x ≠ 0`, values in `ℂ` so that the Hankel members are expressible).

DAG: E-10.51.1.
Numerical: N/A (conjunction-partial)
Verified: unverified
-/
theorem spherical_recurrence (f : ℕ → ℝ → ℂ)
    (hf : f = (fun n x => (sphericalJ n x : ℂ)) ∨
          f = (fun n x => (sphericalY n x : ℂ)) ∨
          f = (fun n x => (sphericalJ n x : ℂ) + Complex.I * sphericalY n x) ∨
          f = (fun n x => (sphericalJ n x : ℂ) - Complex.I * sphericalY n x))
    (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    f n x + f (n + 2) x = (2 * (n : ℂ) + 3) / (x : ℂ) * f (n + 1) x ∧
    ((n : ℂ) + 1) * f n x - ((n : ℂ) + 2) * f (n + 2) x
      = (2 * (n : ℂ) + 3) * deriv (f (n + 1)) x := by
  sorry

/-! ## Closed form for `j₂`, `y₂` (DLMF 10.49.3) -/

-- no-dlmf: chain link 10.49.3 (assembled in sphericalJ_10_49_3)
/-- closed form for `j₂`. -/
theorem sphericalJ_two (x : ℝ) (hx : x ≠ 0) :
    sphericalJ 2 x = (3 / x ^ 3 - 1 / x) * Real.sin x - 3 / x ^ 2 * Real.cos x := by
  have h := sphericalJ_recurrence 0 x
  rw [h, sphericalJ_one, sphericalJ_zero]
  push_cast
  field_simp
  ring

/-- DLMF 10.49.3 — the three-row display giving closed forms for `j₀`, `j₁`,
and `j₂` (assembled from `sphericalJ_zero`, `sphericalJ_one`,
`sphericalJ_two`).
DAG: E-10.49.3.
Numerical: PASS
Verified: unverified
-/
theorem sphericalJ_10_49_3 (x : ℝ) (hx : x ≠ 0) :
    sphericalJ 0 x = Real.sin x / x ∧
      sphericalJ 1 x = Real.sin x / x ^ 2 - Real.cos x / x ∧
      sphericalJ 2 x = (3 / x ^ 3 - 1 / x) * Real.sin x - 3 / x ^ 2 * Real.cos x :=
  ⟨sphericalJ_zero x, sphericalJ_one x, sphericalJ_two x hx⟩

-- no-dlmf: chain link 10.49.5 (assembled in sphericalY_10_49_5)
/-- closed form for `y₂`. -/
theorem sphericalY_two (x : ℝ) (hx : x ≠ 0) :
    sphericalY 2 x = (-3 / x ^ 3 + 1 / x) * Real.cos x - 3 / x ^ 2 * Real.sin x := by
  have h := sphericalY_recurrence 0 x
  rw [h, sphericalY_one, sphericalY_zero]
  push_cast
  field_simp
  ring

/-- DLMF 10.49.5 — the three-row display giving closed forms for `y₀`, `y₁`,
and `y₂` (assembled from `sphericalY_zero_dlmf`, `sphericalY_one_dlmf`,
`sphericalY_two`).
DAG: E-10.49.5.
Numerical: PASS
Verified: unverified
-/
theorem sphericalY_10_49_5 (x : ℝ) (hx : x ≠ 0) :
    sphericalY 0 x = - Real.cos x / x ∧
      sphericalY 1 x = - Real.cos x / x ^ 2 - Real.sin x / x ∧
      sphericalY 2 x = (-3 / x ^ 3 + 1 / x) * Real.cos x - 3 / x ^ 2 * Real.sin x :=
  ⟨sphericalY_zero_dlmf x hx, sphericalY_one_dlmf x hx, sphericalY_two x hx⟩

/-! ## Derivative of the base cases

These verify the standard derivative recurrence
`f₀'(x) = - f₁(x)` (DLMF 10.51.2 with `n = 0`). -/

-- no-dlmf: instance of DLMF 10.51.2 (n = 0, f = j; raw base-case derivative); faithful surface is spherical_deriv_recurrence
/-- `d/dx (sin x / x) = cos x / x - sin x / x²`, valid for `x ≠ 0`
(establishes `j₀'(x) = -j₁(x)`). -/
theorem hasDerivAt_sphericalJ_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (sphericalJ 0) (Real.cos x / x - Real.sin x / x ^ 2) x := by
  have hd : HasDerivAt (fun x : ℝ => Real.sin x / x)
      ((Real.cos x * x - Real.sin x * 1) / x ^ 2) x :=
    (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have he : (Real.cos x * x - Real.sin x * 1) / x ^ 2
      = Real.cos x / x - Real.sin x / x ^ 2 := by
    field_simp
  rw [he] at hd
  simpa only [sphericalJ] using hd

-- no-dlmf: instance of DLMF 10.51.2 (n = 0, f = y; raw base-case derivative); faithful surface is spherical_deriv_recurrence
/-- `d/dx (- cos x / x) = sin x / x + cos x / x²`, valid for `x ≠ 0`
(establishes `y₀'(x) = -y₁(x)`). -/
theorem hasDerivAt_sphericalY_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (sphericalY 0) (Real.sin x / x + Real.cos x / x ^ 2) x := by
  have hd : HasDerivAt (fun x : ℝ => - Real.cos x / x)
      ((-(- Real.sin x) * x - (- Real.cos x) * 1) / x ^ 2) x := by
    have h1 : HasDerivAt (fun x : ℝ => - Real.cos x) (- (- Real.sin x)) x :=
      (Real.hasDerivAt_cos x).neg
    exact h1.div (hasDerivAt_id x) hx
  have he : (-(- Real.sin x) * x - (- Real.cos x) * 1) / x ^ 2
      = Real.sin x / x + Real.cos x / x ^ 2 := by
    field_simp; ring
  rw [he] at hd
  simpa only [sphericalY] using hd

-- no-dlmf: instance of DLMF 10.51.2 (n = 0, f = j); faithful surface is spherical_deriv_recurrence
/-- Derivative recurrence at `n = 0`: `j₀'(x) = - j₁(x)`. -/
theorem deriv_sphericalJ_zero (x : ℝ) (hx : x ≠ 0) :
    deriv (sphericalJ 0) x = - sphericalJ 1 x := by
  rw [(hasDerivAt_sphericalJ_zero x hx).deriv, sphericalJ_one]
  ring

-- no-dlmf: instance of DLMF 10.51.2 (n = 0, f = y); faithful surface is spherical_deriv_recurrence
/-- Derivative recurrence at `n = 0`: `y₀'(x) = - y₁(x)`. -/
theorem deriv_sphericalY_zero (x : ℝ) (hx : x ≠ 0) :
    deriv (sphericalY 0) x = - sphericalY 1 x := by
  rw [(hasDerivAt_sphericalY_zero x hx).deriv, sphericalY_one]
  ring

/-- **DLMF 10.51.2** — derivative recurrences for a general spherical Bessel
function: for `f_n` any of `j_n`, `y_n`, `h⁽¹⁾_n = j_n + i y_n`,
`h⁽²⁾_n = j_n − i y_n` (DLMF §10.47(ii)),
`f_n'(x) = f_{n-1}(x) − ((n+1)/x) f_n(x)` for `n = 1, 2, …` (stated at index
`n + 1` so the constraint is automatic) and
`f_n'(x) = −f_{n+1}(x) + (n/x) f_n(x)` for `n = 0, 1, …` (stated on the real
line `x ≠ 0`, values in `ℂ` so that the Hankel members are expressible).

DAG: E-10.51.2.
Numerical: N/A (conjunction-partial)
Verified: unverified
-/
theorem spherical_deriv_recurrence (f : ℕ → ℝ → ℂ)
    (hf : f = (fun n x => (sphericalJ n x : ℂ)) ∨
          f = (fun n x => (sphericalY n x : ℂ)) ∨
          f = (fun n x => (sphericalJ n x : ℂ) + Complex.I * sphericalY n x) ∨
          f = (fun n x => (sphericalJ n x : ℂ) - Complex.I * sphericalY n x))
    (x : ℝ) (hx : x ≠ 0) :
    (∀ n : ℕ, deriv (f (n + 1)) x
        = f n x - ((n : ℂ) + 2) / (x : ℂ) * f (n + 1) x) ∧
    (∀ n : ℕ, deriv (f n) x
        = - f (n + 1) x + (n : ℂ) / (x : ℂ) * f n x) := by
  sorry

end FLMF.Bessel
