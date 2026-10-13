/-
  Chebyshev Polynomials

  Classical identities for Chebyshev polynomials of the first and second kind,
  wrapping Mathlib results:

  C1:  T_n(cos θ) = cos(nθ)                (trigonometric definition)
  C2:  U_n(cos θ) sin θ = sin((n+1)θ)      (second kind trig definition)
  C3:  T_n(cosh θ) = cosh(nθ)              (hyperbolic version)
  C4:  U_n(cosh θ) sinh θ = sinh((n+1)θ)   (hyperbolic second kind)
  C5:  T_{n+2}(x) = 2x T_{n+1}(x) - T_n(x) (three-term recurrence)
  C6:  U_{n+2}(x) = 2x U_{n+1}(x) - U_n(x) (second kind recurrence)
  C7:  T_n(1) = 1                           (evaluation at 1)
  C8:  U_n(1) = n + 1                       (evaluation at 1)
  C9:  2 T_m T_k = T_{m+k} + T_{m-k}       (product-to-sum)
  C10: T_{mn} = T_m ∘ T_n                   (composition semigroup)
  C11: |T_n(x)| ≤ 1 for x ∈ [-1,1]         (pointwise bound)
  C12: T_n'(1) = n²                         (derivative at endpoint)
  C13: ∫ T_n T_m dμ_T = 0 for n ≠ m        (orthogonality)
  C14: ∫ T_0² dμ_T = π                      (norm squared, n=0)
  C15: ∫ T_n² dμ_T = π/2 for n ≥ 1         (norm squared)
  C16: T_n(-x) = (-1)^n T_n(x)             (parity)
  C17: T_n(-1) = (-1)^n                     (evaluation at -1)
  C18: T_n(0) = (-1)^(n/2) or 0            (evaluation at 0)

  References:
  - DLMF 18.3: Definition of Classical OPs
  - DLMF 18.7: Interrelations of Classical OPs
  - Abramowitz & Stegun §22
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import FLMF.Functions.Chebyshev.Values
import FLMF.Functions.Chebyshev.ProductToSum
import FLMF.Functions.Chebyshev.Deriv
import FLMF.Functions.Chebyshev.DiffEq
import FLMF.Functions.Chebyshev.Normalization
import FLMF.Functions.Chebyshev.GeneratingFunction
import FLMF.Functions.Chebyshev.SumRule
import FLMF.Functions.Chebyshev.Minimax
import FLMF.Functions.Chebyshev.Rodrigues
import FLMF.Functions.Chebyshev.Zeros
import FLMF.Functions.Chebyshev.EndpointValues

open Polynomial.Chebyshev Polynomial Real Set MeasureTheory

namespace FLMF.Functions.Chebyshev

/-! ## Trigonometric Connection -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.5.1
-- surface is T_cos_nat
/-- **C1**: T_n(cos θ) = cos(nθ).
    The defining property of Chebyshev polynomials of the first kind. -/
theorem T_cos (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (cos θ) = cos (↑n * θ) :=
  T_real_cos θ n

/-- **DLMF 18.5.1** — T_n(cos θ) = cos(nθ) = ½(zⁿ+z⁻ⁿ) with `z = e^{iθ}`
(so `x = cos θ = ½(z+z⁻¹)`), as the display's 2-link conjunction
(DLMF-faithful restriction of `T_cos`: `n : ℕ`).
The second link is the `z = e^{iθ}` instance of `Complex.cos`'s definition
via `Complex.exp`.

DLMF 18.5.1.
DAG: E-18.5.1.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem T_cos_nat (n : ℕ) (θ : ℝ) :
    ((T ℝ (n : ℤ)).eval (cos θ) = cos (((n : ℤ) : ℝ) * θ)) ∧
      ((cos (((n : ℤ) : ℝ) * θ) : ℂ) =
        1 / 2 * (Complex.exp (Complex.I * θ) ^ n +
          (Complex.exp (Complex.I * θ))⁻¹ ^ n)) := by
  refine ⟨T_cos (n : ℤ) θ, ?_⟩
  push_cast [Complex.ofReal_cos]
  unfold Complex.cos
  rw [show (Complex.exp (Complex.I * θ))⁻¹ = Complex.exp (-(Complex.I * θ)) from
      (Complex.exp_neg _).symm,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e1 : Complex.exp (((n : ℂ) * θ) * Complex.I) = Complex.exp ((n : ℂ) * (Complex.I * θ)) := by
    congr 1; ring
  have e2 : Complex.exp (-((n : ℂ) * θ) * Complex.I) =
      Complex.exp ((n : ℂ) * -(Complex.I * θ)) := by
    congr 1; ring
  rw [e1, e2]
  ring

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.5.2
-- surface is U_cos_sin_nat
/-- **C2**: U_n(cos θ) sin θ = sin((n+1)θ).
    The defining property of Chebyshev polynomials of the second kind. -/
theorem U_cos_sin (n : ℤ) (θ : ℝ) :
    (U ℝ n).eval (cos θ) * sin θ = sin ((↑n + 1) * θ) :=
  U_real_cos θ n

/-- **DLMF 18.5.2** — U_n(cos θ) sin θ = sin((n+1)θ) = ½(z^{n+1}-z^{-(n+1)})/(z-z⁻¹)
form with `z = e^{iθ}`, as the display's 2-link conjunction (DLMF-faithful
restriction of `U_cos_sin`: `n : ℕ`, `sin θ ≠ 0` — DLMF states the first link
as the quotient `U_n(x) = sin((n+1)θ)/sin θ`, undefined at `sin θ = 0`; this
is the equivalent cross-multiplied form under that same domain restriction).
The second link is likewise stated cross-multiplied
(`sin((n+1)θ)·(z-z⁻¹) = sin θ·(z^{n+1}-z^{-(n+1)})`), the `z = e^{iθ}`
instance of `Complex.sin`'s definition via `Complex.exp` — a pure algebraic
identity that needs no side nonvanishing hypothesis.

DLMF 18.5.2.
DAG: E-18.5.2.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_cos_sin_nat (n : ℕ) (θ : ℝ) (_hθ : sin θ ≠ 0) :
    ((U ℝ (n : ℤ)).eval (cos θ) * sin θ = sin ((((n : ℤ) : ℝ) + 1) * θ)) ∧
      ((sin ((((n : ℤ) : ℝ) + 1) * θ) : ℂ) *
          (Complex.exp (Complex.I * θ) - (Complex.exp (Complex.I * θ))⁻¹) =
        (sin θ : ℂ) * (Complex.exp (Complex.I * θ) ^ (n + 1) -
          (Complex.exp (Complex.I * θ))⁻¹ ^ (n + 1))) := by
  refine ⟨U_cos_sin (n : ℤ) θ, ?_⟩
  have hinv : (Complex.exp (Complex.I * θ))⁻¹ = Complex.exp (-(Complex.I * θ)) :=
    (Complex.exp_neg _).symm
  have hpow : ∀ φ : ℂ, Complex.exp φ ^ (n + 1) = Complex.exp (((n : ℂ) + 1) * φ) := by
    intro φ
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  push_cast [Complex.ofReal_sin]
  unfold Complex.sin
  rw [hinv, hpow, hpow]
  have e1 : Complex.exp (-(((n : ℂ) + 1) * θ) * Complex.I) =
      Complex.exp (((n : ℂ) + 1) * -(Complex.I * θ)) := by
    congr 1; ring
  have e2 : Complex.exp ((((n : ℂ) + 1) * θ) * Complex.I) =
      Complex.exp (((n : ℂ) + 1) * (Complex.I * θ)) := by
    congr 1; ring
  rw [e1, e2]
  ring

/-! ## Hyperbolic Connection -/

-- no-dlmf: strictly-more-general total/junk-value form; the (also no-dlmf)
-- `ℕ`-restricted specialization is `T_cosh_nat`
/-- **C3**: T_n(cosh θ) = cosh(nθ) (hyperbolic z = e^θ instance of the
    z-form ½(zⁿ+z⁻ⁿ) displayed in that equation). -/
theorem T_cosh (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval (cosh θ) = cosh (↑n * θ) :=
  T_real_cosh θ n

-- no-dlmf: real hyperbolic (z = e^θ, θ real) instance of DLMF 18.5.1's
-- z-parametrized equality, not the displayed cos-form relation itself and
-- narrower than DLMF's complex-z domain (Tier-2 audit 2026-08-07); the
-- faithful surface of DLMF 18.5.1 is `T_cos_nat`.
/-- T_n(cosh θ) = cosh(nθ), hyperbolic z = e^θ instance (`n : ℕ` restriction
of `T_cosh`). -/
theorem T_cosh_nat (n : ℕ) (θ : ℝ) :
    (T ℝ (n : ℤ)).eval (cosh θ) = cosh (((n : ℤ) : ℝ) * θ) :=
  T_cosh (n : ℤ) θ

-- no-dlmf: strictly-more-general total/junk-value form (quantifies over all
-- `n : ℤ`, including negative `n`, which DLMF 18.5.2 does not cover); the
-- (also no-dlmf) `ℕ`-restricted specialization is `U_cosh_sinh_nat`.
/-- **C4**: U_n(cosh θ) sinh θ = sinh((n+1)θ) (hyperbolic z = e^θ instance of
    the z-form (zⁿ⁺¹−z⁻ⁿ⁻¹)/(z−z⁻¹) displayed in that equation). -/
theorem U_cosh_sinh (n : ℤ) (θ : ℝ) :
    (U ℝ n).eval (cosh θ) * sinh θ = sinh ((↑n + 1) * θ) :=
  U_real_cosh θ n

-- no-dlmf: real hyperbolic (z = e^θ, θ real) instance of DLMF 18.5.2's
-- z-parametrized equality, not the displayed sin-form relation itself and
-- narrower than DLMF's complex-z domain (Tier-2 audit 2026-08-07); the
-- faithful surface of DLMF 18.5.2 is `U_cos_sin_nat`.
/-- U_n(cosh θ) sinh θ = sinh((n+1)θ), hyperbolic z = e^θ instance (`n : ℕ`
restriction of `U_cosh_sinh`). -/
theorem U_cosh_sinh_nat (n : ℕ) (θ : ℝ) :
    (U ℝ (n : ℤ)).eval (cosh θ) * sinh θ = sinh ((((n : ℤ) : ℝ) + 1) * θ) :=
  U_cosh_sinh (n : ℤ) θ

/-! ## Three-Term Recurrence -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 3.11.7
-- surface is T_recurrence_nat
/-- **C5**: T_{n+2} = 2X · T_{n+1} - T_n. -/
theorem T_recurrence (n : ℤ) :
    T ℝ (n + 2) = 2 * X * T ℝ (n + 1) - T ℝ n :=
  T_add_two ℝ n

/-- **DLMF 3.11.7** — the Chebyshev first-kind recurrence
T_{m+1}(x) - 2x T_m(x) + T_{m-1}(x) = 0 (m ≥ 1), stated at m = n+1 as
T_{n+2} = 2X · T_{n+1} - T_n (DLMF-faithful restriction of `T_recurrence`:
`n : ℕ`).
DAG: E-3.11.7.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem T_recurrence_nat (n : ℕ) :
    T ℝ ((n : ℤ) + 2) = 2 * X * T ℝ ((n : ℤ) + 1) - T ℝ (n : ℤ) :=
  T_recurrence (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.9
-- surface is U_recurrence_nat
/-- **C6**: U_{n+2} = 2X · U_{n+1} - U_n. -/
theorem U_recurrence (n : ℤ) :
    U ℝ (n + 2) = 2 * X * U ℝ (n + 1) - U ℝ n :=
  U_add_two ℝ n

/-- **DLMF 18.9** (18.9.1 specialized by Table 18.9.1, Chebyshev U row:
A_n = 2, B_n = 0, C_n = 1) — U_{n+2} = 2X · U_{n+1} - U_n (DLMF-faithful
restriction of `U_recurrence`: `n : ℕ`).
DAG: E-18.9.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_recurrence_nat (n : ℕ) :
    U ℝ ((n : ℤ) + 2) = 2 * X * U ℝ ((n : ℤ) + 1) - U ℝ (n : ℤ) :=
  U_recurrence (n : ℤ)

/-! ## Initial Values -/

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_0 = 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_0(x) = 1 line of that display). -/
theorem T_zero' : T ℝ 0 = 1 := T_zero ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_1 = X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_1(x) = x line of that display). -/
theorem T_one' : T ℝ 1 = X := T_one ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_2 = 2X² - 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_2(x) = 2x² - 1 line of that display). -/
theorem T_two' : T ℝ 2 = 2 * X ^ 2 - 1 := T_two ℝ

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_3 = 4X³ - 3X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_3(x) = 4x³ - 3x line of that display), from the three-term
recurrence applied to `T_1, T_2`. -/
theorem T_three' : T ℝ 3 = 4 * X ^ 3 - 3 * X := by
  have h := T_recurrence 1
  norm_num at h
  rw [h, T_two']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_4 = 8X⁴ - 8X² + 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_4(x) = 8x⁴ - 8x² + 1 line of that display), from the three-term
recurrence applied to `T_2, T_3`. -/
theorem T_four' : T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  have h := T_recurrence 2
  norm_num at h
  rw [h, T_three', T_two']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_5 = 16X⁵ - 20X³ + 5X. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev first-kind
polynomials: the T_5(x) = 16x⁵ - 20x³ + 5x line of that display), from the three-term
recurrence applied to `T_3, T_4`. -/
theorem T_five' : T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h := T_recurrence 3
  norm_num at h
  rw [h, T_four', T_three']
  ring

-- no-dlmf: single entry of display 18.5.14; conjunction carrier is T_explicit_degree_le_six
/-- T_6 = 32X⁶ - 48X⁴ + 18X² - 1. DLMF 18.5.14 (§18.5(iv), explicit low-degree Chebyshev
first-kind polynomials: the T_6(x) = 32x⁶ - 48x⁴ + 18x² - 1 line of that display), from the
three-term recurrence applied to `T_4, T_5`. -/
theorem T_six' : T ℝ 6 = 32 * X ^ 6 - 48 * X ^ 4 + 18 * X ^ 2 - 1 := by
  have h := T_recurrence 4
  norm_num at h
  rw [h, T_five', T_four']
  ring

/-- **DLMF 18.5.14.** The explicit low-degree Chebyshev polynomials of the first kind,
`T_0(x)` through `T_6(x)`, as polynomial identities over `ℝ[X]`.

DAG: E-18.5.14.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem T_explicit_degree_le_six :
    T ℝ 0 = 1 ∧ T ℝ 1 = X ∧ T ℝ 2 = 2 * X ^ 2 - 1 ∧
      T ℝ 3 = 4 * X ^ 3 - 3 * X ∧ T ℝ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 ∧
      T ℝ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X ∧
      T ℝ 6 = 32 * X ^ 6 - 48 * X ^ 4 + 18 * X ^ 2 - 1 :=
  ⟨T_zero', T_one', T_two', T_three', T_four', T_five', T_six'⟩

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_0 = 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_0(x) = 1 line of that display). -/
theorem U_zero' : U ℝ 0 = 1 := U_zero ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_1 = 2X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_1(x) = 2x line of that display). -/
theorem U_one' : U ℝ 1 = 2 * X := U_one ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_2 = 4X² - 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_2(x) = 4x² - 1 line of that display). -/
theorem U_two' : U ℝ 2 = 4 * X ^ 2 - 1 := U_two ℝ

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_3 = 8X³ - 4X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev second-kind
polynomials: the U_3(x) = 8x³ - 4x line of that display), from the three-term
recurrence applied to `U_1, U_2`. -/
theorem U_three' : U ℝ 3 = 8 * X ^ 3 - 4 * X := by
  have h := U_recurrence 1
  norm_num at h
  rw [h, U_two']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_4 = 16X⁴ - 12X² + 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_4(x) = 16x⁴ - 12x² + 1 line of that display), from the
three-term recurrence applied to `U_2, U_3`. -/
theorem U_four' : U ℝ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 := by
  have h := U_recurrence 2
  norm_num at h
  rw [h, U_three', U_two']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_5 = 32X⁵ - 32X³ + 6X. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_5(x) = 32x⁵ - 32x³ + 6x line of that display), from the
three-term recurrence applied to `U_3, U_4`. -/
theorem U_five' : U ℝ 5 = 32 * X ^ 5 - 32 * X ^ 3 + 6 * X := by
  have h := U_recurrence 3
  norm_num at h
  rw [h, U_four', U_three']
  ring

-- no-dlmf: single entry of display 18.5.15; conjunction carrier is U_explicit_degree_le_six
/-- U_6 = 64X⁶ - 80X⁴ + 24X² - 1. DLMF 18.5.15 (§18.5(iv), explicit low-degree Chebyshev
second-kind polynomials: the U_6(x) = 64x⁶ - 80x⁴ + 24x² - 1 line of that display), from the
three-term recurrence applied to `U_4, U_5`. -/
theorem U_six' : U ℝ 6 = 64 * X ^ 6 - 80 * X ^ 4 + 24 * X ^ 2 - 1 := by
  have h := U_recurrence 4
  norm_num at h
  rw [h, U_five', U_four']
  ring

/-- **DLMF 18.5.15.** The explicit low-degree Chebyshev polynomials of the second kind,
`U_0(x)` through `U_6(x)`, as polynomial identities over `ℝ[X]`.

DAG: E-18.5.15.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem U_explicit_degree_le_six :
    U ℝ 0 = 1 ∧ U ℝ 1 = 2 * X ∧ U ℝ 2 = 4 * X ^ 2 - 1 ∧
      U ℝ 3 = 8 * X ^ 3 - 4 * X ∧ U ℝ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 ∧
      U ℝ 5 = 32 * X ^ 5 - 32 * X ^ 3 + 6 * X ∧
      U ℝ 6 = 64 * X ^ 6 - 80 * X ^ 4 + 24 * X ^ 2 - 1 :=
  ⟨U_zero', U_one', U_two', U_three', U_four', U_five', U_six'⟩

/-! ## Evaluation at Special Points -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1
/-- **C7**: T_n(1) = 1. -/
theorem T_at_one (n : ℤ) : (T ℝ n).eval 1 = 1 := T_eval_one ℝ n

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, p_n(1) column);
-- conjunction carrier is T_table_18_6_1
/-- T_n(1) = 1 (DLMF-faithful restriction of `T_at_one`: `n : ℕ`). -/
theorem T_at_one_nat (n : ℕ) : (T ℝ (n : ℤ)).eval 1 = 1 := T_at_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1 (T_n(-1) = (-1)^n is a derived combination of the
-- parity row and the p_n(1) column, not itself a Table 18.6.1 entry)
/-- **C17**: T_n(-1) = (-1)^n. -/
theorem T_at_neg_one (n : ℤ) : (T ℝ n).eval (-1) = n.negOnePow := T_eval_neg_one ℝ n

-- no-dlmf: derived combination of display 18.6 (Table 18.6.1's T row: the parity
-- p_n(-x) = (-1)^n p_n(x) combined with p_n(1) = 1 at x = 1), not itself a table
-- entry; conjunction carrier is T_table_18_6_1
/-- T_n(-1) = (-1)^n (`n : ℕ` restriction of `T_at_neg_one`). -/
theorem T_at_neg_one_nat (n : ℕ) :
    (T ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow := T_at_neg_one (n : ℤ)

/-- **C18**: T_n(0) evaluation. DLMF 18.6 (Table 18.6.1, values at 0).

Restricted to 0 ≤ n per DLMF §18.3/§18.6 (Tier-2 audit 2026-07-29; Mathlib's
Chebyshev T extends to ℤ via T_{-n}=T_n).

DAG: E-18.6.
Fidelity: tier1 unable (parity)
Verified: verified (tier2)
-/
theorem T_at_zero (n : ℤ) (_hn : 0 ≤ n) :
    (T ℝ n).eval 0 = if Even n then ((n / 2).negOnePow : ℤ) else 0 :=
  T_eval_zero ℝ n

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is U_at_one_nat
/-- **C8**: U_n(1) = n + 1. -/
theorem U_at_one (n : ℤ) : (U ℝ n).eval 1 = ↑n + 1 := U_eval_one ℝ n

/-- **DLMF 18.6** (Table 18.6.1, values at ±1) — U_n(1) = n + 1 (DLMF-faithful
restriction of `U_at_one`: `n : ℕ`).
DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_at_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval 1 = ((n : ℤ) : ℝ) + 1 := U_at_one (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form of U_at_neg_one_nat (itself
-- no-dlmf, an instance of DLMF 18.6; the faithful parity surface is U_eval_neg'_nat)
/-- U_n(-1) = (-1)^n (n + 1). -/
theorem U_at_neg_one (n : ℤ) :
    (U ℝ n).eval (-1) = n.negOnePow * (↑n + 1) := U_eval_neg_one ℝ n

-- no-dlmf: instance of DLMF 18.6 (Table 18.6.1 states the parity
-- U_n(-x) = (-1)^n U_n(x) and the value U_n(1) = n + 1; the value at x = -1 is
-- their derived combination, not a table entry); faithful surface is U_eval_neg'_nat
/-- U_n(-1) = (-1)^n (n + 1) (`n : ℕ` restriction of `U_at_neg_one`). -/
theorem U_at_neg_one_nat (n : ℕ) :
    (U ℝ (n : ℤ)).eval (-1) = (n : ℤ).negOnePow * (((n : ℤ) : ℝ) + 1) :=
  U_at_neg_one (n : ℤ)

/-- **DLMF 18.6** (Table 18.6.1, parity) — U_n(-x) = (-1)^n U_n(x), the Chebyshev
second-kind parity relation.
DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_eval_neg'_nat (n : ℕ) (x : ℝ) :
    (U ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (U ℝ (n : ℤ)).eval x :=
  U_eval_neg ℝ n x

/-! ## Symmetry -/

-- no-dlmf: index symmetry T_{-n}=T_n of Mathlib's ℤ-indexed extension; no DLMF counterpart
/-- T is even: T(-n) = T(n). -/
theorem T_neg' (n : ℤ) : T ℝ (-n) = T ℝ n := T_neg ℝ n

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6
-- surface is T_table_18_6_1
/-- **C16**: T_n(-x) = (-1)^n T_n(x) (parity in x). -/
theorem T_eval_neg' (n : ℤ) (x : ℝ) :
    (T ℝ n).eval (-x) = n.negOnePow * (T ℝ n).eval x := T_eval_neg ℝ n x

-- no-dlmf: single entry of display 18.6 (Table 18.6.1, T row, parity column);
-- conjunction carrier is T_table_18_6_1
/-- T_n(-x) = (-1)^n T_n(x) (DLMF-faithful restriction of `T_eval_neg'`: `n : ℕ`). -/
theorem T_eval_neg'_nat (n : ℕ) (x : ℝ) :
    (T ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (T ℝ (n : ℤ)).eval x :=
  T_eval_neg' (n : ℤ) x

/-- **DLMF 18.6.** Table 18.6.1's `T_n` row (symmetry and special values): the parity
relation `T_n(-x) = (-1)^n T_n(x)` together with the endpoint value `T_n(1) = 1`. (The
further value `T_n(-1) = (-1)^n` is the `x = 1` instance of the parity relation combined
with the endpoint value, not a separate table entry.)

DAG: E-18.6.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem T_table_18_6_1 (n : ℕ) (x : ℝ) :
    (T ℝ (n : ℤ)).eval (-x) = (n : ℤ).negOnePow * (T ℝ (n : ℤ)).eval x ∧
      (T ℝ (n : ℤ)).eval 1 = 1 :=
  ⟨T_eval_neg'_nat n x, T_at_one_nat n⟩

/-! ## Product and Composition Identities -/

/-- **C9**: Product-to-sum: 2 T_m T_k = T_{m+k} + T_{m-k} (DLMF 18.18.21, where
DLMF's `m, n` range over nonnegative integers).

DAG: E-18.18.21.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem T_product_to_sum (m k : ℤ) (_hm : 0 ≤ m) (_hk : 0 ≤ k) :
    2 * T ℝ m * T ℝ k = T ℝ (m + k) + T ℝ (m - k) :=
  T_mul_T ℝ m k

-- no-dlmf: composition/semigroup property T_{mn}=T_m∘T_n; no numbered DLMF equation
-- states this (checked §18.5, §18.7, §18.16 — absent); the previous tag 18.5.4 is
-- unrelated (Chebyshev fourth-kind W_n definition).
/-- **C10**: Composition property: T_{mn} = T_m ∘ T_n (DLMF 18.5.4).
    Chebyshev polynomials form a commutative semigroup under composition.

-/
theorem T_composition (m n : ℤ) :
    T ℝ (m * n) = (T ℝ m).comp (T ℝ n) :=
  T_mul ℝ m n

/-! ## Pointwise Bound -/

-- no-dlmf: strictly-more-general total/junk-value form; see T_abs_le_one_nat and,
-- for the DLMF 18.14.1 general Jacobi form, abs_jacobiP_le_jacobiP_one
-- (FLMF/Functions/Chebyshev/PointwiseBound.lean)
/-- **C11**: |T_n(x)| ≤ 1 for x ∈ [-1,1]. -/
theorem T_abs_le_one (n : ℤ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (T ℝ n).eval x ∈ Icc (-1 : ℝ) 1 :=
  eval_T_real_mem_Icc n hx

-- no-dlmf: instance of DLMF 18.14.1 (Chebyshev T_n is the renormalized Jacobi case
-- α = β = -1/2 of the bound |P_n^{(α,β)}(x)| ≤ P_n^{(α,β)}(1)); faithful surface is
-- abs_jacobiP_le_jacobiP_one (FLMF/Functions/Chebyshev/PointwiseBound.lean)
/-- |T_n(x)| ≤ 1 for x ∈ [-1,1] (`n : ℕ` restriction of `T_abs_le_one`). -/
theorem T_abs_le_one_nat (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (T ℝ (n : ℤ)).eval x ∈ Icc (-1 : ℝ) 1 :=
  T_abs_le_one (n : ℤ) hx

/-! ## Interrelations Between T and U -/

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is `U_eq_X_mul_U_add_T'_nat`
/-- U_{n+1} = X U_n + T_{n+1} (interrelations between T and U). -/
theorem U_eq_X_mul_U_add_T' (n : ℤ) :
    U ℝ (n + 1) = X * U ℝ n + T ℝ (n + 1) :=
  U_eq_X_mul_U_add_T ℝ n

-- no-dlmf: this specific identity `U_{n+1} = X U_n + T_{n+1}` is not itself
-- one of §18.9's stated relations (e.g. `U_{n+1}=2xU_n-U_{n-1}`,
-- `T_n=½(U_n-U_{n-2})`); it is a derived algebraic consequence, not a
-- DLMF-numbered display. `n : ℕ` specialization of `U_eq_X_mul_U_add_T'`.
/-- U_{n+1} = X U_n + T_{n+1} (interrelations between T and U), `n : ℕ`. -/
theorem U_eq_X_mul_U_add_T'_nat (n : ℕ) :
    U ℝ ((n : ℤ) + 1) = X * U ℝ (n : ℤ) + T ℝ ((n : ℤ) + 1) :=
  U_eq_X_mul_U_add_T' (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is T_eq_U_sub_X_mul_U'_nat
/-- T_n = U_n - X U_{n-1} (interrelations between T and U). -/
theorem T_eq_U_sub_X_mul_U' (n : ℤ) :
    T ℝ n = U ℝ n - X * U ℝ (n - 1) :=
  T_eq_U_sub_X_mul_U ℝ n

-- no-dlmf: derived algebraic consequence of DLMF 18.9.9 (T_n = ½(U_n − U_{n−2}))
-- combined with the Chebyshev-U three-term recurrence; not itself a
-- DLMF-numbered display. `n : ℕ` restriction of `T_eq_U_sub_X_mul_U'`.
/-- T_n = U_n - X U_{n-1} (interrelations between T and U), `n : ℕ`. -/
theorem T_eq_U_sub_X_mul_U'_nat (n : ℕ) :
    T ℝ (n : ℤ) = U ℝ (n : ℤ) - X * U ℝ ((n : ℤ) - 1) :=
  T_eq_U_sub_X_mul_U' (n : ℤ)

-- no-dlmf: strictly-more-general total/junk-value form; the (still non-DLMF)
-- `ℕ`-restricted specialization is T_eq_X_mul_U_sub_U'_nat
/-- T_{n+2} = X U_{n+1} - U_n (interrelations between T and U). -/
theorem T_eq_X_mul_U_sub_U' (n : ℤ) :
    T ℝ (n + 2) = X * U ℝ (n + 1) - U ℝ n :=
  T_eq_X_mul_U_sub_U ℝ n

-- no-dlmf: derived algebraic consequence of DLMF 18.9.9 (T_n = ½(U_n − U_{n−2}))
-- combined with the Chebyshev-U three-term recurrence; not itself a
-- DLMF-numbered display. `n : ℕ` restriction of `T_eq_X_mul_U_sub_U'`.
/-- T_{n+2} = X U_{n+1} - U_n (interrelations between T and U), `n : ℕ`. -/
theorem T_eq_X_mul_U_sub_U'_nat (n : ℕ) :
    T ℝ ((n : ℤ) + 2) = X * U ℝ ((n : ℤ) + 1) - U ℝ (n : ℤ) :=
  T_eq_X_mul_U_sub_U' (n : ℤ)

/-! ## Derivatives at Endpoints -/

-- no-dlmf: strictly-more-general total/junk-value form; the faithful DLMF 18.6.1
-- surface is T_deriv_at_one_nat
/-- **C12**: T_n'(1) = n². -/
theorem T_deriv_at_one (n : ℤ) :
    (Polynomial.derivative (T ℝ n)).eval 1 = ↑n ^ 2 :=
  derivative_T_eval_one (R := ℝ) n

-- no-dlmf: no DLMF equation number gives Tₙ'(1) = n² directly (Table 18.6.1
-- has no derivative column; §18.9 derivative relations 18.9.21/18.9.22 do not
-- give this endpoint value either) — matches the sibling `U_deriv_at_one`
-- treatment below. `n : ℕ` specialization of `T_deriv_at_one`.
/-- T_n'(1) = n², `n : ℕ`. -/
theorem T_deriv_at_one_nat (n : ℕ) :
    (Polynomial.derivative (T ℝ (n : ℤ))).eval 1 = ((n : ℤ) : ℝ) ^ 2 :=
  T_deriv_at_one (n : ℤ)

-- no-dlmf: endpoint-derivative value 3 U_n'(1) = n(n+1)(n+2); no DLMF equation states
-- it directly (Table 18.6.1 has no p_n'(1) column, only p'_{2n+1}(0); §18.9 derivative
-- equations 18.9.21/18.9.22 do not give this endpoint value either).
/-- 3 U_n'(1) = n(n+1)(n+2). DLMF 18.6 (Table 18.6.1, endpoint derivatives).

-/
theorem U_deriv_at_one (n : ℤ) :
    3 * (Polynomial.derivative (U ℝ n)).eval 1 = (↑n + 2) * (↑n + 1) * ↑n :=
  derivative_U_eval_one (R := ℝ) n

/-! ## Orthogonality with respect to (1-x²)^{-1/2} measure -/

-- no-dlmf: instance of DLMF 18.2.1 / the j ≠ k case of DLMF 3.11.8 (specific family
-- T_n and weight (1-x²)^{-1/2}, off-diagonal case only); faithful surface is
-- T_orthogonality_relation
/-- **C13**: ∫ T_n T_m dμ_T = 0 for n ≠ m.
    Here μ_T is the Chebyshev measure with density (1-x²)^{-1/2} on [-1,1]. -/
theorem T_orthogonal {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 :=
  integral_eval_T_real_mul_eval_T_real_measureT_of_ne h

-- no-dlmf: instance of DLMF 3.11.8 (fixed j = k = 0; equivalently the n = 0 entry of
-- Table 18.3.1's h_n column); faithful surface is T_orthogonality_relation
/-- **C14**: ∫ T_0² dμ_T = π (norm squared of T_0). -/
theorem T_zero_norm_sq :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π :=
  integral_eval_T_real_mul_self_measureT_zero

/-- **C15**: ∫ T_n² dμ_T = π/2 for n ≥ 1. DLMF 18.3 (Table 18.3.1, h_n column:
    h_n = π/2 for T_n, n > 0).

DAG: E-18.3.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem T_norm_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 :=
  integral_T_real_mul_self_measureT_of_ne_zero hn

/-- **DLMF 3.11.8** — the full Chebyshev first-kind orthogonality relation on
[-1,1] with weight (1-x²)^{-1/2} (realized by `measureT`):
∫ T_j T_k dμ_T = π if j = k = 0, π/2 if j = k ≠ 0, and 0 if j ≠ k.
DAG: E-3.11.8.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem T_orthogonality_relation (j k : ℕ) :
    ∫ x, (T ℝ j).eval x * (T ℝ k).eval x ∂measureT =
      if j = k then (if j = 0 then π else π / 2) else 0 := by
  rcases eq_or_ne j k with rfl | hjk
  · rcases eq_or_ne j 0 with rfl | hj
    · rw [if_pos rfl, if_pos rfl]
      simpa using T_zero_norm_sq
    · rw [if_pos rfl, if_neg hj]
      exact T_norm_sq hj
  · rw [if_neg hjk]
    exact T_orthogonal hjk

/-! ## Degree and Leading Coefficient -/

-- no-dlmf: Table 18.3.1 has no degree column ("p_n has degree n" is §18.2(i)
-- prose, not a displayed equation) — same adjudication as U_degree
-- (2026-08-11 relation-audit); the faithful Table 18.3.1 T-surfaces are the
-- leading-coefficient and normalization lemmas.
/-- deg(T_n) = |n| (DLMF §18.2(i) degree convention).

Restricted to 0 ≤ n per DLMF §18.3/§18.6 (Tier-2 audit 2026-07-29; Mathlib's
Chebyshev T extends to ℤ via T_{-n}=T_n).
-/
theorem T_degree (n : ℤ) (_hn : 0 ≤ n) : (T ℝ n).degree = n.natAbs := degree_T ℝ n

-- no-dlmf: strictly-more-general total/junk-value form (extends via |n| to negative
-- indices not covered by DLMF's nonnegative-integer convention); the faithful DLMF
-- 18.3 surface is T_leading_coeff_nat
/-- leading_coeff(T_n) = 2^{|n|-1} (Table 18.3.1, leading coefficient κ_n). -/
theorem T_leading_coeff (n : ℤ) :
    (T ℝ n).leadingCoeff = 2 ^ (n.natAbs - 1) := leadingCoeff_T ℝ n

/-- **DLMF 18.3** (Table 18.3.1, leading coefficient κ_n) — leading_coeff(T_0) = 1
and leading_coeff(T_n) = 2^{n-1} for n ≥ 1, stated as the two table rows
explicitly (the earlier single ℕ-truncated-subtraction formula was true in Lean
but transcribed as the false real exponent 2^{-1} at n = 0 by the Tier-1
oracle — see the `n ≠ 0` guard precedent of 2026-08-02).
DAG: E-18.3.
Fidelity: tier1 unable (conjunction-partial)
Verified: unverified
-/
theorem T_leading_coeff_nat :
    (T ℝ ((0 : ℕ) : ℤ)).leadingCoeff = 1 ∧
      ∀ n : ℕ, n ≠ 0 → (T ℝ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) :=
  ⟨by simp [T_leading_coeff (0 : ℤ)], fun n _ => by
    simpa using T_leading_coeff (n : ℤ)⟩

-- no-dlmf: Table 18.3.1 has no degree column (its columns are p_n(x), (a,b), w(x),
-- h_n, k_n, k̃_n/k_n, Constraints); "p_n has degree n" is the prose convention of
-- §18.2(i), not a displayed equation. The faithful Table 18.3.1 surfaces for U are
-- U_leading_coeff (k_n column) and the h_n/orthogonality lemmas.
/-- deg(U_n) = n for n : ℕ (Table 18.3.1 lists U_n among the degree-n classical OPs). -/
theorem U_degree (n : ℕ) : (U ℝ (n : ℤ)).degree = n := degree_U_natCast ℝ n

/-- leading_coeff(U_n) = 2^n for n : ℕ. DLMF 18.3 (Table 18.3.1, leading coefficient κ_n).

DAG: E-18.3.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem U_leading_coeff (n : ℕ) :
    (U ℝ (n : ℤ)).leadingCoeff = 2 ^ n := leadingCoeff_U_natCast ℝ n

end FLMF.Functions.Chebyshev
