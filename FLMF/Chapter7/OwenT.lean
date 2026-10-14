import Mathlib

/-!
# Owen's T function

Owen's T function `T(h, a)` is defined by the integral

`T(h, a) = (1 / (2π)) ∫₀ᵃ exp(-h²(1+x²)/2) / (1+x²) dx`.

It arises in the computation of bivariate normal probabilities (cf. DLMF 7.2 for the
related error functions). Here we set up the basic analytic infrastructure: the
definition, continuity/integrability of the integrand, the boundary value
`T(h, 0) = 0`, and the elementary symmetries
`T(-h, a) = T(h, a)` and `T(h, -a) = -T(h, a)`.
-/

namespace FLMF.OwenT

open scoped Real
open intervalIntegral MeasureTheory

-- no-dlmf: integrand of Owen's T; analytic infrastructure, no DLMF identity
/-- The integrand of Owen's T function:
`x ↦ exp(-h²(1+x²)/2) / (1+x²)`. -/
noncomputable def owenIntegrand (h : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-h ^ 2 * (1 + x ^ 2) / 2) / (1 + x ^ 2)

-- no-dlmf: Owen's T defining integral; not a numbered DLMF Ch 7 identity
/-- Owen's T function `T(h, a) = (1/(2π)) ∫₀ᵃ exp(-h²(1+x²)/2)/(1+x²) dx`. -/
noncomputable def owenT (h a : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ x in (0 : ℝ)..a, owenIntegrand h x

-- no-dlmf: continuity of the integrand; analytic infrastructure, no DLMF identity
/-- The integrand is continuous in `x`. -/
theorem continuous_owenIntegrand (h : ℝ) : Continuous (owenIntegrand h) := by
  unfold owenIntegrand
  apply Continuous.div
  · exact Real.continuous_exp.comp (by fun_prop)
  · fun_prop
  · intro x
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    linarith

-- no-dlmf: interval-integrability of the integrand; analytic infrastructure, no DLMF identity
/-- The integrand is interval-integrable on any interval. -/
theorem intervalIntegrable_owenIntegrand (h a b : ℝ) :
    IntervalIntegrable (owenIntegrand h) MeasureTheory.volume a b :=
  (continuous_owenIntegrand h).intervalIntegrable a b

-- no-dlmf: evenness of the integrand in x; elementary parity, no DLMF identity
/-- The integrand is even in `x`. -/
theorem owenIntegrand_neg (h x : ℝ) : owenIntegrand h (-x) = owenIntegrand h x := by
  unfold owenIntegrand
  rw [neg_pow, neg_one_sq, one_mul]

-- no-dlmf: boundary value T(h,0)=0; elementary, no DLMF identity
/-- Owen's T function vanishes at `a = 0`. -/
theorem owenT_zero_right (h : ℝ) : owenT h 0 = 0 := by
  unfold owenT
  rw [intervalIntegral.integral_same, mul_zero]

-- no-dlmf: evenness of T in h; elementary parity, no DLMF identity
/-- Owen's T function is even in `h`. -/
theorem owenT_neg_left (h a : ℝ) : owenT (-h) a = owenT h a := by
  unfold owenT owenIntegrand
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  rw [neg_pow, neg_one_sq, one_mul]

-- no-dlmf: oddness of T in a; elementary parity, no DLMF identity
/-- Owen's T function is odd in `a`. -/
theorem owenT_neg_right (h a : ℝ) : owenT h (-a) = - owenT h a := by
  unfold owenT
  rw [← mul_neg]
  congr 1
  -- `∫ x in 0..-a, f x = ∫ x in -0..-a, f x = ∫ x in a..0, f (-x)`
  have key : (∫ x in (0:ℝ)..(-a), owenIntegrand h x)
      = ∫ x in a..0, owenIntegrand h (-x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => owenIntegrand h x)]
    simp
  have key2 : (∫ x in a..(0:ℝ), owenIntegrand h (-x))
      = ∫ x in a..0, owenIntegrand h x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    rw [owenIntegrand_neg]
  rw [key, key2, intervalIntegral.integral_symm 0 a]

end FLMF.OwenT
