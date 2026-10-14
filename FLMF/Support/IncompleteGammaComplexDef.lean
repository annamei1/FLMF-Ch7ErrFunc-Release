import FLMF.Support.IncompleteGammaDef
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Complex lower/upper incomplete Gamma functions, principal branch (DLMF §8.2, §8.19)

The real `lowerGamma`/`upperGamma` of `IncompleteGamma.Def` are `ℝ → ℝ → ℝ`, so
DLMF displays whose variable is a *complex* `z` (e.g. 7.11.1/7.11.2/7.11.3)
cannot even be stated with them.  Mathlib v4.30.0 has no incomplete Gamma either
(`Complex.partialGamma` has a complex parameter but a **real** upper limit), so
the complex forms are built here.

## Definitions

* `clowerGamma a z = z^a ∫₀¹ e^{-s z} s^{a-1} ds` — DLMF 8.2.1's contour integral
  `γ(a,z) = ∫₀^z t^{a-1} e^{-t} dt` along the **straight segment `0 → z`**, in the
  substituted variable `t = s z`.  This is the DLMF integral verbatim after that
  substitution; no series shortcut is used.
* `cupperGamma a z = Γ(a) - γ(a,z)` — DLMF 8.2.3 read as the definition of `Γ(a,z)`
  (equivalent to DLMF 8.2.2 for `Re a > 0`, where `Γ(a)` converges).
* `cexpIntegralE p z = z^{p-1} Γ(1-p, z)` — DLMF 8.19.1.

## Branch convention (read before using these)

All powers here are **principal**: `w ^ c = Complex.cpow w c = exp (c · Log w)`
with `Log` the principal logarithm (`arg ∈ (-π, π]`).  DLMF's `γ(a,z)`, `Γ(a,z)`,
`E_p(z)` are multivalued in `z` (they carry a `z^a` factor) and its displays are
stated for the analytically continued objects, i.e. they are *branch-implicit*.
Consequently identities that feed `z²` into these functions — DLMF 7.11.1,
7.11.2, 7.11.3 — are true on the principal branch exactly on the half-plane
`Re z > 0` (where principal `(z²)^{1/2} = z`), and are FALSE off it for the
principal branch (`z = -1`: `γ(½,1) = √π erf 1 ≠ √π erf(-1)`).  The sector
hypothesis carried by the theorems downstream is therefore the maximal true
principal-branch domain, not a narrowing of DLMF's claim.

## Agreement with the real definitions

`clowerGamma_ofReal` / `cupperGamma_ofReal` identify these with `lowerGamma` /
`upperGamma` on the positive real axis, so nothing is redefined incompatibly.
-/

namespace FLMF.IncompleteGamma

open MeasureTheory Set

/-- The complex lower incomplete Gamma function on the principal branch,
`γ(a, z) = ∫₀^z t^{a-1} e^{-t} dt` taken along the straight segment `0 → z`
(DLMF 8.2.1, in the substituted variable `t = s z`):
`γ(a,z) = z^a ∫₀¹ e^{-s z} s^{a-1} ds`.

The prefactor `z ^ a` is the **principal** power `exp (a · Log z)`; see the module
docstring for the branch convention. -/
noncomputable def clowerGamma (a z : ℂ) : ℂ :=
  z ^ a * ∫ s in (0:ℝ)..1, Complex.exp (-(s : ℂ) * z) * (s : ℂ) ^ (a - 1)

/-- The complex upper incomplete Gamma function on the principal branch,
`Γ(a, z) = Γ(a) - γ(a, z)` (DLMF 8.2.3; equivalently DLMF 8.2.2 whenever `Re a > 0`,
where the Euler integral for `Γ(a)` converges). -/
noncomputable def cupperGamma (a z : ℂ) : ℂ := Complex.Gamma a - clowerGamma a z

/-- The complex generalized exponential integral on the principal branch,
`E_p(z) = z^{p-1} Γ(1-p, z)` (DLMF 8.19.1).  Both `z ^ (p-1)` and the `z^{1-p}`
hidden inside `cupperGamma` are principal powers. -/
noncomputable def cexpIntegralE (p z : ℂ) : ℂ := z ^ (p - 1) * cupperGamma (1 - p) z

/-! ### Principal-branch square root of a square -/

-- no-dlmf: principal-branch bookkeeping lemma, no DLMF counterpart
/-- **Principal branch:** `(z²)^{1/2} = z` exactly on the right half-plane.
This is the branch fact behind the `0 < z.re` hypothesis of DLMF 7.11.1/7.11.2/7.11.3:
for `Re z > 0` we have `|arg z| < π/2`, so `Log (z²) = 2 Log z` and the principal
square root of `z²` returns `z` itself. -/
theorem cpow_half_sq {z : ℂ} (hz : 0 < z.re) : (z ^ 2) ^ (1 / 2 : ℂ) = z := by
  have harg : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have harg' := abs_lt.1 harg
  have him : (Complex.log z * 2).im = 2 * Complex.arg z := by
    simp [Complex.mul_im, Complex.log_im]
    ring
  have h1 : -Real.pi < (Complex.log z * 2).im := by rw [him]; linarith [harg'.1]
  have h2 : (Complex.log z * 2).im ≤ Real.pi := by rw [him]; linarith [harg'.2]
  have h := Complex.cpow_mul (x := z) (y := 2) (1 / 2 : ℂ) h1 h2
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one] at h
  simpa using h.symm

-- no-dlmf: principal-branch bookkeeping lemma, no DLMF counterpart
/-- **Principal branch:** `(z²)^{-1/2} = z⁻¹` on the right half-plane
(the reciprocal form of `cpow_half_sq`, used by DLMF 7.11.3's `E_{1/2}` factor). -/
theorem cpow_neg_half_sq {z : ℂ} (hz : 0 < z.re) : (z ^ 2) ^ (-(1 / 2) : ℂ) = z⁻¹ := by
  rw [Complex.cpow_neg, cpow_half_sq hz]

/-! ### The `a = 1/2` segment integral -/

-- no-dlmf: change-of-variables lemma (`s = t²`) for the `a = 1/2` segment integral,
-- no DLMF counterpart
/-- The `a = 1/2` segment integral in Gaussian form: substituting `s = t²` on the
real parameter interval (a genuine real change of variables — the complex variable
`w` is only a parameter, so no branch question arises),
`∫₀¹ e^{-s w} s^{-1/2} ds = 2 ∫₀¹ e^{-t² w} dt`. -/
theorem segment_integral_half (w : ℂ) :
    (∫ s in (0:ℝ)..1, Complex.exp (-(s : ℂ) * w) * (s : ℂ) ^ ((1 / 2 : ℂ) - 1))
      = 2 * ∫ t in (0:ℝ)..1, Complex.exp (-(t : ℂ) ^ 2 * w) := by
  set g : ℝ → ℂ := fun y => Complex.exp (-(y : ℂ) * w) * (y : ℂ) ^ ((1 / 2 : ℂ) - 1) with hg
  have hderiv : ∀ t ∈ Ioc (0:ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * t) (Ioc (0:ℝ) 1) t := by
    intro t _
    simpa using ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Ioc (0:ℝ) 1))
  have hinj : InjOn (fun u : ℝ => u ^ 2) (Ioc (0:ℝ) 1) := by
    intro a ha b hb hab
    have hab' : a ^ 2 = b ^ 2 := hab
    have h0 : (a - b) * (a + b) = 0 := by nlinarith [hab']
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exfalso; linarith [ha.1, hb.1]
  have himg : (fun u : ℝ => u ^ 2) '' Ioc (0:ℝ) 1 = Ioc (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨pow_pos ht.1 2, by nlinarith [ht.1, ht.2]⟩
    · intro hy
      refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.2 hy.1, ?_⟩, ?_⟩
      · calc Real.sqrt y ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hy.2
          _ = 1 := Real.sqrt_one
      · simpa using Real.sq_sqrt hy.1.le
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioc (a := (0:ℝ)) (b := 1)) hderiv hinj g
  rw [himg] at hcov
  -- Simplify the transported integrand: `|2t| • g (t²) = 2 e^{-t² w}` on `(0,1]`.
  have hpt : ∀ t ∈ Ioc (0:ℝ) 1,
      |2 * t| • g (t ^ 2) = 2 * Complex.exp (-(t : ℂ) ^ 2 * w) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have hexp : ((1 / 2 : ℂ) - 1) = (((-1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    have hr : (t ^ 2 : ℝ) ^ (-1 / 2 : ℝ) = t⁻¹ := by
      have h2 : (t ^ 2 : ℝ) = t ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h2, ← Real.rpow_mul ht0.le]
      rw [show (2 : ℝ) * (-1 / 2 : ℝ) = -1 by norm_num]
      rw [Real.rpow_neg ht0.le, Real.rpow_one]
    have hcast : ((t ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((t : ℂ))⁻¹ := by
      rw [hexp, ← Complex.ofReal_cpow (by positivity) (-1 / 2 : ℝ), hr]
      push_cast
      ring
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    rw [hg]
    simp only
    rw [hcast, abs_of_pos (by linarith : (0:ℝ) < 2 * t), Complex.real_smul]
    have : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 := by push_cast; ring
    rw [this]
    field_simp
    push_cast
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt] at hcov
  rw [MeasureTheory.integral_const_mul] at hcov
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hcov

/-! ### Agreement with the real incomplete Gamma functions -/

-- no-dlmf: change-of-variables lemma (`t = s x`) putting the real `lowerGamma`
-- in segment form, no DLMF counterpart
/-- The real lower incomplete Gamma in ray form: for `x > 0`,
`γ(a,x) = x^a ∫₀¹ e^{-s x} s^{a-1} ds` (substitution `t = s x` in DLMF 8.2.1). -/
theorem lowerGamma_eq_ray (a : ℝ) {x : ℝ} (hx : 0 < x) :
    lowerGamma a x = x ^ a * ∫ s in (0:ℝ)..1, Real.exp (-(s * x)) * s ^ (a - 1) := by
  set g : ℝ → ℝ := fun t => Real.exp (-t) * t ^ (a - 1) with hg
  have hderiv : ∀ s ∈ Ioc (0:ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => u * x) x (Ioc (0:ℝ) 1) s := by
    intro s _
    simpa using ((hasDerivAt_id s).mul_const x).hasDerivWithinAt (s := Ioc (0:ℝ) 1)
  have hinj : InjOn (fun u : ℝ => u * x) (Ioc (0:ℝ) 1) := by
    intro p _ q _ hpq
    exact mul_right_cancel₀ hx.ne' hpq
  have himg : (fun u : ℝ => u * x) '' Ioc (0:ℝ) 1 = Ioc (0:ℝ) x := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨mul_pos hs.1 hx, by nlinarith [hs.2, hx]⟩
    · intro hy
      refine ⟨y / x, ⟨div_pos hy.1 hx, ?_⟩, ?_⟩
      · rw [div_le_one hx]; exact hy.2
      · field_simp
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioc (a := (0:ℝ)) (b := 1)) hderiv hinj g
  rw [himg] at hcov
  have hpt : ∀ s ∈ Ioc (0:ℝ) 1,
      |x| • g (s * x) = x ^ a * (Real.exp (-(s * x)) * s ^ (a - 1)) := by
    intro s hs
    have hs0 : (0:ℝ) ≤ s := hs.1.le
    rw [hg]
    simp only [smul_eq_mul, abs_of_pos hx]
    rw [Real.mul_rpow hs0 hx.le]
    have hxa : x * x ^ (a - 1) = x ^ a := by
      nth_rewrite 1 [show x = x ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hx]
      norm_num
    calc x * (Real.exp (-(s * x)) * (s ^ (a - 1) * x ^ (a - 1)))
        = (x * x ^ (a - 1)) * (Real.exp (-(s * x)) * s ^ (a - 1)) := by ring
      _ = x ^ a * (Real.exp (-(s * x)) * s ^ (a - 1)) := by rw [hxa]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt,
    MeasureTheory.integral_const_mul] at hcov
  rw [lowerGamma, hg] at *
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hcov

-- no-dlmf: foundational agreement bridge (complex definition restricts to the real
-- one on the positive axis), no DLMF counterpart
/-- **Agreement with the real `lowerGamma`.** On the positive real axis the
principal-branch complex lower incomplete Gamma is the cast of the real one:
`γ(a, x) = ↑(γ(a, x))` for real `a` and `x > 0`. -/
theorem clowerGamma_ofReal (a : ℝ) {x : ℝ} (hx : 0 < x) :
    clowerGamma (a : ℂ) (x : ℂ) = ((lowerGamma a x : ℝ) : ℂ) := by
  have hint : (∫ s in (0:ℝ)..1, Complex.exp (-(s : ℂ) * (x : ℂ)) * (s : ℂ) ^ ((a : ℂ) - 1))
      = ((∫ s in (0:ℝ)..1, Real.exp (-(s * x)) * s ^ (a - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs0 : (0:ℝ) ≤ s := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      exact hs.1
    have hcast : ((a : ℂ) - 1) = (((a - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_cpow hs0 (a - 1), Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [clowerGamma, hint, lowerGamma_eq_ray a hx, ← Complex.ofReal_cpow hx.le a]
  push_cast
  ring

-- no-dlmf: foundational agreement bridge (complex definition restricts to the real
-- one on the positive axis), no DLMF counterpart
/-- **Agreement with the real `upperGamma`.** For `a > 0` and `x > 0`,
`Γ(a, x) = ↑(Γ(a, x))`. -/
theorem cupperGamma_ofReal {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < x) :
    cupperGamma (a : ℂ) (x : ℂ) = ((upperGamma a x : ℝ) : ℂ) := by
  have hsum := lowerGamma_add_upperGamma ha hx.le
  rw [cupperGamma, Complex.Gamma_ofReal, clowerGamma_ofReal a hx, ← Complex.ofReal_sub,
    show Real.Gamma a - lowerGamma a x = upperGamma a x by linarith]

-- no-dlmf: special value `Γ(1/2) = √π` in complex form, no DLMF counterpart
/-- `Γ(1/2) = √π` for Mathlib's complex `Gamma`. -/
theorem cGamma_one_half : Complex.Gamma (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have h := Complex.Gamma_ofReal (1 / 2 : ℝ)
  rw [Real.Gamma_one_half_eq] at h
  simpa using h

end FLMF.IncompleteGamma
