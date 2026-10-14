import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Branch algebra — slit-plane `cpow` laws (E1a, M-branch-algebra)

Shared algebra of the principal complex power `z ^ s` on `Complex.slitPlane`,
consolidating the branch-tracking arguments needed by the `z = 1` connection
formulas for `₂F₁` (C2), the Hankel-loop `1/Γ` module, and the D4 connection
coefficients. Mathlib has the same-base exponent laws (`cpow_add`, `cpow_sub`,
`cpow_neg`), the raw composition law (`Complex.cpow_mul`, conditioned on
`im (log x · y)`), and the norm identities (`norm_cpow_of_ne_zero`,
`norm_cpow_eq_rpow_re_of_pos`, `norm_cpow_le`); what it *lacks* — and this file
provides — is the different-base algebra under `arg`/slit-plane hypotheses:

* `mul_cpow_of_arg_add_mem` — `(xy)^s = x^s y^s` when `arg x + arg y ∈ (-π, π]`
  (Mathlib has only the nonneg-real-factor case `mul_cpow_ofReal_nonneg`);
* `mul_cpow_of_re_pos` — the half-plane corollary (relocated from
  `Frameworks/Hypergeometric/EulerPfaffComplex.lean`);
* `div_cpow_of_arg_sub_mem`, `div_cpow_of_re_pos` — the quotient forms
  (`y` in the slit plane, so `arg y ≠ π` and `y⁻¹` does not wrap);
* `cpow_cpow_real_of_mem_slitPlane` — `(x^a)^b = x^{ab}` for `x ∈ slitPlane`,
  real `|a| ≤ 1` (a slit-plane-friendly face of `Complex.cpow_mul`);
* `one_sub_mem_slitPlane_iff` / `_iff_notMem_Ici` / `_of_norm_lt_one` —
  membership of `1 - z` in the slit plane, i.e. `z` off the cut `[1, ∞)`;
* `hasDerivAt_one_sub_cpow`, `analyticAt_one_sub_cpow`,
  `analyticOnNhd_one_sub_cpow` — derivative `-s(1-z)^{s-1}` and holomorphy of
  `(1-z)^s` off the cut;
* `cpow_rot_extract`, `norm_cpow_rot` — polar extraction
  `(e^{iθ}r)^w = r^w e^{wθi}` and its norm `r^{Re w} e^{-θ Im w}` (relocated
  from `Methods/ContourRotationGamma.lean`).
-/

open Set Complex
open scoped Real

namespace FLMF.Methods.BranchAlgebra

/-! ### Product and quotient splitting under `arg` hypotheses -/

-- no-dlmf: complex-power algebra helper, no DLMF counterpart
/-- **Product splitting for `cpow`.** `(xy)^s = x^s y^s` whenever the principal
arguments do not wrap: `arg x + arg y ∈ (-π, π]`. -/
theorem mul_cpow_of_arg_add_mem {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : arg x + arg y ∈ Ioc (-π) π) (s : ℂ) :
    (x * y) ^ s = x ^ s * y ^ s := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy), Complex.log_mul hx hy h, add_mul,
    Complex.exp_add, ← Complex.cpow_def_of_ne_zero hx, ← Complex.cpow_def_of_ne_zero hy]

/-- `(A·B)^s = A^s·B^s` over `ℂ` when both factors have positive real part
(so `|arg A|, |arg B| < π/2` and `arg A + arg B ∈ (−π, π)`, no branch wrap). -/
-- no-dlmf: complex-power algebra helper, no DLMF counterpart
theorem mul_cpow_of_re_pos {A B : ℂ} (hA : 0 < re A) (hB : 0 < re B) (s : ℂ) :
    (A * B) ^ s = A ^ s * B ^ s := by
  have hA0 : A ≠ 0 := fun h => by simp [h] at hA
  have hB0 : B ≠ 0 := fun h => by simp [h] at hB
  have hargA : |arg A| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hargB : |arg B| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)
  rw [abs_lt] at hargA hargB
  exact mul_cpow_of_arg_add_mem hA0 hB0
    ⟨by linarith [hargA.1, hargB.1], by linarith [hargA.2, hargB.2]⟩ s

-- no-dlmf: complex-power algebra helper, no DLMF counterpart
/-- **Quotient splitting for `cpow`.** `(x/y)^s = x^s/y^s` when `y` lies in the
slit plane (so `arg y ≠ π` and inversion does not wrap) and
`arg x - arg y ∈ (-π, π]`. -/
theorem div_cpow_of_arg_sub_mem {x y : ℂ} (hx : x ≠ 0) (hy : y ∈ slitPlane)
    (h : arg x - arg y ∈ Ioc (-π) π) (s : ℂ) :
    (x / y) ^ s = x ^ s / y ^ s := by
  have hy0 : y ≠ 0 := slitPlane_ne_zero hy
  have hyπ : arg y ≠ π := slitPlane_arg_ne_pi hy
  have hinv : arg y⁻¹ = -arg y := by rw [Complex.arg_inv, if_neg hyπ]
  rw [div_eq_mul_inv,
    mul_cpow_of_arg_add_mem hx (inv_ne_zero hy0)
      (by rw [hinv, ← sub_eq_add_neg]; exact h) s,
    Complex.inv_cpow _ _ hyπ, ← div_eq_mul_inv]

-- no-dlmf: complex-power algebra helper, no DLMF counterpart
/-- Quotient splitting in the right half-plane: `(A/B)^s = A^s/B^s` when
`Re A, Re B > 0`. -/
theorem div_cpow_of_re_pos {A B : ℂ} (hA : 0 < re A) (hB : 0 < re B) (s : ℂ) :
    (A / B) ^ s = A ^ s / B ^ s := by
  have hargA : |arg A| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hargB : |arg B| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)
  rw [abs_lt] at hargA hargB
  exact div_cpow_of_arg_sub_mem (fun h => by simp [h] at hA)
    (mem_slitPlane_iff.mpr (Or.inl hB))
    ⟨by linarith [hargA.1, hargB.2], by linarith [hargA.2, hargB.1]⟩ s

/-! ### Iterated powers -/

-- no-dlmf: complex-power algebra helper, no DLMF counterpart
/-- **Power-of-power composition on the slit plane.** `(x^a)^b = x^{ab}` for
`x ∈ slitPlane` and real `|a| ≤ 1` (then `|a·arg x| ≤ |arg x| < π`, so the
inner power stays on the principal branch). The slit-plane-usable face of
`Complex.cpow_mul`. -/
theorem cpow_cpow_real_of_mem_slitPlane {x : ℂ} (hx : x ∈ slitPlane) {a : ℝ}
    (ha : |a| ≤ 1) (b : ℂ) :
    (x ^ (a : ℂ)) ^ b = x ^ ((a : ℂ) * b) := by
  have harg : |arg x| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg x, (arg_le_pi x).lt_of_ne (slitPlane_arg_ne_pi hx)⟩
  have him : (Complex.log x * (a : ℂ)).im = arg x * a := by
    simp [Complex.mul_im, Complex.log_im]
  have hbound : |arg x * a| < π := by
    calc |arg x * a| = |arg x| * |a| := abs_mul _ _
      _ ≤ |arg x| * 1 := by gcongr
      _ < π := by rwa [mul_one]
  rw [abs_lt] at hbound
  exact (Complex.cpow_mul b (by rw [him]; exact hbound.1)
    (by rw [him]; exact hbound.2.le)).symm

/-! ### `(1 - z)^s` off the cut `[1, ∞)` -/

-- no-dlmf: slit-plane membership helper, no DLMF counterpart
/-- Slit-plane membership of `1 - z`, in coordinates. -/
theorem one_sub_mem_slitPlane_iff {z : ℂ} :
    1 - z ∈ slitPlane ↔ z.re < 1 ∨ z.im ≠ 0 := by
  rw [mem_slitPlane_iff, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    sub_pos, zero_sub, neg_ne_zero]

-- no-dlmf: slit-plane membership helper, no DLMF counterpart
/-- `1 - z` lies in the slit plane exactly when `z` avoids the branch cut
`[1, ∞) ⊂ ℝ ⊂ ℂ` — the natural domain of the principal `(1-z)^s`. -/
theorem one_sub_mem_slitPlane_iff_notMem_Ici {z : ℂ} :
    1 - z ∈ slitPlane ↔ z ∉ (Complex.ofReal '' Ici 1) := by
  rw [one_sub_mem_slitPlane_iff]
  constructor
  · rintro h ⟨x, hx, rfl⟩
    simp only [Complex.ofReal_re, Complex.ofReal_im, ne_eq, not_true_eq_false, or_false] at h
    exact absurd hx (not_le.mpr h)
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨z.re, hc.1, by rw [Complex.ext_iff]; simp [hc.2]⟩

-- no-dlmf: slit-plane membership helper, no DLMF counterpart
/-- On the open unit disc, `1 - z` lies in the slit plane. -/
theorem one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ slitPlane := by
  simpa [sub_eq_add_neg] using
    Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)

-- no-dlmf: holomorphy helper, no DLMF counterpart
/-- **Derivative of `(1-z)^s`** off the cut: `d/dz (1-z)^s = -s(1-z)^{s-1}`
whenever `1 - z ∈ slitPlane`. -/
theorem hasDerivAt_one_sub_cpow {z : ℂ} (h : 1 - z ∈ slitPlane) (s : ℂ) :
    HasDerivAt (fun w : ℂ => (1 - w) ^ s) (-(s * (1 - z) ^ (s - 1))) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub 1
  simpa using h1.cpow_const h

-- no-dlmf: holomorphy helper, no DLMF counterpart
/-- **Holomorphy of `(1-z)^s`** off the cut `[1, ∞)`. -/
theorem analyticAt_one_sub_cpow {z : ℂ} (h : 1 - z ∈ slitPlane) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (1 - w) ^ s) z :=
  (analyticAt_const.sub analyticAt_id).cpow analyticAt_const h

-- no-dlmf: holomorphy helper, no DLMF counterpart
/-- `(1-z)^s` is holomorphic on the full slit domain `{z | 1 - z ∈ slitPlane}`
(= `ℂ ∖ [1, ∞)` by `one_sub_mem_slitPlane_iff_notMem_Ici`). -/
theorem analyticOnNhd_one_sub_cpow (s : ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => (1 - w) ^ s) {z : ℂ | 1 - z ∈ slitPlane} :=
  fun _ hz => analyticAt_one_sub_cpow hz s

/-! ### Polar extraction on a rotated ray

Relocated from `Methods/ContourRotationGamma.lean` (M-branch-algebra): these are
general branch facts about `(e^{iθ}r)^w`, not Γ-specific. -/

-- no-dlmf: contour-rotation infrastructure, no DLMF equation
/-- **cpow extraction on a rotated ray.** For `r > 0` and `|θ| < π`,
`(e^{iθ}·r)^w = r^w · e^{wθI}`. Proved via `e^{iθ}r = e^{log r + iθ}` and the
principal log (`im = θ ∈ (-π,π]`), avoiding any `arg` computation. -/
theorem cpow_rot_extract {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (Complex.exp (θ * Complex.I) * (r : ℂ)) ^ w
      = (r : ℂ) ^ w * Complex.exp (w * (θ : ℂ) * Complex.I) := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr_exp : Complex.exp ((Real.log r : ℝ) : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hr]
  have hz : Complex.exp (θ * Complex.I) * (r : ℂ)
      = Complex.exp (((Real.log r : ℝ) : ℂ) + θ * Complex.I) := by
    rw [← hr_exp, ← Complex.exp_add, add_comm]
  have him : (((Real.log r : ℝ) : ℂ) + (θ : ℂ) * Complex.I).im = θ := by simp
  rw [hz, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by rw [him]; exact hθ.1) (by rw [him]; exact le_of_lt hθ.2),
    add_mul, Complex.exp_add]
  congr 1
  · rw [Complex.cpow_def_of_ne_zero hrne, ← Complex.ofReal_log hr.le]
  · congr 1; ring

-- no-dlmf: norm-bound helper, no DLMF equation
/-- Reusable: `‖(e^{iθ}r)^w‖ = r^{Re w}·e^{-θ Im w}` (`r>0`, `|θ|<π`). -/
theorem norm_cpow_rot (w : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 < r) :
    ‖(Complex.exp (θ * Complex.I) * (r : ℂ)) ^ w‖ = r ^ w.re * Real.exp (-θ * w.im) := by
  rw [cpow_rot_extract hθ hr, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp]
  congr 1
  rw [show (w * (θ : ℂ) * Complex.I).re = -θ * w.im by simp [Complex.mul_re]; ring]

end FLMF.Methods.BranchAlgebra
