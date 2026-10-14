import FLMF.Chapter7.RepeatedErfcIdentities
import FLMF.Support.IdentityTheorem
import FLMF.Support.ParametricIntegralAnalytic

/-!
# The repeated integrals of `erfc` for a complex variable (DLMF §7.18)

DLMF §7.18 assigns its variable `z` the *complex* domain throughout, while
`FLMF.Error.iRepErfc : ℕ → ℝ → ℝ` (`RepeatedErfc.lean`) is the real-axis
object built by iterated Lebesgue tail integrals.  This module supplies the
complex twin and re-surfaces the §7.18 displays over `ℂ`.

The complex definition is the **horizontal-ray Laplace form** of the closed
integral representation 7.18.2, i.e. the substitution `t = z + s` in
`iⁿerfc(z) = (2/√π) ∫_z^∞ (t−z)ⁿ/n! · e^{−t²} dt`:

`iⁿerfc(z) = (2/√π) ∫_0^∞ (sⁿ/n!) e^{−(z+s)²} ds`   (`cRepErfc`).

No sector hypothesis is needed: `‖e^{−(z+s)²}‖ = e^{(Im z)² − (Re z + s)²}`
decays like `e^{−s²/2}` for every fixed `z`, locally uniformly, so the integral
converges on all of `ℂ` and `cRepErfc n` is entire
(`differentiable_cRepErfc`, via `FLMF.Methods.analyticOnNhd_integral_of_locallyDominated`).

Agreement with the real family (`cRepErfc_ofReal`) plus entirety then transfers
every §7.18 polynomial identity from the real axis by the identity theorem
(`FLMF.Methods.eqOn_of_entire_of_eqOn_real`).

Main results:

* `FLMF.Error.cRepErfc`, `cRepErfcNegOne`, `cRepErfcPred` — the complex family,
  its `n = −1` member, and the `n − 1` index shift.
* `FLMF.Error.cRepErfc_ofReal` — `iⁿerfc` on `ℝ` is the restriction of `cRepErfc`.
* `FLMF.Error.differentiable_cRepErfc` — `cRepErfc n` is entire.
* `FLMF.Error.HhC` — the complex probability function `Hhₙ`, with
  `HhC_ofReal` / `differentiable_HhC`.
* `FLMF.Error.cerf_7_18_1`, `cerf_7_18_2`, `cerf_7_18_3`, `cerf_7_18_4`,
  `cerf_7_18_5`, `cerf_7_18_6`, `cerf_7_18_7`, `cerf_7_18_8`, `cerf_7_18_11`,
  `cerf_7_18_12` — the complex-variable surfaces of the corresponding DLMF
  displays.  The real statements of `RepeatedErfc.lean` /
  `Ch7RepeatedErfc.lean` are their real-axis restrictions.

Two of the displays are also *index-repaired* here: `cerf_7_18_3` and
`cerf_7_18_7` are stated through `cRepErfcPred`, so they cover DLMF's lowest
index (`n = 0`, resp. `m = 1`), which the real `ℕ`-shifted statements omitted.
-/

noncomputable section

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set

open scoped FLMF.Hypergeometric

/-! ## Half-line translation `t = x + s` -/

-- no-dlmf: measure-preserving translation of a half-line integral; proof
-- infrastructure, no DLMF identity number
/-- Translating a half-line integral onto `(0,∞)`: `∫_x^∞ f = ∫_0^∞ f(x+s) ds`. -/
private theorem integral_Ioi_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (x : ℝ) : (∫ t in Ioi x, f t) = ∫ s in Ioi (0 : ℝ), f (x + s) := by
  have hmp : MeasurePreserving (fun s : ℝ => s + x) volume volume :=
    measurePreserving_add_right volume x
  have hemb : MeasurableEmbedding (fun s : ℝ => s + x) :=
    (Homeomorph.addRight x).measurableEmbedding
  have hpre : (fun s : ℝ => s + x) ⁻¹' Ioi x = Ioi (0 : ℝ) := by
    ext s; simp
  have h := hmp.setIntegral_preimage_emb hemb f (Ioi x)
  rw [hpre] at h
  rw [← h]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [add_comm]

/-! ## The kernel: bounds and integrability -/

-- no-dlmf: Gaussian norm bound for the shifted kernel; proof infrastructure,
-- no DLMF identity number
/-- `‖e^{−(z+s)²}‖ ≤ e^{(Im z)² + 2(Re z)²} · e^{−s²/2}` for real `s`: the shifted
Gaussian decays like `e^{−s²/2}` uniformly on bounded sets of `z`. -/
private theorem norm_cexp_neg_sq_shift_le (z : ℂ) (s : ℝ) :
    ‖Complex.exp (-(z + (s : ℂ)) ^ 2)‖
      ≤ Real.exp (z.im ^ 2 + 2 * z.re ^ 2) * Real.exp (-(s ^ 2) / 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-(z + (s : ℂ)) ^ 2).re = z.im ^ 2 - (z.re + s) ^ 2 := by
    simp [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre]
  nlinarith [sq_nonneg (3 * z.re + s), sq_nonneg s]

-- no-dlmf: integrability of the polynomial-times-Gaussian majorant; proof
-- infrastructure, no DLMF identity number
/-- `s ↦ sᵏ e^{−s²/2}` is integrable on `(0,∞)`. -/
private theorem integrableOn_pow_mul_gaussHalf (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(s ^ 2) / 2)) (Ioi (0 : ℝ)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num) hk
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  rw [Real.rpow_natCast]
  congr 1
  ring_nf

-- no-dlmf: integrability of the complex shifted-ray kernel; proof
-- infrastructure, no DLMF identity number
/-- The kernel `s ↦ (sⁿ/n!)·e^{−(z+s)²}` is integrable on `(0,∞)` for every
complex `z`. -/
theorem integrableOn_cRepErfcKernel (n : ℕ) (z : ℂ) :
    IntegrableOn (fun s : ℝ =>
      ((s : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ)) ^ 2)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono'
    (((integrableOn_pow_mul_gaussHalf n).const_mul
      (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ)))) ?_ ?_
  · exact (((Complex.continuous_ofReal.pow n).div_const _).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, Complex.norm_natCast]
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have h := norm_cexp_neg_sq_shift_le z s
    have hpow : (0 : ℝ) ≤ s ^ n / (n.factorial : ℝ) := by positivity
    calc s ^ n / (n.factorial : ℝ) * ‖Complex.exp (-(z + (s : ℂ)) ^ 2)‖
        ≤ s ^ n / (n.factorial : ℝ) *
            (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) * Real.exp (-(s ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left h hpow
      _ = Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) *
            (s ^ n * Real.exp (-(s ^ 2) / 2)) := by ring

/-! ## The complex repeated integrals -/

-- no-dlmf: the complex iⁿerfc family def; the 7.18.1 base-case display is
-- surfaced at `cerf_7_18_1`
/-- **The repeated integrals of `erfc` for a complex variable** (DLMF §7.18), as
the horizontal-ray form of the closed representation 7.18.2:
`iⁿerfc(z) = (2/√π) ∫_0^∞ (sⁿ/n!)·e^{−(z+s)²} ds`, the substitution `t = z + s`
in `iⁿerfc(z) = (2/√π) ∫_z^∞ (t−z)ⁿ/n!·e^{−t²} dt`.

-/
noncomputable def cRepErfc (n : ℕ) (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) *
    ∫ s in Ioi (0 : ℝ), ((s : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ)) ^ 2)

-- no-dlmf: the n = -1 member of the complex family; the 7.18.1 base-case display
-- is surfaced at `cerf_7_18_1`
/-- The `n = −1` base case of the complex repeated-integral family (DLMF 7.18.1):
`i⁻¹erfc(z) = (2/√π)·e^{−z²}`. -/
noncomputable def cRepErfcNegOne (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2)

-- no-dlmf: index-shift support def for the complex §7.18 displays
/-- The "index `n − 1`" member of the complex family, for `n : ℕ`:
`cRepErfcPred 0 = cRepErfcNegOne` and `cRepErfcPred (m+1) = cRepErfc m`.  Lets
the displays that mention `i^{n−1}erfc` be stated uniformly for every
`n = 0, 1, 2, …`, matching DLMF's own index range. -/
noncomputable def cRepErfcPred : ℕ → ℂ → ℂ
  | 0 => cRepErfcNegOne
  | m + 1 => cRepErfc m

-- no-dlmf: definitional unfolding of `cRepErfcPred`, structural
@[simp] theorem cRepErfcPred_zero : cRepErfcPred 0 = cRepErfcNegOne := rfl

-- no-dlmf: definitional unfolding of `cRepErfcPred`, structural
@[simp] theorem cRepErfcPred_succ (m : ℕ) : cRepErfcPred (m + 1) = cRepErfc m := rfl

/-! ## Agreement with the real family -/

-- no-dlmf: foundational bridge lemma, no DLMF identity number
/-- **Agreement with the real `iⁿerfc`.** `cRepErfc n ↑x = ↑(iⁿerfc x)`. -/
theorem cRepErfc_ofReal (n : ℕ) (x : ℝ) :
    cRepErfc n (x : ℂ) = ((iRepErfc n x : ℝ) : ℂ) := by
  have hreal : iRepErfc n x
      = 2 / Real.sqrt Real.pi *
        ∫ s in Ioi (0 : ℝ), s ^ n / (n.factorial : ℝ) * Real.exp (-(x + s) ^ 2) := by
    rw [iRepErfc_eq_integral_closedForm n x,
      integral_Ioi_shift (fun t : ℝ => (t - x) ^ n / (n.factorial : ℝ) * Real.exp (-t ^ 2)) x]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 2
    ring
  rw [hreal, cRepErfc]
  have hcast : (∫ s in Ioi (0 : ℝ),
        ((s : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-((x : ℂ) + (s : ℂ)) ^ 2))
      = ((∫ s in Ioi (0 : ℝ), s ^ n / (n.factorial : ℝ) * Real.exp (-(x + s) ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast [Complex.ofReal_exp]
    ring_nf
  rw [hcast]
  push_cast
  ring

-- no-dlmf: foundational bridge lemma, no DLMF identity number
/-- `cRepErfcNegOne ↑x = ↑(i⁻¹erfc x)`. -/
theorem cRepErfcNegOne_ofReal (x : ℝ) :
    cRepErfcNegOne (x : ℂ) = ((iRepErfcNegOne x : ℝ) : ℂ) := by
  rw [cRepErfcNegOne, iRepErfcNegOne]
  push_cast [Complex.ofReal_exp]
  ring_nf

-- no-dlmf: foundational bridge lemma, no DLMF identity number
/-- `cRepErfcPred n ↑x = ↑(iRepErfcPred n x)`. -/
theorem cRepErfcPred_ofReal (n : ℕ) (x : ℝ) :
    cRepErfcPred n (x : ℂ) = ((iRepErfcPred n x : ℝ) : ℂ) := by
  cases n with
  | zero => exact cRepErfcNegOne_ofReal x
  | succ m => exact cRepErfc_ofReal m x

/-! ## Entirety -/

-- no-dlmf: qualitative support lemma (entirety of the complex family), no
-- numbered DLMF display
/-- `cRepErfc n` is entire.  Differentiation under the integral sign with the
locally uniform majorant `2(‖a‖+1+s)(sⁿ/n!)·e^{3(‖a‖+1)²}e^{−s²/2}` on
`ball a 1`, packaged by
`FLMF.Methods.analyticOnNhd_integral_of_locallyDominated`. -/
private theorem analyticOnNhd_cRepErfcIntegral (n : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ s in Ioi (0 : ℝ), ((s : ℂ) ^ n / (n.factorial : ℂ)) *
        Complex.exp (-(z + (s : ℂ)) ^ 2)) Set.univ := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (f := fun (z : ℂ) (s : ℝ) =>
      ((s : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ)) ^ 2))
    (f' := fun (z : ℂ) (s : ℝ) =>
      ((s : ℂ) ^ n / (n.factorial : ℂ)) *
        (-(2 * (z + (s : ℂ))) * Complex.exp (-(z + (s : ℂ)) ^ 2)))
    isOpen_univ ?_ ?_ ?_ ?_ ?_
  · intro z _
    exact (((Complex.continuous_ofReal.pow n).div_const _).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · intro z _
    exact integrableOn_cRepErfcKernel n z
  · intro z _
    exact (((Complex.continuous_ofReal.pow n).div_const _).mul
      (((continuous_const.mul (continuous_const.add Complex.continuous_ofReal)).neg).mul
        (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    intro z _
    have h1 : HasDerivAt (fun w : ℂ => -(w + (s : ℂ)) ^ 2) (-(2 * (z + (s : ℂ)))) z := by
      have h := (((hasDerivAt_id z).add_const ((s : ℂ))).pow 2).neg
      convert h using 1
      simp only [id_eq]
      ring
    have h2 := (h1.cexp).const_mul ((s : ℂ) ^ n / (n.factorial : ℂ))
    convert h2 using 1
    ring
  · intro a _
    refine ⟨1, one_pos, fun s =>
      (2 * (‖a‖ + 1) * Real.exp (3 * (‖a‖ + 1) ^ 2) / (n.factorial : ℝ)) *
          (s ^ n * Real.exp (-(s ^ 2) / 2))
        + (2 * Real.exp (3 * (‖a‖ + 1) ^ 2) / (n.factorial : ℝ)) *
          (s ^ (n + 1) * Real.exp (-(s ^ 2) / 2)), ?_, ?_⟩
    · exact ((integrableOn_pow_mul_gaussHalf n).const_mul _).add
        ((integrableOn_pow_mul_gaussHalf (n + 1)).const_mul _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs z hz
      have hs0 : (0 : ℝ) < s := hs
      have hznorm : ‖z‖ ≤ ‖a‖ + 1 := by
        have h := mem_ball_iff_norm.mp hz
        calc ‖z‖ = ‖a + (z - a)‖ := by ring_nf
          _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
          _ ≤ ‖a‖ + 1 := by linarith
      -- the Gaussian factor
      have hgauss : ‖Complex.exp (-(z + (s : ℂ)) ^ 2)‖
          ≤ Real.exp (3 * (‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 2) := by
        refine (norm_cexp_neg_sq_shift_le z s).trans ?_
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
        have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
        have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        have h1 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
        have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
        have h3 : ‖z‖ ^ 2 ≤ (‖a‖ + 1) ^ 2 := by nlinarith [norm_nonneg z]
        nlinarith
      -- the linear factor
      have hlin : ‖-(2 * (z + (s : ℂ)))‖ ≤ 2 * (‖a‖ + 1) + 2 * s := by
        rw [norm_neg, norm_mul]
        have : ‖z + (s : ℂ)‖ ≤ ‖z‖ + s := by
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        simp only [Complex.norm_ofNat]
        nlinarith [norm_nonneg (z + (s : ℂ))]
      rw [norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0, Complex.norm_natCast]
      have hK : (0 : ℝ) < Real.exp (3 * (‖a‖ + 1) ^ 2) := Real.exp_pos _
      have hpow : (0 : ℝ) ≤ s ^ n / (n.factorial : ℝ) := by positivity
      have hstep : ‖-(2 * (z + (s : ℂ)))‖ * ‖Complex.exp (-(z + (s : ℂ)) ^ 2)‖
          ≤ (2 * (‖a‖ + 1) + 2 * s) *
            (Real.exp (3 * (‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 2)) := by
        refine mul_le_mul hlin hgauss (norm_nonneg _) ?_
        positivity
      calc s ^ n / (n.factorial : ℝ) *
            (‖-(2 * (z + (s : ℂ)))‖ * ‖Complex.exp (-(z + (s : ℂ)) ^ 2)‖)
          ≤ s ^ n / (n.factorial : ℝ) *
              ((2 * (‖a‖ + 1) + 2 * s) *
                (Real.exp (3 * (‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 2))) :=
            mul_le_mul_of_nonneg_left hstep hpow
        _ = (2 * (‖a‖ + 1) * Real.exp (3 * (‖a‖ + 1) ^ 2) / (n.factorial : ℝ)) *
              (s ^ n * Real.exp (-(s ^ 2) / 2))
            + (2 * Real.exp (3 * (‖a‖ + 1) ^ 2) / (n.factorial : ℝ)) *
              (s ^ (n + 1) * Real.exp (-(s ^ 2) / 2)) := by
            field_simp
            ring

-- no-dlmf: qualitative support lemma (entirety of the complex family), no
-- numbered DLMF display
/-- `cRepErfc n` is analytic on all of `ℂ`. -/
theorem analyticOnNhd_cRepErfc (n : ℕ) : AnalyticOnNhd ℂ (cRepErfc n) Set.univ := by
  intro z hz
  have h := (analyticAt_const (v := (2 / Real.sqrt Real.pi : ℂ))).mul
    (analyticOnNhd_cRepErfcIntegral n z hz)
  simpa [cRepErfc] using h

-- no-dlmf: qualitative support lemma (entirety of the complex family), no
-- numbered DLMF display
/-- `cRepErfc n` is entire. -/
theorem differentiable_cRepErfc (n : ℕ) : Differentiable ℂ (cRepErfc n) := by
  rw [← differentiableOn_univ]
  exact (analyticOnNhd_cRepErfc n).differentiableOn

-- no-dlmf: qualitative support lemma (entirety of the derivative), no numbered
-- DLMF display
/-- The derivative of `cRepErfc n` is entire (the derivative of an entire
function is entire). -/
theorem differentiable_deriv_cRepErfc (n : ℕ) : Differentiable ℂ (deriv (cRepErfc n)) := by
  rw [← differentiableOn_univ]
  exact (analyticOnNhd_cRepErfc n).deriv.differentiableOn

-- no-dlmf: qualitative support lemma (entirety of `i⁻¹erfc`), no numbered DLMF display
/-- `cRepErfcNegOne` is entire. -/
theorem differentiable_cRepErfcNegOne : Differentiable ℂ cRepErfcNegOne := by
  unfold cRepErfcNegOne
  fun_prop

-- no-dlmf: qualitative support lemma (entirety of the shifted family), no
-- numbered DLMF display
/-- `cRepErfcPred n` is entire. -/
theorem differentiable_cRepErfcPred (n : ℕ) : Differentiable ℂ (cRepErfcPred n) := by
  cases n with
  | zero => exact differentiable_cRepErfcNegOne
  | succ m => exact differentiable_cRepErfc m

-- no-dlmf: qualitative support lemma (entirety of `erfc`), no numbered DLMF display
/-- `cerfc` is entire. -/
theorem differentiable_cerfc : Differentiable ℂ cerfc :=
  fun z => (differentiableAt_const 1).sub (differentiable_cerf z)

/-! ## The real-to-complex transfer engine -/

-- no-dlmf: derivative-transfer helper (real HasDerivAt ⟹ value of the complex
-- `deriv` on the real axis); proof infrastructure, no DLMF identity number
/-- If an entire `F` restricts on `ℝ` to a real function `f`, then the complex
derivative of `F` at a real point is the cast of the real derivative of `f`. -/
private theorem deriv_ofReal_eq {F : ℂ → ℂ} {f : ℝ → ℝ} (hF : Differentiable ℂ F)
    (hFf : ∀ x : ℝ, F (x : ℂ) = ((f x : ℝ) : ℂ)) {f' x : ℝ} (hf : HasDerivAt f f' x) :
    deriv F (x : ℂ) = ((f' : ℝ) : ℂ) := by
  have h1 : HasDerivAt F (deriv F (x : ℂ)) (x : ℂ) := (hF _).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ => F (y : ℂ)) (deriv F (x : ℂ)) x := h1.comp_ofReal
  rw [funext hFf] at h2
  exact h2.unique hf.ofReal_comp

/-! ## Base identifications -/

-- no-dlmf: chain link 7.18.1 (assembled in `cerf_7_18_1` below); the complex
-- `n = 0` member is `erfc`
/-- `i⁰erfc = erfc` over `ℂ`. -/
theorem cRepErfc_zero (z : ℂ) : cRepErfc 0 z = cerfc z := by
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real (differentiable_cRepErfc 0)
    differentiable_cerfc (fun x => ?_) z
  rw [cRepErfc_ofReal, cerfc_ofReal, iRepErfc_zero_apply]

/-! ## DLMF 7.18.1 -/

/-- **DLMF 7.18.1.** The `n = −1` and `n = 0` base cases of the repeated-integral
family, for complex `z`: `i⁻¹erfc(z) = (2/√π)e^{−z²}` and `i⁰erfc(z) = erfc(z)`.

DLMF 7.18.1.
DAG: E-7.18.1.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_1 (z : ℂ) :
    cRepErfcNegOne z = (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2) ∧
    cRepErfc 0 z = cerfc z :=
  ⟨rfl, cRepErfc_zero z⟩

/-! ## DLMF 7.18.7 — the three-term recurrence -/

/-- **DLMF 7.18.7.** The three-term recurrence
`2n·iⁿerfc(z) = i^{n−2}erfc(z) − 2z·i^{n−1}erfc(z)` for complex `z`, written in
the `ℕ`-index `m` with `n = m+1`, so that it covers DLMF's whole range
`n = 1, 2, 3, …` (the `n = 1` case reaching back to `i⁻¹erfc(z) = (2/√π)e^{−z²}`
through `cRepErfcPred`):
`2(m+1)·i^{m+1}erfc(z) = i^{m−1}erfc(z) − 2z·i^{m}erfc(z)`.

DLMF 7.18.7.
DAG: E-7.18.7.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_7 (m : ℕ) (z : ℂ) :
    2 * ((m : ℂ) + 1) * cRepErfc (m + 1) z
      = cRepErfcPred m z - 2 * z * cRepErfcPred (m + 1) z := by
  have hreal : ∀ x : ℝ,
      2 * ((m : ℝ) + 1) * iRepErfc (m + 1) x
        = iRepErfcPred m x - 2 * x * iRepErfcPred (m + 1) x := by
    intro x
    cases m with
    | zero =>
      simp only [iRepErfcPred, iRepErfcNegOne, iRepErfc_zero_apply, Nat.cast_zero, zero_add,
        mul_one]
      linarith [two_iRepErfc_one_add x]
    | succ k =>
      simp only [iRepErfcPred]
      push_cast
      linarith [erf_7_18_7 k x]
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real
    (f := fun w : ℂ => 2 * ((m : ℂ) + 1) * cRepErfc (m + 1) w)
    (g := fun w : ℂ => cRepErfcPred m w - 2 * w * cRepErfcPred (m + 1) w)
    ((differentiable_cRepErfc (m + 1)).const_mul _)
    ((differentiable_cRepErfcPred m).sub
      ((differentiable_const 2).mul differentiable_id |>.mul (differentiable_cRepErfcPred (m + 1))))
    (fun x => ?_) z
  have h := congrArg (fun r : ℝ => (r : ℂ)) (hreal x)
  push_cast at h
  show 2 * ((m : ℂ) + 1) * cRepErfc (m + 1) (x : ℂ)
    = cRepErfcPred m (x : ℂ) - 2 * (x : ℂ) * cRepErfcPred (m + 1) (x : ℂ)
  rw [cRepErfc_ofReal, cRepErfcPred_ofReal, cRepErfcPred_ofReal]
  linear_combination h

/-! ## DLMF 7.18.3 — the derivative relation -/

-- no-dlmf: functional form of DLMF 7.18.3; the tagged surface is `cerf_7_18_3`
/-- `deriv (iⁿerfc) = −i^{n−1}erfc` over `ℂ`, for every `n : ℕ`. -/
theorem deriv_cRepErfc (n : ℕ) : deriv (cRepErfc n) = fun w : ℂ => -cRepErfcPred n w := by
  refine FLMF.Methods.eq_of_entire_of_eqOn_real (differentiable_deriv_cRepErfc n)
    (differentiable_cRepErfcPred n).neg (fun x => ?_)
  have hr : HasDerivAt (iRepErfc n) (-iRepErfcPred n x) x := by
    cases n with
    | zero =>
      show HasDerivAt (iRepErfc 0) (-iRepErfcPred 0 x) x
      simpa [iRepErfcPred, iRepErfcNegOne, iRepErfc_zero] using hasDerivAt_erfc x
    | succ m => exact hasDerivAt_iRepErfc_succ m x
  rw [deriv_ofReal_eq (differentiable_cRepErfc n) (cRepErfc_ofReal n) hr,
    cRepErfcPred_ofReal]
  push_cast
  ring

-- no-dlmf: `HasDerivAt` workhorse form of DLMF 7.18.3; the tagged surface is
-- `cerf_7_18_3`
/-- `d/dz iⁿerfc(z) = −i^{n−1}erfc(z)` in `HasDerivAt` form, for every `n : ℕ`. -/
theorem hasDerivAt_cRepErfc (n : ℕ) (z : ℂ) :
    HasDerivAt (cRepErfc n) (-cRepErfcPred n z) z := by
  have h := (differentiable_cRepErfc n z).hasDerivAt
  rwa [deriv_cRepErfc n] at h

/-- **DLMF 7.18.3.** The derivative relation `(d/dz) iⁿerfc(z) = −i^{n−1}erfc(z)`
for complex `z`, for every `n = 0, 1, 2, …` (the `n = 0` case reaching back to
`i⁻¹erfc(z) = (2/√π)e^{−z²}` through `cRepErfcPred`).

DLMF 7.18.3.
DAG: E-7.18.3.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_3 (n : ℕ) (z : ℂ) :
    deriv (cRepErfc n) z = -cRepErfcPred n z := by
  rw [deriv_cRepErfc n]

/-! ## DLMF 7.18.2 — the ray integral representations

The two equalities of the display are read along the horizontal ray `t = z + s`,
`s ∈ (0,∞)`, which is the path the definition of `cRepErfc` already uses.  The
closed form (second equality) is then definitional; the first equality
`iⁿerfc(z) = ∫_z^∞ i^{n−1}erfc(t) dt` is the fundamental theorem of calculus on
`(0,∞)` applied to `s ↦ iⁿerfc(z+s)`, whose `s`-derivative is `−i^{n−1}erfc(z+s)`
(7.18.3) and which tends to `0` at `+∞` by the Gaussian ray bound below. -/

-- no-dlmf: integrability of the Gaussian ray majorant; proof infrastructure, no
-- DLMF identity number
/-- `s ↦ e^{−s²/2}` is integrable on `(0,∞)`. -/
private theorem integrableOn_gaussHalf :
    IntegrableOn (fun s : ℝ => Real.exp (-(s ^ 2) / 2)) (Ioi (0 : ℝ)) :=
  (integrableOn_pow_mul_gaussHalf 0).congr_fun (fun s _ => by rw [pow_zero, one_mul])
    measurableSet_Ioi

-- no-dlmf: Gaussian ray-decay bound for the complex family; proof infrastructure,
-- no DLMF identity number
/-- **Ray decay.** `‖iⁿerfc(z+s)‖ ≤ C_z·e^{−s²/2}` for `s ≥ 0`: along a horizontal
ray the complex repeated integrals inherit the Gaussian decay of their kernel,
because `(s+u)² ≥ s² + u²` for `s, u ≥ 0`. -/
private theorem exists_norm_cRepErfc_shift_le (n : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖cRepErfc n (z + (s : ℂ))‖ ≤ C * Real.exp (-(s ^ 2) / 2) := by
  set K : ℝ := ∫ u in Ioi (0 : ℝ), u ^ n * Real.exp (-(u ^ 2) / 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    positivity
  have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  refine ⟨(2 / Real.sqrt Real.pi) * (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) * K),
    by positivity, ?_⟩
  intro s hs
  rw [cRepErfc, norm_mul]
  have hc : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / Real.sqrt Real.pi := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, Complex.norm_ofNat]
  rw [hc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hbound : ‖∫ u in Ioi (0 : ℝ),
        ((u : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ) + (u : ℂ)) ^ 2)‖
      ≤ ∫ u in Ioi (0 : ℝ),
          (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) * Real.exp (-(s ^ 2) / 2))
            * (u ^ n * Real.exp (-(u ^ 2) / 2)) := by
    refine norm_integral_le_of_norm_le ((integrableOn_pow_mul_gaussHalf n).const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      Complex.norm_natCast]
    have hshift : z + (s : ℂ) + (u : ℂ) = z + ((s + u : ℝ) : ℂ) := by push_cast; ring
    rw [hshift]
    have h1 := norm_cexp_neg_sq_shift_le z (s + u)
    have h2 : Real.exp (-((s + u) ^ 2) / 2)
        ≤ Real.exp (-(s ^ 2) / 2) * Real.exp (-(u ^ 2) / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_nonneg hs hu0.le]
    have hpow : (0 : ℝ) ≤ u ^ n / (n.factorial : ℝ) := by positivity
    calc u ^ n / (n.factorial : ℝ) * ‖Complex.exp (-(z + ((s + u : ℝ) : ℂ)) ^ 2)‖
        ≤ u ^ n / (n.factorial : ℝ) *
            (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) *
              (Real.exp (-(s ^ 2) / 2) * Real.exp (-(u ^ 2) / 2))) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hpow
          exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) * Real.exp (-(s ^ 2) / 2))
            * (u ^ n * Real.exp (-(u ^ 2) / 2)) := by ring
  rw [integral_const_mul] at hbound
  calc ‖∫ u in Ioi (0 : ℝ),
        ((u : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ) + (u : ℂ)) ^ 2)‖
      ≤ (Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) * Real.exp (-(s ^ 2) / 2)) * K :=
        hbound
    _ = Real.exp (z.im ^ 2 + 2 * z.re ^ 2) / (n.factorial : ℝ) * K * Real.exp (-(s ^ 2) / 2) := by
        ring

-- no-dlmf: Gaussian ray-decay bound for the shifted family; proof infrastructure,
-- no DLMF identity number
/-- Ray decay for `i^{n−1}erfc`: `‖i^{n−1}erfc(z+s)‖ ≤ C_z·e^{−s²/2}` for `s ≥ 0`. -/
private theorem exists_norm_cRepErfcPred_shift_le (n : ℕ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      ‖cRepErfcPred n (z + (s : ℂ))‖ ≤ C * Real.exp (-(s ^ 2) / 2) := by
  cases n with
  | zero =>
    have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    refine ⟨2 / Real.sqrt Real.pi * Real.exp (z.im ^ 2 + 2 * z.re ^ 2), by positivity, ?_⟩
    intro s hs
    rw [cRepErfcPred_zero, cRepErfcNegOne, norm_mul]
    have hc : ‖(2 / Real.sqrt Real.pi : ℂ)‖ = 2 / Real.sqrt Real.pi := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, Complex.norm_ofNat]
    rw [hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_cexp_neg_sq_shift_le z s) (by positivity)
  | succ m => exact exists_norm_cRepErfc_shift_le m z

-- no-dlmf: integrability of the ray integrand of the 7.18.2 first equality; proof
-- infrastructure, no DLMF identity number
/-- `s ↦ i^{n−1}erfc(z+s)` is integrable on `(0,∞)`. -/
private theorem integrableOn_cRepErfcPred_shift (n : ℕ) (z : ℂ) :
    IntegrableOn (fun s : ℝ => cRepErfcPred n (z + (s : ℂ))) (Ioi (0 : ℝ)) := by
  obtain ⟨C, _, hb⟩ := exists_norm_cRepErfcPred_shift_le n z
  refine Integrable.mono' (integrableOn_gaussHalf.const_mul C) ?_ ?_
  · exact ((differentiable_cRepErfcPred n).continuous.comp
      (by fun_prop : Continuous fun s : ℝ => z + (s : ℂ))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hb s (le_of_lt hs)

-- no-dlmf: vanishing of `iⁿerfc` along horizontal rays; proof infrastructure, no
-- DLMF identity number
/-- `iⁿerfc(z+s) → 0` as `s → +∞` along a horizontal ray. -/
private theorem tendsto_cRepErfc_shift (n : ℕ) (z : ℂ) :
    Tendsto (fun s : ℝ => cRepErfc n (z + (s : ℂ))) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_norm_cRepErfc_shift_le n z
  have h1 : Tendsto (fun s : ℝ => -(s ^ 2) / 2) atTop atBot := by
    have h2 : Tendsto (fun s : ℝ => s ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    exact (tendsto_neg_atTop_atBot.comp h2).congr (fun s => by simp [Function.comp]; ring)
  have h3 : Tendsto (fun s : ℝ => C * Real.exp (-(s ^ 2) / 2)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp h1).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact hb s hs

-- no-dlmf: the `ℝ`-variable derivative of `iⁿerfc` along a horizontal ray; proof
-- infrastructure, no DLMF identity number
/-- `d/ds iⁿerfc(z+s) = −i^{n−1}erfc(z+s)` for the real ray parameter `s`. -/
private theorem hasDerivAt_cRepErfc_shift (n : ℕ) (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => cRepErfc n (z + (t : ℂ))) (-cRepErfcPred n (z + (s : ℂ))) s := by
  have hg : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_add z
  have h := (hasDerivAt_cRepErfc n (z + (s : ℂ))).scomp s hg
  simpa [Function.comp] using h

-- no-dlmf: chain link 7.18.2 (assembled in `cerf_7_18_2` below); the first
-- equality of the display, along the horizontal ray `t = z + s`
/-- `iⁿerfc(z) = ∫_z^∞ i^{n−1}erfc(t) dt` along the horizontal ray `t = z + s`,
uniformly for every `n = 0, 1, 2, …`. -/
theorem cRepErfc_eq_integral_pred (n : ℕ) (z : ℂ) :
    cRepErfc n z = ∫ s in Ioi (0 : ℝ), cRepErfcPred n (z + (s : ℂ)) := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => cRepErfc n (z + (t : ℂ))) (-cRepErfcPred n (z + (s : ℂ))) s :=
    fun s _ => hasDerivAt_cRepErfc_shift n z s
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_cRepErfcPred_shift n z).neg (tendsto_cRepErfc_shift n z)
  rw [integral_neg] at h
  simp only [Complex.ofReal_zero, add_zero, zero_sub, neg_inj] at h
  exact h.symm

/-- **DLMF 7.18.2.** The repeated integral `iⁿerfc(z)` for complex `z` and every
`n = 0, 1, 2, …`, both as the ray integral of the previous member of the family
and in the closed form `(2/√π) ∫_z^∞ (t−z)ⁿ/n!·e^{−t²} dt`; both `∫_z^∞` are read
along the horizontal ray `t = z + s`, `s ∈ (0,∞)`.

DLMF 7.18.2.
DAG: E-7.18.2.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_2 (n : ℕ) (z : ℂ) :
    cRepErfc n z = ∫ s in Ioi (0 : ℝ), cRepErfcPred n (z + (s : ℂ)) ∧
    cRepErfc n z = (2 / Real.sqrt Real.pi : ℂ) *
      ∫ s in Ioi (0 : ℝ),
        (((z + (s : ℂ)) - z) ^ n / (n.factorial : ℂ)) * Complex.exp (-(z + (s : ℂ)) ^ 2) :=
  ⟨cRepErfc_eq_integral_pred n z, by
    rw [cRepErfc]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 2
    ring⟩

/-! ## DLMF 7.18.4 — the `n`-th derivative of `e^{z²}erfc z` -/

-- no-dlmf: derivative of `e^{z²}·iⁿerfc(z)`; support lemma for DLMF 7.18.4, no
-- separate DLMF identity number
/-- `d/dz (e^{z²}·iⁿerfc(z)) = −2(n+1)·e^{z²}·i^{n+1}erfc(z)` over `ℂ`, the single
derivative step powering DLMF 7.18.4 (from 7.18.3 and the recurrence 7.18.7). -/
theorem hasDerivAt_expSq_mul_cRepErfc (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (w ^ 2) * cRepErfc n w)
      (-(2 * ((n : ℂ) + 1)) * (Complex.exp (z ^ 2) * cRepErfc (n + 1) z)) z := by
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w ^ 2)) (Complex.exp (z ^ 2) * (2 * z)) z := by
    have hsq : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    exact hsq.cexp
  have h := hexp.mul (hasDerivAt_cRepErfc n z)
  have h7 : 2 * ((n : ℂ) + 1) * cRepErfc (n + 1) z
      = cRepErfcPred n z - 2 * z * cRepErfc n z := by
    simpa using cerf_7_18_7 n z
  have hval : Complex.exp (z ^ 2) * (2 * z) * cRepErfc n z
        + Complex.exp (z ^ 2) * -cRepErfcPred n z
      = -(2 * ((n : ℂ) + 1)) * (Complex.exp (z ^ 2) * cRepErfc (n + 1) z) := by
    linear_combination Complex.exp (z ^ 2) * h7
  rw [hval] at h
  exact h

/-- **DLMF 7.18.4.** `dⁿ/dzⁿ (e^{z²}erfc z) = (−1)ⁿ 2ⁿ n! e^{z²} iⁿerfc(z)` for
complex `z` and every `n = 0, 1, 2, …`.

DLMF 7.18.4.
DAG: E-7.18.4.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_4 (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => Complex.exp (w ^ 2) * cerfc w) z =
      (-1) ^ n * 2 ^ n * (n.factorial : ℂ) * Complex.exp (z ^ 2) * cRepErfc n z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, cRepErfc_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun w : ℂ => Complex.exp (w ^ 2) * cerfc w)
        = fun w : ℂ => (-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ) * Complex.exp (w ^ 2)
          * cRepErfc n w :=
      funext fun w => ih w
    rw [hfun]
    have hd : HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ)
          * Complex.exp (w ^ 2) * cRepErfc n w)
        ((-1) ^ (n + 1) * 2 ^ (n + 1) * (((n + 1).factorial : ℕ) : ℂ) * Complex.exp (z ^ 2)
          * cRepErfc (n + 1) z) z := by
      have h := (hasDerivAt_expSq_mul_cRepErfc n z).const_mul
        ((-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ))
      have hfeq : (fun w : ℂ => (-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ)
            * (Complex.exp (w ^ 2) * cRepErfc n w))
          = fun w : ℂ => (-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ) * Complex.exp (w ^ 2)
            * cRepErfc n w := funext fun w => by ring
      rw [hfeq] at h
      have hveq : (-1 : ℂ) ^ n * 2 ^ n * (n.factorial : ℂ)
            * (-(2 * ((n : ℂ) + 1)) * (Complex.exp (z ^ 2) * cRepErfc (n + 1) z))
          = (-1) ^ (n + 1) * 2 ^ (n + 1) * (((n + 1).factorial : ℕ) : ℂ) * Complex.exp (z ^ 2)
            * cRepErfc (n + 1) z := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hveq] at h
      exact h
    rw [hd.deriv]

/-! ## DLMF 7.18.5 — the differential equation -/

/-- **DLMF 7.18.5.** Every member `W(z) = A·iⁿerfc(z) + B·iⁿerfc(−z)` of the
general solution family, with **arbitrary complex constants** `A`, `B` and
complex variable `z`, satisfies `W'' + 2z W′ − 2n W = 0`, for `n = 1, 2, 3, …`.

DLMF 7.18.5.
DAG: E-7.18.5.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_5 (n : ℕ) (hn : 1 ≤ n) (A B : ℂ) (z : ℂ) :
    deriv (deriv (fun w : ℂ => A * cRepErfc n w + B * cRepErfc n (-w))) z
      + 2 * z * deriv (fun w : ℂ => A * cRepErfc n w + B * cRepErfc n (-w)) z
      - 2 * (n : ℂ) * (A * cRepErfc n z + B * cRepErfc n (-z)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  -- first derivative
  have hW : ∀ y : ℂ, HasDerivAt (fun w : ℂ => A * cRepErfc (m + 1) w + B * cRepErfc (m + 1) (-w))
      (A * -cRepErfc m y + B * cRepErfc m (-y)) y := by
    intro y
    have hA : HasDerivAt (fun w : ℂ => A * cRepErfc (m + 1) w) (A * -cRepErfc m y) y := by
      have h := (hasDerivAt_cRepErfc (m + 1) y).const_mul A
      simpa using h
    have hB : HasDerivAt (fun w : ℂ => cRepErfc (m + 1) (-w)) (cRepErfc m (-y)) y := by
      have h := (hasDerivAt_cRepErfc (m + 1) (-y)).comp y (hasDerivAt_neg y)
      simpa [Function.comp] using h
    exact hA.add (hB.const_mul B)
  have hd1 : deriv (fun w : ℂ => A * cRepErfc (m + 1) w + B * cRepErfc (m + 1) (-w))
      = fun y : ℂ => A * -cRepErfc m y + B * cRepErfc m (-y) :=
    funext fun y => (hW y).deriv
  simp only [hd1]
  -- second derivative
  have h1 : HasDerivAt (fun y : ℂ => -cRepErfc m y) (cRepErfcPred m z) z := by
    simpa using (hasDerivAt_cRepErfc m z).neg
  have h2 : HasDerivAt (fun y : ℂ => cRepErfc m (-y)) (cRepErfcPred m (-z)) z := by
    have h := (hasDerivAt_cRepErfc m (-z)).comp z (hasDerivAt_neg z)
    simpa [Function.comp] using h
  have hcomb : HasDerivAt (fun y : ℂ => A * -cRepErfc m y + B * cRepErfc m (-y))
      (A * cRepErfcPred m z + B * cRepErfcPred m (-z)) z :=
    (h1.const_mul A).add (h2.const_mul B)
  rw [hcomb.deriv]
  have hr1 := cerf_7_18_7 m z
  have hr2 := cerf_7_18_7 m (-z)
  simp only [cRepErfcPred_succ] at hr1 hr2
  push_cast
  linear_combination (-A) * hr1 + (-B) * hr2

/-! ## DLMF 7.18.8 — the Hermite bridge -/

/-- **DLMF 7.18.8.** The symmetric combination
`(−1)ⁿiⁿerfc(z) + iⁿerfc(−z) = i^{−n}/(2^{n−1}n!)·Hₙ(iz)` for complex `z`, with
`Hₙ` the physicists' Hermite polynomial
(`FLMF.Functions.Hermite.physicistsHermite`); `i^{−n} = (−i)ⁿ` and
`1/2^{n−1} = 2/2ⁿ` avoid negative/`Nat`-subtraction exponents.

DLMF 7.18.8.
DAG: E-7.18.8.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_8 (n : ℕ) (z : ℂ) :
    (-1) ^ n * cRepErfc n z + cRepErfc n (-z) =
      (2 * (-Complex.I) ^ n / ((2 : ℂ) ^ n * (n.factorial : ℂ))) *
        Polynomial.aeval (Complex.I * z)
          (FLMF.Functions.Hermite.physicistsHermite n) := by
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real
    (f := fun w : ℂ => (-1) ^ n * cRepErfc n w + cRepErfc n (-w))
    (g := fun w : ℂ => (2 * (-Complex.I) ^ n / ((2 : ℂ) ^ n * (n.factorial : ℂ))) *
      Polynomial.aeval (Complex.I * w) (FLMF.Functions.Hermite.physicistsHermite n))
    (((differentiable_cRepErfc n).const_mul _).add
      ((differentiable_cRepErfc n).comp differentiable_neg))
    (((Polynomial.differentiable_aeval
        (q := FLMF.Functions.Hermite.physicistsHermite n)).comp
      ((differentiable_const Complex.I).mul differentiable_id)).const_mul _)
    (fun x => ?_) z
  have h := erf_7_18_8 n x
  show (-1) ^ n * cRepErfc n (x : ℂ) + cRepErfc n (-(x : ℂ))
    = (2 * (-Complex.I) ^ n / ((2 : ℂ) ^ n * (n.factorial : ℂ))) *
      Polynomial.aeval (Complex.I * (x : ℂ)) (FLMF.Functions.Hermite.physicistsHermite n)
  rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring, cRepErfc_ofReal, cRepErfc_ofReal]
  push_cast at h ⊢
  linear_combination h

/-! ## DLMF 7.18.11 — the parabolic cylinder `U` representation -/

-- no-dlmf: entirety of the Kummer sum, no DLMF identity number
/-- `₁F₁ a b` is entire (radius `⊤`). -/
private theorem differentiable_kummerM (a b : ℂ) : Differentiable ℂ (fun w : ℂ => ₁F₁ a b w) := by
  have h := (FLMF.Hypergeometric.kummerM_hasFPowerSeriesOnBall
    (𝔸 := ℂ) (a := a) (b := b)).differentiableOn
  have huniv : Metric.eball (0 : ℂ) ⊤ = Set.univ := by
    ext y
    simp
  rw [huniv, differentiableOn_univ] at h
  exact h

-- no-dlmf: entirety of the complex parabolic cylinder `U`, no DLMF identity number
/-- `z ↦ U(a,z)` is entire (the even/odd Kummer basis is entire). -/
private theorem differentiable_UC (a : ℂ) :
    Differentiable ℂ (fun z : ℂ => FLMF.ParabolicCylinder.UC a z) := by
  have hker : ∀ p q : ℂ, Differentiable ℂ (fun z : ℂ => ₁F₁ p q (z ^ 2 / 2)) := by
    intro p q z
    exact (differentiable_kummerM p q (z ^ 2 / 2)).comp z (by fun_prop)
  unfold FLMF.ParabolicCylinder.UC FLMF.ParabolicCylinder.pcfEvenC FLMF.ParabolicCylinder.pcfOddC
  exact ((((Differentiable.cexp (by fun_prop)).mul (hker _ _))).const_mul _).add
    (((((differentiable_id.mul (Differentiable.cexp (by fun_prop)))).mul
      (hker _ _))).const_mul _)

-- no-dlmf: real↔complex bridge for the parabolic cylinder `U`, no DLMF identity number
/-- The real `U(a,x)` is the restriction of the complex `UC` to real arguments. -/
private theorem UC_ofReal (a x : ℝ) :
    ((FLMF.ParabolicCylinder.U a x : ℝ) : ℂ)
      = FLMF.ParabolicCylinder.UC (a : ℂ) (x : ℂ) := by
  unfold FLMF.ParabolicCylinder.U FLMF.ParabolicCylinder.UC FLMF.ParabolicCylinder.pcfEven
    FLMF.ParabolicCylinder.pcfOdd FLMF.ParabolicCylinder.pcfEvenC FLMF.ParabolicCylinder.pcfOddC
  push_cast [← Complex.Gamma_ofReal, Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2),
    FLMF.Hypergeometric.kummerM_ofReal, Complex.ofReal_exp]
  ring

/-- **DLMF 7.18.11.** The parabolic cylinder `U` representation for complex `z`:
`iⁿerfc(z) = e^{−z²/2}/(2^{(n−1)/2}√π) · U(n+½, z√2)`, with `U` the complex
parabolic cylinder function `FLMF.ParabolicCylinder.UC`.

DLMF 7.18.11.
DAG: E-7.18.11.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_11 (n : ℕ) (z : ℂ) :
    cRepErfc n z =
      Complex.exp (-z ^ 2 / 2) /
          ((((2 : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (Real.sqrt Real.pi : ℂ)) *
        FLMF.ParabolicCylinder.UC ((n : ℂ) + 1 / 2) (z * (Real.sqrt 2 : ℂ)) := by
  have hUCz : Differentiable ℂ (fun w : ℂ =>
      FLMF.ParabolicCylinder.UC ((n : ℂ) + 1 / 2) (w * (Real.sqrt 2 : ℂ))) :=
    (differentiable_UC ((n : ℂ) + 1 / 2)).comp (differentiable_id.mul_const _)
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real (differentiable_cRepErfc n)
    (g := fun w : ℂ => Complex.exp (-w ^ 2 / 2) /
        ((((2 : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (Real.sqrt Real.pi : ℂ)) *
      FLMF.ParabolicCylinder.UC ((n : ℂ) + 1 / 2) (w * (Real.sqrt 2 : ℂ)))
    (((Differentiable.cexp (by fun_prop)).div_const _).mul hUCz)
    (fun x => ?_) z
  have h := congrArg (fun r : ℝ => (r : ℂ)) (erf_7_18_11 n x)
  push_cast [UC_ofReal, Complex.ofReal_exp] at h
  rw [cRepErfc_ofReal]
  push_cast
  linear_combination h

/-! ## DLMF 7.18.6 — the Maclaurin series

The complex series is assembled the same way as its real ancestor: the even and
odd halves are the two Kummer series of the transformed 7.18.9 representation
(`erf_7_18_9_key`), interleaved by `HasSum.even_add_odd`.  The coefficient
identifications are the real ones (`erf_7_18_6_even`, `erf_7_18_6_odd` at `z = 1`,
which is exactly the coefficient statement) cast into `ℂ`; the sum function is
entire, so the identification with `cRepErfc n` is an identity-theorem transfer. -/

section Maclaurin

open FLMF.Hypergeometric

-- no-dlmf: `Complex.Gamma`-at-a-real-argument helper, proof infrastructure
/-- `Γ(w) = ↑Γ(y)` whenever `w` is the cast of the real number `y`. -/
private theorem gammaC_ofReal_eq (y : ℝ) (w : ℂ) (h : w = ((y : ℝ) : ℂ)) :
    Complex.Gamma w = ((Real.Gamma y : ℝ) : ℂ) := by
  rw [h, Complex.Gamma_ofReal]

-- no-dlmf: even-index (k = 2j) coefficient identification for the complex 7.18.6
-- Maclaurin series; the cast of `erf_7_18_6_even` at `z = 1`
/-- Even-index term identification for the complex 7.18.6 series. -/
private theorem cerf_7_18_6_even (n : ℕ) (z : ℂ) (j : ℕ) :
    kummerCoefficient (-(n : ℂ) / 2) (1/2 : ℂ) j * (-z ^ 2) ^ j
        / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
      = (-1 : ℂ) ^ (2 * j) * z ^ (2 * j) /
          ((((2 : ℝ) ^ ((n : ℝ) - (2 * j : ℕ)) : ℝ) : ℂ) * (((2 * j).factorial : ℕ) : ℂ) *
            Complex.Gamma (1 + ((n : ℂ) - (2 * j : ℕ)) / 2)) := by
  have hr := erf_7_18_6_even n 1 j
  norm_num at hr
  have hkc : kummerCoefficient (-(n : ℂ) / 2) (1/2 : ℂ) j
      = ((kummerCoefficient (-(n : ℝ) / 2) (1/2 : ℝ) j : ℝ) : ℂ) := by
    rw [kummerCoefficient_ofReal]; push_cast; ring_nf
  obtain ⟨c, hc⟩ : ∃ c : ℝ, kummerCoefficient (-(n : ℝ) / 2) (1/2 : ℝ) j = c := ⟨_, rfl⟩
  rw [hc] at hr hkc
  have hΓ1 : Complex.Gamma ((n : ℂ) / 2 + 1) = ((Real.Gamma ((n : ℝ) / 2 + 1) : ℝ) : ℂ) :=
    gammaC_ofReal_eq _ _ (by push_cast; ring)
  have hΓ2 : Complex.Gamma (1 + ((n : ℂ) - (2 * j : ℕ)) / 2)
      = ((Real.Gamma (1 + ((n : ℝ) - 2 * (j : ℝ)) / 2) : ℝ) : ℂ) :=
    gammaC_ofReal_eq _ _ (by push_cast; ring)
  have hP : ((2 : ℝ) ^ ((n : ℝ) - ((2 * j : ℕ) : ℝ)) : ℝ)
      = (2 : ℝ) ^ ((n : ℝ) - 2 * (j : ℝ)) := by congr 1; push_cast; ring
  have hz : (-z ^ 2 : ℂ) ^ j = (-1) ^ j * z ^ (2 * j) := by rw [neg_pow, ← pow_mul]
  have hone : ((-1 : ℂ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [hkc, hΓ1, hΓ2, hP, hz, hone]
  have hrC := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at hrC
  linear_combination (z ^ (2 * j)) * hrC

-- no-dlmf: odd-index (k = 2j+1) coefficient identification for the complex 7.18.6
-- Maclaurin series; the cast of `erf_7_18_6_odd` at `z = 1`
/-- Odd-index term identification for the complex 7.18.6 series. -/
private theorem cerf_7_18_6_odd (n : ℕ) (z : ℂ) (j : ℕ) :
    -(z * (kummerCoefficient ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) j * (-z ^ 2) ^ j)
        / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2)))
      = (-1 : ℂ) ^ (2 * j + 1) * z ^ (2 * j + 1) /
          ((((2 : ℝ) ^ ((n : ℝ) - (2 * j + 1 : ℕ)) : ℝ) : ℂ) *
            (((2 * j + 1).factorial : ℕ) : ℂ) *
            Complex.Gamma (1 + ((n : ℂ) - (2 * j + 1 : ℕ)) / 2)) := by
  have hr := erf_7_18_6_odd n 1 j
  norm_num at hr
  rw [show ((-1 : ℝ)) ^ (2 * j + 1) = -1 from by rw [pow_succ, pow_mul]; norm_num] at hr
  have hkc : kummerCoefficient ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) j
      = ((kummerCoefficient ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) j : ℝ) : ℂ) := by
    rw [kummerCoefficient_ofReal]; push_cast; ring_nf
  obtain ⟨c, hc⟩ : ∃ c : ℝ, kummerCoefficient ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) j = c :=
    ⟨_, rfl⟩
  rw [hc] at hr hkc
  have hΓ1 : Complex.Gamma ((n : ℂ) / 2 + 1/2) = ((Real.Gamma ((n : ℝ) / 2 + 1/2) : ℝ) : ℂ) :=
    gammaC_ofReal_eq _ _ (by push_cast; ring)
  have hΓ2 : Complex.Gamma (1 + ((n : ℂ) - (2 * j + 1 : ℕ)) / 2)
      = ((Real.Gamma (1 + ((n : ℝ) - (2 * (j : ℝ) + 1)) / 2) : ℝ) : ℂ) :=
    gammaC_ofReal_eq _ _ (by push_cast; ring)
  have hP : ((2 : ℝ) ^ ((n : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) : ℝ)
      = (2 : ℝ) ^ ((n : ℝ) - (2 * (j : ℝ) + 1)) := by congr 1; push_cast; ring
  have hz : (-z ^ 2 : ℂ) ^ j = (-1) ^ j * z ^ (2 * j) := by rw [neg_pow, ← pow_mul]
  have hone : ((-1 : ℂ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hkc, hΓ1, hΓ2, hP, hz, hone]
  have hrC := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at hrC
  linear_combination (z ^ (2 * j + 1)) * hrC

-- no-dlmf: `HasSum` assembly of the complex 7.18.6 Maclaurin series (even/odd
-- interleaving of the two Kummer series); support for `cerf_7_18_6`
/-- The complex 7.18.6 series sums to the transformed Kummer pair of 7.18.9. -/
private theorem cerf_7_18_6_hasSum (n : ℕ) (z : ℂ) :
    HasSum (fun k : ℕ =>
        (-1 : ℂ) ^ k * z ^ k /
          ((((2 : ℝ) ^ ((n : ℝ) - k) : ℝ) : ℂ) * (k.factorial : ℂ) *
            Complex.Gamma (1 + ((n : ℂ) - k) / 2)))
      (₁F₁ (-(n : ℂ) / 2) (1/2 : ℂ) (-z ^ 2) / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
        - z * ₁F₁ ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) (-z ^ 2)
            / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2))) := by
  rw [sub_eq_add_neg]
  refine HasSum.even_add_odd ?_ ?_
  · have He := (kummerM_hasSum (-(n : ℂ) / 2) (1/2 : ℂ) (-z ^ 2)).div_const
      ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
    have hfe : (fun j : ℕ => kummerCoefficient (-(n : ℂ) / 2) (1/2 : ℂ) j * (-z ^ 2) ^ j
          / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1)))
        = fun j : ℕ => (-1 : ℂ) ^ (2 * j) * z ^ (2 * j) /
            ((((2 : ℝ) ^ ((n : ℝ) - (2 * j : ℕ)) : ℝ) : ℂ) * (((2 * j).factorial : ℕ) : ℂ) *
              Complex.Gamma (1 + ((n : ℂ) - (2 * j : ℕ)) / 2)) :=
      funext fun j => cerf_7_18_6_even n z j
    rw [hfe] at He
    exact He
  · have Ho := (((kummerM_hasSum ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ)
        (-z ^ 2)).mul_left z).div_const
      ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2))).neg
    have hfo : (fun j : ℕ => -(z * (kummerCoefficient ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) j
            * (-z ^ 2) ^ j)
          / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2))))
        = fun j : ℕ => (-1 : ℂ) ^ (2 * j + 1) * z ^ (2 * j + 1) /
            ((((2 : ℝ) ^ ((n : ℝ) - (2 * j + 1 : ℕ)) : ℝ) : ℂ) *
              (((2 * j + 1).factorial : ℕ) : ℂ) *
              Complex.Gamma (1 + ((n : ℂ) - (2 * j + 1 : ℕ)) / 2)) :=
      funext fun j => cerf_7_18_6_odd n z j
    rw [hfo] at Ho
    exact Ho

-- no-dlmf: entirety of the transformed Kummer pair; support for `cerf_7_18_6`
/-- The transformed Kummer pair of 7.18.9 is entire in `z`. -/
private theorem differentiable_cRepErfcKummer (n : ℕ) : Differentiable ℂ (fun w : ℂ =>
    ₁F₁ (-(n : ℂ) / 2) (1/2 : ℂ) (-w ^ 2) / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
      - w * ₁F₁ ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) (-w ^ 2)
          / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2))) := by
  have hc : Differentiable ℂ (fun w : ℂ => -w ^ 2) := by fun_prop
  exact (((differentiable_kummerM _ _).comp hc).div_const _).sub
    ((differentiable_id.mul ((differentiable_kummerM _ _).comp hc)).div_const _)

-- no-dlmf: complex form of the transformed 7.18.9 representation; support for
-- `cerf_7_18_6` (the tagged 7.18.9 surface is the real `erf_7_18_9`)
/-- `iⁿerfc(z) = M(−n/2,1/2,−z²)/(2ⁿΓ(n/2+1)) − z·M(1/2−n/2,3/2,−z²)/(2^{n−1}Γ(n/2+1/2))`
for complex `z`: the identity-theorem transfer of `erf_7_18_9_key`. -/
theorem cRepErfc_eq_kummerPair (n : ℕ) (z : ℂ) :
    cRepErfc n z =
      ₁F₁ (-(n : ℂ) / 2) (1/2 : ℂ) (-z ^ 2) / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
        - z * ₁F₁ ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) (-z ^ 2)
            / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1/2)) := by
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real (differentiable_cRepErfc n)
    (differentiable_cRepErfcKummer n) (fun x => ?_) z
  have hM1 : ((₁F₁ (-(n : ℝ) / 2) (1/2 : ℝ) (-x ^ 2) : ℝ) : ℂ)
      = ₁F₁ (-(n : ℂ) / 2) (1/2 : ℂ) (-(x : ℂ) ^ 2) := by
    rw [kummerM_ofReal]; push_cast; ring_nf
  have hM2 : ((₁F₁ ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) (-x ^ 2) : ℝ) : ℂ)
      = ₁F₁ ((1 : ℂ) / 2 - (n : ℂ) / 2) (3/2 : ℂ) (-(x : ℂ) ^ 2) := by
    rw [kummerM_ofReal]; push_cast; ring_nf
  have hΓ1 : ((Real.Gamma ((n : ℝ) / 2 + 1) : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) / 2 + 1) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hΓ2 : ((Real.Gamma ((n : ℝ) / 2 + 1/2) : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) / 2 + 1/2) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  show cRepErfc n (x : ℂ) = _
  rw [cRepErfc_ofReal, erf_7_18_9_key n x]
  push_cast
  rw [hM1, hM2, hΓ1, hΓ2]

/-- **DLMF 7.18.6.** The Maclaurin series of `iⁿerfc` for complex `z`:
`iⁿerfc(z) = ∑_{k≥0} (−1)ᵏ zᵏ / (2^{n−k} k! Γ(1+(n−k)/2))`.

The exponent `n−k` may be negative, so `2^{n−k}` is the *real* power `rpow` cast
into `ℂ` (the exponent is real, so no branch cut is introduced); at a
non-positive integer argument `Γ` has its pole and Mathlib's `Complex.Gamma` is
`0` there, so the corresponding terms vanish — exactly as in the handbook
truncation.

DLMF 7.18.6.
DAG: E-7.18.6.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_6 (n : ℕ) (z : ℂ) :
    cRepErfc n z =
      ∑' k : ℕ,
        (-1 : ℂ) ^ k * z ^ k /
          ((((2 : ℝ) ^ ((n : ℝ) - k) : ℝ) : ℂ) * (k.factorial : ℂ) *
            Complex.Gamma (1 + ((n : ℂ) - k) / 2)) := by
  rw [(cerf_7_18_6_hasSum n z).tsum_eq]
  exact cRepErfc_eq_kummerPair n z

/-! ## DLMF 7.18.9 — the Kummer `M` pair -/

-- no-dlmf: entirety of the 7.18.9 Kummer pair; support for `cerf_7_18_9`
/-- The `e^{−z²}`-weighted Kummer pair of 7.18.9 is entire in `z`. -/
private theorem differentiable_cRepErfcKummerM (n : ℕ) : Differentiable ℂ (fun w : ℂ =>
    Complex.exp (-w ^ 2) *
      (₁F₁ ((n : ℂ) / 2 + 1 / 2) (1 / 2 : ℂ) (w ^ 2)
          / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
        - w * ₁F₁ ((n : ℂ) / 2 + 1) (3 / 2 : ℂ) (w ^ 2)
            / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1 / 2)))) := by
  have hsq : Differentiable ℂ (fun w : ℂ => w ^ 2) := by fun_prop
  exact (Differentiable.cexp (by fun_prop)).mul
    ((((differentiable_kummerM _ _).comp hsq).div_const _).sub
      ((differentiable_id.mul ((differentiable_kummerM _ _).comp hsq)).div_const _))

/-- **DLMF 7.18.9.** The Kummer `M` (`₁F₁`) representation of `iⁿerfc` for complex
`z`: `iⁿerfc(z) = e^{−z²}( M(n/2+1/2,1/2,z²)/(2ⁿΓ(n/2+1))
− z·M(n/2+1,3/2,z²)/(2^{n−1}Γ(n/2+1/2)) )`.

The factor `2^{n−1}` is kept as a *real* power `rpow` cast into `ℂ` (the exponent
is real, so no branch cut is introduced).

DLMF 7.18.9.
DAG: E-7.18.9.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_9 (n : ℕ) (z : ℂ) :
    cRepErfc n z =
      Complex.exp (-z ^ 2) *
        (₁F₁ ((n : ℂ) / 2 + 1 / 2) (1 / 2 : ℂ) (z ^ 2)
            / ((2 : ℂ) ^ n * Complex.Gamma ((n : ℂ) / 2 + 1))
          - z * ₁F₁ ((n : ℂ) / 2 + 1) (3 / 2 : ℂ) (z ^ 2)
              / ((((2 : ℝ) ^ ((n : ℝ) - 1) : ℝ) : ℂ) * Complex.Gamma ((n : ℂ) / 2 + 1 / 2))) := by
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real (differentiable_cRepErfc n)
    (differentiable_cRepErfcKummerM n) (fun x => ?_) z
  have hM1 : ((₁F₁ ((n : ℝ) / 2 + 1 / 2) (1 / 2 : ℝ) (x ^ 2) : ℝ) : ℂ)
      = ₁F₁ ((n : ℂ) / 2 + 1 / 2) (1 / 2 : ℂ) ((x : ℂ) ^ 2) := by
    rw [kummerM_ofReal]; push_cast; ring_nf
  have hM2 : ((₁F₁ ((n : ℝ) / 2 + 1) (3 / 2 : ℝ) (x ^ 2) : ℝ) : ℂ)
      = ₁F₁ ((n : ℂ) / 2 + 1) (3 / 2 : ℂ) ((x : ℂ) ^ 2) := by
    rw [kummerM_ofReal]; push_cast; ring_nf
  have hΓ1 : ((Real.Gamma ((n : ℝ) / 2 + 1) : ℝ) : ℂ) = Complex.Gamma ((n : ℂ) / 2 + 1) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hΓ2 : ((Real.Gamma ((n : ℝ) / 2 + 1 / 2) : ℝ) : ℂ)
      = Complex.Gamma ((n : ℂ) / 2 + 1 / 2) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  show cRepErfc n (x : ℂ) = _
  rw [cRepErfc_ofReal, erf_7_18_9 n x]
  push_cast [Complex.ofReal_exp]
  rw [hM1, hM2, hΓ1, hΓ2]

end Maclaurin

/-! ## DLMF 7.18.12 — the probability function `Hhₙ`

DLMF §7.18(iv) reads `Hhₙ` as a complex-variable object too, so the real
`FLMF.Error.Hh` is complexified here by the same horizontal-ray device used for
`cRepErfc`: `Hhₙ(z) = (1/n!) ∫_z^∞ (t−z)ⁿ e^{−t²/2} dt` becomes
`(1/n!) ∫_0^∞ sⁿ e^{−(z+s)²/2} ds` under `t = z + s`.  The kernel decays like
`e^{−s²/4}` locally uniformly in `z`, so `HhC n` is entire. -/

-- no-dlmf: Gaussian norm bound for the `Hh` kernel; proof infrastructure, no
-- DLMF identity number
/-- `‖e^{−(z+s)²/2}‖ ≤ e^{(Im z)²/2+(Re z)²/2}·e^{−s²/4}` for real `s`. -/
private theorem norm_cexp_neg_sq_half_shift_le (z : ℂ) (s : ℝ) :
    ‖Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)‖
      ≤ Real.exp ((z.im ^ 2 + z.re ^ 2) / 2) * Real.exp (-(s ^ 2) / 4) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-(z + (s : ℂ)) ^ 2 / 2).re = (z.im ^ 2 - (z.re + s) ^ 2) / 2 := by
    simp [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre]
  nlinarith [sq_nonneg (2 * z.re + s)]

-- no-dlmf: integrability of the polynomial-times-Gaussian majorant; proof
-- infrastructure, no DLMF identity number
/-- `s ↦ sᵏ e^{−s²/4}` is integrable on `(0,∞)`. -/
private theorem integrableOn_pow_mul_gaussQuarter (k : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ k * Real.exp (-(s ^ 2) / 4)) (Ioi (0 : ℝ)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ) / 4) (by norm_num) hk
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  rw [Real.rpow_natCast]
  congr 1
  ring_nf

-- no-dlmf: the complex probability-function `Hhₙ` def; the 7.18.12 display is
-- surfaced at `cerf_7_18_12`
/-- **The probability function `Hhₙ` for a complex variable** (DLMF §7.18(iv),
§12.7), as the horizontal-ray form of `Hhₙ(z) = (1/n!)∫_z^∞ (t−z)ⁿ e^{−t²/2} dt`:

`Hhₙ(z) = (1/n!) ∫_0^∞ sⁿ e^{−(z+s)²/2} ds`.

The real `FLMF.Error.Hh` is its restriction to the real axis (`HhC_ofReal`). -/
noncomputable def HhC (n : ℕ) (z : ℂ) : ℂ :=
  (1 / (n.factorial : ℂ)) *
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n * Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)

-- no-dlmf: integrability of the complex `Hh` ray kernel; proof infrastructure,
-- no DLMF identity number
/-- The kernel `s ↦ sⁿ·e^{−(z+s)²/2}` is integrable on `(0,∞)` for every complex `z`. -/
theorem integrableOn_HhCKernel (n : ℕ) (z : ℂ) :
    IntegrableOn (fun s : ℝ =>
      (s : ℂ) ^ n * Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono'
    ((integrableOn_pow_mul_gaussQuarter n).const_mul
      (Real.exp ((z.im ^ 2 + z.re ^ 2) / 2))) ?_ ?_
  · exact ((Complex.continuous_ofReal.pow n).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have h := norm_cexp_neg_sq_half_shift_le z s
    calc s ^ n * ‖Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)‖
        ≤ s ^ n * (Real.exp ((z.im ^ 2 + z.re ^ 2) / 2) * Real.exp (-(s ^ 2) / 4)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.exp ((z.im ^ 2 + z.re ^ 2) / 2) * (s ^ n * Real.exp (-(s ^ 2) / 4)) := by ring

-- no-dlmf: qualitative support lemma (entirety of the complex `Hh`), no numbered
-- DLMF display
/-- The `Hh` ray integral is analytic on all of `ℂ`, by differentiation under the
integral sign with the locally uniform majorant
`(‖a‖+1+s)·sⁿ·e^{(‖a‖+1)²}e^{−s²/4}` on `ball a 1`. -/
private theorem analyticOnNhd_HhCIntegral (n : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n * Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)) Set.univ := by
  refine FLMF.Methods.analyticOnNhd_integral_of_locallyDominated
    (f := fun (z : ℂ) (s : ℝ) => (s : ℂ) ^ n * Complex.exp (-(z + (s : ℂ)) ^ 2 / 2))
    (f' := fun (z : ℂ) (s : ℝ) =>
      (s : ℂ) ^ n * (-(z + (s : ℂ)) * Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)))
    isOpen_univ ?_ ?_ ?_ ?_ ?_
  · intro z _
    exact ((Complex.continuous_ofReal.pow n).mul
      (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · intro z _
    exact integrableOn_HhCKernel n z
  · intro z _
    exact ((Complex.continuous_ofReal.pow n).mul
      (((continuous_const.add Complex.continuous_ofReal).neg).mul
        (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    intro z _
    have h1 : HasDerivAt (fun w : ℂ => -(w + (s : ℂ)) ^ 2 / 2) (-(z + (s : ℂ))) z := by
      have h := ((((hasDerivAt_id z).add_const ((s : ℂ))).pow 2).neg).div_const 2
      convert h using 1
      simp only [id_eq]
      ring
    have h2 := (h1.cexp).const_mul ((s : ℂ) ^ n)
    convert h2 using 1
    ring
  · intro a _
    refine ⟨1, one_pos, fun s =>
      ((‖a‖ + 1) * Real.exp ((‖a‖ + 1) ^ 2)) * (s ^ n * Real.exp (-(s ^ 2) / 4))
        + Real.exp ((‖a‖ + 1) ^ 2) * (s ^ (n + 1) * Real.exp (-(s ^ 2) / 4)), ?_, ?_⟩
    · exact ((integrableOn_pow_mul_gaussQuarter n).const_mul _).add
        ((integrableOn_pow_mul_gaussQuarter (n + 1)).const_mul _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs z hz
      have hs0 : (0 : ℝ) < s := hs
      have hznorm : ‖z‖ ≤ ‖a‖ + 1 := by
        have h := mem_ball_iff_norm.mp hz
        calc ‖z‖ = ‖a + (z - a)‖ := by ring_nf
          _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
          _ ≤ ‖a‖ + 1 := by linarith
      have hgauss : ‖Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)‖
          ≤ Real.exp ((‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 4) := by
        refine (norm_cexp_neg_sq_half_shift_le z s).trans ?_
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
        have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
        have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        have h1 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
        have h2 : z.re ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
        have h3 : ‖z‖ ^ 2 ≤ (‖a‖ + 1) ^ 2 := by nlinarith [norm_nonneg z]
        nlinarith
      have hlin : ‖-(z + (s : ℂ))‖ ≤ (‖a‖ + 1) + s := by
        rw [norm_neg]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
        linarith
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      have hstep : ‖-(z + (s : ℂ))‖ * ‖Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)‖
          ≤ ((‖a‖ + 1) + s) * (Real.exp ((‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 4)) := by
        refine mul_le_mul hlin hgauss (norm_nonneg _) ?_
        positivity
      calc s ^ n * (‖-(z + (s : ℂ))‖ * ‖Complex.exp (-(z + (s : ℂ)) ^ 2 / 2)‖)
          ≤ s ^ n * (((‖a‖ + 1) + s) *
              (Real.exp ((‖a‖ + 1) ^ 2) * Real.exp (-(s ^ 2) / 4))) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = ((‖a‖ + 1) * Real.exp ((‖a‖ + 1) ^ 2)) * (s ^ n * Real.exp (-(s ^ 2) / 4))
            + Real.exp ((‖a‖ + 1) ^ 2) * (s ^ (n + 1) * Real.exp (-(s ^ 2) / 4)) := by
            ring

-- no-dlmf: qualitative support lemma (entirety of the complex `Hh`), no numbered
-- DLMF display
/-- `HhC n` is entire. -/
theorem differentiable_HhC (n : ℕ) : Differentiable ℂ (HhC n) := by
  rw [← differentiableOn_univ]
  refine AnalyticOnNhd.differentiableOn ?_
  intro z hz
  show AnalyticAt ℂ (fun w : ℂ => (1 / (n.factorial : ℂ)) *
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n * Complex.exp (-(w + (s : ℂ)) ^ 2 / 2)) z
  exact (analyticAt_const (v := (1 / (n.factorial : ℂ)))).mul
    (analyticOnNhd_HhCIntegral n z hz)

-- no-dlmf: foundational bridge lemma, no DLMF identity number
/-- **Agreement with the real `Hh`.** `HhC n ↑x = ↑(Hh n x)`. -/
theorem HhC_ofReal (n : ℕ) (x : ℝ) : HhC n (x : ℂ) = ((Hh n x : ℝ) : ℂ) := by
  have hreal : Hh n x
      = 1 / (n.factorial : ℝ) * ∫ s in Ioi (0 : ℝ), s ^ n * Real.exp (-(x + s) ^ 2 / 2) := by
    rw [Hh, integral_Ioi_shift (fun t : ℝ => (t - x) ^ n * Real.exp (-t ^ 2 / 2)) x]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 2
    ring
  rw [hreal, HhC]
  have hcast : (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n * Complex.exp (-((x : ℂ) + (s : ℂ)) ^ 2 / 2))
      = ((∫ s in Ioi (0 : ℝ), s ^ n * Real.exp (-(x + s) ^ 2 / 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    push_cast [Complex.ofReal_exp]
    ring_nf
  rw [hcast]
  push_cast
  ring

/-- **DLMF 7.18.12.** The probability-function representation of `iⁿerfc` for
complex `z`: `iⁿerfc(z) = 1/√(2^{n−1}π)·Hhₙ(√2·z)`, with `Hhₙ` the complex
probability function `HhC`.  The prefactor `√2/(√2)ⁿ = 2^{(1−n)/2} = 1/√(2^{n−1})`
is written with a `ℕ`-power `(√2)ⁿ` to avoid a half-integer/cast exponent.

DLMF 7.18.12.
DAG: E-7.18.12.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_18_12 (n : ℕ) (z : ℂ) :
    cRepErfc n z =
      ((Real.sqrt 2 : ℂ) / ((Real.sqrt 2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ))) *
        HhC n ((Real.sqrt 2 : ℂ) * z) := by
  refine FLMF.Methods.eqOn_of_entire_of_eqOn_real (differentiable_cRepErfc n)
    (g := fun w : ℂ =>
      ((Real.sqrt 2 : ℂ) / ((Real.sqrt 2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ))) *
        HhC n ((Real.sqrt 2 : ℂ) * w))
    (((differentiable_HhC n).comp (differentiable_const _ |>.mul differentiable_id)).const_mul _)
    (fun x => ?_) z
  have h := congrArg (fun r : ℝ => (r : ℂ)) (erf_7_18_12 n x)
  show cRepErfc n (x : ℂ) =
    ((Real.sqrt 2 : ℂ) / ((Real.sqrt 2 : ℂ) ^ n * (Real.sqrt Real.pi : ℂ))) *
      HhC n ((Real.sqrt 2 : ℂ) * (x : ℂ))
  rw [show ((Real.sqrt 2 : ℂ) * (x : ℂ)) = ((Real.sqrt 2 * x : ℝ) : ℂ) by push_cast; ring,
    HhC_ofReal, cRepErfc_ofReal]
  push_cast at h ⊢
  linear_combination h

end FLMF.Error
