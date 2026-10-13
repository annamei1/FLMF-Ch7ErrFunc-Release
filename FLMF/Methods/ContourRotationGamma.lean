import FLMF.Methods.ContourRotation
import FLMF.Methods.AbelianExp
import FLMF.Methods.BranchAlgebra
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Rotated Γ integrand — analytic foundations for the sector engine

The cpow foundations for rotating the Γ integral `Γ(s) = ∫₀^∞ t^{s-1}e^{-t} dt`
onto an interior ray `e^{iθ}·(0,∞)` (`0 ≤ θ < π/2`), via the sector form of the
rotation engine (`ray_rotation_sector` in [`ContourRotation.lean`](ContourRotation.lean)).
The Γ integrand `f(t) = t^{s-1}e^{-t}` has a branch-point singularity at `0`, so it
is *not* entire — but it is holomorphic on the open rotated rays, with the
boundary term `r·f(e^{iθ}r) → 0` killed by the `r` factor once `Re s > 0`, exactly
the situation the sector engine was built for.

The capstone is **`gamma_ray_rotation`**: `Γ(s) = e^{sθ₀i}∫₀^∞ r^{s-1}e^{-e^{iθ₀}r}dr`
for `Re s > 0`, `0 ≤ θ₀ < π/2` — the rotated-Γ representation, the sector engine
fully validated end-to-end on its target integrand.

Rotating to `θ₀ → π/2` (the imaginary axis) and then identifying the bare improper
integral **closes #7**: `mellin_exp_neg_I` proves
`∫₀^∞ t^{s-1}e^{-it}dt = e^{-iπs/2}Γ(s)` for `0 < Re s < 1` (the conditionally
convergent oscillatory integral, `lim_R ∫₀^R`), whose real/imaginary parts are the
cosine/sine Mellin transforms behind `Ci → 0`. The route: improper convergence by
IBP (`improper_converges`), the regularized value (`gamma_abel_regularized`), and
the Abel bridge `habel` (via `AbelianExp.abelian_exp_complex` on a bounded
continuous extension) matching the two limits.

* `cpow_rot_extract` (now in [`BranchAlgebra.lean`](BranchAlgebra.lean)) — the
  factorization `(e^{iθ}r)^w = r^w·e^{wθI}` (`r>0`, `|θ|<π`);
* `gam_hasDerivAt` — holomorphy of `t^{s-1}e^{-t}` on the rotated ray (discharges
  the sector engine's `hf`);
* `norm_gam_rot`, `norm_combo_le`, `dom_integrable` — the norm/integrability bounds;
* `integrable_gam_rot`, `hint_gam`, `hbdry_gam`, `hGcont_gam`, `hIderiv_gam` — the
  discharged `ray_rotation_sector` hypotheses;
* `integral_gam_eq_Gamma` — `∫₀^∞ t^{s-1}e^{-t} = Γ(s)`;
* `gamma_ray_rotation` — **the rotated-Γ representation**;
* `gamma_rotated_tendsto` — the `θ₀→π/2` boundary limit
  `lim ∫₀^∞ r^{s-1}e^{-e^{iθ₀}r}dr = e^{-iπs/2}Γ(s)` (rotation reaching the
  imaginary axis, toward #7);
* `scaled_gamma` — the complex-rate Laplace–Mellin formula
  `∫₀^∞ t^{s-1}e^{-ct}dt = c^{-s}Γ(s)` (`Re c>0`, `Im c≥0`), generalizing the
  representation via a real rescaling (Mathlib has only the real-rate case);
* `gamma_abel_regularized` — the Abel-regularized Mellin transform of `e^{-it}`,
  `lim_{ε↓0} ∫₀^∞ t^{s-1}e^{-(ε+i)t}dt = e^{-iπs/2}Γ(s)` (radial regularization);
* `integrable_tail` — the absolutely-convergent IBP tail `t^{s-2}e^{-it}` on `(1,∞)`
  (`Re s<1`);
* `tail_tendsto` — improper convergence of `∫_1^R t^{s-1}e^{-it}` (`Re s<1`), via
  one interval IBP + boundary decay `R^{Re s-1}→0` + the convergent tail;
* `improper_converges` — the full bare improper Mellin integral converges,
  `∫_0^R t^{s-1}e^{-it} → L` for `0<Re s<1` (splitting off the integrable
  singularity on `(0,1]`);
* `habel` — the Abel bridge: `∫_{(0,∞)} e^{-εt}t^{s-1}e^{-it} → L` as `ε↓0`;
* `mellin_exp_neg_I` — **#7 CLOSED:** `∫_0^∞ t^{s-1}e^{-it}dt = e^{-iπs/2}Γ(s)`
  (`0<Re s<1`), the Mellin transform of `e^{-it}` behind `Ci → 0`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FLMF.Methods.ContourRotation.Gamma

open FLMF.Methods.AbelianExp
-- `cpow_rot_extract`, `norm_cpow_rot` relocated to `Methods/BranchAlgebra.lean`
-- (M-branch-algebra); opened here for the proofs below.
open FLMF.Methods.BranchAlgebra

-- no-dlmf: proof-internal definition (rotated Γ integrand)
/-- The Γ integrand `t^{s-1}e^{-t}`. -/
noncomputable def gam (s : ℂ) : ℂ → ℂ := fun z => z ^ (s - 1) * Complex.exp (-z)

-- no-dlmf: proof-internal definition (derivative of the Γ integrand)
/-- Its derivative `(s-1)z^{s-2}e^{-z} - z^{s-1}e^{-z}` (valid on the slit plane). -/
noncomputable def gam' (s : ℂ) : ℂ → ℂ :=
  fun z => (s - 1) * z ^ (s - 1 - 1) * Complex.exp (-z) + z ^ (s - 1) * (-Complex.exp (-z))

-- no-dlmf: contour-rotation infrastructure, no DLMF equation
/-- The rotated point `e^{iθ}r` (`r>0`, `|θ|<π/2`) lies in the slit plane. -/
theorem rot_mem_slitPlane {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) {r : ℝ} (hr : 0 < r) :
    Complex.exp (θ * Complex.I) * (r : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have hre : (Complex.exp (θ * Complex.I) * (r : ℂ)).re = Real.cos θ * r := by
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre]; have := Real.cos_pos_of_mem_Ioo hθ; positivity

-- no-dlmf: holomorphy helper, no DLMF equation
/-- **Holomorphy on the rotated ray** (discharges the sector engine's `hf`): the Γ
integrand has derivative `gam'` at `e^{iθ}r` for `r > 0`, `|θ| < π/2`. -/
theorem gam_hasDerivAt (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (gam s) (gam' s (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (Complex.exp (θ * Complex.I) * (r : ℂ)) := by
  set z₀ := Complex.exp (θ * Complex.I) * (r : ℂ) with hz₀
  have hslit : z₀ ∈ Complex.slitPlane := rot_mem_slitPlane hθ hr
  have h1 : HasDerivAt (fun z : ℂ => z ^ (s - 1)) ((s - 1) * z₀ ^ (s - 1 - 1)) z₀ :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (Complex.exp (-z₀) * (-1)) z₀ := by
    have : HasDerivAt (fun z : ℂ => -z) (-1) z₀ := (hasDerivAt_id z₀).neg
    simpa using this.cexp
  have hmul := h1.mul h2
  unfold gam gam'
  convert hmul using 1
  ring

-- no-dlmf: norm-bound helper, no DLMF equation
/-- **Norm of the rotated Γ integrand.** For `r > 0`, `|θ| < π`,
`‖(e^{iθ}r)^{s-1} e^{-e^{iθ}r}‖ = r^{Re s-1} · e^{-θ·Im s} · e^{-r·cos θ}`. -/
theorem norm_gam_rot (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 < r) :
    ‖gam s (Complex.exp (θ * Complex.I) * (r : ℂ))‖
      = r ^ (s.re - 1) * Real.exp (-θ * s.im) * Real.exp (-(r * Real.cos θ)) := by
  rw [gam, norm_mul, cpow_rot_extract hθ hr, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp, Complex.norm_exp]
  have hre1 : ((s - 1) * (θ : ℂ) * Complex.I).re = -θ * s.im := by
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]; ring
  have hre2 : (-(Complex.exp (θ * Complex.I) * (r : ℂ))).re = -(r * Real.cos θ) := by
    rw [Complex.neg_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hre1, hre2, Complex.sub_re, Complex.one_re]

-- no-dlmf: continuity helper, no DLMF equation
/-- Continuity of the rotated Γ integrand on the open ray `r > 0`. -/
theorem continuousOn_gam_rot (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    ContinuousOn (fun r : ℝ => gam s (Complex.exp (θ * Complex.I) * (r : ℂ))) (Ioi 0) := by
  intro r hr
  have hslit : Complex.exp (θ * Complex.I) * (r : ℂ) ∈ Complex.slitPlane :=
    rot_mem_slitPlane hθ hr
  have hz : ContinuousAt (fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ)) r := by fun_prop
  have hcpow : ContinuousAt (fun z : ℂ => z ^ (s - 1)) (Complex.exp (θ * Complex.I) * (r : ℂ)) :=
    continuousAt_cpow_const hslit
  have h1 : ContinuousAt ((fun z : ℂ => z ^ (s - 1)) ∘
      (fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ))) r :=
    ContinuousAt.comp (f := fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ)) hcpow hz
  have h2 : ContinuousAt
      (fun r : ℝ => Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ)))) r := by fun_prop
  exact ((h1.mul h2).continuousWithinAt)

/-- **Convergence of the rotated Γ integral.** For `Re s > 0` and `|θ| < π/2`,
`r ↦ (e^{iθ}r)^{s-1} e^{-e^{iθ}r}` is integrable on `(0,∞)`: the singularity
`r^{Re s-1}` at `0` is integrable (`Re s > 0`) and the decay `e^{-r cosθ}` holds
(`cos θ > 0`). -/
-- no-dlmf: integrability helper, no DLMF equation
theorem integrable_gam_rot (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    IntegrableOn (fun r : ℝ => gam s (Complex.exp (θ * Complex.I) * (r : ℂ))) (Ioi 0) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hθπ : θ ∈ Ioo (-π) π :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hbase : IntegrableOn
      (fun r : ℝ => r ^ (s.re - 1) * Real.exp (-(Real.cos θ) * r ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : (-1 : ℝ) < s.re - 1) le_rfl hcos
  refine Integrable.mono' (hbase.const_mul (Real.exp (-θ * s.im)))
    ((continuousOn_gam_rot s hθ).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [norm_gam_rot s hθπ hr, Real.rpow_one, show -(r * Real.cos θ) = -(Real.cos θ) * r by ring]
  apply le_of_eq; ring

/-! ### Domination + boundary bounds for the rotation hypotheses

The norm bounds that discharge the `hint` (integrability of the angle-derivative
integrand) and `hbdry` (boundary vanishing) hypotheses of `ray_rotation_sector`,
and supply the uniform domination for the differentiation-under-the-integral step. -/

-- no-dlmf: norm-bound helper, no DLMF equation
/-- `‖e^{-(e^{iθ}r)}‖ = e^{-r cosθ}`. -/
theorem norm_exp_neg_rot {θ : ℝ} {r : ℝ} :
    ‖Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ)))‖ = Real.exp (-(r * Real.cos θ)) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring

-- no-dlmf: norm-bound helper, no DLMF equation
/-- Bound on `‖gam'‖` on the rotated ray. -/
theorem norm_gam'_rot_le (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 < r) :
    ‖gam' s (Complex.exp (θ * Complex.I) * (r : ℂ))‖
      ≤ (‖s - 1‖ * r ^ (s.re - 2) + r ^ (s.re - 1))
        * (Real.exp (-θ * s.im) * Real.exp (-(r * Real.cos θ))) := by
  set z := Complex.exp (θ * Complex.I) * (r : ℂ) with hz
  rw [gam']
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_neg]
  have hre2 : (s - 1 - 1 : ℂ).re = s.re - 2 := by simp only [Complex.sub_re, Complex.one_re]; ring
  have him2 : (s - 1 - 1 : ℂ).im = s.im := by simp [Complex.sub_im]
  have hre1 : (s - 1 : ℂ).re = s.re - 1 := by simp [Complex.sub_re]
  have him1 : (s - 1 : ℂ).im = s.im := by simp [Complex.sub_im]
  have e1 : ‖z ^ (s - 1 - 1)‖ = r ^ (s.re - 2) * Real.exp (-θ * s.im) := by
    rw [hz, norm_cpow_rot _ hθ hr, hre2, him2]
  have e2 : ‖z ^ (s - 1)‖ = r ^ (s.re - 1) * Real.exp (-θ * s.im) := by
    rw [hz, norm_cpow_rot _ hθ hr, hre1, him1]
  have e3 : ‖Complex.exp (-z)‖ = Real.exp (-(r * Real.cos θ)) := by rw [hz]; exact norm_exp_neg_rot
  rw [e1, e2, e3]
  nlinarith [norm_nonneg (s - 1), Real.rpow_nonneg hr.le (s.re - 2),
    Real.rpow_nonneg hr.le (s.re - 1), Real.exp_pos (-θ * s.im), Real.exp_pos (-(r * Real.cos θ))]

-- no-dlmf: norm-bound helper, no DLMF equation
/-- The angle-derivative integrand `e^{iθ}gam(u) + r·e^{2iθ}gam'(u)` (`u=e^{iθ}r`),
norm-bounded by `((1+‖s-1‖)r^{Re s-1} + r^{Re s})·e^{-θ Im s}·e^{-r cosθ}`. -/
theorem norm_combo_le (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 < r) :
    ‖Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
          * gam' s (Complex.exp (θ * Complex.I) * (r : ℂ))‖
      ≤ ((1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re))
        * (Real.exp (-θ * s.im) * Real.exp (-(r * Real.cos θ))) := by
  have hexp1 : ‖Complex.exp (θ * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hexp1, one_mul, norm_mul, norm_mul, norm_pow, hexp1, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hg := norm_gam_rot s hθ hr
  have hg' := norm_gam'_rot_le s hθ hr
  set E := Real.exp (-θ * s.im) * Real.exp (-(r * Real.cos θ)) with hE
  have hrpow1 : (0:ℝ) ≤ r ^ (s.re - 1) := Real.rpow_nonneg hr.le _
  rw [show ‖gam s (Complex.exp (θ * Complex.I) * (r : ℂ))‖ = r ^ (s.re - 1) * E by
        rw [hg, hE, mul_assoc]]
  have hr1 : r * r ^ (s.re - 2) = r ^ (s.re - 1) := by
    nth_rewrite 1 [← Real.rpow_one r]; rw [← Real.rpow_add hr]; congr 1; ring
  have hr2 : r * r ^ (s.re - 1) = r ^ (s.re) := by
    nth_rewrite 1 [← Real.rpow_one r]; rw [← Real.rpow_add hr]; congr 1; ring
  calc r ^ (s.re - 1) * E + r * ‖gam' s (Complex.exp (θ * Complex.I) * (r : ℂ))‖
      ≤ r ^ (s.re - 1) * E + r * ((‖s - 1‖ * r ^ (s.re - 2) + r ^ (s.re - 1)) * E) := by gcongr
    _ = ((1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re)) * E := by
        rw [show r * ((‖s - 1‖ * r ^ (s.re - 2) + r ^ (s.re - 1)) * E)
              = (‖s - 1‖ * (r * r ^ (s.re - 2)) + (r * r ^ (s.re - 1))) * E by ring,
          hr1, hr2]; ring

/-- The dominating function `((1+‖s-1‖)r^{Re s-1}+r^{Re s})·e^{-(r·c)}` (times a
constant `k`) is integrable on `(0,∞)` for `Re s > 0`, `c > 0` — the uniform
domination underlying `hint` and the differentiation-under-the-integral step. -/
-- no-dlmf: integrability/domination helper, no DLMF equation
theorem dom_integrable (s : ℂ) (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) (k : ℝ) :
    IntegrableOn (fun r : ℝ =>
      k * (((1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re)) * Real.exp (-(r * c)))) (Ioi 0) := by
  have mk : ∀ a : ℝ, -1 < a →
      IntegrableOn (fun r : ℝ => r ^ a * Real.exp (-(r * c))) (Ioi 0) := by
    intro a ha
    refine IntegrableOn.congr_fun (integrableOn_rpow_mul_exp_neg_mul_rpow ha le_rfl hc)
      (fun r _ => ?_) measurableSet_Ioi
    rw [Real.rpow_one]; congr 2; ring
  refine IntegrableOn.congr_fun
    (((mk (s.re - 1) (by linarith)).const_mul (k * (1 + ‖s - 1‖))).add
      ((mk (s.re) (by linarith)).const_mul k))
    (fun r _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, mul_comm r c]
  ring

-- no-dlmf: boundary-vanishing helper, no DLMF equation
/-- `hbdry`: the boundary term `r·e^{iθ}gam(e^{iθ}r) → 0` at `∞`. -/
theorem hbdry_gam (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    Tendsto (fun r : ℝ =>
      (r : ℂ) * (Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))))
      atTop (𝓝 0) := by
  have hθπ : θ ∈ Ioo (-π) π :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have key : Tendsto (fun r : ℝ =>
      Real.exp (-θ * s.im) * (r ^ s.re * Real.exp (-(Real.cos θ) * r))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s.re (Real.cos θ) hcos).const_mul
      (Real.exp (-θ * s.im))
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hexp1 : ‖Complex.exp (θ * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hexp1, one_mul,
    norm_gam_rot s hθπ hr, show -(r * Real.cos θ) = -(Real.cos θ) * r by ring]
  rw [show r ^ s.re = r * r ^ (s.re - 1) by
        nth_rewrite 2 [← Real.rpow_one r]; rw [← Real.rpow_add hr]; congr 1; ring]
  ring


/-! ### Assembly: the rotated Γ representation

Discharging the remaining `ray_rotation_sector` hypotheses for `gam` (boundary
continuity at 0, integrability, differentiation-under-the-integral, Γ
identification) and assembling the rotated-Γ representation. -/

-- no-dlmf: proof-internal factorization helper, no DLMF equation
/-- The boundary function `G(r) = r·e^{iθ}gam(e^{iθ}r)` equals
`H(r) = (r:ℂ)^s·e^{sθI}·e^{-e^{iθ}r}` on `[0,∞)` (for `s ≠ 0`). -/
theorem G_eq_H (s : ℂ) (hs0 : s ≠ 0) {θ : ℝ} (hθ : θ ∈ Ioo (-π) π) {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) * (Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ)))
      = (r : ℂ) ^ s * Complex.exp (s * (θ : ℂ) * Complex.I)
        * Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ))) := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- r = 0
    rw [← hr0]
    simp [gam, Complex.zero_cpow hs0]
  · -- r > 0
    rw [gam, cpow_rot_extract hθ hr0]
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hcpow : (r : ℂ) * (r : ℂ) ^ (s - 1) = (r : ℂ) ^ s := by
      nth_rewrite 1 [← Complex.cpow_one (r : ℂ)]
      rw [← Complex.cpow_add _ _ hrne]; congr 1; ring
    have hexp : Complex.exp (θ * Complex.I) * Complex.exp ((s - 1) * (θ : ℂ) * Complex.I)
        = Complex.exp (s * (θ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc (r : ℂ) * (Complex.exp (θ * Complex.I)
            * ((r : ℂ) ^ (s - 1) * Complex.exp ((s - 1) * (θ : ℂ) * Complex.I)
              * Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ)))))
        = ((r : ℂ) * (r : ℂ) ^ (s - 1))
            * (Complex.exp (θ * Complex.I) * Complex.exp ((s - 1) * (θ : ℂ) * Complex.I))
            * Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ))) := by ring
      _ = (r : ℂ) ^ s * Complex.exp (s * (θ : ℂ) * Complex.I)
            * Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ))) := by rw [hcpow, hexp]

/-- `hGcont`: `r ↦ r·e^{iθ}gam(e^{iθ}r)` is continuous on `[0,∞)`, via the
factorization `G = (r:ℂ)^s·e^{sθI}·e^{-e^{iθ}r}` (`(r:ℂ)^s` continuous for `Re s>0`). -/
-- no-dlmf: continuity helper, no DLMF equation
theorem hGcont_gam (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    ContinuousOn (fun r : ℝ =>
      (r : ℂ) * (Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))))
      (Ici 0) := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hθπ : θ ∈ Ioo (-π) π :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hH : Continuous (fun r : ℝ => (r : ℂ) ^ s * Complex.exp (s * (θ : ℂ) * Complex.I)
      * Complex.exp (-(Complex.exp (θ * Complex.I) * (r : ℂ)))) := by
    have h1 : Continuous (fun r : ℝ => (r : ℂ) ^ s) := Complex.continuous_ofReal_cpow_const hs
    fun_prop (disch := assumption)
  refine (hH.continuousOn).congr (fun r hr => ?_)
  exact G_eq_H s hs0 hθπ hr

-- no-dlmf: continuity helper, no DLMF equation
/-- `gam'` is continuous at slit-plane points. -/
theorem gam'_continuousAt (s : ℂ) {z₀ : ℂ} (h : z₀ ∈ Complex.slitPlane) :
    ContinuousAt (gam' s) z₀ := by
  unfold gam'
  have hcpow1 : ContinuousAt (fun z : ℂ => z ^ (s - 1 - 1)) z₀ := continuousAt_cpow_const h
  have hcpow2 : ContinuousAt (fun z : ℂ => z ^ (s - 1)) z₀ := continuousAt_cpow_const h
  exact ((continuousAt_const.mul hcpow1).mul (by fun_prop)).add (hcpow2.mul (by fun_prop))

-- no-dlmf: continuity helper, no DLMF equation
/-- Continuity of `gam'` on the rotated ray. -/
theorem continuousOn_gam'_rot (s : ℂ) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    ContinuousOn (fun r : ℝ => gam' s (Complex.exp (θ * Complex.I) * (r : ℂ))) (Ioi 0) := by
  intro r hr
  have hslit : Complex.exp (θ * Complex.I) * (r : ℂ) ∈ Complex.slitPlane :=
    rot_mem_slitPlane hθ hr
  have hray : ContinuousAt (fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ)) r := by fun_prop
  have h1 : ContinuousAt ((gam' s) ∘ (fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ))) r :=
    ContinuousAt.comp (f := fun r : ℝ => Complex.exp (θ * Complex.I) * (r : ℂ))
      (gam'_continuousAt s hslit) hray
  exact h1.continuousWithinAt

/-- `hint`: the angle-derivative integrand `e^{iθ}gam(u) + r·e^{2iθ}gam'(u)` is
integrable on `(0,∞)` (`Re s>0`, `|θ|<π/2`). -/
-- no-dlmf: integrability helper, no DLMF equation
theorem hint_gam (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : θ ∈ Ioo (-(π/2)) (π/2)) :
    IntegrableOn (fun r : ℝ =>
      Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
          * gam' s (Complex.exp (θ * Complex.I) * (r : ℂ))) (Ioi 0) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have hθπ : θ ∈ Ioo (-π) π :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))
        + (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
          * gam' s (Complex.exp (θ * Complex.I) * (r : ℂ)))
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    refine (continuousOn_const.mul (continuousOn_gam_rot s hθ)).add ?_
    exact ((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).mul
      (continuousOn_gam'_rot s hθ))
  refine Integrable.mono' (dom_integrable s hs hcos (Real.exp (-θ * s.im))) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  refine (norm_combo_le s hθπ hr).trans (le_of_eq ?_)
  ring

-- no-dlmf: proof-internal identification with Mathlib's Γ integral, no DLMF equation
/-- The base ray integral is the Γ integral: `∫_{(0,∞)} gam s(r) dr = Γ(s)`. -/
theorem integral_gam_eq_Gamma (s : ℂ) (hs : 0 < s.re) :
    ∫ r in Ioi (0 : ℝ), gam s (r : ℂ) = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [gam, show Complex.exp (-(r : ℂ)) = ((Real.exp (-r) : ℝ) : ℂ) by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
  ring

-- no-dlmf: technical bound, no DLMF equation
/-- Cosine lower bound on the wedge `Ioo a b` with `b < π/2`, `|a| ≤ b`. -/
theorem cos_ge_on (a b : ℝ) (hb : b < π / 2) (hab : -b ≤ a) {θ' : ℝ} (h : θ' ∈ Ioo a b) :
    Real.cos b ≤ Real.cos θ' := by
  rw [← Real.cos_abs θ']
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
  rw [abs_le]; exact ⟨by linarith [h.1], le_of_lt h.2⟩

/-- `hIderiv`: differentiate the rotated integral under the integral sign, sector
form (singular `gam`, `ContinuousOn` measurability + the `dom_integrable`/
`norm_combo_le` uniform domination). -/
-- no-dlmf: differentiation-under-the-integral helper, no DLMF equation
theorem hIderiv_gam (s : ℂ) (hs : 0 < s.re) {θ₀ : ℝ} (h0 : 0 ≤ θ₀) (hlt : θ₀ < π / 2) :
    ∀ θ ∈ Icc 0 θ₀, HasDerivAt
      (fun θ' : ℝ => ∫ r in Ioi (0 : ℝ),
        Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ)))
      (∫ r in Ioi (0 : ℝ),
        (Complex.I * Complex.exp (θ * Complex.I) * gam s (Complex.exp (θ * Complex.I) * (r : ℂ))
          + Complex.I * (r : ℂ) * Complex.exp (θ * Complex.I) ^ 2
            * gam' s (Complex.exp (θ * Complex.I) * (r : ℂ)))) θ := by
  intro θ hθ
  obtain ⟨hθl, hθr⟩ := hθ
  set ε := (π / 2 - θ₀) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set a := -ε with ha
  set b := θ₀ + ε with hb
  have hb2 : b < π / 2 := by rw [hb, hε]; linarith
  have hab : -b ≤ a := by rw [ha, hb]; linarith
  set S := Ioo a b with hS
  have hεlt : ε < π / 2 := by rw [hε]; linarith [Real.pi_pos, h0]
  have hθS : θ ∈ S := ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩
  have hSsub : ∀ θ' ∈ S, θ' ∈ Ioo (-(π/2)) (π/2) := fun θ' hθ' =>
    ⟨by have := hθ'.1; rw [ha] at this; linarith, by linarith [hθ'.2, hb2]⟩
  have hbmem : b ∈ Ioo (-(π/2)) (π/2) := ⟨by linarith [hb2, hεpos, h0], hb2⟩
  have hcb : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo hbmem
  set K := b * |s.im| with hK
  set F : ℝ → ℝ → ℂ := fun θ' r =>
    Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ)) with hF
  set F' : ℝ → ℝ → ℂ := fun θ' r =>
    Complex.I * Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ))
      + Complex.I * (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
        * gam' s (Complex.exp (θ' * Complex.I) * (r : ℂ)) with hF'
  have hFmeas : ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable (F θ') (volume.restrict (Ioi 0)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθS] with θ' hθ'
    exact (continuousOn_const.mul (continuousOn_gam_rot s (hSsub θ' hθ'))).aestronglyMeasurable
      measurableSet_Ioi
  have hFint : Integrable (F θ) (volume.restrict (Ioi 0)) :=
    (integrable_gam_rot s hs (hSsub θ hθS)).const_mul _
  have hF'meas : AEStronglyMeasurable (F' θ) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_const.mul (continuousOn_gam_rot s (hSsub θ hθS))).add ?_
    exact ((continuousOn_const.mul Complex.continuous_ofReal.continuousOn).mul continuousOn_const).mul
      (continuousOn_gam'_rot s (hSsub θ hθS))
  have hbound_int : Integrable
      (fun r : ℝ => Real.exp K *
        (((1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re)) * Real.exp (-(r * Real.cos b))))
      (volume.restrict (Ioi 0)) := dom_integrable s hs hcb (Real.exp K)
  have hdom : ∀ᵐ r ∂(volume.restrict (Ioi 0)), ∀ θ' ∈ S,
      ‖F' θ' r‖ ≤ Real.exp K *
        (((1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re)) * Real.exp (-(r * Real.cos b))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr θ' hθ'
    have hrpos : 0 < r := hr
    have hθ'π : θ' ∈ Ioo (-π) π :=
      ⟨by linarith [(hSsub θ' hθ').1, Real.pi_pos], by linarith [(hSsub θ' hθ').2, Real.pi_pos]⟩
    have hnormeq : ‖F' θ' r‖
        = ‖Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ))
            + (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
              * gam' s (Complex.exp (θ' * Complex.I) * (r : ℂ))‖ := by
      simp only [hF']
      rw [show Complex.I * Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ))
            + Complex.I * (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
              * gam' s (Complex.exp (θ' * Complex.I) * (r : ℂ))
          = Complex.I * (Complex.exp (θ' * Complex.I) * gam s (Complex.exp (θ' * Complex.I) * (r : ℂ))
            + (r : ℂ) * Complex.exp (θ' * Complex.I) ^ 2
              * gam' s (Complex.exp (θ' * Complex.I) * (r : ℂ))) by ring,
        norm_mul, Complex.norm_I, one_mul]
    rw [hnormeq]
    refine (norm_combo_le s hθ'π hrpos).trans ?_
    set A := (1 + ‖s - 1‖) * r ^ (s.re - 1) + r ^ (s.re) with hA
    have hA0 : 0 ≤ A := by
      have := Real.rpow_nonneg hr.le (s.re - 1); have := Real.rpow_nonneg hr.le s.re
      have := norm_nonneg (s - 1); rw [hA]; nlinarith
    have h1 : Real.exp (-θ' * s.im) ≤ Real.exp K := by
      apply Real.exp_le_exp.mpr
      have hb' : |θ'| ≤ b := by
        rw [abs_le]; exact ⟨by linarith [hθ'.1, hab], le_of_lt hθ'.2⟩
      calc -θ' * s.im ≤ |(-θ' * s.im)| := le_abs_self _
        _ = |θ'| * |s.im| := by rw [abs_mul, abs_neg]
        _ ≤ b * |s.im| := by apply mul_le_mul_of_nonneg_right hb' (abs_nonneg _)
    have h2 : Real.exp (-(r * Real.cos θ')) ≤ Real.exp (-(r * Real.cos b)) := by
      apply Real.exp_le_exp.mpr
      have := cos_ge_on a b hb2 hab hθ'
      nlinarith [hrpos.le]
    calc A * (Real.exp (-θ' * s.im) * Real.exp (-(r * Real.cos θ')))
        ≤ A * (Real.exp K * Real.exp (-(r * Real.cos b))) := by
          apply mul_le_mul_of_nonneg_left _ hA0; exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = Real.exp K * (A * Real.exp (-(r * Real.cos b))) := by ring
  have hdiff : ∀ᵐ r ∂(volume.restrict (Ioi 0)), ∀ θ' ∈ S,
      HasDerivAt (fun θ'' => F θ'' r) (F' θ' r) θ' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr θ' hθ'
    exact rotation_angle_deriv (gam s) (gam' s) θ' r (gam_hasDerivAt s (hSsub θ' hθ') hr)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs := isOpen_Ioo.mem_nhds hθS)
    (hF_meas := hFmeas) (hF_int := hFint) (hF'_meas := hF'meas) (h_bound := hdom)
    (bound_integrable := hbound_int) (h_diff := hdiff)).2

/-- **Rotated Γ representation.** For `Re s > 0` and `0 ≤ θ₀ < π/2`, the Γ integral
rotates onto the ray `e^{iθ₀}·(0,∞)`:
`Γ(s) = e^{sθ₀i} ∫₀^∞ r^{s-1} e^{-e^{iθ₀}r} dr`.

The contour-rotation engine (`ray_rotation_sector`, singular-at-0 case) applied to
the Γ integrand `t^{s-1}e^{-t}`, with all hypotheses discharged from the
`ContourRotationGamma` foundations. Rotating to `θ₀ → π/2` (the imaginary axis)
would give the Mellin transform of `e^{-it}` behind `Ci → 0` (#7) — that boundary
limit is the remaining conditionally-convergent step. -/
-- no-dlmf: contour-rotation representation (reusable method), no DLMF equation
theorem gamma_ray_rotation (s : ℂ) (hs : 0 < s.re) {θ₀ : ℝ} (h0 : 0 ≤ θ₀) (hlt : θ₀ < π / 2) :
    Complex.Gamma s = Complex.exp (s * (θ₀ : ℂ) * Complex.I) *
      ∫ r in Ioi (0 : ℝ),
        (r : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ₀ * Complex.I) * (r : ℂ))) := by
  have icc_sub : ∀ {θ : ℝ}, θ ∈ Icc 0 θ₀ → θ ∈ Ioo (-(π/2)) (π/2) := fun {θ} hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, hlt]⟩
  have hθ₀π : θ₀ ∈ Ioo (-π) π :=
    ⟨by linarith [h0, Real.pi_pos], by linarith [hlt, Real.pi_pos]⟩
  have hrot := ray_rotation_sector (gam s) (gam' s) θ₀ h0
    (fun θ hθ r hr => gam_hasDerivAt s (icc_sub hθ) hr)
    (fun θ hθ => hGcont_gam s hs (icc_sub hθ))
    (fun θ hθ => (hIderiv_gam s hs h0 hlt θ hθ).continuousAt.continuousWithinAt)
    (hIderiv_gam s hs h0 hlt)
    (fun θ hθ => hint_gam s hs (icc_sub hθ))
    (fun θ hθ => hbdry_gam s (icc_sub hθ))
  rw [integral_gam_eq_Gamma s hs] at hrot
  rw [hrot]
  have hext : ∫ r in Ioi (0 : ℝ), gam s (Complex.exp (θ₀ * Complex.I) * (r : ℂ))
      = Complex.exp ((s - 1) * (θ₀ : ℂ) * Complex.I) *
        ∫ r in Ioi (0 : ℝ),
          (r : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ₀ * Complex.I) * (r : ℂ))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [gam, cpow_rot_extract hθ₀π hr]; ring
  rw [hext, ← mul_assoc]
  congr 1
  rw [← Complex.exp_add]; congr 1; ring


/-! ### Rotation meets the imaginary axis (toward #7) -/

/-- **Rotation meets the imaginary axis (Mellin transform of `e^{-it}`).** As the
rotation ray approaches `θ₀ = π/2⁻`, the (absolutely convergent) rotated Γ integral
converges to `e^{-iπs/2}Γ(s)`:
`lim_{θ₀↑π/2} ∫₀^∞ r^{s-1}e^{-e^{iθ₀}r}dr = e^{-iπs/2}Γ(s)`.

The integral at `θ₀ = π/2` itself is *not* Bochner-defined (`|e^{-ir}| = 1`), so the
imaginary-axis value is recovered as the limit of genuine rotated integrals — the
contour-rotation realization of `∫₀^∞ t^{s-1}e^{-it}dt = e^{-iπs/2}Γ(s)` (the
blocker for `Ci → 0`, #7). The Γ analogue of `rotated_gaussian_tendsto_fresnel`. -/
-- no-dlmf: contour-rotation boundary-limit method, no DLMF equation
theorem gamma_rotated_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun θ₀ : ℝ => ∫ r in Ioi (0 : ℝ),
        (r : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ₀ * Complex.I) * (r : ℂ))))
      (𝓝[<] (π / 2))
      (𝓝 (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s)) := by
  have hg : Continuous
      (fun θ₀ : ℝ => Complex.exp (-(s * (θ₀ : ℂ) * Complex.I)) * Complex.Gamma s) := by fun_prop
  have hlim : Tendsto
      (fun θ₀ : ℝ => Complex.exp (-(s * (θ₀ : ℂ) * Complex.I)) * Complex.Gamma s)
      (𝓝[<] (π / 2))
      (𝓝 (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s)) :=
    (hg.tendsto _).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  have hmem : ∀ᶠ θ₀ in 𝓝[<] (π / 2), θ₀ ∈ Ioo (0 : ℝ) (π / 2) := by
    have h2 : Ioi (0 : ℝ) ∈ 𝓝[<] (π / 2) :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, h2] with θ₀ ha hb using ⟨hb, ha⟩
  filter_upwards [hmem] with θ₀ hθ₀
  -- e^{-sθ₀i}·Γ(s) = ∫, from Γ(s) = e^{sθ₀i}·∫
  rw [gamma_ray_rotation s hs (le_of_lt hθ₀.1) hθ₀.2, ← mul_assoc, ← Complex.exp_add,
    show -(s * (θ₀ : ℂ) * Complex.I) + s * (θ₀ : ℂ) * Complex.I = 0 by ring,
    Complex.exp_zero, one_mul]

/-! ### Scaled Γ integral (complex rate) — the Laplace–Mellin formula -/

/-- **Scaled Γ integral (polar rate).** For `Re s > 0`, `0 ≤ θ < π/2`, `ρ > 0`:
`∫₀^∞ t^{s-1} e^{-(e^{iθ}ρ)t} dt = (e^{iθ}ρ)^{-s} Γ(s)`. The rotated-Γ representation
plus the real scaling `u = ρt`. -/
-- no-dlmf: Laplace–Mellin method lemma (polar rate), no DLMF equation
theorem scaled_gamma_polar (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (h0 : 0 ≤ θ) (hlt : θ < π / 2)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ * Complex.I) * (ρ : ℂ) * (t : ℂ)))
      = (Complex.exp (θ * Complex.I) * (ρ : ℂ)) ^ (-s) * Complex.Gamma s := by
  have hθπ : θ ∈ Ioo (-π) π :=
    ⟨by linarith [h0, Real.pi_pos], by linarith [hlt, Real.pi_pos]⟩
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set G : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ * Complex.I) * (u : ℂ))) with hG
  -- LHS integrand = ρ^{1-s} · G(ρ·t)
  have hpt : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
      (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ * Complex.I) * (ρ : ℂ) * (t : ℂ)))
        = (ρ : ℂ) ^ (1 - s) * G (ρ * t) := by
    intro t ht
    have htpos : 0 < t := ht
    rw [hG]
    simp only [Complex.ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hρ.le htpos.le]
    rw [show (ρ : ℂ) ^ (1 - s) * ((ρ : ℂ) ^ (s - 1) * (t : ℂ) ^ (s - 1)
          * Complex.exp (-(Complex.exp (θ * Complex.I) * ((ρ : ℂ) * (t : ℂ)))))
        = ((ρ : ℂ) ^ (1 - s) * (ρ : ℂ) ^ (s - 1)) * ((t : ℂ) ^ (s - 1)
          * Complex.exp (-(Complex.exp (θ * Complex.I) * ((ρ : ℂ) * (t : ℂ))))) by ring]
    rw [← Complex.cpow_add _ _ hρne, show (1 - s) + (s - 1) = 0 by ring, Complex.cpow_zero, one_mul]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_const_mul, integral_comp_mul_left_Ioi G 0 hρ, mul_zero]
  rw [Complex.real_smul, ← mul_assoc]
  -- ∫ G = e^{-sθi} Γ(s)
  have hint : ∫ u in Ioi (0 : ℝ), G u = Complex.exp (-(s * (θ : ℂ) * Complex.I)) * Complex.Gamma s := by
    have hrep := gamma_ray_rotation s hs h0 hlt
    rw [hG]
    rw [show (∫ u in Ioi (0:ℝ),
        (u : ℂ) ^ (s - 1) * Complex.exp (-(Complex.exp (θ * Complex.I) * (u : ℂ))))
        = Complex.exp (-(s * (θ : ℂ) * Complex.I)) * Complex.Gamma s from ?_]
    rw [hrep, ← mul_assoc, ← Complex.exp_add,
      show -(s * (θ : ℂ) * Complex.I) + s * (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero,
      one_mul]
  rw [hint, cpow_rot_extract hθπ hρ (-s),
    show ((-s) * (θ : ℂ) * Complex.I) = -(s * (θ : ℂ) * Complex.I) by ring]
  have hρpow : (ρ : ℂ) ^ (1 - s) * ((ρ⁻¹ : ℝ) : ℂ) = (ρ : ℂ) ^ (-s) := by
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hρne]
    congr 1; ring
  rw [show (ρ : ℂ) ^ (1 - s) * ((ρ⁻¹ : ℝ) : ℂ)
        * (Complex.exp (-(s * (θ : ℂ) * Complex.I)) * Complex.Gamma s)
      = ((ρ : ℂ) ^ (1 - s) * ((ρ⁻¹ : ℝ) : ℂ))
        * (Complex.exp (-(s * (θ : ℂ) * Complex.I)) * Complex.Gamma s) by ring, hρpow]
  ring

/-- **Scaled Γ integral (complex rate).** For `Re s > 0` and a rate `c` in the
first quadrant (`Re c > 0`, `Im c ≥ 0`):
`∫₀^∞ t^{s-1} e^{-ct} dt = c^{-s} Γ(s)`. The complex-rate Laplace–Mellin formula
(Mathlib has only the real-rate version). -/
-- no-dlmf: Laplace–Mellin method lemma (complex rate), no DLMF equation
theorem scaled_gamma (s : ℂ) (hs : 0 < s.re) {c : ℂ} (hre : 0 < c.re) (him : 0 ≤ c.im) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-(c * (t : ℂ)))
      = c ^ (-s) * Complex.Gamma s := by
  have hcne : c ≠ 0 := by rintro rfl; simp at hre
  set θ := Complex.arg c with hθdef
  set ρ := ‖c‖ with hρdef
  have hθ0 : 0 ≤ θ := Complex.arg_nonneg_iff.mpr him
  have hθlt : θ < π / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hρpos : 0 < ρ := norm_pos_iff.mpr hcne
  have hpolar : c = Complex.exp ((θ : ℝ) * Complex.I) * (ρ : ℂ) := by
    rw [mul_comm]; exact (Complex.norm_mul_exp_arg_mul_I c).symm
  rw [hpolar]
  exact scaled_gamma_polar s hs hθ0 hθlt hρpos

/-! ### Abel-regularized Mellin transform of e^{-it} (radial regularization) -/

/-- **Abel-regularized Mellin transform of `e^{-it}`.** For `Re s > 0`, the
exponentially-damped family converges as `ε ↓ 0`:
`lim_{ε↓0} ∫₀^∞ t^{s-1}e^{-(ε+i)t}dt = e^{-iπs/2}Γ(s)`.

Each `ε>0` integral is `(ε+i)^{-s}Γ(s)` (`scaled_gamma`); as `ε↓0` the rate
`ε+i → i` and `c↦c^{-s}` is continuous at `i` (off the branch cut), giving
`i^{-s}Γ(s) = e^{-iπs/2}Γ(s)`. The radial companion to the angular limit
`gamma_rotated_tendsto`, and the bridge to the bare improper integral via
`AbelianExp` (toward #7). -/
-- no-dlmf: Abel-regularization method lemma, no DLMF equation
theorem gamma_abel_regularized (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (s - 1) * Complex.exp (-(((ε : ℂ) + Complex.I) * (t : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s)) := by
  have hival : (Complex.I) ^ (-s) = Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_I]; congr 1; push_cast; ring
  have hcont : ContinuousAt (fun c : ℂ => c ^ (-s)) Complex.I := by
    apply continuousAt_cpow_const
    rw [Complex.mem_slitPlane_iff]; right; simp
  have hev : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 Complex.I) := by
    have hc : Continuous (fun ε : ℝ => ((ε : ℂ) + Complex.I)) := by fun_prop
    have h : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (((0 : ℝ) : ℂ) + Complex.I)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hlim : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I) ^ (-s) * Complex.Gamma s)
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.I ^ (-s) * Complex.Gamma s)) :=
    (hcont.tendsto.comp hev).mul tendsto_const_nhds
  rw [hival] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hre : 0 < ((ε : ℂ) + Complex.I).re := by simpa using (hε : (0 : ℝ) < ε)
  have him : 0 ≤ ((ε : ℂ) + Complex.I).im := by simp
  exact (scaled_gamma s hs hre him).symm

/-! ### Toward the bare improper integral (#7): the absolutely-convergent IBP tail -/

/-- The IBP tail `t^{s-2}e^{-it}` is absolutely convergent on `(1,∞)` for `Re s < 1`
(`|·| = t^{Re s-2}`, `Re s-2 < -1`). The absolutely-convergent piece underlying the
conditional convergence of `∫₀^∞ t^{s-1}e^{-it}`. -/
-- no-dlmf: integrability helper, no DLMF equation
theorem integrable_tail (s : ℂ) (hs : s.re < 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 2) * Complex.exp (-(Complex.I * (t : ℂ)))) (Ioi 1) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (s.re - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 2 < -1) one_pos
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 2) * Complex.exp (-(Complex.I * (t : ℂ))))
      (volume.restrict (Ioi 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    have htpos : (0 : ℝ) < t := lt_trans one_pos ht
    have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (s - 2)) t :=
      Complex.continuousAt_ofReal_cpow_const t (s - 2) (Or.inr htpos.ne')
    have h2 : ContinuousAt (fun t : ℝ => Complex.exp (-(Complex.I * (t : ℂ)))) t := by fun_prop
    exact (h1.mul h2).continuousWithinAt
  refine Integrable.mono' hbase hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : (0 : ℝ) < t := lt_trans one_pos ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.norm_exp]
  have hre : (-(Complex.I * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one, Complex.sub_re]
  norm_num

/-! ### Improper convergence of the bare oscillatory Mellin integral (toward #7) -/

-- no-dlmf: proof-internal definition (oscillatory Mellin integrand)
noncomputable def fmel (s : ℂ) : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.I * (t : ℂ)))

-- no-dlmf: derivative helper, no DLMF equation
/-- Derivative of `t ↦ (↑t)^(s-1)` at `t > 0`. -/
theorem hasDerivAt_cpow_ofReal (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ (s - 1)) ((s - 1) * (t : ℂ) ^ (s - 1 - 1)) t := by
  have hofR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := t)
  have hslit : (t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using ht
  have hcpow : HasDerivAt (fun z : ℂ => z ^ (s - 1)) ((s - 1) * (t : ℂ) ^ (s - 1 - 1)) (t : ℂ) :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt
  have := hcpow.comp t hofR
  simpa using this

-- no-dlmf: derivative helper, no DLMF equation
/-- Derivative of the antiderivative-partner `v(t) = i·e^{-it}`: `v' = e^{-it}`. -/
theorem hasDerivAt_v (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * (t : ℂ))))
      (Complex.exp (-(Complex.I * (t : ℂ)))) t := by
  have hofR : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := t)
  have h1 : HasDerivAt (fun t : ℝ => -(Complex.I * (t : ℂ))) (-(Complex.I)) t := by
    have := (hofR.const_mul Complex.I).neg
    simpa using this
  have h2 := h1.cexp
  have h3 := h2.const_mul Complex.I
  convert h3 using 1
  rw [show Complex.I * (Complex.exp (-(Complex.I * (t : ℂ))) * -Complex.I)
        = -(Complex.I * Complex.I) * Complex.exp (-(Complex.I * (t : ℂ))) by ring,
    Complex.I_mul_I]
  ring

-- no-dlmf: proof-internal definition (IBP tail integrand)
/-- The IBP tail integrand `(s-1)t^{s-2}·(i e^{-it})`. -/
noncomputable def tailInt (s : ℂ) : ℝ → ℂ :=
  fun t => ((s - 1) * (t : ℂ) ^ (s - 1 - 1)) * (Complex.I * Complex.exp (-(Complex.I * (t : ℂ))))

/-- **Improper convergence of the tail** `∫_1^R t^{s-1}e^{-it}` (`Re s < 1`): it
converges as `R → ∞` (the conditionally-convergent oscillatory integral). -/
-- no-dlmf: improper-convergence helper, no DLMF equation
theorem tail_tendsto (s : ℂ) (hs : s.re < 1) :
    Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..R, fmel s t) atTop
      (𝓝 (-(Complex.I * Complex.exp (-(Complex.I * (1 : ℂ))))
        - ∫ t in Ioi (1 : ℝ), tailInt s t)) := by
  -- IBP identity for each R ≥ 1
  have hIBP : ∀ R : ℝ, 1 ≤ R →
      ∫ t in (1 : ℝ)..R, fmel s t
        = (R : ℂ) ^ (s - 1) * (Complex.I * Complex.exp (-(Complex.I * (R : ℂ))))
          - (1 : ℂ) ^ (s - 1) * (Complex.I * Complex.exp (-(Complex.I * (1 : ℂ))))
          - ∫ t in (1 : ℝ)..R, ((s - 1) * (t : ℂ) ^ (s - 1 - 1))
              * (Complex.I * Complex.exp (-(Complex.I * (t : ℂ)))) := by
    intro R hR
    have hu : ∀ t ∈ uIcc (1 : ℝ) R, HasDerivAt (fun t : ℝ => (t : ℂ) ^ (s - 1))
        ((s - 1) * (t : ℂ) ^ (s - 1 - 1)) t := by
      intro t ht
      have htpos : 0 < t := by
        rw [uIcc_of_le hR] at ht; linarith [ht.1]
      exact hasDerivAt_cpow_ofReal s htpos
    have hv : ∀ t ∈ uIcc (1 : ℝ) R, HasDerivAt
        (fun t : ℝ => Complex.I * Complex.exp (-(Complex.I * (t : ℂ))))
        (Complex.exp (-(Complex.I * (t : ℂ)))) t := fun t _ => hasDerivAt_v t
    have hu' : IntervalIntegrable (fun t : ℝ => (s - 1) * (t : ℂ) ^ (s - 1 - 1)) volume 1 R := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hR]
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      exact (continuousAt_const.mul
        ((Complex.continuousAt_ofReal_cpow_const t (s - 1 - 1) (Or.inr htpos.ne')))).continuousWithinAt
    have hv' : IntervalIntegrable (fun t : ℝ => Complex.exp (-(Complex.I * (t : ℂ)))) volume 1 R := by
      apply Continuous.intervalIntegrable; fun_prop
    have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    simpa [fmel] using key
  -- the tail integrand is integrable on (1,∞)  (const multiple of integrable_tail)
  have htail_int : IntegrableOn (tailInt s) (Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrable_tail s hs).const_mul ((s - 1) * Complex.I))
      (fun t _ => ?_) measurableSet_Ioi
    simp only [tailInt]
    rw [show s - 1 - 1 = s - 2 by ring]; ring
  have htail : Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..R, tailInt s t) atTop
      (𝓝 (∫ t in Ioi (1 : ℝ), tailInt s t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 htail_int tendsto_id
  -- boundary term R^{s-1}·(i e^{-iR}) → 0
  have hbdry : Tendsto (fun R : ℝ =>
      (R : ℂ) ^ (s - 1) * (Complex.I * Complex.exp (-(Complex.I * (R : ℂ))))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdecay : Tendsto (fun R : ℝ => R ^ (-(1 - s.re))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - s.re)
    refine (hdecay.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hR, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_exp]
    have : (-(Complex.I * (R : ℂ))).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one, Complex.sub_re, Complex.one_re]
    congr 1; ring
  -- assemble
  have hcomb : Tendsto (fun R : ℝ =>
      ((R : ℂ) ^ (s - 1) * (Complex.I * Complex.exp (-(Complex.I * (R : ℂ))))
          - Complex.I * Complex.exp (-(Complex.I * (1 : ℂ))))
        - ∫ t in (1 : ℝ)..R, tailInt s t) atTop
      (𝓝 (-(Complex.I * Complex.exp (-(Complex.I * (1 : ℂ)))) - ∫ t in Ioi (1 : ℝ), tailInt s t)) := by
    have h := (hbdry.sub_const (Complex.I * Complex.exp (-(Complex.I * (1 : ℂ))))).sub htail
    simpa using h
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  rw [hIBP R hR, Complex.one_cpow, one_mul]
  simp only [tailInt]


-- no-dlmf: norm-bound helper, no DLMF equation
/-- `‖fmel s t‖ = t^{Re s-1}` for `t > 0`. -/
theorem norm_fmel {s : ℂ} {t : ℝ} (ht : 0 < t) : ‖fmel s t‖ = t ^ (s.re - 1) := by
  rw [fmel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  have : (-(Complex.I * (t : ℂ))).re = 0 := by simp
  rw [this, Real.exp_zero, mul_one, Complex.sub_re, Complex.one_re]

-- no-dlmf: continuity helper, no DLMF equation
/-- `fmel` is continuous on the open ray `t > 0`. -/
theorem continuousOn_fmel (s : ℂ) : ContinuousOn (fmel s) (Ioi 0) := by
  intro t ht
  have htpos : 0 < t := ht
  have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (s - 1)) t :=
    Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr htpos.ne')
  have h2 : ContinuousAt (fun t : ℝ => Complex.exp (-(Complex.I * (t : ℂ)))) t := by fun_prop
  exact (h1.mul h2).continuousWithinAt

-- no-dlmf: integrability helper, no DLMF equation
/-- `fmel` is integrable on `(0,1]` (the integrable singularity, `Re s > 0`). -/
theorem fmel_integrableOn_Ioc01 (s : ℂ) (hs0 : 0 < s.re) : IntegrableOn (fmel s) (Ioc 0 1) := by
  have hdom : IntegrableOn
      (fun t : ℝ => Real.exp 1 * ‖((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)‖) (Ioc 0 1) :=
    (((GammaIntegral_convergent hs0).mono_set Ioc_subset_Ioi_self).norm).const_mul (Real.exp 1)
  refine Integrable.mono' hdom
    ((continuousOn_fmel s).mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htpos : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [norm_fmel htpos, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos htpos,
    Complex.sub_re, Complex.one_re]
  -- t^{Re s-1} ≤ e · (e^{-t} · t^{Re s-1})
  have hrpow : (0:ℝ) ≤ t ^ (s.re - 1) := Real.rpow_nonneg htpos.le _
  have hkey : (1:ℝ) ≤ Real.exp 1 * Real.exp (-t) := by
    rw [← Real.exp_add]
    calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp (1 + -t) := Real.exp_le_exp.mpr (by linarith)
  calc t ^ (s.re - 1) = 1 * t ^ (s.re - 1) := (one_mul _).symm
    _ ≤ (Real.exp 1 * Real.exp (-t)) * t ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right hkey hrpow
    _ = Real.exp 1 * (Real.exp (-t) * t ^ (s.re - 1)) := by ring

-- no-dlmf: improper-convergence helper, no DLMF equation
/-- **Full improper convergence:** `∫_0^R t^{s-1}e^{-it} → L` (`0<Re s<1`). -/
theorem improper_converges (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, fmel s t) atTop
      (𝓝 ((∫ t in (0 : ℝ)..1, fmel s t)
        + (-(Complex.I * Complex.exp (-(Complex.I * (1 : ℂ)))) - ∫ t in Ioi (1 : ℝ), tailInt s t))) := by
  have hii01 : IntervalIntegrable (fmel s) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact fmel_integrableOn_Ioc01 s hs0
  refine (tendsto_const_nhds.add (tail_tendsto s hs1)).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hii1R : IntervalIntegrable (fmel s) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hR]
    exact (continuousOn_fmel s).mono (fun t ht => by simp only [mem_Ioi]; linarith [ht.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals hii01 hii1R]

/-! ### Closing #7: the bare improper Mellin transform of e^{-it} -/

-- no-dlmf: proof-internal definition (bounded continuous extension)
/-- The bounded continuous extension `f̂(t) = fmel(max t 1)` (constant `fmel 1` on
`[0,1]`, equal to `fmel` on `[1,∞)`). -/
noncomputable def fhat (s : ℂ) : ℝ → ℂ := fun t => fmel s (max t 1)

-- no-dlmf: continuity helper, no DLMF equation
theorem fhat_continuous (s : ℂ) : Continuous (fhat s) := by
  have hmax : Continuous (fun t : ℝ => max t 1) := by fun_prop
  refine (continuousOn_fmel s).comp_continuous hmax (fun t => ?_)
  simp only [mem_Ioi]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

-- no-dlmf: technical bound, no DLMF equation
theorem fhat_bound (s : ℂ) (hs1 : s.re < 1) : ∀ t, ‖fhat s t‖ ≤ 1 := by
  intro t
  have hmax1 : (1:ℝ) ≤ max t 1 := le_max_right _ _
  rw [fhat, norm_fmel (lt_of_lt_of_le zero_lt_one hmax1)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hmax1 (by linarith)

-- no-dlmf: technical bound, no DLMF equation
/-- `‖↑(e^{-εt}) z‖ ≤ ‖z‖` for `ε,t>0`. -/
theorem norm_exp_smul_le {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (z : ℂ) :
    ‖((Real.exp (-ε * t) : ℝ) : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-ε * t) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (-ε * t) * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
    _ = ‖z‖ := one_mul _

-- no-dlmf: dominated-convergence helper, no DLMF equation
/-- DCT on `(0,1]`: `∫ ↑(e^{-εt}) g → ∫ g` as `ε ↓ 0`. -/
theorem dct01 {g : ℝ → ℂ} (hg : IntegrableOn g (Ioc 0 1)) :
    Tendsto (fun ε : ℝ => ∫ t in Ioc (0:ℝ) 1, ((Real.exp (-ε * t) : ℝ) : ℂ) * g t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioc (0:ℝ) 1, g t)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖) ?_ ?_ hg.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (by fun_prop : Continuous fun t : ℝ => ((Real.exp (-ε * t) : ℝ) : ℂ)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact norm_exp_smul_le hε ht.1 (g t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h1 : Tendsto (fun ε : ℝ => Real.exp (-ε * t)) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => Real.exp (-ε * t)) := by fun_prop
      have h : Tendsto (fun ε : ℝ => Real.exp (-ε * t)) (𝓝[>] (0:ℝ)) (𝓝 (Real.exp (-0 * t))) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have h2 := ((Complex.continuous_ofReal.tendsto (1:ℝ)).comp h1).mul_const (g t)
    rw [Complex.ofReal_one, one_mul] at h2
    exact h2

-- no-dlmf: integrability helper, no DLMF equation
/-- `↑(e^{-εt})·fmel` integrable on `(0,∞)` (`Re s>0`, `ε>0`). -/
theorem efmel_int (s : ℂ) (hs0 : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t) (Ioi 0) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-ε * t ^ (1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hε
  refine Integrable.mono' hbase
    ((by fun_prop : Continuous fun t : ℝ => ((Real.exp (-ε * t) : ℝ) : ℂ)).aestronglyMeasurable.mul
      ((continuousOn_fmel s).aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_fmel htpos,
    Real.rpow_one]
  rw [mul_comm]

-- no-dlmf: integrability helper, no DLMF equation
/-- `↑(e^{-εt})·fhat` integrable on `(0,∞)` (`Re s<1`, `ε>0`). -/
theorem efhat_int (s : ℂ) (hs1 : s.re < 1) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t => ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t) (Ioi 0) := by
  have hexp : IntegrableOn (fun t => Real.exp (-ε * t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (a := -ε) (by linarith) (0:ℝ)
  refine Integrable.mono' hexp
    ((by fun_prop : Continuous fun t : ℝ => ((Real.exp (-ε * t) : ℝ) : ℂ)).aestronglyMeasurable.mul
      (fhat_continuous s).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-ε * t) * ‖fhat s t‖ ≤ Real.exp (-ε * t) * 1 :=
        mul_le_mul_of_nonneg_left (fhat_bound s hs1 t) (Real.exp_pos _).le
    _ = Real.exp (-ε * t) := mul_one _

-- no-dlmf: proof-internal definition (improper-convergence value)
/-- The improper-convergence value `L`. -/
noncomputable def Lval (s : ℂ) : ℂ :=
  (∫ t in (0:ℝ)..1, fmel s t)
    + (-(Complex.I * Complex.exp (-(Complex.I * (1 : ℂ)))) - ∫ t in Ioi (1 : ℝ), tailInt s t)

-- no-dlmf: integrability helper, no DLMF equation
/-- `fhat` is integrable on `(0,1]` (continuous). -/
theorem fhat_integrableOn_Ioc01 (s : ℂ) : IntegrableOn (fhat s) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    ((fhat_continuous s).intervalIntegrable 0 1)

-- no-dlmf: Abel-bridge method lemma, no DLMF equation
/-- **The Abel bridge for `fmel`:** `∫_{(0,∞)} e^{-εt}·t^{s-1}e^{-it} → L` (`0<Re s<1`). -/
theorem habel (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
      (𝓝[>] 0) (𝓝 (Lval s)) := by
  -- ∫_0^R fhat → L̂ = fmel 1 + L₁
  have hfhat_conv : Tendsto (fun R => ∫ t in (0:ℝ)..R, fhat s t) atTop
      (𝓝 (fmel s 1
        + (-(Complex.I * Complex.exp (-(Complex.I * (1:ℂ)))) - ∫ t in Ioi (1:ℝ), tailInt s t))) := by
    refine (tendsto_const_nhds.add (tail_tendsto s hs1)).congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    rw [← intervalIntegral.integral_add_adjacent_intervals
        ((fhat_continuous s).intervalIntegrable 0 1) ((fhat_continuous s).intervalIntegrable 1 R)]
    congr 1
    · have hc : (∫ t in (0:ℝ)..1, fhat s t) = ∫ _t in (0:ℝ)..1, fmel s 1 :=
        intervalIntegral.integral_congr (fun t ht => by
          rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; rw [fhat, max_eq_right ht.2])
      rw [hc, intervalIntegral.integral_const]; simp
    · refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hR] at ht
      rw [fhat, max_eq_left ht.1]
  have hC := abelian_exp_complex (fhat s) _ (fhat_continuous s) (fhat_bound s hs1) hfhat_conv
  -- the splits and DCTs
  have hsplit_eq : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
        = (∫ t in Ioc (0:ℝ) 1, ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
          + ((∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t)
            - ∫ t in Ioc (0:ℝ) 1, ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t) := by
    intro ε hε
    have hfm := efmel_int s hs0 hε
    have hfh := efhat_int s hs1 hε
    have hunion : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi_same
    have hfm_split : (∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
        = (∫ t in Ioc (0:ℝ) 1, ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
          + ∫ t in Ioi (1:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t := by
      rw [hunion, setIntegral_union hdisj measurableSet_Ioi
        (hfm.mono_set (by rw [hunion]; exact subset_union_left))
        (hfm.mono_set (by rw [hunion]; exact subset_union_right))]
    have hfh_split : (∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t)
        = (∫ t in Ioc (0:ℝ) 1, ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t)
          + ∫ t in Ioi (1:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t := by
      rw [hunion, setIntegral_union hdisj measurableSet_Ioi
        (hfh.mono_set (by rw [hunion]; exact subset_union_left))
        (hfh.mono_set (by rw [hunion]; exact subset_union_right))]
    have heq1R : (∫ t in Ioi (1:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
        = ∫ t in Ioi (1:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fhat s t := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [fhat, max_eq_left (le_of_lt ht)]
    rw [hfm_split, hfh_split, heq1R]; ring
  -- assemble the limit
  have hB := dct01 (fmel_integrableOn_Ioc01 s hs0)
  have hD := dct01 (fhat_integrableOn_Ioc01 s)
  have hlim := hB.add (hC.sub hD)
  -- the limit value equals Lval
  have hfhat01 : (∫ t in Ioc (0:ℝ) 1, fhat s t) = fmel s 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => fmel s 1) (fun t ht => by
        rw [fhat, max_eq_right ht.2]), setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num)]
    simp
  have hI01 : (∫ t in (0:ℝ)..1, fmel s t) = ∫ t in Ioc (0:ℝ) 1, fmel s t :=
    intervalIntegral.integral_of_le (by norm_num)
  have hval : (∫ t in Ioc (0:ℝ) 1, fmel s t)
      + ((fmel s 1
          + (-(Complex.I * Complex.exp (-(Complex.I * (1:ℂ)))) - ∫ t in Ioi (1:ℝ), tailInt s t))
        - ∫ t in Ioc (0:ℝ) 1, fhat s t) = Lval s := by
    rw [hfhat01, Lval, hI01]; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hsplit_eq ε hε).symm

/-- **The Mellin transform of `e^{-it}` (closing #7).** For `0 < Re s < 1`, the bare
improper oscillatory integral converges to the imaginary-axis value:
`∫_0^∞ t^{s-1}e^{-it} dt = e^{-iπs/2}Γ(s)`. -/
-- no-dlmf: Mellin-transform method result, no DLMF Ch 1–2 equation
theorem mellin_exp_neg_I (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, fmel s t) atTop
      (𝓝 (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s)) := by
  have hL : Lval s = Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s := by
    have ha := habel s hs0 hs1
    have hg := gamma_abel_regularized s hs0
    have hmatch : (fun ε : ℝ => ∫ t in Ioi (0:ℝ), ((Real.exp (-ε * t) : ℝ) : ℂ) * fmel s t)
        = (fun ε : ℝ => ∫ t in Ioi (0:ℝ),
            (t : ℂ) ^ (s - 1) * Complex.exp (-(((ε : ℂ) + Complex.I) * (t : ℂ)))) := by
      funext ε
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      rw [fmel, show -(((ε : ℂ) + Complex.I) * (t : ℂ))
            = -((ε : ℂ) * (t : ℂ)) + -(Complex.I * (t : ℂ)) by ring, Complex.exp_add,
        show ((Real.exp (-ε * t) : ℝ) : ℂ) = Complex.exp (-((ε : ℂ) * (t : ℂ))) by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
      ring
    rw [hmatch] at ha
    exact tendsto_nhds_unique ha hg
  rw [← hL]
  exact improper_converges s hs0 hs1

/-! ### Scaled bare Mellin transform (general rate a>0) -/

/-- **Scaled bare Mellin transform of `e^{-iat}`** (`a>0`, `0<Re s<1`):
`∫₀^∞ t^{s-1}e^{-iat} dt = a^{-s} e^{-iπs/2} Γ(s)` (bare improper `lim_R ∫₀^R`). -/
-- no-dlmf: Mellin-transform method result, no DLMF Ch 1–2 equation
theorem mellin_exp_neg_Ia (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,
        (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ)))) atTop
      (𝓝 ((a : ℂ) ^ (-s) * (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s))) := by
  -- per-R substitution u = a·t
  have hsub : ∀ R : ℝ, 0 ≤ R →
      (∫ t in (0:ℝ)..R, (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))))
        = (a : ℂ) ^ (-s) * ∫ u in (0:ℝ)..(a * R), fmel s u := by
    intro R hR
    have hcongr : (∫ t in (0:ℝ)..R, (t : ℂ) ^ (s - 1) * Complex.exp (-(Complex.I * (a : ℂ) * (t : ℂ))))
        = ∫ t in (0:ℝ)..R, (a : ℂ) ^ (1 - s) * fmel s (a * t) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hR] at ht
      have htpos : 0 ≤ t := ht.1
      rw [fmel, Complex.ofReal_mul, mul_cpow_ofReal_nonneg ha.le htpos]
      rw [show (a : ℂ) ^ (1 - s) * ((a : ℂ) ^ (s - 1) * (t : ℂ) ^ (s - 1)
            * Complex.exp (-(Complex.I * ((a : ℂ) * (t : ℂ)))))
          = ((a : ℂ) ^ (1 - s) * (a : ℂ) ^ (s - 1)) * ((t : ℂ) ^ (s - 1)
            * Complex.exp (-(Complex.I * ((a : ℂ) * (t : ℂ))))) by ring]
      rw [← Complex.cpow_add _ _ (by exact_mod_cast ha.ne' : (a : ℂ) ≠ 0),
        show (1 - s) + (s - 1) = 0 by ring, Complex.cpow_zero, one_mul]
      congr 2; ring
    rw [hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fmel s) ha.ne', mul_zero, Complex.real_smul,
      ← mul_assoc]
    congr 1
    rw [show ((a⁻¹ : ℝ) : ℂ) = (a : ℂ) ^ (-1 : ℂ) by
        rw [Complex.cpow_neg_one]; exact Complex.ofReal_inv a,
      ← Complex.cpow_add _ _ (by exact_mod_cast ha.ne' : (a : ℂ) ≠ 0)]
    congr 1; ring
  -- compose the mellin limit with R ↦ a·R → ∞
  have hcomp : Tendsto (fun R : ℝ => ∫ u in (0:ℝ)..(a * R), fmel s u) atTop
      (𝓝 (Complex.exp (-(s * ((π / 2 : ℝ) : ℂ) * Complex.I)) * Complex.Gamma s)) := by
    have hmel := mellin_exp_neg_I s hs0 hs1
    have haR : Tendsto (fun R : ℝ => a * R) atTop atTop := Filter.Tendsto.const_mul_atTop ha tendsto_id
    exact hmel.comp haR
  refine (hcomp.const_mul ((a : ℂ) ^ (-s))).congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  exact (hsub R hR).symm

end FLMF.Methods.ContourRotation.Gamma
