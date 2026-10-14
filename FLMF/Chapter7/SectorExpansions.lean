import FLMF.Support.SectorPoincare
import FLMF.Chapter7.ErfcLeading
import FLMF.Chapter7.ComplexRepeatedErfc
import FLMF.Chapter7.AsymptoticExpansions
import FLMF.Chapter7.FresnelComplex

/-!
# Sector-uniform Poincaré expansions in DLMF Chapter 7

DLMF states three of the Chapter-7 asymptotic expansions as *sector* statements:

* **7.12.2** `f(z) ∼ (1/(πz)) ∑_m (−1)ᵐ (½)_{2m}/(πz²/2)^{2m}`, `z → ∞`, `|ph z| ≤ ½π − δ`;
* **7.12.3** `g(z) ∼ (1/(πz)) ∑_m (−1)ᵐ (½)_{2m+1}/(πz²/2)^{2m+1}`, same sector;
* **7.18.14** `iⁿerfc(z) ∼ (2/√π)·e^{−z²}/(2z)^{n+1} ∑_m (−1)ᵐ (2m+n)!/(n! m! (2z)^{2m})`,
  `z → ∞`, `|ph z| ≤ ¾π − δ`.

This file gives all three as **explicit-constant Poincaré remainder bounds**, uniform on
the closed sector and asserted at *every* truncation order (which pins every coefficient
of the expansion).

The engine is `FLMF.Methods.SectorPoincare`:

* for 7.18.14 the horizontal-ray representation
  `iⁿerfc(z) = (2/√π)∫₀^∞ (sⁿ/n!) e^{−(z+s)²} ds` is first *rotated* onto the ray
  `arg s = θ` (`cRepErfc_rotated_rep`), which is proved from the `n = 0` rotated
  representation together with the integration-by-parts recurrence in `n` — the rotated
  moments satisfy the same three-term recurrence DLMF 7.18.7 as `iⁿerfc` itself.  Choosing
  `θ = −(ph z)/3` puts the Laplace rate `2 z e^{iθ}` in the half-plane
  `Re ≥ 2 sin(2δ/3)‖z‖` and the Gaussian rate `e^{2iθ}` in the closed right half-plane,
  and the Watson-type lemma `norm_gaussLaplace_moment_sub_taylor_le` finishes.
* for 7.12.2/7.12.3 the relation DLMF 7.5.10
  `g(z) ± i f(z) = ½(1±i) e^{ζ±²} erfc(ζ±)`, `ζ± = ½√π(1∓i)z`,
  transports the *already proven* `erfc` sector bound `FLMF.Error.cerfc_poincare_bound`
  from `|ph ζ| ≤ ¾π − δ` back to `|ph z| ≤ ½π − δ` — the `±π/4` rotation of the argument
  is exactly the difference between the two DLMF sectors.  The half of the `erfc` series
  with the "wrong" parity cancels between the two branches, which is what turns a series
  in `ζ^{−(2j+1)}` into DLMF's series in `(πz²/2)^{−2m}` (resp. `(πz²/2)^{−(2m+1)}`).

Main results: `erf_7_18_14_sector`, `erf_7_12_2_sector`, `erf_7_12_3_sector`.
-/

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set FLMF.Methods.SectorPoincare

/-! ## Part I — the rotated-ray representation of `iⁿerfc` -/

-- no-dlmf: support def, the rotated-ray moment behind the 7.18.14 sector bound
/-- The rotated-ray moment `Aₙ(ω,z) = ∫₀^∞ sⁿ e^{−(z+ωs)²} ds`. -/
private noncomputable def rotMoment (ω z : ℂ) (n : ℕ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)

-- no-dlmf: Gaussian majorant on the rotated ray; proof infrastructure
/-- On the rotated ray, `‖e^{−(z+ωs)²}‖ ≤ e^{−Re(z²)+2‖z‖²/μ}·e^{−(μ/2)s²}` where
`μ = Re(ω²) > 0` and `‖ω‖ = 1`. -/
private theorem norm_exp_rotRay_le {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re)
    (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (-(z + ω * (s : ℂ)) ^ 2)‖
      ≤ Real.exp (-(z ^ 2).re + 2 * ‖z‖ ^ 2 / (ω ^ 2).re)
          * Real.exp (-((ω ^ 2).re / 2) * s ^ 2) := by
  set μ : ℝ := (ω ^ 2).re with hμdef
  have hre : (-(z + ω * (s : ℂ)) ^ 2).re
      = -((z ^ 2).re + 2 * (z * ω).re * s + μ * s ^ 2) := by
    have hsre : ((s : ℂ) ^ 2).re = s ^ 2 := by
      simp [pow_two, Complex.mul_re]
    have hsim : ((s : ℂ) ^ 2).im = 0 := by
      simp [pow_two, Complex.mul_im]
    have h : -(z + ω * (s : ℂ)) ^ 2
        = -(z ^ 2) - (2 * (z * ω)) * ((s : ℝ) : ℂ) - (ω ^ 2) * ((s : ℂ) ^ 2) := by
      ring
    rw [h]
    simp [Complex.mul_re, hsre, hsim, hμdef]
    ring
  have hzω : |(z * ω).re| ≤ ‖z‖ := by
    have h1 : |(z * ω).re| ≤ ‖z * ω‖ := Complex.abs_re_le_norm _
    rwa [norm_mul, hωn, mul_one] at h1
  rw [Complex.norm_exp, hre, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h2 : -(2 * (z * ω).re * s) ≤ 2 * ‖z‖ * s := by
    have := abs_le.mp hzω
    nlinarith [this.1, this.2]
  have h3 : 2 * ‖z‖ * s - (μ / 2) * s ^ 2 ≤ 2 * ‖z‖ ^ 2 / μ := by
    rw [le_div_iff₀ hμ]
    nlinarith [sq_nonneg (μ * s - 2 * ‖z‖)]
  nlinarith [h2, h3]

-- no-dlmf: integrability of the rotated-ray moment integrand; proof infrastructure
private theorem integrableOn_rotMoment {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re)
    (z : ℂ) (n : ℕ) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
      (Ioi (0 : ℝ)) := by
  set μ : ℝ := (ω ^ 2).re with hμdef
  set K : ℝ := Real.exp (-(z ^ 2).re + 2 * ‖z‖ ^ 2 / μ) with hKdef
  have hgauss : IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-(μ / 2) * s ^ 2))
      (Ioi (0 : ℝ)) := by
    have hn : (-1 : ℝ) < (n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := μ / 2) (by positivity) hn
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    rw [Real.rpow_natCast]
  refine Integrable.mono' (hgauss.const_mul K) ?_ ?_
  · exact (Complex.continuous_ofReal.pow n).aestronglyMeasurable.mul
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := hs
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have h := norm_exp_rotRay_le hωn hμ z hs0.le
    calc s ^ n * ‖Complex.exp (-(z + ω * (s : ℂ)) ^ 2)‖
        ≤ s ^ n * (K * Real.exp (-(μ / 2) * s ^ 2)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * (s ^ n * Real.exp (-(μ / 2) * s ^ 2)) := by ring

-- no-dlmf: decay of the rotated-ray integrand at `+∞`; proof infrastructure
private theorem tendsto_rotRay_atTop {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re)
    (z : ℂ) (n : ℕ) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
      atTop (𝓝 0) := by
  set μ : ℝ := (ω ^ 2).re with hμdef
  set K : ℝ := Real.exp (-(z ^ 2).re + 2 * ‖z‖ ^ 2 / μ) with hKdef
  have hK : 0 < K := Real.exp_pos _
  -- majorant `K (2/μ)ⁿ · (μ s/2)ⁿ e^{−μ s/2}` for `s ≥ 1`
  have hbase : Tendsto (fun s : ℝ => (μ * s / 2) ^ n * Real.exp (-(μ * s / 2)))
      atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    have hc : Tendsto (fun s : ℝ => μ * s / 2) atTop atTop := by
      apply Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 2)
      exact Filter.Tendsto.const_mul_atTop hμ tendsto_id
    exact h.comp hc
  have hmaj : Tendsto (fun s : ℝ => (K * (2 / μ) ^ n) * ((μ * s / 2) ^ n
      * Real.exp (-(μ * s / 2)))) atTop (𝓝 0) := by
    simpa using hbase.const_mul (K * (2 / μ) ^ n)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have h := norm_exp_rotRay_le hωn hμ z hs0.le
  have hsq : Real.exp (-(μ / 2) * s ^ 2) ≤ Real.exp (-(μ * s / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_pos hμ hs0).le (sub_nonneg.mpr hs)]
  have hp : (2 / μ : ℝ) ^ n * (μ * s / 2) ^ n = s ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hrw : (K * (2 / μ) ^ n) * ((μ * s / 2) ^ n * Real.exp (-(μ * s / 2)))
      = K * (s ^ n * Real.exp (-(μ * s / 2))) := by
    rw [show (K * (2 / μ : ℝ) ^ n) * ((μ * s / 2) ^ n * Real.exp (-(μ * s / 2)))
        = ((2 / μ : ℝ) ^ n * (μ * s / 2) ^ n) * (K * Real.exp (-(μ * s / 2))) by ring, hp]
    ring
  rw [hrw]
  calc s ^ n * ‖Complex.exp (-(z + ω * (s : ℂ)) ^ 2)‖
      ≤ s ^ n * (K * Real.exp (-(μ / 2) * s ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ s ^ n * (K * Real.exp (-(μ * s / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq hK.le
    _ = K * (s ^ n * Real.exp (-(μ * s / 2))) := by ring

-- no-dlmf: derivative of the rotated-ray integrand; proof infrastructure
private theorem hasDerivAt_rotRay (ω z : ℂ) (n : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(z + ω * (t : ℂ)) ^ 2))
      ((n : ℂ) * ((s : ℂ) ^ (n - 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
        - 2 * ω * z * ((s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
        - 2 * ω ^ 2 * ((s : ℂ) ^ (n + 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))) s := by
  have hpow : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ) ^ n)
      ((n : ℂ) * (s : ℂ) ^ (n - 1)) s := by
    have h : HasDerivAt (fun u : ℂ => u ^ n) ((n : ℂ) * (s : ℂ) ^ (n - 1) * 1) (s : ℂ) :=
      (hasDerivAt_id (s : ℂ)).pow n
    simpa using h.comp_ofReal
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(z + ω * ((t : ℝ) : ℂ)) ^ 2))
      (-(2 * (z + ω * (s : ℂ)) * ω) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)) s := by
    have hin : HasDerivAt (fun u : ℂ => -(z + ω * u) ^ 2)
        (-(2 * (z + ω * (s : ℂ)) * ω)) (s : ℂ) := by
      have h1 : HasDerivAt (fun u : ℂ => z + ω * u) ω (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).const_mul ω).const_add z
      have h2 : HasDerivAt (fun u : ℂ => (z + ω * u) ^ 2)
          (2 * (z + ω * (s : ℂ)) ^ 1 * ω) (s : ℂ) := h1.pow 2
      simpa using h2.neg
    simpa [mul_comm] using (hin.cexp).comp_ofReal
  have hfin := hpow.mul hexp
  convert hfin using 1
  rw [pow_succ]
  ring

-- no-dlmf: integrability of the derivative of the rotated-ray integrand; infrastructure
private theorem integrableOn_rotRayDeriv {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re)
    (z : ℂ) (n : ℕ) :
    IntegrableOn (fun s : ℝ =>
        (n : ℂ) * ((s : ℂ) ^ (n - 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
        - 2 * ω * z * ((s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
        - 2 * ω ^ 2 * ((s : ℂ) ^ (n + 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)))
      (Ioi (0 : ℝ)) :=
  (((integrableOn_rotMoment hωn hμ z (n - 1)).const_mul ((n : ℂ))).sub
      ((integrableOn_rotMoment hωn hμ z n).const_mul (2 * ω * z))).sub
    ((integrableOn_rotMoment hωn hμ z (n + 1)).const_mul (2 * ω ^ 2))

-- no-dlmf: the integration-by-parts recurrence for the rotated-ray moments;
-- proof infrastructure for the 7.18.14 sector bound
/-- **Integration by parts in `s` for the rotated-ray moments.**  With
`Aₙ = ∫₀^∞ sⁿ e^{−(z+ωs)²} ds` (`‖ω‖ = 1`, `Re ω² > 0`),
`n·A_{n−1} + 0ⁿ·e^{−z²} = 2ωz·Aₙ + 2ω²·A_{n+1}`.
(The `n = 0` instance reads `e^{−z²} = 2ωz A₀ + 2ω² A₁`; for `n ≥ 1` the boundary term at
`s = 0` vanishes.)  This is the *only* analytic input needed to move the rotation past
`n = 0`: rewritten in terms of `(2/√π)ω^{n+1}Aₙ/n!` it becomes verbatim the three-term
recurrence DLMF 7.18.7 satisfied by `iⁿerfc`. -/
private theorem rotMoment_ibp {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re) (z : ℂ) (n : ℕ) :
    (n : ℂ) * rotMoment ω z (n - 1) + (0 : ℂ) ^ n * Complex.exp (-z ^ 2)
      = 2 * ω * z * rotMoment ω z n + 2 * ω ^ 2 * rotMoment ω z (n + 1) := by
  set F : ℝ → ℂ := fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(z + ω * (t : ℂ)) ^ 2) with hFdef
  set G : ℝ → ℂ := fun s : ℝ =>
      (n : ℂ) * ((s : ℂ) ^ (n - 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
      - 2 * ω * z * ((s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
      - 2 * ω ^ 2 * ((s : ℂ) ^ (n + 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)) with hGdef
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) := integrableOn_rotRayDeriv hωn hμ z n
  have hcont : ContinuousWithinAt F (Ici (0 : ℝ)) 0 := by
    have : Continuous F := by
      rw [hFdef]
      exact (Complex.continuous_ofReal.pow n).mul (Complex.continuous_exp.comp (by fun_prop))
    exact this.continuousWithinAt
  have hFtop : Tendsto F atTop (𝓝 0) := tendsto_rotRay_atTop hωn hμ z n
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (f' := G)
    (a := (0 : ℝ)) (m := (0 : ℂ)) hcont (fun s _ => hasDerivAt_rotRay ω z n s) hGint hFtop
  have hF0 : F 0 = (0 : ℂ) ^ n * Complex.exp (-z ^ 2) := by
    rw [hFdef]
    simp
  -- split the integral of `G`
  have hsplit : (∫ s in Ioi (0 : ℝ), G s)
      = (n : ℂ) * rotMoment ω z (n - 1) - 2 * ω * z * rotMoment ω z n
        - 2 * ω ^ 2 * rotMoment ω z (n + 1) := by
    have hi1 : IntegrableOn
        (fun s : ℝ => (n : ℂ) * ((s : ℂ) ^ (n - 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)))
        (Ioi (0 : ℝ)) := (integrableOn_rotMoment hωn hμ z (n - 1)).const_mul ((n : ℂ))
    have hi2 : IntegrableOn
        (fun s : ℝ => 2 * ω * z * ((s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)))
        (Ioi (0 : ℝ)) := (integrableOn_rotMoment hωn hμ z n).const_mul (2 * ω * z)
    have hi3 : IntegrableOn
        (fun s : ℝ => 2 * ω ^ 2 * ((s : ℂ) ^ (n + 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)))
        (Ioi (0 : ℝ)) := (integrableOn_rotMoment hωn hμ z (n + 1)).const_mul (2 * ω ^ 2)
    have hi12 : IntegrableOn
        (fun s : ℝ => (n : ℂ) * ((s : ℂ) ^ (n - 1) * Complex.exp (-(z + ω * (s : ℂ)) ^ 2))
          - 2 * ω * z * ((s : ℂ) ^ n * Complex.exp (-(z + ω * (s : ℂ)) ^ 2)))
        (Ioi (0 : ℝ)) := hi1.sub hi2
    simp only [hGdef]
    rw [MeasureTheory.integral_sub hi12 hi3, MeasureTheory.integral_sub hi1 hi2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit, hF0] at hftc
  linear_combination hftc

/-! ### The rotated representation of `iⁿerfc` -/

-- no-dlmf: support def, the rotated-ray form of `iⁿerfc`
/-- `(2/√π)·ω^{n+1}·Aₙ(ω,z)/n!` — the candidate rotated-ray representation of
`iⁿerfc(z)`. -/
private noncomputable def rotRep (ω z : ℂ) (n : ℕ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * ω ^ (n + 1) * rotMoment ω z n / (n.factorial : ℂ)

-- no-dlmf: the `n = 0` rotated representation (a re-derivation of the DLMF 7.7.3
-- Gaussian integral in rotated form); proof infrastructure
private theorem rotRep_zero {θ : ℝ} (hθ : |θ| < Real.pi / 4) (z : ℂ) :
    rotRep (Complex.exp ((θ : ℂ) * Complex.I)) z 0 = cerfc z := by
  obtain ⟨hθ1, hθ2⟩ := abs_lt.mp hθ
  have hπ : 0 < Real.pi := Real.pi_pos
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hωne : ω ≠ 0 := Complex.exp_ne_zero _
  have him : (((2 * θ : ℝ) : ℂ) * Complex.I).im = 2 * θ := by simp [Complex.mul_im]
  have hω2 : ω ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hωdef, sq, ← Complex.exp_add]; congr 1; push_cast; ring
  have ha : 0 < (ω ^ 2).re := by
    rw [hω2, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcpow : (ω ^ 2) ^ (-(1 : ℂ) / 2) = ω⁻¹ := by
    rw [hω2, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
    rw [Complex.log_exp (by rw [him]; linarith) (by rw [him]; linarith)]
    rw [hωdef, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hg := gaussLin_integral_eq_cerfc (a := ω ^ 2) (z := Complex.I * (z * ω)) ha
  rw [hcpow] at hg
  have hexp : -(Complex.I * (z * ω)) ^ 2 / ω ^ 2 = z ^ 2 := by
    have h : (Complex.I * (z * ω)) ^ 2 = -(z ^ 2 * ω ^ 2) := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [h]
    field_simp
  have harg : -Complex.I * (Complex.I * (z * ω)) * ω⁻¹ = z := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hexp, harg] at hg
  -- the rotated-ray moment is `e^{−z²}` times the Gaussian-linear integral
  have hmom : rotMoment ω z 0 = Complex.exp (-z ^ 2) *
      ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(ω ^ 2) * (t : ℂ) ^ 2 + 2 * Complex.I * (Complex.I * (z * ω)) * (t : ℂ)) := by
    rw [rotMoment, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [pow_zero, one_mul, ← Complex.exp_add]
    congr 1
    have h : 2 * Complex.I * (Complex.I * (z * ω)) * (t : ℂ) = -(2 * (z * ω) * (t : ℂ)) := by
      rw [show (2:ℂ) * Complex.I * (Complex.I * (z * ω)) * (t:ℂ)
            = (Complex.I * Complex.I) * (2 * (z * ω) * (t:ℂ)) by ring, Complex.I_mul_I]
      ring
    rw [h]
    ring
  have hsπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hexpz : Complex.exp (-z ^ 2) * Complex.exp (z ^ 2) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [rotRep, hmom, hg, pow_one, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [show (2 / (Real.sqrt Real.pi : ℂ)) * ω *
        (Complex.exp (-z ^ 2) *
          (1 / 2 * (Real.sqrt Real.pi : ℂ) * ω⁻¹ * Complex.exp (z ^ 2) * cerfc z))
      = (Complex.exp (-z ^ 2) * Complex.exp (z ^ 2)) *
          ((2 / (Real.sqrt Real.pi : ℂ)) * (1 / 2 * (Real.sqrt Real.pi : ℂ))) *
          (ω * ω⁻¹) * cerfc z by ring]
  rw [hexpz, mul_inv_cancel₀ hωne]
  field_simp

-- no-dlmf: the three-term recurrence inherited by the rotated representation
/-- The rotated representation obeys the same three-term recurrence (DLMF 7.18.7) as
`iⁿerfc`: `Rₙ = 2z·R_{n+1} + 2(n+2)·R_{n+2}`. -/
private theorem rotRep_rec {ω : ℂ} (hωn : ‖ω‖ = 1) (hμ : 0 < (ω ^ 2).re) (z : ℂ) (n : ℕ) :
    rotRep ω z n = 2 * z * rotRep ω z (n + 1) + 2 * ((n : ℂ) + 2) * rotRep ω z (n + 2) := by
  have hibp := rotMoment_ibp hωn hμ z (n + 1)
  simp only [Nat.add_sub_cancel] at hibp
  rw [show (0 : ℂ) ^ (n + 1) = 0 by simp, zero_mul, add_zero] at hibp
  push_cast at hibp
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simpa using h
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by
    have h : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (n + 1))
    push_cast at h
    convert h using 2
  have hfn : ((n.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hA0 : rotMoment ω z n
      = (2 * ω * z * rotMoment ω z (n + 1) + 2 * ω ^ 2 * rotMoment ω z (n + 2))
          / ((n : ℂ) + 1) := by
    rw [eq_div_iff hn1]
    linear_combination hibp
  have hf1 : (((n + 1).factorial : ℕ) : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf2 : (((n + 2).factorial : ℕ) : ℂ)
      = ((n : ℂ) + 2) * (((n : ℂ) + 1) * (n.factorial : ℂ)) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [rotRep, rotRep, rotRep, hf1, hf2, hA0]
  field_simp
  ring

-- no-dlmf: identification of the rotated representation with `iⁿerfc`
/-- **Rotated-ray representation of `iⁿerfc`.**  For every rotation angle `|θ| < π/4`,
with `ω = e^{iθ}`,
`iⁿerfc(z) = (2/√π)·ω^{n+1}·(1/n!)·∫₀^∞ sⁿ e^{−(z+ωs)²} ds`.

The value is independent of `θ`: the `n = 0` case is the rotated Gaussian integral
(DLMF 7.7.3, `rotRep_zero`), and both sides obey the same three-term recurrence
(DLMF 7.18.7), the rotated one by integration by parts in `s` (`rotMoment_ibp`).  It is
the rotation that reaches the sector `|ph z| ≤ 3π/4 − δ`: on the unrotated ray the
integrand is controllable only for `Re z > 0`. -/
private theorem rotRep_eq_cRepErfc {θ : ℝ} (hθ : |θ| < Real.pi / 4) (z : ℂ) (n : ℕ) :
    rotRep (Complex.exp ((θ : ℂ) * Complex.I)) z n = cRepErfc n z := by
  obtain ⟨hθ1, hθ2⟩ := abs_lt.mp hθ
  have hπ : 0 < Real.pi := Real.pi_pos
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hωn : ‖ω‖ = 1 := by rw [hωdef]; exact Complex.norm_exp_ofReal_mul_I θ
  have hω2 : ω ^ 2 = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hωdef, sq, ← Complex.exp_add]; congr 1; push_cast; ring
  have hμ : 0 < (ω ^ 2).re := by
    rw [hω2, Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- base case `n = 0`
  have h0 : rotRep ω z 0 = cRepErfc 0 z := by
    rw [rotRep_zero hθ z, cRepErfc_zero]
  -- base case `n = 1`, from the `n = 0` integration by parts and DLMF 7.18.7
  have h1 : rotRep ω z 1 = cRepErfc 1 z := by
    have hibp := rotMoment_ibp hωn hμ z 0
    simp only [Nat.zero_sub, Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul] at hibp
    have hsπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
    have hpair : 2 * z * rotRep ω z 0 + 2 * rotRep ω z 1 = cRepErfcNegOne z := by
      rw [rotRep, rotRep, cRepErfcNegOne]
      simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl, pow_one]
      field_simp
      linear_combination (-1 : ℂ) * hibp
    have h718 := cerf_7_18_7 0 z
    simp only [Nat.cast_zero, zero_add, mul_one, cRepErfcPred_zero, cRepErfcPred_succ] at h718
    rw [cRepErfc_zero] at h718
    rw [rotRep_zero hθ z] at hpair
    linear_combination (hpair - h718) / 2
  -- two-step induction
  have main : ∀ m : ℕ, rotRep ω z m = cRepErfc m z ∧ rotRep ω z (m + 1) = cRepErfc (m + 1) z := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr := rotRep_rec hωn hμ z k
      have hc := cerf_7_18_7 (k + 1) z
      simp only [cRepErfcPred_succ] at hc
      push_cast at hc
      have hne : (2 : ℂ) * ((k : ℂ) + 2) ≠ 0 := by
        have h : ((k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (k + 1))
        push_cast at h
        simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
        exact h
      have hkey : 2 * ((k : ℂ) + 2) * rotRep ω z (k + 2)
          = 2 * ((k : ℂ) + 2) * cRepErfc (k + 2) z := by
        rw [ih.1, ih.2] at hr
        linear_combination -hr - hc
      exact mul_left_cancel₀ hne hkey
  exact (main n).1

-- no-dlmf: rewriting of the rotated-ray moment in Gaussian-damped Laplace form
private theorem rotMoment_eq_gaussLaplace (ω z : ℂ) (n : ℕ) :
    rotMoment ω z n = Complex.exp (-z ^ 2) *
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n *
        (Complex.exp (-((2 * (z * ω)) * (s : ℂ))) * Complex.exp (-(ω ^ 2) * (s : ℂ) ^ 2)) := by
  rw [rotMoment, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  have h : Complex.exp (-z ^ 2) *
      (Complex.exp (-((2 * (z * ω)) * (s : ℂ))) * Complex.exp (-(ω ^ 2) * (s : ℂ) ^ 2))
      = Complex.exp (-(z + ω * (s : ℂ)) ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [← h]
  ring

/-! ## Part II — DLMF 7.18.14 on the sector `|ph z| ≤ ¾π − δ` -/

-- no-dlmf: support def, the `N`-term truncation of the DLMF 7.18.14 series
/-- The `N`-term truncation of the DLMF 7.18.14 series,
`(2/√π)·(e^{−z²}/(2z)^{n+1})·∑_{m<N} (−1)ᵐ (2m+n)!/(n! m! (2z)^{2m})`. -/
noncomputable def ctruncRepErfc (n N : ℕ) (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi : ℂ) * Complex.exp (-z ^ 2) / (2 * z) ^ (n + 1) *
    ∑ m ∈ Finset.range N, (-1 : ℂ) ^ m * ((2 * m + n).factorial : ℂ)
        / ((n.factorial : ℂ) * (m.factorial : ℂ) * (2 * z) ^ (2 * m))

-- no-dlmf: global-in-`z` sector bound, the engine behind the tagged
-- `erf_7_18_14_sector` below (which restricts to the DLMF `z → ∞` regime
-- `1 ≤ ‖z‖`); support lemma
/-- The Poincaré remainder bound for the repeated integrals of the
complementary error function (7.18.14), *uniform on the closed sector*
`|ph z| ≤ ¾π − δ` and global in `z ≠ 0`:
for every order `n` and every truncation order `N`, and every `δ ∈ (0, ¾π)`, there is a
constant `C > 0` (independent of `z`) with

`‖iⁿerfc(z) − (2/√π)(e^{−z²}/(2z)^{n+1}) ∑_{m<N} (−1)ᵐ(2m+n)!/(n! m! (2z)^{2m})‖
    ≤ C·‖e^{−z²}‖/‖z‖^{n+2N+1}`

for all `z ≠ 0` with `|ph z| ≤ ¾π − δ`.

Because the estimate is asserted for *every* `N`, it pins every coefficient of the
expansion, and because the right-hand side is `o` of the last retained term as `z → ∞`
in the sector, it is exactly Poincaré's `∼` for the displayed series.  An admissible
constant is `C = (2/√π)·(n+2N)!/(n!·(2 sin(2δ/3))^{n+2N+1})`. -/
theorem cRepErfc_sector_bound (n N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * Real.pi / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → |Complex.arg z| ≤ 3 * Real.pi / 4 - δ →
      ‖cRepErfc n z - ctruncRepErfc n N z‖
        ≤ C * ‖Complex.exp (-z ^ 2)‖ / ‖z‖ ^ (n + 2 * N + 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsπ : (0:ℝ) < Real.sqrt Real.pi := by positivity
  set κ : ℝ := Real.sin (2 * δ / 3) with hκdef
  have hκ : 0 < κ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  refine ⟨(2 / Real.sqrt Real.pi) * (Nat.factorial (n + 2 * N) : ℝ)
      / ((Nat.factorial n : ℝ) * (2 * κ) ^ (n + 2 * N + 1)), by positivity, ?_⟩
  intro z hz hsec
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨hθabs, hwre, hbre0⟩ := FLMF.Methods.SectorPoincare.sector_rotation_bounds hδ hδ' hz hsec
  set θ : ℝ := -Complex.arg z / 3 with hθdef
  set ω : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hωdef
  have hθ : |θ| < Real.pi / 4 := by
    have := hθabs
    linarith [this]
  have hωn : ‖ω‖ = 1 := by rw [hωdef]; exact Complex.norm_exp_ofReal_mul_I θ
  have hωne : ω ≠ 0 := by
    intro h; rw [h] at hωn; simp at hωn
  set c : ℂ := 2 * (z * ω) with hcdef
  set b : ℂ := ω ^ 2 with hbdef
  have hcre : c.re = 2 * (z * ω).re := by rw [hcdef]; simp [Complex.mul_re]
  have hcpos : 0 < c.re := by
    rw [hcre]
    have : 0 < κ * ‖z‖ := by positivity
    linarith [hwre]
  have hbn : ‖b‖ ≤ 1 := by rw [hbdef, norm_pow, hωn, one_pow]
  have hbre : 0 ≤ b.re := hbre0
  set Iint : ℂ := ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ n *
      (Complex.exp (-(c * (s : ℂ))) * Complex.exp (-b * (s : ℂ) ^ 2)) with hIdef
  set S : ℂ := ∑ j ∈ Finset.range N, ((-b) ^ j / (Nat.factorial j : ℂ))
      * ((Nat.factorial (n + 2 * j) : ℂ) / c ^ (n + 2 * j + 1)) with hSdef
  have hwatson : ‖Iint - S‖ ≤ (Nat.factorial (n + 2 * N) : ℝ) / c.re ^ (n + 2 * N + 1) :=
    FLMF.Methods.SectorPoincare.norm_gaussLaplace_moment_sub_taylor_le hcpos hbre hbn n N
  -- the rotated representation, with the Gaussian factor split off
  have hrep : cRepErfc n z
      = (2 / Real.sqrt Real.pi : ℂ) * ω ^ (n + 1) * Complex.exp (-z ^ 2)
          / (Nat.factorial n : ℂ) * Iint := by
    rw [← rotRep_eq_cRepErfc hθ z n, rotRep, rotMoment_eq_gaussLaplace, ← hcdef, ← hbdef,
      ← hIdef]
    ring
  -- the truncation, in the same form
  have hsπc : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hzc : (z : ℂ) ≠ 0 := hz
  have hfn : ((Nat.factorial n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have htrunc : ctruncRepErfc n N z
      = (2 / Real.sqrt Real.pi : ℂ) * ω ^ (n + 1) * Complex.exp (-z ^ 2)
          / (Nat.factorial n : ℂ) * S := by
    rw [ctruncRepErfc, hSdef, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfj : ((Nat.factorial j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hbj : (-b) ^ j = (-1 : ℂ) ^ j * ω ^ (2 * j) := by
      rw [hbdef, neg_pow, ← pow_mul]
    have hcj : c ^ (n + 2 * j + 1) = (2 * z) ^ (n + 2 * j + 1) * ω ^ (n + 2 * j + 1) := by
      rw [hcdef, show (2 : ℂ) * (z * ω) = (2 * z) * ω by ring, mul_pow]
    have hfac : ((2 * j + n).factorial : ℂ) = ((n + 2 * j).factorial : ℂ) := by
      rw [show 2 * j + n = n + 2 * j by omega]
    rw [hbj, hcj, hfac]
    field_simp
    ring
  have hdiff : cRepErfc n z - ctruncRepErfc n N z
      = (2 / Real.sqrt Real.pi : ℂ) * ω ^ (n + 1) * Complex.exp (-z ^ 2)
          / (Nat.factorial n : ℂ) * (Iint - S) := by
    rw [hrep, htrunc]; ring
  have hnormcoef : ‖(2 / Real.sqrt Real.pi : ℂ) * ω ^ (n + 1) * Complex.exp (-z ^ 2)
      / (Nat.factorial n : ℂ)‖
      = (2 / Real.sqrt Real.pi) * ‖Complex.exp (-z ^ 2)‖ / (Nat.factorial n : ℝ) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, hωn, one_pow, mul_one,
      Complex.norm_natCast, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsπ]
    simp
  calc ‖cRepErfc n z - ctruncRepErfc n N z‖
      = (2 / Real.sqrt Real.pi) * ‖Complex.exp (-z ^ 2)‖ / (Nat.factorial n : ℝ)
          * ‖Iint - S‖ := by rw [hdiff, norm_mul, hnormcoef]
    _ ≤ (2 / Real.sqrt Real.pi) * ‖Complex.exp (-z ^ 2)‖ / (Nat.factorial n : ℝ)
          * ((Nat.factorial (n + 2 * N) : ℝ) / c.re ^ (n + 2 * N + 1)) :=
        mul_le_mul_of_nonneg_left hwatson (by positivity)
    _ ≤ (2 / Real.sqrt Real.pi) * ‖Complex.exp (-z ^ 2)‖ / (Nat.factorial n : ℝ)
          * ((Nat.factorial (n + 2 * N) : ℝ) / (2 * (κ * ‖z‖)) ^ (n + 2 * N + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        rw [hcre]
        linarith [hwre]
    _ = (2 / Real.sqrt Real.pi) * (Nat.factorial (n + 2 * N) : ℝ)
          / ((Nat.factorial n : ℝ) * (2 * κ) ^ (n + 2 * N + 1))
          * ‖Complex.exp (-z ^ 2)‖ / ‖z‖ ^ (n + 2 * N + 1) := by
        rw [show (2 * (κ * ‖z‖)) ^ (n + 2 * N + 1)
            = (2 * κ) ^ (n + 2 * N + 1) * ‖z‖ ^ (n + 2 * N + 1) by
          rw [← mul_pow]; ring_nf]
        have hfnr : ((Nat.factorial n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        have h1 : ((2 * κ) ^ (n + 2 * N + 1) : ℝ) ≠ 0 := by positivity
        have h2 : (‖z‖ ^ (n + 2 * N + 1) : ℝ) ≠ 0 := by positivity
        field_simp

/-! ## Part III — DLMF 7.12.2 and 7.12.3 on the sector `|ph z| ≤ ½π − δ` -/

-- no-dlmf: closed form of the half-integer Pochhammer symbol; proof infrastructure
/-- `(½)_k = (2k)!/(4ᵏ k!)` — the coefficient appearing in the `erfc` expansion
(DLMF 7.12.1) is the `pochHalf` of the Fresnel expansions (DLMF 7.12.2/7.12.3). -/
private theorem pochHalf_eq_factorial (k : ℕ) :
    pochHalf k = (Nat.factorial (2 * k) : ℝ) / (4 ^ k * (Nat.factorial k : ℝ)) := by
  induction k with
  | zero =>
    have hΓ : Real.Gamma (2⁻¹ : ℝ) ≠ 0 := by
      rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num, Real.Gamma_one_half_eq]; positivity
    simp [pochHalf, hΓ]
  | succ m ih =>
    have hpos : (0:ℝ) < 1 / 2 + (m : ℝ) := by positivity
    have hstep : Real.Gamma (1 / 2 + ((m + 1 : ℕ) : ℝ))
        = (1 / 2 + (m : ℝ)) * Real.Gamma (1 / 2 + (m : ℝ)) := by
      rw [show (1 / 2 + ((m + 1 : ℕ) : ℝ)) = (1 / 2 + (m : ℝ)) + 1 by push_cast; ring]
      exact Real.Gamma_add_one (ne_of_gt hpos)
    have hrec : pochHalf (m + 1) = (1 / 2 + (m : ℝ)) * pochHalf m := by
      simp only [pochHalf]
      rw [hstep]
      ring
    have hfm : (0:ℝ) < (Nat.factorial m : ℝ) := by positivity
    have hfac : (Nat.factorial (2 * (m + 1)) : ℝ)
        = (2 * (m : ℝ) + 2) * ((2 * (m : ℝ) + 1) * (Nat.factorial (2 * m) : ℝ)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hrec, ih, hfac,
      show Nat.factorial (m + 1) = (m + 1) * Nat.factorial m from Nat.factorial_succ m]
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

-- no-dlmf: polar form of `1 ∓ i`; proof infrastructure for the sector transport
private theorem one_sub_I_polar :
    ((Real.sqrt 2 : ℝ) : ℂ) * (Complex.cos ((-(Real.pi / 4) : ℝ) : ℂ)
        + Complex.sin ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) = 1 - Complex.I := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  linear_combination (1 / 2 - Complex.I / 2) * h2

-- no-dlmf: polar form of `1 ± i`; proof infrastructure for the sector transport
private theorem one_add_I_polar :
    ((Real.sqrt 2 : ℝ) : ℂ) * (Complex.cos (((Real.pi / 4) : ℝ) : ℂ)
        + Complex.sin (((Real.pi / 4) : ℝ) : ℂ) * Complex.I) = 1 + Complex.I := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  linear_combination (1 / 2 + Complex.I / 2) * h2

-- no-dlmf: `arg (1 − i) = −π/4`; proof infrastructure
private theorem arg_one_sub_I : Complex.arg (1 - Complex.I) = -(Real.pi / 4) := by
  have hπ := Real.pi_pos
  have hr : (0:ℝ) < Real.sqrt 2 := by positivity
  have hmem : -(Real.pi / 4) ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have h := Complex.arg_mul_cos_add_sin_mul_I hr hmem
  rwa [one_sub_I_polar] at h

-- no-dlmf: `arg (1 + i) = π/4`; proof infrastructure
private theorem arg_one_add_I : Complex.arg (1 + Complex.I) = Real.pi / 4 := by
  have hπ := Real.pi_pos
  have hr : (0:ℝ) < Real.sqrt 2 := by positivity
  have hmem : (Real.pi / 4) ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, by linarith⟩
  have h := Complex.arg_mul_cos_add_sin_mul_I hr hmem
  rwa [one_add_I_polar] at h

-- no-dlmf: `‖1 ∓ i‖ = √2`; proof infrastructure
private theorem norm_one_sub_I : ‖(1 - Complex.I : ℂ)‖ = Real.sqrt 2 := by
  rw [← one_sub_I_polar, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

-- no-dlmf: `‖1 ± i‖ = √2`; proof infrastructure
private theorem norm_one_add_I : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
  rw [← one_add_I_polar, norm_mul, Complex.norm_cos_add_sin_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

-- no-dlmf: pairing of a `2N`-term sum; proof infrastructure
private theorem sum_range_two_mul (a : ℕ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), a j = ∑ m ∈ Finset.range N, (a (2 * m) + a (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

-- no-dlmf: the finite algebraic identity behind the 7.12.2/7.12.3 transport
/-- **Parity split of the `erfc` truncation on the two Fresnel branches.**  With
`ζ± = ½√π(1∓i)z`, writing `X` (resp. `Y`) for the `½(1+i)/√π` (resp. `½(1−i)/√π`) multiple
of the `2N`-term DLMF 7.12.1 truncation at `ζ₊` (resp. `ζ₋`),
`X − Y = 2i·(f-truncation)` and `X + Y = 2·(g-truncation)`:
the odd-index terms cancel in the first combination and the even-index terms in the
second, which is exactly how a series in `ζ^{−(2j+1)}` becomes DLMF's series in
`(πz²/2)^{−2m}` resp. `(πz²/2)^{−(2m+1)}`. -/
private theorem fresnel_trunc_identity (N : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (((1 / 2) * (1 + Complex.I) / (Real.sqrt Real.pi : ℂ)) *
        ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z) ^ (2 * j + 1))
      - (((1 / 2) * (1 - Complex.I) / (Real.sqrt Real.pi : ℂ)) *
        ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ^ (2 * j + 1))
      = 2 * Complex.I * ctruncF N z
    ∧ (((1 / 2) * (1 + Complex.I) / (Real.sqrt Real.pi : ℂ)) *
        ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z) ^ (2 * j + 1))
      + (((1 / 2) * (1 - Complex.I) / (Real.sqrt Real.pi : ℂ)) *
        ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ^ (2 * j + 1))
      = 2 * ctruncG N z := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set r : ℂ := (Real.sqrt Real.pi : ℂ) with hrdef
  have hr : r ≠ 0 := by rw [hrdef]; simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hrr : r * r = (Real.pi : ℂ) := by
    rw [hrdef]; norm_cast; exact Real.mul_self_sqrt hπ.le
  have hπc : (Real.pi : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  set ζp : ℂ := (1 / 2) * r * (1 - Complex.I) * z with hζpdef
  set ζm : ℂ := (1 / 2) * r * (1 + Complex.I) * z with hζmdef
  set u : ℂ := (Real.pi : ℂ) * z ^ 2 / 2 with hudef
  have hu : u ≠ 0 := by rw [hudef]; simp [hπc, hz]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hnI2 : (-Complex.I) ^ 2 = -1 := by rw [neg_pow]; simp [hI2]
  have hζp2 : ζp ^ 2 = -Complex.I * u := by
    rw [hζpdef, hudef]
    linear_combination (z ^ 2 / 4 * (1 - Complex.I) ^ 2) * hrr
      + ((Real.pi : ℂ) * z ^ 2 / 4) * hI2
  have hζm2 : ζm ^ 2 = Complex.I * u := by
    rw [hζmdef, hudef]
    linear_combination (z ^ 2 / 4 * (1 + Complex.I) ^ 2) * hrr
      + ((Real.pi : ℂ) * z ^ 2 / 4) * hI2
  have hζpne : ζp ≠ 0 := by
    rw [hζpdef]
    have h1 : (1 - Complex.I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    exact by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨by norm_num, hr⟩, h1⟩, hz⟩
  have hζmne : ζm ≠ 0 := by
    rw [hζmdef]
    have h1 : (1 + Complex.I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    exact by
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨⟨⟨by norm_num, hr⟩, h1⟩, hz⟩
  have hrζp : r * ζp ≠ 0 := mul_ne_zero hr hζpne
  have hrζm : r * ζm ≠ 0 := mul_ne_zero hr hζmne
  have hπz : (Real.pi : ℂ) * z ≠ 0 := mul_ne_zero hπc hz
  have hkeyp : (1 / 2) * (1 + Complex.I) / (r * ζp) = Complex.I / ((Real.pi : ℂ) * z) := by
    rw [div_eq_div_iff hrζp hπz, hζpdef]
    linear_combination (-(1 / 2) * Complex.I * (1 - Complex.I) * z) * hrr
      + ((Real.pi : ℂ) * z / 2) * hI2
  have hkeym : (1 / 2) * (1 - Complex.I) / (r * ζm) = -Complex.I / ((Real.pi : ℂ) * z) := by
    rw [div_eq_div_iff hrζm hπz, hζmdef]
    linear_combination ((1 / 2) * Complex.I * (1 + Complex.I) * z) * hrr
      + ((Real.pi : ℂ) * z / 2) * hI2
  -- per-term transport
  have hXterm : ∀ j : ℕ,
      ((1 / 2) * (1 + Complex.I) / r) * ((-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
          / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / ζp ^ (2 * j + 1))
      = (Complex.I / ((Real.pi : ℂ) * z)) *
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * (-Complex.I) ^ j / u ^ j) := by
    intro j
    have hw : ((-Complex.I) ^ j) * ((-Complex.I) ^ j) = (-1 : ℂ) ^ j := by
      rw [← pow_add, ← two_mul, pow_mul, hnI2]
    have hwne : ((-Complex.I) ^ j) ≠ 0 := pow_ne_zero _ (by simp)
    have hune : u ^ j ≠ 0 := pow_ne_zero _ hu
    have hfj : ((Nat.factorial j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h4 : ((4 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpow : ζp ^ (2 * j + 1) = ((-Complex.I) ^ j * u ^ j) * ζp := by
      rw [pow_succ, pow_mul, hζp2, mul_pow]
    rw [hpow, ← hw]
    rw [show ((1 / 2) * (1 + Complex.I) / r) *
          (((-Complex.I) ^ j * (-Complex.I) ^ j) * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / (((-Complex.I) ^ j * u ^ j) * ζp))
        = ((1 / 2) * (1 + Complex.I) / (r * ζp)) *
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * (-Complex.I) ^ j / u ^ j) by field_simp]
    rw [hkeyp]
  have hYterm : ∀ j : ℕ,
      ((1 / 2) * (1 - Complex.I) / r) * ((-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
          / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / ζm ^ (2 * j + 1))
      = (-Complex.I / ((Real.pi : ℂ) * z)) *
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * Complex.I ^ j / u ^ j) := by
    intro j
    have hw : (Complex.I ^ j) * (Complex.I ^ j) = (-1 : ℂ) ^ j := by
      rw [← pow_add, ← two_mul, pow_mul, hI2]
    have hwne : (Complex.I ^ j) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    have hune : u ^ j ≠ 0 := pow_ne_zero _ hu
    have hfj : ((Nat.factorial j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h4 : ((4 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpow : ζm ^ (2 * j + 1) = ((Complex.I ^ j) * u ^ j) * ζm := by
      rw [pow_succ, pow_mul, hζm2, mul_pow]
    rw [hpow, ← hw]
    rw [show ((1 / 2) * (1 - Complex.I) / r) *
          ((Complex.I ^ j * Complex.I ^ j) * (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            / ((Complex.I ^ j * u ^ j) * ζm))
        = ((1 / 2) * (1 - Complex.I) / (r * ζm)) *
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * Complex.I ^ j / u ^ j) by field_simp]
    rw [hkeym]
  -- the coefficient is `(½)_j`
  have hcast : ∀ k : ℕ, (Nat.factorial (2 * k) : ℂ) / ((4 : ℂ) ^ k * (Nat.factorial k : ℂ))
      = ((pochHalf k : ℝ) : ℂ) := by
    intro k
    rw [pochHalf_eq_factorial]
    push_cast
    ring
  -- the two parity combinations
  have hpairF : ∀ m : ℕ,
      ((Nat.factorial (2 * (2 * m)) : ℂ) / ((4 : ℂ) ^ (2 * m) * (Nat.factorial (2 * m) : ℂ))
          * (-Complex.I) ^ (2 * m) / u ^ (2 * m)
        + (Nat.factorial (2 * (2 * m)) : ℂ) / ((4 : ℂ) ^ (2 * m) * (Nat.factorial (2 * m) : ℂ))
          * Complex.I ^ (2 * m) / u ^ (2 * m))
      + ((Nat.factorial (2 * (2 * m + 1)) : ℂ)
            / ((4 : ℂ) ^ (2 * m + 1) * (Nat.factorial (2 * m + 1) : ℂ))
          * (-Complex.I) ^ (2 * m + 1) / u ^ (2 * m + 1)
        + (Nat.factorial (2 * (2 * m + 1)) : ℂ)
            / ((4 : ℂ) ^ (2 * m + 1) * (Nat.factorial (2 * m + 1) : ℂ))
          * Complex.I ^ (2 * m + 1) / u ^ (2 * m + 1))
      = 2 * ((-1 : ℂ) ^ m * ((pochHalf (2 * m) : ℝ) : ℂ) / u ^ (2 * m)) := by
    intro m
    rw [hcast (2 * m), hcast (2 * m + 1)]
    rw [show (-Complex.I) ^ (2 * m) = (-1 : ℂ) ^ m by rw [pow_mul, hnI2],
      show Complex.I ^ (2 * m) = (-1 : ℂ) ^ m by rw [pow_mul, hI2],
      show (-Complex.I) ^ (2 * m + 1) = (-1 : ℂ) ^ m * (-Complex.I) by
        rw [pow_succ, pow_mul, hnI2],
      show Complex.I ^ (2 * m + 1) = (-1 : ℂ) ^ m * Complex.I by rw [pow_succ, pow_mul, hI2]]
    ring
  have hpairG : ∀ m : ℕ,
      ((Nat.factorial (2 * (2 * m)) : ℂ) / ((4 : ℂ) ^ (2 * m) * (Nat.factorial (2 * m) : ℂ))
          * (-Complex.I) ^ (2 * m) / u ^ (2 * m)
        - (Nat.factorial (2 * (2 * m)) : ℂ) / ((4 : ℂ) ^ (2 * m) * (Nat.factorial (2 * m) : ℂ))
          * Complex.I ^ (2 * m) / u ^ (2 * m))
      + ((Nat.factorial (2 * (2 * m + 1)) : ℂ)
            / ((4 : ℂ) ^ (2 * m + 1) * (Nat.factorial (2 * m + 1) : ℂ))
          * (-Complex.I) ^ (2 * m + 1) / u ^ (2 * m + 1)
        - (Nat.factorial (2 * (2 * m + 1)) : ℂ)
            / ((4 : ℂ) ^ (2 * m + 1) * (Nat.factorial (2 * m + 1) : ℂ))
          * Complex.I ^ (2 * m + 1) / u ^ (2 * m + 1))
      = (-2 * Complex.I) * ((-1 : ℂ) ^ m * ((pochHalf (2 * m + 1) : ℝ) : ℂ) / u ^ (2 * m + 1)) := by
    intro m
    rw [hcast (2 * m), hcast (2 * m + 1)]
    rw [show (-Complex.I) ^ (2 * m) = (-1 : ℂ) ^ m by rw [pow_mul, hnI2],
      show Complex.I ^ (2 * m) = (-1 : ℂ) ^ m by rw [pow_mul, hI2],
      show (-Complex.I) ^ (2 * m + 1) = (-1 : ℂ) ^ m * (-Complex.I) by
        rw [pow_succ, pow_mul, hnI2],
      show Complex.I ^ (2 * m + 1) = (-1 : ℂ) ^ m * Complex.I by rw [pow_succ, pow_mul, hI2]]
    ring
  constructor
  · -- `X − Y = 2i · ctruncF N z`
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (2 * N)) => hXterm j),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (2 * N)) => hYterm j),
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hsum : (∑ j ∈ Finset.range (2 * N),
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * (-Complex.I) ^ j / u ^ j))
        + (∑ j ∈ Finset.range (2 * N),
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * Complex.I ^ j / u ^ j))
        = 2 * ∑ m ∈ Finset.range N,
            ((-1 : ℂ) ^ m * ((pochHalf (2 * m) : ℝ) : ℂ) / u ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib,
        sum_range_two_mul (fun j => (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) * (-Complex.I) ^ j / u ^ j
          + (Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * Complex.I ^ j / u ^ j) N,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => hpairF m
    rw [ctruncF, ← hudef]
    rw [show Complex.I / ((Real.pi : ℂ) * z) *
          ∑ j ∈ Finset.range (2 * N),
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * (-Complex.I) ^ j / u ^ j)
        - -Complex.I / ((Real.pi : ℂ) * z) *
          ∑ j ∈ Finset.range (2 * N),
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * Complex.I ^ j / u ^ j)
        = Complex.I / ((Real.pi : ℂ) * z) *
            ((∑ j ∈ Finset.range (2 * N),
              ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
                * (-Complex.I) ^ j / u ^ j))
            + (∑ j ∈ Finset.range (2 * N),
              ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
                * Complex.I ^ j / u ^ j))) by ring]
    rw [hsum]
    field_simp
  · -- `X + Y = 2 · ctruncG N z`
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (2 * N)) => hXterm j),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (2 * N)) => hYterm j),
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hsum : (∑ j ∈ Finset.range (2 * N),
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * (-Complex.I) ^ j / u ^ j))
        - (∑ j ∈ Finset.range (2 * N),
          ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * Complex.I ^ j / u ^ j))
        = (-2 * Complex.I) * ∑ m ∈ Finset.range N,
            ((-1 : ℂ) ^ m * ((pochHalf (2 * m + 1) : ℝ) : ℂ) / u ^ (2 * m + 1)) := by
      rw [← Finset.sum_sub_distrib,
        sum_range_two_mul (fun j => (Nat.factorial (2 * j) : ℂ)
            / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) * (-Complex.I) ^ j / u ^ j
          - (Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
            * Complex.I ^ j / u ^ j) N,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => hpairG m
    rw [ctruncG, ← hudef]
    rw [show Complex.I / ((Real.pi : ℂ) * z) *
          ∑ j ∈ Finset.range (2 * N),
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * (-Complex.I) ^ j / u ^ j)
        + -Complex.I / ((Real.pi : ℂ) * z) *
          ∑ j ∈ Finset.range (2 * N),
            ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
              * Complex.I ^ j / u ^ j)
        = Complex.I / ((Real.pi : ℂ) * z) *
            ((∑ j ∈ Finset.range (2 * N),
              ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
                * (-Complex.I) ^ j / u ^ j))
            - (∑ j ∈ Finset.range (2 * N),
              ((Nat.factorial (2 * j) : ℂ) / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ))
                * Complex.I ^ j / u ^ j))) by ring]
    rw [hsum]
    field_simp
    linear_combination (-(∑ m ∈ Finset.range N,
        ((-1 : ℂ) ^ m * ((pochHalf (2 * m + 1) : ℝ) : ℂ) / u ^ (2 * m + 1)))) * hI2

-- no-dlmf: the ±π/4 argument rotation carrying the ½π−δ sector of `z` into the
-- ¾π−δ sector of `ζ±`; proof infrastructure
private theorem arg_fresnelZeta_le {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0)
    (hsec : |Complex.arg z| ≤ Real.pi / 2 - δ) :
    |Complex.arg ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z)|
        ≤ 3 * Real.pi / 4 - δ
    ∧ |Complex.arg ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z)|
        ≤ 3 * Real.pi / 4 - δ := by
  have hπ := Real.pi_pos
  have hrpos : (0:ℝ) < Real.sqrt Real.pi / 2 := by positivity
  have hargz := abs_le.mp hsec
  have hIm : (1 - Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hIp : (1 + Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  constructor
  · have hfold : (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z
        = ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * ((1 - Complex.I) * z) := by push_cast; ring
    rw [hfold, Complex.arg_real_mul _ hrpos]
    rw [Complex.arg_mul hIm hz (by rw [arg_one_sub_I]; constructor <;> [linarith; linarith]),
      arg_one_sub_I]
    rw [abs_le]
    constructor <;> linarith [hargz.1, hargz.2]
  · have hfold : (1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z
        = ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) * ((1 + Complex.I) * z) := by push_cast; ring
    rw [hfold, Complex.arg_real_mul _ hrpos]
    rw [Complex.arg_mul hIp hz (by rw [arg_one_add_I]; constructor <;> [linarith; linarith]),
      arg_one_add_I]
    rw [abs_le]
    constructor <;> linarith [hargz.1, hargz.2]

-- no-dlmf: modulus of the rotated Fresnel argument; proof infrastructure
private theorem norm_fresnelZeta (z : ℂ) :
    ‖(1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z‖
        = (Real.sqrt Real.pi * Real.sqrt 2 / 2) * ‖z‖
    ∧ ‖(1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z‖
        = (Real.sqrt Real.pi * Real.sqrt 2 / 2) * ‖z‖ := by
  have hp : (0:ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  constructor
  · rw [norm_mul, norm_mul, norm_mul, norm_one_sub_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp]
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    ring
  · rw [norm_mul, norm_mul, norm_mul, norm_one_add_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp]
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    ring

-- no-dlmf: the shared sector estimate behind `erf_7_12_2_sector` / `erf_7_12_3_sector`
/-- The two Fresnel-auxiliary sector remainder bounds, obtained from
`FLMF.Error.cerfc_poincare_bound` at truncation order `2N` on the branches `ζ± = ½√π(1∓i)z`
and the parity split `fresnel_trunc_identity`. -/
private theorem fresnel_sector_core (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi / 2)
    {z : ℂ} (hz : z ≠ 0) (hsec : |Complex.arg z| ≤ Real.pi / 2 - δ) :
    ‖FLMF.Fresnel.cfresnelAuxF z - ctruncF N z‖
        ≤ (Real.sqrt 2 * (Nat.factorial (2 * (2 * N)) : ℝ)
            / (Real.sqrt Real.pi * (2 * (Real.sin (2 * δ / 3)
                * (Real.sqrt Real.pi * Real.sqrt 2 / 2))) ^ (2 * (2 * N) + 1)))
          / ‖z‖ ^ (2 * (2 * N) + 1)
    ∧ ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG N z‖
        ≤ (Real.sqrt 2 * (Nat.factorial (2 * (2 * N)) : ℝ)
            / (Real.sqrt Real.pi * (2 * (Real.sin (2 * δ / 3)
                * (Real.sqrt Real.pi * Real.sqrt 2 / 2))) ^ (2 * (2 * N) + 1)))
          / ‖z‖ ^ (2 * (2 * N) + 1) := by
  have hπ := Real.pi_pos
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hδ3 : δ < 3 * Real.pi / 4 := by linarith
  -- all the external inputs, *before* abbreviating (so the abbreviations fold them)
  obtain ⟨hidF, hidG⟩ := fresnel_trunc_identity N hz
  obtain ⟨hargp, hargm⟩ := arg_fresnelZeta_le hδ hz hsec
  obtain ⟨hnp, hnm⟩ := norm_fresnelZeta z
  have hζpne : ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 - Complex.I) * z) ≠ 0 := by
    rw [← norm_pos_iff, hnp]; positivity
  have hζmne : ((1 / 2) * (Real.sqrt Real.pi : ℂ) * (1 + Complex.I) * z) ≠ 0 := by
    rw [← norm_pos_iff, hnm]; positivity
  have hBp0 := cerfc_poincare_bound hδ hδ3 hζpne hargp (2 * N)
  have hBm0 := cerfc_poincare_bound hδ hδ3 hζmne hargm (2 * N)
  rw [hnp] at hBp0
  rw [hnm] at hBm0
  have h75 := FLMF.Fresnel.cfresnel_7_5_10 z
  -- abbreviations
  set κ : ℝ := Real.sin (2 * δ / 3) with hκdef
  have hκ : 0 < κ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set ρ : ℝ := Real.sqrt Real.pi * Real.sqrt 2 / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  set r : ℂ := (Real.sqrt Real.pi : ℂ) with hrdef
  have hr : r ≠ 0 := by rw [hrdef]; simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  set ζp : ℂ := (1 / 2) * r * (1 - Complex.I) * z with hζpdef
  set ζm : ℂ := (1 / 2) * r * (1 + Complex.I) * z with hζmdef
  set P : ℂ := (1 / 2) * (1 + Complex.I) / r with hPdef
  set Q : ℂ := (1 / 2) * (1 - Complex.I) / r with hQdef
  set Ap : ℂ := r * Complex.exp (ζp ^ 2) * cerfc ζp with hApdef
  set Am : ℂ := r * Complex.exp (ζm ^ 2) * cerfc ζm with hAmdef
  set Tp : ℂ := ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
      / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / ζp ^ (2 * j + 1) with hTpdef
  set Tm : ℂ := ∑ j ∈ Finset.range (2 * N), (-1 : ℂ) ^ j * (Nat.factorial (2 * j) : ℂ)
      / ((4 : ℂ) ^ j * (Nat.factorial j : ℂ)) / ζm ^ (2 * j + 1) with hTmdef
  clear_value Tp Tm Ap Am P Q ζp ζm r ρ κ
  have hBp : ‖Ap - Tp‖
      ≤ 2 * (Nat.factorial (2 * (2 * N)) : ℝ) / (2 * (κ * (ρ * ‖z‖))) ^ (2 * (2 * N) + 1) :=
    hBp0
  have hBm : ‖Am - Tm‖
      ≤ 2 * (Nat.factorial (2 * (2 * N)) : ℝ) / (2 * (κ * (ρ * ‖z‖))) ^ (2 * (2 * N) + 1) :=
    hBm0
  -- DLMF 7.5.10 in the `P`/`Q` normalisation
  have hA1 : P * Ap = FLMF.Fresnel.cfresnelAuxG z + Complex.I * FLMF.Fresnel.cfresnelAuxF z := by
    rw [h75.1, hPdef, hApdef]
    field_simp
  have hA2 : Q * Am = FLMF.Fresnel.cfresnelAuxG z - Complex.I * FLMF.Fresnel.cfresnelAuxF z := by
    rw [h75.2, hQdef, hAmdef]
    field_simp
  -- the norms of the two branch weights
  have hPn : ‖P‖ = Real.sqrt 2 / (2 * Real.sqrt Real.pi) := by
    rw [hPdef, norm_div, norm_mul, norm_one_add_I, hrdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    ring
  have hQn : ‖Q‖ = Real.sqrt 2 / (2 * Real.sqrt Real.pi) := by
    rw [hQdef, norm_div, norm_mul, norm_one_sub_I, hrdef, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    ring
  set B : ℝ := 2 * (Nat.factorial (2 * (2 * N)) : ℝ)
      / (2 * (κ * (ρ * ‖z‖))) ^ (2 * (2 * N) + 1) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hfinal : Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B
      = (Real.sqrt 2 * (Nat.factorial (2 * (2 * N)) : ℝ)
          / (Real.sqrt Real.pi * (2 * (κ * ρ)) ^ (2 * (2 * N) + 1)))
        / ‖z‖ ^ (2 * (2 * N) + 1) := by
    rw [hBdef, show (2 * (κ * (ρ * ‖z‖))) ^ (2 * (2 * N) + 1)
        = (2 * (κ * ρ)) ^ (2 * (2 * N) + 1) * ‖z‖ ^ (2 * (2 * N) + 1) by
      rw [← mul_pow]; ring_nf]
    have h1 : Real.sqrt Real.pi ≠ 0 := by positivity
    have h2 : ((2 * (κ * ρ)) ^ (2 * (2 * N) + 1) : ℝ) ≠ 0 := by positivity
    have h3 : (‖z‖ ^ (2 * (2 * N) + 1) : ℝ) ≠ 0 := by positivity
    field_simp
  constructor
  · -- DLMF 7.12.2
    have hdiff : FLMF.Fresnel.cfresnelAuxF z - ctruncF N z
        = (-Complex.I / 2) * (P * (Ap - Tp) - Q * (Am - Tm)) := by
      linear_combination (Complex.I / 2) * hA1 + (-Complex.I / 2) * hA2
        + (-Complex.I / 2) * hidF
        + (FLMF.Fresnel.cfresnelAuxF z - ctruncF N z) * hI2
    rw [← hfinal]
    calc ‖FLMF.Fresnel.cfresnelAuxF z - ctruncF N z‖
        = (1 / 2) * ‖P * (Ap - Tp) - Q * (Am - Tm)‖ := by
          rw [hdiff, norm_mul, show ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 by
            rw [norm_div, norm_neg, Complex.norm_I]; norm_num]
      _ ≤ (1 / 2) * (‖P‖ * ‖Ap - Tp‖ + ‖Q‖ * ‖Am - Tm‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc ‖P * (Ap - Tp) - Q * (Am - Tm)‖
              ≤ ‖P * (Ap - Tp)‖ + ‖Q * (Am - Tm)‖ := norm_sub_le _ _
            _ = ‖P‖ * ‖Ap - Tp‖ + ‖Q‖ * ‖Am - Tm‖ := by rw [norm_mul, norm_mul]
      _ ≤ (1 / 2) * (Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B
            + Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
          · rw [hPn]; exact mul_le_mul_of_nonneg_left hBp (by positivity)
          · rw [hQn]; exact mul_le_mul_of_nonneg_left hBm (by positivity)
      _ = Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B := by ring
  · -- DLMF 7.12.3
    have hdiff : FLMF.Fresnel.cfresnelAuxG z - ctruncG N z
        = (1 / 2 : ℂ) * (P * (Ap - Tp) + Q * (Am - Tm)) := by
      linear_combination (-1 / 2 : ℂ) * hA1 + (-1 / 2 : ℂ) * hA2 + (1 / 2 : ℂ) * hidG
    rw [← hfinal]
    calc ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG N z‖
        = (1 / 2) * ‖P * (Ap - Tp) + Q * (Am - Tm)‖ := by
          rw [hdiff, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      _ ≤ (1 / 2) * (‖P‖ * ‖Ap - Tp‖ + ‖Q‖ * ‖Am - Tm‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc ‖P * (Ap - Tp) + Q * (Am - Tm)‖
              ≤ ‖P * (Ap - Tp)‖ + ‖Q * (Am - Tm)‖ := norm_add_le _ _
            _ = ‖P‖ * ‖Ap - Tp‖ + ‖Q‖ * ‖Am - Tm‖ := by rw [norm_mul, norm_mul]
      _ ≤ (1 / 2) * (Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B
            + Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
          · rw [hPn]; exact mul_le_mul_of_nonneg_left hBp (by positivity)
          · rw [hQn]; exact mul_le_mul_of_nonneg_left hBm (by positivity)
      _ = Real.sqrt 2 / (2 * Real.sqrt Real.pi) * B := by ring

-- no-dlmf: positivity of the explicit constant; proof infrastructure
private theorem fresnel_const_pos (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi / 2) :
    0 < Real.sqrt 2 * (Nat.factorial (4 * N) : ℝ)
      / (Real.sqrt Real.pi * (2 * (Real.sin (2 * δ / 3)
          * (Real.sqrt Real.pi * Real.sqrt 2 / 2))) ^ (4 * N + 1)) := by
  have hπ := Real.pi_pos
  have hκ : 0 < Real.sin (2 * δ / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hρ : (0:ℝ) < Real.sqrt Real.pi * Real.sqrt 2 / 2 := by positivity
  have hbase : (0:ℝ) < 2 * (Real.sin (2 * δ / 3) * (Real.sqrt Real.pi * Real.sqrt 2 / 2)) :=
    mul_pos (by norm_num) (mul_pos hκ hρ)
  exact div_pos (by positivity) (mul_pos (by positivity) (pow_pos hbase _))

-- no-dlmf: global-in-`z` sector bound, the engine behind the tagged
-- `erf_7_12_2_sector` below (which restricts to the DLMF `z → ∞` regime
-- `1 ≤ ‖z‖`); support lemma
/-- The Poincaré remainder bound for the Fresnel auxiliary function `f`
(7.12.2), *uniform on the closed sector* `|ph z| ≤ ½π − δ` and global in
`z ≠ 0`: for every truncation order `N` and
every `δ ∈ (0, ½π)` there is a constant `C > 0` (independent of `z`) with

`‖f(z) − (1/(πz)) ∑_{m<N} (−1)ᵐ (½)_{2m}/(πz²/2)^{2m}‖ ≤ C/‖z‖^{4N+1}`

for all `z ≠ 0` with `|ph z| ≤ ½π − δ`.

Asserting the estimate for *every* `N` pins every coefficient of the expansion, and the
bound `O(z^{−(4N+1)})` is `o` of the last retained term `z^{−(4N−3)}`, so this is exactly
Poincaré's `∼` for the displayed series, on DLMF's sector.  The truncation is the
`ctruncF` of 7.12.4.

The proof transports the already-proven `erfc` sector bound `cerfc_poincare_bound` along
7.5.10 (`g ± i f = ½(1±i) e^{ζ∓²} erfc(ζ∓)`, `ζ± = ½√π(1∓i)z`): the argument
rotation by `∓π/4` carries `|ph z| ≤ ½π − δ` onto `|ph ζ±| ≤ ¾π − δ`, which is precisely
DLMF's `erfc` sector, and the odd-order terms of the two `erfc` series cancel in the
combination that produces `f`.  An admissible constant is
`C = √2·(4N)!/(√π·(2 sin(2δ/3)·√(π/2))^{4N+1})`. -/
theorem cfresnelAuxF_sector_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → |Complex.arg z| ≤ Real.pi / 2 - δ →
      ‖FLMF.Fresnel.cfresnelAuxF z - ctruncF N z‖ ≤ C / ‖z‖ ^ (4 * N + 1) := by
  refine ⟨Real.sqrt 2 * (Nat.factorial (4 * N) : ℝ)
      / (Real.sqrt Real.pi * (2 * (Real.sin (2 * δ / 3)
          * (Real.sqrt Real.pi * Real.sqrt 2 / 2))) ^ (4 * N + 1)),
    fresnel_const_pos N hδ hδ', ?_⟩
  intro z hz hsec
  have h := (fresnel_sector_core N hδ hδ' hz hsec).1
  rwa [show 2 * (2 * N) = 4 * N from by ring] at h

-- no-dlmf: global-in-`z` sector bound, the engine behind the tagged
-- `erf_7_12_3_sector` below (which restricts to the DLMF `z → ∞` regime
-- `1 ≤ ‖z‖` and carries the sharp first-neglected-term exponent); support
-- lemma
/-- The Poincaré remainder bound for the Fresnel auxiliary function `g`
(7.12.3), *uniform on the closed sector* `|ph z| ≤ ½π − δ` and global in
`z ≠ 0`: for every truncation order `N` and
every `δ ∈ (0, ½π)` there is a constant `C > 0` (independent of `z`) with

`‖g(z) − (1/(πz)) ∑_{m<N} (−1)ᵐ (½)_{2m+1}/(πz²/2)^{2m+1}‖ ≤ C/‖z‖^{4N+1}`

for all `z ≠ 0` with `|ph z| ≤ ½π − δ`.

As for 7.12.2 the estimate holds at *every* truncation order, which pins every coefficient
of the expansion; the truncation is the `ctruncG` of 7.12.5.  Here it is the
*even*-order terms of the two `erfc` series that cancel, leaving DLMF's odd-power series
in `(πz²/2)^{−(2m+1)}`.  An admissible constant is
`C = √2·(4N)!/(√π·(2 sin(2δ/3)·√(π/2))^{4N+1})`. -/
theorem cfresnelAuxG_sector_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → |Complex.arg z| ≤ Real.pi / 2 - δ →
      ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG N z‖ ≤ C / ‖z‖ ^ (4 * N + 1) := by
  refine ⟨Real.sqrt 2 * (Nat.factorial (4 * N) : ℝ)
      / (Real.sqrt Real.pi * (2 * (Real.sin (2 * δ / 3)
          * (Real.sqrt Real.pi * Real.sqrt 2 / 2))) ^ (4 * N + 1)),
    fresnel_const_pos N hδ hδ', ?_⟩
  intro z hz hsec
  have h := (fresnel_sector_core N hδ hδ' hz hsec).2
  rwa [show 2 * (2 * N) = 4 * N from by ring] at h

/-! ## Part IV — the tagged DLMF displays, in the `z → ∞` regime

DLMF asserts 7.12.2, 7.12.3 and 7.18.14 as Poincaré asymptotic expansions
(`∼`, §2.1(iii)): for each truncation order the remainder is of the order of
the first neglected term as `z → ∞` in the sector.  The global-in-`z` bounds
of Parts II–III restrict to that regime (`1 ≤ ‖z‖`); for `g` the restriction
also upgrades the exponent to the sharp first-neglected-term order `4N+3`,
by peeling one term off the `(N+1)`-order bound. -/

-- no-dlmf: `0 < (½)_m`; arithmetic support
private theorem pochHalf_pos (m : ℕ) : 0 < pochHalf m :=
  div_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by norm_num))

-- no-dlmf: nonvanishing from the `z → ∞` regime; arithmetic support
private theorem ne_zero_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) : z ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at hz
  linarith

/-- **DLMF 7.12.2** — the Poincaré asymptotic expansion of the Fresnel auxiliary function
`f` as `z → ∞` in the sector `|ph z| ≤ ½π − δ`: for every truncation order `N` and every
`δ ∈ (0, ½π)` there is a constant `C > 0` with

`‖f(z) − (1/(πz)) ∑_{m<N} (−1)ᵐ (½)_{2m}/(πz²/2)^{2m}‖ ≤ C/‖z‖^{4N+1}`

for all sufficiently large `‖z‖` (some threshold `R`) in the sector — the remainder
after `N+1` terms is of the order of the first neglected term
`(πz²/2)^{−2(N+1)}/(πz) ≍ z^{−(4(N+1)+1)}`, for every positive truncation order
`N+1` and every positive separation `δ` from the Stokes lines.  This is exactly
DLMF's `∼` (a Poincaré expansion, §2.1(iii): `f(x) = ∑_{s<n} a_s x^{−s} + O(x^{−n})`
for each positive integer `n`, as `x → ∞` in the set) for the displayed series on
DLMF's sector `|ph z| ≤ ½π − δ(<½π)`.  `f` is the auxiliary function of §7.2(iv)
(the entire extension `cfresnelAuxF`); the truncation is the `ctruncF` of 7.12.4.
(The underlying global bound `cfresnelAuxF_sector_bound` is in fact uniform down to
`R = 1` with an explicit constant.)

DLMF 7.12.2.
DAG: E-7.12.2.
Numerical: N/A
Verified: verified
-/
theorem erf_7_12_2_sector (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R C : ℝ, 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → |Complex.arg z| ≤ Real.pi / 2 - δ →
      ‖FLMF.Fresnel.cfresnelAuxF z - ctruncF (N + 1) z‖
        ≤ C / ‖z‖ ^ (4 * (N + 1) + 1) := by
  have hδ'0 : 0 < min δ (Real.pi / 4) := lt_min hδ (by positivity)
  have hδ'lt : min δ (Real.pi / 4) < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  obtain ⟨C, hC, h⟩ := cfresnelAuxF_sector_bound (N + 1) hδ'0 hδ'lt
  refine ⟨1, C, hC, fun z hz hsec => h z (ne_zero_of_one_le_norm hz) ?_⟩
  have := min_le_left δ (Real.pi / 4)
  linarith

/-- **DLMF 7.18.14** — the Poincaré asymptotic expansion of the repeated integrals of the
complementary error function as `z → ∞` in the sector `|ph z| ≤ ¾π − δ`: for every order
`n`, every truncation order `N` and every `δ ∈ (0, ¾π)` there is a constant `C > 0` with

`‖iⁿerfc(z) − (2/√π)(e^{−z²}/(2z)^{n+1}) ∑_{m<N} (−1)ᵐ(2m+n)!/(n! m! (2z)^{2m})‖
    ≤ C·‖e^{−z²}‖/‖z‖^{n+2N+1}`

for all sufficiently large `‖z‖` (some threshold `R`) in the sector — the remainder
after `N+1` terms is of the order of the first neglected term, for every positive
truncation order `N+1` and every positive separation `δ` from the Stokes lines.
This is exactly DLMF's `∼` (a Poincaré expansion, §2.1(iii): remainder `O` of the first
neglected term for each positive order, as `z → ∞` in the set) for the displayed series
on DLMF's sector `|ph z| ≤ ¾π − δ(<¾π)`.  `iⁿerfc` is the entire extension `cRepErfc`
(7.18.1/7.18.2); the truncation `ctruncRepErfc` matches the display term-by-term.
(The underlying global bound `cRepErfc_sector_bound` is in fact uniform down to
`R = 1` with an explicit constant.)

DLMF 7.18.14.
DAG: E-7.18.14.
Numerical: N/A
Verified: verified
-/
theorem erf_7_18_14_sector (n N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R C : ℝ, 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → |Complex.arg z| ≤ 3 * Real.pi / 4 - δ →
      ‖cRepErfc n z - ctruncRepErfc n (N + 1) z‖
        ≤ C * ‖Complex.exp (-z ^ 2)‖ / ‖z‖ ^ (n + 2 * (N + 1) + 1) := by
  have hδ'0 : 0 < min δ (Real.pi / 2) := lt_min hδ (by positivity)
  have hδ'lt : min δ (Real.pi / 2) < 3 * Real.pi / 4 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  obtain ⟨C, hC, h⟩ := cRepErfc_sector_bound n (N + 1) hδ'0 hδ'lt
  refine ⟨1, C, hC, fun z hz hsec => h z (ne_zero_of_one_le_norm hz) ?_⟩
  have := min_le_left δ (Real.pi / 2)
  linarith

-- no-dlmf: the `m = N` term of the `g`-series peels off the truncation;
-- support lemma for `erf_7_12_3_sector`
private theorem ctruncG_succ_sub (N : ℕ) (z : ℂ) :
    ctruncG (N + 1) z - ctruncG N z
      = ((-1 : ℂ) ^ N * (pochHalf (2 * N + 1) : ℂ))
          / (((Real.pi : ℂ) * z) * ((Real.pi : ℂ) * z ^ 2 / 2) ^ (2 * N + 1)) := by
  unfold ctruncG
  rw [Finset.sum_range_succ, mul_add, add_sub_cancel_left, one_div, inv_mul_eq_div,
    div_div]
  ring

-- no-dlmf: norm of the `m = N` term of the `g`-series; support lemma
private theorem norm_ctruncG_term (N : ℕ) {z : ℂ} (hz0 : z ≠ 0) :
    ‖((-1 : ℂ) ^ N * (pochHalf (2 * N + 1) : ℂ))
        / (((Real.pi : ℂ) * z) * ((Real.pi : ℂ) * z ^ 2 / 2) ^ (2 * N + 1))‖
      = pochHalf (2 * N + 1) / ((Real.pi / 2) ^ (2 * N + 1) * Real.pi)
          / ‖z‖ ^ (4 * N + 3) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hph := pochHalf_pos (2 * N + 1)
  have hnum : ‖((-1 : ℂ) ^ N * (pochHalf (2 * N + 1) : ℂ))‖ = pochHalf (2 * N + 1) := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hph]
  have hden : ‖(((Real.pi : ℂ) * z) * ((Real.pi : ℂ) * z ^ 2 / 2) ^ (2 * N + 1))‖
      = Real.pi * ‖z‖ * (Real.pi * ‖z‖ ^ 2 / 2) ^ (2 * N + 1) := by
    rw [norm_mul, norm_pow, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ, Complex.norm_ofNat]
  rw [norm_div, hnum, hden,
    show Real.pi * ‖z‖ ^ 2 / 2 = Real.pi / 2 * ‖z‖ ^ 2 by ring, mul_pow, ← pow_mul,
    show 2 * (2 * N + 1) = 4 * N + 2 by ring,
    show ‖z‖ ^ (4 * N + 3) = ‖z‖ * ‖z‖ ^ (4 * N + 2) by rw [← pow_succ']]
  have hhalf : (0 : ℝ) < (Real.pi / 2) ^ (2 * N + 1) := by positivity
  have hzpow : (0 : ℝ) < ‖z‖ ^ (4 * N + 2) := by positivity
  field_simp

-- no-dlmf: sharp first-neglected-term bound for `g`, global down to `‖z‖ ≥ 1`;
-- the engine behind the tagged `erf_7_12_3_sector` below (proof: peel the
-- `m = N` term off the `(N+1)`-order global bound of Part III); support lemma
/-- The sharp Poincaré remainder bound for the Fresnel auxiliary function `g`
(7.12.3): for every truncation order `N` and every `δ ∈ (0, ½π)` there is a
constant `C > 0` with

`‖g(z) − (1/(πz)) ∑_{m<N} (−1)ᵐ (½)_{2m+1}/(πz²/2)^{2m+1}‖ ≤ C/‖z‖^{4N+3}`

for all `z` in the sector `|ph z| ≤ ½π − δ` with `‖z‖ ≥ 1` — the remainder after
`N` terms is of the order of the first neglected term
`(πz²/2)^{−(2N+1)}/(πz) ≍ z^{−(4N+3)}`, uniformly in the closed sector. -/
theorem cfresnelAuxG_sharp_bound (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |Complex.arg z| ≤ Real.pi / 2 - δ →
      ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG N z‖ ≤ C / ‖z‖ ^ (4 * N + 3) := by
  obtain ⟨C₁, hC₁, h₁⟩ := cfresnelAuxG_sector_bound (N + 1) hδ hδ'
  have hph := pochHalf_pos (2 * N + 1)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨C₁ + pochHalf (2 * N + 1) / ((Real.pi / 2) ^ (2 * N + 1) * Real.pi),
    by positivity, ?_⟩
  intro z hz hsec
  have hz0 : z ≠ 0 := ne_zero_of_one_le_norm hz
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hsplit : FLMF.Fresnel.cfresnelAuxG z - ctruncG N z
      = (FLMF.Fresnel.cfresnelAuxG z - ctruncG (N + 1) z)
        + (ctruncG (N + 1) z - ctruncG N z) := by ring
  have hmono : C₁ / ‖z‖ ^ (4 * (N + 1) + 1) ≤ C₁ / ‖z‖ ^ (4 * N + 3) := by
    have hle : ‖z‖ ^ (4 * N + 3) ≤ ‖z‖ ^ (4 * (N + 1) + 1) :=
      pow_le_pow_right₀ hz (by omega)
    exact div_le_div_of_nonneg_left hC₁.le (by positivity) hle
  calc ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG N z‖
      ≤ ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG (N + 1) z‖
        + ‖ctruncG (N + 1) z - ctruncG N z‖ := by
          rw [hsplit]; exact norm_add_le _ _
    _ ≤ C₁ / ‖z‖ ^ (4 * (N + 1) + 1)
        + pochHalf (2 * N + 1) / ((Real.pi / 2) ^ (2 * N + 1) * Real.pi)
            / ‖z‖ ^ (4 * N + 3) := by
          refine add_le_add (h₁ z hz0 hsec) ?_
          rw [ctruncG_succ_sub, norm_ctruncG_term N hz0]
    _ ≤ C₁ / ‖z‖ ^ (4 * N + 3)
        + pochHalf (2 * N + 1) / ((Real.pi / 2) ^ (2 * N + 1) * Real.pi)
            / ‖z‖ ^ (4 * N + 3) := add_le_add hmono le_rfl
    _ = (C₁ + pochHalf (2 * N + 1) / ((Real.pi / 2) ^ (2 * N + 1) * Real.pi))
          / ‖z‖ ^ (4 * N + 3) := by
          field_simp

/-- **DLMF 7.12.3** — the Poincaré asymptotic expansion of the Fresnel auxiliary function
`g` as `z → ∞` in the sector `|ph z| ≤ ½π − δ`: for every positive truncation order
`N+1` and every `δ > 0` there are a threshold `R` and a constant `C > 0` with

`‖g(z) − (1/(πz)) ∑_{m<N+1} (−1)ᵐ (½)_{2m+1}/(πz²/2)^{2m+1}‖ ≤ C/‖z‖^{4(N+1)+3}`

for all sufficiently large `‖z‖` (`≥ R`) in the sector — the remainder after `N+1`
terms is of the order of the first neglected term
`(πz²/2)^{−(2(N+1)+1)}/(πz) ≍ z^{−(4(N+1)+3)}`, for every positive truncation order
and every positive separation `δ` from the Stokes lines.  This is exactly DLMF's `∼`
(a Poincaré expansion, §2.1(iii): remainder `O` of the first neglected term for each
positive order, as `z → ∞` in the set) for the displayed series on DLMF's sector
`|ph z| ≤ ½π − δ(<½π)`.  `g` is the auxiliary function of §7.2(iv) (the entire
extension `cfresnelAuxG`); the truncation is the `ctruncG` of 7.12.5.
(The underlying bound `cfresnelAuxG_sharp_bound` is in fact uniform down to `R = 1`
with an explicit constant.)

DLMF 7.12.3.
DAG: E-7.12.3.
Numerical: N/A
Verified: verified
-/
theorem erf_7_12_3_sector (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R C : ℝ, 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → |Complex.arg z| ≤ Real.pi / 2 - δ →
      ‖FLMF.Fresnel.cfresnelAuxG z - ctruncG (N + 1) z‖
        ≤ C / ‖z‖ ^ (4 * (N + 1) + 3) := by
  have hδ'0 : 0 < min δ (Real.pi / 4) := lt_min hδ (by positivity)
  have hδ'lt : min δ (Real.pi / 4) < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  obtain ⟨C, hC, h⟩ := cfresnelAuxG_sharp_bound (N + 1) hδ'0 hδ'lt
  refine ⟨1, C, hC, fun z hz hsec => h z hz ?_⟩
  have := min_le_left δ (Real.pi / 4)
  linarith

/-! ## Part V — DLMF 7.2.4, the limiting values on the sector `|ph z| ≤ ¼π − δ`

On the closed sector `|ph z| ≤ ¼π` one has `Re(z²) = ‖z‖² cos(2 ph z) ≥ 0`, so the Gaussian
factor `‖e^{−z²}‖ = e^{−Re(z²)} ≤ 1`.  Feeding this into the `n = 0` case of the uniform
Poincaré bound `cerfc_poincare_bound` (available on the much larger sector `|ph z| ≤ ¾π − δ'`)
gives the sector-uniform decay `‖erfc z‖ ≤ 2/(√3 √π ‖z‖)`, which is all that the two limits
of 7.2.4 need — `erf z − 1 = −erfc z`. -/

-- no-dlmf: sector-uniform decay of `erfc` on `|ph z| ≤ ¼π`; support lemma for `cerf_7_2_4`
/-- On the closed sector `|ph z| ≤ ¼π` one has `Re(z²) ≥ 0`, so the `n = 0` Poincaré
remainder bound `cerfc_poincare_bound` (used with `δ = ½π`) gives the uniform estimate
`‖erfc z‖ ≤ 2/(√3 √π ‖z‖)`. -/
private theorem norm_cerfc_le_of_abs_arg_le_pi_div_four {z : ℂ} (hz : z ≠ 0)
    (hsec : |Complex.arg z| ≤ Real.pi / 4) :
    ‖cerfc z‖ ≤ 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ‖z‖) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  -- the `n = 0` Poincaré bound on the larger sector `|ph z| ≤ ¾π − ½π = ¼π`
  have hsec' : |Complex.arg z| ≤ 3 * Real.pi / 4 - Real.pi / 2 := by linarith
  have h := cerfc_poincare_bound (δ := Real.pi / 2) (by positivity) (by linarith) hz hsec' 0
  rw [Finset.range_zero, Finset.sum_empty, sub_zero] at h
  have hsin : Real.sin (2 * (Real.pi / 2) / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * (Real.pi / 2) / 3 = Real.pi / 3 by ring, Real.sin_pi_div_three]
  have hR : 2 * (Nat.factorial (2 * 0) : ℝ)
      / (2 * (Real.sin (2 * (Real.pi / 2) / 3) * ‖z‖)) ^ (2 * 0 + 1)
      = 2 / (Real.sqrt 3 * ‖z‖) := by
    rw [hsin]
    norm_num
    ring
  rw [hR] at h
  -- `Re(z²) = ‖z‖² cos(2 ph z) ≥ 0` on the sector
  have hre : 0 ≤ (z ^ 2).re := by
    have hzrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    have hsq : z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ)
        * Complex.exp (((2 * Complex.arg z : ℝ) : ℂ) * Complex.I) := by
      have harg : ((2 * Complex.arg z : ℝ) : ℂ) * Complex.I
          = (Complex.arg z : ℂ) * Complex.I + (Complex.arg z : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_add]
      conv_lhs => rw [hzrep]
      push_cast
      ring
    rw [hsq, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hcos : 0 ≤ Real.cos (2 * Complex.arg z) := by
      obtain ⟨h1, h2⟩ := abs_le.mp hsec
      exact Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
    positivity
  -- combine: `√π ‖erfc z‖ ≤ √π e^{Re z²} ‖erfc z‖ ≤ 2/(√3 ‖z‖)`
  have hL : ‖(Real.sqrt Real.pi : ℂ) * Complex.exp (z ^ 2) * cerfc z‖
      = Real.sqrt Real.pi * Real.exp ((z ^ 2).re) * ‖cerfc z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  rw [hL] at h
  have hexp : (1 : ℝ) ≤ Real.exp ((z ^ 2).re) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hre
  have hmono : Real.sqrt Real.pi * ‖cerfc z‖
      ≤ Real.sqrt Real.pi * Real.exp ((z ^ 2).re) * ‖cerfc z‖ := by
    have h1 : Real.sqrt Real.pi * 1 ≤ Real.sqrt Real.pi * Real.exp ((z ^ 2).re) :=
      mul_le_mul_of_nonneg_left hexp hsp.le
    rw [mul_one] at h1
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hfinal : Real.sqrt Real.pi * ‖cerfc z‖ ≤ 2 / (Real.sqrt 3 * ‖z‖) := le_trans hmono h
  rw [show 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ‖z‖)
      = 2 / (Real.sqrt 3 * ‖z‖) / Real.sqrt Real.pi by field_simp,
    le_div_iff₀ hsp]
  linarith [hfinal]

/-- **DLMF 7.2.4** — the limiting values of the error functions at infinity in the sector:
`lim_{z→∞} erf z = 1` and `lim_{z→∞} erfc z = 0` as `z → ∞` in the closed sector
`|ph z| ≤ ¼π − δ`, for every `δ > 0` (DLMF's `δ(<¼π)`).  The tagged entry is an equation
group asserting both limits, so both are asserted here in one conjunction.

Encoding: "the limit as `z → ∞` in the sector" is written in `ε`-`R` form — for every
`ε > 0` there is a threshold `R` beyond which *every* point of the closed sector is within
`ε` of the limit.  This is the standard unrestricted-limit-in-a-sector statement (the
filter of complements of bounded sets, restricted to the sector), and it is uniform in
`ph z`, as DLMF's uniform sector statement requires.  `erf`/`erfc` are the entire complex
extensions `cerf`/`cerfc` of 7.2.1/7.2.2.  No upper bound on `δ` is imposed: for `δ ≥ ¼π`
the sector degenerates (to the positive real axis, or to the empty set) and the statement
holds a fortiori.

DLMF 7.2.4.
DAG: E-7.2.4.
Numerical: N/A
Verified: verified
-/
theorem cerf_7_2_4 {δ : ℝ} (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → |Complex.arg z| ≤ Real.pi / 4 - δ →
      ‖cerf z - 1‖ < ε ∧ ‖cerfc z‖ < ε := by
  intro ε hε
  have hπ : 0 < Real.pi := Real.pi_pos
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := by positivity
  have hA : (0 : ℝ) < Real.sqrt 3 * Real.sqrt Real.pi := by positivity
  refine ⟨1 + 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ε), fun z hz hsec => ?_⟩
  have hB : (0 : ℝ) < 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ε) := by positivity
  have hzn : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzn
  have hsec' : |Complex.arg z| ≤ Real.pi / 4 := le_trans hsec (by linarith)
  have hb := norm_cerfc_le_of_abs_arg_le_pi_div_four hz0 hsec'
  have hlt : 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ‖z‖) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have hprod : (ε * (Real.sqrt 3 * Real.sqrt Real.pi))
        * (1 + 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ε))
        = ε * (Real.sqrt 3 * Real.sqrt Real.pi) + 2 := by
      field_simp
    calc (2 : ℝ) < ε * (Real.sqrt 3 * Real.sqrt Real.pi) + 2 := by nlinarith
      _ = (ε * (Real.sqrt 3 * Real.sqrt Real.pi))
            * (1 + 2 / (Real.sqrt 3 * Real.sqrt Real.pi * ε)) := hprod.symm
      _ ≤ (ε * (Real.sqrt 3 * Real.sqrt Real.pi)) * ‖z‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)
      _ = ε * (Real.sqrt 3 * Real.sqrt Real.pi * ‖z‖) := by ring
  have hkey : ‖cerfc z‖ < ε := lt_of_le_of_lt hb hlt
  refine ⟨?_, hkey⟩
  have hdiff : cerf z - 1 = -cerfc z := by
    simp only [cerfc]; ring
  rw [hdiff, norm_neg]
  exact hkey

end FLMF.Error
