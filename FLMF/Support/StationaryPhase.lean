import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Method of stationary phase (method kit — DLMF §2.3)

Leading-order asymptotics of oscillatory integrals `∫ g(t) e^{i M φ(t)} dt`: the
dominant contribution comes from stationary points `φ'(t₀)=0`, with the
characteristic `√(2π/M)` decay and a phase from the Hessian signature.

## Why this is *not* a corollary of `SaddlePoint`/`Laplace`

The saddle-point (`PicardLefschetz.saddlePoint_asymp`) and half-line Laplace
(`PicardLefschetz.laplace_Ioi`) theorems both drive their limit through
**dominated convergence with a real Gaussian dominator**, which requires genuine
exponential decay of the integrand (`Re S ≻ 0`, encoded as `hDecay`/`hgap`). On
the imaginary axis the phase is purely oscillatory, `|e^{i M φ}| = 1`, so there
is *nothing to dominate* — that route is unavailable, and the boundary
(`Re b = 0`) Gaussian is absent from Mathlib (`integral_gaussian_complex` needs
`0 < re b`).

The honest substitute used here is **exact evaluation + boundary limit**: write
the oscillatory phase together with a real Gaussian window `e^{-c x²}` as a single
complex Gaussian `e^{-(c - iMa)x²}` with `Re(c - iMa) = c > 0`, evaluate it in
closed form with `integral_gaussian_complex`, and pass to the oscillatory boundary
`c/M - ia → -ia` by **continuity of the principal branch** `b ↦ (π/b)^{1/2}` (the
target `π/(-ia) = (π/a) i` is off the branch cut, `im ≠ 0`). No DCT, no
dominator.

## Main results

* `scaled_integral` — the change of variables `x = u/√M` folding the `√M`
  prefactor into the integral: `√M · ∫ e^{-(c-iMa)x²} = ∫ e^{-(c/M-ia)u²}`.
* `stationaryPhase_gaussianWindow` — the leading-order stationary-phase law
  for a Gaussian window over a non-degenerate quadratic phase `φ(x) = a x²`
  (`a ≠ 0`, either sign):
  `√M · ∫_ℝ e^{-c x²} e^{i M a x²} dx → (π/a · i)^{1/2} = √(π/|a|)·e^{i·sgn(a)·π/4}`.
  With `g(0) = 1` and `φ''(0) = 2a` this is the DLMF §2.3(iii) constant
  `g(0)·√(2π/|φ''|)·e^{i·sgn(φ'')·π/4}`.
* `fresnel_regularized` — the Abel-regularized Fresnel integral:
  `lim_{ε↓0} ∫_ℝ e^{-(ε - ia)x²} dx = (π/a · i)^{1/2}` (`a ≠ 0`).
* `nonstationaryPhase_decay` — the **localization pillar**: away from a stationary
  point (`φ' ≠ 0`), `‖∫_a^b (h·φ') e^{iMφ}‖ ≤ (1/M) ∫ ‖h'‖`, an `O(1/M)` bound via
  one integration by parts (`h = g/φ'` recovers a general amplitude `g`).
* `stationaryPhase_gaussianWindow_closedForm` — the leading term in explicit
  Fresnel-constant form `√(π/a)·e^{iπ/4}` (`a > 0`), via `cpow_half_pos_mul_I`
  (`(r·i)^{1/2} = √r·e^{iπ/4}`).

## The two pillars of stationary phase

The DLMF §2.3(iii) asymptotic assembles from two complementary facts:

* **leading term** at the stationary point — `stationaryPhase_gaussianWindow`
  (the `√(2π/M)` Gaussian/Fresnel contribution), and
* **rapid decay** where there is no stationary point —
  `nonstationaryPhase_decay` (non-stationary phase / integration by parts).

Both are proved here, sorry-free, against Mathlib alone — including the genuine
`Re = 0` boundary Gaussian that neither Mathlib nor the `picard-lefschetz` spine
carried.

## Scope / frontier

What remains for the *fully general* single-stationary-point asymptotic is to glue
the two pillars: a `C^∞` cut-off splitting `∫ g e^{iMφ}` into a core (reduced to
the Gaussian form by the 1-D Morse change of variables `u = sgn·√(φ−φ(x₀))`) and a
tail (controlled by `nonstationaryPhase_decay`, iterated through
`Methods.RepeatedIBP` for `O(M^{-N})`). That gluing — and the multiple- or
degenerate-stationary-point and higher-dimensional cases — is the natural next
layer.
-/

namespace FLMF.Methods.StationaryPhase

open MeasureTheory Filter Topology Complex
open scoped Real

/-- The oscillatory-boundary value `π / (-(i a)) = (π/a)·i` for `a ≠ 0`. The
limiting `b₀` of the regularized Gaussian coefficient lands here, on the imaginary
axis — off the principal-branch cut. -/
-- no-dlmf: algebraic base case, infra
lemma base_eq (a : ℝ) (ha : a ≠ 0) :
    (Real.pi : ℂ) / (-(Complex.I * (a : ℂ))) = ((Real.pi / a : ℝ) : ℂ) * Complex.I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb0 : (-(Complex.I * (a : ℂ))) ≠ 0 := by simp [ha']
  rw [Complex.ofReal_div, div_eq_iff hb0]
  have hrw : ((Real.pi : ℂ) / (a : ℂ) * Complex.I * (-(Complex.I * (a : ℂ))))
      = (Real.pi : ℂ) / (a : ℂ) * (-(Complex.I * Complex.I)) * (a : ℂ) := by ring
  rw [hrw, Complex.I_mul_I]
  field_simp

/-- **Continuity of the principal-branch leading factor at the oscillatory
boundary.** The map `b ↦ (π/b)^{1/2}` is continuous at `b₀ = -(i a)` (`a ≠ 0`):
`b₀ ≠ 0` and `π/b₀ = (π/a) i` has nonzero imaginary part (either sign), hence lies
in the slit plane where `(·)^{1/2}` is continuous. This is the analytic step that
*replaces* the dominated-convergence argument of the real-axis methods. -/
-- no-dlmf: continuity helper, analytic infra
lemma cpow_half_continuousAt (a : ℝ) (ha : a ≠ 0) :
    ContinuousAt (fun b : ℂ => ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ))
      (-(Complex.I * (a : ℂ))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hb0 : (-(Complex.I * (a : ℂ))) ≠ 0 := by simp [ha']
  have hslit : ((Real.pi : ℂ) / (-(Complex.I * (a : ℂ)))) ∈ Complex.slitPlane := by
    rw [base_eq a ha, Complex.mem_slitPlane_iff]
    right
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact div_ne_zero Real.pi_ne_zero ha
  exact (continuousAt_cpow_const hslit).comp
    (continuousAt_const.div continuousAt_id hb0)

/-- **Change of variables `x = u/√M`** folding the `√M` prefactor into the
integral. For `M > 0`,
`√M · ∫ e^{-(c - iMa)x²} dx = ∫ e^{-(c/M - ia)u²} du`. The substitution turns the
fixed-window/growing-frequency integral into a fixed-frequency integral with a
vanishing real damping `c/M`, which is exactly the form `integral_gaussian_complex`
evaluates and whose `M → ∞` limit is the oscillatory boundary. -/
-- no-dlmf: scaling helper for the integral, analytic infra
lemma scaled_integral (a c : ℝ) {M : ℝ} (hM : 0 < M) :
    ((Real.sqrt M : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-((c : ℂ) - Complex.I * (M : ℂ) * (a : ℂ)) * (x : ℂ) ^ 2)
      = ∫ u : ℝ, Complex.exp (-((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)) * (u : ℂ) ^ 2) := by
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsqMnn : (0 : ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hsqMne : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM).ne'
  set g : ℝ → ℂ := fun u => Complex.exp (-((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)) * (u : ℂ) ^ 2)
    with hg
  have hsq : ((Real.sqrt M : ℝ) : ℂ) ^ 2 = (M : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hM.le]
  have hpt : ∀ x : ℝ,
      Complex.exp (-((c : ℂ) - Complex.I * (M : ℂ) * (a : ℂ)) * (x : ℂ) ^ 2)
        = g (Real.sqrt M * x) := by
    intro x
    rw [hg]
    simp only
    congr 1
    rw [Complex.ofReal_mul, mul_pow, hsq]
    rw [show -((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)) * ((M : ℂ) * (x : ℂ) ^ 2)
          = -((c : ℂ) / (M : ℂ) * (M : ℂ) - Complex.I * (a : ℂ) * (M : ℂ)) * (x : ℂ) ^ 2 from by
        ring]
    rw [div_mul_cancel₀ (c : ℂ) hMne]
    ring
  calc
    ((Real.sqrt M : ℝ) : ℂ) *
          ∫ x : ℝ, Complex.exp (-((c : ℂ) - Complex.I * (M : ℂ) * (a : ℂ)) * (x : ℂ) ^ 2)
        = ((Real.sqrt M : ℝ) : ℂ) * ∫ x : ℝ, g (Real.sqrt M * x) := by
          simp_rw [hpt]
      _ = ((Real.sqrt M : ℝ) : ℂ) * (|(Real.sqrt M)⁻¹| • ∫ u : ℝ, g u) := by
          rw [Measure.integral_comp_mul_left g (Real.sqrt M)]
      _ = ∫ u : ℝ, g u := by
          rw [abs_of_nonneg (inv_nonneg.2 hsqMnn), Complex.real_smul, ← mul_assoc,
            show ((Real.sqrt M : ℝ) : ℂ) * (((Real.sqrt M)⁻¹ : ℝ) : ℂ) = 1 by
              rw [← Complex.ofReal_mul, mul_inv_cancel₀ hsqMne, Complex.ofReal_one],
            one_mul]

/-- **Leading-order stationary phase (Gaussian window, quadratic phase).**

For a non-degenerate quadratic phase `φ(x) = a x²` (`a ≠ 0`, either sign of
curvature) and a Gaussian window `g(x) = e^{-c x²}` (`c > 0`),
`√M · ∫_ℝ e^{-c x²} · e^{i M a x²} dx  ⟶  (π/a · i)^{1/2}`  as `M → ∞`.

The limit `(π/a · i)^{1/2} = √(π/|a|) · e^{i·sgn(a)·π/4}` is the DLMF §2.3(iii)
leading constant `g(0)·√(2π/|φ''(0)|)·e^{i·sgn(φ'')·π/4}` (here `g(0) = 1`,
`φ''(0) = 2a`, so `√(2π/(2|a|)) = √(π/|a|)`). The `±π/4` phase is the signature
`sgn(a)` of the curvature — `+π/4` for `a > 0`, `−π/4` for `a < 0`. -/
-- no-dlmf: Gaussian-window stationary phase, method infra (DLMF §2.3 area)
theorem stationaryPhase_gaussianWindow (a c : ℝ) (ha : a ≠ 0) (hc : 0 < c) :
    Tendsto (fun M : ℝ =>
        ((Real.sqrt M : ℝ) : ℂ) *
          ∫ x : ℝ, Complex.exp (-(c : ℂ) * (x : ℂ) ^ 2)
            * Complex.exp (Complex.I * (M : ℂ) * (a : ℂ) * (x : ℂ) ^ 2))
      atTop (𝓝 ((((Real.pi / a : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
  -- The boundary coefficient `c/M - ia → -ia`.
  have hphi : Tendsto (fun M : ℝ => ((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ))) atTop
      (𝓝 (-(Complex.I * (a : ℂ)))) := by
    have hcM : Tendsto (fun M : ℝ => c / M) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul c)
    have hcMc : Tendsto (fun M : ℝ => ((c : ℂ) / (M : ℂ))) atTop (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp hcM
      simp only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_zero] at h
      exact h
    have := hcMc.sub (tendsto_const_nhds (x := Complex.I * (a : ℂ)))
    simpa using this
  -- Continuity at the boundary gives the cpow-form limit.
  have hlim : Tendsto
      (fun M : ℝ => ((Real.pi : ℂ) / ((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ))) ^ (1 / 2 : ℂ))
      atTop (𝓝 ((((Real.pi / a : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
    have h := (cpow_half_continuousAt a ha).tendsto.comp hphi
    rw [base_eq a ha] at h
    exact h
  -- Eventually (M > 0) the original sequence equals the cpow-form.
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  -- combine the window and oscillatory exponentials into one complex Gaussian
  have hpt2 : ∀ x : ℝ,
      Complex.exp (-(c : ℂ) * (x : ℂ) ^ 2)
          * Complex.exp (Complex.I * (M : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)
        = Complex.exp (-((c : ℂ) - Complex.I * (M : ℂ) * (a : ℂ)) * (x : ℂ) ^ 2) := by
    intro x
    rw [← Complex.exp_add]; congr 1; ring
  -- real part of the boundary coefficient is `c/M > 0`
  have hbre : ((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)).re = c / M := by
    rw [← Complex.ofReal_div]
    simp [Complex.sub_re, Complex.mul_re]
  have hb : 0 < ((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)).re := by
    rw [hbre]; exact div_pos hc hM
  rw [eq_comm]
  calc
    ((Real.sqrt M : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-(c : ℂ) * (x : ℂ) ^ 2)
          * Complex.exp (Complex.I * (M : ℂ) * (a : ℂ) * (x : ℂ) ^ 2)
        = ((Real.sqrt M : ℝ) : ℂ) *
            ∫ x : ℝ, Complex.exp (-((c : ℂ) - Complex.I * (M : ℂ) * (a : ℂ)) * (x : ℂ) ^ 2) := by
          simp_rw [hpt2]
      _ = ∫ u : ℝ, Complex.exp (-((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ)) * (u : ℂ) ^ 2) :=
          scaled_integral a c hM
      _ = ((Real.pi : ℂ) / ((c : ℂ) / (M : ℂ) - Complex.I * (a : ℂ))) ^ (1 / 2 : ℂ) :=
          integral_gaussian_complex hb

/-- **Abel-regularized Fresnel integral.** For `a > 0`,
`lim_{ε↓0} ∫_ℝ e^{-(ε - i a) x²} dx = (π/a · i)^{1/2} = √(π/a)·e^{iπ/4}`.

The Bochner integral of the bare Fresnel integrand `e^{i a x²}` does not exist
(`|e^{iax²}| = 1 ∉ L¹`), so the oscillatory value is recovered as the `ε ↓ 0`
limit of the genuinely-integrable damped family — the same boundary continuity
that powers `stationaryPhase_gaussianWindow`, here with the frequency fixed
and the damping sent to zero. Either sign of `a` (`a ≠ 0`). -/
-- no-dlmf: regularized Fresnel limit, analytic infra
theorem fresnel_regularized (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, Complex.exp (-((ε : ℂ) - Complex.I * (a : ℂ)) * (x : ℂ) ^ 2))
      (𝓝[>] 0) (𝓝 ((((Real.pi / a : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
  -- coefficient `ε - ia → -ia` as `ε ↓ 0`
  have hphi : Tendsto (fun ε : ℝ => ((ε : ℂ) - Complex.I * (a : ℂ))) (𝓝[>] 0)
      (𝓝 (-(Complex.I * (a : ℂ)))) := by
    have hε : Tendsto (fun ε : ℝ => ((ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using h
    have h := hε.sub (tendsto_const_nhds (x := Complex.I * (a : ℂ)))
    simpa using h
  have hlim : Tendsto
      (fun ε : ℝ => ((Real.pi : ℂ) / ((ε : ℂ) - Complex.I * (a : ℂ))) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 ((((Real.pi / a : ℝ) : ℂ) * Complex.I) ^ (1 / 2 : ℂ))) := by
    have h := (cpow_half_continuousAt a ha).tendsto.comp hphi
    rw [base_eq a ha] at h
    exact h
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hbre : ((ε : ℂ) - Complex.I * (a : ℂ)).re = ε := by
    simp [Complex.sub_re, Complex.mul_re]
  have hb : 0 < ((ε : ℂ) - Complex.I * (a : ℂ)).re := by rw [hbre]; exact hεpos
  exact (integral_gaussian_complex hb).symm

/-- **Non-stationary phase (localization / rapid decay).**

The complementary pillar of the method: where the phase has *no* stationary point,
the oscillatory integral decays. For an amplitude written as `h · φ'` (so that
`h = g/φ'` recovers a general amplitude `g` wherever `φ' ≠ 0`), with `h`
vanishing at the endpoints `a, b`,
`‖∫_a^b h(x) φ'(x) e^{i M φ(x)} dx‖ ≤ (1/M) ∫_a^b ‖h'(x)‖`,
an `O(1/M)` bound. (Iterating with `Methods.RepeatedIBP` upgrades this to
`O(M^{-N})`.)

Proof: a single integration by parts moving the `φ'` onto `d/dx e^{iMφ} = iMφ'
e^{iMφ}`; the endpoint terms vanish, and `|e^{iMφ}| = 1` bounds the remainder.
This is the half that, combined with the leading-order law at the stationary
point, assembles the full DLMF §2.3(iii) asymptotic by localizing the integral to
a neighbourhood of `φ' = 0`. -/
-- no-dlmf: non-stationary phase decay, method infra (DLMF §2.3 area)
theorem nonstationaryPhase_decay (a b M : ℝ) (hab : a ≤ b) (hM : 0 < M)
    (φ φ' : ℝ → ℝ) (h h' : ℝ → ℂ)
    (hφ : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (φ' x) x)
    (hh : ∀ x ∈ Set.uIcc a b, HasDerivAt h (h' x) x)
    (hφ'c : ContinuousOn φ' (Set.uIcc a b))
    (hh'c : ContinuousOn h' (Set.uIcc a b))
    (ha0 : h a = 0) (hb0 : h b = 0) :
    ‖∫ x in a..b, h x * (φ' x : ℂ) * Complex.exp (Complex.I * (M : ℂ) * (φ x : ℂ))‖
      ≤ (1 / M) * ∫ x in a..b, ‖h' x‖ := by
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * (M : ℂ) * (φ x : ℂ)) with he_def
  -- `|e| = 1`: the phase is purely imaginary.
  have henorm : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    rw [he_def]
    simp only
    rw [Complex.norm_exp]
    have hre : (Complex.I * (M : ℂ) * (φ x : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  -- `e` is differentiable with `e' = iMφ'·e`.
  have he : ∀ x ∈ Set.uIcc a b, HasDerivAt e (e x * (Complex.I * (M : ℂ) * (φ' x : ℂ))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((φ y : ℝ) : ℂ)) ((φ' x : ℝ) : ℂ) x :=
      (hφ x hx).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => Complex.I * (M : ℂ) * ((φ y : ℝ) : ℂ))
        (Complex.I * (M : ℂ) * ((φ' x : ℝ) : ℂ)) x :=
      h1.const_mul (Complex.I * (M : ℂ))
    exact h2.cexp
  -- continuity / integrability side conditions
  have hφcont : ContinuousOn φ (Set.uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hecont : ContinuousOn e (Set.uIcc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφcont))
  have hh'ii : IntervalIntegrable h' volume a b := hh'c.intervalIntegrable
  have he'ii : IntervalIntegrable (fun x => e x * (Complex.I * (M : ℂ) * (φ' x : ℂ)))
      volume a b :=
    (hecont.mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hφ'c))).intervalIntegrable
  -- integration by parts (`u = h`, `v = e`)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hh he hh'ii he'ii
  -- pull the constant `iM` out of the rewritten left integral
  have hLHS : (∫ x in a..b, h x * (e x * (Complex.I * (M : ℂ) * (φ' x : ℂ))))
      = (Complex.I * (M : ℂ)) * ∫ x in a..b, h x * (φ' x : ℂ) * e x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  -- the key identity: `iM · ∫ hφ'e = -∫ h'e`
  have key : (Complex.I * (M : ℂ)) * ∫ x in a..b, h x * (φ' x : ℂ) * e x
      = -∫ x in a..b, h' x * e x := by
    rw [← hLHS, hIBP, ha0, hb0]
    ring
  -- norms
  have hMnorm : ‖Complex.I * (M : ℂ)‖ = M := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  have hbound : M * ‖∫ x in a..b, h x * (φ' x : ℂ) * e x‖ ≤ ∫ x in a..b, ‖h' x‖ := by
    have e1 : M * ‖∫ x in a..b, h x * (φ' x : ℂ) * e x‖
        = ‖(Complex.I * (M : ℂ)) * ∫ x in a..b, h x * (φ' x : ℂ) * e x‖ := by
      rw [norm_mul, hMnorm]
    have e2 : ‖(Complex.I * (M : ℂ)) * ∫ x in a..b, h x * (φ' x : ℂ) * e x‖
        = ‖∫ x in a..b, h' x * e x‖ := by rw [key, norm_neg]
    have e3 : ‖∫ x in a..b, h' x * e x‖ ≤ ∫ x in a..b, ‖h' x‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp [henorm]
    rw [e1, e2]; exact e3
  rw [one_div_mul_eq_div, le_div_iff₀ hM]
  calc ‖∫ x in a..b, h x * (φ' x : ℂ) * e x‖ * M
      = M * ‖∫ x in a..b, h x * (φ' x : ℂ) * e x‖ := by ring
    _ ≤ ∫ x in a..b, ‖h' x‖ := hbound

/-- The principal-branch value `(r·i)^{1/2}` for `r > 0`, in closed form:
`(r·i)^{1/2} = √r · e^{iπ/4}`. This turns the oscillatory-boundary limit value
into the recognizable Fresnel constant. -/
-- no-dlmf: cpow helper, infra
lemma cpow_half_pos_mul_I (r : ℝ) (hr : 0 < r) :
    ((r : ℂ) * Complex.I) ^ (1 / 2 : ℂ)
      = (Real.sqrt r : ℂ) * Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) := by
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hne : (r : ℂ) * Complex.I ≠ 0 := mul_ne_zero hrne Complex.I_ne_zero
  rw [Complex.cpow_def_of_ne_zero hne, Complex.log_ofReal_mul hr Complex.I_ne_zero,
    Complex.log_I]
  rw [show ((Real.log r : ℂ) + (Real.pi : ℂ) / 2 * Complex.I) * (1 / 2 : ℂ)
        = ((Real.log r / 2 : ℝ) : ℂ) + Complex.I * ((Real.pi / 4 : ℝ) : ℂ) from by
      push_cast; ring]
  rw [Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
  congr 1
  ring

/-- **Leading-order stationary phase, closed form (positive curvature).**

For `a > 0`, `c > 0`,
`√M · ∫_ℝ e^{-c x²} · e^{i M a x²} dx  ⟶  √(π/a) · e^{iπ/4}`  as `M → ∞`,
the DLMF §2.3(iii) leading constant in explicit `√(2π/(M|φ''|))·e^{iπ/4}` form
(`g(0) = 1`, `φ''(0) = 2a`). The `a < 0` case is the complex conjugate
(`e^{-iπ/4}`); see `stationaryPhase_gaussianWindow` for the unified
principal-branch statement. -/
-- no-dlmf: closed-form Gaussian-window stationary phase, method infra (DLMF §2.3 area)
theorem stationaryPhase_gaussianWindow_closedForm (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun M : ℝ =>
        ((Real.sqrt M : ℝ) : ℂ) *
          ∫ x : ℝ, Complex.exp (-(c : ℂ) * (x : ℂ) ^ 2)
            * Complex.exp (Complex.I * (M : ℂ) * (a : ℂ) * (x : ℂ) ^ 2))
      atTop (𝓝 ((Real.sqrt (Real.pi / a) : ℂ)
        * Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)))) := by
  have h := stationaryPhase_gaussianWindow a c ha.ne' hc
  rwa [cpow_half_pos_mul_I (Real.pi / a) (by positivity)] at h

/-- **Oscillatory change of variables onto the quadratic phase.**

On an interval `[c,d]` carrying a `C¹` chart `u` for the phase `φ`
(`φ(x) = φ(x₀) + u(x)²` — the Morse normal form near a non-degenerate stationary
point `x₀`, see `Methods/MorseLemma.morse_normal_form`), the substitution
`v = u(x)` turns a general oscillatory integral into a *pure quadratic-phase*
integral times the constant phase `e^{iMφ(x₀)}`:
`∫_c^d u'(x)·h(u x)·e^{iMφ(x)} dx = e^{iMφ(x₀)} · ∫_{u c}^{u d} h(v)·e^{iMv²} dv`.

This is the reduction of the DLMF §2.3 single-stationary-point integral to the
Fresnel/quadratic case (issue #4). The amplitude is presented in transported
form `u'·(h∘u)`; combining with the Morse chart (and its inverse) realizes a
given amplitude `g` via `h = (g/u')∘u⁻¹`, whence `h(0) = g(x₀)/u'(x₀)` is the
classical leading constant. -/
-- no-dlmf: change-of-variables for oscillatory integral, analytic infra
theorem morse_oscillatory_subst
    (φ u u' : ℝ → ℝ) (h : ℝ → ℂ) (M x₀ c d : ℝ)
    (hu : ∀ x ∈ Set.uIcc c d, HasDerivAt u (u' x) x)
    (hu' : ContinuousOn u' (Set.uIcc c d))
    (hh : ContinuousOn h (u '' Set.uIcc c d))
    (hphase : ∀ x ∈ Set.uIcc c d, φ x = φ x₀ + (u x) ^ 2) :
    (∫ x in c..d, (u' x : ℂ) * h (u x) * Complex.exp (Complex.I * (M : ℂ) * (φ x : ℂ)))
      = Complex.exp (Complex.I * (M : ℂ) * (φ x₀ : ℂ))
          * ∫ v in (u c)..(u d), h v * Complex.exp (Complex.I * (M : ℂ) * (v : ℂ) ^ 2) := by
  set g : ℝ → ℂ := fun v => h v * Complex.exp (Complex.I * (M : ℂ) * (v : ℂ) ^ 2) with hg
  have hgc : ContinuousOn g (u '' Set.uIcc c d) :=
    hh.mul (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  have hsubst : (∫ x in c..d, (u' x : ℝ) • (g ∘ u) x) = ∫ v in (u c)..(u d), g v :=
    intervalIntegral.integral_deriv_smul_comp' hu hu' hgc
  have hpt : Set.EqOn
      (fun x => (u' x : ℂ) * h (u x) * Complex.exp (Complex.I * (M : ℂ) * (φ x : ℂ)))
      (fun x => Complex.exp (Complex.I * (M : ℂ) * (φ x₀ : ℂ)) * ((u' x : ℝ) • (g ∘ u) x))
      (Set.uIcc c d) := by
    intro x hx
    simp only [hg, Function.comp_apply, Complex.real_smul]
    rw [hphase x hx]
    push_cast
    rw [show (Complex.I * (M : ℂ) * ((φ x₀ : ℂ) + (u x : ℂ) ^ 2))
          = Complex.I * (M : ℂ) * (φ x₀ : ℂ) + Complex.I * (M : ℂ) * (u x : ℂ) ^ 2 from by ring,
      Complex.exp_add]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, hsubst]

end FLMF.Methods.StationaryPhase
