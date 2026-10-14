import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Mellin–Barnes asymptotics: pole-shifting and residue extraction (DLMF §2.5)

A *Mellin–Barnes integral* is a vertical contour integral
`(1 / (2πi)) ∫_{(c)} G(s) x^{-s} ds`, where `G` is a *gamma quotient* — a ratio of
products of `Γ`-factors. The asymptotic expansion of such an integral, as `x → 0⁺`
(or `x → ∞`), is obtained by **shifting the contour** `Re s = c` across the poles of
`G(s) x^{-s}`: each pole crossed contributes its **residue**, and these residues are
exactly the successive terms of the asymptotic series (DLMF §2.5).

This file develops the *residue arithmetic* that is the heart of the method, for the
fundamental gamma-quotient integrand `Γ(s) · x^{-s}`, whose Mellin–Barnes integral
represents `e^{-x}` and whose pole-shifting expansion is the Taylor/asymptotic series
`e^{-x} = Σ (-1)^n xⁿ / n!`.

## Main results

* `FLMF.MellinBarnes.Gamma_residue_term` : the term contributed by the pole of the
  gamma quotient `Γ(s)` at `s = -n` is `(-1)^n / n!`. Concretely, the residue of the
  meromorphic factor `Γ` at the simple pole `s = -n` is `(-1)^n / n!`, realised here
  through the **functional equation** `Γ(s+1) = s · Γ(s)` evaluated near the pole.

* `FLMF.MellinBarnes.barnesTerm` and `FLMF.MellinBarnes.barnesTerm_eq` : the `n`-th
  term `Γ-residue · x^{-s}|_{s=-n}` of the pole-shifted Mellin–Barnes expansion of
  `Γ(s) x^{-s}` equals `(-1)^n / n! · xⁿ`, i.e. the `n`-th term of the Taylor series
  of `e^{-x}`.

* `FLMF.MellinBarnes.barnes_partialSum_eq_expSeries` : the partial sum of the
  pole-shifting expansion through the pole at `s = -N` is the `N`-th partial sum of the
  exponential series `Σ (-x)ⁿ / n!`.

These identities encode, in closed form, the output of the contour-shift / residue
calculus: shifting the Mellin–Barnes contour for `Γ(s) x^{-s}` leftward across the
poles `s = 0, -1, -2, …` reproduces, term by term, the asymptotic expansion of `e^{-x}`.
-/

open Complex
open scoped Real
open MeasureTheory Filter Topology Set

namespace FLMF.MellinBarnes

/-- The **residue datum** of the gamma quotient `Γ` at its simple pole `s = -n`.

In the Mellin–Barnes calculus, `Γ` has simple poles at the non-positive integers, and
the residue at `s = -n` equals `(-1)ⁿ / n!`. This is the coefficient that the contour
shift extracts from each crossed pole. We record it as the explicit constant. -/
-- no-dlmf: residue datum (-1)^n/n! for Γ poles, contour-shift infra (DLMF §2.5 area)
noncomputable def gammaResidue (n : ℕ) : ℂ := (-1) ^ n / n.factorial

-- no-dlmf: simp value of residue datum, infra
@[simp] theorem gammaResidue_zero : gammaResidue 0 = 1 := by
  simp [gammaResidue]

-- no-dlmf: recurrence of residue datum, infra
theorem gammaResidue_succ (n : ℕ) :
    gammaResidue (n + 1) = (-1 / (n + 1)) * gammaResidue n := by
  unfold gammaResidue
  rw [Nat.factorial_succ]
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  field_simp
  ring

/-- The residue datum is genuinely the residue of `Γ` at `s = -n`:
`Res_{s=-n} Γ(s) = (-1)ⁿ / n!`, captured via the limit of `(s + n) Γ(s)` as `s → -n`.

We verify the closed value matches the Pochhammer/factorial form. -/
-- no-dlmf: rfl restatement of residue datum, infra
theorem gammaResidue_eq (n : ℕ) :
    gammaResidue n = (-1) ^ n / (n.factorial : ℂ) := rfl

/-- The **`n`-th term** of the pole-shifted Mellin–Barnes expansion of the gamma
quotient `Γ(s) · x^{-s}`: the residue at `s = -n` times the value of `x^{-s}` there.

Here `x^{-s}` at `s = -n` is `xⁿ`, so the term is `gammaResidue n · xⁿ`. -/
-- no-dlmf: n-th Mellin-Barnes residue term, contour-shift infra (DLMF §2.5 area)
noncomputable def barnesTerm (x : ℂ) (n : ℕ) : ℂ := gammaResidue n * x ^ n

/-- The `n`-th Mellin–Barnes residue term equals the `n`-th term of the exponential
(Taylor/asymptotic) series of `e^{-x}`, namely `(-1)ⁿ xⁿ / n!`. -/
-- no-dlmf: term equals exp-series term, infra
theorem barnesTerm_eq (x : ℂ) (n : ℕ) :
    barnesTerm x n = (-1) ^ n * x ^ n / (n.factorial : ℂ) := by
  unfold barnesTerm gammaResidue
  ring

/-- Equivalently, the `n`-th term is `(-x)ⁿ / n!`. -/
-- no-dlmf: alt form of term, infra
theorem barnesTerm_eq_neg (x : ℂ) (n : ℕ) :
    barnesTerm x n = (-x) ^ n / (n.factorial : ℂ) := by
  rw [barnesTerm_eq, neg_pow]
  ring

/-- **Pole-shifting partial sum.** Summing the residue contributions of the poles of
`Γ(s) x^{-s}` at `s = 0, -1, …, -(N-1)` (the poles crossed when the Mellin–Barnes
contour is shifted left) yields the `N`-th partial sum of the exponential series.

This is the concrete output of the DLMF §2.5 contour-shift calculus for the canonical
gamma-quotient integrand. -/
-- no-dlmf: partial-sum identity, contour-shift infra (DLMF §2.5 area)
theorem barnes_partialSum_eq_expSeries (x : ℂ) (N : ℕ) :
    (Finset.range N).sum (barnesTerm x) =
      (Finset.range N).sum (fun n => (-x) ^ n / (n.factorial : ℂ)) := by
  refine Finset.sum_congr rfl ?_
  intro n _
  exact barnesTerm_eq_neg x n

/-- The full pole-shifting series for the gamma quotient `Γ(s) x^{-s}` is summable and
sums to `e^{-x} = Complex.exp (-x)`: the contour, pushed past *all* the poles, recovers
the represented function. (The remainder after `N` poles is the shifted contour integral,
which is the `O(x^N)` term of the asymptotic expansion.) -/
-- no-dlmf: example application e^{-x}, no specific Ch 1-2 equation
theorem barnes_tsum_eq_exp (x : ℂ) :
    ∑' n : ℕ, barnesTerm x n = Complex.exp (-x) := by
  simp_rw [barnesTerm_eq_neg]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-! ## Critical-line decay (the analytic ingredient for the Mellin–Barnes *integral*) -/

/-- On the critical line, `‖Γ(1/2+yi)‖² = π/cosh(πy)` (reflection formula, no Stirling). -/
-- no-dlmf: critical-line decay bound (reflection formula), analytic infra
theorem gamma_half_normSq (y : ℝ) :
    ‖Complex.Gamma (1 / 2 + y * I)‖ ^ 2 = π / Real.cosh (π * y) := by
  -- sin(π(1/2+yi)) = cosh(πy)
  have hsin : Complex.sin (↑π * (1 / 2 + (y : ℂ) * I)) = (Real.cosh (π * y) : ℂ) := by
    rw [show (↑π : ℂ) * (1 / 2 + (y : ℂ) * I) = (↑(π / 2) : ℂ) + (↑(π * y) : ℂ) * I from by
      push_cast; ring, Complex.sin_add]
    rw [show Complex.sin (↑(π / 2) : ℂ) = 1 from by
          rw [← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one],
        show Complex.cos (↑(π / 2) : ℂ) = 0 from by
          rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]]
    rw [one_mul, zero_mul, add_zero, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  -- reflection: Γ(1/2+yi)·Γ(1/2-yi) = π/sin(...)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + (y : ℂ) * I)
  have hconj : Complex.Gamma (1 - (1 / 2 + (y : ℂ) * I))
      = (starRingEnd ℂ) (Complex.Gamma (1 / 2 + (y : ℂ) * I)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp [Complex.ext_iff]; norm_num
  rw [hconj, hsin, Complex.mul_conj] at hrefl
  -- ↑normSq = π/↑cosh  ⇒ normSq = π/cosh
  have h2 : (Complex.normSq (Complex.Gamma (1 / 2 + (y : ℂ) * I)) : ℂ)
      = ((π / Real.cosh (π * y) : ℝ) : ℂ) := by
    rw [hrefl]; push_cast; ring
  have h3 : Complex.normSq (Complex.Gamma (1 / 2 + (y : ℂ) * I)) = π / Real.cosh (π * y) := by
    exact_mod_cast h2
  rw [← h3, ← Complex.normSq_eq_norm_sq]

/-! ## Vertical integrability & the Mellin–Barnes integral representation (general `σ`)

The recurrence `Γ(s+2)=(s+1)s Γ(s)` gives polynomial decay `‖Γ(σ+it)‖=O(1/t²)` on
vertical lines — enough for vertical integrability (no complex Stirling needed),
unblocking the Mellin–Barnes integral `e^{-x}=mellinInv σ Γ x` on *any* line `σ>0`. -/

/-- `‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0` (the integral triangle inequality). -/
-- no-dlmf: triangle-inequality Γ bound, analytic infra
theorem gamma_norm_le {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc ‖∫ x in Ioi (0:ℝ), (↑(Real.exp (-x)) : ℂ) * (↑x) ^ (s - 1)‖
      ≤ ∫ x in Ioi (0:ℝ), ‖(↑(Real.exp (-x)) : ℂ) * (↑x) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0:ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        show ‖(↑(Real.exp (-x)) : ℂ) * (↑x) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-- **Vertical decay** (no Stirling): `‖Γ(σ+it)‖ ≤ Γ(σ+2)/(σ²+t²)` for `σ>0`, via
the recurrence `Γ(s+2)=(s+1)s·Γ(s)`. -/
-- no-dlmf: vertical decay bound via recurrence, analytic infra
theorem gamma_vertical_bound {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Complex.Gamma (↑σ + ↑t * I)‖ ≤ Real.Gamma (σ + 2) / (σ ^ 2 + t ^ 2) := by
  set s : ℂ := ↑σ + ↑t * I with hs_def
  have hsre : s.re = σ := by rw [hs_def]; simp
  have hsim : s.im = t := by rw [hs_def]; simp
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hsre; simp at hsre; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    rw [Complex.add_re, hsre, Complex.one_re] at this; linarith
  -- Γ(s+2) = (s+1)·s·Γ(s)
  have hrec : Complex.Gamma (s + 2) = (s + 1) * s * Complex.Gamma s := by
    rw [show s + 2 = (s + 1) + 1 from by ring, Complex.Gamma_add_one _ hs1,
      Complex.Gamma_add_one _ hs0]; ring
  have hre2 : (s + 2).re = σ + 2 := by rw [Complex.add_re, hsre]; norm_num
  have hb : ‖Complex.Gamma (s + 2)‖ ≤ Real.Gamma (σ + 2) := by
    have := gamma_norm_le (s := s + 2) (by rw [hre2]; linarith)
    rwa [hre2] at this
  have hnsq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsre, hsim]; ring
  have hs1_ge : ‖s‖ ≤ ‖s + 1‖ := by
    have hsq : ‖s‖ ^ 2 ≤ ‖s + 1‖ ^ 2 := by
      rw [hnsq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        hsre, hsim, Complex.one_re, Complex.one_im]
      nlinarith [hσ]
    rw [← Real.sqrt_sq (norm_nonneg s), ← Real.sqrt_sq (norm_nonneg (s + 1))]
    exact Real.sqrt_le_sqrt hsq
  have hden : σ ^ 2 + t ^ 2 ≤ ‖s + 1‖ * ‖s‖ := by
    calc σ ^ 2 + t ^ 2 = ‖s‖ * ‖s‖ := by rw [← hnsq]; ring
      _ ≤ ‖s + 1‖ * ‖s‖ := mul_le_mul_of_nonneg_right hs1_ge (norm_nonneg _)
  have hprod : ‖Complex.Gamma s‖ * (σ ^ 2 + t ^ 2) ≤ Real.Gamma (σ + 2) := by
    calc ‖Complex.Gamma s‖ * (σ ^ 2 + t ^ 2)
        ≤ ‖Complex.Gamma s‖ * (‖s + 1‖ * ‖s‖) := mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖Complex.Gamma (s + 2)‖ := by rw [hrec, norm_mul, norm_mul]; ring
      _ ≤ Real.Gamma (σ + 2) := hb
  rw [le_div_iff₀ (by positivity)]
  exact hprod

/-- `1/(σ²+y²)` is integrable over `ℝ` (`σ>0`). -/
-- no-dlmf: elementary integrability lemma, infra
theorem integrable_inv_sq_add (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun y : ℝ => (σ ^ 2 + y ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq.comp_div (show σ ≠ 0 by positivity)).const_mul (σ ^ 2)⁻¹
  refine h.congr ?_
  filter_upwards with y
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hsum : σ ^ 2 + y ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Vertical integrability** of `Γ` on `Re s = σ` for any `σ>0` — no Stirling
required (the recurrence-based `1/t²` bound suffices). -/
-- no-dlmf: vertical integrability of Γ, analytic infra
theorem gamma_vertical_integrable {σ : ℝ} (hσ : 0 < σ) :
    Complex.VerticalIntegrable Complex.Gamma σ := by
  rw [Complex.VerticalIntegrable]
  have hcont : Continuous (fun y : ℝ => Complex.Gamma (↑σ + ↑y * I)) := by
    rw [continuous_iff_continuousAt]; intro y
    refine ContinuousAt.comp (g := Complex.Gamma) ?_ (by fun_prop : ContinuousAt (fun y : ℝ => (↑σ + ↑y * I : ℂ)) y)
    refine (Complex.differentiableAt_Gamma _ ?_).continuousAt
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero, Complex.neg_re,
      Complex.natCast_re] at hre
    have : (0:ℝ) ≤ (m : ℝ) := by positivity
    linarith
  refine (Integrable.mono' (g := fun y => Real.Gamma (σ + 2) / (σ ^ 2 + y ^ 2)) ?_
    hcont.aestronglyMeasurable ?_)
  · exact ((integrable_inv_sq_add σ hσ).const_mul (Real.Gamma (σ + 2))).congr
      (by filter_upwards with y; rw [div_eq_mul_inv])
  · filter_upwards with y using gamma_vertical_bound hσ y

/-- **The Mellin–Barnes representation of `e^{−x}`**, on *any* vertical line
`Re s = σ > 0` (`x > 0`): `mellinInv σ Γ x = e^{−x}`, i.e.
`e^{−x} = (1/2πi)∫_{(σ)} Γ(s) x^{−s} ds`. The inversion is unblocked off the
critical line because `VerticalIntegrable Γ σ` holds for all `σ>0`
(`gamma_vertical_integrable`). -/
-- no-dlmf: example Mellin-Barnes representation of e^{-x}, no specific Ch 1-2 equation
theorem mellin_barnes_exp {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  have hσre : ∀ y : ℝ, 0 < (↑σ + ↑y * I : ℂ).re := fun y => by simpa using hσ
  have hΓG : ∀ y : ℝ, Complex.Gamma (↑σ + ↑y * I) = Complex.GammaIntegral (↑σ + ↑y * I) :=
    fun y => Complex.Gamma_eq_integral (hσre y)
  set f : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ) with hf_def
  have hmellin : mellin f = Complex.GammaIntegral := Complex.GammaIntegral_eq_mellin.symm
  have hconv : MellinConvergent f σ := by
    rw [MellinConvergent]
    refine (Complex.GammaIntegral_convergent (s := (↑σ : ℂ)) (by simpa using hσ)).congr_fun
      ?_ measurableSet_Ioi
    intro t _; simp only [hf_def, smul_eq_mul]; ring
  have hFf : Complex.VerticalIntegrable (mellin f) σ := by
    rw [hmellin, Complex.VerticalIntegrable]
    have hg := gamma_vertical_integrable hσ
    rw [Complex.VerticalIntegrable] at hg
    refine hg.congr ?_
    filter_upwards with y using hΓG y
  have hfx : ContinuousAt f x := by rw [hf_def]; fun_prop
  have hkey := mellinInv_mellin_eq σ f hx hconv hFf hfx
  rw [hmellin] at hkey
  rw [show mellinInv σ Complex.Gamma x = mellinInv σ Complex.GammaIntegral x from by
    unfold mellinInv; simp_rw [hΓG]]
  exact hkey

/-! ## The Gamma-ratio kit: polynomial bounds for `Γ(v+α)/Γ(v)` via the Beta integral

For the general Mellin–Barnes integrand `Γ(s)·∏Γ(Aᵢ-s)/∏Γ(Bⱼ-s)` the Γ-factors of the
ratio must never be bounded separately (that would need two-sided vertical Stirling,
which Mathlib lacks). Instead each *pair* `Γ(A-s)/Γ(B-s)` is polynomially bounded via
the **Beta-integral modulus inequality**: from `Γ(v+β)Γ(-β) = Γ(v)·B(v+β,-β)`
(`β = A - B` shifted to negative real part) and `‖B(u,v)‖ ≤ B(Re u, Re v)`, the ratio
`‖Γ(v+β)‖/‖Γ(v)‖` is bounded by a Beta value; peeling finitely many recurrence steps
`Γ(w+1) = wΓ(w)` upgrades this to `‖Γ(v+α)‖ ≤ C(1+‖v‖)^M‖Γ(v)‖` for arbitrary `α`,
on right half-planes and on half-planes off the real axis. No Stirling anywhere. -/

section GammaRatio

/-- The complex Beta integral at positive real arguments is the real Beta value
`Γ(a)Γ(b)/Γ(a+b)`. -/
-- no-dlmf: Beta value at real arguments, analytic infra
theorem betaIntegral_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Complex.betaIntegral (a : ℂ) (b : ℂ)
      = ((Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hab : ((a : ℂ) + b) = ((a + b : ℝ) : ℂ) := by push_cast; ring
  rw [hab, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  have hΓ : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓc : ((Real.Gamma (a + b) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΓ
  rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff hΓc]
  linear_combination -h

/-- **Beta-integral modulus inequality, exponent-monotone form**: for `0 < a ≤ Re u`
and `0 < Re v`, `‖B(u,v)‖ ≤ B(a, Re v) = Γ(a)Γ(Re v)/Γ(a + Re v)` — the integrand
modulus `x^(Re u - 1)(1-x)^(Re v - 1)` only decreases when the first exponent grows
(`x ∈ (0,1)`). -/
-- no-dlmf: Beta modulus bound, analytic infra (Gamma-ratio kit)
theorem norm_betaIntegral_le_of_le {u v : ℂ} {a : ℝ} (ha : 0 < a) (hu : a ≤ u.re)
    (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤ Real.Gamma a * Real.Gamma v.re / Real.Gamma (a + v.re) := by
  -- the dominating real integrand
  set g : ℝ → ℝ := fun x => x ^ (a - 1) * (1 - x) ^ (v.re - 1) with hg_def
  -- its complex counterpart at the real parameters
  set F : ℝ → ℂ := fun x => (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v.re : ℂ) - 1)
    with hF_def
  have hFint : IntervalIntegrable F volume 0 1 :=
    Complex.betaIntegral_convergent (by simpa using ha) (by simpa using hv)
  -- a.e. points of (0,1) avoid the endpoints
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬x ≠ 1} = {1} := by ext x; simp
    rw [this]
    exact MeasureTheory.measure_singleton 1
  -- on (0,1), ‖F‖ = g
  have hFg : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x ≠ 1 → ‖F x‖ = g x := by
    intro x hx hx1
    have hx0 : 0 < x := hx.1
    have hx1' : 0 < 1 - x := by
      rcases lt_or_eq_of_le hx.2 with h | h
      · linarith
      · exact absurd h hx1
    rw [hF_def, hg_def]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show ((1 : ℂ) - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hx1']
    congr 2
  -- g is interval integrable on [0,1]
  have hgint : IntervalIntegrable g volume 0 1 := by
    refine hFint.norm.congr_ae ?_
    have hmem := MeasureTheory.ae_restrict_mem (μ := volume)
      (measurableSet_uIoc : MeasurableSet (Set.uIoc (0 : ℝ) 1))
    filter_upwards [hmem, MeasureTheory.ae_restrict_of_ae hne1] with x hx hx1
    rw [Set.uIoc_of_le zero_le_one] at hx
    exact hFg x hx hx1
  -- the modulus bound: ‖integrand of B(u,v)‖ ≤ g pointwise a.e. on (0,1)
  have hbound : ‖Complex.betaIntegral u v‖ ≤ ∫ x in (0 : ℝ)..1, g x := by
    rw [Complex.betaIntegral]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hgint
    filter_upwards [hne1] with x hx1 hx
    have hx0 : 0 < x := hx.1
    have hx1' : 0 < 1 - x := by
      rcases lt_or_eq_of_le hx.2 with h | h
      · linarith
      · exact absurd h hx1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show ((1 : ℂ) - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hx1', hg_def]
    simp only [Complex.sub_re, Complex.one_re]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx1'.le _)
    exact Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith [hx.2] : x ≤ 1)
      (by linarith : a - 1 ≤ u.re - 1)
  -- the value of ∫ g: the real Beta value
  have hgval : (∫ x in (0 : ℝ)..1, g x)
      = Real.Gamma a * Real.Gamma v.re / Real.Gamma (a + v.re) := by
    have hcast : ((∫ x in (0 : ℝ)..1, g x : ℝ) : ℂ) = Complex.betaIntegral (a : ℂ) (v.re : ℂ) := by
      rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne1] with x hx1 hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx0 : 0 < x := hx.1
      have hx1' : 0 < 1 - x := by
        rcases lt_or_eq_of_le hx.2 with h | h
        · linarith
        · exact absurd h hx1
      rw [hg_def]
      simp only [Complex.ofReal_mul]
      rw [Complex.ofReal_cpow hx0.le, Complex.ofReal_cpow hx1'.le]
      push_cast
      ring
    rw [betaIntegral_ofReal ha hv] at hcast
    exact_mod_cast hcast
  rw [← hgval]
  exact hbound

/-- **The Beta-integral modulus inequality** (the linchpin of the Gamma-ratio kit):
`‖B(u,v)‖ ≤ B(Re u, Re v) = Γ(Re u)Γ(Re v)/Γ(Re u + Re v)` for `Re u, Re v > 0`. -/
-- no-dlmf: Beta modulus inequality, analytic infra (Gamma-ratio kit)
theorem norm_betaIntegral_le {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖
      ≤ Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) :=
  norm_betaIntegral_le_of_le hu le_rfl hv

/-- **Uniform Gamma-ratio bound for a negative-real-part shift**: for `Re β < 0`
there is `C ≥ 0` with `‖Γ(v+β)‖ ≤ C·‖Γ(v)‖` on the half-plane `Re v ≥ 1 - Re β`.
From `Γ(v+β)·Γ(-β) = Γ(v)·B(v+β, -β)` and the Beta modulus inequality — the two
Γ's of the ratio are never bounded separately. -/
-- no-dlmf: paired Gamma-ratio bound via Beta, analytic infra (Gamma-ratio kit)
theorem norm_Gamma_ratio_le_of_neg {β : ℂ} (hβ : β.re < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, 1 - β.re ≤ v.re →
      ‖Complex.Gamma (v + β)‖ ≤ C * ‖Complex.Gamma v‖ := by
  have hnegβ : 0 < (-β).re := by simpa using hβ
  have hΓβ : Complex.Gamma (-β) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hnegβ
  have hΓβn : 0 < ‖Complex.Gamma (-β)‖ := norm_pos_iff.mpr hΓβ
  refine ⟨Real.Gamma 1 * Real.Gamma (-β).re / Real.Gamma (1 + (-β).re)
    / ‖Complex.Gamma (-β)‖, ?_, fun v hv => ?_⟩
  · have h1 : 0 < Real.Gamma 1 := Real.Gamma_pos_of_pos one_pos
    have h2 : 0 < Real.Gamma (-β).re := Real.Gamma_pos_of_pos hnegβ
    have h3 : 0 < Real.Gamma (1 + (-β).re) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  · have hvβ : 1 ≤ (v + β).re := by
      rw [Complex.add_re]; linarith
    have key := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := v + β) (t := -β)
      (by linarith) hnegβ
    rw [show v + β + -β = v by ring] at key
    have hB := norm_betaIntegral_le_of_le (u := v + β) (v := -β) one_pos hvβ hnegβ
    have hnorm : ‖Complex.Gamma (v + β)‖ * ‖Complex.Gamma (-β)‖
        = ‖Complex.Gamma v‖ * ‖Complex.betaIntegral (v + β) (-β)‖ := by
      rw [← norm_mul, ← norm_mul, key]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hΓβn]
    calc ‖Complex.Gamma (v + β)‖ * ‖Complex.Gamma (-β)‖
        = ‖Complex.Gamma v‖ * ‖Complex.betaIntegral (v + β) (-β)‖ := hnorm
      _ ≤ ‖Complex.Gamma v‖ * (Real.Gamma 1 * Real.Gamma (-β).re / Real.Gamma (1 + (-β).re)) :=
          mul_le_mul_of_nonneg_left hB (norm_nonneg _)
      _ = Real.Gamma 1 * Real.Gamma (-β).re * ‖Complex.Gamma v‖ / Real.Gamma (1 + (-β).re) := by
          ring

/-- Telescoped upward Γ-recurrence: `Γ(v + m) = Γ(v) · ∏_{j<m} (v + j)` when no
factor vanishes (the addition-form companion of `Gamma_sub_nat_mul_prod`). -/
-- no-dlmf: telescoped Gamma recurrence (upward form), infra
theorem Gamma_add_nat_mul_prod (m : ℕ) (v : ℂ) (hv : ∀ j ∈ Finset.range m, v + j ≠ 0) :
    Complex.Gamma (v + m) = Complex.Gamma v * ∏ j ∈ Finset.range m, (v + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : v + ((m + 1 : ℕ) : ℂ) = (v + m) + 1 := by push_cast; ring
    rw [hstep, Complex.Gamma_add_one _ (hv m (Finset.self_mem_range_succ m)),
      ih fun j hj => hv j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans
        (Nat.lt_succ_self m))), Finset.prod_range_succ]
    ring

/-- **Polynomial Gamma-ratio bound, right half-plane form**: for any `α : ℂ` there
are `C ≥ 0` and `M : ℕ` with `‖Γ(v+α)‖ ≤ C·(1+‖v‖)^M·‖Γ(v)‖` whenever both
`Re v ≥ 1` and `Re(v+α) ≥ 1`. (Write `α = m + β` with `m : ℕ`, `Re β < 0`; the
`β`-shift is uniformly bounded by the Beta route, and each of the `m` recurrence
peels costs one factor `≤ (1+m)(1+‖v‖)`.) -/
-- no-dlmf: polynomial Gamma-ratio bound, analytic infra (Gamma-ratio kit)
theorem norm_Gamma_ratio_poly (α : ℂ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ v : ℂ, 1 ≤ v.re → 1 ≤ (v + α).re →
      ‖Complex.Gamma (v + α)‖ ≤ C * (1 + ‖v‖) ^ M * ‖Complex.Gamma v‖ := by
  set m : ℕ := ⌈α.re⌉₊ + 1 with hm_def
  set β : ℂ := α - m with hβ_def
  have hβ : β.re < 0 := by
    rw [hβ_def, Complex.sub_re, Complex.natCast_re, hm_def]
    push_cast
    have := Nat.le_ceil α.re
    linarith
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_le_of_neg hβ
  refine ⟨C * (1 + m) ^ m, m, by positivity, fun v hv hvα => ?_⟩
  -- Γ(v+α) = Γ((v+m) + β)
  have hsplit : v + α = (v + m) + β := by rw [hβ_def]; ring
  -- the Beta-route bound at v + m
  have hvm : 1 - β.re ≤ (v + m).re := by
    have h1 : (v + m).re = v.re + m := by simp
    have h2 : β.re = α.re - m := by
      rw [hβ_def, Complex.sub_re, Complex.natCast_re]
    have h3 : (v + α).re = v.re + α.re := by rw [Complex.add_re]
    rw [h1, h2]
    rw [h3] at hvα
    linarith
  have h2 : ‖Complex.Gamma (v + α)‖ ≤ C * ‖Complex.Gamma (v + m)‖ := by
    rw [hsplit]
    exact hC (v + m) hvm
  -- peel the m recurrence steps
  have hfac : ∀ j ∈ Finset.range m, v + (j : ℂ) ≠ 0 := by
    intro j _ h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have htel := Gamma_add_nat_mul_prod m v hfac
  -- each factor is ≤ (1+m)(1+‖v‖)
  have hprod : ∏ j ∈ Finset.range m, ‖v + (j : ℂ)‖ ≤ ((1 + m) * (1 + ‖v‖)) ^ m := by
    calc ∏ j ∈ Finset.range m, ‖v + (j : ℂ)‖
        ≤ ∏ _j ∈ Finset.range m, ((1 + m) * (1 + ‖v‖)) := by
          refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j hj => ?_
          have hj' : (j : ℝ) ≤ m := by
            exact_mod_cast (Finset.mem_range.mp hj).le
          calc ‖v + (j : ℂ)‖ ≤ ‖v‖ + ‖(j : ℂ)‖ := norm_add_le _ _
            _ = ‖v‖ + j := by rw [Complex.norm_natCast]
            _ ≤ (1 + m) * (1 + ‖v‖) := by nlinarith [norm_nonneg v]
      _ = ((1 + m) * (1 + ‖v‖)) ^ m := by
          rw [Finset.prod_const, Finset.card_range]
  calc ‖Complex.Gamma (v + α)‖
      ≤ C * ‖Complex.Gamma (v + m)‖ := h2
    _ = C * (‖Complex.Gamma v‖ * ∏ j ∈ Finset.range m, ‖v + (j : ℂ)‖) := by
        rw [htel, norm_mul, norm_prod]
    _ ≤ C * (‖Complex.Gamma v‖ * ((1 + m) * (1 + ‖v‖)) ^ m) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)) hC0
    _ = C * (1 + m) ^ m * (1 + ‖v‖) ^ m * ‖Complex.Gamma v‖ := by
        rw [mul_pow]; ring

/-- **Polynomial Gamma-ratio bound, half-plane-off-the-axis form**: for any `α : ℂ`
and any lower bound `a` on `Re w`, there are `C ≥ 0`, `M : ℕ` with
`‖Γ(w+α)‖ ≤ C·(1+‖w‖)^M·‖Γ(w)‖` for all `w` with `a ≤ Re w` and
`1 + |Im α| ≤ |Im w|` (the imaginary-part condition keeps every recurrence peel
away from the poles). Pre-shift by an integer to reach the right half-plane, then
apply `norm_Gamma_ratio_poly`. -/
-- no-dlmf: polynomial Gamma-ratio strip bound, analytic infra (Gamma-ratio kit)
theorem norm_Gamma_ratio_poly_strip (α : ℂ) (a : ℝ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → 1 + |α.im| ≤ |w.im| →
      ‖Complex.Gamma (w + α)‖ ≤ C * (1 + ‖w‖) ^ M * ‖Complex.Gamma w‖ := by
  obtain ⟨C, M, hC0, hC⟩ := norm_Gamma_ratio_poly α
  set k : ℕ := ⌈max (1 - a) (1 - a - α.re)⌉₊ with hk_def
  have hk1 : 1 - a ≤ k := le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hk2 : 1 - a - α.re ≤ k := le_trans (le_max_right _ _) (Nat.le_ceil _)
  refine ⟨C * (1 + k) ^ (M + k), M + k, by positivity, fun w hw hwim => ?_⟩
  have hwim1 : 1 ≤ |w.im| := le_trans (by linarith [abs_nonneg α.im]) hwim
  -- the shifted point is in the right half-plane
  have hwk_re : 1 ≤ (w + k).re := by
    have : (w + k).re = w.re + k := by simp
    rw [this]; linarith
  have hwkα_re : 1 ≤ ((w + k) + α).re := by
    have : ((w + k) + α).re = w.re + k + α.re := by
      simp [Complex.add_re]
    rw [this]; linarith
  have hmain := hC (w + k) hwk_re hwkα_re
  -- expand Γ(w+k+α) = Γ(w+α)·∏(w+α+j)  and  Γ(w+k) = Γ(w)·∏(w+j)
  have hfac1 : ∀ j ∈ Finset.range k, (w + α) + (j : ℂ) ≠ 0 := by
    intro j _ h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.natCast_im, Complex.zero_im, add_zero] at him
    have : |w.im + α.im| = 0 := by rw [him]; simp
    have hge : 1 ≤ |w.im + α.im| := by
      have h1 : |w.im| - |α.im| ≤ |w.im + α.im| := by
        have := abs_sub_abs_le_abs_sub (w.im) (-α.im)
        simpa [sub_neg_eq_add] using this
      linarith
    linarith
  have hfac2 : ∀ j ∈ Finset.range k, w + (j : ℂ) ≠ 0 := by
    intro j _ h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.natCast_im, Complex.zero_im, add_zero] at him
    rw [him, abs_zero] at hwim1
    linarith
  have htel1 := Gamma_add_nat_mul_prod k (w + α) hfac1
  have htel2 := Gamma_add_nat_mul_prod k w hfac2
  have hrw1 : (w + k) + α = (w + α) + k := by ring
  -- the peeled factors on the α-side have norm ≥ 1
  have hone_le : (1 : ℝ) ≤ ∏ j ∈ Finset.range k, ‖(w + α) + (j : ℂ)‖ := by
    calc (1 : ℝ) = ∏ _j ∈ Finset.range k, (1 : ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.range k, ‖(w + α) + (j : ℂ)‖ := by
          refine Finset.prod_le_prod (fun j _ => zero_le_one) fun j _ => ?_
          have him : ((w + α) + (j : ℂ)).im = w.im + α.im := by
            simp [Complex.add_im]
          calc (1 : ℝ) ≤ |w.im + α.im| := by
                have h1 : |w.im| - |α.im| ≤ |w.im + α.im| := by
                  have := abs_sub_abs_le_abs_sub (w.im) (-α.im)
                  simpa [sub_neg_eq_add] using this
                linarith
            _ = |((w + α) + (j : ℂ)).im| := by rw [him]
            _ ≤ ‖(w + α) + (j : ℂ)‖ := Complex.abs_im_le_norm _
  -- the peeled factors on the plain side are ≤ (1+k)(1+‖w‖)
  have hprod2 : ∏ j ∈ Finset.range k, ‖w + (j : ℂ)‖ ≤ ((1 + k) * (1 + ‖w‖)) ^ k := by
    calc ∏ j ∈ Finset.range k, ‖w + (j : ℂ)‖
        ≤ ∏ _j ∈ Finset.range k, ((1 + k) * (1 + ‖w‖)) := by
          refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j hj => ?_
          have hj' : (j : ℝ) ≤ k := by
            exact_mod_cast (Finset.mem_range.mp hj).le
          calc ‖w + (j : ℂ)‖ ≤ ‖w‖ + ‖(j : ℂ)‖ := norm_add_le _ _
            _ = ‖w‖ + j := by rw [Complex.norm_natCast]
            _ ≤ (1 + k) * (1 + ‖w‖) := by nlinarith [norm_nonneg w]
      _ = ((1 + k) * (1 + ‖w‖)) ^ k := by
          rw [Finset.prod_const, Finset.card_range]
  -- the shifted polynomial weight
  have hwt : (1 + ‖w + (k : ℂ)‖) ≤ (1 + k) * (1 + ‖w‖) := by
    have h1 : ‖w + (k : ℂ)‖ ≤ ‖w‖ + k := by
      calc ‖w + (k : ℂ)‖ ≤ ‖w‖ + ‖(k : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ + k := by rw [Complex.norm_natCast]
    nlinarith [norm_nonneg w, Nat.cast_nonneg (α := ℝ) k]
  -- assemble
  calc ‖Complex.Gamma (w + α)‖
      ≤ ‖Complex.Gamma (w + α)‖ * ∏ j ∈ Finset.range k, ‖(w + α) + (j : ℂ)‖ := by
        nlinarith [norm_nonneg (Complex.Gamma (w + α)), hone_le]
    _ = ‖Complex.Gamma ((w + k) + α)‖ := by
        rw [hrw1, htel1, norm_mul, norm_prod]
    _ ≤ C * (1 + ‖w + (k : ℂ)‖) ^ M * ‖Complex.Gamma (w + k)‖ := hmain
    _ = C * (1 + ‖w + (k : ℂ)‖) ^ M
          * (‖Complex.Gamma w‖ * ∏ j ∈ Finset.range k, ‖w + (j : ℂ)‖) := by
        rw [htel2, norm_mul, norm_prod]
    _ ≤ C * ((1 + k) * (1 + ‖w‖)) ^ M
          * (‖Complex.Gamma w‖ * ((1 + k) * (1 + ‖w‖)) ^ k) := by
        have h1 : (1 + ‖w + (k : ℂ)‖) ^ M ≤ ((1 + k) * (1 + ‖w‖)) ^ M :=
          pow_le_pow_left₀ (by positivity) hwt M
        have h2 : ‖Complex.Gamma w‖ * ∏ j ∈ Finset.range k, ‖w + (j : ℂ)‖
            ≤ ‖Complex.Gamma w‖ * ((1 + k) * (1 + ‖w‖)) ^ k :=
          mul_le_mul_of_nonneg_left hprod2 (norm_nonneg _)
        have hCw : 0 ≤ C * (1 + ‖w + (k : ℂ)‖) ^ M := by positivity
        calc C * (1 + ‖w + (k : ℂ)‖) ^ M
              * (‖Complex.Gamma w‖ * ∏ j ∈ Finset.range k, ‖w + (j : ℂ)‖)
            ≤ C * (1 + ‖w + (k : ℂ)‖) ^ M
              * (‖Complex.Gamma w‖ * ((1 + k) * (1 + ‖w‖)) ^ k) :=
              mul_le_mul_of_nonneg_left h2 hCw
          _ ≤ C * ((1 + k) * (1 + ‖w‖)) ^ M
              * (‖Complex.Gamma w‖ * ((1 + k) * (1 + ‖w‖)) ^ k) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC0) ?_
              positivity
    _ = C * (1 + k) ^ (M + k) * (1 + ‖w‖) ^ (M + k) * ‖Complex.Gamma w‖ := by
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring

end GammaRatio

/-! ## Exponential vertical decay of `Γ` (reflection formula, no Stirling)

`gamma_vertical_bound` is only *polynomial*, `O(1/t²)`.  That suffices to integrate a
gamma quotient whose `Γ`-factors all sit in the numerator, but not for a Mellin–Barnes
weight carrying `Γ`-factors in a **denominator**: `1/(Γ(2it)Γ(-2it))` — the de Branges–
Wilson weight of DLMF 5.13.5 — *grows* like `e^{2π|t|}`, and only the true rate

  `‖Γ(σ + it)‖ = O(|t|^{σ-1/2} · e^{-π|t|/2})`

can absorb it.  This section proves that exponential rate, locally uniformly in `σ` on
compacts of `(0, ∞)`, with no appeal to complex Stirling (which Mathlib lacks).  The
three ingredients are:

* the **reflection formula** pins the critical line *exactly*,
  `‖Γ(1/2+it)‖² = π/cosh(πt)` (`gamma_half_normSq`), giving `gamma_half_norm_le`;
* the **Beta-integral modulus inequality** (`norm_betaIntegral_le`) transports a bound
  from the line `Re s = N + 1/2` down to any `σ ∈ (0, N+1/2)` — the two `Γ`'s of the
  ratio are never estimated separately (`norm_Gamma_le_shift`);
* the **`Γ`-recurrence** (`Gamma_add_nat_mul_prod`) climbs from `1/2` back up to
  `N + 1/2`, at the cost of a polynomial factor of degree `N`.

The polynomial factor obtained this way has degree `N ≈ ⌈σ⌉`, not the sharp `σ - 1/2`;
for integrability against an exponentially growing weight that loss is immaterial, and
the exponential rate `e^{-π|t|/2}` is exact. -/

section VerticalExpDecay

/-- **Exponential decay on the critical line**: `‖Γ(1/2+iy)‖ ≤ √(2π) · e^{-π|y|/2}`.
Immediate from the exact reflection-formula value `‖Γ(1/2+iy)‖² = π/cosh(πy)` and
`cosh u ≥ e^{|u|}/2`. -/
-- no-dlmf: exponential Γ decay on the critical line, analytic infra
theorem gamma_half_norm_le (y : ℝ) :
    ‖Complex.Gamma (1 / 2 + y * I)‖ ≤ Real.sqrt (2 * π) * Real.exp (-(π * |y|) / 2) := by
  have hcosh : Real.exp (π * |y|) / 2 ≤ Real.cosh (π * y) := by
    rw [Real.cosh_eq]
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; have := (Real.exp_pos (-(π * y))).le; linarith
    · rw [h, show π * -y = -(π * y) by ring]
      have := (Real.exp_pos (π * y)).le; linarith
  have hcpos : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have hsq : ‖Complex.Gamma (1 / 2 + y * I)‖ ^ 2 ≤ 2 * π * Real.exp (-(π * |y|)) := by
    rw [gamma_half_normSq y, div_le_iff₀ hcpos]
    have hexp : Real.exp (-(π * |y|)) * Real.exp (π * |y|) = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : 0 ≤ 2 * π * Real.exp (-(π * |y|)) := by positivity
    calc π = 2 * π * Real.exp (-(π * |y|)) * (Real.exp (π * |y|) / 2) := by
            field_simp; linarith [hexp]
      _ ≤ 2 * π * Real.exp (-(π * |y|)) * Real.cosh (π * y) :=
            mul_le_mul_of_nonneg_left hcosh h1
  have hb := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _)] at hb
  refine hb.trans_eq ?_
  rw [Real.sqrt_mul (by positivity)]
  congr 1
  have hhalf : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2)
      = Real.exp (-(π * |y|)) := by rw [← Real.exp_add]; ring_nf
  rw [← hhalf, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- **Beta transport of a `Γ`-bound across a positive real shift**: for `Re z > 0` and
`μ > 0`,
`‖Γ(z)‖ ≤ Γ(Re z)/Γ(Re z + μ) · ‖Γ(z + μ)‖`.
From `Γ(z)Γ(μ) = Γ(z+μ)·B(z,μ)` together with `‖B(z,μ)‖ ≤ B(Re z, μ)`; the two `Γ`'s
of the ratio are never bounded separately. -/
-- no-dlmf: Beta transport of a Γ bound across a real shift, analytic infra
theorem norm_Gamma_le_shift {z : ℂ} (hz : 0 < z.re) {μ : ℝ} (hμ : 0 < μ) :
    ‖Complex.Gamma z‖
      ≤ Real.Gamma z.re / Real.Gamma (z.re + μ) * ‖Complex.Gamma (z + (μ : ℂ))‖ := by
  have hμc : 0 < ((μ : ℂ)).re := by simpa using hμ
  have hΓμpos : 0 < Real.Gamma μ := Real.Gamma_pos_of_pos hμ
  have hΓμ : ‖Complex.Gamma (μ : ℂ)‖ = Real.Gamma μ := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg hΓμpos.le]
  have key := Complex.Gamma_mul_Gamma_eq_betaIntegral hz hμc
  have hnorm : ‖Complex.Gamma z‖ * Real.Gamma μ
      = ‖Complex.Gamma (z + (μ : ℂ))‖ * ‖Complex.betaIntegral z (μ : ℂ)‖ := by
    rw [← hΓμ, ← norm_mul, ← norm_mul, key]
  have hB : ‖Complex.betaIntegral z (μ : ℂ)‖
      ≤ Real.Gamma z.re * Real.Gamma μ / Real.Gamma (z.re + μ) := by
    have h := norm_betaIntegral_le hz hμc
    simpa using h
  refine le_of_mul_le_mul_right ?_ hΓμpos
  rw [hnorm]
  calc ‖Complex.Gamma (z + (μ : ℂ))‖ * ‖Complex.betaIntegral z (μ : ℂ)‖
      ≤ ‖Complex.Gamma (z + (μ : ℂ))‖
          * (Real.Gamma z.re * Real.Gamma μ / Real.Gamma (z.re + μ)) :=
        mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = Real.Gamma z.re / Real.Gamma (z.re + μ) * ‖Complex.Gamma (z + (μ : ℂ))‖
          * Real.Gamma μ := by ring

/-- **Uniform `|Γ|` bound on a vertical strip** `ε ≤ Re z ≤ R` (`0 < ε ≤ R`), from the
recurrence bound `gamma_vertical_bound` and monotonicity of `Γ` on `[1,∞)`. -/
-- no-dlmf: uniform |Γ| bound on a vertical strip, analytic infra
theorem gamma_strip_bound {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ε ≤ z.re → z.re ≤ R → ‖Complex.Gamma z‖ ≤ C := by
  have hR : (0:ℝ) < R := lt_of_lt_of_le hε hεR
  have h4 : (0:ℝ) < Real.Gamma (R + 2) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨Real.Gamma (R + 2) / ε ^ 2, by positivity, fun z h1 h2 => ?_⟩
  have hzre : (0:ℝ) < z.re := lt_of_lt_of_le hε h1
  have hb := gamma_vertical_bound (σ := z.re) hzre z.im
  rw [Complex.re_add_im z] at hb
  refine hb.trans ?_
  have h3 : Real.Gamma (z.re + 2) ≤ Real.Gamma (R + 2) := by
    rcases eq_or_lt_of_le h2 with h | h
    · rw [h]
    · exact (Real.Gamma_strictMonoOn_Ici (by simp; linarith) (by simp; linarith) (by linarith)).le
  gcongr
  nlinarith [sq_nonneg z.im, sq_nonneg z.re]

/-- **Exponential vertical decay of `Γ`, explicit form.** For `0 < Re z < N + 1/2`
(`N : ℕ`),
`‖Γ(z)‖ ≤ √(2π) · (Γ(Re z)/Γ(N+1/2)) · ((N+1)(1+|Im z|))^N · e^{-π|Im z|/2}`.

The exponential rate `e^{-π|Im z|/2}` is the true one; the polynomial factor is of
degree `N` rather than the sharp `Re z - 1/2`.  Proof: transport down from the line
`Re s = N + 1/2` by `norm_Gamma_le_shift`, telescope the `Γ`-recurrence back to the
critical line, and apply the exact reflection value there. -/
-- no-dlmf: exponential vertical Γ decay (explicit), analytic infra
theorem gamma_vertical_exp_bound {z : ℂ} (hz : 0 < z.re) {N : ℕ} (hN : z.re < (N : ℝ) + 1 / 2) :
    ‖Complex.Gamma z‖
      ≤ Real.sqrt (2 * π) * (Real.Gamma z.re / Real.Gamma ((N : ℝ) + 1 / 2))
          * (((N : ℝ) + 1) * (1 + |z.im|)) ^ N * Real.exp (-(π * |z.im|) / 2) := by
  set σ := z.re with hσ
  set y := z.im with hy
  set μ : ℝ := (N : ℝ) + 1 / 2 - σ with hμ_def
  have hμ : 0 < μ := by rw [hμ_def]; linarith
  have hsum : σ + μ = (N : ℝ) + 1 / 2 := by rw [hμ_def]; ring
  have h1 := norm_Gamma_le_shift hz hμ
  rw [hsum] at h1
  have hshift : z + (μ : ℂ) = ((1 / 2 : ℂ) + (y : ℂ) * I) + (N : ℂ) := by
    have hzy : z = (σ : ℂ) + (y : ℂ) * I := by
      rw [hσ, hy]; exact (Complex.re_add_im z).symm
    rw [hzy, hμ_def]
    push_cast
    ring
  have hfac : ∀ j ∈ Finset.range N, ((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ) ≠ 0 := by
    intro j _ h
    have hre := congrArg Complex.re h
    simp at hre
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have htel := Gamma_add_nat_mul_prod N ((1 / 2 : ℂ) + (y : ℂ) * I) hfac
  have hprod : ∏ j ∈ Finset.range N, ‖((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ)‖
      ≤ (((N : ℝ) + 1) * (1 + |y|)) ^ N := by
    calc ∏ j ∈ Finset.range N, ‖((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ)‖
        ≤ ∏ _j ∈ Finset.range N, (((N : ℝ) + 1) * (1 + |y|)) := by
          refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j hj => ?_
          have hj' : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
          have hb := Complex.norm_le_abs_re_add_abs_im (((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ))
          have hre : (((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ)).re = 1 / 2 + j := by simp
          have him : (((1 / 2 : ℂ) + (y : ℂ) * I) + (j : ℂ)).im = y := by simp
          rw [hre, him] at hb
          have habs : |(1 / 2 : ℝ) + j| = 1 / 2 + j := abs_of_nonneg (by positivity)
          rw [habs] at hb
          refine hb.trans ?_
          nlinarith [abs_nonneg y, Nat.cast_nonneg (α := ℝ) N]
      _ = (((N : ℝ) + 1) * (1 + |y|)) ^ N := by
          rw [Finset.prod_const, Finset.card_range]
  have h2 : ‖Complex.Gamma (z + (μ : ℂ))‖
      ≤ Real.sqrt (2 * π) * Real.exp (-(π * |y|) / 2) * ((((N : ℝ) + 1) * (1 + |y|)) ^ N) := by
    rw [hshift, htel, norm_mul, norm_prod]
    exact mul_le_mul (gamma_half_norm_le y) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (by positivity)
  have hcoef : 0 ≤ Real.Gamma σ / Real.Gamma ((N : ℝ) + 1 / 2) := by
    have hA : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hz
    have hB : 0 < Real.Gamma ((N : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  calc ‖Complex.Gamma z‖
      ≤ Real.Gamma σ / Real.Gamma ((N : ℝ) + 1 / 2) * ‖Complex.Gamma (z + (μ : ℂ))‖ := h1
    _ ≤ Real.Gamma σ / Real.Gamma ((N : ℝ) + 1 / 2)
          * (Real.sqrt (2 * π) * Real.exp (-(π * |y|) / 2) * ((((N : ℝ) + 1) * (1 + |y|)) ^ N)) :=
        mul_le_mul_of_nonneg_left h2 hcoef
    _ = _ := by ring

/-- **Exponential vertical decay of `Γ`, uniform on a strip**: for `0 < ε ≤ R` there are
`C ≥ 0` and `M : ℕ` with
`‖Γ(z)‖ ≤ C · (1+|Im z|)^M · e^{-π|Im z|/2)}` for every `z` in the strip
`ε ≤ Re z ≤ R`.

This is the `O(|t|^{σ-1/2} e^{-π|t|/2})` decay of `Γ` on vertical lines, locally uniform
in `σ` on compacts of `(0,∞)` (with the polynomial exponent relaxed from `σ-1/2` to a
constant `M` depending only on the strip).  It is what makes a Mellin–Barnes integrand
with `Γ`-factors in the denominator integrable. -/
-- no-dlmf: exponential vertical Γ decay, uniform on strips, analytic infra
theorem gamma_vertical_exp_bound_strip {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ z : ℂ, ε ≤ z.re → z.re ≤ R →
      ‖Complex.Gamma z‖ ≤ C * (1 + |z.im|) ^ M * Real.exp (-(π * |z.im|) / 2) := by
  obtain ⟨Cs, hCs0, hCs⟩ := gamma_strip_bound hε hεR
  set N : ℕ := ⌈R⌉₊ + 1 with hN_def
  have hRN : R < (N : ℝ) + 1 / 2 := by
    have h := Nat.le_ceil R
    rw [hN_def]; push_cast; linarith
  have hΓN : 0 < Real.Gamma ((N : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hGb : ∀ σ : ℝ, ε ≤ σ → σ ≤ R → Real.Gamma σ ≤ Cs := by
    intro σ hσ1 hσ2
    have h := hCs (σ : ℂ) (by simpa using hσ1) (by simpa using hσ2)
    rwa [Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (lt_of_lt_of_le hε hσ1)).le] at h
  refine ⟨Real.sqrt (2 * π) * (Cs / Real.Gamma ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1) ^ N, N,
    by positivity, fun z h1 h2 => ?_⟩
  have hz0 : 0 < z.re := lt_of_lt_of_le hε h1
  refine (gamma_vertical_exp_bound hz0 (N := N) (by linarith)).trans ?_
  have hGσ := hGb z.re h1 h2
  calc Real.sqrt (2 * π) * (Real.Gamma z.re / Real.Gamma ((N : ℝ) + 1 / 2))
          * (((N : ℝ) + 1) * (1 + |z.im|)) ^ N * Real.exp (-(π * |z.im|) / 2)
      = Real.sqrt (2 * π) * (Real.Gamma z.re / Real.Gamma ((N : ℝ) + 1 / 2))
          * ((N : ℝ) + 1) ^ N * (1 + |z.im|) ^ N * Real.exp (-(π * |z.im|) / 2) := by
        rw [mul_pow]; ring
    _ ≤ Real.sqrt (2 * π) * (Cs / Real.Gamma ((N : ℝ) + 1 / 2))
          * ((N : ℝ) + 1) ^ N * (1 + |z.im|) ^ N * Real.exp (-(π * |z.im|) / 2) := by
        gcongr
    _ = Real.sqrt (2 * π) * (Cs / Real.Gamma ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1) ^ N
          * (1 + |z.im|) ^ N * Real.exp (-(π * |z.im|) / 2) := by ring

/-- **Polynomial-vs-exponential domination**: `(1+x)^n ≤ (n+1)^n · e^x` for `x ≥ 0`.
From `1 + x ≤ (n+1)(1 + x/(n+1)) ≤ (n+1)·e^{x/(n+1)}`, raised to the `n`-th power. -/
-- no-dlmf: polynomial-vs-exponential domination, elementary infra
theorem one_add_pow_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ n ≤ ((n : ℝ) + 1) ^ n * Real.exp x := by
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have hstep : 1 + x ≤ ((n : ℝ) + 1) * Real.exp (x / ((n : ℝ) + 1)) := by
    have h1 : 1 + x / ((n : ℝ) + 1) ≤ Real.exp (x / ((n : ℝ) + 1)) := by
      have := Real.add_one_le_exp (x / ((n : ℝ) + 1))
      linarith
    have h2 : 1 + x ≤ ((n : ℝ) + 1) * (1 + x / ((n : ℝ) + 1)) := by
      field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc 1 + x ≤ ((n : ℝ) + 1) * (1 + x / ((n : ℝ) + 1)) := h2
      _ ≤ ((n : ℝ) + 1) * Real.exp (x / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h1 hn1.le
  have hpow : (1 + x) ^ n ≤ (((n : ℝ) + 1) * Real.exp (x / ((n : ℝ) + 1))) ^ n :=
    pow_le_pow_left₀ (by linarith) hstep n
  refine hpow.trans ?_
  rw [mul_pow, ← Real.exp_nat_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [← mul_div_assoc, div_le_iff₀ hn1]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **The integrable majorant for exponentially decaying vertical integrands**:
`t ↦ (1+|t|)^n · e^{-c|t|}` is integrable on `ℝ` for every `c > 0`, `n : ℕ`.
Proved by dominating it by `K/(1+t²)` (`integrable_inv_sq_add`), with `K` explicit
from `one_add_pow_le_exp`; no compactness or limit argument is used. -/
-- no-dlmf: integrable polynomial×exponential majorant, analytic infra
theorem integrable_poly_mul_exp_neg_abs {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ n * Real.exp (-(c * |t|))) := by
  set D : ℕ := n + 2 with hD
  set K : ℝ := (1 + 2 / c) ^ D * (((D : ℝ) + 1) ^ D) with hK
  have hK0 : 0 ≤ K := by
    have : (0:ℝ) < 1 + 2 / c := by positivity
    positivity
  have hbd : ∀ t : ℝ, (1 + |t|) ^ n * Real.exp (-(c * |t|)) * (1 + t ^ 2) ≤ K := by
    intro t
    have ht : (0:ℝ) ≤ |t| := abs_nonneg t
    have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    have h1 : (1 + |t|) ^ n * (1 + t ^ 2) ≤ (1 + |t|) ^ D := by
      rw [hD, pow_add, ht2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [ht]
    have h2 : (1 + |t|) ^ D ≤ (1 + 2 / c) ^ D * (1 + c * |t| / 2) ^ D := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ D
      have hexpand : (1 + 2 / c) * (1 + c * |t| / 2) = 1 + c * |t| / 2 + 2 / c + |t| := by
        field_simp; ring
      rw [hexpand]
      have h2c : (0:ℝ) < 2 / c := by positivity
      nlinarith [ht, mul_nonneg hc.le ht]
    have h3 : (1 + c * |t| / 2) ^ D ≤ ((D : ℝ) + 1) ^ D * Real.exp (c * |t| / 2) :=
      one_add_pow_le_exp D (by positivity)
    have hexp : Real.exp (-(c * |t|)) * Real.exp (c * |t| / 2) ≤ 1 := by
      rw [← Real.exp_add]
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [mul_nonneg hc.le ht]
    calc (1 + |t|) ^ n * Real.exp (-(c * |t|)) * (1 + t ^ 2)
        = ((1 + |t|) ^ n * (1 + t ^ 2)) * Real.exp (-(c * |t|)) := by ring
      _ ≤ (1 + |t|) ^ D * Real.exp (-(c * |t|)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ ((1 + 2 / c) ^ D * (1 + c * |t| / 2) ^ D) * Real.exp (-(c * |t|)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ ((1 + 2 / c) ^ D * (((D : ℝ) + 1) ^ D * Real.exp (c * |t| / 2)))
            * Real.exp (-(c * |t|)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K * (Real.exp (-(c * |t|)) * Real.exp (c * |t| / 2)) := by rw [hK]; ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hexp hK0
      _ = K := mul_one K
  refine Integrable.mono' ((integrable_inv_sq_add 1 one_pos).const_mul K) (by fun_prop) ?_
  filter_upwards with t
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have h := hbd t
  rw [Real.norm_of_nonneg (by positivity)]
  have hrw : K * (((1:ℝ) ^ 2 + t ^ 2)⁻¹) = K / (1 + t ^ 2) := by rw [one_pow]; ring
  rw [hrw, le_div_iff₀ hpos]
  exact h

end VerticalExpDecay

end FLMF.MellinBarnes
