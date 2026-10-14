import FLMF.Support.HypergeometricGaussPrincipalGlobal
import FLMF.Support.HypergeometricPFQ
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Fin.VecNotation

/-!
# DLMF §15.12: asymptotic approximations

This file makes the limiting filters, remainder functions, local generating
germs, and root branches explicit.  In particular, no displayed `O` term is
represented as an unconstrained scalar.
-/

namespace FLMF.Hypergeometric

noncomputable section

open Asymptotics Filter Set Topology

/-- DLMF 15.12.1, the upper signed angle. -/
-- DAG: E-15.12.1.
-- Verified: unverified
def chapter15AlphaPlus (z : ℂ) : ℝ :=
  Real.arctan
    ((Complex.arg z - Complex.arg (1 - z) - Real.pi) /
      Real.log ‖1 - z⁻¹‖)

/-- DLMF 15.12.1, the lower signed angle.
DAG: E-15.12.1.
-/
-- Verified: unverified
def chapter15AlphaMinus (z : ℂ) : ℝ :=
  Real.arctan
    ((Complex.arg z - Complex.arg (1 - z) + Real.pi) /
      Real.log ‖1 - z⁻¹‖)

/-- The four DLMF admissibility alternatives preceding 15.12.2, together with
the standing regularity hypothesis `GaussRegular c` (`c ∉ {0, -1, -2, …}`).

The `GaussRegular c` conjunct is not decorative: `principalGauss` returns the
junk value `0` at singular lower parameters (its own contract requires every
theorem that uses it to carry `GaussRegular c`), and DLMF 15.12.2 is the
asymptotics of the *ordinary* Gauss function `F(a,b;c;z)`, whose implicit
domain excludes the nonpositive integers `c`.  Without this conjunct the filter
would admit `c = -N` through the terminating-`a`/`b` alternatives, where
`principalGauss` is `0` but the partial sum is not, making 15.12.2 false.

DLMF 15.12.2.
-/
-- DAG: E-15.12.2.
-- Verified: unverified
def LargeCAdmissible (δ : ℝ) (a b z c : ℂ) : Prop :=
  GaussRegular c ∧
  ((∃ n : ℕ, a = -(n : ℂ)) ∨ (∃ n : ℕ, b = -(n : ℂ)) ∨
  (z.re < 1 / 2 ∧ ∀ n : ℕ, δ ≤ ‖c + n‖) ∨
  (z.re = 1 / 2 ∧ |Complex.arg c| ≤ Real.pi - δ) ∨
  (1 / 2 < z.re ∧
    chapter15AlphaMinus z - Real.pi / 2 + δ ≤ Complex.arg c ∧
    Complex.arg c ≤ chapter15AlphaPlus z + Real.pi / 2 - δ))

/-- Complex infinity restricted to the large-`c` regions used in §15.12(ii).

DLMF 15.12.
-/
-- DAG: E-15.12.
-- Verified: unverified
def largeCFilter (δ : ℝ) (a b z : ℂ) : Filter ℂ :=
  comap norm atTop ⊓ principal {c | LargeCAdmissible δ a b z c}

/-- DLMF 15.12.2 with its `O(c⁻ᵐ)` remainder interpreted by `IsBigO` on the
explicit large-`c` filter.
DAG: E-15.12.2.
Numerical: N/A (numerical-pending)
Verified: unverified
-/
theorem hypergeometric_15_12_2_large_c
    (a b z : ℂ) (m : ℕ) (δ : ℝ) (_hδ : 0 < δ) :
    IsBigO (largeCFilter δ a b z)
      (fun c => principalGauss a b c z -
        ∑ s ∈ Finset.range m,
          ordinaryHypergeometricCoefficient a b c s * z ^ s)
      (fun c : ℂ => c ^ (-(m : ℤ))) := by
  -- PARKED[M]: awaits M-comparison-ode-uniform
  sorry

-- no-dlmf: generic Poincaré-expansion predicate (§2.1(iii) concept, no ch15 display)
/-- A Poincaré expansion: after truncating before term `m`, the remainder is
`O` of the first omitted term. -/
def HasPoincareExpansion (l : Filter ℂ) (f : ℂ → ℂ)
    (term : ℕ → ℂ → ℂ) : Prop :=
  ∀ m : ℕ, IsBigO l
    (fun x => f x - ∑ s ∈ Finset.range m, term s x)
    (term m)

-- no-dlmf: uniformity-sector bookkeeping for the §15.12(iii) asymptotics
/-- Infinity in the closed complex sector `|arg λ| ≤ π - δ`. -/
def sectorAtInfinity (δ : ℝ) : Filter ℂ :=
  comap norm atTop ⊓ principal {lam : ℂ | |Complex.arg lam| ≤ Real.pi - δ}

/-- The norm map tends to `atTop` along `comap norm atTop ⊓ principal S`, for any
constraining set `S : Set ℂ`.  Generic over the principal component, so it
specializes definitionally to `sectorAtInfinity δ`, `airySectorAtInfinity δ`,
and `largeCFilter δ a b z` (each is `comap norm atTop ⊓ principal S` for its
own `S`).
-- no-dlmf: filter-plumbing support lemma. -/
theorem tendsto_norm_comap_inf_principal (S : Set ℂ) :
    Filter.Tendsto (fun lam : ℂ => ‖lam‖)
      (Filter.comap norm Filter.atTop ⊓ Filter.principal S) Filter.atTop :=
  Filter.tendsto_comap.mono_left inf_le_left

/-- The working eventual facts every sectorial proof opens with: along
`sectorAtInfinity δ` the norm eventually exceeds any prescribed `R`, the
variable is eventually nonzero, and the principal sector constraint
`|arg λ| ≤ π - δ` holds.  The norm bound comes from the `comap norm atTop`
component (strengthened to `max R 1` so that nonvanishing follows), the arg
bound from the principal component. -/
theorem eventually_sectorAtInfinity (δ R : ℝ) :
    ∀ᶠ lam in sectorAtInfinity δ,
      R ≤ ‖lam‖ ∧ lam ≠ 0 ∧ |Complex.arg lam| ≤ Real.pi - δ := by
  rw [sectorAtInfinity]
  have hnorm : ∀ᶠ lam : ℂ in comap norm atTop, max R 1 ≤ ‖lam‖ :=
    eventually_comap.2 ((eventually_ge_atTop (max R 1)).mono fun b hb a ha => ha ▸ hb)
  have harg : ∀ᶠ lam in principal {lam : ℂ | |Complex.arg lam| ≤ Real.pi - δ},
      |Complex.arg lam| ≤ Real.pi - δ := fun _ h => h
  filter_upwards [hnorm.filter_mono inf_le_left, harg.filter_mono inf_le_right]
    with lam hn ha
  refine ⟨le_trans (le_max_left _ _) hn, fun h0 => ?_, ha⟩
  rw [h0, norm_zero] at hn
  have := le_max_right R 1
  linarith

/-- The removable analytic extension of `(exp t - 1) / t` at `t = 0`. -/
def expSubOneDiv (t : ℂ) : ℂ :=
  if t = 0 then 1 else (Complex.exp t - 1) / t

/-- `expSubOneDiv 0 = 1`: the value of the removable extension of
`(exp t - 1)/t` at the origin. -/
@[simp] theorem expSubOneDiv_zero : expSubOneDiv 0 = 1 := if_pos rfl

/-- The removable extension `expSubOneDiv` of `(exp t - 1)/t` is exactly
`dslope Complex.exp 0`: off the origin both are the difference quotient
`(exp t - exp 0)/(t - 0)`, and at the origin both take the value
`deriv Complex.exp 0 = 1`. -/
theorem expSubOneDiv_eq_dslope : expSubOneDiv = dslope Complex.exp 0 := by
  funext t
  by_cases h : t = 0
  · subst h
    simp [expSubOneDiv_zero, dslope_same, Complex.deriv_exp]
  · rw [expSubOneDiv, if_neg h, dslope_of_ne _ h, slope_def_field]
    simp [div_eq_mul_inv, sub_zero, Complex.exp_zero]

/-- The removable extension `expSubOneDiv` of `(exp t - 1)/t` is analytic at
`t = 0`; its power series there is the shifted exponential series
`∑ tⁿ/(n+1)!` (the `fslope` of the series of `exp` at `0`).  Since
`expSubOneDiv 0 = 1 ≠ 0`, continuity gives eventual nonvanishing near `0`. -/
theorem analyticAt_expSubOneDiv : AnalyticAt ℂ expSubOneDiv 0 := by
  rw [expSubOneDiv_eq_dslope]
  obtain ⟨p, hp⟩ := analyticAt_cexp (z := 0)
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- The generating germ on the left of DLMF 15.12.4.

DLMF 15.12.4.
-/
-- DAG: E-15.12.4.
-- Verified: verified
def qGeneratingFunction (a b c z t : ℂ) : ℂ :=
  expSubOneDiv t ^ (b - 1) * Complex.exp (t * (1 - c)) *
    (1 - z + z * Complex.exp (-t)) ^ (-a)

-- no-dlmf: analyticity-only support lemma; the DLMF 15.12.4 generating identity
-- itself is `hypergeometric_15_12_4_q_generating`
/-- The DLMF 15.12.4 generating germ
`q(t) = ((eᵗ − 1)/t)^{b−1} · e^{t(1−c)} · (1 − z + z·e^{−t})^{−a}`
is analytic at `t = 0` for **all** parameters `a b c z : ℂ`: the removable
extension `expSubOneDiv` is the `dslope` of the entire function `Complex.exp`
at `0` (hence analytic, with value `1 ∈ slitPlane`, so its `cpow` by the
constant `b − 1` is analytic), the middle factor is entire, and the last
`cpow` base equals `1 ∈ slitPlane` at `t = 0` for every `z`. -/
theorem analyticAt_qGeneratingFunction (a b c z : ℂ) :
    AnalyticAt ℂ (qGeneratingFunction a b c z) 0 := by
  have h1 : AnalyticAt ℂ expSubOneDiv 0 := by
    have h : expSubOneDiv = dslope Complex.exp 0 := by
      funext t
      by_cases ht : t = 0
      · subst ht
        simp [expSubOneDiv, dslope, Complex.deriv_exp]
      · rw [dslope_of_ne _ ht, slope_def_field, expSubOneDiv, if_neg ht]
        simp
    rw [h]
    obtain ⟨p, hp⟩ := analyticAt_cexp (z := (0 : ℂ))
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have h2 : AnalyticAt ℂ (fun t : ℂ => expSubOneDiv t ^ (b - 1)) 0 :=
    h1.cpow analyticAt_const (by simp [expSubOneDiv])
  have h3 : AnalyticAt ℂ (fun t : ℂ => Complex.exp (t * (1 - c))) 0 :=
    (analyticAt_id.mul analyticAt_const).cexp
  have h4 : AnalyticAt ℂ (fun t : ℂ => (1 - z + z * Complex.exp (-t)) ^ (-a)) 0 := by
    have hbase : AnalyticAt ℂ (fun t : ℂ => 1 - z + z * Complex.exp (-t)) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id.neg.cexp)
    exact hbase.cpow analyticAt_const (by simp)
  exact (h2.mul h3).mul h4

/-- The coefficient `q_s(z)` as the Taylor coefficient of the DLMF generating
germ at the origin.

DLMF 15.12.4. -/
-- DAG: E-15.12.4.
-- Verified: verified
def qCoefficient (a b c z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (qGeneratingFunction a b c z) 0 / (Nat.factorial s : ℂ)

/-- DLMF 15.12.4: the local Taylor series defining `q_s(z)`.
DAG: E-15.12.4.
Numerical: N/A (numerical-pending)
Verified: verified
-/
theorem hypergeometric_15_12_4_q_generating
    (a b c z : ℂ) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      HasSum (fun s : ℕ => qCoefficient a b c z s * t ^ s)
        (qGeneratingFunction a b c z t) := by
  obtain ⟨r, hr, hq⟩ :=
    (analyticAt_qGeneratingFunction a b c z).exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with t ht
  have hTaylor :=
    Complex.hasSum_taylorSeries_on_ball hq.differentiableOn ht
  convert hTaylor using 1 with s
  simp [qCoefficient, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- DLMF 15.12.3: large denominator parameter, with the coefficient family
from 15.12.4 and a sectorial Poincaré interpretation of `∼`.
DAG: E-15.12.3.
Numerical: N/A (numerical-pending)
Verified: unverified
-/
theorem hypergeometric_15_12_3_large_denominator
    (a b c z : ℂ) (δ : ℝ) (_hδ : 0 < δ)
    (_hz : z.re ≤ 1 / 2) :
    HasPoincareExpansion (sectorAtInfinity δ)
      (fun lam => principalGauss a b (c + lam) z)
      (fun s lam =>
        Complex.Gamma (c + lam) / Complex.Gamma (c - b + lam) *
          qCoefficient a b c z s * (ascPochhammer ℂ s).eval b *
          lam ^ (-(s : ℂ) - b)) := by
  -- PARKED[M]: awaits M-comparison-ode-uniform
  sorry

/-! ### Branch-selected change-of-variable equations -/

/-- Principal complex inverse hyperbolic cosine (DLMF 15.12.6, the change of
variable `ζ = arccosh z`; also used in defining 15.12.10). -/
-- DAG: E-15.12.6.
-- Verified: unverified
def chapter15Arccosh (z : ℂ) : ℂ :=
  Complex.log (z + (z - 1) ^ (1 / 2 : ℂ) * (z + 1) ^ (1 / 2 : ℂ))

-- no-dlmf: trivial unfolding of the `chapter15Arccosh` def (DLMF 15.12.6 is the
-- change-of-variable ζ = arccosh z, not a logarithmic formula; the def itself
-- carries the tag)
/-- `chapter15Arccosh` unfolds to its defining log expression.

-/
theorem hypergeometric_15_12_6_zeta (z : ℂ) :
    chapter15Arccosh z =
      Complex.log (z + (z - 1) ^ (1 / 2 : ℂ) * (z + 1) ^ (1 / 2 : ℂ)) :=
  rfl

/-- DLMF 15.12.8: the continuous branch of the square root defining
`α = (−2 ln(1 − ((z−1)/(z+1))²))^{1/2}`, normalized so that `Re α > 0` when
`Re((z−1)/(z+1)) > 0`.  This `structure` IS the formalization of the definition
15.12.8 (as `def chapter15AiryZeta` is of 15.12.10); its fields are exactly the
defining square relation and the branch/sign normalization.
DAG: E-15.12.8.
-/
-- Verified: unverified
structure Chapter15AlphaBranch (U : Set ℂ) where
  value : ℂ → ℂ
  continuousOn : ContinuousOn value U
  sq_eq : ∀ z ∈ U,
    value z ^ 2 = -2 * Complex.log (1 - ((z - 1) / (z + 1)) ^ 2)
  positive_normalization : ∀ z ∈ U,
    0 < ((z - 1) / (z + 1)).re → 0 < (value z).re

-- no-dlmf: reusable branch-uniqueness engine for §15.12(iii)
/-- If two continuous functions on a preconnected set `U` have equal `n`-th
powers there, the denominator branch `g` is nowhere zero on `U`, and they agree
at a single point `z₀`, then they agree on all of `U`.

Mathematics: the ratio `f/g` is continuous on `U`, its `n`-th power is `1`, so
it takes values in the finite (hence discrete) set of `n`-th roots of unity; a
continuous map from a preconnected set into a discrete set is constant, and it
equals `1` at `z₀`, so `f = g` throughout `U`.  This is the "a continuous
branch of an `n`-th root is pinned by one value" principle underlying
15.12.8/15.12.11. -/
theorem eqOn_of_pow_eq {U : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hgne : ∀ z ∈ U, g z ≠ 0) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ z ∈ U, f z ^ n = g z ^ n)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (heq : f z₀ = g z₀) :
    Set.EqOn f g U := by
  have hrc : ContinuousOn (fun z => f z / g z) U := hf.div hg hgne
  have hmaps : Set.MapsTo (fun z => f z / g z) U
      (↑(Polynomial.nthRootsFinset n (1 : ℂ)) : Set ℂ) := by
    intro z hz
    have hp : (f z / g z) ^ n = 1 := by
      rw [div_pow, hpow z hz]
      exact div_self (pow_ne_zero n (hgne z hz))
    simpa [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn] using hp
  have hdisc : IsDiscrete (↑(Polynomial.nthRootsFinset n (1 : ℂ)) : Set ℂ) :=
    (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet.isDiscrete
  have hconst : ∀ z ∈ U, f z / g z = f z₀ / g z₀ := by
    intro z hz
    have := hU.constant_of_mapsTo hdisc hrc hmaps hz hz₀
    simpa using this
  have hr0 : f z₀ / g z₀ = 1 := by rw [heq]; exact div_self (hgne z₀ hz₀)
  intro z hz
  have hz1 : f z / g z = 1 := by rw [hconst z hz, hr0]
  field_simp [hgne z hz] at hz1
  exact hz1

/-- DLMF 15.12.8: the positive-real-part continuity normalization determines
the `α` branch uniquely (where `α ≠ 0`).

DLMF 15.12.8 *defines* `α = (-2 ln(1 - ((z-1)/(z+1))²))^{1/2}` on the branch
chosen so that `Re α > 0` when `Re((z-1)/(z+1)) > 0`; its content is that this
choice makes `α` well-defined.  We formalize that as uniqueness: on a
preconnected `U` on which the chosen branch is nowhere zero and whose
positivity region is nonempty, any two `Chapter15AlphaBranch U` instances have
the same value on all of `U`.  (Nonvanishing is genuinely required — at a zero
of `α` two continuous square-root branches may cross, so a preconnected `U`
pinched at such a zero admits two distinct branches.)
The DLMF 15.12.8 surface is the definition `Chapter15AlphaBranch` itself; this
is an auxiliary well-definedness (uniqueness) lemma, not a fidelity surface. -/
-- no-dlmf: uniqueness of the 15.12.8 branch; the definition is `Chapter15AlphaBranch`
theorem hypergeometric_15_12_8_alpha {U : Set ℂ} (hU : IsPreconnected U)
    (A A' : Chapter15AlphaBranch U)
    (hne : ∀ z ∈ U, A.value z ≠ 0)
    (hpos : ∃ z ∈ U, 0 < ((z - 1) / (z + 1)).re) :
    Set.EqOn A.value A'.value U := by
  obtain ⟨z₀, hz₀U, hz₀pos⟩ := hpos
  have hpow : ∀ z ∈ U, A.value z ^ 2 = A'.value z ^ 2 := by
    intro z hz; rw [A.sq_eq z hz, A'.sq_eq z hz]
  have hne' : ∀ z ∈ U, A'.value z ≠ 0 := by
    intro z hz h0
    exact hne z hz ((pow_eq_zero_iff (two_ne_zero)).mp (by rw [hpow z hz, h0]; ring))
  have hposA : 0 < (A.value z₀).re := A.positive_normalization z₀ hz₀U hz₀pos
  have hposA' : 0 < (A'.value z₀).re := A'.positive_normalization z₀ hz₀U hz₀pos
  have heq0 : A.value z₀ = A'.value z₀ := by
    have hfac : (A.value z₀ - A'.value z₀) * (A.value z₀ + A'.value z₀) = 0 := by
      have := hpow z₀ hz₀U; linear_combination this
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have ha : A.value z₀ = -A'.value z₀ := by linear_combination h
      rw [ha, Complex.neg_re] at hposA
      linarith
  exact eqOn_of_pow_eq hU A.continuousOn A'.continuousOn hne' (by norm_num)
    hpow hz₀U heq0

/-- DLMF 15.12.10.
DAG: E-15.12.10.
-/
-- Verified: verified
def chapter15AiryZeta (z : ℂ) : ℂ :=
  chapter15Arccosh (z / 4 - 1)

/-- DLMF 15.12.11: the continuous cube-root branch defining
`β = (−3/2·ζ + 9/4·ln((2+e^ζ)/(2+e^{−ζ})))^{1/3}`, normalized so that `β > 0`
when `ζ > 0`.  This `structure` IS the formalization of the definition 15.12.11
(as `def chapter15AiryZeta` is of 15.12.10); its fields are exactly the defining
cube relation and the branch/sign normalization.
DAG: E-15.12.11.
-/
-- Verified: unverified
structure Chapter15BetaBranch (U : Set ℂ) (zeta : ℂ → ℂ) where
  value : ℂ → ℂ
  continuousOn : ContinuousOn value U
  cube_eq : ∀ z ∈ U,
    value z ^ 3 = -3 / 2 * zeta z + 9 / 4 *
      Complex.log ((2 + Complex.exp (zeta z)) /
        (2 + Complex.exp (-zeta z)))
  positive_normalization : ∀ z ∈ U,
    0 < (zeta z).re → (zeta z).im = 0 →
      0 < (value z).re ∧ (value z).im = 0

/-- DLMF 15.12.11: the real-`ζ` positivity normalization determines the `β`
branch uniquely (where `β ≠ 0`).

DLMF 15.12.11 defines `β` as the continuous cube-root branch of
`-3/2·ζ + 9/4·ln(...)`, normalized by `β > 0` when `ζ > 0`.  A cube root has
three branches, so uniqueness needs continuity plus the real-axis
normalization: on a preconnected `U` on which the chosen branch is nowhere zero
and whose real-positive-`ζ` region is nonempty, any two `Chapter15BetaBranch U`
instances agree on all of `U`.  (At such a point both branches are positive
reals with equal cubes, hence equal; the ratio of the two branches is a
continuous cube root of unity, so constant `= 1` on the preconnected set.  As
in 15.12.8, nonvanishing is genuinely required.)
The DLMF 15.12.11 surface is the definition `Chapter15BetaBranch` itself; this
is an auxiliary well-definedness (uniqueness) lemma, not a fidelity surface. -/
-- no-dlmf: uniqueness of the 15.12.11 branch; the definition is `Chapter15BetaBranch`
theorem hypergeometric_15_12_11_beta {U : Set ℂ} {zeta : ℂ → ℂ}
    (hU : IsPreconnected U)
    (B B' : Chapter15BetaBranch U zeta)
    (hne : ∀ z ∈ U, B.value z ≠ 0)
    (hpos : ∃ z ∈ U, 0 < (zeta z).re ∧ (zeta z).im = 0) :
    Set.EqOn B.value B'.value U := by
  obtain ⟨z₀, hz₀U, hz₀re, hz₀im⟩ := hpos
  have hpow : ∀ z ∈ U, B.value z ^ 3 = B'.value z ^ 3 := by
    intro z hz; rw [B.cube_eq z hz, B'.cube_eq z hz]
  have hne' : ∀ z ∈ U, B'.value z ≠ 0 := by
    intro z hz h0
    exact hne z hz ((pow_eq_zero_iff (three_ne_zero)).mp (by rw [hpow z hz, h0]; ring))
  obtain ⟨_, hBim⟩ := B.positive_normalization z₀ hz₀U hz₀re hz₀im
  obtain ⟨_, hB'im⟩ := B'.positive_normalization z₀ hz₀U hz₀re hz₀im
  have heq0 : B.value z₀ = B'.value z₀ := by
    have hae : B.value z₀ = ((B.value z₀).re : ℂ) := by
      apply Complex.ext <;> simp [hBim]
    have hbe : B'.value z₀ = ((B'.value z₀).re : ℂ) := by
      apply Complex.ext <;> simp [hB'im]
    have hcube : (((B.value z₀).re : ℂ)) ^ 3 = (((B'.value z₀).re : ℂ)) ^ 3 := by
      rw [← hae, ← hbe]; exact hpow z₀ hz₀U
    have hx3 : (B.value z₀).re ^ 3 = (B'.value z₀).re ^ 3 := by exact_mod_cast hcube
    have hxy : (B.value z₀).re = (B'.value z₀).re :=
      (Odd.strictMono_pow (by decide : Odd 3)).injective hx3
    rw [hae, hbe, hxy]
  exact eqOn_of_pow_eq hU B.continuousOn B'.continuousOn hne' (by norm_num)
    hpow hz₀U heq0

/-- A logarithm value of `x`, used to keep all powers in 15.12.13 on their
jointly selected branches. -/
structure LogValue (x : ℂ) where
  value : ℂ
  exp_value : Complex.exp value = x

-- no-dlmf: shared four-factor product shape of 15.12.13; the DLMF surfaces are
-- `chapter15G0` and `Chapter15G0Branch.value`, both defined through it
/-- The common four-factor branch-power product of DLMF 15.12.13, as a function
of the four selected logarithm values. -/
def chapter15G0Product (a b c l2 l1 lz ls : ℂ) : ℂ :=
  Complex.exp ((c - b - 1 / 2) * l2) *
    Complex.exp ((a - c + 1 / 2) * l1) *
    Complex.exp ((-a + 1 / 2) * lz) *
    Complex.exp ((1 / 2) * ls)

/-- DLMF 15.12.13 for either simultaneous sign. -/
-- DAG: E-15.12.13.
-- Verified: unverified
def chapter15G0 (a b c z zeta beta : ℂ) (sgn : ℂ)
    (L2 : LogValue (2 + Complex.exp (sgn * zeta)))
    (L1 : LogValue (1 + Complex.exp (sgn * zeta)))
    (Lz : LogValue (z - 1 - Complex.exp (sgn * zeta)))
    (Ls : LogValue (beta /
      (Complex.exp zeta - Complex.exp (-zeta)))) : ℂ :=
  chapter15G0Product a b c L2.value L1.value Lz.value Ls.value

-- no-dlmf: rfl tag-carrier over chapter15G0's own body; the faithful 15.12.13 surface is the def chapter15G0
/-- `chapter15G0` unfolded to its defining product of branch-explicit powers
(a pure `rfl` restatement of its own body); see `chapter15G0` for the
DLMF 15.12.13 surface.
DAG: E-15.12.13.
-/
theorem hypergeometric_15_12_13_G0 (a b c z zeta beta sgn : ℂ)
    (L2 : LogValue (2 + Complex.exp (sgn * zeta)))
    (L1 : LogValue (1 + Complex.exp (sgn * zeta)))
    (Lz : LogValue (z - 1 - Complex.exp (sgn * zeta)))
    (Ls : LogValue (beta /
      (Complex.exp zeta - Complex.exp (-zeta)))) :
    chapter15G0 a b c z zeta beta sgn L2 L1 Lz Ls =
      Complex.exp ((c - b - 1 / 2) * L2.value) *
        Complex.exp ((a - c + 1 / 2) * L1.value) *
        Complex.exp ((-a + 1 / 2) * Lz.value) *
        Complex.exp ((1 / 2) * Ls.value) :=
  rfl

/-- DLMF 15.12.12: the even and odd coefficient combinations of `G₀(±β)`.
DAG: E-15.12.12.
-/
-- Verified: unverified
def chapter15AiryCoefficients (beta Gplus Gminus : ℂ) : ℂ × ℂ :=
  ((Gplus + Gminus) / 2, (Gplus - Gminus) / (2 * beta))

/-! ### Comparison functions and uniform approximations -/

/-- Complex modified Bessel `I_ν`, expressed as its entire `₀F₁` parent. -/
def complexModifiedBesselI (nu z : ℂ) : ℂ :=
  (z / 2) ^ nu / Complex.Gamma (nu + 1) *
    pFq (![] : Fin 0 → ℂ) ![nu + 1] (z ^ 2 / 4)

/-- The right side of 15.12.5 after replacing its two displayed `O(λ⁻²)`
terms by named remainder values.

DLMF 15.12.5. -/
-- Scope: `r0`, `r1` are the two O(λ⁻²) remainder slots of the display; the
-- asymptotic conditions binding them are stated by the tagged theorem that
-- consumes this carrier, not by this expression.
-- DAG: E-15.12.5.
-- Verified: unverified
def chapter15BesselApproximation
    (a b c z zeta lam r0 r1 : ℂ) : ℂ :=
  let L := lam + a / 2 - b / 2
  2 ^ ((a + b - 1) / 2) *
    (z + 1) ^ ((c - a - b - 1) / 2) / (z - 1) ^ (c / 2) *
    (zeta * Complex.sinh zeta) ^ (1 / 2 : ℂ) * L ^ (1 - c) *
    (complexModifiedBesselI (c - 1) (L * zeta) * (1 + r0) +
      complexModifiedBesselI (c - 2) (L * zeta) / (2 * lam + a - b) *
        ((c - 1 / 2) * (c - 3 / 2) *
            (1 / zeta - Complex.cosh zeta / Complex.sinh zeta) +
          1 / 2 * (2 * c - a - b - 1) * (a + b - 1) *
            (Complex.sinh (zeta / 2) / Complex.cosh (zeta / 2)) + r1))

/-- DLMF 15.12.5 with both uniform `O(λ⁻²)` remainders explicit.
DAG: E-15.12.5.
Numerical: N/A (numerical-pending)
Verified: unverified
-/
theorem hypergeometric_15_12_5_bessel_uniform
    (a b c z : ℂ) (δ : ℝ) (_hδ : 0 < δ)
    (_hz1 : z ≠ 1) (_hz : |Complex.arg (z - 1)| < Real.pi) :
    ∃ r0 r1 : ℂ → ℂ,
      IsBigO (sectorAtInfinity δ) r0 (fun lam : ℂ => lam⁻¹ ^ 2) ∧
      IsBigO (sectorAtInfinity δ) r1 (fun lam : ℂ => lam⁻¹ ^ 2) ∧
      ∀ᶠ lam in sectorAtInfinity δ,
        principalOlver (a + lam) (b - lam) c (1 / 2 - z / 2) =
          chapter15BesselApproximation a b c z (chapter15Arccosh z)
            lam (r0 lam) (r1 lam) := by
  -- PARKED[M]: awaits M-comparison-ode-uniform
  sorry

/-- Complex parabolic-cylinder `U(a,z)` in the even/odd Kummer basis, with
the standard DLMF normalization at zero. -/
def complexParabolicCylinderU (a z : ℂ) : ℂ :=
  let even := Complex.exp (-z ^ 2 / 4) *
    kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2)
  let odd := z * Complex.exp (-z ^ 2 / 4) *
    kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2)
  ((Real.sqrt Real.pi : ℝ) : ℂ) * 2 ^ (-1 / 4 - a / 2) /
      Complex.Gamma (3 / 4 + a / 2) * even -
    ((Real.sqrt Real.pi : ℝ) : ℂ) * 2 ^ (1 / 4 - a / 2) /
      Complex.Gamma (1 / 4 + a / 2) * odd

/-- The right side of 15.12.7 with its two `O(λ⁻¹)` terms named.

DLMF 15.12.7. -/
-- Scope: `alpha` is DLMF's α(z) (see `Chapter15AlphaBranch`) and `r0`, `r1`
-- are the O(λ⁻¹) remainder slots; the binding asymptotic conditions live in
-- the tagged theorem that consumes this carrier.
-- DAG: E-15.12.7.
-- Verified: unverified
def chapter15ParabolicCylinderApproximation
    (a b c z alpha lam r0 r1 : ℂ) : ℂ :=
  let common := (1 + z) ^ (c - a - b) * z ^ (1 - c) *
    (alpha / (z - 1)) ^ (1 - a)
  2 ^ (b - c + 1 / 2) * ((z + 1) / (2 * z ^ (1 / 2 : ℂ))) ^ lam *
    (lam ^ (a / 2) *
        complexParabolicCylinderU (a - 1 / 2)
          (-alpha * lam ^ (1 / 2 : ℂ)) * (common + r0) +
      lam ^ ((a - 1) / 2) / alpha *
        complexParabolicCylinderU (a - 3 / 2)
          (-alpha * lam ^ (1 / 2 : ℂ)) *
          (common - 2 ^ (c - b - 1 / 2) *
            (alpha / (z - 1)) ^ a + r1))

/-- DLMF 15.12.7 with a continuous `α` branch and both `O(λ⁻¹)` remainders.
DAG: E-15.12.7.
Numerical: N/A (numerical-pending)
Verified: unverified
-/
theorem hypergeometric_15_12_7_parabolic_cylinder
    (U : Set ℂ) (hU : IsPreconnected U) (A : Chapter15AlphaBranch U)
    (a b c z : ℂ) (hzU : z ∈ U) (δ : ℝ) (_hδ : 0 < δ)
    (_hz0 : z ≠ 0) (_hz1 : z ≠ 1)
    (hne : ∀ w ∈ U, A.value w ≠ 0)
    (hpos : ∃ w ∈ U, 0 < ((w - 1) / (w + 1)).re)
    (_hz : |Complex.arg z| < Real.pi) :
    ∃ r0 r1 : ℂ → ℂ,
      IsBigO (sectorAtInfinity δ) r0 (fun lam : ℂ => lam⁻¹) ∧
      IsBigO (sectorAtInfinity δ) r1 (fun lam : ℂ => lam⁻¹) ∧
      ∀ᶠ lam in sectorAtInfinity δ,
        principalGauss a (b - lam) (c + lam) (-z) =
          chapter15ParabolicCylinderApproximation a b c z (A.value z)
            lam (r0 lam) (r1 lam) := by
  -- PARKED[M]: awaits M-comparison-ode-uniform
  sorry

/-- Complex Airy `Ai`, represented by its two entire `₀F₁` series. -/
def complexAiryAi (z : ℂ) : ℂ :=
  1 / (3 ^ (2 / 3 : ℂ) * Complex.Gamma (2 / 3)) *
      pFq (![] : Fin 0 → ℂ) ![(2 / 3 : ℂ)] (z ^ 3 / 9) -
    z / (3 ^ (1 / 3 : ℂ) * Complex.Gamma (1 / 3)) *
      pFq (![] : Fin 0 → ℂ) ![(4 / 3 : ℂ)] (z ^ 3 / 9)

/-- The derivative `Ai'` appearing in 15.12.9. -/
def complexAiryAiPrime (z : ℂ) : ℂ := deriv complexAiryAi z

/-- A jointly continuous, principal-value–normalized choice of the four
logarithms entering `G₀(sgn·β)` in 15.12.13, tying every branch to the
already-fixed `ζ` and `β` branches.

An unconstrained `exp`-inverse (as `LogValue` alone provides) leaves each
logarithm free up to an independent `2πi`-shift, so the bare existential
`∃ L2 L1 Lz Ls, G = chapter15G0 …` ranged over a whole `2πiℤ`-lattice of
values of `G₀` rather than the single DLMF-intended one. Requiring the four
log functions to be `ContinuousOn U` and to reduce to their principal values
on the real-`ζ`, real-`β` locus pins each branch uniquely (mirroring the
continuity + real-axis normalization used for `Chapter15AlphaBranch` and
`Chapter15BetaBranch`), ruling out those spurious shifts.

The product formula itself is `chapter15G0` (tag carrier
`hypergeometric_15_12_13_G0`); this structure is the branch datum pinning its
four logarithms. -/
-- no-dlmf: branch certificate for the 15.12.13 product; the display is carried
-- by `chapter15G0` / `hypergeometric_15_12_13_G0`
-- Verified: unverified
structure Chapter15G0Branch (U : Set ℂ) (zeta beta : ℂ → ℂ) (sgn : ℂ) where
  L2 : ℂ → ℂ
  L1 : ℂ → ℂ
  Lz : ℂ → ℂ
  Ls : ℂ → ℂ
  exp_L2 : ∀ z ∈ U, Complex.exp (L2 z) = 2 + Complex.exp (sgn * zeta z)
  exp_L1 : ∀ z ∈ U, Complex.exp (L1 z) = 1 + Complex.exp (sgn * zeta z)
  exp_Lz : ∀ z ∈ U, Complex.exp (Lz z) = z - 1 - Complex.exp (sgn * zeta z)
  exp_Ls : ∀ z ∈ U,
    Complex.exp (Ls z) = beta z / (Complex.exp (zeta z) - Complex.exp (-zeta z))
  continuousOn_L2 : ContinuousOn L2 U
  continuousOn_L1 : ContinuousOn L1 U
  continuousOn_Lz : ContinuousOn Lz U
  continuousOn_Ls : ContinuousOn Ls U
  principal_normalization : ∀ z ∈ U,
    (zeta z).im = 0 → 0 < (zeta z).re → (beta z).im = 0 → 0 < (beta z).re →
      L2 z = Complex.log (2 + Complex.exp (sgn * zeta z)) ∧
      L1 z = Complex.log (1 + Complex.exp (sgn * zeta z)) ∧
      Lz z = Complex.log (z - 1 - Complex.exp (sgn * zeta z)) ∧
      Ls z =
        Complex.log (beta z / (Complex.exp (zeta z) - Complex.exp (-zeta z)))

-- no-dlmf: application of the 15.12.13 branch datum
/-- The value `G₀(sgn·β)` of 15.12.13 assembled from a pinned
`Chapter15G0Branch`, in the shape of `chapter15G0`. -/
-- Verified: unverified
def Chapter15G0Branch.value {U : Set ℂ} {zeta beta : ℂ → ℂ} {sgn : ℂ}
    (Gb : Chapter15G0Branch U zeta beta sgn) (a b c z : ℂ) : ℂ :=
  chapter15G0Product a b c (Gb.L2 z) (Gb.L1 z) (Gb.Lz z) (Gb.Ls z)

-- no-dlmf: sector bookkeeping for the 15.12.9 regime
/-- Infinity in the narrower Airy sector `|arg λ| ≤ π/2 - δ`; this is
`sectorAtInfinity` at the shifted aperture `π - (π/2 + δ) = π/2 - δ`. -/
abbrev airySectorAtInfinity (δ : ℝ) : Filter ℂ :=
  sectorAtInfinity (Real.pi / 2 + δ)

/-- The right side of 15.12.9 with its two `O(λ⁻¹)` terms named.

DLMF 15.12.9. -/
-- DAG: E-15.12.9.
-- Verified: unverified
def chapter15AiryApproximation
    (a c beta a0 a1 lam r0 r1 : ℂ) : ℂ :=
  let xminus := Complex.exp (-2 * Real.pi * Complex.I / 3) *
    lam ^ (2 / 3 : ℂ) * beta ^ 2
  let xplus := Complex.exp (2 * Real.pi * Complex.I / 3) *
    lam ^ (2 / 3 : ℂ) * beta ^ 2
  lam ^ (-1 / 3 : ℂ) *
      (Complex.exp (Real.pi * Complex.I * (a - c + lam + 1 / 3)) *
          complexAiryAi xminus +
        Complex.exp (Real.pi * Complex.I * (c - a - lam - 1 / 3)) *
          complexAiryAi xplus) * (a0 + r0) +
    lam ^ (-2 / 3 : ℂ) *
      (Complex.exp (Real.pi * Complex.I * (a - c + lam + 2 / 3)) *
          complexAiryAiPrime xminus +
        Complex.exp (Real.pi * Complex.I * (c - a - lam - 2 / 3)) *
          complexAiryAiPrime xplus) * (a1 + r1)

/-- DLMF 15.12.9 with the continuous `β` branch, the 15.12.12--13
coefficients, and both Airy `O(λ⁻¹)` remainders explicit.
DAG: E-15.12.9.
Numerical: N/A (numerical-pending)
Verified: unverified
-/
theorem hypergeometric_15_12_9_airy_uniform
    (U : Set ℂ)
    (B : Chapter15BetaBranch U chapter15AiryZeta)
    (Gplus : Chapter15G0Branch U chapter15AiryZeta B.value 1)
    (Gminus : Chapter15G0Branch U chapter15AiryZeta B.value (-1))
    (a b c z : ℂ) (hzU : z ∈ U)
    (δ : ℝ) (_hδ : 0 < δ) (_hz0 : z ≠ 0)
    (_hbeta : B.value z ≠ 0)
    (_hz : |Complex.arg z| < Real.pi) :
    ∃ r0 r1 : ℂ → ℂ,
      IsBigO (airySectorAtInfinity δ) r0 (fun lam : ℂ => lam⁻¹) ∧
      IsBigO (airySectorAtInfinity δ) r1 (fun lam : ℂ => lam⁻¹) ∧
      ∀ᶠ lam in airySectorAtInfinity δ,
        (z + 1) ^ (3 * lam / 2) * (2 * lam) ^ (c - 1) *
            principalOlver (a + lam) (b + 2 * lam) c (-z) =
          chapter15AiryApproximation a c (B.value z)
            (chapter15AiryCoefficients (B.value z)
              (Gplus.value a b c z) (Gminus.value a b c z)).1
            (chapter15AiryCoefficients (B.value z)
              (Gplus.value a b c z) (Gminus.value a b c z)).2
            lam (r0 lam) (r1 lam) := by
  -- PARKED[M]: awaits M-comparison-ode-uniform
  sorry

end

end FLMF.Hypergeometric
