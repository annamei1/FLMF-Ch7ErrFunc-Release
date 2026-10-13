import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Ch7Definitions
import FLMF.Functions.Fresnel.Basic
import FLMF.Functions.Fresnel.Limit
import FLMF.Functions.Fresnel.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Asymptotic expansions of `erfc`, `f`, `g` (DLMF §7.12)

DLMF §7.12 records the large-argument asymptotic expansions, with explicit
remainder integrals, of the complementary error function `erfc` and of the
Fresnel auxiliary functions `f`, `g` (DLMF 7.2.10, 7.2.11):

  `f(z) = (1/2 − S(z)) cos(πz²/2) − (1/2 − C(z)) sin(πz²/2)`
  `g(z) = (1/2 − C(z)) cos(πz²/2) + (1/2 − S(z)) sin(πz²/2)`,

where `C = fresnelC`, `S = fresnelS`.  FLMF's `erfc`, `fresnelC`, `fresnelS`
are REAL-valued, so we state the real-argument (`x → +∞`, `ph z = 0`)
specializations of the §7.12 equations, which all lie inside the validity
sectors `|ph z| ≤ π/2 − δ` (7.12.3) and `|ph z| < π/4` (7.12.6, 7.12.7).

The Pochhammer symbol `(1/2)_m = (1/2)(3/2)…((2m−1)/2)` is written inline via
`Real.Gamma` as `Gamma(1/2 + m) / Gamma(1/2)`, since no chapter-7 helper exists.

To keep the remainder honest, the `n`-term remainders `Rⁿᶠ`, `Rⁿᵍ` are defined
as the structural defect `f − (truncated sum)` and `g − (truncated sum)`; the
content of 7.12.6 / 7.12.7 is then the convergent-integral representation of
those defects (not a definitional `rfl`).

Main statement surfaces (all `:= by sorry`, statement-faithful):

* `erf_7_12_2` — full Poincaré asymptotic expansion of `f` (remainder form, all `n`).
* `erf_7_12_3` — full Poincaré asymptotic expansion of `g` (remainder form, all `n`).
* `erf_7_12_4` — real (`no-dlmf`) exact `n`-term truncation of `f` with remainder `Rⁿᶠ`.
* `erf_7_12_5` — real (`no-dlmf`) exact `n`-term truncation of `g` with remainder `Rⁿᵍ`.
* `erf_7_12_6` — integral representation of the `f`-remainder `Rⁿᶠ(x)`.
* `erf_7_12_7` — integral representation of the `g`-remainder `Rⁿᵍ(x)`.

The canonical (complex) carriers of the 7.12.6/7.12.7 remainder integrals are the
defs `cremFInt`/`cremGInt` (complex `z`, DLMF sector `|ph z| < π/4`); the real
`remF`/`remG` are their restriction to the positive real axis (`cremFInt_ofReal`,
`cremGInt_ofReal`) and are `no-dlmf` twins.

The faithful complex-domain surfaces of 7.12.4/7.12.5 are `erf_7_12_4_complex`
(sector `|ph z| ≤ π/2 − δ`) and `erf_7_12_5_complex` (sector `|ph z| < π/4`);
these use complex remainders `cremF`/`cremG` defined structurally (as DLMF's own
equations define `Rₙ`), proven directly — the real `remF`/`remG` above instead
implement the narrower §7.12.6/§7.12.7 integral formula for the remainder.
-/

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set

-- The Fresnel auxiliary functions `f`, `g` (DLMF 7.2.10/7.2.11) are defined in
-- `FLMF.Functions.Error.Ch7Definitions` as `fresnelAuxF` / `fresnelAuxG`; reuse them.

/-- The Pochhammer symbol `(1/2)_m = Γ(1/2 + m) / Γ(1/2)` as a real number. -/
noncomputable def pochHalf (m : ℕ) : ℝ := Real.Gamma (1 / 2 + m) / Real.Gamma (1 / 2)

-- no-dlmf: support def (truncated 7.12.4 sum); display surfaced at `erf_7_12_4_dlmf`
/-- The `n`-term truncation of the `f`-series (DLMF 7.12.4):
`(1/(πx)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m} / (πx²/2)^{2m}`.

-/
noncomputable def truncF (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (Real.pi * x)) *
    ∑ m ∈ Finset.range n,
      ((-1) ^ m * pochHalf (2 * m)) / (Real.pi * x ^ 2 / 2) ^ (2 * m)

-- no-dlmf: support def (truncated 7.12.5 sum); display surfaced at `erf_7_12_5_complex`
/-- The `n`-term truncation of the `g`-series (DLMF 7.12.5):
`(1/(πx)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m+1} / (πx²/2)^{2m+1}`.

-/
noncomputable def truncG (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (Real.pi * x)) *
    ∑ m ∈ Finset.range n,
      ((-1) ^ m * pochHalf (2 * m + 1)) / (Real.pi * x ^ 2 / 2) ^ (2 * m + 1)

-- no-dlmf: real/narrowed twin of DLMF 7.12.x; canonical surface is cremFInt/cremGInt
/-- The `f`-remainder `Rⁿᶠ(x)` on the positive real axis (`ph z = 0`), DEFINED by its
integral representation: `Rⁿᶠ(x) = (−1)ⁿ/(π√2) ∫₀^∞ e^{−πx²t/2} t^{2n−1/2}/(t²+1) dt`.
Defining the remainder by this convergent integral is what makes the truncation identity
`erf_7_12_4` (`f = truncF + Rⁿᶠ`) a genuine, non-vacuous theorem.

This is the real restriction of the complex carrier `cremFInt` (they agree on the
positive real axis by `cremFInt_ofReal`); it is kept because the whole real §7.12
development (`erf_7_12_4`, the `_kit_remF_step` recursion) is stated over `ℝ`. -/
noncomputable def remF (n : ℕ) (x : ℝ) : ℝ :=
  ((-1) ^ n / (Real.pi * Real.sqrt 2)) *
    ∫ t in Ioi (0 : ℝ),
      Real.exp (-Real.pi * x ^ 2 * t / 2) * t ^ ((2 * n : ℝ) - 1 / 2) / (t ^ 2 + 1)

-- no-dlmf: real/narrowed twin of DLMF 7.12.x; canonical surface is cremFInt/cremGInt
/-- The `g`-remainder `Rⁿᵍ(x)` on the positive real axis (`ph z = 0`), DEFINED by its
integral representation: `Rⁿᵍ(x) = (−1)ⁿ/(π√2) ∫₀^∞ e^{−πx²t/2} t^{2n+1/2}/(t²+1) dt`.
Defining the remainder by this convergent integral is what makes the truncation identity
`erf_7_12_5` (`g = truncG + Rⁿᵍ`) a genuine, non-vacuous theorem.

This is the real restriction of the complex carrier `cremGInt` (they agree on the
positive real axis by `cremGInt_ofReal`); it is kept because the whole real §7.12
development (`erf_7_12_5`, the `_kit_remG_step` recursion) is stated over `ℝ`. -/
noncomputable def remG (n : ℕ) (x : ℝ) : ℝ :=
  ((-1) ^ n / (Real.pi * Real.sqrt 2)) *
    ∫ t in Ioi (0 : ℝ),
      Real.exp (-Real.pi * x ^ 2 * t / 2) * t ^ ((2 * n : ℝ) + 1 / 2) / (t ^ 2 + 1)

/-- The `f`-remainder `Rₙ^{(f)}(z)` for COMPLEX `z`, defined by DLMF's own remainder
integral: for `n = 0, 1, 2, …` and `|ph z| < π/4`,

`Rₙ^{(f)}(z) = ((−1)ⁿ/(π√2)) ∫₀^∞ e^{−πz²t/2} t^{2n−1/2}/(t²+1) dt`,

the integral being taken along the positive real `t`-axis exactly as DLMF writes it,
with `t^{2n−1/2}` the principal complex power `(t : ℂ) ^ ((2n − 1/2 : ℝ) : ℂ)` (equal to
the real `rpow` for `t > 0`).

Domain guard. DLMF §7.12(ii) states this remainder integral only for the sector
`|ph z| < π/4`, and that is exactly the hypothesis carried by the `if`: outside the
sector the definition takes the explicit junk value `0`. The guard is not cosmetic.
Without it the unguarded integral would still converge on the *mirror* cone
`|ph z − π| < π/4` (there too `Re(z²) > 0`, so the exponential still decays) and the
`def` would silently assign values DLMF never defines; on the remaining `z` the
Bochner integral would fall back on its own junk `0`. Guarding makes the
out-of-domain value a declared `0` everywhere instead. Use `cremFInt_of_mem` to
unfold inside the sector.

Along the positive real axis this agrees with the real `remF` (`cremFInt_ofReal`).

DLMF 7.12.6. -/
-- DAG: E-7.12.6.
-- Verified: verified (tier2)
noncomputable def cremFInt (n : ℕ) (z : ℂ) : ℂ :=
  if |z.arg| < Real.pi / 4 then
    ((-1) ^ n / ((Real.pi : ℂ) * (Real.sqrt 2 : ℝ))) *
      ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) *
            (t : ℂ) ^ (((2 * n : ℝ) - 1 / 2 : ℝ) : ℂ) / ((t : ℂ) ^ 2 + 1)
  else 0

-- no-dlmf: unguard lemma — `cremFInt` on its declared DLMF sector `|ph z| < π/4`
/-- Inside DLMF's sector `|ph z| < π/4` the guard of `cremFInt` opens up to the
7.12.6 remainder integral. -/
theorem cremFInt_of_mem {z : ℂ} (hz : |z.arg| < Real.pi / 4) (n : ℕ) :
    cremFInt n z =
      ((-1) ^ n / ((Real.pi : ℂ) * (Real.sqrt 2 : ℝ))) *
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) *
              (t : ℂ) ^ (((2 * n : ℝ) - 1 / 2 : ℝ) : ℂ) / ((t : ℂ) ^ 2 + 1) :=
  if_pos hz

/-- The `g`-remainder `Rₙ^{(g)}(z)` for COMPLEX `z`, defined by DLMF's own remainder
integral: for `n = 0, 1, 2, …` and `|ph z| < π/4`,

`Rₙ^{(g)}(z) = ((−1)ⁿ/(π√2)) ∫₀^∞ e^{−πz²t/2} t^{2n+1/2}/(t²+1) dt`,

the integral being taken along the positive real `t`-axis exactly as DLMF writes it,
with `t^{2n+1/2}` the principal complex power `(t : ℂ) ^ ((2n + 1/2 : ℝ) : ℂ)` (equal to
the real `rpow` for `t > 0`).

Domain guard. DLMF §7.12(ii) states this remainder integral only for the sector
`|ph z| < π/4`, and that is exactly the hypothesis carried by the `if`: outside the
sector the definition takes the explicit junk value `0`. The guard is not cosmetic.
Without it the unguarded integral would still converge on the *mirror* cone
`|ph z − π| < π/4` (there too `Re(z²) > 0`, so the exponential still decays) and the
`def` would silently assign values DLMF never defines; on the remaining `z` the
Bochner integral would fall back on its own junk `0`. Guarding makes the
out-of-domain value a declared `0` everywhere instead. Use `cremGInt_of_mem` to
unfold inside the sector.

Along the positive real axis this agrees with the real `remG` (`cremGInt_ofReal`).

DLMF 7.12.7. -/
-- DAG: E-7.12.7.
-- Verified: verified (tier2)
noncomputable def cremGInt (n : ℕ) (z : ℂ) : ℂ :=
  if |z.arg| < Real.pi / 4 then
    ((-1) ^ n / ((Real.pi : ℂ) * (Real.sqrt 2 : ℝ))) *
      ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) *
            (t : ℂ) ^ (((2 * n : ℝ) + 1 / 2 : ℝ) : ℂ) / ((t : ℂ) ^ 2 + 1)
  else 0

-- no-dlmf: unguard lemma — `cremGInt` on its declared DLMF sector `|ph z| < π/4`
/-- Inside DLMF's sector `|ph z| < π/4` the guard of `cremGInt` opens up to the
7.12.7 remainder integral. -/
theorem cremGInt_of_mem {z : ℂ} (hz : |z.arg| < Real.pi / 4) (n : ℕ) :
    cremGInt n z =
      ((-1) ^ n / ((Real.pi : ℂ) * (Real.sqrt 2 : ℝ))) *
        ∫ t in Ioi (0 : ℝ),
          Complex.exp (-(Real.pi : ℂ) * z ^ 2 * (t : ℂ) / 2) *
              (t : ℂ) ^ (((2 * n : ℝ) + 1 / 2 : ℝ) : ℂ) / ((t : ℂ) ^ 2 + 1) :=
  if_pos hz

-- no-dlmf: agreement lemma tying the real twin `remF` to the canonical `cremFInt`
/-- On the positive real axis (`ph z = 0`) the complex remainder integral `cremFInt`
restricts to the real one: `Rₙ^{(f)}(x) = remF n x`. -/
theorem cremFInt_ofReal (n : ℕ) {x : ℝ} (hx : 0 < x) :
    cremFInt n (x : ℂ) = (remF n x : ℂ) := by
  have harg : |((x : ℂ)).arg| < Real.pi / 4 := by
    rw [Complex.arg_ofReal_of_nonneg hx.le, abs_zero]
    positivity
  rw [cremFInt_of_mem harg, remF]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  push_cast
  rw [Complex.ofReal_cpow ht0]
  push_cast
  ring

-- no-dlmf: agreement lemma tying the real twin `remG` to the canonical `cremGInt`
/-- On the positive real axis (`ph z = 0`) the complex remainder integral `cremGInt`
restricts to the real one: `Rₙ^{(g)}(x) = remG n x`. -/
theorem cremGInt_ofReal (n : ℕ) {x : ℝ} (hx : 0 < x) :
    cremGInt n (x : ℂ) = (remG n x : ℂ) := by
  have harg : |((x : ℂ)).arg| < Real.pi / 4 := by
    rw [Complex.arg_ofReal_of_nonneg hx.le, abs_zero]
    positivity
  rw [cremGInt_of_mem harg, remG]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  push_cast
  rw [Complex.ofReal_cpow ht0]
  push_cast
  ring

/-- Measurability of the weighted exponential integrand. -/
private lemma _kit_meas_exp_rpow (b s : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      (volume.restrict (Ioi 0)) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

-- no-dlmf: integrability support lemma (Gamma-type integrand), not a DLMF equation
/-- Integrability of the pure Gamma-type integrand `e^{-bt} t^s` on `(0,∞)`. -/
lemma integrableOn_exp_neg_mul_rpow_Ioi (b s : ℝ) (hb : 0 < b) (hs : -1 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) * t ^ s) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs le_rfl hb
  simp only [Real.rpow_one] at h
  exact h.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi

/-- Integrability of the damped integrand `e^{-bt} t^s/(t²+1)` on `(0,∞)`. -/
private lemma _kit_integrable_J (b s : ℝ) (hb : 0 < b) (hs : -1 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-b * t) * t ^ s / (t ^ 2 + 1)) (Ioi 0) := by
  refine ((integrableOn_exp_neg_mul_rpow_Ioi b s hb hs).mono' (_kit_meas_exp_rpow b s) ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hpos : 0 ≤ Real.exp (-b * t) * t ^ s := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self hpos (by nlinarith)

-- no-dlmf: scaled Gamma-integral evaluation, support lemma (not a DLMF equation)
/-- The scaled Gamma integral `∫₀^∞ e^{-bt} t^s dt = (1/b)^{s+1} Γ(s+1)`. -/
lemma integral_exp_neg_mul_rpow_Ioi (b s : ℝ) (hb : 0 < b) (hs : -1 < s) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s
      = (1 / b) ^ (s + 1) * Real.Gamma (s + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < s + 1) hb
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [add_sub_cancel_right, neg_mul]
  exact mul_comm _ _

/-- Two-term split of the damped integral against `t² + 1`. -/
private lemma _kit_J_split (b s : ℝ) (hb : 0 < b) (hs : -1 < s) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ (s + 2) / (t ^ 2 + 1))
      = (1 / b) ^ (s + 1) * Real.Gamma (s + 1)
        - ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s / (t ^ 2 + 1) := by
  have h2 := _kit_integrable_J b (s + 2) hb (by linarith)
  have h0 := _kit_integrable_J b s hb hs
  have hadd : (∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ (s + 2) / (t ^ 2 + 1))
      + (∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      = ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s := by
    rw [← integral_add h2 h0]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hr : t ^ (s + 2) = t ^ s * t ^ 2 := by
      rw [Real.rpow_add ht0, Real.rpow_two]
    rw [hr]
    have hne : t ^ 2 + 1 ≠ 0 := by positivity
    field_simp
  rw [integral_exp_neg_mul_rpow_Ioi b s hb hs] at hadd
  linarith

/-- Differentiation in the rate `b` of the damped integral. -/
private lemma _kit_J_hasDerivAt (s : ℝ) (hs : -1 < s) {b₀ : ℝ} (hb : 0 < b₀) :
    HasDerivAt (fun b => ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      (-∫ t in Ioi (0 : ℝ), Real.exp (-b₀ * t) * t ^ (s + 1) / (t ^ 2 + 1)) b₀ := by
  have hball : Metric.ball b₀ (b₀ / 2) ∈ 𝓝 b₀ := Metric.ball_mem_nhds _ (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioi 0))
      (F := fun b t => Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      (F' := fun b t => -(t * (Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))))
      (bound := fun t => Real.exp (-(b₀ / 2) * t) * t ^ (s + 1) / (t ^ 2 + 1))
      hball
      (Eventually.of_forall fun b => _kit_meas_exp_rpow b s)
      (_kit_integrable_J b₀ s hb hs)
      (by apply Measurable.aestronglyMeasurable; fun_prop)
      ?_ (_kit_integrable_J (b₀ / 2) (s + 1) (by linarith) (by linarith)) ?_
  · have hval : (∫ t in Ioi (0 : ℝ), -(t * (Real.exp (-b₀ * t) * t ^ s / (t ^ 2 + 1))))
        = -∫ t in Ioi (0 : ℝ), Real.exp (-b₀ * t) * t ^ (s + 1) / (t ^ 2 + 1) := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := ht
      rw [Real.rpow_add_one (ne_of_gt ht0)]
      ring
    rw [← hval]
    exact key.2
  · -- bound
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro b hbmem
    have ht0 : (0 : ℝ) < t := ht
    have hb2 : b₀ / 2 ≤ b := by
      have h := Metric.mem_ball.mp hbmem
      rw [Real.dist_eq] at h
      have h' := abs_lt.mp h
      linarith [h'.1]
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    calc t * (Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
        = Real.exp (-b * t) * (t ^ s * t) / (t ^ 2 + 1) := by ring
      _ ≤ Real.exp (-(b₀ / 2) * t) * (t ^ s * t) / (t ^ 2 + 1) := by
          gcongr
      _ = Real.exp (-(b₀ / 2) * t) * t ^ (s + 1) / (t ^ 2 + 1) := by
          rw [Real.rpow_add_one (ne_of_gt ht0)]
  · -- differentiability
    filter_upwards with t
    intro b _
    have h1 : HasDerivAt (fun b : ℝ => -b * t) (-t) b := by
      simpa using ((hasDerivAt_id b).neg.mul_const t)
    have h2 := (h1.exp.mul_const (t ^ s)).div_const (t ^ 2 + 1)
    convert h2 using 1
    ring

/-- The damped integral tends to `0` as the rate `b → ∞`. -/
private lemma _kit_J_tendsto_zero (s : ℝ) (hs : -1 < s) :
    Tendsto (fun b => ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      atTop (𝓝 0) := by
  have hbi : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ s / (t ^ 2 + 1)) (Ioi 0) := by
    have h := _kit_integrable_J 1 s one_pos hs
    simpa using h
  have key := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi 0)) (l := atTop)
      (F := fun (b : ℝ) t => Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
      (f := fun _ => (0 : ℝ))
      (fun t => Real.exp (-t) * t ^ s / (t ^ 2 + 1))
      (Eventually.of_forall fun b => _kit_meas_exp_rpow b s)
      ?_ hbi ?_
  · simpa using key
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-b * t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have h1 : Tendsto (fun b : ℝ => -b * t) atTop atBot := by
      have h2 : Tendsto (fun b : ℝ => b * t) atTop atTop :=
        Tendsto.atTop_mul_const ht0 tendsto_id
      have h3 := tendsto_neg_atTop_atBot.comp h2
      refine h3.congr fun b => ?_
      simp [neg_mul]
    have h4 := Real.tendsto_exp_atBot.comp h1
    have h5 := (h4.mul_const (t ^ s)).div_const (t ^ 2 + 1)
    simpa using h5

/-- Derivative of the Fresnel phase `y ↦ π y²/2`. -/
private lemma _kit_theta_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.pi * y ^ 2 / 2) (Real.pi * x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul Real.pi).div_const 2
  convert h using 1
  push_cast
  ring

-- no-dlmf: HasDerivAt support form of 7.10.4 (display form in Ch7Derivatives)
/-- DLMF 7.10.4, first half: `f′(x) = -π x g(x)` (as a `HasDerivAt`). -/
lemma fresnelAuxF_hasDerivAt (x : ℝ) :
    HasDerivAt fresnelAuxF (-Real.pi * x * fresnelAuxG x) x := by
  have hθ := _kit_theta_hasDerivAt x
  have hC : HasDerivAt FLMF.Fresnel.fresnelC (Real.cos (Real.pi * x ^ 2 / 2)) x :=
    FLMF.Fresnel.hasDerivAt_fresnelC x
  have hS : HasDerivAt FLMF.Fresnel.fresnelS (Real.sin (Real.pi * x ^ 2 / 2)) x :=
    FLMF.Fresnel.hasDerivAt_fresnelS x
  have h1 := ((hasDerivAt_const x ((1 : ℝ) / 2)).sub hS).mul hθ.cos
  have h2 := ((hasDerivAt_const x ((1 : ℝ) / 2)).sub hC).mul hθ.sin
  have h := h1.sub h2
  unfold fresnelAuxF
  convert h using 1
  unfold fresnelAuxG
  simp only [Pi.sub_apply]
  ring

-- no-dlmf: HasDerivAt support form of 7.10.4 (display form in Ch7Derivatives)
/-- DLMF 7.10.4, second half: `g′(x) = π x f(x) - 1` (as a `HasDerivAt`). -/
lemma fresnelAuxG_hasDerivAt (x : ℝ) :
    HasDerivAt fresnelAuxG (Real.pi * x * fresnelAuxF x - 1) x := by
  have hθ := _kit_theta_hasDerivAt x
  have hC : HasDerivAt FLMF.Fresnel.fresnelC (Real.cos (Real.pi * x ^ 2 / 2)) x :=
    FLMF.Fresnel.hasDerivAt_fresnelC x
  have hS : HasDerivAt FLMF.Fresnel.fresnelS (Real.sin (Real.pi * x ^ 2 / 2)) x :=
    FLMF.Fresnel.hasDerivAt_fresnelS x
  have h1 := ((hasDerivAt_const x ((1 : ℝ) / 2)).sub hC).mul hθ.cos
  have h2 := ((hasDerivAt_const x ((1 : ℝ) / 2)).sub hS).mul hθ.sin
  have h := h1.add h2
  unfold fresnelAuxG
  convert h using 1
  unfold fresnelAuxF
  simp only [Pi.sub_apply]
  linear_combination Real.sin_sq_add_cos_sq (Real.pi * x ^ 2 / 2)

/-- The Fresnel auxiliary function `f` tends to `0` at `+∞`. -/
private lemma _kit_fresnelAuxF_tendsto_zero :
    Tendsto fresnelAuxF atTop (𝓝 0) := by
  have hS : Tendsto (fun y => 1 / 2 - FLMF.Fresnel.fresnelS y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := atTop)).sub
      FLMF.Fresnel.tendsto_fresnelS
    simpa using h
  have hC : Tendsto (fun y => 1 / 2 - FLMF.Fresnel.fresnelC y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := atTop)).sub
      FLMF.Fresnel.tendsto_fresnelC
    simpa using h
  refine squeeze_zero_norm (a := fun y => |1 / 2 - FLMF.Fresnel.fresnelS y|
      + |1 / 2 - FLMF.Fresnel.fresnelC y|) (fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold fresnelAuxF
    calc |(1 / 2 - FLMF.Fresnel.fresnelS y) * Real.cos (Real.pi * y ^ 2 / 2)
          - (1 / 2 - FLMF.Fresnel.fresnelC y) * Real.sin (Real.pi * y ^ 2 / 2)|
        ≤ |(1 / 2 - FLMF.Fresnel.fresnelS y) * Real.cos (Real.pi * y ^ 2 / 2)|
          + |(1 / 2 - FLMF.Fresnel.fresnelC y) * Real.sin (Real.pi * y ^ 2 / 2)| :=
          abs_sub _ _
      _ ≤ |1 / 2 - FLMF.Fresnel.fresnelS y| + |1 / 2 - FLMF.Fresnel.fresnelC y| := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  · have h := hS.abs.add hC.abs
    simpa using h

/-- The Fresnel auxiliary function `g` tends to `0` at `+∞`. -/
private lemma _kit_fresnelAuxG_tendsto_zero :
    Tendsto fresnelAuxG atTop (𝓝 0) := by
  have hS : Tendsto (fun y => 1 / 2 - FLMF.Fresnel.fresnelS y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := atTop)).sub
      FLMF.Fresnel.tendsto_fresnelS
    simpa using h
  have hC : Tendsto (fun y => 1 / 2 - FLMF.Fresnel.fresnelC y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := atTop)).sub
      FLMF.Fresnel.tendsto_fresnelC
    simpa using h
  refine squeeze_zero_norm (a := fun y => |1 / 2 - FLMF.Fresnel.fresnelC y|
      + |1 / 2 - FLMF.Fresnel.fresnelS y|) (fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold fresnelAuxG
    calc |(1 / 2 - FLMF.Fresnel.fresnelC y) * Real.cos (Real.pi * y ^ 2 / 2)
          + (1 / 2 - FLMF.Fresnel.fresnelS y) * Real.sin (Real.pi * y ^ 2 / 2)|
        ≤ |(1 / 2 - FLMF.Fresnel.fresnelC y) * Real.cos (Real.pi * y ^ 2 / 2)|
          + |(1 / 2 - FLMF.Fresnel.fresnelS y) * Real.sin (Real.pi * y ^ 2 / 2)| :=
          abs_add_le _ _
      _ ≤ |1 / 2 - FLMF.Fresnel.fresnelC y| + |1 / 2 - FLMF.Fresnel.fresnelS y| := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  · have h := hC.abs.add hS.abs
    simpa using h

/-- `x`-space derivative of the parametric integral `y ↦ ∫₀^∞ e^{-(πy²/2)t} t^s/(t²+1)`. -/
private lemma _kit_K_hasDerivAt (s : ℝ) (hs : -1 < s) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ =>
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1))
      (-Real.pi * x *
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ (s + 1) / (t ^ 2 + 1))
      x := by
  have h1 := _kit_J_hasDerivAt s hs (show (0 : ℝ) < Real.pi * x ^ 2 / 2 by positivity)
  have h2 := h1.comp x (_kit_theta_hasDerivAt x)
  have hfun : ((fun b => ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * t ^ s / (t ^ 2 + 1))
        ∘ (fun y : ℝ => Real.pi * y ^ 2 / 2))
      = fun y : ℝ =>
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1) := rfl
  rw [hfun] at h2
  convert h2 using 1
  ring

/-- The parametric integral `y ↦ ∫₀^∞ e^{-(πy²/2)t} t^s/(t²+1)` vanishes at `+∞`. -/
private lemma _kit_K_tendsto_zero (s : ℝ) (hs : -1 < s) :
    Tendsto (fun y : ℝ =>
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.pi * y ^ 2 / 2) atTop atTop := by
    apply Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    exact Tendsto.const_mul_atTop Real.pi_pos (tendsto_pow_atTop two_ne_zero)
  exact (_kit_J_tendsto_zero s hs).comp h1

-- no-dlmf: ODE-pair/first-integral uniqueness engine, support lemma (not a DLMF equation)
/-- ODE-pair uniqueness: any pair `(F, G)` with `F′ = -πx G`, `G′ = πx F - 1` on `(0,∞)`
that vanishes at `+∞` agrees with `(f, g)` on `(0,∞)` (first-integral argument). -/
lemma fresnelAux_pair_uniqueness {F G : ℝ → ℝ}
    (hFd : ∀ y : ℝ, 0 < y → HasDerivAt F (-Real.pi * y * G y) y)
    (hGd : ∀ y : ℝ, 0 < y → HasDerivAt G (Real.pi * y * F y - 1) y)
    (hF0 : Tendsto F atTop (𝓝 0)) (hG0 : Tendsto G atTop (𝓝 0))
    {x : ℝ} (hx : 0 < x) :
    fresnelAuxF x = F x ∧ fresnelAuxG x = G x := by
  have hφd : ∀ y : ℝ, 0 < y → HasDerivAt
      (fun y => (fresnelAuxF y - F y) ^ 2 + (fresnelAuxG y - G y) ^ 2) 0 y := by
    intro y hy
    have hu := (fresnelAuxF_hasDerivAt y).sub (hFd y hy)
    have hv := (fresnelAuxG_hasDerivAt y).sub (hGd y hy)
    have h := (hu.pow 2).add (hv.pow 2)
    convert h using 1
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hconst : ∀ z, x ≤ z →
      (fresnelAuxF z - F z) ^ 2 + (fresnelAuxG z - G z) ^ 2
        = (fresnelAuxF x - F x) ^ 2 + (fresnelAuxG x - G x) ^ 2 := by
    intro z hz
    have hcont : ContinuousOn
        (fun y => (fresnelAuxF y - F y) ^ 2 + (fresnelAuxG y - G y) ^ 2) (Icc x z) :=
      fun y hy => ((hφd y (lt_of_lt_of_le hx hy.1)).continuousAt).continuousWithinAt
    have hderiv : ∀ y ∈ Ico x z, HasDerivWithinAt
        (fun y => (fresnelAuxF y - F y) ^ 2 + (fresnelAuxG y - G y) ^ 2) 0 (Ici y) y :=
      fun y hy => (hφd y (lt_of_lt_of_le hx hy.1)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv z (right_mem_Icc.mpr hz)
  have hφ0 : Tendsto (fun y => (fresnelAuxF y - F y) ^ 2 + (fresnelAuxG y - G y) ^ 2)
      atTop (𝓝 0) := by
    have h1 := ((_kit_fresnelAuxF_tendsto_zero.sub hF0).pow 2).add
      ((_kit_fresnelAuxG_tendsto_zero.sub hG0).pow 2)
    simpa using h1
  have hφx : (fresnelAuxF x - F x) ^ 2 + (fresnelAuxG x - G x) ^ 2 = 0 := by
    have h1 : Tendsto (fun y => (fresnelAuxF y - F y) ^ 2 + (fresnelAuxG y - G y) ^ 2)
        atTop (𝓝 ((fresnelAuxF x - F x) ^ 2 + (fresnelAuxG x - G x) ^ 2)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop x] with z hz
      exact (hconst z hz).symm
    exact tendsto_nhds_unique h1 hφ0
  constructor
  · have h1 : (fresnelAuxF x - F x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (fresnelAuxF x - F x), sq_nonneg (fresnelAuxG x - G x)]
    have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    linarith
  · have h1 : (fresnelAuxG x - G x) ^ 2 = 0 := by
      nlinarith [sq_nonneg (fresnelAuxF x - F x), sq_nonneg (fresnelAuxG x - G x)]
    have h2 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    linarith

/-- `(1/(π x²/2))^{1/2} = √2/(√π x)` for `x > 0`. -/
private lemma _kit_inv_b_rpow_half {x : ℝ} (hx : 0 < x) :
    (1 / (Real.pi * x ^ 2 / 2)) ^ ((1 : ℝ) / 2)
      = Real.sqrt 2 / (Real.sqrt Real.pi * x) := by
  have hpi := Real.pi_pos
  rw [← Real.sqrt_eq_rpow]
  rw [show 1 / (Real.pi * x ^ 2 / 2) = (Real.sqrt 2 / (Real.sqrt Real.pi * x)) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hpi.le]
    field_simp]
  exact Real.sqrt_sq (by positivity)

-- no-dlmf: kit lemma; DLMF citation is context, not an equation surface
/-- Base case of DLMF 7.12.4: the `n = 0` remainder integral is exactly `f` (DLMF 7.7.10). -/
lemma fresnelAuxF_eq_remF_zero {x : ℝ} (hx : 0 < x) : fresnelAuxF x = remF 0 x := by
  have hpi := Real.pi_pos
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have main := fresnelAux_pair_uniqueness
    (F := fun y : ℝ => 1 / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1))
    (G := fun y : ℝ => 1 / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1))
    ?_ ?_ ?_ ?_ hx
  · refine main.1.trans ?_
    show (1 / (Real.pi * Real.sqrt 2) *
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1))
      = remF 0 x
    rw [remF]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show ((2 : ℝ) * ((0 : ℕ) : ℝ) - 1 / 2) = (-(1 / 2) : ℝ) by norm_num,
      show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  · -- F′ = -πy G
    intro y hy
    have h1 := (_kit_K_hasDerivAt (-(1 / 2)) (by norm_num) hy).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    rw [show ((-(1 / 2) : ℝ) + 1) = ((1 : ℝ) / 2) by norm_num] at h1
    beta_reduce
    convert h1 using 1
    ring
  · -- G′ = πy F - 1
    intro y hy
    have h1 := (_kit_K_hasDerivAt ((1 / 2)) (by norm_num) hy).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    rw [show (((1 / 2) : ℝ) + 1) = ((-(1 / 2) : ℝ) + 2) by norm_num] at h1
    rw [_kit_J_split (Real.pi * y ^ 2 / 2) (-(1 / 2)) (by positivity) (by norm_num)] at h1
    rw [show ((-(1 / 2) : ℝ) + 1) = ((1 : ℝ) / 2) by norm_num] at h1
    rw [Real.Gamma_one_half_eq, _kit_inv_b_rpow_half hy] at h1
    beta_reduce
    convert h1 using 1
    field_simp
    ring
  · -- F → 0
    have h := (_kit_K_tendsto_zero (-(1 / 2)) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    simpa using h
  · -- G → 0
    have h := (_kit_K_tendsto_zero ((1 / 2)) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    simpa using h

-- no-dlmf: kit lemma; DLMF citation is context, not an equation surface
/-- Base case of DLMF 7.12.5: the `n = 0` remainder integral is exactly `g` (DLMF 7.7.11). -/
lemma fresnelAuxG_eq_remG_zero {x : ℝ} (hx : 0 < x) : fresnelAuxG x = remG 0 x := by
  have hpi := Real.pi_pos
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have main := fresnelAux_pair_uniqueness
    (F := fun y : ℝ => 1 / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ (-(1 / 2) : ℝ) / (t ^ 2 + 1))
    (G := fun y : ℝ => 1 / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * y ^ 2 / 2) * t) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1))
    ?_ ?_ ?_ ?_ hx
  · refine main.2.trans ?_
    show (1 / (Real.pi * Real.sqrt 2) *
        ∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ ((1 / 2) : ℝ) / (t ^ 2 + 1))
      = remG 0 x
    rw [remG]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show ((2 : ℝ) * ((0 : ℕ) : ℝ) + 1 / 2) = ((1 / 2) : ℝ) by norm_num,
      show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  · -- F′ = -πy G
    intro y hy
    have h1 := (_kit_K_hasDerivAt (-(1 / 2)) (by norm_num) hy).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    rw [show ((-(1 / 2) : ℝ) + 1) = ((1 : ℝ) / 2) by norm_num] at h1
    beta_reduce
    convert h1 using 1
    ring
  · -- G′ = πy F - 1
    intro y hy
    have h1 := (_kit_K_hasDerivAt ((1 / 2)) (by norm_num) hy).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    rw [show (((1 / 2) : ℝ) + 1) = ((-(1 / 2) : ℝ) + 2) by norm_num] at h1
    rw [_kit_J_split (Real.pi * y ^ 2 / 2) (-(1 / 2)) (by positivity) (by norm_num)] at h1
    rw [show ((-(1 / 2) : ℝ) + 1) = ((1 : ℝ) / 2) by norm_num] at h1
    rw [Real.Gamma_one_half_eq, _kit_inv_b_rpow_half hy] at h1
    beta_reduce
    convert h1 using 1
    field_simp
    ring
  · -- F → 0
    have h := (_kit_K_tendsto_zero (-(1 / 2)) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    simpa using h
  · -- G → 0
    have h := (_kit_K_tendsto_zero ((1 / 2)) (by norm_num)).const_mul
      (1 / (Real.pi * Real.sqrt 2))
    simpa using h

/-- Induction step: peeling one term off the remainder integral. -/
private lemma _kit_remF_step (n : ℕ) {x : ℝ} (hx : 0 < x) :
    remF n x = 1 / (Real.pi * x) *
        (((-1) ^ n * pochHalf (2 * n)) / (Real.pi * x ^ 2 / 2) ^ (2 * n)) + remF (n + 1) x := by
  have hpi := Real.pi_pos
  have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hcast : ∀ m : ℕ, remF m x = (-1 : ℝ) ^ m / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ (2 * (m : ℝ) - 1 / 2) / (t ^ 2 + 1) := by
    intro m
    rw [remF]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  have hsn : (-1 : ℝ) < 2 * (n : ℝ) - 1 / 2 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  have e2 : remF (n + 1) x = (-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ ((2 * (n : ℝ) - 1 / 2) + 2) / (t ^ 2 + 1) := by
    rw [hcast (n + 1)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (2 * (((n + 1) : ℕ) : ℝ) - 1 / 2) = ((2 * (n : ℝ) - 1 / 2) + 2) by push_cast; ring]
  have hγ : (-1 : ℝ) ^ n / (Real.pi * Real.sqrt 2) *
      ((1 / (Real.pi * x ^ 2 / 2)) ^ ((2 * (n : ℝ) - 1 / 2) + 1)
        * Real.Gamma ((2 * (n : ℝ) - 1 / 2) + 1))
      = 1 / (Real.pi * x) *
        (((-1) ^ n * pochHalf (2 * n)) / (Real.pi * x ^ 2 / 2) ^ (2 * n)) := by
    rw [show ((2 * (n : ℝ) - 1 / 2) + 1) = ((2 * n : ℕ) : ℝ) + (1 : ℝ) / 2 by push_cast; ring]
    rw [Real.rpow_add (by positivity : (0 : ℝ) < 1 / (Real.pi * x ^ 2 / 2))]
    rw [Real.rpow_natCast]
    rw [_kit_inv_b_rpow_half hx]
    rw [pochHalf, Real.Gamma_one_half_eq]
    rw [show ((2 * n : ℕ) : ℝ) + (1 : ℝ) / 2 = 1 / 2 + ((2 * n : ℕ) : ℝ) by ring]
    rw [one_div_pow]
    have hbne : (Real.pi * x ^ 2 / 2) ^ (2 * n) ≠ 0 := pow_ne_zero _ (ne_of_gt hb)
    field_simp
  have hsplit := _kit_J_split (Real.pi * x ^ 2 / 2) (2 * (n : ℝ) - 1 / 2) hb hsn
  rw [hcast n, e2, hsplit]
  linear_combination hγ

/-- Induction step for `g`: peeling one term off the remainder integral. -/
private lemma _kit_remG_step (n : ℕ) {x : ℝ} (hx : 0 < x) :
    remG n x = 1 / (Real.pi * x) *
        (((-1) ^ n * pochHalf (2 * n + 1)) / (Real.pi * x ^ 2 / 2) ^ (2 * n + 1))
      + remG (n + 1) x := by
  have hpi := Real.pi_pos
  have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hcast : ∀ m : ℕ, remG m x = (-1 : ℝ) ^ m / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ (2 * (m : ℝ) + 1 / 2) / (t ^ 2 + 1) := by
    intro m
    rw [remG]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  have hsn : (-1 : ℝ) < 2 * (n : ℝ) + 1 / 2 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  have e2 : remG (n + 1) x = (-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ ((2 * (n : ℝ) + 1 / 2) + 2) / (t ^ 2 + 1) := by
    rw [hcast (n + 1)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (2 * (((n + 1) : ℕ) : ℝ) + 1 / 2) = ((2 * (n : ℝ) + 1 / 2) + 2) by push_cast; ring]
  have hγ : (-1 : ℝ) ^ n / (Real.pi * Real.sqrt 2) *
      ((1 / (Real.pi * x ^ 2 / 2)) ^ ((2 * (n : ℝ) + 1 / 2) + 1)
        * Real.Gamma ((2 * (n : ℝ) + 1 / 2) + 1))
      = 1 / (Real.pi * x) *
        (((-1) ^ n * pochHalf (2 * n + 1)) / (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)) := by
    rw [show ((2 * (n : ℝ) + 1 / 2) + 1) = ((2 * n + 1 : ℕ) : ℝ) + (1 : ℝ) / 2 by
      push_cast; ring]
    rw [Real.rpow_add (by positivity : (0 : ℝ) < 1 / (Real.pi * x ^ 2 / 2))]
    rw [Real.rpow_natCast]
    rw [_kit_inv_b_rpow_half hx]
    rw [pochHalf, Real.Gamma_one_half_eq]
    rw [show ((2 * n + 1 : ℕ) : ℝ) + (1 : ℝ) / 2 = 1 / 2 + ((2 * n + 1 : ℕ) : ℝ) by ring]
    rw [one_div_pow]
    have hbne : (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hb)
    field_simp
  have hsplit := _kit_J_split (Real.pi * x ^ 2 / 2) (2 * (n : ℝ) + 1 / 2) hb hsn
  rw [hcast n, e2, hsplit]
  linear_combination hγ

-- no-dlmf: real/narrowed restriction of DLMF 7.12.4; faithful surface is erf_7_12_4_complex
/-- Asymptotic expansion of the Fresnel auxiliary function `f` to `n` terms, with
explicit integral remainder (real, `ph z = 0` specialization of DLMF 7.12.4): for
`x > 0` and `n : ℕ`,
`f(x) = (1/(πx)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m}/(πx²/2)^{2m} + Rⁿᶠ(x)`,
where `Rⁿᶠ = remF` is the §7.12.6 integral remainder.  This is a genuine identity:
it asserts that `f` minus its `n`-term truncation equals the convergent integral
`remF` — the basis of the §7.12 error bounds.  DLMF 7.12.4 itself is stated for
complex `z` in the sector `|ph z| ≤ π/2 − δ`; see `erf_7_12_4_complex`.
-/
theorem erf_7_12_4 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    fresnelAuxF x = truncF n x + remF n x := by
  induction n with
  | zero =>
    have h0 : truncF 0 x = 0 := by
      rw [truncF, Finset.sum_range_zero, mul_zero]
    rw [h0, zero_add]
    exact fresnelAuxF_eq_remF_zero hx
  | succ n ih =>
    have ht : truncF (n + 1) x = truncF n x
        + 1 / (Real.pi * x) *
          (((-1) ^ n * pochHalf (2 * n)) / (Real.pi * x ^ 2 / 2) ^ (2 * n)) := by
      rw [truncF, truncF, Finset.sum_range_succ, mul_add]
    rw [ht, ih, _kit_remF_step n hx]
    ring

-- no-dlmf: helper definition, the complex `n`-term truncation of the `f`-series
-- (mirrors `truncF`), used by `erf_7_12_4_complex`.
/-- The complex `n`-term truncation of the `f`-series, `(1/(πz)) ∑_{m=0}^{n-1}
(−1)ᵐ (1/2)_{2m} / (πz²/2)^{2m}` (complex form of `truncF`). -/
noncomputable def ctruncF (n : ℕ) (z : ℂ) : ℂ :=
  (1 / ((Real.pi : ℂ) * z)) *
    ∑ m ∈ Finset.range n,
      ((-1 : ℂ) ^ m * (pochHalf (2 * m) : ℂ)) / ((Real.pi : ℂ) * z ^ 2 / 2) ^ (2 * m)

-- no-dlmf: helper definition, the `f`-remainder as the structural defect
-- `f(z) − ctruncF n z`.  DLMF itself defines `Rₙ^(f)` exactly this way via
-- 7.12.4 ("The remainder terms are given by 7.12.4 …"); the convergent-integral
-- formula for this quantity (DLMF 7.12.6) is proven separately, on its natural
-- (narrower) sector, by the real-valued `remF`.
/-- The complex `f`-remainder `Rⁿᶠ(z) := f(z) − ctruncF n z` (complex form of
`remF`, defined structurally rather than by the §7.12.6 integral). -/
noncomputable def cremF (n : ℕ) (z : ℂ) : ℂ :=
  FLMF.Fresnel.cfresnelAuxF z - ctruncF n z

-- no-dlmf: domain-wider version of DLMF 7.12.4, valid on the full open sector
-- `|arg z| < π/2` rather than DLMF's closed sub-sector `|ph z| ≤ π/2 − δ`;
-- faithful surface is `erf_7_12_4_dlmf`
/-- The `n`-term truncation of the Fresnel auxiliary `f` with remainder, for complex
`z` in the open sector `|arg z| < π/2` and `z ≠ 0`:
`f(z) = (1/(πz)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m}/(πz²/2)^{2m} + Rⁿᶠ(z)`. -/
theorem erf_7_12_4_complex (n : ℕ) (z : ℂ) (hz0 : z ≠ 0) (hph : |z.arg| < Real.pi / 2) :
    FLMF.Fresnel.cfresnelAuxF z = ctruncF n z + cremF n z := by
  unfold cremF; ring

/-- **DLMF 7.12.4** — for complex `z ≠ 0` in the sector `|ph z| ≤ π/2 − δ` for some
`δ ∈ (0, π/2)`, the `n`-term truncation of the Fresnel auxiliary `f` with remainder:
`f(z) = (1/(πz)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m}/(πz²/2)^{2m} + Rⁿᶠ(z)`.

DAG: E-7.12.4.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem erf_7_12_4_dlmf (n : ℕ) (z : ℂ) (hz0 : z ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (hph : |z.arg| ≤ Real.pi / 2 - δ) :
    FLMF.Fresnel.cfresnelAuxF z = ctruncF n z + cremF n z :=
  erf_7_12_4_complex n z hz0 (lt_of_le_of_lt hph (by linarith))

-- no-dlmf: real/narrowed restriction of DLMF 7.12.5; faithful surface is erf_7_12_5_complex
/-- Asymptotic expansion of the Fresnel auxiliary function `g` to `n` terms, with
explicit integral remainder (real, `ph z = 0` specialization of DLMF 7.12.5): for
`x > 0` and `n : ℕ`,
`g(x) = (1/(πx)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m+1}/(πx²/2)^{2m+1} + Rⁿᵍ(x)`,
where `Rⁿᵍ = remG` is the §7.12.7 integral remainder.  This is a genuine identity:
it asserts that `g` minus its `n`-term truncation equals the convergent integral
`remG`.  DLMF 7.12.5 itself is stated for complex `z` with `|ph z| < π/4`; see
`erf_7_12_5_complex`.
-/
theorem erf_7_12_5 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    fresnelAuxG x = truncG n x + remG n x := by
  induction n with
  | zero =>
    have h0 : truncG 0 x = 0 := by
      rw [truncG, Finset.sum_range_zero, mul_zero]
    rw [h0, zero_add]
    exact fresnelAuxG_eq_remG_zero hx
  | succ n ih =>
    have ht : truncG (n + 1) x = truncG n x
        + 1 / (Real.pi * x) *
          (((-1) ^ n * pochHalf (2 * n + 1)) / (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)) := by
      rw [truncG, truncG, Finset.sum_range_succ, mul_add]
    rw [ht, ih, _kit_remG_step n hx]
    ring

-- no-dlmf: helper definition, the complex `n`-term truncation of the `g`-series
-- (mirrors `truncG`), used by `erf_7_12_5_complex`.
/-- The complex `n`-term truncation of the `g`-series, `(1/(πz)) ∑_{m=0}^{n-1}
(−1)ᵐ (1/2)_{2m+1} / (πz²/2)^{2m+1}` (complex form of `truncG`). -/
noncomputable def ctruncG (n : ℕ) (z : ℂ) : ℂ :=
  (1 / ((Real.pi : ℂ) * z)) *
    ∑ m ∈ Finset.range n,
      ((-1 : ℂ) ^ m * (pochHalf (2 * m + 1) : ℂ)) / ((Real.pi : ℂ) * z ^ 2 / 2) ^ (2 * m + 1)

-- no-dlmf: helper definition, the `g`-remainder as the structural defect
-- `g(z) − ctruncG n z`.  DLMF itself defines `Rₙ^(g)` exactly this way via
-- 7.12.5; the convergent-integral formula for this quantity (DLMF 7.12.7) is
-- proven separately, on its natural sector, by the real-valued `remG`.
/-- The complex `g`-remainder `Rⁿᵍ(z) := g(z) − ctruncG n z` (complex form of
`remG`, defined structurally rather than by the §7.12.7 integral). -/
noncomputable def cremG (n : ℕ) (z : ℂ) : ℂ :=
  FLMF.Fresnel.cfresnelAuxG z - ctruncG n z

/-- **DLMF 7.12.5** — the `n`-term truncation of the Fresnel auxiliary `g` with
remainder, for complex `z` with `|ph z| < π/4`:
`g(z) = (1/(πz)) ∑_{m=0}^{n-1} (−1)ᵐ (1/2)_{2m+1}/(πz²/2)^{2m+1} + Rⁿᵍ(z)`.

DAG: E-7.12.5.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem erf_7_12_5_complex (n : ℕ) (z : ℂ) (hph : |z.arg| < Real.pi / 4) :
    FLMF.Fresnel.cfresnelAuxG z = ctruncG n z + cremG n z := by
  unfold cremG; ring

-- no-dlmf: real-axis specialization of DLMF 7.12.2; the canonical carrier is
-- `erf_7_12_2_sector` (Error/Ch7SectorExpansions.lean)
/-- The complete (Poincaré) asymptotic expansion (7.12.2, real form) of the Fresnel
auxiliary function `f` on the real axis:
`f(x) ∼ (1/(πx)) ∑_{m=0}^∞ (−1)ᵐ (1/2)_{2m}/(πx²/2)^{2m}` as `x → +∞`
(real specialization, `ph z = 0`, of the sector `|ph z| ≤ π/2 − δ`).

Stated in remainder form, valid for *every* truncation order `n` (which pins every
coefficient): the `n`-term remainder `f − truncF n`, scaled by `πx (πx²/2)^{2n}`,
converges to the next coefficient `(−1)ⁿ (1/2)_{2n}`.  (For `n = 0` this is the
leading-term statement `f(x) ∼ 1/(πx)`.)

The proof peels one term off the remainder (`_kit_remF_step` on top of the exact
truncation identity `erf_7_12_4`) and kills the scaled `(n+1)`-remainder by the
Gamma-integral bound `Rᶠ_{n+1}(x) = O(x^{-(4n+5)})`.  The faithful sector
surface (DLMF's `|ph z| ≤ π/2 − δ`) is `erf_7_12_2_sector`
(Error/Ch7SectorExpansions.lean). -/
theorem erf_7_12_2 (n : ℕ) :
    Tendsto (fun x : ℝ =>
        Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n) * (fresnelAuxF x - truncF n x))
      atTop (𝓝 ((-1 : ℝ) ^ n * pochHalf (2 * n))) := by
  have hpi := Real.pi_pos
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  -- the exponent of the `(n+1)`-remainder integrand
  set s : ℝ := 2 * (n : ℝ) + 3 / 2 with hsdef
  have hsn : (-1 : ℝ) < s := by
    have h := Nat.cast_nonneg (α := ℝ) n
    rw [hsdef]; linarith
  -- kit form of the `(n+1)`-remainder
  have hrem : ∀ x : ℝ, remF (n + 1) x = (-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1) := by
    intro x
    rw [remF]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) - 1 / 2) = s by rw [hsdef]; push_cast; ring,
      show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  -- the rescaled remainder `πx (πx²/2)^{2n} · Rᶠ_{n+1}(x)` vanishes at `+∞`
  have hrem0 : Tendsto (fun x : ℝ =>
      Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n) * remF (n + 1) x) atTop (𝓝 0) := by
    have hC : Tendsto (fun x : ℝ =>
        (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4)
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
    rw [hrem x]
    set J := ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1) with hJdef
    have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      positivity
    have hJle : J ≤ (1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1) := by
      have h1 : J ≤ ∫ t in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s := by
        refine setIntegral_mono_on
          (_kit_integrable_J _ _ hb hsn)
          (integrableOn_exp_neg_mul_rpow_Ioi _ _ hb hsn) measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht
        exact div_le_self (by positivity) (by nlinarith)
      rwa [integral_exp_neg_mul_rpow_Ioi _ _ hb hsn] at h1
    -- the scale times the Gamma bound collapses to a constant over `x⁴`
    have halg : Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n)
          * (1 / (Real.pi * Real.sqrt 2))
          * ((1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1))
        = (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4 := by
      have hBne : (Real.pi * x ^ 2 / 2) ≠ 0 := ne_of_gt hb
      -- Nat pow → rpow
      rw [show (1 / (Real.pi * x ^ 2 / 2)) = (Real.pi * x ^ 2 / 2)⁻¹ by rw [one_div],
        Real.inv_rpow hb.le, ← Real.rpow_neg hb.le,
        ← Real.rpow_natCast (Real.pi * x ^ 2 / 2) (2 * n)]
      rw [show Real.pi * x * (Real.pi * x ^ 2 / 2) ^ ((2 * n : ℕ) : ℝ)
            * (1 / (Real.pi * Real.sqrt 2))
            * ((Real.pi * x ^ 2 / 2) ^ (-(s + 1)) * Real.Gamma (s + 1))
          = (Real.Gamma (s + 1) / Real.sqrt 2) * (x *
              ((Real.pi * x ^ 2 / 2) ^ ((2 * n : ℕ) : ℝ)
                * (Real.pi * x ^ 2 / 2) ^ (-(s + 1)))) by field_simp]
      rw [← Real.rpow_add hb]
      rw [show ((2 * n : ℕ) : ℝ) + -(s + 1) = -(5 / 2) by rw [hsdef]; push_cast; ring]
      -- (πx²/2)^{-5/2} = (π/2)^{-5/2} x^{-5}
      have hsplit : (Real.pi * x ^ 2 / 2) ^ (-(5 / 2 : ℝ))
          = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)) := by
        rw [show Real.pi * x ^ 2 / 2 = (Real.pi / 2) * x ^ 2 by ring,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
        norm_num
      rw [hsplit]
      have hx4 : x * ((Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)))
          = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) / x ^ 4 := by
        rw [show x * ((Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)))
            = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) * (x ^ (1 : ℝ) * x ^ (-(5 : ℝ))) by
          rw [Real.rpow_one]; ring]
        rw [← Real.rpow_add hx,
          show ((1 : ℝ) + -(5 : ℝ)) = -(((4 : ℕ) : ℝ)) by norm_num,
          Real.rpow_neg hx.le, Real.rpow_natCast]
        exact (div_eq_mul_inv _ _).symm
      rw [hx4]
      have hinv : (Real.pi / 2) ^ (-(5 / 2 : ℝ)) = (2 / Real.pi) ^ ((5 : ℝ) / 2) := by
        rw [show (2 / Real.pi) = (Real.pi / 2)⁻¹ by rw [inv_div],
          Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
      rw [hinv]
      ring
    -- assemble the squeeze bound
    rw [show Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n)
          * ((-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) * J)
        = (-1 : ℝ) ^ (n + 1) * (Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n)
            * (1 / (Real.pi * Real.sqrt 2)) * J) by ring]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n)
          * (1 / (Real.pi * Real.sqrt 2)) * J
        ≤ Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n)
            * (1 / (Real.pi * Real.sqrt 2))
            * ((1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1)) :=
          mul_le_mul_of_nonneg_left hJle (by positivity)
      _ = (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4 := halg
  -- eventual identity: the scaled remainder after `n` terms is the next coefficient
  -- plus the scaled `(n+1)`-remainder
  have hkey : (fun x : ℝ =>
        Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n) * (fresnelAuxF x - truncF n x))
      =ᶠ[atTop] fun x : ℝ => (-1 : ℝ) ^ n * pochHalf (2 * n)
        + Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n) * remF (n + 1) x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
    have hbne : (Real.pi * x ^ 2 / 2) ^ (2 * n) ≠ 0 := pow_ne_zero _ (ne_of_gt hb)
    have hF : fresnelAuxF x - truncF n x = remF n x := by
      rw [erf_7_12_4 n x hx]; ring
    rw [hF, _kit_remF_step n hx]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ n * pochHalf (2 * n)
      + Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n) * remF (n + 1) x) atTop
      (𝓝 ((-1 : ℝ) ^ n * pochHalf (2 * n))) := by
    have h := (tendsto_const_nhds
      (x := ((-1 : ℝ) ^ n * pochHalf (2 * n))) (f := atTop)).add hrem0
    simpa using h
  exact Tendsto.congr' hkey.symm h1

-- no-dlmf: real-axis specialization of DLMF 7.12.3; the canonical carrier is
-- `erf_7_12_3_sector` (Error/Ch7SectorExpansions.lean)
/-- The complete (Poincaré) asymptotic expansion (7.12.3, real form) of the Fresnel
auxiliary function `g` on the real axis:
`g(x) ∼ (1/(πx)) ∑_{m=0}^∞ (−1)ᵐ (1/2)_{2m+1}/(πx²/2)^{2m+1}` as `x → +∞`
(real specialization, `ph z = 0`, of the sector `|ph z| ≤ π/2 − δ`).

Stated in remainder form, valid for *every* truncation order `n` (which pins every
coefficient): the `n`-term remainder `g − truncG n`, scaled by `πx (πx²/2)^{2n+1}`,
converges to the next coefficient `(−1)ⁿ (1/2)_{2n+1}`.  (For `n = 0` this is the
leading-term statement `g(x) ∼ 1/(π²x³)`.)

The proof peels one term off the remainder (`_kit_remG_step` on top of the exact
truncation identity `erf_7_12_5`) and kills the scaled `(n+1)`-remainder by the
Gamma-integral bound `Rᵍ_{n+1}(x) = O(x^{-(4n+7)})`.  The faithful sector
surface (DLMF's `|ph z| ≤ π/2 − δ`) is `erf_7_12_3_sector`
(Error/Ch7SectorExpansions.lean). -/
theorem erf_7_12_3 (n : ℕ) :
    Tendsto (fun x : ℝ =>
        Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) * (fresnelAuxG x - truncG n x))
      atTop (𝓝 ((-1 : ℝ) ^ n * pochHalf (2 * n + 1))) := by
  have hpi := Real.pi_pos
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  -- the exponent of the `(n+1)`-remainder integrand
  set s : ℝ := 2 * (n : ℝ) + 5 / 2 with hsdef
  have hsn : (-1 : ℝ) < s := by
    have h := Nat.cast_nonneg (α := ℝ) n
    rw [hsdef]; linarith
  -- kit form of the `(n+1)`-remainder
  have hrem : ∀ x : ℝ, remG (n + 1) x = (-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) *
      ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1) := by
    intro x
    rw [remG]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show ((2 * ((n + 1 : ℕ) : ℝ) : ℝ) + 1 / 2) = s by rw [hsdef]; push_cast; ring,
      show -Real.pi * x ^ 2 * t / 2 = -(Real.pi * x ^ 2 / 2) * t by ring]
  -- the rescaled remainder `πx (πx²/2)^{2n+1} · Rᵍ_{n+1}(x)` vanishes at `+∞`
  have hrem0 : Tendsto (fun x : ℝ =>
      Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) * remG (n + 1) x) atTop (𝓝 0) := by
    have hC : Tendsto (fun x : ℝ =>
        (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4)
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
    rw [hrem x]
    set J := ∫ t in Ioi (0 : ℝ),
        Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s / (t ^ 2 + 1) with hJdef
    have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      positivity
    have hJle : J ≤ (1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1) := by
      have h1 : J ≤ ∫ t in Ioi (0 : ℝ),
          Real.exp (-(Real.pi * x ^ 2 / 2) * t) * t ^ s := by
        refine setIntegral_mono_on
          (_kit_integrable_J _ _ hb hsn)
          (integrableOn_exp_neg_mul_rpow_Ioi _ _ hb hsn) measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht
        exact div_le_self (by positivity) (by nlinarith)
      rwa [integral_exp_neg_mul_rpow_Ioi _ _ hb hsn] at h1
    -- the scale times the Gamma bound collapses to a constant over `x⁴`
    have halg : Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)
          * (1 / (Real.pi * Real.sqrt 2))
          * ((1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1))
        = (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4 := by
      have hB := hb
      have hBne : (Real.pi * x ^ 2 / 2) ≠ 0 := ne_of_gt hB
      -- Nat pow → rpow
      rw [show (1 / (Real.pi * x ^ 2 / 2)) = (Real.pi * x ^ 2 / 2)⁻¹ by rw [one_div],
        Real.inv_rpow hB.le, ← Real.rpow_neg hB.le,
        ← Real.rpow_natCast (Real.pi * x ^ 2 / 2) (2 * n + 1)]
      rw [show Real.pi * x * (Real.pi * x ^ 2 / 2) ^ ((2 * n + 1 : ℕ) : ℝ)
            * (1 / (Real.pi * Real.sqrt 2))
            * ((Real.pi * x ^ 2 / 2) ^ (-(s + 1)) * Real.Gamma (s + 1))
          = (Real.Gamma (s + 1) / Real.sqrt 2) * (x *
              ((Real.pi * x ^ 2 / 2) ^ ((2 * n + 1 : ℕ) : ℝ)
                * (Real.pi * x ^ 2 / 2) ^ (-(s + 1)))) by field_simp]
      rw [← Real.rpow_add hB]
      rw [show ((2 * n + 1 : ℕ) : ℝ) + -(s + 1) = -(5 / 2) by rw [hsdef]; push_cast; ring]
      -- (πx²/2)^{-5/2} = (π/2)^{-5/2} x^{-5}
      have hsplit : (Real.pi * x ^ 2 / 2) ^ (-(5 / 2 : ℝ))
          = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)) := by
        rw [show Real.pi * x ^ 2 / 2 = (Real.pi / 2) * x ^ 2 by ring,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
        norm_num
      rw [hsplit]
      have hx4 : x * ((Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)))
          = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) / x ^ 4 := by
        rw [show x * ((Real.pi / 2) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 : ℝ)))
            = (Real.pi / 2) ^ (-(5 / 2 : ℝ)) * (x ^ (1 : ℝ) * x ^ (-(5 : ℝ))) by
          rw [Real.rpow_one]; ring]
        rw [← Real.rpow_add hx,
          show ((1 : ℝ) + -(5 : ℝ)) = -(((4 : ℕ) : ℝ)) by norm_num,
          Real.rpow_neg hx.le, Real.rpow_natCast]
        exact (div_eq_mul_inv _ _).symm
      rw [hx4]
      have hinv : (Real.pi / 2) ^ (-(5 / 2 : ℝ)) = (2 / Real.pi) ^ ((5 : ℝ) / 2) := by
        rw [show (2 / Real.pi) = (Real.pi / 2)⁻¹ by rw [inv_div],
          Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
      rw [hinv]
      ring
    -- assemble the squeeze bound
    rw [show Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)
          * ((-1 : ℝ) ^ (n + 1) / (Real.pi * Real.sqrt 2) * J)
        = (-1 : ℝ) ^ (n + 1) * (Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)
            * (1 / (Real.pi * Real.sqrt 2)) * J) by ring]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)
          * (1 / (Real.pi * Real.sqrt 2)) * J
        ≤ Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1)
            * (1 / (Real.pi * Real.sqrt 2))
            * ((1 / (Real.pi * x ^ 2 / 2)) ^ (s + 1) * Real.Gamma (s + 1)) :=
          mul_le_mul_of_nonneg_left hJle (by positivity)
      _ = (Real.Gamma (s + 1) * (2 / Real.pi) ^ ((5 : ℝ) / 2) / Real.sqrt 2) / x ^ 4 := halg
  -- eventual identity: the scaled remainder after `n` terms is the next coefficient
  -- plus the scaled `(n+1)`-remainder
  have hkey : (fun x : ℝ =>
        Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) * (fresnelAuxG x - truncG n x))
      =ᶠ[atTop] fun x : ℝ => (-1 : ℝ) ^ n * pochHalf (2 * n + 1)
        + Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) * remG (n + 1) x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hb : (0 : ℝ) < Real.pi * x ^ 2 / 2 := by positivity
    have hbne : (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hb)
    have hG : fresnelAuxG x - truncG n x = remG n x := by
      rw [erf_7_12_5 n x hx]; ring
    rw [hG, _kit_remG_step n hx]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ n * pochHalf (2 * n + 1)
      + Real.pi * x * (Real.pi * x ^ 2 / 2) ^ (2 * n + 1) * remG (n + 1) x) atTop
      (𝓝 ((-1 : ℝ) ^ n * pochHalf (2 * n + 1))) := by
    have h := (tendsto_const_nhds
      (x := ((-1 : ℝ) ^ n * pochHalf (2 * n + 1))) (f := atTop)).add hrem0
    simpa using h
  exact Tendsto.congr' hkey.symm h1

-- DLMF 7.12.6 / 7.12.7 (the integral representations of the remainders Rⁿᶠ, Rⁿᵍ) are
-- the DEFINING equations of `remF` / `remG` above (see their docstrings), so they need
-- no separate theorem; their content is carried by `erf_7_12_4` / `erf_7_12_5`, which
-- now genuinely assert `f − truncF = remF` and `g − truncG = remG`.

end FLMF.Error
