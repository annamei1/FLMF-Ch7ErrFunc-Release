import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Analytic continuation along a second-order linear ODE (method kit — E1b, DLMF §1.13, §15.10)

The three ingredients needed to continue a special function beyond the disc of
convergence of its defining series by riding its differential equation, over any
`RCLike` field (`ℝ` or `ℂ`):

1. **1-jet uniqueness** (`linODE2_eqOn_of_jet_eq`, primed variant for the
   non-normalized form `P w'' + Q w' + R w = 0` with `P ≠ 0` on the domain):
   two analytic solutions of `w'' + p w' + q w = 0` on an open preconnected set
   with the same value and derivative at one point agree everywhere.  Proof: the
   ODE forces all iterated derivatives of the difference to vanish at the point
   (Leibniz + strong induction), so the difference has infinite analytic order,
   vanishes near the point, and the identity theorem spreads the vanishing.

2. **Existence at an ordinary point** (`exists_analyticOnNhd_linODE2`): the ODE
   `(p₀ + p₁ t + p₂ t²) w'' + (q₀ + q₁ t) w' + r w = 0` (`t = z - z₀`;
   polynomial coefficients of the Gauss/Kummer shape, `p₀ ≠ 0` = ordinary point)
   has an analytic solution with prescribed 1-jet `(w₀, w₁)` on the explicit disc
   `‖z - z₀‖ < (4·ode2K)⁻¹`.  The solution is the power series with coefficients
   `ode2SeriesCoeff` from the two-term recurrence; convergence is by the
   geometric majorant `‖aₙ‖ ≤ max ‖w₀‖ ‖w₁‖ · ode2Kⁿ` (`ode2SeriesCoeff_norm_le`).
   The radius is *not* optimal (the true radius is the distance to the nearest
   singularity, a Cauchy-majorant refinement left open), but it is explicit and
   uniform in the initial data — enough to chain discs.

3. **Disc-step gluing** (`exists_analyticOnNhd_extension_union`): analytic
   functions on two open sets agreeing on the overlap glue to an analytic
   function on the union — one step of analytic continuation.

Infrastructure exposed along the way: `hasFPowerSeriesOnBall_ofScalars_sub`
(recentring a scalar power series) and `hasSum_deriv_of_ofScalars` (termwise
differentiation of `∑ cₙ (z-z₀)ⁿ` in `HasSum` form, generalizing the
`GaussODE`/`KummerODE` pattern).

The C2 Phase-2 consumer (`z = 1` connection formulas for `₂F₁`, DLMF §15.10)
instantiates 1. with `P = z(1-z)`, `Q = c-(a+b+1)z`, `R = -ab` on a preconnected
subdomain of `ℂ ∖ {0,1}`: any two solution bases with matched 1-jets at a common
point are thereby compared.  The `₂F₁` continuation certificate itself lives in
`Frameworks/Hypergeometric` (validated in `Methods/ODEContinuationProto.lean`).

## References

- DLMF §1.13: https://dlmf.nist.gov/1.13 (linear second-order ODEs)
- DLMF §15.10: https://dlmf.nist.gov/15.10 (the hypergeometric ODE, consumer)
-/

open Filter Set FormalMultilinearSeries Function TopologicalSpace CategoryTheory Opposite
open scoped Topology ENNReal NNReal

namespace FLMF.Methods.ODEContinuation

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Part 1 — 1-jet uniqueness for 2nd-order linear ODEs -/

section Uniqueness

variable {U : Set 𝕜} {p q f g : 𝕜 → 𝕜} {z₀ : 𝕜}

-- no-dlmf: iterated-derivative induction infrastructure, no DLMF counterpart
/-- At a point of an open set where an analytic function solves
`w'' + p w' + q w = 0` with vanishing 1-jet, all iterated derivatives vanish. -/
theorem iteratedDeriv_eq_zero_of_linODE2 (hUo : IsOpen U)
    (hp : AnalyticOnNhd 𝕜 p U) (hq : AnalyticOnNhd 𝕜 q U) (hf : AnalyticOnNhd 𝕜 f U)
    (hode : ∀ z ∈ U, deriv (deriv f) z + p z * deriv f z + q z * f z = 0)
    (hz₀ : z₀ ∈ U) (h0 : f z₀ = 0) (h1 : deriv f z₀ = 0) :
    ∀ n, iteratedDeriv n f z₀ = 0 := by
  have hdf : AnalyticOnNhd 𝕜 (deriv f) U := hf.deriv
  have key : ∀ n, ∀ k ≤ n + 1, iteratedDeriv k f z₀ = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      match k, hk with
      | 0, _ => simpa using h0
      | 1, _ => simpa [iteratedDeriv_one] using h1
      | (k + 2), h => exact absurd h (by omega)
    | succ n ih =>
      intro k hk
      rcases Nat.lt_or_ge k (n + 2) with h | h
      · exact ih k (by omega)
      have hk2 : k = n + 2 := le_antisymm hk h
      subst hk2
      -- rewrite the (n+2)-nd derivative through the ODE
      have hDD : deriv (deriv f) =ᶠ[𝓝 z₀]
          fun z => -(p z * deriv f z) + -(q z * f z) := by
        filter_upwards [hUo.mem_nhds hz₀] with z hz
        linear_combination hode z hz
      have hstep : iteratedDeriv n (deriv (deriv f)) z₀ =
          iteratedDeriv n (fun z => -(p z * deriv f z) + -(q z * f z)) z₀ :=
        (hDD.iteratedDeriv n).eq_of_nhds
      have hA : iteratedDeriv n (fun z => p z * deriv f z) z₀ = 0 := by
        rw [iteratedDeriv_fun_mul ((hp z₀ hz₀).contDiffAt) ((hdf z₀ hz₀).contDiffAt)]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hsh : iteratedDeriv (n - i) (deriv f) z₀ = iteratedDeriv (n - i + 1) f z₀ := by
          rw [iteratedDeriv_succ']
        rw [hsh, ih _ (by omega), mul_zero]
      have hB : iteratedDeriv n (fun z => q z * f z) z₀ = 0 := by
        rw [iteratedDeriv_fun_mul ((hq z₀ hz₀).contDiffAt) ((hf z₀ hz₀).contDiffAt)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [ih _ (by omega), mul_zero]
      have hCD : ContDiffAt 𝕜 n (fun z => -(p z * deriv f z)) z₀ :=
        (((hp z₀ hz₀).mul (hdf z₀ hz₀)).contDiffAt).neg
      have hCD' : ContDiffAt 𝕜 n (fun z => -(q z * f z)) z₀ :=
        (((hq z₀ hz₀).mul (hf z₀ hz₀)).contDiffAt).neg
      calc iteratedDeriv (n + 2) f z₀
          = iteratedDeriv n (deriv (deriv f)) z₀ := by
            rw [show n + 2 = n + 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_succ']
        _ = iteratedDeriv n (fun z => -(p z * deriv f z) + -(q z * f z)) z₀ := hstep
        _ = 0 := by
            rw [iteratedDeriv_fun_add hCD hCD', iteratedDeriv_fun_neg, iteratedDeriv_fun_neg,
              hA, hB]
            ring
  exact fun n : ℕ => key n n (by omega)

-- no-dlmf: uniqueness infrastructure, no DLMF equation number
/-- **Vanishing lemma.** An analytic solution of `w'' + p w' + q w = 0` on an
open preconnected set with vanishing 1-jet at one point vanishes identically. -/
theorem eqOn_zero_of_linODE2 (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hp : AnalyticOnNhd 𝕜 p U) (hq : AnalyticOnNhd 𝕜 q U) (hf : AnalyticOnNhd 𝕜 f U)
    (hode : ∀ z ∈ U, deriv (deriv f) z + p z * deriv f z + q z * f z = 0)
    (hz₀ : z₀ ∈ U) (h0 : f z₀ = 0) (h1 : deriv f z₀ = 0) :
    EqOn f 0 U := by
  have hall := iteratedDeriv_eq_zero_of_linODE2 hUo hp hq hf hode hz₀ h0 h1
  have hord : analyticOrderAt f z₀ = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z₀ hz₀)).mpr
      fun i _ => hall i
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀
    (analyticOrderAt_eq_top.mp hord)

-- no-dlmf: uniqueness infrastructure, no DLMF equation number
/-- **1-jet uniqueness.** Two analytic solutions of `w'' + p w' + q w = 0` on an
open preconnected set with the same value and derivative at one point agree
everywhere on the set. -/
theorem linODE2_eqOn_of_jet_eq (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hp : AnalyticOnNhd 𝕜 p U) (hq : AnalyticOnNhd 𝕜 q U)
    (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hfode : ∀ z ∈ U, deriv (deriv f) z + p z * deriv f z + q z * f z = 0)
    (hgode : ∀ z ∈ U, deriv (deriv g) z + p z * deriv g z + q z * g z = 0)
    (hz₀ : z₀ ∈ U) (hval : f z₀ = g z₀) (hder : deriv f z₀ = deriv g z₀) :
    EqOn f g U := by
  set h : 𝕜 → 𝕜 := fun z => f z - g z with hh
  have hha : AnalyticOnNhd 𝕜 h U := hf.sub hg
  have hdh : ∀ z ∈ U, deriv h z = deriv f z - deriv g z := fun z hz =>
    deriv_sub ((hf z hz).differentiableAt) ((hg z hz).differentiableAt)
  have hddh : ∀ z ∈ U, deriv (deriv h) z = deriv (deriv f) z - deriv (deriv g) z := by
    intro z hz
    have hev : deriv h =ᶠ[𝓝 z] fun w => deriv f w - deriv g w := by
      filter_upwards [hUo.mem_nhds hz] with w hw
      exact hdh w hw
    rw [hev.deriv_eq]
    exact deriv_sub ((hf.deriv z hz).differentiableAt) ((hg.deriv z hz).differentiableAt)
  have hode : ∀ z ∈ U, deriv (deriv h) z + p z * deriv h z + q z * h z = 0 := by
    intro z hz
    rw [hddh z hz, hdh z hz]
    have h1 := hfode z hz
    have h2 := hgode z hz
    simp only [hh]
    linear_combination h1 - h2
  have hzero : EqOn h 0 U :=
    eqOn_zero_of_linODE2 hUo hUc hp hq hha hode hz₀ (by simp [hh, hval])
      (by rw [hdh z₀ hz₀, hder, sub_self])
  intro z hz
  have := hzero hz
  simpa [hh, sub_eq_zero] using this

-- no-dlmf: uniqueness infrastructure, no DLMF equation number
/-- 1-jet uniqueness for the **non-normalized form** `P w'' + Q w' + R w = 0`
with analytic coefficients and non-vanishing leading coefficient `P` — the form
in which the hypergeometric-type equations are stated. -/
theorem linODE2_eqOn_of_jet_eq' {P Q R : 𝕜 → 𝕜} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hP : AnalyticOnNhd 𝕜 P U) (hQ : AnalyticOnNhd 𝕜 Q U) (hR : AnalyticOnNhd 𝕜 R U)
    (hPne : ∀ z ∈ U, P z ≠ 0)
    (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hfode : ∀ z ∈ U, P z * deriv (deriv f) z + Q z * deriv f z + R z * f z = 0)
    (hgode : ∀ z ∈ U, P z * deriv (deriv g) z + Q z * deriv g z + R z * g z = 0)
    (hz₀ : z₀ ∈ U) (hval : f z₀ = g z₀) (hder : deriv f z₀ = deriv g z₀) :
    EqOn f g U := by
  refine linODE2_eqOn_of_jet_eq (p := fun z => Q z / P z) (q := fun z => R z / P z)
    hUo hUc (hQ.div hP hPne) (hR.div hP hPne) hf hg ?_ ?_ hz₀ hval hder
  · intro z hz
    have h := hfode z hz
    have hPz := hPne z hz
    field_simp
    linear_combination h
  · intro z hz
    have h := hgode z hz
    have hPz := hPne z hz
    field_simp
    linear_combination h

end Uniqueness

/-! ### Part 2 — existence at an ordinary point (power-series construction) -/

section Existence

variable (p₀ p₁ p₂ q₀ q₁ r : 𝕜)

-- no-dlmf: series-coefficient recurrence data, no single DLMF equation number
/-- Taylor coefficients (about the expansion point) of the local solution of
`(p₀ + p₁ t + p₂ t²) w'' + (q₀ + q₁ t) w' + r w = 0` (`t` the local variable)
with initial data `w(0) = w₀`, `w'(0) = w₁`, from the two-term recurrence
obtained by collecting the `tⁿ` coefficient. -/
noncomputable def ode2SeriesCoeff (w₀ w₁ : 𝕜) : ℕ → 𝕜
  | 0 => w₀
  | 1 => w₁
  | n + 2 =>
      -((p₁ * n + q₀) * ((n : 𝕜) + 1) * ode2SeriesCoeff w₀ w₁ (n + 1)
          + (p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * ode2SeriesCoeff w₀ w₁ n)
        / (p₀ * ((n : 𝕜) + 2) * ((n : 𝕜) + 1))

-- no-dlmf: definitional equation lemma, no DLMF counterpart
@[simp] theorem ode2SeriesCoeff_zero (w₀ w₁ : 𝕜) :
    ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ 0 = w₀ := rfl

-- no-dlmf: definitional equation lemma, no DLMF counterpart
@[simp] theorem ode2SeriesCoeff_one (w₀ w₁ : 𝕜) :
    ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ 1 = w₁ := rfl

-- no-dlmf: series-coefficient recurrence, no single DLMF equation number
/-- The coefficient recurrence in multiplied-out form (`p₀ ≠ 0`):
`p₀(n+2)(n+1)·a_{n+2} + (p₁n+q₀)(n+1)·a_{n+1} + (p₂n(n-1)+q₁n+r)·aₙ = 0`. -/
theorem ode2SeriesCoeff_rec (hp₀ : p₀ ≠ 0) (w₀ w₁ : 𝕜) (n : ℕ) :
    p₀ * ((n : 𝕜) + 2) * ((n : 𝕜) + 1) * ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ (n + 2)
      + (p₁ * n + q₀) * ((n : 𝕜) + 1) * ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ (n + 1)
      + (p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ n
      = 0 := by
  have h2 : ((n : 𝕜) + 2) ≠ 0 := by
    have : ((n : 𝕜) + 2) = ((n + 2 : ℕ) : 𝕜) := by push_cast; ring
    rw [this]
    exact Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((n : 𝕜) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [ode2SeriesCoeff]
  field_simp
  ring

-- no-dlmf: majorant-rate bookkeeping, no DLMF counterpart
/-- The geometric growth rate controlling the recurrence: any `ρ < 1/ode2K`
is a radius of convergence for the coefficient series. -/
noncomputable def ode2K : ℝ := (‖p₁‖ + ‖q₀‖ + ‖p₂‖ + ‖q₁‖ + ‖r‖) / ‖p₀‖ + 1

-- no-dlmf: majorant-rate bookkeeping, no DLMF counterpart
theorem one_le_ode2K : 1 ≤ ode2K p₀ p₁ p₂ q₀ q₁ r := by
  have : 0 ≤ (‖p₁‖ + ‖q₀‖ + ‖p₂‖ + ‖q₁‖ + ‖r‖) / ‖p₀‖ := by positivity
  unfold ode2K; linarith

-- no-dlmf: majorant-rate bookkeeping, no DLMF counterpart
theorem ode2K_pos : 0 < ode2K p₀ p₁ p₂ q₀ q₁ r :=
  lt_of_lt_of_le one_pos (one_le_ode2K p₀ p₁ p₂ q₀ q₁ r)

-- no-dlmf: majorant estimate infrastructure, no DLMF counterpart
/-- Geometric bound on the recurrence coefficients:
`‖aₙ‖ ≤ max ‖w₀‖ ‖w₁‖ · Kⁿ` with `K = ode2K`. -/
theorem ode2SeriesCoeff_norm_le (hp₀ : p₀ ≠ 0) (w₀ w₁ : 𝕜) :
    ∀ n, ‖ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ n‖
      ≤ max ‖w₀‖ ‖w₁‖ * ode2K p₀ p₁ p₂ q₀ q₁ r ^ n := by
  set a := ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ with ha
  set K := ode2K p₀ p₁ p₂ q₀ q₁ r with hKdef
  set C := max ‖w₀‖ ‖w₁‖ with hC
  have hK1 : 1 ≤ K := one_le_ode2K p₀ p₁ p₂ q₀ q₁ r
  have hK0 : 0 < K := ode2K_pos p₀ p₁ p₂ q₀ q₁ r
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (le_max_left _ _)
  have hp₀' : 0 < ‖p₀‖ := norm_pos_iff.mpr hp₀
  -- ‖p₀‖ * K = (sum of coefficient norms) + ‖p₀‖
  have hpK : ‖p₀‖ * K = (‖p₁‖ + ‖q₀‖ + ‖p₂‖ + ‖q₁‖ + ‖r‖) + ‖p₀‖ := by
    rw [hKdef]
    unfold ode2K
    field_simp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [ha, ode2SeriesCoeff_zero, pow_zero, mul_one]
      exact le_max_left _ _
    | 1 =>
      rw [ha, ode2SeriesCoeff_one, pow_one]
      exact le_trans (le_max_right _ _) (le_mul_of_one_le_right hC0 hK1)
    | (n + 2) =>
      have hbn : ‖a n‖ ≤ C * K ^ n := ih n (by omega)
      have hbn1 : ‖a (n + 1)‖ ≤ C * K ^ (n + 1) := ih (n + 1) (by omega)
      have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      -- solve for a (n+2) from the recurrence and estimate norms
      have hrec := ode2SeriesCoeff_rec p₀ p₁ p₂ q₀ q₁ r hp₀ w₀ w₁ n
      rw [← ha] at hrec
      have heq : p₀ * ((n : 𝕜) + 2) * ((n : 𝕜) + 1) * a (n + 2)
          = -((p₁ * n + q₀) * ((n : 𝕜) + 1) * a (n + 1))
            - (p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * a n := by
        linear_combination hrec
      have hnormn : ‖(n : 𝕜)‖ = (n : ℝ) := RCLike.norm_natCast n
      have hnorm2 : ‖((n : 𝕜) + 2)‖ = (n : ℝ) + 2 := by
        rw [show ((n : 𝕜) + 2) = ((n + 2 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
        push_cast; ring
      have hnorm1 : ‖((n : 𝕜) + 1)‖ = (n : ℝ) + 1 := by
        rw [show ((n : 𝕜) + 1) = ((n + 1 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
        push_cast; ring
      -- first product: ‖(p₁n+q₀)(n+1)·a_{n+1}‖
      have hmuln : ‖p₁ * (n : 𝕜)‖ = ‖p₁‖ * (n : ℝ) := by rw [norm_mul, hnormn]
      have hnq : ‖p₁ * (n : 𝕜) + q₀‖ ≤ ‖p₁‖ * (n : ℝ) + ‖q₀‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [hmuln]
      have hX : ‖(p₁ * n + q₀) * ((n : 𝕜) + 1) * a (n + 1)‖
          ≤ (‖p₁‖ * (n : ℝ) + ‖q₀‖) * ((n : ℝ) + 1) * (C * K ^ (n + 1)) := by
        rw [norm_mul, norm_mul, hnorm1]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hnq (by linarith)) hbn1
          (norm_nonneg _) (by positivity)
      -- second product: ‖(p₂n(n-1)+q₁n+r)·aₙ‖
      have hns : ‖(n : 𝕜) - 1‖ ≤ (n : ℝ) + 1 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [hnormn, norm_one]
      have hnY : ‖p₂ * (n : 𝕜) * ((n : 𝕜) - 1) + q₁ * (n : 𝕜) + r‖
          ≤ ‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖ := by
        refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add ?_ ?_)) le_rfl)
        · rw [norm_mul, norm_mul, hnormn]
          exact mul_le_mul_of_nonneg_left hns (by positivity)
        · rw [norm_mul, hnormn]
      have hY : ‖(p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * a n‖
          ≤ (‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖) * (C * K ^ n) := by
        rw [norm_mul]
        exact mul_le_mul hnY hbn (norm_nonneg _) (by positivity)
      -- combine
      have hLbound : ‖p₀‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * ‖a (n + 2)‖
          ≤ (‖p₁‖ * (n : ℝ) + ‖q₀‖) * ((n : ℝ) + 1) * (C * K ^ (n + 1))
            + (‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖) * (C * K ^ n) := by
        calc ‖p₀‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * ‖a (n + 2)‖
            = ‖p₀ * ((n : 𝕜) + 2) * ((n : 𝕜) + 1) * a (n + 2)‖ := by
              rw [norm_mul, norm_mul, norm_mul, hnorm2, hnorm1]
          _ ≤ ‖(p₁ * n + q₀) * ((n : 𝕜) + 1) * a (n + 1)‖
              + ‖(p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * a n‖ := by
              rw [heq]
              refine le_trans (norm_sub_le _ _) ?_
              rw [norm_neg]
          _ ≤ _ := add_le_add hX hY
      -- arithmetic: bound the right side by ‖p₀‖(n+2)(n+1)·C·K^{n+2}
      have hb1 : (‖p₁‖ * (n : ℝ) + ‖q₀‖) * ((n : ℝ) + 1)
          ≤ (‖p₁‖ + ‖q₀‖) * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
        nlinarith [norm_nonneg p₁, norm_nonneg q₀, hN0, sq_nonneg (n : ℝ)]
      have hb2 : ‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖
          ≤ (‖p₂‖ + ‖q₁‖ + ‖r‖) * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
        nlinarith [norm_nonneg p₂, norm_nonneg q₁, norm_nonneg r, hN0, sq_nonneg (n : ℝ)]
      have hbr : (‖p₁‖ + ‖q₀‖) * K + (‖p₂‖ + ‖q₁‖ + ‖r‖) ≤ ‖p₀‖ * K * K := by
        have hB0 : (0 : ℝ) ≤ ‖p₂‖ + ‖q₁‖ + ‖r‖ := by positivity
        have h1 : (‖p₁‖ + ‖q₀‖) * K + (‖p₂‖ + ‖q₁‖ + ‖r‖)
            ≤ (‖p₁‖ + ‖q₀‖ + (‖p₂‖ + ‖q₁‖ + ‖r‖)) * K := by
          nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hK1)]
        have h2 : (‖p₁‖ + ‖q₀‖ + (‖p₂‖ + ‖q₁‖ + ‖r‖)) * K ≤ ‖p₀‖ * K * K := by
          refine le_trans (mul_le_mul_of_nonneg_right ?_ hK0.le) le_rfl
          rw [hpK]; linarith [hp₀'.le]
        linarith
      have harith : (‖p₁‖ * (n : ℝ) + ‖q₀‖) * ((n : ℝ) + 1) * (C * K ^ (n + 1))
            + (‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖) * (C * K ^ n)
          ≤ ‖p₀‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * (C * K ^ (n + 2)) := by
        have t1 := mul_le_mul_of_nonneg_right hb1
          (show (0 : ℝ) ≤ C * K ^ (n + 1) by positivity)
        have t2 := mul_le_mul_of_nonneg_right hb2
          (show (0 : ℝ) ≤ C * K ^ n by positivity)
        have t3 := mul_le_mul_of_nonneg_left hbr
          (show (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (C * K ^ n) by positivity)
        calc (‖p₁‖ * (n : ℝ) + ‖q₀‖) * ((n : ℝ) + 1) * (C * K ^ (n + 1))
              + (‖p₂‖ * (n : ℝ) * ((n : ℝ) + 1) + ‖q₁‖ * (n : ℝ) + ‖r‖) * (C * K ^ n)
            ≤ (‖p₁‖ + ‖q₀‖) * (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (C * K ^ (n + 1))
              + (‖p₂‖ + ‖q₁‖ + ‖r‖) * (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (C * K ^ n) := by
              linarith
          _ = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (C * K ^ n)
              * ((‖p₁‖ + ‖q₀‖) * K + (‖p₂‖ + ‖q₁‖ + ‖r‖)) := by
              rw [pow_succ]; ring
          _ ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (C * K ^ n) * (‖p₀‖ * K * K) := t3
          _ = ‖p₀‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) * (C * K ^ (n + 2)) := by
              rw [pow_succ, pow_succ]; ring
      -- cancel the positive factor
      have hfin := le_trans hLbound harith
      have hpos : (0 : ℝ) < ‖p₀‖ * ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
      exact le_of_mul_le_mul_left hfin hpos

-- no-dlmf: cast-norm helper, no DLMF counterpart
/-- Norm of `(n : 𝕜) + 1` in an `RCLike` field. -/
theorem norm_natCast_add_one (n : ℕ) : ‖((n : 𝕜) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : 𝕜) + 1) = ((n + 1 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
  push_cast; ring

-- no-dlmf: power-series recentring infrastructure, no DLMF counterpart
/-- The sum of a scalar power series, recentered at `z₀`, has that series as its
power series on any ball inside the radius. -/
theorem hasFPowerSeriesOnBall_ofScalars_sub {c : ℕ → 𝕜} {ρ : ℝ≥0} (hρ : 0 < ρ)
    (hr : (ρ : ℝ≥0∞) ≤ (ofScalars 𝕜 c).radius) (z₀ : 𝕜) :
    HasFPowerSeriesOnBall (fun z => (ofScalars 𝕜 c).sum (z - z₀)) (ofScalars 𝕜 c) z₀ ρ where
  r_le := hr
  r_pos := ENNReal.coe_pos.mpr hρ
  hasSum := by
    intro y hy
    have hy' : y ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 c).radius :=
      Metric.eball_subset_eball hr hy
    simpa [add_sub_cancel_left] using (ofScalars 𝕜 c).hasSum hy'

-- no-dlmf: termwise-differentiation infrastructure, no DLMF counterpart
/-- **Termwise differentiation** of a scalar power series centered at `z₀`
(`HasSum` form): if `f = ∑ cₙ (z-z₀)ⁿ` on a ball then
`f'(z₀+y) = ∑ (n+1)c_{n+1} yⁿ` there. -/
theorem hasSum_deriv_of_ofScalars {c : ℕ → 𝕜} {f : 𝕜 → 𝕜} {z₀ : 𝕜} {ρ : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (ofScalars 𝕜 c) z₀ ρ) {y : 𝕜}
    (hy : y ∈ Metric.eball (0 : 𝕜) ρ) :
    HasSum (fun n : ℕ => ((n : 𝕜) + 1) * c (n + 1) * y ^ n) (deriv f (z₀ + y)) := by
  have hsum : HasSum (fun n : ℕ => (ofScalars 𝕜 c).derivSeries n fun _ => y)
      (fderiv 𝕜 f (z₀ + y)) := hf.fderiv.hasSum hy
  have happ := hsum.mapL (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜))
  have he : (fun n : ℕ => ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)
      ((ofScalars 𝕜 c).derivSeries n fun _ => y))
      = fun n : ℕ => ((n : 𝕜) + 1) * c (n + 1) * y ^ n := by
    funext n
    rw [ContinuousLinearMap.apply_apply,
      apply_eq_pow_smul_coeff (p := (ofScalars 𝕜 c).derivSeries) (n := n) (z := y),
      ContinuousLinearMap.smul_apply, derivSeries_coeff_one,
      show (ofScalars 𝕜 c).coeff (n + 1) = c (n + 1) from coeff_ofScalars]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [he] at happ
  have hd : ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜) (fderiv 𝕜 f (z₀ + y))
      = deriv f (z₀ + y) := by
    rw [ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv]
  rwa [hd] at happ

section MainExistence

variable (p₀ p₁ p₂ q₀ q₁ r : 𝕜)

-- no-dlmf: local-solution existence, no DLMF equation number
/-- **Existence of an analytic local solution at an ordinary point** of the
second-order linear ODE `(p₀ + p₁ t + p₂ t²) w'' + (q₀ + q₁ t) w' + r w = 0`
(`t = z - z₀` the local variable, `p₀ ≠ 0` the ordinary-point hypothesis),
with prescribed initial data `w(z₀) = w₀`, `w'(z₀) = w₁`, on the explicit disc
of radius `(4·ode2K)⁻¹`. -/
theorem exists_analyticOnNhd_linODE2 (hp₀ : p₀ ≠ 0) (z₀ w₀ w₁ : 𝕜) :
    ∃ f : 𝕜 → 𝕜,
      AnalyticOnNhd 𝕜 f (Metric.ball z₀ (4 * ode2K p₀ p₁ p₂ q₀ q₁ r)⁻¹) ∧
      f z₀ = w₀ ∧ deriv f z₀ = w₁ ∧
      ∀ x ∈ Metric.ball z₀ (4 * ode2K p₀ p₁ p₂ q₀ q₁ r)⁻¹,
        (p₀ + p₁ * (x - z₀) + p₂ * (x - z₀) ^ 2) * deriv (deriv f) x
          + (q₀ + q₁ * (x - z₀)) * deriv f x + r * f x = 0 := by
  classical
  set K := ode2K p₀ p₁ p₂ q₀ q₁ r with hK
  have hK1 : 1 ≤ K := one_le_ode2K p₀ p₁ p₂ q₀ q₁ r
  have hK0 : 0 < K := ode2K_pos p₀ p₁ p₂ q₀ q₁ r
  set a := ode2SeriesCoeff p₀ p₁ p₂ q₀ q₁ r w₀ w₁ with ha
  set C := max ‖w₀‖ ‖w₁‖ with hC
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (le_max_left _ _)
  have hbound : ∀ n, ‖a n‖ ≤ C * K ^ n := by
    intro n
    rw [ha, hC, hK]
    exact ode2SeriesCoeff_norm_le p₀ p₁ p₂ q₀ q₁ r hp₀ w₀ w₁ n
  -- the shifted (derivative) coefficient sequence
  set c1 : ℕ → 𝕜 := fun n : ℕ => ((n : 𝕜) + 1) * a (n + 1) with hc1
  -- the working radius
  have hR0 : (0 : ℝ) < (4 * K)⁻¹ := by positivity
  set ρ : ℝ≥0 := ⟨(4 * K)⁻¹, hR0.le⟩ with hρ
  have hρcoe : ((ρ : ℝ≥0) : ℝ) = (4 * K)⁻¹ := rfl
  have hρ0 : 0 < ρ := NNReal.coe_pos.mp (by rw [hρcoe]; exact hR0)
  -- growth facts
  have htwo : ∀ n : ℕ, ((n : ℝ) + 1) ≤ 2 ^ n := by
    intro n
    have := Nat.lt_two_pow_self (n := n)
    have h' : (n + 1 : ℕ) ≤ 2 ^ n := this
    exact_mod_cast h'
  -- radius bounds for both series
  have hrad0 : (ρ : ℝ≥0∞) ≤ (ofScalars 𝕜 a).radius := by
    refine (ofScalars 𝕜 a).le_radius_of_bound C fun n : ℕ => ?_
    rw [ofScalars_norm, hρcoe]
    calc ‖a n‖ * ((4 * K)⁻¹) ^ n
        ≤ C * K ^ n * ((4 * K)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right (hbound n) (by positivity)
      _ = C * (K * (4 * K)⁻¹) ^ n := by rw [mul_pow]; ring
      _ = C * ((4 : ℝ)⁻¹) ^ n := by
          rw [show K * (4 * K)⁻¹ = (4 : ℝ)⁻¹ by field_simp]
      _ ≤ C := mul_le_of_le_one_right hC0 (pow_le_one₀ (by norm_num) (by norm_num))
  have hrad1 : (ρ : ℝ≥0∞) ≤ (ofScalars 𝕜 c1).radius := by
    refine (ofScalars 𝕜 c1).le_radius_of_bound (C * K) fun n : ℕ => ?_
    rw [ofScalars_norm, hρcoe]
    have hnorm : ‖c1 n‖ = ((n : ℝ) + 1) * ‖a (n + 1)‖ := by
      rw [hc1]
      simp only []
      rw [norm_mul, norm_natCast_add_one]
    calc ‖c1 n‖ * ((4 * K)⁻¹) ^ n
        = ((n : ℝ) + 1) * ‖a (n + 1)‖ * ((4 * K)⁻¹) ^ n := by rw [hnorm]
      _ ≤ (2 : ℝ) ^ n * (C * K ^ (n + 1)) * ((4 * K)⁻¹) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul (htwo n) (hbound (n + 1)) (norm_nonneg _) (by positivity)
      _ = C * K * ((2 : ℝ) * K * (4 * K)⁻¹) ^ n := by
          rw [mul_pow, mul_pow, pow_succ]; ring
      _ = C * K * ((2 : ℝ)⁻¹) ^ n := by
          rw [show (2 : ℝ) * K * (4 * K)⁻¹ = (2 : ℝ)⁻¹ by field_simp; ring]
      _ ≤ C * K := mul_le_of_le_one_right (by positivity)
          (pow_le_one₀ (by norm_num) (by norm_num))
  -- the two sums
  set F : 𝕜 → 𝕜 := fun z => (ofScalars 𝕜 a).sum (z - z₀) with hF
  set G : 𝕜 → 𝕜 := fun z => (ofScalars 𝕜 c1).sum (z - z₀) with hG
  have hFb : HasFPowerSeriesOnBall F (ofScalars 𝕜 a) z₀ ρ :=
    hasFPowerSeriesOnBall_ofScalars_sub hρ0 hrad0 z₀
  have hGb : HasFPowerSeriesOnBall G (ofScalars 𝕜 c1) z₀ ρ :=
    hasFPowerSeriesOnBall_ofScalars_sub hρ0 hrad1 z₀
  -- ball membership translation
  have hmem : ∀ x ∈ Metric.ball z₀ (4 * K)⁻¹,
      (x - z₀) ∈ Metric.eball (0 : 𝕜) (ρ : ℝ≥0∞) := by
    intro x hx
    rw [Metric.eball_coe, mem_ball_zero_iff, hρcoe]
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  -- HasSum forms on the ball
  have hFx : ∀ y ∈ Metric.eball (0 : 𝕜) (ρ : ℝ≥0∞),
      HasSum (fun n : ℕ => a n * y ^ n) (F (z₀ + y)) := by
    intro y hy
    have h := hFb.hasSum hy
    have he : (fun n : ℕ => (ofScalars 𝕜 a) n fun _ => y) = fun n : ℕ => a n * y ^ n := by
      funext n
      rw [ofScalars_apply_eq, smul_eq_mul]
    rwa [he] at h
  have hGx : ∀ y ∈ Metric.eball (0 : 𝕜) (ρ : ℝ≥0∞),
      HasSum (fun n : ℕ => c1 n * y ^ n) (G (z₀ + y)) := by
    intro y hy
    have h := hGb.hasSum hy
    have he : (fun n : ℕ => (ofScalars 𝕜 c1) n fun _ => y) = fun n : ℕ => c1 n * y ^ n := by
      funext n
      rw [ofScalars_apply_eq, smul_eq_mul]
    rwa [he] at h
  -- deriv F = G on the ball
  have hDFG : Set.EqOn (deriv F) G (Metric.ball z₀ (4 * K)⁻¹) := by
    intro x hx
    have hy := hmem x hx
    have h1 := hasSum_deriv_of_ofScalars hFb hy
    have h2 := hGx _ hy
    rw [show z₀ + (x - z₀) = x by ring] at h1 h2
    refine h1.unique ?_
    have : (fun n : ℕ => c1 n * (x - z₀) ^ n)
        = fun n : ℕ => ((n : 𝕜) + 1) * a (n + 1) * (x - z₀) ^ n := by
      funext n; rw [hc1]
    rwa [this] at h2
  -- second derivative through G
  have hDDF : ∀ x ∈ Metric.ball z₀ (4 * K)⁻¹, deriv (deriv F) x = deriv G x := by
    intro x hx
    have hev : deriv F =ᶠ[𝓝 x] G := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw
      exact hDFG hw
    exact hev.deriv_eq
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · -- analyticity
    have h := hFb.analyticOnNhd
    rwa [Metric.eball_coe, hρcoe] at h
  · -- value at the center
    simpa [ofScalars_apply_eq, ha] using (hFb.coeff_zero fun _ => (1 : 𝕜)).symm
  · -- derivative at the center
    have h := hFb.hasFPowerSeriesAt.deriv
    rw [h, ofScalars_apply_eq]
    simp [ha]
  · -- the ODE on the ball
    intro x hx
    have hy := hmem x hx
    -- the three aligned sums, at t = x - z₀
    have h0 := hFx _ hy
    have h1 := hasSum_deriv_of_ofScalars hFb hy
    have h2 := hasSum_deriv_of_ofScalars hGb hy
    rw [show z₀ + (x - z₀) = x by ring] at h0 h1 h2
    rw [← hDDF x hx] at h2
    have h2' : HasSum (fun n : ℕ => ((n : 𝕜) + 1) * ((n : 𝕜) + 2) * a (n + 2) * (x - z₀) ^ n)
        (deriv (deriv F) x) := by
      have : (fun n : ℕ => ((n : 𝕜) + 1) * c1 (n + 1) * (x - z₀) ^ n)
          = fun n : ℕ => ((n : 𝕜) + 1) * ((n : 𝕜) + 2) * a (n + 2) * (x - z₀) ^ n := by
        funext n
        rw [hc1]
        push_cast
        ring
      rwa [this] at h2
    set t : 𝕜 := x - z₀ with ht
    -- reindexed sums: t·w'', t²·w'', t·w'
    have hs2 : HasSum (fun n : ℕ => (n : 𝕜) * ((n : 𝕜) + 1) * a (n + 1) * t ^ n)
        (t * (deriv (deriv F) x)) := by
      have h := h2'.mul_left t
      have he : (fun n : ℕ => t * (((n : 𝕜) + 1) * ((n : 𝕜) + 2) * a (n + 2) * t ^ n))
          = fun n : ℕ => (((n + 1 : ℕ) : 𝕜)) * (((n + 1 : ℕ) : 𝕜) + 1) * a (n + 1 + 1)
            * t ^ (n + 1) := by
        funext n; push_cast; ring
      rw [he] at h
      have h' := (hasSum_nat_add_iff
        (f := fun n : ℕ => (n : 𝕜) * ((n : 𝕜) + 1) * a (n + 1) * t ^ n) 1).mp h
      simpa using h'
    have hs3 : HasSum (fun n : ℕ => ((n : 𝕜) - 1) * (n : 𝕜) * a n * t ^ n)
        (t * (t * (deriv (deriv F) x))) := by
      have h := (h2'.mul_left t).mul_left t
      have he : (fun n : ℕ => t * (t * (((n : 𝕜) + 1) * ((n : 𝕜) + 2) * a (n + 2) * t ^ n)))
          = fun n : ℕ => (((n + 2 : ℕ) : 𝕜) - 1) * ((n + 2 : ℕ) : 𝕜) * a (n + 2)
            * t ^ (n + 2) := by
        funext n; push_cast; ring
      rw [he] at h
      have h' := (hasSum_nat_add_iff
        (f := fun n : ℕ => ((n : 𝕜) - 1) * (n : 𝕜) * a n * t ^ n) 2).mp h
      simpa [Finset.sum_range_succ] using h'
    have hs1 : HasSum (fun n : ℕ => (n : 𝕜) * a n * t ^ n) (t * deriv F x) := by
      have h := h1.mul_left t
      have he : (fun n : ℕ => t * (((n : 𝕜) + 1) * a (n + 1) * t ^ n))
          = fun n : ℕ => (((n + 1 : ℕ) : 𝕜)) * a (n + 1) * t ^ (n + 1) := by
        funext n; push_cast; ring
      rw [he] at h
      have h' := (hasSum_nat_add_iff
        (f := fun n : ℕ => (n : 𝕜) * a n * t ^ n) 1).mp h
      simpa using h'
    -- combine with the recurrence: everything cancels termwise
    have hrec : ∀ n : ℕ,
        p₀ * ((n : 𝕜) + 2) * ((n : 𝕜) + 1) * a (n + 2)
          + (p₁ * n + q₀) * ((n : 𝕜) + 1) * a (n + 1)
          + (p₂ * n * ((n : 𝕜) - 1) + q₁ * n + r) * a n = 0 := by
      intro n
      rw [ha]
      exact ode2SeriesCoeff_rec p₀ p₁ p₂ q₀ q₁ r hp₀ w₀ w₁ n
    have hT := (((((h2'.mul_left p₀).add (hs2.mul_left p₁)).add (hs3.mul_left p₂)).add
      (h1.mul_left q₀)).add (hs1.mul_left q₁)).add (h0.mul_left r)
    have hzero : (fun n : ℕ =>
        ((((p₀ * (((n : 𝕜) + 1) * ((n : 𝕜) + 2) * a (n + 2) * t ^ n)
          + p₁ * ((n : 𝕜) * ((n : 𝕜) + 1) * a (n + 1) * t ^ n))
          + p₂ * (((n : 𝕜) - 1) * (n : 𝕜) * a n * t ^ n))
          + q₀ * (((n : 𝕜) + 1) * a (n + 1) * t ^ n))
          + q₁ * ((n : 𝕜) * a n * t ^ n))
          + r * (a n * t ^ n)) = fun _ => (0 : 𝕜) := by
      funext n
      linear_combination t ^ n * hrec n
    rw [hzero] at hT
    have hT0 := hT.unique hasSum_zero
    rw [ht] at hT0 ⊢
    linear_combination hT0

end MainExistence

/-! ### Part 3 — disc-step continuation (gluing along an overlap) -/

section Gluing

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] {E F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup F'] [NormedSpace 𝕜' F']

-- no-dlmf: continuation-step infrastructure, no DLMF counterpart
/-- **Disc-step analytic continuation.** Two analytic functions on open sets
agreeing on the overlap glue to a single analytic function on the union. -/
theorem exists_analyticOnNhd_extension_union {U V : Set E} (hUo : IsOpen U) (hVo : IsOpen V)
    {f g : E → F'} (hf : AnalyticOnNhd 𝕜' f U) (hg : AnalyticOnNhd 𝕜' g V)
    (hfg : EqOn f g (U ∩ V)) :
    ∃ h : E → F', AnalyticOnNhd 𝕜' h (U ∪ V) ∧ EqOn h f U ∧ EqOn h g V := by
  classical
  refine ⟨fun z => if z ∈ U then f z else g z, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzU : z ∈ U
    · refine (hf z hzU).congr ?_
      filter_upwards [hUo.mem_nhds hzU] with w hw
      simp [hw]
    · have hzV : z ∈ V := hz.resolve_left hzU
      refine (hg z hzV).congr ?_
      filter_upwards [hVo.mem_nhds hzV] with w hw
      by_cases hwU : w ∈ U
      · simp [hwU, (hfg ⟨hwU, hw⟩).symm]
      · simp [hwU]
  · intro z hz
    simp [hz]
  · intro z hz
    by_cases hzU : z ∈ U
    · simp [hzU, hfg ⟨hzU, hz⟩]
    · simp [hzU]

-- no-dlmf: analytic-sheaf gluing infrastructure, no DLMF counterpart
/-- **Analytic gluing over an arbitrary open cover.** A pairwise-compatible
family of analytic local representatives glues to one analytic function on the
union of its domains.

This is the cover-level counterpart of `exists_analyticOnNhd_extension_union`.
It isolates the final sheaf-gluing step needed by global analytic continuation:
the remaining mathematical work is to construct a covering family of local
solutions and prove their compatibility by ODE uniqueness. -/
theorem exists_analyticOnNhd_extension_iUnion {ι : Type*}
    (U : ι → Set E) (f : ι → E → F')
    (hUo : ∀ i, IsOpen (U i))
    (hf : ∀ i, AnalyticOnNhd 𝕜' (f i) (U i))
    (hcompat : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : E → F', AnalyticOnNhd 𝕜' g (⋃ i, U i) ∧
      ∀ i, EqOn g (f i) (U i) := by
  classical
  let g : E → F' := fun z =>
    if hz : ∃ i, z ∈ U i then f (Classical.choose hz) z else 0
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    refine (hf i z hi).congr ?_
    filter_upwards [(hUo i).mem_nhds hi] with w hw
    simp only [g]
    have hex : ∃ j, w ∈ U j := ⟨i, hw⟩
    rw [dif_pos hex]
    exact hcompat i (Classical.choose hex) ⟨hw, Classical.choose_spec hex⟩
  · intro i z hz
    simp only [g]
    have hex : ∃ j, z ∈ U j := ⟨i, hz⟩
    rw [dif_pos hex]
    exact (hcompat i (Classical.choose hex) ⟨hz, Classical.choose_spec hex⟩).symm

end Gluing

end Existence

/-! ### Part 4 — global monodromy-free gluing -/

section GlobalContinuation

universe u

variable {X : TopCat.{u}} {T : X → Type u}

-- no-dlmf: abstract continuation-space infrastructure, no DLMF counterpart
/-- A local predicate whose germs are determined by their fibre value, and for
which arbitrary fibre values have unique representatives on one common
neighborhood, has a covering étalé space.  This packages the local
existence-and-uniqueness input needed for global continuation. -/
theorem isCoveringMap_etaleSpace_of_unique_local_sections
    (P : TopCat.LocalPredicate T)
    (heval : ∀ x, Injective (TopCat.stalkToFiber P x))
    (hlocal : ∀ x, ∃ (U : Opens X), x ∈ U ∧
      ∀ y (hy : y ∈ U) (t : T y), ∃! s :
        (TopCat.subsheafToTypes P).presheaf.obj (op U),
        s.1 ⟨y, hy⟩ = t) :
    IsCoveringMap
      (TopCat.Presheaf.EtaleSpace.base
        (F := (TopCat.subsheafToTypes P).presheaf)) := by
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨U, hxU, hU⟩ := hlocal x
  refine ⟨U, hxU, ?_⟩
  intro y hy
  constructor
  · intro s₁ s₂ hs
    obtain ⟨s, hsval, hs_unique⟩ := hU y hy (s₁.1 ⟨y, hy⟩)
    have hval : s₁.1 ⟨y, hy⟩ = s₂.1 ⟨y, hy⟩ := by
      have h := congr_arg (TopCat.stalkToFiber P y) hs
      rw [TopCat.stalkToFiber_germ P U y hy s₁,
        TopCat.stalkToFiber_germ P U y hy s₂] at h
      exact h
    exact (hs_unique s₁ rfl).trans (hs_unique s₂ hval.symm).symm
  · intro g
    let t : T y := TopCat.stalkToFiber P y g
    obtain ⟨s, hs, -⟩ := hU y hy t
    refine ⟨s, heval y ?_⟩
    rw [TopCat.stalkToFiber_germ]
    exact hs

-- no-dlmf: abstract monodromy theorem for local solution sheaves, no DLMF counterpart
/-- **Global monodromy-free gluing.** On a simply connected, locally
path-connected base, a locally well-posed sheaf with point-determined germs has
a global section through every prescribed initial germ.

The proof forms the étalé space of germs, proves that its projection is a
covering map from the supplied local well-posedness data, lifts the identity map
of the base, and recovers the global section from the lifted germs. -/
theorem exists_global_of_unique_local_sections
    {Y : Type u}
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => Y))
    (heval : ∀ x, Injective (TopCat.stalkToFiber P x))
    (hlocal : ∀ x, ∃ (U : Opens X), x ∈ U ∧
      ∀ y (hy : y ∈ U) (t : Y), ∃! s :
        (TopCat.subsheafToTypes P).presheaf.obj (op U),
        s.1 ⟨y, hy⟩ = t)
    (x₀ : X) (g₀ : (TopCat.subsheafToTypes P).presheaf.stalk x₀) :
    ∃ s : X → Y,
      P.pred (fun x : (⊤ : Opens X) => s x.1) ∧
        s x₀ = TopCat.stalkToFiber P x₀ g₀ := by
  let F := (TopCat.subsheafToTypes P).presheaf
  let e₀ : F.EtaleSpace := ⟨x₀, g₀⟩
  have hcov : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F)) :=
    isCoveringMap_etaleSpace_of_unique_local_sections P heval hlocal
  obtain ⟨L, hL, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hb : ∀ x, (L x).base = x := by
    intro x
    exact congr_fun hL.2 x
  let s : X → Y := fun x => TopCat.stalkToFiber P (L x).base (L x).germ
  refine ⟨s, ?_, ?_⟩
  · apply P.locality
    intro x
    obtain ⟨U, hxU, f, hf⟩ :=
      TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto
        L.continuous.continuousAt
    obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hf
    have hVU : V ⊆ U := by
      intro y hy
      obtain ⟨hyU, -⟩ := hVsub hy
      simpa [hb y] using hyU
    let V' : Opens X := ⟨V, hVo⟩
    let iVU : V' ⟶ U := homOfLE hVU
    refine ⟨V', hxV, Opens.leTop V', ?_⟩
    have hp := P.res iVU f.1 f.2
    convert hp using 1
    funext y
    obtain ⟨hyU, hgy⟩ := hVsub y.2
    change s y.1 = f.1 (iVU y)
    dsimp [s]
    dsimp [F] at hgy ⊢
    rw [hgy]
    calc
      _ = f.1 ⟨(L y.1).base, hyU⟩ :=
        TopCat.stalkToFiber_germ P U (L y.1).base hyU f
      _ = f.1 (iVU y) := by
        have heq : (⟨(L y.1).base, hyU⟩ : U) = iVU y := by
          apply Subtype.ext
          exact hb y.1
        rw [heq]
  · dsimp [s]
    rw [hL.1]

end GlobalContinuation

end FLMF.Methods.ODEContinuation
