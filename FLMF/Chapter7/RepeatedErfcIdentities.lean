import FLMF.Chapter7.RepeatedErfc
import FLMF.Chapter7.ErfcLeading
import FLMF.Chapter7.KummerBridge
import FLMF.Chapter7.TricomiBridge
import FLMF.Support.Confluent
import FLMF.Support.ParabolicCylinder
import FLMF.Support.HypergeometricKummer
import FLMF.Support.HypergeometricKummerTransform
import FLMF.Support.HypergeometricKummerContiguous
import FLMF.Support.HermiteNormalization
import FLMF.Chapter7.ContinuedFractions
import FLMF.Support.Recurrence
import Mathlib.Analysis.Calculus.LHopital

/-!
# Repeated integrals of the complementary error function — chapter surfaces (DLMF §7.18)

Statement surfaces (Phase 5) for the remaining numbered identities of DLMF §7.18,
stated faithfully against `FLMF.Error.iRepErfc : ℕ → ℝ → ℝ`
(`iⁿerfc`, defined in `RepeatedErfc.lean`).  The initial value (7.18.1), the
defining integral (7.18.2), the derivative relation (7.18.3) and the
super-exponential decay are already in `RepeatedErfc.lean` (which also records the
ODE 7.18.5 and the three-term recurrence 7.18.7 as documented deferrals); this
file adds:

* `erf_7_18_2`  — the explicit integral representation
  `iⁿerfc(z) = (2/√π) ∫_z^∞ (t−z)ⁿ/n! · e^{−t²} dt`.
* `erf_7_18_4`  — `dⁿ/dzⁿ(e^{z²}erfc z) = (−1)ⁿ 2ⁿ n! e^{z²} iⁿerfc(z)`.
* `erf_7_18_6`  — the Maclaurin series in `z`.
* `erf_7_18_8`  — the complex Hermite bridge `(−1)ⁿiⁿerfc(z)+iⁿerfc(−z)=…Hₙ(iz)`,
  with `Hₙ = FLMF.Functions.Hermite.physicistsHermite n`.
* `erf_7_18_9`  — the Kummer `M` (`₁F₁`) representation.
* `erf_7_18_10` — the Tricomi `U` representation.
* `erf_7_18_11` — the parabolic cylinder `U` representation.
* `erf_7_18_12` — the `Hh_n` probability-function representation.
* `erf_7_18_13` — the continued fraction for the consecutive ratio, for DLMF
  indices `≥ 1` (proved); `erf_7_18_13_general` is the faithful full surface
  including the DLMF `n = 0` case with `i⁻¹erfc(z) = (2/√π)e^{−z²}`.
* `erf_7_18_14` — the leading large-`z` asymptotic.
-/

noncomputable section

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set Asymptotics
open scoped FLMF.Hypergeometric

-- no-dlmf: integrability of the shifted-power Gaussian kernel on a half-line;
-- proof infrastructure for DLMF 7.18.2, no DLMF identity number
/-- The kernel `t ↦ (t−s)ⁿ e^{−t²}` is integrable on `(s, ∞)` for every real `s`
(continuous, and `O(e^{−t})` at `+∞`). -/
theorem integrableOn_sub_pow_mul_gauss (n : ℕ) (s : ℝ) :
    IntegrableOn (fun t : ℝ => (t - s) ^ n * Real.exp (-t ^ 2)) (Ioi s) := by
  refine integrable_of_isBigO_exp_neg (b := 1) one_pos
    ((((continuous_id.sub continuous_const).pow n).mul
      (Real.continuous_exp.comp (continuous_pow 2).neg)).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (2 ^ n) ?_
  have h1 : ∀ᶠ t : ℝ in atTop, t ^ n * Real.exp (-t) ≤ 1 :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero n).eventually_le_const one_pos
  filter_upwards [h1, eventually_ge_atTop (2 * |s|), eventually_ge_atTop (2 : ℝ)]
    with t ht1 hts ht2
  have habs : |s| ≤ t / 2 := by linarith
  have hst : s ≤ t := le_trans (le_trans (le_abs_self s) habs) (by linarith)
  have h0 : (0 : ℝ) ≤ t - s := by linarith
  have hub : t - s ≤ 2 * t := by
    have := neg_abs_le s
    linarith
  have hexp : Real.exp (-t ^ 2) ≤ Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnorm : ‖(t - s) ^ n * Real.exp (-t ^ 2)‖ = (t - s) ^ n * Real.exp (-t ^ 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg h0 n) (Real.exp_pos _).le)]
  rw [hnorm]
  have hpow : (t - s) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ h0 hub n
  calc (t - s) ^ n * Real.exp (-t ^ 2)
      ≤ (2 * t) ^ n * (Real.exp (-t) * Real.exp (-t)) := by
        apply mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = 2 ^ n * ((t ^ n * Real.exp (-t)) * Real.exp (-t)) := by ring
    _ ≤ 2 ^ n * (1 * Real.exp (-t)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right ht1 (Real.exp_pos _).le
    _ = 2 ^ n * ‖Real.exp (-1 * t)‖ := by
        rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, neg_one_mul]

-- no-dlmf: chain link 7.18.2 (assembled in `erf_7_18_2` below, alongside
-- `iRepErfc_eq_integral_pred`); the closed-form second equality of the display
/-- Integral representation of `iⁿerfc` (DLMF 7.18.2): the `n`-fold repeated
integral equals the single weighted Gaussian tail integral
`(2/√π) ∫_z^∞ (t−z)ⁿ/n! · e^{−t²} dt`. -/
theorem iRepErfc_eq_integral_closedForm (n : ℕ) (z : ℝ) :
    iRepErfc n z =
      2 / Real.sqrt Real.pi *
        ∫ t in Ioi z, (t - z) ^ n / n.factorial * Real.exp (-t ^ 2) := by
  induction n generalizing z with
  | zero =>
    rw [iRepErfc_zero_apply, erfc_eq_tail_global]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp
  | succ n ih =>
    have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    set F : ℝ → ℝ → ℝ := fun s t =>
      Set.indicator (Ioi s) (fun u => (u - s) ^ n / n.factorial * Real.exp (-u ^ 2)) t with hFdef
    -- kernel integrability (with the 1/n! constant)
    have hker : ∀ s : ℝ, IntegrableOn
        (fun u : ℝ => (u - s) ^ n / n.factorial * Real.exp (-u ^ 2)) (Ioi s) := by
      intro s
      have h := (integrableOn_sub_pow_mul_gauss n s).mul_const ((n.factorial : ℝ))⁻¹
      have heq : (fun t : ℝ => (t - s) ^ n * Real.exp (-t ^ 2) * (n.factorial : ℝ)⁻¹)
          = fun u : ℝ => (u - s) ^ n / n.factorial * Real.exp (-u ^ 2) :=
        funext fun t => by ring
      rwa [heq] at h
    -- each slice is integrable
    have hslice : ∀ s : ℝ, Integrable (F s) volume := fun s =>
      (integrable_indicator_iff measurableSet_Ioi).mpr (hker s)
    -- slice nonnegativity
    have hFnn : ∀ s t : ℝ, 0 ≤ F s t := by
      intro s t
      refine Set.indicator_nonneg (fun u hu => ?_) t
      have : (0 : ℝ) ≤ u - s := by
        have : s < u := hu
        linarith
      positivity
    -- the inner integral equals (√π/2)·iⁿerfc
    have hinner : ∀ s : ℝ, (∫ t, F s t) = Real.sqrt Real.pi / 2 * iRepErfc n s := by
      intro s
      rw [hFdef]
      rw [integral_indicator measurableSet_Ioi]
      rw [ih s]
      field_simp
    -- measurability of the uncurried kernel
    have hmeas : AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Ioi z)).prod volume) := by
      have hFeq : Function.uncurry F = Set.indicator {p : ℝ × ℝ | p.1 < p.2}
          (fun p : ℝ × ℝ => (p.2 - p.1) ^ n / n.factorial * Real.exp (-p.2 ^ 2)) := by
        funext p
        rcases p with ⟨s, t⟩
        by_cases h : s < t
        · simp [Function.uncurry, hFdef, Set.indicator_apply, Set.mem_Ioi, h]
        · simp [Function.uncurry, hFdef, Set.indicator_apply, Set.mem_Ioi, h]
      rw [hFeq]
      refine (Measurable.indicator ?_ ?_).aestronglyMeasurable
      · exact (((continuous_snd.sub continuous_fst).pow n).div_const _|>.mul
          (Real.continuous_exp.comp (continuous_snd.pow 2).neg)).measurable
      · exact measurableSet_lt measurable_fst measurable_snd
    -- product integrability
    have hprod : Integrable (Function.uncurry F) ((volume.restrict (Ioi z)).prod volume) := by
      rw [integrable_prod_iff hmeas]
      constructor
      · exact Eventually.of_forall fun s => hslice s
      · refine ((integrableOn_iRepErfc n z).const_mul (Real.sqrt Real.pi / 2)).congr
          (Eventually.of_forall fun s => ?_)
        simp only [Function.uncurry_apply_pair]
        have h1 : (fun t => ‖F s t‖) = F s := funext fun t => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hFnn s t)]
        rw [h1, hinner s]
    -- the swap
    have hswap := MeasureTheory.integral_integral_swap hprod
    -- LHS identification
    have hLHS : iRepErfc (n + 1) z = 2 / Real.sqrt Real.pi * ∫ s in Ioi z, ∫ t, F s t := by
      rw [iRepErfc_succ_eq]
      rw [show (∫ s in Ioi z, ∫ t, F s t)
          = ∫ s in Ioi z, Real.sqrt Real.pi / 2 * iRepErfc n s from
        setIntegral_congr_fun measurableSet_Ioi fun s _ => hinner s]
      rw [integral_const_mul]
      field_simp
    -- inner s-integral for fixed t
    have hsint : ∀ t : ℝ, (∫ s in Ioi z, F s t)
        = Set.indicator (Ioi z)
            (fun u => (u - z) ^ (n + 1) / (n + 1).factorial * Real.exp (-u ^ 2)) t := by
      intro t
      have hFs : (fun s => F s t) = Set.indicator (Iio t)
          (fun s => (t - s) ^ n / n.factorial * Real.exp (-t ^ 2)) := by
        funext s
        by_cases h : s < t
        · simp [hFdef, Set.indicator_apply, Set.mem_Ioi, Set.mem_Iio, h]
        · simp [hFdef, Set.indicator_apply, Set.mem_Ioi, Set.mem_Iio, h]
      rw [hFs, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
      by_cases hzt : z < t
      · have hle : z ≤ t := hzt.le
        have hIoo : (∫ s in Ioo z t, (t - s) ^ n / n.factorial * Real.exp (-t ^ 2))
            = ∫ s in (z)..(t), (t - s) ^ n / n.factorial * Real.exp (-t ^ 2) := by
          rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
        rw [hIoo]
        have hpull : (∫ s in (z)..(t), (t - s) ^ n / n.factorial * Real.exp (-t ^ 2))
            = (∫ s in (z)..(t), (t - s) ^ n) * (Real.exp (-t ^ 2) / n.factorial) := by
          rw [← intervalIntegral.integral_mul_const]
          congr 1
          funext s
          ring
        rw [hpull]
        have hcomp : (∫ s in (z)..(t), (t - s) ^ n) = (t - z) ^ (n + 1) / (n + 1) := by
          rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ n) t]
          rw [sub_self]
          rw [integral_pow]
          simp
        rw [hcomp, Set.indicator_of_mem (Set.mem_Ioi.mpr hzt)]
        rw [Nat.factorial_succ]
        push_cast
        have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      · rw [Set.indicator_of_notMem (by simpa using hzt)]
        have : Ioo z t = ∅ := Set.Ioo_eq_empty (by simpa using hzt)
        rw [this]
        simp
    -- assemble
    rw [hLHS, hswap]
    congr 1
    rw [show (∫ t, ∫ s in Ioi z, F s t)
        = ∫ t, Set.indicator (Ioi z)
            (fun u => (u - z) ^ (n + 1) / (n + 1).factorial * Real.exp (-u ^ 2)) t from
      integral_congr_ae (Eventually.of_forall hsint)]
    rw [integral_indicator measurableSet_Ioi]

-- no-dlmf: index-shift support def for the 7.18.2 display; surfaced at `erf_7_18_2`
/-- The "index `n − 1`" member of the repeated-integral family, for `n : ℕ`:
`iRepErfcPred 0 = iRepErfcNegOne` (the `n = -1` base case) and
`iRepErfcPred (m+1) = iRepErfc m` for `m ≥ 0`. Lets 7.18.2's first
equality (`iⁿerfc(z) = ∫_z^∞ i^{n-1}erfc(t) dt`) be stated uniformly for every
`n = 0, 1, 2, …`, matching the display's own range. -/
noncomputable def iRepErfcPred : ℕ → ℝ → ℝ
  | 0 => iRepErfcNegOne
  | m + 1 => iRepErfc m

-- no-dlmf: chain link 7.18.2 (assembled in `erf_7_18_2` below, alongside
-- `iRepErfc_eq_integral_closedForm`); the n = 0 case of the first equality,
-- `i⁰erfc(z) = ∫_z^∞ i⁻¹erfc(t) dt`, via the tail-integral form of `erfc`
theorem iRepErfc_zero_eq_integral (z : ℝ) :
    iRepErfc 0 z = ∫ t in Ioi z, iRepErfcPred 0 t := by
  simp only [iRepErfcPred, iRepErfcNegOne]
  rw [MeasureTheory.integral_const_mul, ← erfc_eq_tail_global, iRepErfc_zero_apply]

-- no-dlmf: chain link 7.18.2 (assembled in `erf_7_18_2` below); the first
-- equality of the display, `iⁿerfc(z) = ∫_z^∞ i^{n-1}erfc(t) dt`, uniformly for
-- every `n = 0, 1, 2, …` (the `n = 0` case reaching back to `i⁻¹erfc`, via
-- `iRepErfc_zero_eq_integral`; every `n = m+1` case via `iRepErfc_succ_eq`)
theorem iRepErfc_eq_integral_pred (n : ℕ) (z : ℝ) :
    iRepErfc n z = ∫ t in Ioi z, iRepErfcPred n t := by
  cases n with
  | zero => exact iRepErfc_zero_eq_integral z
  | succ m => exact iRepErfc_succ_eq m z

-- no-dlmf: real-axis restriction of DLMF 7.18.2 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_2` (ComplexRepeatedErfc.lean)
/-- The real repeated integral `iⁿerfc(z)`, for every `n = 0, 1, 2, …`,
both as the tail integral of the previous member of the family and as the
explicit closed form `(2/√π) ∫_z^∞ (t−z)ⁿ/n! · e^{−t²} dt`. -/
theorem erf_7_18_2 (n : ℕ) (z : ℝ) :
    iRepErfc n z = ∫ t in Ioi z, iRepErfcPred n t ∧
    iRepErfc n z =
      2 / Real.sqrt Real.pi *
        ∫ t in Ioi z, (t - z) ^ n / n.factorial * Real.exp (-t ^ 2) :=
  ⟨iRepErfc_eq_integral_pred n z, iRepErfc_eq_integral_closedForm n z⟩

-- no-dlmf: real-axis restriction of DLMF 7.18.4 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_4` (ComplexRepeatedErfc.lean)
/-- `n`-th derivative relation for the repeated erfc on the real axis:
`dⁿ/dzⁿ (e^{z²} erfc z) = (−1)ⁿ 2ⁿ n! e^{z²} iⁿerfc(z)`. -/
theorem erf_7_18_4 (n : ℕ) (z : ℝ) :
    iteratedDeriv n (fun z => Real.exp (z ^ 2) * erfc z) z =
      (-1) ^ n * 2 ^ n * n.factorial * Real.exp (z ^ 2) * iRepErfc n z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun z => Real.exp (z ^ 2) * erfc z)
        = fun t => (-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ) * Real.exp (t ^ 2)
          * iRepErfc n t :=
      funext fun t => ih t
    rw [hfun]
    have hd : HasDerivAt (fun t => (-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ)
          * Real.exp (t ^ 2) * iRepErfc n t)
        ((-1) ^ (n + 1) * 2 ^ (n + 1) * ((n + 1).factorial : ℝ) * Real.exp (z ^ 2)
          * iRepErfc (n + 1) z) z := by
      have h := (hasDerivAt_expSq_mul_iRepErfc n z).const_mul
        ((-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ))
      have hfeq : (fun t => (-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ)
            * (Real.exp (t ^ 2) * iRepErfc n t))
          = fun t => (-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ) * Real.exp (t ^ 2)
            * iRepErfc n t :=
        funext fun t => by ring
      rw [hfeq] at h
      have hveq : (-1 : ℝ) ^ n * 2 ^ n * (n.factorial : ℝ)
            * (-(2 * ((n : ℝ) + 1)) * (Real.exp (z ^ 2) * iRepErfc (n + 1) z))
          = (-1) ^ (n + 1) * 2 ^ (n + 1) * ((n + 1).factorial : ℝ) * Real.exp (z ^ 2)
            * iRepErfc (n + 1) z := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hveq] at h
      exact h
    rw [hd.deriv]

-- no-dlmf: real-axis restriction of DLMF 7.18.8 (the variable `z` is real, cast up
-- on the left; DLMF assigns `z` a complex domain); faithful surface is
-- `cerf_7_18_8` (ComplexRepeatedErfc.lean)
/-- Hermite bridge for the real `iⁿerfc`: the symmetric combination
`(−1)ⁿiⁿerfc(z)+iⁿerfc(−z)` equals `i^{−n}/(2^{n−1}n!)·Hₙ(iz)`, with `Hₙ` the
physicists' Hermite polynomial (`FLMF.Functions.Hermite.physicistsHermite`)
evaluated at the imaginary argument `iz`.

Stated over `ℂ` (the left side is real, cast up); we write `i^{−n}=(−i)ⁿ` and
`1/2^{n−1}=2/2ⁿ` to avoid negative/`Nat`-subtraction exponents.

Proof: both sides satisfy the same three-term recursion
`2(n+2)·Aₙ₊₂ = Aₙ + 2z·Aₙ₊₁` — the left-hand side from the repeated-integral
recurrence `erf_7_18_7` applied at `±z`, the right-hand side from
`H_{n+2}(w) = 2w·H_{n+1}(w) − 2(n+1)·Hₙ(w)` at `w = iz` — and they agree at
`n = 0` (`erfc z + erfc(−z) = 2`, from `cerf_neg`) and at `n = 1`
(`−i¹erfc(z) + i¹erfc(−z) = 2z`, from the seed `two_iRepErfc_one_add` at `±z`),
so a two-step induction closes it.  The induction is run in the cleared form
`2ⁿ·n!·Aₙ = 2(−i)ⁿHₙ(iz)` so that no division appears until the last step. -/
theorem erf_7_18_8 (n : ℕ) (z : ℝ) :
    (((-1) ^ n * iRepErfc n z + iRepErfc n (-z) : ℝ) : ℂ) =
      (2 * (-Complex.I) ^ n / ((2 : ℂ) ^ n * (n.factorial : ℂ))) *
        Polynomial.aeval (Complex.I * (z : ℂ))
          (FLMF.Functions.Hermite.physicistsHermite n) := by
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  -- `erfc(z) + erfc(−z) = 2` (real form of DLMF 7.4.2, via the oddness `cerf_neg`)
  have herfc_add : ∀ x : ℝ, erfc x + erfc (-x) = 2 := by
    intro x
    have hneg : ((-x : ℝ) : ℂ) = -((x : ℝ) : ℂ) := by push_cast; ring
    have hc : cerfc ((x : ℝ) : ℂ) + cerfc ((-x : ℝ) : ℂ) = 2 := by
      rw [hneg]
      simp only [cerfc, cerf_neg]
      ring
    rw [cerfc_ofReal, cerfc_ofReal] at hc
    exact_mod_cast hc
  -- the `n = 1` seed value `−i¹erfc(z) + i¹erfc(−z) = 2z`
  have hL1 : (-1 : ℝ) * iRepErfc 1 z + iRepErfc 1 (-z) = 2 * z := by
    have hs1 := two_iRepErfc_one_add z
    have hs2 := two_iRepErfc_one_add (-z)
    rw [neg_sq] at hs2
    linear_combination (-(1 : ℝ) / 2) * hs1 + (1 / 2) * hs2 + z * herfc_add z
  -- two-step induction on the cleared identity `2ᵐ·m!·Aₘ = 2(−i)ᵐ Hₘ(iz)`
  have key : ∀ m : ℕ,
      ((2 : ℂ) ^ m * (m.factorial : ℂ))
          * ((((-1 : ℝ)) ^ m * iRepErfc m z + iRepErfc m (-z) : ℝ) : ℂ)
        = 2 * (-Complex.I) ^ m
            * Polynomial.aeval (Complex.I * (z : ℂ))
                (FLMF.Functions.Hermite.physicistsHermite m)
      ∧ ((2 : ℂ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℂ))
          * ((((-1 : ℝ)) ^ (m + 1) * iRepErfc (m + 1) z + iRepErfc (m + 1) (-z) : ℝ) : ℂ)
        = 2 * (-Complex.I) ^ (m + 1)
            * Polynomial.aeval (Complex.I * (z : ℂ))
                (FLMF.Functions.Hermite.physicistsHermite (m + 1)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, iRepErfc_zero_apply,
          FLMF.Functions.Hermite.aeval_physicistsHermite_zero, mul_one]
        have hc : ((erfc z : ℝ) : ℂ) + ((erfc (-z) : ℝ) : ℂ) = 2 := by
          exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (herfc_add z)
        push_cast
        linear_combination hc
      · simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, zero_add,
          FLMF.Functions.Hermite.aeval_physicistsHermite_one]
        have hc := congrArg (fun r : ℝ => (r : ℂ)) hL1
        push_cast at hc ⊢
        linear_combination 2 * hc + 4 * (z : ℂ) * hI2
    | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      have h1 := erf_7_18_7 m z
      have h2 := erf_7_18_7 m (-z)
      have hAreal : 2 * ((m : ℝ) + 2) *
            ((-1) ^ (m + 2) * iRepErfc (m + 2) z + iRepErfc (m + 2) (-z))
          = ((-1) ^ m * iRepErfc m z + iRepErfc m (-z))
            + 2 * z * ((-1) ^ (m + 1) * iRepErfc (m + 1) z + iRepErfc (m + 1) (-z)) := by
        linear_combination ((-1 : ℝ) ^ m) * h1 + h2
      have hAC := congrArg (fun r : ℝ => (r : ℂ)) hAreal
      have hH := FLMF.Functions.Hermite.aeval_physicistsHermite_add_two m (Complex.I * (z : ℂ))
      have hIpow : (-Complex.I) ^ (m + 1 + 1) = -((-Complex.I) ^ m) := by
        rw [pow_succ, pow_succ]
        linear_combination ((-Complex.I) ^ m) * hI2
      have hfac2 : ((((m + 1 + 1)).factorial : ℕ) : ℂ)
          = ((m : ℂ) + 2) * ((m : ℂ) + 1) * ((m.factorial : ℕ) : ℂ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have hfac1 : ((((m + 1)).factorial : ℕ) : ℂ)
          = ((m : ℂ) + 1) * ((m.factorial : ℕ) : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac1] at ih1
      rw [hIpow, hfac2]
      push_cast at hAC ih0 ih1 ⊢
      linear_combination ((2 : ℂ) ^ (m + 1) * ((m : ℂ) + 1) * ((m.factorial : ℕ) : ℂ)) * hAC
        + (2 * ((m : ℂ) + 1)) * ih0 + (2 * (z : ℂ)) * ih1
        + (2 * (-Complex.I) ^ m) * hH
  have hQ := (key n).1
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hfn : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp
  linear_combination hQ

/-! ### Kummer support kit for DLMF 7.18.9

The route: transform both `M`-terms with Kummer's transformation (DLMF 13.2.39)
into `M(−n/2, 1/2, −z²)` and `z·M(1/2−n/2, 3/2, −z²)`, whose `z`-derivatives close
under the pair (via the `b = 3/2` ladder contiguous relation, DLMF 13.3-family):
`d/dz M(c,1/2,−z²) = −4cz·M(c+1,3/2,−z²)` and `d/dz [z·M(c,3/2,−z²)] = M(c,1/2,−z²)`.
The right side of 7.18.9 then satisfies the same first-order recursion
`R_{n+1}' = −R_n` as `iⁿerfc` (DLMF 7.18.3), with matching values at `z = 0`
(`iⁿerfc(0) = 1/(2ⁿΓ(n/2+1))`, DLMF 7.18.1/7.18.6 at `z=0`), so induction on `n`
plus the vanishing-derivative constancy argument identifies the two sides. -/

section KummerSupport

open Polynomial FLMF.Hypergeometric FLMF.Methods

-- no-dlmf: pole-avoidance for the half-integer b-parameters; trivial arithmetic
private lemma no_pole_half : ∀ k : ℕ, (k : ℝ) ≠ -(1/2 : ℝ) := by
  intro k h
  have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  rw [h] at h0
  norm_num at h0

-- no-dlmf: pole-avoidance for the half-integer b-parameters; trivial arithmetic
private lemma no_pole_threehalf : ∀ k : ℕ, (k : ℝ) ≠ -(3/2 : ℝ) := by
  intro k h
  have h0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  rw [h] at h0
  norm_num at h0

-- no-dlmf: b-ladder contiguous relation at b = 3/2 (DLMF 13.3-family instance
-- M(a,b−1,x) = M(a,b,x) + a/(b(b−1))·x·M(a+1,b+1,x) at b = 3/2); support for 7.18.9
/-- `M(c,1/2,x) = M(c,3/2,x) + (4c/3)·x·M(c+1,5/2,x)` — the `b = 3/2` instance of the
`b`-ladder contiguous relation, proved termwise from the Kummer coefficients. -/
private lemma kummerM_half_ladder (c x : ℝ) :
    ₁F₁ c (1/2 : ℝ) x = ₁F₁ c (3/2 : ℝ) x + 4 * c / 3 * x * ₁F₁ (c + 1) (5/2 : ℝ) x := by
  have hT0 := hasSum_eq_zero
    (((kummerM_hasSum c (1/2 : ℝ) x).sub
      (kummerM_hasSum c (3/2 : ℝ) x)).sub
      ((kummerM_hasSum_shift (c + 1) (5/2 : ℝ) x).mul_left (4 * c / 3)))
    (fun n => by
      cases n with
      | zero => simp [kummerCoefficient]
      | succ m =>
        have hPm : (ascPochhammer ℝ m).eval (3/2 : ℝ) ≠ 0 :=
          ascPochhammer_eval_ne_zero no_pole_threehalf m
        have h1 := kummerCoefficient_succ_eq c (3/2 : ℝ) m (by norm_num)
        rw [show (3/2 : ℝ) + 1 = 5/2 by norm_num] at h1
        have h2 : kummerCoefficient c (1/2 : ℝ) (m + 1)
            = (2 * (m : ℝ) + 3) * kummerCoefficient c (3/2 : ℝ) (m + 1) := by
          simp only [kummerCoefficient, ascPochhammer_succ_eval' m (1/2 : ℝ),
            ascPochhammer_succ_eval m (3/2 : ℝ)]
          rw [show (1/2 : ℝ) + 1 = 3/2 by norm_num]
          have hm32 : (3/2 : ℝ) + (m : ℝ) ≠ 0 := by positivity
          have hfac : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.2 (m + 1).factorial_ne_zero
          field_simp
          ring
        show kummerCoefficient c (1/2 : ℝ) (m + 1) * x ^ (m + 1)
            - kummerCoefficient c (3/2 : ℝ) (m + 1) * x ^ (m + 1)
            - 4 * c / 3 * (kummerCoefficient (c + 1) (5/2 : ℝ) m * x ^ (m + 1)) = 0
        linear_combination x ^ (m + 1) * h2 + 2 * x ^ (m + 1) * h1)
  linear_combination hT0

-- no-dlmf: chain-rule derivative of the even Hermite-type Kummer combination;
-- support for 7.18.9
/-- `d/dz M(c,1/2,−z²) = −4cz·M(c+1,3/2,−z²)`. -/
private lemma hasDerivAt_kummerM_even (c z : ℝ) :
    HasDerivAt (fun t : ℝ => ₁F₁ c (1/2 : ℝ) (-t ^ 2))
      (-(4 * c * z * ₁F₁ (c + 1) (3/2 : ℝ) (-z ^ 2))) z := by
  have hM := kummerM_hasDerivAt c (1/2 : ℝ) (by norm_num) (-z ^ 2)
  have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * z)) z := by
    simpa using (hasDerivAt_pow 2 z).neg
  have h := hM.comp z hsq
  have hval : c / (1/2 : ℝ) * ₁F₁ (c + 1) (1/2 + 1 : ℝ) (-z ^ 2) * -(2 * z)
      = -(4 * c * z * ₁F₁ (c + 1) (3/2 : ℝ) (-z ^ 2)) := by
    rw [show (1/2 : ℝ) + 1 = 3/2 by norm_num]
    ring
  rw [hval] at h
  exact h

-- no-dlmf: product/chain-rule derivative of the odd Hermite-type Kummer
-- combination, closed by the half-ladder relation; support for 7.18.9
/-- `d/dz [z·M(c,3/2,−z²)] = M(c,1/2,−z²)`. -/
private lemma hasDerivAt_kummerM_odd (c z : ℝ) :
    HasDerivAt (fun t : ℝ => t * ₁F₁ c (3/2 : ℝ) (-t ^ 2))
      (₁F₁ c (1/2 : ℝ) (-z ^ 2)) z := by
  have hM := kummerM_hasDerivAt c (3/2 : ℝ) (by norm_num) (-z ^ 2)
  have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * z)) z := by
    simpa using (hasDerivAt_pow 2 z).neg
  have hcomp : HasDerivAt (fun t : ℝ => ₁F₁ c (3/2 : ℝ) (-t ^ 2))
      (c / (3/2 : ℝ) * ₁F₁ (c + 1) (3/2 + 1 : ℝ) (-z ^ 2) * -(2 * z)) z := hM.comp z hsq
  have h : HasDerivAt (fun t : ℝ => t * ₁F₁ c (3/2 : ℝ) (-t ^ 2))
      (1 * ₁F₁ c (3/2 : ℝ) (-z ^ 2)
        + z * (c / (3/2 : ℝ) * ₁F₁ (c + 1) (3/2 + 1 : ℝ) (-z ^ 2) * -(2 * z))) z :=
    (hasDerivAt_id z).mul hcomp
  have hval : 1 * ₁F₁ c (3/2 : ℝ) (-z ^ 2)
      + z * (c / (3/2 : ℝ) * ₁F₁ (c + 1) (3/2 + 1 : ℝ) (-z ^ 2) * -(2 * z))
      = ₁F₁ c (1/2 : ℝ) (-z ^ 2) := by
    rw [show (3/2 : ℝ) + 1 = 5/2 by norm_num]
    linear_combination -kummerM_half_ladder c (-z ^ 2)
  rw [hval] at h
  exact h

-- no-dlmf: real-argument specialization of Kummer's transformation (DLMF 13.2.39,
-- surfaced as `kummerM_kummer_transform`) at argument z²; support for 7.18.9
/-- `e^{−z²}·M(a,b,z²) = M(b−a,b,−z²)`. -/
private lemma exp_neg_sq_mul_kummerM (a b : ℝ) (hb : ∀ k : ℕ, (k : ℝ) ≠ -b) (z : ℝ) :
    Real.exp (-z ^ 2) * ₁F₁ a b (z ^ 2) = ₁F₁ (b - a) b (-z ^ 2) := by
  have h := kummerM_kummer_transform a b hb (z ^ 2 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  rw [h, ← mul_assoc, ← Real.exp_add]
  norm_num

-- no-dlmf: degenerate Kummer value M(0,b,x) = 1 (the series terminates at its
-- constant term); support for 7.18.9
private lemma kummerM_a_zero (b x : ℝ) : ₁F₁ (0 : ℝ) b x = 1 := by
  have h := kummerM_hasSum (0 : ℝ) b x
  have he : (fun n : ℕ => kummerCoefficient (0 : ℝ) b n * x ^ n)
      = fun n : ℕ => if n = 0 then 1 else 0 := by
    funext n
    cases n with
    | zero => simp [kummerCoefficient]
    | succ m => simp [kummerCoefficient, ascPochhammer_succ_eval' m (0 : ℝ)]
  rw [he] at h
  exact h.unique (hasSum_ite_eq 0 1)

-- no-dlmf: central value iⁿerfc(0) = 1/(2ⁿΓ(n/2+1)) (DLMF 7.18.6 at z = 0),
-- from the three-term recurrence 7.18.7 at z = 0; support for 7.18.9
/-- `iⁿerfc(0) = 1/(2ⁿ·Γ(n/2+1))`. -/
private lemma iRepErfc_zero_val (n : ℕ) :
    iRepErfc n 0 = 1 / (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [iRepErfc_zero_apply, erfc_zero]
    norm_num [Real.Gamma_one]
  | one =>
    have h := two_iRepErfc_one_add 0
    rw [erfc_zero] at h
    norm_num [Real.exp_zero] at h
    have hπ : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hΓ : Real.Gamma (((1:ℕ) : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
      rw [show (((1:ℕ) : ℝ) / 2 + 1) = 1/2 + 1 by norm_num,
        Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      ring
    rw [hΓ, pow_one]
    rw [show (2 : ℝ) * (Real.sqrt Real.pi / 2) = Real.sqrt Real.pi by ring]
    field_simp at h ⊢
    linarith
  | more n ih _ =>
    have h7 := erf_7_18_7 n 0
    simp only [mul_zero, zero_mul, sub_zero] at h7
    rw [ih] at h7
    have hne : (n : ℝ) / 2 + 1 ≠ 0 := by positivity
    have hΓrec : Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1)
        = ((n : ℝ) / 2 + 1) * Real.Gamma ((n : ℝ) / 2 + 1) := by
      rw [show ((n + 2 : ℕ) : ℝ) / 2 + 1 = ((n : ℝ) / 2 + 1) + 1 by push_cast; ring,
        Real.Gamma_add_one hne]
    rw [hΓrec]
    have hΓpos : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 := by
      have := Real.Gamma_pos_of_pos (show (0:ℝ) < (n : ℝ) / 2 + 1 by positivity)
      exact this.ne'
    set G := Real.Gamma ((n : ℝ) / 2 + 1) with hG
    have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp at h7 ⊢
    linear_combination 2 * h7

-- no-dlmf: the transformed-parameter (Hermite-type) form of DLMF 7.18.9, from
-- which the surface statement follows by Kummer's transformation; support lemma
/-- Transformed form of DLMF 7.18.9:
`iⁿerfc(w) = M(−n/2,1/2,−w²)/(2ⁿΓ(n/2+1)) − w·M(1/2−n/2,3/2,−w²)/(2^{n−1}Γ(n/2+1/2))`. -/
lemma erf_7_18_9_key (m : ℕ) (w : ℝ) :
    iRepErfc m w
      = ₁F₁ (-(m : ℝ) / 2) (1/2 : ℝ) (-w ^ 2) / (2 ^ m * Real.Gamma ((m : ℝ) / 2 + 1))
        - w * ₁F₁ ((1 : ℝ) / 2 - (m : ℝ) / 2) (3/2 : ℝ) (-w ^ 2)
            / ((2 : ℝ) ^ ((m : ℝ) - 1) * Real.Gamma ((m : ℝ) / 2 + 1/2)) := by
  induction m generalizing w with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, zero_div, pow_zero, zero_add, zero_sub, sub_zero]
    rw [kummerM_a_zero, Real.Gamma_one]
    rw [show ((2:ℝ) ^ (-1 : ℝ)) = 1/2 by
      rw [Real.rpow_neg_one]
      norm_num]
    rw [Real.Gamma_one_half_eq]
    rw [iRepErfc_zero_apply, erfc, erf_eq_kummerM]
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
  | succ m ih =>
    push_cast
    have hΓh : (0:ℝ) < Real.Gamma ((m:ℝ)/2 + 1/2) := Real.Gamma_pos_of_pos (by positivity)
    have hΓ1 : (0:ℝ) < Real.Gamma ((m:ℝ)/2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hΓCrec : Real.Gamma (((m:ℝ) + 1)/2 + 1)
        = ((m:ℝ)/2 + 1/2) * Real.Gamma ((m:ℝ)/2 + 1/2) := by
      rw [show ((m:ℝ) + 1)/2 + 1 = ((m:ℝ)/2 + 1/2) + 1 by ring,
        Real.Gamma_add_one (by positivity)]
    have hΓD : Real.Gamma (((m:ℝ) + 1)/2 + 1/2) = Real.Gamma ((m:ℝ)/2 + 1) := by
      rw [show ((m:ℝ) + 1)/2 + 1/2 = (m:ℝ)/2 + 1 by ring]
    have hrpowD : (2:ℝ) ^ ((m:ℝ) + 1 - 1) = 2 ^ m := by
      rw [show (m:ℝ) + 1 - 1 = ((m : ℕ) : ℝ) by ring, Real.rpow_natCast]
    have hrpowm : (2:ℝ) ^ ((m:ℝ) - 1) = 2 ^ m / 2 := by
      rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_one]
    have hgd : ∀ y : ℝ, HasDerivAt (fun t : ℝ => iRepErfc (m + 1) t
        - (₁F₁ (-((m:ℝ) + 1) / 2) (1/2 : ℝ) (-t ^ 2)
              / (2 ^ (m + 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1))
          - t * ₁F₁ ((1:ℝ)/2 - ((m:ℝ) + 1) / 2) (3/2 : ℝ) (-t ^ 2)
              / ((2:ℝ) ^ ((m:ℝ) + 1 - 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1/2)))) 0 y := by
      intro y
      have h1 := (hasDerivAt_kummerM_even (-((m:ℝ) + 1) / 2) y).div_const
        (2 ^ (m + 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1))
      have h2 := (hasDerivAt_kummerM_odd ((1:ℝ)/2 - ((m:ℝ) + 1) / 2) y).div_const
        ((2:ℝ) ^ ((m:ℝ) + 1 - 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1/2))
      have hd := (hasDerivAt_iRepErfc_succ m y).sub (h1.sub h2)
      have hval : -iRepErfc m y
          - (-(4 * (-((m:ℝ) + 1) / 2) * y * ₁F₁ (-((m:ℝ) + 1) / 2 + 1) (3/2 : ℝ) (-y ^ 2))
              / (2 ^ (m + 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1))
            - ₁F₁ ((1:ℝ)/2 - ((m:ℝ) + 1) / 2) (1/2 : ℝ) (-y ^ 2)
              / ((2:ℝ) ^ ((m:ℝ) + 1 - 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1/2))) = 0 := by
        rw [show -((m:ℝ) + 1) / 2 + 1 = (1:ℝ)/2 - (m:ℝ)/2 by ring,
          show (1:ℝ)/2 - ((m:ℝ) + 1) / 2 = -(m:ℝ)/2 by ring,
          hΓCrec, hΓD, hrpowD, ih y, hrpowm]
        have h2m : ((2:ℝ) ^ m) ≠ 0 := by positivity
        have hmm : ((m:ℝ)/2 + 1/2) ≠ 0 := by positivity
        field_simp
        ring
      rw [hval] at hd
      exact hd
    have hconst := fun y : ℝ =>
      is_const_of_deriv_eq_zero (fun t => (hgd t).differentiableAt)
        (fun t => (hgd t).deriv) y 0
    have hw := hconst w
    have hg0 : iRepErfc (m + 1) 0
        - (₁F₁ (-((m:ℝ) + 1) / 2) (1/2 : ℝ) (-(0:ℝ) ^ 2)
              / (2 ^ (m + 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1))
          - 0 * ₁F₁ ((1:ℝ)/2 - ((m:ℝ) + 1) / 2) (3/2 : ℝ) (-(0:ℝ) ^ 2)
              / ((2:ℝ) ^ ((m:ℝ) + 1 - 1) * Real.Gamma (((m:ℝ) + 1) / 2 + 1/2))) = 0 := by
      have hz := iRepErfc_zero_val (m + 1)
      push_cast at hz
      rw [hz, show (-(0:ℝ) ^ 2) = 0 by norm_num, kummerM_zero]
      simp
    rw [hg0] at hw
    linarith [hw]

-- no-dlmf: descending-factorial/Γ ratio `(−1)ʲ(−x)ⱼ/Γ(x+1) = 1/Γ(x−j+1)`, valid for
-- ALL real `x` under Mathlib's junk conventions (both sides vanish across the poles);
-- support for the 7.18.6 series split
private lemma gamma_ratio (x : ℝ) : ∀ j : ℕ,
    (-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (-x) / Real.Gamma (x + 1)
      = 1 / Real.Gamma (x - j + 1)
  | 0 => by simp
  | (j + 1) => by
    have ih := gamma_ratio x j
    rw [ascPochhammer_succ_eval]
    have h1 : (-1 : ℝ) ^ (j + 1) * ((ascPochhammer ℝ j).eval (-x) * (-x + j)) / Real.Gamma (x + 1)
        = (x - j) * ((-1 : ℝ) ^ j * (ascPochhammer ℝ j).eval (-x) / Real.Gamma (x + 1)) := by
      rw [pow_succ]; ring
    rw [h1, ih]
    by_cases hxj : x - j = 0
    · rw [show x - ((j : ℕ) + 1 : ℕ) + 1 = x - j by push_cast; ring, hxj, Real.Gamma_zero]
      simp
    · rw [show x - ((j : ℕ) + 1 : ℕ) + 1 = x - j by push_cast; ring]
      rw [show x - (j : ℝ) + 1 = (x - j) + 1 by ring, Real.Gamma_add_one hxj]
      rw [mul_one_div, div_mul_cancel_left₀ hxj, one_div]

-- no-dlmf: closed form (½)ⱼ = (2j)!/(4ʲ·j!) of the half-integer rising factorial;
-- reusable arithmetic identity, support for the 7.18.6 series split
private lemma ascPochhammer_half_eval (N : ℕ) :
    (ascPochhammer ℝ N).eval (1/2 : ℝ)
      = (Nat.factorial (2 * N) : ℝ) / (4 ^ N * (Nat.factorial N : ℝ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hfn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_natCast, ih]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

-- no-dlmf: closed form (³⁄₂)ⱼ = (2j+1)!/(4ʲ·j!) of the three-half rising factorial;
-- support for the 7.18.6 series split
private lemma ascPochhammer_threehalf_eval (N : ℕ) :
    (ascPochhammer ℝ N).eval (3/2 : ℝ)
      = (Nat.factorial (2 * N + 1) : ℝ) / (4 ^ N * (Nat.factorial N : ℝ)) := by
  have h := ascPochhammer_half_eval (N + 1)
  rw [ascPochhammer_succ_eval'] at h
  rw [show (1/2 : ℝ) + 1 = 3/2 by norm_num] at h
  have hfn : (Nat.factorial N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Nat.factorial_succ (2 * N + 1),
    Nat.factorial_succ N] at h
  push_cast at h ⊢
  have h4 : (4 : ℝ) ^ (N + 1) = 4 * 4 ^ N := by rw [pow_succ]; ring
  rw [h4] at h
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have h4N : (4 : ℝ) ^ N ≠ 0 := by positivity
  field_simp at h ⊢
  have hc : (4 * ((N : ℝ) + 1)) * (Polynomial.eval (3/2 : ℝ) (ascPochhammer ℝ N)
        * 4 ^ N * (Nat.factorial N : ℝ))
      = (4 * ((N : ℝ) + 1)) * ((Nat.factorial (2 * N + 1) : ℝ)) := by
    linear_combination h
  exact mul_left_cancel₀ (by positivity) hc

-- no-dlmf: even-index (k = 2j) coefficient identification for the 7.18.6 Maclaurin
-- series against the M(−n/2,1/2,−z²) term of the transformed 7.18.9 representation
lemma erf_7_18_6_even (n : ℕ) (z : ℝ) (j : ℕ) :
    kummerCoefficient (-(n : ℝ) / 2) (1/2 : ℝ) j * (-z ^ 2) ^ j
        / (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1))
      = (-1) ^ (2 * j) * z ^ (2 * j) /
          ((2 : ℝ) ^ ((n : ℝ) - (2 * j : ℕ)) * ((2 * j).factorial : ℝ) *
            Real.Gamma (1 + ((n : ℝ) - (2 * j : ℕ)) / 2)) := by
  have hgr := gamma_ratio ((n : ℝ) / 2) j
  rw [show -((n : ℝ) / 2) = -(n : ℝ) / 2 by ring] at hgr
  have hrpow : (2 : ℝ) ^ ((n : ℝ) - ((2 * j : ℕ) : ℝ)) = 2 ^ n / 4 ^ j := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_natCast, pow_mul]
    norm_num
  have hΓarg : (1 : ℝ) + ((n : ℝ) - ((2 * j : ℕ) : ℝ)) / 2 = (n : ℝ) / 2 - (j : ℝ) + 1 := by
    push_cast; ring
  rw [hrpow, hΓarg]
  rw [show ((-1 : ℝ)) ^ (2 * j) = 1 by rw [pow_mul]; norm_num]
  rw [show ((-z ^ 2 : ℝ)) ^ j = (-1) ^ j * z ^ (2 * j) by rw [neg_pow, ← pow_mul]]
  have hΓpos : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hfj : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hf2j : (Nat.factorial (2 * j) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2n : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have h4j : ((4 : ℝ) ^ j) ≠ 0 := by positivity
  calc kummerCoefficient (-(n : ℝ) / 2) (1/2 : ℝ) j * ((-1) ^ j * z ^ (2 * j))
        / (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1))
      = (z ^ (2 * j) * 4 ^ j / ((2 : ℝ) ^ n * (Nat.factorial (2 * j) : ℝ)))
          * ((-1) ^ j * (ascPochhammer ℝ j).eval (-(n : ℝ) / 2)
              / Real.Gamma ((n : ℝ) / 2 + 1)) := by
        simp only [kummerCoefficient, ascPochhammer_half_eval]
        field_simp
    _ = (z ^ (2 * j) * 4 ^ j / ((2 : ℝ) ^ n * (Nat.factorial (2 * j) : ℝ)))
          * (1 / Real.Gamma ((n : ℝ) / 2 - j + 1)) := by rw [hgr]
    _ = 1 * z ^ (2 * j) / (2 ^ n / 4 ^ j * ((2 * j).factorial : ℝ)
          * Real.Gamma ((n : ℝ) / 2 - j + 1)) := by
        conv_rhs => rw [← div_div]
        conv_lhs => rw [mul_one_div]
        congr 1
        field_simp

-- no-dlmf: odd-index (k = 2j+1) coefficient identification for the 7.18.6 Maclaurin
-- series against the z·M(1/2−n/2,3/2,−z²) term of the transformed 7.18.9 representation
lemma erf_7_18_6_odd (n : ℕ) (z : ℝ) (j : ℕ) :
    -(z * (kummerCoefficient ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) j * (-z ^ 2) ^ j)
        / ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1/2)))
      = (-1) ^ (2 * j + 1) * z ^ (2 * j + 1) /
          ((2 : ℝ) ^ ((n : ℝ) - (2 * j + 1 : ℕ)) * ((2 * j + 1).factorial : ℝ) *
            Real.Gamma (1 + ((n : ℝ) - (2 * j + 1 : ℕ)) / 2)) := by
  have hgr := gamma_ratio ((n : ℝ) / 2 - 1/2) j
  rw [show -((n : ℝ) / 2 - 1/2) = (1 : ℝ) / 2 - (n : ℝ) / 2 by ring,
    show (n : ℝ) / 2 - 1/2 + 1 = (n : ℝ) / 2 + 1/2 by ring] at hgr
  have hrpow : (2 : ℝ) ^ ((n : ℝ) - ((2 * j + 1 : ℕ) : ℝ))
      = (2 : ℝ) ^ ((n : ℝ) - 1) / 4 ^ j := by
    rw [show (n : ℝ) - ((2 * j + 1 : ℕ) : ℝ) = ((n : ℝ) - 1) - ((2 * j : ℕ) : ℝ) by
        push_cast; ring,
      Real.rpow_sub two_pos, Real.rpow_natCast, pow_mul]
    norm_num
  have hΓarg : (1 : ℝ) + ((n : ℝ) - ((2 * j + 1 : ℕ) : ℝ)) / 2
      = (n : ℝ) / 2 - 1/2 - (j : ℝ) + 1 := by
    push_cast; ring
  rw [hrpow, hΓarg]
  rw [show ((-1 : ℝ)) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
  rw [show ((-z ^ 2 : ℝ)) ^ j = (-1) ^ j * z ^ (2 * j) by rw [neg_pow, ← pow_mul]]
  have hΓpos : Real.Gamma ((n : ℝ) / 2 + 1/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hfj : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hf2j : (Nat.factorial (2 * j + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2r : ((2 : ℝ) ^ ((n : ℝ) - 1)) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  have h4j : ((4 : ℝ) ^ j) ≠ 0 := by positivity
  calc -(z * (kummerCoefficient ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) j
          * ((-1) ^ j * z ^ (2 * j)))
        / ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1/2)))
      = (-(z ^ (2 * j + 1)) * 4 ^ j
            / ((2 : ℝ) ^ ((n : ℝ) - 1) * (Nat.factorial (2 * j + 1) : ℝ)))
          * ((-1) ^ j * (ascPochhammer ℝ j).eval ((1 : ℝ) / 2 - (n : ℝ) / 2)
              / Real.Gamma ((n : ℝ) / 2 + 1/2)) := by
        simp only [kummerCoefficient, ascPochhammer_threehalf_eval]
        field_simp
        ring
    _ = (-(z ^ (2 * j + 1)) * 4 ^ j
            / ((2 : ℝ) ^ ((n : ℝ) - 1) * (Nat.factorial (2 * j + 1) : ℝ)))
          * (1 / Real.Gamma ((n : ℝ) / 2 - 1/2 - j + 1)) := by rw [hgr]
    _ = -1 * z ^ (2 * j + 1) / ((2 : ℝ) ^ ((n : ℝ) - 1) / 4 ^ j
          * ((2 * j + 1).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 - 1/2 - j + 1)) := by
        conv_rhs => rw [← div_div]
        conv_lhs => rw [mul_one_div]
        congr 1
        field_simp

-- no-dlmf: HasSum assembly of the 7.18.6 Maclaurin series (even/odd interleaving of
-- the two transformed Kummer series); support for erf_7_18_6
private lemma erf_7_18_6_hasSum (n : ℕ) (z : ℝ) :
    HasSum (fun k : ℕ =>
        (-1) ^ k * z ^ k /
          ((2 : ℝ) ^ ((n : ℝ) - k) * (k.factorial : ℝ) *
            Real.Gamma (1 + ((n : ℝ) - k) / 2)))
      (₁F₁ (-(n : ℝ) / 2) (1/2 : ℝ) (-z ^ 2) / (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1))
        - z * ₁F₁ ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) (-z ^ 2)
            / ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1/2))) := by
  rw [sub_eq_add_neg]
  refine HasSum.even_add_odd ?_ ?_
  · have He := (kummerM_hasSum (-(n : ℝ) / 2) (1/2 : ℝ) (-z ^ 2)).div_const
      (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1))
    have hfe : (fun j : ℕ => kummerCoefficient (-(n : ℝ) / 2) (1/2 : ℝ) j * (-z ^ 2) ^ j
          / (2 ^ n * Real.Gamma ((n : ℝ) / 2 + 1)))
        = fun j : ℕ => (-1) ^ (2 * j) * z ^ (2 * j) /
            ((2 : ℝ) ^ ((n : ℝ) - (2 * j : ℕ)) * ((2 * j).factorial : ℝ) *
              Real.Gamma (1 + ((n : ℝ) - (2 * j : ℕ)) / 2)) :=
      funext fun j => erf_7_18_6_even n z j
    rw [hfe] at He
    exact He
  · have Ho := (((kummerM_hasSum ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) (-z ^ 2)).mul_left
      z).div_const ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1/2))).neg
    have hfo : (fun j : ℕ => -(z * (kummerCoefficient ((1 : ℝ) / 2 - (n : ℝ) / 2) (3/2 : ℝ) j
            * (-z ^ 2) ^ j)
          / ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1/2))))
        = fun j : ℕ => (-1) ^ (2 * j + 1) * z ^ (2 * j + 1) /
            ((2 : ℝ) ^ ((n : ℝ) - (2 * j + 1 : ℕ)) * ((2 * j + 1).factorial : ℝ) *
              Real.Gamma (1 + ((n : ℝ) - (2 * j + 1 : ℕ)) / 2)) :=
      funext fun j => erf_7_18_6_odd n z j
    rw [hfo] at Ho
    exact Ho

end KummerSupport

-- no-dlmf: real-axis restriction of DLMF 7.18.6 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_6` (ComplexRepeatedErfc.lean)
/-- Maclaurin series of the real `iⁿerfc`:
`iⁿerfc(z) = ∑_{k≥0} (−1)ᵏ zᵏ / (2^{n−k} k! Γ(1+(n−k)/2))`.

The exponent `n−k` may be negative, so `2^{n−k}` is the real power `rpow`; at a
non-positive integer argument `Γ` has its pole and Mathlib's `Real.Gamma` is `0`
there, so the corresponding terms vanish — exactly as in the handbook truncation. -/
theorem erf_7_18_6 (n : ℕ) (z : ℝ) :
    iRepErfc n z =
      ∑' k : ℕ,
        (-1) ^ k * z ^ k /
          ((2 : ℝ) ^ ((n : ℝ) - k) * k.factorial *
            Real.Gamma (1 + ((n : ℝ) - k) / 2)) := by
  rw [erf_7_18_9_key n z]
  exact (erf_7_18_6_hasSum n z).tsum_eq.symm

-- no-dlmf: real-axis restriction of DLMF 7.18.9 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_9` (ComplexRepeatedErfc.lean)
/-- Kummer `M` (`₁F₁`) representation of the real `iⁿerfc`:
`iⁿerfc(z) = e^{−z²}( M(n/2+1/2,1/2,z²)/(2ⁿΓ(n/2+1))
              − z·M(n/2+1,3/2,z²)/(2^{n−1}Γ(n/2+1/2)) )`. -/
theorem erf_7_18_9 (n : ℕ) (z : ℝ) :
    iRepErfc n z =
      Real.exp (-z ^ 2) *
        (₁F₁ ((n : ℝ) / 2 + 1 / 2) (1 / 2) (z ^ 2) /
            ((2 : ℝ) ^ n * Real.Gamma ((n : ℝ) / 2 + 1))
          - z * ₁F₁ ((n : ℝ) / 2 + 1) (3 / 2) (z ^ 2) /
              ((2 : ℝ) ^ ((n : ℝ) - 1) * Real.Gamma ((n : ℝ) / 2 + 1 / 2))) := by
  have hA := exp_neg_sq_mul_kummerM ((n:ℝ)/2 + 1/2) (1/2) no_pole_half z
  have hB := exp_neg_sq_mul_kummerM ((n:ℝ)/2 + 1) (3/2) no_pole_threehalf z
  rw [show (1/2 : ℝ) - ((n:ℝ)/2 + 1/2) = -(n:ℝ)/2 by ring] at hA
  rw [show (3/2 : ℝ) - ((n:ℝ)/2 + 1) = (1:ℝ)/2 - (n:ℝ)/2 by ring] at hB
  rw [erf_7_18_9_key n z, ← hA, ← hB]
  ring

/-! ### Tricomi support kit for DLMF 7.18.10

The `n`-ladder of `U(n/2+1/2; 1/2; z²)` moves the first Tricomi parameter by
*half* steps at fixed `b = 1/2`, so neither the `(a,b) → (a+1,b+1)` derivative
ladder (`tricomiU_hasDerivAt`, DLMF 13.3.22) nor the contiguous relation
(`tricomiU_contiguous`) reaches it directly. What does close the loop is the
`b`-ladder relation `U(a;b;x) + (b−a−1)·U(a+1;b;x) = x·U(a+1;b+1;x)`
(`tricomiU_bLadder` below, proved here by parts from the defining integral),
which — combined with the `x`-derivative — turns `d/dz [e^{−z²}U(a;1/2;z²)]`
into a combination of the *same* member and the member two indices up.  The
repeated integrals satisfy the identical two-step relation (from the recurrence
7.18.7 and the derivative 7.18.3), so a two-step induction with the bases
`n = 0` (`erfc_eq_tricomiU_half`, DLMF 7.11.5) and `n = 1` (the `a = 0`
boundary instance `tricomiU_one_half_boundary`, with `erfc_eq_tricomiU`)
identifies the two families on `z > 0`. -/

section TricomiSupport

open FLMF.Hypergeometric

variable {a b x : ℝ}

-- no-dlmf: auxiliary potential `g(t) = e^{−xt} t^a (1+t)^{b−a−1}` for the
-- integration-by-parts proof of `tricomiU_bLadder`; no DLMF counterpart
private def tricomiPot (a b x t : ℝ) : ℝ :=
  Real.exp (-x * t) * t ^ a * (1 + t) ^ (b - a - 1)

-- no-dlmf: the derivative `g'(t)` of `tricomiPot`, expressed in the
-- Tricomi-integrand basis; no DLMF counterpart
private def tricomiPotDer (a b x t : ℝ) : ℝ :=
  a * tricomiIntegrand a b x t + (b - a - 1) * tricomiIntegrand (a + 1) b x t
    - x * tricomiIntegrand (a + 1) (b + 1) x t

-- no-dlmf: derivative of the auxiliary potential; proof infrastructure
private lemma tricomiPot_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => tricomiPot a b x t) (tricomiPotDer a b x t) t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-x * t)) (-x * Real.exp (-x * t)) t := by
    have hinner : HasDerivAt (fun t : ℝ => -x * t) (-x) t := by
      simpa using (hasDerivAt_id t).const_mul (-x)
    simpa [mul_comm] using hinner.exp
  have hta : HasDerivAt (fun t : ℝ => t ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have htb : HasDerivAt (fun t : ℝ => (1 + t) ^ (b - a - 1))
      ((b - a - 1) * (1 + t) ^ (b - a - 1 - 1)) t := by
    have := (Real.hasDerivAt_rpow_const (p := b - a - 1) (Or.inl h1t.ne')).comp t
      ((hasDerivAt_const t 1).add (hasDerivAt_id t))
    simpa using this
  have hmul := (hexp.mul hta).mul htb
  refine hmul.congr_deriv ?_
  simp only [tricomiPotDer, tricomiIntegrand, Pi.mul_apply]
  rw [show a + 1 - 1 = a by ring, show b - (a + 1) - 1 = b - a - 1 - 1 by ring,
    show b + 1 - (a + 1) - 1 = b - a - 1 by ring]
  ring

-- no-dlmf: continuity of the auxiliary potential at the left endpoint;
-- proof infrastructure
private lemma tricomiPot_continuousWithinAt (ha : 0 ≤ a) :
    ContinuousWithinAt (fun t => tricomiPot a b x t) (Ici 0) 0 := by
  apply ContinuousWithinAt.mul
  apply ContinuousWithinAt.mul
  · exact ((continuous_const.mul continuous_id).rexp).continuousWithinAt
  · exact (Real.continuousAt_rpow_const 0 a (Or.inr ha)).continuousWithinAt
  · have : ContinuousAt (fun t : ℝ => (1 + t) ^ (b - a - 1)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left; norm_num
    exact this.continuousWithinAt

-- no-dlmf: decay of the auxiliary potential at `+∞`; proof infrastructure
private lemma tricomiPot_tendsto_zero (hx : 0 < x) :
    Tendsto (fun t => tricomiPot a b x t) atTop (𝓝 0) := by
  set C : ℝ := max ((2 : ℝ) ^ (b - a - 1)) 1 with hC
  have hub : Tendsto (fun t : ℝ => C * (t ^ (b - 1) * Real.exp (-x * t))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b - 1) x hx).const_mul C
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h1t : (0 : ℝ) < 1 + t := by linarith
    simp only [tricomiPot]
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have hpow : (1 + t) ^ (b - a - 1) ≤ C * t ^ (b - a - 1) := by
      rcases le_or_gt 0 (b - a - 1) with hexp | hexp
      · calc (1 + t) ^ (b - a - 1) ≤ (2 * t) ^ (b - a - 1) :=
              Real.rpow_le_rpow (by linarith) (by linarith) hexp
          _ = (2 : ℝ) ^ (b - a - 1) * t ^ (b - a - 1) := Real.mul_rpow (by norm_num) htpos.le
          _ ≤ C * t ^ (b - a - 1) := by gcongr; exact le_max_left _ _
      · calc (1 + t) ^ (b - a - 1) ≤ t ^ (b - a - 1) :=
              Real.rpow_le_rpow_of_nonpos htpos (by linarith) hexp.le
          _ ≤ C * t ^ (b - a - 1) :=
              le_mul_of_one_le_left (Real.rpow_nonneg htpos.le _) (le_max_right _ _)
    have htab : t ^ a * t ^ (b - a - 1) = t ^ (b - 1) := by
      rw [← Real.rpow_add htpos]; ring_nf
    calc tricomiPot a b x t
        = Real.exp (-x * t) * t ^ a * (1 + t) ^ (b - a - 1) := rfl
      _ ≤ Real.exp (-x * t) * t ^ a * (C * t ^ (b - a - 1)) := by gcongr
      _ = C * (t ^ (b - 1) * Real.exp (-x * t)) := by
          rw [show Real.exp (-x * t) * t ^ a * (C * t ^ (b - a - 1))
            = C * ((t ^ a * t ^ (b - a - 1)) * Real.exp (-x * t)) by ring, htab]

-- no-dlmf: integrability of the derivative combination; proof infrastructure
private lemma tricomiPotDer_integrableOn (ha : 0 ≤ a) (hx : 0 < x) :
    IntegrableOn (fun t => tricomiPotDer a b x t) (Ioi 0) := by
  have h1 := tricomiU_integrand_integrableOn (a := a + 1) (b := b) (by linarith) hx
  have h2 := tricomiU_integrand_integrableOn (a := a + 1) (b := b + 1) (by linarith) hx
  have h0 : IntegrableOn (fun t => a * tricomiIntegrand a b x t) (Ioi 0) := by
    rcases ha.lt_or_eq with hpos | hzero
    · exact (tricomiU_integrand_integrableOn hpos hx).const_mul a
    · rw [← hzero]
      simp only [zero_mul]
      exact integrable_zero ℝ ℝ _
  unfold tricomiPotDer
  exact (h0.add (h1.const_mul (b - a - 1))).sub (h2.const_mul x)

-- no-dlmf: the fundamental theorem of calculus on `(0,∞)` for the auxiliary
-- potential; proof infrastructure
private lemma tricomiPotDer_integral (ha : 0 ≤ a) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), tricomiPotDer a b x t) = -tricomiPot a b x 0 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (tricomiPot_continuousWithinAt ha)
    (fun t ht => tricomiPot_hasDerivAt ht) (tricomiPotDer_integrableOn ha hx)
    (tricomiPot_tendsto_zero hx)]
  ring

-- no-dlmf: local instance of the Tricomi `b`-ladder contiguous relation (the
-- DLMF 13.3 family), proved here by parts from the defining integral 13.4.4.
-- The Confluent framework carries only the `(a,b) → (a+2,b+2)` form
-- (`tricomiU_contiguous`), which does not reach the `b`-shift used by 7.18.10;
-- support lemma, not a display surface
/-- `U(a;b;x) + (b−a−1)·U(a+1;b;x) = x·U(a+1;b+1;x)` for `a > 0`, `x > 0`. -/
private lemma tricomiU_bLadder (ha : 0 < a) (hx : 0 < x) :
    tricomiU a b x + (b - a - 1) * tricomiU (a + 1) b x = x * tricomiU (a + 1) (b + 1) x := by
  have hint := tricomiPotDer_integral (a := a) (b := b) (x := x) ha.le hx
  have h0 : tricomiPot a b x 0 = 0 := by simp [tricomiPot, Real.zero_rpow ha.ne']
  rw [h0, neg_zero] at hint
  have hsplit : (∫ t in Ioi (0 : ℝ), tricomiPotDer a b x t)
      = a * (∫ t in Ioi (0 : ℝ), tricomiIntegrand a b x t)
        + (b - a - 1) * (∫ t in Ioi (0 : ℝ), tricomiIntegrand (a + 1) b x t)
        - x * (∫ t in Ioi (0 : ℝ), tricomiIntegrand (a + 1) (b + 1) x t) := by
    have h1 := tricomiU_integrand_integrableOn (a := a + 1) (b := b) (by linarith) hx
    have h2 := tricomiU_integrand_integrableOn (a := a + 1) (b := b + 1) (by linarith) hx
    have h0' := tricomiU_integrand_integrableOn (a := a) (b := b) ha hx
    have hA : IntegrableOn (fun t => a * tricomiIntegrand a b x t) (Ioi 0) := h0'.const_mul a
    have hB : IntegrableOn (fun t => (b - a - 1) * tricomiIntegrand (a + 1) b x t) (Ioi 0) :=
      h1.const_mul _
    have hC : IntegrableOn (fun t => x * tricomiIntegrand (a + 1) (b + 1) x t) (Ioi 0) :=
      h2.const_mul x
    have hAB : IntegrableOn (fun t => a * tricomiIntegrand a b x t
        + (b - a - 1) * tricomiIntegrand (a + 1) b x t) (Ioi 0) := hA.add hB
    unfold tricomiPotDer
    rw [integral_sub hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hsplit, integral_tricomiIntegrand ha,
    integral_tricomiIntegrand (by linarith : (0:ℝ) < a + 1),
    integral_tricomiIntegrand (by linarith : (0:ℝ) < a + 1)] at hint
  have hΓ1 : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha.ne'
  rw [hΓ1] at hint
  have hΓa : (0 : ℝ) < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have key : a * Real.Gamma a *
      (tricomiU a b x + (b - a - 1) * tricomiU (a + 1) b x
        - x * tricomiU (a + 1) (b + 1) x) = 0 := by linear_combination hint
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (by positivity)
  · linarith [sub_eq_zero.1 h]

-- no-dlmf: the `a = 0` boundary instance of the same integration by parts
-- (where the potential does *not* vanish at `t = 0`, contributing the `2`);
-- support lemma for the `n = 1` base case of 7.18.10
/-- `U(1;1/2;x) = 2 − 2x·U(1;3/2;x)` for `x > 0`. -/
private lemma tricomiU_one_half_boundary (hx : 0 < x) :
    tricomiU 1 (1 / 2) x = 2 - 2 * x * tricomiU 1 (3 / 2) x := by
  have hint := tricomiPotDer_integral (a := 0) (b := 1 / 2) (x := x) le_rfl hx
  have h0 : tricomiPot 0 (1 / 2 : ℝ) x 0 = 1 := by simp [tricomiPot]
  rw [h0] at hint
  have hfun : (fun t => tricomiPotDer 0 (1 / 2 : ℝ) x t)
      = fun t => -(1 / 2 : ℝ) * tricomiIntegrand 1 (1 / 2) x t
          - x * tricomiIntegrand 1 (3 / 2) x t := by
    funext t
    simp only [tricomiPotDer]
    rw [show (0 : ℝ) + 1 = 1 by norm_num, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    ring
  rw [hfun] at hint
  have h1 := tricomiU_integrand_integrableOn (a := (1 : ℝ)) (b := (1 / 2 : ℝ)) one_pos hx
  have h2 := tricomiU_integrand_integrableOn (a := (1 : ℝ)) (b := (3 / 2 : ℝ)) one_pos hx
  have hA : IntegrableOn (fun t => -(1 / 2 : ℝ) * tricomiIntegrand 1 (1 / 2) x t) (Ioi 0) :=
    h1.const_mul _
  have hB : IntegrableOn (fun t => x * tricomiIntegrand 1 (3 / 2) x t) (Ioi 0) := h2.const_mul x
  rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
    integral_tricomiIntegrand (by norm_num : (0:ℝ) < 1),
    integral_tricomiIntegrand (by norm_num : (0:ℝ) < 1), Real.Gamma_one] at hint
  linarith

-- no-dlmf: private kit definition for the 7.18.10 induction — the (cleared)
-- right-hand side `e^{−z²}·U(n/2+1/2; 1/2; z²)` of DLMF 7.18.10
private noncomputable def repErfcU (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (-z ^ 2) * tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) (z ^ 2)

-- no-dlmf: two-step derivative relation for the repeated integrals, from the
-- recurrence 7.18.7 and the derivative relation 7.18.3; proof infrastructure
/-- `d/dz [2ⁿ√π·iⁿerfc(z)] = (−(2z²+n+1)·2ⁿ√π·iⁿerfc(z)
  + ((n+1)(n+2)/2)·2^{n+2}√π·i^{n+2}erfc(z))/z`. -/
private lemma iRepErfc_hasDerivAt_two_step (n : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w => iRepErfc n w * ((2 : ℝ) ^ n * Real.sqrt Real.pi))
      ((-(2 * z ^ 2 + ((n : ℝ) + 1)) * (iRepErfc n z * ((2 : ℝ) ^ n * Real.sqrt Real.pi))
        + ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2
          * (iRepErfc (n + 2) z * ((2 : ℝ) ^ (n + 2) * Real.sqrt Real.pi))) / z) z := by
  have hzne : z ≠ 0 := hz.ne'
  cases n with
  | zero =>
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have hd : HasDerivAt (fun w => iRepErfc 0 w)
        (-(2 / Real.sqrt Real.pi * Real.exp (-z ^ 2))) z := hasDerivAt_erfc z
    have h := hd.mul_const ((2 : ℝ) ^ (0 : ℕ) * Real.sqrt Real.pi)
    have hval : -(2 / Real.sqrt Real.pi * Real.exp (-z ^ 2))
          * ((2 : ℝ) ^ (0 : ℕ) * Real.sqrt Real.pi)
        = -(2 * Real.exp (-z ^ 2)) := by field_simp
    rw [hval] at h
    refine h.congr_deriv ?_
    have h7 := erf_7_18_7 0 z
    have hseed := two_iRepErfc_one_add z
    have hseed' : Real.sqrt Real.pi * (2 * iRepErfc 1 z + 2 * z * erfc z)
        = 2 * Real.exp (-z ^ 2) := by rw [hseed]; field_simp
    simp only [Nat.cast_zero, pow_zero, iRepErfc_zero_apply, zero_add] at h7 ⊢
    rw [eq_comm, div_eq_iff hzne]
    linear_combination (-z) * hseed' + Real.sqrt Real.pi * h7
  | succ m =>
    have hd : HasDerivAt (fun w => iRepErfc (m + 1) w) (-iRepErfc m z) z :=
      hasDerivAt_iRepErfc_succ m z
    have h := hd.mul_const ((2 : ℝ) ^ (m + 1) * Real.sqrt Real.pi)
    refine h.congr_deriv ?_
    have h7a := erf_7_18_7 m z
    have h7b := erf_7_18_7 (m + 1) z
    have e1 : m + 1 + 2 = m + 3 := rfl
    have e2 : m + 1 + 1 = m + 2 := rfl
    rw [e1, e2] at h7b
    push_cast at h7a h7b ⊢
    rw [eq_comm, div_eq_iff hzne]
    linear_combination (-(2 : ℝ) ^ (m + 1) * Real.sqrt Real.pi * z) * h7a
      + ((2 : ℝ) ^ (m + 1) * Real.sqrt Real.pi * ((m : ℝ) + 2)) * h7b

-- no-dlmf: the matching two-step derivative relation on the Tricomi side, from
-- the `x`-derivative 13.3.22 and the `b`-ladder `tricomiU_bLadder`;
-- proof infrastructure
private lemma repErfcU_hasDerivAt_two_step (n : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (repErfcU n)
      ((-(2 * z ^ 2 + ((n : ℝ) + 1)) * repErfcU n z
        + ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 * repErfcU (n + 2) z) / z) z := by
  have hzne : z ≠ 0 := hz.ne'
  have ha : (0 : ℝ) < (n : ℝ) / 2 + 1 / 2 := by positivity
  have hx : (0 : ℝ) < z ^ 2 := by positivity
  have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hU : HasDerivAt (fun w : ℝ => tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) (w ^ 2))
      (-((n : ℝ) / 2 + 1 / 2) * tricomiU ((n : ℝ) / 2 + 1 / 2 + 1) (1 / 2 + 1) (z ^ 2) * (2 * z))
      z := by
    have h := HasDerivAt.comp (h := fun w : ℝ => w ^ 2)
      (h₂ := fun y : ℝ => tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) y) z
      (tricomiU_hasDerivAt (a := (n : ℝ) / 2 + 1 / 2) (b := 1 / 2) ha hx) hsq
    simpa using h
  have hE : HasDerivAt (fun w : ℝ => Real.exp (-w ^ 2)) (Real.exp (-z ^ 2) * -(2 * z)) z := by
    have hsq2 : HasDerivAt (fun w : ℝ => -w ^ 2) (-(2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).neg
    exact hsq2.exp
  have h := hE.mul hU
  refine h.congr_deriv ?_
  have hlad := tricomiU_bLadder (a := (n : ℝ) / 2 + 1 / 2) (b := 1 / 2) (x := z ^ 2) ha hx
  have hidx : ((n : ℝ) + 2) / 2 + 1 / 2 = (n : ℝ) / 2 + 1 / 2 + 1 := by ring
  simp only [repErfcU]
  push_cast
  rw [hidx, eq_comm, div_eq_iff hzne]
  linear_combination (-((n : ℝ) + 1) * Real.exp (-z ^ 2)) * hlad

-- no-dlmf: cleared (division-free) form of DLMF 7.18.10, proved by two-step
-- induction; the display surface is `erf_7_18_10` below
private lemma iRepErfc_mul_eq_repErfcU (n : ℕ) : ∀ z : ℝ, 0 < z →
    iRepErfc n z * ((2 : ℝ) ^ n * Real.sqrt Real.pi) = repErfcU n z := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro z hz
    have h := erfc_eq_tricomiU_half hz
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    simp only [repErfcU, Nat.cast_zero, pow_zero, iRepErfc_zero_apply]
    rw [show (0 : ℝ) / 2 + 1 / 2 = 1 / 2 by norm_num, h]
    field_simp
  | one =>
    intro z hz
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have hb := tricomiU_one_half_boundary (x := z ^ 2) (by positivity)
    have hE := erfc_eq_tricomiU hz
    have hseed := two_iRepErfc_one_add z
    have hseed' : Real.sqrt Real.pi * (2 * iRepErfc 1 z + 2 * z * erfc z)
        = 2 * Real.exp (-z ^ 2) := by rw [hseed]; field_simp
    have hE' : Real.sqrt Real.pi * erfc z
        = z * (Real.exp (-z ^ 2) * tricomiU 1 (3 / 2) (z ^ 2)) := by
      rw [hE]; field_simp
    simp only [repErfcU, Nat.cast_one]
    rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, hb]
    linear_combination hseed' - 2 * z * hE'
  | more n ih _ =>
    intro z hz
    have hzne : z ≠ 0 := hz.ne'
    have hP := iRepErfc_hasDerivAt_two_step n hz
    have hS := repErfcU_hasDerivAt_two_step n hz
    have heq : (fun w => iRepErfc n w * ((2 : ℝ) ^ n * Real.sqrt Real.pi))
        =ᶠ[nhds z] repErfcU n := by
      filter_upwards [Ioi_mem_nhds hz] with w hw using ih w hw
    have hP' := hP.congr_of_eventuallyEq heq.symm
    have huniq := hP'.unique hS
    rw [div_eq_div_iff hzne hzne] at huniq
    have huniq' := mul_right_cancel₀ hzne huniq
    rw [ih z hz] at huniq'
    have hcoef : (((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ≠ 0 := by positivity
    refine mul_left_cancel₀ hcoef ?_
    linear_combination huniq'

end TricomiSupport

-- no-dlmf: real-axis restriction of DLMF 7.18.10 over the real `tricomiU`;
-- the canonical carrier is the complex `cerf_7_18_10`
-- (Error/ComplexTricomi.lean, over `tricomiUC`)
/-- Tricomi `U` representation of `iⁿerfc` (7.18.10, real form): for `z > 0`,
`iⁿerfc(z) = e^{−z²}/(2ⁿ√π) · U(n/2+1/2, 1/2, z²)`.
(Hypothesis `0 < z` added 2026-06-25: the U-representation uses `z²`, losing the
sign, so it holds only for `z > 0` — at `z = −0.8` the two sides give 1.112 vs 0.028.
See ERRATA.) The faithful complex surface is `cerf_7_18_10`
(Error/ComplexTricomi.lean). -/
theorem erf_7_18_10 (n : ℕ) {z : ℝ} (hz : 0 < z) :
    iRepErfc n z =
      Real.exp (-z ^ 2) / ((2 : ℝ) ^ n * Real.sqrt Real.pi) *
        FLMF.Hypergeometric.tricomiU ((n : ℝ) / 2 + 1 / 2) (1 / 2) (z ^ 2) := by
  have h := iRepErfc_mul_eq_repErfcU n z hz
  have hne : ((2 : ℝ) ^ n * Real.sqrt Real.pi) ≠ 0 := by positivity
  simp only [repErfcU] at h
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination h

-- no-dlmf: real-axis restriction of DLMF 7.18.11 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_11` (ComplexRepeatedErfc.lean)
/-- Parabolic cylinder `U` representation of the real `iⁿerfc`:
`iⁿerfc(x) = e^{−x²/2}/(2^{(n−1)/2}√π) · U(n+1/2, x√2)`,
with `U` the real parabolic cylinder function `FLMF.ParabolicCylinder.U`.
(Corrected 2026-06-27 via the Numerical fidelity sweep: the prefactor exponent is
`(n−1)/2`, not `n−1` — off by a constant factor `(√2)^{n−1}`. See docs/ERRATA.md.) -/
theorem erf_7_18_11 (n : ℕ) (z : ℝ) :
    iRepErfc n z =
      Real.exp (-z ^ 2 / 2) / ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) * Real.sqrt Real.pi) *
        FLMF.ParabolicCylinder.U ((n : ℝ) + 1 / 2) (z * Real.sqrt 2) := by
  rw [erf_7_18_9 n z, FLMF.ParabolicCylinder.U, FLMF.ParabolicCylinder.pcfEven,
    FLMF.ParabolicCylinder.pcfOdd]
  rw [show (z * Real.sqrt 2) ^ 2 = 2 * z ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring]
  rw [show -(2 * z ^ 2) / 4 = -z ^ 2 / 2 by ring,
    show 2 * z ^ 2 / 2 = z ^ 2 by ring,
    show ((n:ℝ) + 1/2)/2 + 1/4 = (n:ℝ)/2 + 1/2 by ring,
    show ((n:ℝ) + 1/2)/2 + 3/4 = (n:ℝ)/2 + 1 by ring,
    show (3:ℝ)/4 + ((n:ℝ) + 1/2)/2 = (n:ℝ)/2 + 1 by ring,
    show (1:ℝ)/4 + ((n:ℝ) + 1/2)/2 = (n:ℝ)/2 + 1/2 by ring,
    show -1/4 - ((n:ℝ) + 1/2)/2 = -((1:ℝ)/2) - (n:ℝ)/2 by ring,
    show 1/4 - ((n:ℝ) + 1/2)/2 = -((n:ℝ)/2) by ring]
  have hCne : ((2:ℝ) ^ (((n : ℝ) - 1) / 2)) ≠ 0 := by positivity
  have hA' : (2:ℝ) ^ (-((1:ℝ)/2) - (n:ℝ)/2) = 1/2 / (2:ℝ) ^ (((n:ℝ) - 1)/2) := by
    rw [eq_div_iff hCne, ← Real.rpow_add two_pos,
      show -((1:ℝ)/2) - (n:ℝ)/2 + ((n:ℝ) - 1)/2 = (-1 : ℝ) by ring, Real.rpow_neg_one]
    norm_num
  have hB' : (2:ℝ) ^ (-((n:ℝ)/2)) = (Real.sqrt 2)⁻¹ / (2:ℝ) ^ (((n:ℝ) - 1)/2) := by
    rw [eq_div_iff hCne, ← Real.rpow_add two_pos,
      show -((n:ℝ)/2) + ((n:ℝ) - 1)/2 = (-(1/2) : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  have hD : (2:ℝ) ^ ((n:ℝ) - 1) = 2 ^ n / 2 := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_one]
  have hCC : (2:ℝ) ^ (((n:ℝ) - 1)/2) * (2:ℝ) ^ (((n:ℝ) - 1)/2) = 2 ^ n / 2 := by
    rw [← Real.rpow_add two_pos,
      show ((n:ℝ) - 1)/2 + ((n:ℝ) - 1)/2 = (n:ℝ) - 1 by ring, hD]
  have hexp : Real.exp (-z ^ 2 / 2) * Real.exp (-z ^ 2 / 2) = Real.exp (-z ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hA', hB', hD, ← hexp]
  have hmul2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hπne : Real.sqrt Real.pi ≠ 0 := by positivity
  have hΓ1 : Real.Gamma ((n:ℝ)/2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (n:ℝ)/2 + 1)).ne'
  have hΓh : Real.Gamma ((n:ℝ)/2 + 1/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (n:ℝ)/2 + 1/2)).ne'
  have h2n : ((2:ℝ) ^ n) ≠ 0 := by positivity
  set MA := ₁F₁ ((n : ℝ) / 2 + 1 / 2) (1 / 2) (z ^ 2) with hMA
  set MB := ₁F₁ ((n : ℝ) / 2 + 1) (3 / 2) (z ^ 2) with hMB
  set G1 := Real.Gamma ((n:ℝ)/2 + 1) with hG1
  set Gh := Real.Gamma ((n:ℝ)/2 + 1/2) with hGh
  set C := (2:ℝ) ^ (((n:ℝ) - 1)/2) with hC
  set E := Real.exp (-z ^ 2 / 2) with hE
  have hCC' : 2 * (C * C) = 2 ^ n := by
    rw [hCC]
    ring
  field_simp
  linear_combination (E ^ 2 * MA * Gh - 2 * E ^ 2 * G1 * z * MB) * hCC'

/-- The repeated-integral probability function `Hhₙ(x) = (1/n!) ∫ₓ^∞ (t-x)ⁿ e^{-t²/2} dt` (DLMF §7.18).

DLMF 7.18.
-/
-- DAG: E-7.18.
-- Verified: unverified
noncomputable def Hh (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∫ t in Set.Ioi x, (t - x) ^ n * Real.exp (-t ^ 2 / 2)

-- no-dlmf: real-axis restriction of DLMF 7.18.12 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_12` (ComplexRepeatedErfc.lean)
/-- Probability-function representation of the real `iⁿerfc`:
`iⁿerfc(z) = √2/((√2)ⁿ·√π)·Hhₙ(√2·z)`, with `Hh` the repeated-integral
probability function above. (The prefactor `√2/(√2)ⁿ = 2^{(1−n)/2} = 1/2^{(n−1)/2}`
is written with a `ℕ`-power `(√2)ⁿ` to avoid a half-integer/cast exponent.)
(Corrected 2026-06-24 via the Numerical fidelity sweep + DLMF: the argument is `√2·z`
(not `2z`) and the prefactor exponent is `(n−1)/2` (a ½ the OCR/web source had
dropped); verified to match `iⁿerfc` for n=0..4. See docs/ERRATA.md.) -/
theorem erf_7_18_12 (n : ℕ) (z : ℝ) :
    iRepErfc n z
      = (Real.sqrt 2 / ((Real.sqrt 2) ^ n * Real.sqrt π)) * Hh n (Real.sqrt 2 * z) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have h := MeasureTheory.integral_comp_mul_left_Ioi
      (fun t => (t - Real.sqrt 2 * z) ^ n * Real.exp (-t ^ 2 / 2)) z hs2
  have hcong : ∀ u ∈ Ioi z,
      (Real.sqrt 2 * u - Real.sqrt 2 * z) ^ n * Real.exp (-(Real.sqrt 2 * u) ^ 2 / 2)
        = (Real.sqrt 2) ^ n * ((u - z) ^ n * Real.exp (-u ^ 2)) := by
    intro u _
    have he : -(Real.sqrt 2 * u) ^ 2 / 2 = -u ^ 2 := by
      rw [mul_pow]
      rw [show (Real.sqrt 2) ^ 2 = 2 from by rw [sq, hmul]]
      ring
    rw [he, ← mul_sub, mul_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcong] at h
  rw [MeasureTheory.integral_const_mul, smul_eq_mul] at h
  have h' : (Real.sqrt 2) ^ n * (∫ u in Ioi z, (u - z) ^ n * Real.exp (-u ^ 2))
      = (Real.sqrt 2)⁻¹ * ∫ t in Ioi (Real.sqrt 2 * z),
          (t - Real.sqrt 2 * z) ^ n * Real.exp (-t ^ 2 / 2) := h
  have hJ : (∫ t in Ioi (Real.sqrt 2 * z), (t - Real.sqrt 2 * z) ^ n * Real.exp (-t ^ 2 / 2))
      = Real.sqrt 2 * ((Real.sqrt 2) ^ n *
          ∫ u in Ioi z, (u - z) ^ n * Real.exp (-u ^ 2)) := by
    rw [h']
    field_simp
  have hpull : (∫ t in Ioi z, (t - z) ^ n / n.factorial * Real.exp (-t ^ 2))
      = (n.factorial : ℝ)⁻¹ * ∫ u in Ioi z, (u - z) ^ n * Real.exp (-u ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [iRepErfc_eq_integral_closedForm n z, hpull, Hh, hJ]
  set I := ∫ u in Ioi z, (u - z) ^ n * Real.exp (-u ^ 2) with hI
  have hp2 : (Real.sqrt 2) ^ n ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [sq, hmul]

/-! ### Support kit for the DLMF 7.18.13 continued fraction

Strict positivity of `iⁿerfc`, the fraction's `GenContFract` packaging, its exact
tails (ratios of consecutive repeated integrals, via the three-term recurrence
7.18.7), and the Stieltjes gap estimates feeding the method kit of
`FLMF.Methods.ContinuedFraction` — the same route as `erf_7_9_1`. -/

-- no-dlmf: strict positivity of iⁿerfc; analytic infrastructure, no DLMF identity
/-- `iⁿerfc(z) > 0` for every real `z`: the tail integral of a strictly positive
integrand over an infinite half-line, by induction on `n`. -/
theorem iRepErfc_pos (n : ℕ) (z : ℝ) : 0 < iRepErfc n z := by
  induction n generalizing z with
  | zero =>
    rw [iRepErfc_zero_apply, erfc_eq_tail_global]
    have hgi : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi z) := by
      have h : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
        simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
      exact h.integrableOn
    have hpos : 0 < ∫ t in Ioi z, Real.exp (-t ^ 2) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun t => (Real.exp_pos _).le) hgi]
      have hsup : Function.support (fun t : ℝ => Real.exp (-t ^ 2)) = Set.univ := by
        ext t
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact (Real.exp_pos _).ne'
      rw [hsup, Set.univ_inter, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    have hc : (0 : ℝ) < 2 / Real.sqrt Real.pi := by positivity
    exact mul_pos hc hpos
  | succ n ih =>
    rw [iRepErfc_succ_eq]
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun t => (ih t).le) (integrableOn_iRepErfc n z)]
    have hsup : Function.support (iRepErfc n) = Set.univ := by
      ext t
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (ih t).ne'
    rw [hsup, Set.univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top

-- no-dlmf: partial numerators of the DLMF 7.18.13 fraction; private kit sequence
/-- Partial numerators of the DLMF 7.18.13 fraction, as a one-parameter family in
`ν` (`a 1 = 1/2`, `a k = (ν+k)/2` for `k ≥ 2`): `ν = n` is the `a`-sequence of
`erf_7_18_13`, and the boundary value `ν = −1` is the DLMF `n = 0` case of
`erf_7_18_13_general`.  Everything below needs only `ν ≥ −1` (which is what keeps
the partial numerators positive). -/
private noncomputable def repA (ν : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else (ν + k) / 2

-- no-dlmf: partial denominators of the DLMF 7.18.13 fraction; private kit sequence
/-- Partial denominators of the DLMF 7.18.13 fraction (constant `z`). -/
private noncomputable def repB (z : ℝ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else z

-- no-dlmf: GenContFract packaging of the 7.18.13 fraction; private kit definition
/-- The DLMF 7.18.13 continued fraction packaged as a (non-terminating)
`GenContFract`, so the method kit of `FLMF.Methods.ContinuedFraction` applies. -/
private noncomputable def repCF (ν : ℝ) (z : ℝ) : GenContFract ℝ :=
  ⟨repB z 0, ⟨fun m => some ⟨repA ν (m + 1), repB z (m + 1)⟩, fun {m} h => by simp at h⟩⟩

-- no-dlmf: private kit lemma (sequence access)
/-- The `m`-th partial pair of `repCF` is `⟨a (m+1), b (m+1)⟩`. -/
private lemma repCF_s_get? (ν : ℝ) (z : ℝ) (m : ℕ) :
    (repCF ν z).s.get? m = some ⟨repA ν (m + 1), repB z (m + 1)⟩ := rfl

-- no-dlmf: private kit lemma (positivity of partial numerators)
private lemma repA_pos {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) (k : ℕ) (hk : k ≠ 0) : 0 < repA ν k := by
  unfold repA
  rcases eq_or_ne k 1 with rfl | h1
  · norm_num
  · have hk2 : 2 ≤ k := by omega
    rw [if_neg hk, if_neg h1]
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith

-- no-dlmf: private kit lemma (positivity of partial denominators)
private lemma repB_pos {z : ℝ} (hz : 0 < z) (k : ℕ) (hk : k ≠ 0) : 0 < repB z k := by
  unfold repB
  rw [if_neg hk]
  exact hz

-- no-dlmf: private kit lemma (value of partial numerators for k ≥ 2)
private lemma repA_val (ν : ℝ) {k : ℕ} (hk : 2 ≤ k) : repA ν k = (ν + k) / 2 := by
  unfold repA
  rw [if_neg (by omega), if_neg (by omega)]

-- no-dlmf: private kit lemma (value of partial denominators for k ≥ 1)
private lemma repB_val {z : ℝ} {k : ℕ} (hk : k ≠ 0) : repB z k = z := by
  unfold repB
  rw [if_neg hk]

-- no-dlmf: private kit lemma (numerator continuants agree with the Wallis cfNum)
private lemma repCF_num (ν : ℝ) (z : ℝ) :
    ∀ m, (repCF ν z).nums m = cfNum (repA ν) (repB z) m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_num_eq_h]
    rfl
  | one =>
    rw [GenContFract.first_num_eq (repCF_s_get? ν z 0)]
    rfl
  | more m ih ih1 =>
    have h := GenContFract.nums_recurrence (repCF_s_get? ν z (m + 1)) ih ih1
    simpa [cfNum] using h

-- no-dlmf: private kit lemma (denominator continuants agree with the Wallis cfDen)
private lemma repCF_den (ν : ℝ) (z : ℝ) :
    ∀ m, (repCF ν z).dens m = cfDen (repA ν) (repB z) m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_den_eq_one]
    rfl
  | one =>
    rw [GenContFract.first_den_eq (repCF_s_get? ν z 0)]
    rfl
  | more m ih ih1 =>
    have h := GenContFract.dens_recurrence (repCF_s_get? ν z (m + 1)) ih ih1
    simpa [cfDen] using h

-- no-dlmf: private kit lemma (cfConv equals the GenContFract convergents)
private lemma repCF_conv (ν : ℝ) (z : ℝ) (m : ℕ) :
    cfConv (repA ν) (repB z) m = (repCF ν z).convs m := by
  rw [cfConv, GenContFract.conv_eq_num_div_den, repCF_num, repCF_den]

-- no-dlmf: private kit lemma (Stieltjes positivity of the fraction)
private lemma repCF_pos {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) :
    ∀ m gp, (repCF ν z).s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b := by
  intro m gp h
  rw [repCF_s_get?, Option.some.injEq] at h
  subst h
  exact ⟨repA_pos hν (m + 1) (by omega), repB_pos hz (m + 1) (by omega)⟩

-- no-dlmf: exact tails of the DLMF 7.18.13 fraction; private kit definition
/-- Exact tails of the DLMF 7.18.13 fraction: `t 0` is the target ratio
`i^{n+1}erfc(z)/iⁿerfc(z)`, and for `m ≥ 1` the weighted ratios
`(n+m+1)·i^{n+m+1}erfc(z)/i^{n+m}erfc(z)`. -/
private noncomputable def repTail (n : ℕ) (z : ℝ) : ℕ → ℝ
  | 0 => iRepErfc (n + 1) z / iRepErfc n z
  | (m + 1) => ((n : ℝ) + m + 2) * iRepErfc (n + m + 2) z / iRepErfc (n + m + 1) z

-- no-dlmf: private kit lemma (tail positivity)
private lemma repTail_pos (n : ℕ) (z : ℝ) (m : ℕ) : 0 < repTail n z m := by
  cases m with
  | zero => exact div_pos (iRepErfc_pos (n + 1) z) (iRepErfc_pos n z)
  | succ m =>
    show 0 < ((n : ℝ) + m + 2) * iRepErfc (n + m + 2) z / iRepErfc (n + m + 1) z
    have hc : (0 : ℝ) < (n : ℝ) + m + 2 := by positivity
    exact div_pos (mul_pos hc (iRepErfc_pos (n + m + 2) z)) (iRepErfc_pos (n + m + 1) z)

-- no-dlmf: private kit lemma; the tail recursion is the three-term recurrence 7.18.7
/-- The exact-tail backwards recurrence `t m = aₘ₊₁/(bₘ₊₁ + t (m+1))`: both cases
reduce to the three-term recurrence `erf_7_18_7`. -/
private lemma repTail_rec (n : ℕ) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    repTail n z m = repA (n : ℝ) (m + 1) / (repB z (m + 1) + repTail n z (m + 1)) := by
  cases m with
  | zero =>
    have h7 := erf_7_18_7 n z
    have hW0 := iRepErfc_pos n z
    have hW1 := iRepErfc_pos (n + 1) z
    have hW2 := iRepErfc_pos (n + 2) z
    have ha : repA (n : ℝ) 1 = 1 / 2 := by unfold repA; norm_num
    have hb : repB z 1 = z := repB_val one_ne_zero
    have ht0 : repTail n z 0 = iRepErfc (n + 1) z / iRepErfc n z := rfl
    have ht1 : repTail n z 1
        = ((n : ℝ) + (0 : ℕ) + 2) * iRepErfc (n + 0 + 2) z / iRepErfc (n + 0 + 1) z := rfl
    rw [ht0, ht1, ha, hb]
    simp only [Nat.cast_zero, add_zero]
    have hden : z + ((n : ℝ) + 2) * iRepErfc (n + 2) z / iRepErfc (n + 1) z ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      exact (add_pos hz (div_pos (mul_pos this hW2) hW1)).ne'
    field_simp
    linear_combination h7
  | succ m =>
    have h7 := erf_7_18_7 (n + m + 1) z
    have e1 : n + m + 1 + 2 = n + m + 3 := rfl
    have e2 : n + m + 1 + 1 = n + m + 2 := rfl
    rw [e1, e2] at h7
    push_cast at h7
    have hW1 := iRepErfc_pos (n + m + 1) z
    have hW2 := iRepErfc_pos (n + m + 2) z
    have hW3 := iRepErfc_pos (n + m + 3) z
    have ha : repA (n : ℝ) (m + 2) = ((n : ℝ) + (m + 2 : ℕ)) / 2 := repA_val (n : ℝ) (by omega)
    have hb : repB z (m + 2) = z := repB_val (by omega)
    have ht1 : repTail n z (m + 1)
        = ((n : ℝ) + m + 2) * iRepErfc (n + m + 2) z / iRepErfc (n + m + 1) z := rfl
    have ht2 : repTail n z (m + 2)
        = ((n : ℝ) + (m + 1 : ℕ) + 2) * iRepErfc (n + m + 3) z / iRepErfc (n + m + 2) z := rfl
    rw [ht1, ht2, ha, hb]
    push_cast
    have hden : z + ((n : ℝ) + m + 1 + 2) * iRepErfc (n + m + 3) z
        / iRepErfc (n + m + 2) z ≠ 0 := by
      have hc : (0 : ℝ) < (n : ℝ) + m + 1 + 2 := by positivity
      exact (add_pos hz (div_pos (mul_pos hc hW3) hW2)).ne'
    field_simp
    linear_combination ((n : ℝ) + m + 2) * h7

-- no-dlmf: private kit lemma (continuant denominators positive)
private lemma repCF_dens_pos {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    0 < (repCF ν z).dens m :=
  FLMF.Methods.dens_pos (repCF_pos hν hz) m

-- no-dlmf: private kit lemma (partial-numerator access with default)
private lemma repCF_partNum_getD (ν : ℝ) (z : ℝ) (i : ℕ) :
    ((repCF ν z).partNums.get? i).getD 0 = repA ν (i + 1) := by
  rw [GenContFract.partNum_eq_s_a (repCF_s_get? ν z i)]
  rfl

-- no-dlmf: private kit lemma (partial-numerator products positive)
private lemma repCF_partNumProd_pos {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) (z : ℝ) (m : ℕ) :
    0 < FLMF.Methods.partNumProd (repCF ν z) m := by
  unfold FLMF.Methods.partNumProd
  apply Finset.prod_pos
  intro i _
  rw [repCF_partNum_getD]
  exact repA_pos hν (i + 1) (by omega)

-- no-dlmf: private kit lemma (product recurrence)
private lemma repCF_partNumProd_succ (ν : ℝ) (z : ℝ) (m : ℕ) :
    FLMF.Methods.partNumProd (repCF ν z) (m + 1) =
      FLMF.Methods.partNumProd (repCF ν z) m * repA ν (m + 1) := by
  rw [FLMF.Methods.partNumProd_succ, repCF_partNum_getD]

-- no-dlmf: private kit lemma; two-step convergent-gap contraction
/-- Two-step gap estimate `convGap (m+2)·(1 + 2z²/(ν+m+3)) ≤ convGap m`: expanding
two steps of the Wallis recurrence produces the cross term
`z·aₘ₊₂·Bₘ·Bₘ₊₂ ≥ z²·aₘ₊₂·Bₘ·Bₘ₊₁`, which supplies the extra
`z²/aₘ₊₃`-fraction of the gap since `aₘ₊₃ = (ν+m+3)/2`. -/
private lemma repCF_gap_two_step {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) (m : ℕ) :
    FLMF.Methods.convGap (repCF ν z) (m + 2) * (1 + 2 * z ^ 2 / (ν + m + 3)) ≤
      FLMF.Methods.convGap (repCF ν z) m := by
  have hpos := repCF_pos hν hz
  have hB0 := repCF_dens_pos hν hz m
  have hB1 := repCF_dens_pos hν hz (m + 1)
  have hB2 := repCF_dens_pos hν hz (m + 2)
  have hB3 := repCF_dens_pos hν hz (m + 3)
  have hP1 := repCF_partNumProd_pos hν z (m + 1)
  have hrec2 : (repCF ν z).dens (m + 2) =
      repB z (m + 2) * (repCF ν z).dens (m + 1) + repA ν (m + 2) * (repCF ν z).dens m :=
    GenContFract.dens_recurrence (repCF_s_get? ν z (m + 1)) rfl rfl
  have hrec3 : (repCF ν z).dens (m + 3) =
      repB z (m + 3) * (repCF ν z).dens (m + 2) + repA ν (m + 3) * (repCF ν z).dens (m + 1) :=
    GenContFract.dens_recurrence (repCF_s_get? ν z (m + 2)) rfl rfl
  have hb2 : repB z (m + 2) = z := repB_val (by omega)
  have hb3 : repB z (m + 3) = z := repB_val (by omega)
  have ha2 : 0 < repA ν (m + 2) := repA_pos hν (m + 2) (by omega)
  have ha3 : 0 < repA ν (m + 3) := repA_pos hν (m + 3) (by omega)
  have ha2v : repA ν (m + 2) = (ν + m + 2) / 2 := by
    rw [repA_val ν (by omega)]
    push_cast
    ring
  have ha3v : repA ν (m + 3) = (ν + m + 3) / 2 := by
    rw [repA_val ν (by omega)]
    push_cast
    ring
  rw [FLMF.Methods.convGap_eq hpos, FLMF.Methods.convGap_eq hpos]
  have hP3 : FLMF.Methods.partNumProd (repCF ν z) (m + 2 + 1) =
      FLMF.Methods.partNumProd (repCF ν z) (m + 1) * repA ν (m + 2) * repA ν (m + 3) := by
    rw [repCF_partNumProd_succ, repCF_partNumProd_succ]
  rw [hP3]
  have e3 : (repCF ν z).dens (m + 2 + 1) = (repCF ν z).dens (m + 3) := rfl
  rw [e3]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hfac : repA ν (m + 2) * repA ν (m + 3) * (1 + 2 * z ^ 2 / (ν + m + 3)) =
      repA ν (m + 2) * repA ν (m + 3) + repA ν (m + 2) * z ^ 2 := by
    rw [ha2v, ha3v]
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hne : (ν + m + 3) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hkey : repA ν (m + 2) * repA ν (m + 3) * (1 + 2 * z ^ 2 / (ν + m + 3)) *
        ((repCF ν z).dens m * (repCF ν z).dens (m + 1)) ≤
      (repCF ν z).dens (m + 2) * (repCF ν z).dens (m + 3) := by
    rw [hfac, hrec3, hrec2, hb2, hb3]
    have t1 : 0 ≤ z * (z * (z * ((repCF ν z).dens (m + 1) * (repCF ν z).dens (m + 1)))) :=
      mul_nonneg hz.le (mul_nonneg hz.le (mul_nonneg hz.le (mul_nonneg hB1.le hB1.le)))
    have t2 : 0 ≤ z * (z * (repA ν (m + 2) * ((repCF ν z).dens m * (repCF ν z).dens (m + 1)))) :=
      mul_nonneg hz.le (mul_nonneg hz.le (mul_nonneg ha2.le (mul_nonneg hB0.le hB1.le)))
    have t3 : 0 ≤ z * (repA ν (m + 3) * ((repCF ν z).dens (m + 1) * (repCF ν z).dens (m + 1))) :=
      mul_nonneg hz.le (mul_nonneg ha3.le (mul_nonneg hB1.le hB1.le))
    have t4 : 0 ≤ z * (repA ν (m + 2) * (repA ν (m + 2)
        * ((repCF ν z).dens m * (repCF ν z).dens m))) :=
      mul_nonneg hz.le (mul_nonneg ha2.le (mul_nonneg ha2.le (mul_nonneg hB0.le hB0.le)))
    nlinarith [t1, t2, t3, t4]
  nlinarith [hkey, hP1, mul_pos hB0 hB1, mul_pos hB2 hB3]

-- no-dlmf: private kit lemma; chained gap estimate with the harmonic partial sum
/-- Chained gap estimate: `convGap (2M)·(1 + (2z²/(ν+3))·H_M) ≤ convGap 0` with `H_M`
the harmonic partial sum, by induction on `M` from the two-step estimate (using
`2/(ν+2i+3) ≥ (2/(ν+3))·1/(i+1)`, which needs `ν ≥ −1`). -/
private lemma repCF_gap_chain {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) (M : ℕ) :
    FLMF.Methods.convGap (repCF ν z) (2 * M) *
        (1 + 2 * z ^ 2 / (ν + 3) * ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1)) ≤
      FLMF.Methods.convGap (repCF ν z) 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hpos := repCF_pos hν hz
    have h2 := repCF_gap_two_step hν hz (2 * M)
    push_cast at h2
    have hchain : FLMF.Methods.convGap (repCF ν z) (2 * M + 2) ≤
        FLMF.Methods.convGap (repCF ν z) (2 * M) :=
      le_trans (FLMF.Methods.convGap_succ_le hpos (2 * M + 1))
        (FLMF.Methods.convGap_succ_le hpos (2 * M))
    have hG2 : 0 ≤ FLMF.Methods.convGap (repCF ν z) (2 * M + 2) :=
      FLMF.Methods.convGap_nonneg hpos _
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hcnn : (0 : ℝ) ≤ 2 * z ^ 2 / (ν + 3) :=
      div_nonneg (by positivity) (by linarith)
    have hcS : (0 : ℝ) ≤ 2 * z ^ 2 / (ν + 3)
        * ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) :=
      mul_nonneg hcnn hSnn
    have hle : 2 * z ^ 2 / (ν + 3) * (1 / ((M : ℝ) + 1)) ≤
        2 * z ^ 2 / (ν + 2 * M + 3) := by
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      rw [div_mul_div_comm, mul_one,
        div_le_div_iff₀ (mul_pos (by linarith) (by positivity)) (by linarith)]
      have hzz : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
      have hn : (0 : ℝ) ≤ ν + 1 := by linarith
      nlinarith [mul_nonneg hzz (mul_nonneg hn hMnn), mul_nonneg hzz hMnn]
    have hidx : 2 * (M + 1) = 2 * M + 2 := by ring
    rw [hidx, Finset.sum_range_succ]
    have hmm := mul_le_mul_of_nonneg_left hle hG2
    have hmm2 := mul_le_mul_of_nonneg_right hchain hcS
    nlinarith [ih, h2, hchain, hG2, hcS, hmm, hmm2]

-- no-dlmf: private kit lemma; the convergent gap tends to 0
/-- The convergent gap of the DLMF 7.18.13 fraction tends to `0`: the even-index
bound `convGap (2M) ≤ convGap 0 / (1 + (2z²/(ν+3))·H_M)` with `H_M → ∞`, plus
antitonicity of the gap for the full sequence. -/
private lemma repCF_gap_tendsto {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun m => FLMF.Methods.convGap (repCF ν z) m) atTop (𝓝 0) := by
  have hpos := repCF_pos hν hz
  have hantitone : Antitone fun m => FLMF.Methods.convGap (repCF ν z) m :=
    antitone_nat_of_succ_le fun m => FLMF.Methods.convGap_succ_le hpos m
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  have hc : (0 : ℝ) < 2 * z ^ 2 / (ν + 3) := by
    apply div_pos (by linarith) (by linarith)
  have hH : Tendsto (fun M : ℕ => 1 + 2 * z ^ 2 / (ν + 3) *
      ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact Filter.Tendsto.const_mul_atTop hc Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hbound : ∀ M : ℕ, FLMF.Methods.convGap (repCF ν z) (2 * M) ≤
      FLMF.Methods.convGap (repCF ν z) 0 /
        (1 + 2 * z ^ 2 / (ν + 3) * ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1)) := by
    intro M
    have h := repCF_gap_chain hν hz M
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hpos1 : (0 : ℝ) < 1 + 2 * z ^ 2 / (ν + 3)
        * ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1) := by
      nlinarith [mul_nonneg hc.le hSnn]
    rw [le_div_iff₀ hpos1]
    linarith [h]
  have heven : Tendsto (fun M : ℕ => FLMF.Methods.convGap (repCF ν z) (2 * M)) atTop (𝓝 0) := by
    apply squeeze_zero (fun M => FLMF.Methods.convGap_nonneg hpos (2 * M)) hbound
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hH
  have hdiv2 : Tendsto (fun m : ℕ => m / 2) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => Nat.div_le_div_right h)
      (fun b => ⟨2 * b, by omega⟩)
  have hcomp : Tendsto (fun m : ℕ => FLMF.Methods.convGap (repCF ν z) (2 * (m / 2)))
      atTop (𝓝 0) :=
    heven.comp hdiv2
  apply squeeze_zero (fun m => FLMF.Methods.convGap_nonneg hpos m) (fun m => ?_) hcomp
  exact hantitone (by omega : 2 * (m / 2) ≤ m)

-- no-dlmf: private kit lemma; consecutive-convergent difference tends to 0
private lemma repCF_diff_tendsto {ν : ℝ} (hν : (-1 : ℝ) ≤ ν) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun m => (repCF ν z).convs (m + 1) - (repCF ν z).convs m) atTop (𝓝 0) := by
  have hpos := repCF_pos hν hz
  have hgapT := repCF_gap_tendsto hν hz
  have key : ∀ m, |(repCF ν z).convs (m + 1) - (repCF ν z).convs m| =
      FLMF.Methods.convGap (repCF ν z) m := by
    intro m
    have hnn := FLMF.Methods.convGap_nonneg hpos m
    have hdef : FLMF.Methods.convGap (repCF ν z) m =
        (-1) ^ m * ((repCF ν z).convs (m + 1) - (repCF ν z).convs m) := rfl
    rcases Nat.even_or_odd m with he | ho
    · rw [hdef, he.neg_one_pow, one_mul] at hnn ⊢
      exact abs_of_nonneg hnn
    · rw [hdef, ho.neg_one_pow, neg_one_mul] at hnn ⊢
      rw [abs_of_nonpos (by linarith)]
  have habs0 : Tendsto (fun m => |(repCF ν z).convs (m + 1) - (repCF ν z).convs m|)
      atTop (𝓝 0) := by
    have hfe : (fun m => |(repCF ν z).convs (m + 1) - (repCF ν z).convs m|) =
        fun m => FLMF.Methods.convGap (repCF ν z) m := funext key
    rw [hfe]
    exact hgapT
  have hneg : Tendsto (fun m => -|(repCF ν z).convs (m + 1) - (repCF ν z).convs m|)
      atTop (𝓝 0) := by
    simpa using habs0.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs0
    (fun m => neg_abs_le _) (fun m => le_abs_self _)

-- no-dlmf: instance of DLMF 7.18.13 (DLMF index m = n+1 ≥ 1 only; misses the n = 0 case with i⁻¹erfc); faithful surface is cerf_7_18_13 (Error/ComplexErfcFraction.lean)
/-- Continued-fraction expansion for the ratio of consecutive repeated integrals:
for `0 < z`,
`iᵐerfc(z)/iᵐ⁻¹erfc(z) = (1/2)/(z + ((m+1)/2)/(z + ((m+2)/2)/(z + ⋯)))` with
`m = n+1`, stated as the limit of the Wallis convergents
`FLMF.Error.cfConv` (partial numerators `a 1 = 1/2`, `a k = (n+k)/2` for `k ≥ 2`;
partial denominators `b k = z` for `k ≥ 1`). -/
theorem erf_7_18_13 (n : ℕ) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto
      (fun N =>
        FLMF.Error.cfConv
          (fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else (n + k) / 2)
          (fun k => if k = 0 then 0 else z) N)
      Filter.atTop (nhds (iRepErfc (n + 1) z / iRepErfc n z)) := by
  have hνn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hν : (-1 : ℝ) ≤ (n : ℝ) := by linarith
  have hpos := repCF_pos hν hz
  have htail : ∀ m, ∃ gp, (repCF (n : ℝ) z).s.get? m = some gp ∧
      repTail n z m = gp.a / (gp.b + repTail n z (m + 1)) :=
    fun m => ⟨⟨repA (n : ℝ) (m + 1), repB z (m + 1)⟩, repCF_s_get? (n : ℝ) z m,
      repTail_rec n hz m⟩
  have hmain := FLMF.Methods.tendsto_convs_of_tails hpos (repTail_pos n z) htail
    (repCF_diff_tendsto hν hz)
  have hlim : (repCF (n : ℝ) z).h + repTail n z 0 = iRepErfc (n + 1) z / iRepErfc n z := by
    show repB z 0 + repTail n z 0 = _
    have h0 : repB z 0 = 0 := by unfold repB; norm_num
    have ht : repTail n z 0 = iRepErfc (n + 1) z / iRepErfc n z := rfl
    rw [h0, ht, zero_add]
  rw [hlim] at hmain
  have hfun : cfConv (repA (n : ℝ)) (repB z) = (repCF (n : ℝ) z).convs :=
    funext (repCF_conv (n : ℝ) z)
  show Tendsto (fun N => cfConv (repA (n : ℝ)) (repB z) N) atTop _
  rw [show (fun N => cfConv (repA (n : ℝ)) (repB z) N) = cfConv (repA (n : ℝ)) (repB z) from rfl,
    hfun]
  exact hmain

-- no-dlmf: exact tails of the DLMF 7.18.13 fraction at the boundary index `n = 0`
-- (the `ν = −1` member of the family, whose denominator is `i⁻¹erfc`);
-- private kit definition
/-- Exact tails of the `n = 0` member of the DLMF 7.18.13 family: `t 0` is the
target ratio `i⁰erfc(z)/i⁻¹erfc(z)`, and for `m ≥ 1` the weighted ratios
`m·i^m erfc(z)/i^{m−1}erfc(z)` — the `ν = −1` instance of `repTail`. -/
private noncomputable def repTailNegOne (z : ℝ) : ℕ → ℝ
  | 0 => iRepErfc 0 z / iRepErfcNegOne z
  | (m + 1) => ((m : ℝ) + 1) * iRepErfc (m + 1) z / iRepErfc m z

-- no-dlmf: private kit lemma (positivity of the `n = −1` member)
private lemma iRepErfcNegOne_pos (z : ℝ) : 0 < iRepErfcNegOne z := by
  unfold iRepErfcNegOne
  have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

-- no-dlmf: private kit lemma (tail positivity at the boundary index)
private lemma repTailNegOne_pos (z : ℝ) (m : ℕ) : 0 < repTailNegOne z m := by
  cases m with
  | zero => exact div_pos (iRepErfc_pos 0 z) (iRepErfcNegOne_pos z)
  | succ m =>
    show 0 < ((m : ℝ) + 1) * iRepErfc (m + 1) z / iRepErfc m z
    have hc : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    exact div_pos (mul_pos hc (iRepErfc_pos (m + 1) z)) (iRepErfc_pos m z)

-- no-dlmf: private kit lemma; the boundary tail recursion, from the seed identity
-- `2·i¹erfc + 2z·erfc = i⁻¹erfc` (DLMF 7.18.7 at n = 1) and 7.18.7
/-- The exact-tail backwards recurrence at the boundary index. -/
private lemma repTailNegOne_rec {z : ℝ} (hz : 0 < z) (m : ℕ) :
    repTailNegOne z m
      = repA (-1 : ℝ) (m + 1) / (repB z (m + 1) + repTailNegOne z (m + 1)) := by
  cases m with
  | zero =>
    have hseed := two_iRepErfc_one_add z
    rw [← iRepErfc_zero_apply] at hseed
    have hW0 := iRepErfc_pos 0 z
    have hW1 := iRepErfc_pos 1 z
    have hN := iRepErfcNegOne_pos z
    have ha : repA (-1 : ℝ) 1 = 1 / 2 := by unfold repA; norm_num
    have hb : repB z 1 = z := repB_val one_ne_zero
    have ht0 : repTailNegOne z 0 = iRepErfc 0 z / iRepErfcNegOne z := rfl
    have ht1 : repTailNegOne z 1
        = (((0 : ℕ) : ℝ) + 1) * iRepErfc 1 z / iRepErfc 0 z := rfl
    rw [ht0, ht1, ha, hb]
    simp only [Nat.cast_zero, zero_add, one_mul]
    have hden : z + iRepErfc 1 z / iRepErfc 0 z ≠ 0 :=
      (add_pos hz (div_pos hW1 hW0)).ne'
    have hNval : iRepErfcNegOne z = 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) := rfl
    have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
    have h0ne : iRepErfc 0 z ≠ 0 := hW0.ne'
    have hseed' : Real.sqrt Real.pi * (2 * iRepErfc 1 z + 2 * z * iRepErfc 0 z)
        = 2 * Real.exp (-z ^ 2) := by rw [hseed]; field_simp
    rw [hNval]
    rw [hNval] at hN
    field_simp
    linear_combination (1 / 2 : ℝ) * hseed'
  | succ k =>
    have h7 := erf_7_18_7 k z
    have hW0 := iRepErfc_pos k z
    have hW1 := iRepErfc_pos (k + 1) z
    have hW2 := iRepErfc_pos (k + 2) z
    have ha : repA (-1 : ℝ) (k + 2) = ((-1 : ℝ) + (k + 2 : ℕ)) / 2 :=
      repA_val (-1 : ℝ) (by omega)
    have hb : repB z (k + 2) = z := repB_val (by omega)
    have ht1 : repTailNegOne z (k + 1) = ((k : ℝ) + 1) * iRepErfc (k + 1) z / iRepErfc k z :=
      rfl
    have ht2 : repTailNegOne z (k + 2)
        = (((k + 1 : ℕ) : ℝ) + 1) * iRepErfc (k + 2) z / iRepErfc (k + 1) z := rfl
    rw [ht1, ht2, ha, hb]
    push_cast
    have hden : z + ((k : ℝ) + 1 + 1) * iRepErfc (k + 2) z / iRepErfc (k + 1) z ≠ 0 := by
      have hc : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
      exact (add_pos hz (div_pos (mul_pos hc hW2) hW1)).ne'
    have h0ne : iRepErfc k z ≠ 0 := hW0.ne'
    have h1ne : iRepErfc (k + 1) z ≠ 0 := hW1.ne'
    field_simp
    linear_combination ((k : ℝ) + 1) * h7

-- no-dlmf: real-axis slice of DLMF 7.18.13 (DLMF states ℜz > 0, complex);
-- the canonical carrier is the complex `cerf_7_18_13`
-- (Error/ComplexErfcFraction.lean)
/-- Continued-fraction expansion for the ratio of consecutive
repeated integrals of the complementary error function (7.18.13, real slice):
for every nonnegative integer `n` and `0 < z`,
`iⁿerfc(z)/iⁿ⁻¹erfc(z) = (1/2)/(z + ((n+1)/2)/(z + ((n+2)/2)/(z + ⋯)))`,
stated as the limit of the Wallis convergents `FLMF.Error.cfConv`
(partial numerators `a 1 = 1/2`, `a k = (n+k−1)/2` for `k ≥ 2`; partial
denominators `b k = z` for `k ≥ 1`), where for `n = 0` the denominator is
`i⁻¹erfc(z) = (2/√π)·e^{−z²}` (7.18.1).  The DLMF indices `n ≥ 1` are
`erf_7_18_13` (at parameter `n−1`); the `n = 0` boundary case is the `ν = −1`
member of the same one-parameter family of fractions (partial numerators
`repA ν`, `ν ≥ −1`), whose exact tails `repTailNegOne` close on the seed
identity `2·i¹erfc(z) + 2z·erfc(z) = i⁻¹erfc(z)`.  The faithful complex
surface (DLMF's own domain `ℜz > 0`) is `cerf_7_18_13`
(Error/ComplexErfcFraction.lean). -/
theorem erf_7_18_13_general (n : ℕ) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto
      (fun N =>
        FLMF.Error.cfConv
          (fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else ((n : ℝ) + (k : ℝ) - 1) / 2)
          (fun k => if k = 0 then 0 else z) N)
      Filter.atTop
      (nhds (iRepErfc n z /
        (match n with
          | 0 => 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2)
          | m + 1 => iRepErfc m z))) := by
  cases n with
  | zero =>
    -- the boundary case: the `ν = −1` member of the fraction family, whose tails
    -- are `repTailNegOne` and whose denominator is `i⁻¹erfc(z) = (2/√π)e^{−z²}`
    have hν : (-1 : ℝ) ≤ (-1 : ℝ) := le_rfl
    have hpos := repCF_pos hν hz
    have htail : ∀ m, ∃ gp, (repCF (-1 : ℝ) z).s.get? m = some gp ∧
        repTailNegOne z m = gp.a / (gp.b + repTailNegOne z (m + 1)) :=
      fun m => ⟨⟨repA (-1 : ℝ) (m + 1), repB z (m + 1)⟩, repCF_s_get? (-1 : ℝ) z m,
        repTailNegOne_rec hz m⟩
    have hmain := FLMF.Methods.tendsto_convs_of_tails hpos (repTailNegOne_pos z) htail
      (repCF_diff_tendsto hν hz)
    have hlim : (repCF (-1 : ℝ) z).h + repTailNegOne z 0
        = iRepErfc 0 z / (2 / Real.sqrt Real.pi * Real.exp (-z ^ 2)) := by
      show repB z 0 + repTailNegOne z 0 = _
      have h0 : repB z 0 = 0 := by unfold repB; norm_num
      have ht : repTailNegOne z 0 = iRepErfc 0 z / iRepErfcNegOne z := rfl
      rw [h0, ht, zero_add]
      rfl
    rw [hlim] at hmain
    have hfunA : (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 1 / 2
        else (((0 : ℕ) : ℝ) + (k : ℝ) - 1) / 2) = repA (-1 : ℝ) := by
      funext k
      unfold repA
      split_ifs <;> push_cast <;> ring
    have hgoal : (fun N => FLMF.Error.cfConv
          (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 1 / 2
            else (((0 : ℕ) : ℝ) + (k : ℝ) - 1) / 2)
          (fun k : ℕ => if k = 0 then (0 : ℝ) else z) N)
        = (repCF (-1 : ℝ) z).convs := by
      funext N
      rw [hfunA, show (fun k : ℕ => if k = 0 then (0 : ℝ) else z) = repB z from rfl]
      exact repCF_conv (-1 : ℝ) z N
    rw [hgoal]
    exact hmain
  | succ m =>
    -- the DLMF indices `n ≥ 1`: exactly `erf_7_18_13` at parameter `n − 1`
    have h := erf_7_18_13 m hz
    have hfunA : (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 1 / 2
        else (((m + 1 : ℕ) : ℝ) + (k : ℝ) - 1) / 2)
        = (fun k : ℕ => if k = 0 then (0 : ℝ) else if k = 1 then 1 / 2
            else ((m : ℝ) + (k : ℝ)) / 2) := by
      funext k
      split_ifs <;> push_cast <;> ring
    rw [hfunA]
    exact h

-- no-dlmf: real-axis leading-order instance of DLMF 7.18.14; the canonical
-- carrier is the sector-uniform `erf_7_18_14_sector`
-- (Error/Ch7SectorExpansions.lean)
/-- Leading large-`z` asymptotic of `iⁿerfc` (7.18.14, leading term): the
`m = 0` term of the asymptotic series gives
`iⁿerfc(z) ∼ (2/√π) · e^{−z²}/(2z)^{n+1}`  as `z → +∞`.

We state the honest leading-order asymptotic equivalence `~[atTop]`.  The full
correction series, sector-uniform on `|ph z| ≤ 3π/4 − δ` at every truncation
order, is `erf_7_18_14_sector` (Error/Ch7SectorExpansions.lean). -/
theorem erf_7_18_14 (n : ℕ) :
    (fun z : ℝ => iRepErfc n z) ~[atTop]
      fun z : ℝ => 2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (n + 1)) := by
  have hsπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  -- The ratio form `iⁿerfc(z) / ((2/√π)·e^{-z²}/(2z)^{n+1}) → 1`, by induction with
  -- L'Hôpital at `atTop` for the step.
  have key : ∀ m : ℕ, Tendsto (fun z : ℝ =>
      iRepErfc m z / (2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1))))
      atTop (𝓝 1) := by
    intro m
    induction m with
    | zero =>
      refine erfc_asymptotic.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hexp0 : Real.exp (x ^ 2) ≠ 0 := (Real.exp_pos _).ne'
      have hsπ0 : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsπ
      rw [iRepErfc_zero_apply, zero_add, pow_one, Real.exp_neg]
      field_simp
    | succ m ih =>
      -- L'Hôpital data: numerator `i^{m+1}erfc`, denominator `(2/√π)·e^{-z²}/(2z)^{m+2}`.
      have hff' : ∀ᶠ z : ℝ in atTop, HasDerivAt (iRepErfc (m + 1)) (-iRepErfc m z) z :=
        Filter.Eventually.of_forall fun z => hasDerivAt_iRepErfc_succ m z
      have hgg' : ∀ᶠ z : ℝ in atTop, HasDerivAt (fun t : ℝ => 2 / Real.sqrt Real.pi
          * (Real.exp (-t ^ 2) / (2 * t) ^ (m + 1 + 1)))
          (-(2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1))
            * (1 + ((m : ℝ) + 2) / (2 * z ^ 2)))) z := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have h2z : (0 : ℝ) < 2 * z := by linarith
        have hnum : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2))
            (Real.exp (-z ^ 2) * -(2 * z)) z := by
          have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * z)) z := by
            simpa using (hasDerivAt_pow 2 z).neg
          exact hsq.exp
        have hden : HasDerivAt (fun t : ℝ => (2 * t) ^ (m + 1 + 1))
            ((↑(m + 1 + 1) : ℝ) * (2 * z) ^ (m + 1) * 2) z := by
          have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 z := by
            simpa using (hasDerivAt_id z).const_mul (2 : ℝ)
          simpa using h1.pow (m + 1 + 1)
        have hpow_ne : ((2 * z) ^ (m + 1 + 1) : ℝ) ≠ 0 := ne_of_gt (pow_pos h2z _)
        have hd := (hnum.div hden hpow_ne).const_mul (2 / Real.sqrt Real.pi)
        have hveq : 2 / Real.sqrt Real.pi
            * ((Real.exp (-z ^ 2) * -(2 * z) * (2 * z) ^ (m + 1 + 1)
                - Real.exp (-z ^ 2) * ((↑(m + 1 + 1) : ℝ) * (2 * z) ^ (m + 1) * 2))
              / ((2 * z) ^ (m + 1 + 1)) ^ 2)
            = -(2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1))
              * (1 + ((m : ℝ) + 2) / (2 * z ^ 2))) := by
          have hz0 : z ≠ 0 := ne_of_gt hz
          have h2z0 : (2 * z : ℝ) ≠ 0 := ne_of_gt h2z
          have hsπ0 : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsπ
          push_cast
          field_simp
          ring
        rw [hveq] at hd
        exact hd
      have hg'ne : ∀ᶠ z : ℝ in atTop, -(2 / Real.sqrt Real.pi
          * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1))
          * (1 + ((m : ℝ) + 2) / (2 * z ^ 2))) ≠ 0 := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have h2z : (0 : ℝ) < 2 * z := by linarith
        have hpow : (0 : ℝ) < (2 * z) ^ (m + 1) := pow_pos h2z _
        have hB : (0 : ℝ) < 1 + ((m : ℝ) + 2) / (2 * z ^ 2) := by positivity
        exact neg_ne_zero.mpr (ne_of_gt (mul_pos
          (mul_pos (div_pos two_pos hsπ) (div_pos (Real.exp_pos _) hpow)) hB))
      have hg : Tendsto (fun z : ℝ => 2 / Real.sqrt Real.pi
          * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1 + 1))) atTop (𝓝 0) := by
        have h2 : Tendsto (fun z : ℝ => (2 * z) ^ (m + 1 + 1)) atTop atTop :=
          (tendsto_pow_atTop (Nat.succ_ne_zero _)).comp
            (tendsto_id.const_mul_atTop two_pos)
        simpa using (Filter.Tendsto.div_atTop tendsto_exp_neg_sq_atTop h2).const_mul
          (2 / Real.sqrt Real.pi)
      have hB : Tendsto (fun z : ℝ => 1 + ((m : ℝ) + 2) / (2 * z ^ 2)) atTop (𝓝 1) := by
        have h2 : Tendsto (fun z : ℝ => 2 * z ^ 2) atTop atTop :=
          (tendsto_pow_atTop two_ne_zero).const_mul_atTop two_pos
        have h3 := Filter.Tendsto.div_atTop
          (tendsto_const_nhds (x := ((m : ℝ) + 2)) (f := atTop)) h2
        simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h3
      have h4 : Tendsto (fun z : ℝ => iRepErfc m z
          / (2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1)))
          / (1 + ((m : ℝ) + 2) / (2 * z ^ 2))) atTop (𝓝 1) := by
        simpa using ih.div hB one_ne_zero
      have hdiv : Tendsto (fun z : ℝ => -iRepErfc m z
          / -(2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (m + 1))
            * (1 + ((m : ℝ) + 2) / (2 * z ^ 2)))) atTop (𝓝 1) := by
        refine h4.congr fun z => ?_
        rw [div_div, neg_div_neg_eq]
      exact HasDerivAt.lhopital_zero_atTop hff' hgg' hg'ne
        (tendsto_iRepErfc_atTop (m + 1)) hg hdiv
  have hne : ∀ᶠ z : ℝ in atTop,
      2 / Real.sqrt Real.pi * (Real.exp (-z ^ 2) / (2 * z) ^ (n + 1)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    have h2z : (0 : ℝ) < 2 * z := by linarith
    have hpow : (0 : ℝ) < (2 * z) ^ (n + 1) := pow_pos h2z _
    exact ne_of_gt (mul_pos (div_pos two_pos hsπ) (div_pos (Real.exp_pos _) hpow))
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  exact key n

end FLMF.Error
