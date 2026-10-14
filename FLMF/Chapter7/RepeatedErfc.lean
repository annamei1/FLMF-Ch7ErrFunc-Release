import FLMF.Chapter7.Erf
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Repeated integrals of the complementary error function `iⁿerfc` (DLMF §7.18)

We define the `n`-fold repeated integral of `erfc`,
`iⁿerfc(x) = ∫ₓ^∞ i^{n-1}erfc(t) dt`, by recursion on `ℕ`:

`iRepErfc 0 x = erfc x`,
`iRepErfc (n+1) x = ∫_{(x,∞)} iRepErfc n t dt`   (DLMF 7.18.1, 7.18.2).

For the recursive integral to be meaningful we must know that each `iRepErfc n`
is integrable on every right half-line `Ioi x`.  The functions decay
super-exponentially; here we extract the (more than sufficient) uniform
exponential domination

`0 ≤ iRepErfc n t ≤ 3 · e^{-t}`   for `t ≥ 0`     (`iRepErfc_le_three_exp`),

which is *stable under the tail integral* — `∫_x^∞ 3 e^{-t} dt = 3 e^{-x}` — so a
single induction with a fixed constant carries the bound through every level.
Combined with continuity this gives integrability on all of `Ioi x`.

Main results:

* `FLMF.Error.iRepErfc` — the repeated integral, defined by `ℕ`-recursion.
* `FLMF.Error.iRepErfc_zero` — `i⁰erfc = erfc` (DLMF 7.18.1).
* `FLMF.Error.iRepErfc_nonneg`, `FLMF.Error.iRepErfc_le_three_exp` — nonnegativity
  and the uniform exponential bound on `[0, ∞)`.
* `FLMF.Error.continuous_iRepErfc`, `FLMF.Error.integrableOn_iRepErfc` — continuity
  and integrability on every `Ioi x`.
* `FLMF.Error.iRepErfc_succ_eq` — one unfold of the defining recursion (the
  DLMF 7.18.2 closed form for all `n ≥ 0` is `erf_7_18_2` in `Ch7RepeatedErfc.lean`).
* `FLMF.Error.hasDerivAt_iRepErfc_succ` — the derivative relation
  `d/dx i^{n+1}erfc(x) = − iⁿerfc(x)` (DLMF 7.18.3).
* `FLMF.Error.deriv_iRepErfc_succ` — the same relation in `deriv` form.
* `FLMF.Error.tendsto_iRepErfc_atTop` — `iⁿerfc(t) → 0` as `t → +∞`.
* `FLMF.Error.erf_7_18_5` — the second-order ODE `W'' + 2z W' − 2n W = 0`
  (DLMF 7.18.5), for the general solution `W = A·iⁿerfc(z) + B·iⁿerfc(−z)`, `1 ≤ n`.
* `FLMF.Error.erf_7_18_7` — the three-term recurrence (DLMF 7.18.7).
-/

noncomputable section

namespace FLMF.Error

open MeasureTheory Real Filter Topology Set

-- no-dlmf: the iⁿefc family def; the 7.18.1 base-case display is surfaced at `erf_7_18_1`
/-- The `n`-fold repeated integral of the complementary error function
(DLMF 7.18.1, 7.18.2):
`iRepErfc 0 x = erfc x` and `iRepErfc (n+1) x = ∫_{(x,∞)} iRepErfc n t dt`.

-/
noncomputable def iRepErfc : ℕ → ℝ → ℝ
  | 0, x => erfc x
  | n + 1, x => ∫ t in Ioi x, iRepErfc n t

-- no-dlmf: the n = -1 member; the 7.18.1 base-case display is surfaced at `erf_7_18_1`
/-- The `n = -1` base case of the repeated-integral family (DLMF 7.18.1):
`i⁻¹erfc(z) = (2/√π)·e^{-z²}`. Stated as a standalone function since
`iRepErfc` is `ℕ`-indexed and cannot represent a negative index.

-/
noncomputable def iRepErfcNegOne (x : ℝ) : ℝ := 2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)

-- no-dlmf: chain link 7.18.1 (assembled in `erf_7_18_1` below, alongside
-- `iRepErfc_zero_apply`); redundant unapplied form of `iRepErfc_zero_apply`,
-- not itself a distinct DLMF equation
/-- `i⁰erfc = erfc`. -/
@[simp]
theorem iRepErfc_zero : iRepErfc 0 = erfc := rfl

-- no-dlmf: chain link 7.18.1 (assembled in `erf_7_18_1` below, alongside
-- `iRepErfcNegOne`'s definitional equality)
/-- `i⁰erfc x = erfc x` (applied form). -/
@[simp]
theorem iRepErfc_zero_apply (x : ℝ) : iRepErfc 0 x = erfc x := rfl

-- no-dlmf: real-axis restriction of DLMF 7.18.1 (DLMF assigns `z` a complex
-- domain); faithful surface is `cerf_7_18_1` (ComplexRepeatedErfc.lean)
/-- The `n = -1` and `n = 0` base cases of the repeated-integral family on the
real axis: `i⁻¹erfc(x) = (2/√π)e^{-x²}` and `i⁰erfc(x) = erfc(x)`. -/
theorem erf_7_18_1 (x : ℝ) :
    iRepErfcNegOne x = 2 / Real.sqrt Real.pi * Real.exp (-x ^ 2) ∧
    iRepErfc 0 x = erfc x :=
  ⟨rfl, iRepErfc_zero_apply x⟩

-- no-dlmf: instance of DLMF 7.18.2 (first equality only, reindexed n ↦ n+1, so the n = 0
-- case of the displayed recurrence is omitted); faithful surface is erf_7_18_2
-- (Ch7RepeatedErfc.lean, the closed form for all n ≥ 0)
/-- The defining integral, unfolding one level of the recursion. -/
theorem iRepErfc_succ_eq (n : ℕ) (x : ℝ) :
    iRepErfc (n + 1) x = ∫ t in Ioi x, iRepErfc n t := rfl

/-! ## Base estimates on `erfc` -/

-- no-dlmf: global integrability of the Gaussian; analytic infrastructure, no DLMF identity
/-- `e^{-s²}` is globally integrable. -/
private theorem integrable_gaussian : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  have := integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
  simpa [one_mul] using this

-- no-dlmf: private tail-integral rewrite of erfc; proof infrastructure, no specific DLMF identity number
/-- For `t ≥ 0`, the tail form `erfc t = (2/√π) ∫_{(t,∞)} e^{-s²} ds`. -/
private theorem erfc_eq_tail {t : ℝ} (ht : 0 ≤ t) :
    erfc t = 2 / Real.sqrt Real.pi * ∫ s in Ioi t, Real.exp (-s ^ 2) := by
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hgi := integrable_gaussian
  have hsplit : (∫ s in Ioi (0 : ℝ), Real.exp (-s ^ 2))
      = (∫ s in Ioc 0 t, Real.exp (-s ^ 2)) + ∫ s in Ioi t, Real.exp (-s ^ 2) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hgi.integrableOn hgi.integrableOn, Ioc_union_Ioi_eq_Ioi ht]
  have hocx : (∫ s in Ioc 0 t, Real.exp (-s ^ 2)) = ∫ s in (0 : ℝ)..t, Real.exp (-s ^ 2) := by
    rw [intervalIntegral.integral_of_le ht]
  have hIoix : (∫ s in Ioi t, Real.exp (-s ^ 2))
      = Real.sqrt Real.pi / 2 - ∫ s in (0 : ℝ)..t, Real.exp (-s ^ 2) := by
    have := hsplit
    rw [integral_Ioi_gaussian, hocx] at this
    linarith
  rw [hIoix, erfc, erf]
  field_simp

-- no-dlmf: nonnegativity bound on erfc; analytic infrastructure, no DLMF identity
/-- `erfc` is nonnegative on `[0, ∞)` (it is the `(2/√π)`-multiple of a tail
integral of a positive function). -/
theorem erfc_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ erfc t := by
  rw [erfc_eq_tail ht]
  have hπ : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi := by positivity
  refine mul_nonneg hπ ?_
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => (Real.exp_pos _).le

-- no-dlmf: upper bound erfc ≤ 1; analytic infrastructure, no DLMF identity
/-- `erfc t ≤ 1` for `t ≥ 0` (since `erf` is nonnegative there). -/
theorem erfc_le_one {t : ℝ} (ht : 0 ≤ t) : erfc t ≤ 1 := by
  rw [erfc, sub_le_self_iff, erf]
  refine mul_nonneg (by positivity) ?_
  rw [intervalIntegral.integral_of_le ht]
  exact setIntegral_nonneg measurableSet_Ioc fun s _ => (Real.exp_pos _).le

-- no-dlmf: exponential domination bound on erfc; proof infrastructure, no DLMF identity
/-- The base exponential bound: `erfc t ≤ 3 · e^{-t}` for `t ≥ 0`.

Two regimes.  For `t ≤ ln 3` we use `erfc t ≤ 1 ≤ 3 e^{-t}`.  For `t ≥ 1` we use
`erfc t = (2/√π) ∫_t^∞ e^{-s²} ds ≤ (2/√π) ∫_t^∞ e^{-s} ds = (2/√π) e^{-t} ≤ 3 e^{-t}`,
because `s² ≥ s` on `[t, ∞)`. -/
theorem erfc_le_three_exp {t : ℝ} (ht : 0 ≤ t) : erfc t ≤ 3 * Real.exp (-t) := by
  rcases le_or_gt t 1 with h1 | h1
  · -- `t ≤ 1 ≤ ln 3`, so `1 ≤ 3 e^{-t}`.
    have hb : (1 : ℝ) ≤ 3 * Real.exp (-t) := by
      have hmono : Real.exp (-1 : ℝ) ≤ Real.exp (-t) := by
        apply Real.exp_le_exp.mpr; linarith
      have he1 : (1 : ℝ) ≤ 3 * Real.exp (-1) := by
        have h3 : Real.exp (1 : ℝ) ≤ 3 := Real.exp_one_lt_three.le
        rw [Real.exp_neg, le_mul_inv_iff₀ (Real.exp_pos _)]
        linarith
      calc (1 : ℝ) ≤ 3 * Real.exp (-1) := he1
        _ ≤ 3 * Real.exp (-t) := by linarith
    exact le_trans (erfc_le_one ht) hb
  · -- `t ≥ 1`: dominate the Gaussian tail by the exponential tail.
    have ht1 : (1 : ℝ) ≤ t := h1.le
    have htail := erfc_eq_tail ht
    have hgi := integrable_gaussian
    have hexp_int : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi t) := by
      have := exp_neg_integrableOn_Ioi t (b := (1 : ℝ)) one_pos
      simpa [one_mul] using this
    have hcmp : (∫ s in Ioi t, Real.exp (-s ^ 2)) ≤ ∫ s in Ioi t, Real.exp (-s) := by
      refine setIntegral_mono_on hgi.integrableOn hexp_int measurableSet_Ioi ?_
      intro s hs
      have hs1 : (1 : ℝ) ≤ s := le_trans ht1 (le_of_lt hs)
      apply Real.exp_le_exp.mpr
      nlinarith [hs1]
    have hval : (∫ s in Ioi t, Real.exp (-s)) = Real.exp (-t) := integral_exp_neg_Ioi t
    rw [hval] at hcmp
    have hπ : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi := by positivity
    have hcoef : 2 / Real.sqrt Real.pi ≤ 3 := by
      rw [div_le_iff₀ (by positivity)]
      have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt Real.pi := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      nlinarith [hsqrt_ge]
    calc erfc t = 2 / Real.sqrt Real.pi * ∫ s in Ioi t, Real.exp (-s ^ 2) := htail
      _ ≤ 2 / Real.sqrt Real.pi * Real.exp (-t) := by
          apply mul_le_mul_of_nonneg_left hcmp hπ
      _ ≤ 3 * Real.exp (-t) := by
          apply mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

/-! ## Continuity, nonnegativity, the uniform bound, and integrability -/

-- no-dlmf: integrability of the dominating exponential; proof infrastructure, no DLMF identity
/-- `s ↦ 3 e^{-s}` is integrable on every `Ioi x`. -/
private theorem integrableOn_three_exp (x : ℝ) :
    IntegrableOn (fun s : ℝ => 3 * Real.exp (-s)) (Ioi x) := by
  have := exp_neg_integrableOn_Ioi x (b := (1 : ℝ)) one_pos
  simpa [one_mul] using this.const_mul 3

-- no-dlmf: tail integral of the dominating exponential; proof infrastructure, no DLMF identity
/-- `∫_{(x,∞)} 3 e^{-t} dt = 3 e^{-x}` — the tail-invariance powering the bound
induction. -/
private theorem integral_three_exp_Ioi (x : ℝ) :
    (∫ t in Ioi x, 3 * Real.exp (-t)) = 3 * Real.exp (-x) := by
  rw [integral_const_mul, integral_exp_neg_Ioi]

-- no-dlmf: generic tail = const − primitive rewrite; proof infrastructure, no DLMF identity
/-- Generic "tail = constant − primitive" rewrite for a function integrable on
every right half-line: `∫_{(x,∞)} f = (∫_{(0,∞)} f) − ∫_0^x f`. -/
private theorem tail_eq_const_sub {f : ℝ → ℝ} (hf : ∀ x, IntegrableOn f (Ioi x))
    (x : ℝ) : (∫ t in Ioi x, f t)
      = (∫ t in Ioi (0 : ℝ), f t) - ∫ t in (0 : ℝ)..x, f t := by
  rcases le_total 0 x with hx | hx
  · have hsplit : (∫ t in Ioi (0 : ℝ), f t)
        = (∫ t in Ioc 0 x, f t) + ∫ t in Ioi x, f t := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((hf 0).mono_set Set.Ioc_subset_Ioi_self) (hf x), Ioc_union_Ioi_eq_Ioi hx]
    rw [intervalIntegral.integral_of_le hx, hsplit]; ring
  · have hsplit : (∫ t in Ioi x, f t)
        = (∫ t in Ioc x 0, f t) + ∫ t in Ioi (0 : ℝ), f t := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((hf x).mono_set Set.Ioc_subset_Ioi_self) (hf 0), Ioc_union_Ioi_eq_Ioi hx]
    rw [intervalIntegral.integral_of_ge hx, hsplit]; ring

-- no-dlmf: joint induction bundling continuity/nonneg/bound/integrability; proof infrastructure, no DLMF identity
/-- **Joint induction.** For each `n`:
`iRepErfc n` is continuous, nonnegative on `[0,∞)`, bounded by `3 e^{-t}` on
`[0,∞)`, and integrable on every `Ioi x`. -/
private theorem iRepErfc_props (n : ℕ) :
    Continuous (iRepErfc n) ∧ (∀ t, 0 ≤ t → 0 ≤ iRepErfc n t) ∧
      (∀ t, 0 ≤ t → iRepErfc n t ≤ 3 * Real.exp (-t)) ∧
      (∀ x, IntegrableOn (iRepErfc n) (Ioi x)) := by
  induction n with
  | zero =>
    refine ⟨continuous_erfc, fun t ht => erfc_nonneg ht, fun t ht => erfc_le_three_exp ht, ?_⟩
    intro x
    -- integrability of `erfc` on `Ioi x`: continuous on `Ici x`, dominated by `3 e^{-s}`.
    refine integrable_of_isBigO_exp_neg (b := 1) one_pos
      (continuous_erfc.continuousOn) ?_
    -- `erfc =O[atTop] e^{-x}` via the bound.
    refine Asymptotics.IsBigO.of_bound 3 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    show ‖iRepErfc 0 s‖ ≤ 3 * ‖Real.exp (-1 * s)‖
    rw [iRepErfc_zero_apply, neg_one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (erfc_nonneg hs), abs_of_nonneg (Real.exp_pos _).le]
    exact erfc_le_three_exp hs
  | succ n ih =>
    obtain ⟨hcont, hnn, hbd, hint⟩ := ih
    -- Continuity of `x ↦ ∫_{(x,∞)} iRepErfc n`.
    have hcont' : Continuous (iRepErfc (n + 1)) := by
      -- `iRepErfc (n+1) x = (∫_{Ioi 0} f) - ∫_0^x f`, continuous as a primitive.
      rw [show iRepErfc (n + 1) = fun x => (∫ t in Ioi (0 : ℝ), iRepErfc n t)
          - ∫ t in (0 : ℝ)..x, iRepErfc n t from funext fun x => tail_eq_const_sub hint x]
      refine continuous_const.sub ?_
      exact intervalIntegral.continuous_primitive
        (fun a b => (hcont.intervalIntegrable a b)) 0
    -- Nonnegativity on `[0,∞)`.
    have hnn' : ∀ t, 0 ≤ t → 0 ≤ iRepErfc (n + 1) t := by
      intro t ht
      rw [iRepErfc_succ_eq]
      refine setIntegral_nonneg measurableSet_Ioi ?_
      intro s hs
      exact hnn s (le_trans ht hs.le)
    -- The exponential bound on `[0,∞)`, with the *same* constant 3.
    have hbd' : ∀ t, 0 ≤ t → iRepErfc (n + 1) t ≤ 3 * Real.exp (-t) := by
      intro t ht
      rw [iRepErfc_succ_eq]
      calc (∫ s in Ioi t, iRepErfc n s)
          ≤ ∫ s in Ioi t, 3 * Real.exp (-s) := by
            refine setIntegral_mono_on (hint t) (integrableOn_three_exp t)
              measurableSet_Ioi ?_
            intro s hs
            exact hbd s (le_trans ht hs.le)
        _ = 3 * Real.exp (-t) := integral_three_exp_Ioi t
    -- Integrability of `iRepErfc (n+1)` on every `Ioi x`: continuous + `O(e^{-s})`.
    have hint' : ∀ x, IntegrableOn (iRepErfc (n + 1)) (Ioi x) := by
      intro x
      refine integrable_of_isBigO_exp_neg (b := 1) one_pos
        (hcont'.continuousOn) ?_
      refine Asymptotics.IsBigO.of_bound 3 ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      show ‖iRepErfc (n + 1) s‖ ≤ 3 * ‖Real.exp (-1 * s)‖
      rw [neg_one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn' s hs),
        abs_of_nonneg (Real.exp_pos _).le]
      exact hbd' s hs
    exact ⟨hcont', hnn', hbd', hint'⟩

-- no-dlmf: continuity of iⁿerfc; analytic infrastructure, no DLMF identity
/-- `iRepErfc n` is continuous. -/
theorem continuous_iRepErfc (n : ℕ) : Continuous (iRepErfc n) :=
  (iRepErfc_props n).1

-- no-dlmf: nonnegativity of iⁿerfc; analytic infrastructure, no DLMF identity
/-- `iRepErfc n` is nonnegative on `[0, ∞)`. -/
theorem iRepErfc_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ iRepErfc n t :=
  (iRepErfc_props n).2.1 t ht

-- no-dlmf: uniform exponential decay bound; §7.18 is a section ref, no specific DLMF identity number
/-- **Uniform exponential bound** (DLMF §7.18 decay): `iⁿerfc(t) ≤ 3 e^{-t}` for
`t ≥ 0`, for every `n`. -/
theorem iRepErfc_le_three_exp (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iRepErfc n t ≤ 3 * Real.exp (-t) :=
  (iRepErfc_props n).2.2.1 t ht

-- no-dlmf: integrability of iⁿerfc on right half-lines; analytic infrastructure, no DLMF identity
/-- `iRepErfc n` is integrable on every right half-line `Ioi x` — so the defining
integral really converges at every level. -/
theorem integrableOn_iRepErfc (n : ℕ) (x : ℝ) : IntegrableOn (iRepErfc n) (Ioi x) :=
  (iRepErfc_props n).2.2.2 x

/-! ## The derivative relation (DLMF 7.18.3) -/

-- no-dlmf: HasDerivAt workhorse form of DLMF 7.18.3; canonical surface is `deriv_iRepErfc_succ`
/-- **DLMF 7.18.3.** `d/dx i^{n+1}erfc(x) = − iⁿerfc(x)` — the derivative relation
`(d/dz) iⁿerfc(z) = − i^{n−1}erfc(z)` in the shifted index `n ↦ n+1` that keeps the
lowered index a genuine repeated integral (`i⁰erfc = erfc`).

The derivative of the tail integral `x ↦ ∫_{(x,∞)} f` is `−f x` whenever `f` is
continuous and integrable on `Ioi x`; we obtain it by writing the tail as
`(∫_{Ioi 0} f) − ∫_0^x f` and differentiating the primitive (interval FTC).

-/
theorem hasDerivAt_iRepErfc_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (iRepErfc (n + 1)) (-iRepErfc n x) x := by
  have hcont := continuous_iRepErfc n
  -- `iRepErfc (n+1) x = C - ∫_0^x iRepErfc n`.
  have hfix : (iRepErfc (n + 1)) = fun x => (∫ t in Ioi (0 : ℝ), iRepErfc n t)
      - ∫ t in (0 : ℝ)..x, iRepErfc n t :=
    funext fun y => tail_eq_const_sub (integrableOn_iRepErfc n) y
  rw [hfix]
  have hprim : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, iRepErfc n t) (iRepErfc n x) x :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  simpa using (hasDerivAt_const x _).sub hprim

-- no-dlmf: real-axis, shifted-index restriction of DLMF 7.18.3 (real `x` and real
-- `deriv`, and the shift `n ↦ n+1` omits DLMF's `n = 0` case); faithful surface is
-- `cerf_7_18_3` (ComplexRepeatedErfc.lean)
/-- The derivative-of-`deriv` form of the real derivative relation
`d/dx i^{n+1}erfc(x) = − iⁿerfc(x)`. -/
theorem deriv_iRepErfc_succ (n : ℕ) (x : ℝ) :
    deriv (iRepErfc (n + 1)) x = -iRepErfc n x :=
  (hasDerivAt_iRepErfc_succ n x).deriv

/-! ## Decay at `+∞` -/

-- no-dlmf: decay limit iⁿerfc → 0 at +∞; §7.18 is a section ref, no specific DLMF identity number
/-- **DLMF §7.18 decay.** `iⁿerfc(t) → 0` as `t → +∞`, for every `n` — squeezed
between `0` and `3 e^{-t} → 0`. -/
theorem tendsto_iRepErfc_atTop (n : ℕ) :
    Tendsto (iRepErfc n) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => 3 * Real.exp (-t)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (3 : ℝ)
    simpa using h
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using iRepErfc_nonneg n ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using iRepErfc_le_three_exp n ht

/-! ## Helper lemmas: global tail form, vanishing criterion, decay of `z·iⁿerfc`,
and the seed identity for the recurrence -/

-- no-dlmf: global tail-integral form of erfc (drops the `0 ≤ x` restriction of the
-- private `erfc_eq_tail`); proof infrastructure, no DLMF identity number
/-- The tail form `erfc x = (2/√π) ∫_{(x,∞)} e^{-t²} dt`, valid for **every** real `x`. -/
theorem erfc_eq_tail_global (x : ℝ) :
    erfc x = 2 / Real.sqrt Real.pi * ∫ t in Ioi x, Real.exp (-t ^ 2) := by
  have h := integral_Ioi_gaussian_scaled_erfc (a := (1 : ℝ)) one_pos x
  simp only [neg_mul, one_mul, div_one, Real.sqrt_one] at h
  rw [h]
  have hπ : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp

-- no-dlmf: vanishing criterion (zero derivative everywhere + vanishing limit at +∞);
-- proof infrastructure, no DLMF identity number
/-- A real function with derivative `0` everywhere and limit `0` at `+∞` vanishes
identically. -/
theorem eq_zero_of_hasDerivAt_zero_of_tendsto {f : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f 0 x) (h0 : Tendsto f atTop (𝓝 0)) (x : ℝ) : f x = 0 := by
  have hconst : ∀ y, f y = f x := fun y =>
    is_const_of_deriv_eq_zero (fun z => (hf z).differentiableAt)
      (fun z => (hf z).deriv) y x
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun y => (hconst y).symm) h0

-- no-dlmf: Gaussian decay at +∞; proof infrastructure, no DLMF identity number
/-- `e^{-z²} → 0` as `z → +∞`. -/
theorem tendsto_exp_neg_sq_atTop :
    Tendsto (fun z : ℝ => Real.exp (-z ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => -z ^ 2) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)
  exact Real.tendsto_exp_atBot.comp h

-- no-dlmf: decay of z·iⁿerfc(z) at +∞; proof infrastructure, no DLMF identity number
/-- `z · iⁿerfc(z) → 0` as `z → +∞`, squeezed against `3·z·e^{-z}`. -/
theorem tendsto_id_mul_iRepErfc_atTop (n : ℕ) :
    Tendsto (fun z => z * iRepErfc n z) atTop (𝓝 0) := by
  have hexp : Tendsto (fun z : ℝ => 3 * (z ^ 1 * Real.exp (-z))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (3 : ℝ)
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg hz (iRepErfc_nonneg n hz)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    calc z * iRepErfc n z ≤ z * (3 * Real.exp (-z)) :=
          mul_le_mul_of_nonneg_left (iRepErfc_le_three_exp n hz) hz
      _ = 3 * (z ^ 1 * Real.exp (-z)) := by ring

-- no-dlmf: the `i^{-1}erfc` seed identity `2·i¹erfc(z) + 2z·erfc(z) = (2/√π)e^{-z²}`
-- (DLMF 7.18.7 at n = 1, written without negative indices); proof infrastructure
/-- The seed identity for the three-term recurrence (DLMF 7.18.7 at `n = 1`, with
`i^{-1}erfc(z) = (2/√π)e^{-z²}` written out): `2·i¹erfc(z) + 2z·erfc(z) = (2/√π)e^{-z²}`. -/
theorem two_iRepErfc_one_add (z : ℝ) :
    2 * iRepErfc 1 z + 2 * z * erfc z = 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t => 2 * iRepErfc 1 t + 2 * t * erfc t
      - 2 / Real.sqrt Real.pi * Real.exp (-t ^ 2)) 0 y := by
    intro y
    have h1 : HasDerivAt (fun t => 2 * iRepErfc 1 t) (2 * -iRepErfc 0 y) y :=
      (hasDerivAt_iRepErfc_succ 0 y).const_mul 2
    have h2 : HasDerivAt (fun t : ℝ => 2 * t * erfc t)
        (2 * 1 * erfc y + 2 * y * -(2 / Real.sqrt Real.pi * Real.exp (-y ^ 2))) y :=
      ((hasDerivAt_id y).const_mul 2).mul (hasDerivAt_erfc y)
    have h3 : HasDerivAt (fun t : ℝ => 2 / Real.sqrt Real.pi * Real.exp (-t ^ 2))
        (2 / Real.sqrt Real.pi * (Real.exp (-y ^ 2) * -(2 * y))) y := by
      have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * y)) y := by
        simpa using (hasDerivAt_pow 2 y).neg
      exact hsq.exp.const_mul _
    have h := (h1.add h2).sub h3
    have hval : 2 * -iRepErfc 0 y
        + (2 * 1 * erfc y + 2 * y * -(2 / Real.sqrt Real.pi * Real.exp (-y ^ 2)))
        - 2 / Real.sqrt Real.pi * (Real.exp (-y ^ 2) * -(2 * y)) = 0 := by
      rw [iRepErfc_zero_apply]; ring
    rw [hval] at h
    exact h
  have hlim : Tendsto (fun t : ℝ => 2 * iRepErfc 1 t + 2 * t * erfc t
      - 2 / Real.sqrt Real.pi * Real.exp (-t ^ 2)) atTop (𝓝 0) := by
    have hA := (tendsto_iRepErfc_atTop 1).const_mul (2 : ℝ)
    have hB := (tendsto_id_mul_iRepErfc_atTop 0).const_mul (2 : ℝ)
    have hC := tendsto_exp_neg_sq_atTop.const_mul (2 / Real.sqrt Real.pi)
    simpa using ((hA.add hB).sub hC).congr fun t => by
      rw [iRepErfc_zero_apply]; ring
  have h := eq_zero_of_hasDerivAt_zero_of_tendsto hderiv hlim z
  have h' : 2 * iRepErfc 1 z + 2 * z * erfc z
      - 2 / Real.sqrt Real.pi * Real.exp (-z ^ 2) = 0 := h
  linarith

/-! ## The differential equation (DLMF 7.18.5) and recurrence (DLMF 7.18.7) -/

-- no-dlmf: real-axis, shifted-index restriction of DLMF 7.18.7 (real `x`, and the
-- shift `n ↦ n+2` omits DLMF's lowest index `n = 1`); faithful surface is
-- `cerf_7_18_7` (ComplexRepeatedErfc.lean)
/-- The three-term recurrence on the real axis, shifted to `n ↦ n+2` so every
repeated-integral index is a genuine natural number (no `i^{-1}`, `i^{-2}` seeds):
`2(n+2)·i^{n+2}erfc(x) = iⁿerfc(x) − 2x·i^{n+1}erfc(x)`, valid for all `n : ℕ`. -/
theorem erf_7_18_7 (n : ℕ) (x : ℝ) :
    2 * ((n : ℝ) + 2) * iRepErfc (n + 2) x
      = iRepErfc n x - 2 * x * iRepErfc (n + 1) x := by
  induction n generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    -- goal: `2 * 2 * i²erfc x = erfc x - 2x·i¹erfc x`; consider
    -- g(t) = 2·2·i²erfc t − i⁰erfc t + 2t·i¹erfc t: g' = 0 via the seed identity, g → 0.
    have hderiv : ∀ y : ℝ, HasDerivAt (fun t => 2 * 2 * iRepErfc 2 t
        - iRepErfc 0 t + 2 * t * iRepErfc 1 t) 0 y := by
      intro y
      have h2 : HasDerivAt (fun t => 2 * 2 * iRepErfc 2 t) (2 * 2 * -iRepErfc 1 y) y :=
        (hasDerivAt_iRepErfc_succ 1 y).const_mul _
      have h0 : HasDerivAt (fun t => iRepErfc 0 t)
          (-(2 / Real.sqrt Real.pi * Real.exp (-y ^ 2))) y := hasDerivAt_erfc y
      have h1 : HasDerivAt (fun t : ℝ => 2 * t * iRepErfc 1 t)
          (2 * 1 * iRepErfc 1 y + 2 * y * -iRepErfc 0 y) y :=
        ((hasDerivAt_id y).const_mul 2).mul (hasDerivAt_iRepErfc_succ 0 y)
      have h := (h2.sub h0).add h1
      have hval : 2 * 2 * -iRepErfc 1 y - -(2 / Real.sqrt Real.pi * Real.exp (-y ^ 2))
          + (2 * 1 * iRepErfc 1 y + 2 * y * -iRepErfc 0 y) = 0 := by
        simp only [iRepErfc_zero_apply]
        linarith [two_iRepErfc_one_add y]
      rw [hval] at h
      exact h
    have hlim : Tendsto (fun t : ℝ => 2 * 2 * iRepErfc 2 t
        - iRepErfc 0 t + 2 * t * iRepErfc 1 t) atTop (𝓝 0) := by
      have hA := (tendsto_iRepErfc_atTop 2).const_mul (2 * 2 : ℝ)
      have hB := tendsto_iRepErfc_atTop 0
      have hC := (tendsto_id_mul_iRepErfc_atTop 1).const_mul (2 : ℝ)
      simpa using ((hA.sub hB).add hC).congr fun t => by
        simp only [iRepErfc_zero_apply]; ring
    have h := eq_zero_of_hasDerivAt_zero_of_tendsto hderiv hlim x
    have h' : 2 * 2 * iRepErfc 2 x - iRepErfc 0 x + 2 * x * iRepErfc 1 x = 0 := h
    linarith
  | succ n ih =>
    push_cast
    rw [show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl]
    -- goal: `2·(n+3)·i^{n+3}erfc x = i^{n+1}erfc x − 2x·i^{n+2}erfc x`; consider
    -- g(t) = 2(n+3)·i^{n+3}erfc t − i^{n+1}erfc t + 2t·i^{n+2}erfc t: g' = −(IH) = 0, g → 0.
    have hderiv : ∀ y : ℝ, HasDerivAt (fun t => 2 * ((n : ℝ) + 1 + 2) * iRepErfc (n + 3) t
        - iRepErfc (n + 1) t + 2 * t * iRepErfc (n + 2) t) 0 y := by
      intro y
      have h3 : HasDerivAt (fun t => 2 * ((n : ℝ) + 1 + 2) * iRepErfc (n + 3) t)
          (2 * ((n : ℝ) + 1 + 2) * -iRepErfc (n + 2) y) y :=
        (hasDerivAt_iRepErfc_succ (n + 2) y).const_mul _
      have h0 : HasDerivAt (fun t => iRepErfc (n + 1) t) (-iRepErfc n y) y :=
        hasDerivAt_iRepErfc_succ n y
      have h1 : HasDerivAt (fun t : ℝ => 2 * t * iRepErfc (n + 2) t)
          (2 * 1 * iRepErfc (n + 2) y + 2 * y * -iRepErfc (n + 1) y) y :=
        ((hasDerivAt_id y).const_mul 2).mul (hasDerivAt_iRepErfc_succ (n + 1) y)
      have h := (h3.sub h0).add h1
      have hval : 2 * ((n : ℝ) + 1 + 2) * -iRepErfc (n + 2) y - -iRepErfc n y
          + (2 * 1 * iRepErfc (n + 2) y + 2 * y * -iRepErfc (n + 1) y) = 0 := by
        linarith [ih y]
      rw [hval] at h
      exact h
    have hlim : Tendsto (fun t : ℝ => 2 * ((n : ℝ) + 1 + 2) * iRepErfc (n + 3) t
        - iRepErfc (n + 1) t + 2 * t * iRepErfc (n + 2) t) atTop (𝓝 0) := by
      have hA := (tendsto_iRepErfc_atTop (n + 3)).const_mul (2 * ((n : ℝ) + 1 + 2))
      have hB := tendsto_iRepErfc_atTop (n + 1)
      have hC := (tendsto_id_mul_iRepErfc_atTop (n + 2)).const_mul (2 : ℝ)
      simpa using ((hA.sub hB).add hC).congr fun t => by ring
    have h := eq_zero_of_hasDerivAt_zero_of_tendsto hderiv hlim x
    have h' : 2 * ((n : ℝ) + 1 + 2) * iRepErfc (n + 3) x - iRepErfc (n + 1) x
        + 2 * x * iRepErfc (n + 2) x = 0 := h
    linarith

-- no-dlmf: real-axis restriction of DLMF 7.18.5 (real variable *and* real
-- constants `A`, `B`, where DLMF's `z` is complex and `A`, `B` are arbitrary);
-- faithful surface is `cerf_7_18_5` (ComplexRepeatedErfc.lean)
/-- Every member `W(x) = A·iⁿerfc(x) + B·iⁿerfc(−x)` of the real solution family
satisfies the second-order ODE `W'' + 2x W' − 2n W = 0`, for `n = 1, 2, 3, …`
(the DLMF index convention `1 ≤ n`). -/
theorem erf_7_18_5 (n : ℕ) (hn : 1 ≤ n) (A B : ℝ) (x : ℝ) :
    deriv (deriv (fun z => A * iRepErfc n z + B * iRepErfc n (-z))) x
      + 2 * x * deriv (fun z => A * iRepErfc n z + B * iRepErfc n (-z)) x
      - 2 * (n : ℝ) * (A * iRepErfc n x + B * iRepErfc n (-x)) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hW : ∀ y : ℝ, HasDerivAt (fun z => A * iRepErfc (m + 1) z + B * iRepErfc (m + 1) (-z))
      (A * -iRepErfc m y + B * iRepErfc m (-y)) y := by
    intro y
    have hA : HasDerivAt (fun z : ℝ => A * iRepErfc (m + 1) z) (A * -iRepErfc m y) y :=
      (hasDerivAt_iRepErfc_succ m y).const_mul A
    have hB : HasDerivAt (fun z : ℝ => iRepErfc (m + 1) (-z)) (iRepErfc m (-y)) y := by
      simpa [Function.comp] using
        (hasDerivAt_iRepErfc_succ m (-y)).comp y (hasDerivAt_neg y)
    exact hA.add (hB.const_mul B)
  have hd1 : deriv (fun z => A * iRepErfc (m + 1) z + B * iRepErfc (m + 1) (-z))
      = fun y => A * -iRepErfc m y + B * iRepErfc m (-y) :=
    funext fun y => (hW y).deriv
  simp only [hd1]
  cases m with
  | zero =>
    have h1 : HasDerivAt (fun y : ℝ => -iRepErfc 0 y)
        (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
      simpa using (hasDerivAt_erfc x).neg
    have h2 : HasDerivAt (fun y : ℝ => iRepErfc 0 (-y))
        (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
      simpa [Function.comp, neg_sq] using
        (hasDerivAt_erfc (-x)).comp x (hasDerivAt_neg x)
    have hcomb : HasDerivAt (fun y : ℝ => A * -iRepErfc 0 y + B * iRepErfc 0 (-y))
        (A * (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2))
          + B * (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2))) x :=
      (h1.const_mul A).add (h2.const_mul B)
    rw [hcomb.deriv]
    simp only [iRepErfc_zero_apply, zero_add, Nat.cast_one]
    have h7 := two_iRepErfc_one_add (-x)
    rw [neg_sq] at h7
    linear_combination (-A) * two_iRepErfc_one_add x + (-B) * h7
  | succ k =>
    rw [show k + 1 + 1 = k + 2 from rfl]
    have h1 : HasDerivAt (fun y : ℝ => -iRepErfc (k + 1) y) (iRepErfc k x) x := by
      simpa using (hasDerivAt_iRepErfc_succ k x).neg
    have h2 : HasDerivAt (fun y : ℝ => iRepErfc (k + 1) (-y)) (iRepErfc k (-x)) x := by
      simpa [Function.comp] using
        (hasDerivAt_iRepErfc_succ k (-x)).comp x (hasDerivAt_neg x)
    have hcomb : HasDerivAt (fun y : ℝ => A * -iRepErfc (k + 1) y + B * iRepErfc (k + 1) (-y))
        (A * iRepErfc k x + B * iRepErfc k (-x)) x :=
      (h1.const_mul A).add (h2.const_mul B)
    rw [hcomb.deriv]
    push_cast
    linear_combination (-A) * erf_7_18_7 k x + (-B) * erf_7_18_7 k (-x)

-- no-dlmf: derivative of e^{z²}·iⁿerfc(z); support lemma for DLMF 7.18.4, no separate
-- DLMF identity number
/-- `d/dz (e^{z²}·iⁿerfc(z)) = −2(n+1)·e^{z²}·i^{n+1}erfc(z)` — the single derivative
step powering DLMF 7.18.4, from the recurrence 7.18.7 (seed case: `two_iRepErfc_one_add`). -/
theorem hasDerivAt_expSq_mul_iRepErfc (n : ℕ) (z : ℝ) :
    HasDerivAt (fun t => Real.exp (t ^ 2) * iRepErfc n t)
      (-(2 * ((n : ℝ) + 1)) * (Real.exp (z ^ 2) * iRepErfc (n + 1) z)) z := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2)) (Real.exp (z ^ 2) * (2 * z)) z := by
    have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    exact hsq.exp
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    have h := hexp.mul (hasDerivAt_erfc z)
    have hval : Real.exp (z ^ 2) * (2 * z) * erfc z
        + Real.exp (z ^ 2) * -(2 / Real.sqrt Real.pi * Real.exp (-z ^ 2))
        = -(2 * 1) * (Real.exp (z ^ 2) * iRepErfc 1 z) := by
      linear_combination Real.exp (z ^ 2) * two_iRepErfc_one_add z
    rw [hval] at h
    exact h
  | succ m =>
    have h := hexp.mul (hasDerivAt_iRepErfc_succ m z)
    have hval : Real.exp (z ^ 2) * (2 * z) * iRepErfc (m + 1) z
        + Real.exp (z ^ 2) * -iRepErfc m z
        = -(2 * ((↑(m + 1) : ℝ) + 1)) * (Real.exp (z ^ 2) * iRepErfc (m + 1 + 1) z) := by
      rw [show m + 1 + 1 = m + 2 from rfl]
      push_cast
      linear_combination Real.exp (z ^ 2) * erf_7_18_7 m z
    rw [hval] at h
    exact h

end FLMF.Error
