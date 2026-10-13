import FLMF.Functions.Error.Erf
import FLMF.Functions.Error.Ch7Symmetry
import FLMF.Functions.Error.ComplexErf
import FLMF.Functions.Error.Ch7Inequalities
import FLMF.Methods.SeriesReversion

/-!
# Inverse error functions `inverf` and `inverfc` (DLMF §7.17)

This file is the statement surface for DLMF §7.17 "Inverse Error Functions"
(equations 7.17.1–7.17.6, plus the coefficient recursion 7.17.2_5).

The inverse error functions are intrinsic to this section, so we define them here
as honest total `noncomputable def`s using `Function.invFun`:

* `FLMF.Error.inverf  x = Function.invFun erf  x`
* `FLMF.Error.inverfc x = Function.invFun erfc x`

`erf` and `erfc` are strictly monotone (hence injective) on `ℝ`, so on the
respective ranges `(-1, 1)` and `(0, 2)` these `invFun`s are genuine inverses:
`erf (inverf x) = x` for `|x| < 1` and `erfc (inverfc x) = x` for `0 < x < 2`.

All identities below are stated faithfully and none is weakened to a
vacuous/`True` form.  The file is now `sorry`-free: the last open gap,
the leading-term asymptotic 7.17.3, is proved in the
`InverfcAsymptotics` section below.
-/

namespace FLMF.Error

open Real

-- no-dlmf: defined by the 7.17.1 display (both inverses); surfaced at `erf_7_17_1`
/-- The inverse error function `inverf = erf⁻¹`, defined as `Function.invFun erf`
(DLMF 7.17.1). On the range `(-1, 1)` of `erf` this is a genuine inverse.

-/
noncomputable def inverf (x : ℝ) : ℝ := Function.invFun erf x

-- no-dlmf: defined by the 7.17.1 display (both inverses); surfaced at `erf_7_17_1`
/-- The inverse complementary error function `inverfc = erfc⁻¹`, defined as
`Function.invFun erfc` (DLMF 7.17.1). On the range `(0, 2)` of `erfc` this is a
genuine inverse.

-/
noncomputable def inverfc (x : ℝ) : ℝ := Function.invFun erfc x

-- no-dlmf: coefficient def for the 7.17.2 series (display surfaced at `erf_7_17_2`; its recursion 7.17.2_5 at `erf_7_17_2_5`)
/-- The power-series coefficients `a_m` of `inverf` (DLMF 7.17.2/7.17.2_5):
`a₀ = 1` and `a_{m+1} = (1/(2m+3)) · ∑_{n=0}^{m} ((2n+1)/(m-n+1)) · a_n · a_{m-n}`.
This is the honest total definition by strong recursion; the recursion identity
is recorded as the theorem `erf_7_17_2_5`.

-/
noncomputable def inverfCoeff : ℕ → ℝ :=
  fun k => k.strongRecOn' fun k ih =>
    match k, ih with
    | 0, _ => 1
    | (m + 1), ih =>
        (1 / (2 * m + 3)) *
          ∑ n ∈ (Finset.range (m + 1)).attach,
            ((2 * (n : ℝ) + 1) / (m - n + 1)) *
              ih n (Nat.lt_succ_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp n.2))) *
              ih (m - n) (Nat.lt_succ_of_le (Nat.sub_le m n))

-- no-dlmf: support lemma for 7.17.1 surjectivity
/-- `erf x → -1` as `x → -∞` (oddness of `erf` applied to `erf_tendsto_one`). -/
theorem erf_tendsto_atBot : Filter.Tendsto erf Filter.atBot (nhds (-1)) := by
  have h : Filter.Tendsto (fun x : ℝ => erf (-x)) Filter.atBot (nhds 1) :=
    erf_tendsto_one.comp Filter.tendsto_neg_atBot_atTop
  have h2 : Filter.Tendsto (fun x : ℝ => -erf x) Filter.atBot (nhds 1) := by
    refine h.congr fun x => ?_
    rw [erf_7_4_1]
  have h3 := h2.neg
  simpa using h3

-- no-dlmf: support lemma for 7.17.1 surjectivity
/-- `erf` is surjective onto `(-1, 1)`: every `y` in that open interval is
`erf x` for some `x` (via the intermediate value theorem between the atBot/atTop
limits `-1`/`1`). -/
theorem erf_surj {y : ℝ} (h1 : -1 < y) (h2 : y < 1) : ∃ x, erf x = y := by
  obtain ⟨a0, ha0⟩ := Filter.eventually_atBot.mp (erf_tendsto_atBot.eventually_lt_const h1)
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp (erf_tendsto_one.eventually_const_lt h2)
  set a := min a0 b0 - 1 with ha_def
  set b := max a0 b0 + 1 with hb_def
  have hale : a ≤ a0 := by rw [ha_def]; have := min_le_left a0 b0; linarith
  have hble : b0 ≤ b := by rw [hb_def]; have := le_max_right a0 b0; linarith
  have hab : a ≤ b := by
    have h1' : a ≤ min a0 b0 := by rw [ha_def]; linarith
    have h2' : max a0 b0 ≤ b := by rw [hb_def]; linarith
    have := min_le_max (a := a0) (b := b0)
    linarith
  have hya : erf a < y := ha0 a hale
  have hyb : y < erf b := hb0 b hble
  have hmem : y ∈ Set.Icc (erf a) (erf b) := ⟨hya.le, hyb.le⟩
  have hsub := intermediate_value_Icc hab continuous_erf.continuousOn
  obtain ⟨x, _, hx⟩ := hsub hmem
  exact ⟨x, hx⟩

-- no-dlmf: chain link 7.17.1 (assembled in `erf_7_17_1` below, alongside the
-- inverfc branch); `inverf` is the inverse of `erf` on `erf`'s range `(-1, 1)`
/-- `inverf` is the inverse of `erf`: for `|x| < 1` (the open interval that is
the range of `erf` on `ℝ`), `erf (inverf x) = x`. -/
theorem inverf_erf_eq (x : ℝ) (hx : |x| < 1) : erf (inverf x) = x := by
  unfold inverf
  rw [abs_lt] at hx
  exact Function.invFun_eq (erf_surj hx.1 hx.2)

-- no-dlmf: chain link 7.17.1 (assembled in `erf_7_17_1` below, alongside the
-- inverf branch); `inverfc` is the inverse of `erfc` on `erfc`'s range `(0, 2)`
/-- `inverfc` is the inverse of `erfc`: for `0 < x < 2` (the open interval that
is the range of `erfc` on `ℝ`), `erfc (inverfc x) = x`. -/
theorem inverfc_erfc_eq (x : ℝ) (hx₀ : 0 < x) (hx₂ : x < 2) : erfc (inverfc x) = x := by
  unfold inverfc
  refine Function.invFun_eq ?_
  obtain ⟨a, ha⟩ := erf_surj (y := 1 - x) (by linarith) (by linarith)
  exact ⟨a, by unfold erfc; rw [ha]; ring⟩

/-- **DLMF 7.17.1**: `inverf`/`inverfc` are the inverses of `erf`/`erfc`, on
`erf`'s range `(-1, 1)` and `erfc`'s range `(0, 2)` respectively.

DLMF 7.17.1.
DAG: E-7.17.1.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem erf_7_17_1 :
    (∀ x : ℝ, |x| < 1 → erf (inverf x) = x) ∧
    (∀ x : ℝ, 0 < x → x < 2 → erfc (inverfc x) = x) :=
  ⟨inverf_erf_eq, inverfc_erfc_eq⟩

/-- **DLMF 7.17.2_5.** Recursion for the power-series coefficients `a_m` of
`inverf`: for every `m`,
`a_{m+1} = (1/(2m+3)) · ∑_{n=0}^{m} ((2n+1)/(m-n+1)) · a_n · a_{m-n}`.
Here `a_m = inverfCoeff m`; this is exactly the defining recursion, recorded as a
checkable identity.

DLMF 7.17.2_5.
DAG: E-7.17.2_5.
Fidelity: tier1 PASS
Verified: verified (tier2)
-/
theorem erf_7_17_2_5 (m : ℕ) :
    inverfCoeff (m + 1) =
      (1 / (2 * m + 3)) *
        ∑ n ∈ Finset.range (m + 1),
          ((2 * (n : ℝ) + 1) / (m - n + 1)) * inverfCoeff n * inverfCoeff (m - n) := by
  conv_lhs => rw [inverfCoeff, Nat.strongRecOn'_beta]
  rw [← Finset.sum_attach (Finset.range (m + 1))
        (fun n => ((2 * (n : ℝ) + 1) / (m - n + 1)) * inverfCoeff n * inverfCoeff (m - n))]
  rfl

/-- **DLMF 7.17.5.** The expansion variable `u` for the large-argument (small
`x → 0⁺`) asymptotics of `inverfc`:
`u = -2 / ln(π x² ln(1/x))`.

Domain guard. DLMF §7.17(iii) is the small positive-`x` regime, so the formula is
declared only on `0 < x < 1`; there every logarithm argument is a genuine positive
real (`ln(1/x) > 0`, hence `π x² ln(1/x) > 0`). At `x ≤ 0` or `x ≥ 1` Mathlib's
`Real.log` would still return a value, but a sign-blind one (`Real.log` is
`log |·|`, with `Real.log 0 = 0`), i.e. a number DLMF never asserts. The `if`
therefore sends every out-of-domain argument to the explicit junk value `0`,
so nothing outside DLMF's regime is silently claimed. Use `asymU_of_mem` to
unfold inside the domain.

DLMF 7.17.5.
DAG: E-7.17.5.
-/
-- Verified: verified (tier2)
noncomputable def asymU (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then -2 / Real.log (Real.pi * x ^ 2 * Real.log (1 / x)) else 0

-- no-dlmf: unguard lemma — `asymU` on its declared DLMF domain `0 < x < 1`
/-- Inside DLMF's regime `0 < x < 1` the guard of `asymU` opens up to the
7.17.5 formula. -/
theorem asymU_of_mem {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    asymU x = -2 / Real.log (Real.pi * x ^ 2 * Real.log (1 / x)) :=
  if_pos ⟨hx0, hx1⟩

/-- **DLMF 7.17.6.** The second expansion variable `v`:
`v = ln(ln(1/x)) - 2 + ln π`.

Domain guard. As for `asymU`, DLMF §7.17(iii) is the small positive-`x` regime,
so the formula is declared only on `0 < x < 1`, where `ln(1/x) > 0` and the outer
logarithm has a positive real argument. Outside that interval Mathlib's
`Real.log` would evaluate sign-blind (`log |·|`, `Real.log 0 = 0`) and produce a
value DLMF never defines, so the `if` replaces it with the explicit junk value
`0`. Use `asymV_of_mem` to unfold inside the domain.

DLMF 7.17.6.
DAG: E-7.17.6.
-/
-- Verified: verified (tier2)
noncomputable def asymV (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then Real.log (Real.log (1 / x)) - 2 + Real.log Real.pi else 0

-- no-dlmf: unguard lemma — `asymV` on its declared DLMF domain `0 < x < 1`
/-- Inside DLMF's regime `0 < x < 1` the guard of `asymV` opens up to the
7.17.6 formula. -/
theorem asymV_of_mem {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    asymV x = Real.log (Real.log (1 / x)) - 2 + Real.log Real.pi :=
  if_pos ⟨hx0, hx1⟩

-- no-dlmf: support def for the 7.17.4 expansion; display surfaced at `erf_7_17_4_dlmf`
/-- **DLMF 7.17.4.** The first asymptotic coefficients of the `inverfc`
large-argument expansion, in terms of `v = asymV x` (DLMF 7.17.6):
`a₂ = v/8`, `a₃ = -(v² + 6v - 6)/32`, `a₄ = (4v³ + 27v² + 108v - 300)/384`.
(These `a_k` are *local* to the asymptotic expansion and are distinct from the
power-series coefficients `inverfCoeff` of 7.17.2.)

-/
noncomputable def asymA (x : ℝ) : ℕ → ℝ
  | 2 => (1 / 8) * asymV x
  | 3 => -(1 / 32) * ((asymV x) ^ 2 + 6 * asymV x - 6)
  | 4 => (1 / 384) * (4 * (asymV x) ^ 3 + 27 * (asymV x) ^ 2 + 108 * asymV x - 300)
  | _ => 0

-- no-dlmf: chain link 7.17.4 (assembled in `erf_7_17_4` below, alongside the
-- a₃/a₄ links); definitional unfolding of `asymA` at k=2 (the identity is
-- `rfl`), holding only in the asymptotic regime `x → 0⁺` (not "for any real x"
-- as this unrestricted rfl fact would suggest)
/-- `a₂ = v/8`.  Recorded as a checkable equality. -/
theorem erf_7_17_4_a2 (x : ℝ) : asymA x 2 = (1 / 8) * asymV x := rfl

-- no-dlmf: chain link 7.17.4 (assembled in `erf_7_17_4` below, alongside the
-- a₂/a₄ links); definitional unfolding of `asymA` at k=3 (the identity is
-- `rfl`), holding only in the asymptotic regime `x → 0⁺` (not "for any real x"
-- as this unrestricted rfl fact would suggest)
/-- `a₃ = -(v² + 6v - 6)/32`. -/
theorem erf_7_17_4_a3 (x : ℝ) :
    asymA x 3 = -(1 / 32) * ((asymV x) ^ 2 + 6 * asymV x - 6) := rfl

-- no-dlmf: chain link 7.17.4 (assembled in `erf_7_17_4` below, alongside the
-- a₂/a₃ links); definitional unfolding of `asymA` at k=4 (the identity is
-- `rfl`), holding only in the asymptotic regime `x → 0⁺` (not "for any real x"
-- as this unrestricted rfl fact would suggest)
/-- `a₄ = (4v³ + 27v² + 108v - 300)/384`. -/
theorem erf_7_17_4_a4 (x : ℝ) :
    asymA x 4 = (1 / 384) * (4 * (asymV x) ^ 3 + 27 * (asymV x) ^ 2 + 108 * asymV x - 300) :=
  rfl

-- no-dlmf: domain-wider version of DLMF 7.17.4, holding as an unconditional
-- definitional identity for every real `x`, whereas DLMF places these
-- coefficients `a₂,a₃,a₄` in the asymptotic regime `x → 0⁺`; faithful surface
-- is `erf_7_17_4_dlmf`
/-- The first asymptotic coefficients of the `inverfc` large-argument expansion, in
terms of `v = asymV x` (DLMF 7.17.6): `a₂ = v/8`, `a₃ = -(v² + 6v - 6)/32`,
`a₄ = (4v³ + 27v² + 108v - 300)/384`. -/
theorem erf_7_17_4 (x : ℝ) :
    asymA x 2 = (1 / 8) * asymV x ∧
    asymA x 3 = -(1 / 32) * ((asymV x) ^ 2 + 6 * asymV x - 6) ∧
    asymA x 4 = (1 / 384) * (4 * (asymV x) ^ 3 + 27 * (asymV x) ^ 2 + 108 * asymV x - 300) :=
  ⟨erf_7_17_4_a2 x, erf_7_17_4_a3 x, erf_7_17_4_a4 x⟩

/-- **DLMF 7.17.4.** As `x → 0⁺`, the first asymptotic coefficients of the
`inverfc` small-argument expansion, in terms of `v = asymV x` (7.17.6):
`a₂ = v/8`, `a₃ = -(v² + 6v - 6)/32`, `a₄ = (4v³ + 27v² + 108v - 300)/384`.

DLMF places these coefficient formulas in the `x → 0⁺` asymptotic setting of
§7.17(iii); this is encoded by asserting them eventually along the filter
`𝓝[>] 0` (they in fact hold identically in the regime, so no truncation of
content occurs).

DAG: E-7.17.4.
Fidelity: tier1 stale
Verified: verified (tier2)
-/
theorem erf_7_17_4_dlmf :
    ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      asymA x 2 = (1 / 8) * asymV x ∧
      asymA x 3 = -(1 / 32) * ((asymV x) ^ 2 + 6 * asymV x - 6) ∧
      asymA x 4 = (1 / 384) * (4 * (asymV x) ^ 3 + 27 * (asymV x) ^ 2 + 108 * asymV x - 300) :=
  Filter.Eventually.of_forall erf_7_17_4

section InverfcAsymptotics

open Filter Topology Asymptotics

/-! ### Support for DLMF 7.17.3: `inverfc x · √(u) → 1` as `x → 0⁺`

The route is a change of variable.  Put `y = inverfc x`, so `erfc y = x` and
`y → ∞` as `x → 0⁺`.  The Mills-ratio bounds of DLMF 7.8.2 (`erf_7_8_2`) pin
`erfc y` between two explicit multiples of `e^{−y²}/y`, hence
`ln(erfc y) = −y² − ln y + O(1)`.  Feeding that into the expansion variable
`u = asymU x = −2 / ln(π x² ln(1/x))` of 7.17.5 gives
`ln(π x² ln(1/x)) = −2y² + O(ln y)`, i.e. `y² · u → 1`, which is exactly the
leading term `inverfc x ∼ u^{−1/2}` of 7.17.3.
-/

-- no-dlmf: analytic support lemma — strict monotonicity of `erf` (positive derivative)
/-- `erf` is strictly monotone (its derivative `(2/√π) e^{-x²}` is positive). -/
theorem strictMono_erf : StrictMono erf := by
  refine strictMono_of_deriv_pos fun x => ?_
  rw [(hasDerivAt_erf x).deriv]
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

-- no-dlmf: support lemma for 7.17.3 — positivity of `erfc` on all of `ℝ`
/-- `erfc` is everywhere positive (`erf < 1`, by strict monotonicity and `erf → 1`). -/
theorem erfc_pos (x : ℝ) : 0 < erfc x := by
  have h1 : erf x < erf (x + 1) := strictMono_erf (by linarith)
  have h2 : erf (x + 1) ≤ 1 := strictMono_erf.monotone.ge_of_tendsto erf_tendsto_one (x + 1)
  unfold erfc
  linarith

-- no-dlmf: support lemma for 7.17.3 — `erfc` is strictly decreasing
/-- `erfc = 1 − erf` is strictly antitone. -/
theorem strictAnti_erfc : StrictAnti erfc := by
  intro a b hab
  have := strictMono_erf hab
  unfold erfc
  linarith

-- no-dlmf: support lemma for 7.17.3 — explicit Mills lower bound on `[1,∞)`
/-- For `y ≥ 1`, `erfc y > (2/(3√π))·e^{−y²}/y` (from DLMF 7.8.2 and
`y + √(y²+2) ≤ 3y`). -/
theorem erfc_lower_bound {y : ℝ} (hy : 1 ≤ y) :
    2 / (3 * Real.sqrt Real.pi) * (Real.exp (-y ^ 2) / y) < erfc y := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hlow := (erf_7_8_2 y hy0.le).1
  have hs : Real.sqrt (y ^ 2 + 2) ≤ 2 * y := by
    rw [show (2:ℝ) * y = Real.sqrt ((2 * y) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : 1 / (3 * y) ≤ 1 / (y + Real.sqrt (y ^ 2 + 2)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1 / (3 * y) < Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y :=
    lt_of_le_of_lt h1 hlow
  have hcoef : (0:ℝ) < 2 / Real.sqrt Real.pi * Real.exp (-y ^ 2) := by positivity
  have he : Real.exp (-y ^ 2) * Real.exp (y ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc 2 / (3 * Real.sqrt Real.pi) * (Real.exp (-y ^ 2) / y)
      = (2 / Real.sqrt Real.pi * Real.exp (-y ^ 2)) * (1 / (3 * y)) := by
        field_simp
    _ < (2 / Real.sqrt Real.pi * Real.exp (-y ^ 2)) *
          (Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y) :=
        mul_lt_mul_of_pos_left h2 hcoef
    _ = (2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2)) *
          (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) * erfc y := by ring
    _ = erfc y := by rw [he]; field_simp

-- no-dlmf: support lemma for 7.17.3 — explicit Mills upper bound on `[1,∞)`
/-- For `y ≥ 1`, `erfc y ≤ (1/√π)·e^{−y²}/y` (from DLMF 7.8.2 and
`y + √(y²+4/π) ≥ 2y`). -/
theorem erfc_upper_bound {y : ℝ} (hy : 1 ≤ y) :
    erfc y ≤ 1 / Real.sqrt Real.pi * (Real.exp (-y ^ 2) / y) := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hup := (erf_7_8_2 y hy0.le).2
  have hs : y ≤ Real.sqrt (y ^ 2 + 4 / Real.pi) := by
    rw [show y = Real.sqrt (y ^ 2) by rw [Real.sqrt_sq hy0.le]]
    refine Real.sqrt_le_sqrt ?_
    rw [Real.sqrt_sq hy0.le]
    have : (0:ℝ) < 4 / Real.pi := by positivity
    linarith
  have h1 : 1 / (y + Real.sqrt (y ^ 2 + 4 / Real.pi)) ≤ 1 / (2 * y) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y ≤ 1 / (2 * y) := le_trans hup h1
  have hcoef : (0:ℝ) < 2 / Real.sqrt Real.pi * Real.exp (-y ^ 2) := by positivity
  have he : Real.exp (-y ^ 2) * Real.exp (y ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc erfc y
      = (2 / Real.sqrt Real.pi * (Real.sqrt Real.pi / 2)) *
          (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) * erfc y := by rw [he]; field_simp
    _ = (2 / Real.sqrt Real.pi * Real.exp (-y ^ 2)) *
          (Real.sqrt Real.pi / 2 * Real.exp (y ^ 2) * erfc y) := by ring
    _ ≤ (2 / Real.sqrt Real.pi * Real.exp (-y ^ 2)) * (1 / (2 * y)) :=
        mul_le_mul_of_nonneg_left h2 hcoef.le
    _ = 1 / Real.sqrt Real.pi * (Real.exp (-y ^ 2) / y) := by field_simp

-- no-dlmf: support lemma for 7.17.3 — logarithm of the Mills majorants
/-- `ln (K · e^{−y²}/y) = ln K − y² − ln y` for `K, y > 0`. -/
theorem log_bound_split {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    Real.log (K * (Real.exp (-y ^ 2) / y)) = Real.log K - y ^ 2 - Real.log y := by
  rw [Real.log_mul hK.ne' (by positivity), Real.log_div (Real.exp_ne_zero _) hy.ne',
    Real.log_exp]
  ring

-- no-dlmf: support lemma for 7.17.3 — lower log bound on `erfc`
/-- `ln(2/(3√π)) − y² − ln y ≤ ln (erfc y)` for `y ≥ 1`. -/
theorem log_erfc_lower {y : ℝ} (hy : 1 ≤ y) :
    Real.log (2 / (3 * Real.sqrt Real.pi)) - y ^ 2 - Real.log y ≤ Real.log (erfc y) := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hK : (0:ℝ) < 2 / (3 * Real.sqrt Real.pi) := by positivity
  have h := (erfc_lower_bound hy).le
  have := Real.log_le_log (by positivity) h
  rwa [log_bound_split hK hy0] at this

-- no-dlmf: support lemma for 7.17.3 — upper log bound on `erfc`
/-- `ln (erfc y) ≤ ln(1/√π) − y² − ln y` for `y ≥ 1`. -/
theorem log_erfc_upper {y : ℝ} (hy : 1 ≤ y) :
    Real.log (erfc y) ≤ Real.log (1 / Real.sqrt Real.pi) - y ^ 2 - Real.log y := by
  have hpi : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hK : (0:ℝ) < 1 / Real.sqrt Real.pi := by positivity
  have h := erfc_upper_bound hy
  have := Real.log_le_log (erfc_pos y) h
  rwa [log_bound_split hK hy0] at this

-- no-dlmf: support limit for 7.17.3
/-- `ln y / y² → 0` as `y → ∞`. -/
theorem tendsto_log_div_sq : Tendsto (fun y : ℝ => Real.log y / y ^ 2) atTop (𝓝 0) := by
  have ha : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hb : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ha.mul hb
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  field_simp

-- no-dlmf: support limit for 7.17.3
/-- `(a + b·ln y)/y² → 0` as `y → ∞`. -/
theorem tendsto_affine_log_div_sq (a b : ℝ) :
    Tendsto (fun y : ℝ => (a + b * Real.log y) / y ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => a / y ^ 2) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (tendsto_pow_atTop (two_ne_zero)) a
  have h2 := tendsto_log_div_sq.const_mul b
  rw [mul_zero] at h2
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  field_simp

-- no-dlmf: support limit for 7.17.3 — the common limit of both Mills log bounds
/-- `(K − y² − ln y)/y² → −1` as `y → ∞`. -/
theorem tendsto_base_bound (K : ℝ) :
    Tendsto (fun y : ℝ => (K - y ^ 2 - Real.log y) / y ^ 2) atTop (𝓝 (-1)) := by
  have h := (tendsto_affine_log_div_sq K (-1)).add_const (-1)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  field_simp
  ring

-- no-dlmf: support limit for 7.17.3 — squeeze of the two Mills log bounds
/-- `ln (erfc y) / y² → −1` as `y → ∞`. -/
theorem tendsto_log_erfc_div_sq :
    Tendsto (fun y : ℝ => Real.log (erfc y) / y ^ 2) atTop (𝓝 (-1)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_base_bound (Real.log (2 / (3 * Real.sqrt Real.pi))))
    (tendsto_base_bound (Real.log (1 / Real.sqrt Real.pi))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have := log_erfc_lower hy
    gcongr
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have := log_erfc_upper hy
    gcongr

-- no-dlmf: support lemma for 7.17.3
/-- `ln (1/erfc y) = −ln (erfc y)`. -/
theorem log_one_div_erfc (y : ℝ) : Real.log (1 / erfc y) = -Real.log (erfc y) := by
  rw [one_div, Real.log_inv]

-- no-dlmf: support limit for 7.17.3 — the doubly-logarithmic term is negligible
/-- `ln (ln (1/erfc y)) / y² → 0` as `y → ∞` (from `y² ≤ ln(1/erfc y) ≤ 2y²`). -/
theorem tendsto_loglog_div_sq :
    Tendsto (fun y : ℝ => Real.log (Real.log (1 / erfc y)) / y ^ 2) atTop (𝓝 0) := by
  set c : ℝ := -Real.log (2 / (3 * Real.sqrt Real.pi)) with hc
  have hπ1 : (1:ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hK2 : Real.log (1 / Real.sqrt Real.pi) ≤ 0 := by
    rw [one_div, Real.log_inv, neg_nonpos]
    exact Real.log_nonneg hπ1
  -- eventual sandwich `y² ≤ log(1/erfc y) ≤ 2y²`
  have hsand : ∀ᶠ y : ℝ in atTop,
      y ^ 2 ≤ Real.log (1 / erfc y) ∧ Real.log (1 / erfc y) ≤ 2 * y ^ 2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (2 + |c|)] with y hy hyc
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
    have hlogy' : Real.log y ≤ y - 1 := by
      have := Real.add_one_le_exp (Real.log y)
      rw [Real.exp_log (by positivity)] at this
      linarith
    rw [log_one_div_erfc]
    constructor
    · have := log_erfc_upper hy
      linarith
    · have := log_erfc_lower hy
      have hcy : y - 1 + c ≤ y ^ 2 := by nlinarith [abs_nonneg c, le_abs_self c]
      simp only [hc] at this hcy ⊢
      linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun y : ℝ => Real.log (Real.log (1 / erfc y)) / y ^ 2)
    (g := fun y : ℝ => (0 + 2 * Real.log y) / y ^ 2)
    (h := fun y : ℝ => (Real.log 2 + 2 * Real.log y) / y ^ 2)
    (tendsto_affine_log_div_sq 0 2) (tendsto_affine_log_div_sq (Real.log 2) 2) ?_ ?_
  · filter_upwards [hsand, eventually_ge_atTop (1:ℝ)] with y hy hy1
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy1
    have hlow : Real.log (y ^ 2) ≤ Real.log (Real.log (1 / erfc y)) :=
      Real.log_le_log (by positivity) hy.1
    rw [Real.log_pow] at hlow
    push_cast at hlow
    gcongr
    linarith
  · filter_upwards [hsand, eventually_ge_atTop (1:ℝ)] with y hy hy1
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy1
    have hup : Real.log (Real.log (1 / erfc y)) ≤ Real.log (2 * y ^ 2) :=
      Real.log_le_log (by nlinarith [hy.1]) hy.2
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at hup
    push_cast at hup
    gcongr

-- no-dlmf: support limit for 7.17.3 — `y²·u → 1` along `x = erfc y`
/-- With `u = asymU x` the 7.17.5 expansion variable, `y² · asymU (erfc y) → 1`
as `y → ∞`. -/
theorem tendsto_sq_mul_asymU :
    Tendsto (fun y : ℝ => y ^ 2 * asymU (erfc y)) atTop (𝓝 1) := by
  have hL : Tendsto (fun y : ℝ =>
      Real.log (Real.pi * (erfc y) ^ 2 * Real.log (1 / erfc y)) / y ^ 2) atTop (𝓝 (-2)) := by
    have h1 : Tendsto (fun y : ℝ => Real.log Real.pi / y ^ 2) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop (tendsto_pow_atTop two_ne_zero) _
    have h2 := tendsto_log_erfc_div_sq.const_mul (2:ℝ)
    have h3 := tendsto_loglog_div_sq
    have h := (h1.add h2).add h3
    rw [show (0:ℝ) + 2 * (-1) + 0 = -2 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
    have hE : (0:ℝ) < erfc y := erfc_pos y
    have hℓ : (0:ℝ) < Real.log (1 / erfc y) := by
      rw [log_one_div_erfc]
      have := log_erfc_upper hy
      have hπ1 : (1:ℝ) ≤ Real.sqrt Real.pi := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      have hK2 : Real.log (1 / Real.sqrt Real.pi) ≤ 0 := by
        rw [one_div, Real.log_inv, neg_nonpos]
        exact Real.log_nonneg hπ1
      have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
      nlinarith
    rw [Real.log_mul (by positivity) hℓ.ne', Real.log_mul Real.pi_ne_zero (by positivity),
      Real.log_pow]
    push_cast
    field_simp
  have hne : (-2 : ℝ) ≠ 0 := by norm_num
  have hinvL := hL.inv₀ hne
  have hdiv := hinvL.const_mul (-2 : ℝ)
  rw [show (-2:ℝ) * (-2:ℝ)⁻¹ = 1 by norm_num] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hlt1 : erfc y < 1 := by
    have h := strictAnti_erfc hy
    rwa [erfc_zero] at h
  rw [asymU_of_mem (erfc_pos y) hlt1]
  set L := Real.log (Real.pi * (erfc y) ^ 2 * Real.log (1 / erfc y)) with hLdef
  rcases eq_or_ne L 0 with h | h
  · rw [h]; simp
  · field_simp

-- no-dlmf: support limit for 7.17.3 — square root of the previous limit
/-- `y · √(asymU (erfc y)) → 1` as `y → ∞`. -/
theorem tendsto_mul_sqrt_asymU :
    Tendsto (fun y : ℝ => y * Real.sqrt (asymU (erfc y))) atTop (𝓝 1) := by
  have h := tendsto_sq_mul_asymU
  have hs := h.sqrt
  rw [Real.sqrt_one] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℝ),
    h.eventually_const_lt (show (0:ℝ) < 1 by norm_num)] with y hy hpos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have hu : 0 ≤ asymU (erfc y) := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hy0.le]

-- no-dlmf: support lemma for 7.17.3 — eventual positivity of the expansion variable
/-- `asymU (erfc y) > 0` for all large `y`. -/
theorem eventually_asymU_pos_atTop : ∀ᶠ y : ℝ in atTop, 0 < asymU (erfc y) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    tendsto_sq_mul_asymU.eventually_const_lt (show (0:ℝ) < 1 by norm_num)] with y hy hpos
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith

-- no-dlmf: support lemma for 7.17.3 — the change of variable `y = inverfc x`
/-- `inverfc x → ∞` as `x → 0⁺` (`erfc` is strictly antitone and positive). -/
theorem tendsto_inverfc_atTop : Tendsto inverfc (𝓝[>] (0:ℝ)) atTop := by
  rw [tendsto_atTop]
  intro M
  have hpos : (0:ℝ) < erfc (M + 1) := erfc_pos _
  have hm : (0:ℝ) < min (erfc (M + 1)) 1 := lt_min hpos one_pos
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x < min (erfc (M + 1)) 1 :=
    Filter.eventually_iff.mpr (nhdsWithin_le_nhds (Iio_mem_nhds hm))
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hx0
  have hx0' : (0:ℝ) < x := hx0
  have hx1 : x < erfc (M + 1) := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : x < 2 := lt_of_lt_of_le (lt_of_lt_of_le hx (min_le_right _ _)) (by norm_num)
  have hE := inverfc_erfc_eq x hx0' hx2
  by_contra hcon
  rw [not_le] at hcon
  have hlt : erfc (M + 1) < erfc (inverfc x) := strictAnti_erfc (by linarith)
  rw [hE] at hlt
  linarith

-- no-dlmf: support lemma for 7.17.3 — the punctured neighbourhood sits in `erfc`'s range
/-- Every `x` near `0⁺` lies in `(0, 2)`, the range of `erfc`. -/
theorem eventually_mem_Ioo : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), 0 < x ∧ x < 2 := by
  have h2 : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x < 2 :=
    Filter.eventually_iff.mpr (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 2)))
  filter_upwards [h2, self_mem_nhdsWithin] with x hx hx0
  exact ⟨hx0, hx⟩

-- no-dlmf: support limit for 7.17.3 — the previous limit pulled back to `x → 0⁺`
/-- `inverfc x · √(asymU x) → 1` as `x → 0⁺`. -/
theorem tendsto_inverfc_mul_sqrt :
    Tendsto (fun x : ℝ => inverfc x * Real.sqrt (asymU x)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hcomp := tendsto_mul_sqrt_asymU.comp tendsto_inverfc_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_mem_Ioo] with x hx
  simp only [Function.comp_apply]
  rw [inverfc_erfc_eq x hx.1 hx.2]

-- no-dlmf: support lemma for 7.17.3 — eventual positivity of `asymU` near `0⁺`
/-- `asymU x > 0` for `x` near `0⁺`. -/
theorem eventually_asymU_pos : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), 0 < asymU x := by
  have h := tendsto_inverfc_atTop.eventually eventually_asymU_pos_atTop
  filter_upwards [h, eventually_mem_Ioo] with x hx hx2
  rwa [inverfc_erfc_eq x hx2.1 hx2.2] at hx

-- no-dlmf: first-term truncation of DLMF 7.17.3; the canonical carrier is the
-- four-term `erf_7_17_3_full` (Error/Ch7InverseErfExpansion.lean)
/-- Large-argument asymptotic expansion of `inverfc` as `x → 0⁺` (7.17.3,
first-term form): with `u = asymU x` (7.17.5) and the local coefficients
`a_k = asymA x k` (7.17.4),
`inverfc x ∼ u^{-1/2} + a₂ u^{3/2} + a₃ u^{5/2} + a₄ u^{7/2} + ⋯`.

We state the first-term form: the error after the leading term `u^{-1/2}` is
`o(u^{-1/2})` as `x → 0⁺` (a genuine, non-vacuous truncation of the asymptotic
series; the full series is an asymptotic, not convergent, expansion). The
faithful four-term surface is `erf_7_17_3_full`
(Error/Ch7InverseErfExpansion.lean). -/
theorem erf_7_17_3 :
    (fun x : ℝ => inverfc x - (asymU x) ^ (-(1 : ℝ) / 2))
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => (asymU x) ^ (-(1 : ℝ) / 2)) := by
  have hzero : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ),
      (asymU x) ^ (-(1 : ℝ) / 2) = 0 → inverfc x - (asymU x) ^ (-(1 : ℝ) / 2) = 0 := by
    filter_upwards [eventually_asymU_pos] with x hx hcon
    exact absurd hcon (by positivity)
  rw [Asymptotics.isLittleO_iff_tendsto' hzero]
  have h := tendsto_inverfc_mul_sqrt.sub_const 1
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_asymU_pos] with x hx
  have hs : (0:ℝ) < Real.sqrt (asymU x) := Real.sqrt_pos.mpr hx
  have hw : (asymU x) ^ (-(1 : ℝ) / 2) = (Real.sqrt (asymU x))⁻¹ := by
    rw [show (-(1:ℝ)) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  rw [hw]
  field_simp

end InverfcAsymptotics

/-! ## Remaining members of the DLMF 7.17.2 chain -/

-- no-dlmf: instance of DLMF 7.17.2 (only the four leading coefficients a₀..a₃ of the display); faithful surface is erf_7_17_2
/-- The explicit front of the Maclaurin series display
`inverf x = t + ⅓ t³ + (7/30) t⁵ + (127/630) t⁷ + ⋯` (with `t = ½ √π x`) records
the concrete leading coefficients `a₀ = 1`, `a₁ = 1/3`, `a₂ = 7/30`,
`a₃ = 127/630`.  This pins the written-out members of the display to the closed
form `∑ a_m t^{2m+1}` (`erf_7_17_2`); the values follow from the recursion
`erf_7_17_2_5`.
-/
theorem erf_7_17_2_coeffs :
    inverfCoeff 0 = 1 ∧ inverfCoeff 1 = 1 / 3 ∧ inverfCoeff 2 = 7 / 30 ∧
      inverfCoeff 3 = 127 / 630 := by
  have h0 : inverfCoeff 0 = 1 := by
    rw [inverfCoeff, Nat.strongRecOn'_beta]
  have h1 : inverfCoeff 1 = 1 / 3 := by
    rw [erf_7_17_2_5 0]; simp [h0]
  have h2 : inverfCoeff 2 = 7 / 30 := by
    rw [erf_7_17_2_5 1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [h0, h1]; norm_num
  have h3 : inverfCoeff 3 = 127 / 630 := by
    rw [erf_7_17_2_5 2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [h0, h1, h2]; norm_num
  exact ⟨h0, h1, h2, h3⟩

/-! ## Ingredients for the Maclaurin series 7.17.2

The route to `erf_7_17_2` is:

* `inverfCoeff_nonneg` / `inverfCoeff_le` — the coefficients `a_m` of 7.17.2_5 are
  nonnegative and bounded by `2^{2m+1}/(2m+1)`, so `∑ a_m t^{2m+1}` converges for
  `|t| < 1/2`;
* `erf_inverfSeries` — on any interval of convergence the sum `y(t) = ∑ a_m t^{2m+1}`
  satisfies `erf (y t) = 2t/√π`.  This is the exp-free ODE `y' · (1 - 2∫₀ᵗ y) = 1`
  of DLMF 1.10(vii) applied to the recursion 7.17.2_5, assembled by a Cauchy
  product;
* `analyticAt_inverf` — `inverf` is real-analytic on `(-1, 1)` (analytic inverse
  function theorem applied to `erf`);
* `summable_inverfCoeff` — Pringsheim (`FLMF.Methods.summable_mul_pow_of_analyticAt`)
  then pushes the radius of `∑ a_m t^{2m+1}` out to `√π/2`, i.e. `|x| < 1`.
-/

-- no-dlmf: analytic support lemma — `inverf` is a left inverse of `erf`
/-- `inverf (erf x) = x` for every real `x` (`erf` is injective). -/
theorem inverf_erf (x : ℝ) : inverf (erf x) = x :=
  Function.leftInverse_invFun strictMono_erf.injective x

/-! ### The coefficients `a_m` of 7.17.2_5: sign and growth -/

-- no-dlmf: support lemma for `inverfCoeff_le` — a telescoping bound for the
-- convolution sum produced by the recursion 7.17.2_5
/-- `∑_{n<N} 1/((n+1)(2n+1)) ≤ 2`, by telescoping against `2/(2n+1)`. -/
theorem sum_inv_mul_le_two (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) ≤ 2 := by
  have hstep : ∀ n ∈ Finset.range N,
      (1 : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
        ≤ 2 / (2 * (n : ℝ) + 1) - 2 / (2 * ((n : ℝ) + 1) + 1) := by
    intro n _
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < 2 * ((n : ℝ) + 1) + 1 := by positivity
    rw [div_sub_div _ _ (ne_of_gt h2) (ne_of_gt h3), div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg ((n : ℝ))]
  calc ∑ n ∈ Finset.range N, (1 : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.range N,
          (2 / (2 * (n : ℝ) + 1) - 2 / (2 * ((n : ℝ) + 1) + 1)) := Finset.sum_le_sum hstep
    _ = 2 / (2 * ((0 : ℕ) : ℝ) + 1) - 2 / (2 * (N : ℝ) + 1) := by
        have := Finset.sum_range_sub' (f := fun n : ℕ => 2 / (2 * (n : ℝ) + 1)) N
        simpa using this
    _ ≤ 2 := by
        have : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
        simp only [Nat.cast_zero]
        have : (0 : ℝ) ≤ 2 / (2 * (N : ℝ) + 1) := by positivity
        linarith

-- no-dlmf: M0 — nonnegativity of the 7.17.2_5 coefficients
/-- All the Maclaurin coefficients `a_m` of `inverf` (7.17.2_5) are nonnegative. -/
theorem inverfCoeff_nonneg (m : ℕ) : 0 ≤ inverfCoeff m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => rw [erf_7_17_2_coeffs.1]; norm_num
    | (k + 1) =>
      rw [erf_7_17_2_5 k]
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun n hn => ?_)
      rw [Finset.mem_range] at hn
      have hnk : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn
      have h1 : 0 ≤ inverfCoeff n := ih n (by omega)
      have h2 : 0 ≤ inverfCoeff (k - n) := ih (k - n) (by omega)
      have h3 : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) / ((k : ℝ) - (n : ℝ) + 1) :=
        div_nonneg (by positivity) (by linarith)
      exact mul_nonneg (mul_nonneg h3 h1) h2

set_option maxHeartbeats 800000 in
-- no-dlmf: growth bound on the 7.17.2_5 coefficients, giving a positive radius
/-- The Maclaurin coefficients of `inverf` satisfy `a_m ≤ 2^{2m+1}/(2m+1)`.
(The true radius is `√π/2`; this crude bound only certifies `≥ 1/2`, which is
what starts the Pringsheim argument.) -/
theorem inverfCoeff_le (m : ℕ) : inverfCoeff m ≤ 2 ^ (2 * m + 1) / (2 * (m : ℝ) + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => rw [erf_7_17_2_coeffs.1]; norm_num
    | (k + 1) =>
      rw [erf_7_17_2_5 k]
      -- bound each term of the convolution sum by `2^{2k+2} / ((j)(2j-1))`, `j = k-n+1`
      have hterm : ∀ n ∈ Finset.range (k + 1),
          ((2 * (n : ℝ) + 1) / ((k : ℝ) - (n : ℝ) + 1)) * inverfCoeff n * inverfCoeff (k - n)
            ≤ 2 ^ (2 * k + 2) *
                (1 / ((((k - n : ℕ) : ℝ) + 1) * (2 * ((k - n : ℕ) : ℝ) + 1))) := by
        intro n hn
        rw [Finset.mem_range] at hn
        have hnk : n ≤ k := Nat.lt_succ_iff.mp hn
        have hcast : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := by
          push_cast [Nat.cast_sub hnk]; ring
        have h1 : inverfCoeff n ≤ 2 ^ (2 * n + 1) / (2 * (n : ℝ) + 1) := ih n (by omega)
        have h2 : inverfCoeff (k - n) ≤ 2 ^ (2 * (k - n) + 1) / (2 * ((k - n : ℕ) : ℝ) + 1) :=
          ih (k - n) (by omega)
        have hn0 : 0 ≤ inverfCoeff n := inverfCoeff_nonneg n
        have hn1 : 0 ≤ inverfCoeff (k - n) := inverfCoeff_nonneg (k - n)
        have hd1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
        have hd2 : (0 : ℝ) < 2 * ((k - n : ℕ) : ℝ) + 1 := by positivity
        have hd3 : (0 : ℝ) < ((k - n : ℕ) : ℝ) + 1 := by positivity
        have hpow : (2 : ℝ) ^ (2 * n + 1) * 2 ^ (2 * (k - n) + 1) = 2 ^ (2 * k + 2) := by
          rw [← pow_add]
          congr 1
          omega
        have hfac : ((2 * (n : ℝ) + 1) / ((k : ℝ) - (n : ℝ) + 1)) * inverfCoeff n *
              inverfCoeff (k - n)
            ≤ ((2 * (n : ℝ) + 1) / (((k - n : ℕ) : ℝ) + 1)) *
                (2 ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) *
                (2 ^ (2 * (k - n) + 1) / (2 * ((k - n : ℕ) : ℝ) + 1)) := by
          rw [hcast]
          have hc0 : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) / ((k : ℝ) - (n : ℝ) + 1) := by
            refine div_nonneg (by positivity) ?_
            rw [← hcast]; positivity
          have := mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 hn1 (by positivity)
          simpa [hcast] using this
        refine hfac.trans (le_of_eq ?_)
        rw [← hpow]
        field_simp
      have hsum : ∑ n ∈ Finset.range (k + 1),
          ((2 * (n : ℝ) + 1) / ((k : ℝ) - (n : ℝ) + 1)) * inverfCoeff n * inverfCoeff (k - n)
            ≤ 2 ^ (2 * k + 2) * 2 := by
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hrefl := Finset.sum_range_reflect
          (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))) (k + 1)
        calc ∑ n ∈ Finset.range (k + 1),
              (1 : ℝ) / ((((k - n : ℕ) : ℝ) + 1) * (2 * ((k - n : ℕ) : ℝ) + 1))
            = ∑ n ∈ Finset.range (k + 1), (1 : ℝ) / (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) := by
              simpa using hrefl
          _ ≤ 2 := sum_inv_mul_le_two (k + 1)
      refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
      have he : (2 : ℝ) ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 2) * 2 := by
        rw [← pow_succ, show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by omega]
      rw [he]
      push_cast
      field_simp
      ring

/-! ### L3: real-analyticity of `erf` and of `inverf` on `(-1,1)` -/

-- no-dlmf: analytic support lemma — `erf` is real-analytic, as the real
-- restriction of the entire complex `cerf`
/-- `erf` is real-analytic at every real point. -/
theorem analyticAt_erf (x : ℝ) : AnalyticAt ℝ erf x := by
  have h1 : AnalyticAt ℂ cerf (x : ℂ) :=
    (differentiable_cerf.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have h2 : AnalyticAt ℝ cerf ((x : ℂ)) := h1.restrictScalars
  have h3 : AnalyticAt ℝ (fun t : ℝ => cerf (t : ℂ)) x := by
    have := h2.comp (Complex.ofRealCLM.analyticAt x)
    simpa [Function.comp] using this
  have hre : AnalyticAt ℝ (fun w : ℂ => w.re) (cerf (x : ℂ)) := by
    simpa using Complex.reCLM.analyticAt (cerf (x : ℂ))
  have h4 : AnalyticAt ℝ (fun t : ℝ => (cerf (t : ℂ)).re) x := by
    simpa [Function.comp] using
      AnalyticAt.comp (g := fun w : ℂ => w.re) (f := fun t : ℝ => cerf (t : ℂ)) (x := x) hre h3
  refine h4.congr (Filter.Eventually.of_forall fun t => ?_)
  show (cerf (t : ℂ)).re = erf t
  rw [cerf_ofReal, Complex.ofReal_re]

-- no-dlmf: L3 — real-analyticity of `inverf` on the range `(-1,1)` of `erf`,
-- via the analytic inverse function theorem
/-- **L3.**  `inverf` is real-analytic at every point of `(-1, 1)`. -/
theorem analyticAt_inverf {y : ℝ} (hy : |y| < 1) : AnalyticAt ℝ inverf y := by
  set a : ℝ := inverf y with ha
  have hay : erf a = y := inverf_erf_eq y hy
  have hE : AnalyticAt ℝ erf a := analyticAt_erf a
  have hd : deriv erf a ≠ 0 := by
    rw [(hasDerivAt_erf a).deriv]
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hloc := hE.analyticAt_localInverse hd
  rw [hay] at hloc
  refine hloc.congr ?_
  have hri := HasStrictDerivAt.eventually_right_inverse hE.hasStrictDerivAt hd
  rw [hay] at hri
  have hnear : {z : ℝ | |z| < 1} ∈ nhds y :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hy
  filter_upwards [hri, hnear] with z hz1 hz2
  refine strictMono_erf.injective ?_
  rw [hz1, inverf_erf_eq z hz2]

/-! ### L4: the exp-free ODE `y' · (1 - 2∫₀ᵗ y) = 1` for the series of 7.17.2 -/

-- no-dlmf: support — convergence of the 7.17.2 series inside its interval
/-- If `∑ a_m r^{2m+1}` converges then so does `∑ a_m s^{2m+1}` for `0 ≤ s ≤ r`. -/
theorem summable_inverfCoeff_pow {r s : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r)
    (hr : Summable fun m : ℕ => inverfCoeff m * r ^ (2 * m + 1)) :
    Summable fun m : ℕ => inverfCoeff m * s ^ (2 * m + 1) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (inverfCoeff_nonneg m) (by positivity))
    (fun m => ?_) hr
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsr _) (inverfCoeff_nonneg m)

-- no-dlmf: support — convergence of the termwise-differentiated 7.17.2 series
/-- The differentiated series `∑ (2m+1) a_m s^{2m}` converges for `0 ≤ s < r`
whenever `∑ a_m r^{2m+1}` converges. -/
theorem summable_inverfCoeff_moment {r s : ℝ} (hr0 : 0 < r) (hs0 : 0 ≤ s) (hsr : s < r)
    (hr : Summable fun m : ℕ => inverfCoeff m * r ^ (2 * m + 1)) :
    Summable fun m : ℕ => (2 * (m : ℝ) + 1) * inverfCoeff m * s ^ (2 * m) := by
  set C : ℝ := ∑' m : ℕ, inverfCoeff m * r ^ (2 * m + 1) with hCdef
  have hCm : ∀ m : ℕ, inverfCoeff m * r ^ (2 * m + 1) ≤ C := fun m =>
    hr.le_tsum m fun j _ => mul_nonneg (inverfCoeff_nonneg j) (by positivity)
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (inverfCoeff_nonneg 0) (by positivity)) (hCm 0)
  set q : ℝ := (s / r) ^ 2 with hqdef
  have hsr1 : s / r < 1 := (div_lt_one hr0).mpr hsr
  have hsr0 : 0 ≤ s / r := div_nonneg hs0 hr0.le
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hqdef, sq]
    nlinarith
  have h1 : Summable fun m : ℕ => (m : ℝ) * q ^ m := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rwa [Real.norm_of_nonneg hq0] : ‖q‖ < 1)
    simpa using this
  have h2 : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0 hq1
  have hmaj : Summable fun m : ℕ => (C / r) * ((2 * (m : ℝ) + 1) * q ^ m) := by
    refine (((h1.mul_left 2).add h2).mul_left (C / r)).congr fun m => ?_
    ring
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hmaj
  · have : (0 : ℝ) ≤ s ^ (2 * m) := by rw [pow_mul]; positivity
    have := inverfCoeff_nonneg m
    positivity
  · have hrpow : (0 : ℝ) < r ^ (2 * m + 1) := by positivity
    have ha : inverfCoeff m ≤ C / r ^ (2 * m + 1) :=
      (le_div_iff₀ hrpow).mpr (hCm m)
    have hspow : s ^ (2 * m) = (s / r) ^ (2 * m) * r ^ (2 * m) := by
      rw [div_pow]
      field_simp
    have hq' : q ^ m = (s / r) ^ (2 * m) := by rw [hqdef, ← pow_mul, mul_comm]
    have h2m : (0 : ℝ) ≤ (s / r) ^ (2 * m) := by positivity
    have key : inverfCoeff m * s ^ (2 * m) ≤ (C / r) * (s / r) ^ (2 * m) := by
      calc inverfCoeff m * s ^ (2 * m)
          ≤ (C / r ^ (2 * m + 1)) * s ^ (2 * m) := by
            refine mul_le_mul_of_nonneg_right ha ?_
            rw [pow_mul]; positivity
        _ = (C / r) * (s / r) ^ (2 * m) := by
            rw [hspow]
            field_simp
            ring
    calc (2 * (m : ℝ) + 1) * inverfCoeff m * s ^ (2 * m)
        = (2 * (m : ℝ) + 1) * (inverfCoeff m * s ^ (2 * m)) := by ring
      _ ≤ (2 * (m : ℝ) + 1) * ((C / r) * (s / r) ^ (2 * m)) := by
          refine mul_le_mul_of_nonneg_left key (by positivity)
      _ = (C / r) * ((2 * (m : ℝ) + 1) * q ^ m) := by rw [hq']; ring

set_option maxHeartbeats 1000000 in
-- no-dlmf: L4 (i) — the Cauchy-product form of the recursion 7.17.2_5
/-- **The recursion 7.17.2_5 as a Cauchy product.**  With `α_m = (2m+1) a_m` and
`γ_k = a_k/(k+1)`, the recursion says exactly that

`(∑ α_m uᵐ) · (1 - ∑ γ_k u^{k+1}) = 1`,

i.e. `y' · (1 - 2∫₀ᵗ y) = 1` in the variable `u = t²`. -/
theorem inverfCoeff_cauchy {u : ℝ} (hu0 : 0 ≤ u)
    (hα : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m)
    (hγ : Summable fun k : ℕ => (inverfCoeff k / ((k : ℝ) + 1)) * u ^ (k + 1)) :
    (∑' m : ℕ, (2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m) *
      (1 - ∑' k : ℕ, (inverfCoeff k / ((k : ℝ) + 1)) * u ^ (k + 1)) = 1 := by
  have hαnn : ∀ m : ℕ, 0 ≤ (2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m := fun m => by
    have := inverfCoeff_nonneg m; positivity
  have hγnn : ∀ k : ℕ, 0 ≤ (inverfCoeff k / ((k : ℝ) + 1)) * u ^ (k + 1) := fun k => by
    have := inverfCoeff_nonneg k; positivity
  have hfn : Summable fun m : ℕ => ‖(2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m‖ :=
    hα.congr fun m => (Real.norm_of_nonneg (hαnn m)).symm
  have hgn : Summable fun k : ℕ => ‖(inverfCoeff k / ((k : ℝ) + 1)) * u ^ (k + 1)‖ :=
    hγ.congr fun k => (Real.norm_of_nonneg (hγnn k)).symm
  -- the Cauchy product of the two series
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  -- each antidiagonal block collapses, by 7.17.2_5, to the next coefficient
  have hinner : ∀ N : ℕ,
      ∑ p ∈ Finset.antidiagonal N,
          ((2 * (p.1 : ℝ) + 1) * inverfCoeff p.1 * u ^ p.1) *
            ((inverfCoeff p.2 / ((p.2 : ℝ) + 1)) * u ^ (p.2 + 1))
        = (2 * ((N : ℝ) + 1) + 1) * inverfCoeff (N + 1) * u ^ (N + 1) := by
    intro N
    have hrec := erf_7_17_2_5 N
    have hsplit : ∑ p ∈ Finset.antidiagonal N,
        ((2 * (p.1 : ℝ) + 1) * inverfCoeff p.1 * u ^ p.1) *
          ((inverfCoeff p.2 / ((p.2 : ℝ) + 1)) * u ^ (p.2 + 1))
        = (∑ n ∈ Finset.range (N + 1),
            ((2 * (n : ℝ) + 1) / (((N - n : ℕ) : ℝ) + 1)) * inverfCoeff n *
              inverfCoeff (N - n)) * u ^ (N + 1) := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp hn
      have hpow : u ^ n * u ^ (N - n + 1) = u ^ (N + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hne : ((N - n : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      rw [← hpow]
      field_simp
    rw [hsplit]
    have hcast : ∀ n ∈ Finset.range (N + 1),
        ((2 * (n : ℝ) + 1) / (((N - n : ℕ) : ℝ) + 1)) * inverfCoeff n * inverfCoeff (N - n)
          = ((2 * (n : ℝ) + 1) / ((N : ℝ) - (n : ℝ) + 1)) * inverfCoeff n * inverfCoeff (N - n) := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp hn
      rw [Nat.cast_sub hnN]
    rw [Finset.sum_congr rfl hcast, hrec]
    have h3 : (2 * (N : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  -- assemble: the product of `A` with the integral term is `A - α₀`
  have hzero := hα.tsum_eq_zero_add
  have hprod : (∑' m : ℕ, (2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m) *
      (∑' k : ℕ, (inverfCoeff k / ((k : ℝ) + 1)) * u ^ (k + 1))
      = (∑' m : ℕ, (2 * (m : ℝ) + 1) * inverfCoeff m * u ^ m)
        - (2 * ((0 : ℕ) : ℝ) + 1) * inverfCoeff 0 * u ^ 0 := by
    rw [hcauchy]
    rw [tsum_congr hinner]
    have : ∑' N : ℕ, (2 * ((N : ℝ) + 1) + 1) * inverfCoeff (N + 1) * u ^ (N + 1)
        = ∑' N : ℕ, (2 * (((N + 1 : ℕ)) : ℝ) + 1) * inverfCoeff (N + 1) * u ^ (N + 1) := by
      refine tsum_congr fun N => ?_
      push_cast
      ring
    rw [this, hzero]
    ring
  rw [mul_sub, mul_one, hprod, erf_7_17_2_coeffs.1]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
-- no-dlmf: L4 — the sum of the 7.17.2 series is a right inverse of `erf`
/-- **L4.**  Wherever the Maclaurin series `y(t) = ∑ a_m t^{2m+1}` of DLMF 7.17.2
converges, its sum satisfies `erf (y t) = 2t/√π`.

The proof is the exp-free ODE of DLMF 1.10(vii): the recursion 7.17.2_5 says
exactly that `y' · (1 - 2∫₀ᵗ y) = 1` (a Cauchy product, `inverfCoeff_cauchy`);
differentiating `(1 - 2∫₀ᵗ y)·e^{y²}` then identifies `1 - 2∫₀ᵗ y = e^{-y²}`,
whence `y' = e^{y²}` and `(erf ∘ y)' = 2/√π`. -/
theorem erf_inverfSeries {r t : ℝ} (hr0 : 0 < r)
    (hr : Summable fun m : ℕ => inverfCoeff m * r ^ (2 * m + 1)) (ht : |t| < r) :
    erf (∑' m : ℕ, inverfCoeff m * t ^ (2 * m + 1)) = 2 * t / Real.sqrt Real.pi := by
  obtain ⟨r', htr', hr'r⟩ := exists_between ht
  have hr'0 : 0 < r' := lt_of_le_of_lt (abs_nonneg t) htr'
  have hIopen : IsOpen (Set.Ioo (-r') r') := isOpen_Ioo
  have hIconn : IsPreconnected (Set.Ioo (-r') r') := (convex_Ioo _ _).isPreconnected
  have h0I : (0 : ℝ) ∈ Set.Ioo (-r') r' := Set.mem_Ioo.mpr ⟨by linarith, hr'0⟩
  have htI : t ∈ Set.Ioo (-r') r' := by
    rw [Set.mem_Ioo]
    have h1 := neg_abs_le t
    have h2 := le_abs_self t
    constructor <;> linarith
  have habs : ∀ z ∈ Set.Ioo (-r') r', |z| ≤ r' := by
    intro z hz
    rw [Set.mem_Ioo] at hz
    rw [abs_le]
    exact ⟨hz.1.le, hz.2.le⟩
  have hsq : ∀ z ∈ Set.Ioo (-r') r', z ^ 2 ≤ r' ^ 2 := by
    intro z hz
    have h := abs_le.mp (habs z hz)
    nlinarith [h.1, h.2]
  have hsum1 : Summable fun m : ℕ => inverfCoeff m * r' ^ (2 * m + 1) :=
    summable_inverfCoeff_pow hr'0.le hr'r.le hr
  have hsum2 : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * inverfCoeff m * r' ^ (2 * m) :=
    summable_inverfCoeff_moment hr0 hr'0.le hr'r hr
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun z => ∑' m : ℕ, inverfCoeff m * z ^ (2 * m + 1) :=
    ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → ℝ,
      A = fun z => ∑' m : ℕ, (2 * (m : ℝ) + 1) * inverfCoeff m * z ^ (2 * m) := ⟨_, rfl⟩
  obtain ⟨Bf, hBdef⟩ : ∃ Bf : ℝ → ℝ,
      Bf = fun z => 1 - 2 * ∑' k : ℕ, (inverfCoeff k / (2 * (k : ℝ) + 2)) * z ^ (2 * k + 2) :=
    ⟨_, rfl⟩
  -- (F1) termwise differentiation of the series
  have hGderiv : ∀ z ∈ Set.Ioo (-r') r', HasDerivAt G (A z) z := by
    intro z hz
    simp only [hGdef, hAdef]
    refine hasDerivAt_tsum_of_isPreconnected
      (u := fun m : ℕ => (2 * (m : ℝ) + 1) * inverfCoeff m * r' ^ (2 * m))
      (g := fun (m : ℕ) (w : ℝ) => inverfCoeff m * w ^ (2 * m + 1))
      (g' := fun (m : ℕ) (w : ℝ) => (2 * (m : ℝ) + 1) * inverfCoeff m * w ^ (2 * m))
      hsum2 hIopen hIconn (fun m y _ => ?_) (fun m y hy => ?_) h0I ?_ hz
    · have h := (hasDerivAt_pow (2 * m + 1) y).const_mul (inverfCoeff m)
      convert h using 1
      push_cast
      ring
    · have h2 : (0 : ℝ) ≤ y ^ (2 * m) := by rw [pow_mul]; positivity
      have hcoef : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) * inverfCoeff m :=
        mul_nonneg (by positivity) (inverfCoeff_nonneg m)
      have h1 : y ^ (2 * m) ≤ r' ^ (2 * m) := by
        rw [pow_mul, pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg y) (hsq y hy) m
      rw [Real.norm_of_nonneg (mul_nonneg hcoef h2)]
      exact mul_le_mul_of_nonneg_left h1 hcoef
    · have hzero : (fun m : ℕ => inverfCoeff m * (0 : ℝ) ^ (2 * m + 1)) = fun _ => 0 := by
        funext m
        rw [zero_pow (by omega)]
        ring
      rw [hzero]
      exact summable_zero
  -- (F2) the antiderivative side
  have hSderiv : ∀ z ∈ Set.Ioo (-r') r',
      HasDerivAt (fun w : ℝ => ∑' k : ℕ, (inverfCoeff k / (2 * (k : ℝ) + 2)) * w ^ (2 * k + 2))
        (G z) z := by
    intro z hz
    simp only [hGdef]
    refine hasDerivAt_tsum_of_isPreconnected
      (u := fun k : ℕ => inverfCoeff k * r' ^ (2 * k + 1))
      (g := fun (k : ℕ) (w : ℝ) => (inverfCoeff k / (2 * (k : ℝ) + 2)) * w ^ (2 * k + 2))
      (g' := fun (k : ℕ) (w : ℝ) => inverfCoeff k * w ^ (2 * k + 1))
      hsum1 hIopen hIconn (fun k y _ => ?_) (fun k y hy => ?_) h0I ?_ hz
    · have h := (hasDerivAt_pow (2 * k + 2) y).const_mul (inverfCoeff k / (2 * (k : ℝ) + 2))
      convert h using 1
      have hne : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
    · rw [norm_mul, Real.norm_of_nonneg (inverfCoeff_nonneg k)]
      refine mul_le_mul_of_nonneg_left ?_ (inverfCoeff_nonneg k)
      calc ‖y ^ (2 * k + 1)‖ = |y| ^ (2 * k + 1) := by rw [Real.norm_eq_abs, abs_pow]
        _ ≤ r' ^ (2 * k + 1) := pow_le_pow_left₀ (abs_nonneg y) (habs y hy) _
    · have hzero : (fun k : ℕ => (inverfCoeff k / (2 * (k : ℝ) + 2)) * (0 : ℝ) ^ (2 * k + 2))
          = fun _ => 0 := by
        funext k
        rw [zero_pow (by omega)]
        ring
      rw [hzero]
      exact summable_zero
  have hBderiv : ∀ z ∈ Set.Ioo (-r') r', HasDerivAt Bf (-(2 * G z)) z := by
    intro z hz
    rw [hBdef]
    exact ((hSderiv z hz).const_mul (2 : ℝ)).const_sub (1 : ℝ)
  -- (F3) the ODE, from the recursion 7.17.2_5
  have hAB : ∀ z ∈ Set.Ioo (-r') r', A z * Bf z = 1 := by
    intro z hz
    have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
    have hα : Summable fun m : ℕ => (2 * (m : ℝ) + 1) * inverfCoeff m * (z ^ 2) ^ m := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hsum2
      · have := inverfCoeff_nonneg m; positivity
      · have hcoef : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) * inverfCoeff m :=
          mul_nonneg (by positivity) (inverfCoeff_nonneg m)
        have h1 : (z ^ 2) ^ m ≤ r' ^ (2 * m) := by
          rw [pow_mul]
          exact pow_le_pow_left₀ hz2 (hsq z hz) m
        exact mul_le_mul_of_nonneg_left h1 hcoef
    have hγ : Summable fun k : ℕ => (inverfCoeff k / ((k : ℝ) + 1)) * (z ^ 2) ^ (k + 1) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hsum1.mul_left r')
      · have := inverfCoeff_nonneg k; positivity
      · have h1 : (z ^ 2) ^ (k + 1) ≤ r' ^ (2 * k + 2) := by
          rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
          exact pow_le_pow_left₀ hz2 (hsq z hz) (k + 1)
        have h2 : inverfCoeff k / ((k : ℝ) + 1) ≤ inverfCoeff k := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [inverfCoeff_nonneg k]
        have h3 : (0 : ℝ) ≤ (z ^ 2) ^ (k + 1) := by positivity
        calc (inverfCoeff k / ((k : ℝ) + 1)) * (z ^ 2) ^ (k + 1)
            ≤ inverfCoeff k * (z ^ 2) ^ (k + 1) := mul_le_mul_of_nonneg_right h2 h3
          _ ≤ inverfCoeff k * r' ^ (2 * k + 2) :=
              mul_le_mul_of_nonneg_left h1 (inverfCoeff_nonneg k)
          _ = r' * (inverfCoeff k * r' ^ (2 * k + 1)) := by ring
    have hAeq : A z = ∑' m : ℕ, (2 * (m : ℝ) + 1) * inverfCoeff m * (z ^ 2) ^ m := by
      simp only [hAdef]
      exact tsum_congr fun m => by rw [pow_mul]
    have hBeq : Bf z = 1 - ∑' k : ℕ, (inverfCoeff k / ((k : ℝ) + 1)) * (z ^ 2) ^ (k + 1) := by
      simp only [hBdef]
      congr 1
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      have hne : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
      have hne2 : ((k : ℝ) + 1) ≠ 0 := by positivity
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
      field_simp
    rw [hAeq, hBeq]
    exact inverfCoeff_cauchy hz2 hα hγ
  -- values at the origin
  have hG0 : G 0 = 0 := by
    simp only [hGdef]
    have hzero : (fun m : ℕ => inverfCoeff m * (0 : ℝ) ^ (2 * m + 1)) = fun _ => 0 := by
      funext m
      rw [zero_pow (by omega)]
      ring
    rw [hzero, tsum_zero]
  have hB0 : Bf 0 = 1 := by
    simp only [hBdef]
    have hzero : (fun k : ℕ => (inverfCoeff k / (2 * (k : ℝ) + 2)) * (0 : ℝ) ^ (2 * k + 2))
        = fun _ => 0 := by
      funext k
      rw [zero_pow (by omega)]
      ring
    rw [hzero, tsum_zero]
    ring
  -- (F4) `1 - 2∫₀ᵗ y = e^{-y²}`
  have hphi : ∀ z ∈ Set.Ioo (-r') r',
      HasDerivAt (fun w : ℝ => Bf w * Real.exp ((G w) ^ 2)) 0 z := by
    intro z hz
    have hG := hGderiv z hz
    have hsqd : HasDerivAt (fun w : ℝ => (G w) ^ 2) (2 * G z * A z) z := by
      have h := hG.pow 2
      convert h using 1
      push_cast
      ring
    have hexp : HasDerivAt (fun w : ℝ => Real.exp ((G w) ^ 2))
        (Real.exp ((G z) ^ 2) * (2 * G z * A z)) z := by
      simpa [Function.comp] using (Real.hasDerivAt_exp ((G z) ^ 2)).comp z hsqd
    have h := (hBderiv z hz).mul hexp
    convert h using 1
    have hone := hAB z hz
    linear_combination (-(2 * G z * Real.exp ((G z) ^ 2))) * hone
  have hBexp : ∀ z ∈ Set.Ioo (-r') r', Bf z = Real.exp (-(G z) ^ 2) := by
    intro z hz
    have hc : Bf z * Real.exp ((G z) ^ 2) = 1 := by
      have h := hIopen.is_const_of_deriv_eq_zero hIconn
        (fun w hw => (hphi w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hphi w hw).deriv) hz h0I
      rw [h, hB0, hG0]
      simp
    rw [Real.exp_neg, inv_eq_one_div, eq_div_iff (Real.exp_ne_zero _)]
    exact hc
  -- (F5) `y' = e^{y²}`
  have hAexp : ∀ z ∈ Set.Ioo (-r') r', A z = Real.exp ((G z) ^ 2) := by
    intro z hz
    have h1 := hAB z hz
    rw [hBexp z hz, Real.exp_neg] at h1
    field_simp at h1
    exact h1
  -- (F6) `erf ∘ y` has constant derivative `2/√π`
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpsi : ∀ z ∈ Set.Ioo (-r') r',
      HasDerivAt (fun w : ℝ => erf (G w) - 2 * w / Real.sqrt Real.pi) 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w : ℝ => erf (G w))
        ((2 / Real.sqrt Real.pi * Real.exp (-(G z) ^ 2)) * A z) z := by
      simpa [Function.comp] using (hasDerivAt_erf (G z)).comp z (hGderiv z hz)
    have h2 : HasDerivAt (fun w : ℝ => 2 * w / Real.sqrt Real.pi) (2 / Real.sqrt Real.pi) z := by
      simpa using ((hasDerivAt_id z).const_mul (2 : ℝ)).div_const (Real.sqrt Real.pi)
    have h := h1.sub h2
    convert h using 1
    rw [hAexp z hz, Real.exp_neg]
    field_simp
    ring
  have hfin := hIopen.is_const_of_deriv_eq_zero hIconn
    (fun w hw => (hpsi w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hpsi w hw).deriv) htI h0I
  simp only [hG0, erf_zero, mul_zero, zero_div, sub_zero] at hfin
  simp only [hGdef] at hfin
  linarith [hfin]

/-! ### Pringsheim: the radius of the 7.17.2 series reaches `√π/2` -/

-- no-dlmf: parity bookkeeping — the odd series of 7.17.2 as a full power series
/-- The odd series `∑ a_m z^{2m+1}` written as a full power series with vanishing
even coefficients, on the summability side. -/
theorem summable_inverfCoeff_parity {z : ℝ} :
    (Summable fun n : ℕ => (if n % 2 = 1 then inverfCoeff (n / 2) else 0) * z ^ n)
      ↔ Summable fun m : ℕ => inverfCoeff m * z ^ (2 * m + 1) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := by
    intro a b h
    dsimp only at h
    omega
  have hoff : ∀ n ∉ Set.range (fun m : ℕ => 2 * m + 1),
      (if n % 2 = 1 then inverfCoeff (n / 2) else 0) * z ^ n = 0 := by
    intro n hn
    have hn2 : n % 2 ≠ 1 := by
      intro h
      exact hn ⟨n / 2, by show 2 * (n / 2) + 1 = n; omega⟩
    rw [if_neg hn2, zero_mul]
  have hfg : (fun n : ℕ => (if n % 2 = 1 then inverfCoeff (n / 2) else 0) * z ^ n) ∘
      (fun m : ℕ => 2 * m + 1) = fun m : ℕ => inverfCoeff m * z ^ (2 * m + 1) := by
    funext m
    simp only [Function.comp_apply]
    rw [if_pos (by omega), show (2 * m + 1) / 2 = m by omega]
  rw [← hfg]
  exact (hinj.summable_iff hoff).symm

-- no-dlmf: parity bookkeeping — same identification for the sums
/-- The odd series `∑ a_m z^{2m+1}` written as a full power series with vanishing
even coefficients, on the value side. -/
theorem tsum_inverfCoeff_parity {z : ℝ} :
    (∑' n : ℕ, (if n % 2 = 1 then inverfCoeff (n / 2) else 0) * z ^ n)
      = ∑' m : ℕ, inverfCoeff m * z ^ (2 * m + 1) := by
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := by
    intro a b h
    dsimp only at h
    omega
  have hsupp : Function.support
      (fun n : ℕ => (if n % 2 = 1 then inverfCoeff (n / 2) else 0) * z ^ n)
      ⊆ Set.range (fun m : ℕ => 2 * m + 1) := by
    intro n hn
    by_cases h : n % 2 = 1
    · exact ⟨n / 2, by show 2 * (n / 2) + 1 = n; omega⟩
    · exact absurd (by rw [Function.mem_support] at hn; rw [if_neg h, zero_mul] at hn; exact hn)
        (by simp)
  have hfg : ∀ m : ℕ,
      (if (2 * m + 1) % 2 = 1 then inverfCoeff ((2 * m + 1) / 2) else 0) * z ^ (2 * m + 1)
        = inverfCoeff m * z ^ (2 * m + 1) := by
    intro m
    rw [if_pos (by omega), show (2 * m + 1) / 2 = m by omega]
  rw [← hinj.tsum_eq hsupp]
  exact tsum_congr hfg

set_option maxHeartbeats 800000 in
-- no-dlmf: the radius of the 7.17.2 series, via L1+L2+L3 (Pringsheim)
/-- **Radius of the 7.17.2 series.**  `∑ a_m s^{2m+1}` converges for every
`0 ≤ s < √π/2`.  The crude bound `inverfCoeff_le` gives a positive radius; the
sum inverts `erf` there (`erf_inverfSeries`), so it agrees with the real-analytic
function `t ↦ inverf (2t/√π)` (`analyticAt_inverf`); since the coefficients are
nonnegative, Pringsheim (`FLMF.Methods.summable_mul_pow_of_analyticAt`) then
forbids the radius from stopping before `√π/2`, the point where `2t/√π` leaves
the range of `erf`. -/
theorem summable_inverfCoeff {s : ℝ} (hs : 0 ≤ s) (hsL : s < Real.sqrt Real.pi / 2) :
    Summable fun m : ℕ => inverfCoeff m * s ^ (2 * m + 1) := by
  have hpi0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  rw [← summable_inverfCoeff_parity]
  refine FLMF.Methods.summable_mul_pow_of_analyticAt
    (c := fun n : ℕ => if n % 2 = 1 then inverfCoeff (n / 2) else 0)
    (f := fun z : ℝ => inverf (2 * z / Real.sqrt Real.pi))
    (L := Real.sqrt Real.pi / 2) (fun n => ?_) ⟨1 / 4, by norm_num, by linarith, ?_⟩
    (fun x hx0 hxL => ?_) (fun r z hr0 hrL hrsum hz => ?_) hs hsL
  · -- nonnegativity of the parity-split coefficients
    show (0 : ℝ) ≤ if n % 2 = 1 then inverfCoeff (n / 2) else 0
    by_cases h : n % 2 = 1
    · rw [if_pos h]; exact inverfCoeff_nonneg _
    · rw [if_neg h]
  · -- convergence at `1/4`, from the crude coefficient bound
    rw [summable_inverfCoeff_parity]
    have hgeo : Summable fun m : ℕ => (2 * (1 / 4 : ℝ)) * ((2 * (1 / 4 : ℝ)) ^ 2) ^ m := by
      refine Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    refine Summable.of_nonneg_of_le (fun m => by
      have := inverfCoeff_nonneg m; positivity) (fun m => ?_) hgeo
    have h1 : inverfCoeff m ≤ 2 ^ (2 * m + 1) := by
      refine (inverfCoeff_le m).trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (2 * m + 1)]
    calc inverfCoeff m * (1 / 4 : ℝ) ^ (2 * m + 1)
        ≤ 2 ^ (2 * m + 1) * (1 / 4 : ℝ) ^ (2 * m + 1) := by
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 * (1 / 4 : ℝ)) * ((2 * (1 / 4 : ℝ)) ^ 2) ^ m := by
          rw [← mul_pow, ← pow_mul]
          rw [show 2 * m + 1 = 2 * m + 1 from rfl, pow_succ, pow_mul]
          ring
  · -- `z ↦ inverf (2z/√π)` is analytic on `[0, √π/2)`
    have hlin : AnalyticAt ℝ (fun z : ℝ => 2 * z / Real.sqrt Real.pi) x := by
      have h : (fun z : ℝ => 2 * z / Real.sqrt Real.pi)
          = fun z : ℝ => (2 / Real.sqrt Real.pi) * (id z) := by
        funext z; simp only [id_eq]; ring
      rw [h]
      exact analyticAt_const.mul analyticAt_id
    have harg : |2 * x / Real.sqrt Real.pi| < 1 := by
      rw [abs_lt]
      constructor
      · have : (0 : ℝ) ≤ 2 * x / Real.sqrt Real.pi := by positivity
        linarith
      · rw [div_lt_one hpi0]
        linarith
    have hcomp := AnalyticAt.comp (g := inverf) (f := fun z : ℝ => 2 * z / Real.sqrt Real.pi)
      (x := x) (analyticAt_inverf harg) hlin
    simpa [Function.comp] using hcomp
  · -- the sum represents `inverf (2z/√π)` inside the interval of convergence
    have hr0' : 0 < r := lt_of_le_of_lt (abs_nonneg z) hz
    have hrsum' : Summable fun m : ℕ => inverfCoeff m * r ^ (2 * m + 1) :=
      summable_inverfCoeff_parity.mp hrsum
    have h := erf_inverfSeries hr0' hrsum' hz
    rw [tsum_inverfCoeff_parity]
    show ∑' m : ℕ, inverfCoeff m * z ^ (2 * m + 1) = inverf (2 * z / Real.sqrt Real.pi)
    rw [← h, inverf_erf]

/-- **DLMF 7.17.2.** Maclaurin (power) series of the inverse error function:
with `t = (1/2)·√π·x`, for `|x| < 1`,
`inverf x = ∑_{m=0}^∞ a_m t^{2m+1}`, where the `a_m = inverfCoeff m` are given by
the recursion 7.17.2_5 (e.g. `a₀ = 1`, `a₁ = 1/3`, `a₂ = 7/30`, `a₃ = 127/630`).

DLMF 7.17.2.
DAG: E-7.17.2.
Fidelity: tier1 n/a
Verified: verified (tier2)
-/
theorem erf_7_17_2 {x : ℝ} (hx : |x| < 1) :
    inverf x = ∑' m : ℕ, inverfCoeff m * ((1 / 2) * Real.sqrt Real.pi * x) ^ (2 * m + 1) := by
  have hpi0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set z : ℝ := (1 / 2) * Real.sqrt Real.pi * x with hzdef
  have hz : |z| < Real.sqrt Real.pi / 2 := by
    rw [hzdef, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hpi0.le]
    calc 1 / 2 * Real.sqrt Real.pi * |x|
        < 1 / 2 * Real.sqrt Real.pi * 1 := by
          exact mul_lt_mul_of_pos_left hx (by positivity)
      _ = Real.sqrt Real.pi / 2 := by ring
  obtain ⟨s, hzs, hsL⟩ := exists_between hz
  have hsum := summable_inverfCoeff (le_trans (abs_nonneg z) hzs.le) hsL
  have h := erf_inverfSeries (lt_of_le_of_lt (abs_nonneg z) hzs) hsum hzs
  have h2 : 2 * z / Real.sqrt Real.pi = x := by
    rw [hzdef]
    field_simp
  rw [h2] at h
  rw [← h, inverf_erf]

end FLMF.Error
