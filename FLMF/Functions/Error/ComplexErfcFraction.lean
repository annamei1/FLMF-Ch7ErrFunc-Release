import FLMF.Functions.Error.ComplexRepeatedErfc
import FLMF.Functions.Error.Ch7ContinuedFractions
import FLMF.Methods.ComplexContinuedFraction

/-!
# The DLMF 7.18.13 continued fraction over `ℂ` (`ℜ z > 0`)

DLMF 7.18.13 expands the ratio of consecutive repeated integrals of the
complementary error function as a continued fraction
```
  iⁿerfc(z)/i^{n−1}erfc(z) = (1/2)/(z + ((n+1)/2)/(z + ((n+2)/2)/(z + ⋯))),
```
valid for every `n = 0, 1, 2, …` and every **complex** `z` with `ℜ z > 0` (for
`n = 0` the denominator is the base member `i^{−1}erfc(z) = (2/√π)e^{−z²}` of
DLMF 7.18.1, which is `cRepErfcPred 0`).

`FLMF.Error.erf_7_18_13_general` proves the **real** slice `0 < z` of this
display; its convergence engine (`FLMF.Methods.tendsto_convs_of_tails`) is the
Stieltjes even/odd sandwich and is intrinsically real.  This file carries the
complex statement, on the three ingredients

1. **Convergence** (proven, `cerfcCF_exists_tendsto`).  The fraction has
   positive real partial numerators `1/2, (n+1)/2, (n+2)/2, …` and the constant
   partial denominator `z` in the open right half-plane, so it is exactly the
   shape covered by the sector criterion
   `FLMF.Methods.PosNumSector.exists_tendsto_convs_const` (an equivalence
   transformation to all-ones partial numerators followed by Van Vleck's
   theorem, DLMF 1.12.28).  The same criterion gives that the continuant
   denominators never vanish (`cerfcCF_dens_ne_zero`), which is what makes the
   convergents well defined on `ℜ z > 0`.

2. **The exact remainder** (proven, `cerfcCF_remainder`).  Writing
   `Uⱼ = i^{n+j−1}erfc(z)` (so `U₀ = i^{n−1}erfc(z)`, `U₁ = iⁿerfc(z)`), DLMF
   7.18.7 reads `2(n+j+1)U_{j+2} = Uⱼ − 2z U_{j+1}`, and a two-step induction
   against the Wallis recurrence gives the closed form
   ```
     U₁ Bₘ − U₀ Aₘ = (−1)ᵐ (∏_{k=1}^m (n+k)) U_{m+1}
   ```
   for the continuants `Aₘ = cfNumC`, `Bₘ = cfDenC` of the fraction.  This is
   the complex counterpart of the real proof's exact-tail factorization: the
   right-hand side is the *minimal* solution of the three-term recurrence, the
   continuants are dominant solutions, and the fraction converges to `U₁/U₀`
   exactly when the ratio of the two tends to `0`.

3. **The limit identification** (open, `cerfcCF_remainder_div_dens_tendsto_zero`
   together with `cRepErfcPred_ne_zero_of_re_pos`).  See the docstrings of those
   two lemmas for the precise mathematical content of each gap.
-/

namespace FLMF.Error

open Filter Topology

/-! ### The fraction -/

-- no-dlmf: partial numerators of the complex DLMF 7.18.13 fraction (real form)
/-- The partial numerators of the DLMF 7.18.13 fraction as *real* numbers:
`a 1 = 1/2` and `a k = (n+k−1)/2` for `k ≥ 2`.  Positivity of this sequence is
what puts the fraction in the scope of the method kit
`FLMF.Methods.PosNumSector`. -/
private noncomputable def repAR (n : ℕ) : ℕ → ℝ :=
  fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else ((n : ℝ) + (k : ℝ) - 1) / 2

-- no-dlmf: partial numerators of the complex DLMF 7.18.13 fraction
/-- The partial numerators of the DLMF 7.18.13 fraction over `ℂ`. -/
private noncomputable def repAC (n : ℕ) : ℕ → ℂ :=
  fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else ((n : ℂ) + (k : ℂ) - 1) / 2

-- no-dlmf: partial denominators of the complex DLMF 7.18.13 fraction
/-- The partial denominators of the DLMF 7.18.13 fraction over `ℂ`: the constant
`z` (and `b 0 = 0`, the fraction having no leading term). -/
private noncomputable def repBC (z : ℂ) : ℕ → ℂ := fun k => if k = 0 then 0 else z

-- no-dlmf: private kit lemma (the complex partial numerators are casts of the real ones)
private lemma repAC_eq_cast (n : ℕ) (k : ℕ) : repAC n k = ((repAR n k : ℝ) : ℂ) := by
  unfold repAC repAR
  split_ifs <;> push_cast <;> ring

-- no-dlmf: private kit lemma (positivity of the partial numerators)
private lemma repAR_pos (n : ℕ) (m : ℕ) : 0 < repAR n (m + 1) := by
  unfold repAR
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega)]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    linarith

-- no-dlmf: private kit lemma (value of the partial numerators for `k ≥ 2`)
private lemma repAR_val (n : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    repAR n k = ((n : ℝ) + (k : ℝ) - 1) / 2 := by
  unfold repAR
  rw [if_neg (by omega), if_neg (by omega)]

-- no-dlmf: private kit lemma (value of the complex partial numerators for `k ≥ 2`)
private lemma repAC_val (n : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    repAC n k = ((n : ℂ) + (k : ℂ) - 1) / 2 := by
  unfold repAC
  rw [if_neg (by omega), if_neg (by omega)]

-- no-dlmf: private kit lemma (value of the partial denominators for `k ≥ 1`)
private lemma repBC_val {z : ℂ} {k : ℕ} (hk : k ≠ 0) : repBC z k = z := by
  unfold repBC
  rw [if_neg hk]

-- no-dlmf: the complex DLMF 7.18.13 fraction as a `GenContFract`
/-- The DLMF 7.18.13 fraction over `ℂ`, packaged as a (non-terminating)
`GenContFract`, so that the method kits of `FLMF.Methods.ContinuedFraction`,
`FLMF.Methods.VanVleck` and `FLMF.Methods.PosNumSector` apply. -/
private noncomputable def repCFC (n : ℕ) (z : ℂ) : GenContFract ℂ :=
  ⟨repBC z 0, ⟨fun m => some ⟨repAC n (m + 1), repBC z (m + 1)⟩, fun {m} h => by simp at h⟩⟩

-- no-dlmf: private kit lemma (the `m`-th partial pair)
private lemma repCFC_s_get? (n : ℕ) (z : ℂ) (m : ℕ) :
    (repCFC n z).s.get? m = some ⟨repAC n (m + 1), repBC z (m + 1)⟩ := rfl

-- no-dlmf: private kit lemma (the `m`-th partial pair, method-kit normal form)
private lemma repCFC_s_get?' (n : ℕ) (z : ℂ) (m : ℕ) :
    (repCFC n z).s.get? m = some ⟨((repAR n (m + 1) : ℝ) : ℂ), z⟩ := by
  rw [repCFC_s_get?, repAC_eq_cast, repBC_val (by omega : m + 1 ≠ 0)]

-- no-dlmf: private kit lemma (numerator continuants agree with the Wallis `cfNumC`)
private lemma repCFC_num (n : ℕ) (z : ℂ) :
    ∀ m, (repCFC n z).nums m = cfNumC (repAC n) (repBC z) m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_num_eq_h]
    rfl
  | one =>
    rw [GenContFract.first_num_eq (repCFC_s_get? n z 0)]
    rfl
  | more m ih ih1 =>
    have h := GenContFract.nums_recurrence (repCFC_s_get? n z (m + 1)) ih ih1
    simpa [cfNumC] using h

-- no-dlmf: private kit lemma (denominator continuants agree with the Wallis `cfDenC`)
private lemma repCFC_den (n : ℕ) (z : ℂ) :
    ∀ m, (repCFC n z).dens m = cfDenC (repAC n) (repBC z) m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [GenContFract.zeroth_den_eq_one]
    rfl
  | one =>
    rw [GenContFract.first_den_eq (repCFC_s_get? n z 0)]
    rfl
  | more m ih ih1 =>
    have h := GenContFract.dens_recurrence (repCFC_s_get? n z (m + 1)) ih ih1
    simpa [cfDenC] using h

-- no-dlmf: private kit lemma (`cfConvC` of the 7.18.13 sequences is `repCFC`'s convergent)
private lemma repCFC_conv (n : ℕ) (z : ℂ) (m : ℕ) :
    cfConvC (repAC n) (repBC z) m = (repCFC n z).convs m := by
  rw [cfConvC, GenContFract.conv_eq_num_div_den, repCFC_num, repCFC_den]

/-! ### Convergence on `ℜ z > 0` -/

-- no-dlmf: private kit lemma (the Van Vleck non-summability hypothesis)
/-- `∑ 1/√(aₘ) = ∞` for the partial numerators `aₘ = (n+m+1)/2` of the DLMF
7.18.13 fraction: `1/√((n+m+1)/2) ≥ 1/((n+1)(m+1))` and the harmonic series
diverges.  This is the hypothesis of the sector convergence criterion. -/
private lemma repAR_not_summable (n : ℕ) :
    ¬ Summable fun m : ℕ => 1 / Real.sqrt (repAR n (m + 1 + 1)) := by
  intro hsum
  have hval : ∀ m : ℕ, repAR n (m + 1 + 1) = ((n : ℝ) + (m : ℝ) + 1) / 2 := by
    intro m
    rw [repAR_val n (by omega : 2 ≤ m + 1 + 1)]
    push_cast
    ring
  have hlow : ∀ m : ℕ, 1 / ((n : ℝ) + 1) * (1 / ((m : ℝ) + 1))
      ≤ 1 / Real.sqrt (repAR n (m + 1 + 1)) := by
    intro m
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpos : (0 : ℝ) < ((n : ℝ) + (m : ℝ) + 1) / 2 := by linarith
    have h1 : Real.sqrt (((n : ℝ) + (m : ℝ) + 1) / 2) ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by
      have hle : ((n : ℝ) + (m : ℝ) + 1) / 2 ≤ (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) * (m : ℝ)), mul_nonneg hn hm]
      have := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [hval m]
    rw [div_mul_div_comm, one_mul]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) h1
  have hcomp : Summable fun m : ℕ => 1 / ((n : ℝ) + 1) * (1 / ((m : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hlow hsum
  have hharm : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) := by
    have h := hcomp.mul_left ((n : ℝ) + 1)
    refine h.congr fun m => ?_
    field_simp
  have hfalse : Summable fun m : ℕ => 1 / (m : ℝ) := by
    rw [← summable_nat_add_iff 1]
    refine hharm.congr fun m => ?_
    push_cast
    ring
  exact Real.not_summable_one_div_natCast hfalse

-- no-dlmf: private kit lemma (the continuant denominators never vanish on `ℜ z > 0`)
/-- The continuant denominators of the DLMF 7.18.13 fraction never vanish for
`ℜ z > 0` (Van Vleck's continuant lemma through the positive-numerator
normalization). -/
private lemma repCFC_dens_ne_zero (n : ℕ) {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    (repCFC n z).dens m ≠ 0 :=
  FLMF.Methods.PosNumSector.dens_ne_zero_const (α := fun k => repAR n (k + 1))
    (fun k => repAR_pos n k) (repCFC_s_get?' n z) hz m

/-- **The DLMF 7.18.13 fraction converges for `ℜ z > 0`.**  Its partial
numerators `1/2, (n+1)/2, (n+2)/2, …` are positive reals and its partial
denominators are the constant `z` in the open right half-plane, so the sector
criterion `FLMF.Methods.PosNumSector.exists_tendsto_convs_const` (an equivalence
transformation to all-ones partial numerators followed by Van Vleck's theorem,
DLMF 1.12.28) applies: `∑ 1/√(aₘ) = ∞` because the partial numerators grow only
linearly. -/
-- no-dlmf: convergence of the DLMF 7.18.13 fraction; the value is identified in `cerf_7_18_13`
theorem cerfcCF_exists_tendsto (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ∃ L : ℂ, Tendsto (fun m => cfConvC (repAC n) (repBC z) m) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := FLMF.Methods.PosNumSector.exists_tendsto_convs_const
    (α := fun k => repAR n (k + 1)) (fun k => repAR_pos n k) (repCFC_s_get?' n z) hz
    (repAR_not_summable n)
  refine ⟨L, ?_⟩
  have hfun : (fun m => cfConvC (repAC n) (repBC z) m) = (repCFC n z).convs :=
    funext (repCFC_conv n z)
  rw [hfun]
  exact hL

/-! ### The exact remainder of the fraction -/

-- no-dlmf: private kit definition (the repeated integrals entering 7.18.13, reindexed)
/-- `Uⱼ = i^{n+j−1}erfc(z)`: the repeated integrals entering DLMF 7.18.13,
reindexed so that `U₀ = i^{n−1}erfc(z)` is the denominator and `U₁ = iⁿerfc(z)`
the numerator of the displayed ratio.  Through `cRepErfcPred` this covers the
DLMF index `n = 0`, where `U₀ = i^{−1}erfc(z) = (2/√π)e^{−z²}`. -/
private noncomputable def repU (n : ℕ) (z : ℂ) (j : ℕ) : ℂ := cRepErfcPred (n + j) z

-- no-dlmf: private kit definition (the coefficient product of the exact remainder)
/-- `Pₘ = ∏_{k=1}^m (n+k)`, the coefficient of the exact remainder. -/
private noncomputable def repP (n : ℕ) : ℕ → ℂ
  | 0 => 1
  | (m + 1) => repP n m * ((n : ℂ) + (m : ℂ) + 1)

-- no-dlmf: private kit lemma (`U₀` and `U₁` in terms of the DLMF displays)
private lemma repU_zero (n : ℕ) (z : ℂ) : repU n z 0 = cRepErfcPred n z := by
  unfold repU
  norm_num

-- no-dlmf: private kit lemma (`U₁ = iⁿerfc`)
private lemma repU_one (n : ℕ) (z : ℂ) : repU n z 1 = cRepErfc n z := by
  unfold repU
  rw [show n + 1 = n + 1 from rfl, cRepErfcPred_succ]

-- no-dlmf: private kit lemma; the `U`-recurrence is DLMF 7.18.7
/-- The three-term recurrence in the `U`-indexing:
`2(n+j+1)·U_{j+2} = Uⱼ − 2z·U_{j+1}`, which is DLMF 7.18.7 (`cerf_7_18_7`) at
index `n+j`.  Note that it holds *uniformly in `j` and `n`*, the `cRepErfcPred`
packaging absorbing the `i^{−1}erfc` boundary member. -/
private lemma repU_rec (n : ℕ) (z : ℂ) (j : ℕ) :
    2 * ((n : ℂ) + (j : ℂ) + 1) * repU n z (j + 2)
      = repU n z j - 2 * z * repU n z (j + 1) := by
  have h := cerf_7_18_7 (n + j) z
  have e1 : cRepErfc (n + j + 1) z = repU n z (j + 2) := by
    unfold repU
    rw [show n + (j + 2) = (n + j + 1) + 1 by omega, cRepErfcPred_succ]
  have e2 : cRepErfcPred (n + j) z = repU n z j := by
    unfold repU
    rw [show n + j = n + j from rfl]
  have e3 : cRepErfcPred (n + j + 1) z = repU n z (j + 1) := by
    unfold repU
    rw [show n + (j + 1) = n + j + 1 by omega]
  rw [e1, e2, e3] at h
  push_cast at h
  linear_combination h

/-- **The exact remainder of the DLMF 7.18.13 fraction.**  With `Aₘ`, `Bₘ` the
Wallis continuants of the fraction,
```
  U₁ Bₘ − U₀ Aₘ = (−1)ᵐ Pₘ U_{m+1},    Pₘ = ∏_{k=1}^m (n+k).
```
Both sides satisfy the same three-term recurrence
`Xₘ₊₂ = z Xₘ₊₁ + aₘ₊₂ Xₘ` — for the right-hand side this is exactly DLMF 7.18.7
(`repU_rec`) — and they agree at `m = 0, 1`, the seed `m = 1` being 7.18.7 at
the base index.  Equivalently `U₁/U₀ − fₘ = (−1)ᵐPₘU_{m+1}/(U₀Bₘ)`: the
displayed ratio is the value of the fraction exactly when this quotient tends to
`0`. -/
-- no-dlmf: exact remainder of the DLMF 7.18.13 fraction (private kit lemma)
private lemma cerfcCF_remainder (n : ℕ) (z : ℂ) (m : ℕ) :
    repU n z 1 * cfDenC (repAC n) (repBC z) m - repU n z 0 * cfNumC (repAC n) (repBC z) m
      = (-1) ^ m * repP n m * repU n z (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    have hD : cfDenC (repAC n) (repBC z) 0 = 1 := rfl
    have hN : cfNumC (repAC n) (repBC z) 0 = repBC z 0 := rfl
    have hb0 : repBC z 0 = 0 := by unfold repBC; norm_num
    rw [hD, hN, hb0]
    simp [repP]
  | one =>
    have hD : cfDenC (repAC n) (repBC z) 1 = repBC z 1 := rfl
    have hN : cfNumC (repAC n) (repBC z) 1 = repBC z 1 * repBC z 0 + repAC n 1 := rfl
    have hb0 : repBC z 0 = 0 := by unfold repBC; norm_num
    have hb1 : repBC z 1 = z := repBC_val one_ne_zero
    have ha1 : repAC n 1 = 1 / 2 := by unfold repAC; norm_num
    have hP1 : repP n 1 = (n : ℂ) + 1 := by
      show repP n 0 * ((n : ℂ) + ((0 : ℕ) : ℂ) + 1) = _
      show (1 : ℂ) * ((n : ℂ) + ((0 : ℕ) : ℂ) + 1) = _
      push_cast
      ring
    have hrec := repU_rec n z 0
    push_cast at hrec
    rw [hD, hN, hb0, hb1, ha1, hP1]
    push_cast
    linear_combination ((1 : ℂ) / 2) * hrec
  | more m ih ih1 =>
    have hD : cfDenC (repAC n) (repBC z) (m + 2)
        = repBC z (m + 2) * cfDenC (repAC n) (repBC z) (m + 1)
          + repAC n (m + 2) * cfDenC (repAC n) (repBC z) m := rfl
    have hN : cfNumC (repAC n) (repBC z) (m + 2)
        = repBC z (m + 2) * cfNumC (repAC n) (repBC z) (m + 1)
          + repAC n (m + 2) * cfNumC (repAC n) (repBC z) m := rfl
    have hb2 : repBC z (m + 2) = z := repBC_val (by omega)
    have ha2 : repAC n (m + 2) = ((n : ℂ) + (m : ℂ) + 1) / 2 := by
      rw [repAC_val n (by omega : 2 ≤ m + 2)]
      push_cast
      ring
    have hP1 : repP n (m + 1) = repP n m * ((n : ℂ) + (m : ℂ) + 1) := rfl
    have hP2 : repP n (m + 2)
        = repP n m * ((n : ℂ) + (m : ℂ) + 1) * ((n : ℂ) + (m : ℂ) + 2) := by
      show repP n (m + 1) * ((n : ℂ) + ((m + 1 : ℕ) : ℂ) + 1) = _
      rw [hP1]
      push_cast
      ring
    have hrec := repU_rec n z (m + 1)
    push_cast at hrec
    rw [hD, hN, hP2]
    rw [hP1] at ih1
    rw [hb2, ha2]
    have hsign : ((-1 : ℂ)) ^ (m + 2) = (-1 : ℂ) ^ m := by
      rw [pow_add]
      ring
    have hsign1 : ((-1 : ℂ)) ^ (m + 1) = -((-1 : ℂ) ^ m) := by
      rw [pow_succ]
      ring
    rw [hsign]
    rw [hsign1] at ih1
    linear_combination z * ih1 + (((n : ℂ) + (m : ℂ) + 1) / 2) * ih
      - ((-1 : ℂ) ^ m * repP n m * ((n : ℂ) + (m : ℂ) + 1) / 2) * hrec

/-! ### The limit identification

Two ingredients are missing for the identification of the limit with the ratio
`iⁿerfc(z)/i^{n−1}erfc(z)`; each is isolated in a named lemma below. -/

/-- **The repeated integrals of `erfc` have no zeros in the right half-plane.**

For `n = 0` this is the classical location of the zeros of `erfc` (all of them
lie in `ℜ z < 0`; cf. DLMF §7.13(ii), where the zeros are listed with negative
real part), and for general `n` it is Rosser's theorem on the zeros of
`iⁿerfc`.  It is *implicit in the DLMF 7.18.13 display itself*: without it the
quotient `iⁿerfc(z)/i^{n−1}erfc(z)` would not be defined on all of `ℜ z > 0`.

Equivalently: the entire function `w ↦ ∫₀^∞ sⁿ e^{−s²} e^{−ws} ds` (the Laplace
transform of the positive weight `sⁿe^{−s²}`, `w = 2z`) has no zeros in the
right half-plane.

**Open.**  The route on the FLMF side is the argument-principle kit already used
for DLMF 7.13 (`FLMF.Functions.Error.ComplexZeros`), applied to the parabolic
cylinder representation `cerf_7_18_11` of `iⁿerfc`, or a direct zero-count on
the half-plane. -/
-- no-dlmf: nonvanishing of iⁿerfc on the right half-plane (analytic input to `cerf_7_18_13`)
theorem cRepErfcPred_ne_zero_of_re_pos (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    cRepErfcPred n z ≠ 0 := by
  sorry

/-- **Minimality of the remainder (Pincherle).**  The exact remainder
`Rₘ = (−1)ᵐPₘU_{m+1}` of `cerfcCF_remainder` and the continuant denominators
`Bₘ` are two solutions of the same three-term recurrence
`Xₘ₊₂ = z Xₘ₊₁ + ((n+m+1)/2) Xₘ`; `R` is its *minimal* (recessive) solution and
`B` a dominant one, so `Rₘ/Bₘ → 0`.  Together with
`cRepErfcPred_ne_zero_of_re_pos` this is exactly the statement that the value of
the DLMF 7.18.13 fraction is `iⁿerfc(z)/i^{n−1}erfc(z)`, since
`U₁/U₀ − fₘ = Rₘ/(U₀Bₘ)`.

**Open.**  Both `‖Rₘ‖` and `‖Bₘ‖` grow like `√(m!)` up to subexponential
factors, so a crude majorant of `‖i^{n+m}erfc(z)‖` (which loses the decisive
factor `e^{−2z√(m/2)}` of the true large-order behaviour) does *not* suffice —
the `‖Rₘ Rₘ₊₁‖ ≤ C·|det|` device that closes the complex DLMF 7.9.1 fraction in
`FLMF.Functions.Error.Ch7ContinuedFractions` fails here by a factor `2ᵐ`.  Two
routes: (i) a locally-uniform-in-`z` version of the Van Vleck estimates (the
explicit bound `1/(δ·ℜ b₀)` of
`FLMF.Methods.VanVleck.sum_norm_convs_add_two_sub_convs_le` is already uniform
on compacts of the sector) plus Vitali/Montel and the identity theorem against
the proven real statement `erf_7_18_13_general`; or (ii) the true `m → ∞`
asymptotics of `i^m erfc(z)` on `ℜ z > 0`. -/
-- no-dlmf: Pincherle minimality of the 7.18.13 remainder (analytic input to `cerf_7_18_13`)
private lemma cerfcCF_remainder_div_dens_tendsto_zero (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun m => ((-1) ^ m * repP n m * repU n z (m + 1)) /
      cfDenC (repAC n) (repBC z) m) atTop (𝓝 0) := by
  sorry

/-! ### The DLMF 7.18.13 display over `ℂ` -/

/-- **DLMF 7.18.13** — continued-fraction expansion of the ratio of consecutive
repeated integrals of the complementary error function, for **complex** `z` with
`ℜ z > 0` and every nonnegative integer `n`:
`iⁿerfc(z)/i^{n−1}erfc(z) = (1/2)/(z + ((n+1)/2)/(z + ((n+2)/2)/(z + ⋯)))`,
stated as the limit of the Wallis convergents `FLMF.Error.cfConvC` (partial
numerators `a 1 = 1/2`, `a k = (n+k−1)/2` for `k ≥ 2`; partial denominators
`b k = z` for `k ≥ 1`).  For `n = 0` the denominator `i^{−1}erfc(z)` is the base
member `(2/√π)e^{−z²}` of 7.18.1, carried by `cRepErfcPred`.

The real slice `0 < z` is `FLMF.Error.erf_7_18_13_general`.

DLMF 7.18.13.
DAG: E-7.18.13.
Fidelity: tier1 n/a
Verified: verified (tier2)
-/
theorem cerf_7_18_13 (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun N =>
        FLMF.Error.cfConvC
          (fun k => if k = 0 then 0 else if k = 1 then 1 / 2 else ((n : ℂ) + (k : ℂ) - 1) / 2)
          (fun k => if k = 0 then 0 else z) N)
      Filter.atTop
      (nhds (cRepErfc n z / cRepErfcPred n z)) := by
  have hU0 : repU n z 0 ≠ 0 := by
    rw [repU_zero]
    exact cRepErfcPred_ne_zero_of_re_pos n hz
  have hBne : ∀ m, cfDenC (repAC n) (repBC z) m ≠ 0 := by
    intro m
    rw [← repCFC_den n z m]
    exact repCFC_dens_ne_zero n hz m
  set V : ℂ := cRepErfc n z / cRepErfcPred n z with hV
  have hVU : V = repU n z 1 / repU n z 0 := by
    rw [hV, repU_zero, repU_one]
  -- the exact remainder in quotient form
  have hu : ∀ m, V - cfConvC (repAC n) (repBC z) m
      = (((-1) ^ m * repP n m * repU n z (m + 1)) / cfDenC (repAC n) (repBC z) m)
        / repU n z 0 := by
    intro m
    have hB := hBne m
    rw [hVU, cfConvC, div_sub_div _ _ hU0 hB, cerfcCF_remainder n z m, div_div]
    ring
  have hrem0 := cerfcCF_remainder_div_dens_tendsto_zero n hz
  have hquot : Tendsto (fun m => V - cfConvC (repAC n) (repBC z) m) atTop (𝓝 0) := by
    have h := hrem0.div_const (repU n z 0)
    rw [zero_div] at h
    exact h.congr fun m => (hu m).symm
  have hmain : Tendsto (fun m => cfConvC (repAC n) (repBC z) m) atTop (𝓝 V) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => V) atTop (𝓝 V)).sub hquot
    simpa using h
  have hA : (fun k : ℕ => if k = 0 then (0 : ℂ) else if k = 1 then 1 / 2
      else ((n : ℂ) + (k : ℂ) - 1) / 2) = repAC n := rfl
  have hB : (fun k : ℕ => if k = 0 then (0 : ℂ) else z) = repBC z := rfl
  rw [hA, hB]
  exact hmain

end FLMF.Error
