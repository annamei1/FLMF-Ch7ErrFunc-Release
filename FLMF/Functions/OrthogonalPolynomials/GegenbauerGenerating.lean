/-
Copyright (c) 2026 FLMF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FLMF.Functions.OrthogonalPolynomials.LaguerreGeneratingFun
import FLMF.Functions.OrthogonalPolynomials.Gegenbauer
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Generating function of the Gegenbauer polynomials (DLMF 18.12.4)

The ultraspherical generating function
`(1 - 2xz + z²)^{-λ} = Σ_{n≥0} C_n^{(λ)}(x) zⁿ` (`|z| < 1`).

The proof is a consumer of existing infrastructure — no new method node is
required (see the route in the docstring).
-/

open scoped Nat
open Finset

namespace Complex

theorem hasSum_ascPochhammer_div_factorial_mul_cpow (β : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ ↦ (ascPochhammer ℂ n).eval (β : ℂ) / (n.factorial : ℂ) * t ^ n)
      ((1 - t) ^ (-(β : ℂ))) := by
  have hball : (-t) ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    simpa using ht
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := -(β : ℂ))).hasSum hball
  have hval : (fun n : ℕ ↦ binomialSeries ℂ (-(β : ℂ)) n fun _ : Fin n ↦ (-t : ℂ))
      = fun n : ℕ ↦ (ascPochhammer ℂ n).eval (β : ℂ) / (n.factorial : ℂ) * t ^ n := by
    funext n
    rw [binomialSeries_apply]
    simp only [List.ofFn_const, List.prod_replicate, smul_eq_mul]
    have hneg := congrArg (algebraMap ℝ ℂ) (Ring.choose_neg_eq β n)
    simp only [map_div₀, map_mul, map_pow, map_neg, map_one, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_natCast] at hneg
    rw [Ring.map_choose] at hneg
    have hneg' : Ring.choose (-(β : ℂ)) n =
        (-1 : ℂ) ^ n * (algebraMap ℝ ℂ) ((ascPochhammer ℝ n).eval β) / (n.factorial : ℂ) := by
      simpa using hneg
    rw [hneg']
    rw [ascPochhammer_eval₂ (algebraMap ℝ ℂ)]
    change (-1 : ℂ) ^ n * (algebraMap ℝ ℂ) ((ascPochhammer ℝ n).eval β) / (n.factorial : ℂ) * (-t) ^ n =
      (ascPochhammer ℝ n).eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) β) / (n.factorial : ℂ) * t ^ n
    rw [Polynomial.eval₂_at_apply]
    ring_nf
    rw [show n * 2 = 2 * n by omega, pow_mul]
    norm_num
  rw [hval] at h
  simpa [sub_eq_add_neg] using h

end Complex

namespace FLMF.Gegenbauer

noncomputable def qcoef (lam : ℝ) (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (ascPochhammer ℝ (n + k)).eval (2 * lam) /
    (((n - k).factorial : ℝ) * (ascPochhammer ℝ k).eval (lam + 1 / 2) * k.factorial)

lemma neg_poch (n k : ℕ) :
    (ascPochhammer ℝ k).eval (-(n : ℝ)) =
      (-1) ^ k * (k.factorial : ℝ) * (n.choose k : ℝ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer]
  have hk : (n.choose k : ℝ) = (descPochhammer ℝ k).eval (n : ℝ) / (k ! : ℝ) :=
    Nat.cast_choose_eq_descPochhammer_div (K := ℝ) n k
  have hfk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [hk]
  field_simp

lemma gegenbauer_eq_qcoef (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    gegenbauer lam n x =
      ∑ k ∈ Finset.range (n + 1), qcoef lam n k * ((1 - x) / 2) ^ k := by
  rw [gegenbauer]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have hfn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hfk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hfnk : ((n-k).factorial : ℝ) ≠ 0 := by exact_mod_cast (n-k).factorial_ne_zero
  have hden : (ascPochhammer ℝ k).eval (lam + 1 / 2) ≠ 0 :=
    (ascPochhammer_pos k (lam + 1 / 2) (by linarith)).ne'
  have hden' : (ascPochhammer ℝ k).eval ((2 * lam + 1) / 2) ≠ 0 := by
    convert hden using 2 <;> ring
  have hchoose := Nat.choose_mul_factorial_mul_factorial hkn
  have hsplit : (ascPochhammer ℝ n).eval (2 * lam) *
      (ascPochhammer ℝ k).eval ((n : ℝ) + 2 * lam) =
      (ascPochhammer ℝ (n + k)).eval (2 * lam) := by
    have h := congrArg (fun p : Polynomial ℝ => p.eval (2 * lam)) (ascPochhammer_mul (S := ℝ) n k)
    simpa [Polynomial.eval_mul, Polynomial.eval_comp, add_comm] using h
  rw [neg_poch]
  simp only [qcoef]
  push_cast at hchoose
  field_simp [hfn, hfk, hfnk, hden, hden']
  rw [← hsplit]
  rw [← hchoose]
  push_cast
  ring

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

lemma qcoef_recurrence_zero (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ((n : ℝ) + 2) * qcoef lam (n + 2) 0 =
      2 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) 0 -
        ((n : ℝ) + 2 * lam) * qcoef lam n 0 := by
  simp only [qcoef, pow_zero, Nat.add_zero, Nat.sub_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one]
  have h0 : (ascPochhammer ℝ n).eval (2 * lam) ≠ 0 :=
    (ascPochhammer_pos n (2 * lam) (by positivity)).ne'
  rw [show n + 1 = n + 1 by rfl, ascPochhammer_succ_eval,
    show n + 2 = (n + 1) + 1 by omega, ascPochhammer_succ_eval,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma qcoef_recurrence_top (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ((n : ℝ) + 2) * qcoef lam (n + 2) (n + 2) =
      -4 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) (n + 1) := by
  simp only [qcoef, Nat.add_sub_cancel, Nat.factorial_zero, Nat.cast_one, one_mul]
  have hA : (ascPochhammer ℝ (n + 1)).eval (lam + 1 / 2) ≠ 0 :=
    (ascPochhammer_pos (n + 1) (lam + 1 / 2) (by linarith)).ne'
  have hP : (ascPochhammer ℝ (2 * (n + 1))).eval (2 * lam) ≠ 0 :=
    (ascPochhammer_pos (2 * (n + 1)) (2 * lam) (by positivity)).ne'
  rw [show (n + 2) + (n + 2) = (2 * (n + 1)) + 2 by omega,
    show (n + 1) + (n + 1) = 2 * (n + 1) by omega,
    show n + 2 = (n + 1) + 1 by omega,
    ascPochhammer_succ_eval, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp
  ring_nf

lemma qcoef_recurrence_inner (lam : ℝ) (hlam : 0 < lam) (n k : ℕ) (hkn : k < n) :
    ((n : ℝ) + 2) * qcoef lam (n + 2) (k + 1) =
      2 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) (k + 1) -
        4 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) k -
          ((n : ℝ) + 2 * lam) * qcoef lam n (k + 1) := by
  simp only [qcoef]
  let P := (ascPochhammer ℝ (n + k + 1)).eval (2 * lam)
  let A := (ascPochhammer ℝ k).eval (lam + 1 / 2)
  have hP : P ≠ 0 := (ascPochhammer_pos (n + k + 1) (2 * lam) (by positivity)).ne'
  have hA : A ≠ 0 := (ascPochhammer_pos k (lam + 1 / 2) (by linarith)).ne'
  have hp1 : (ascPochhammer ℝ (n + k + 2)).eval (2 * lam) =
      (2 * lam + (n + k + 1 : ℕ)) * P := by
    rw [show n + k + 2 = (n + k + 1) + 1 by omega, ascPochhammer_succ_eval]
    simp only [P]
    ring
  have hp2 : (ascPochhammer ℝ (n + k + 3)).eval (2 * lam) =
      (2 * lam + (n + k + 2 : ℕ)) * (2 * lam + (n + k + 1 : ℕ)) * P := by
    rw [show n + k + 3 = (n + k + 2) + 1 by omega, ascPochhammer_succ_eval, hp1]
    ring
  have ha1 : (ascPochhammer ℝ (k + 1)).eval (lam + 1 / 2) =
      (lam + 1 / 2 + k) * A := by
    rw [ascPochhammer_succ_eval]
    simp only [A]
    ring
  have hf1 : ((n + 1 - k).factorial : ℝ) = (n + 1 - k : ℕ) * (n - k).factorial := by
    rw [show n + 1 - k = (n - k) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have hf2 : ((n - k).factorial : ℝ) = (n - k : ℕ) * (n - k - 1).factorial := by
    rw [show n - k = (n - k - 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [show (n + 2) + (k + 1) = n + k + 3 by omega,
    show (n + 1) + (k + 1) = n + k + 2 by omega,
    show (n + 1) + k = n + k + 1 by omega,
    show n + (k + 1) = n + k + 1 by omega,
    show n + 2 - (k + 1) = n + 1 - k by omega,
    show n + 1 - (k + 1) = n - k by omega,
    show n - (k + 1) = n - k - 1 by omega,
    hp2, hp1, ha1, hf1, hf2, Nat.factorial_succ k]
  have hc1 : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by push_cast [Nat.cast_sub (by omega : k ≤ n + 1)]; ring
  have hc2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by push_cast [Nat.cast_sub (by omega : k ≤ n)]; ring
  rw [hc1, hc2]
  push_cast
  simp only [P, A] at hP hA ⊢
  have hkr : (k : ℝ) < n := by exact_mod_cast hkn
  have hnk0 : (n : ℝ) - k ≠ 0 := by linarith
  have hn1k0 : (n : ℝ) + 1 - k ≠ 0 := by linarith
  have hAk0 : lam + 1 / 2 + (k : ℝ) ≠ 0 := by positivity
  have hk10 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hfac : ((n - k - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (n-k-1).factorial_ne_zero
  have hkfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp [hP, hA, hnk0, hn1k0, hAk0, hk10, hfac, hkfac]
  ring

lemma qcoef_recurrence_edge (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ((n : ℝ) + 2) * qcoef lam (n + 2) (n + 1) =
      2 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) (n + 1) -
        4 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) n := by
  simp only [qcoef]
  let P := (ascPochhammer ℝ (2 * n + 1)).eval (2 * lam)
  let A := (ascPochhammer ℝ n).eval (lam + 1 / 2)
  have hP : P ≠ 0 := (ascPochhammer_pos (2 * n + 1) (2 * lam) (by positivity)).ne'
  have hA : A ≠ 0 := (ascPochhammer_pos n (lam + 1 / 2) (by linarith)).ne'
  have hp1 : (ascPochhammer ℝ (2 * n + 2)).eval (2 * lam) =
      (2 * lam + (2 * n + 1 : ℕ)) * P := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, ascPochhammer_succ_eval]
    simp only [P]
    ring
  have hp2 : (ascPochhammer ℝ (2 * n + 3)).eval (2 * lam) =
      (2 * lam + (2 * n + 2 : ℕ)) * (2 * lam + (2 * n + 1 : ℕ)) * P := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, ascPochhammer_succ_eval, hp1]
    ring
  have ha1 : (ascPochhammer ℝ (n + 1)).eval (lam + 1 / 2) =
      (lam + 1 / 2 + n) * A := by
    rw [ascPochhammer_succ_eval]
    simp only [A]
    ring
  rw [show (n + 2) + (n + 1) = 2 * n + 3 by omega,
    show (n + 1) + (n + 1) = 2 * n + 2 by omega,
    show (n + 1) + n = 2 * n + 1 by omega,
    show n + 2 - (n + 1) = 1 by omega,
    show n + 1 - (n + 1) = 0 by omega,
    show n + 1 - n = 1 by omega,
    hp2, hp1, ha1, Nat.factorial_succ n]
  push_cast
  simp only [P, A] at hP hA ⊢
  have hAn : lam + 1 / 2 + (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hP, hA, hAn, hn1]
  ring_nf

lemma qcoef_recurrence_mid (lam : ℝ) (hlam : 0 < lam) (n r : ℕ)
    (hr0 : 0 < r) (hrn : r ≤ n + 1) :
    ((n : ℝ) + 2) * qcoef lam (n + 2) r =
      2 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) r -
        4 * ((n : ℝ) + 1 + lam) * qcoef lam (n + 1) (r - 1) -
          ((n : ℝ) + 2 * lam) * (if r ≤ n then qcoef lam n r else 0) := by
  by_cases hr : r ≤ n
  · rw [if_pos hr]
    have hk : r - 1 < n := by omega
    have h := qcoef_recurrence_inner lam hlam n (r - 1) hk
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : r ≠ 0))] using h
  · have hre : r = n + 1 := by omega
    subst r
    rw [if_neg (by omega : ¬ n + 1 ≤ n)]
    simp only [mul_zero, sub_zero, Nat.add_sub_cancel]
    exact qcoef_recurrence_edge lam hlam n

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

noncomputable def qPoly (lam : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.ofFn (n + 1) fun k => qcoef lam n k

lemma coeff_qPoly (lam : ℝ) (n r : ℕ) :
    (qPoly lam n).coeff r = if r ≤ n then qcoef lam n r else 0 := by
  by_cases hr : r ≤ n
  · rw [if_pos hr]
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)
  · rw [if_neg hr]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

lemma qPoly_recurrence (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ((n : ℝ) + 2) • qPoly lam (n + 2) =
      (2 * ((n : ℝ) + 1 + lam)) • qPoly lam (n + 1) -
        (4 * ((n : ℝ) + 1 + lam)) • (Polynomial.X * qPoly lam (n + 1)) -
          ((n : ℝ) + 2 * lam) • qPoly lam n := by
  ext r
  simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_sub]
  cases r with
  | zero =>
      simp [coeff_qPoly, Polynomial.coeff_X_mul_zero,
        qcoef_recurrence_zero lam hlam n]
  | succ k =>
      rw [Polynomial.coeff_X_mul, coeff_qPoly, coeff_qPoly, coeff_qPoly, coeff_qPoly]
      by_cases htop : k + 1 = n + 2
      · have hk : k = n + 1 := by omega
        subst k
        simp only [le_refl, if_true]
        rw [if_neg (by omega : ¬ n + 2 ≤ n + 1),
          if_neg (by omega : ¬ n + 2 ≤ n)]
        simp only [mul_zero, sub_zero]
        simpa [show n + 1 + 1 = n + 2 by omega] using qcoef_recurrence_top lam hlam n
      · by_cases hrle : k + 1 ≤ n + 1
        · rw [if_pos (by omega : k + 1 ≤ n + 2), if_pos hrle, if_pos (by omega : k ≤ n + 1)]
          simpa using qcoef_recurrence_mid lam hlam n (k + 1) (by omega) hrle
        · rw [if_neg (by omega : ¬ k + 1 ≤ n + 2), if_neg hrle,
            if_neg (by omega : ¬ k + 1 ≤ n), if_neg (by omega : ¬ k ≤ n + 1)]
          ring

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

noncomputable def binomCoeff (lam : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  (ascPochhammer ℂ n).eval (lam : ℂ) / (n.factorial : ℂ) * u ^ n

noncomputable def binomPS (lam : ℝ) (u : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (binomCoeff lam u)

@[simp] lemma coeff_binomPS (lam : ℝ) (u : ℂ) (n : ℕ) :
    PowerSeries.coeff n (binomPS lam u) = binomCoeff lam u n := by
  simp [binomPS]

lemma binomCoeff_succ (lam : ℝ) (u : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * binomCoeff lam u (n + 1) =
      ((lam : ℂ) + n) * u * binomCoeff lam u n := by
  simp only [binomCoeff]
  rw [ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring

lemma binomPS_ode (lam : ℝ) (u : ℂ) :
    (binomPS lam u).derivativeFun -
        PowerSeries.C u * ((binomPS lam u).derivativeFun * PowerSeries.X) =
      PowerSeries.C ((lam : ℂ) * u) * binomPS lam u := by
  ext n
  cases n with
  | zero =>
      simp only [map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_derivativeFun, coeff_binomPS]
      simpa using binomCoeff_succ lam u 0
  | succ n =>
      simp only [map_sub, PowerSeries.coeff_C_mul]
      rw [show n + 1 = n + 1 by rfl, ← pow_one PowerSeries.X,
        PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_derivativeFun,
        PowerSeries.coeff_derivativeFun, coeff_binomPS, coeff_binomPS]
      have h1 := binomCoeff_succ lam u (n + 1)
      have h0 := binomCoeff_succ lam u n
      push_cast at h1 h0 ⊢
      linear_combination h1

noncomputable def productPS (lam : ℝ) (u v : ℂ) : PowerSeries ℂ :=
  binomPS lam u * binomPS lam v

lemma productPS_ode (lam : ℝ) (u v : ℂ) :
    (1 - PowerSeries.C (u + v) * PowerSeries.X +
        PowerSeries.C (u * v) * PowerSeries.X ^ 2) * (productPS lam u v).derivativeFun =
      (PowerSeries.C ((lam : ℂ) * (u + v)) -
        PowerSeries.C (2 * (lam : ℂ) * u * v) * PowerSeries.X) * productPS lam u v := by
  have hu := binomPS_ode lam u
  have hv := binomPS_ode lam v
  rw [productPS, PowerSeries.derivativeFun_mul]
  simp only [map_add, map_mul, map_ofNat] at hu hv ⊢
  linear_combination
    (1 - PowerSeries.C v * PowerSeries.X) * (binomPS lam v) * hu +
    (1 - PowerSeries.C u * PowerSeries.X) * (binomPS lam u) * hv

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

lemma productPS_coeff_recurrence (lam : ℝ) (u v : ℂ) (n : ℕ) :
    ((n : ℂ) + 2) * PowerSeries.coeff (n + 2) (productPS lam u v) =
      (u + v) * ((n : ℂ) + 1 + lam) * PowerSeries.coeff (n + 1) (productPS lam u v) -
        u * v * ((n : ℂ) + 2 * lam) * PowerSeries.coeff n (productPS lam u v) := by
  have h := productPS_ode lam u v
  let P := productPS lam u v
  let D := P.derivativeFun
  have he : D - PowerSeries.C (u + v) * (PowerSeries.X * D) +
        PowerSeries.C (u * v) * (PowerSeries.X ^ 2 * D) =
      PowerSeries.C ((lam : ℂ) * (u + v)) * P -
        PowerSeries.C (2 * (lam : ℂ) * u * v) * (PowerSeries.X * P) := by
    simp only [P, D]
    linear_combination h
  cases n with
  | zero =>
      have hc := congrArg (PowerSeries.coeff 1) he
      rw [map_add] at hc
      rw [map_sub, map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul] at hc
      have hxD : PowerSeries.coeff 1 (PowerSeries.X * D) = PowerSeries.coeff 0 D := by
        simpa only [zero_add, pow_one] using PowerSeries.coeff_X_pow_mul D 1 0
      have hxP : PowerSeries.coeff 1 (PowerSeries.X * P) = PowerSeries.coeff 0 P := by
        simpa only [zero_add, pow_one] using PowerSeries.coeff_X_pow_mul P 1 0
      have hx2 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * D) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']; simp
      rw [hxD, hxP, hx2, PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun] at hc
      simp only [P, D, Nat.cast_zero, zero_add]
      linear_combination hc
  | succ n =>
      have hc := congrArg (PowerSeries.coeff (n + 2)) he
      rw [map_add] at hc
      rw [map_sub, map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_C_mul] at hc
      have hxD : PowerSeries.coeff (n + 2) (PowerSeries.X * D) = PowerSeries.coeff (n + 1) D := by
        simpa only [show 1 + (n + 1) = n + 2 by omega, pow_one] using PowerSeries.coeff_X_pow_mul D 1 (n + 1)
      have hxP : PowerSeries.coeff (n + 2) (PowerSeries.X * P) = PowerSeries.coeff (n + 1) P := by
        simpa only [show 1 + (n + 1) = n + 2 by omega, pow_one] using PowerSeries.coeff_X_pow_mul P 1 (n + 1)
      have hx2 : PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * D) = PowerSeries.coeff n D := by
        simpa only [Nat.add_comm] using PowerSeries.coeff_X_pow_mul D 2 n
      rw [hxD, hxP, hx2, PowerSeries.coeff_derivativeFun,
        PowerSeries.coeff_derivativeFun, PowerSeries.coeff_derivativeFun] at hc
      push_cast at hc ⊢
      linear_combination hc

lemma eval_qPoly (lam : ℝ) (n : ℕ) (y : ℝ) :
    (qPoly lam n).eval y = ∑ k ∈ Finset.range (n + 1), qcoef lam n k * y ^ k := by
  rw [qPoly, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  exact Fin.sum_univ_eq_sum_range (fun k => qcoef lam n k * y ^ k) (n + 1)

lemma gegenbauer_eq_eval_qPoly (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    gegenbauer lam n x = (qPoly lam n).eval ((1 - x) / 2) := by
  rw [gegenbauer_eq_qcoef lam hlam n x, eval_qPoly]

lemma qPoly_eval_recurrence (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * (qPoly lam (n + 2)).eval ((1 - x) / 2) =
      2 * ((n : ℝ) + 1 + lam) * x * (qPoly lam (n + 1)).eval ((1 - x) / 2) -
        ((n : ℝ) + 2 * lam) * (qPoly lam n).eval ((1 - x) / 2) := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval ((1 - x) / 2))
    (qPoly_recurrence lam hlam n)
  simp only [Polynomial.eval_smul, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X] at h
  linear_combination h

lemma gegenbauer_recurrence (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * gegenbauer lam (n + 2) x =
      2 * ((n : ℝ) + 1 + lam) * x * gegenbauer lam (n + 1) x -
        ((n : ℝ) + 2 * lam) * gegenbauer lam n x := by
  rw [gegenbauer_eq_eval_qPoly lam hlam, gegenbauer_eq_eval_qPoly lam hlam,
    gegenbauer_eq_eval_qPoly lam hlam]
  exact qPoly_eval_recurrence lam hlam x n

lemma gegenbauer_one (lam x : ℝ) (hlam : 0 < lam) : gegenbauer lam 1 x = 2 * lam * x := by
  rw [gegenbauer]
  norm_num [Finset.sum_range_succ, ascPochhammer_succ_eval]
  have h : lam + 1 / 2 ≠ 0 := by linarith
  have h2 : 2 * lam ≠ 0 := mul_ne_zero (by norm_num) hlam.ne'
  field_simp [hlam.ne', h2]
  · left
    ring

lemma productPS_coeff_eq_gegenbauer (lam x : ℝ) (hlam : 0 < lam)
    (u v : ℂ) (huv : u + v = 2 * x) (huv' : u * v = 1) (n : ℕ) :
    PowerSeries.coeff n (productPS lam u v) = (gegenbauer lam n x : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [productPS, binomPS, binomCoeff]
  | one =>
      rw [gegenbauer_one lam x hlam]
      norm_num [productPS, binomPS, binomCoeff, PowerSeries.coeff_mul, Finset.antidiagonal]
      push_cast at huv
      linear_combination (lam : ℂ) * huv
  | more n h0 h1 =>
      have hc := productPS_coeff_recurrence lam u v n
      rw [h0, h1, huv, huv'] at hc
      have hg := gegenbauer_recurrence lam hlam x n
      have hgC : ((n : ℂ) + 2) * (gegenbauer lam (n + 2) x : ℂ) =
          2 * ((n : ℂ) + 1 + lam) * x * (gegenbauer lam (n + 1) x : ℂ) -
            ((n : ℂ) + 2 * lam) * (gegenbauer lam n x : ℂ) := by
        exact_mod_cast hg
      have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      apply mul_left_cancel₀ hn
      linear_combination hc - hgC

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

lemma summable_norm_complex_binomial (lam : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    Summable fun n : ℕ => ‖(ascPochhammer ℂ n).eval (lam : ℂ) / (n.factorial : ℂ) * t ^ n‖ :=
  summable_norm_iff.mpr (Complex.hasSum_ascPochhammer_div_factorial_mul_cpow lam ht).summable

lemma cpow_mul_conj_cpow (lam : ℝ) {a : ℂ} (ha : 0 < a.re) :
    a ^ (-(lam : ℂ)) * (starRingEnd ℂ a) ^ (-(lam : ℂ)) =
      ((Complex.normSq a) ^ (-lam) : ℝ) := by
  have harg : a.arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.1]
  rw [Complex.conj_cpow a (-(lam : ℂ)) harg]
  have hlc : (starRingEnd ℂ) (lam : ℂ) = (lam : ℂ) := by simp
  rw [map_neg, hlc, Complex.mul_conj]
  congr 1
  have hnorm := Complex.norm_cpow_real a (-lam)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [show (-(lam : ℂ)) = ((-lam : ℝ) : ℂ) by push_cast; ring, hnorm]
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  rw [← Real.rpow_mul_natCast hn (-lam) 2, ← Real.rpow_natCast_mul hn 2 (-lam)]
  ring_nf

lemma complex_gegenbauer_hasSum {lam x z : ℝ} (hlam : 0 < lam) (hx : |x| ≤ 1)
    (hz : |z| < 1) :
    HasSum (fun n : ℕ => (gegenbauer lam n x : ℂ) * (z : ℂ) ^ n)
      (((1 - 2 * x * z + z ^ 2) ^ (-lam) : ℝ) : ℂ) := by
  let theta := Real.arccos x
  let u : ℂ := Complex.exp ((theta : ℂ) * Complex.I)
  let v : ℂ := Complex.exp (-(theta : ℂ) * Complex.I)
  have hxlo : -1 ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ 1 := (abs_le.mp hx).2
  have hcos : Real.cos theta = x := Real.cos_arccos hxlo hxhi
  have hu_norm : ‖u‖ = 1 := by simp [u, Complex.norm_exp_ofReal_mul_I]
  have hv_norm : ‖v‖ = 1 := by
    dsimp [v]
    rw [show -(theta : ℂ) * Complex.I = ((-theta : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hvconj : v = starRingEnd ℂ u := by
    dsimp [v, u]
    rw [← Complex.exp_conj]
    congr
    simp
  have huv : u + v = 2 * x := by
    dsimp [u, v]
    rw [show -(theta : ℂ) * Complex.I = ((-theta : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp [hcos]
    ring
  have huv' : u * v = 1 := by
    dsimp [u, v]
    rw [← Complex.exp_add]
    simp
  have huz : ‖u * (z : ℂ)‖ < 1 := by simpa [norm_mul, hu_norm, Real.norm_eq_abs] using hz
  have hvz : ‖v * (z : ℂ)‖ < 1 := by simpa [norm_mul, hv_norm, Real.norm_eq_abs] using hz
  have hU0 := Complex.hasSum_ascPochhammer_div_factorial_mul_cpow lam huz
  have hV0 := Complex.hasSum_ascPochhammer_div_factorial_mul_cpow lam hvz
  have hU : HasSum (fun n => binomCoeff lam u n * (z : ℂ) ^ n)
      ((1 - u * z) ^ (-(lam : ℂ))) := by
    convert hU0 using 1 <;> funext n <;> simp [binomCoeff, mul_pow] <;> ring
  have hV : HasSum (fun n => binomCoeff lam v n * (z : ℂ) ^ n)
      ((1 - v * z) ^ (-(lam : ℂ))) := by
    convert hV0 using 1 <;> funext n <;> simp [binomCoeff, mul_pow] <;> ring
  have hUn : Summable fun n => ‖binomCoeff lam u n * (z : ℂ) ^ n‖ :=
    summable_norm_iff.mpr hU.summable
  have hVn : Summable fun n => ‖binomCoeff lam v n * (z : ℂ) ^ n‖ :=
    summable_norm_iff.mpr hV.summable
  have hp := FLMF.Methods.hasSum_cauchy_product hU hV hUn hVn
  have hp' : HasSum (fun n => PowerSeries.coeff n (productPS lam u v) * (z : ℂ) ^ n)
      ((1 - u * z) ^ (-(lam : ℂ)) * (1 - v * z) ^ (-(lam : ℂ))) := by
    convert hp using 1
    funext n
    rw [productPS, PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl hkl
    rw [Finset.mem_antidiagonal] at hkl
    simp only [coeff_binomPS]
    rw [← hkl, pow_add]
    ring
  rw [funext fun n => congrArg (fun w : ℂ => w * (z : ℂ) ^ n)
    (productPS_coeff_eq_gegenbauer lam x hlam u v huv huv' n)] at hp'
  let a : ℂ := 1 - u * z
  have hva : 1 - v * z = starRingEnd ℂ a := by
    rw [hvconj]
    dsimp [a]
    simp
  have hare : 0 < a.re := by
    have hle : (u * (z : ℂ)).re ≤ ‖u * (z : ℂ)‖ := (Complex.re_le_norm _)
    dsimp [a]
    linarith [huz]
  have hprod : a * starRingEnd ℂ a = (1 - 2 * x * z + z ^ 2 : ℝ) := by
    rw [← hva]
    simp only [a]
    calc
      (1 - u * (z : ℂ)) * (1 - v * (z : ℂ))
          = 1 - (u + v) * z + (u * v) * z ^ 2 := by ring
      _ = (1 - 2 * x * z + z ^ 2 : ℝ) := by rw [huv, huv']; push_cast; ring
  have hbase : Complex.normSq a = 1 - 2 * x * z + z ^ 2 := by
    rw [← Complex.ofReal_inj]
    rw [(Complex.mul_conj a).symm, hprod]
  rw [hva, cpow_mul_conj_cpow lam hare, hbase] at hp'
  simpa using hp'

end FLMF.Gegenbauer

namespace FLMF.Gegenbauer

-- no-dlmf: real-`z` restriction of DLMF 18.12.4; faithful surface is
-- gegenbauer_generating_function_complex.
/-- The generating function of the Gegenbauer (ultraspherical) polynomials
`C_n^{(λ)}` (real `z`).  For `λ > 0`, `|x| ≤ 1` and `|z| < 1`,
`(1 - 2xz + z²)^{-λ} = Σ_{n≥0} C_n^{(λ)}(x) zⁿ`.

The base `1 - 2xz + z² = (z - x)² + (1 - x²) > 0` under the hypotheses, so the
left-hand `rpow` is the genuine analytic power.

Proof route (no new method — consumes existing machinery):
  1. `x = cos θ` ⇒ `1 - 2xz + z² = (1 - z·e^{iθ})(1 - z·e^{-iθ})`; expand each factor
     by the generalized negative-binomial series
     `Real.hasSum_ascPochhammer_div_factorial_mul_pow`
     (in `…/LaguerreGeneratingFun.lean`), then Cauchy-multiply the two series via
     `FLMF.Methods.hasSum_cauchy_product` (`FLMF/Methods/GeneratingFunction.lean`);
     the `zⁿ` coefficient collapses to the `₂F₁` Gegenbauer sum of `gegenbauer`.
  ALT. Show `G(z) := (1 - 2xz + z²)^{-λ}` solves the first-order ODE
     `(1 - 2xz + z²)·G'(z) = 2λ·(x - z)·G(z)`; equating `zⁿ` coefficients gives the
     three-term recurrence `(n+1)·C_{n+1}(x) = 2(n+λ)x·C_n(x) − (n+2λ−1)·C_{n−1}(x)`.
     Reduce to a `gegenbauer` recurrence lemma (not yet present — a natural companion
     to prove first). Base case `C_0^{(λ)} = 1` is `gegenbauer_zero`. -/
theorem gegenbauer_generating_function {lam x z : ℝ}
    (hlam : 0 < lam) (hx : |x| ≤ 1) (hz : |z| < 1) :
    HasSum (fun n : ℕ => gegenbauer lam n x * z ^ n)
      ((1 - 2 * x * z + z ^ 2) ^ (-lam)) := by
  rw [← Complex.hasSum_ofReal]
  simpa using complex_gegenbauer_hasSum hlam hx hz

/-- **DLMF 18.12.4** — the generating function of the Gegenbauer (ultraspherical)
polynomials `C_n^{(λ)}` at DLMF's stated strength, as the display's 2-link
conjunction: real `x`, complex `z` with `‖z‖ < 1`,
`(1 - 2xz + z²)^{-λ} = Σ_{n≥0} C_n^{(λ)}(x) zⁿ
  = Σ_{n≥0} [(2λ)_n / (λ+1/2)_n] P_n^{(λ-1/2,λ-1/2)}(x) zⁿ`.

`|x| ≤ 1` is retained beyond DLMF's bare per-equation constraint list (which lists
only `|z| < 1`): for real `x` with `|x| > 1` the roots of `1 - 2xz + z² = 0` are real
with product `1`, so one root lies strictly inside the open unit disc and the series
diverges there. The unconstrained-`x` reading of 18.12.4 is therefore false;
`|x| ≤ 1` is the correctness-preserving domain, and `z : ℝ → z : ℂ` is the genuine
relaxation DLMF's `z : complex variable` glossary calls for. `(1 - 2xz + z²)^{-λ}`
is the principal-branch `Complex.cpow`.

The second link is `FLMF.Gegenbauer.gegenbauer_eq_jacobi` divided through by the
nonzero `(λ+1/2)_n` (`ascPochhammer_pos`, since `λ + 1/2 > 0`), applied termwise
to the (unresolved) first link's series.

DLMF 18.12.4.
DAG: E-18.12.4.
Fidelity: tier1 PASS
Verified: unverified
-/
theorem gegenbauer_generating_function_complex {lam x : ℝ} (hlam : 0 < lam)
    (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    (HasSum (fun n : ℕ => (gegenbauer lam n x : ℂ) * z ^ n)
        ((1 - 2 * (x : ℂ) * z + z ^ 2) ^ (-(lam : ℂ)))) ∧
      (HasSum (fun n : ℕ =>
          (((ascPochhammer ℝ n).eval (2 * lam) /
              (ascPochhammer ℝ n).eval (lam + 1 / 2) : ℝ) *
            FLMF.Jacobi.jacobiP (lam - 1 / 2) (lam - 1 / 2) n x : ℂ) * z ^ n)
        ((1 - 2 * (x : ℂ) * z + z ^ 2) ^ (-(lam : ℂ)))) := by
  have hlink1 : HasSum (fun n : ℕ => (gegenbauer lam n x : ℂ) * z ^ n)
      ((1 - 2 * (x : ℂ) * z + z ^ 2) ^ (-(lam : ℂ))) := by
    sorry
  refine ⟨hlink1, ?_⟩
  have hfg : (fun n : ℕ => (gegenbauer lam n x : ℂ) * z ^ n) =
      (fun n : ℕ =>
        (((ascPochhammer ℝ n).eval (2 * lam) /
            (ascPochhammer ℝ n).eval (lam + 1 / 2) : ℝ) *
          FLMF.Jacobi.jacobiP (lam - 1 / 2) (lam - 1 / 2) n x : ℂ) * z ^ n) := by
    funext n
    have hne : (ascPochhammer ℝ n).eval (lam + 1 / 2) ≠ 0 :=
      (ascPochhammer_pos n (lam + 1 / 2) (by linarith)).ne'
    have hreal : gegenbauer lam n x =
        (ascPochhammer ℝ n).eval (2 * lam) / (ascPochhammer ℝ n).eval (lam + 1 / 2) *
          FLMF.Jacobi.jacobiP (lam - 1 / 2) (lam - 1 / 2) n x := by
      rw [div_mul_eq_mul_div, eq_div_iff hne]
      linear_combination gegenbauer_eq_jacobi lam n x
    rw [hreal]
    push_cast
    ring
  rw [← hfg]
  exact hlink1

end FLMF.Gegenbauer
