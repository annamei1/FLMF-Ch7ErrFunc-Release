import FLMF.Support.HypergeometricKummerODE
import FLMF.Support.Recurrence

/-!
# Contiguous relations for `₁F₁` (framework — DLMF §13.3)

The Gauss contiguous relations for Kummer's confluent hypergeometric function,
connecting `M` at parameters shifted by one:

* `kummerM_contiguous_a` — DLMF 13.3.1:
  `(b−a) M(a−1;b;z) + (2a−b+z) M(a;b;z) − a M(a+1;b;z) = 0`.
* `kummerM_contiguous_b` — DLMF 13.3.2:
  `b(b−1) M(a;b−1;z) + b(1−b−z) M(a;b;z) + z(b−a) M(a;b+1;z) = 0`.
* `kummerM_contiguous_ab` — DLMF 13.3.5:
  `b(a+z) M(a;b;z) + z(a−b) M(a;b+1;z) − ab M(a+1;b;z) = 0`.

(The differentiated relation DLMF 13.3.15 is `kummerM_deriv` in `KummerODE`.)

Each proof matches coefficients of `zⁿ` through the `FLMF.Methods.Recurrence`
combinators: the series are combined through their `HasSum` forms
(`kummerM_hasSum`, with `z·M` reindexed down one exponent by
`hasSum_zero_cons`) and `hasSum_eq_zero` reduces the relation to the termwise
identity, where every coefficient vanishes by Pochhammer algebra — the
normalizers `ascPochhammer_succ_eval_sub_one`, `ascPochhammer_succ_eval'`, and
the bridge `ascPochhammer_shift_bridge` `(x)ₘ·(x+m) = x·(x+1)ₘ` reduce all
terms to the atoms `(a)ₘ`, `(a+1)ₘ`, `(b)ₘ`, `(b+1)ₘ`, which are `ring`-equal.
-/

open Nat FormalMultilinearSeries FLMF.Methods

namespace FLMF.Hypergeometric

section Coefficients

variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂] (a b : 𝕂)

omit [CharZero 𝕂] in
/-- `c₀(a,b) = 1`. -/
-- no-dlmf: trivial base coefficient, no DLMF counterpart
theorem kummerCoefficient_zero : kummerCoefficient a b 0 = 1 := by
  simp [kummerCoefficient]

-- no-dlmf: termwise Pochhammer-coefficient identity (no `M` or `z`), an
-- intermediate step in the proof of `kummerM_contiguous_a`, which is the
-- DLMF-faithful surface for DLMF 13.3.1.
/-- Termwise form of DLMF 13.3.1 at exponent `m+1`, for `b` not a nonpositive
integer: `(b−a)·cₘ₊₁(a−1,b) + (2a−b)·cₘ₊₁(a,b) + cₘ(a,b) − a·cₘ₊₁(a+1,b) = 0`
(the `cₘ(a,b)` term is the reindexed `z·M` contribution). -/
theorem kummerCoefficient_contiguous_a (m : ℕ) (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) :
    (b - a) * kummerCoefficient (a - 1) b (m + 1) + (2 * a - b) * kummerCoefficient a b (m + 1)
      + kummerCoefficient a b m - a * kummerCoefficient (a + 1) b (m + 1) = 0 := by
  have hB : (ascPochhammer 𝕂 m).eval b ≠ 0 := ascPochhammer_eval_ne_zero hb m
  have hbm : b + (m : 𝕂) ≠ 0 := fun h => hb m (by linear_combination h)
  have hm1 : ((m : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  simp only [kummerCoefficient, cast_factorial_succ, ascPochhammer_succ_eval_sub_one a m,
    ascPochhammer_succ_eval, mul_inv]
  field_simp
  linear_combination (-(((m ! : ℕ) : 𝕂))⁻¹ * (a + 1 + (m : 𝕂))) * ascPochhammer_shift_bridge a m

-- no-dlmf: termwise Pochhammer-coefficient identity (no `M` or `z`), an
-- intermediate step in the proof of `kummerM_contiguous_b`, which is the
-- DLMF-faithful surface for DLMF 13.3.2.
/-- Termwise form of DLMF 13.3.2 at exponent `m+1`, for `b−1` not a nonpositive
integer: `b(b−1)·cₘ₊₁(a,b−1) + b(1−b)·cₘ₊₁(a,b) − b·cₘ(a,b) + (b−a)·cₘ(a,b+1) = 0`
(the `cₘ` terms are the reindexed `z·M` contributions). -/
theorem kummerCoefficient_contiguous_b (m : ℕ) (hb1 : ∀ k : ℕ, (k : 𝕂) ≠ -(b - 1)) :
    b * (b - 1) * kummerCoefficient a (b - 1) (m + 1) + b * (1 - b) * kummerCoefficient a b (m + 1)
      - b * kummerCoefficient a b m + (b - a) * kummerCoefficient a (b + 1) m = 0 := by
  have hB : (ascPochhammer 𝕂 m).eval b ≠ 0 :=
    ascPochhammer_eval_ne_zero (fun k h => hb1 (k + 1) (by push_cast; linear_combination h)) m
  have hB1 : (ascPochhammer 𝕂 m).eval (b + 1) ≠ 0 :=
    ascPochhammer_eval_ne_zero (fun k h => hb1 (k + 2) (by push_cast; linear_combination h)) m
  have hb0 : b ≠ 0 := fun h => hb1 1 (by push_cast; linear_combination h)
  have hbs : b - 1 ≠ 0 := fun h => hb1 0 (by push_cast; linear_combination h)
  have hm1 : ((m : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  simp only [kummerCoefficient, cast_factorial_succ, ascPochhammer_succ_eval_sub_one b m,
    ascPochhammer_succ_eval' m b, ascPochhammer_succ_eval m a, mul_inv]
  field_simp
  linear_combination (((m ! : ℕ) : 𝕂))⁻¹ * (a - 1) * (ascPochhammer 𝕂 m).eval a *
    ascPochhammer_shift_bridge b m

-- no-dlmf: termwise Pochhammer-coefficient identity (no `M` or `z`), an
-- intermediate step in the proof of `kummerM_contiguous_ab`, which is the
-- DLMF-faithful surface for DLMF 13.3.5.
/-- Termwise form of DLMF 13.3.5 at exponent `m+1`, for `b` not a nonpositive
integer: `ba·cₘ₊₁(a,b) + b·cₘ(a,b) + (a−b)·cₘ(a,b+1) − ab·cₘ₊₁(a+1,b) = 0`
(the `cₘ` terms are the reindexed `z·M` contributions). -/
theorem kummerCoefficient_contiguous_ab (m : ℕ) (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) :
    b * a * kummerCoefficient a b (m + 1) + b * kummerCoefficient a b m
      + (a - b) * kummerCoefficient a (b + 1) m - a * b * kummerCoefficient (a + 1) b (m + 1)
      = 0 := by
  have hB : (ascPochhammer 𝕂 m).eval b ≠ 0 := ascPochhammer_eval_ne_zero hb m
  have hB1 : (ascPochhammer 𝕂 m).eval (b + 1) ≠ 0 :=
    ascPochhammer_eval_ne_zero (fun k h => hb (k + 1) (by push_cast; linear_combination h)) m
  have hb0 : b ≠ 0 := fun h => hb 0 (by simp [h])
  have hbm : b + (m : 𝕂) ≠ 0 := fun h => hb m (by linear_combination h)
  have hm1 : ((m : 𝕂) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  simp only [kummerCoefficient, cast_factorial_succ, ascPochhammer_succ_eval, mul_inv]
  field_simp
  linear_combination (((m ! : ℕ) : 𝕂))⁻¹ * ((b - a) * ((m : 𝕂) + 1) * (ascPochhammer 𝕂 m).eval a
    * ascPochhammer_shift_bridge b m - b * (a + (m : 𝕂) + 1) * (ascPochhammer 𝕂 m).eval (b + 1)
    * ascPochhammer_shift_bridge a m)

end Coefficients

section Relations

variable {𝕂 : Type*} [RCLike 𝕂] (a b : 𝕂)

/-- The `z·M(a;b;z)` series, aligned to exponent `n`: the `n = 0` term is `0`
and the `n = m+1` term is `cₘ(a,b)·z^(m+1)`. -/
-- no-dlmf: series-reindexing infrastructure, no DLMF counterpart
theorem kummerM_hasSum_shift (x : 𝕂) :
    HasSum (fun n : ℕ => (match n with
      | 0 => (0 : 𝕂)
      | m + 1 => kummerCoefficient a b m * x ^ (m + 1)))
      (x * ₁F₁ a b x) :=
  hasSum_zero_cons ((kummerM_hasSum a b x).mul_left x) rfl fun m => by
    show kummerCoefficient a b m * x ^ (m + 1) = x * (kummerCoefficient a b m * x ^ m)
    ring

/-- **Contiguous relation in `a`** (DLMF 13.3.1):
`(b−a) M(a−1;b;z) + (2a−b+z) M(a;b;z) − a M(a+1;b;z) = 0`, for `b` not a
nonpositive integer.

DAG: E-13.3.1.
Numerical: PASS
Verified: unverified
-/
theorem kummerM_contiguous_a (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) (x : 𝕂) :
    (b - a) * ₁F₁ (a - 1) b x + (2 * a - b + x) * ₁F₁ a b x - a * ₁F₁ (a + 1) b x = 0 := by
  have hT0 := hasSum_eq_zero (((((kummerM_hasSum (a - 1) b x).mul_left (b - a)).add
      ((kummerM_hasSum a b x).mul_left (2 * a - b))).add
      (kummerM_hasSum_shift a b x)).sub
      ((kummerM_hasSum (a + 1) b x).mul_left a)) fun n => by
    cases n with
    | zero => simp [kummerCoefficient_zero]; ring
    | succ m => linear_combination x ^ (m + 1) * kummerCoefficient_contiguous_a a b m hb
  linear_combination hT0

/-- **Contiguous relation in `b`** (DLMF 13.3.2):
`b(b−1) M(a;b−1;z) + b(1−b−z) M(a;b;z) + z(b−a) M(a;b+1;z) = 0`, for `b−1` not
a nonpositive integer.

DAG: E-13.3.2.
Numerical: PASS
Verified: unverified
-/
theorem kummerM_contiguous_b (hb1 : ∀ k : ℕ, (k : 𝕂) ≠ -(b - 1)) (x : 𝕂) :
    b * (b - 1) * ₁F₁ a (b - 1) x + b * (1 - b - x) * ₁F₁ a b x
      + x * (b - a) * ₁F₁ a (b + 1) x = 0 := by
  have hT0 := hasSum_eq_zero (((((kummerM_hasSum a (b - 1) x).mul_left (b * (b - 1))).add
      ((kummerM_hasSum a b x).mul_left (b * (1 - b)))).sub
      ((kummerM_hasSum_shift a b x).mul_left b)).add
      ((kummerM_hasSum_shift a (b + 1) x).mul_left (b - a))) fun n => by
    cases n with
    | zero => simp [kummerCoefficient_zero]; ring
    | succ m => linear_combination x ^ (m + 1) * kummerCoefficient_contiguous_b a b m hb1
  linear_combination hT0

/-- **Mixed contiguous relation** (DLMF 13.3.5):
`b(a+z) M(a;b;z) + z(a−b) M(a;b+1;z) − ab M(a+1;b;z) = 0`, for `b` not a
nonpositive integer.

DAG: E-13.3.5.
Numerical: PASS
Verified: unverified
-/
theorem kummerM_contiguous_ab (hb : ∀ k : ℕ, (k : 𝕂) ≠ -b) (x : 𝕂) :
    b * (a + x) * ₁F₁ a b x + x * (a - b) * ₁F₁ a (b + 1) x
      - a * b * ₁F₁ (a + 1) b x = 0 := by
  have hT0 := hasSum_eq_zero (((((kummerM_hasSum a b x).mul_left (b * a)).add
      ((kummerM_hasSum_shift a b x).mul_left b)).add
      ((kummerM_hasSum_shift a (b + 1) x).mul_left (a - b))).sub
      ((kummerM_hasSum (a + 1) b x).mul_left (a * b))) fun n => by
    cases n with
    | zero => simp [kummerCoefficient_zero]; ring
    | succ m => linear_combination x ^ (m + 1) * kummerCoefficient_contiguous_ab a b m hb
  linear_combination hT0

end Relations

end FLMF.Hypergeometric
