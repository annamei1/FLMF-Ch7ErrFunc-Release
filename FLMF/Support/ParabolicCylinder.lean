import FLMF.Support.HypergeometricKummer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FLMF.Support.HypergeometricCh15AsymptoticApproximations

section

/-!
# Parabolic cylinder functions — even/odd fundamental solutions (DLMF §12.4)

Reference: DLMF §12.4, <https://dlmf.nist.gov/12.4>.

The **parabolic cylinder equation** (DLMF 12.2.2, here in the second standard
form) is
```
  w'' − (¼ x² + a) w = 0.
```
DLMF 12.4.1–12.4.2 give two standard fundamental solutions, an **even** and an
**odd** one, built from the confluent hypergeometric (Kummer) function
`M(a;b;z) = ₁F₁ a b z`:
```
  w₁(a, x) = exp(−x²/4) · ₁F₁(½a + ¼; ½;   ½x²)     (even in x)
  w₂(a, x) = x · exp(−x²/4) · ₁F₁(½a + ¾; 3/2; ½x²)  (odd  in x).
```
Here `w₁` is even (`w₁(a,0)=1`, `w₁'(a,0)=0`) and `w₂` is odd (`w₂(a,0)=0`,
`w₂'(a,0)=1`); together they form a fundamental system for the equation.

The recessive/dominant Whittaker normalizations `U(a,x)` and `V(a,x)` (DLMF
12.2.x, 12.4.x) are specific Gamma-function combinations of `w₁` and `w₂`; those
coefficients must be reproduced exactly, so `U`/`V` and the ODE itself are
deferred to follow-up work. This file establishes only the two even/odd
fundamental solutions and their basic structural properties (values at `0` and
parity).
-/

open scoped FLMF.Hypergeometric

namespace FLMF.ParabolicCylinder

/-- The **even** fundamental solution `w₁(a, x)` of the parabolic cylinder
equation `w'' − (¼x² + a)w = 0` (DLMF 12.4.3):
`w₁(a,x) = exp(−x²/4) · ₁F₁(½a + ¼; ½; ½x²)`. -/
noncomputable def pcfEven (a x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 4) * ₁F₁ (a / 2 + 1 / 4) (1 / 2) (x ^ 2 / 2)

/-- The **odd** fundamental solution `w₂(a, x)` of the parabolic cylinder
equation `w'' − (¼x² + a)w = 0` (DLMF 12.4.4):
`w₂(a,x) = x · exp(−x²/4) · ₁F₁(½a + ¾; 3/2; ½x²)`. -/
noncomputable def pcfOdd (a x : ℝ) : ℝ :=
  x * Real.exp (-x ^ 2 / 4) * ₁F₁ (a / 2 + 3 / 4) (3 / 2) (x ^ 2 / 2)

-- no-dlmf: instance of DLMF 12.4.3 (value at x = 0); faithful surface is
-- pcfEven_series_complex below.
/-- `w₁(a, 0) = 1`: `exp 0 = 1` and `₁F₁ _ _ 0 = 1`. -/
@[simp]
theorem pcfEven_zero (a : ℝ) : pcfEven a 0 = 1 := by
  simp [pcfEven]

/-- **DLMF 12.4.3** — the even fundamental solution `u₁(a,z)` of the parabolic
cylinder equation as its defining power series, for complex parameter `a` and
complex variable `z` (this file's `pcfEven` is its restriction to real
arguments): `u₁(a,z) = e^{−z²/4}·(1 + (a+½)·z²/2! + (a+½)(a+5/2)·z⁴/4! + ⋯)`,
i.e. the `n`-th term carries the coefficient `∏_{k<n} (a+½+2k)` against
`z^{2n}/(2n)!`.

DAG: E-12.4.3.
Numerical: PASS
Verified: unverified
-/
theorem pcfEven_series_complex (a z : ℂ) :
    Complex.exp (-z ^ 2 / 4) * ₁F₁ (a / 2 + 1 / 4) (1 / 2 : ℂ) (z ^ 2 / 2)
      = Complex.exp (-z ^ 2 / 4)
        * ∑' n : ℕ, (∏ k ∈ Finset.range n, (a + 1 / 2 + 2 * k)) * z ^ (2 * n)
            / ((2 * n).factorial : ℂ) := by
  sorry

-- no-dlmf: instance of DLMF 12.4.4 (value at x = 0); faithful surface is
-- pcfOdd_series_complex below.
/-- `w₂(a, 0) = 0`: the leading factor `x` vanishes. -/
@[simp]
theorem pcfOdd_zero (a : ℝ) : pcfOdd a 0 = 0 := by
  simp [pcfOdd]

/-- **DLMF 12.4.4** — the odd fundamental solution `u₂(a,z)` of the parabolic
cylinder equation as its defining power series, for complex parameter `a` and
complex variable `z` (this file's `pcfOdd` is its restriction to real
arguments): `u₂(a,z) = e^{−z²/4}·(z + (a+3/2)·z³/3! + (a+3/2)(a+7/2)·z⁵/5! + ⋯)`,
i.e. the `n`-th term carries the coefficient `∏_{k<n} (a+3/2+2k)` against
`z^{2n+1}/(2n+1)!`.

DAG: E-12.4.4.
Numerical: PASS
Verified: unverified
-/
theorem pcfOdd_series_complex (a z : ℂ) :
    z * Complex.exp (-z ^ 2 / 4) * ₁F₁ (a / 2 + 3 / 4) (3 / 2 : ℂ) (z ^ 2 / 2)
      = Complex.exp (-z ^ 2 / 4)
        * ∑' n : ℕ, (∏ k ∈ Finset.range n, (a + 3 / 2 + 2 * k)) * z ^ (2 * n + 1)
            / ((2 * n + 1).factorial : ℂ) := by
  sorry

-- no-dlmf: parity consequence of the `pcfEven` definition, not itself the DLMF
-- 12.4.3 series-defining equation; the faithful surface of 12.4.3 is
-- pcfEven_series_complex above.
/-- `w₁` is **even** in `x`: it depends on `x` only through `x²`. -/
theorem pcfEven_neg (a x : ℝ) : pcfEven a (-x) = pcfEven a x := by
  simp [pcfEven]

-- no-dlmf: parity/oddness consequence of the `pcfOdd` definition (tagged DLMF
-- 12.4.4 above); not itself the tagged series-defining equation.
/-- `w₂` is **odd** in `x`: the `x` prefactor flips sign while the `x²`-dependent
factors are unchanged. -/
theorem pcfOdd_neg (a x : ℝ) : pcfOdd a (-x) = -(pcfOdd a x) := by
  simp [pcfOdd]

/-- The **standard parabolic cylinder function** `U(a,x)` (DLMF 12.2.6–7, 12.4.1),
the recessive solution of `w'' − (¼x²+a)w = 0`, written in the even/odd basis as
`U(a,x) = U(a,0)·w₁(a,x) + U'(a,0)·w₂(a,x)` with the initial values
`U(a,0) = √π·2^{−¼−a/2}/Γ(¾+a/2)` and `U'(a,0) = −√π·2^{¼−a/2}/Γ(¼+a/2)`. -/
-- DAG: E-12.2.6.
-- Verified: unverified
noncomputable def U (a x : ℝ) : ℝ :=
  (Real.sqrt Real.pi * (2 : ℝ) ^ (-1 / 4 - a / 2) / Real.Gamma (3 / 4 + a / 2)) * pcfEven a x
    + (-(Real.sqrt Real.pi * (2 : ℝ) ^ (1 / 4 - a / 2) / Real.Gamma (1 / 4 + a / 2))) * pcfOdd a x

/-- The **second standard parabolic cylinder function** `V(a,x)` (DLMF 12.2.15),
expressed through `U` by the connection formula
`V(a,x) = (Γ(½+a)/π)·(sin(πa)·U(a,x) + U(a,−x))`. -/
-- DAG: E-12.2.15.
-- Verified: unverified
noncomputable def V (a x : ℝ) : ℝ :=
  Real.Gamma (1 / 2 + a) / Real.pi
    * (Real.sin (Real.pi * a) * U a x + U a (-x))

-- no-dlmf: real-parameter instance of DLMF 12.2.6 (`a` restricted to ℝ, where
-- DLMF assigns `a` a real-or-complex domain); faithful surface is
-- U_zero_complex below.
/-- `U(a,0) = √π·2^{−¼−a/2}/Γ(¾+a/2)`, since `w₁(a,0)=1`, `w₂(a,0)=0`. -/
@[simp]
theorem U_zero (a : ℝ) :
    U a 0 = Real.sqrt Real.pi * (2 : ℝ) ^ (-1 / 4 - a / 2) / Real.Gamma (3 / 4 + a / 2) := by
  simp [U]

-- no-dlmf: real-parameter instance of DLMF 12.2.15 (`a`, `x` restricted to ℝ,
-- where DLMF assigns `a` a real-or-complex domain and `z` a complex domain);
-- faithful surface is U_neg_complex below.
/-- The connection formula relating `U(a,−x)` to `U(a,x)` and `V(a,x)`,
valid where `Γ(½+a) ≠ 0`: `U(a,−x) = −sin(πa)·U(a,x) + (π/Γ(½+a))·V(a,x)`. -/
theorem U_neg (a x : ℝ) (ha : Real.Gamma (1 / 2 + a) ≠ 0) :
    U a (-x) = -Real.sin (Real.pi * a) * U a x + Real.pi / Real.Gamma (1 / 2 + a) * V a x := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcancel : Real.pi / Real.Gamma (1 / 2 + a) * (Real.Gamma (1 / 2 + a) / Real.pi) = 1 := by
    rw [div_mul_div_comm, mul_comm (Real.Gamma (1 / 2 + a)) Real.pi,
      div_self (mul_ne_zero hpi ha)]
  rw [V, show Real.pi / Real.Gamma (1 / 2 + a)
        * (Real.Gamma (1 / 2 + a) / Real.pi * (Real.sin (Real.pi * a) * U a x + U a (-x)))
      = (Real.pi / Real.Gamma (1 / 2 + a) * (Real.Gamma (1 / 2 + a) / Real.pi))
        * (Real.sin (Real.pi * a) * U a x + U a (-x)) from by ring, hcancel, one_mul]
  ring

/-! ### Complex-domain surfaces

DLMF assigns `a` a real-or-complex domain and `z` a complex domain throughout
§12.2, so `U(a,z)` and `V(a,z)` are genuinely complex-analytic objects. The
real-argument `U`/`V` above are the restriction of that object to real `a, x`;
`UC`/`VC` below reproduce the same Gamma-quotient combination of `w₁`, `w₂`
over `ℂ`, giving the faithful full-strength surfaces of DLMF 12.2.6/12.2.15. -/

/-- Complex-parameter, complex-variable even fundamental solution
`w₁(a,z) = exp(−z²/4) · ₁F₁(½a + ¼; ½; ½z²)` (DLMF 12.4.3), the complex twin of
`pcfEven`. -/
noncomputable def pcfEvenC (a z : ℂ) : ℂ :=
  Complex.exp (-z ^ 2 / 4) * ₁F₁ (a / 2 + 1 / 4) (1 / 2 : ℂ) (z ^ 2 / 2)

/-- Complex-parameter, complex-variable odd fundamental solution
`w₂(a,z) = z · exp(−z²/4) · ₁F₁(½a + ¾; 3/2; ½z²)` (DLMF 12.4.4), the complex
twin of `pcfOdd`. -/
noncomputable def pcfOddC (a z : ℂ) : ℂ :=
  z * Complex.exp (-z ^ 2 / 4) * ₁F₁ (a / 2 + 3 / 4) (3 / 2 : ℂ) (z ^ 2 / 2)

/-- The complex-parameter, complex-variable standard parabolic cylinder function
`U(a,z)` (DLMF 12.2.6–7, 12.4.1), the complex twin of `U`. -/
noncomputable def UC (a z : ℂ) : ℂ :=
  ((Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-1 / 4 - a / 2) / Complex.Gamma (3 / 4 + a / 2))
      * pcfEvenC a z
    + (-((Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (1 / 4 - a / 2) / Complex.Gamma (1 / 4 + a / 2)))
      * pcfOddC a z

/-- The complex-parameter, complex-variable second standard parabolic cylinder
function `V(a,z)` (DLMF 12.2.15), the complex twin of `V`. -/
noncomputable def VC (a z : ℂ) : ℂ :=
  Complex.Gamma (1 / 2 + a) / (Real.pi : ℂ)
    * (Complex.sin ((Real.pi : ℂ) * a) * UC a z + UC a (-z))

/-- **DLMF 12.2.6** — `U(a,0) = √π·2^{−¼−a/2}/Γ(¾+a/2)`, for real-or-complex
parameter `a`, since `w₁(a,0)=1`, `w₂(a,0)=0`.

DAG: E-12.2.6.
Numerical: PASS
Verified: verified
-/
theorem U_zero_complex (a : ℂ) :
    UC a 0 = (Real.sqrt Real.pi : ℂ) * (2 : ℂ) ^ (-1 / 4 - a / 2) / Complex.Gamma (3 / 4 + a / 2) := by
  simp [UC, pcfEvenC, pcfOddC]

/-- **DLMF 12.2.15** — the connection formula relating `U(a,−z)` to `U(a,z)` and
`V(a,z)`, for real-or-complex parameter `a` and complex variable `z`, valid
where `Γ(½+a) ≠ 0`: `U(a,−z) = −sin(πa)·U(a,z) + (π/Γ(½+a))·V(a,z)`.

DAG: E-12.2.15.
Numerical: PASS
Verified: unverified
-/
theorem U_neg_complex (a z : ℂ) (ha : Complex.Gamma (1 / 2 + a) ≠ 0) :
    UC a (-z) = -Complex.sin ((Real.pi : ℂ) * a) * UC a z
      + (Real.pi : ℂ) / Complex.Gamma (1 / 2 + a) * VC a z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcancel : (Real.pi : ℂ) / Complex.Gamma (1 / 2 + a)
      * (Complex.Gamma (1 / 2 + a) / (Real.pi : ℂ)) = 1 := by
    rw [div_mul_div_comm, mul_comm (Complex.Gamma (1 / 2 + a)) (Real.pi : ℂ),
      div_self (mul_ne_zero hpi ha)]
  rw [VC, show (Real.pi : ℂ) / Complex.Gamma (1 / 2 + a)
        * (Complex.Gamma (1 / 2 + a) / (Real.pi : ℂ)
          * (Complex.sin ((Real.pi : ℂ) * a) * UC a z + UC a (-z)))
      = ((Real.pi : ℂ) / Complex.Gamma (1 / 2 + a) * (Complex.Gamma (1 / 2 + a) / (Real.pi : ℂ)))
        * (Complex.sin ((Real.pi : ℂ) * a) * UC a z + UC a (-z)) from by ring, hcancel, one_mul]
  ring

end FLMF.ParabolicCylinder

end

section

/-!
# Parabolic cylinder `U` — real/complex bridge (DLMF §12.2 ↔ §15.12)

The Frameworks layer (`Ch15AsymptoticApproximations`) defines the complex
comparison function `complexParabolicCylinderU` from scratch, because the layer
order Methods → Frameworks → Functions forbids it from importing the Functions
layer.  This file closes the duplication downward: the Functions-layer real
`U(a,x)` (DLMF 12.2.6–7 via the even/odd Kummer basis, `Basic.lean`) is the
restriction of the Frameworks-layer complex comparison function to real
arguments.

The two definitions are term-for-term the same formula; the proof pushes the
`ℝ → ℂ` cast through `exp`, `Γ`, real `rpow` → complex `cpow` (base `2 > 0`),
and the Kummer sum (`kummerM_ofReal`).  Note the sign convention: the real `U`
writes `+ (−C₂)·w₂` where the complex definition writes `− C₂·odd` — the same
value.
-/

open FLMF.Hypergeometric

namespace FLMF.ParabolicCylinder

-- no-dlmf: real↔complex scalar-tower bridge between the Functions-layer `U`
-- and the Frameworks-layer comparison function, no DLMF counterpart
/-- The real parabolic cylinder function `U(a,x)` (DLMF 12.2.6–7) is the
restriction to real arguments of the complex comparison function
`complexParabolicCylinderU` of DLMF §15.12. -/
theorem U_ofReal (a x : ℝ) :
    ((U a x : ℝ) : ℂ) = complexParabolicCylinderU (a : ℂ) (x : ℂ) := by
  unfold U complexParabolicCylinderU pcfEven pcfOdd
  push_cast [← Complex.Gamma_ofReal, Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2),
    kummerM_ofReal, Complex.ofReal_exp]
  ring

end FLMF.ParabolicCylinder

end

section

/-!
# Parabolic cylinder functions (chapter — DLMF §12)

Solutions of the parabolic cylinder (Weber) equation `w'' − (¼x² + a)w = 0`:
the even/odd fundamental pair `w₁, w₂` and the standard functions `U`, `V`
(DLMF §12.2, §12.4), built on the confluent hypergeometric framework `₁F₁`.
-/

end
