import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Generalized Laguerre polynomials `L_n^α`

We define the generalized (associated) Laguerre polynomials `L_n^α(x)` following
the explicit representation DLMF 18.5.12:

```
L_n^α(x) = Σ_{k=0}^{n} (-1)^k * C(n+α, n-k) * x^k / k!
```

where the (generalized) binomial coefficient is expressed via the ascending
Pochhammer (rising factorial) symbol

```
C(n+α, n-k) = (α + k + 1)_{n-k} / (n-k)!.
```

We work over `ℝ` with a real parameter `α`, packaging the result as a real
polynomial `Polynomial.laguerre α n : ℝ[X]`.

The special cases (DLMF 18.5: Table / 18.3) are

* `L_0^α(x) = 1`;
* `L_1^α(x) = 1 + α - x`.
-/

namespace Polynomial

open scoped BigOperators

open Finset

/-- The generalized Laguerre polynomial `L_n^α` over `ℝ`, defined via the
explicit sum DLMF 18.5.12.  Here `α : ℝ` is the parameter and `n : ℕ` the
degree. -/
noncomputable def laguerre (α : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (n + 1),
    C ((-1) ^ k * ((ascPochhammer ℝ (n - k)).eval (α + (k : ℝ) + 1))
        / (k.factorial * (n - k).factorial : ℝ)) * X ^ k

-- no-dlmf: P_0 normalization (L_0^α = 1)
/-- `L_0^α = 1`. -/
@[simp]
theorem laguerre_zero (α : ℝ) : laguerre α 0 = 1 := by
  simp [laguerre, ascPochhammer_zero]

/-- **DLMF §18.5(iv)** (the `L_1^{(α)}` line of the *generalized* Laguerre list,
equation 18.5.17_5): `L_1^α(x) = -x + α + 1`, i.e. `L_1^α = (1 + α) - X`.

Tagged at section level because the tag extractor cannot address sub-numbered
ids: the plain-numbered 18.5.17 is the **ordinary** list
`L_n(x) = L_n^{(0)}(x)` (`L_1(x) = -x + 1`), which is the `α = 0` case of the
statement below.

DAG: E-18.5.
Fidelity: tier1 PASS
Verified: unverified
-/
@[simp]
theorem laguerre_one (α : ℝ) : laguerre α 1 = C (1 + α) - X := by
  rw [laguerre, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [map_add, map_one]
  norm_num [ascPochhammer_one, ascPochhammer_zero]
  ring
