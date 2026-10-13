import FLMF.Frameworks.Hypergeometric.Kummer
import FLMF.Methods.BranchAlgebra
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Tricomi's confluent hypergeometric function `U(a;b;z)`, complex argument
(framework — DLMF 13.2.42)

`FLMF.Hypergeometric.tricomiU` (`Tricomi.lean`) is **real by design**: it is the
DLMF 13.4.4 Laplace integral
`U(a;b;x) = Γ(a)⁻¹ ∫₀^∞ e^{−xt} t^{a−1}(1+t)^{b−a−1} dt`, an intrinsically
half-line object, with junk value `0` off `a > 0 ∧ x > 0`.  Every DLMF display
whose `U` carries a *complex* argument — DLMF 7.11.5 and 7.18.10 among them —
is therefore inexpressible with it.  This module supplies the complex twin.

## Why the connection formula and not the integral

Three candidate complexifications were weighed.

* **Straight-ray Laplace integral.**  `Γ(a)⁻¹ ∫₀^∞ e^{−zt} t^{a−1}(1+t)^{b−a−1} dt`
  converges exactly on `Re z > 0`.  Honest, and definitionally parallel to the
  real form — but the §7 applications feed it `z²`, and `Re (z²) > 0` is the
  *quarter* plane `|ph z| < π/4`, strictly **narrower** than the half-plane
  `|ph z| < π/2` on which DLMF's own displays hold.  It would buy a complex
  statement at the price of a domain narrower than the DLMF display.
* **Rotated-ray Laplace integral.**  Integrating along `t = s·e^{−i(ph z)/2}`
  reaches the whole cut plane, but every downstream use then needs
  contour-rotation invariance (Cauchy on a circular sector with vanishing arcs)
  before analyticity — and even after that, each §7 identity needs a separate
  analytic-continuation transfer.
* **Kummer's connection formula, DLMF 13.2.42** — the route taken here.  For `b`
  off the integers, `M(a,b,z)` and `z^{1−b} M(a−b+1,2−b,z)` are the standard
  basis of solutions of Kummer's equation at the regular singular point `z = 0`,
  and `U` is the combination

  `U(a,b,z) = Γ(1−b)/Γ(a−b+1) · M(a,b,z) + Γ(b−1)/Γ(a) · z^{1−b} · M(a−b+1,2−b,z)`.

  `kummerM` is already generic over a complete normed algebra
  (`Kummer.lean`), so `M` over `ℂ` is free and entire; the only branch is the
  principal `z^{1−b}`, which puts `U` on `ℂ ∖ (−∞,0]` — **exactly DLMF's
  principal-branch domain** — and makes holomorphy there immediate.

## Honest domain and junk values

`tricomiUC a b z` returns the 13.2.42 combination when

* `z ∈ Complex.slitPlane` (i.e. `z ∉ (−∞, 0]`, so the principal `z^{1−b}` is the
  DLMF principal branch), **and**
* `b` is off the integers (13.2.42 fails at integer `b`, where the second
  solution acquires a logarithm),

and the junk value `0` otherwise.  A `def` cannot carry hypotheses and `sorry`
is forbidden in `def` bodies, so this is the repo's standard junk-guard pattern
(`tricomiU` itself is guarded the same way).  Unguard with `tricomiUC_of_mem`.

Note that the `Γ`-quotients need no side conditions: Lean's `Complex.Gamma`
takes the value `0` at its poles, so `Γ(1−b)/Γ(a−b+1)` and `Γ(b−1)/Γ(a)`
already evaluate to the correct limits `Γ(1−b)·(1/Γ(a−b+1))` and
`Γ(b−1)·(1/Γ(a))` when `a−b+1` or `a` is a nonpositive integer (`1/Γ` is entire
and vanishes there), which is the standard reading of 13.2.42.

## What is *not* proved here

The identification of `tricomiUC` with the real `tricomiU` on the positive axis,
`tricomiUC a b (x : ℝ) = (tricomiU a b x : ℂ)` for `a, x > 0` and `b` off the
integers, **is** the real case of DLMF 13.2.42 (equivalently: that the 13.4.4
Laplace integral equals the 13.2.42 combination).  That is a Frameworks-level
theorem in its own right — the standard proof runs through Kummer's ODE, the
Wronskian of the `M`-pair, and the `x → 0⁺` asymptotics of the integral — and it
is deliberately *not* attempted here.  Instead, agreement is established on
exactly the slices the §7 applications use, downstream in
`FLMF/Functions/Error/ComplexTricomi.lean` (`tricomiUC_ofReal_repErfc_slice`,
`tricomiUC_ofReal_erfc_slice`), where it follows from the already-proven real and
complex `erfc`/`iⁿerfc` representations.  Those slices cover
`(a, b) = (n/2+1/2, 1/2)`, `(1/2, 1/2)` and `(1, 3/2)` at every `x > 0`, so the
definition is pinned to the real `U` where it is used and nowhere silently
assumed elsewhere.

Main results:

* `tricomiUC` — the function (complex form, DLMF 13.2.42).
* `tricomiUC_of_mem` — the unguard lemma.
* `tricomiUC_eq_zero_of_notMem_slitPlane`, `tricomiUC_eq_zero_of_intCast` — the
  junk values, stated explicitly.
* `differentiableAt_tricomiUC`, `differentiableOn_tricomiUC` — holomorphy on the
  cut plane for `b` off the integers.
-/

noncomputable section

open Set

namespace FLMF.Hypergeometric

/-! ### The definition -/

open scoped Classical in
/-- **Tricomi's confluent hypergeometric function `U(a;b;z)` for a complex
argument**, on the principal branch, given by Kummer's connection formula:

`U(a,b,z) = Γ(1−b)/Γ(a−b+1)·M(a,b,z) + Γ(b−1)/Γ(a)·z^{1−b}·M(a−b+1,2−b,z)`.

Here `M = ₁F₁ = kummerM` and `z^{1−b}` is the **principal** power
`exp((1−b)·Log z)`.  The formula is valid for `b` off the integers (at integer
`b` the second solution of Kummer's equation carries a logarithm) and for `z` in
the slit plane `ℂ ∖ (−∞,0]`, which is DLMF's principal-branch domain; outside
that domain the junk value `0` is returned (`def`s cannot carry hypotheses).
Unguard with `tricomiUC_of_mem`.

The real, positive-axis form built from the Laplace integral 13.4.4 is
`FLMF.Hypergeometric.tricomiU`; see the module docstring for the relationship
between the two (and for what is, and is not, proved about it).

DLMF 13.2.42.
DAG: E-13.2.42.
Verified: verified (tier2)
-/
def tricomiUC (a b z : ℂ) : ℂ :=
  if z ∈ Complex.slitPlane ∧ ∀ k : ℤ, b ≠ (k : ℂ) then
    Complex.Gamma (1 - b) / Complex.Gamma (a - b + 1) * kummerM a b z
      + Complex.Gamma (b - 1) / Complex.Gamma a * z ^ (1 - b)
          * kummerM (a - b + 1) (2 - b) z
  else 0

/-! ### Unguarding and junk values -/

-- no-dlmf: unguard lemma for the junk-guarded `tricomiUC`; the DLMF 13.2.42
-- surface is the definition itself
/-- **Unguard `tricomiUC`.**  On its honest domain — `z` off the cut `(−∞,0]`
and `b` off the integers — `tricomiUC` is the 13.2.42 combination. -/
theorem tricomiUC_of_mem {a b z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) :
    tricomiUC a b z =
      Complex.Gamma (1 - b) / Complex.Gamma (a - b + 1) * kummerM a b z
        + Complex.Gamma (b - 1) / Complex.Gamma a * z ^ (1 - b)
            * kummerM (a - b + 1) (2 - b) z := by
  classical
  rw [tricomiUC, if_pos ⟨hz, hb⟩]

-- no-dlmf: junk value off the principal-branch domain, no DLMF counterpart
/-- The junk value on the cut: `tricomiUC a b z = 0` for `z ∈ (−∞, 0]`. -/
theorem tricomiUC_eq_zero_of_notMem_slitPlane {a b z : ℂ}
    (hz : z ∉ Complex.slitPlane) : tricomiUC a b z = 0 := by
  classical
  rw [tricomiUC, if_neg (fun h => hz h.1)]

-- no-dlmf: junk value at integer `b` (13.2.42 degenerates there), no DLMF
-- counterpart
/-- The junk value at integer `b`, where 13.2.42 degenerates (the second
solution of Kummer's equation acquires a logarithm): `tricomiUC a k z = 0`. -/
theorem tricomiUC_eq_zero_of_intCast {a z : ℂ} (k : ℤ) :
    tricomiUC a (k : ℂ) z = 0 := by
  classical
  rw [tricomiUC, if_neg (fun h => h.2 k rfl)]

/-! ### Half-integer regularity witnesses

The `b` values arising in DLMF §7 are `1/2` and `3/2`, both half-odd-integers,
hence off the integers; these are the corresponding guard witnesses. -/

-- no-dlmf: arithmetic guard witness, no DLMF counterpart
/-- A half-odd-integer is not an integer: `m + 1/2 ≠ k` in `ℂ`. -/
theorem intCast_add_half_ne_intCast (m k : ℤ) : ((m : ℂ) + 1 / 2) ≠ (k : ℂ) := by
  intro h
  have hre : (m : ℝ) + 1 / 2 = (k : ℝ) := by
    have := congrArg Complex.re h
    simpa using this
  have h2 : ((2 * m + 1 : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (2 * m + 1 : ℤ) = 2 * k := Int.cast_injective h2
  omega

-- no-dlmf: arithmetic guard witness for `b = 1/2`, no DLMF counterpart
/-- `b = 1/2` is off the integers. -/
theorem half_ne_intCast (k : ℤ) : (1 / 2 : ℂ) ≠ (k : ℂ) := by
  have h := intCast_add_half_ne_intCast 0 k
  simpa using h

-- no-dlmf: arithmetic guard witness for `b = 3/2`, no DLMF counterpart
/-- `b = 3/2` is off the integers. -/
theorem three_half_ne_intCast (k : ℤ) : (3 / 2 : ℂ) ≠ (k : ℂ) := by
  have h := intCast_add_half_ne_intCast 1 k
  have he : ((1 : ℤ) : ℂ) + 1 / 2 = (3 / 2 : ℂ) := by push_cast; ring
  rwa [he] at h

/-! ### Holomorphy on the cut plane -/

-- no-dlmf: entirety of the Kummer sum over ℂ (radius `⊤`), no DLMF identity
-- number
/-- `M(a;b;·) = ₁F₁ a b` is entire over `ℂ`. -/
theorem differentiable_kummerM_complex (a b : ℂ) :
    Differentiable ℂ (fun w : ℂ => kummerM a b w) := by
  have h := (kummerM_hasFPowerSeriesOnBall (𝔸 := ℂ) (a := a) (b := b)).differentiableOn
  have huniv : Metric.eball (0 : ℂ) ⊤ = Set.univ := by ext y; simp
  rw [huniv, differentiableOn_univ] at h
  exact h

-- no-dlmf: holomorphy of `U` on its principal-branch domain; consequence of
-- DLMF 13.2.42, not itself a numbered display
/-- `U(a;b;·)` is holomorphic at every point of the cut plane `ℂ ∖ (−∞,0]`, for
`b` off the integers: the `M`-factors are entire and the only branch is the
principal `z^{1−b}`, holomorphic off the cut. -/
theorem differentiableAt_tricomiUC {a b z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hb : ∀ k : ℤ, b ≠ (k : ℂ)) : DifferentiableAt ℂ (tricomiUC a b) z := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => kummerM a b w) z :=
    differentiable_kummerM_complex a b z
  have h2 : DifferentiableAt ℂ (fun w : ℂ => kummerM (a - b + 1) (2 - b) w) z :=
    differentiable_kummerM_complex _ _ z
  have h3 : DifferentiableAt ℂ (fun w : ℂ => w ^ (1 - b)) z :=
    (Complex.hasStrictDerivAt_cpow_const hz).hasDerivAt.differentiableAt
  have hform : DifferentiableAt ℂ (fun w : ℂ =>
      Complex.Gamma (1 - b) / Complex.Gamma (a - b + 1) * kummerM a b w
        + Complex.Gamma (b - 1) / Complex.Gamma a * w ^ (1 - b)
            * kummerM (a - b + 1) (2 - b) w) z :=
    (h1.const_mul _).add ((h3.const_mul _).mul h2)
  refine hform.congr_of_eventuallyEq ?_
  filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
  exact tricomiUC_of_mem hw hb

-- no-dlmf: holomorphy of `U` on its principal-branch domain, set form
/-- `U(a;b;·)` is holomorphic on the cut plane `ℂ ∖ (−∞,0]`, for `b` off the
integers. -/
theorem differentiableOn_tricomiUC {a b : ℂ} (hb : ∀ k : ℤ, b ≠ (k : ℂ)) :
    DifferentiableOn ℂ (tricomiUC a b) Complex.slitPlane :=
  fun _ hz => (differentiableAt_tricomiUC hz hb).differentiableWithinAt

end FLMF.Hypergeometric
