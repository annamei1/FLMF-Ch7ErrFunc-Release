import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.EReal.Basic
import FLMF.Functions.OrthogonalPolynomials.Zeros

/-!
# Chebyshev polynomials of the first kind: zeros are real, simple, and in the support

This file packages DLMF 18.2(vi) for the Chebyshev polynomials of the first kind
`T_n`.  The zeros of `T_n` are

  x_k = cos ((2k+1) π / (2n)),   k = 0, …, n-1,

and we prove that:

* there are exactly `n` of them (`FLMF.Chebyshev.card_roots_T`),
* each is a simple root (`FLMF.Chebyshev.rootMultiplicity_Tzero`),
* all of them lie in the open support interval `(-1, 1)`
  (`FLMF.Chebyshev.roots_T_mem_Ioo`).

We also record that the multiset of roots has no repetition
(`FLMF.Chebyshev.roots_T_nodup`), i.e. the zeros are real and simple.

The explicit description of `(T ℝ n).roots` is taken from Mathlib; here we collect the
location/cardinality/simplicity facts in the DLMF form.
-/

open Real Polynomial

namespace FLMF.Chebyshev

open Polynomial.Chebyshev

-- no-dlmf: packaging def for the explicit zero `cos((2k+1)π/(2n))`; the zero facts are DLMF 18.2 below.
/-- The explicit zero of `T_n` of index `k`. -/
noncomputable def Tzero (n k : ℕ) : ℝ := cos ((2 * k + 1) * π / (2 * n))

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — the zeros of `T_n` are exactly the `n` real numbers
`cos ((2k+1) π / (2n))`, `k = 0, …, n-1`.
-/
theorem roots_T_eq (n : ℕ) :
    (T ℝ n).roots =
      ((Finset.range n).image (fun k : ℕ => Tzero n k)).val :=
  roots_T_real n

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — each zero of `T_n` (for `k < n`) is a root.
-/
theorem isRoot_Tzero {n k : ℕ} (hk : k < n) : (T ℝ n).IsRoot (Tzero n k) := by
  rw [← mem_roots (T_ne_zero ℝ n), roots_T_real, Finset.mem_val, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr hk, rfl⟩

-- no-dlmf: explicit Chebyshev zeros — no numbered DLMF display; consequence of 18.5.1
/-- **(DLMF 18.2(vi))** — each zero of `T_n` is a **simple** root: its multiplicity is `1`.
-/
theorem rootMultiplicity_Tzero {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (Tzero n k) = 1 :=
  rootMultiplicity_T_real hk

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`); the cited
-- section states the general orthogonal-polynomial zero properties for p_n(x),
-- not Chebyshev-specific ones; faithful surface is
-- FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq (whose
-- `roots.toFinset.card = n ∧ Multiset.card roots = n` jointly give no-repetition).
/-- The zeros of `T_n` (as a multiset of roots) have no repetition:
the zeros are **real and simple**. -/
theorem roots_T_nodup (n : ℕ) : (T ℝ n).roots.Nodup := by
  rw [roots_T_real]
  exact (Finset.range n).image (fun k : ℕ => Tzero n k) |>.nodup

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`); faithful surface is
-- FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq
/-- `T_n` has exactly `n` distinct real zeros (accounting for the full multiplicity
budget). This is the cardinality part of the general orthogonal-polynomial zeros
property, specialized to the Chebyshev polynomials of the first kind.
-/
theorem card_roots_T (n : ℕ) : Multiset.card (T ℝ n).roots = n := by
  rw [roots_T_real, ← Finset.card_def, Finset.card_image_of_injOn, Finset.card_range]
  exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

-- no-dlmf: instance of DLMF 18.2(vi) (fixed family: Chebyshev `T_n`, orthogonality interval (-1,1)); faithful surface is orthogonalPoly_roots_mem_Ioo
/-- **All zeros of `T_n` lie in the open support interval `(-1, 1)`.**
This is the location part of the general orthogonal-polynomial zeros property,
specialized to the Chebyshev polynomials of the first kind.
-/
theorem roots_T_mem_Ioo {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ (T ℝ n).roots) :
    x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [roots_T_real, Finset.mem_val, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  -- the angle θ = (2k+1)π/(2n) lies strictly in (0, π), so cos θ ∈ (-1,1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set θ : ℝ := (2 * (k : ℝ) + 1) * π / (2 * n) with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθlt : θ < π := by
    rw [hθ, div_lt_iff₀ (by positivity)]
    have hkn : (2 * (k : ℝ) + 1) < 2 * n := by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
      nlinarith
    nlinarith [Real.pi_pos]
  have hmemTzero : Tzero n k = cos θ := rfl
  -- cos π = -1 < cos θ since cos is strictly antitone on [0,π]
  have hlow : (-1 : ℝ) < cos θ := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨hθpos.le, hθlt.le⟩)
      (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_refl π⟩) hθlt
    rw [Real.cos_pi] at this
    exact this
  -- cos θ < cos 0 = 1
  have hhigh : cos θ < 1 := by
    have := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), Real.pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hθpos.le, hθlt.le⟩) hθpos
    rw [Real.cos_zero] at this
    exact this
  rw [Set.mem_Ioo]
  exact ⟨hlow, hhigh⟩

section GeneralLocation

open MeasureTheory
open FLMF.Functions.OrthogonalPolynomials

/-- **DLMF 18.2(vi)** — location of the zeros of a general orthogonal polynomial:
if `P` has degree `n ≥ 1` and is orthogonal to every polynomial of lower degree
against a positive nondegenerate measure `μ` (finite total mass and finite moments
of every order, matching the Lebesgue–Stieltjes setting of §18.2(i)) whose mass
lies in the closed orthogonality interval `[a, b]` — endpoints taken in `EReal`,
so unbounded orthogonality intervals are included — then every real zero of `P`
lies in the *open* interval `(a, b)`.

Together with `FLMF.Functions.OrthogonalPolynomials.OrthogonalPoly.card_roots_eq`
(the "real and simple, exactly `n`" half) this renders the full §18.2(vi) zeros
statement; `roots_T_mem_Ioo` above is its Chebyshev-`T` instance.

DAG: E-18.2.
Fidelity: tier1 unable (membership)
Verified: unverified
-/
theorem orthogonalPoly_roots_mem_Ioo {μ : Measure ℝ} {n : ℕ}
    (O : OrthogonalPoly μ n) (hn : 1 ≤ n)
    (hfin : IsFiniteMeasure μ)
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    {a b : EReal} (hsupp : ∀ᵐ y ∂μ, (↑(y : ℝ) : EReal) ∈ Set.Icc a b)
    {x : ℝ} (hx : x ∈ O.P.roots) :
    (x : EReal) ∈ Set.Ioo a b := by
  sorry

end GeneralLocation

end FLMF.Chebyshev
