import FLMF.Frameworks.Hypergeometric.GaussConnectionGeneral
import FLMF.Frameworks.Hypergeometric.Olver
import FLMF.Methods.BranchAlgebra

/-!
# A principal two-chart continuation of the Gauss hypergeometric function

The power-series realization `₂F₁` is honest only on `‖z‖ < 1`.  This file
constructs the first canonical piece of its principal analytic continuation by
gluing that series to the Kummer basis at `z = 1` (DLMF 15.10.13--15.10.14),
using the proved complex connection formula (DLMF 15.10.21) on the overlap.

The resulting domain is the union of the unit disc and the principal slit
disc `‖z - 1‖ < 1`, `1 - z ∈ Complex.slitPlane`.  It is intentionally *not*
called a continuation on the full DLMF slit plane: further charts, in
particular the infinity charts, still have to be glued.
-/

noncomputable section

open Set Metric FLMF.Methods.BranchAlgebra

namespace FLMF.Hypergeometric

/-- The principal Kummer chart at `z = 1`: the open unit disc around `1`, cut
along the ray `[1,∞)` so that `(1-z)^(c-a-b)` uses the principal branch. -/
def gaussOneChart : Set ℂ :=
  ball (1 : ℂ) 1 ∩ {z : ℂ | 1 - z ∈ Complex.slitPlane}

-- no-dlmf: topology bookkeeping for the principal `z = 1` chart
theorem isOpen_gaussOneChart : IsOpen gaussOneChart :=
  isOpen_ball.inter (Complex.isOpen_slitPlane.preimage
    (continuous_const.sub continuous_id))

/-- The domain currently covered by the principal Gauss continuation: the
defining unit disc together with the principal Kummer chart at `z = 1`. -/
def gaussPrincipalFirstDomain : Set ℂ :=
  ball (0 : ℂ) 1 ∪ gaussOneChart

-- no-dlmf: topology bookkeeping for the two-chart domain
theorem isOpen_gaussPrincipalFirstDomain : IsOpen gaussPrincipalFirstDomain :=
  isOpen_ball.union isOpen_gaussOneChart

/-- The connection-formula realization of `₂F₁(a,b;c;z)` in the principal
Kummer chart at `z = 1`.  Its two summands are the local solutions `w₃,w₄`
from DLMF 15.10.13--15.10.14 with the coefficients of DLMF 15.10.21.

DLMF 15.10.21.
-/
-- DAG: E-15.10.21.
-- Verified: unverified (tier2 DIVERGES)
def gaussAtOneExtension (a b c : ℂ) (z : ℂ) : ℂ :=
  Complex.Gamma c * Complex.Gamma (c - a - b)
      / (Complex.Gamma (c - a) * Complex.Gamma (c - b)) * gaussW3 a b c z
    + Complex.Gamma c * Complex.Gamma (a + b - c)
      / (Complex.Gamma a * Complex.Gamma b) * gaussW4 a b c z

-- no-dlmf: analyticity certificate for the DLMF 15.10.13--15.10.14 chart
/-- The `z = 1` connection-formula realization is analytic throughout its
principal slit chart. -/
theorem analyticOnNhd_gaussAtOneExtension {a b c : ℂ}
    (h3 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    (h4 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧
        (kn : ℂ) ≠ -(c - a - b + 1)) :
    AnalyticOnNhd ℂ (gaussAtOneExtension a b c) gaussOneChart := by
  intro z hz
  have hz1 : ‖1 - z‖ < 1 := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
    exact mem_ball_iff_norm.mp hz.1
  have hw3 := gaussW3_analyticAt h3 hz1
  have hw4 := gaussW4_analyticAt h4 hz1 hz.2
  exact (analyticAt_const.mul hw3).add (analyticAt_const.mul hw4)

-- no-dlmf: overlap certificate supplied by DLMF 15.10.21
/-- On the overlap of the unit disc and the principal `z = 1` chart, the
connection-formula realization agrees with the defining Gauss series. -/
theorem gaussAtOneExtension_eq_series {a b c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    EqOn (gaussAtOneExtension a b c) (₂F₁ a b c)
      (ball (0 : ℂ) 1 ∩ gaussOneChart) := by
  intro z hz
  have hz0 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
  have hz1 : ‖z - 1‖ < 1 := mem_ball_iff_norm.mp hz.2.1
  symm
  simpa [gaussAtOneExtension, gaussW3, gaussW4] using
    ordinaryHypergeometric_one_sub_connection_complex hc hs hz0 hz1

/-- The canonical first-stage principal continuation of the Gauss function.
It uses the defining series on `‖z‖ < 1` and the connection-formula chart
elsewhere.  Its certified mathematical domain is
`gaussPrincipalFirstDomain`; values outside that domain are unspecified. -/
def gaussPrincipalFirst (a b c : ℂ) (z : ℂ) : ℂ :=
  by
    classical
    exact if z ∈ ball (0 : ℂ) 1 then ₂F₁ a b c z else gaussAtOneExtension a b c z

-- no-dlmf: restriction of the glued continuation to its defining chart
theorem gaussPrincipalFirst_eq_series (a b c : ℂ) :
    EqOn (gaussPrincipalFirst a b c) (₂F₁ a b c) (ball (0 : ℂ) 1) := by
  intro z hz
  simp [gaussPrincipalFirst, hz]

-- no-dlmf: restriction of the glued continuation to the `z = 1` chart
theorem gaussPrincipalFirst_eq_atOne {a b c : ℂ}
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    EqOn (gaussPrincipalFirst a b c) (gaussAtOneExtension a b c)
      gaussOneChart := by
  intro z hz
  by_cases hz0 : z ∈ ball (0 : ℂ) 1
  · rw [gaussPrincipalFirst, if_pos hz0]
    exact (gaussAtOneExtension_eq_series hc hs ⟨hz0, hz⟩).symm
  · simp [gaussPrincipalFirst, hz0]

-- no-dlmf: analytic gluing certificate for the first principal continuation
/-- The first-stage principal Gauss continuation is analytic on the union of
its two charts. -/
theorem analyticOnNhd_gaussPrincipalFirst {a b c : ℂ}
    (habc : ∀ kn : ℕ,
      (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c)
    (h3 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    (h4 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧
        (kn : ℂ) ≠ -(c - a - b + 1))
    (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (gaussPrincipalFirst a b c) gaussPrincipalFirstDomain := by
  have hseries := analyticOnNhd_ordinaryHypergeometric habc
  have hone := analyticOnNhd_gaussAtOneExtension h3 h4
  have hagree := gaussAtOneExtension_eq_series (fun k => (habc k).2.2) hs
  intro z hz
  by_cases hz0 : z ∈ ball (0 : ℂ) 1
  · refine (hseries z hz0).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hz0] with w hw
    simp [gaussPrincipalFirst, hw]
  · have hz1 : z ∈ gaussOneChart := hz.resolve_left hz0
    refine (hone z hz1).congr ?_
    filter_upwards [isOpen_gaussOneChart.mem_nhds hz1] with w hw
    by_cases hw0 : w ∈ ball (0 : ℂ) 1
    · simp [gaussPrincipalFirst, hw0, (hagree ⟨hw0, hw⟩).symm]
    · simp [gaussPrincipalFirst, hw0]

/-! ### The regular-parameter Olver continuation -/

-- no-dlmf: termwise series expansion of Olver's DLMF 15.2.2 definition
theorem olverHypergeometric_eq_tsum (a b c z : ℂ) :
    olverHypergeometric a b c z =
      ∑' n : ℕ, olverHypergeometricCoefficient a b c n * z ^ n := by
  unfold olverHypergeometric
  exact tsum_congr fun n => by
    rw [olverHypergeometricSeries, FormalMultilinearSeries.ofScalars_apply_eq]
    simp [smul_eq_mul]

-- no-dlmf: Gamma pole avoidance after a natural-number shift
private theorem Gamma_add_nat_ne_zero {c : ℂ} (hc : ∀ m : ℕ, c ≠ -m) (n : ℕ) :
    Complex.Gamma (c + n) ≠ 0 := by
  refine Complex.Gamma_ne_zero ?_
  intro m hm
  apply hc (m + n)
  push_cast
  linear_combination hm

-- no-dlmf: coefficient bridge between DLMF 15.2.1 and 15.2.2
private theorem ordinary_term_eq_Gamma_mul_olver {a b c z : ℂ}
    (hc : ∀ m : ℕ, c ≠ -m) (n : ℕ) :
    ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a *
        (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval c)⁻¹) * z ^ n
      = Complex.Gamma c * (olverHypergeometricCoefficient a b c n * z ^ n) := by
  have hpoch := ascPochhammer_eval_eq_Gamma_div c n hc
  have hGc : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero hc
  have hGcn : Complex.Gamma (c + n) ≠ 0 := Gamma_add_nat_ne_zero hc n
  rw [hpoch]
  dsimp [olverHypergeometricCoefficient]
  field_simp

/-- At regular lower parameters, the Gauss and Olver series have their exact
classical normalization `₂F₁(a,b;c;z) = Γ(c) 𝐅(a,b;c;z)`. -/
theorem ordinaryHypergeometric_eq_Gamma_mul_olver {a b c z : ℂ}
    (hc : ∀ m : ℕ, c ≠ -m) :
    ₂F₁ a b c z = Complex.Gamma c * olverHypergeometric a b c z := by
  rw [show (₂F₁ a b c z : ℂ) = ∑' n : ℕ,
      ((n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a *
        (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval c)⁻¹) * z ^ n by
      simpa [smul_eq_mul] using congrFun (ordinaryHypergeometric_eq_tsum a b c) z,
    olverHypergeometric_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => ordinary_term_eq_Gamma_mul_olver hc n

/-- The first principal continuation of Olver's regularized Gauss function at
regular `c`, obtained by dividing the certified Gauss continuation by `Γ(c)`.
The singular lower-parameter case needs a separate parameter-limit gluing
argument and is intentionally not claimed here. -/
def olverPrincipalFirst (a b c z : ℂ) : ℂ :=
  (Complex.Gamma c)⁻¹ * gaussPrincipalFirst a b c z

-- no-dlmf: restriction of the regular-parameter Olver continuation to its series
theorem olverPrincipalFirst_eq_series {a b c : ℂ}
    (hc : ∀ m : ℕ, c ≠ -m) :
    EqOn (olverPrincipalFirst a b c) (olverHypergeometric a b c)
      (ball (0 : ℂ) 1) := by
  intro z hz
  rw [olverPrincipalFirst, gaussPrincipalFirst_eq_series a b c hz,
    ordinaryHypergeometric_eq_Gamma_mul_olver hc]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.Gamma_ne_zero hc), one_mul]

-- no-dlmf: analyticity of the regular-parameter Olver continuation
theorem analyticOnNhd_olverPrincipalFirst {a b c : ℂ}
    (habc : ∀ kn : ℕ,
      (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -c)
    (h3 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    (h4 : ∀ kn : ℕ,
      (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧
        (kn : ℂ) ≠ -(c - a - b + 1))
    (hs : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    AnalyticOnNhd ℂ (olverPrincipalFirst a b c) gaussPrincipalFirstDomain := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_gaussPrincipalFirst habc h3 h4 hs z hz)

end FLMF.Hypergeometric

end
