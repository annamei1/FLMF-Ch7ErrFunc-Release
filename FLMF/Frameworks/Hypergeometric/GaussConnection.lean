import FLMF.Frameworks.Hypergeometric.GaussContinuation
import FLMF.Frameworks.Hypergeometric.GaussValues
import FLMF.Methods.BranchAlgebra
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The `z = 1` connection formula for `₂F₁` (framework — DLMF 15.10.21 / 15.8.4)

The two-term connection formula between the `z = 0` and `z = 1` solution bases
of the hypergeometric equation (DLMF 15.10.1):

  `₂F₁(a,b;c;z) = [Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))] · ₂F₁(a,b;a+b−c+1;1−z)`
  `             + [Γ(c)Γ(a+b−c)/(Γ(a)Γ(b))] · (1−z)^{c−a−b} · ₂F₁(c−a,c−b;c−a−b+1;1−z)`

(DLMF 15.10.21: `w₁ = A·w₃ + B·w₄` with `w₃`, `w₄` the Kummer solutions
15.10.13/15.10.14 at `z = 1`; equivalently 15.8.4 in **F**-normalized form.)

**Proved here for real parameters** in the regime
`0 < b < c < min(1, a+1)`, `c − a − b > 0`, `a` off the nonpositive integers,
on the lens `ball 0 1 ∩ ball 1 1 ⊂ ℂ` — the honest restricted instance
(`Re(c−a−b) > 0` so both boundary limits exist); the equation *form* is the
full DLMF 15.10.21.

**Route** (the C2 Phase-2 lens argument, consuming `M-ode-continuation` and
`M-branch-algebra`):

1. `gaussODE_comp_one_sub` — the Gauss ODE's `z ↦ 1−z` symmetry
   (`c ↦ a+b−c+1`): reflected solutions solve the reflected equation.
2. `gaussODE_second_solution` — `u^{γ−1}·₂F₁(α,β;γ;u)` solves the
   hypergeometric equation with parameters `(α+1−γ, β+1−γ, 2−γ)` on the slit
   unit disc (the second Kummer solution at `u = 0`, DLMF 15.10.12).
3. Both RHS terms solve DLMF 15.10.1 on the lens (`gaussW3_ode`,
   `gaussW4_ode`); `Methods/ODEContinuation`'s 1-jet uniqueness
   (`linODE2_eqOn_of_jet_eq'`) reduces the identity to jet-matching.
4. The Wronskian of `(w₃, w₄)` is pinned nonzero near `z = 1`
   (`W = (1−z)^{c−a−b−1}·Ψ(z)` with `Ψ(1) = −(c−a−b) ≠ 0`), so the difference
   `Φ = w₁ − A·w₃ − B·w₄` decomposes as `γ₃w₃ + γ₄w₄` by Cramer + uniqueness.
5. `z → 1⁻`: Gauss's theorem (DLMF 15.4.20, `GaussValues`) plus
   `(1−z)^{c−a−b} → 0` forces `γ₃ = 0`; `z → 0⁺`: Gauss's theorem at the
   reflected parameters plus Euler's reflection formula (the sine identity
   `sin π(c−a) sin π(c−b) − sin πa sin πb = sin π(c−a−b) sin πc`) forces
   `γ₄ = 0`.

## References

- DLMF §15.10(ii): https://dlmf.nist.gov/15.10#ii (15.10.21)
- DLMF §15.8(i): https://dlmf.nist.gov/15.8#i (15.8.4)
-/

noncomputable section

open Set Metric Filter Topology FLMF.Methods.ODEContinuation FLMF.Methods.BranchAlgebra
open scoped Real

namespace FLMF.Hypergeometric

/-! ### `ofReal` bridges for the Gauss series -/

-- no-dlmf: cast bookkeeping, no DLMF counterpart
/-- `ascPochhammer` evaluation commutes with the `ℝ → ℂ` cast. -/
theorem ascPochhammer_eval_ofReal (x : ℝ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (x : ℂ) = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  have h : ((ascPochhammer ℝ n).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) x)
      = (algebraMap ℝ ℂ) ((ascPochhammer ℝ n).eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [ascPochhammer_map] at h
  simpa using h

-- no-dlmf: cast bookkeeping, no DLMF counterpart
/-- The Gauss series coefficients commute with the `ℝ → ℂ` cast. -/
theorem ordinaryHypergeometricCoefficient_ofReal (a b c : ℝ) (n : ℕ) :
    ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n
      = ((ordinaryHypergeometricCoefficient a b c n : ℝ) : ℂ) := by
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_eval_ofReal]
  push_cast
  ring

-- no-dlmf: cast bookkeeping, no DLMF counterpart
/-- On the open unit disc, `₂F₁` at real parameters and a real argument is the
cast of the real `₂F₁`. -/
theorem ordinaryHypergeometric_ofReal {a b c : ℝ}
    (habc : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -c)
    {x : ℝ} (hx : |x| < 1) :
    ₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) = ((₂F₁ a b c x : ℝ) : ℂ) := by
  have habcC : ∀ kn : ℕ, (kn : ℂ) ≠ -(a : ℂ) ∧ (kn : ℂ) ≠ -(b : ℂ) ∧ (kn : ℂ) ≠ -(c : ℂ) :=
    fun kn => ⟨fun h => (habc kn).1 (by exact_mod_cast h),
      fun h => (habc kn).2.1 (by exact_mod_cast h),
      fun h => (habc kn).2.2 (by exact_mod_cast h)⟩
  have hR := ordinaryHypergeometric_hasSum a b c habc (x := x) (by rwa [Real.norm_eq_abs])
  have hC := ordinaryHypergeometric_hasSum (a : ℂ) (b : ℂ) (c : ℂ) habcC (x := (x : ℂ))
    (by rwa [Complex.norm_real])
  have hRC := Complex.hasSum_ofReal.mpr hR
  have he : (fun n : ℕ => ((ordinaryHypergeometricCoefficient a b c n * x ^ n : ℝ) : ℂ))
      = fun n : ℕ => ordinaryHypergeometricCoefficient (a : ℂ) (b : ℂ) (c : ℂ) n * (x : ℂ) ^ n := by
    funext n
    rw [ordinaryHypergeometricCoefficient_ofReal a b c n]
    push_cast
    ring
  rw [he] at hRC
  exact hC.unique hRC

/-! ### The `z ↦ 1 − z` symmetry of the hypergeometric equation -/

-- no-dlmf: ODE-transport infrastructure (the symmetry behind DLMF 15.10.13), no equation number
/-- **Reflection transport for the Gauss ODE.** If `f` solves the hypergeometric
equation with parameters `(a, b, a+b−c+1)` on an open set `S`, then
`z ↦ f(1−z)` solves the equation with parameters `(a, b, c)` at any `z` with
`1 − z ∈ S` — the `z ↦ 1−z` symmetry of DLMF 15.10.1. -/
theorem gaussODE_comp_one_sub {a b c : ℂ} {S : Set ℂ} (hS : IsOpen S) {f : ℂ → ℂ}
    (hf1 : ∀ u ∈ S, DifferentiableAt ℂ f u)
    (hf2 : ∀ u ∈ S, DifferentiableAt ℂ (deriv f) u)
    (hode : ∀ u ∈ S, u * (1 - u) * deriv (deriv f) u
      + ((a + b - c + 1) - (a + b + 1) * u) * deriv f u - a * b * f u = 0)
    {z : ℂ} (hz : 1 - z ∈ S) :
    z * (1 - z) * deriv (deriv (fun w => f (1 - w))) z
      + (c - (a + b + 1) * z) * deriv (fun w => f (1 - w)) z
      - a * b * f (1 - z) = 0 := by
  have hSop : IsOpen {w : ℂ | 1 - w ∈ S} := hS.preimage (continuous_const.sub continuous_id)
  have hd1 : ∀ w, 1 - w ∈ S → HasDerivAt (fun v => f (1 - v)) (-(deriv f (1 - w))) w := by
    intro w hw
    have h := ((hf1 _ hw).hasDerivAt).comp w ((hasDerivAt_id w).const_sub 1)
    simpa [Function.comp_def, mul_neg_one] using h
  have hev : deriv (fun v => f (1 - v)) =ᶠ[𝓝 z] fun w => -(deriv f (1 - w)) := by
    filter_upwards [hSop.mem_nhds hz] with w hw
    exact (hd1 w hw).deriv
  have hd2 : HasDerivAt (fun w => -(deriv f (1 - w))) (deriv (deriv f) (1 - z)) z := by
    have h := ((hf2 _ hz).hasDerivAt).comp z ((hasDerivAt_id z).const_sub 1)
    have h' := h.neg
    simpa [Function.comp_def, mul_neg_one] using h'
  have hD1 : deriv (fun v => f (1 - v)) z = -(deriv f (1 - z)) := (hd1 z hz).deriv
  have hD2 : deriv (deriv (fun v => f (1 - v))) z = deriv (deriv f) (1 - z) := by
    rw [hev.deriv_eq]
    exact hd2.deriv
  rw [hD1, hD2]
  linear_combination hode (1 - z) hz

-- no-dlmf: chain-rule helper, no DLMF counterpart
/-- Derivative of a reflected function: `(f(1−·))'(z) = −f'(1−z)`. -/
theorem deriv_comp_one_sub {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (1 - z)) :
    deriv (fun w => f (1 - w)) z = -(deriv f (1 - z)) := by
  have h := (hf.hasDerivAt).comp z ((hasDerivAt_id z).const_sub 1)
  have h' : HasDerivAt (fun w => f (1 - w)) (deriv f (1 - z) * (-1)) z := by
    simpa [Function.comp_def] using h
  rw [h'.deriv]
  ring

/-! ### The second Kummer solution at `z = 0` (DLMF 15.10.12) -/

-- no-dlmf: product-rule helper on the slit plane, no DLMF counterpart
/-- Derivative of `w ↦ w^σ · G(w)` at a slit-plane point. -/
theorem deriv_cpow_mul {G : ℂ → ℂ} {σ u : ℂ} (hG : DifferentiableAt ℂ G u)
    (hsl : u ∈ Complex.slitPlane) :
    deriv (fun w : ℂ => w ^ σ * G w) u = σ * u ^ (σ - 1) * G u + u ^ σ * deriv G u := by
  have hpow : HasDerivAt (fun w : ℂ => w ^ σ) (σ * u ^ (σ - 1) * 1) u :=
    (hasDerivAt_id u).cpow_const hsl
  have h : HasDerivAt (fun w : ℂ => w ^ σ * G w)
      (σ * u ^ (σ - 1) * 1 * G u + u ^ σ * deriv G u) u := hpow.mul hG.hasDerivAt
  rw [h.deriv]
  ring

/-- **The second Kummer solution solves the hypergeometric equation**
(DLMF 15.10.12: the second fundamental solution `w₂` of DLMF 15.10.1 at
`z = 0`): on the slit unit disc,
`u^{γ−1} · ₂F₁(α,β;γ;u)` solves the hypergeometric equation with parameters
`(α+1−γ, β+1−γ, 2−γ)` — equivalently, `z^{1−c}·₂F₁(a−c+1,b−c+1;2−c;z)` solves
the `(a,b,c)` equation, which is precisely the assertion of 15.10.12 as a
member of the §15.10(i) fundamental pair. Only `γ` (the analogue of the lower
`c`-parameter of `₂F₁ α β γ`) need be off the nonpositive integers, matching
DLMF 15.2.1's existence convention for `F(α,β;γ;·)`; `α`, `β` are unrestricted
(as in `ordinaryHypergeometric_ode_of_c`).

DLMF 15.10.12.
Fidelity: tier1 PASS
Verified: unverified
DAG: E-15.10.12.
-/
theorem gaussODE_second_solution {α β γ : ℂ}
    (hc : ∀ kn : ℕ, (kn : ℂ) ≠ -γ)
    {u : ℂ} (hu : ‖u‖ < 1) (hsl : u ∈ Complex.slitPlane) :
    u * (1 - u) * deriv (deriv (fun w : ℂ => w ^ (γ - 1) * ₂F₁ α β γ w)) u
      + ((2 - γ) - ((α + 1 - γ) + (β + 1 - γ) + 1) * u)
        * deriv (fun w : ℂ => w ^ (γ - 1) * ₂F₁ α β γ w) u
      - (α + 1 - γ) * (β + 1 - γ) * (u ^ (γ - 1) * ₂F₁ α β γ u) = 0 := by
  classical
  set G : ℂ → ℂ := (₂F₁ α β γ : ℂ → ℂ) with hGdef
  set V : Set ℂ := ball (0 : ℂ) 1 ∩ Complex.slitPlane with hVdef
  have hVo : IsOpen V := isOpen_ball.inter Complex.isOpen_slitPlane
  have huV : u ∈ V := ⟨mem_ball_zero_iff.mpr hu, hsl⟩
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hsl
  have hGa : AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) :=
    analyticOnNhd_ordinaryHypergeometric_of_c α β γ hc
  have hGd : AnalyticOnNhd ℂ (deriv G) (ball (0 : ℂ) 1) := hGa.deriv
  -- first derivative on V
  have hw2d : ∀ v ∈ V, HasDerivAt (fun w : ℂ => w ^ (γ - 1) * G w)
      (((γ - 1) * v ^ (γ - 1 - 1) * 1) * G v + v ^ (γ - 1) * deriv G v) v := by
    intro v hv
    have hpow : HasDerivAt (fun w : ℂ => w ^ (γ - 1)) ((γ - 1) * v ^ (γ - 1 - 1) * 1) v :=
      (hasDerivAt_id v).cpow_const hv.2
    exact hpow.mul (hGa v hv.1).differentiableAt.hasDerivAt
  have hd1val : deriv (fun w : ℂ => w ^ (γ - 1) * G w) u
      = ((γ - 1) * u ^ (γ - 1 - 1) * 1) * G u + u ^ (γ - 1) * deriv G u := (hw2d u huV).deriv
  -- second derivative at u
  have hDD : deriv (deriv (fun w : ℂ => w ^ (γ - 1) * G w)) u
      = (γ - 1) * ((γ - 1 - 1) * u ^ (γ - 1 - 1 - 1)) * G u
        + 2 * ((γ - 1) * u ^ (γ - 1 - 1)) * deriv G u
        + u ^ (γ - 1) * deriv (deriv G) u := by
    have hev : deriv (fun w : ℂ => w ^ (γ - 1) * G w) =ᶠ[𝓝 u]
        fun v => ((γ - 1) * v ^ (γ - 1 - 1) * 1) * G v + v ^ (γ - 1) * deriv G v := by
      filter_upwards [hVo.mem_nhds huV] with v hv
      exact (hw2d v hv).deriv
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun v : ℂ => v ^ (γ - 1 - 1)) ((γ - 1 - 1) * u ^ (γ - 1 - 1 - 1) * 1) u :=
      (hasDerivAt_id u).cpow_const hsl
    have h2 : HasDerivAt (fun v : ℂ => v ^ (γ - 1)) ((γ - 1) * u ^ (γ - 1 - 1) * 1) u :=
      (hasDerivAt_id u).cpow_const hsl
    have hGu : HasDerivAt G (deriv G u) u := (hGa u huV.1).differentiableAt.hasDerivAt
    have hGu' : HasDerivAt (deriv G) (deriv (deriv G) u) u :=
      (hGd u huV.1).differentiableAt.hasDerivAt
    have hA : HasDerivAt (fun v : ℂ => (γ - 1) * v ^ (γ - 1 - 1) * 1)
        ((γ - 1) * ((γ - 1 - 1) * u ^ (γ - 1 - 1 - 1) * 1) * 1) u :=
      (h1.const_mul (γ - 1)).mul_const (1 : ℂ)
    have htot : HasDerivAt
        (fun v : ℂ => (γ - 1) * v ^ (γ - 1 - 1) * 1 * G v + v ^ (γ - 1) * deriv G v)
        ((γ - 1) * ((γ - 1 - 1) * u ^ (γ - 1 - 1 - 1) * 1) * 1 * G u
            + (γ - 1) * u ^ (γ - 1 - 1) * 1 * deriv G u
          + ((γ - 1) * u ^ (γ - 1 - 1) * 1 * deriv G u + u ^ (γ - 1) * deriv (deriv G) u)) u :=
      (hA.mul hGu).add (h2.mul hGu')
    rw [htot.deriv]
    ring
  -- the hypergeometric equation for G
  have hodeG := ordinaryHypergeometric_ode_of_c α β γ hc hu
  rw [← hGdef] at hodeG
  -- normalize exponents to the common factor u^(γ-2-1)... rewrite powers
  have e0 : u ^ (γ - 1 - 1) = u ^ (γ - 1 - 1 - 1) * u := by
    conv_lhs => rw [show γ - 1 - 1 = (γ - 1 - 1 - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have e1 : u ^ (γ - 1) = u ^ (γ - 1 - 1 - 1) * u * u := by
    conv_lhs => rw [show γ - 1 = (γ - 1 - 1 - 1) + 1 + 1 by ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_add _ _ hu0, Complex.cpow_one]
  rw [hDD, hd1val, e0, e1]
  linear_combination (u ^ (γ - 1 - 1 - 1) * u * u) * hodeG

/-! ### The Kummer solutions `w₃`, `w₄` at `z = 1` (DLMF 15.10.13, 15.10.14) -/

/-- The Kummer solution `w₃(z) = ₂F₁(a,b;a+b−c+1;1−z)` at `z = 1`
(DLMF 15.10.13, first branch).

DLMF 15.10.13.
-/
-- DAG: E-15.10.13.
-- Verified: verified (tier2)
def gaussW3 (a b c : ℂ) : ℂ → ℂ := fun z => ₂F₁ a b (a + b - c + 1) (1 - z)

/-- The Kummer solution `w₄(z) = (1−z)^{c−a−b} ₂F₁(c−a,c−b;c−a−b+1;1−z)` at
`z = 1` (DLMF 15.10.14, first branch).

DLMF 15.10.14.
-/
-- DAG: E-15.10.14.
-- Verified: verified (tier2)
def gaussW4 (a b c : ℂ) : ℂ → ℂ :=
  fun z => (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)

-- no-dlmf: solution-verification for DLMF §15.10(i) (w₃ solves 15.10.1), no equation number
/-- `w₃` solves the hypergeometric equation (DLMF 15.10.1) wherever `‖1−z‖ < 1`. -/
theorem gaussW3_ode {a b c : ℂ}
    (h3 : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) :
    z * (1 - z) * deriv (deriv (gaussW3 a b c)) z
      + (c - (a + b + 1) * z) * deriv (gaussW3 a b c) z - a * b * gaussW3 a b c z = 0 := by
  have hFa : AnalyticOnNhd ℂ (₂F₁ a b (a + b - c + 1) : ℂ → ℂ) (ball (0 : ℂ) 1) :=
    analyticOnNhd_ordinaryHypergeometric h3
  have hFd : AnalyticOnNhd ℂ (deriv (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (ball (0 : ℂ) 1) :=
    hFa.deriv
  have h := gaussODE_comp_one_sub (S := ball (0 : ℂ) 1) isOpen_ball
    (fun u hu => (hFa u hu).differentiableAt)
    (fun u hu => (hFd u hu).differentiableAt)
    (fun u hu => ordinaryHypergeometric_ode a b (a + b - c + 1) h3 (mem_ball_zero_iff.mp hu))
    (z := z) (mem_ball_zero_iff.mpr hz)
  simpa [gaussW3] using h

-- no-dlmf: solution-verification for DLMF §15.10(i) (w₄ solves 15.10.1), no equation number
/-- `w₄` solves the hypergeometric equation (DLMF 15.10.1) wherever `‖1−z‖ < 1`
and `1 − z` avoids the branch cut. -/
theorem gaussW4_ode {a b c : ℂ}
    (h4 : ∀ kn : ℕ, (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧ (kn : ℂ) ≠ -(c - a - b + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) (hsl : 1 - z ∈ Complex.slitPlane) :
    z * (1 - z) * deriv (deriv (gaussW4 a b c)) z
      + (c - (a + b + 1) * z) * deriv (gaussW4 a b c) z - a * b * gaussW4 a b c z = 0 := by
  set G : ℂ → ℂ := (₂F₁ (c - a) (c - b) (c - a - b + 1) : ℂ → ℂ) with hGdef
  set V : Set ℂ := ball (0 : ℂ) 1 ∩ Complex.slitPlane with hVdef
  have hVo : IsOpen V := isOpen_ball.inter Complex.isOpen_slitPlane
  have hGa : AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) := analyticOnNhd_ordinaryHypergeometric h4
  -- the inner function u ↦ u^(c-a-b) · G(u) is analytic on V
  have hha : AnalyticOnNhd ℂ (fun u : ℂ => u ^ (c - a - b) * G u) V := by
    intro u hu
    exact (analyticAt_id.cpow analyticAt_const hu.2).mul (hGa u hu.1)
  have hhd : AnalyticOnNhd ℂ (deriv (fun u : ℂ => u ^ (c - a - b) * G u)) V := hha.deriv
  -- it solves the (a, b, a+b-c+1)-equation on V, via the second-solution lemma
  have hode : ∀ u ∈ V, u * (1 - u) * deriv (deriv (fun w : ℂ => w ^ (c - a - b) * G w)) u
      + ((a + b - c + 1) - (a + b + 1) * u) * deriv (fun w : ℂ => w ^ (c - a - b) * G w) u
      - a * b * (fun w : ℂ => w ^ (c - a - b) * G w) u = 0 := by
    intro u hu
    have h2 := gaussODE_second_solution (α := c - a) (β := c - b) (γ := c - a - b + 1)
      (fun k => (h4 k).2.2) (mem_ball_zero_iff.mp hu.1) hu.2
    have hfeq : (fun w : ℂ => w ^ (c - a - b + 1 - 1) * ₂F₁ (c - a) (c - b) (c - a - b + 1) w)
        = fun w : ℂ => w ^ (c - a - b) * G w := by
      funext w
      rw [show c - a - b + 1 - 1 = c - a - b by ring, hGdef]
    rw [hfeq, show c - a - b + 1 - 1 = c - a - b by ring] at h2
    linear_combination h2
  have h := gaussODE_comp_one_sub (S := V) hVo
    (fun u hu => (hha u hu).differentiableAt)
    (fun u hu => (hhd u hu).differentiableAt)
    hode (z := z) ⟨mem_ball_zero_iff.mpr hz, hsl⟩
  simpa [gaussW4, hGdef] using h

/-! ### Linearity of the hypergeometric equation -/

-- no-dlmf: linearity infrastructure for DLMF 15.10.1, no equation number
/-- Linear combinations of solutions of the hypergeometric equation solve it. -/
theorem gaussODE_linComb {a b c : ℂ} {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (α β : ℂ)
    (hfode : ∀ z ∈ U, z * (1 - z) * deriv (deriv f) z
      + (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0)
    (hgode : ∀ z ∈ U, z * (1 - z) * deriv (deriv g) z
      + (c - (a + b + 1) * z) * deriv g z - a * b * g z = 0) :
    ∀ z ∈ U, z * (1 - z) * deriv (deriv (fun w => α * f w + β * g w)) z
      + (c - (a + b + 1) * z) * deriv (fun w => α * f w + β * g w) z
      - a * b * (α * f z + β * g z) = 0 := by
  intro z hz
  have hd : ∀ w ∈ U, HasDerivAt (fun v => α * f v + β * g v)
      (α * deriv f w + β * deriv g w) w := by
    intro w hw
    exact (((hf w hw).differentiableAt.hasDerivAt).const_mul α).add
      (((hg w hw).differentiableAt.hasDerivAt).const_mul β)
  have hD1 : deriv (fun v => α * f v + β * g v) z = α * deriv f z + β * deriv g z :=
    (hd z hz).deriv
  have hev : deriv (fun v => α * f v + β * g v) =ᶠ[𝓝 z]
      fun w => α * deriv f w + β * deriv g w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hd w hw).deriv
  have hd2 : HasDerivAt (fun w => α * deriv f w + β * deriv g w)
      (α * deriv (deriv f) z + β * deriv (deriv g) z) z :=
    (((hf.deriv z hz).differentiableAt.hasDerivAt).const_mul α).add
      (((hg.deriv z hz).differentiableAt.hasDerivAt).const_mul β)
  have hD2 : deriv (deriv (fun v => α * f v + β * g v)) z
      = α * deriv (deriv f) z + β * deriv (deriv g) z := by
    rw [hev.deriv_eq]
    exact hd2.deriv
  rw [hD1, hD2]
  linear_combination α * hfode z hz + β * hgode z hz

/-! ### Analyticity and derivatives of `w₃`, `w₄` -/

-- no-dlmf: analyticity bookkeeping for DLMF 15.10.13, no equation number
/-- `w₃` is analytic wherever `‖1 − z‖ < 1`. -/
theorem gaussW3_analyticAt {a b c : ℂ}
    (h3 : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) : AnalyticAt ℂ (gaussW3 a b c) z := by
  have hF := analyticOnNhd_ordinaryHypergeometric h3 (1 - z) (mem_ball_zero_iff.mpr hz)
  have hin : AnalyticAt ℂ (fun w : ℂ => 1 - w) z := analyticAt_const.sub analyticAt_id
  have hcomp := hF.comp hin
  simpa [gaussW3, Function.comp_def] using hcomp

-- no-dlmf: analyticity bookkeeping for DLMF 15.10.14, no equation number
/-- `w₄` is analytic wherever `‖1 − z‖ < 1` and `1 − z` avoids the branch cut. -/
theorem gaussW4_analyticAt {a b c : ℂ}
    (h4 : ∀ kn : ℕ, (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧ (kn : ℂ) ≠ -(c - a - b + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) (hsl : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (gaussW4 a b c) z := by
  have hpow : AnalyticAt ℂ (fun w : ℂ => (1 - w) ^ (c - a - b)) z :=
    analyticAt_one_sub_cpow hsl (c - a - b)
  have hF := analyticOnNhd_ordinaryHypergeometric h4 (1 - z) (mem_ball_zero_iff.mpr hz)
  have hin : AnalyticAt ℂ (fun w : ℂ => 1 - w) z := analyticAt_const.sub analyticAt_id
  have hcomp := hF.comp hin
  have := hpow.mul hcomp
  simpa [gaussW4, Function.comp_def] using this

-- no-dlmf: chain-rule bookkeeping for DLMF 15.10.13, no equation number
/-- Derivative of `w₃`: `w₃'(z) = −(₂F₁(a,b;a+b−c+1;·))'(1−z)`. -/
theorem gaussW3_deriv {a b c : ℂ}
    (h3 : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(a + b - c + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) :
    deriv (gaussW3 a b c) z = -(deriv (₂F₁ a b (a + b - c + 1) : ℂ → ℂ) (1 - z)) := by
  have hF := analyticOnNhd_ordinaryHypergeometric h3 (1 - z) (mem_ball_zero_iff.mpr hz)
  have h := deriv_comp_one_sub (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) hF.differentiableAt
  simpa [gaussW3] using h

-- no-dlmf: chain-rule bookkeeping for DLMF 15.10.14, no equation number
/-- Derivative of `w₄` on the slit disc around `z = 1`. -/
theorem gaussW4_deriv {a b c : ℂ}
    (h4 : ∀ kn : ℕ, (kn : ℂ) ≠ -(c - a) ∧ (kn : ℂ) ≠ -(c - b) ∧ (kn : ℂ) ≠ -(c - a - b + 1))
    {z : ℂ} (hz : ‖1 - z‖ < 1) (hsl : 1 - z ∈ Complex.slitPlane) :
    deriv (gaussW4 a b c) z
      = -((c - a - b) * (1 - z) ^ (c - a - b - 1) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)
          + (1 - z) ^ (c - a - b)
            * deriv (₂F₁ (c - a) (c - b) (c - a - b + 1) : ℂ → ℂ) (1 - z)) := by
  have hG := analyticOnNhd_ordinaryHypergeometric h4 (1 - z) (mem_ball_zero_iff.mpr hz)
  have hh : DifferentiableAt ℂ
      (fun u : ℂ => u ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) u) (1 - z) :=
    ((analyticAt_id.cpow analyticAt_const hsl).mul hG).differentiableAt
  have h1 := deriv_comp_one_sub
    (f := fun u : ℂ => u ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) u) hh
  have h2 := deriv_cpow_mul (G := (₂F₁ (c - a) (c - b) (c - a - b + 1) : ℂ → ℂ))
    (σ := c - a - b) hG.differentiableAt hsl
  rw [h2] at h1
  have hfun : (fun w => (fun u : ℂ => u ^ (c - a - b)
      * ₂F₁ (c - a) (c - b) (c - a - b + 1) u) (1 - w)) = gaussW4 a b c := by
    funext w
    simp only [gaussW4]
  rw [hfun] at h1
  exact h1

/-! ### A Wronskian-normalization point near `z = 1` -/

-- no-dlmf: basis-nondegeneracy infrastructure for DLMF §15.10(ii), no equation number
/-- There is a real point `x₀ ∈ (0,1)` of the lens where the Wronskian-type
determinant `w₃·w₄' − w₃'·w₄` of the `z = 1` Kummer basis is nonzero: near
`z = 1` one has `W = (1−z)^{c−a−b−1}·Ψ(z)` with `Ψ` continuous and
`Ψ(1) = −(c−a−b) ≠ 0`. Real parameters, `0 < c − a − b`. -/
theorem exists_gaussW_wronskian_ne_zero {a b c : ℝ}
    (h3 : ∀ kn : ℕ, (kn : ℂ) ≠ -(a : ℂ) ∧ (kn : ℂ) ≠ -(b : ℂ)
      ∧ (kn : ℂ) ≠ -((a : ℂ) + b - c + 1))
    (h4 : ∀ kn : ℕ, (kn : ℂ) ≠ -((c : ℂ) - a) ∧ (kn : ℂ) ≠ -((c : ℂ) - b)
      ∧ (kn : ℂ) ≠ -((c : ℂ) - a - b + 1))
    (hs : 0 < c - a - b) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ < 1 ∧
      gaussW3 (a : ℂ) b c (x₀ : ℂ) * deriv (gaussW4 (a : ℂ) b c) (x₀ : ℂ)
        - deriv (gaussW3 (a : ℂ) b c) (x₀ : ℂ) * gaussW4 (a : ℂ) b c (x₀ : ℂ) ≠ 0 := by
  set F3 : ℂ → ℂ := (₂F₁ (a : ℂ) (b : ℂ) ((a : ℂ) + b - c + 1) : ℂ → ℂ) with hF3def
  set F4 : ℂ → ℂ := (₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) : ℂ → ℂ) with hF4def
  have hF3a := analyticOnNhd_ordinaryHypergeometric h3
  have hF4a := analyticOnNhd_ordinaryHypergeometric h4
  rw [← hF3def] at hF3a
  rw [← hF4def] at hF4a
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- the normalized Wronskian Ψ, continuous at 1 with Ψ(1) = −(c−a−b) ≠ 0
  set Ψ : ℂ → ℂ := fun z => -(((c : ℂ) - a - b) * F3 (1 - z) * F4 (1 - z))
      - (1 - z) * (F3 (1 - z) * deriv F4 (1 - z) - deriv F3 (1 - z) * F4 (1 - z)) with hΨdef
  have t1 : Tendsto (fun z : ℂ => 1 - z) (𝓝 (1 : ℂ)) (𝓝 0) := by
    have hcont : Continuous (fun z : ℂ => 1 - z) := continuous_const.sub continuous_id
    have h := hcont.tendsto (1 : ℂ)
    simpa using h
  have tF3 : Tendsto (fun z : ℂ => F3 (1 - z)) (𝓝 (1 : ℂ)) (𝓝 (F3 0)) := by
    have := ((hF3a 0 h0b).continuousAt.tendsto).comp t1
    simpa [Function.comp_def] using this
  have tF4 : Tendsto (fun z : ℂ => F4 (1 - z)) (𝓝 (1 : ℂ)) (𝓝 (F4 0)) := by
    have := ((hF4a 0 h0b).continuousAt.tendsto).comp t1
    simpa [Function.comp_def] using this
  have tF3' : Tendsto (fun z : ℂ => deriv F3 (1 - z)) (𝓝 (1 : ℂ)) (𝓝 (deriv F3 0)) := by
    have := ((hF3a.deriv 0 h0b).continuousAt.tendsto).comp t1
    simpa [Function.comp_def] using this
  have tF4' : Tendsto (fun z : ℂ => deriv F4 (1 - z)) (𝓝 (1 : ℂ)) (𝓝 (deriv F4 0)) := by
    have := ((hF4a.deriv 0 h0b).continuousAt.tendsto).comp t1
    simpa [Function.comp_def] using this
  have hΨt : Tendsto Ψ (𝓝 (1 : ℂ))
      (𝓝 (-(((c : ℂ) - a - b) * F3 0 * F4 0)
        - 0 * (F3 0 * deriv F4 0 - deriv F3 0 * F4 0))) := by
    rw [hΨdef]
    exact (((tF3.const_mul _).mul tF4).neg).sub
      (t1.mul ((tF3.mul tF4').sub (tF3'.mul tF4)))
  have hF30 : F3 0 = 1 := ordinaryHypergeometric_zero _ _ _
  have hF40 : F4 0 = 1 := ordinaryHypergeometric_zero _ _ _
  have hs0 : ((c : ℂ) - a - b) ≠ 0 := by
    rw [show (c : ℂ) - a - b = ((c - a - b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr hs.ne'
  have hΨt' : Tendsto Ψ (𝓝 (1 : ℂ)) (𝓝 (-((c : ℂ) - a - b))) := by
    have hval : -(((c : ℂ) - a - b) * F3 0 * F4 0)
        - 0 * (F3 0 * deriv F4 0 - deriv F3 0 * F4 0) = -((c : ℂ) - a - b) := by
      rw [hF30, hF40]
      ring
    rwa [hval] at hΨt
  have hev : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), Ψ z ≠ 0 :=
    hΨt'.eventually_ne (neg_ne_zero.mpr hs0)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  -- the real point x₀ = 1 − min ε 1 / 2
  set δ : ℝ := min ε 1 with hδdef
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set x₀ : ℝ := 1 - δ / 2 with hx₀def
  have hx₀0 : 0 < x₀ := by rw [hx₀def]; linarith
  have hx₀1 : x₀ < 1 := by rw [hx₀def]; linarith
  refine ⟨x₀, hx₀0, hx₀1, ?_⟩
  -- basic facts at x₀
  have hdist : dist ((x₀ : ℝ) : ℂ) 1 < ε := by
    rw [Complex.dist_eq, show ((x₀ : ℝ) : ℂ) - 1 = ((x₀ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    rw [hx₀def]
    rw [show (1 : ℝ) - δ / 2 - 1 = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    calc δ / 2 < δ := by linarith
      _ ≤ ε := min_le_left _ _
  have hΨx₀ : Ψ ((x₀ : ℝ) : ℂ) ≠ 0 := hball hdist
  have hu_norm : ‖1 - ((x₀ : ℝ) : ℂ)‖ < 1 := by
    rw [show 1 - ((x₀ : ℝ) : ℂ) = ((1 - x₀ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hx₀def]
    linarith
  have hu_slit : 1 - ((x₀ : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    rw [show 1 - ((x₀ : ℝ) : ℂ) = ((1 - x₀ : ℝ) : ℂ) by push_cast; ring]
    simpa using by linarith [hx₀1]
  have hu0 : (1 : ℂ) - ((x₀ : ℝ) : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hu_slit
  -- rewrite the Wronskian through the derivative formulas
  have hd3 := gaussW3_deriv h3 hu_norm
  have hd4 := gaussW4_deriv h4 hu_norm hu_slit
  rw [hd3, hd4]
  have hW3v : gaussW3 (a : ℂ) b c ((x₀ : ℝ) : ℂ) = F3 (1 - ((x₀ : ℝ) : ℂ)) := by
    rw [gaussW3, hF3def]
  have hW4v : gaussW4 (a : ℂ) b c ((x₀ : ℝ) : ℂ)
      = (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b) * F4 (1 - ((x₀ : ℝ) : ℂ)) := by
    rw [gaussW4, hF4def]
  rw [hW3v, hW4v, ← hF3def, ← hF4def]
  -- W = (1−x₀)^(s−1) · Ψ(x₀) ≠ 0
  have epow : (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b)
      = (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b - 1) * (1 - ((x₀ : ℝ) : ℂ)) := by
    conv_lhs => rw [show (c : ℂ) - a - b = ((c : ℂ) - a - b - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hu0, Complex.cpow_one]
  have hWeq : F3 (1 - ((x₀ : ℝ) : ℂ))
        * -(((c : ℂ) - a - b) * (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b - 1)
            * F4 (1 - ((x₀ : ℝ) : ℂ))
          + (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b) * deriv F4 (1 - ((x₀ : ℝ) : ℂ)))
      - -(deriv F3 (1 - ((x₀ : ℝ) : ℂ)))
        * ((1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b) * F4 (1 - ((x₀ : ℝ) : ℂ)))
      = (1 - ((x₀ : ℝ) : ℂ)) ^ ((c : ℂ) - a - b - 1) * Ψ ((x₀ : ℝ) : ℂ) := by
    rw [hΨdef, epow]
    ring
  rw [hWeq]
  refine mul_ne_zero ?_ hΨx₀
  rw [Ne, Complex.cpow_eq_zero_iff]
  push Not
  intro h
  exact absurd h hu0

/-! ### The connection-coefficient Gamma identity -/

-- no-dlmf: the coefficient identity behind DLMF 15.10.21 (Euler reflection algebra), no equation number
/-- The sine identity `sin π(c−a) sin π(c−b) − sin πa sin πb = sin π(c−a−b) sin πc`
(product-to-sum, one Pythagorean identity). -/
theorem sin_connection_identity (a b c : ℝ) :
    Real.sin (π * (c - a)) * Real.sin (π * (c - b))
      - Real.sin (π * a) * Real.sin (π * b)
      = Real.sin (π * (c - a - b)) * Real.sin (π * c) := by
  rw [show π * (c - a) = π * c - π * a by ring, show π * (c - b) = π * c - π * b by ring,
    show π * (c - a - b) = π * c - π * a - π * b by ring]
  rw [Real.sin_sub (π * c) (π * a), Real.sin_sub (π * c) (π * b),
    Real.sin_sub (π * c - π * a) (π * b), Real.sin_sub (π * c) (π * a),
    Real.cos_sub (π * c) (π * a)]
  linear_combination (Real.sin (π * a) * Real.sin (π * b)) * Real.sin_sq_add_cos_sq (π * c)

-- no-dlmf: sine-nonvanishing helper, no DLMF counterpart
/-- `sin(πt) ≠ 0` for `t ∈ (−1,1) ∖ {0}`. -/
theorem sin_pi_mul_ne_zero {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) (ht0 : t ≠ 0) :
    Real.sin (π * t) ≠ 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · have hpos : 0 < Real.sin (π * (-t)) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (by linarith))
        (by nlinarith [mul_pos Real.pi_pos (show (0 : ℝ) < 1 + t by linarith)])
    have hneg : Real.sin (π * t) = -Real.sin (π * (-t)) := by
      rw [show π * t = -(π * (-t)) by ring, Real.sin_neg]
    rw [hneg]
    exact neg_ne_zero.mpr hpos.ne'
  · exact absurd h ht0
  · exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h)
      (by nlinarith [mul_pos Real.pi_pos (show (0 : ℝ) < 1 - t by linarith)])).ne'

-- no-dlmf: the connection-coefficient identity behind DLMF 15.10.21, no single equation number
/-- **The connection-coefficient identity**: with `A`, `B` the two Gamma-ratio
coefficients of DLMF 15.10.21 and `G₃`, `G₄` the Gauss values (DLMF 15.4.20) of
`w₃`, `w₄` at `z = 0`, one has `A·G₃ + B·G₄ = 1` — Euler's reflection formula
reduces it to the sine identity. -/
theorem gauss_connection_gamma_identity {a b c : ℝ} (ha : ∀ k : ℕ, (k : ℝ) ≠ -a)
    (hb : 0 < b) (hbc : b < c) (hs : a + b < c) (hc1 : c < 1) (hac : c < a + 1) :
    gaussValue a b c * gaussValue a b (a + b - c + 1)
      + Real.Gamma c * Real.Gamma (a + b - c) / (Real.Gamma a * Real.Gamma b)
        * gaussValue (c - a) (c - b) (c - a - b + 1) = 1 := by
  have hs' : 0 < c - a - b := by linarith
  have hc0 : 0 < c := lt_trans hb hbc
  have hb1 : b < 1 := lt_trans hbc hc1
  have hca0 : 0 < c - a := by linarith
  have hca1 : c - a < 1 := by linarith
  have hcb0 : 0 < c - b := by linarith
  have hcb1 : c - b < 1 := by linarith
  have hcab1 : c - a - b < 1 := by linarith
  have ha1 : a < 1 := by linarith
  have ham1 : -1 < a := by linarith
  have ha0 : a ≠ 0 := fun h => ha 0 (by simp [h])
  have habc0 : a + b - c < 0 := by linarith
  have habcm1 : -1 < a + b - c := by linarith
  -- Gamma nonvanishing
  have hΓ : ∀ t : ℝ, 0 < t → Real.Gamma t ≠ 0 := fun t ht => (Real.Gamma_pos_of_pos ht).ne'
  have hΓa : Real.Gamma a ≠ 0 :=
    Real.Gamma_ne_zero fun m h => ha m (by rw [h]; ring)
  have hΓabc : Real.Gamma (a + b - c) ≠ 0 := by
    refine Real.Gamma_ne_zero fun m h => ?_
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm] at h; simp at h; linarith
    · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith [h]
  -- sine nonvanishing
  have hsc : Real.sin (π * c) ≠ 0 := sin_pi_mul_ne_zero (by linarith) hc1 hc0.ne'
  have hss : Real.sin (π * (c - a - b)) ≠ 0 := sin_pi_mul_ne_zero (by linarith) hcab1 hs'.ne'
  have hsca : Real.sin (π * (c - a)) ≠ 0 := sin_pi_mul_ne_zero (by linarith) hca1 hca0.ne'
  have hscb : Real.sin (π * (c - b)) ≠ 0 := sin_pi_mul_ne_zero (by linarith) hcb1 hcb0.ne'
  have hsa : Real.sin (π * a) ≠ 0 := sin_pi_mul_ne_zero ham1 ha1 ha0
  have hsb : Real.sin (π * b) ≠ 0 := sin_pi_mul_ne_zero (by linarith) hb1 hb.ne'
  -- the two product terms in sine form
  have hT1 : gaussValue a b c * gaussValue a b (a + b - c + 1)
      = Real.sin (π * (c - a)) * Real.sin (π * (c - b))
        / (Real.sin (π * c) * Real.sin (π * (c - a - b))) := by
    rw [gaussValue, gaussValue,
      show a + b - c + 1 - a - b = 1 - c by ring,
      show a + b - c + 1 - a = 1 - (c - b) by ring,
      show a + b - c + 1 - b = 1 - (c - a) by ring,
      show a + b - c + 1 = 1 - (c - a - b) by ring]
    rw [div_mul_div_comm,
      show Real.Gamma c * Real.Gamma (c - a - b)
          * (Real.Gamma (1 - (c - a - b)) * Real.Gamma (1 - c))
        = Real.Gamma c * Real.Gamma (1 - c)
          * (Real.Gamma (c - a - b) * Real.Gamma (1 - (c - a - b))) by ring,
      show Real.Gamma (c - a) * Real.Gamma (c - b)
          * (Real.Gamma (1 - (c - b)) * Real.Gamma (1 - (c - a)))
        = Real.Gamma (c - a) * Real.Gamma (1 - (c - a))
          * (Real.Gamma (c - b) * Real.Gamma (1 - (c - b))) by ring,
      Real.Gamma_mul_Gamma_one_sub c, Real.Gamma_mul_Gamma_one_sub (c - a - b),
      Real.Gamma_mul_Gamma_one_sub (c - a), Real.Gamma_mul_Gamma_one_sub (c - b)]
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  have hT2 : Real.Gamma c * Real.Gamma (a + b - c) / (Real.Gamma a * Real.Gamma b)
      * gaussValue (c - a) (c - b) (c - a - b + 1)
      = -(Real.sin (π * a) * Real.sin (π * b))
        / (Real.sin (π * c) * Real.sin (π * (c - a - b))) := by
    rw [gaussValue,
      show c - a - b + 1 - (c - a) - (c - b) = 1 - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring,
      show c - a - b + 1 - (c - b) = 1 - a by ring,
      show c - a - b + 1 = 1 - (a + b - c) by ring]
    rw [div_mul_div_comm,
      show Real.Gamma c * Real.Gamma (a + b - c)
          * (Real.Gamma (1 - (a + b - c)) * Real.Gamma (1 - c))
        = Real.Gamma c * Real.Gamma (1 - c)
          * (Real.Gamma (a + b - c) * Real.Gamma (1 - (a + b - c))) by ring,
      show Real.Gamma a * Real.Gamma b * (Real.Gamma (1 - b) * Real.Gamma (1 - a))
        = Real.Gamma a * Real.Gamma (1 - a) * (Real.Gamma b * Real.Gamma (1 - b)) by ring,
      Real.Gamma_mul_Gamma_one_sub c, Real.Gamma_mul_Gamma_one_sub (a + b - c),
      Real.Gamma_mul_Gamma_one_sub a, Real.Gamma_mul_Gamma_one_sub b]
    have hsabc : Real.sin (π * (a + b - c)) = -Real.sin (π * (c - a - b)) := by
      rw [show π * (a + b - c) = -(π * (c - a - b)) by ring, Real.sin_neg]
    rw [hsabc]
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hT1, hT2]
  field_simp
  linear_combination sin_connection_identity a b c

-- no-dlmf: linearity infrastructure for DLMF 15.10.1, no equation number
/-- The difference of two solutions of the hypergeometric equation solves it. -/
theorem gaussODE_sub {a b c : ℂ} {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfode : ∀ z ∈ U, z * (1 - z) * deriv (deriv f) z
      + (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0)
    (hgode : ∀ z ∈ U, z * (1 - z) * deriv (deriv g) z
      + (c - (a + b + 1) * z) * deriv g z - a * b * g z = 0) :
    ∀ z ∈ U, z * (1 - z) * deriv (deriv (fun w => f w - g w)) z
      + (c - (a + b + 1) * z) * deriv (fun w => f w - g w) z
      - a * b * (f z - g z) = 0 := by
  intro z hz
  have hd : ∀ w ∈ U, HasDerivAt (fun v => f v - g v) (deriv f w - deriv g w) w := fun w hw =>
    ((hf w hw).differentiableAt.hasDerivAt).sub ((hg w hw).differentiableAt.hasDerivAt)
  have hD1 : deriv (fun v => f v - g v) z = deriv f z - deriv g z := (hd z hz).deriv
  have hev : deriv (fun v => f v - g v) =ᶠ[𝓝 z] fun w => deriv f w - deriv g w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hd w hw).deriv
  have hd2 : HasDerivAt (fun w => deriv f w - deriv g w)
      (deriv (deriv f) z - deriv (deriv g) z) z :=
    ((hf.deriv z hz).differentiableAt.hasDerivAt).sub
      ((hg.deriv z hz).differentiableAt.hasDerivAt)
  have hD2 : deriv (deriv (fun v => f v - g v)) z = deriv (deriv f) z - deriv (deriv g) z := by
    rw [hev.deriv_eq]
    exact hd2.deriv
  rw [hD1, hD2]
  linear_combination hfode z hz - hgode z hz

/-! ### The connection formula (DLMF 15.10.21) -/

-- no-dlmf: real/narrowed restriction of DLMF 15.10.21; faithful surface is
-- `ordinaryHypergeometric_one_sub_connection_complex`
/-- **Gauss's `z = 1` connection formula**, proved for real parameters in the
regime `0 < b < c`, `c − a − b > 0`, `c < 1`, `c < a + 1`, `a` off the
nonpositive integers, for `z` in the lens `‖z‖ < 1`, `‖z − 1‖ < 1` (the
`Re(c−a−b) > 0` instance of the general complex formula, on the lens where the
`z = 0` and `z = 1` solution bases overlap):

`₂F₁(a,b;c;z) = [Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))] ₂F₁(a,b;a+b−c+1;1−z)
  + [Γ(c)Γ(a+b−c)/(Γ(a)Γ(b))] (1−z)^{c−a−b} ₂F₁(c−a,c−b;c−a−b+1;1−z)`.

The full complex-parameter statement (DLMF 15.10.21; equivalently DLMF 15.8.4
in **F**-normalized form) is `ordinaryHypergeometric_one_sub_connection_complex`
in `GaussConnectionGeneral.lean`.
-/
theorem ordinaryHypergeometric_one_sub_connection {a b c : ℝ}
    (ha : ∀ k : ℕ, (k : ℝ) ≠ -a) (hb : 0 < b) (hbc : b < c) (hs : a + b < c)
    (hc1 : c < 1) (hac : c < a + 1) {z : ℂ} (hz0 : ‖z‖ < 1) (hz1 : ‖z - 1‖ < 1) :
    ₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) z
      = Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - a - b)
          / (Complex.Gamma ((c : ℂ) - a) * Complex.Gamma ((c : ℂ) - b))
          * ₂F₁ (a : ℂ) (b : ℂ) ((a : ℂ) + b - c + 1) (1 - z)
        + Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + b - c)
          / (Complex.Gamma (a : ℂ) * Complex.Gamma (b : ℂ))
          * ((1 - z) ^ ((c : ℂ) - a - b)
            * ₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) (1 - z)) := by
  classical
  -- ===== basic real inequalities =====
  have hs' : 0 < c - a - b := by linarith
  have hc0 : 0 < c := lt_trans hb hbc
  -- ===== parameter packages =====
  have h1 : ∀ kn : ℕ, (kn : ℂ) ≠ -(a : ℂ) ∧ (kn : ℂ) ≠ -(b : ℂ) ∧ (kn : ℂ) ≠ -(c : ℂ) := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    refine ⟨fun h => ha kn (by exact_mod_cast h), fun h => ?_, fun h => ?_⟩
    · have h' : (kn : ℝ) = -b := by exact_mod_cast h
      linarith
    · have h' : (kn : ℝ) = -c := by exact_mod_cast h
      linarith
  have h3 : ∀ kn : ℕ, (kn : ℂ) ≠ -(a : ℂ) ∧ (kn : ℂ) ≠ -(b : ℂ)
      ∧ (kn : ℂ) ≠ -((a : ℂ) + b - c + 1) := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    refine ⟨(h1 kn).1, (h1 kn).2.1, fun h => ?_⟩
    have h' : (kn : ℝ) = -(a + b - c + 1) := by exact_mod_cast h
    linarith
  have h4 : ∀ kn : ℕ, (kn : ℂ) ≠ -((c : ℂ) - a) ∧ (kn : ℂ) ≠ -((c : ℂ) - b)
      ∧ (kn : ℂ) ≠ -((c : ℂ) - a - b + 1) := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have h' : (kn : ℝ) = -(c - a) := by exact_mod_cast h
      linarith
    · have h' : (kn : ℝ) = -(c - b) := by exact_mod_cast h
      linarith
    · have h' : (kn : ℝ) = -(c - a - b + 1) := by exact_mod_cast h
      linarith
  have h1R : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -c := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    exact ⟨ha kn, fun h => by linarith, fun h => by linarith⟩
  have h3R : ∀ kn : ℕ, (kn : ℝ) ≠ -a ∧ (kn : ℝ) ≠ -b ∧ (kn : ℝ) ≠ -(a + b - c + 1) := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    exact ⟨ha kn, fun h => by linarith, fun h => by linarith⟩
  have h4R : ∀ kn : ℕ, (kn : ℝ) ≠ -(c - a) ∧ (kn : ℝ) ≠ -(c - b)
      ∧ (kn : ℝ) ≠ -(c - a - b + 1) := by
    intro kn
    have hk := Nat.cast_nonneg (α := ℝ) kn
    exact ⟨fun h => by linarith, fun h => by linarith, fun h => by linarith⟩
  -- ===== the lens =====
  set U : Set ℂ := ball (0 : ℂ) 1 ∩ ball (1 : ℂ) 1 with hUdef
  have hUo : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected
  have hzU : z ∈ U := ⟨mem_ball_zero_iff.mpr hz0, by rw [mem_ball_iff_norm]; exact hz1⟩
  have hUfacts : ∀ w ∈ U, ‖w‖ < 1 ∧ ‖1 - w‖ < 1 ∧ 1 - w ∈ Complex.slitPlane := by
    intro w hw
    have h1' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.1
    have h2' : ‖1 - w‖ < 1 := by
      rw [show (1 : ℂ) - w = -(w - 1) by ring, norm_neg]
      exact mem_ball_iff_norm.mp hw.2
    exact ⟨h1', h2', one_sub_mem_slitPlane_of_norm_lt_one h1'⟩
  -- ===== the functions =====
  set A : ℂ := Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - a - b)
      / (Complex.Gamma ((c : ℂ) - a) * Complex.Gamma ((c : ℂ) - b)) with hAdef
  set B : ℂ := Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + b - c)
      / (Complex.Gamma (a : ℂ) * Complex.Gamma (b : ℂ)) with hBdef
  set F1 : ℂ → ℂ := (₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) : ℂ → ℂ) with hF1def
  set w3 : ℂ → ℂ := gaussW3 (a : ℂ) (b : ℂ) (c : ℂ) with hw3def
  set w4 : ℂ → ℂ := gaussW4 (a : ℂ) (b : ℂ) (c : ℂ) with hw4def
  -- ===== analyticity and the ODE on the lens =====
  have hw3a : AnalyticOnNhd ℂ w3 U := fun w hw => gaussW3_analyticAt h3 (hUfacts w hw).2.1
  have hw4a : AnalyticOnNhd ℂ w4 U := fun w hw =>
    gaussW4_analyticAt h4 (hUfacts w hw).2.1 (hUfacts w hw).2.2
  have hF1a : AnalyticOnNhd ℂ F1 U :=
    (analyticOnNhd_ordinaryHypergeometric h1).mono inter_subset_left
  have hw3ode : ∀ w ∈ U, w * (1 - w) * deriv (deriv w3) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv w3 w
      - (a : ℂ) * (b : ℂ) * w3 w = 0 :=
    fun w hw => gaussW3_ode h3 (hUfacts w hw).2.1
  have hw4ode : ∀ w ∈ U, w * (1 - w) * deriv (deriv w4) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv w4 w
      - (a : ℂ) * (b : ℂ) * w4 w = 0 :=
    fun w hw => gaussW4_ode h4 (hUfacts w hw).2.1 (hUfacts w hw).2.2
  have hF1ode : ∀ w ∈ U, w * (1 - w) * deriv (deriv F1) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv F1 w
      - (a : ℂ) * (b : ℂ) * F1 w = 0 :=
    fun w hw => ordinaryHypergeometric_ode (a : ℂ) (b : ℂ) (c : ℂ) h1 (hUfacts w hw).1
  -- ===== Φ = w₁ − (A·w₃ + B·w₄) =====
  set g0 : ℂ → ℂ := fun w => A * w3 w + B * w4 w with hg0def
  have hg0a : AnalyticOnNhd ℂ g0 U := fun w hw =>
    (analyticAt_const.mul (hw3a w hw)).add (analyticAt_const.mul (hw4a w hw))
  have hg0ode : ∀ w ∈ U, w * (1 - w) * deriv (deriv g0) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv g0 w
      - (a : ℂ) * (b : ℂ) * g0 w = 0 :=
    gaussODE_linComb hUo hw3a hw4a A B hw3ode hw4ode
  set Φ : ℂ → ℂ := fun w => F1 w - g0 w with hΦdef
  have hΦa : AnalyticOnNhd ℂ Φ U := hF1a.sub hg0a
  have hΦode : ∀ w ∈ U, w * (1 - w) * deriv (deriv Φ) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv Φ w
      - (a : ℂ) * (b : ℂ) * Φ w = 0 :=
    gaussODE_sub hUo hF1a hg0a hF1ode hg0ode
  -- ===== the Wronskian point and the Cramer coefficients =====
  obtain ⟨x₀, hx₀0, hx₀1, hWr0⟩ := exists_gaussW_wronskian_ne_zero h3 h4 hs'
  rw [← hw3def, ← hw4def] at hWr0
  have hx₀U : ((x₀ : ℝ) : ℂ) ∈ U := by
    constructor
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx₀0]
      exact hx₀1
    · rw [mem_ball_iff_norm, show ((x₀ : ℝ) : ℂ) - 1 = ((x₀ - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), neg_sub]
      linarith
  set Wr : ℂ := w3 ((x₀ : ℝ) : ℂ) * deriv w4 ((x₀ : ℝ) : ℂ)
      - deriv w3 ((x₀ : ℝ) : ℂ) * w4 ((x₀ : ℝ) : ℂ) with hWrdef
  set γ₃ : ℂ := (Φ ((x₀ : ℝ) : ℂ) * deriv w4 ((x₀ : ℝ) : ℂ)
      - w4 ((x₀ : ℝ) : ℂ) * deriv Φ ((x₀ : ℝ) : ℂ)) / Wr with hγ₃def
  set γ₄ : ℂ := (w3 ((x₀ : ℝ) : ℂ) * deriv Φ ((x₀ : ℝ) : ℂ)
      - Φ ((x₀ : ℝ) : ℂ) * deriv w3 ((x₀ : ℝ) : ℂ)) / Wr with hγ₄def
  set gc : ℂ → ℂ := fun w => γ₃ * w3 w + γ₄ * w4 w with hgcdef
  have hgca : AnalyticOnNhd ℂ gc U := fun w hw =>
    (analyticAt_const.mul (hw3a w hw)).add (analyticAt_const.mul (hw4a w hw))
  have hgcode : ∀ w ∈ U, w * (1 - w) * deriv (deriv gc) w
      + ((c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w) * deriv gc w
      - (a : ℂ) * (b : ℂ) * gc w = 0 :=
    gaussODE_linComb hUo hw3a hw4a γ₃ γ₄ hw3ode hw4ode
  -- the jets of Φ and γ₃·w₃ + γ₄·w₄ agree at x₀
  have hgcd : deriv gc ((x₀ : ℝ) : ℂ)
      = γ₃ * deriv w3 ((x₀ : ℝ) : ℂ) + γ₄ * deriv w4 ((x₀ : ℝ) : ℂ) := by
    have hd : HasDerivAt gc
        (γ₃ * deriv w3 ((x₀ : ℝ) : ℂ) + γ₄ * deriv w4 ((x₀ : ℝ) : ℂ)) ((x₀ : ℝ) : ℂ) := by
      rw [hgcdef]
      exact (((hw3a _ hx₀U).differentiableAt.hasDerivAt).const_mul γ₃).add
        (((hw4a _ hx₀U).differentiableAt.hasDerivAt).const_mul γ₄)
    exact hd.deriv
  have hval : Φ ((x₀ : ℝ) : ℂ) = gc ((x₀ : ℝ) : ℂ) := by
    simp only [hgcdef]
    rw [hγ₃def, hγ₄def, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      eq_div_iff hWr0, hWrdef]
    ring
  have hder : deriv Φ ((x₀ : ℝ) : ℂ) = deriv gc ((x₀ : ℝ) : ℂ) := by
    rw [hgcd, hγ₃def, hγ₄def, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      eq_div_iff hWr0, hWrdef]
    ring
  -- ===== 1-jet uniqueness on the lens (Methods/ODEContinuation) =====
  have hEq : Set.EqOn Φ gc U := by
    refine linODE2_eqOn_of_jet_eq' (P := fun w : ℂ => w * (1 - w))
      (Q := fun w : ℂ => (c : ℂ) - ((a : ℂ) + (b : ℂ) + 1) * w)
      (R := fun _ : ℂ => -((a : ℂ) * (b : ℂ))) hUo hUc
      (fun w _ => analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
      (fun w _ => analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (fun w _ => analyticAt_const) ?_ hΦa hgca ?_ ?_ hx₀U hval hder
    · intro w hw
      have hw0 : w ≠ 0 := by
        intro h
        have hmem := mem_ball_iff_norm.mp hw.2
        rw [h] at hmem
        simp at hmem
      have hw1 : (1 : ℂ) - w ≠ 0 := by
        intro h
        have h1' : w = 1 := by linear_combination -h
        have hmem := mem_ball_zero_iff.mp hw.1
        rw [h1'] at hmem
        simp at hmem
      exact mul_ne_zero hw0 hw1
    · intro w hw
      have h := hΦode w hw
      linear_combination h
    · intro w hw
      have h := hgcode w hw
      linear_combination h
  -- ===== the limit x → 1⁻ pins γ₃ = 0 =====
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hG1 := ordinaryHypergeometric_tendsto_gaussValue a b c ha hb hbc hs'
  have hG3 := ordinaryHypergeometric_tendsto_gaussValue a b (a + b - c + 1) ha hb
    (by linarith) (by linarith)
  have hG4 := ordinaryHypergeometric_tendsto_gaussValue (c - a) (c - b) (c - a - b + 1)
    (fun k => by have := Nat.cast_nonneg (α := ℝ) k; intro h; linarith)
    (by linarith) (by linarith) (by linarith)
  have tcast1 : Tendsto (fun x : ℝ => ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have t1z1 : Tendsto (fun x : ℝ => 1 - ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h := tcast1.const_sub (1 : ℂ)
    simpa using h
  have tw3_1 : Tendsto (fun x : ℝ => w3 ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h := ((analyticOnNhd_ordinaryHypergeometric h3 0 h0ball).continuousAt.tendsto).comp t1z1
    have h' : Tendsto (fun x : ℝ => ₂F₁ (a : ℂ) (b : ℂ) ((a : ℂ) + b - c + 1) (1 - ((x : ℝ) : ℂ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (₂F₁ (a : ℂ) (b : ℂ) ((a : ℂ) + b - c + 1) 0)) := by
      simpa [Function.comp_def] using h
    rw [ordinaryHypergeometric_zero] at h'
    exact h'.congr fun x => by simp only [hw3def, gaussW3]
  have tF4_1 : Tendsto (fun x : ℝ =>
      ₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) (1 - ((x : ℝ) : ℂ)))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h := ((analyticOnNhd_ordinaryHypergeometric h4 0 h0ball).continuousAt.tendsto).comp t1z1
    have h' : Tendsto (fun x : ℝ =>
        ₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) (1 - ((x : ℝ) : ℂ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) 0)) := by
      simpa [Function.comp_def] using h
    rwa [ordinaryHypergeometric_zero] at h'
  have tw4_1 : Tendsto (fun x : ℝ => w4 ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hin : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun x : ℝ => 1 - x := continuous_const.sub continuous_id
      have h := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      simpa using h
    have hrpow : Tendsto (fun x : ℝ => (1 - x) ^ (c - a - b)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun t : ℝ => t ^ (c - a - b)) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr hs'.le)
      have h := hcont.tendsto.comp hin
      simpa [Function.comp_def, Real.zero_rpow hs'.ne'] using h
    have hcast : Tendsto (fun x : ℝ => (((1 - x) ^ (c - a - b) : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp hrpow
      simpa [Function.comp_def] using h
    have hprod0 : Tendsto (fun x : ℝ => (((1 - x) ^ (c - a - b) : ℝ) : ℂ)
        * ₂F₁ ((c : ℂ) - a) ((c : ℂ) - b) ((c : ℂ) - a - b + 1) (1 - ((x : ℝ) : ℂ)))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have h := hcast.mul tF4_1
      simpa using h
    refine hprod0.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x (hx : x < 1)
    simp only [hw4def, gaussW4]
    rw [Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x)]
    push_cast
    ring_nf
  have hev01 : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), 0 < x :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num))
  have hgV : Tendsto (fun x : ℝ => ((₂F₁ a b c x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ))
      (𝓝 ((gaussValue a b c : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp hG1
    simpa [Function.comp_def] using h
  have tF1_1 : Tendsto (fun x : ℝ => F1 ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ))
      (𝓝 ((gaussValue a b c : ℝ) : ℂ)) := by
    refine hgV.congr' ?_
    filter_upwards [hev01, eventually_mem_nhdsWithin] with x hx0 (hx1 : x < 1)
    rw [hF1def]
    exact (ordinaryHypergeometric_ofReal h1R (by rw [abs_of_pos hx0]; exact hx1)).symm
  have hAeq : A = ((gaussValue a b c : ℝ) : ℂ) := by
    rw [hAdef, gaussValue,
      show ((c : ℂ) - a - b) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
      show ((c : ℂ) - a) = ((c - a : ℝ) : ℂ) by push_cast; ring,
      show ((c : ℂ) - b) = ((c - b : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.Gamma_ofReal]
    push_cast
    ring
  have hevU1 : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), ((x : ℝ) : ℂ) ∈ U := by
    filter_upwards [hev01, eventually_mem_nhdsWithin] with x hx0 (hx1 : x < 1)
    constructor
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    · rw [mem_ball_iff_norm, show ((x : ℝ) : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), neg_sub]
      linarith
  have hT1 : Tendsto (fun x : ℝ => Φ ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h := tF1_1.sub ((tw3_1.const_mul A).add (tw4_1.const_mul B))
    have hv : ((gaussValue a b c : ℝ) : ℂ) - (A * 1 + B * 0) = 0 := by
      rw [hAeq]
      ring
    rw [hv] at h
    exact h.congr fun x => by simp only [hΦdef, hg0def]
  have hT1' : Tendsto (fun x : ℝ => Φ ((x : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 γ₃) := by
    have h := (tw3_1.const_mul γ₃).add (tw4_1.const_mul γ₄)
    have hv : γ₃ * 1 + γ₄ * 0 = γ₃ := by ring
    rw [hv] at h
    refine h.congr' ?_
    filter_upwards [hevU1] with x hxU
    rw [hEq hxU]
  have hγ₃0 : γ₃ = 0 := tendsto_nhds_unique hT1' hT1
  -- ===== the limit x → 0⁺ pins γ₄ = 0 =====
  have hevpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact hx
  have hev01' : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num))
  have tcast0 : Tendsto (fun x : ℝ => ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have tF1_0 : Tendsto (fun x : ℝ => F1 ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := ((analyticOnNhd_ordinaryHypergeometric h1 0 h0ball).continuousAt.tendsto).comp tcast0
    have h' : Tendsto (fun x : ℝ => ₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) ((x : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) 0)) := by
      simpa [Function.comp_def] using h
    rw [ordinaryHypergeometric_zero] at h'
    exact h'.congr fun x => by rw [hF1def]
  have hmap01 : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous fun x : ℝ => 1 - x := continuous_const.sub continuous_id
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    · filter_upwards [hevpos] with x hx
      simp only [mem_Iio]
      linarith
  have tw3_0 : Tendsto (fun x : ℝ => w3 ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp (hG3.comp hmap01)
    have h' : Tendsto (fun x : ℝ => ((₂F₁ a b (a + b - c + 1) (1 - x) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)) := by
      simpa [Function.comp_def] using h
    refine h'.congr' ?_
    filter_upwards [hevpos, hev01'] with x hx0 hx1
    have hb3 := ordinaryHypergeometric_ofReal h3R (x := 1 - x)
      (by rw [abs_of_pos (by linarith)]; linarith)
    rw [← hb3]
    simp only [hw3def, gaussW3]
    push_cast
    ring_nf
  have tw4_0 : Tendsto (fun x : ℝ => w4 ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ)) := by
    have hrpow1 : Tendsto (fun x : ℝ => (1 - x) ^ (c - a - b)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hcont : ContinuousAt (fun t : ℝ => t ^ (c - a - b)) 1 :=
        Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
      have hin : Tendsto (fun x : ℝ => 1 - x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
        hmap01.mono_right nhdsWithin_le_nhds
      have h := hcont.tendsto.comp hin
      simpa [Function.comp_def, Real.one_rpow] using h
    have hF4r : Tendsto (fun x : ℝ => ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - x))
        (𝓝[>] (0 : ℝ)) (𝓝 (gaussValue (c - a) (c - b) (c - a - b + 1))) := by
      have h := hG4.comp hmap01
      simpa [Function.comp_def] using h
    have hprod := hrpow1.mul hF4r
    rw [one_mul] at hprod
    have hcast := (Complex.continuous_ofReal.tendsto _).comp hprod
    have h' : Tendsto (fun x : ℝ =>
        (((1 - x) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - x) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ)) := by
      simpa [Function.comp_def] using hcast
    refine h'.congr' ?_
    filter_upwards [hevpos, hev01'] with x hx0 hx1
    have hb4 := ordinaryHypergeometric_ofReal h4R (x := 1 - x)
      (by rw [abs_of_pos (by linarith)]; linarith)
    rw [Complex.ofReal_mul, ← hb4, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - x)]
    simp only [hw4def, gaussW4]
    push_cast
    ring_nf
  have hevU0 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ((x : ℝ) : ℂ) ∈ U := by
    filter_upwards [hevpos, hev01'] with x hx0 hx1
    constructor
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx1
    · rw [mem_ball_iff_norm, show ((x : ℝ) : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), neg_sub]
      linarith
  have hT2 : Tendsto (fun x : ℝ => Φ ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (1 - (A * ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)
        + B * ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ)))) := by
    have h := tF1_0.sub ((tw3_0.const_mul A).add (tw4_0.const_mul B))
    exact h.congr fun x => by simp only [hΦdef, hg0def]
  have hT2' : Tendsto (fun x : ℝ => Φ ((x : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (γ₃ * ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)
        + γ₄ * ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ))) := by
    have h := (tw3_0.const_mul γ₃).add (tw4_0.const_mul γ₄)
    refine h.congr' ?_
    filter_upwards [hevU0] with x hxU
    rw [hEq hxU]
  have hkey := tendsto_nhds_unique hT2 hT2'
  -- the Gamma identity forces the left side to vanish
  have hBeq : B = ((Real.Gamma c * Real.Gamma (a + b - c)
      / (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ) := by
    rw [hBdef, show ((a : ℂ) + b - c) = ((a + b - c : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.Gamma_ofReal]
    push_cast
    ring
  have hid := gauss_connection_gamma_identity ha hb hbc hs hc1 hac
  have hzero : (1 : ℂ) - (A * ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)
      + B * ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ)) = 0 := by
    rw [hAeq, hBeq]
    rw [show (1 : ℂ) - (((gaussValue a b c : ℝ) : ℂ)
          * ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)
        + ((Real.Gamma c * Real.Gamma (a + b - c) / (Real.Gamma a * Real.Gamma b) : ℝ) : ℂ)
          * ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ))
      = (((1 : ℝ) - (gaussValue a b c * gaussValue a b (a + b - c + 1)
        + Real.Gamma c * Real.Gamma (a + b - c) / (Real.Gamma a * Real.Gamma b)
          * gaussValue (c - a) (c - b) (c - a - b + 1)) : ℝ) : ℂ) by push_cast; ring]
    rw [show (1 : ℝ) - (gaussValue a b c * gaussValue a b (a + b - c + 1)
        + Real.Gamma c * Real.Gamma (a + b - c) / (Real.Gamma a * Real.Gamma b)
          * gaussValue (c - a) (c - b) (c - a - b + 1)) = 0 by linarith [hid]]
    exact Complex.ofReal_zero
  have hG4pos : 0 < gaussValue (c - a) (c - b) (c - a - b + 1) := by
    rw [gaussValue]
    have h1' := Real.Gamma_pos_of_pos (show 0 < c - a - b + 1 by linarith)
    have h2' := Real.Gamma_pos_of_pos (show 0 < c - a - b + 1 - (c - a) - (c - b) by linarith)
    have h3' := Real.Gamma_pos_of_pos (show 0 < c - a - b + 1 - (c - a) by linarith)
    have h4' := Real.Gamma_pos_of_pos (show 0 < c - a - b + 1 - (c - b) by linarith)
    exact div_pos (mul_pos h1' h2') (mul_pos h3' h4')
  have hγ₄0 : γ₄ = 0 := by
    have h0 : γ₃ * ((gaussValue a b (a + b - c + 1) : ℝ) : ℂ)
        + γ₄ * ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ) = 0 := by
      rw [← hkey]
      exact hzero
    rw [hγ₃0, zero_mul, zero_add] at h0
    have hne : ((gaussValue (c - a) (c - b) (c - a - b + 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hG4pos.ne'
    exact (mul_eq_zero.mp h0).resolve_right hne
  -- ===== conclusion on the lens =====
  have hfin := hEq hzU
  rw [hgcdef] at hfin
  simp only [hγ₃0, hγ₄0, zero_mul, add_zero] at hfin
  have hfin' : F1 z = A * w3 z + B * w4 z := by
    have h := hfin
    simp only [hΦdef, hg0def] at h
    linear_combination h
  rw [hw3def, hw4def, gaussW3, gaussW4] at hfin'
  exact hfin'

end FLMF.Hypergeometric
