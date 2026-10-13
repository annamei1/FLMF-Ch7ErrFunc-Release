import FLMF.Frameworks.Hypergeometric.GaussPrincipal
import FLMF.Methods.ODEContinuation
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Global principal continuations for Gauss and Olver hypergeometric functions

This file isolates the genuine mathematical existence problem shared by the
global Chapter 15 formulas.  A continuation datum is an analytic function on
the principal slit plane that agrees with the defining series on the unit
disc.  Existence is kept as an explicit theorem-level gap; the public functions
are chosen from that datum and therefore do not pretend that the raw series is
meaningful outside its convergence disc.
-/

noncomputable section

open Set Metric CategoryTheory TopologicalSpace Filter
open TopologicalSpace.Opens

namespace FLMF.Hypergeometric

/-- The principal Gauss domain `|ph (1-z)| < π`, represented as the preimage of
Mathlib's plane slit along the nonpositive real axis.

DLMF 15.2. -/
-- DAG: E-15.2.
-- Verified: verified (tier2)
def gaussPrincipalDomain : Set ℂ := {z : ℂ | 1 - z ∈ Complex.slitPlane}

-- no-dlmf: list-lifted domain-membership bookkeeping
/-- Every displayed hypergeometric argument lies in the certified principal
continuation domain. -/
def InPrincipalGaussDomain (zs : List ℂ) : Prop :=
  ∀ z ∈ zs, z ∈ gaussPrincipalDomain

-- no-dlmf: topological infrastructure for global continuation
theorem isOpen_gaussPrincipalDomain : IsOpen gaussPrincipalDomain :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

-- no-dlmf: branch bookkeeping for the principal slit domain
/-- For `z` in the principal Gauss domain and `t ∈ [0,1]`, the point
`1 - zt` remains in the slit plane. -/
theorem one_sub_mul_mem_slitPlane {z : ℂ} (hz : z ∈ gaussPrincipalDomain)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 1 - z * t ∈ Complex.slitPlane := by
  have h := Complex.starConvex_one_slitPlane (y := 1 - z) hz
    (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
  have he : (1 - t) • (1 : ℂ) + t • (1 - z) = 1 - z * t := by
    simp only [Complex.real_smul]
    push_cast
    ring
  rwa [he] at h

-- no-dlmf: topological infrastructure for global continuation
/-- The principal Gauss domain is star-shaped about the origin. -/
theorem starConvex_zero_gaussPrincipalDomain :
    StarConvex ℝ (0 : ℂ) gaussPrincipalDomain := by
  intro y hy s t hs ht hst
  have h := one_sub_mul_mem_slitPlane hy ht (by linarith)
  show 1 - (s • (0 : ℂ) + t • y) ∈ Complex.slitPlane
  have he : 1 - (s • (0 : ℂ) + t • y) = 1 - y * t := by
    simp only [smul_zero, zero_add, Complex.real_smul]
    ring
  rwa [he]

-- no-dlmf: topological infrastructure for global continuation
/-- The origin lies in the principal Gauss domain. -/
theorem zero_mem_gaussPrincipalDomain : (0 : ℂ) ∈ gaussPrincipalDomain := by
  show (1 : ℂ) - 0 ∈ Complex.slitPlane
  simpa using Complex.one_mem_slitPlane

-- no-dlmf: topological infrastructure for global continuation
/-- The principal Gauss domain is preconnected. -/
theorem isPreconnected_gaussPrincipalDomain : IsPreconnected gaussPrincipalDomain :=
  (starConvex_zero_gaussPrincipalDomain.isPathConnected
    zero_mem_gaussPrincipalDomain).isConnected.isPreconnected

-- no-dlmf: topological infrastructure for the monodromy theorem
noncomputable instance contractibleSpace_gaussPrincipalDomain :
    ContractibleSpace gaussPrincipalDomain :=
  starConvex_zero_gaussPrincipalDomain.contractibleSpace
    ⟨0, zero_mem_gaussPrincipalDomain⟩

-- no-dlmf: topological infrastructure for the monodromy theorem
instance locPathConnectedSpace_gaussPrincipalDomain :
    LocPathConnectedSpace gaussPrincipalDomain :=
  isOpen_gaussPrincipalDomain.locPathConnectedSpace

/-! ### An ordinary simply connected chart -/

-- no-dlmf: simply connected chart bookkeeping for the continuation
/-- The principal ordinary chart cuts from `0` along the positive real ray.
It avoids both Gauss singularities; the omitted segment `[0,1)` is restored by
the defining unit disc. -/
def gaussOrdinaryPrincipalDomain : Set ℂ :=
  {z : ℂ | -z ∈ Complex.slitPlane}

theorem isOpen_gaussOrdinaryPrincipalDomain :
    IsOpen gaussOrdinaryPrincipalDomain :=
  Complex.isOpen_slitPlane.preimage continuous_neg

theorem gaussOrdinaryPrincipalDomain_ne_zero {z : ℂ}
    (hz : z ∈ gaussOrdinaryPrincipalDomain) : z ≠ 0 := by
  intro h
  subst z
  change -(0 : ℂ) ∈ Complex.slitPlane at hz
  exact Complex.zero_notMem_slitPlane (by simpa using hz)

theorem gaussOrdinaryPrincipalDomain_ne_one {z : ℂ}
    (hz : z ∈ gaussOrdinaryPrincipalDomain) : z ≠ 1 := by
  intro h
  subst z
  change -(1 : ℂ) ∈ Complex.slitPlane at hz
  norm_num [Complex.mem_slitPlane_iff] at hz

theorem starConvex_neg_one_gaussOrdinaryPrincipalDomain :
    StarConvex ℝ (-1 : ℂ) gaussOrdinaryPrincipalDomain := by
  intro y hy s t hs ht hst
  have h := Complex.starConvex_one_slitPlane (y := -y) hy hs ht hst
  show -(s • (-1 : ℂ) + t • y) ∈ Complex.slitPlane
  convert h using 1 <;> module

noncomputable instance contractibleSpace_gaussOrdinaryPrincipalDomain :
    ContractibleSpace gaussOrdinaryPrincipalDomain :=
  starConvex_neg_one_gaussOrdinaryPrincipalDomain.contractibleSpace
    ⟨-1, by simp [gaussOrdinaryPrincipalDomain, Complex.mem_slitPlane_iff]⟩

instance locPathConnectedSpace_gaussOrdinaryPrincipalDomain :
    LocPathConnectedSpace gaussOrdinaryPrincipalDomain :=
  isOpen_gaussOrdinaryPrincipalDomain.locPathConnectedSpace

/-- The ordinary slit chart together with the defining disc covers exactly the
principal Gauss domain. -/
theorem gaussPrincipalDomain_eq_ball_union_ordinary :
    gaussPrincipalDomain =
      ball (0 : ℂ) 1 ∪ gaussOrdinaryPrincipalDomain := by
  ext z
  constructor
  · intro hz
    by_cases hball : z ∈ ball (0 : ℂ) 1
    · exact Or.inl hball
    · right
      change -z ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      by_cases him : z.im = 0
      · left
        simp only [gaussPrincipalDomain, Complex.mem_slitPlane_iff] at hz
        have hre : z.re < 1 := by
          rcases hz with hz | hz
          · simpa using hz
          · simp [him] at hz
        have hzreal : z = (z.re : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using him
        have habs : 1 ≤ |z.re| := by
          have hn : 1 ≤ ‖z‖ := by
            rw [mem_ball_zero_iff] at hball
            exact le_of_not_gt hball
          rw [hzreal, Complex.norm_real] at hn
          exact hn
        change 0 < -z.re
        rcases le_total 0 z.re with hnonneg | hnonpos
        · rw [abs_of_nonneg hnonneg] at habs
          linarith
        · rw [abs_of_nonpos hnonpos] at habs
          linarith
      · right
        simpa using him
  · rintro (hz | hz)
    · show 1 - z ∈ Complex.slitPlane
      have hnorm : ‖-z‖ < 1 := by
        simpa [mem_ball_zero_iff] using hz
      simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hnorm
    · change -z ∈ Complex.slitPlane at hz
      rw [Complex.mem_slitPlane_iff] at hz
      change 1 - z ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      rcases hz with hz | hz
      · left
        change 0 < -z.re at hz
        change 0 < 1 - z.re
        linarith
      · right
        simpa using hz

-- no-dlmf: topology of the overlap used to initialize continuation
/-- The overlap of the defining disc with the ordinary slit chart is
star-shaped about `-1/2`. -/
theorem starConvex_neg_half_gauss_overlap :
    StarConvex ℝ (-(1 / 2 : ℂ))
      (Metric.ball (0 : ℂ) 1 ∩ gaussOrdinaryPrincipalDomain) := by
  have hcenterBall : -(1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num [Complex.norm_real]
  intro y hy s t hs ht hst
  constructor
  · exact (convex_ball (0 : ℂ) 1) hcenterBall hy.1 hs ht hst
  · change -(s • (-(1 / 2 : ℂ)) + t • y) ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]
    by_cases hyim : y.im = 0
    · left
      have hyord := hy.2
      change -y ∈ Complex.slitPlane at hyord
      rw [Complex.mem_slitPlane_iff] at hyord
      rcases hyord with hyre | hyim'
      · simp only [map_add, map_smul, Complex.neg_re, Complex.real_smul,
          Complex.ofReal_re, neg_neg]
        have : y.re < 0 := by simpa using hyre
        norm_num [Complex.real_smul]
        by_cases hs0 : s = 0
        · subst s
          have ht1 : t = 1 := by linarith
          subst t
          norm_num
          exact this
        · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
          have hty : t * y.re ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ht (le_of_lt this)
          nlinarith
      · exact (hyim' (by simpa using hyim)).elim
    · by_cases ht0 : t = 0
      · left
        subst t
        have hs1 : s = 1 := by linarith
        subst s
        norm_num [Complex.mem_slitPlane_iff]
      · right
        norm_num [Complex.real_smul]
        exact ⟨ht0, hyim⟩

/-! ### The sheaf of ordinary Gauss solution jets -/

-- no-dlmf: transparent alias of gaussOrdinaryPrincipalDomain
/-- Points of the simply connected ordinary Gauss chart. -/
abbrev GaussOrdinaryPoint := gaussOrdinaryPrincipalDomain

/-- The prelocal predicate describing 1-jets of analytic solutions of the
Gauss differential equation on the ordinary chart. -/
def gaussJetPrelocal (a b c : ℂ) :
    TopCat.PrelocalPredicate (fun _ : TopCat.of GaussOrdinaryPoint => ℂ × ℂ) where
  pred {U} s := ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f (Subtype.val '' (U : Set GaussOrdinaryPoint)) ∧
    (∀ z ∈ Subtype.val '' (U : Set GaussOrdinaryPoint),
      z * (1 - z) * deriv (deriv f) z +
        (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0) ∧
    ∀ x, s x = (f x.1.1, deriv f x.1.1)
  res {U V} i s hs := by
    obtain ⟨f, hf, hode, hjet⟩ := hs
    refine ⟨f, hf.mono ?_, ?_, ?_⟩
    · rintro z ⟨x, hx, rfl⟩
      exact ⟨x, i.le hx, rfl⟩
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hode x ⟨x, i.le hx, rfl⟩
    · intro x
      exact hjet ⟨x, i.le x.2⟩

/-- The local predicate obtained by sheafifying ordinary Gauss solution
1-jets. -/
def gaussJetLocal (a b c : ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of GaussOrdinaryPoint => ℂ × ℂ) :=
  (gaussJetPrelocal a b c).sheafify

-- no-dlmf: uniqueness input for global analytic continuation
/-- Evaluation of a germ of ordinary Gauss solution jets at its base point is
injective.  The proof shrinks two local representatives to a common complex
ball and applies analytic 1-jet uniqueness for the Gauss ODE. -/
theorem gaussJetLocal_stalkToFiber_injective (a b c : ℂ)
    (x : TopCat.of GaussOrdinaryPoint) :
    Function.Injective (TopCat.stalkToFiber (gaussJetLocal a b c) x) := by
  apply TopCat.stalkToFiber_injective
  intro U V sU hsU sV hsV hjet
  rcases hsU ⟨x, U.2⟩ with ⟨U', hxU', iU', hsU'⟩
  rcases hsV ⟨x, V.2⟩ with ⟨V', hxV', iV', hsV'⟩
  rcases hsU' with ⟨f, hf, hfode, hfjet⟩
  rcases hsV' with ⟨g, hg, hgode, hgjet⟩
  let AU : Set ℂ := Subtype.val '' (U' : Set GaussOrdinaryPoint)
  let AV : Set ℂ := Subtype.val '' (V' : Set GaussOrdinaryPoint)
  have hAUo : IsOpen AU :=
    isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val _ U'.2
  have hAVo : IsOpen AV :=
    isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val _ V'.2
  have hxAU : x.1 ∈ AU := ⟨x, hxU', rfl⟩
  have hxAV : x.1 ∈ AV := ⟨x, hxV', rfl⟩
  obtain ⟨r, hr, hrsub⟩ :=
    Metric.isOpen_iff.mp (hAUo.inter hAVo) x.1 ⟨hxAU, hxAV⟩
  let W₀ : Opens (TopCat.of GaussOrdinaryPoint) :=
    ⟨Subtype.val ⁻¹' Metric.ball x.1 r,
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hxW₀ : x ∈ W₀ := by
    change x.1 ∈ Metric.ball x.1 r
    simpa [Metric.mem_ball] using hr
  let W : OpenNhds x := ⟨W₀, hxW₀⟩
  have hWU' : W.1 ≤ U' := by
    intro y hy
    have hyAU : y.1 ∈ AU := (hrsub hy).1
    rcases hyAU with ⟨y', hy'U', hyy'⟩
    have hyy : y' = y := Subtype.ext hyy'
    simpa [hyy] using hy'U'
  have hWV' : W.1 ≤ V' := by
    intro y hy
    have hyAV : y.1 ∈ AV := (hrsub hy).2
    rcases hyAV with ⟨y', hy'V', hyy'⟩
    have hyy : y' = y := Subtype.ext hyy'
    simpa [hyy] using hy'V'
  let jU' : W ⟶ U := homOfLE (hWU'.trans iU'.le)
  let jV' : W ⟶ V := homOfLE (hWV'.trans iV'.le)
  have hfjetx := hfjet ⟨x, hxU'⟩
  have hgjetx := hgjet ⟨x, hxV'⟩
  change sU (⟨x, iU'.le hxU'⟩ : U.1) =
    (f x.1, deriv f x.1) at hfjetx
  change sV (⟨x, iV'.le hxV'⟩ : V.1) =
    (g x.1, deriv g x.1) at hgjetx
  have hiUx : (⟨x, iU'.le hxU'⟩ : U.1) = ⟨x, U.2⟩ := Subtype.ext rfl
  have hiVx : (⟨x, iV'.le hxV'⟩ : V.1) = ⟨x, V.2⟩ := Subtype.ext rfl
  rw [hiUx] at hfjetx
  rw [hiVx] at hgjetx
  have hfgjet : (f x.1, deriv f x.1) = (g x.1, deriv g x.1) :=
    hfjetx ▸ hgjetx ▸ hjet
  have heq : EqOn f g (Metric.ball x.1 r) := by
    refine FLMF.Methods.ODEContinuation.linODE2_eqOn_of_jet_eq'
      (P := fun z : ℂ => z * (1 - z))
      (Q := fun z : ℂ => c - (a + b + 1) * z)
      (R := fun _ : ℂ => -(a * b))
      Metric.isOpen_ball (convex_ball x.1 r).isPreconnected ?_ ?_ ?_ ?_
      (hf.mono fun z hz => (hrsub hz).1)
      (hg.mono fun z hz => (hrsub hz).2) ?_ ?_ (Metric.mem_ball_self hr)
      (congrArg Prod.fst hfgjet) (congrArg Prod.snd hfgjet)
    · exact fun _ _ => analyticAt_id.mul (analyticAt_const.sub analyticAt_id)
    · exact fun _ _ => analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    · exact fun _ _ => analyticAt_const
    · intro z hz
      rcases (hrsub hz).1 with ⟨z', -, rfl⟩
      exact mul_ne_zero (gaussOrdinaryPrincipalDomain_ne_zero z'.2)
        (sub_ne_zero.mpr (gaussOrdinaryPrincipalDomain_ne_one z'.2).symm)
    · intro z hz
      have h := hfode z (hrsub hz).1
      linear_combination h
    · intro z hz
      have h := hgode z (hrsub hz).2
      linear_combination h
  refine ⟨W, jU', jV', ?_⟩
  intro y
  have hyball : y.1.1 ∈ Metric.ball x.1 r := y.2
  have hyU' : y.1 ∈ U' := hWU' y.2
  have hyV' : y.1 ∈ V' := hWV' y.2
  have hfjety := hfjet ⟨y.1, hyU'⟩
  have hgjety := hgjet ⟨y.1, hyV'⟩
  change sU (⟨y.1, iU'.le hyU'⟩ : U.1) =
    (f y.1.1, deriv f y.1.1) at hfjety
  change sV (⟨y.1, iV'.le hyV'⟩ : V.1) =
    (g y.1.1, deriv g y.1.1) at hgjety
  change sU (jU' y : U.1) = sV (jV' y : V.1)
  rw [show (jU' y : U.1) = (⟨y.1, iU'.le hyU'⟩ : U.1) by
        apply Subtype.ext
        rfl,
    show (jV' y : V.1) = (⟨y.1, iV'.le hyV'⟩ : V.1) by
        apply Subtype.ext
        rfl,
    hfjety, hgjety]
  apply Prod.ext
  · exact heq hyball
  · exact (heq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hyball)).deriv_eq

-- no-dlmf: local existence input for global analytic continuation
/-- Evaluation of a germ of ordinary Gauss solution jets at its base point is
surjective: every prescribed value and first derivative is realized by a
local analytic solution. -/
theorem gaussJetLocal_stalkToFiber_surjective (a b c : ℂ)
    (x : TopCat.of GaussOrdinaryPoint) :
    Function.Surjective (TopCat.stalkToFiber (gaussJetLocal a b c) x) := by
  apply TopCat.stalkToFiber_surjective
  rintro ⟨w₀, w₁⟩
  have hx0 : x.1 ≠ 0 := gaussOrdinaryPrincipalDomain_ne_zero x.2
  have hx1 : x.1 ≠ 1 := gaussOrdinaryPrincipalDomain_ne_one x.2
  obtain ⟨f, hf, hf0, hf1, hfode⟩ :=
    exists_local_gauss_solution a b c hx0 hx1 (w₀ := w₀) (w₁ := w₁)
  let U₀ : Opens (TopCat.of GaussOrdinaryPoint) :=
    ⟨Subtype.val ⁻¹' Metric.ball x.1 (gaussOrdinaryRadius a b c x.1),
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hxU₀ : x ∈ U₀ := by
    change x.1 ∈ Metric.ball x.1 (gaussOrdinaryRadius a b c x.1)
    exact Metric.mem_ball_self (gaussOrdinaryRadius_pos a b c hx0 hx1)
  let U : OpenNhds x := ⟨U₀, hxU₀⟩
  let s : ∀ y : U.1, ℂ × ℂ := fun y => (f y.1.1, deriv f y.1.1)
  refine ⟨U, s, ?_, ?_⟩
  · apply TopCat.PrelocalPredicate.sheafifyOf
    refine ⟨f, hf.mono ?_, ?_, ?_⟩
    · rintro z ⟨y, hy, rfl⟩
      exact hy
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact hfode y.1 hy
    · intro y
      rfl
  · change (f x.1, deriv f x.1) = (w₀, w₁)
    rw [hf0, hf1]

-- no-dlmf: regularity of local solution-jet sections
theorem gaussJetLocal_section_continuous {a b c : ℂ}
    {U : Opens (TopCat.of GaussOrdinaryPoint)}
    {s : ∀ y : U, ℂ × ℂ} (hs : (gaussJetLocal a b c).pred s) :
    Continuous s := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases hs y with ⟨V, hyV, i, f, hf, -, hjet⟩
  have hjcont : Continuous (fun z : V => (f z.1.1, deriv f z.1.1)) := by
    rw [continuous_iff_continuousAt]
    intro z
    apply ContinuousAt.prodMk
    · exact ((hf z.1.1 ⟨z.1, z.2, rfl⟩).continuousAt.comp
        continuousAt_subtype_val).comp continuousAt_subtype_val
    · exact ((hf.deriv z.1.1 ⟨z.1, z.2, rfl⟩).continuousAt.comp
        continuousAt_subtype_val).comp continuousAt_subtype_val
  have hsic : Continuous (fun z : V => s (⟨z.1, i.le z.2⟩ : U)) := by
    convert hjcont using 1
    funext z
    exact hjet z
  rw [continuous_iff_continuousAt] at hsic
  simpa using (Opens.isOpenEmbedding_of_le i.le).continuousAt_iff.mp
    (hsic ⟨y, hyV⟩)

-- no-dlmf: uniqueness of a solution-jet section on a connected chart
theorem gaussJetLocal_section_eq_of_eq_at {a b c : ℂ}
    {U : Opens (TopCat.of GaussOrdinaryPoint)}
    (hU : IsPreconnected (U : Set GaussOrdinaryPoint))
    {s t : ∀ y : U, ℂ × ℂ}
    (hs : (gaussJetLocal a b c).pred s)
    (ht : (gaussJetLocal a b c).pred t)
    (y : U) (hy : s y = t y) : s = t := by
  let E : Set U := {z | s z = t z}
  have hEc : IsClosed E :=
    isClosed_eq (gaussJetLocal_section_continuous hs)
      (gaussJetLocal_section_continuous ht)
  have hEo : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    let F := (TopCat.subsheafToTypes (gaussJetLocal a b c)).presheaf
    have hgerm : F.germ U z.1 z.2 ⟨s, hs⟩ = F.germ U z.1 z.2 ⟨t, ht⟩ := by
      apply gaussJetLocal_stalkToFiber_injective a b c z.1
      rw [TopCat.stalkToFiber_germ, TopCat.stalkToFiber_germ]
      exact hz
    obtain ⟨W, hzW, iS, iT, hres⟩ :=
      F.germ_eq z.1 z.2 z.2 ⟨s, hs⟩ ⟨t, ht⟩ hgerm
    have hfun : (fun w : W => s (⟨w.1, iS.le w.2⟩ : U)) =
        fun w : W => t (⟨w.1, iT.le w.2⟩ : U) :=
      congrArg Subtype.val hres
    refine Filter.mem_of_superset
      ((W.2.preimage continuous_subtype_val).mem_nhds hzW) ?_
    intro q hq
    have hqS : (⟨q.1, iS.le hq⟩ : U) = q := Subtype.ext rfl
    have hqT : (⟨q.1, iT.le hq⟩ : U) = q := Subtype.ext rfl
    change s q = t q
    calc
      s q = s (⟨q.1, iS.le hq⟩ : U) := congrArg s hqS.symm
      _ = t (⟨q.1, iT.le hq⟩ : U) := congrFun hfun ⟨q.1, hq⟩
      _ = t q := congrArg t hqT
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hU
  have hEcl : IsClopen E := ⟨hEc, hEo⟩
  have hE : E = Set.univ := hEcl.eq_univ ⟨y, hy⟩
  funext z
  have hzE : z ∈ E := by rw [hE]; exact Set.mem_univ z
  exact hzE

-- no-dlmf: common-neighborhood well-posedness for the Gauss ODE
theorem gaussJetLocal_unique_local_sections (a b c : ℂ)
    (x : TopCat.of GaussOrdinaryPoint) :
    ∃ (U : Opens (TopCat.of GaussOrdinaryPoint)), x ∈ U ∧
      ∀ y (hy : y ∈ U) (t : ℂ × ℂ), ∃! s :
        (TopCat.subsheafToTypes (gaussJetLocal a b c)).presheaf.obj (Opposite.op U),
        s.1 ⟨y, hy⟩ = t := by
  have hx0 : x.1 ≠ 0 := gaussOrdinaryPrincipalDomain_ne_zero x.2
  have hx1 : x.1 ≠ 1 := gaussOrdinaryPrincipalDomain_ne_one x.2
  obtain ⟨f, hf, hf0, hf1, hfode⟩ :=
    exists_local_gauss_solution a b c hx0 hx1 (w₀ := 1) (w₁ := 0)
  obtain ⟨g, hg, hg0, hg1, hgode⟩ :=
    exists_local_gauss_solution a b c hx0 hx1 (w₀ := 0) (w₁ := 1)
  let D : ℂ → ℂ := fun z => f z * deriv g z - g z * deriv f z
  have hxball : x.1 ∈ Metric.ball x.1 (gaussOrdinaryRadius a b c x.1) :=
    Metric.mem_ball_self (gaussOrdinaryRadius_pos a b c hx0 hx1)
  have hDcont : ContinuousAt D x.1 := by
    exact ((hf x.1 hxball).continuousAt.mul (hg.deriv x.1 hxball).continuousAt).sub
      ((hg x.1 hxball).continuousAt.mul (hf.deriv x.1 hxball).continuousAt)
  have hD1 : D x.1 = 1 := by simp [D, hf0, hf1, hg0, hg1]
  have hgood : {z | D z ≠ 0} ∩
      Metric.ball x.1 (gaussOrdinaryRadius a b c x.1) ∩
      gaussOrdinaryPrincipalDomain ∈ nhds x.1 := by
    exact Filter.inter_mem
      (Filter.inter_mem (hDcont.eventually_ne (by rw [hD1]; norm_num))
        (Metric.isOpen_ball.mem_nhds hxball))
      (isOpen_gaussOrdinaryPrincipalDomain.mem_nhds x.2)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hgood
  let U : Opens (TopCat.of GaussOrdinaryPoint) :=
    ⟨Subtype.val ⁻¹' Metric.ball x.1 r,
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hxU : x ∈ U := Metric.mem_ball_self hr
  refine ⟨U, hxU, ?_⟩
  intro y hy t
  have hygood := hrsub hy
  have hDy : D y ≠ 0 := hygood.1.1
  let A : ℂ := (t.1 * deriv g y - g y * t.2) / D y
  let B : ℂ := (f y * t.2 - t.1 * deriv f y) / D y
  let h : ℂ → ℂ := fun z => A * f z + B * g z
  let s : ∀ z : U, ℂ × ℂ := fun z => (h z.1.1, deriv h z.1.1)
  have hh : AnalyticOnNhd ℂ h (Subtype.val '' (U : Set GaussOrdinaryPoint)) := by
    rintro z ⟨z', hz', rfl⟩
    exact (analyticAt_const.mul (hf z'.1 (hrsub hz').1.2)).add
      (analyticAt_const.mul (hg z'.1 (hrsub hz').1.2))
  have hhode : ∀ z ∈ Subtype.val '' (U : Set GaussOrdinaryPoint),
      z * (1 - z) * deriv (deriv h) z +
        (c - (a + b + 1) * z) * deriv h z - a * b * h z = 0 := by
    rintro _ ⟨z', hz, rfl⟩
    have hzbig : z'.1 ∈ Metric.ball x.1 (gaussOrdinaryRadius a b c x.1) :=
      (hrsub hz).1.2
    have hfa := (hf z'.1 hzbig).differentiableAt
    have hga := (hg z'.1 hzbig).differentiableAt
    have hdfa := (hf.deriv z'.1 hzbig).differentiableAt
    have hdga := (hg.deriv z'.1 hzbig).differentiableAt
    have hdh : deriv h z'.1 = A * deriv f z'.1 + B * deriv g z'.1 := by
      simp [h, deriv_add, deriv_const_mul, hfa, hga]
    have hev : deriv h =ᶠ[nhds z'.1] fun w => A * deriv f w + B * deriv g w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzbig] with w hw
      simp [h, deriv_add, deriv_const_mul, (hf w hw).differentiableAt,
        (hg w hw).differentiableAt]
    have hddh : deriv (deriv h) z'.1 =
        A * deriv (deriv f) z'.1 + B * deriv (deriv g) z'.1 := by
      rw [hev.deriv_eq]
      simp [deriv_add, deriv_const_mul, hdfa, hdga]
    rw [hdh, hddh]
    simp only [h]
    linear_combination A * (hfode z'.1 hzbig) + B * (hgode z'.1 hzbig)
  have hs : (gaussJetLocal a b c).pred s := by
    apply TopCat.PrelocalPredicate.sheafifyOf
    exact ⟨h, hh, hhode, fun _ => rfl⟩
  have hsy : s ⟨y, hy⟩ = t := by
    have hfa := (hf y hygood.1.2).differentiableAt
    have hga := (hg y hygood.1.2).differentiableAt
    change (h y, deriv h y) = t
    have hdh : deriv h y = A * deriv f y + B * deriv g y := by
      simp [h, deriv_add, deriv_const_mul, hfa, hga]
    rw [hdh]
    apply Prod.ext
    · dsimp [h, A, B]
      field_simp
      simp only [D] at hDy ⊢
      ring
    · dsimp [A, B]
      field_simp
      simp only [D] at hDy ⊢
      ring
  refine ⟨⟨s, hs⟩, hsy, ?_⟩
  intro q hqy
  apply Subtype.ext
  have hUpre : IsPreconnected (U : Set GaussOrdinaryPoint) :=
    (convex_ball x.1 r).isPreconnected.preimage_of_isOpenMap
      Subtype.val_injective
      isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val
      (fun z hz => ⟨⟨z, (hrsub hz).2⟩, rfl⟩)
  exact gaussJetLocal_section_eq_of_eq_at (a := a) (b := b) (c := c)
    hUpre q.2 hs ⟨y, hy⟩ (hqy.trans hsy.symm)

-- no-dlmf: extraction of an ambient analytic function from a global jet section
theorem exists_ambient_gauss_solution_of_top_section {a b c : ℂ}
    {s : GaussOrdinaryPoint → ℂ × ℂ}
    (hs : (gaussJetLocal a b c).pred
      (fun x : (⊤ : Opens (TopCat.of GaussOrdinaryPoint)) => s x.1)) :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f gaussOrdinaryPrincipalDomain ∧
      (∀ z ∈ gaussOrdinaryPrincipalDomain,
        z * (1 - z) * deriv (deriv f) z +
          (c - (a + b + 1) * z) * deriv f z - a * b * f z = 0) ∧
      ∀ z : GaussOrdinaryPoint, s z = (f z.1, deriv f z.1) := by
  classical
  let f : ℂ → ℂ := fun z => if hz : z ∈ gaussOrdinaryPrincipalDomain then (s ⟨z, hz⟩).1 else 0
  have hfa : AnalyticOnNhd ℂ f gaussOrdinaryPrincipalDomain := by
    intro z hz
    rcases hs ⟨⟨z, hz⟩, Set.mem_univ _⟩ with ⟨V, hzV, i, g, hg, -, hjet⟩
    have hVo : IsOpen (Subtype.val '' (V : Set GaussOrdinaryPoint)) :=
      isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val _ V.2
    refine (hg z ⟨⟨z, hz⟩, hzV, rfl⟩).congr ?_
    filter_upwards [hVo.mem_nhds ⟨⟨z, hz⟩, hzV, rfl⟩] with w hw
    rcases hw with ⟨w', hw'V, rfl⟩
    have hj := hjet ⟨w', hw'V⟩
    change s w' = (g w'.1, deriv g w'.1) at hj
    simp [f, w'.2, hj]
  refine ⟨f, hfa, ?_, ?_⟩
  · intro z hz
    rcases hs ⟨⟨z, hz⟩, Set.mem_univ _⟩ with ⟨V, hzV, i, g, hg, hgode, hjet⟩
    have hVo : IsOpen (Subtype.val '' (V : Set GaussOrdinaryPoint)) :=
      isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val _ V.2
    have hev : f =ᶠ[nhds z] g := by
      filter_upwards [hVo.mem_nhds ⟨⟨z, hz⟩, hzV, rfl⟩] with w hw
      rcases hw with ⟨w', hw'V, rfl⟩
      have hj := hjet ⟨w', hw'V⟩
      change s w' = (g w'.1, deriv g w'.1) at hj
      simp [f, w'.2, hj]
    have hd : deriv f z = deriv g z := hev.deriv_eq
    have hdd : deriv (deriv f) z = deriv (deriv g) z := hev.deriv.deriv_eq
    rw [hd, hdd, hev.eq_of_nhds]
    exact hgode z ⟨⟨z, hz⟩, hzV, rfl⟩
  · intro z
    rcases hs ⟨z, Set.mem_univ _⟩ with ⟨V, hzV, i, g, hg, -, hjet⟩
    have hVo : IsOpen (Subtype.val '' (V : Set GaussOrdinaryPoint)) :=
      isOpen_gaussOrdinaryPrincipalDomain.isOpenMap_subtype_val _ V.2
    have hj := hjet ⟨z, hzV⟩
    change s z = (g z.1, deriv g z.1) at hj
    have hev : f =ᶠ[nhds z.1] g := by
      filter_upwards [hVo.mem_nhds ⟨z, hzV, rfl⟩] with w hw
      rcases hw with ⟨w', hw'V, rfl⟩
      have hjw := hjet ⟨w', hw'V⟩
      change s w' = (g w'.1, deriv g w'.1) at hjw
      simp [f, w'.2, hjw]
    rw [hj]
    apply Prod.ext
    · exact hev.eq_of_nhds.symm
    · exact hev.deriv_eq.symm

-- no-dlmf: parameter-regularity vocabulary (DLMF prose caveat, no display)
/-- Regularity of the lower Gauss parameter: `c` is not a nonpositive
integer. -/
def GaussRegular (c : ℂ) : Prop := ∀ n : ℕ, c ≠ -(n : ℂ)

-- no-dlmf: parameter-regularity vocabulary (DLMF prose caveat, no display)
/-- No member of the descending integer translate `w-k` is a Gamma pole. -/
def GammaRegularDescending (w : ℂ) : Prop :=
  ∀ k n : ℕ, w - (k : ℂ) ≠ -(n : ℂ)

-- no-dlmf: parameter-regularity vocabulary (DLMF prose caveat, no display)
/-- Every listed Gamma factor is finite in Mathlib's totalized convention.
This is the compact regular-parameter hypothesis used by connection formulas
whose exceptional cases require separate limiting interpretations. -/
def GammaFinite (zs : List ℂ) : Prop :=
  ∀ z ∈ zs, Complex.Gamma z ≠ 0

-- no-dlmf: parameter-regularity bookkeeping (Gamma poles are exactly the
-- nonpositive integers)
/-- A point with a finite (nonzero) Gamma value is a regular Gauss parameter. -/
theorem gaussRegular_of_Gamma_ne_zero {w : ℂ}
    (hw : Complex.Gamma w ≠ 0) : GaussRegular w := by
  intro n hn
  apply hw
  rw [Complex.Gamma_eq_zero_iff]
  exact ⟨n, hn⟩

-- no-dlmf: the three regularity spellings are one condition; these bridges
-- record the exact relations (`GammaFinite` is list-lifted `GaussRegular`,
-- `GammaRegularDescending` is `GaussRegular` along the descending translates)
/-- `GammaFinite` is exactly the list-lifted regular-parameter condition. -/
theorem gammaFinite_iff_forall_gaussRegular (zs : List ℂ) :
    GammaFinite zs ↔ ∀ z ∈ zs, GaussRegular z := by
  unfold GammaFinite GaussRegular
  constructor
  · intro h z hz n hn
    exact (h z hz) (by rw [Complex.Gamma_eq_zero_iff]; exact ⟨n, hn⟩)
  · intro h z hz hΓ
    obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff z).mp hΓ
    exact h z hz m hm

/-- `GammaRegularDescending` is `GaussRegular` at every descending integer
translate (definitional unfolding). -/
theorem gammaRegularDescending_iff_forall_gaussRegular (w : ℂ) :
    GammaRegularDescending w ↔ ∀ k : ℕ, GaussRegular (w - (k : ℂ)) :=
  Iff.rfl

/-- An honest principal continuation datum for the ordinary Gauss function. -/
structure PrincipalGaussContinuation (a b c : ℂ) where
  toFun : ℂ → ℂ
  analyticOn : AnalyticOnNhd ℂ toFun gaussPrincipalDomain
  eq_series : Set.EqOn toFun (₂F₁ a b c) (ball (0 : ℂ) 1)

/-- An honest principal continuation datum for Olver's regularized Gauss
function. -/
structure PrincipalOlverContinuation (a b c : ℂ) where
  toFun : ℂ → ℂ
  analyticOn : AnalyticOnNhd ℂ toFun gaussPrincipalDomain
  eq_series : Set.EqOn toFun (olverHypergeometric a b c) (ball (0 : ℂ) 1)

private lemma poch_add_eval (x : ℂ) (m n : ℕ) :
    (ascPochhammer ℂ (m + n)).eval x =
      (ascPochhammer ℂ m).eval x * (ascPochhammer ℂ n).eval (x + m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, ascPochhammer_succ_eval, ih, ascPochhammer_succ_eval]
      push_cast
      ring

private lemma olver_neg_nat_tail_term (a b z : ℂ) (N m : ℕ) :
    olverHypergeometricCoefficient a b (-(N : ℂ)) (m + (N + 1)) * z ^ (m + (N + 1)) =
      ((ascPochhammer ℂ (N + 1)).eval a * (ascPochhammer ℂ (N + 1)).eval b /
        (Nat.factorial (N + 1) : ℂ)) * z ^ (N + 1) *
      (((m.factorial : ℂ)⁻¹ * (ascPochhammer ℂ m).eval (a + (N + 1)) *
        (ascPochhammer ℂ m).eval (b + (N + 1)) *
        ((ascPochhammer ℂ m).eval ((N + 2 : ℕ) : ℂ))⁻¹) * z ^ m) := by
  unfold olverHypergeometricCoefficient
  rw [show m + (N + 1) = (N + 1) + m by omega,
    poch_add_eval a (N + 1) m, poch_add_eval b (N + 1) m, pow_add]
  have hGamma : Complex.Gamma (-(N : ℂ) + ((N + 1 + m : ℕ) : ℂ)) = (m.factorial : ℂ) := by
    convert Complex.Gamma_nat_eq_factorial m using 1 <;> push_cast <;> ring
  rw [hGamma]
  have hfac : ((N + 1 + m).factorial : ℂ) =
      (Nat.factorial (N + 1) : ℂ) * (ascPochhammer ℂ m).eval ((N + 2 : ℕ) : ℂ) := by
    rw [show (ascPochhammer ℂ m).eval ((N + 2 : ℕ) : ℂ) =
      (((N + 2).ascFactorial m : ℕ) : ℂ) by
        norm_cast
        exact ascPochhammer_nat_eq_ascFactorial (N + 2) m]
    norm_cast
    exact (Nat.factorial_mul_ascFactorial (N + 1) m).symm
  rw [hfac]
  field_simp
  push_cast
  ring

private lemma olver_neg_nat_initial_term (a b z : ℂ) (N k : ℕ) (hk : k < N + 1) :
    olverHypergeometricCoefficient a b (-(N : ℂ)) k * z ^ k = 0 := by
  have hkN : k ≤ N := by omega
  have harg : -(N : ℂ) + (k : ℂ) = -((N - k : ℕ) : ℂ) := by
    apply Complex.ext
    · simp
      norm_cast
      omega
    · simp
  have hG : Complex.Gamma (-(N : ℂ) + (k : ℂ)) = 0 := by
    rw [Complex.Gamma_eq_zero_iff]
    exact ⟨N - k, harg⟩
  simp [olverHypergeometricCoefficient, hG]

theorem olverHypergeometric_neg_nat_eq_shifted (a b z : ℂ) (N : ℕ) (hz : ‖z‖ < 1) :
    olverHypergeometric a b (-(N : ℂ)) z =
      ((ascPochhammer ℂ (N + 1)).eval a * (ascPochhammer ℂ (N + 1)).eval b /
        (Nat.factorial (N + 1) : ℂ)) * z ^ (N + 1) *
      ₂F₁ (a + (N + 1)) (b + (N + 1)) ((N + 2 : ℕ) : ℂ) z := by
  let C : ℂ := ((ascPochhammer ℂ (N + 1)).eval a *
    (ascPochhammer ℂ (N + 1)).eval b / (Nat.factorial (N + 1) : ℂ)) * z ^ (N + 1)
  have hc : ∀ k : ℕ, (k : ℂ) ≠ -(((N + 2 : ℕ) : ℂ)) := by
    intro k h
    have hre := congrArg Complex.re h
    simp at hre
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hN : (0 : ℝ) < N + 2 := by positivity
    linarith
  have hbase := ordinaryHypergeometric_hasSum_of_c
    (a + (N + 1)) (b + (N + 1)) (((N + 2 : ℕ) : ℂ)) hc hz
  have htail : HasSum
      (fun m : ℕ => olverHypergeometricCoefficient a b (-(N : ℂ)) (m + (N + 1)) *
        z ^ (m + (N + 1)))
      (C * ₂F₁ (a + (N + 1)) (b + (N + 1)) ((N + 2 : ℕ) : ℂ) z) := by
    refine (hbase.mul_left C).congr_fun ?_
    exact fun m => olver_neg_nat_tail_term a b z N m
  have hfull := (hasSum_nat_add_iff (f := fun k : ℕ =>
    olverHypergeometricCoefficient a b (-(N : ℂ)) k * z ^ k) (N + 1)).mp htail
  have hfin : ∑ k ∈ Finset.range (N + 1),
      olverHypergeometricCoefficient a b (-(N : ℂ)) k * z ^ k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact olver_neg_nat_initial_term a b z N k (Finset.mem_range.mp hk)
  rw [hfin, add_zero] at hfull
  rw [olverHypergeometric_eq_tsum]
  exact hfull.tsum_eq

-- no-dlmf: the global analytic-continuation existence theorem
/-- The regular Gauss germ has an analytic continuation to the principal slit
plane.  This theorem is the explicit mathematical gap behind the global
Chapter 15 transformation surfaces. -/
theorem exists_principalGaussContinuation (a b c : ℂ) (hc : GaussRegular c) :
    Nonempty (PrincipalGaussContinuation a b c) := by
  classical
  have hc' : ∀ n : ℕ, (n : ℂ) ≠ -c := by
    intro n hn
    apply hc n
    linear_combination hn
  let x₀ : GaussOrdinaryPoint :=
    ⟨-(1 / 2 : ℂ), by
      change -(-(1 / 2 : ℂ)) ∈ Complex.slitPlane
      norm_num [Complex.mem_slitPlane_iff]⟩
  let t₀ : ℂ × ℂ :=
    (₂F₁ a b c x₀.1, deriv (₂F₁ a b c : ℂ → ℂ) x₀.1)
  obtain ⟨g₀, hg₀⟩ := gaussJetLocal_stalkToFiber_surjective a b c x₀ t₀
  obtain ⟨s, hs, hs₀⟩ :=
    FLMF.Methods.ODEContinuation.exists_global_of_unique_local_sections
      (gaussJetLocal a b c)
      (gaussJetLocal_stalkToFiber_injective a b c)
      (gaussJetLocal_unique_local_sections a b c) x₀ g₀
  have hs₀' : s x₀ = t₀ := hs₀.trans hg₀
  obtain ⟨f, hf, hfode, hfjet⟩ :=
    exists_ambient_gauss_solution_of_top_section hs
  let O : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ gaussOrdinaryPrincipalDomain
  have hx₀O : x₀.1 ∈ O := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      norm_num [Complex.norm_real]
    · exact x₀.2
  have hOpre : IsPreconnected O :=
    (starConvex_neg_half_gauss_overlap.isPathConnected hx₀O).isConnected.isPreconnected
  have hpair : (f x₀.1, deriv f x₀.1) = t₀ := by
    rw [← hfjet x₀]
    exact hs₀'
  have heq : EqOn f (₂F₁ a b c) O := by
    refine FLMF.Methods.ODEContinuation.linODE2_eqOn_of_jet_eq'
      (P := fun z : ℂ => z * (1 - z))
      (Q := fun z : ℂ => c - (a + b + 1) * z)
      (R := fun _ : ℂ => -(a * b))
      (Metric.isOpen_ball.inter isOpen_gaussOrdinaryPrincipalDomain) hOpre
      ?_ ?_ ?_ ?_ (hf.mono Set.inter_subset_right)
      ((analyticOnNhd_ordinaryHypergeometric_of_c a b c hc').mono Set.inter_subset_left)
      ?_ ?_ hx₀O (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)
    · exact fun _ _ => analyticAt_id.mul (analyticAt_const.sub analyticAt_id)
    · exact fun _ _ => analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    · exact fun _ _ => analyticAt_const
    · intro z hz
      exact mul_ne_zero (gaussOrdinaryPrincipalDomain_ne_zero hz.2)
        (sub_ne_zero.mpr (gaussOrdinaryPrincipalDomain_ne_one hz.2).symm)
    · intro z hz
      have h := hfode z hz.2
      linear_combination h
    · intro z hz
      have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
      have h := ordinaryHypergeometric_ode_of_c a b c hc' hz'
      linear_combination h
  obtain ⟨F, hFa, hFseries, -⟩ :=
    FLMF.Methods.ODEContinuation.exists_analyticOnNhd_extension_union
      Metric.isOpen_ball isOpen_gaussOrdinaryPrincipalDomain
      (analyticOnNhd_ordinaryHypergeometric_of_c a b c hc') hf
      (fun z hz => (heq hz).symm)
  refine ⟨⟨F, ?_, hFseries⟩⟩
  rw [gaussPrincipalDomain_eq_ball_union_ordinary]
  exact hFa

-- no-dlmf: the regularized global analytic-continuation existence theorem
/-- Olver's regularized Gauss germ has an analytic continuation to the
principal slit plane, including singular lower parameters. -/
theorem exists_principalOlverContinuation (a b c : ℂ) :
    Nonempty (PrincipalOlverContinuation a b c) := by
  classical
  by_cases hc : GaussRegular c
  · obtain ⟨G⟩ := exists_principalGaussContinuation a b c hc
    let F : ℂ → ℂ := fun z => (Complex.Gamma c)⁻¹ * G.toFun z
    refine ⟨⟨F, ?_, ?_⟩⟩
    · exact fun z hz => analyticAt_const.mul (G.analyticOn z hz)
    · intro z hz
      have hGc : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero hc
      change (Complex.Gamma c)⁻¹ * G.toFun z = olverHypergeometric a b c z
      rw [G.eq_series hz, ordinaryHypergeometric_eq_Gamma_mul_olver hc]
      field_simp
  · simp only [GaussRegular, not_forall, not_ne_iff] at hc
    obtain ⟨N, rfl⟩ := hc
    let C : ℂ := (ascPochhammer ℂ (N + 1)).eval a *
      (ascPochhammer ℂ (N + 1)).eval b / (Nat.factorial (N + 1) : ℂ)
    have hreg : GaussRegular (((N + 2 : ℕ) : ℂ)) := by
      intro k h
      have hre := congrArg Complex.re h
      simp at hre
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hN : (0 : ℝ) < N + 2 := by positivity
      linarith
    obtain ⟨G⟩ := exists_principalGaussContinuation
      (a + (N + 1)) (b + (N + 1)) (((N + 2 : ℕ) : ℂ)) hreg
    let F : ℂ → ℂ := fun z => C * z ^ (N + 1) * G.toFun z
    refine ⟨⟨F, ?_, ?_⟩⟩
    · intro z hz
      exact (analyticAt_const.mul (analyticAt_id.pow (N + 1))).mul (G.analyticOn z hz)
    · intro z hz
      have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      change C * z ^ (N + 1) * G.toFun z = olverHypergeometric a b (-(N : ℂ)) z
      rw [G.eq_series hz]
      exact (olverHypergeometric_neg_nat_eq_shifted a b z N hz').symm

-- no-dlmf: named Gamma-quotient shorthand (the tagged 15.4.20 surface is the Gauss-sum theorem)
/-- The complex Gauss value `Γ(c)·Γ(c−a−b) / (Γ(c−a)·Γ(c−b))` — the DLMF
15.4.20 Gamma quotient (the right-hand side of Gauss's summation theorem),
as it appears in the `z = 1` connection coefficients.  Complex analogue of
`gaussValue`; see `gaussValue_ofReal` for the cast bridge. -/
def complexGaussValue (a b c : ℂ) : ℂ :=
  Complex.Gamma c * Complex.Gamma (c - a - b)
    / (Complex.Gamma (c - a) * Complex.Gamma (c - b))

-- no-dlmf: cast bridge between the real and complex Gamma-quotient shorthands
/-- The real Gauss value casts to the complex one. -/
theorem gaussValue_ofReal (a b c : ℝ) :
    ((gaussValue a b c : ℝ) : ℂ) = complexGaussValue a b c := by
  simp only [gaussValue, complexGaussValue]
  rw [show ((c : ℂ) - a - b) = ((c - a - b : ℝ) : ℂ) by push_cast; ring,
    show ((c : ℂ) - a) = ((c - a : ℝ) : ℂ) by push_cast; ring,
    show ((c : ℂ) - b) = ((c - b : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  ring

/-- The selected principal continuation of the ordinary Gauss function.
Values at singular lower parameters are intentionally unspecified (`0`); every
theorem using this function must carry `GaussRegular c`.

DLMF 15.2.1. -/
-- DAG: E-15.2.1.
-- Verified: verified (tier2)
noncomputable def principalGauss (a b c z : ℂ) : ℂ :=
  by
    classical
    exact if hc : GaussRegular c then
      Classical.choice (exists_principalGaussContinuation a b c hc) |>.toFun z
    else 0

/-- The selected principal continuation of Olver's regularized Gauss
function.

DLMF 15.2.2. -/
-- DAG: E-15.2.2.
-- Verified: unverified (tier2 DIVERGES)
noncomputable def principalOlver (a b c z : ℂ) : ℂ :=
  Classical.choice (exists_principalOlverContinuation a b c) |>.toFun z

-- no-dlmf: defining-disc agreement for the selected continuation
theorem principalGauss_eq_series {a b c z : ℂ} (hc : GaussRegular c)
    (hz : ‖z‖ < 1) : principalGauss a b c z = ₂F₁ a b c z := by
  classical
  rw [principalGauss, dif_pos hc]
  exact (Classical.choice (exists_principalGaussContinuation a b c hc)).eq_series
    (mem_ball_zero_iff.mpr hz)

-- no-dlmf: defining-disc agreement for the selected regularized continuation
theorem principalOlver_eq_series {a b c z : ℂ} (hz : ‖z‖ < 1) :
    principalOlver a b c z = olverHypergeometric a b c z :=
  (Classical.choice (exists_principalOlverContinuation a b c)).eq_series
    (mem_ball_zero_iff.mpr hz)

-- no-dlmf: analyticity of the selected ordinary continuation
theorem principalGauss_analyticOn {a b c : ℂ} (hc : GaussRegular c) :
    AnalyticOnNhd ℂ (principalGauss a b c) gaussPrincipalDomain := by
  classical
  have heq : principalGauss a b c =
      (Classical.choice (exists_principalGaussContinuation a b c hc)).toFun := by
    funext z
    simp [principalGauss, hc]
  rw [heq]
  exact (Classical.choice (exists_principalGaussContinuation a b c hc)).analyticOn

-- no-dlmf: analyticity of the selected regularized continuation
theorem principalOlver_analyticOn (a b c : ℂ) :
    AnalyticOnNhd ℂ (principalOlver a b c) gaussPrincipalDomain :=
  (Classical.choice (exists_principalOlverContinuation a b c)).analyticOn

end FLMF.Hypergeometric
