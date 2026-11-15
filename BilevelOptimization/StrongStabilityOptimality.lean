/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.PiecewiseSolution

/-!
# Optimality conditions based on strong stability

Thm. 5.4 of [Dempe 2002] (Dempe 1992), in the (LICQ) case: if the follower's problem is convex
and satisfies (LICQ) and (SSOC) at `(x̄, ȳ)`, its solution is a single point `y(x)` near `x̄`,
and at a local optimal solution of the bilevel problem the leader's objective has a nonnegative
directional derivative `∇f(x̄, ȳ)(r, y'(x̄; r))` along every direction `r` that is strictly
feasible for the leader's constraints (5.10), or, under (ULR), along every linearized feasible
direction (5.11).

## Main results

* `exists_solutionFunction_of_isConvexLower`: for a convex follower's problem with (LICQ) and
  (SSOC), `Ψ(x) = {y(x)}` near `x̄`, with `y(·)` `PC¹` and directionally differentiable, the
  derivative being the unique solution of `QP(λ⁰, r)` (4.20).
* `nonneg_fderiv_of_isLocalMinOn_bilevelFeasible`: Thm. 5.4, conditions (5.10) and (5.11).
* `LowerQPSystem`, `eq_of_lowerQPSystem`: the linear system of (5.12) is the KKT system of
  `QP(λ⁰, r)` with the constraints in `K` active, and determines `d = y'(x̄; r)`.
* `nonneg_of_lowerQPSystem_of_isLocalMinOn_bilevelFeasible`: the combinatorial form (5.12).
* `solutionMap_example`, `hasDerivAt_example`, `not_isLocalMinOn_example`: the example on p. 138,
  showing that the conditions are not sufficient.

## Differences from the book

* The book assumes (MFCQ), (SSOC) and (CRCQ) and gives no proof (it refers to [67] and says the
  result follows from Thm. 4.11 and the chain rule). We assume (LICQ), as in our versions of
  Thm. 4.4, 4.10 and 4.11.
* The optimal value of (5.10) (resp. (5.11)) being nonnegative is stated in the equivalent sign
  form: `∇f(x̄, ȳ)(r, y'(x̄; r)) ≥ 0` for every `r` with `∇Gₖ(x̄) r < 0` (resp. `≤ 0`) for the
  active `k`; the normalization `‖r‖ ≤ 1` is irrelevant by positive homogeneity.
* Local optimality is local minimality of `f` on the feasible set of (5.5)
  (`IsLocalOptimisticSolution.isLocalMinOn` provides it for local optimistic solutions), and
  convexity of the follower's problem is only needed near `x̄`.
* In (5.12), `EΛ(x̄, ȳ) = {λ⁰}` under (LICQ), and `v_α(λ⁰, K) ≥ 0` is stated as `α ≥ 0` at every
  feasible point; the normalization `‖r‖ ≤ 1` is dropped (the statement is stronger without it).
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι] [Fintype κ]
  {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {G : κ → E → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] in
/-- The feasible set of a convex follower's problem is convex. -/
theorem convex_lowerFeasible {x : E} (hconv : IsConvexLower φ g x) :
    Convex ℝ (lowerFeasible g x) := fun a ha b hb t u ht hu htu i ↦
  ((hconv.2 i).2 (mem_univ a) (mem_univ b) ht hu htu).trans (by
    simp only [smul_eq_mul]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (ha i))
      (mul_nonpos_of_nonneg_of_nonpos hu (hb i)))

variable [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The solution function of a convex follower's problem under (LICQ) and (SSOC): near `x̄`,
`Ψ(x) = {y(x)}` with `y(·)` continuous at `x̄`, `PC¹`, and directionally differentiable with the
directional derivative given by `QP(λ⁰, r)` (Thm. 4.4, 4.10, 4.11 of [Dempe 2002]). -/
theorem exists_solutionFunction_of_isConvexLower (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hconv : ∀ᶠ x in 𝓝 x₀, IsConvexLower φ g x) :
    ∃ s s' : E → F, s x₀ = y₀ ∧ ContinuousAt s x₀ ∧ IsPC1At s x₀ ∧
      (∀ᶠ x in 𝓝 x₀, solutionMap φ (lowerFeasible g) x = {s x}) ∧ HasDirDerivAt s s' x₀ ∧
      ∀ r, s' r ∈ lowerQPFeasible g x₀ y₀ lam₀ r ∧
        ∀ d ∈ lowerQPFeasible g x₀ y₀ lam₀ r, d ≠ s' r →
          lowerQPObjective φ g x₀ y₀ lam₀ r (s' r) < lowerQPObjective φ g x₀ y₀ lam₀ r d := by
  obtain ⟨δ, -, U, hU, s, hs₀, hsc, hs⟩ := isLowerStronglyStable hφ hg hkkt hlicq hssoc
  have hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x) := fun x hx ↦
    ⟨(hs x hx).2.1, (hs x hx).2.2.1⟩
  obtain ⟨s', hs', hqp⟩ := hasDirDerivAt_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  refine ⟨s, s', hs₀, hsc.continuousAt hU,
    isPC1At_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin, ?_, hs', hqp⟩
  filter_upwards [hU, hconv] with x hxU hcx
  obtain ⟨hball, hfeas, hloc, huniq⟩ := hs x hxU
  have hGc := convex_lowerFeasible hcx
  -- a local solution of a convex problem is a global one
  have hglob : s x ∈ solutionMap φ (lowerFeasible g) x :=
    ⟨hfeas, fun z hz ↦ IsMinOn.of_isLocalMinOn_of_convexOn hfeas hloc
      (hcx.1.subset (subset_univ _) hGc) hz⟩
  ext z
  rw [mem_singleton_iff]
  refine ⟨fun hz ↦ ?_, fun hz ↦ hz ▸ hglob⟩
  -- solutions form a convex set, and near `s x` they are local solutions in the ball
  by_contra hne
  have hcont : Tendsto (fun t : ℝ ↦ (1 - t) • s x + t • z) (𝓝[>] 0) (𝓝 (s x)) := by
    have : Continuous fun t : ℝ ↦ (1 - t) • s x + t • z := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht1, ht2⟩ :=
    ((hcont.eventually (Metric.isOpen_ball.mem_nhds hball)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hwG : (1 - t) • s x + t • z ∈ lowerFeasible g x :=
    hGc hfeas hz.1 (by linarith [ht2.2]) ht2.1.le (by ring)
  have hwmin : φ (x, (1 - t) • s x + t • z) ≤ φ (x, s x) := by
    have h1 := hcx.1.2 (mem_univ (s x)) (mem_univ z) (sub_nonneg.2 ht2.2.le) ht2.1.le (by ring)
    have h2 := hz.2 (s x) hfeas
    simp only [smul_eq_mul] at h1
    nlinarith [ht2.1]
  have hw := huniq _ ht1 hwG
    (IsMinOn.localize (isMinOn_iff.2 fun v hv ↦ hwmin.trans (hglob.2 v hv)))
  have h0 : t • (z - s x) = 0 := by
    rw [show t • (z - s x) = ((1 - t) • s x + t • z) - s x by module, hw, sub_self]
  exact hne (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left ht2.1.ne'))

/-- **Thm. 5.4 of [Dempe 2002]** under (LICQ): let `(x̄, ȳ)` be a local optimal solution of the
bilevel problem with leader constraints `Gₖ(x) ≤ 0`, where the follower's problem is convex near
`x̄` and satisfies (LICQ) and (SSOC) at `(x̄, ȳ)` with multiplier `λ⁰`. Then `Ψ(x) = {y(x)}` near
`x̄`, `y(·)` is directionally differentiable at `x̄` with `y'(x̄; r)` the unique solution of
`QP(λ⁰, r)`, and
* (5.10) `∇f(x̄, ȳ)(r, y'(x̄; r)) ≥ 0` whenever `∇Gₖ(x̄) r < 0` for all active `k`;
* (5.11) under (ULR), `∇f(x̄, ȳ)(r, y'(x̄; r)) ≥ 0` whenever `∇Gₖ(x̄) r ≤ 0` for all active `k`. -/
theorem nonneg_fderiv_of_isLocalMinOn_bilevelFeasible {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hf : DifferentiableAt ℝ f (x₀, y₀)) (hG : ∀ k, DifferentiableAt ℝ (G k) x₀)
    (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hconv : ∀ᶠ x in 𝓝 x₀, IsConvexLower φ g x)
    (hx₀ : ∀ k, G k x₀ ≤ 0)
    (hmin : IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) {x | ∀ k, G k x ≤ 0}) (x₀, y₀)) :
    ∃ s s' : E → F, s x₀ = y₀ ∧ (∀ᶠ x in 𝓝 x₀, solutionMap φ (lowerFeasible g) x = {s x}) ∧
      HasDirDerivAt s s' x₀ ∧
      (∀ r, s' r ∈ lowerQPFeasible g x₀ y₀ lam₀ r ∧
        ∀ d ∈ lowerQPFeasible g x₀ y₀ lam₀ r, d ≠ s' r →
          lowerQPObjective φ g x₀ y₀ lam₀ r (s' r) < lowerQPObjective φ g x₀ y₀ lam₀ r d) ∧
      (∀ r, (∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r < 0) → 0 ≤ fderiv ℝ f (x₀, y₀) (r, s' r)) ∧
      ((∃ r₀, ∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r₀ < 0) →
        ∀ r, (∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r ≤ 0) →
          0 ≤ fderiv ℝ f (x₀, y₀) (r, s' r)) := by
  obtain ⟨s, s', hs₀, hsc, hpc, hΨ, hs', hqp⟩ :=
    exists_solutionFunction_of_isConvexLower hφ hg hkkt hlicq hssoc hconv
  -- (5.10): a strictly feasible descent direction contradicts local optimality
  have h510 : ∀ r, (∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r < 0) →
      0 ≤ fderiv ℝ f (x₀, y₀) (r, s' r) := by
    intro r hr
    by_contra hneg
    push Not at hneg
    have hl : HasDerivAt (fun t : ℝ ↦ x₀ + t • r) r 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const r).const_add x₀
    have hγ : Tendsto (fun t : ℝ ↦ x₀ + t • r) (𝓝[>] 0) (𝓝 x₀) := by
      have hc : Continuous fun t : ℝ ↦ x₀ + t • r := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hsγ : Tendsto (fun t : ℝ ↦ s (x₀ + t • r)) (𝓝[>] 0) (𝓝 y₀) := by
      have := hsc.tendsto.comp hγ
      rwa [hs₀] at this
    have hp : Tendsto (fun t : ℝ ↦ (x₀ + t • r, s (x₀ + t • r))) (𝓝[>] 0) (𝓝 (x₀, y₀)) :=
      hγ.prodMk_nhds hsγ
    have h1 : Tendsto (fun t : ℝ ↦ t⁻¹ • ((x₀ + t • r) - x₀)) (𝓝[>] 0) (𝓝 r) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ by
        show r = t⁻¹ • (x₀ + t • r - x₀)
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul])
    have h2 : Tendsto (fun t : ℝ ↦ t⁻¹ • (s (x₀ + t • r) - y₀)) (𝓝[>] 0) (𝓝 (s' r)) := by
      have := hs' r
      rwa [hs₀] at this
    have hv : Tendsto (fun t : ℝ ↦ t⁻¹ • ((x₀ + t • r, s (x₀ + t • r)) - (x₀, y₀))) (𝓝[>] 0)
        (𝓝 (r, s' r)) :=
      (h1.prodMk_nhds h2).congr fun t ↦ rfl
    have hslope := tendsto_slope_comp_of_hasFDerivAt hf.hasFDerivAt hp hv
    -- eventually, the leader's constraints hold along the ray
    have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, G k (x₀ + t • r) ≤ 0 := by
      refine eventually_all.2 fun k ↦ ?_
      rcases (hx₀ k).eq_or_lt with hk | hk
      · have hd : HasDerivAt (fun t : ℝ ↦ G k (x₀ + t • r)) (fderiv ℝ (G k) x₀ r) 0 :=
          (hG k).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
        filter_upwards [hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds (hr k hk)),
          self_mem_nhdsWithin] with t ht (ht0 : 0 < t)
        simp only [zero_add, zero_smul, add_zero, hk, sub_zero, smul_eq_mul] at ht
        by_contra hpos
        exact absurd ht (not_lt.2 (mul_nonneg (inv_nonneg.2 ht0.le) (not_le.1 hpos).le))
      · exact (((hG k).continuousAt.tendsto.comp hγ).eventually (eventually_lt_nhds hk)).mono
          fun t ht ↦ ht.le
    have hmin' := (eventually_nhdsWithin_iff.1 hmin)
    obtain ⟨t, ht0, htG, htΨ, htmin, htlt⟩ := ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
      (hfeas.and ((hγ.eventually hΨ).and ((hp.eventually hmin').and
        (hslope.eventually (eventually_lt_nhds hneg)))))).exists
    have hmem : (x₀ + t • r, s (x₀ + t • r)) ∈
        bilevelFeasible φ (lowerFeasible g) {x | ∀ k, G k x ≤ 0} :=
      ⟨htG, by rw [htΨ]; exact mem_singleton _⟩
    have hle := htmin hmem
    simp only [smul_eq_mul] at htlt
    have := mul_nonneg (inv_nonneg.2 ht0.le) (sub_nonneg.2 hle)
    linarith
  refine ⟨s, s', hs₀, hΨ, hs', hqp, h510, fun ⟨r₀, hr₀⟩ r hr ↦ ?_⟩
  -- (5.11): `y'(x̄; ·)` is Lipschitz, so (5.10) passes to the closure
  obtain ⟨K, V, hV, hL⟩ := hpc.exists_lipschitzOnWith
  have hcont : Continuous s' := (LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [dist_eq_norm, dist_eq_norm]
    exact hs'.norm_sub_le hV hL a b).continuous
  have hc : Continuous fun ε : ℝ ↦ fderiv ℝ f (x₀, y₀) (r + ε • r₀, s' (r + ε • r₀)) :=
    (fderiv ℝ f (x₀, y₀)).continuous.comp ((by fun_prop : Continuous fun ε : ℝ ↦ r + ε • r₀).prodMk
      (hcont.comp (by fun_prop)))
  have hlim : Tendsto (fun ε : ℝ ↦ fderiv ℝ f (x₀, y₀) (r + ε • r₀, s' (r + ε • r₀))) (𝓝[>] 0)
      (𝓝 (fderiv ℝ f (x₀, y₀) (r, s' r))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
    h510 _ fun k hk ↦ ?_)
  rw [map_add, map_smul, smul_eq_mul]
  linarith [hr k hk, mul_neg_of_pos_of_neg hε (hr₀ k hk)]

/-! ### The combinatorial form (5.12) -/

section Combinatorial

variable (φ g) in
/-- The linear system of the problem defining `v_α(λ⁰, K)` in (5.12) of [Dempe 2002] (without the
rows involving `α`): the KKT conditions of `QP(λ⁰, r)` (4.20) with the constraints in `K` active,
`∇²_yx L r + ∇²_yy L d + ∑ γᵢ ∇_y gᵢ = 0`, `∇gᵢ(x̄, ȳ)(r, d) = 0` for `i ∈ K`,
`∇gᵢ(x̄, ȳ)(r, d) ≤ 0` for active `i ∉ K`, `γᵢ ≥ 0` for `i ∈ K \ J(λ⁰)` and `γᵢ = 0` for
`i ∉ K`. -/
def LowerQPSystem (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (K : Finset ι) (r : E) (d : F)
    (γ : ι → ℝ) : Prop :=
  lowerMixedHessian φ g x₀ y₀ lam₀ r + lowerHessian φ g x₀ y₀ lam₀ d +
      ∑ i, γ i • fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = 0 ∧
    (∀ i ∈ K, fderiv ℝ (g i) (x₀, y₀) (r, d) = 0) ∧
    (∀ i ∉ K, g i (x₀, y₀) = 0 → fderiv ℝ (g i) (x₀, y₀) (r, d) ≤ 0) ∧
    (∀ i ∈ K, ¬ 0 < lam₀ i → 0 ≤ γ i) ∧ (∀ i ∉ K, γ i = 0)

omit [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem mem_lowerQPFeasible_of_lowerQPSystem {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} {K : Finset ι}
    {r : E} {d : F} {γ : ι → ℝ} (hJK : ∀ i, 0 < lam₀ i → i ∈ K)
    (hsys : LowerQPSystem φ g x₀ y₀ lam₀ K r d γ) : d ∈ lowerQPFeasible g x₀ y₀ lam₀ r := by
  refine ⟨fun i hi ↦ hsys.2.1 i (hJK i hi), fun i hi ↦ ?_⟩
  by_cases hiK : i ∈ K
  · exact (hsys.2.1 i hiK).le
  · exact hsys.2.2.1 i hiK hi

omit [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A solution of the system of (5.12) minimizes `QP(λ⁰, r)`. -/
theorem lowerQPObjective_le_of_lowerQPSystem (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hssoc : LowerSSOC φ g x₀ y₀) {K : Finset ι} {r : E}
    {d : F} {γ : ι → ℝ} (hJK : ∀ i, 0 < lam₀ i → i ∈ K) (hKI : ∀ i ∈ K, g i (x₀, y₀) = 0)
    (hsys : LowerQPSystem φ g x₀ y₀ lam₀ K r d γ) :
    ∀ d' ∈ lowerQPFeasible g x₀ y₀ lam₀ r,
      lowerQPObjective φ g x₀ y₀ lam₀ r d ≤ lowerQPObjective φ g x₀ y₀ lam₀ r d' := by
  intro d' hd'
  have hgd : ∀ i, DifferentiableAt ℝ (g i) (x₀, y₀) := fun i ↦
    (hg i).differentiable (by norm_num) _
  set e := d' - d with he
  have hsub : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ e =
      fderiv ℝ (g i) (x₀, y₀) (r, d') - fderiv ℝ (g i) (x₀, y₀) (r, d) := fun i ↦ by
    rw [he, ← fderiv_apply_sub_section (hgd i), map_sub]
  have hlin : ∑ i, γ i * fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ e ≤ 0 := by
    refine Finset.sum_nonpos fun i _ ↦ ?_
    by_cases hiK : i ∈ K
    · rw [hsub, hsys.2.1 i hiK, sub_zero]
      by_cases hi : 0 < lam₀ i
      · rw [hd'.1 i hi, mul_zero]
      · exact mul_nonpos_of_nonneg_of_nonpos (hsys.2.2.2.1 i hiK hi) (hd'.2 i (hKI i hiK))
    · rw [hsys.2.2.2.2 i hiK, zero_mul]
  have hquad : 0 ≤ lowerHessian φ g x₀ y₀ lam₀ e e := by
    by_cases he0 : e = 0
    · simp [he0]
    · refine (hssoc lam₀ hkkt e he0 fun i hi ↦ ?_).le
      rw [hsub, hd'.1 i hi, hsys.2.1 i (hJK i hi), sub_zero]
  have h0 := congrArg (fun ℓ : StrongDual ℝ F ↦ ℓ e) hsys.1
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at h0
  have hd'e : d' = d + e := by rw [he, add_sub_cancel]
  unfold lowerQPObjective
  rw [hd'e]
  simp only [map_add, add_apply]
  rw [lowerHessian_symm hφ hg _ _ _ e d]
  linarith

omit [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Under (SSOC), the system of (5.12) determines `d` as the unique solution of `QP(λ⁰, r)`. -/
theorem eq_of_lowerQPSystem (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E}
    {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hssoc : LowerSSOC φ g x₀ y₀)
    {K : Finset ι} {r : E} {d d₀ : F} {γ : ι → ℝ} (hJK : ∀ i, 0 < lam₀ i → i ∈ K)
    (hKI : ∀ i ∈ K, g i (x₀, y₀) = 0) (hsys : LowerQPSystem φ g x₀ y₀ lam₀ K r d γ)
    (hd₀ : d₀ ∈ lowerQPFeasible g x₀ y₀ lam₀ r ∧
      ∀ d ∈ lowerQPFeasible g x₀ y₀ lam₀ r, d ≠ d₀ →
        lowerQPObjective φ g x₀ y₀ lam₀ r d₀ < lowerQPObjective φ g x₀ y₀ lam₀ r d) :
    d = d₀ := by
  by_contra hne
  have h1 := hd₀.2 d (mem_lowerQPFeasible_of_lowerQPSystem hJK hsys) hne
  have h2 := lowerQPObjective_le_of_lowerQPSystem hφ hg hkkt hssoc hJK hKI hsys d₀ hd₀.1
  linarith

/-- **(5.12) of [Dempe 2002]** under (LICQ), where `EΛ(x̄, ȳ) = {λ⁰}`: under the assumptions of
Thm. 5.4, for every index set `K` with `J(λ⁰) ⊆ K ⊆ I(x̄, ȳ)`, the problem defining `v_α(λ⁰, K)`
has only feasible points with `α ≥ 0`; under (ULR), the rows `∇Gₖ(x̄) r ≤ α` can be replaced
by `∇Gₖ(x̄) r ≤ 0`. -/
theorem nonneg_of_lowerQPSystem_of_isLocalMinOn_bilevelFeasible {x₀ : E} {y₀ : F}
    {lam₀ : ι → ℝ} (hf : DifferentiableAt ℝ f (x₀, y₀)) (hG : ∀ k, DifferentiableAt ℝ (G k) x₀)
    (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hconv : ∀ᶠ x in 𝓝 x₀, IsConvexLower φ g x)
    (hx₀ : ∀ k, G k x₀ ≤ 0)
    (hmin : IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) {x | ∀ k, G k x ≤ 0}) (x₀, y₀)) :
    (∀ K : Finset ι, (∀ i, 0 < lam₀ i → i ∈ K) → (∀ i ∈ K, g i (x₀, y₀) = 0) →
      ∀ (r : E) (d : F) (γ : ι → ℝ) (α : ℝ), LowerQPSystem φ g x₀ y₀ lam₀ K r d γ →
        fderiv ℝ f (x₀, y₀) (r, d) ≤ α → (∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r ≤ α) →
          0 ≤ α) ∧
    ((∃ r₀, ∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r₀ < 0) →
      ∀ K : Finset ι, (∀ i, 0 < lam₀ i → i ∈ K) → (∀ i ∈ K, g i (x₀, y₀) = 0) →
        ∀ (r : E) (d : F) (γ : ι → ℝ), LowerQPSystem φ g x₀ y₀ lam₀ K r d γ →
          (∀ k, G k x₀ = 0 → fderiv ℝ (G k) x₀ r ≤ 0) → 0 ≤ fderiv ℝ f (x₀, y₀) (r, d)) := by
  obtain ⟨s, s', -, -, -, hqp, h510, h511⟩ := nonneg_fderiv_of_isLocalMinOn_bilevelFeasible hf hG
    hφ hg hkkt hlicq hssoc hconv hx₀ hmin
  refine ⟨fun K hJK hKI r d γ α hsys hfα hGα ↦ ?_, fun hulr K hJK hKI r d γ hsys hr ↦ ?_⟩
  · rw [eq_of_lowerQPSystem hφ hg hkkt hssoc hJK hKI hsys (hqp r)] at hfα
    by_contra hα
    push Not at hα
    have := h510 r fun k hk ↦ (hGα k hk).trans_lt hα
    linarith
  · rw [eq_of_lowerQPSystem hφ hg hkkt hssoc hJK hKI hsys (hqp r)]
    exact h511 hulr r hr

end Combinatorial

/-! ### Example p. 138: the conditions are not sufficient -/

section Example

/-- The leader's objective of the example on p. 138 of [Dempe 2002] (letters swapped). -/
def exampleF (p : ℝ × ℝ) : ℝ := (p.2 + 4) ^ 2 + (p.1 - 3.5) ^ 2

/-- The follower's objective of the example on p. 138: `(y - 3)²`. -/
def exampleφ (p : ℝ × ℝ) : ℝ := (p.2 - 3) ^ 2

/-- The follower's constraint of the example on p. 138: `y² ≤ x`. -/
def exampleg (_ : Unit) (p : ℝ × ℝ) : ℝ := p.2 ^ 2 - p.1

theorem solutionMap_example {x : ℝ} (hx : 0 < x) (hx9 : x < 9) :
    solutionMap exampleφ (lowerFeasible exampleg) x = {√x} := by
  have hs : √x < 3 := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hx.le hx9
  have hsq : √x ^ 2 = x := Real.sq_sqrt hx.le
  have hle : ∀ z : ℝ, z ^ 2 ≤ x → z ≤ √x := fun z hz ↦
    (le_abs_self z).trans (Real.abs_le_sqrt hz)
  have hfeas : √x ∈ lowerFeasible exampleg x := fun _ ↦ by simp [exampleg, hsq]
  ext y
  simp only [mem_singleton_iff]
  constructor
  · rintro ⟨hy, hmin⟩
    have h1 := hmin √x hfeas
    have h2 := hle y (by have := hy (); simp only [exampleg] at this; linarith)
    simp only [exampleφ] at h1
    nlinarith
  · rintro rfl
    refine ⟨hfeas, fun z hz ↦ ?_⟩
    have h2 := hle z (by have := hz (); simp only [exampleg] at this; linarith)
    simp only [exampleφ]
    nlinarith

/-- In the example on p. 138 of [Dempe 2002] the composite objective `x ↦ f(x, y(x))` with
`y(x) = √x` is stationary at `x̄ = 1`, so the first-order conditions (5.10), (5.11) hold there. -/
theorem hasDerivAt_example : HasDerivAt (fun x ↦ exampleF (x, √x)) 0 1 := by
  have h := (((Real.hasDerivAt_sqrt one_ne_zero).add_const 4).pow 2).add
    (((hasDerivAt_id (1 : ℝ)).sub_const 3.5).pow 2)
  show HasDerivAt (fun x ↦ (√x + 4) ^ 2 + (x - 3.5) ^ 2) 0 1
  refine h.congr_deriv ?_
  norm_num

/-- ... but `(1, 1)` is not a local optimal solution of the bilevel problem: the conditions of
Thm. 5.4 are not sufficient. -/
theorem not_isLocalMinOn_example :
    ¬ IsLocalMinOn exampleF (bilevelFeasible exampleφ (lowerFeasible exampleg) univ) (1, 1) := by
  intro hmin
  have hc : Tendsto (fun u : ℝ ↦ (u ^ 2, u)) (𝓝[<] 1) (𝓝 (1, 1)) := by
    have : Continuous fun u : ℝ ↦ (u ^ 2, u) := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  obtain ⟨u, hu, hmin'⟩ := ((show ∀ᶠ u in 𝓝[<] (1 : ℝ), u ∈ Ioo 0 1 from
    Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)).and
    (hc.eventually (eventually_nhdsWithin_iff.1 hmin))).exists
  obtain ⟨hu0, hu1⟩ := hu
  have hmem : (u ^ 2, u) ∈ bilevelFeasible exampleφ (lowerFeasible exampleg) univ := by
    refine ⟨mem_univ _, ?_⟩
    rw [solutionMap_example (by positivity) (by nlinarith), Real.sqrt_sq hu0.le]
    exact mem_singleton u
  have := hmin' hmem
  simp only [exampleF] at this
  nlinarith [mul_pos (pow_pos (sub_pos.2 hu1) 3) (show (0 : ℝ) < u + 3 by linarith)]

end Example

end Bilevel
