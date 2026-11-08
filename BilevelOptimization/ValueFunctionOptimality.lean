/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.KKT
import BilevelOptimization.LipschitzProgram
import BilevelOptimization.ValueFunction

/-!
# Optimality conditions via the follower's value function

Sect. 5.6 of [Dempe 2002]: the optimistic bilevel problem as the one-level problem (5.36)

`min f(x, y)` subject to `φ(x, y) - μ(x) ≤ 0`, `gᵢ(x, y) ≤ 0`, `hⱼ(x) ≤ 0`,

where `μ` is the follower's optimal value function, and its necessary optimality conditions in
terms of Clarke's generalized gradient of `μ` (Thm. 4.17).

## Main definitions

* `valueConstraints`: the inequality constraints of (5.36), with a real function in place of `μ`.

## Main results

* `exists_abnormalMultiplier_valueConstraints`: Thm. 5.19 of [Dempe 2002]: (5.36) has a nontrivial
  abnormal multiplier.
* `not_nonsmoothMFCQ_valueConstraints`: neither (NMFCQ) nor (NLICQ) holds for (5.36).
* `exists_fritzJohn_valueFunction`: Thm. 5.20 (Fritz John conditions).
* `exists_kkt_valueFunction`: Thm. 5.21 (KKT conditions under partial calmness).

## Notation

Leader variable `x ∈ E`, follower variable `y ∈ F` (the book uses `y` for the leader). The
book's `F`, `f`, `g`, `G` are `f`, `φ`, `g`, `h` here; the follower has no equality constraints.
The multipliers `μ₀`, `γ`, `ξ` of the book are `μ₀`, `β`, `α`, and the convex combination
`∑ ζₖ ∇ₓL(x̄, yᵏ, λᵏ)` is an element `w` of `co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`.

## Remarks on the book

* Assumption (C) is replaced by continuity of `φ`, `gᵢ` and local boundedness of the follower's
  feasible-set map, as in `ValueFunction.lean`; (MFCQ) is lower-level regularity
  (`VariationalAnalysis.LowerLevelRegular`).
* Thm. 5.19 only needs (MFCQ) at `(x̄, ȳ)` and a function `μ'` Lipschitz around `x̄` that agrees
  with `μ` near `x̄` and has `co ⋃ {∇ₓL(x̄, y, λ)} ⊆ ∂̄μ'(x̄)`. Under (C) and (MFCQ) at all
  `y ∈ Ψ(x̄)`, Thm. 4.14 provides `μ'` and Thm. 4.17 gives the reverse inclusion, so this hypothesis
  is "equality holds in (4.27)".
* The book states Thm. 5.20 without nontriviality of the multipliers; it is added here, since
  otherwise the zero multipliers satisfy the conditions.
* Thm. 5.21 does not need equality in (4.27). The proof follows the book (exact penalization by
  partial calmness, then the KKT conditions for Lipschitz programs), with (MFCQ) for the penalized
  problem checked in the dual form: a vanishing leading multiplier contradicts lower-level
  regularity at `(x̄, ȳ)` and (ULR).
-/

open Filter Topology Set
open scoped NNReal Pointwise
open VariationalAnalysis (lowerFeasible lowerSolution lowerValue clarkeSubdiff LowerLevelRegular
  UpperLevelRegular LocallyBoundedAt PartiallyCalm)
open ContinuousLinearMap (inl inr fst)

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι J : Type*} [Fintype ι] [Fintype J] {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {h : J → E → ℝ}
  {x₀ : E} {y₀ : F}

variable (φ g h) in
/-- The inequality constraints of (5.36) of [Dempe 2002], indexed by `Option (ι ⊕ J)`:
`φ(x, y) - μ(x) ≤ 0` (`none`), `gᵢ(x, y) ≤ 0` and `hⱼ(x) ≤ 0`. -/
def valueConstraints (μ : E → ℝ) : Option (ι ⊕ J) → E × F → ℝ :=
  fun k ↦ k.elim (fun p ↦ φ p - μ p.1) (Sum.elim g fun j p ↦ h j p.1)

omit [FiniteDimensional ℝ E] [Fintype J] in
/-- The KKT conditions of the follower's problem at a solution `ȳ ∈ Ψ(x̄)` under (MFCQ), with
partial gradients written as `∇φ(x̄, ȳ) ∘ inr`. -/
theorem exists_lowerMultiplier (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i (x₀, y₀) = 0) ∧
      (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
        ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 := by
  have hφd : DifferentiableAt ℝ φ (x₀, y₀) := hφ.differentiableAt one_ne_zero
  have hgd : ∀ i, DifferentiableAt ℝ (g i) (x₀, y₀) := fun i ↦ (hg i).differentiableAt one_ne_zero
  obtain ⟨lam, -, hl0, hcs, heq⟩ := exists_isLowerKKT_of_mem_solutionMap (φ := φ) (g := g)
    (by rw [solutionMap_lowerFeasible]; exact hy₀)
    (hφd.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀).differentiableAt)
    (fun i ↦ (hg i).comp y₀ (contDiff_prodMk_right x₀).contDiffAt)
    ((lowerPLI_iff_lowerLevelRegular hgd).2 hreg)
  have hs : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) :=
    fun i ↦ fderiv_section (hgd i)
  refine ⟨lam, hl0, hcs, ?_⟩
  simpa only [hs, fderiv_section hφd] using heq

theorem mem_clarkeSubdiff_comp_fst {ψ : E → ℝ} (hψ : ContDiffAt ℝ 1 ψ x₀) :
    (fderiv ℝ ψ x₀).comp (fst ℝ E F) ∈ clarkeSubdiff (fun p : E × F ↦ ψ p.1) (x₀, y₀) := by
  have := VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt
    (f := fun p : E × F ↦ ψ p.1) (x₀ := (x₀, y₀))
    ((hψ.hasStrictFDerivAt one_ne_zero).comp (x₀, y₀) (hasStrictFDerivAt_fst (p := (x₀, y₀))))
  rw [this]
  exact mem_singleton _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem mem_clarkeSubdiff_of_contDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {ψ : X → ℝ} {p : X} (hψ : ContDiffAt ℝ 1 ψ p) : fderiv ℝ ψ p ∈ clarkeSubdiff ψ p := by
  rw [VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt
    (hψ.hasStrictFDerivAt one_ne_zero)]
  exact mem_singleton _

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem eq_of_mem_clarkeSubdiff_of_contDiffAt {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] {ψ : X → ℝ} {p : X} {ξ : StrongDual ℝ X} (hψ : ContDiffAt ℝ 1 ψ p)
    (hξ : ξ ∈ clarkeSubdiff ψ p) : ξ = fderiv ℝ ψ p := by
  rwa [VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt
    (hψ.hasStrictFDerivAt one_ne_zero), mem_singleton_iff] at hξ

theorem eq_of_mem_clarkeSubdiff_comp_fst {ψ : E → ℝ} {ξ : StrongDual ℝ (E × F)}
    (hψ : ContDiffAt ℝ 1 ψ x₀) (hξ : ξ ∈ clarkeSubdiff (fun p : E × F ↦ ψ p.1) (x₀, y₀)) :
    ξ = (fderiv ℝ ψ x₀).comp (fst ℝ E F) := by
  have := VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt
    (f := fun p : E × F ↦ ψ p.1) (x₀ := (x₀, y₀))
    ((hψ.hasStrictFDerivAt one_ne_zero).comp (x₀, y₀) (hasStrictFDerivAt_fst (p := (x₀, y₀))))
  rwa [this, mem_singleton_iff] at hξ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Fintype ι] [Fintype J] in
theorem lowerValue_eq_coe {U : Set E} {μ : E → ℝ} (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x) : μ x₀ = φ (x₀, y₀) := by
  have := hμ x₀ (mem_of_mem_nhds hU)
  rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀] at this
  exact (EReal.coe_eq_coe_iff.1 this).symm

/-- Thm. 5.19 of [Dempe 2002]: let `ȳ ∈ Ψ(x̄)`, let the follower's data be `C¹` at `(x̄, ȳ)` with
(MFCQ) there, `hⱼ` be `C¹` at `x̄`, and let `μ'` be Lipschitz around `x̄`, agree with `μ` near
`x̄`, and satisfy `co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)} ⊆ ∂̄μ'(x̄)` (equality in (4.27),
see `clarkeSubdiff_lowerValue_subset`). Then (5.36) has a nontrivial abnormal multiplier at
`(x̄, ȳ)`: with `λ ∈ Λ(x̄, ȳ)`, the multiplier `(1, λ, 0)`. -/
theorem exists_abnormalMultiplier_valueConstraints (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hh : ∀ j, ContDiffAt ℝ 1 (h j) x₀) {U : Set E}
    {L : ℝ≥0} {μ : E → ℝ} (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x)
    (hL : LipschitzOnWith L μ U)
    (heq : convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y) ⊆
      clarkeSubdiff μ x₀) :
    ∃ m ∈ abnormalMultipliers (valueConstraints φ g h μ) (Empty.elim : Empty → E × F → ℝ)
      (x₀, y₀), m ≠ 0 := by
  obtain ⟨lam, hl0, hcs, hKKT⟩ := exists_lowerMultiplier hy₀ hφ hg hreg
  set u : StrongDual ℝ E := (fderiv ℝ φ (x₀, y₀)).comp (inl ℝ E F) +
    ∑ i, lam i • (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F) with hu_def
  have hu : u ∈ clarkeSubdiff μ x₀ :=
    heq (subset_convexHull ℝ _ (mem_biUnion hy₀ ⟨lam, hl0, hcs, hKKT, rfl⟩))
  have hμ₀ := lowerValue_eq_coe hy₀ hU hμ
  have hS0 : fderiv ℝ φ (x₀, y₀) - u.comp (fst ℝ E F) ∈
      clarkeSubdiff (valueConstraints φ g h μ none) (x₀, y₀) := by
    show _ ∈ clarkeSubdiff (fun q ↦ φ q - μ q.1) (x₀, y₀)
    rw [clarkeSubdiff_sub_comp_fst (hφ.hasStrictFDerivAt one_ne_zero) hU hL]
    exact ⟨_, mem_singleton _, _, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨(fun k ↦ k.elim 1 (Sum.elim lam 0), 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro (_ | i | j)
    exacts [zero_le_one, hl0 i, le_rfl]
  · rintro (_ | i | j)
    · show (1 : ℝ) * (φ (x₀, y₀) - μ x₀) = 0
      rw [hμ₀]
      ring
    · exact hcs i
    · exact zero_mul _
  · refine ⟨fun k ↦ k.elim (fderiv ℝ φ (x₀, y₀) - u.comp (fst ℝ E F))
      (Sum.elim (fun i ↦ fderiv ℝ (g i) (x₀, y₀)) fun j ↦ (fderiv ℝ (h j) x₀).comp (fst ℝ E F)),
      ?_, Empty.elim, fun e ↦ e.elim, ?_⟩
    · rintro (_ | i | j)
      · exact hS0
      · exact mem_clarkeSubdiff_of_contDiffAt (hg i)
      · exact mem_clarkeSubdiff_comp_fst (hh j)
    · simp only [Fintype.sum_option, Fintype.sum_sum_type, Finset.univ_eq_empty, add_zero, Option.elim, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        zero_smul, Finset.sum_const_zero, one_smul]
      refine ContinuousLinearMap.ext fun p ↦ ?_
      obtain ⟨a, b⟩ := p
      have e1 := congrArg (fun T : StrongDual ℝ F ↦ T b) hKKT
      simp only [hu_def, add_apply, sub_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
        sum_apply, smul_apply, smul_eq_mul,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
        zero_apply] at e1 ⊢
      rw [show ((a, b) : E × F) = (a, 0) + (0, b) by simp]
      simp only [map_add, mul_add, Finset.sum_add_distrib]
      linarith
  · intro h0
    have := congrArg (fun m : (Option (ι ⊕ J) → ℝ) × (Empty → ℝ) ↦ m.1 none) h0
    simp at this

/-- Thm. 5.19 of [Dempe 2002], consequence: under the assumptions of
`exists_abnormalMultiplier_valueConstraints`, neither (NMFCQ) nor (NLICQ) holds for (5.36) at
`(x̄, ȳ)` (Thm. 5.18). -/
theorem not_nonsmoothMFCQ_valueConstraints (hy₀ : y₀ ∈ lowerSolution φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) (hh : ∀ j, ContDiffAt ℝ 1 (h j) x₀) {U : Set E}
    {L : ℝ≥0} {μ : E → ℝ} (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x)
    (hL : LipschitzOnWith L μ U)
    (heq : convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y) ⊆
      clarkeSubdiff μ x₀) :
    ¬ NonsmoothMFCQ (valueConstraints φ g h μ) (Empty.elim : Empty → E × F → ℝ) (x₀, y₀) ∧
      ¬ NonsmoothLICQ (valueConstraints φ g h μ) (Empty.elim : Empty → E × F → ℝ) (x₀, y₀) := by
  obtain ⟨m, hm, hne⟩ :=
    exists_abnormalMultiplier_valueConstraints hy₀ hφ hg hreg hh hU hμ hL heq
  obtain ⟨-, -, η, hη, -⟩ := id hm
  have hG : ∀ k, (clarkeSubdiff (valueConstraints φ g h μ k) (x₀, y₀)).Nonempty :=
    fun k ↦ ⟨η k, hη k⟩
  have hH : ∀ e : Empty, (clarkeSubdiff ((Empty.elim : Empty → E × F → ℝ) e) (x₀, y₀)).Nonempty :=
    fun e ↦ e.elim
  have hMF : ¬ NonsmoothMFCQ (valueConstraints φ g h μ) (Empty.elim : Empty → E × F → ℝ)
      (x₀, y₀) := by
    rw [nonsmoothMFCQ_iff_abnormalMultipliers_eq hG hH]
    intro hΛ
    rw [hΛ] at hm
    exact hne hm
  exact ⟨hMF, fun hLI ↦ hMF (hLI.nonsmoothMFCQ hG hH)⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι] [Fintype J] in
theorem lipschitzOnWith_comp_fst {ψ : E → ℝ} {K : ℝ≥0} {V : Set E}
    (hψ : LipschitzOnWith K ψ V) :
    LipschitzOnWith (K * 1) (fun p : E × F ↦ ψ p.1) (Prod.fst ⁻¹' V) :=
  hψ.comp LipschitzWith.prod_fst.lipschitzOnWith fun _ hp ↦ hp

/-- Thm. 5.20 of [Dempe 2002] (Fritz John conditions): let `(x̄, ȳ)` be a local solution of (5.36),
let the `gᵢ` and `φ` be continuous, the follower's feasible-set map be locally bounded at `x̄`, and
let the follower's data be `C¹` with (MFCQ) at all `(x̄, y)`, `y ∈ Ψ(x̄)`; let `f` be `C¹` at
`(x̄, ȳ)` and the `hⱼ` at `x̄`. Then there are `κ₀ ∈ {0, 1}`, `μ₀ ≥ 0`, `β, α ≥ 0`, not all zero,
with complementary slackness, and
`w ∈ co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}` such that
`κ₀ ∇ₓf + μ₀ (∇ₓφ - w) + ∑ βᵢ ∇ₓgᵢ + ∑ αⱼ ∇hⱼ = 0` and `κ₀ ∇_yf + μ₀ ∇_yφ + ∑ βᵢ ∇_ygᵢ = 0`. -/
theorem exists_fritzJohn_valueFunction (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y)
    (hp₀ : (x₀, y₀) ∈ bilevelFeasible φ (lowerFeasible g) {x | ∀ j, h j x ≤ 0})
    (hmin : IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) {x | ∀ j, h j x ≤ 0}) (x₀, y₀))
    (hf : ContDiffAt ℝ 1 f (x₀, y₀)) (hh : ∀ j, ContDiffAt ℝ 1 (h j) x₀) :
    ∃ κ₀ μ₀ : ℝ, ∃ β : ι → ℝ, ∃ α : J → ℝ, (κ₀ = 0 ∨ κ₀ = 1) ∧ 0 ≤ μ₀ ∧ (κ₀, μ₀, β, α) ≠ 0 ∧
      (∀ i, 0 ≤ β i ∧ β i * g i (x₀, y₀) = 0) ∧ (∀ j, 0 ≤ α j ∧ α j * h j x₀ = 0) ∧
      ∃ w ∈ convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y),
        κ₀ • (fderiv ℝ f (x₀, y₀)).comp (inl ℝ E F) +
            μ₀ • ((fderiv ℝ φ (x₀, y₀)).comp (inl ℝ E F) - w) +
            ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F) +
            ∑ j, α j • fderiv ℝ (h j) x₀ = 0 ∧
        κ₀ • (fderiv ℝ f (x₀, y₀)).comp (inr ℝ E F) +
            μ₀ • (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
            ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 := by
  have hy₀ : y₀ ∈ lowerSolution φ g x₀ := by rw [← solutionMap_lowerFeasible]; exact hp₀.2
  obtain ⟨U, hU, L, μ, hμ, hL⟩ :=
    exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt hgc hφc hb ⟨y₀, hy₀.1⟩ hφ hg hreg
  have hμ₀ := lowerValue_eq_coe hy₀ hU hμ
  have hUp : Prod.fst ⁻¹' U ∈ 𝓝 (x₀, y₀) := continuous_fst.continuousAt.preimage_mem_nhds hU
  -- local minimality for the constraints `valueConstraints φ g h μ`
  have hmin' : IsLocalMinOn f {p | (∀ k, valueConstraints φ g h μ k p ≤ 0) ∧
      ∀ e : Empty, (Empty.elim e : E × F → ℝ) p = 0} (x₀, y₀) := by
    have h1 := eventually_nhdsWithin_iff.1 hmin
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [h1, hUp] with p hp hpU hpS
    have h0 : φ p - μ p.1 ≤ 0 := hpS.1 none
    have hpG : p.2 ∈ lowerFeasible g p.1 := fun i ↦ hpS.1 (some (Sum.inl i))
    refine hp ⟨fun j ↦ hpS.1 (some (Sum.inr j)), ?_⟩
    rw [solutionMap_lowerFeasible]
    refine (VariationalAnalysis.mem_valueFeasible_iff (Ω := univ)).1 ⟨mem_univ _, hpG, ?_⟩ |>.2
    rw [hμ p.1 hpU, EReal.coe_le_coe_iff]
    linarith
  -- Lipschitz data
  have hGL : ∀ k, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (x₀, y₀), LipschitzOnWith K (valueConstraints φ g h μ k) V := by
    rintro (_ | i | j)
    · obtain ⟨K, V, hV, hK⟩ := (hφ y₀ hy₀).exists_lipschitzOnWith
      exact ⟨_, V ∩ Prod.fst ⁻¹' U, inter_mem hV hUp,
        (hK.mono inter_subset_left).sub ((lipschitzOnWith_comp_fst hL).mono inter_subset_right)⟩
    · obtain ⟨K, V, hV, hK⟩ := (hg y₀ hy₀ i).exists_lipschitzOnWith
      exact ⟨K, V, hV, hK⟩
    · obtain ⟨K, V, hV, hK⟩ := (hh j).exists_lipschitzOnWith
      exact ⟨_, _, continuous_fst.continuousAt.preimage_mem_nhds hV, lipschitzOnWith_comp_fst hK⟩
  have hfL : ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (x₀, y₀), LipschitzOnWith K f V :=
    let ⟨K, V, hV, hK⟩ := hf.exists_lipschitzOnWith; ⟨K, V, hV, hK⟩
  have hz₀ : (∀ k, valueConstraints φ g h μ k (x₀, y₀) ≤ 0) ∧
      ∀ e : Empty, (Empty.elim e : E × F → ℝ) (x₀, y₀) = 0 := by
    refine ⟨?_, fun e ↦ e.elim⟩
    rintro (_ | i | j)
    · show φ (x₀, y₀) - μ x₀ ≤ 0
      rw [hμ₀, sub_self]
    · exact hy₀.1 i
    · exact hp₀.1 j
  -- the multiplier rule for Lipschitz programs
  obtain ⟨κ₀, lam, ν, hκ₀, hl0, hcs, hne, ζ, hζ, η, hη, ξ, -, hsum⟩ :=
    exists_fritzJohn_clarke hz₀ hmin' hfL hGL (fun e ↦ e.elim)
  rw [eq_of_mem_clarkeSubdiff_of_contDiffAt hf hζ] at hsum
  have hη0 : η none ∈ clarkeSubdiff (fun q ↦ φ q - μ q.1) (x₀, y₀) := hη none
  rw [clarkeSubdiff_sub_comp_fst ((hφ y₀ hy₀).hasStrictFDerivAt one_ne_zero) hU hL] at hη0
  obtain ⟨_, rfl, _, ⟨u, hu, rfl⟩, hηu⟩ := hη0
  have hηi : ∀ i, η (some (Sum.inl i)) = fderiv ℝ (g i) (x₀, y₀) := fun i ↦
    eq_of_mem_clarkeSubdiff_of_contDiffAt (hg y₀ hy₀ i) (hη (some (Sum.inl i)))
  have hηj : ∀ j, η (some (Sum.inr j)) = (fderiv ℝ (h j) x₀).comp (fst ℝ E F) := fun j ↦
    eq_of_mem_clarkeSubdiff_comp_fst (hh j) (hη (some (Sum.inr j)))
  have hw := clarkeSubdiff_lowerValue_subset hgc hφc hb ⟨y₀, hy₀.1⟩ hφ hg hreg hU hμ hL hu
  simp only [Fintype.sum_option, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, hηi, hηj, ← hηu] at hsum
  refine ⟨κ₀, lam none, fun i ↦ lam (some (Sum.inl i)), fun j ↦ lam (some (Sum.inr j)), hκ₀,
    hl0 none, ?_, fun i ↦ ⟨hl0 _, hcs (some (Sum.inl i))⟩,
    fun j ↦ ⟨hl0 _, hcs (some (Sum.inr j))⟩, u, hw, ?_, ?_⟩
  · intro h0
    simp only [Prod.mk_eq_zero] at h0
    obtain ⟨h1, h2, h3, h4⟩ := h0
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨h1, funext ?_, Subsingleton.elim _ _⟩
    rintro (_ | i | j)
    exacts [h2, congrFun h3 i, congrFun h4 j]
  · refine ContinuousLinearMap.ext fun a ↦ ?_
    have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (a, 0)) hsum
    simp only [add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
      sum_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.inl_apply, zero_apply] at e ⊢
    linear_combination e
  · refine ContinuousLinearMap.ext fun b ↦ ?_
    have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, b)) hsum
    simp only [add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
      sum_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.inr_apply, zero_apply, map_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, add_zero] at e ⊢
    linear_combination e

/-- Thm. 5.21 of [Dempe 2002] (KKT conditions): under the assumptions of
`exists_fritzJohn_valueFunction`, if (5.36) is partially calm at `(x̄, ȳ)` (Def. 5.9,
`VariationalAnalysis.PartiallyCalm`) and (ULR) holds at `x̄`, then the conditions of Thm. 5.20 hold
with `κ₀ = 1` and `μ₀ > 0`. -/
theorem exists_kkt_valueFunction (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y)
    (hy₀ : y₀ ∈ lowerSolution φ g x₀) (hh₀ : ∀ j, h j x₀ ≤ 0)
    (hcalm : PartiallyCalm f φ g {x | ∀ j, h j x ≤ 0} x₀ y₀)
    (hf : ContDiffAt ℝ 1 f (x₀, y₀)) (hh : ∀ j, ContDiffAt ℝ 1 (h j) x₀)
    (hul : UpperLevelRegular h x₀) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∃ β : ι → ℝ, ∃ α : J → ℝ,
      (∀ i, 0 ≤ β i ∧ β i * g i (x₀, y₀) = 0) ∧ (∀ j, 0 ≤ α j ∧ α j * h j x₀ = 0) ∧
      ∃ w ∈ convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y),
        (fderiv ℝ f (x₀, y₀)).comp (inl ℝ E F) +
            μ₀ • ((fderiv ℝ φ (x₀, y₀)).comp (inl ℝ E F) - w) +
            ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F) +
            ∑ j, α j • fderiv ℝ (h j) x₀ = 0 ∧
        (fderiv ℝ f (x₀, y₀)).comp (inr ℝ E F) + μ₀ • (fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F) +
            ∑ i, β i • (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) = 0 := by
  have hp₀F : (x₀, y₀) ∈ VariationalAnalysis.valueFeasible φ g {x | ∀ j, h j x ≤ 0} :=
    VariationalAnalysis.mem_valueFeasible_iff.2 ⟨hh₀, hy₀⟩
  obtain ⟨κ, hκ, hcalmκ⟩ := hcalm
  have hpen := VariationalAnalysis.isLocalMinOn_penalizedObjective hκ hcalmκ hf.continuousAt hp₀F
  obtain ⟨U, hU, L, μ, hμ, hL⟩ :=
    exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt hgc hφc hb ⟨y₀, hy₀.1⟩ hφ hg hreg
  have hμ₀ := lowerValue_eq_coe hy₀ hU hμ
  have hUp : Prod.fst ⁻¹' U ∈ 𝓝 (x₀, y₀) := continuous_fst.continuousAt.preimage_mem_nhds hU
  -- the penalized problem as a Lipschitz program
  let G : ι ⊕ J → E × F → ℝ := Sum.elim g fun j p ↦ h j p.1
  have hmin : IsLocalMinOn (fun p ↦ f p + κ * φ p - κ * μ p.1)
      {p | (∀ k, G k p ≤ 0) ∧ ∀ e : Empty, (Empty.elim e : E × F → ℝ) p = 0} (x₀, y₀) := by
    have h1 := eventually_nhdsWithin_iff.1 hpen
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [h1, hUp] with p hp hpU hpS
    have := hp ⟨fun j ↦ hpS.1 (Sum.inr j), fun i ↦ hpS.1 (Sum.inl i)⟩
    rw [VariationalAnalysis.penalizedObjective_of_mem_valueFeasible hp₀F,
      VariationalAnalysis.penalizedObjective_of_eq (hμ p.1 hpU), EReal.coe_le_coe_iff] at this
    show f (x₀, y₀) + κ * φ (x₀, y₀) - κ * μ x₀ ≤ f p + κ * φ p - κ * μ p.1
    rw [hμ₀]
    linarith
  have hφ₀ := hφ y₀ hy₀
  have hfL : ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (x₀, y₀),
      LipschitzOnWith K (fun p ↦ f p + κ * φ p - κ * μ p.1) V := by
    obtain ⟨K₁, V₁, hV₁, hL₁⟩ := hf.exists_lipschitzOnWith
    obtain ⟨K₂, V₂, hV₂, hL₂⟩ := hφ₀.exists_lipschitzOnWith
    exact ⟨_, V₁ ∩ V₂ ∩ Prod.fst ⁻¹' U, inter_mem (inter_mem hV₁ hV₂) hUp,
      ((hL₁.mono fun _ hp ↦ hp.1.1).add
        (VariationalAnalysis.lipschitzOnWith_const_mul (hL₂.mono fun _ hp ↦ hp.1.2) κ)).sub
        (VariationalAnalysis.lipschitzOnWith_const_mul
          ((lipschitzOnWith_comp_fst hL).mono fun _ hp ↦ hp.2) κ)⟩
  have hGL : ∀ k, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (x₀, y₀), LipschitzOnWith K (G k) V := by
    rintro (i | j)
    · obtain ⟨K, V, hV, hK⟩ := (hg y₀ hy₀ i).exists_lipschitzOnWith
      exact ⟨K, V, hV, hK⟩
    · obtain ⟨K, V, hV, hK⟩ := (hh j).exists_lipschitzOnWith
      exact ⟨_, _, continuous_fst.continuousAt.preimage_mem_nhds hV, lipschitzOnWith_comp_fst hK⟩
  have hz₀ : (∀ k, G k (x₀, y₀) ≤ 0) ∧ ∀ e : Empty, (Empty.elim e : E × F → ℝ) (x₀, y₀) = 0 :=
    ⟨by rintro (i | j); exacts [hy₀.1 i, hh₀ j], fun e ↦ e.elim⟩
  obtain ⟨κ₀, lam, ν, hκ₀, hl0, hcs, hne, ζ, hζ, η, hη, ξ, -, hsum⟩ :=
    exists_fritzJohn_clarke hz₀ hmin hfL hGL (fun e ↦ e.elim)
  -- the generalized gradient of the penalized objective
  have hΦs : HasStrictFDerivAt (fun p ↦ f p + κ * φ p)
      (fderiv ℝ f (x₀, y₀) + κ • fderiv ℝ φ (x₀, y₀)) (x₀, y₀) :=
    (hf.hasStrictFDerivAt one_ne_zero).add ((hφ₀.hasStrictFDerivAt one_ne_zero).const_mul κ)
  have hζ' : ζ ∈ {fderiv ℝ f (x₀, y₀) + κ • fderiv ℝ φ (x₀, y₀)} -
      (fun v : StrongDual ℝ E ↦ v.comp (fst ℝ E F)) '' clarkeSubdiff (fun x ↦ κ * μ x) x₀ := by
    rw [← clarkeSubdiff_sub_comp_fst (φ := fun p ↦ f p + κ * φ p) (μ := fun x ↦ κ * μ x)
      (p := (x₀, y₀)) hΦs hU (VariationalAnalysis.lipschitzOnWith_const_mul hL κ)]
    exact hζ
  rw [VariationalAnalysis.clarkeSubdiff_const_mul hU hL] at hζ'
  obtain ⟨_, rfl, _, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hζu⟩ := hζ'
  have hηi : ∀ i, η (Sum.inl i) = fderiv ℝ (g i) (x₀, y₀) := fun i ↦
    eq_of_mem_clarkeSubdiff_of_contDiffAt (hg y₀ hy₀ i) (hη (Sum.inl i))
  have hηj : ∀ j, η (Sum.inr j) = (fderiv ℝ (h j) x₀).comp (fst ℝ E F) := fun j ↦
    eq_of_mem_clarkeSubdiff_comp_fst (hh j) (hη (Sum.inr j))
  have hw := clarkeSubdiff_lowerValue_subset hgc hφc hb ⟨y₀, hy₀.1⟩ hφ hg hreg hU hμ hL hu
  simp only [Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, hηi, hηj,
    ← hζu] at hsum
  set β : ι → ℝ := fun i ↦ lam (Sum.inl i)
  set α : J → ℝ := fun j ↦ lam (Sum.inr j)
  have hβcs : ∀ i, β i * g i (x₀, y₀) = 0 := fun i ↦ hcs (Sum.inl i)
  have hαcs : ∀ j, α j * h j x₀ = 0 := fun j ↦ hcs (Sum.inr j)
  rcases hκ₀ with hκ₀ | hκ₀
  · -- a vanishing leading multiplier contradicts the regularity conditions
    exfalso
    subst hκ₀
    simp only [zero_smul, zero_add] at hsum
    have hβ : β = 0 := hreg y₀ hy₀ β (fun i ↦ hl0 _)
      (fun i hi ↦ (mul_eq_zero.1 (hβcs i)).resolve_right hi.ne) (by
        refine ContinuousLinearMap.ext fun b ↦ ?_
        have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, b)) hsum
        simpa using e)
    have hα : α = 0 := hul α (fun j ↦ hl0 _)
      (fun j hj ↦ (mul_eq_zero.1 (hαcs j)).resolve_right hj.ne) (by
        refine ContinuousLinearMap.ext fun a ↦ ?_
        have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (a, 0)) hsum
        simpa [β, show ∀ i, lam (Sum.inl i) = 0 from congrFun hβ] using e)
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨trivial, funext ?_, Subsingleton.elim _ _⟩
    rintro (i | j)
    exacts [congrFun hβ i, congrFun hα j]
  · subst hκ₀
    simp only [one_smul] at hsum
    refine ⟨κ, hκ, β, α, fun i ↦ ⟨hl0 _, hβcs i⟩, fun j ↦ ⟨hl0 _, hαcs j⟩, u, hw, ?_, ?_⟩
    · refine ContinuousLinearMap.ext fun a ↦ ?_
      have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (a, 0)) hsum
      simp only [add_apply, sub_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
        sum_apply, smul_apply, smul_eq_mul,
        ContinuousLinearMap.inl_apply, zero_apply] at e ⊢
      linear_combination e
    · refine ContinuousLinearMap.ext fun b ↦ ?_
      have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, b)) hsum
      simp only [add_apply, sub_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
        sum_apply, smul_apply, smul_eq_mul,
        ContinuousLinearMap.inr_apply, zero_apply, map_zero, mul_zero,
        Finset.sum_const_zero, sub_zero, add_zero] at e ⊢
      linear_combination e

end Bilevel
