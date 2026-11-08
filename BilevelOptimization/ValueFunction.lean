/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Parametric
import VariationalAnalysis.Subdifferential.Clarke
import VariationalAnalysis.Subdifferential.MarginalLipschitz

/-!
# The optimal value function of the follower's problem

Sect. 4.5 of [Dempe 2002]: local Lipschitz continuity of the follower's optimal value function
`μ(x) = inf {φ(x, y) | gᵢ(x, y) ≤ 0}` and an upper estimate of its Clarke generalized gradient.

## Main results

* `exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt`: Thm. 4.14 of [Dempe 2002]: if the
  feasible-set map is locally bounded at `x̄` and (MFCQ) holds at all `(x̄, y)`, `y ∈ Ψ(x̄)`, then
  `μ` is locally Lipschitz around `x̄`.
* `subdiff_lowerValue_subset_iUnion`: the limiting subgradients of `μ` at `x̄` are partial
  gradients `∇ₓL(x̄, y, λ)` of the Lagrangian with `y ∈ Ψ(x̄)` and `λ ∈ Λ(x̄, y)`
  ([Mordukhovich 2018, Thm. 4.1(ii)] for the marginal function `μ`).
* `clarkeSubdiff_lowerValue_subset`, `exists_clarkeSubdiff_lowerValue_subset`: Thm. 4.17 of
  [Dempe 2002], (4.27):
  `∂̄μ(x̄) ⊆ co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`, via `∂̄μ(x̄) = co ∂μ(x̄)`
  (`VariationalAnalysis.clarkeSubdiff_eq_convexHull`).

## Remarks on the book

* Assumption (C) of [Dempe 2002] is replaced by what the proofs use: continuity of the `gᵢ` and
  local boundedness of the feasible-set map `G` at `x̄` (implied by (C)).
* (MFCQ) is used in the dual form of lower-level regularity
  (`VariationalAnalysis.LowerLevelRegular`, see `lowerPLI_iff_lowerLevelRegular`), only at the
  points `(x̄, y)` with `y ∈ Ψ(x̄)`, as in the book.
* `μ` takes values in `EReal`; the Lipschitz statements are about a real function `μ'` that
  agrees with `μ` near `x̄`. The generalized gradient only depends on `μ'` near `x̄`.
-/

open Filter Topology Set
open scoped NNReal
open VariationalAnalysis (graph lowerFeasible lowerSolution lowerValue marginal argminMap subdiff
  singularSubdiff clarkeSubdiff LowerLevelRegular LocallyBoundedAt)
open ContinuousLinearMap (inl inr)

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ} {x₀ : E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Near a point where `G` is locally bounded, the values of `G` are compact. -/
theorem eventually_isCompact_lowerFeasible (hgc : ∀ i, Continuous (g i))
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) :
    ∀ᶠ x in 𝓝 x₀, IsCompact (lowerFeasible g x) := by
  obtain ⟨U, hU, hB⟩ := hb
  filter_upwards [hU] with x hx
  refine Metric.isCompact_of_isClosed_isBounded ?_ (hB.subset (subset_biUnion_of_mem hx))
  exact (show IsClosed ((fun y : F ↦ (x, y)) ⁻¹' graph (lowerFeasible g)) from
    (isClosed_graph_lowerFeasible hgc).preimage (by fun_prop))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Local boundedness of `G` at `x₀` gives uniform compact bounds near every point close to
`x₀`. -/
theorem eventually_exists_isCompact_lowerFeasible (hb : LocallyBoundedAt (lowerFeasible g) x₀) :
    ∀ᶠ x in 𝓝 x₀, ∃ U ∈ 𝓝 x, ∃ C, IsCompact C ∧ ∀ x' ∈ U, lowerFeasible g x' ⊆ C := by
  obtain ⟨U, hU, hB⟩ := hb
  filter_upwards [eventually_mem_nhds_iff.2 hU] with x hx
  exact ⟨U, hx, _, Metric.isCompact_of_isClosed_isBounded isClosed_closure hB.closure,
    fun x' hx' ↦ (subset_biUnion_of_mem hx').trans subset_closure⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- The value function is lower semicontinuous near a point where `G` is locally bounded. -/
theorem eventually_lowerSemicontinuousAt_lowerValue (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀) :
    ∀ᶠ x in 𝓝 x₀, LowerSemicontinuousAt (lowerValue φ g) x := by
  filter_upwards [eventually_exists_isCompact_lowerFeasible hb] with x hx
  exact lowerSemicontinuousAt_marginal (isClosed_graph_lowerFeasible hgc) hx hφc

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Near a point where `G` is locally bounded, the infimum defining `μ` is attained whenever the
follower's problem is feasible. -/
theorem eventually_lowerSolution_nonempty (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) :
    ∀ᶠ x in 𝓝 x₀, (lowerFeasible g x).Nonempty → (lowerSolution φ g x).Nonempty := by
  filter_upwards [eventually_isCompact_lowerFeasible hgc hb] with x hx hne
  have h := solutionMap_nonempty_of_isCompact hx hne hφc
  rwa [solutionMap_lowerFeasible] at h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι] in
theorem lowerFeasible_nonempty_of_marginal_ne_top {x : E}
    (h : marginal (fun p ↦ (φ p : EReal)) (lowerFeasible g) x ≠ ⊤) :
    (lowerFeasible g x).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  exact h (by simp [VariationalAnalysis.marginal, hne])

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι] in
theorem locallyBoundedAt_lowerSolution (hb : LocallyBoundedAt (lowerFeasible g) x₀) :
    LocallyBoundedAt (lowerSolution φ g) x₀ :=
  let ⟨U, hU, hB⟩ := hb
  ⟨U, hU, hB.subset (biUnion_mono subset_rfl fun _ _ _ hy ↦ hy.1)⟩

/-- Thm. 4.14 of [Dempe 2002]: if the `gᵢ` are continuous, `G` is locally bounded at `x̄` and
feasible there, and at every `y ∈ Ψ(x̄)` the data are `C¹` and (MFCQ) holds, then the value
function `μ` agrees near `x̄` with a real function that is Lipschitz around `x̄`. -/
theorem exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) :
    ∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ μ : E → ℝ, (∀ x ∈ U, lowerValue φ g x = μ x) ∧
      LipschitzOnWith L μ U := by
  obtain ⟨y₀, hy₀⟩ := (eventually_lowerSolution_nonempty hgc hφc hb).self_of_nhds hne
  exact VariationalAnalysis.exists_lipschitzOnWith_marginal_of_locallyBoundedAt (f := φ)
    (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀) (locallyBoundedAt_lowerSolution hb)
    ((eventually_lowerSolution_nonempty hgc hφc hb).mono fun x hx hx' ↦
      hx (lowerFeasible_nonempty_of_marginal_ne_top hx'))
    (isClosed_graph_lowerFeasible hgc)
    (fun _ _ ↦ ⟨univ, univ_mem,
      (continuous_coe_real_ereal.comp hφc).lowerSemicontinuous.lowerSemicontinuousOn _⟩)
    (fun y hy ↦ let ⟨K, s, hs, h⟩ := (hφ y hy).exists_lipschitzOnWith; ⟨s, hs, K, h⟩)
    (fun y hy ↦ lipschitzLikeAt_lowerFeasible (hg y hy) hy.1 (hreg y hy))
    (eventually_lowerSemicontinuousAt_lowerValue hgc hφc hb)

/-- The set `{∇ₓL(x̄, y, λ) | λ ∈ Λ(x̄, y)}` of partial gradients of the Lagrangian
`L = φ + ∑ λᵢ gᵢ` over the multipliers at `(x̄, y)`. -/
def lagrangianGradients (φ : E × F → ℝ) (g : ι → E × F → ℝ) (x : E) (y : F) :
    Set (StrongDual ℝ E) :=
  {u | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i (x, y) = 0) ∧
    (fderiv ℝ φ (x, y)).comp (inr ℝ E F) + ∑ i, lam i • (fderiv ℝ (g i) (x, y)).comp (inr ℝ E F) = 0 ∧
    u = (fderiv ℝ φ (x, y)).comp (inl ℝ E F) + ∑ i, lam i • (fderiv ℝ (g i) (x, y)).comp (inl ℝ E F)}

/-- Limiting subgradients of the value function under the assumptions of
`exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt`: every `u ∈ ∂μ(x̄)` is `∇ₓL(x̄, y, λ)`
for some `y ∈ Ψ(x̄)` and `λ ∈ Λ(x̄, y)` ([Mordukhovich 2018, Thm. 4.1(ii)] with the normals to
`gph G` of [Exercise 2.51(ii)]). -/
theorem subdiff_lowerValue_subset_iUnion (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) :
    subdiff (lowerValue φ g) x₀ ⊆ ⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y := by
  obtain ⟨y₀, hy₀⟩ := (eventually_lowerSolution_nonempty hgc hφc hb).self_of_nhds hne
  intro u hu
  have h := VariationalAnalysis.subdiff_marginal_subset_of_locallyBoundedAt
    (φ := fun p ↦ (φ p : EReal))
    (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀) (locallyBoundedAt_lowerSolution hb)
    ((eventually_lowerSolution_nonempty hgc hφc hb).mono fun x hx hx' ↦
      hx (lowerFeasible_nonempty_of_marginal_ne_top hx'))
    (isClosed_graph_lowerFeasible hgc)
    (fun _ _ ↦ ⟨univ, univ_mem,
      (continuous_coe_real_ereal.comp hφc).lowerSemicontinuous.lowerSemicontinuousOn _⟩)
    (fun y hy w hw _ ↦ by
      obtain ⟨K, V, hV, hK⟩ := (hφ y hy).exists_lipschitzOnWith
      rwa [VariationalAnalysis.singularSubdiff_eq_zero_of_lipschitz hV hK] at hw) hu
  obtain ⟨y, hy, a, b, hab, hcod⟩ := mem_iUnion₂.1 h
  rw [VariationalAnalysis.subdiff_of_contDiffAt (hφ y hy), mem_singleton_iff] at hab
  obtain ⟨lam, hlam, hcs, heq⟩ :=
    VariationalAnalysis.normalCone_graph_lowerFeasible_subset (hg y hy) hy.1 (hreg y hy) hcod
  refine mem_iUnion₂.2 ⟨y, hy, lam, hlam, hcs, ?_, ?_⟩
  · ext z
    have h1 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, z)) heq
    have h2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, z)) hab
    simp at h1 h2 ⊢
    linarith
  · ext z
    have h1 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (z, 0)) heq
    have h2 := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (z, 0)) hab
    simp at h1 h2 ⊢
    linarith

/-- Thm. 4.17 of [Dempe 2002], (4.27): under the assumptions of
`exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt`, for every real `μ'` Lipschitz around `x̄`
that agrees with `μ` near `x̄`,
`∂̄μ'(x̄) ⊆ co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`. -/
theorem clarkeSubdiff_lowerValue_subset (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) {U : Set E} {L : ℝ≥0}
    {μ : E → ℝ} (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x)
    (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff μ x₀ ⊆
      convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y) := by
  rw [VariationalAnalysis.clarkeSubdiff_eq_convexHull hU hL]
  refine convexHull_mono ?_
  rw [← VariationalAnalysis.subdiff_congr
    (show lowerValue φ g =ᶠ[𝓝 x₀] fun x ↦ (μ x : EReal) from eventually_of_mem hU hμ)]
  exact subdiff_lowerValue_subset_iUnion hgc hφc hb hne hφ hg hreg

/-- Thm. 4.17 of [Dempe 2002] with Thm. 4.14: under (C) (local boundedness of `G`) and (MFCQ) at
all `(x̄, y)`, `y ∈ Ψ(x̄)`, the value function is locally Lipschitz and its generalized gradient
satisfies (4.27). -/
theorem exists_clarkeSubdiff_lowerValue_subset (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) :
    ∃ U ∈ 𝓝 x₀, ∃ L : ℝ≥0, ∃ μ : E → ℝ, (∀ x ∈ U, lowerValue φ g x = μ x) ∧
      LipschitzOnWith L μ U ∧
      clarkeSubdiff μ x₀ ⊆
        convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y) := by
  obtain ⟨U, hU, L, μ, hμ, hL⟩ :=
    exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt hgc hφc hb hne hφ hg hreg
  exact ⟨U, hU, L, μ, hμ, hL,
    clarkeSubdiff_lowerValue_subset hgc hφc hb hne hφ hg hreg hU hμ hL⟩

end Bilevel
