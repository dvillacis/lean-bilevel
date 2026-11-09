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
`μ(x) = inf {φ(x, y) | gᵢ(x, y) ≤ 0}` and an estimate of its Clarke generalized gradient, with
equality under (LICQ) or convexity.

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
* `clarkeSubdiff_lowerValue_eq_of_lowerLICQ`: Cor. 4.5 of [Dempe 2002]: equality in (4.27) under
  (LICQ) at all `(x̄, y)`, `y ∈ Ψ(x̄)`.
* `clarkeSubdiff_lowerValue_eq_of_isConvexLower`: Cor. 4.6 of [Dempe 2002]: for a follower's
  problem convex at `x̄` with `Ψ(x̄) = {ȳ}`, `∂̄μ'(x̄) = {∇ₓL(x̄, ȳ, λ) | λ ∈ Λ(x̄, ȳ)}`.
* `clarkeSubdiff_lowerValue_eq_of_convexOn`: Cor. 4.7 of [Dempe 2002]: the same for jointly convex
  problems, at any `ȳ ∈ Ψ(x̄)`.

## Remarks on the book

* Assumption (C) of [Dempe 2002] is replaced by what the proofs use: continuity of the `gᵢ` and
  local boundedness of the feasible-set map `G` at `x̄` (implied by (C)).
* (MFCQ) is used in the dual form of lower-level regularity
  (`VariationalAnalysis.LowerLevelRegular`, see `lowerPLI_iff_lowerLevelRegular`), only at the
  points `(x̄, y)` with `y ∈ Ψ(x̄)`, as in the book.
* `μ` takes values in `EReal`; the Lipschitz statements are about a real function `μ'` that
  agrees with `μ` near `x̄`. The generalized gradient only depends on `μ'` near `x̄`.
* The book derives Cor. 4.5–4.7 from directional derivatives of `μ` (Cor. 4.4, Thm. 4.16). The
  proofs here are direct and show more: in each case the gradients `u = ∇ₓL(x̄, y, λ)` are regular
  subgradients, of `-μ` at `x̄` (with `-u`) under (LICQ) (`eventually_lowerValue_le_of_lowerLICQ`,
  along feasible curves that keep the active constraints strictly negative), and of `μ` in the
  convex cases (`eventually_le_lowerValue_of_isConvexLower`, `le_lowerValue_of_convexOn`).
  Clarke regularity of `μ` in Cor. 4.5 is not formalized.
* In Cor. 4.6 the convexity is only needed at `x̄`, and the upper semicontinuity of `Ψ` at `x̄`
  comes from the continuity of `μ` (`upperHemicontinuousAt_lowerSolution`), so (MFCQ) is only
  used at `(x̄, ȳ)`.
* In Cor. 4.7 (MFCQ) is assumed at all `(x̄, y)`, `y ∈ Ψ(x̄)`, as in Thm. 4.17; for convex problems
  it is equivalent to Slater's condition (`lowerPLI_of_slaterAt`). The inclusion
  `∇ₓL(x̄, y, Λ(x̄, y)) ⊆ ∇ₓL(x̄, ȳ, Λ(x̄, ȳ))` for `y, ȳ ∈ Ψ(x̄)` comes from the KKT conditions of
  the joint problem `min {φ(x, z) - u x | g(x, z) ≤ 0}` instead of Lemma 4.4
  (`lagrangianGradients_subset_of_convexOn`).
-/

open Filter Topology Set Asymptotics
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


/-! ### Equality in (4.27): Cor. 4.5–4.7 -/

section Equality

variable {x₀ : E} {y₀ : F} {u : StrongDual ℝ E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- If `λ` makes `∇_y L(x̄, ȳ, λ)` vanish and `u = ∇ₓL(x̄, ȳ, λ)`, then
`∇L(x̄, ȳ, λ)(h, k) = u h`. -/
theorem lagrangian_apply_eq {T : StrongDual ℝ (E × F)} {S : ι → StrongDual ℝ (E × F)}
    {lam : ι → ℝ} (hstat : T.comp (inr ℝ E F) + ∑ i, lam i • (S i).comp (inr ℝ E F) = 0)
    (hu : u = T.comp (inl ℝ E F) + ∑ i, lam i • (S i).comp (inl ℝ E F)) (h : E) (k : F) :
    T (h, k) + ∑ i, lam i * S i (h, k) = u h := by
  have h1 := congrArg (fun A : StrongDual ℝ F ↦ A k) hstat
  have e : ∀ A : StrongDual ℝ (E × F), A (h, k) = A (h, 0) + A (0, k) := fun A ↦ by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  simp at h1
  rw [hu, e T]
  simp only [e (S _), mul_add, Finset.sum_add_distrib]
  simp
  linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem add_sum_smul_combo {M : Type*} [AddCommGroup M] [Module ℝ M] {a b : ℝ}
    (hab : a + b = 1) (T : M) (S : ι → M) (l₁ l₂ : ι → ℝ) :
    T + ∑ i, (a • l₁ + b • l₂) i • S i =
      a • (T + ∑ i, l₁ i • S i) + b • (T + ∑ i, l₂ i • S i) := by
  have e : ∑ i, (a • l₁ + b • l₂) i • S i = a • ∑ i, l₁ i • S i + b • ∑ i, l₂ i • S i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  rw [e]
  calc T + (a • ∑ i, l₁ i • S i + b • ∑ i, l₂ i • S i)
      = (a + b) • T + (a • ∑ i, l₁ i • S i + b • ∑ i, l₂ i • S i) := by rw [hab, one_smul]
    _ = _ := by module

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `{∇ₓL(x̄, ȳ, λ) | λ ∈ Λ(x̄, ȳ)}` is convex (a linear image of the convex set `Λ(x̄, ȳ)`). -/
theorem convex_lagrangianGradients : Convex ℝ (lagrangianGradients φ g x₀ y₀) := by
  rintro u₁ ⟨l₁, h1, c1, s1, rfl⟩ u₂ ⟨l₂, h2, c2, s2, rfl⟩ a b ha hb hab
  refine ⟨a • l₁ + b • l₂, fun i ↦ ?_, fun i ↦ ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (h1 i)) (mul_nonneg hb (h2 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, mul_assoc, mul_assoc, c1 i, c2 i, mul_zero, mul_zero, add_zero]
  · have := add_sum_smul_combo hab ((fderiv ℝ φ (x₀, y₀)).comp (inr ℝ E F))
      (fun i ↦ (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F)) l₁ l₂
    rw [this, s1, s2, smul_zero, smul_zero, add_zero]
  · have := add_sum_smul_combo hab ((fderiv ℝ φ (x₀, y₀)).comp (inl ℝ E F))
      (fun i ↦ (fderiv ℝ (g i) (x₀, y₀)).comp (inl ℝ E F)) l₁ l₂
    rw [this]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι] in
theorem lowerValue_eq_top {x : E} (h : ¬ (lowerFeasible g x).Nonempty) : lowerValue φ g x = ⊤ := by
  simp [VariationalAnalysis.lowerValue, VariationalAnalysis.marginal,
    not_nonempty_iff_eq_empty.1 h]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A first-order lower estimate of `ψ` at `x̄` puts `u` in the generalized gradient of any real
function agreeing with `ψ` near `x̄` (`u` is a regular subgradient). -/
theorem mem_clarkeSubdiff_of_le {ψ : E → EReal} {μ : E → ℝ} {U : Set E} (hU : U ∈ 𝓝 x₀)
    (hμ : ∀ x ∈ U, ψ x = μ x)
    (h : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ((μ x₀ + u (x - x₀) - ε * ‖x - x₀‖ : ℝ) : EReal) ≤ ψ x) :
    u ∈ clarkeSubdiff μ x₀ :=
  VariationalAnalysis.subdiff_subset_clarkeSubdiff (VariationalAnalysis.regularSubdiff_subset_subdiff
    ((VariationalAnalysis.mem_regularSubdiff_iff (φ := fun x ↦ ((μ x : ℝ) : EReal)) (x₀ := x₀)
      (r := μ x₀) rfl).2 fun ε hε ↦ by
      filter_upwards [h ε hε, hU] with x hx hxU
      rwa [hμ x hxU] at hx))

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A first-order upper estimate of `ψ` at `x̄` puts `u` in the generalized gradient of any real
function agreeing with `ψ` near `x̄` (`-u` is a regular subgradient of the negative). -/
theorem mem_clarkeSubdiff_of_ge {ψ : E → EReal} {μ : E → ℝ} {U : Set E} (hU : U ∈ 𝓝 x₀)
    (hμ : ∀ x ∈ U, ψ x = μ x)
    (h : ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ψ x ≤ ((μ x₀ + u (x - x₀) + ε * ‖x - x₀‖ : ℝ) : EReal)) :
    u ∈ clarkeSubdiff μ x₀ := by
  have hneg : -u ∈ VariationalAnalysis.regularSubdiff (fun x ↦ ((-μ x : ℝ) : EReal)) x₀ :=
    (VariationalAnalysis.mem_regularSubdiff_iff (φ := fun x ↦ ((-μ x : ℝ) : EReal)) (x₀ := x₀)
      (r := -μ x₀) rfl).2 fun ε hε ↦ by
      filter_upwards [h ε hε, hU] with x hx hxU
      rw [hμ x hxU, EReal.coe_le_coe_iff] at hx
      rw [EReal.coe_le_coe_iff, neg_apply]
      linarith
  have := VariationalAnalysis.subdiff_neg_subset_neg_clarkeSubdiff
    (VariationalAnalysis.regularSubdiff_subset_subdiff hneg)
  simpa using this

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- If the value function agrees near `x̄` with a function continuous at `x̄` and `G` is locally
bounded at `x̄`, the solution map `Ψ` is upper semicontinuous at `x̄`. -/
theorem upperHemicontinuousAt_lowerSolution (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) {U : Set E} {μ : E → ℝ} (hU : U ∈ 𝓝 x₀)
    (hμ : ∀ x ∈ U, lowerValue φ g x = μ x) (hμc : ContinuousAt μ x₀) :
    UpperHemicontinuousAt (lowerSolution φ g) x₀ := by
  refine upperHemicontinuousAt_of_mem_closure_graph (fun y hy ↦ ?_) ?_
  · obtain ⟨p, hpΨ, hp⟩ := mem_closure_iff_seq_limit.1 hy
    have hyG : y ∈ lowerFeasible g x₀ := (isClosed_graph_lowerFeasible hgc).mem_of_tendsto hp
      (Eventually.of_forall fun n ↦ (hpΨ n).1)
    have hfst : Tendsto (fun n ↦ (p n).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp
    have h1 : Tendsto (fun n ↦ φ (p n)) atTop (𝓝 (φ (x₀, y))) := (hφc.tendsto _).comp hp
    have heq : (fun n ↦ μ (p n).1) =ᶠ[atTop] fun n ↦ φ (p n) := by
      filter_upwards [hfst.eventually hU] with n hn
      have := (hμ _ hn).symm.trans
        (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution (hpΨ n))
      exact_mod_cast this
    have he : φ (x₀, y) = μ x₀ := tendsto_nhds_unique h1 ((hμc.tendsto.comp hfst).congr' heq)
    refine ⟨hyG, ?_⟩
    change ((φ (x₀, y) : ℝ) : EReal) = lowerValue φ g x₀
    rw [hμ x₀ (mem_of_mem_nhds hU), he]
  · obtain ⟨V, hV, hB⟩ := locallyBoundedAt_lowerSolution (φ := φ) hb
    exact ⟨V, hV, _, hB.isCompact_closure, fun x hx y hy ↦ subset_closure (mem_biUnion hx hy)⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For a jointly convex follower's problem, every `∇ₓL(x̄, ȳ, λ)`, `λ ∈ Λ(x̄, ȳ)`, is a global
subgradient of the value function at `x̄`: `μ(x) ≥ φ(x̄, ȳ) + ∇ₓL(x̄, ȳ, λ)(x - x̄)`. -/
theorem le_lowerValue_of_convexOn (hφv : ConvexOn ℝ univ φ) (hgv : ∀ i, ConvexOn ℝ univ (g i))
    (hφ : DifferentiableAt ℝ φ (x₀, y₀)) (hg : ∀ i, DifferentiableAt ℝ (g i) (x₀, y₀))
    (hu : u ∈ lagrangianGradients φ g x₀ y₀) (x : E) :
    ((φ (x₀, y₀) + u (x - x₀) : ℝ) : EReal) ≤ lowerValue φ g x := by
  obtain ⟨lam, hl0, hcs, hstat, hu⟩ := hu
  change _ ≤ ⨅ z ∈ lowerFeasible g x, ((φ (x, z) : ℝ) : EReal)
  refine le_iInf₂ fun z hz ↦ EReal.coe_le_coe_iff.2 ?_
  have hz' : ∀ i, g i (x, z) ≤ 0 := hz
  have h1 := Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ φ (x₀, y₀)) hφ.hasFDerivAt hφv
    (mem_univ _) (x, z) (mem_univ _)
  have h2 : ∀ i, g i (x₀, y₀) + fderiv ℝ (g i) (x₀, y₀) ((x, z) - (x₀, y₀)) ≤ g i (x, z) :=
    fun i ↦ Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (g i) (x₀, y₀))
      (hg i).hasFDerivAt (hgv i) (mem_univ _) (x, z) (mem_univ _)
  have hL := lagrangian_apply_eq hstat hu (x - x₀) (z - y₀)
  simp only [Prod.mk_sub_mk] at h1 h2
  have h3 : ∑ i, lam i * (g i (x₀, y₀) + fderiv ℝ (g i) (x₀, y₀) (x - x₀, z - y₀)) ≤
      ∑ i, lam i * g i (x, z) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h2 i) (hl0 i)
  have h4 : ∑ i, lam i * g i (x, z) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hz' i)
  simp only [mul_add, hcs, zero_add] at h3
  linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For a follower's problem that is convex at `x̄`, with `C¹` data at `(x̄, ȳ)` and `Ψ(x̄) = {ȳ}`,
if `Ψ` is upper semicontinuous at `x̄`, every `∇ₓL(x̄, ȳ, λ)`, `λ ∈ Λ(x̄, ȳ)`, is a regular
subgradient of the value function at `x̄`. -/
theorem eventually_le_lowerValue_of_isConvexLower (hconv : IsConvexLower φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hΨ : lowerSolution φ g x₀ = {y₀}) (husc : UpperHemicontinuousAt (lowerSolution φ g) x₀)
    (hex : ∀ᶠ x in 𝓝 x₀, (lowerFeasible g x).Nonempty → (lowerSolution φ g x).Nonempty)
    (hu : u ∈ lagrangianGradients φ g x₀ y₀) :
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀,
      ((φ (x₀, y₀) + u (x - x₀) - ε * ‖x - x₀‖ : ℝ) : EReal) ≤ lowerValue φ g x := by
  intro ε hε
  obtain ⟨lam, hl0, hcs, hstat, hu⟩ := hu
  set D' := fderiv ℝ φ (x₀, y₀) + ∑ i, lam i • fderiv ℝ (g i) (x₀, y₀) with hD'
  have hℓ : HasStrictFDerivAt (fun p ↦ φ p + ∑ i, lam i * g i p) D' (x₀, y₀) :=
    (hφ.hasStrictFDerivAt one_ne_zero).add (HasStrictFDerivAt.fun_sum fun i _ ↦
      ((hg i).hasStrictFDerivAt one_ne_zero).const_mul (lam i))
  have hm : Tendsto (fun q : E × F ↦ (q, (x₀, q.2))) (𝓝 (x₀, y₀)) (𝓝 ((x₀, y₀), (x₀, y₀))) :=
    (by fun_prop : Continuous fun q : E × F ↦ (q, (x₀, q.2))).tendsto' _ _ rfl
  have hP := hm.eventually ((hasStrictFDerivAt_iff_isLittleO.1 hℓ).def hε)
  obtain ⟨U, hU, W, hWo, hy₀W, hUW⟩ := exists_isOpen_of_eventually_nhds_prod
    (P := fun x y ↦ ‖(φ (x, y) + ∑ i, lam i * g i (x, y)) - (φ (x₀, y) + ∑ i, lam i * g i (x₀, y)) -
      D' ((x, y) - (x₀, y))‖ ≤ ε * ‖(x, y) - (x₀, y)‖) hP
  -- the Lagrangian `L(x̄, ·, λ)` is minimized at `ȳ`
  have hsec : ∀ f : E × F → ℝ, DifferentiableAt ℝ f (x₀, y₀) → ConvexOn ℝ univ (fun z ↦ f (x₀, z)) →
      ∀ y, f (x₀, y₀) + fderiv ℝ f (x₀, y₀) (0, y - y₀) ≤ f (x₀, y) := fun f hf hfc y ↦ by
    have := Convex_first_order_condition (f' := fun _ ↦ (fderiv ℝ f (x₀, y₀)).comp (inr ℝ E F))
      (hf.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)) hfc (mem_univ y₀) y (mem_univ y)
    simpa using this
  have hmin : ∀ y, φ (x₀, y₀) ≤ φ (x₀, y) + ∑ i, lam i * g i (x₀, y) := fun y ↦ by
    have h1 := hsec φ (hφ.differentiableAt one_ne_zero) hconv.1 y
    have h3 : ∑ i, lam i * (g i (x₀, y₀) + fderiv ℝ (g i) (x₀, y₀) (0, y - y₀)) ≤
        ∑ i, lam i * g i (x₀, y) := Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (hsec (g i) ((hg i).differentiableAt one_ne_zero) (hconv.2 i) y) (hl0 i)
    have hL := lagrangian_apply_eq hstat hu 0 (y - y₀)
    simp only [mul_add, hcs, zero_add, map_zero] at h3 hL
    linarith
  have hD'0 : ∀ h : E, D' (h, 0) = u h := fun h ↦ by
    rw [← lagrangian_apply_eq hstat hu h 0, hD']
    simp
  filter_upwards [hU, husc W hWo (by rw [hΨ]; exact singleton_subset_iff.2 hy₀W), hex]
    with x hxU hxW hxex
  by_cases hG : (lowerFeasible g x).Nonempty
  swap
  · rw [lowerValue_eq_top hG]
    exact le_top
  obtain ⟨y, hy⟩ := hxex hG
  rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy, EReal.coe_le_coe_iff]
  have hxy := hUW x hxU y (hxW hy)
  simp only [Prod.mk_sub_mk, sub_self, hD'0] at hxy
  have hn : ‖(x - x₀, (0 : F))‖ = ‖x - x₀‖ := by simp
  rw [hn, Real.norm_eq_abs, abs_le] at hxy
  have hy' : ∀ i, g i (x, y) ≤ 0 := hy.1
  have hneg : ∑ i, lam i * g i (x, y) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hy' i)
  linarith [hmin y, hxy.1]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [Fintype ι] in
/-- Linearly independent functionals admit a biorthogonal family of vectors. -/
theorem exists_biorthogonal {A : Type*} [Finite A] [DecidableEq A] {v : A → StrongDual ℝ F}
    (hv : LinearIndependent ℝ v) : ∃ w : A → F, ∀ i j, v i (w j) = if i = j then 1 else 0 := by
  classical
  cases nonempty_fintype A
  let T : F →ₗ[ℝ] (A → ℝ) := LinearMap.pi fun i ↦ (v i : F →ₗ[ℝ] ℝ)
  have hT : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hzero : ∑ i, f (Pi.single i 1) • v i = 0 := by
      ext w
      have h := hle (LinearMap.mem_range_self T w)
      rw [LinearMap.mem_ker] at h
      have e : T w = ∑ i, v i w • Pi.single i (1 : ℝ) := by
        ext j
        simp [T, Pi.single_apply]
      rw [e, map_sum] at h
      simpa [map_smul, mul_comm] using h
    have hc := Fintype.linearIndependent_iff.1 hv _ hzero
    exact hf ((Pi.basisFun ℝ A).ext fun i ↦ by simpa using hc i)
  choose w hw using fun j ↦ hT (Pi.single j 1)
  refine ⟨w, fun i j ↦ ?_⟩
  have := congrFun (hw j) i
  simpa [T, Pi.single_apply] using this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Under (LICQ) at `(x̄, ȳ)` with `ȳ ∈ Ψ(x̄)`, every `∇ₓL(x̄, ȳ, λ)`, `λ ∈ Λ(x̄, ȳ)`, gives a
first-order upper estimate of the value function at `x̄`, along feasible curves
`x ↦ (x, ȳ + K(x - x̄))` that keep the active constraints strictly negative. -/
theorem eventually_lowerValue_le_of_lowerLICQ (hφ : DifferentiableAt ℝ φ (x₀, y₀))
    (hg : ∀ i, DifferentiableAt ℝ (g i) (x₀, y₀)) (hy₀ : y₀ ∈ lowerFeasible g x₀)
    (hlicq : LowerLICQ g x₀ y₀) (hu : u ∈ lagrangianGradients φ g x₀ y₀) :
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀,
      lowerValue φ g x ≤ ((φ (x₀, y₀) + u (x - x₀) + ε * ‖x - x₀‖ : ℝ) : EReal) := by
  classical
  intro ε hε
  obtain ⟨lam, hl0, hcs, hstat, hu⟩ := hu
  have hli : LinearIndependent ℝ
      (fun i : {i // g i (x₀, y₀) = 0} ↦ (fderiv ℝ (g i.1) (x₀, y₀)).comp (inr ℝ E F)) := by
    have e : (fun i : {i // g i (x₀, y₀) = 0} ↦ (fderiv ℝ (g i.1) (x₀, y₀)).comp (inr ℝ E F)) =
        fun i ↦ fderiv ℝ (fun z ↦ g i.1 (x₀, z)) y₀ :=
      funext fun i ↦ (fderiv_section (hg i.1)).symm
    rw [e]
    exact hlicq
  obtain ⟨w, hw⟩ := exists_biorthogonal hli
  have hΛ : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ ↦ hl0 i
  obtain ⟨s, hs, hsΛ⟩ : ∃ s > 0, s * ∑ i, lam i ≤ ε / 2 :=
    ⟨ε / (2 * (∑ i, lam i + 1)), by positivity, by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith⟩
  -- the correction `K h`: `∇gᵢ(x̄, ȳ)(h, K h) = -s ‖h‖` for the active constraints
  set K : E → F := fun h ↦
    ∑ j : {i // g i (x₀, y₀) = 0}, (-fderiv ℝ (g j.1) (x₀, y₀) (h, 0) - s * ‖h‖) • w j with hK
  have hKact : ∀ (i : {i // g i (x₀, y₀) = 0}) (h : E),
      fderiv ℝ (g i.1) (x₀, y₀) (h, K h) = -(s * ‖h‖) := fun i h ↦ by
    have e1 : fderiv ℝ (g i.1) (x₀, y₀) (h, K h) =
        fderiv ℝ (g i.1) (x₀, y₀) (h, 0) + (fderiv ℝ (g i.1) (x₀, y₀)).comp (inr ℝ E F) (K h) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add,
        Prod.mk_add_mk, add_zero, zero_add]
    have e2 : (fderiv ℝ (g i.1) (x₀, y₀)).comp (inr ℝ E F) (K h) =
        -fderiv ℝ (g i.1) (x₀, y₀) (h, 0) - s * ‖h‖ := by
      simp only [hK, map_sum, map_smul, hw, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e1, e2]
    ring
  have hKlam : ∀ i (h : E), lam i * fderiv ℝ (g i) (x₀, y₀) (h, K h) = lam i * -(s * ‖h‖) :=
    fun i h ↦ by
      by_cases hi : g i (x₀, y₀) = 0
      · rw [hKact ⟨i, hi⟩ h]
      · rw [(mul_eq_zero.1 (hcs i)).resolve_right hi, zero_mul, zero_mul]
  have hKφ : ∀ h : E, fderiv ℝ φ (x₀, y₀) (h, K h) = u h + s * ‖h‖ * ∑ i, lam i := fun h ↦ by
    have := lagrangian_apply_eq hstat hu h (K h)
    simp only [hKlam, mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul] at this
    linarith
  set M : ℝ := ∑ j : {i // g i (x₀, y₀) = 0}, (‖fderiv ℝ (g j.1) (x₀, y₀)‖ + s) * ‖w j‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ ↦ by positivity
  have hKb : ∀ h, ‖K h‖ ≤ M * ‖h‖ := fun h ↦ by
    calc ‖K h‖ ≤ ∑ j : {i // g i (x₀, y₀) = 0},
          ‖(-fderiv ℝ (g j.1) (x₀, y₀) (h, 0) - s * ‖h‖) • w j‖ := norm_sum_le _ _
      _ ≤ ∑ j : {i // g i (x₀, y₀) = 0}, (‖fderiv ℝ (g j.1) (x₀, y₀)‖ + s) * ‖w j‖ * ‖h‖ :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [norm_smul]
            have hop := (fderiv ℝ (g j.1) (x₀, y₀)).le_opNorm (h, 0)
            have hn : ‖(h, (0 : F))‖ = ‖h‖ := by simp
            rw [hn, Real.norm_eq_abs] at hop
            have h1 : ‖-fderiv ℝ (g j.1) (x₀, y₀) (h, 0) - s * ‖h‖‖ ≤
                (‖fderiv ℝ (g j.1) (x₀, y₀)‖ + s) * ‖h‖ := by
              rw [Real.norm_eq_abs, abs_le]
              have := abs_le.1 hop
              constructor <;> nlinarith [norm_nonneg h]
            calc _ ≤ (‖fderiv ℝ (g j.1) (x₀, y₀)‖ + s) * ‖h‖ * ‖w j‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
              _ = _ := by ring
      _ = M * ‖h‖ := by rw [← Finset.sum_mul]
  have hvO : (fun h : E ↦ ((h, K h) : E × F)) =O[𝓝 0] fun h ↦ h :=
    IsBigO.of_bound (1 + M) (Eventually.of_forall fun h ↦ by
      rw [norm_prod_le_iff]
      exact ⟨by nlinarith [norm_nonneg h], (hKb h).trans (by nlinarith [norm_nonneg h])⟩)
  have hvt : Tendsto (fun h : E ↦ ((h, K h) : E × F)) (𝓝 0) (𝓝 0) := hvO.trans_tendsto tendsto_id
  have hlo : ∀ {f : E × F → ℝ}, DifferentiableAt ℝ f (x₀, y₀) → ∀ c > 0, ∀ᶠ h in 𝓝 (0 : E),
      |f ((x₀, y₀) + (h, K h)) - f (x₀, y₀) - fderiv ℝ f (x₀, y₀) (h, K h)| ≤ c * ‖h‖ :=
    fun hf c hc ↦ by
      have := (((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).comp_tendsto hvt).trans_isBigO
        hvO).def hc
      simpa [Real.norm_eq_abs] using this
  have hpt : Tendsto (fun h : E ↦ (x₀, y₀) + ((h, K h) : E × F)) (𝓝 0) (𝓝 (x₀, y₀)) := by
    have := (tendsto_const_nhds (x := (x₀, y₀))).add hvt
    rwa [add_zero] at this
  have hge : ∀ᶠ h in 𝓝 (0 : E), ∀ i, g i ((x₀, y₀) + (h, K h)) ≤ 0 := eventually_all.2 fun i ↦ by
    by_cases hi : g i (x₀, y₀) = 0
    · filter_upwards [hlo (hg i) (s / 2) (half_pos hs)] with h hh
      rw [hKact ⟨i, hi⟩ h, hi] at hh
      have := (abs_le.1 hh).2
      nlinarith [norm_nonneg h]
    · have hneg : g i (x₀, y₀) < 0 := lt_of_le_of_ne (hy₀ i) hi
      exact (hpt.eventually ((hg i).continuousAt.eventually_lt continuousAt_const hneg)).mono
        fun _ hh ↦ hh.le
  have hh : ∀ᶠ h in 𝓝 (0 : E),
      lowerValue φ g (x₀ + h) ≤ ((φ (x₀, y₀) + u h + ε * ‖h‖ : ℝ) : EReal) := by
    filter_upwards [hlo hφ (ε / 2) (half_pos hε), hge] with h h1 h2
    have hfeas : y₀ + K h ∈ lowerFeasible g (x₀ + h) := fun i ↦ h2 i
    refine (VariationalAnalysis.lowerValue_le hfeas).trans (EReal.coe_le_coe_iff.2 ?_)
    rw [hKφ h] at h1
    have h3 : s * ‖h‖ * ∑ i, lam i ≤ ε / 2 * ‖h‖ := by nlinarith [norm_nonneg h]
    have := (abs_le.1 h1).2
    simp only [Prod.mk_add_mk] at this
    linarith
  have ht : Tendsto (fun x ↦ x - x₀) (𝓝 x₀) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 x₀)).sub_const x₀
  filter_upwards [ht.eventually hh] with x hx
  rwa [add_sub_cancel] at hx

/-- For a jointly convex follower's problem with (MFCQ) at `(x̄, ȳ₀)`, `ȳ₀ ∈ Ψ(x̄)`, the partial
gradients of the Lagrangian at any `y ∈ Ψ(x̄)` are partial gradients at `ȳ₀`: a gradient
`u ∈ ∇ₓL(x̄, y, Λ(x̄, y))` is a global subgradient of `μ` (`le_lowerValue_of_convexOn`), so
`(x̄, ȳ₀)` minimizes `φ(x, z) - u x` subject to `g(x, z) ≤ 0`, and its KKT conditions give
`u ∈ ∇ₓL(x̄, ȳ₀, Λ(x̄, ȳ₀))`. -/
theorem lagrangianGradients_subset_of_convexOn (hφv : ConvexOn ℝ univ φ)
    (hgv : ∀ i, ConvexOn ℝ univ (g i)) {y : F} (hy : y ∈ lowerSolution φ g x₀)
    (hy₀ : y₀ ∈ lowerSolution φ g x₀) (hφ : DifferentiableAt ℝ φ (x₀, y))
    (hg : ∀ i, DifferentiableAt ℝ (g i) (x₀, y)) (hφ₀ : DifferentiableAt ℝ φ (x₀, y₀))
    (hg₀ : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀)) (hreg : LowerLevelRegular g x₀ y₀) :
    lagrangianGradients φ g x₀ y ⊆ lagrangianGradients φ g x₀ y₀ := by
  intro u hu
  have heq : φ (x₀, y) = φ (x₀, y₀) := by
    have := (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy).symm.trans
      (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀)
    exact_mod_cast this
  have hmin : ∀ p : E × F, (∀ i, g i p ≤ 0) → φ (x₀, y₀) - u x₀ ≤ φ p - u p.1 := fun p hp ↦ by
    have h1 := (le_lowerValue_of_convexOn hφv hgv hφ hg hu p.1).trans
      (VariationalAnalysis.lowerValue_le (φ := φ) (y := p.2) hp)
    rw [EReal.coe_le_coe_iff, map_sub] at h1
    linarith
  -- the joint problem in the variable `p = (x, z)`, with a dummy leader variable
  have hφ' : HasFDerivAt (fun p : E × F ↦ φ p - u p.1)
      (fderiv ℝ φ (x₀, y₀) - u.comp (ContinuousLinearMap.fst ℝ E F)) (x₀, y₀) :=
    hφ₀.hasFDerivAt.sub (u.hasFDerivAt.comp _ (hasFDerivAt_fst))
  have hreg' : LowerPLI (fun i (q : E × (E × F)) ↦ g i q.2) x₀ (x₀, y₀) := by
    intro lam hl hin hsum
    refine (lowerPLI_iff_lowerLevelRegular fun i ↦ (hg₀ i).differentiableAt one_ne_zero).2 hreg
      lam hl hin ?_
    have hs : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = (fderiv ℝ (g i) (x₀, y₀)).comp (inr ℝ E F) :=
      fun i ↦ fderiv_section ((hg₀ i).differentiableAt one_ne_zero)
    simp only [hs]
    ext k
    have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, k)) hsum
    simpa using this
  obtain ⟨lam, -, hl0, hcs, hstat⟩ := exists_isLowerKKT_of_isLocalMinOn
    (φ := fun q : E × (E × F) ↦ φ q.2 - u q.2.1) (g := fun i q ↦ g i q.2) (x := x₀)
    (y := (x₀, y₀)) hy₀.1 (isMinOn_iff.2 fun p hp ↦ hmin p hp).localize hφ'.differentiableAt
    (fun i ↦ hg₀ i) hreg'
  rw [hφ'.fderiv] at hstat
  refine ⟨lam, hl0, hcs, ?_, ?_⟩
  · ext k
    have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, k)) hstat
    simpa using this
  · ext h
    have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (h, 0)) hstat
    simp at this ⊢
    linarith

/-- Cor. 4.5 of [Dempe 2002]: under the assumptions of Thm. 4.17
(`clarkeSubdiff_lowerValue_subset`) with (LICQ) in place of (MFCQ) at all `(x̄, y)`, `y ∈ Ψ(x̄)`,
equality holds in (4.27): `∂̄μ'(x̄) = co ⋃ {∇ₓL(x̄, y, λ) | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}` (`λ` is
unique for each `y`). -/
theorem clarkeSubdiff_lowerValue_eq_of_lowerLICQ (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hlicq : ∀ y ∈ lowerSolution φ g x₀, LowerLICQ g x₀ y) {U : Set E} {L : ℝ≥0} {μ : E → ℝ}
    (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x) (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff μ x₀ =
      convexHull ℝ (⋃ y ∈ lowerSolution φ g x₀, lagrangianGradients φ g x₀ y) := by
  have hdg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, DifferentiableAt ℝ (g i) (x₀, y) :=
    fun y hy i ↦ (hg y hy i).differentiableAt one_ne_zero
  have hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y := fun y hy ↦
    (lowerPLI_iff_lowerLevelRegular (hdg y hy)).1 (lowerPLI_of_lowerLICQ hy.1 (hlicq y hy))
  refine subset_antisymm (clarkeSubdiff_lowerValue_subset hgc hφc hb hne hφ hg hreg hU hμ hL)
    (convexHull_min (iUnion₂_subset fun y hy u hu ↦ ?_) VariationalAnalysis.convex_clarkeSubdiff)
  have hμ₀ : μ x₀ = φ (x₀, y) := by
    have := (hμ x₀ (mem_of_mem_nhds hU)).symm.trans
      (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy)
    exact_mod_cast this
  refine mem_clarkeSubdiff_of_ge hU hμ fun ε hε ↦ ?_
  rw [hμ₀]
  exact eventually_lowerValue_le_of_lowerLICQ ((hφ y hy).differentiableAt one_ne_zero) (hdg y hy)
    hy.1 (hlicq y hy) hu ε hε

/-- Cor. 4.6 of [Dempe 2002]: for a follower's problem that is convex at `x̄`, under (C) and
(MFCQ) at `(x̄, ȳ)` with `Ψ(x̄) = {ȳ}`, `∂̄μ'(x̄) = {∇ₓL(x̄, ȳ, λ) | λ ∈ Λ(x̄, ȳ)}` for every real
`μ'` Lipschitz around `x̄` that agrees with `μ` near `x̄`. -/
theorem clarkeSubdiff_lowerValue_eq_of_isConvexLower (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hΨ : lowerSolution φ g x₀ = {y₀}) (hconv : IsConvexLower φ g x₀)
    (hφ : ContDiffAt ℝ 1 φ (x₀, y₀)) (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hreg : LowerLevelRegular g x₀ y₀) {U : Set E} {L : ℝ≥0} {μ : E → ℝ} (hU : U ∈ 𝓝 x₀)
    (hμ : ∀ x ∈ U, lowerValue φ g x = μ x) (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff μ x₀ = lagrangianGradients φ g x₀ y₀ := by
  have hy₀ : y₀ ∈ lowerSolution φ g x₀ := hΨ ▸ mem_singleton y₀
  have hsub := clarkeSubdiff_lowerValue_subset hgc hφc hb ⟨y₀, hy₀.1⟩
    (fun y hy ↦ by rw [hΨ, mem_singleton_iff] at hy; exact hy ▸ hφ)
    (fun y hy ↦ by rw [hΨ, mem_singleton_iff] at hy; exact hy ▸ hg)
    (fun y hy ↦ by rw [hΨ, mem_singleton_iff] at hy; exact hy ▸ hreg) hU hμ hL
  rw [hΨ, biUnion_singleton, convex_lagrangianGradients.convexHull_eq] at hsub
  refine subset_antisymm hsub fun u hu ↦ ?_
  have hμ₀ : μ x₀ = φ (x₀, y₀) := by
    have := (hμ x₀ (mem_of_mem_nhds hU)).symm.trans
      (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀)
    exact_mod_cast this
  refine mem_clarkeSubdiff_of_le hU hμ fun ε hε ↦ ?_
  rw [hμ₀]
  exact eventually_le_lowerValue_of_isConvexLower hconv hφ hg hΨ
    (upperHemicontinuousAt_lowerSolution hgc hφc hb hU hμ (hL.continuousOn.continuousAt hU))
    (eventually_lowerSolution_nonempty hgc hφc hb) hu ε hε

/-- Cor. 4.7 of [Dempe 2002]: for a jointly convex follower's problem, under (C) and (MFCQ) at all
`(x̄, y)`, `y ∈ Ψ(x̄)`, `∂̄μ'(x̄) = {∇ₓL(x̄, ȳ, λ) | λ ∈ Λ(x̄, ȳ)}` for every `ȳ ∈ Ψ(x̄)` and every
real `μ'` Lipschitz around `x̄` that agrees with `μ` near `x̄`; `Ψ(x̄)` need not be a singleton. -/
theorem clarkeSubdiff_lowerValue_eq_of_convexOn (hgc : ∀ i, Continuous (g i))
    (hφc : Continuous φ) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hy₀ : y₀ ∈ lowerSolution φ g x₀) (hφv : ConvexOn ℝ univ φ)
    (hgv : ∀ i, ConvexOn ℝ univ (g i))
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) {U : Set E} {L : ℝ≥0}
    {μ : E → ℝ} (hU : U ∈ 𝓝 x₀) (hμ : ∀ x ∈ U, lowerValue φ g x = μ x)
    (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff μ x₀ = lagrangianGradients φ g x₀ y₀ := by
  have hdφ : ∀ y ∈ lowerSolution φ g x₀, DifferentiableAt ℝ φ (x₀, y) :=
    fun y hy ↦ (hφ y hy).differentiableAt one_ne_zero
  have hdg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, DifferentiableAt ℝ (g i) (x₀, y) :=
    fun y hy i ↦ (hg y hy i).differentiableAt one_ne_zero
  refine subset_antisymm ((clarkeSubdiff_lowerValue_subset hgc hφc hb ⟨y₀, hy₀.1⟩ hφ hg hreg hU hμ
    hL).trans (convexHull_min (iUnion₂_subset fun y hy ↦
      lagrangianGradients_subset_of_convexOn hφv hgv hy hy₀ (hdφ y hy) (hdg y hy) (hdφ y₀ hy₀)
        (hg y₀ hy₀) (hreg y₀ hy₀)) convex_lagrangianGradients)) fun u hu ↦ ?_
  have hμ₀ : μ x₀ = φ (x₀, y₀) := by
    have := (hμ x₀ (mem_of_mem_nhds hU)).symm.trans
      (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀)
    exact_mod_cast this
  refine mem_clarkeSubdiff_of_le hU hμ fun ε hε ↦ Eventually.of_forall fun x ↦ ?_
  rw [hμ₀]
  refine le_trans (EReal.coe_le_coe_iff.2 ?_)
    (le_lowerValue_of_convexOn hφv hgv (hdφ y₀ hy₀) (hdg y₀ hy₀) hu x)
  nlinarith [norm_nonneg (x - x₀)]

end Equality

end Bilevel
