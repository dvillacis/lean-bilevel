/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.LinearGeometry

/-!
# Regions of stability and local optimality for linear bilevel problems

Sect. 3.5.2 of [Dempe 2002]. The graph of the follower's solution map is the union of the faces
`activeFace I` of the follower's constraint set over the dual supports `I` (Thm. 3.1). The index
set `I` plays the role of an optimal basic matrix, and its *region of stability* is the set of
leader's choices `x` over which the face has a point. Since the regions are closed and there are
finitely many of them, near `x̄` only the regions containing `x̄` matter, and on each of them the
problem is a linear program over a convex polyhedron. This reduces local optimality to finitely
many linear comparisons.

## Main results

* `IsConvexPolyhedral.isClosed_image_fst`: the projection of a convex polyhedral set in `E × F`
  onto `E` is closed (`F` finite-dimensional), via the inhomogeneous Farkas lemma
  `exists_forall_le_of_forall_nonneg`.
* `stabilityRegion`, `isClosed_stabilityRegion`, `convex_stabilityRegion`: regions of stability
  [Dempe 2002, Def. 3.3].
* `eventually_exists_mem_stabilityRegion`: near `x̄`, every follower's solution lies on a face whose
  region of stability contains `x̄` [Dempe 2002, p. 49].
* `not_isLocalOptimistic_iff`: Thm. 3.8 of [Dempe 2002]: `(x̄, ȳ)` is not a local optimistic
  solution iff some follower's solution at `x̄` is better for the leader, or some face through an
  equally good point over `x̄` contains a strictly better point.
* `isLocalOptimisticSolution_iff_isLocalOptimistic`: for leader's constraints not involving `y`,
  `IsLocalOptimistic` is the general notion of Def. 5.2.
* `stableInterior`, `lowerSolution_eq_singleton`: the set `R⁰(B)` of [Dempe 2002, p. 52]; uniqueness
  of the follower's solution at a point of `R⁰` propagates along segments in the region.
* `not_isLocalPessimisticSolution`: Thm. 3.9 of [Dempe 2002].
* `isLocalPessimisticSolution_of_forall`: Thm. 3.10 of [Dempe 2002].

## Differences from [Dempe 2002]

* The follower's problem is `min {d y : C x + D y ≥ b}` instead of the standard form
  `min {⟨y¹, x⟩ : A¹ x + A² y² = a, x ≥ 0}`, and the leader's variable enters only the right-hand
  side. Basic matrices `B` are replaced by index sets `I` of active constraints that support a dual
  feasible multiplier, and the basic solution `x^B(y)` by the points of the face `activeFace I`. The
  book's comparison `⟨d¹_B, B⁻¹ A² (ỹ² - ȳ²)⟩ < ⟨d², ȳ - ỹ⟩` is the comparison of the leader's
  objective at two points of the same face.
* Thm. 3.8 is stated for leader's constraints `A x + B y ≥ a` that may involve `y`, with the local
  optimistic notion "`f(x̄, ȳ) ≤ f(x, y)` for all feasible `(x, y)` with `x` near `x̄`".
* `R⁰(I)` is the set of `x` with a unique follower's solution whose active index set is exactly
  `I` (the analogue of `M(ỹ) = {B}` for a nondegenerate basis). With this, Thm. 3.9 needs no
  genericity assumption, and its two cases hold for any point of the face over `x̄`, not only for
  basic solutions in `M(ȳ)`. The upper-level set `Ω` is any convex set.
* Thm. 3.10 is proved with the whole regions `R(I)` in place of `R⁰(B)`, so the genericity
  assumption `cl R⁰(B) = R(B)` is not needed; the book's first condition (all follower's solutions
  at `x̄` give the leader the same value) is replaced by `ȳ` being a worst one, which is part of the
  definition of a pessimistic solution.
-/

open Filter Topology Set

namespace Bilevel

section Polyhedral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem IsConvexPolyhedral.inter {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S T : Set X} (hS : IsConvexPolyhedral S) (hT : IsConvexPolyhedral T) :
    IsConvexPolyhedral (S ∩ T) := by
  classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hT
  refine ⟨s ∪ t, ?_⟩
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_union]
  exact ⟨fun h q hq ↦ hq.elim (h.1 q) (h.2 q), fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq),
    fun q hq ↦ h q (Or.inr hq)⟩⟩

theorem isConvexPolyhedral_halfSpace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (l : StrongDual ℝ X) (c : ℝ) : IsConvexPolyhedral {p | l p ≤ c} :=
  ⟨{(l, c)}, by ext; simp⟩

/-- The inhomogeneous **Farkas lemma**: the system `aⱼ y ≤ cⱼ` is solvable if `∑ μⱼ cⱼ ≥ 0`
whenever `μ ≥ 0` and `∑ μⱼ aⱼ = 0`. -/
theorem exists_forall_le_of_forall_nonneg {J : Type*} [Fintype J] [FiniteDimensional ℝ F]
    (a : J → StrongDual ℝ F) (c : J → ℝ)
    (h : ∀ μ : J → ℝ, (∀ j, 0 ≤ μ j) → ∑ j, μ j • a j = 0 → 0 ≤ ∑ j, μ j * c j) :
    ∃ y, ∀ j, a j y ≤ c j := by
  by_contra hno
  push Not at hno
  let α : Option J → StrongDual ℝ (F × ℝ) := fun o ↦ o.elim (ContinuousLinearMap.snd ℝ F ℝ)
    fun j ↦ c j • ContinuousLinearMap.snd ℝ F ℝ - (a j).comp (ContinuousLinearMap.fst ℝ F ℝ)
  have key : ∀ v : F × ℝ, (∀ o, 0 ≤ α o v) → 0 ≤ (-ContinuousLinearMap.snd ℝ F ℝ) v := by
    rintro ⟨y, t⟩ hv
    have ht : 0 ≤ t := by simpa [α] using hv none
    rcases ht.eq_or_lt with rfl | ht
    · simp
    · exfalso
      obtain ⟨j, hj⟩ := hno (t⁻¹ • y)
      have h1 : 0 ≤ c j * t - a j y := by simpa [α] using hv (some j)
      rw [map_smul, smul_eq_mul] at hj
      have h2 : c j * t < a j y := by
        have := mul_lt_mul_of_pos_right hj ht
        rwa [mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one] at this
      linarith
  obtain ⟨μ, hμ, he⟩ := VariationalAnalysis.exists_nonneg_eq_sum_of_forall_nonneg α _ key
  have h1 : ∑ j, μ (some j) • a j = 0 := by
    ext y
    have := congrArg (fun l : StrongDual ℝ (F × ℝ) ↦ l (y, 0)) he
    simp [α, Fintype.sum_option] at this
    simp [this]
  have h2 := congrArg (fun l : StrongDual ℝ (F × ℝ) ↦ l (0, 1)) he
  simp [α, Fintype.sum_option] at h2
  have := h (fun j ↦ μ (some j)) (fun j ↦ hμ _) h1
  linarith [hμ none]

/-- The projection onto `E` of a convex polyhedral set in `E × F` is closed. -/
theorem IsConvexPolyhedral.isClosed_image_fst [FiniteDimensional ℝ F] {S : Set (E × F)}
    (hS : IsConvexPolyhedral S) : IsClosed (Prod.fst '' S) := by
  obtain ⟨s, rfl⟩ := hS
  have e : Prod.fst '' {p | ∀ q ∈ s, q.1 p ≤ q.2} =
      ⋂ μ ∈ {μ : s → ℝ | (∀ j, 0 ≤ μ j) ∧
        ∑ j, μ j • (j.1.1.comp (ContinuousLinearMap.inr ℝ E F)) = 0},
        {x | ∑ j, μ j * j.1.1 (x, 0) ≤ ∑ j, μ j * j.1.2} := by
    ext x
    simp only [mem_image, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨x', y⟩, hp, rfl⟩ μ ⟨hμ, h0⟩
      have hy : ∑ j, μ j * j.1.1 (0, y) = 0 := by
        have := congrArg (fun l : StrongDual ℝ F ↦ l y) h0
        simpa using this
      calc ∑ j, μ j * j.1.1 (x', 0)
          = ∑ j, μ j * j.1.1 (x', y) - ∑ j, μ j * j.1.1 (0, y) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [← mul_sub, ← map_sub, Prod.mk_sub_mk, sub_zero, sub_self]
        _ ≤ ∑ j, μ j * j.1.2 := by
            rw [hy, sub_zero]
            exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hp j.1 j.2) (hμ j)
    · intro h
      obtain ⟨y, hy⟩ := exists_forall_le_of_forall_nonneg
        (fun j : s ↦ j.1.1.comp (ContinuousLinearMap.inr ℝ E F)) (fun j ↦ j.1.2 - j.1.1 (x, 0))
        fun μ hμ h0 ↦ by
          have := h μ ⟨hμ, h0⟩
          simp only [mul_sub, Finset.sum_sub_distrib]
          linarith
      refine ⟨(x, y), fun q hq ↦ ?_, rfl⟩
      have h1 := hy ⟨q, hq⟩
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.inr_apply] at h1
      have h2 : q.1 (x, y) = q.1 (x, 0) + q.1 (0, y) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      linarith
  rw [e]
  exact isClosed_biInter fun μ _ ↦ isClosed_le (continuous_finsetSum _ fun j _ ↦
    continuous_const.mul (j.1.1.continuous.comp (continuous_id.prodMk continuous_const)))
    continuous_const

end Polyhedral

namespace LinearBilevel

variable {E F κ ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (P : LinearBilevel E F κ ι)

/-- The linear part `(x, y) ↦ Aₖ x + Bₖ y` of the `k`-th leader's constraint. -/
def upperFunctional (k : κ) : StrongDual ℝ (E × F) :=
  (P.A k).comp (ContinuousLinearMap.fst ℝ E F) + (P.B k).comp (ContinuousLinearMap.snd ℝ E F)

theorem isConvexPolyhedral_upperFeasible [Fintype κ] : IsConvexPolyhedral P.upperFeasible := by
  classical
  refine ⟨Finset.univ.image fun k ↦ (-P.upperFunctional k, -P.a k), ?_⟩
  ext p
  simp only [upperFeasible, mem_ofPred_eq, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  simp only [upperFunctional, neg_apply, add_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', neg_le_neg_iff]

theorem objective_add_smul_sub (p q : E × F) (t : ℝ) :
    P.objective (p + t • (q - p)) = P.objective p + t * (P.objective q - P.objective p) := by
  simp only [objective_eq, map_add, map_smul, map_sub, smul_eq_mul]

/-- The region of stability of the index set `I` [Dempe 2002, Def. 3.3]: the leader's choices `x`
over which the face `activeFace I` has a point. For a dual support `I` these points solve the
follower's problem (`mem_lowerSolution_of_mem_activeFace`). -/
def stabilityRegion (I : Set ι) : Set E := Prod.fst '' P.activeFace I

/-- The set `R⁰(I)` [Dempe 2002, p. 52]: the leader's choices `x` for which the follower's
solution is unique and its active index set is exactly `I`. -/
def stableInterior (I : Set ι) : Set E :=
  {x | ∃ y, P.lowerSolution x = {y} ∧ ∀ i, P.slack i (x, y) = 0 ↔ i ∈ I}

/-- A local optimistic solution of a linear bilevel problem whose leader's constraints may
involve `y`: `f(x̄, ȳ) ≤ f(x, y)` for all feasible `(x, y)` with `x` near `x̄`. -/
def IsLocalOptimistic (p : E × F) : Prop :=
  p ∈ P.feasible ∧ ∀ᶠ x in 𝓝 p.1, ∀ y, (x, y) ∈ P.feasible → P.objective p ≤ P.objective (x, y)

/-- The leader's constraint set `{x | A x ≥ a}`, the upper-level set when `B = 0`. -/
def leaderFeasible : Set E := {x | ∀ k, P.a k ≤ P.A k x}

variable {P}

theorem stableInterior_subset_stabilityRegion (I : Set ι) :
    P.stableInterior I ⊆ P.stabilityRegion I := by
  rintro x ⟨y, hy, hact⟩
  have hy' : y ∈ P.lowerSolution x := hy ▸ rfl
  exact ⟨(x, y), ⟨mem_lowerFeasible_iff.1 hy'.1, fun i hi ↦ (hact i).2 hi⟩, rfl⟩

theorem convex_stabilityRegion [Fintype ι] (I : Set ι) : Convex ℝ (P.stabilityRegion I) :=
  (P.isConvexPolyhedral_activeFace I).convex.linear_image (LinearMap.fst ℝ E F)

theorem isClosed_stabilityRegion [Fintype ι] [FiniteDimensional ℝ F] (I : Set ι) :
    IsClosed (P.stabilityRegion I) :=
  (P.isConvexPolyhedral_activeFace I).isClosed_image_fst

variable [Fintype ι] [FiniteDimensional ℝ F]

theorem mem_lowerSolution_of_mem_activeFace {I : Set ι} (hI : P.IsDualSupport I) {p : E × F}
    (hp : p ∈ P.activeFace I) : p.2 ∈ P.lowerSolution p.1 :=
  (Set.ext_iff.1 P.graph_lowerSolution_eq p).2 (mem_iUnion₂.2 ⟨I, hI, hp⟩)

theorem mem_feasible_of_mem_activeFace {I : Set ι} (hI : P.IsDualSupport I) {p : E × F}
    (hp : p ∈ P.activeFace I ∩ P.upperFeasible) : p ∈ P.feasible :=
  (Set.ext_iff.1 P.feasible_eq p).2 (mem_iUnion₂.2 ⟨I, hI, hp⟩)

/-- Near `x̄`, every follower's solution lies on a face, with a dual support as its index set,
whose region of stability contains `x̄` [Dempe 2002, p. 49]. -/
theorem eventually_exists_mem_stabilityRegion (x₀ : E) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ P.lowerSolution x, ∃ I, P.IsDualSupport I ∧ (x, y) ∈ P.activeFace I ∧
      x₀ ∈ P.stabilityRegion I := by
  classical
  have h : ∀ᶠ x in 𝓝 x₀, ∀ I : Set ι, x ∈ P.stabilityRegion I → x₀ ∈ P.stabilityRegion I := by
    refine eventually_all.2 fun I ↦ ?_
    by_cases hI : x₀ ∈ P.stabilityRegion I
    · exact Eventually.of_forall fun _ _ ↦ hI
    · exact Filter.mem_of_superset ((P.isClosed_stabilityRegion I).isOpen_compl.mem_nhds hI)
        fun x hx h ↦ absurd h hx
  refine h.mono fun x hx y hy ↦ ?_
  obtain ⟨I, hI, hp⟩ := mem_iUnion₂.1 ((Set.ext_iff.1 P.graph_lowerSolution_eq (x, y)).1 hy)
  exact ⟨I, hI, hp, hx I ⟨(x, y), hp, rfl⟩⟩

/-! ### The optimistic case -/

/-- One direction of Thm. 3.8 of [Dempe 2002]: a better follower's solution at `x̄`, or a face
through an equally good point over `x̄` containing a strictly better point, excludes local
optimality. -/
theorem not_isLocalOptimistic_of_exists [Fintype κ] {p : E × F}
    (h : (∃ y, (p.1, y) ∈ P.feasible ∧ P.objective (p.1, y) < P.objective p) ∨
      ∃ I, P.IsDualSupport I ∧ ∃ y, (p.1, y) ∈ P.activeFace I ∩ P.upperFeasible ∧
        P.objective (p.1, y) = P.objective p ∧
        ∃ q ∈ P.activeFace I ∩ P.upperFeasible, P.objective q < P.objective p) :
    ¬ P.IsLocalOptimistic p := by
  rintro ⟨-, hev⟩
  rcases h with ⟨y, hy, hlt⟩ | ⟨I, hI, y, hy, heq, q, hq, hlt⟩
  · exact (hev.self_of_nhds y hy).not_gt hlt
  · have hc : Tendsto (fun t : ℝ ↦ ((p.1, y) + t • (q - (p.1, y))).1) (𝓝[>] 0) (𝓝 p.1) :=
      ((by fun_prop : Continuous fun t : ℝ ↦ ((p.1, y) + t • (q - (p.1, y))).1).tendsto'
        0 p.1 (by simp)).mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht1⟩ := ((hc.eventually hev).and (Ioo_mem_nhdsGT one_pos)).exists
    have hmem : (p.1, y) + t • (q - (p.1, y)) ∈ P.activeFace I ∩ P.upperFeasible :=
      ((P.isConvexPolyhedral_activeFace I).inter P.isConvexPolyhedral_upperFeasible).convex
        |>.add_smul_sub_mem hy hq ⟨ht1.1.le, ht1.2.le⟩
    have : P.objective p ≤ P.objective ((p.1, y) + t • (q - (p.1, y))) :=
      ht _ (P.mem_feasible_of_mem_activeFace hI hmem)
    rw [objective_add_smul_sub, heq] at this
    nlinarith [ht1.1]

/-- The other direction of Thm. 3.8 of [Dempe 2002]. -/
theorem isLocalOptimistic_of_forall [Fintype κ] {p : E × F} (hp : p ∈ P.feasible)
    (h1 : ∀ y, (p.1, y) ∈ P.feasible → P.objective p ≤ P.objective (p.1, y))
    (h2 : ∀ I, P.IsDualSupport I → ∀ y, (p.1, y) ∈ P.activeFace I ∩ P.upperFeasible →
      P.objective (p.1, y) = P.objective p →
      ∀ q ∈ P.activeFace I ∩ P.upperFeasible, P.objective p ≤ P.objective q) :
    P.IsLocalOptimistic p := by
  classical
  let T : Set ι → Set E := fun I ↦ Prod.fst ''
    (P.activeFace I ∩ P.upperFeasible ∩ {r | P.objectiveFunctional r ≤ P.objective p})
  have hT : ∀ I, IsClosed (T I) := fun I ↦
    (((P.isConvexPolyhedral_activeFace I).inter P.isConvexPolyhedral_upperFeasible).inter
      (isConvexPolyhedral_halfSpace _ _)).isClosed_image_fst
  have hev : ∀ᶠ x in 𝓝 p.1, ∀ I, x ∈ T I → p.1 ∈ T I := eventually_all.2 fun I ↦ by
    by_cases hI : p.1 ∈ T I
    · exact Eventually.of_forall fun _ _ ↦ hI
    · exact Filter.mem_of_superset ((hT I).isOpen_compl.mem_nhds hI) fun x hx h ↦ absurd h hx
  refine ⟨hp, hev.mono fun x hx y hxy ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨I, hI, hmem⟩ := mem_iUnion₂.1 ((Set.ext_iff.1 P.feasible_eq (x, y)).1 hxy)
  obtain ⟨r, ⟨hr, hro⟩, hr1⟩ := hx I ⟨(x, y), ⟨hmem, hlt.le⟩, rfl⟩
  have hre : (p.1, r.2) = r := Prod.ext hr1.symm rfl
  have hfe : P.objective (p.1, r.2) = P.objective p := by
    refine le_antisymm (by rw [hre]; exact hro) (h1 _ ?_)
    rw [hre]
    exact P.mem_feasible_of_mem_activeFace hI hr
  exact (h2 I hI r.2 (by rw [hre]; exact hr) hfe (x, y) hmem).not_gt hlt

/-- Thm. 3.8 of [Dempe 2002]: a feasible point `(x̄, ȳ)` is not a local optimistic solution iff
either some follower's solution at `x̄` is better for the leader, or for some dual support `I`
the face `activeFace I` (intersected with the leader's constraints) contains an equally good
point `(x̄, y)` and a strictly better point. -/
theorem not_isLocalOptimistic_iff [Fintype κ] {p : E × F} (hp : p ∈ P.feasible) :
    ¬ P.IsLocalOptimistic p ↔
      (∃ y, (p.1, y) ∈ P.feasible ∧ P.objective (p.1, y) < P.objective p) ∨
      ∃ I, P.IsDualSupport I ∧ ∃ y, (p.1, y) ∈ P.activeFace I ∩ P.upperFeasible ∧
        P.objective (p.1, y) = P.objective p ∧
        ∃ q ∈ P.activeFace I ∩ P.upperFeasible, P.objective q < P.objective p := by
  refine ⟨fun h ↦ ?_, not_isLocalOptimistic_of_exists⟩
  by_contra hc
  push Not at hc
  exact h (isLocalOptimistic_of_forall hp hc.1 hc.2)

omit [Fintype ι] [FiniteDimensional ℝ F] in
/-- For leader's constraints not involving `y`, `IsLocalOptimistic` is the local optimistic
solution of Def. 5.2 of [Dempe 2002] with `Ω = {x | A x ≥ a}`. -/
theorem isLocalOptimisticSolution_iff_isLocalOptimistic (hB : P.B = 0) {p : E × F} :
    IsLocalOptimisticSolution P.objective P.lowerObjective P.lowerFeasible P.leaderFeasible
      p.1 p.2 ↔ P.IsLocalOptimistic p := by
  have hu : ∀ q : E × F, q ∈ P.upperFeasible ↔ q.1 ∈ P.leaderFeasible := fun q ↦ by
    simp [upperFeasible, leaderFeasible, hB]
  rw [isLocalOptimisticSolution_iff, IsLocalOptimistic, eventually_nhdsWithin_iff]
  simp only [feasible, mem_ofPred_eq, hu]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3.mono fun x hx y hy ↦ hx hy.1 y hy.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3.mono fun x hx hxΩ y hy ↦ hx y ⟨hxΩ, hy⟩⟩

/-! ### The pessimistic case -/

/-- If the follower's solution at `q.1` is unique with active index set exactly `I`, then the
follower's solution stays unique along the segment from any point `p` of the face `activeFace I`
to `q` (except possibly at `p`). -/
theorem lowerSolution_eq_singleton {I : Set ι} {p q : E × F} (hp : p ∈ P.activeFace I)
    (hq : P.lowerSolution q.1 = {q.2}) (hact : ∀ i, P.slack i q = 0 ↔ i ∈ I) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    P.lowerSolution (p + t • (q - p)).1 = {(p + t • (q - p)).2} := by
  have hqs : q.2 ∈ P.lowerSolution q.1 := hq ▸ rfl
  have hqf : ∀ i, 0 ≤ P.slack i q := mem_lowerFeasible_iff.1 hqs.1
  have hqI : q ∈ P.activeFace I := ⟨hqf, fun i hi ↦ (hact i).2 hi⟩
  have hI : P.IsDualSupport I := by
    obtain ⟨J, ⟨lam, hlam, hJ⟩, hqJ⟩ :=
      mem_iUnion₂.1 ((Set.ext_iff.1 P.graph_lowerSolution_eq q).1 hqs)
    exact ⟨lam, hlam, fun i hi ↦ hJ i fun hiJ ↦ hi ((hact i).1 (hqJ.2 i hiJ))⟩
  set r := p + t • (q - p) with hr
  have hrI : r ∈ P.activeFace I :=
    (P.isConvexPolyhedral_activeFace I).convex.add_smul_sub_mem hp hqI ⟨ht.1.le, ht.2⟩
  have hrs : r.2 ∈ P.lowerSolution r.1 := mem_lowerSolution_of_mem_activeFace hI hrI
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hrs, fun z hz ↦ ?_⟩
  have hdz : P.d z = P.d r.2 := le_antisymm (hz.2 _ hrs.1) (hrs.2 _ hz.1)
  have hsl : ∀ (s : ℝ) i, P.slack i (q.1, q.2 + s • (z - r.2)) =
      P.slack i q + s * (P.slack i (r.1, z) - P.slack i r) := by
    intro s i
    simp only [slack, map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, i ∉ I →
      0 < P.slack i q + s * (P.slack i (r.1, z) - P.slack i r) := by
    refine eventually_all.2 fun i ↦ ?_
    by_cases hi : i ∈ I
    · exact Eventually.of_forall fun _ h ↦ absurd hi h
    · have h0 : 0 < P.slack i q := lt_of_le_of_ne (hqf i) fun h ↦ hi ((hact i).1 h.symm)
      have hc : Tendsto (fun s : ℝ ↦ P.slack i q + s * (P.slack i (r.1, z) - P.slack i r))
          (𝓝 0) (𝓝 (P.slack i q + 0 * (P.slack i (r.1, z) - P.slack i r))) :=
        tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at hc
      exact (hc.eventually (lt_mem_nhds h0)).mono fun _ h _ ↦ h
  obtain ⟨s, hs, hs0⟩ := ((hpos.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hw : q.2 + s • (z - r.2) ∈ P.lowerSolution q.1 := by
    refine ⟨mem_lowerFeasible_iff.2 fun i ↦ ?_, fun z' hz' ↦ ?_⟩
    · rw [hsl]
      by_cases hi : i ∈ I
      · have h1 : P.slack i r = 0 := hrI.2 i hi
        have h2 : 0 ≤ P.slack i (r.1, z) := mem_lowerFeasible_iff.1 hz.1 i
        rw [h1, sub_zero]
        have : (0 : ℝ) < s := hs0
        nlinarith [hqf i]
      · exact (hs i hi).le
    · show P.d (q.2 + s • (z - r.2)) ≤ P.d z'
      rw [map_add, map_smul, map_sub, hdz, sub_self, smul_zero, add_zero]
      exact hqs.2 z' hz'
  rw [hq] at hw
  have h3 : s • (z - r.2) = 0 := by simpa using hw
  rcases smul_eq_zero.1 h3 with h | h
  · exact absurd h (ne_of_gt hs0)
  · exact sub_eq_zero.1 h

/-- Thm. 3.9 of [Dempe 2002]: let `(x̄, y')` lie on the face `activeFace I` and let `x̂ ∈ Ω` be a
point of `R⁰(I)` with follower's solution `ŷ`. If `(x̄, y')` is better for the leader than `ȳ`, or
equally good while `(x̂, ŷ)` is strictly better, then `(x̄, ȳ)` is not a local pessimistic
solution. -/
theorem not_isLocalPessimisticSolution {Ω : Set E} (hΩ : Convex ℝ Ω) {x₀ : E} {y₀ y' : F}
    {I : Set ι} (hy' : (x₀, y') ∈ P.activeFace I) {x₁ : E} {y₁ : F} (hx₁ : x₁ ∈ Ω)
    (hy₁ : P.lowerSolution x₁ = {y₁}) (hact : ∀ i, P.slack i (x₁, y₁) = 0 ↔ i ∈ I)
    (hdesc : P.objective (x₀, y') < P.objective (x₀, y₀) ∨
      P.objective (x₀, y') = P.objective (x₀, y₀) ∧
        P.objective (x₁, y₁) < P.objective (x₀, y₀)) :
    ¬ IsLocalPessimisticSolution P.objective P.lowerObjective P.lowerFeasible Ω x₀ y₀ := by
  rintro ⟨hx₀, hy₀, hworst, hmin⟩
  set p : E × F := (x₀, y') with hp
  set q : E × F := (x₁, y₁) with hq
  have hseg : ∀ t ∈ Ioc (0 : ℝ) 1,
      (p + t • (q - p)).1 ∈ solvableSet P.lowerObjective P.lowerFeasible Ω ∧
      pessimisticValue P.objective P.lowerObjective P.lowerFeasible (p + t • (q - p)).1 =
        (P.objective (p + t • (q - p)) : EReal) := by
    intro t ht
    have hu := lowerSolution_eq_singleton hy' hy₁ hact ht
    have hmem : (p + t • (q - p)).2 ∈ P.lowerSolution (p + t • (q - p)).1 := hu ▸ rfl
    refine ⟨⟨?_, _, hmem⟩, ?_⟩
    · have := hΩ.add_smul_sub_mem hx₀ hx₁ ⟨ht.1.le, ht.2⟩
      simpa [hp, hq] using this
    · refine pessimisticValue_eq hmem fun z hz ↦ ?_
      have hz' : z = (p + t • (q - p)).2 := by
        have : z ∈ P.lowerSolution (p + t • (q - p)).1 := hz
        rw [hu] at this
        exact this
      subst hz'
      exact le_rfl
  have hcont : Tendsto (fun t : ℝ ↦ (p + t • (q - p)).1) (𝓝[>] 0) (𝓝 x₀) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ (p + t • (q - p)).1).tendsto' 0 x₀
      (by simp [hp])).mono_left nhdsWithin_le_nhds
  have hT : Tendsto (fun t : ℝ ↦ (p + t • (q - p)).1) (𝓝[>] 0)
      (𝓝[solvableSet P.lowerObjective P.lowerFeasible Ω] x₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hcont, mem_of_superset (Ioo_mem_nhdsGT one_pos)
      fun t ht ↦ (hseg t ⟨ht.1, ht.2.le⟩).1⟩
  have hdes : ∀ᶠ t in 𝓝[>] (0 : ℝ), P.objective (p + t • (q - p)) < P.objective (x₀, y₀) := by
    simp only [objective_add_smul_sub]
    rcases hdesc with h | ⟨h1, h2⟩
    · have hc : Tendsto (fun t : ℝ ↦ P.objective p + t * (P.objective q - P.objective p))
          (𝓝 0) (𝓝 (P.objective p + 0 * (P.objective q - P.objective p))) :=
        tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at hc
      exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds h))
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have h1' : P.objective p = P.objective (x₀, y₀) := h1
      have h2' : P.objective q < P.objective (x₀, y₀) := h2
      nlinarith
  obtain ⟨t, ⟨h1, h2⟩, h3⟩ :=
    (((hT.eventually (hmin : ∀ᶠ x in _, _ ≤ _)).and hdes).and (Ioo_mem_nhdsGT one_pos)).exists
  rw [pessimisticValue_eq hy₀ hworst, (hseg t ⟨h3.1, h3.2.le⟩).2] at h1
  exact (EReal.coe_le_coe_iff.1 h1).not_gt h2

/-- Thm. 3.10 of [Dempe 2002]: if `ȳ` is a worst follower's solution at `x̄ ∈ Ω` and no point of
a face whose region of stability contains `x̄` is better for the leader than `(x̄, ȳ)`, then
`(x̄, ȳ)` is a local pessimistic solution. -/
theorem isLocalPessimisticSolution_of_forall {Ω : Set E} {x₀ : E} {y₀ : F} (hx₀ : x₀ ∈ Ω)
    (hy₀ : y₀ ∈ P.lowerSolution x₀)
    (hworst : ∀ y ∈ P.lowerSolution x₀, P.objective (x₀, y) ≤ P.objective (x₀, y₀))
    (h : ∀ I, P.IsDualSupport I → x₀ ∈ P.stabilityRegion I →
      ∀ q ∈ P.activeFace I, q.1 ∈ Ω → P.objective (x₀, y₀) ≤ P.objective q) :
    IsLocalPessimisticSolution P.objective P.lowerObjective P.lowerFeasible Ω x₀ y₀ := by
  refine ⟨hx₀, hy₀, hworst, ?_⟩
  show ∀ᶠ x in 𝓝[solvableSet P.lowerObjective P.lowerFeasible Ω] x₀, _ ≤ _
  filter_upwards [nhdsWithin_le_nhds (P.eventually_exists_mem_stabilityRegion x₀),
    self_mem_nhdsWithin] with x hx hxs
  obtain ⟨hxΩ, y, hy⟩ := hxs
  rw [pessimisticValue_eq hy₀ hworst]
  obtain ⟨I, hI, hxy, hx₀I⟩ := hx y hy
  exact (EReal.coe_le_coe_iff.2 (h I hI hx₀I (x, y) hxy hxΩ)).trans (le_pessimisticValue hy)

end LinearBilevel

end Bilevel
