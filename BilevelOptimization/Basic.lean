/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Optimality.Bilevel

/-!
# Solution concepts for bilevel programs

Sect. 5.1 of [Dempe 2002]: optimistic and pessimistic solutions, the joint problem (5.5), lower
optimal solutions (5.8), and the lower-level value function reformulation (5.36) of Sect. 5.6.

We follow the conventions of `VariationalAnalysis.Optimality.Bilevel`: the leader's variable is
`x ∈ E`, the follower's variable is `y ∈ F` (Dempe uses the opposite letters). The data are the
leader's objective `f : E × F → ℝ`, the follower's objective `φ : E × F → ℝ`, the follower's
feasible-set map `K : E → Set F` and the leader's constraint set `Ω : Set E`. The follower's
problem is `min_y {φ(x, y) | y ∈ K(x)}` (5.1) with solution map `Ψ = solutionMap φ K`.

## Main definitions

* `solutionMap φ K`: the lower-level solution map `Ψ`.
* `optimisticValue f φ K`, `pessimisticValue f φ K`: `φ_o` (5.4) and `φ_p` (5.7), with values in
  `EReal` (`φ_o(x) = +∞` and `φ_p(x) = -∞` when `Ψ(x) = ∅`).
* `IsLocalOptimisticSolution`, `IsOptimisticSolution`: Def. 5.2.
* `IsLocalPessimisticSolution`, `IsPessimisticSolution`: Def. 5.3.
* `bilevelFeasible φ K Ω`: the feasible set `{(x, y) | x ∈ Ω, y ∈ Ψ(x)}` of (5.5).
* `lowerOptimalSet f φ K Ω`: the lower optimal solutions (5.8).

## Main results

* `isOptimisticSolution_iff`: global optimistic solutions are the global solutions of (5.5)
  [Dempe 2002, p. 132].
* `IsLocalOptimisticSolution.isLocalMinOn`: local optimistic solutions are local solutions of
  (5.5), hence of the value function reformulation (5.36) [Dempe 2002, p. 163].
* `not_isLocalOptimisticSolution_example`: the converse fails [Dempe 2002, Example on p. 157].
* `bilevelFeasible_eq_valueFeasible`: (5.5) and the value function reformulation (5.36) have the
  same feasible set; for `K = lowerFeasible g` this is `VariationalAnalysis.valueFeasible`.
* `exists_isOptimisticSolution_of_isCompact`: existence of global optimistic solutions when the
  feasible set of (5.5) is compact (the abstract core of Thm. 5.2).
* `isOptimisticSolution_example`, `not_isPessimisticSolution_example`: an optimistic solution
  exists while no pessimistic solution does [Dempe 2002, Example on pp. 129, 134].

## Remarks on the book

* In the Example on p. 134 the displayed formulas for `φ_o` and `φ_p` have the sign of the
  parameter swapped (they correspond to `Ψ(y) = Argmin_x {xy : 0 ≤ x ≤ 1}`); with
  `Ψ(y) = Argmin_x {-xy : 0 ≤ x ≤ 1}` as stated, `φ_o(y) = y²` for `y ≤ 0`,
  `φ_o(y) = 1 + y²` for `y > 0`, `φ_p(y) = y²` for `y < 0` and `φ_p(y) = 1 + y²` for `y ≥ 0`.
  The conclusion (optimistic solution `y = 0`, no pessimistic solution) is unchanged.
-/

open Filter Topology Set

namespace Bilevel

variable {E F : Type*}

section Definitions

variable (f φ : E × F → ℝ) (K : E → Set F) (Ω : Set E)

/-- The lower-level solution map `Ψ(x) = Argmin_y {φ(x, y) | y ∈ K(x)}` [Dempe 2002, (5.1)]. -/
def solutionMap (x : E) : Set F :=
  {y | y ∈ K x ∧ ∀ z ∈ K x, φ (x, y) ≤ φ (x, z)}

/-- The optimistic value function `φ_o(x) = inf {f(x, y) | y ∈ Ψ(x)}` [Dempe 2002, (5.4)]. -/
noncomputable def optimisticValue (x : E) : EReal :=
  ⨅ y ∈ solutionMap φ K x, (f (x, y) : EReal)

/-- The pessimistic value function `φ_p(x) = sup {f(x, y) | y ∈ Ψ(x)}` [Dempe 2002, (5.7)]. -/
noncomputable def pessimisticValue (x : E) : EReal :=
  ⨆ y ∈ solutionMap φ K x, (f (x, y) : EReal)

/-- The feasible set `{(x, y) | x ∈ Ω, y ∈ Ψ(x)}` of the joint problem (5.5) of
[Dempe 2002]. -/
def bilevelFeasible : Set (E × F) :=
  {p | p.1 ∈ Ω ∧ p.2 ∈ solutionMap φ K p.1}

/-- A global optimistic solution [Dempe 2002, Def. 5.2]. -/
def IsOptimisticSolution (x₀ : E) (y₀ : F) : Prop :=
  x₀ ∈ Ω ∧ y₀ ∈ solutionMap φ K x₀ ∧ (∀ y ∈ solutionMap φ K x₀, f (x₀, y₀) ≤ f (x₀, y)) ∧
    IsMinOn (optimisticValue f φ K) Ω x₀

/-- A global pessimistic solution [Dempe 2002, Def. 5.3]. -/
def IsPessimisticSolution (x₀ : E) (y₀ : F) : Prop :=
  x₀ ∈ Ω ∧ y₀ ∈ solutionMap φ K x₀ ∧ (∀ y ∈ solutionMap φ K x₀, f (x₀, y) ≤ f (x₀, y₀)) ∧
    IsMinOn (pessimisticValue f φ K) Ω x₀

/-- The lower optimal solutions `{(x, y) | x ∈ Ω, y ∈ Ψ(x), f(x, y) ≤ inf_{z ∈ Ω} φ_p(z)}`
[Dempe 2002, (5.8)]. -/
def lowerOptimalSet : Set (E × F) :=
  {p | p ∈ bilevelFeasible φ K Ω ∧ (f p : EReal) ≤ ⨅ x ∈ Ω, pessimisticValue f φ K x}

variable [TopologicalSpace E]

/-- A local optimistic solution [Dempe 2002, Def. 5.2]. -/
def IsLocalOptimisticSolution (x₀ : E) (y₀ : F) : Prop :=
  x₀ ∈ Ω ∧ y₀ ∈ solutionMap φ K x₀ ∧ (∀ y ∈ solutionMap φ K x₀, f (x₀, y₀) ≤ f (x₀, y)) ∧
    IsLocalMinOn (optimisticValue f φ K) Ω x₀

/-- A local pessimistic solution [Dempe 2002, Def. 5.3]. -/
def IsLocalPessimisticSolution (x₀ : E) (y₀ : F) : Prop :=
  x₀ ∈ Ω ∧ y₀ ∈ solutionMap φ K x₀ ∧ (∀ y ∈ solutionMap φ K x₀, f (x₀, y) ≤ f (x₀, y₀)) ∧
    IsLocalMinOn (pessimisticValue f φ K) Ω x₀

end Definitions

variable {f φ : E × F → ℝ} {K : E → Set F} {Ω : Set E} {x x₀ : E} {y y₀ : F}

/-! ### Value functions -/

theorem optimisticValue_le (hy : y ∈ solutionMap φ K x) :
    optimisticValue f φ K x ≤ f (x, y) :=
  biInf_le (fun y ↦ (f (x, y) : EReal)) hy

theorem le_pessimisticValue (hy : y ∈ solutionMap φ K x) :
    (f (x, y) : EReal) ≤ pessimisticValue f φ K x :=
  le_biSup (fun y ↦ (f (x, y) : EReal)) hy

theorem optimisticValue_eq (hy : y ∈ solutionMap φ K x)
    (hmin : ∀ z ∈ solutionMap φ K x, f (x, y) ≤ f (x, z)) :
    optimisticValue f φ K x = f (x, y) :=
  le_antisymm (optimisticValue_le hy) (le_iInf₂ fun z hz ↦ EReal.coe_le_coe_iff.2 (hmin z hz))

theorem pessimisticValue_eq (hy : y ∈ solutionMap φ K x)
    (hmax : ∀ z ∈ solutionMap φ K x, f (x, z) ≤ f (x, y)) :
    pessimisticValue f φ K x = f (x, y) :=
  le_antisymm (iSup₂_le fun z hz ↦ EReal.coe_le_coe_iff.2 (hmax z hz)) (le_pessimisticValue hy)

/-! ### Optimistic solutions and the joint problem (5.5) -/

theorem mem_bilevelFeasible_iff {p : E × F} :
    p ∈ bilevelFeasible φ K Ω ↔ p.1 ∈ Ω ∧ p.2 ∈ solutionMap φ K p.1 :=
  Iff.rfl

/-- Global optimistic solutions are exactly the global solutions of the joint problem (5.5)
[Dempe 2002, p. 132]. -/
theorem isOptimisticSolution_iff :
    IsOptimisticSolution f φ K Ω x₀ y₀ ↔
      (x₀, y₀) ∈ bilevelFeasible φ K Ω ∧ IsMinOn f (bilevelFeasible φ K Ω) (x₀, y₀) := by
  constructor
  · rintro ⟨hx, hy, hbest, hmin⟩
    refine ⟨⟨hx, hy⟩, fun p hp ↦ ?_⟩
    have h1 := hmin hp.1
    rw [mem_ofPred_eq, optimisticValue_eq hy hbest] at h1
    exact EReal.coe_le_coe_iff.1 (h1.trans (optimisticValue_le hp.2))
  · rintro ⟨⟨hx, hy⟩, hmin⟩
    have hbest : ∀ y ∈ solutionMap φ K x₀, f (x₀, y₀) ≤ f (x₀, y) := fun y hy' ↦ hmin ⟨hx, hy'⟩
    refine ⟨hx, hy, hbest, fun x hx' ↦ ?_⟩
    rw [mem_ofPred_eq, optimisticValue_eq hy hbest]
    exact le_iInf₂ fun y hy' ↦ EReal.coe_le_coe_iff.2 (hmin ⟨hx', hy'⟩)

/-- Existence of global optimistic solutions when the feasible set of (5.5) is nonempty and
compact and `f` is continuous on it (the abstract core of [Dempe 2002, Thm. 5.2], where
compactness comes from (C), (MFCQ) and Thm. 4.3). -/
theorem exists_isOptimisticSolution_of_isCompact [TopologicalSpace E] [TopologicalSpace F]
    (hc : IsCompact (bilevelFeasible φ K Ω)) (hne : (bilevelFeasible φ K Ω).Nonempty)
    (hf : ContinuousOn f (bilevelFeasible φ K Ω)) :
    ∃ x₀ y₀, IsOptimisticSolution f φ K Ω x₀ y₀ := by
  obtain ⟨p, hp, hmin⟩ := hc.exists_isMinOn hne hf
  exact ⟨p.1, p.2, isOptimisticSolution_iff.2 ⟨hp, hmin⟩⟩

section Local

variable [TopologicalSpace E] [TopologicalSpace F]

/-- Local optimistic solutions are local solutions of the joint problem (5.5)
[Dempe 2002, p. 163, proof of Thm. 5.15]. -/
theorem IsLocalOptimisticSolution.isLocalMinOn (h : IsLocalOptimisticSolution f φ K Ω x₀ y₀) :
    IsLocalMinOn f (bilevelFeasible φ K Ω) (x₀, y₀) := by
  obtain ⟨-, hy, hbest, hmin⟩ := h
  have hmin' : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), p.1 ∈ Ω →
      optimisticValue f φ K x₀ ≤ optimisticValue f φ K p.1 :=
    (continuous_fst.tendsto (x₀, y₀)).eventually (eventually_nhdsWithin_iff.1 hmin)
  refine eventually_nhdsWithin_iff.2 (hmin'.mono fun p hp hpF ↦ ?_)
  have h1 := hp hpF.1
  rw [optimisticValue_eq hy hbest] at h1
  exact EReal.coe_le_coe_iff.1 (h1.trans (optimisticValue_le hpF.2))

omit [TopologicalSpace F] in
theorem IsOptimisticSolution.isLocalOptimisticSolution (h : IsOptimisticSolution f φ K Ω x₀ y₀) :
    IsLocalOptimisticSolution f φ K Ω x₀ y₀ :=
  ⟨h.1, h.2.1, h.2.2.1, IsMinOn.localize h.2.2.2⟩

omit [TopologicalSpace F] in
theorem IsPessimisticSolution.isLocalPessimisticSolution
    (h : IsPessimisticSolution f φ K Ω x₀ y₀) : IsLocalPessimisticSolution f φ K Ω x₀ y₀ :=
  ⟨h.1, h.2.1, h.2.2.1, IsMinOn.localize h.2.2.2⟩

end Local

/-! ### The value function reformulation (5.36) -/

section ValueFunction

open VariationalAnalysis (marginal lowerFeasible lowerSolution lowerValue valueFeasible)

/-- `y ∈ Ψ(x)` iff `y ∈ K(x)` and `φ(x, y) ≤ μ(x)`, where `μ` is the lower-level value function
(a marginal function). -/
theorem mem_solutionMap_iff_le_marginal :
    y ∈ solutionMap φ K x ↔
      y ∈ K x ∧ (φ (x, y) : EReal) ≤ marginal (fun p ↦ (φ p : EReal)) K x := by
  refine and_congr_right fun _ ↦ ⟨fun h ↦ le_iInf₂ fun z hz ↦ EReal.coe_le_coe_iff.2 (h z hz),
    fun h z hz ↦ EReal.coe_le_coe_iff.1 (h.trans (biInf_le (fun z ↦ (φ (x, z) : EReal)) hz))⟩

/-- The joint problem (5.5) and the value function reformulation (5.36) of [Dempe 2002] have the
same feasible set. -/
theorem bilevelFeasible_eq_valueFeasible :
    bilevelFeasible φ K Ω =
      {p | p.1 ∈ Ω ∧ p.2 ∈ K p.1 ∧ (φ p : EReal) ≤ marginal (fun p ↦ (φ p : EReal)) K p.1} := by
  ext p
  exact and_congr_right fun _ ↦ mem_solutionMap_iff_le_marginal

variable {ι : Type*} {g : ι → E × F → ℝ}

/-- For lower-level constraints `gᵢ(x, y) ≤ 0`, `solutionMap` is
`VariationalAnalysis.lowerSolution`. -/
theorem solutionMap_lowerFeasible :
    solutionMap φ (lowerFeasible g) = lowerSolution φ g := by
  ext x y
  rw [mem_solutionMap_iff_le_marginal]
  exact ⟨fun h ↦ ⟨h.1, le_antisymm h.2 (VariationalAnalysis.lowerValue_le h.1)⟩,
    fun h ↦ ⟨h.1, h.2.le⟩⟩

/-- For lower-level constraints `gᵢ(x, y) ≤ 0`, the feasible set of (5.5) is the feasible set
`VariationalAnalysis.valueFeasible` of the value function reformulation, so that the optimality
conditions of [Mordukhovich 2018, Sect. 6.3] apply to local solutions of (5.5). -/
theorem bilevelFeasible_lowerFeasible :
    bilevelFeasible φ (lowerFeasible g) Ω = valueFeasible φ g Ω := by
  ext p
  rw [mem_bilevelFeasible_iff, VariationalAnalysis.mem_valueFeasible_iff,
    solutionMap_lowerFeasible]

end ValueFunction

/-! ### Examples -/

section Examples

/-- The follower's problem `min_y {x y | 0 ≤ y ≤ 1}` of the Example on p. 157 of
[Dempe 2002]. -/
private def exK : ℝ → Set ℝ := fun _ ↦ Icc 0 1

private theorem exΨ_of_neg {x y : ℝ} (hx : x < 0)
    (hy : y ∈ solutionMap (fun p : ℝ × ℝ ↦ p.1 * p.2) exK x) : y = 1 := by
  obtain ⟨⟨_, hy1⟩, hmin⟩ := hy
  have := hmin 1 ⟨zero_le_one, le_rfl⟩
  simp only at this
  nlinarith

/-- Local solutions of (5.5) need not be local optimistic solutions [Dempe 2002, Example on
p. 157]: for `min {x | x ∈ [-1, 1], y ∈ Argmin_y {x y | 0 ≤ y ≤ 1}}` the point `(0, 0)` is a
local solution of (5.5), but `φ_o(x) = x` has no local minimum at `0` on `[-1, 1]`. -/
theorem not_isLocalOptimisticSolution_example :
    IsLocalMinOn (fun p : ℝ × ℝ ↦ p.1)
        (bilevelFeasible (fun p : ℝ × ℝ ↦ p.1 * p.2) exK (Icc (-1) 1)) (0, 0) ∧
      ¬ IsLocalOptimisticSolution (fun p : ℝ × ℝ ↦ p.1) (fun p : ℝ × ℝ ↦ p.1 * p.2) exK
        (Icc (-1) 1) 0 0 := by
  constructor
  · have hU : {p : ℝ × ℝ | p.2 < 1} ∈ 𝓝 ((0 : ℝ), (0 : ℝ)) :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds (by norm_num)
    refine eventually_nhdsWithin_iff.2 (Filter.mem_of_superset hU fun p hp hpF ↦ ?_)
    by_contra hneg
    exact (ne_of_lt hp) (exΨ_of_neg (not_le.1 hneg) hpF.2)
  · rintro ⟨-, -, -, hmin⟩
    -- `φ_o(x) = x` whenever `Ψ(x) ≠ ∅`
    have hval : ∀ x : ℝ, x < 0 → optimisticValue (fun p : ℝ × ℝ ↦ p.1)
        (fun p : ℝ × ℝ ↦ p.1 * p.2) exK x = x := fun x hx ↦
      optimisticValue_eq (y := 1) ⟨⟨zero_le_one, le_rfl⟩, fun z hz ↦ by
        simp only; nlinarith [hz.2]⟩ fun _ _ ↦ le_rfl
    have hval0 : optimisticValue (fun p : ℝ × ℝ ↦ p.1) (fun p : ℝ × ℝ ↦ p.1 * p.2) exK 0 = 0 :=
      optimisticValue_eq (y := 0) ⟨⟨le_rfl, zero_le_one⟩, fun z _ ↦ by simp⟩ fun _ _ ↦ le_rfl
    obtain ⟨U, hUo, h0U, hsub⟩ := mem_nhdsWithin.1 hmin
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo 0 h0U
    set x := -min (ε / 2) 1
    have hx : x < 0 := neg_neg_of_pos (lt_min (half_pos hε) one_pos)
    have hxU : x ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hx, neg_neg]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
    have hxΩ : x ∈ Icc (-1 : ℝ) 1 := ⟨neg_le_neg (min_le_right _ _), hx.le.trans zero_le_one⟩
    have := hsub ⟨hxU, hxΩ⟩
    rw [mem_ofPred_eq, hval0, hval x hx] at this
    exact absurd (EReal.coe_le_coe_iff.1 this) (not_le.2 hx)

/-- The follower's problem `min_y {-x y | 0 ≤ y ≤ 1}` of the Example on pp. 129, 134 of
[Dempe 2002]. -/
private theorem exΨ'_of_neg {x y : ℝ} (hx : x < 0)
    (hy : y ∈ solutionMap (fun p : ℝ × ℝ ↦ -(p.1 * p.2)) exK x) : y = 0 := by
  obtain ⟨⟨hy0, _⟩, hmin⟩ := hy
  have := hmin 0 ⟨le_rfl, zero_le_one⟩
  simp only [mul_zero, neg_zero] at this
  nlinarith

private theorem one_mem_exΨ' {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ∈ solutionMap (fun p : ℝ × ℝ ↦ -(p.1 * p.2)) exK x :=
  ⟨⟨zero_le_one, le_rfl⟩, fun z hz ↦ by simp only [mul_one]; nlinarith [hz.2]⟩

/-- An optimistic solution exists [Dempe 2002, Example on pp. 129, 134]: for
`min {x² + y² | x ∈ [-1, 1], y ∈ Argmin_y {-x y | 0 ≤ y ≤ 1}}`, `(0, 0)` is a global optimistic
solution. -/
theorem isOptimisticSolution_example :
    IsOptimisticSolution (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) (fun p : ℝ × ℝ ↦ -(p.1 * p.2)) exK
      (Icc (-1) 1) 0 0 := by
  refine isOptimisticSolution_iff.2 ⟨⟨⟨by norm_num, by norm_num⟩,
    ⟨le_rfl, zero_le_one⟩, fun z _ ↦ by simp⟩, fun p _ ↦ ?_⟩
  simp only [mem_ofPred_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero]
  positivity

/-- No pessimistic solution exists [Dempe 2002, Example on pp. 129, 134]: for the problem of
`isOptimisticSolution_example`, `φ_p(x) = x²` for `x < 0` and `φ_p(x) ≥ 1 + x²` for `x ≥ 0`, so
`inf φ_p = 0` is not attained. -/
theorem not_isPessimisticSolution_example (x₀ y₀ : ℝ) :
    ¬ IsPessimisticSolution (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) (fun p : ℝ × ℝ ↦ -(p.1 * p.2))
      exK (Icc (-1) 1) x₀ y₀ := by
  set f : ℝ × ℝ → ℝ := fun p ↦ p.1 ^ 2 + p.2 ^ 2
  set φ : ℝ × ℝ → ℝ := fun p ↦ -(p.1 * p.2)
  have hneg : ∀ x : ℝ, x < 0 → pessimisticValue f φ exK x ≤ (x ^ 2 : ℝ) := fun x hx ↦
    iSup₂_le fun y hy ↦ by
      rw [exΨ'_of_neg hx hy]
      exact EReal.coe_le_coe_iff.2 (by simp [f])
  rintro ⟨hx₀, -, -, hmin⟩
  rcases lt_or_ge x₀ 0 with hx | hx
  · -- `x₀ < 0`: `φ_p(x₀) ≥ x₀² > (x₀ / 2)² ≥ φ_p(x₀ / 2)`
    have hy0 : (0 : ℝ) ∈ solutionMap φ exK x₀ :=
      ⟨⟨le_rfl, zero_le_one⟩, fun z hz ↦ by simp only [φ, mul_zero, neg_zero]; nlinarith [hz.1]⟩
    have h1 := le_pessimisticValue (f := f) hy0
    have h2 := hmin (show x₀ / 2 ∈ Icc (-1 : ℝ) 1 from
      ⟨by linarith [hx₀.1], by linarith⟩)
    have h3 := hneg (x₀ / 2) (by linarith)
    have := EReal.coe_le_coe_iff.1 (h1.trans (h2.trans h3))
    simp only [f] at this
    nlinarith
  · -- `x₀ ≥ 0`: `φ_p(x₀) ≥ 1 + x₀² ≥ 1 > 1/4 ≥ φ_p(-1/2)`
    have h1 := le_pessimisticValue (f := f) (one_mem_exΨ' hx)
    have h2 := hmin (show (-1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
    have h3 := hneg (-1 / 2) (by norm_num)
    have := EReal.coe_le_coe_iff.1 (h1.trans (h2.trans h3))
    simp only [f] at this
    nlinarith

end Examples

end Bilevel
