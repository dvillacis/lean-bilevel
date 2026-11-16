/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.LinearBilevel

/-!
# Bilevel problems and multicriteria optimization

Sect. 3.4.1 of [Dempe 2002], after [Fülöp 1993]. Feasibility in a bilevel problem is Pareto
optimality in a multicriteria problem whose criteria pin down the leader's variable and add the
follower's objective (Thm. 3.4, Cor. 3.2). Conversely, finding a best Pareto optimal point of a
multicriteria problem is a bilevel problem (Thm. 3.5). The example on p. 40 shows that an optimal
solution of a bilevel problem need not be Pareto optimal for the bicriteria problem built from
the two objectives.

## Main results

* `IsParetoMinOn`: Pareto optimality for a vector-valued objective.
* `multicriteriaObjective`, `isParetoMinOn_multicriteriaObjective_iff`, `paretoSet_eq`: Thm. 3.4.
* `isMinOn_paretoSet_iff`, `LinearBilevel.feasible_eq_paretoSet`: Cor. 3.2.
* `paretoLowerFeasible`, `paretoLowerObjective`, `isParetoMinOn_of_mem_solutionMap`,
  `isParetoMinOn_tfae`: Thm. 3.5 and problems (3.12)–(3.13).
* `exampleBilevelPareto…`: the example on p. 40.

## Differences from the book

* Linearity plays no role: both theorems are proved for arbitrary objectives and constraint sets.
  In Thm. 3.4 the book's criteria `(A y, -eᵀ A y)`, with `A` a square submatrix of full rank of the
  constraint matrix (and of `-E`), are replaced by `(ℓ x, -∑ₖ ℓₖ x)` for an arbitrary injective
  map `ℓ`, e.g. the coordinates in a basis.
* In Thm. 3.4 the leader's constraints `x ∈ X` must not depend on the follower's variable; for
  `LinearBilevel` this means `B = 0`.
* The roles of `x` (leader) and `y` (follower) are as in the rest of the library, which in the
  example on p. 40 is the reverse of the book.
-/

open Set

namespace Bilevel

variable {α E F κ : Type*}

/-- `a` is a Pareto optimal (efficient) point of the vector objective `f` on `S`: no point of `S`
is at least as good in every criterion and strictly better in one. -/
def IsParetoMinOn (f : α → κ → ℝ) (S : Set α) (a : α) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, f b ≤ f a → f a ≤ f b

/-- Componentwise `u ≤ v` with `∑ v ≤ ∑ u` forces `u = v`. -/
theorem eq_of_le_of_sum_le [Fintype κ] {u v : κ → ℝ} (h : u ≤ v)
    (hs : ∑ k, v k ≤ ∑ k, u k) : u = v :=
  funext fun k ↦ (Finset.sum_eq_sum_iff_of_le fun i _ ↦ h i).1
    (le_antisymm (Finset.sum_le_sum fun i _ ↦ h i) hs) k (Finset.mem_univ k)

/-! ### From bilevel to multicriteria problems -/

section ToMulticriteria

variable [Fintype κ]

/-- The criteria of problem (3.10) of [Dempe 2002]: `ℓ x` and `-∑ₖ ℓₖ x`, which force the leader's
variable to stay fixed, and the follower's objective `φ`. -/
def multicriteriaObjective (ℓ : E → κ → ℝ) (φ : E × F → ℝ) (p : E × F) :
    Option (Option κ) → ℝ
  | none => φ p
  | some none => -∑ k, ℓ p.1 k
  | some (some k) => ℓ p.1 k

theorem eq_of_multicriteriaObjective_le {ℓ : E → κ → ℝ} (hℓ : Function.Injective ℓ)
    {φ : E × F → ℝ} {p q : E × F}
    (h : multicriteriaObjective ℓ φ q ≤ multicriteriaObjective ℓ φ p) : q.1 = p.1 := by
  refine hℓ (eq_of_le_of_sum_le (fun k ↦ h (some (some k))) ?_)
  have := h (some none)
  simp only [multicriteriaObjective, neg_le_neg_iff] at this
  exact this

/-- **Thm. 3.4 of [Dempe 2002]**: `(x̄, ȳ)` is feasible for the bilevel problem with leader's
constraints `x ∈ X` and follower's problem `min_y {φ(x, y) : y ∈ K(x)}` if and only if it is a
Pareto optimal point of the multicriteria problem (3.10) on `{(x, y) : x ∈ X, y ∈ K(x)}`. -/
theorem isParetoMinOn_multicriteriaObjective_iff {ℓ : E → κ → ℝ} (hℓ : Function.Injective ℓ)
    (φ : E × F → ℝ) (X : Set E) (K : E → Set F) (p : E × F) :
    IsParetoMinOn (multicriteriaObjective ℓ φ) {q | q.1 ∈ X ∧ q.2 ∈ K q.1} p ↔
      p.1 ∈ X ∧ p.2 ∈ solutionMap φ K p.1 := by
  constructor
  · rintro ⟨⟨hX, hK⟩, hmin⟩
    refine ⟨hX, hK, fun z hz ↦ ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hle : multicriteriaObjective ℓ φ (p.1, z) ≤ multicriteriaObjective ℓ φ p := by
      rintro (_ | _ | k)
      · exact hlt.le
      · exact le_rfl
      · exact le_rfl
    exact hlt.not_ge (hmin (p.1, z) ⟨hX, hz⟩ hle none)
  · rintro ⟨hX, hK, hmin⟩
    refine ⟨⟨hX, hK⟩, fun q hq hle ↦ ?_⟩
    have h1 := eq_of_multicriteriaObjective_le hℓ hle
    rintro (_ | _ | k)
    · have := hmin q.2 (h1 ▸ hq.2)
      rw [Prod.mk.eta, show (p.1, q.2) = q from Prod.ext h1.symm rfl] at this
      exact this
    · simp [multicriteriaObjective, h1]
    · simp [multicriteriaObjective, h1]

/-- Thm. 3.4 as an equality of sets: the Pareto optimal points of (3.10) are the feasible points of
the bilevel problem. -/
theorem paretoSet_eq {ℓ : E → κ → ℝ} (hℓ : Function.Injective ℓ) (φ : E × F → ℝ) (X : Set E)
    (K : E → Set F) :
    {p | IsParetoMinOn (multicriteriaObjective ℓ φ) {q | q.1 ∈ X ∧ q.2 ∈ K q.1} p} =
      {p | p.1 ∈ X ∧ p.2 ∈ solutionMap φ K p.1} :=
  Set.ext fun p ↦ isParetoMinOn_multicriteriaObjective_iff hℓ φ X K p

/-- **Cor. 3.2 of [Dempe 2002]**: the bilevel problem is the problem of minimizing the leader's
objective over the Pareto optimal points of (3.10). -/
theorem isMinOn_paretoSet_iff {ℓ : E → κ → ℝ} (hℓ : Function.Injective ℓ) (f φ : E × F → ℝ)
    (X : Set E) (K : E → Set F) (p : E × F) :
    IsMinOn f {p | IsParetoMinOn (multicriteriaObjective ℓ φ) {q | q.1 ∈ X ∧ q.2 ∈ K q.1} p} p ↔
      IsMinOn f {p | p.1 ∈ X ∧ p.2 ∈ solutionMap φ K p.1} p := by
  rw [paretoSet_eq hℓ]

/-- Cor. 3.2 for LP–LP bilevel problems whose leader's constraints `A x ≥ a` do not involve `y`:
the feasible set is the set of Pareto optimal points of (3.10). -/
theorem LinearBilevel.feasible_eq_paretoSet [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {κ' ι : Type*} (P : LinearBilevel E F κ' ι)
    (hB : ∀ k, P.B k = 0) {ℓ : E → κ → ℝ} (hℓ : Function.Injective ℓ) :
    P.feasible = {p | IsParetoMinOn (multicriteriaObjective ℓ P.lowerObjective)
      {q | q.1 ∈ {x | ∀ k, P.a k ≤ P.A k x} ∧ q.2 ∈ P.lowerFeasible q.1} p} := by
  rw [paretoSet_eq hℓ]
  ext p
  simp [LinearBilevel.feasible, LinearBilevel.upperFeasible, LinearBilevel.lowerSolution, hB]

end ToMulticriteria

/-! ### From multicriteria to bilevel problems -/

section ToBilevel

variable [Fintype κ]

/-- The feasible set of problem (3.12) of [Dempe 2002]: the points of `M` that are at least as good
as `y` in every criterion. -/
def paretoLowerFeasible (C : E → κ → ℝ) (M : Set E) (y : E) : Set E :=
  {x | x ∈ M ∧ C x ≤ C y}

/-- The objective `⟨e, C x⟩` of problem (3.12) of [Dempe 2002], as a function of `(y, x)`. -/
def paretoLowerObjective (C : E → κ → ℝ) (p : E × E) : ℝ :=
  ∑ k, C p.2 k

/-- For `y ∈ M`, every optimal solution of (3.12) is a Pareto optimal point of `C` on `M`. -/
theorem isParetoMinOn_of_mem_solutionMap {C : E → κ → ℝ} {M : Set E} {y x : E}
    (hx : x ∈ solutionMap (paretoLowerObjective C) (paretoLowerFeasible C M) y) :
    IsParetoMinOn C M x := by
  obtain ⟨⟨hxM, hxy⟩, hmin⟩ := hx
  refine ⟨hxM, fun z hzM hzx ↦ ?_⟩
  have := hmin z ⟨hzM, hzx.trans hxy⟩
  exact (eq_of_le_of_sum_le hzx this).ge

/-- **Thm. 3.5 of [Dempe 2002]**: the following are equivalent: `x̄` is a Pareto optimal point of
`C` on `M` (3.11); `x̄` solves (3.12) for `y = x̄`; `(ȳ, x̄)` is feasible for the bilevel problem
(3.13) for some `ȳ`. -/
theorem isParetoMinOn_tfae (C : E → κ → ℝ) (M : Set E) (x : E) :
    List.TFAE [IsParetoMinOn C M x,
      x ∈ solutionMap (paretoLowerObjective C) (paretoLowerFeasible C M) x,
      ∃ y ∈ M, x ∈ solutionMap (paretoLowerObjective C) (paretoLowerFeasible C M) y] := by
  tfae_have 1 → 2 := fun ⟨hxM, hmin⟩ ↦ ⟨⟨hxM, le_rfl⟩, fun z ⟨hzM, hzx⟩ ↦
    (Finset.sum_le_sum fun k _ ↦ hmin z hzM hzx k).trans_eq rfl⟩
  tfae_have 2 → 3 := fun h ↦ ⟨x, h.1.1, h⟩
  tfae_have 3 → 1 := fun ⟨_, _, h⟩ ↦ isParetoMinOn_of_mem_solutionMap h
  tfae_finish

end ToBilevel

/-! ### The example on p. 40

The leader minimizes `2 y₂ - x` over `0 ≤ x ≤ 3`, the follower minimizes `-y₁` subject to
`100 y₁ - y₂ ≤ 1`, `y₂ ≤ x`, `y ≥ 0`. The unique solution of the follower's problem is
`((1 + x)/100, x)`, and the bilevel solution `x = 0`, `y = (1/100, 0)` is not even weakly
efficient for the bicriteria problem with criteria `(2 y₂ - x, -y₁)`. -/

section Example

/-- The follower's constraint set in the example on p. 40. -/
def exampleBilevelParetoK (x : ℝ) : Set (ℝ × ℝ) :=
  {y | 100 * y.1 - y.2 ≤ 1 ∧ y.2 ≤ x ∧ 0 ≤ y.1 ∧ 0 ≤ y.2}

/-- The follower's objective in the example on p. 40. -/
def exampleBilevelParetoφ (p : ℝ × (ℝ × ℝ)) : ℝ := -p.2.1

/-- The leader's objective in the example on p. 40. -/
def exampleBilevelParetoF (p : ℝ × (ℝ × ℝ)) : ℝ := 2 * p.2.2 - p.1

/-- The bicriteria objective `(2 y₂ - x, -y₁)` in the example on p. 40. -/
def exampleBilevelParetoCrit (p : ℝ × (ℝ × ℝ)) : Fin 2 → ℝ :=
  ![exampleBilevelParetoF p, exampleBilevelParetoφ p]

theorem solutionMap_exampleBilevelPareto {x : ℝ} (hx : 0 ≤ x) :
    solutionMap exampleBilevelParetoφ exampleBilevelParetoK x = {((1 + x) / 100, x)} := by
  ext ⟨y₁, y₂⟩
  simp only [solutionMap, exampleBilevelParetoK, exampleBilevelParetoφ, mem_ofPred_eq,
    mem_singleton_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, hmin⟩
    have := hmin ((1 + x) / 100, x) ⟨by linarith, le_rfl, by positivity, hx⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨by linarith, le_rfl, by positivity, hx⟩, fun z ⟨h1, h2, _, _⟩ ↦ by
      simp only [neg_le_neg_iff]; linarith⟩

/-- In the example on p. 40, `x = 0`, `y = (1/100, 0)` solves the bilevel problem. -/
theorem isMinOn_exampleBilevelPareto :
    IsMinOn exampleBilevelParetoF
      {p | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ solutionMap exampleBilevelParetoφ exampleBilevelParetoK p.1}
      (0, (1 / 100, 0)) := by
  rintro ⟨x, y⟩ ⟨⟨hx, -⟩, hy⟩
  dsimp only at hx hy
  rw [solutionMap_exampleBilevelPareto hx, mem_singleton_iff] at hy
  subst hy
  show exampleBilevelParetoF _ ≤ exampleBilevelParetoF _
  simp only [exampleBilevelParetoF]
  linarith

/-- In the example on p. 40, the bilevel solution is not a Pareto optimal point of the bicriteria
problem: it is strictly dominated in both criteria by `x = 5/2`, `y = (3/200, 1/2)`. -/
theorem not_isParetoMinOn_exampleBilevelPareto :
    (∃ q ∈ {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ exampleBilevelParetoK p.1},
      ∀ i, exampleBilevelParetoCrit q i < exampleBilevelParetoCrit (0, (1 / 100, 0)) i) ∧
    ¬ IsParetoMinOn exampleBilevelParetoCrit
      {p | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ exampleBilevelParetoK p.1} (0, (1 / 100, 0)) := by
  have hq : ((5 / 2 : ℝ), ((3 / 200 : ℝ), (1 / 2 : ℝ))) ∈
      {p : ℝ × (ℝ × ℝ) | p.1 ∈ Icc (0 : ℝ) 3 ∧ p.2 ∈ exampleBilevelParetoK p.1} := by
    simp only [exampleBilevelParetoK, mem_ofPred_eq, mem_Icc]
    norm_num
  have hlt : ∀ i, exampleBilevelParetoCrit (5 / 2, (3 / 200, 1 / 2)) i <
      exampleBilevelParetoCrit (0, (1 / 100, 0)) i := by
    intro i
    fin_cases i <;>
      simp [exampleBilevelParetoCrit, exampleBilevelParetoF, exampleBilevelParetoφ] <;> norm_num
  refine ⟨⟨_, hq, hlt⟩, fun ⟨_, hmin⟩ ↦ ?_⟩
  exact (hlt 0).not_ge (hmin _ hq (fun i ↦ (hlt i).le) 0)

end Example

end Bilevel
