/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.PiecewiseSolution
import BilevelOptimization.LipschitzMaps

/-!
# Upper Lipschitz continuity of local solutions and multipliers

Thm. 4.5 of [Dempe 2002] (Robinson 1982), in the (LICQ) case: if the follower's problem satisfies
(LICQ) and (SSOC) at a KKT point `(ȳ, λ⁰)` for the parameter `x̄`, then there are `δ > 0` and
`L < ∞` with
`‖(y, λ) - (ȳ, λ⁰)‖ ≤ L ‖x - x̄‖`
for every local solution `y` with `‖y - ȳ‖ < δ` at a parameter `x` with `‖x - x̄‖ < δ`, and every
multiplier `λ ∈ Λ(x, y)`.

## Main results

* `exists_dist_le_of_isLowerKKT`: the estimate for every KKT point `(y, λ)` near `(ȳ, λ⁰)`, not
  only for local solutions.
* `exists_dist_le_of_lowerSSOC`: Thm. 4.5; local solutions near `ȳ` have multipliers, and the
  estimate holds for all of them.
* `upperLipschitzAt_localSolutions`: the localized local solution map
  `x ↦ Ψ_loc(x) ∩ B(ȳ, δ)` is upper Lipschitz continuous at `x̄` (Def. 4.3).

## Differences from the book

* The book assumes (MFCQ) and (SSOC) (for all multipliers) and bounds the distance to
  `{ȳ} × Λ(x̄, ȳ)`; we assume (LICQ), so that `Λ(x̄, ȳ) = {λ⁰}`, as in our versions of
  Thm. 4.4, 4.10 and 4.11. The book gives no proof.
* The proof uses the finitely many `C¹` selection functions of (4.19) (`lowerSelection`), each
  Lipschitz near `x̄`: every KKT point near `(x̄, ȳ)` is the value of one of them.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {φ : E × F → ℝ} {g : ι → E × F → ℝ}

/-- Under (LICQ) and (SSOC), every KKT point `(y, λ)` of the follower's problem at a parameter
`x` near `x̄`, with `y` near `ȳ`, satisfies `‖(y, λ) - (ȳ, λ⁰)‖ ≤ L ‖x - x̄‖`. -/
theorem exists_dist_le_of_isLowerKKT (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ L, ∃ δ > 0, ∀ (x : E) (y : F) (lam : ι → ℝ), dist x x₀ < δ → dist y y₀ < δ →
      IsLowerKKT φ g x y lam → dist (y, lam) (y₀, lam₀) ≤ L * dist x x₀ := by
  obtain ⟨δ₁, hδ₁, hsel⟩ := exists_pos_lowerSelection_eq hφ hg hkkt hlicq hssoc
  choose K t ht hL using fun I : Finset ι ↦
    (contDiffAt_lowerSelection (φ := φ) (g := g) x₀ y₀ lam₀ I).exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (iInter_mem.2 ht)
  refine ⟨∑ I, (K I : ℝ), min δ₁ ε, lt_min hδ₁ hε, fun x y lam hx hy hkx ↦ ?_⟩
  obtain ⟨I, -, -, he⟩ :=
    hsel x y lam (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _)) hkx
  have hxt : x ∈ t I := mem_iInter.1 (hball (Metric.mem_ball.2 (hx.trans_le (min_le_right _ _)))) I
  have hx₀t : x₀ ∈ t I := mem_iInter.1 (hball (Metric.mem_ball_self hε)) I
  have h := (hL I).dist_le_mul x hxt x₀ hx₀t
  rw [he, lowerSelection_apply_self] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  exact Finset.single_le_sum (f := fun I ↦ (K I : ℝ)) (fun I _ ↦ (K I).coe_nonneg)
    (Finset.mem_univ I)

/-- **Thm. 4.5 of [Dempe 2002]** under (LICQ): if the follower's problem satisfies (LICQ) and
(SSOC) at the KKT point `(ȳ, λ⁰)` for `x̄`, there are `δ > 0` and `L` such that every local solution
`y` with `‖y - ȳ‖ < δ` at a parameter `x` with `‖x - x̄‖ < δ` has a multiplier, and
`‖(y, λ) - (ȳ, λ⁰)‖ ≤ L ‖x - x̄‖` for all `λ ∈ Λ(x, y)`. -/
theorem exists_dist_le_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ L, ∃ δ > 0, ∀ (x : E) (y : F), dist x x₀ < δ → dist y y₀ < δ → y ∈ lowerFeasible g x →
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) y →
        (lowerMultipliers φ g x y).Nonempty ∧
        ∀ lam ∈ lowerMultipliers φ g x y, dist (y, lam) (y₀, lam₀) ≤ L * dist x x₀ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  obtain ⟨L, δ₁, hδ₁, hle⟩ := exists_dist_le_of_isLowerKKT hφ hg hkkt hlicq hssoc
  obtain ⟨δ₂, hδ₂, hpli⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_lowerPLI hg1 (lowerPLI_of_lowerLICQ hkkt.1 hlicq))
  refine ⟨L, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x y hx hy hyG hmin ↦ ⟨?_, fun lam hlam ↦
    hle x y lam (hx.trans_le (min_le_left _ _)) (hy.trans_le (min_le_left _ _)) hlam⟩⟩
  have hp : dist (x, y) (x₀, y₀) < δ₂ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _))
  exact exists_isLowerKKT_of_isLocalMinOn hyG hmin
    ((hφ1.comp (contDiff_prodMk_right x)).differentiable one_ne_zero y)
    (fun i ↦ ((hg1 i).comp (contDiff_prodMk_right x)).contDiffAt) (hpli hp)

/-- Under (LICQ) and (SSOC), the localized local solution map `x ↦ Ψ_loc(x) ∩ B(ȳ, δ)` is upper
Lipschitz continuous at `x̄` (Def. 4.3 of [Dempe 2002]); its value at `x̄` is `{ȳ}` for small
`δ`. -/
theorem upperLipschitzAt_localSolutions (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ δ > 0, UpperLipschitzAt (fun x ↦ {y | dist y y₀ < δ ∧ y ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) y}) x₀ := by
  obtain ⟨L, δ₁, hδ₁, hle⟩ := exists_dist_le_of_lowerSSOC hφ hg hkkt hlicq hssoc
  obtain ⟨ρ, hρ, hstrict⟩ := exists_pos_lt_of_lowerSSOC hφ hg hkkt hssoc
  have hy₀ : IsLocalMinOn (fun z ↦ φ (x₀, z)) (lowerFeasible g x₀) y₀ := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds y₀ hρ), self_mem_nhdsWithin]
      with z hz hzG
    rcases eq_or_ne z y₀ with rfl | hne
    · exact le_rfl
    · exact (hstrict z hzG hne hz).le
  refine ⟨δ₁, hδ₁, L, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ hδ₁] with x hx y hyΓ
  obtain ⟨hy, hyG, hmin⟩ := hyΓ
  refine ⟨y₀, ⟨by simpa using hδ₁, hkkt.1, hy₀⟩, ?_⟩
  obtain ⟨⟨lam, hlam⟩, hbd⟩ := hle x y hx hy hyG hmin
  have h := hbd lam hlam
  rw [Prod.dist_eq] at h
  exact (le_max_left _ _).trans h

end Bilevel
