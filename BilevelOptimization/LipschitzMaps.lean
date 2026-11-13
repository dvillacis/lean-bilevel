/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Parametric

/-!
# Upper and local Lipschitz continuity of set-valued maps

Def. 4.3 of [Dempe 2002]: a set-valued map `Γ` is *upper Lipschitz continuous* at `x̄` if
`Γ(x) ⊆ Γ(x̄) + L ‖x - x̄‖ 𝔹` for `x` near `x̄`, and *locally Lipschitz continuous* at `x̄` if
`Γ(x) ⊆ Γ(u) + L ‖x - u‖ 𝔹` for `x, u` near `x̄`.

## Main results

* `LocallyLipschitzAt.upperLipschitzAt`: local Lipschitz continuity implies upper Lipschitz
  continuity.
* `UpperLipschitzAt.upperHemicontinuousAt`: an upper Lipschitz continuous map with compact
  `Γ(x̄)` is upper semicontinuous at `x̄` (Def. 4.2).
* `LocallyLipschitzAt.lowerHemicontinuousAt`: a locally Lipschitz continuous map is lower
  semicontinuous.
* `LocallyLipschitzAt.lipschitzLikeAt`: a locally Lipschitz continuous map is Lipschitz-like
  (Aubin) around every point of its graph over `x̄` [Mordukhovich 2018, Def. 3.1(c)].
* `upperLipschitzAt_singleton_iff`, `locallyLipschitzAt_singleton_iff`: for single-valued maps
  the two notions are the local (upper) Lipschitz continuity of functions of Def. 4.4.
* `upperLipschitzAt_example`, `not_locallyLipschitzAt_example`: the two notions differ.

## Remarks on the sources

* The inclusion `Γ(x) ⊆ Γ(u) + L ‖x - u‖ 𝔹` is stated as: every `y ∈ Γ(x)` has some `w ∈ Γ(u)`
  with `dist y w ≤ L * dist x u`. The book's standing assumption that the images are nonempty
  and compact is not part of the definitions; compactness of `Γ(x̄)` is assumed where it is used.
-/

open Filter Topology Set

namespace Bilevel

variable {E F : Type*}

section Metric

variable [PseudoMetricSpace E] [PseudoMetricSpace F] {Γ : E → Set F} {x₀ : E}

/-- Upper Lipschitz continuity of a set-valued map at `x₀` [Dempe 2002, Def. 4.3]:
`Γ(x) ⊆ Γ(x₀) + L ‖x - x₀‖ 𝔹` for `x` near `x₀`. -/
def UpperLipschitzAt (Γ : E → Set F) (x₀ : E) : Prop :=
  ∃ L : ℝ, ∀ᶠ x in 𝓝 x₀, ∀ y ∈ Γ x, ∃ w ∈ Γ x₀, dist y w ≤ L * dist x x₀

/-- Local Lipschitz continuity of a set-valued map at `x₀` [Dempe 2002, Def. 4.3]:
`Γ(x) ⊆ Γ(u) + L ‖x - u‖ 𝔹` for `x, u` near `x₀`. -/
def LocallyLipschitzAt (Γ : E → Set F) (x₀ : E) : Prop :=
  ∃ L : ℝ, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ u ∈ U, ∀ y ∈ Γ x, ∃ w ∈ Γ u, dist y w ≤ L * dist x u

/-- Local Lipschitz continuity implies upper Lipschitz continuity. -/
theorem LocallyLipschitzAt.upperLipschitzAt (h : LocallyLipschitzAt Γ x₀) :
    UpperLipschitzAt Γ x₀ := by
  obtain ⟨L, U, hU, hL⟩ := h
  exact ⟨L, by filter_upwards [hU] with x hx using hL x hx x₀ (mem_of_mem_nhds hU)⟩

/-- An upper Lipschitz continuous map with compact `Γ(x₀)` is upper semicontinuous at `x₀`. -/
theorem UpperLipschitzAt.upperHemicontinuousAt (h : UpperLipschitzAt Γ x₀)
    (hc : IsCompact (Γ x₀)) : UpperHemicontinuousAt Γ x₀ := by
  obtain ⟨L, hL⟩ := h
  intro V hV hsub
  obtain ⟨δ, hδ, hδV⟩ := hc.exists_thickening_subset_open hV hsub
  have ht : Tendsto (fun x ↦ L * dist x x₀) (𝓝 x₀) (𝓝 0) := by
    have hc : Continuous fun x ↦ L * dist x x₀ :=
      continuous_const.mul (continuous_id.dist continuous_const)
    have := hc.tendsto x₀
    rwa [dist_self, mul_zero] at this
  filter_upwards [hL, ht.eventually (gt_mem_nhds hδ)] with x hx hlt y hy
  obtain ⟨w, hw, hd⟩ := hx y hy
  exact hδV (Metric.mem_thickening_iff.2 ⟨w, hw, hd.trans_lt hlt⟩)

/-- A locally Lipschitz continuous map is lower semicontinuous. -/
theorem LocallyLipschitzAt.lowerHemicontinuousAt (h : LocallyLipschitzAt Γ x₀) :
    LowerHemicontinuousAt Γ x₀ := by
  obtain ⟨L, U, hU, hL⟩ := h
  rintro V hV ⟨y₀, hy₀, hy₀V⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV y₀ hy₀V
  have ht : Tendsto (fun x ↦ L * dist x₀ x) (𝓝 x₀) (𝓝 0) := by
    have hc : Continuous fun x ↦ L * dist x₀ x :=
      continuous_const.mul (continuous_const.dist continuous_id)
    have := hc.tendsto x₀
    rwa [dist_self, mul_zero] at this
  filter_upwards [hU, ht.eventually (gt_mem_nhds hε)] with x hx hlt
  obtain ⟨w, hw, hd⟩ := hL x₀ (mem_of_mem_nhds hU) x hx y₀ hy₀
  exact ⟨w, hw, hball (Metric.mem_ball'.2 (hd.trans_lt hlt))⟩

/-- For a single-valued map, upper Lipschitz continuity is the local upper Lipschitz continuity
of functions of [Dempe 2002, Def. 4.4]. -/
theorem upperLipschitzAt_singleton_iff {z : E → F} :
    UpperLipschitzAt (fun x ↦ {z x}) x₀ ↔
      ∃ L : ℝ, ∀ᶠ x in 𝓝 x₀, dist (z x) (z x₀) ≤ L * dist x x₀ := by
  refine exists_congr fun L ↦ eventually_congr (Eventually.of_forall fun x ↦ ?_)
  constructor
  · intro h
    obtain ⟨w, rfl, hd⟩ := h (z x) rfl
    exact hd
  · rintro h y rfl
    exact ⟨z x₀, rfl, h⟩

/-- For a single-valued map, local Lipschitz continuity is the local Lipschitz continuity of
functions of [Dempe 2002, Def. 4.4]. -/
theorem locallyLipschitzAt_singleton_iff {z : E → F} :
    LocallyLipschitzAt (fun x ↦ {z x}) x₀ ↔ ∃ K, ∃ U ∈ 𝓝 x₀, LipschitzOnWith K z U := by
  constructor
  · rintro ⟨L, U, hU, hL⟩
    refine ⟨L.toNNReal, U, hU, LipschitzOnWith.of_dist_le_mul fun x hx u hu ↦ ?_⟩
    obtain ⟨w, rfl, hd⟩ := hL x hx u hu (z x) rfl
    exact hd.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)
  · rintro ⟨K, U, hU, hK⟩
    refine ⟨K, U, hU, ?_⟩
    rintro x hx u hu y rfl
    exact ⟨z u, rfl, hK.dist_le_mul x hx u hu⟩

end Metric

/-- A locally Lipschitz continuous map is Lipschitz-like around every point `(x₀, y₀)`
[Mordukhovich 2018, Def. 3.1(c)]. -/
theorem LocallyLipschitzAt.lipschitzLikeAt [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Γ : E → Set F} {x₀ : E}
    (h : LocallyLipschitzAt Γ x₀) (y₀ : F) : VariationalAnalysis.LipschitzLikeAt Γ x₀ y₀ := by
  obtain ⟨L, U, hU, hL⟩ := h
  refine ⟨L.toNNReal, U, hU, univ, univ_mem, fun x hx u hu y hy ↦ ?_⟩
  obtain ⟨w, hw, hd⟩ := hL x hx u hu y hy.1
  exact ⟨w, hw, hd.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)⟩

/-! ### An upper Lipschitz map that is not locally Lipschitz -/

/-- The map `Γ(0) = {0, 1}`, `Γ(x) = {0}` for `x ≠ 0` is upper Lipschitz continuous at `0`. -/
theorem upperLipschitzAt_example :
    UpperLipschitzAt (fun x : ℝ ↦ {y : ℝ | y = 0 ∨ (x = 0 ∧ y = 1)}) 0 := by
  refine ⟨0, Eventually.of_forall fun x y hy ↦ ⟨y, ?_, by simp⟩⟩
  rcases hy with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨rfl, h⟩

/-- The map of `upperLipschitzAt_example` is not locally Lipschitz continuous at `0`. -/
theorem not_locallyLipschitzAt_example :
    ¬ LocallyLipschitzAt (fun x : ℝ ↦ {y : ℝ | y = 0 ∨ (x = 0 ∧ y = 1)}) 0 := fun h ↦ by
  have hl := h.lowerHemicontinuousAt (Metric.ball (1 : ℝ) 1) Metric.isOpen_ball
    ⟨1, Or.inr ⟨rfl, rfl⟩, Metric.mem_ball_self one_pos⟩
  have hl' : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      ({y : ℝ | y = 0 ∨ (x = 0 ∧ y = 1)} ∩ Metric.ball (1 : ℝ) 1).Nonempty :=
    hl.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, ⟨y, hy, hyb⟩, hx⟩ := (hl'.and self_mem_nhdsWithin).exists
  rcases hy with rfl | ⟨h0, -⟩
  · simp [Real.dist_eq] at hyb
  · exact hx h0

end Bilevel
