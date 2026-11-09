/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Parametric

/-!
# Local solutions of the KKT reformulation

The converse of Thm. 5.15 of [Dempe 2002] (`isLocalMinOn_kktFeasible_of_isLocalMinOn`), following
[Dempe–Dutta 2012, Thm. 3.1]: if `((x̄, ȳ), λ)` is a local solution of the KKT reformulation (5.26)
for *every* multiplier `λ ∈ Λ(x̄, ȳ)`, then `(x̄, ȳ)` is a local solution of (5.5). One multiplier
is not enough, so local solutions of (5.26) need not be local solutions of the bilevel problem
[Schmidt 2024, p. 188].

## Main results

* `isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible`: for `C¹` data with (MFCQ)
  at `(x̄, ȳ)`, local optimality in (5.26) for all `λ ∈ Λ(x̄, ȳ)` gives local optimality in (5.5).
  No convexity is needed.
* `isLocalMinOn_bilevelFeasible_iff_forall_isLocalMinOn_kktFeasible`: [Dempe–Dutta 2012,
  Thm. 3.1]: for a convex follower's problem with `C¹` data and Slater's condition at `x̄`,
  `(x̄, ȳ)` is a local solution of (5.5) iff `((x̄, ȳ), λ)` is a local solution of (5.26) for every
  `λ ∈ Λ(x̄, ȳ)`.
* `isLocalMinOn_kktFeasible_not_isLocalMinOn_bilevelFeasible_example`: a linear bilevel problem
  where `((0, 1), (1, 0))` is a local solution of (5.26) but `(0, 1)` is not a local solution of
  (5.5).

## Remarks on the sources

* The proof replaces the sequence argument of [Dempe–Dutta 2012] by the tube lemma for the
  compact set `Λ(x̄, ȳ)` (`IsCompact.mem_prod_nhdsSet_of_forall`) and the upper semicontinuity of
  `Λ` (Thm. 4.2 of [Dempe 2002], `upperHemicontinuousAt_lowerMultipliers`).
* [Dempe–Dutta 2012] assume convexity and Slater's condition for all `x ∈ Ω` (the hypotheses of the
  global result). For the converse, convexity is not needed: the KKT conditions are only used as
  necessary conditions near `(x̄, ȳ)`, and dual (MFCQ) persists from `(x̄, ȳ)` (`eventually_lowerPLI`).
  For a convex follower's problem, Slater's condition at `x̄` gives (MFCQ) at `(x̄, ȳ)`
  (`lowerPLI_of_slaterAt`), so the equivalence needs Slater's condition only at `x̄`.
* The example is taken from [Dempe et al. 2015], as presented in the Notability note *Solving
  Methods for Bilevel Optimization Problems* (p. 27, printed p. 23). [Schmidt 2024,
  Example 4.6] gives a nonlinear example of the same phenomenon.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι] {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {Ω : Set E} {x₀ : E}
  {y₀ : F}

/-- The converse of Thm. 5.15 of [Dempe 2002] [Dempe–Dutta 2012, Thm. 3.1]: for `C¹` data with
(MFCQ) at `(x̄, ȳ)` (in its dual form), if `((x̄, ȳ), λ)` is a local solution of the KKT
reformulation (5.26) for every `λ ∈ Λ(x̄, ȳ)`, then `(x̄, ȳ)` is a local solution of (5.5). -/
theorem isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible [FiniteDimensional ℝ F]
    (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀)
    (hloc : ∀ lam ∈ lowerMultipliers φ g x₀ y₀,
      IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam)) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) := by
  -- tube lemma: one neighborhood of `(x̄, ȳ)` works for a neighborhood of the compact `Λ(x̄, ȳ)`
  have hS : {q : (E × F) × (ι → ℝ) | q ∈ kktFeasible φ g Ω → f (x₀, y₀) ≤ f q.1} ∈
      𝓝 (x₀, y₀) ×ˢ 𝓝ˢ (lowerMultipliers φ g x₀ y₀) :=
    (isCompact_lowerMultipliers hreg).mem_prod_nhdsSet_of_forall fun lam hlam ↦ by
      rw [← nhds_prod_eq]
      exact eventually_nhdsWithin_iff.1 (hloc lam hlam)
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.1 hS
  obtain ⟨V, hV, hΛV, hVt⟩ := mem_nhdsSet_iff_exists.1 ht₂
  have husc := upperHemicontinuousAt_lowerMultipliers hφ hg hreg V hV hΛV
  refine eventually_nhdsWithin_iff.2 ?_
  filter_upwards [ht₁, husc, eventually_lowerPLI hg hreg] with p hp₁ hpV hpreg hpB
  obtain ⟨lam, hlam⟩ := exists_isLowerKKT_of_mem_solutionMap hpB.2
    ((hφ.comp (contDiff_prodMk_right p.1)).differentiable one_ne_zero p.2)
    (fun i ↦ ((hg i).comp (contDiff_prodMk_right p.1)).contDiffAt) hpreg
  exact hsub (mk_mem_prod hp₁ (hVt (hpV hlam))) ⟨hpB.1, hlam⟩

/-- [Dempe–Dutta 2012, Thm. 3.1]: for a convex follower's problem with `C¹` data and Slater's
condition at `x̄`, a bilevel-feasible point `(x̄, ȳ)` is a local solution of (5.5) iff
`((x̄, ȳ), λ)` is a local solution of the KKT reformulation (5.26) for every `λ ∈ Λ(x̄, ȳ)`. -/
theorem isLocalMinOn_bilevelFeasible_iff_forall_isLocalMinOn_kktFeasible [FiniteDimensional ℝ F]
    (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hmem : (x₀, y₀) ∈ bilevelFeasible φ (lowerFeasible g) Ω)
    (hconv : ∀ x ∈ Ω, IsConvexLower φ g x) (hS : SlaterAt g x₀) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) ↔
      ∀ lam ∈ lowerMultipliers φ g x₀ y₀,
        IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam) := by
  have hdiff : ∀ x, IsDifferentiableLower φ g x := fun x z ↦
    ⟨(hφ.comp (contDiff_prodMk_right x)).differentiable one_ne_zero z,
      fun i ↦ ((hg i).comp (contDiff_prodMk_right x)).differentiable one_ne_zero z⟩
  refine ⟨fun h lam _ ↦ isLocalMinOn_kktFeasible_of_isLocalMinOn h hconv
    fun x _ ↦ hdiff x, fun h ↦ ?_⟩
  exact isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible hφ hg
    (lowerPLI_of_slaterAt (hconv x₀ hmem.1).2 (hdiff x₀ y₀).2 hmem.2.1 hS) h

/-! ### Example: one multiplier is not enough -/

section Example

/-- The leader's objective `(x - 1)² + (y - 1)²` of the example. -/
private def exf : ℝ × ℝ → ℝ := fun p ↦ (p.1 - 1) ^ 2 + (p.2 - 1) ^ 2

/-- The follower's objective `-y`. -/
private def exφ : ℝ × ℝ → ℝ := fun p ↦ -p.2

/-- The follower's constraints `y ≤ x + 1`, `y ≤ -x + 1`. -/
private def exg : Fin 2 → ℝ × ℝ → ℝ := ![fun p ↦ p.2 - p.1 - 1, fun p ↦ p.2 + p.1 - 1]

private theorem exg_zero (p : ℝ × ℝ) : exg 0 p = p.2 - p.1 - 1 := rfl

private theorem exg_one (p : ℝ × ℝ) : exg 1 p = p.2 + p.1 - 1 := rfl

/-- Local solutions of the KKT reformulation (5.26) need not be local solutions of (5.5)
[Dempe et al. 2015; Dempe–Dutta 2012]: for
`min {(x - 1)² + (y - 1)² | x ∈ [-1, 1], y ∈ Argmin_y {-y | y ≤ x + 1, y ≤ -x + 1}}`
the follower's solution is `y = 1 - |x|`, and `Λ(0, 1)` is the segment between `(1, 0)` and
`(0, 1)`. The point `((0, 1), (1, 0))` is a local solution of (5.26) (near it `λ₁ > 0`, which
forces `y = x + 1` and hence `x ≤ 0`), but `(0, 1)` is not a local solution of (5.5): the points
`(t, 1 - t)`, `t ∈ (0, 1)`, are bilevel-feasible with objective `1 - 2t + 2t² < 1`. By
`isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible`, `((0, 1), (0, 1))` is not a
local solution of (5.26). -/
theorem isLocalMinOn_kktFeasible_not_isLocalMinOn_bilevelFeasible_example :
    ((0, 1), ![1, 0]) ∈ kktFeasible exφ exg (Icc (-1) 1) ∧
      IsLocalMinOn (fun q : (ℝ × ℝ) × (Fin 2 → ℝ) ↦ exf q.1) (kktFeasible exφ exg (Icc (-1) 1))
        ((0, 1), ![1, 0]) ∧
      (0, 1) ∈ bilevelFeasible exφ (lowerFeasible exg) (Icc (-1) 1) ∧
      ¬ IsLocalMinOn exf (bilevelFeasible exφ (lowerFeasible exg) (Icc (-1) 1)) (0, 1) := by
  -- `(t, 1 - t)` is bilevel-feasible for `t ∈ [0, 1]`
  have hB : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((t, 1 - t) : ℝ × ℝ) ∈ bilevelFeasible exφ (lowerFeasible exg) (Icc (-1) 1) := by
    intro t ht0 ht1
    refine ⟨⟨by show (-1 : ℝ) ≤ t; linarith, ht1⟩, ⟨fun i ↦ ?_, fun z hz ↦ ?_⟩⟩
    · fin_cases i
      · show exg 0 (t, 1 - t) ≤ 0
        rw [exg_zero]
        dsimp only
        linarith
      · show exg 1 (t, 1 - t) ≤ 0
        rw [exg_one]
        dsimp only
        linarith
    · have h1 := hz 1
      rw [exg_one] at h1
      dsimp only at h1
      show -(1 - t) ≤ -z
      linarith
  refine ⟨⟨⟨by norm_num, by norm_num⟩, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, ?_⟩, ?_,
    by simpa using hB 0 le_rfl zero_le_one, ?_⟩
  · fin_cases i
    · show exg 0 (0, 1) ≤ 0
      rw [exg_zero]
      norm_num
    · show exg 1 (0, 1) ≤ 0
      rw [exg_one]
      norm_num
  · fin_cases i <;> simp
  · fin_cases i
    · show (![1, 0] : Fin 2 → ℝ) 0 * exg 0 (0, 1) = 0
      rw [exg_zero]
      norm_num
    · show (![1, 0] : Fin 2 → ℝ) 1 * exg 1 (0, 1) = 0
      simp
  · -- stationarity: `-1 + 1 · 1 + 0 · 1 = 0`
    refine ContinuousLinearMap.ext_ring ?_
    simp only [Fin.sum_univ_two, add_apply, smul_apply, smul_eq_mul,
      zero_apply]
    rw [show (fun z ↦ exφ (((0 : ℝ), (1 : ℝ)).1, z)) = fun z : ℝ ↦ -z from rfl,
      show (fun z ↦ exg 0 (((0 : ℝ), (1 : ℝ)).1, z)) = fun z : ℝ ↦ z - 0 - 1 from rfl,
      show (fun z ↦ exg 1 (((0 : ℝ), (1 : ℝ)).1, z)) = fun z : ℝ ↦ z + 0 - 1 from rfl,
      fderiv_apply_one_of_hasDerivAt (hasDerivAt_neg' 1),
      fderiv_apply_one_of_hasDerivAt (((hasDerivAt_id' 1).sub_const 0).sub_const 1),
      fderiv_apply_one_of_hasDerivAt (((hasDerivAt_id' 1).add_const 0).sub_const 1)]
    simp
  · -- near `λ = (1, 0)`, `λ₁ > 0` forces `y = x + 1`, hence `x ≤ 0`
    have hpos : ∀ᶠ q : (ℝ × ℝ) × (Fin 2 → ℝ) in 𝓝 ((0, 1), ![1, 0]), 0 < q.2 0 :=
      continuousAt_const.eventually_lt
        (show Continuous fun q : (ℝ × ℝ) × (Fin 2 → ℝ) ↦ q.2 0 by fun_prop).continuousAt
        (by simp)
    refine eventually_nhdsWithin_iff.2 (hpos.mono fun q hq hqK ↦ ?_)
    obtain ⟨-, hfeas, -, hcs, -⟩ := hqK
    have h0 : exg 0 q.1 = 0 := (mul_eq_zero.1 (hcs 0)).resolve_left hq.ne'
    have h1 := hfeas 1
    rw [exg_zero] at h0
    rw [exg_one] at h1
    show exf (0, 1) ≤ exf q.1
    simp only [exf]
    nlinarith
  · intro hmin
    have htend : Tendsto (fun t : ℝ ↦ ((t, 1 - t) : ℝ × ℝ)) (𝓝[>] 0)
        (𝓝[bilevelFeasible exφ (lowerFeasible exg) (Icc (-1) 1)] (0, 1)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun t ht ↦
        hB t ht.1.le ht.2.le⟩
      have hc : Continuous fun t : ℝ ↦ ((t, 1 - t) : ℝ × ℝ) := by fun_prop
      have := hc.tendsto 0
      simp only [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := ((htend.eventually hmin).and (Ioo_mem_nhdsGT zero_lt_one)).exists
    simp only [exf] at ht
    nlinarith [ht0.1, ht0.2]

end Example

end Bilevel
