/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.SolutionJacobian
import Mathlib.Analysis.Convex.Measure

/-!
# The method of active constraints

Sect. 4.4.2 of [Dempe 2002], pp. 93–96, in the (LICQ) case, where `Λ(x̄, ȳ) = {λ⁰}`. The sets
`R(I, λ⁰)` of directions `r` for which `KKT(r, I, λ⁰)` is solvable are convex and cover the
parameter space (4.23): the active set of the solution `y'(x̄; r)` of `QP(λ⁰, r)` is always a
suitable `I`. Their boundaries are Lebesgue null, so for almost every direction `r` every
admissible `I` with `r ∈ R(I, λ⁰)` satisfies `r ∈ int R(I, λ⁰)`, and Thm. 4.13 gives
`∇y^I(x̄) ∈ ∂y(x̄)`. This is the correctness of the *method of active constraints* (p. 95): pick
a direction `r` at random, solve `QP(λ⁰, r)`, take its active set `I` and compute `∇y^I(x̄)`; the
result lies in `∂y(x̄)` with probability one.

## Main results

* `convex_lowerQPRegion`: `R(I, λ⁰)` is convex.
* `lowerQPActive`, `lowerAdmissible_lowerQPActive`, `exists_lowerQPSystem_of_isMinOn`: the KKT
  conditions of `QP(λ⁰, r)` (linear constraints, no constraint qualification needed).
* `mem_lowerQPRegion_lowerQPActive`: (4.23).
* `ae_forall_mem_interior_of_convex`: for finitely many convex sets, almost every point of
  their union is interior to each set containing it.
* `ae_fderiv_mem_clarkeJacobian`, `ae_fderiv_lowerQPActive_mem_clarkeJacobian`: the method of
  active constraints computes an element of `∂y(x̄)` for almost every direction.

## Differences from the book

* Under (LICQ), `S(r) = {λ⁰}`, so step 2 of the method is trivial, and the active set of
  `QP(λ⁰, r)` is admissible, so its "else" branch (passing to a vertex of the multiplier set of
  `QP(λ⁰, r)` and deleting constraints) is not needed.
* "With probability one" for `r` uniform on the unit sphere is formalized as "for almost every
  `r`" with respect to any additive Haar measure on the parameter space; since the sets
  `R(I, λ⁰)` are cones, the two are equivalent.
-/

open Filter Topology Set MeasureTheory
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ}

/-- The sets `R(I, λ⁰)` of [Dempe 2002, p. 94] are convex (indeed convex polyhedral cones). -/
theorem convex_lowerQPRegion (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (I : Finset ι) :
    Convex ℝ (lowerQPRegion φ g x₀ y₀ lam₀ I) := by
  rintro r ⟨d, γ, h1, h2, h3, h4, h5⟩ r' ⟨d', γ', h1', h2', h3', h4', h5'⟩ a b ha hb -
  have hlin : ∀ i, fderiv ℝ (g i) (x₀, y₀) (a • r + b • r', a • d + b • d') =
      a * fderiv ℝ (g i) (x₀, y₀) (r, d) + b * fderiv ℝ (g i) (x₀, y₀) (r', d') := fun i ↦ by
    rw [show ((a • r + b • r', a • d + b • d') : E × F) = a • (r, d) + b • (r', d') by simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨a • d + b • d', a • γ + b • γ', ?_, fun i hi ↦ ?_, fun i hi hia ↦ ?_,
    fun i hi hl ↦ ?_, fun i hi ↦ ?_⟩
  · have h := congrArg₂ (fun u v : StrongDual ℝ F ↦ a • u + b • v) h1 h1'
    simp only [smul_zero, add_zero] at h
    rw [← h]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum, smul_add]
    abel
  · rw [hlin, h2 i hi, h2' i hi]
    ring
  · rw [hlin]
    have := h3 i hi hia
    have := h3' i hi hia
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h4 i hi hl
    have := h4' i hi hl
    positivity
  · simp [h5 i hi, h5' i hi]

variable (g) in
/-- The active set of the linearized constraints of `QP(λ⁰, r)` at `d`: the constraints active at
`(x̄, ȳ)` with `∇gᵢ(x̄, ȳ)(r, d) = 0`. -/
noncomputable def lowerQPActive (x₀ : E) (y₀ : F) (r : E) (d : F) : Finset ι :=
  {i | g i (x₀, y₀) = 0 ∧ fderiv ℝ (g i) (x₀, y₀) (r, d) = 0}

theorem mem_lowerQPActive {x₀ : E} {y₀ : F} {r : E} {d : F} {i : ι} :
    i ∈ lowerQPActive g x₀ y₀ r d ↔ g i (x₀, y₀) = 0 ∧ fderiv ℝ (g i) (x₀, y₀) (r, d) = 0 := by
  simp [lowerQPActive]

/-- The active set of a feasible point of `QP(λ⁰, r)` is admissible. -/
theorem lowerAdmissible_lowerQPActive {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) {r : E} {d : F} (hd : d ∈ lowerQPFeasible g x₀ y₀ lam₀ r) :
    LowerAdmissible g x₀ y₀ lam₀ (lowerQPActive g x₀ y₀ r d) := by
  refine ⟨fun i hi ↦ mem_lowerQPActive.2 ⟨?_, hd.1 i hi⟩, fun i hi ↦ (mem_lowerQPActive.1 hi).1⟩
  have h := hkkt.2.2.1 i
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hi.ne'
  · exact h

/-- The objective of `QP(λ⁰, r)` along a ray. -/
theorem lowerQPObjective_add_smul (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i)) (x₀ : E)
    (y₀ : F) (lam₀ : ι → ℝ) (r : E) (d e : F) (t : ℝ) :
    lowerQPObjective φ g x₀ y₀ lam₀ r (d + t • e) = lowerQPObjective φ g x₀ y₀ lam₀ r d +
      t * (lowerMixedHessian φ g x₀ y₀ lam₀ r + lowerHessian φ g x₀ y₀ lam₀ d) e +
        t ^ 2 / 2 * lowerHessian φ g x₀ y₀ lam₀ e e := by
  unfold lowerQPObjective
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  rw [lowerHessian_symm hφ hg x₀ y₀ lam₀ e d]
  ring

/-- **KKT conditions of `QP(λ⁰, r)`**: a minimizer `d₀` of `QP(λ⁰, r)` (4.20) solves
`KKT(r, I, λ⁰)` with `I` its active set. The constraints are linear, so no constraint qualification
is needed (Farkas' lemma). -/
theorem exists_lowerQPSystem_of_isMinOn [FiniteDimensional ℝ F] (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) {r : E} {d₀ : F}
    (hd₀ : d₀ ∈ lowerQPFeasible g x₀ y₀ lam₀ r)
    (hmin : ∀ d ∈ lowerQPFeasible g x₀ y₀ lam₀ r,
      lowerQPObjective φ g x₀ y₀ lam₀ r d₀ ≤ lowerQPObjective φ g x₀ y₀ lam₀ r d) :
    ∃ γ, LowerQPSystem φ g x₀ y₀ lam₀ (lowerQPActive g x₀ y₀ r d₀) r d₀ γ := by
  classical
  set K := lowerQPActive g x₀ y₀ r d₀ with hK
  have hadm := lowerAdmissible_lowerQPActive hkkt hd₀
  set a : ι → StrongDual ℝ F := fun i ↦ (fderiv ℝ (g i) (x₀, y₀)).comp
    (ContinuousLinearMap.inr ℝ E F) with ha
  have hsec : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = a i := fun i ↦
    fderiv_section ((hg i).differentiable (by norm_num) _)
  have hray : ∀ i (e : F) (t : ℝ), fderiv ℝ (g i) (x₀, y₀) (r, d₀ + t • e) =
      fderiv ℝ (g i) (x₀, y₀) (r, d₀) + t * a i e := fun i e t ↦ by
    rw [show ((r, d₀ + t • e) : E × F) = (r, d₀) + t • (0, e) by simp, map_add, map_smul,
      smul_eq_mul]
    rfl
  set c := lowerMixedHessian φ g x₀ y₀ lam₀ r + lowerHessian φ g x₀ y₀ lam₀ d₀ with hc
  -- first-order condition along admissible directions
  have hfo : ∀ e : F, (∀ i, 0 < lam₀ i → a i e = 0) → (∀ i ∈ K, a i e ≤ 0) → 0 ≤ c e := by
    intro e hJ hKe
    have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), d₀ + t • e ∈ lowerQPFeasible g x₀ y₀ lam₀ r := by
      have hin : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), g i (x₀, y₀) = 0 → i ∉ K →
          fderiv ℝ (g i) (x₀, y₀) (r, d₀) + t * a i e ≤ 0 := fun i ↦ by
        by_cases hi : g i (x₀, y₀) = 0 ∧ i ∉ K
        · have hneg : fderiv ℝ (g i) (x₀, y₀) (r, d₀) < 0 := lt_of_le_of_ne (hd₀.2 i hi.1)
            fun h ↦ hi.2 (mem_lowerQPActive.2 ⟨hi.1, h⟩)
          have hcont : Continuous fun t : ℝ ↦ fderiv ℝ (g i) (x₀, y₀) (r, d₀) + t * a i e := by
            fun_prop
          have := hcont.continuousAt (x := 0) |>.eventually (gt_mem_nhds (by simpa using hneg))
          exact this.mono fun t ht _ _ ↦ ht.le
        · exact Eventually.of_forall fun t h1 h2 ↦ absurd ⟨h1, h2⟩ hi
      refine ((eventually_all.2 hin).filter_mono nhdsWithin_le_nhds).mp
        (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) hall ↦ ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩)
      · rw [hray, hd₀.1 i hi, hJ i hi]
        simp
      · rw [hray]
        by_cases hiK : i ∈ K
        · rw [(mem_lowerQPActive.1 hiK).2, zero_add]
          exact mul_nonpos_of_nonneg_of_nonpos ht.le (hKe i hiK)
        · exact hall i hi hiK
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ c e + t / 2 * lowerHessian φ g x₀ y₀ lam₀ e e := by
      refine hfeas.mp (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) hf ↦ ?_)
      have h := hmin _ hf
      rw [lowerQPObjective_add_smul hφ hg] at h
      have h' : 0 ≤ t * (c e + t / 2 * lowerHessian φ g x₀ y₀ lam₀ e e) := by
        rw [hc]
        nlinarith
      exact (mul_nonneg_iff_of_pos_left ht).1 h'
    have hlim : Tendsto (fun t : ℝ ↦ c e + t / 2 * lowerHessian φ g x₀ y₀ lam₀ e e) (𝓝[>] 0)
        (𝓝 (c e)) := by
      have : Continuous fun t : ℝ ↦ c e + t / 2 * lowerHessian φ g x₀ y₀ lam₀ e e := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim hle
  -- Farkas
  set A : ι ⊕ ι → StrongDual ℝ F :=
    Sum.elim (fun i ↦ if i ∈ K then -a i else 0) (fun i ↦ if 0 < lam₀ i then a i else 0) with hA
  obtain ⟨μ, hμ, hcμ⟩ := VariationalAnalysis.exists_nonneg_eq_sum_of_forall_nonneg A c
    fun v hv ↦ by
      refine hfo v (fun i hi ↦ ?_) fun i hi ↦ ?_
      · have h1 := hv (Sum.inr i)
        have h2 := hv (Sum.inl i)
        have hK' := hadm.1 i hi
        simp only [hA, Sum.elim_inr, Sum.elim_inl] at h1 h2
        rw [if_pos hi] at h1
        rw [if_pos hK', neg_apply] at h2
        linarith
      · have h2 := hv (Sum.inl i)
        simp only [hA, Sum.elim_inl] at h2
        rw [if_pos hi, neg_apply] at h2
        linarith
  refine ⟨fun i ↦ (if i ∈ K then μ (Sum.inl i) else 0) - (if 0 < lam₀ i then μ (Sum.inr i) else 0),
    ?_, fun i hi ↦ (mem_lowerQPActive.1 hi).2, fun i _ hia ↦ hd₀.2 i hia, fun i hi hl ↦ ?_,
    fun i hi ↦ ?_⟩
  · simp only [hsec]
    rw [← hc, hcμ, Fintype.sum_sum_type, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [hA, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp [sub_smul]
  · simp [hi, hl, hμ]
  · have hl : ¬ 0 < lam₀ i := fun h ↦ hi (hadm.1 i h)
    simp [hi, hl]

/-- For finitely (or countably) many convex sets in a finite-dimensional space, almost every point
lies in the interior of each of the sets containing it: their boundaries are null sets. -/
theorem ae_forall_mem_interior_of_convex {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G] (μ : Measure G)
    [μ.IsAddHaarMeasure] {κ : Type*} [Countable κ] {S : κ → Set G} (hS : ∀ k, Convex ℝ (S k)) :
    ∀ᵐ r ∂μ, ∀ k, r ∈ S k → r ∈ interior (S k) := by
  refine ae_all_iff.2 fun k ↦ ?_
  rw [ae_iff]
  refine measure_mono_null (fun r hr ↦ ?_) ((hS k).addHaar_frontier μ)
  have hr' : r ∈ S k ∧ r ∉ interior (S k) := Classical.not_imp.1 hr
  exact ⟨subset_closure hr'.1, hr'.2⟩

section Method

variable [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {s : E → F} {U : Set E}

/-- **(4.23) of [Dempe 2002]** under (LICQ): for every direction `r`, the active set `I` of the
solution `y'(x̄; r)` of `QP(λ⁰, r)` is admissible and `r ∈ R(I, λ⁰)`. -/
theorem mem_lowerQPRegion_lowerQPActive (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀)
    (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {s' : E → F} (hs' : HasDirDerivAt s s' x₀) (r : E) :
    LowerAdmissible g x₀ y₀ lam₀ (lowerQPActive g x₀ y₀ r (s' r)) ∧
      r ∈ lowerQPRegion φ g x₀ y₀ lam₀ (lowerQPActive g x₀ y₀ r (s' r)) := by
  obtain ⟨s'', hs'', hqp⟩ := hasDirDerivAt_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  rw [tendsto_nhds_unique (hs' r) (hs'' r)]
  obtain ⟨hfeas, hmin⟩ := hqp r
  refine ⟨lowerAdmissible_lowerQPActive hkkt hfeas, s'' r, ?_⟩
  exact exists_lowerQPSystem_of_isMinOn hφ hg hkkt hfeas fun d hd ↦ by
    by_cases h : d = s'' r
    · rw [h]
    · exact (hmin d hd h).le

/-- **(4.23) of [Dempe 2002]** under (LICQ): the sets `R(I, λ⁰)`, `I` admissible, cover the
parameter space. -/
theorem iUnion_lowerQPRegion (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀)
    (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    ⋃ I : {I // LowerAdmissible g x₀ y₀ lam₀ I}, lowerQPRegion φ g x₀ y₀ lam₀ I = univ := by
  obtain ⟨s', hs', -⟩ := hasDirDerivAt_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  refine eq_univ_of_forall fun r ↦ mem_iUnion.2 ?_
  obtain ⟨hI, hr⟩ := mem_lowerQPRegion_lowerQPActive hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin hs' r
  exact ⟨⟨_, hI⟩, hr⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The probabilistic statement on p. 94 of [Dempe 2002] together with Thm. 4.13, under (LICQ):
for almost every direction `r`, every admissible `I` with `r ∈ R(I, λ⁰)` satisfies
`r ∈ int R(I, λ⁰)` and `∇y^I(x̄) ∈ ∂y(x̄)`. -/
theorem ae_fderiv_mem_clarkeJacobian (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀)
    (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    ∀ᵐ r ∂μ, ∀ I, LowerAdmissible g x₀ y₀ lam₀ I → r ∈ lowerQPRegion φ g x₀ y₀ lam₀ I →
      r ∈ interior (lowerQPRegion φ g x₀ y₀ lam₀ I) ∧
        fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ ∈ clarkeJacobian s x₀ := by
  filter_upwards [ae_forall_mem_interior_of_convex μ
    (S := fun I : Finset ι ↦ lowerQPRegion φ g x₀ y₀ lam₀ I)
    fun I ↦ convex_lowerQPRegion x₀ y₀ lam₀ I] with r hr I hI hrI
  have hint := hr I hrI
  obtain ⟨-, -, -, h⟩ := exists_stronglyActive_fderiv_eq_of_mem_interior_lowerQPRegion hφ hg hkkt
    hlicq hssoc hU hs₀ hsc hsmin hI hint
  exact ⟨hint, h⟩

/-- **The method of active constraints** of [Dempe 2002, p. 95] under (LICQ): for almost every
direction `r`, the Jacobian `∇y^I(x̄)` of the selection function given by the active set `I` of the
solution `y'(x̄; r)` of `QP(λ⁰, r)` is an element of the generalized Jacobian `∂y(x̄)`. -/
theorem ae_fderiv_lowerQPActive_mem_clarkeJacobian (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {s' : E → F} (hs' : HasDirDerivAt s s' x₀) :
    ∀ᵐ r ∂μ, fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀
      (lowerQPActive g x₀ y₀ r (s' r))) x₀ ∈ clarkeJacobian s x₀ := by
  filter_upwards [ae_fderiv_mem_clarkeJacobian μ hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin]
    with r hr
  obtain ⟨hI, hrI⟩ := mem_lowerQPRegion_lowerQPActive hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin hs' r
  exact (hr _ hI hrI).2

end Method

end Bilevel
