/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.LinearBilevel
import BilevelOptimization.LipschitzProgram

/-!
# Failure of constraint qualifications for the KKT reformulation

Sect. 5.4 of [Dempe 2002]: if the complementarity conditions

`gᵢ(z) ≤ 0`, `vᵢ(z) ≥ 0`, `vᵢ(z) gᵢ(z) = 0` (`i ∈ ι`)

are part of the constraints of an optimization problem, then the Mangasarian–Fromovitz constraint
qualification is violated at every feasible point (Thm. 5.11, from [Scheel–Scholtes 2000]; see
also [Ye–Zhu 1995] and [Schmidt 2024, p. 127]). For the KKT reformulation (5.26) of a bilevel
problem, `z = (x, y, λ)`, `gᵢ` are the follower's constraints and `vᵢ(z) = λᵢ`.

## Main definitions

* `complementarityInequalities G g v`, `complementarityEqualities H g v`: the constraints
  `G ≤ 0`, `g ≤ 0`, `-v ≤ 0` and `H = 0`, `vᵢ gᵢ = 0` of a program (5.37) containing the
  complementarity conditions, with arbitrary further constraints `G`, `H`.
* `aggregatedComplementarityEqualities H g v`: the same with the single equation
  `∑ vᵢ gᵢ = 0`, as in the book.

## Main results

* `exists_abnormalMultiplier_complementarity`, `exists_abnormalMultiplier_aggregatedComplementarity`:
  at every feasible point `z` the multiplier `(v(z), -g(z), -1)` is abnormal.
* `not_nonsmoothMFCQ_complementarity`, `not_nonsmoothMFCQ_aggregatedComplementarity`: Thm. 5.11
  of [Dempe 2002]: neither (MFCQ) nor (LICQ) holds.
* `not_nonsmoothMFCQ_kkt`, `not_nonsmoothMFCQ_kkt_aggregated`: the same for the KKT reformulation
  (5.26) of a bilevel problem.
* `LinearBilevel.not_nonsmoothMFCQ_kkt`: the same for LP–LP bilevel problems
  [Schmidt 2024, p. 127].

## Remarks on the sources

* The constraint qualifications are `NonsmoothMFCQ` and `NonsmoothLICQ` of `LipschitzProgram.lean`.
  For strictly differentiable data Clarke's generalized gradients are the singletons `{∇Gᵢ(z)}`,
  `{∇Hₖ(z)}`, so these are the classical (MFCQ) and (LICQ).
* The further constraints `G`, `H` are arbitrary (with nonempty generalized gradients at `z`,
  e.g. Lipschitz around `z`). In (5.26) they contain the leader's constraints and the components
  of the stationarity condition `∇_y φ + ∑ λᵢ ∇_y gᵢ = 0`, which plays no role.
* The proof in [Dempe 2002, p. 184] argues with the primal form of (MFCQ). Here the dual form
  (Thm. 5.18) is used: by the product rule
  `∇(vᵢ gᵢ)(z) = vᵢ(z) ∇gᵢ(z) + gᵢ(z) ∇vᵢ(z)`, so the multipliers `vᵢ(z) ≥ 0` of `gᵢ ≤ 0`,
  `-gᵢ(z) ≥ 0` of `-vᵢ ≤ 0` and `-1` of `vᵢ gᵢ = 0` are abnormal, and they satisfy complementary
  slackness because `vᵢ(z) gᵢ(z) = 0`. In (5.26) this is the multiplier `(λ, -g(x, y), -1)`.
* With one equation per index the index set must be nonempty. With the single equation
  `∑ vᵢ gᵢ = 0` the statement also holds for `ι = ∅`, where the equation is `0 = 0`.
-/

open Filter Topology Set
open VariationalAnalysis (clarkeSubdiff)

namespace Bilevel

/-! ### Complementarity constraints -/

section Complementarity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {I K ι : Type*}

section Definitions

variable (G : I → X → ℝ) (H : K → X → ℝ) (g v : ι → X → ℝ)

/-- The inequality constraints `Gⱼ ≤ 0`, `gᵢ ≤ 0`, `-vᵢ ≤ 0` of a program containing the
complementarity conditions `g ≤ 0`, `v ≥ 0`, `vᵢ gᵢ = 0`. -/
def complementarityInequalities : I ⊕ (ι ⊕ ι) → X → ℝ :=
  Sum.elim G (Sum.elim g fun i z ↦ -v i z)

/-- The equality constraints `Hₖ = 0`, `vᵢ gᵢ = 0` of a program containing the complementarity
conditions `g ≤ 0`, `v ≥ 0`, `vᵢ gᵢ = 0`. -/
def complementarityEqualities : K ⊕ ι → X → ℝ :=
  Sum.elim H fun i z ↦ v i z * g i z

/-- The equality constraints `Hₖ = 0`, `∑ vᵢ gᵢ = 0`: complementarity as a single equation, as in
the proof of Thm. 5.11 of [Dempe 2002]. -/
def aggregatedComplementarityEqualities [Fintype ι] : K ⊕ Unit → X → ℝ :=
  Sum.elim H fun _ z ↦ ∑ i, v i z * g i z

end Definitions

variable [Fintype I] [Fintype K] [Fintype ι] [FiniteDimensional ℝ X]
  {G : I → X → ℝ} {H : K → X → ℝ} {g v : ι → X → ℝ} {g' v' : ι → StrongDual ℝ X} {z : X}

omit [Fintype I] [Fintype K] [Fintype ι] in
theorem mem_clarkeSubdiff_of_hasStrictFDerivAt {ψ : X → ℝ} {ψ' : StrongDual ℝ X}
    (hψ : HasStrictFDerivAt ψ ψ' z) : ψ' ∈ clarkeSubdiff ψ z := by
  rw [VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt hψ]
  exact mem_singleton _

/-- At every point `z` with `g(z) ≤ 0`, `v(z) ≥ 0`, `vᵢ(z) gᵢ(z) = 0`, the multiplier
`(v(z), -g(z), -1)` of the constraints `g ≤ 0`, `-v ≤ 0`, `vᵢ gᵢ = 0` is abnormal, whatever the
further constraints `G ≤ 0`, `H = 0` are. -/
theorem exists_abnormalMultiplier_complementarity [Nonempty ι]
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z)
    (hg0 : ∀ i, g i z ≤ 0) (hv0 : ∀ i, 0 ≤ v i z) (hc : ∀ i, v i z * g i z = 0)
    (hG : ∀ j, (clarkeSubdiff (G j) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    ∃ m ∈ abnormalMultipliers (complementarityInequalities G g v)
      (complementarityEqualities H g v) z, m ≠ 0 := by
  choose η hη using hG
  choose ξ hξ using hH
  refine ⟨(Sum.elim 0 (Sum.elim (fun i ↦ v i z) fun i ↦ -g i z), Sum.elim 0 fun _ ↦ -1),
    ⟨?_, ?_, Sum.elim η (Sum.elim g' fun i ↦ -v' i), ?_,
      Sum.elim ξ (fun i ↦ v i z • g' i + g i z • v' i), ?_, ?_⟩, ?_⟩
  · rintro (j | i | i)
    exacts [le_rfl, hv0 i, neg_nonneg.2 (hg0 i)]
  · rintro (j | i | i)
    · exact zero_mul _
    · exact hc i
    · show -g i z * -v i z = 0
      rw [neg_mul_neg, mul_comm]
      exact hc i
  · rintro (j | i | i)
    · exact hη j
    · show g' i ∈ clarkeSubdiff (g i) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i)
    · show -v' i ∈ clarkeSubdiff (fun z ↦ -v i z) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt (hv i).neg
  · rintro (k | i)
    · exact hξ k
    · show v i z • g' i + g i z • v' i ∈ clarkeSubdiff (fun z ↦ v i z * g i z) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt ((hv i).mul (hg i))
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ by module
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    intro h0
    have := congrArg (fun m : (I ⊕ (ι ⊕ ι) → ℝ) × (K ⊕ ι → ℝ) ↦ m.2 (Sum.inr i₀)) h0
    simp at this

/-- Thm. 5.11 of [Dempe 2002]: if the complementarity conditions `g ≤ 0`, `v ≥ 0`, `vᵢ gᵢ = 0`
are part of the constraints of an optimization problem, then neither (MFCQ) nor (LICQ) holds at
any feasible point. -/
theorem not_nonsmoothMFCQ_complementarity [Nonempty ι]
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z)
    (hg0 : ∀ i, g i z ≤ 0) (hv0 : ∀ i, 0 ≤ v i z) (hc : ∀ i, v i z * g i z = 0)
    (hG : ∀ j, (clarkeSubdiff (G j) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    ¬ NonsmoothMFCQ (complementarityInequalities G g v) (complementarityEqualities H g v) z ∧
      ¬ NonsmoothLICQ (complementarityInequalities G g v) (complementarityEqualities H g v) z :=
  not_nonsmoothMFCQ_of_abnormalMultiplier
    (exists_abnormalMultiplier_complementarity hg hv hg0 hv0 hc hG hH)

/-- The abnormal multiplier `(v(z), -g(z), -1)` for complementarity written as the single
equation `∑ vᵢ gᵢ = 0`. -/
theorem exists_abnormalMultiplier_aggregatedComplementarity
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z)
    (hg0 : ∀ i, g i z ≤ 0) (hv0 : ∀ i, 0 ≤ v i z) (hc : ∑ i, v i z * g i z = 0)
    (hG : ∀ j, (clarkeSubdiff (G j) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    ∃ m ∈ abnormalMultipliers (complementarityInequalities G g v)
      (aggregatedComplementarityEqualities H g v) z, m ≠ 0 := by
  have hc' : ∀ i, v i z * g i z = 0 := fun i ↦
    (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hv0 i) (hg0 i)).1 hc i (Finset.mem_univ i)
  choose η hη using hG
  choose ξ hξ using hH
  refine ⟨(Sum.elim 0 (Sum.elim (fun i ↦ v i z) fun i ↦ -g i z), Sum.elim 0 fun _ ↦ -1),
    ⟨?_, ?_, Sum.elim η (Sum.elim g' fun i ↦ -v' i), ?_,
      Sum.elim ξ (fun _ ↦ ∑ i, (v i z • g' i + g i z • v' i)), ?_, ?_⟩, ?_⟩
  · rintro (j | i | i)
    exacts [le_rfl, hv0 i, neg_nonneg.2 (hg0 i)]
  · rintro (j | i | i)
    · exact zero_mul _
    · exact hc' i
    · show -g i z * -v i z = 0
      rw [neg_mul_neg, mul_comm]
      exact hc' i
  · rintro (j | i | i)
    · exact hη j
    · show g' i ∈ clarkeSubdiff (g i) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i)
    · show -v' i ∈ clarkeSubdiff (fun z ↦ -v i z) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt (hv i).neg
  · rintro (k | u)
    · exact hξ k
    · show ∑ i, (v i z • g' i + g i z • v' i) ∈
        clarkeSubdiff (fun z ↦ ∑ i, v i z * g i z) z
      exact mem_clarkeSubdiff_of_hasStrictFDerivAt
        (HasStrictFDerivAt.fun_sum fun i _ ↦ (hv i).mul (hg i))
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton, Finset.smul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ ↦ by module
  · intro h0
    have := congrArg (fun m : (I ⊕ (ι ⊕ ι) → ℝ) × (K ⊕ Unit → ℝ) ↦ m.2 (Sum.inr ())) h0
    simp at this

/-- Thm. 5.11 of [Dempe 2002] with complementarity written as the single equation
`∑ vᵢ gᵢ = 0`. -/
theorem not_nonsmoothMFCQ_aggregatedComplementarity
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z)
    (hg0 : ∀ i, g i z ≤ 0) (hv0 : ∀ i, 0 ≤ v i z) (hc : ∑ i, v i z * g i z = 0)
    (hG : ∀ j, (clarkeSubdiff (G j) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    ¬ NonsmoothMFCQ (complementarityInequalities G g v)
        (aggregatedComplementarityEqualities H g v) z ∧
      ¬ NonsmoothLICQ (complementarityInequalities G g v)
        (aggregatedComplementarityEqualities H g v) z :=
  not_nonsmoothMFCQ_of_abnormalMultiplier
    (exists_abnormalMultiplier_aggregatedComplementarity hg hv hg0 hv0 hc hG hH)

end Complementarity

/-! ### The KKT reformulation -/

section KKT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {I K ι : Type*} [Fintype I] [Fintype K] [Fintype ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ}
  {G : I → (E × F) × (ι → ℝ) → ℝ} {H : K → (E × F) × (ι → ℝ) → ℝ} {q : (E × F) × (ι → ℝ)}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasStrictFDerivAt_comp_fst_kkt (hg : ∀ i, ContDiffAt ℝ 1 (g i) q.1) (i : ι) :
    HasStrictFDerivAt (fun r : (E × F) × (ι → ℝ) ↦ g i r.1)
      ((fderiv ℝ (g i) q.1).comp (ContinuousLinearMap.fst ℝ (E × F) (ι → ℝ))) q :=
  ((hg i).hasStrictFDerivAt one_ne_zero).comp q hasStrictFDerivAt_fst

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasStrictFDerivAt_multiplier_kkt (i : ι) :
    HasStrictFDerivAt (fun r : (E × F) × (ι → ℝ) ↦ r.2 i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (ContinuousLinearMap.snd ℝ (E × F) (ι → ℝ))) q :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasStrictFDerivAt.comp q
    hasStrictFDerivAt_snd

/-- Thm. 5.11 of [Dempe 2002] for the KKT reformulation (5.26): at every point `(x, y, λ)`
satisfying the KKT conditions of the follower's problem, neither (MFCQ) nor (LICQ) holds for the
constraints `g(x, y) ≤ 0`, `-λ ≤ 0`, `λᵢ gᵢ(x, y) = 0` together with arbitrary further constraints
`G ≤ 0`, `H = 0` in `(x, y, λ)` (the leader's constraints and the stationarity condition). -/
theorem not_nonsmoothMFCQ_kkt [Nonempty ι] (hq : IsLowerKKT φ g q.1.1 q.1.2 q.2)
    (hg : ∀ i, ContDiffAt ℝ 1 (g i) q.1)
    (hG : ∀ j, (clarkeSubdiff (G j) q).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) q).Nonempty) :
    ¬ NonsmoothMFCQ (complementarityInequalities G (fun i r ↦ g i r.1) fun i r ↦ r.2 i)
        (complementarityEqualities H (fun i r ↦ g i r.1) fun i r ↦ r.2 i) q ∧
      ¬ NonsmoothLICQ (complementarityInequalities G (fun i r ↦ g i r.1) fun i r ↦ r.2 i)
        (complementarityEqualities H (fun i r ↦ g i r.1) fun i r ↦ r.2 i) q :=
  not_nonsmoothMFCQ_complementarity (hasStrictFDerivAt_comp_fst_kkt hg)
    hasStrictFDerivAt_multiplier_kkt hq.1 hq.2.1 hq.2.2.1 hG hH

/-- Thm. 5.11 of [Dempe 2002] for the KKT reformulation (5.26) with the complementarity
conditions written as `λᵀ g(x, y) = 0`. -/
theorem not_nonsmoothMFCQ_kkt_aggregated (hq : IsLowerKKT φ g q.1.1 q.1.2 q.2)
    (hg : ∀ i, ContDiffAt ℝ 1 (g i) q.1)
    (hG : ∀ j, (clarkeSubdiff (G j) q).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) q).Nonempty) :
    ¬ NonsmoothMFCQ (complementarityInequalities G (fun i r ↦ g i r.1) fun i r ↦ r.2 i)
        (aggregatedComplementarityEqualities H (fun i r ↦ g i r.1) fun i r ↦ r.2 i) q ∧
      ¬ NonsmoothLICQ (complementarityInequalities G (fun i r ↦ g i r.1) fun i r ↦ r.2 i)
        (aggregatedComplementarityEqualities H (fun i r ↦ g i r.1) fun i r ↦ r.2 i) q :=
  not_nonsmoothMFCQ_aggregatedComplementarity (hasStrictFDerivAt_comp_fst_kkt hg)
    hasStrictFDerivAt_multiplier_kkt hq.1 hq.2.1
    (Finset.sum_eq_zero fun i _ ↦ hq.2.2.1 i) hG hH

/-- (MFCQ) and (LICQ) fail at every feasible point of the KKT reformulation of an LP–LP bilevel
problem [Ye–Zhu 1995; Schmidt 2024, p. 127]. -/
theorem LinearBilevel.not_nonsmoothMFCQ_kkt {κ : Type*} [Nonempty ι] {P : LinearBilevel E F κ ι}
    (hq : q ∈ P.kktFeasible)
    (hG : ∀ j, (clarkeSubdiff (G j) q).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) q).Nonempty) :
    ¬ NonsmoothMFCQ
        (complementarityInequalities G (fun i r ↦ P.lowerConstraints i r.1) fun i r ↦ r.2 i)
        (complementarityEqualities H (fun i r ↦ P.lowerConstraints i r.1) fun i r ↦ r.2 i) q ∧
      ¬ NonsmoothLICQ
        (complementarityInequalities G (fun i r ↦ P.lowerConstraints i r.1) fun i r ↦ r.2 i)
        (complementarityEqualities H (fun i r ↦ P.lowerConstraints i r.1) fun i r ↦ r.2 i) q := by
  obtain ⟨-, hfeas, hdual, hcs⟩ := hq
  have hg : ∀ i, ContDiffAt ℝ 1 (P.lowerConstraints i) q.1 := fun i ↦ by
    unfold LinearBilevel.lowerConstraints
    fun_prop
  refine not_nonsmoothMFCQ_complementarity (hasStrictFDerivAt_comp_fst_kkt hg)
    hasStrictFDerivAt_multiplier_kkt hfeas hdual.1 (fun i ↦ ?_) hG hH
  have := hcs i
  simp only [LinearBilevel.slack] at this
  simp only [LinearBilevel.lowerConstraints]
  linear_combination -this

end KKT

end Bilevel
