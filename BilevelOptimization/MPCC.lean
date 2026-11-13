/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.KKTRegularity
import VariationalAnalysis.Subdifferential.MinMax

/-!
# Programs with complementarity constraints

The nonsmooth form of a mathematical program with complementarity constraints

`min f(z)` subject to `Gⱼ(z) ≤ 0`, `Hₖ(z) = 0`, `min {-gᵢ(z), vᵢ(z)} = 0`,

and its Fritz John and KKT conditions [Scheel–Scholtes 2000], which Sect. 5.5 of [Dempe 2002]
applies to the nonsmooth KKT reformulation (5.27) of a bilevel problem (Thm. 5.16, 5.17).

## Main definitions

* `mpccFeasible G H g v`: the feasible set.
* `tightenedEqualities H g v z₀`: the equality constraints `H = 0`, `gᵢ = 0` (`gᵢ(z₀) = 0`),
  `vᵢ = 0` (`vᵢ(z₀) = 0`) of the tightened problem at `z₀` ((5.30) of [Dempe 2002]).

## Main results

* `exists_of_mem_clarkeSubdiff_min`: Clarke's generalized gradient of `min {a, b}` for strictly
  differentiable `a`, `b` lies in the segment `[∇a, ∇b]`, and reduces to the gradient of the
  smaller function where they differ.
* `exists_fritzJohn_mpcc`: Fritz John conditions with multipliers `ζᵢ`, `ξᵢ` of `gᵢ`, `vᵢ` such
  that `ζᵢ ξᵢ ≥ 0`.
* `exists_kkt_mpcc`: the same with leading multiplier `1` under (MFCQ) for the tightened problem.
* `nonneg_and_unique_of_isWeakMultiplier`: under (SMFCQ) for the tightened problem (in dual form)
  the multipliers are unique and `ζᵢ ≥ 0`, `ξᵢ ≥ 0` at the biactive indices.
-/

open Filter Topology Set
open scoped NNReal
open VariationalAnalysis (clarkeSubdiff subdiff)

namespace Bilevel

/-! ### Clarke's generalized gradient of a minimum -/

section ClarkeMin

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {a b : X → ℝ} {a' b' : StrongDual ℝ X} {z : X}

theorem eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt {w : StrongDual ℝ X}
    (ha : HasStrictFDerivAt a a' z) (hw : w ∈ clarkeSubdiff a z) : w = a' := by
  rwa [VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt ha,
    mem_singleton_iff] at hw

theorem subdiff_coe_eq_singleton_of_hasStrictFDerivAt (ha : HasStrictFDerivAt a a' z) :
    subdiff (fun x ↦ (a x : EReal)) z = {a'} := by
  have h := (VariationalAnalysis.strictDifferentiability_tfae (φ := fun x ↦ (a x : EReal))
    (x₀ := z) (x' := a')).out 2 1
  exact (h.1 ⟨a, Eventually.of_forall fun _ ↦ rfl, ha⟩).2

omit [FiniteDimensional ℝ X] in
theorem exists_lipschitzOnWith_min (ha : HasStrictFDerivAt a a' z)
    (hb : HasStrictFDerivAt b b' z) :
    ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z, LipschitzOnWith L (fun x ↦ min (a x) (b x)) U := by
  obtain ⟨Ka, Ua, hUa, hLa⟩ := ha.exists_lipschitzOnWith
  obtain ⟨Kb, Ub, hUb, hLb⟩ := hb.exists_lipschitzOnWith
  refine ⟨max Ka Kb, Ua ∩ Ub, inter_mem hUa hUb, ?_⟩
  rw [lipschitzOnWith_iff_restrict]
  exact (lipschitzOnWith_iff_restrict.1 (hLa.mono inter_subset_left)).min
    (lipschitzOnWith_iff_restrict.1 (hLb.mono inter_subset_right))

/-- Clarke's generalized gradient of `min {a, b}` for `a`, `b` strictly differentiable at `z`:
every element is `α ∇a(z) + (1 - α) ∇b(z)` with `α ∈ [0, 1]`, where `α = 1` if `a(z) < b(z)` and
`α = 0` if `b(z) < a(z)`. -/
theorem exists_of_mem_clarkeSubdiff_min (ha : HasStrictFDerivAt a a' z)
    (hb : HasStrictFDerivAt b b' z) {w : StrongDual ℝ X}
    (hw : w ∈ clarkeSubdiff (fun x ↦ min (a x) (b x)) z) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ (a z < b z → α = 1) ∧ (b z < a z → α = 0) ∧
      w = α • a' + (1 - α) • b' := by
  obtain ⟨L, U, hU, hL⟩ := exists_lipschitzOnWith_min ha hb
  rw [VariationalAnalysis.clarkeSubdiff_eq_convexHull hU hL] at hw
  -- the minimum as an infimum over `Bool`
  set φ : Bool → X → EReal := fun i x ↦ ((bif i then a x else b x : ℝ) : EReal) with hφ
  have hfun : (fun x ↦ ((min (a x) (b x) : ℝ) : EReal)) = fun x ↦ ⨅ i, φ i x := by
    funext x
    rw [iInf_bool_eq]
    exact EReal.coe_strictMono.monotone.map_min
  have hl : ∀ i, LowerSemicontinuousAt (φ i) z := by
    rintro (_ | _)
    · exact (continuous_coe_real_ereal.continuousAt.comp hb.continuousAt).lowerSemicontinuousAt
    · exact (continuous_coe_real_ereal.continuousAt.comp ha.continuousAt).lowerSemicontinuousAt
  have hS : subdiff (fun x ↦ ((min (a x) (b x) : ℝ) : EReal)) z ⊆
      {w | (w = a' ∧ a z ≤ b z) ∨ (w = b' ∧ b z ≤ a z)} := by
    rw [hfun]
    refine (VariationalAnalysis.subdiff_iInf_subset hl).trans fun w hw ↦ ?_
    obtain ⟨i, hi, hw⟩ := mem_iUnion₂.1 hw
    have hi' : φ i z = ⨅ j, φ j z := hi
    rw [iInf_bool_eq] at hi'
    cases i
    · have hs : subdiff (φ false) z = {b'} := subdiff_coe_eq_singleton_of_hasStrictFDerivAt hb
      rw [hs] at hw
      have h2 : ((b z : ℝ) : EReal) ≤ (a z : EReal) := by
        have := inf_le_left (a := φ true z) (b := φ false z)
        rw [← hi'] at this
        exact this
      exact Or.inr ⟨hw, EReal.coe_le_coe_iff.1 h2⟩
    · have hs : subdiff (φ true) z = {a'} := subdiff_coe_eq_singleton_of_hasStrictFDerivAt ha
      rw [hs] at hw
      have h2 : ((a z : ℝ) : EReal) ≤ (b z : EReal) := by
        have := inf_le_right (a := φ true z) (b := φ false z)
        rw [← hi'] at this
        exact this
      exact Or.inl ⟨hw, EReal.coe_le_coe_iff.1 h2⟩
  rcases lt_trichotomy (a z) (b z) with h | h | h
  · have hsub : subdiff (fun x ↦ ((min (a x) (b x) : ℝ) : EReal)) z ⊆ {a'} := fun w hw ↦
      (hS hw).elim (fun h' ↦ h'.1) fun h' ↦ absurd h'.2 (not_le.2 h)
    have hw' := convexHull_mono hsub hw
    rw [convexHull_singleton, mem_singleton_iff] at hw'
    exact ⟨1, zero_le_one, le_rfl, fun _ ↦ rfl, fun h' ↦ absurd h' (lt_asymm h), by
      rw [hw']; simp⟩
  · have hsub : subdiff (fun x ↦ ((min (a x) (b x) : ℝ) : EReal)) z ⊆ {a', b'} := fun w hw ↦
      (hS hw).elim (fun h' ↦ Or.inl h'.1) fun h' ↦ Or.inr h'.1
    have hw' := convexHull_mono hsub hw
    rw [convexHull_pair] at hw'
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hw'
    refine ⟨s, hs, by linarith, fun h' ↦ absurd h h'.ne, fun h' ↦ absurd h.symm h'.ne, ?_⟩
    rw [← hst, add_sub_cancel_left]
  · have hsub : subdiff (fun x ↦ ((min (a x) (b x) : ℝ) : EReal)) z ⊆ {b'} := fun w hw ↦
      (hS hw).elim (fun h' ↦ absurd h'.2 (not_le.2 h)) fun h' ↦ h'.1
    have hw' := convexHull_mono hsub hw
    rw [convexHull_singleton, mem_singleton_iff] at hw'
    exact ⟨0, le_rfl, zero_le_one, fun h' ↦ absurd h' (lt_asymm h), fun _ ↦ rfl, by
      rw [hw']; simp⟩

end ClarkeMin

/-! ### Fritz John and KKT conditions -/

section MPCC

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {I K ι : Type*}

/-- The feasible set of the program with complementarity constraints
`G ≤ 0`, `H = 0`, `min {-gᵢ, vᵢ} = 0`, i.e. `g ≤ 0`, `v ≥ 0`, `vᵢ gᵢ = 0`. -/
def mpccFeasible (G : I → X → ℝ) (H : K → X → ℝ) (g v : ι → X → ℝ) : Set X :=
  {z | (∀ j, G j z ≤ 0) ∧ (∀ k, H k z = 0) ∧ ∀ i, min (-g i z) (v i z) = 0}

/-- The equality constraints `H = 0`, `gᵢ = 0` for `gᵢ(z₀) = 0`, `vᵢ = 0` for `vᵢ(z₀) = 0` of
the tightened problem at `z₀` ((5.30) of [Dempe 2002]); its inequality constraints active at `z₀`
are `G ≤ 0`. -/
def tightenedEqualities (H : K → X → ℝ) (g v : ι → X → ℝ) (z₀ : X) :
    K ⊕ ({i // g i z₀ = 0} ⊕ {i // v i z₀ = 0}) → X → ℝ :=
  Sum.elim H (Sum.elim (fun i ↦ g i.1) fun i ↦ v i.1)

theorem sum_subtype_eq_sum {M : Type*} [AddCommMonoid M] [Fintype ι] {p : ι → Prop}
    [DecidablePred p] (F : ι → M) (h : ∀ i, ¬ p i → F i = 0) :
    ∑ i : {i // p i}, F i.1 = ∑ i, F i := by
  rw [← Fintype.sum_subtype_add_sum_subtype p F,
    Finset.sum_eq_zero (s := (Finset.univ : Finset {i // ¬ p i})) fun i _ ↦ h i.1 i.2, add_zero]

variable [FiniteDimensional ℝ X] [Fintype I] [Fintype K] [Fintype ι]
  {f : X → ℝ} {G : I → X → ℝ} {H : K → X → ℝ} {g v : ι → X → ℝ} {f' : StrongDual ℝ X}
  {G' : I → StrongDual ℝ X} {H' : K → StrongDual ℝ X} {g' v' : ι → StrongDual ℝ X} {z₀ : X}

/-- Fritz John conditions for programs with complementarity constraints [Scheel–Scholtes 2000]:
at a local minimizer `z₀` of `f` subject to `G ≤ 0`, `H = 0`, `min {-gᵢ, vᵢ} = 0` with strictly
differentiable data there are `κ₀ ∈ {0, 1}`, `κ ≥ 0`, `μ`, `ζ`, `ξ`, not all zero, with
`κ₀ ∇f + ∑ κⱼ ∇Gⱼ + ∑ μₖ ∇Hₖ + ∑ ζᵢ ∇gᵢ - ∑ ξᵢ ∇vᵢ = 0`, complementary slackness
`κⱼ Gⱼ = 0`, `ζᵢ gᵢ = 0`, `ξᵢ vᵢ = 0`, and `ζᵢ ξᵢ ≥ 0`. -/
theorem exists_fritzJohn_mpcc (hz₀ : z₀ ∈ mpccFeasible G H g v)
    (hmin : IsLocalMinOn f (mpccFeasible G H g v) z₀) (hf : HasStrictFDerivAt f f' z₀)
    (hG : ∀ j, HasStrictFDerivAt (G j) (G' j) z₀) (hH : ∀ k, HasStrictFDerivAt (H k) (H' k) z₀)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z₀) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z₀) :
    ∃ κ₀ : ℝ, ∃ κ : I → ℝ, ∃ μ : K → ℝ, ∃ ζ ξ : ι → ℝ, (κ₀ = 0 ∨ κ₀ = 1) ∧ (∀ j, 0 ≤ κ j) ∧
      (∀ j, κ j * G j z₀ = 0) ∧ (∀ i, ζ i * g i z₀ = 0) ∧ (∀ i, ξ i * v i z₀ = 0) ∧
      (∀ i, 0 ≤ ζ i * ξ i) ∧ (κ₀, κ, μ, ζ, ξ) ≠ 0 ∧
      κ₀ • f' + ∑ j, κ j • G' j + ∑ k, μ k • H' k + ∑ i, ζ i • g' i - ∑ i, ξ i • v' i = 0 := by
  -- the program as a Lipschitz program with equality constraints `H = 0`, `min {-g, v} = 0`
  set Hm : K ⊕ ι → X → ℝ := Sum.elim H fun i z ↦ min (-g i z) (v i z) with hHm
  have hset : {z | (∀ j, G j z ≤ 0) ∧ ∀ k, Hm k z = 0} = mpccFeasible G H g v := by
    ext z
    simp only [mpccFeasible, Hm, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  have hz₀' : (∀ j, G j z₀ ≤ 0) ∧ ∀ k, Hm k z₀ = 0 := by
    have := hz₀
    rwa [← hset] at this
  obtain ⟨κ₀, κ, μm, hκ₀, hκ, hcs, hne, ζ₀, hζ₀, η, hη, ξm, hξm, hsum⟩ :=
    exists_fritzJohn_clarke (f := f) (G := G) (H := Hm) hz₀' (by rw [hset]; exact hmin)
      hf.exists_lipschitzOnWith (fun j ↦ (hG j).exists_lipschitzOnWith) (by
        rintro (k | i)
        exacts [(hH k).exists_lipschitzOnWith, exists_lipschitzOnWith_min (hg i).neg (hv i)])
  have e0 : ζ₀ = f' := eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt hf hζ₀
  have eG : ∀ j, η j = G' j := fun j ↦ eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hG j) (hη j)
  have eH : ∀ k, ξm (Sum.inl k) = H' k := fun k ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hH k) (hξm (Sum.inl k))
  have hmn : ∀ i, ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ (-g i z₀ < v i z₀ → α = 1) ∧
      (v i z₀ < -g i z₀ → α = 0) ∧ ξm (Sum.inr i) = α • -g' i + (1 - α) • v' i := fun i ↦
    exists_of_mem_clarkeSubdiff_min (hg i).neg (hv i) (hξm (Sum.inr i))
  choose α hα0 hα1 hαg hαv hαeq using hmn
  have hfeas : ∀ i, 0 ≤ -g i z₀ ∧ 0 ≤ v i z₀ ∧ -g i z₀ * v i z₀ = 0 := fun i ↦
    min_eq_zero_iff.1 (hz₀.2.2 i)
  refine ⟨κ₀, κ, fun k ↦ μm (Sum.inl k), fun i ↦ -(μm (Sum.inr i) * α i),
    fun i ↦ -(μm (Sum.inr i) * (1 - α i)), hκ₀, hκ, hcs, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_,
    ?_, ?_⟩
  · dsimp only
    by_cases h : g i z₀ = 0
    · rw [h, mul_zero]
    · obtain ⟨h1, h2, h3⟩ := hfeas i
      have hpos : 0 < -g i z₀ := lt_of_le_of_ne h1 fun h' ↦ h (by linarith)
      have hv0 : v i z₀ = 0 := (mul_eq_zero.1 h3).resolve_left hpos.ne'
      rw [hαv i (by linarith)]
      ring
  · dsimp only
    by_cases h : v i z₀ = 0
    · rw [h, mul_zero]
    · obtain ⟨h1, h2, h3⟩ := hfeas i
      have hpos : 0 < v i z₀ := lt_of_le_of_ne h2 (Ne.symm h)
      have hg0 : -g i z₀ = 0 := (mul_eq_zero.1 h3).resolve_right hpos.ne'
      rw [hαg i (by linarith)]
      ring
  · dsimp only
    have e : -(μm (Sum.inr i) * α i) * -(μm (Sum.inr i) * (1 - α i)) =
        μm (Sum.inr i) ^ 2 * (α i * (1 - α i)) := by ring
    rw [e]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hα0 i) (sub_nonneg.2 (hα1 i)))
  · intro h0
    simp only [Prod.mk_eq_zero] at h0
    obtain ⟨h1, h2, h3, h4, h5⟩ := h0
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨h1, h2, funext ?_⟩
    rintro (k | i)
    · exact congrFun h3 k
    · have a1 := congrFun h4 i
      have a2 := congrFun h5 i
      simp only [Pi.zero_apply] at a1 a2 ⊢
      linear_combination -a1 - a2
  · have hS : ∑ i, μm (Sum.inr i) • (α i • -g' i + (1 - α i) • v' i) =
        ∑ i, -(μm (Sum.inr i) * α i) • g' i - ∑ i, -(μm (Sum.inr i) * (1 - α i)) • v' i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by module
    simp only [Fintype.sum_sum_type, e0, eG, eH, hαeq, hS] at hsum
    rw [← hsum]
    abel

/-- KKT conditions for programs with complementarity constraints [Scheel–Scholtes 2000]: if in
addition (MFCQ) holds at `z₀` for the tightened problem, with equality constraints
`tightenedEqualities H g v z₀`, then the leading multiplier in `exists_fritzJohn_mpcc` is `1`. -/
theorem exists_kkt_mpcc (hz₀ : z₀ ∈ mpccFeasible G H g v)
    (hmin : IsLocalMinOn f (mpccFeasible G H g v) z₀) (hf : HasStrictFDerivAt f f' z₀)
    (hG : ∀ j, HasStrictFDerivAt (G j) (G' j) z₀) (hH : ∀ k, HasStrictFDerivAt (H k) (H' k) z₀)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z₀) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z₀)
    (hcq : NonsmoothMFCQ G (tightenedEqualities H g v z₀) z₀) :
    ∃ κ : I → ℝ, ∃ μ : K → ℝ, ∃ ζ ξ : ι → ℝ, (∀ j, 0 ≤ κ j) ∧
      (∀ j, κ j * G j z₀ = 0) ∧ (∀ i, ζ i * g i z₀ = 0) ∧ (∀ i, ξ i * v i z₀ = 0) ∧
      (∀ i, 0 ≤ ζ i * ξ i) ∧
      f' + ∑ j, κ j • G' j + ∑ k, μ k • H' k + ∑ i, ζ i • g' i - ∑ i, ξ i • v' i = 0 := by
  classical
  obtain ⟨κ₀, κ, μ, ζ, ξ, hκ₀ | hκ₀, hκ, hcs, hζ, hξ, hprod, hne, hsum⟩ :=
    exists_fritzJohn_mpcc hz₀ hmin hf hG hH hg hv
  · -- a vanishing leading multiplier gives an abnormal multiplier of the tightened problem
    exfalso
    subst hκ₀
    have hT : ∀ k, (clarkeSubdiff (tightenedEqualities H g v z₀ k) z₀).Nonempty := by
      rintro (k | i | i)
      exacts [⟨_, mem_clarkeSubdiff_of_hasStrictFDerivAt (hH k)⟩,
        ⟨_, mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i.1)⟩,
        ⟨_, mem_clarkeSubdiff_of_hasStrictFDerivAt (hv i.1)⟩]
    have hΛ := (nonsmoothMFCQ_iff_abnormalMultipliers_eq
      (fun j ↦ ⟨_, mem_clarkeSubdiff_of_hasStrictFDerivAt (hG j)⟩) hT).1 hcq
    have hmem : (κ, Sum.elim μ (Sum.elim (fun i : {i // g i z₀ = 0} ↦ ζ i.1)
        fun i : {i // v i z₀ = 0} ↦ -ξ i.1)) ∈
        abnormalMultipliers G (tightenedEqualities H g v z₀) z₀ := by
      refine ⟨hκ, hcs, G', fun j ↦ mem_clarkeSubdiff_of_hasStrictFDerivAt (hG j),
        Sum.elim H' (Sum.elim (fun i ↦ g' i.1) fun i ↦ v' i.1), ?_, ?_⟩
      · rintro (k | i | i)
        exacts [mem_clarkeSubdiff_of_hasStrictFDerivAt (hH k),
          mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i.1),
          mem_clarkeSubdiff_of_hasStrictFDerivAt (hv i.1)]
      · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
        rw [sum_subtype_eq_sum (p := fun i ↦ g i z₀ = 0) (fun i ↦ ζ i • g' i) fun i hi ↦ by
            rw [(mul_eq_zero.1 (hζ i)).resolve_right hi, zero_smul],
          sum_subtype_eq_sum (p := fun i ↦ v i z₀ = 0) (fun i ↦ -ξ i • v' i) fun i hi ↦ by
            rw [(mul_eq_zero.1 (hξ i)).resolve_right hi, neg_zero, zero_smul]]
        have e : ∑ i, -ξ i • v' i = -∑ i, ξ i • v' i := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by module
        rw [e, ← hsum]
        simp only [zero_smul, zero_add]
        abel
    rw [hΛ, mem_singleton_iff, Prod.mk_eq_zero] at hmem
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨trivial, hmem.1, funext fun k ↦ congrFun hmem.2 (Sum.inl k), funext fun i ↦ ?_,
      funext fun i ↦ ?_⟩
    · by_cases h : g i z₀ = 0
      · exact congrFun hmem.2 (Sum.inr (Sum.inl ⟨i, h⟩))
      · exact (mul_eq_zero.1 (hζ i)).resolve_right h
    · by_cases h : v i z₀ = 0
      · exact neg_eq_zero.1 (congrFun hmem.2 (Sum.inr (Sum.inr ⟨i, h⟩)))
      · exact (mul_eq_zero.1 (hξ i)).resolve_right h
  · subst hκ₀
    exact ⟨κ, μ, ζ, ξ, hκ, hcs, hζ, hξ, hprod, by simpa using hsum⟩

/-! ### Strong stationarity -/

section ExtendZero

variable {p : ι → Prop} [DecidablePred p]

/-- Extension by zero of a family indexed by a subtype. -/
def extendZero (c : {i // p i} → ℝ) : ι → ℝ := fun i ↦ if h : p i then c ⟨i, h⟩ else 0

omit [Fintype ι] in
theorem extendZero_coe (c : {i // p i} → ℝ) (i : {i // p i}) : extendZero c i.1 = c i :=
  dif_pos i.2

omit [Fintype ι] in
theorem extendZero_of_not (c : {i // p i} → ℝ) {i : ι} (h : ¬ p i) : extendZero c i = 0 :=
  dif_neg h

theorem sum_extendZero_smul {M : Type*} [AddCommGroup M] [Module ℝ M]
    (c : {i // p i} → ℝ) (w : ι → M) :
    ∑ i, extendZero c i • w i = ∑ i : {i // p i}, c i • w i.1 := by
  rw [← sum_subtype_eq_sum (p := p) (fun i ↦ extendZero c i • w i) fun i hi ↦ by
    rw [extendZero_of_not c hi, zero_smul]]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [extendZero_coe]

end ExtendZero

/-- Multipliers `m = (κ, μ, ζ, ξ)` of the tightened problem with objective gradient `c`:
`c + ∑ κⱼ ∇Gⱼ + ∑ μₖ ∇Hₖ + ∑ ζᵢ ∇gᵢ - ∑ ξᵢ ∇vᵢ = 0` with complementary slackness `κⱼ Gⱼ = 0`,
`ζᵢ gᵢ = 0`, `ξᵢ vᵢ = 0`; no sign conditions. The gradients are passed as families
`G'`, `H'`, `g'`, `v'`. -/
def IsWeakMultiplier (G : I → X → ℝ) (g v : ι → X → ℝ) (z₀ : X) (c : StrongDual ℝ X)
    (G' : I → StrongDual ℝ X) (H' : K → StrongDual ℝ X) (g' v' : ι → StrongDual ℝ X)
    (m : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ)) : Prop :=
  (∀ j, m.1 j * G j z₀ = 0) ∧ (∀ i, m.2.2.1 i * g i z₀ = 0) ∧ (∀ i, m.2.2.2 i * v i z₀ = 0) ∧
    c + ∑ j, m.1 j • G' j + ∑ k, m.2.1 k • H' k + ∑ i, m.2.2.1 i • g' i -
      ∑ i, m.2.2.2 i • v' i = 0

omit [FiniteDimensional ℝ X] in
theorem IsWeakMultiplier.sub {c₁ c₂ : StrongDual ℝ X} {m₁ m₂ : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ)}
    (h₁ : IsWeakMultiplier G g v z₀ c₁ G' H' g' v' m₁)
    (h₂ : IsWeakMultiplier G g v z₀ c₂ G' H' g' v' m₂) :
    IsWeakMultiplier G g v z₀ (c₁ - c₂) G' H' g' v' (m₁ - m₂) := by
  obtain ⟨a1, a2, a3, a4⟩ := h₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂
  refine ⟨fun j ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, sub_mul, a1 j, b1 j, sub_zero]
  · simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, a2 i, b2 i, sub_zero]
  · simp only [Prod.snd_sub, Pi.sub_apply, sub_mul, a3 i, b3 i, sub_zero]
  · have hs : ∀ (a b : ι → ℝ) (w : ι → StrongDual ℝ X),
        ∑ i, (a i - b i) • w i = ∑ i, a i • w i - ∑ i, b i • w i := fun a b w ↦ by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by module
    have hsI : ∑ j, (m₁.1 j - m₂.1 j) • G' j = ∑ j, m₁.1 j • G' j - ∑ j, m₂.1 j • G' j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by module
    have hsK : ∑ k, (m₁.2.1 k - m₂.2.1 k) • H' k =
        ∑ k, m₁.2.1 k • H' k - ∑ k, m₂.2.1 k • H' k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by module
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, hs, hsI, hsK]
    rw [← sub_eq_zero.2 (a4.trans b4.symm)]
    abel

omit [FiniteDimensional ℝ X] in
/-- Exchanging the roles of `g` and `v` (`min {-g, v} = min {-(-v), -g}`). -/
theorem IsWeakMultiplier.swap {c : StrongDual ℝ X} {m : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ)}
    (h : IsWeakMultiplier G (fun i z ↦ -v i z) (fun i z ↦ -g i z) z₀ c G' H' (fun i ↦ -v' i)
      (fun i ↦ -g' i) m) :
    IsWeakMultiplier G g v z₀ c G' H' g' v' (m.1, m.2.1, m.2.2.2, m.2.2.1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · simpa using h3 i
  · simpa using h2 i
  · simp only [smul_neg, Finset.sum_neg_distrib] at h4
    rw [← h4]
    abel

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [Fintype I] [Fintype K]
  [Fintype ι] in
theorem mpccFeasible_swap :
    mpccFeasible G H (fun i z ↦ -v i z) (fun i z ↦ -g i z) = mpccFeasible G H g v := by
  ext z
  simp only [mpccFeasible, mem_ofPred_eq, neg_neg, min_comm]

/-- A multiplier of the tightened problem whose component `ζ_{i₀}` at a biactive index `i₀` is
nonnegative: `z₀` is a local minimizer of the problem in which `g_{i₀} = 0` is relaxed to
`g_{i₀} ≤ 0`, and that problem is regular by `hreg`. -/
theorem exists_isWeakMultiplier_relaxed (hz₀ : z₀ ∈ mpccFeasible G H g v)
    (hmin : IsLocalMinOn f (mpccFeasible G H g v) z₀) (hf : HasStrictFDerivAt f f' z₀)
    (hG : ∀ j, HasStrictFDerivAt (G j) (G' j) z₀) (hH : ∀ k, HasStrictFDerivAt (H k) (H' k) z₀)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z₀) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z₀)
    {κ : I → ℝ}
    (hreg : ∀ m : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ), (∀ j, κ j = 0 → 0 ≤ m.1 j) →
      IsWeakMultiplier G g v z₀ 0 G' H' g' v' m → m = 0)
    {i₀ : ι} (hg₀ : g i₀ z₀ = 0) (hv₀ : v i₀ z₀ = 0) :
    ∃ m, IsWeakMultiplier G g v z₀ f' G' H' g' v' m ∧ (∀ j, 0 ≤ m.1 j) ∧ 0 ≤ m.2.2.1 i₀ := by
  classical
  -- the relaxed problem
  set Gr : I ⊕ Unit → X → ℝ := Sum.elim G fun _ ↦ g i₀ with hGr
  set Hr : K ⊕ ({i // g i z₀ = 0 ∧ i ≠ i₀} ⊕ {i // v i z₀ = 0}) → X → ℝ :=
    Sum.elim H (Sum.elim (fun i ↦ g i.1) fun i ↦ v i.1) with hHr
  have hfeasP : (∀ k, Gr k z₀ ≤ 0) ∧ ∀ k, Hr k z₀ = 0 := by
    refine ⟨?_, ?_⟩
    · rintro (j | u)
      exacts [hz₀.1 j, hg₀.le]
    · rintro (k | i | i)
      exacts [hz₀.2.1 k, i.2.1, i.2]
  have hev : ∀ᶠ z in 𝓝 z₀, ∀ i, (0 < v i z₀ → 0 < v i z) ∧ (g i z₀ < 0 → g i z < 0) := by
    refine eventually_all.2 fun i ↦ Eventually.and ?_ ?_
    · by_cases h : 0 < v i z₀
      · exact ((hv i).continuousAt.eventually (lt_mem_nhds h)).mono fun z hz _ ↦ hz
      · exact Eventually.of_forall fun z h' ↦ absurd h' h
    · by_cases h : g i z₀ < 0
      · exact ((hg i).continuousAt.eventually (gt_mem_nhds h)).mono fun z hz _ ↦ hz
      · exact Eventually.of_forall fun z h' ↦ absurd h' h
  have hminP : IsLocalMinOn f {z | (∀ k, Gr k z ≤ 0) ∧ ∀ k, Hr k z = 0} z₀ := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [eventually_nhdsWithin_iff.1 hmin, hev] with z hz hzev hzP
    refine hz ⟨fun j ↦ hzP.1 (Sum.inl j), fun k ↦ hzP.2 (Sum.inl k), fun i ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := min_eq_zero_iff.1 (hz₀.2.2 i)
    by_cases hv0 : v i z₀ = 0
    · have hvz : v i z = 0 := hzP.2 (Sum.inr (Sum.inr ⟨i, hv0⟩))
      have hgz : g i z ≤ 0 := by
        by_cases hi : i = i₀
        · subst hi
          exact hzP.1 (Sum.inr ())
        · by_cases hg0 : g i z₀ = 0
          · exact (hzP.2 (Sum.inr (Sum.inl ⟨i, hg0, hi⟩))).le
          · exact ((hzev i).2 (lt_of_le_of_ne (by linarith) hg0)).le
      rw [hvz]
      exact min_eq_right (by linarith)
    · have hpos : 0 < v i z₀ := lt_of_le_of_ne h2 (Ne.symm hv0)
      have hg0 : g i z₀ = 0 := by
        have := (mul_eq_zero.1 h3).resolve_right hv0
        linarith
      have hi : i ≠ i₀ := fun h ↦ hv0 (h ▸ hv₀)
      have hgz : g i z = 0 := hzP.2 (Sum.inr (Sum.inl ⟨i, hg0, hi⟩))
      rw [hgz, neg_zero]
      exact min_eq_left ((hzev i).1 hpos).le
  obtain ⟨κ₀, lam, μm, hκ₀, hlam, hcs, hne, ζ₀, hζ₀, η, hη, ξm, hξm, hsum⟩ :=
    exists_fritzJohn_clarke (f := f) (G := Gr) (H := Hr) hfeasP hminP hf.exists_lipschitzOnWith
      (by
        rintro (j | u)
        exacts [(hG j).exists_lipschitzOnWith, (hg i₀).exists_lipschitzOnWith])
      (by
        rintro (k | i | i)
        exacts [(hH k).exists_lipschitzOnWith, (hg i.1).exists_lipschitzOnWith,
          (hv i.1).exists_lipschitzOnWith])
  have e0 : ζ₀ = f' := eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt hf hζ₀
  have eG : ∀ j, η (Sum.inl j) = G' j := fun j ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hG j) (hη (Sum.inl j))
  have eg₀ : ∀ u : Unit, η (Sum.inr u) = g' i₀ := fun u ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i₀) (hη (Sum.inr u))
  have eH : ∀ k, ξm (Sum.inl k) = H' k := fun k ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hH k) (hξm (Sum.inl k))
  have eg : ∀ i, ξm (Sum.inr (Sum.inl i)) = g' i.1 := fun i ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hg i.1) (hξm (Sum.inr (Sum.inl i)))
  have ev : ∀ i, ξm (Sum.inr (Sum.inr i)) = v' i.1 := fun i ↦
    eq_of_mem_clarkeSubdiff_of_hasStrictFDerivAt (hv i.1) (hξm (Sum.inr (Sum.inr i)))
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, e0, eG, eg₀, eH, eg,
    ev] at hsum
  -- multipliers of the relaxed problem as multipliers of the tightened problem
  set cζ : {i // g i z₀ = 0 ∧ i ≠ i₀} → ℝ := fun i ↦ μm (Sum.inr (Sum.inl i)) with hcζ
  set cξ : {i // v i z₀ = 0} → ℝ := fun i ↦ μm (Sum.inr (Sum.inr i)) with hcξ
  set ζ' : ι → ℝ := Pi.single i₀ (lam (Sum.inr ())) + extendZero cζ with hζ'
  set ξ' : ι → ℝ := -extendZero cξ with hξ'
  have hζi₀ : ζ' i₀ = lam (Sum.inr ()) := by
    rw [hζ', Pi.add_apply, Pi.single_eq_same, extendZero_of_not cζ fun h ↦ h.2 rfl, add_zero]
  have hζsub : ∀ i : {i // g i z₀ = 0 ∧ i ≠ i₀}, ζ' i.1 = cζ i := fun i ↦ by
    rw [hζ', Pi.add_apply, Pi.single_eq_of_ne i.2.2, zero_add, extendZero_coe]
  have hξsub : ∀ i : {i // v i z₀ = 0}, ξ' i.1 = -cξ i := fun i ↦ by
    rw [hξ', Pi.neg_apply, extendZero_coe]
  have hW : IsWeakMultiplier G g v z₀ (κ₀ • f') G' H' g' v'
      (fun j ↦ lam (Sum.inl j), fun k ↦ μm (Sum.inl k), ζ', ξ') := by
    refine ⟨fun j ↦ hcs (Sum.inl j), fun i ↦ ?_, fun i ↦ ?_, ?_⟩
    · by_cases hgi : g i z₀ = 0
      · rw [hgi, mul_zero]
      · have hi : i ≠ i₀ := fun h ↦ hgi (h ▸ hg₀)
        show ζ' i * g i z₀ = 0
        rw [hζ', Pi.add_apply, Pi.single_eq_of_ne hi, extendZero_of_not cζ fun h ↦ hgi h.1,
          add_zero, zero_mul]
    · by_cases hvi : v i z₀ = 0
      · rw [hvi, mul_zero]
      · show ξ' i * v i z₀ = 0
        rw [hξ', Pi.neg_apply, extendZero_of_not cξ hvi, neg_zero, zero_mul]
    · show κ₀ • f' + ∑ j, lam (Sum.inl j) • G' j + ∑ k, μm (Sum.inl k) • H' k +
        ∑ i, ζ' i • g' i - ∑ i, ξ' i • v' i = 0
      have s1 : ∑ i, ζ' i • g' i = lam (Sum.inr ()) • g' i₀ +
          ∑ i : {i // g i z₀ = 0 ∧ i ≠ i₀}, cζ i • g' i.1 := by
        simp only [hζ', Pi.add_apply, add_smul, Finset.sum_add_distrib, sum_extendZero_smul]
        rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_smul])
          (fun hi ↦ absurd (Finset.mem_univ i₀) hi), Pi.single_eq_same]
      have s2 : ∑ i, ξ' i • v' i = -∑ i : {i // v i z₀ = 0}, cξ i • v' i.1 := by
        rw [← sum_extendZero_smul cξ v', ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hξ', Pi.neg_apply]; module
      rw [s1, s2, ← hsum]
      abel
  rcases hκ₀ with h0 | h1
  · exfalso
    rw [h0, zero_smul] at hW
    have hm0 := hreg _ (fun j _ ↦ hlam (Sum.inl j)) hW
    simp only [Prod.mk_eq_zero] at hm0
    obtain ⟨m1, m2, m3, m4⟩ := hm0
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨h0, funext ?_, funext ?_⟩
    · rintro (j | u)
      · exact congrFun m1 j
      · have := congrFun m3 i₀
        rw [hζi₀] at this
        exact this
    · rintro (k | i | i)
      · exact congrFun m2 k
      · have := congrFun m3 i.1
        rw [hζsub i] at this
        exact this
      · have := congrFun m4 i.1
        rw [hξsub i] at this
        exact neg_eq_zero.1 this
  · rw [h1, one_smul] at hW
    exact ⟨_, hW, fun j ↦ hlam (Sum.inl j), by
      show 0 ≤ ζ' i₀
      rw [hζi₀]
      exact hlam (Sum.inr ())⟩

/-- Strong stationarity for programs with complementarity constraints [Scheel–Scholtes 2000]:
let `z₀` be a local minimizer and `m = (κ, μ, ζ, ξ)` a multiplier of the tightened problem with
`κ ≥ 0`, and assume the dual form `hreg` of (SMFCQ) for the tightened problem: the only
multiplier `m'` for the zero objective with `κ'ⱼ ≥ 0` where `κⱼ = 0` is `m' = 0`. Then
`ζᵢ ≥ 0` and `ξᵢ ≥ 0` at the biactive indices, and `m` is the unique multiplier with `κ ≥ 0`. -/
theorem nonneg_and_unique_of_isWeakMultiplier (hz₀ : z₀ ∈ mpccFeasible G H g v)
    (hmin : IsLocalMinOn f (mpccFeasible G H g v) z₀) (hf : HasStrictFDerivAt f f' z₀)
    (hG : ∀ j, HasStrictFDerivAt (G j) (G' j) z₀) (hH : ∀ k, HasStrictFDerivAt (H k) (H' k) z₀)
    (hg : ∀ i, HasStrictFDerivAt (g i) (g' i) z₀) (hv : ∀ i, HasStrictFDerivAt (v i) (v' i) z₀)
    {m : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ)}
    (hm : IsWeakMultiplier G g v z₀ f' G' H' g' v' m)
    (hreg : ∀ m' : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ), (∀ j, m.1 j = 0 → 0 ≤ m'.1 j) →
      IsWeakMultiplier G g v z₀ 0 G' H' g' v' m' → m' = 0) :
    (∀ i, g i z₀ = 0 → v i z₀ = 0 → 0 ≤ m.2.2.1 i ∧ 0 ≤ m.2.2.2 i) ∧
      ∀ m', IsWeakMultiplier G g v z₀ f' G' H' g' v' m' → (∀ j, 0 ≤ m'.1 j) → m' = m := by
  have huniq : ∀ m', IsWeakMultiplier G g v z₀ f' G' H' g' v' m' → (∀ j, 0 ≤ m'.1 j) →
      m' = m := fun m' hm' hnn ↦ by
    have hd := hm'.sub hm
    rw [sub_self] at hd
    exact sub_eq_zero.1 (hreg _ (fun j hj ↦ by
      simp only [Prod.fst_sub, Pi.sub_apply, hj, sub_zero]
      exact hnn j) hd)
  refine ⟨fun i hgi hvi ↦ ⟨?_, ?_⟩, huniq⟩
  · obtain ⟨m', hm', hnn, hζ⟩ :=
      exists_isWeakMultiplier_relaxed hz₀ hmin hf hG hH hg hv hreg hgi hvi
    rw [← huniq m' hm' hnn]
    exact hζ
  · -- the same with the roles of `g` and `v` exchanged
    have hregs : ∀ ms : (I → ℝ) × (K → ℝ) × (ι → ℝ) × (ι → ℝ), (∀ j, m.1 j = 0 → 0 ≤ ms.1 j) →
        IsWeakMultiplier G (fun i z ↦ -v i z) (fun i z ↦ -g i z) z₀ 0 G' H' (fun i ↦ -v' i)
          (fun i ↦ -g' i) ms → ms = 0 := fun ms hnn hms ↦ by
      have := hreg (ms.1, ms.2.1, ms.2.2.2, ms.2.2.1) hnn hms.swap
      simp only [Prod.mk_eq_zero] at this
      obtain ⟨a1, a2, a3, a4⟩ := this
      exact Prod.ext a1 (Prod.ext a2 (Prod.ext a4 a3))
    obtain ⟨m', hm', hnn, hξ⟩ :=
      exists_isWeakMultiplier_relaxed (g := fun i z ↦ -v i z) (v := fun i z ↦ -g i z)
        (g' := fun i ↦ -v' i) (v' := fun i ↦ -g' i) (by rw [mpccFeasible_swap]; exact hz₀)
        (by rw [mpccFeasible_swap]; exact hmin) hf hG hH (fun i ↦ (hv i).neg)
        (fun i ↦ (hg i).neg) hregs (by rw [hvi, neg_zero]) (by rw [hgi, neg_zero])
    have := huniq _ hm'.swap hnn
    rw [← this]
    exact hξ

end MPCC

end Bilevel
