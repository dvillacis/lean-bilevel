/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import VariationalAnalysis.Subdifferential.Clarke
import VariationalAnalysis.Optimality.Programming
import VariationalAnalysis.Optimality.BilevelSmooth

/-!
# Lipschitz programs and Clarke multipliers

Sect. 5.6 of [Dempe 2002]: the problem (5.37)

`min f(z)` subject to `Gᵢ(z) ≤ 0` (`i ∈ I`), `Hₖ(z) = 0` (`k ∈ K`)

with locally Lipschitz data, its nonsmooth constraint qualifications, and its multiplier rules in
terms of Clarke's generalized gradient `∂̄`.

## Main definitions

* `NonsmoothMFCQ`: the nonsmooth Mangasarian–Fromovitz constraint qualification (NMFCQ).
* `NonsmoothLICQ`: the nonsmooth linear independence constraint qualification (NLICQ).
* `abnormalMultipliers`: the set `Λ⁰(z)` of abnormal multipliers (5.39).

## Main results

* `exists_multipliers_of_not_exists_direction`: Motzkin's theorem of the alternative.
* `nonsmoothMFCQ_iff_abnormalMultipliers_eq`: Thm. 5.18 of [Dempe 2002]: (NMFCQ) holds iff
  `Λ⁰(z) = {0}`.
* `NonsmoothLICQ.nonsmoothMFCQ`: (NLICQ) implies (NMFCQ).
* `exists_fritzJohn_clarke`: the Lagrange multiplier rule for Lipschitz programs [Clarke 1983,
  Thm. 6.1.1], in Fritz John form with `κ₀ ∈ {0, 1}`, derived from Thm. 6.5(ii) of
  [Mordukhovich 2018] and `∂f ⊆ ∂̄f`.
* `exists_kkt_clarke_of_abnormalMultipliers_eq`, `exists_kkt_clarke_of_nonsmoothMFCQ`: the KKT
  form under (NMFCQ).

## Clarke calculus

* `clarkeSubdiff_comp_fst`: `∂̄(ψ ∘ fst)(x, y) = ∂̄ψ(x) × {0}`.
* `clarkeSubdiff_add_eq_of_hasStrictFDerivAt`: `∂̄(f + g)(x) = ∇f(x) + ∂̄g(x)` for `f` strictly
  differentiable at `x` and `g` Lipschitz around `x`.

## Remarks on the book

* In (NMFCQ) and (NLICQ) the generalized gradients of the inactive inequality constraints play no
  role. In `Λ⁰(z)` every constraint carries a generalized gradient, as in `λᵀ∂̄G(z) + μᵀ∂̄H(z)`;
  these sets are nonempty for Lipschitz data.
* Thm. 5.18 does not need `z` to be feasible.
-/

open Filter Topology Set
open scoped NNReal Pointwise
open VariationalAnalysis (clarkeDeriv clarkeSubdiff subdiff)

namespace Bilevel

/-! ### Clarke calculus -/

section Clarke

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem clarkeDeriv_zero (f : E → ℝ) (x₀ : E) : clarkeDeriv f x₀ 0 = 0 := by
  simp only [clarkeDeriv, smul_zero, add_zero, sub_self, zero_div, EReal.coe_zero]
  exact limsup_const 0

theorem clarkeDeriv_comp_fst (ψ : E → ℝ) (p v : E × F) :
    clarkeDeriv (fun q : E × F ↦ ψ q.1) p v = clarkeDeriv ψ p.1 v.1 := by
  have hfun : (fun q : (E × F) × ℝ ↦ (((ψ (q.1 + q.2 • v).1 - ψ q.1.1) / q.2 : ℝ) : EReal)) =
      (fun r : E × ℝ ↦ (((ψ (r.1 + r.2 • v.1) - ψ r.1) / r.2 : ℝ) : EReal)) ∘
        fun q ↦ (q.1.1, q.2) := by
    funext q
    simp
  have hmap : map (fun q : (E × F) × ℝ ↦ (q.1.1, q.2)) (𝓝 p ×ˢ 𝓝[>] 0) =
      𝓝 p.1 ×ˢ 𝓝[>] (0 : ℝ) := by
    have := (prod_map_map_eq (f₁ := 𝓝 p) (f₂ := 𝓝[>] (0 : ℝ)) (m₁ := Prod.fst)
      (m₂ := id)).symm
    rwa [map_fst_nhds, map_id] at this
  unfold clarkeDeriv
  rw [hfun, limsup_comp, hmap]

/-- The generalized gradient of `ψ ∘ fst` is `∂̄ψ × {0}`. -/
theorem clarkeSubdiff_comp_fst (ψ : E → ℝ) (p : E × F) :
    clarkeSubdiff (fun q : E × F ↦ ψ q.1) p =
      (fun u : StrongDual ℝ E ↦ u.comp (ContinuousLinearMap.fst ℝ E F)) '' clarkeSubdiff ψ p.1 := by
  ext ξ
  simp only [clarkeSubdiff, mem_ofPred_eq, mem_image, clarkeDeriv_comp_fst]
  constructor
  · intro h
    have h0 : ∀ w : F, ξ (0, w) = 0 := fun w ↦ by
      have h1 := h (0, w)
      have h2 := h (0, -w)
      simp only [clarkeDeriv_zero, EReal.coe_nonpos] at h1 h2
      have : ξ (0, -w) = -ξ (0, w) := by rw [← map_neg]; simp
      linarith
    refine ⟨ξ.comp (ContinuousLinearMap.inl ℝ E F), fun w ↦ by simpa using h (w, 0), ?_⟩
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : ξ v = ξ (v.1, 0) + ξ (0, v.2) := by rw [← map_add]; simp
    simp [hv, h0]
  · rintro ⟨u, hu, rfl⟩ v
    simpa using hu v.1

omit [NormedSpace ℝ E] in
theorem lipschitzOnWith_neg {f : E → ℝ} {U : Set E} {K : ℝ≥0} (hf : LipschitzOnWith K f U) :
    LipschitzOnWith K (fun x ↦ -f x) U :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
    rw [dist_neg_neg]
    exact hf.dist_le_mul x hx y hy

variable [FiniteDimensional ℝ E]

/-- `∂̄(f + g)(x₀) = ∇f(x₀) + ∂̄g(x₀)` if `f` is strictly differentiable at `x₀` and `g` is
Lipschitz around `x₀`. -/
theorem clarkeSubdiff_add_eq_of_hasStrictFDerivAt {f g : E → ℝ} {f' : StrongDual ℝ E} {x₀ : E}
    (hf : HasStrictFDerivAt f f' x₀) {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 x₀)
    (hg : LipschitzOnWith L g U) :
    clarkeSubdiff (fun x ↦ f x + g x) x₀ = {f'} + clarkeSubdiff g x₀ := by
  obtain ⟨K, V, hV, hK⟩ := hf.exists_lipschitzOnWith
  refine subset_antisymm ?_ ?_
  · have := VariationalAnalysis.clarkeSubdiff_add_subset hV hK hU hg
    rwa [VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt hf] at this
  · rintro x ⟨a', ha', ξ, hξ, hx⟩
    rw [mem_singleton_iff] at ha'
    simp only at hx
    rw [← hx, ha']
    have hfg : LipschitzOnWith (K + L) (fun x ↦ f x + g x) (V ∩ U) :=
      (hK.mono inter_subset_left).add (hg.mono inter_subset_right)
    have h := VariationalAnalysis.clarkeSubdiff_add_subset (inter_mem hV hU) hfg hV
      (lipschitzOnWith_neg hK)
    have hg' : (fun x ↦ (f x + g x) + -f x) = g := by funext x; ring
    rw [hg', VariationalAnalysis.clarkeSubdiff_neg,
      VariationalAnalysis.clarkeSubdiff_eq_singleton_of_hasStrictFDerivAt hf, neg_singleton] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h hξ
    rw [mem_singleton_iff] at hb
    simp only at hab
    subst hb
    have : f' + ξ = a := by rw [← hab]; abel
    rw [this]
    exact ha

/-- `∂̄(φ - μ ∘ fst)(p) = ∇φ(p) - ∂̄μ(p.1) × {0}` for `φ` strictly differentiable at `p` and `μ`
Lipschitz around `p.1`. -/
theorem clarkeSubdiff_sub_comp_fst [FiniteDimensional ℝ F] {φ : E × F → ℝ}
    {φ' : StrongDual ℝ (E × F)} {p : E × F} (hφ : HasStrictFDerivAt φ φ' p) {μ : E → ℝ}
    {U : Set E} {L : ℝ≥0} (hU : U ∈ 𝓝 p.1) (hL : LipschitzOnWith L μ U) :
    clarkeSubdiff (fun q ↦ φ q - μ q.1) p =
      {φ'} - (fun u : StrongDual ℝ E ↦ u.comp (ContinuousLinearMap.fst ℝ E F)) ''
        clarkeSubdiff μ p.1 := by
  have hU' : Prod.fst ⁻¹' U ∈ 𝓝 p := continuous_fst.continuousAt.preimage_mem_nhds hU
  have hL' : LipschitzOnWith (L * 1) (fun q : E × F ↦ μ q.1) (Prod.fst ⁻¹' U) :=
    hL.comp LipschitzWith.prod_fst.lipschitzOnWith fun _ hq ↦ hq
  rw [show (fun q ↦ φ q - μ q.1) = fun q ↦ φ q + -μ q.1 from funext fun q ↦ sub_eq_add_neg _ _,
    clarkeSubdiff_add_eq_of_hasStrictFDerivAt hφ hU' (lipschitzOnWith_neg hL'),
    VariationalAnalysis.clarkeSubdiff_neg, clarkeSubdiff_comp_fst, sub_eq_add_neg]

end Clarke

/-! ### Motzkin's theorem of the alternative -/

section Motzkin

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {I K : Type*} [Fintype I] [Fintype K]

/-- Motzkin's theorem of the alternative: if the system `⟨ηᵢ, d⟩ < 0` (`i ∈ A`), `⟨ξₖ, d⟩ = 0`
has no solution, then `∑ λᵢ ηᵢ + ∑ μₖ ξₖ = 0` for some `λ ≥ 0`, `λ ≠ 0`, supported on `A`. -/
theorem exists_multipliers_of_not_exists_direction (η : I → StrongDual ℝ X)
    (ξ : K → StrongDual ℝ X) (A : Set I)
    (h : ¬ ∃ d : X, (∀ i ∈ A, η i d < 0) ∧ ∀ k, ξ k d = 0) :
    ∃ lam : I → ℝ, ∃ μ : K → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i ∉ A, lam i = 0) ∧ lam ≠ 0 ∧
      ∑ i, lam i • η i + ∑ k, μ k • ξ k = 0 := by
  classical
  rcases A.eq_empty_or_nonempty with hA | ⟨i₀, hi₀⟩
  · exact absurd ⟨0, by simp [hA], by simp⟩ h
  by_contra hne
  push Not at hne
  set Δ : Set (I → ℝ) := {lam | (∀ i, 0 ≤ lam i) ∧ (∀ i ∉ A, lam i = 0) ∧ ∑ i, lam i = 1}
  set T : (I → ℝ) → StrongDual ℝ X := fun lam ↦ ∑ i, lam i • η i
  set S₂ : Submodule ℝ (StrongDual ℝ X) := Submodule.span ℝ (range ξ)
  set S : Set (StrongDual ℝ X) := T '' Δ + (S₂ : Set (StrongDual ℝ X))
  -- `Δ` is a compact convex set and `S` is closed and convex
  have hΔc : Convex ℝ Δ := by
    rintro a ⟨ha0, haA, ha1⟩ b ⟨hb0, hbA, hb1⟩ s t hs ht hst
    refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := ha0 i
      have := hb0 i
      positivity
    · simp [haA i hi, hbA i hi]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha1, hb1, mul_one, hst]
  have hΔcl : IsClosed Δ := by
    have : Δ = (⋂ i, {lam : I → ℝ | 0 ≤ lam i}) ∩ (⋂ i ∈ Aᶜ, {lam : I → ℝ | lam i = 0}) ∩
        {lam | ∑ i, lam i = 1} := by
      ext lam
      simp [Δ, and_assoc]
    rw [this]
    exact ((isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_biInter fun i _ ↦ isClosed_eq (continuous_apply i) continuous_const)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hΔk : IsCompact Δ :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hΔcl
      fun lam ⟨h0, _, h1⟩ i _ ↦
        ⟨h0 i, h1 ▸ Finset.single_le_sum (fun j _ ↦ h0 j) (Finset.mem_univ i)⟩
  have hTc : Continuous T := continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hTl : IsLinearMap ℝ T :=
    ⟨fun a b ↦ by simp [T, add_smul, Finset.sum_add_distrib],
      fun c a ↦ by simp [T, Finset.smul_sum, smul_smul]⟩
  have hSconv : Convex ℝ S := (hΔc.is_linear_image hTl).add S₂.convex
  have hScl : IsClosed S := S₂.closed_of_finiteDimensional.add_left_of_isCompact (hΔk.image hTc)
  -- `0 ∉ S`
  have h0 : (0 : StrongDual ℝ X) ∉ S := by
    rintro ⟨_, ⟨lam, ⟨hl0, hlA, hl1⟩, rfl⟩, b, hb, hsum⟩
    obtain ⟨μ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hb
    exact hne lam μ hl0 hlA (fun hl ↦ by simp [hl] at hl1) hsum
  -- separation
  obtain ⟨f, u, hf0, hfS⟩ := geometric_hahn_banach_point_closed hSconv hScl h0
  obtain ⟨d, rfl⟩ := VariationalAnalysis.inclusionInDoubleDual_surjective f
  simp only [map_zero, NormedSpace.dual_def] at hf0 hfS
  have hmem : ∀ lam ∈ Δ, ∀ μ : K → ℝ, T lam + ∑ k, μ k • ξ k ∈ S := fun lam hl μ ↦
    ⟨T lam, ⟨lam, hl, rfl⟩, _, (Submodule.mem_span_range_iff_exists_fun ℝ).2 ⟨μ, rfl⟩, rfl⟩
  have hsingle : ∀ i ∈ A, (Pi.single i 1 : I → ℝ) ∈ Δ := fun i hi ↦
    ⟨fun j ↦ by rw [Pi.single_apply]; split_ifs <;> norm_num,
      fun j hj ↦ by rw [Pi.single_apply, if_neg (fun h : j = i ↦ hj (h ▸ hi))], by simp⟩
  have hTs : ∀ i, T (Pi.single i 1) = η i := fun i ↦ by
    simp [T]
  have hη : ∀ i ∈ A, u < η i d := fun i hi ↦ by
    simpa [hTs] using hfS _ (hmem _ (hsingle i hi) 0)
  have hξ : ∀ k, ξ k d = 0 := fun k ↦ by
    by_contra hk
    have key := hfS _ (hmem _ (hsingle i₀ hi₀) (Pi.single k ((u - η i₀ d - 1) / ξ k d)))
    simp only [hTs, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, add_apply, smul_apply,
      smul_eq_mul] at key
    rw [div_mul_cancel₀ _ hk] at key
    linarith
  exact h ⟨-d, fun i hi ↦ by simp only [map_neg]; linarith [hη i hi], fun k ↦ by simp [hξ k]⟩

end Motzkin

/-! ### Constraint qualifications and abnormal multipliers -/

section Program

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {I K : Type*} [Fintype I] [Fintype K]

section Definitions

variable (G : I → X → ℝ) (H : K → X → ℝ)

/-- The nonsmooth Mangasarian–Fromovitz constraint qualification (NMFCQ) for (5.37) at `z`
[Dempe 2002, p. 163]: for all `ηᵢ ∈ ∂̄Gᵢ(z)` (`Gᵢ(z) = 0`) and `ξₖ ∈ ∂̄Hₖ(z)`, the `ξₖ` are linearly
independent and some `d` has `⟨ηᵢ, d⟩ < 0` for the active `i` and `⟨ξₖ, d⟩ = 0` for all `k`. -/
def NonsmoothMFCQ (z : X) : Prop :=
  ∀ η : I → StrongDual ℝ X, (∀ i, G i z = 0 → η i ∈ clarkeSubdiff (G i) z) →
    ∀ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z) →
      LinearIndependent ℝ ξ ∧ ∃ d : X, (∀ i, G i z = 0 → η i d < 0) ∧ ∀ k, ξ k d = 0

/-- The nonsmooth linear independence constraint qualification (NLICQ) for (5.37) at `z`
[Dempe 2002, p. 163]: for all `ηᵢ ∈ ∂̄Gᵢ(z)` (`Gᵢ(z) = 0`) and `ξₖ ∈ ∂̄Hₖ(z)`, the vectors
`{ηᵢ | Gᵢ(z) = 0} ∪ {ξₖ}` are linearly independent. -/
def NonsmoothLICQ (z : X) : Prop :=
  ∀ η : I → StrongDual ℝ X, (∀ i, G i z = 0 → η i ∈ clarkeSubdiff (G i) z) →
    ∀ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z) →
      LinearIndependent ℝ (Sum.elim (fun i : {i // G i z = 0} ↦ η i) ξ)

/-- The set `Λ⁰(z)` of abnormal multipliers (5.39) of [Dempe 2002]: `λ ≥ 0`, `λᵀG(z) = 0` and
`0 ∈ λᵀ∂̄G(z) + μᵀ∂̄H(z)`. -/
def abnormalMultipliers (z : X) : Set ((I → ℝ) × (K → ℝ)) :=
  {m | (∀ i, 0 ≤ m.1 i) ∧ (∀ i, m.1 i * G i z = 0) ∧
    ∃ η : I → StrongDual ℝ X, (∀ i, η i ∈ clarkeSubdiff (G i) z) ∧
    ∃ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z) ∧
      ∑ i, m.1 i • η i + ∑ k, m.2 k • ξ k = 0}

end Definitions

variable {G : I → X → ℝ} {H : K → X → ℝ} {z : X}

/-- Thm. 5.18 of [Dempe 2002]: if all generalized gradients of the constraints at `z` are nonempty
(e.g. for Lipschitz data, `VariationalAnalysis.clarkeSubdiff_nonempty`), then (NMFCQ) holds at
`z` iff `Λ⁰(z) = {0}`. -/
theorem nonsmoothMFCQ_iff_abnormalMultipliers_eq [FiniteDimensional ℝ X]
    (hG : ∀ i, (clarkeSubdiff (G i) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    NonsmoothMFCQ G H z ↔ abnormalMultipliers G H z = {0} := by
  classical
  constructor
  · intro hcq
    ext ⟨lam, μ⟩
    simp only [mem_singleton_iff, Prod.mk_eq_zero]
    constructor
    · rintro ⟨hl0, hcs, η, hη, ξ, hξ, hsum⟩
      simp only at hl0 hcs hsum
      obtain ⟨hli, d, hd, hξd⟩ := hcq η (fun i _ ↦ hη i) ξ hξ
      have hsumd := congrArg (fun T : StrongDual ℝ X ↦ T d) hsum
      simp only [add_apply, sum_apply,
        smul_apply, smul_eq_mul, hξd, mul_zero, Finset.sum_const_zero,
        add_zero, zero_apply] at hsumd
      have hterm : ∀ i, lam i * η i d ≤ 0 := fun i ↦ by
        rcases mul_eq_zero.1 (hcs i) with h | h
        · simp [h]
        · exact mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hd i h).le
      have hl : lam = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hterm i).1 hsumd i (Finset.mem_univ _)
        rcases mul_eq_zero.1 (hcs i) with h | h
        · exact h
        · exact (mul_eq_zero.1 this).resolve_right (hd i h).ne
      subst hl
      refine ⟨rfl, funext fun k ↦ Fintype.linearIndependent_iff.1 hli μ ?_ k⟩
      simpa using hsum
    · rintro ⟨rfl, rfl⟩
      choose η hη using hG
      choose ξ hξ using hH
      exact ⟨fun _ ↦ le_rfl, fun _ ↦ zero_mul _, η, hη, ξ, hξ, by simp⟩
  · intro hΛ η hη ξ hξ
    choose e he using hG
    set η' : I → StrongDual ℝ X := fun i ↦ if G i z = 0 then η i else e i
    have hη' : ∀ i, η' i ∈ clarkeSubdiff (G i) z := fun i ↦ by
      by_cases h : G i z = 0
      · simpa [η', h] using hη i h
      · simpa [η', h] using he i
    have hmem : ∀ (lam : I → ℝ) (μ : K → ℝ), (∀ i, 0 ≤ lam i) → (∀ i, lam i * G i z = 0) →
        ∑ i, lam i • η' i + ∑ k, μ k • ξ k = 0 → lam = 0 ∧ μ = 0 := fun lam μ h0 hcs hs ↦ by
      have : (lam, μ) ∈ abnormalMultipliers G H z := ⟨h0, hcs, η', hη', ξ, hξ, hs⟩
      rwa [hΛ, mem_singleton_iff, Prod.mk_eq_zero] at this
    refine ⟨Fintype.linearIndependent_iff.2 fun μ hμ k ↦ ?_, ?_⟩
    · have := (hmem 0 μ (fun _ ↦ le_rfl) (fun _ ↦ zero_mul _) (by simpa using hμ)).2
      exact congrFun this k
    · by_contra hd
      obtain ⟨lam, μ, hl0, hlA, hlne, hs⟩ :=
        exists_multipliers_of_not_exists_direction η' ξ {i | G i z = 0} (by
          rintro ⟨d, hd1, hd2⟩
          refine hd ⟨d, fun i hi ↦ ?_, hd2⟩
          have := hd1 i hi
          simpa [η', hi] using this)
      refine hlne (hmem lam μ hl0 (fun i ↦ ?_) hs).1
      by_cases h : G i z = 0
      · simp [h]
      · simp [hlA i h]

/-- (NLICQ) implies (NMFCQ) [Dempe 2002, p. 164]. -/
theorem NonsmoothLICQ.nonsmoothMFCQ [FiniteDimensional ℝ X] (hcq : NonsmoothLICQ G H z)
    (hG : ∀ i, (clarkeSubdiff (G i) z).Nonempty) (hH : ∀ k, (clarkeSubdiff (H k) z).Nonempty) :
    NonsmoothMFCQ G H z := by
  classical
  refine (nonsmoothMFCQ_iff_abnormalMultipliers_eq hG hH).2 ?_
  ext ⟨lam, μ⟩
  simp only [mem_singleton_iff, Prod.mk_eq_zero]
  constructor
  · rintro ⟨-, hcs, η, hη, ξ, hξ, hsum⟩
    simp only at hcs hsum
    have hli := Fintype.linearIndependent_iff.1 (hcq η (fun i _ ↦ hη i) ξ hξ)
      (Sum.elim (fun i : {i // G i z = 0} ↦ lam i) μ) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← hsum, ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ G i z = 0)
          (fun i ↦ lam i • η i)]
        congr 1
        refine (add_eq_left.2 (Finset.sum_eq_zero fun i _ ↦ ?_)).symm
        rw [(mul_eq_zero.1 (hcs i)).resolve_right i.2, zero_smul])
    refine ⟨funext fun i ↦ ?_, funext fun k ↦ hli (Sum.inr k)⟩
    by_cases h : G i z = 0
    · exact hli (Sum.inl ⟨i, h⟩)
    · exact (mul_eq_zero.1 (hcs i)).resolve_right h
  · rintro ⟨rfl, rfl⟩
    choose η hη using hG
    choose ξ hξ using hH
    exact ⟨fun _ ↦ le_rfl, fun _ ↦ zero_mul _, η, hη, ξ, hξ, by simp⟩

/-! ### Multiplier rules -/

variable [FiniteDimensional ℝ X]

/-- The Lagrange multiplier rule for Lipschitz programs [Clarke 1983, Thm. 6.1.1], used in the
proof of Thm. 5.20 of [Dempe 2002]: at a local minimizer `z₀` of (5.37) with data Lipschitz around
`z₀`, there are `κ₀ ∈ {0, 1}`, `λ ≥ 0` with `λᵀG(z₀) = 0` and `μ`, not all zero, such that
`0 ∈ κ₀ ∂̄f(z₀) + λᵀ∂̄G(z₀) + μᵀ∂̄H(z₀)`. Derived from Thm. 6.5(ii) of [Mordukhovich 2018]
(limiting subgradients) with `∂f ⊆ ∂̄f` and `∂(-h) ⊆ -∂̄h`. -/
theorem exists_fritzJohn_clarke {f : X → ℝ} {z₀ : X}
    (hz₀ : (∀ i, G i z₀ ≤ 0) ∧ ∀ k, H k z₀ = 0)
    (hmin : IsLocalMinOn f {z | (∀ i, G i z ≤ 0) ∧ ∀ k, H k z = 0} z₀)
    (hf : ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L f U)
    (hG : ∀ i, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (G i) U)
    (hH : ∀ k, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (H k) U) :
    ∃ κ₀ : ℝ, ∃ lam : I → ℝ, ∃ μ : K → ℝ, (κ₀ = 0 ∨ κ₀ = 1) ∧ (∀ i, 0 ≤ lam i) ∧
      (∀ i, lam i * G i z₀ = 0) ∧ (κ₀, lam, μ) ≠ 0 ∧
      ∃ ζ ∈ clarkeSubdiff f z₀, ∃ η : I → StrongDual ℝ X, (∀ i, η i ∈ clarkeSubdiff (G i) z₀) ∧
      ∃ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z₀) ∧
        κ₀ • ζ + ∑ i, lam i • η i + ∑ k, μ k • ξ k = 0 := by
  classical
  -- (5.37) as a problem (6.11) with data indexed by `Option (I ⊕ K)`
  let Φ : Option (I ⊕ K) → X → ℝ := fun k ↦ k.elim f (Sum.elim G H)
  let Q : Set (Option (I ⊕ K)) := range fun k ↦ some (Sum.inr k)
  have hk₀ : (none : Option (I ⊕ K)) ∉ Q := by rintro ⟨k, hk⟩; cases hk
  have hinl : ∀ i, (some (Sum.inl i) : Option (I ⊕ K)) ∉ Q := by rintro i ⟨k, hk⟩; cases hk
  have hfeas : VariationalAnalysis.feasibleSet Q none univ Φ =
      {z | (∀ i, G i z ≤ 0) ∧ ∀ k, H k z = 0} := by
    ext z
    simp only [VariationalAnalysis.feasibleSet, mem_ofPred_eq, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i ↦ h1 (some (Sum.inl i)) (by simp) (hinl i), fun k ↦ h2 _ ⟨k, rfl⟩⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rintro (_ | i | k) hk hkQ
        · exact absurd rfl hk
        · exact h1 i
        · exact absurd ⟨k, rfl⟩ hkQ
      · rintro _ ⟨k, rfl⟩
        exact h2 k
  obtain ⟨U, hU, L, hL⟩ := VariationalAnalysis.exists_common_lipschitzOnWith (Φ := Φ) (by
    rintro (_ | i | k)
    exacts [hf, hG i, hH k])
  obtain ⟨lam, hne, hnn, hcs, h0⟩ :=
    VariationalAnalysis.exists_multipliers_zero_mem_sum_separateSubdiff (Q := Q) (k₀ := none)
      (Ω := univ) (φ := Φ) hk₀ (by rw [hfeas]; exact hz₀) (by rw [hfeas]; exact hmin) hU hL
      ⟨1, one_pos, by simpa using Metric.isClosed_closedBall⟩
  rw [VariationalAnalysis.normalCone_of_mem_interior (Ω := univ) (x₀ := z₀) (by simp)] at h0
  obtain ⟨a, ha, b, hb, hab⟩ := h0
  rw [mem_singleton_iff] at hb
  simp only [hb, add_zero] at hab
  subst hab
  rw [mem_fintype_sum] at ha
  obtain ⟨v, hv, hvsum⟩ := ha
  choose w hw hwv using fun k ↦ mem_smul_set.1 (hv k)
  -- generalized gradients with signs `±1`
  have hsel : ∀ k, ∃ s : ℝ, ∃ e ∈ clarkeSubdiff (Φ k) z₀, (s = 1 ∨ (k ∈ Q ∧ s = -1)) ∧
      w k = s • e := fun k ↦ by
    rcases hw k with h | ⟨hkQ, h⟩
    · exact ⟨1, w k, VariationalAnalysis.subdiff_subset_clarkeSubdiff h, Or.inl rfl,
        (one_smul _ _).symm⟩
    · exact ⟨-1, -w k, VariationalAnalysis.subdiff_neg_subset_neg_clarkeSubdiff h,
        Or.inr ⟨hkQ, rfl⟩, by simp⟩
  choose s e he hs hwe using hsel
  have hs1 : ∀ k, k ∉ Q → s k = 1 := fun k hk ↦ (hs k).resolve_right fun h ↦ hk h.1
  have hs0 : ∀ k, s k ≠ 0 := fun k ↦ by rcases hs k with h | ⟨-, h⟩ <;> rw [h] <;> norm_num
  have hsum : lam none • e none + ∑ i, lam (some (Sum.inl i)) • e (some (Sum.inl i)) +
      ∑ k, (lam (some (Sum.inr k)) * s (some (Sum.inr k))) • e (some (Sum.inr k)) = 0 := by
    have := hvsum
    simp only [← hwv, hwe, smul_smul, Fintype.sum_option, Fintype.sum_sum_type, hs1 none hk₀,
      fun i ↦ hs1 (some (Sum.inl i)) (hinl i), mul_one] at this
    rw [← add_assoc] at this
    exact this
  -- normalization `κ₀ ∈ {0, 1}`
  set c : ℝ := if lam none = 0 then 1 else (lam none)⁻¹
  have hc : c ≠ 0 := by
    simp only [c]
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero h
  have heN : e none ∈ clarkeSubdiff f z₀ := he none
  have heI : ∀ i, e (some (Sum.inl i)) ∈ clarkeSubdiff (G i) z₀ := fun i ↦ he (some (Sum.inl i))
  have heK : ∀ k, e (some (Sum.inr k)) ∈ clarkeSubdiff (H k) z₀ := fun k ↦ he (some (Sum.inr k))
  refine ⟨c * lam none, fun i ↦ c * lam (some (Sum.inl i)),
    fun k ↦ c * (lam (some (Sum.inr k)) * s (some (Sum.inr k))), ?_,
    fun i ↦ mul_nonneg ?_ (hnn _), fun i ↦ ?_, ?_, e none, heN, fun i ↦ e (some (Sum.inl i)),
    heI, fun k ↦ e (some (Sum.inr k)), heK, ?_⟩
  · simp only [c]
    split_ifs with h
    · exact Or.inl (by rw [h, mul_zero])
    · exact Or.inr (inv_mul_cancel₀ h)
  · simp only [c]
    split_ifs
    · exact zero_le_one
    · exact inv_nonneg.2 (hnn none)
  · rw [mul_assoc, show lam (some (Sum.inl i)) * G i z₀ = 0 from
      hcs (some (Sum.inl i)) (Option.some_ne_none _) (hinl i), mul_zero]
  · intro h0
    simp only [Prod.mk_eq_zero] at h0
    obtain ⟨h1, h2, h3⟩ := h0
    apply hne
    funext k
    rcases k with _ | i | k
    · exact (mul_eq_zero.1 h1).resolve_left hc
    · exact (mul_eq_zero.1 (congrFun h2 i)).resolve_left hc
    · exact ((mul_eq_zero.1 ((mul_eq_zero.1 (congrFun h3 k)).resolve_left hc)).resolve_right
        (hs0 _))
  · have := congrArg (c • ·) hsum
    simp only [smul_add, Finset.smul_sum, smul_smul, smul_zero] at this
    exact this

/-- The KKT conditions for Lipschitz programs: if `Λ⁰(z₀) = {0}`, the leading multiplier in
`exists_fritzJohn_clarke` is `1`, i.e. the set `Λ¹(z₀)` (5.38) of regular multipliers is
nonempty. -/
theorem exists_kkt_clarke_of_abnormalMultipliers_eq {f : X → ℝ} {z₀ : X}
    (hz₀ : (∀ i, G i z₀ ≤ 0) ∧ ∀ k, H k z₀ = 0)
    (hmin : IsLocalMinOn f {z | (∀ i, G i z ≤ 0) ∧ ∀ k, H k z = 0} z₀)
    (hf : ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L f U)
    (hG : ∀ i, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (G i) U)
    (hH : ∀ k, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (H k) U)
    (hΛ : abnormalMultipliers G H z₀ = {0}) :
    ∃ lam : I → ℝ, ∃ μ : K → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i z₀ = 0) ∧
      ∃ ζ ∈ clarkeSubdiff f z₀, ∃ η : I → StrongDual ℝ X, (∀ i, η i ∈ clarkeSubdiff (G i) z₀) ∧
      ∃ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z₀) ∧
        ζ + ∑ i, lam i • η i + ∑ k, μ k • ξ k = 0 := by
  obtain ⟨κ₀, lam, μ, hκ₀ | hκ₀, hl0, hcs, hne, ζ, hζ, η, hη, ξ, hξ, hsum⟩ :=
    exists_fritzJohn_clarke hz₀ hmin hf hG hH
  · subst hκ₀
    have : (lam, μ) ∈ abnormalMultipliers G H z₀ :=
      ⟨hl0, hcs, η, hη, ξ, hξ, by simpa using hsum⟩
    rw [hΛ, mem_singleton_iff, Prod.mk_eq_zero] at this
    exact absurd (by rw [this.1, this.2]; rfl) hne
  · subst hκ₀
    exact ⟨lam, μ, hl0, hcs, ζ, hζ, η, hη, ξ, hξ, by simpa using hsum⟩

/-- The KKT conditions for Lipschitz programs under (NMFCQ) (Thm. 5.18 and
`exists_kkt_clarke_of_abnormalMultipliers_eq`). -/
theorem exists_kkt_clarke_of_nonsmoothMFCQ {f : X → ℝ} {z₀ : X}
    (hz₀ : (∀ i, G i z₀ ≤ 0) ∧ ∀ k, H k z₀ = 0)
    (hmin : IsLocalMinOn f {z | (∀ i, G i z ≤ 0) ∧ ∀ k, H k z = 0} z₀)
    (hf : ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L f U)
    (hG : ∀ i, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (G i) U)
    (hH : ∀ k, ∃ L : ℝ≥0, ∃ U ∈ 𝓝 z₀, LipschitzOnWith L (H k) U)
    (hcq : NonsmoothMFCQ G H z₀) :
    ∃ lam : I → ℝ, ∃ μ : K → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i z₀ = 0) ∧
      ∃ ζ ∈ clarkeSubdiff f z₀, ∃ η : I → StrongDual ℝ X, (∀ i, η i ∈ clarkeSubdiff (G i) z₀) ∧
      ∃ ξ : K → StrongDual ℝ X, (∀ k, ξ k ∈ clarkeSubdiff (H k) z₀) ∧
        ζ + ∑ i, lam i • η i + ∑ k, μ k • ξ k = 0 :=
  exists_kkt_clarke_of_abnormalMultipliers_eq hz₀ hmin hf hG hH
    ((nonsmoothMFCQ_iff_abnormalMultipliers_eq
      (fun i ↦ let ⟨_, _, hU, hL⟩ := hG i; VariationalAnalysis.clarkeSubdiff_nonempty hU hL)
      (fun k ↦ let ⟨_, _, hU, hL⟩ := hH k; VariationalAnalysis.clarkeSubdiff_nonempty hU hL)).1 hcq)

end Program

end Bilevel
