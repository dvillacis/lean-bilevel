/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.ValueFunctionDirectional

/-!
# Strong stability of local solutions

Thm. 4.4 of [Dempe 2002] (Kojima's theorem): if `ȳ` is a KKT point of the follower's problem
`min_y {φ(x̄, y) | gᵢ(x̄, y) ≤ 0}` at which (MFCQ) and the strong second-order sufficient
condition (SSOC) hold, then `ȳ` is *strongly stable*: for `x` near `x̄` the problem has a unique
local solution `y(x)` near `ȳ`, and `x ↦ y(x)` is continuous.

## Main results

* `LowerSSOC`: the strong second-order sufficient condition (SSOC) [Dempe 2002, p. 74], with the
  `y`-Hessian `lowerHessian` of the follower's Lagrangian `lowerLagrangian`.
* `IsLowerStronglyStable`: strong stability [Dempe 2002, Def. 4.4].
* `exists_pos_lowerLagrangian_expansion`: a second-order expansion of the Lagrangian, uniform in
  `x`, the base point and the multiplier; `exists_pos_lowerLagrangian_expansion_uniform`: the same
  for all multipliers, with the Hessian at the same multiplier (`lowerHessian_eq_sum`).
* `exists_pos_lowerSSOC_of_isCompact`: (SSOC) in quantitative form, uniform over a compact set of
  multipliers.
* `exists_pos_lt_of_lowerSSOC`: (SSOC) makes a KKT point a strict local solution.
* `exists_pos_eq_of_isLowerKKT`: under (SSOC), KKT points near `(x̄, ȳ)` with multipliers near
  `λ⁰` are unique (no constraint qualification needed).
* `exists_pos_eq_of_isLowerKKT_of_lowerPLI`: under (MFCQ) and (SSOC), KKT points near `(x̄, ȳ)`
  with multipliers near `Λ(x̄, ȳ)` are unique.
* `isLowerStronglyStable_of_lowerPLI`, `isLowerStronglyStable_of_isLocalMinOn_of_lowerPLI`:
  Thm. 4.4; `isLowerStronglyStable`, `isLowerStronglyStable_of_isLocalMinOn`: its (LICQ) case.

## Differences from the book

* The book proves Thm. 4.4 (pp. 101–104) only under (LICQ), which makes the multiplier unique,
  and refers to Kojima's proof by degree theory for (MFCQ). We prove the (MFCQ) case without
  degree theory, with (MFCQ) in its dual form (PLI). The only new ingredient is the uniqueness of
  nearby KKT points (`exists_pos_eq_of_isLowerKKT_of_lowerPLI`): if `(y¹, λ¹)` and `(y², λ²)` are
  KKT pairs at `x` with `λʲ` near `μʲ ∈ Λ(x̄, ȳ)`, adding the two second-order expansions gives
  `∇²_yy L(x̄, ȳ, μ)(v, v) ≤ o(‖v‖²)` for `v = y² - y¹` and the midpoint
  `μ = (μ¹ + μ²) / 2 ∈ Λ(x̄, ȳ)`, the same identity shows that `v` is almost critical for `μ`,
  and (SSOC), uniform on the compact set `Λ(x̄, ȳ)`, forces `v = 0`.
* The data are `C²` on all of `E × F` and there are no equality constraints.
* Existence uses the problem restricted to a closed ball `B̄(ȳ, ρ)` as in (4.29); its solutions
  stay in the open ball by the Berge argument
  (`upperHemicontinuousAt_solutionMap_of_upperSemicontinuousAt`), where only lower
  semicontinuity of the feasible set at `ȳ` (not on the boundary of the ball) is needed.
* Continuity of the solution function is obtained from closedness of the KKT relation and the
  uniqueness of nearby KKT points, rather than from a second application of the Berge argument.
-/

open Filter Topology Set
open VariationalAnalysis (graph lowerFeasible marginal)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι]

/-! ### Strict differentiability in `δ`-form -/

/-- Strict differentiability at `p₀`, in `ε`–`δ` form. -/
theorem exists_pos_norm_sub_le_of_hasStrictFDerivAt {X G : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup G] [NormedSpace ℝ G] {u : X → G} {u' : X →L[ℝ] G}
    {p₀ : X} (h : HasStrictFDerivAt u u' p₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q, dist p p₀ < δ → dist q p₀ < δ → ‖u p - u q - u' (p - q)‖ ≤ ε * ‖p - q‖ := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 ((hasStrictFDerivAt_iff_isLittleO.1 h).def hε)
  exact ⟨δ, hδ, fun p q hp hq ↦ h (y := (p, q)) (by rw [Prod.dist_eq]; exact max_lt hp hq)⟩

/-! ### The follower's Lagrangian and its `y`-Hessian -/

section Lagrangian

variable (φ : E × F → ℝ) (g : ι → E × F → ℝ)

/-- The follower's Lagrangian `L(x, ·, λ) = φ(x, ·) + ∑ λᵢ gᵢ(x, ·)` as a function of `y`. -/
def lowerLagrangian (x : E) (lam : ι → ℝ) (y : F) : ℝ :=
  φ (x, y) + ∑ i, lam i * g i (x, y)

/-- The `y`-gradient `∇_y L(x, y, λ)` of the follower's Lagrangian, as a function of `(x, y)`. -/
noncomputable def lowerLagrangianDeriv (lam : ι → ℝ) (p : E × F) : StrongDual ℝ F :=
  (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ E F) +
    ∑ i, lam i • (fderiv ℝ (g i) p).comp (ContinuousLinearMap.inr ℝ E F)

/-- The `y`-Hessian `∇²_yy L(x̄, ȳ, λ)` of the follower's Lagrangian. -/
noncomputable def lowerHessian (x₀ : E) (y₀ : F) (lam : ι → ℝ) : F →L[ℝ] StrongDual ℝ F :=
  (fderiv ℝ (lowerLagrangianDeriv φ g lam) (x₀, y₀)).comp (ContinuousLinearMap.inr ℝ E F)

/-- The strong second-order sufficient condition (SSOC) [Dempe 2002, p. 74] for the follower's
problem at `(x̄, ȳ)`: `dᵀ ∇²_yy L(x̄, ȳ, λ) d > 0` for every multiplier `λ ∈ Λ(x̄, ȳ)` and every
`d ≠ 0` with `∇_y gᵢ(x̄, ȳ) d = 0` whenever `λᵢ > 0`. -/
def LowerSSOC (x₀ : E) (y₀ : F) : Prop :=
  ∀ lam ∈ lowerMultipliers φ g x₀ y₀, ∀ d : F, d ≠ 0 →
    (∀ i, 0 < lam i → fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ d = 0) →
      0 < lowerHessian φ g x₀ y₀ lam d d

/-- Strong stability of a local solution `ȳ` of the follower's problem at `x̄` (Kojima; [Dempe
2002, Def. 4.4]): there are `δ > 0`, a neighborhood `U` of `x̄` and a function `y(·)`, continuous
on `U` with `y(x̄) = ȳ`, such that for every `x ∈ U`, `y(x)` is the unique local solution of the
follower's problem at `x` in the ball `B(ȳ, δ)`. -/
def IsLowerStronglyStable (x₀ : E) (y₀ : F) : Prop :=
  ∃ δ > 0, ∃ U ∈ 𝓝 x₀, ∃ s : E → F, s x₀ = y₀ ∧ ContinuousOn s U ∧ ∀ x ∈ U,
    s x ∈ Metric.ball y₀ δ ∧ s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x) ∧
      ∀ z ∈ Metric.ball y₀ δ, z ∈ lowerFeasible g x →
        IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) z → z = s x

end Lagrangian

variable {φ : E × F → ℝ} {g : ι → E × F → ℝ}

theorem hasFDerivAt_lowerLagrangian {x : E} {y : F} (lam : ι → ℝ)
    (hφ : DifferentiableAt ℝ φ (x, y)) (hg : ∀ i, DifferentiableAt ℝ (g i) (x, y)) :
    HasFDerivAt (lowerLagrangian φ g x lam) (lowerLagrangianDeriv φ g lam (x, y)) y := by
  have h1 := hφ.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦
    ((hg i).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).const_mul (lam i)
  exact h1.add h2

theorem lowerLagrangianDeriv_eq_zero {x : E} {y : F} {lam : ι → ℝ}
    (hφ : DifferentiableAt ℝ φ (x, y)) (hg : ∀ i, DifferentiableAt ℝ (g i) (x, y))
    (h : IsLowerKKT φ g x y lam) : lowerLagrangianDeriv φ g lam (x, y) = 0 := by
  have h4 := h.2.2.2
  rw [fderiv_section hφ] at h4
  simp only [fderiv_section (hg _)] at h4
  exact h4

/-- `∇_y gᵢ(x, y)` as the partial derivative of `gᵢ`. -/
theorem fderiv_section_apply {u : E × F → ℝ} {x : E} {y : F} (h : DifferentiableAt ℝ u (x, y))
    (d : F) : fderiv ℝ (fun z ↦ u (x, z)) y d = fderiv ℝ u (x, y) (0, d) := by
  rw [fderiv_section h]
  rfl

theorem fderiv_apply_sub_section {u : E × F → ℝ} {x₀ : E} {y₀ : F}
    (h : DifferentiableAt ℝ u (x₀, y₀)) (x : E) (y₁ y₂ : F) :
    fderiv ℝ u (x₀, y₀) ((x, y₂) - (x, y₁)) = fderiv ℝ (fun z ↦ u (x₀, z)) y₀ (y₂ - y₁) := by
  rw [fderiv_section_apply h, Prod.mk_sub_mk, sub_self]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem norm_prodMk_sub (x : E) (y₁ y₂ : F) : ‖(x, y₂) - (x, y₁)‖ = ‖y₂ - y₁‖ := by
  rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

/-- Strict differentiability of finitely many `C¹` functions at `p₀`, uniformly in `i`. -/
theorem exists_pos_abs_sub_le_of_contDiff (hg : ∀ i, ContDiff ℝ 1 (g i)) (p₀ : E × F) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ i p q, dist p p₀ < δ → dist q p₀ < δ →
      |g i p - g i q - fderiv ℝ (g i) p₀ (p - q)| ≤ ε * ‖p - q‖ := by
  have h : ∀ᶠ r : (E × F) × (E × F) in 𝓝 (p₀, p₀), ∀ i,
      ‖g i r.1 - g i r.2 - fderiv ℝ (g i) p₀ (r.1 - r.2)‖ ≤ ε * ‖r.1 - r.2‖ :=
    eventually_all.2 fun i ↦ (hasStrictFDerivAt_iff_isLittleO.1
      (((hg i).contDiffAt).hasStrictFDerivAt one_ne_zero)).def hε
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun i p q hp hq ↦ ?_⟩
  have := h (y := (p, q)) (by rw [Prod.dist_eq]; exact max_lt hp hq) i
  rwa [Real.norm_eq_abs] at this

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem lowerLagrangian_sub_lowerLagrangian (x : E) (lam lam' : ι → ℝ) (y : F) :
    lowerLagrangian φ g x lam y - lowerLagrangian φ g x lam' y =
      ∑ i, lam i * g i (x, y) - ∑ i, lam' i * g i (x, y) := by
  simp only [lowerLagrangian]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem lowerLagrangian_eq_of_isLowerKKT {x : E} {y : F} {lam : ι → ℝ}
    (h : IsLowerKKT φ g x y lam) : lowerLagrangian φ g x lam y = φ (x, y) := by
  simp only [lowerLagrangian, h.2.2.1, Finset.sum_const_zero, add_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem sum_mul_nonpos_of_mem_lowerFeasible {x : E} {y : F} {lam : ι → ℝ}
    (hy : y ∈ lowerFeasible g x) (hlam : ∀ i, 0 ≤ lam i) : ∑ i, lam i * g i (x, y) ≤ 0 :=
  Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hlam i) (hy i)

/-- A quantitative form of (SSOC), uniform over a compact set `K` of multipliers on which the
Hessian depends continuously: `∇²_yy L(x̄, ȳ, λ)(v, v) ≥ c ‖v‖²` for all `λ ∈ K` and all `v` that
are critical up to `η ‖v‖` in the weighted sense `∑ λᵢ |∇_y gᵢ(x̄, ȳ) v| < η ‖v‖`. -/
theorem exists_pos_lowerSSOC_of_isCompact [ProperSpace F] {x₀ : E} {y₀ : F}
    {K : Set (ι → ℝ)} (hK : IsCompact K) (hKΛ : K ⊆ lowerMultipliers φ g x₀ y₀)
    (hH : ContinuousOn (fun p : (ι → ℝ) × F ↦ lowerHessian φ g x₀ y₀ p.1 p.2 p.2) (K ×ˢ univ))
    (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ c > 0, ∃ η > 0, ∀ lam ∈ K, ∀ v : F,
      ∑ i, lam i * |fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ v| < η * ‖v‖ →
        c * ‖v‖ ^ 2 ≤ lowerHessian φ g x₀ y₀ lam v v := by
  set D : ι → StrongDual ℝ F := fun i ↦ fderiv ℝ (fun z ↦ g i (x₀, z)) y₀
  set u : (ι → ℝ) × F → ℝ := fun p ↦ ∑ i, p.1 i * |D i p.2| with hu_def
  set q : (ι → ℝ) × F → ℝ := fun p ↦ lowerHessian φ g x₀ y₀ p.1 p.2 p.2 with hq_def
  set S : Set ((ι → ℝ) × F) := K ×ˢ Metric.sphere (0 : F) 1 with hS_def
  have hu : Continuous u := continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp continuous_fst).mul (((D i).continuous.comp continuous_snd).abs)
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hScl : IsClosed S := hS.isClosed
  have hq : ContinuousOn q S := hH.mono (prod_mono subset_rfl (subset_univ _))
  have hu0 : ∀ p ∈ S, 0 ≤ u p := fun p hp ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg ((hKΛ hp.1).2.1 i) (abs_nonneg _)
  -- positivity on the critical directions of the unit sphere
  obtain ⟨c, hc, hcC⟩ : ∃ c > 0, ∀ p ∈ S, u p = 0 → 2 * c ≤ q p := by
    set C := S ∩ u ⁻¹' {0}
    have hC : IsCompact C := hS.inter_right (isClosed_singleton.preimage hu)
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨1, one_pos, fun p hp hp0 ↦ ?_⟩
      have : p ∈ C := ⟨hp, hp0⟩
      rw [hCe] at this
      simp at this
    obtain ⟨⟨lam, d⟩, ⟨⟨hlam, hdS⟩, hd0⟩, hmin⟩ := hC.exists_isMinOn hCne (hq.mono inter_subset_left)
    have hd0' : u (lam, d) = 0 := hd0
    have hpos : 0 < q (lam, d) := by
      refine hssoc lam (hKΛ hlam) d (fun h ↦ by rw [h] at hdS; simp at hdS) fun i hi ↦ ?_
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
        mul_nonneg ((hKΛ hlam).2.1 i) (abs_nonneg (D i d))).1 hd0' i (Finset.mem_univ i)
      exact abs_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hi.ne')
    refine ⟨q (lam, d) / 2, by positivity, fun p hp hp0 ↦ ?_⟩
    have : q (lam, d) ≤ q p := hmin ⟨hp, hp0⟩
    linarith
  -- a margin around the critical directions
  obtain ⟨η, hη, hηT⟩ : ∃ η > 0, ∀ p ∈ S, u p < η → c ≤ q p := by
    set T := S ∩ q ⁻¹' Iic c
    have hT : IsCompact T :=
      hS.of_isClosed_subset (hq.preimage_isClosed_of_isClosed hScl isClosed_Iic)
        inter_subset_left
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · refine ⟨1, one_pos, fun p hp _ ↦ ?_⟩
      by_contra hlt
      have : p ∈ T := ⟨hp, (not_le.1 hlt).le⟩
      rw [hTe] at this
      simp at this
    obtain ⟨p, ⟨hpS, hpq⟩, hmin⟩ := hT.exists_isMinOn hTne hu.continuousOn
    have hpq' : q p ≤ c := hpq
    have hp0 : 0 < u p := by
      refine lt_of_le_of_ne (hu0 p hpS) fun h ↦ ?_
      have := hcC p hpS h.symm
      linarith
    refine ⟨u p, hp0, fun p' hp' hlt ↦ ?_⟩
    by_contra hle
    have : u p ≤ u p' := hmin ⟨hp', (not_le.1 hle).le⟩
    linarith
  -- homogeneity
  refine ⟨c, hc, η, hη, fun lam hlam v hv ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set d := ‖v‖⁻¹ • v with hd
  have hdS : (lam, d) ∈ S := by
    refine ⟨hlam, ?_⟩
    rw [mem_sphere_zero_iff_norm, hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hud : u (lam, d) = ‖v‖⁻¹ * u (lam, v) := by
    simp only [u, hd, map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hqd : q (lam, d) = ‖v‖⁻¹ ^ 2 * q (lam, v) := by
    simp only [q, hd, map_smul, smul_apply, smul_eq_mul]
    ring
  have h1 := hηT _ hdS (by
    rw [hud]
    calc ‖v‖⁻¹ * u (lam, v) < ‖v‖⁻¹ * (η * ‖v‖) := mul_lt_mul_of_pos_left hv (inv_pos.2 hn)
      _ = η := by field_simp)
  rw [hqd] at h1
  calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ ^ 2 * q (lam, v) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = q (lam, v) := by field_simp

/-- A quantitative form of (SSOC): `∇²_yy L(x̄, ȳ, λ⁰)(v, v) ≥ c ‖v‖²` for all `v` that are
critical up to `η ‖v‖` in the weighted sense `∑ λ⁰ᵢ |∇_y gᵢ(x̄, ȳ) v| < η ‖v‖`. -/
theorem exists_pos_lowerSSOC [ProperSpace F] {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ c > 0, ∃ η > 0, ∀ v : F,
      ∑ i, lam₀ i * |fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ v| < η * ‖v‖ →
        c * ‖v‖ ^ 2 ≤ lowerHessian φ g x₀ y₀ lam₀ v v := by
  have hH : ContinuousOn (fun p : (ι → ℝ) × F ↦ lowerHessian φ g x₀ y₀ p.1 p.2 p.2)
      ({lam₀} ×ˢ univ) :=
    (((lowerHessian φ g x₀ y₀ lam₀).continuous.comp continuous_snd).clm_apply
      continuous_snd).continuousOn.congr fun p hp ↦ by
        rw [show p.1 = lam₀ from hp.1]
        rfl
  obtain ⟨c, hc, η, hη, h⟩ := exists_pos_lowerSSOC_of_isCompact isCompact_singleton
    (singleton_subset_iff.2 hkkt) hH hssoc
  exact ⟨c, hc, η, hη, h lam₀ rfl⟩


theorem contDiff_fderiv_comp_inr {u : E × F → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 fun p ↦ (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ E F) :=
  (hu.fderiv_right (by norm_num)).clm_comp contDiff_const

theorem contDiff_lowerLagrangianDeriv (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (lam : ι → ℝ) : ContDiff ℝ 1 (lowerLagrangianDeriv φ g lam) :=
  (contDiff_fderiv_comp_inr hφ).add
    (ContDiff.sum fun i _ ↦ (contDiff_fderiv_comp_inr (hg i)).const_smul (lam i))

/-- `lowerHessian` is the Hessian of `y ↦ L(x̄, y, λ)` at `ȳ`. -/
theorem fderiv_fderiv_lowerLagrangian (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (x₀ : E) (y₀ : F) (lam : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (lowerLagrangian φ g x₀ lam)) y₀ = lowerHessian φ g x₀ y₀ lam := by
  have e : fderiv ℝ (lowerLagrangian φ g x₀ lam) =
      fun w ↦ lowerLagrangianDeriv φ g lam (x₀, w) := funext fun w ↦
    (hasFDerivAt_lowerLagrangian lam (hφ.differentiable (by norm_num) _)
      fun i ↦ (hg i).differentiable (by norm_num) _).fderiv
  rw [e]
  exact (((contDiff_lowerLagrangianDeriv hφ hg lam).differentiable one_ne_zero _).hasFDerivAt.comp
    y₀ (hasFDerivAt_prodMk_right x₀ y₀)).fderiv

/-- A uniform second-order expansion of the follower's Lagrangian: for `x` near `x̄`, `y₁, y₂`
near `ȳ` and `λ` near `λ⁰`,
`L(x, y₂, λ) = L(x, y₁, λ) + ∇_y L(x, y₁, λ)(y₂ - y₁) + ½ ∇²_yy L(x̄, ȳ, λ⁰)(y₂ - y₁)² + o(‖y₂ - y₁‖²)`. -/
theorem exists_pos_lowerLagrangian_expansion (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (x : E) (y₁ y₂ : F) (lam : ι → ℝ), dist x x₀ < δ → dist y₁ y₀ < δ →
      dist y₂ y₀ < δ → dist lam lam₀ < δ →
      |lowerLagrangian φ g x lam y₂ - lowerLagrangian φ g x lam y₁ -
        lowerLagrangianDeriv φ g lam (x, y₁) (y₂ - y₁) -
        lowerHessian φ g x₀ y₀ lam₀ (y₂ - y₁) (y₂ - y₁) / 2| ≤ ε * ‖y₂ - y₁‖ ^ 2 := by
  set p₀ : E × F := (x₀, y₀)
  set A : E × F → StrongDual ℝ F := fun p ↦ (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ E F)
  set B : ι → E × F → StrongDual ℝ F :=
    fun i p ↦ (fderiv ℝ (g i) p).comp (ContinuousLinearMap.inr ℝ E F)
  have hA := ((contDiff_fderiv_comp_inr hφ).contDiffAt (x := p₀)).hasStrictFDerivAt one_ne_zero
  have hB := fun i ↦
    ((contDiff_fderiv_comp_inr (hg i)).contDiffAt (x := p₀)).hasStrictFDerivAt one_ne_zero
  set A' := fderiv ℝ A p₀
  set B' := fun i ↦ fderiv ℝ (B i) p₀
  -- the Hessian in terms of `A'` and `B'`
  have hH : ∀ u : E × F, u.1 = 0 →
      lowerHessian φ g x₀ y₀ lam₀ u.2 = A' u + ∑ i, lam₀ i • B' i u := by
    rintro ⟨u₁, u₂⟩ (rfl : u₁ = 0)
    have hd : HasFDerivAt (lowerLagrangianDeriv φ g lam₀) (A' + ∑ i, lam₀ i • B' i) p₀ :=
      hA.hasFDerivAt.add (HasFDerivAt.fun_sum fun i _ ↦ (hB i).hasFDerivAt.const_smul (lam₀ i))
    change (fderiv ℝ (lowerLagrangianDeriv φ g lam₀) p₀) (0, u₂) = _
    rw [hd.fderiv]
    simp only [add_apply, sum_apply, smul_apply]
  -- the constants
  set N : ℝ := ∑ i, (|lam₀ i| + 1) with hN
  set Mb : ℝ := ∑ i, ‖B' i‖ with hMb
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ ↦ by positivity
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg fun i _ ↦ ContinuousLinearMap.opNorm_nonneg _
  set ε₁ : ℝ := ε / (2 * (1 + N)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hstrict : ∀ᶠ r : (E × F) × (E × F) in 𝓝 (p₀, p₀),
      ‖A r.1 - A r.2 - A' (r.1 - r.2)‖ ≤ ε₁ * ‖r.1 - r.2‖ ∧
        ∀ i, ‖B i r.1 - B i r.2 - B' i (r.1 - r.2)‖ ≤ ε₁ * ‖r.1 - r.2‖ :=
    ((hasStrictFDerivAt_iff_isLittleO.1 hA).def hε₁0).and
      (eventually_all.2 fun i ↦ (hasStrictFDerivAt_iff_isLittleO.1 (hB i)).def hε₁0)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.1 hstrict
  set δ : ℝ := min (min δ₁ 1) (ε / (2 * (Mb + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδ₁ one_pos) (by positivity)
  have hδδ₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε / (2 * (Mb + 1)) := min_le_right _ _
  -- the derivative estimate
  have hderiv : ∀ (x : E) (w y₁ : F) (lam : ι → ℝ), dist x x₀ < δ → dist w y₀ < δ →
      dist y₁ y₀ < δ → dist lam lam₀ < δ →
      ‖lowerLagrangianDeriv φ g lam (x, w) - lowerLagrangianDeriv φ g lam (x, y₁) -
        lowerHessian φ g x₀ y₀ lam₀ (w - y₁)‖ ≤ ε * ‖w - y₁‖ := by
    intro x w y₁ lam hx hw hy hlam
    set P : E × F := (x, w)
    set Q : E × F := (x, y₁)
    have hPQ : P - Q = (0, w - y₁) := by simp [P, Q]
    have hnPQ : ‖P - Q‖ = ‖w - y₁‖ := by rw [hPQ, Prod.norm_def, norm_zero, max_eq_right
      (norm_nonneg _)]
    have hr := hδ₁' (y := (P, Q)) (by
      rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
      exact max_lt (max_lt (hx.trans_le hδδ₁) (hw.trans_le hδδ₁))
        (max_lt (hx.trans_le hδδ₁) (hy.trans_le hδδ₁)))
    have hH' := hH (P - Q) (by rw [hPQ])
    rw [hPQ] at hH'
    have e : lowerLagrangianDeriv φ g lam P - lowerLagrangianDeriv φ g lam Q -
        lowerHessian φ g x₀ y₀ lam₀ (w - y₁) = (A P - A Q - A' (P - Q)) +
          ∑ i, (lam i • (B i P - B i Q - B' i (P - Q)) + (lam i - lam₀ i) • B' i (P - Q)) := by
      rw [show w - y₁ = (P - Q).2 by rw [hPQ], hH (P - Q) (by rw [hPQ])]
      have hs : ∑ i, (lam i - lam₀ i) • B' i (P - Q) =
          ∑ i, lam i • B' i (P - Q) - ∑ i, lam₀ i • B' i (P - Q) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by
          ext z
          simp only [smul_apply, sub_apply, smul_eq_mul, sub_mul]
      have hs2 : ∑ i, lam i • (B i P - B i Q - B' i (P - Q)) =
          ∑ i, lam i • B i P - ∑ i, lam i • B i Q - ∑ i, lam i • B' i (P - Q) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_sub, smul_sub]
      rw [Finset.sum_add_distrib, hs, hs2]
      simp only [lowerLagrangianDeriv, A, B]
      abel
    rw [e]
    have hlam' : ∀ i, |lam i - lam₀ i| < δ := fun i ↦ by
      have := (dist_le_pi_dist lam lam₀ i).trans_lt hlam
      rwa [Real.dist_eq] at this
    calc _ ≤ ‖A P - A Q - A' (P - Q)‖ + ∑ i, (‖lam i • (B i P - B i Q - B' i (P - Q))‖ +
            ‖(lam i - lam₀ i) • B' i (P - Q)‖) :=
          (norm_add_le _ _).trans (by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_add_le _ _))
      _ ≤ ε₁ * ‖w - y₁‖ + ∑ i, ((|lam₀ i| + 1) * (ε₁ * ‖w - y₁‖) +
            δ * (‖B' i‖ * ‖w - y₁‖)) := by
          gcongr with i
          · rw [← hnPQ]; exact hr.1
          · rw [norm_smul, Real.norm_eq_abs]
            refine mul_le_mul ?_ (hnPQ ▸ hr.2 i) (norm_nonneg _) (by positivity)
            have := hlam' i
            have h1 : |lam i| ≤ |lam₀ i| + |lam i - lam₀ i| := by
              have := abs_add_le (lam₀ i) (lam i - lam₀ i)
              rwa [add_sub_cancel] at this
            linarith
          · rw [norm_smul, Real.norm_eq_abs]
            refine mul_le_mul (hlam' i).le ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
              (norm_nonneg _) hδ0.le
            rw [hnPQ]
      _ = ε₁ * (1 + N) * ‖w - y₁‖ + δ * Mb * ‖w - y₁‖ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
            ← hN, ← hMb]
          ring
      _ ≤ ε / 2 * ‖w - y₁‖ + ε / 2 * ‖w - y₁‖ := by
          gcongr
          · rw [hε₁]; field_simp; rfl
          · calc δ * Mb ≤ ε / (2 * (Mb + 1)) * Mb := mul_le_mul_of_nonneg_right hδε hMb0
              _ ≤ ε / 2 := by
                rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
                nlinarith
      _ = ε * ‖w - y₁‖ := by ring
  -- integrate along the segment
  refine ⟨δ, hδ0, fun x y₁ y₂ lam hx hy₁ hy₂ hlam ↦ ?_⟩
  set v := y₂ - y₁ with hv
  set H := lowerHessian φ g x₀ y₀ lam₀
  set c := lowerLagrangianDeriv φ g lam (x, y₁) v
  set h : ℝ → ℝ := fun t ↦ lowerLagrangian φ g x lam (y₁ + t • v) - t * c - t ^ 2 / 2 * H v v
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, dist (y₁ + t • v) y₀ < δ := fun t ht ↦ by
    have h := (convex_ball y₀ δ) (Metric.mem_ball.2 hy₁) (Metric.mem_ball.2 hy₂)
      (sub_nonneg.2 ht.2) ht.1 (by ring : 1 - t + t = 1)
    rw [Metric.mem_ball] at h
    convert h using 2
    rw [hv]
    module
  have hderivh : ∀ t, HasDerivAt h (lowerLagrangianDeriv φ g lam (x, y₁ + t • v) v - c -
      t * H v v) t := fun t ↦ by
    have hl : HasDerivAt (fun t : ℝ ↦ y₁ + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y₁
    have h1 := (hasFDerivAt_lowerLagrangian (x := x) (y := y₁ + t • v) lam
      (hφ.differentiable (by norm_num) _)
      (fun i ↦ (hg i).differentiable (by norm_num) _)).comp_hasDerivAt t hl
    have h2 := (hasDerivAt_id t).mul_const c
    have h3 := ((hasDerivAt_pow 2 t).div_const 2).mul_const (H v v)
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [one_mul, Nat.cast_ofNat]
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖lowerLagrangianDeriv φ g lam (x, y₁ + t • v) v - c - t * H v v‖ ≤ ε * ‖v‖ ^ 2 := by
    intro t ht
    have hd := hderiv x (y₁ + t • v) y₁ lam hx (hseg t (Ico_subset_Icc_self ht)) hy₁ hlam
    rw [add_sub_cancel_left] at hd
    have e : lowerLagrangianDeriv φ g lam (x, y₁ + t • v) v - c - t * H v v =
        (lowerLagrangianDeriv φ g lam (x, y₁ + t • v) - lowerLagrangianDeriv φ g lam (x, y₁) -
          H (t • v)) v := by
      simp only [c, sub_apply, map_smul, smul_apply,
        smul_eq_mul]
    rw [e]
    calc _ ≤ ‖lowerLagrangianDeriv φ g lam (x, y₁ + t • v) - lowerLagrangianDeriv φ g lam (x, y₁) -
          H (t • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖t • v‖ * ‖v‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ ≤ ε * ‖v‖ * ‖v‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      _ = ε * ‖v‖ ^ 2 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ ↦ (hderivh t).hasDerivWithinAt) hbound 1 ⟨zero_le_one, le_rfl⟩
  have e1 : h 1 - h 0 = lowerLagrangian φ g x lam y₂ - lowerLagrangian φ g x lam y₁ - c -
      H v v / 2 := by
    simp only [h, one_smul, zero_smul, add_zero, hv, add_sub_cancel]
    ring
  rw [e1, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  exact hmv

/-! ### Dependence on the multiplier -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem lowerLagrangian_eq_sum (x : E) (lam : ι → ℝ) (y : F) :
    lowerLagrangian φ g x lam y =
      lowerLagrangian φ g x 0 y + ∑ i, lam i * lowerLagrangian (g i) g x 0 y := by
  simp [lowerLagrangian]

theorem lowerLagrangianDeriv_eq_sum (lam : ι → ℝ) (p : E × F) :
    lowerLagrangianDeriv φ g lam p =
      lowerLagrangianDeriv φ g 0 p + ∑ i, lam i • lowerLagrangianDeriv (g i) g 0 p := by
  simp [lowerLagrangianDeriv]

/-- The Hessian `∇²_yy L(x̄, ȳ, λ)` is affine in `λ`. -/
theorem lowerHessian_eq_sum (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i)) (x₀ : E)
    (y₀ : F) (lam : ι → ℝ) :
    lowerHessian φ g x₀ y₀ lam =
      lowerHessian φ g x₀ y₀ 0 + ∑ i, lam i • lowerHessian (g i) g x₀ y₀ 0 := by
  set p₀ : E × F := (x₀, y₀)
  set B : ι → E × F → StrongDual ℝ F :=
    fun i p ↦ (fderiv ℝ (g i) p).comp (ContinuousLinearMap.inr ℝ E F)
  have hB := fun i ↦
    ((contDiff_fderiv_comp_inr (hg i)).differentiable one_ne_zero p₀).hasFDerivAt
  have h : ∀ (u : E × F → ℝ), ContDiff ℝ 2 u → ∀ lam : ι → ℝ, lowerHessian u g x₀ y₀ lam =
      (fderiv ℝ (fun p ↦ (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ E F)) p₀ +
        ∑ i, lam i • fderiv ℝ (B i) p₀).comp (ContinuousLinearMap.inr ℝ E F) := by
    intro u hu lam
    have hd : HasFDerivAt (lowerLagrangianDeriv u g lam)
        (fderiv ℝ (fun p ↦ (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ E F)) p₀ +
          ∑ i, lam i • fderiv ℝ (B i) p₀) p₀ :=
      ((contDiff_fderiv_comp_inr hu).differentiable one_ne_zero p₀).hasFDerivAt.add
        (HasFDerivAt.fun_sum fun i _ ↦ (hB i).const_smul (lam i))
    rw [lowerHessian, hd.fderiv]
  have h0 : ∀ (u : E × F → ℝ), ContDiff ℝ 2 u → lowerHessian u g x₀ y₀ 0 =
      (fderiv ℝ (fun p ↦ (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ E F)) p₀).comp
        (ContinuousLinearMap.inr ℝ E F) := fun u hu ↦ by
    rw [h u hu 0, Finset.sum_eq_zero (fun i _ ↦ by
      rw [Pi.zero_apply]; exact zero_smul ℝ (fderiv ℝ (B i) p₀)), add_zero]
  have hg0 : ∀ i, lowerHessian (g i) g x₀ y₀ 0 =
      (fderiv ℝ (B i) p₀).comp (ContinuousLinearMap.inr ℝ E F) := fun i ↦ h0 (g i) (hg i)
  rw [h φ hφ, h0 φ hφ, ContinuousLinearMap.add_comp, ContinuousLinearMap.finsetSum_comp]
  simp only [hg0, ContinuousLinearMap.smul_comp]

/-- A second-order expansion of the follower's Lagrangian, uniform in `x`, the base point and
all multipliers `λ`, with the Hessian `∇²_yy L(x̄, ȳ, λ)` at the same multiplier: the error is
at most `ε (1 + ∑ |λᵢ|) ‖y₂ - y₁‖²`. -/
theorem exists_pos_lowerLagrangian_expansion_uniform (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (x₀ : E) (y₀ : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (x : E) (y₁ y₂ : F) (lam : ι → ℝ), dist x x₀ < δ → dist y₁ y₀ < δ →
      dist y₂ y₀ < δ →
      |lowerLagrangian φ g x lam y₂ - lowerLagrangian φ g x lam y₁ -
        lowerLagrangianDeriv φ g lam (x, y₁) (y₂ - y₁) -
        lowerHessian φ g x₀ y₀ lam (y₂ - y₁) (y₂ - y₁) / 2| ≤
          ε * (1 + ∑ i, |lam i|) * ‖y₂ - y₁‖ ^ 2 := by
  -- the expansion of a single function
  have h1 : ∀ u : E × F → ℝ, ContDiff ℝ 2 u → ∀ᶠ q : E × F × F in 𝓝 (x₀, y₀, y₀),
      |lowerLagrangian u g q.1 0 q.2.2 - lowerLagrangian u g q.1 0 q.2.1 -
        lowerLagrangianDeriv u g 0 (q.1, q.2.1) (q.2.2 - q.2.1) -
        lowerHessian u g x₀ y₀ 0 (q.2.2 - q.2.1) (q.2.2 - q.2.1) / 2| ≤
          ε * ‖q.2.2 - q.2.1‖ ^ 2 := by
    intro u hu
    obtain ⟨δ, hδ, h⟩ := exists_pos_lowerLagrangian_expansion hu hg x₀ y₀ 0 hε
    filter_upwards [Metric.ball_mem_nhds _ hδ] with q hq
    simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
    exact h q.1 q.2.1 q.2.2 0 hq.1 hq.2.1 hq.2.2 (by rw [dist_self]; exact hδ)
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
    ((h1 φ hφ).and (eventually_all.2 fun i ↦ h1 (g i) (hg i)))
  refine ⟨δ, hδ, fun x y₁ y₂ lam hx hy₁ hy₂ ↦ ?_⟩
  obtain ⟨hφe, hge⟩ := h (y := (x, y₁, y₂)) (by
    simp only [Prod.dist_eq, max_lt_iff]
    exact ⟨hx, hy₁, hy₂⟩)
  set v := y₂ - y₁
  set Eφ := lowerLagrangian φ g x 0 y₂ - lowerLagrangian φ g x 0 y₁ -
    lowerLagrangianDeriv φ g 0 (x, y₁) v - lowerHessian φ g x₀ y₀ 0 v v / 2 with hEφ
  set Eg : ι → ℝ := fun i ↦ lowerLagrangian (g i) g x 0 y₂ - lowerLagrangian (g i) g x 0 y₁ -
    lowerLagrangianDeriv (g i) g 0 (x, y₁) v - lowerHessian (g i) g x₀ y₀ 0 v v / 2 with hEg
  have e : lowerLagrangian φ g x lam y₂ - lowerLagrangian φ g x lam y₁ -
      lowerLagrangianDeriv φ g lam (x, y₁) v - lowerHessian φ g x₀ y₀ lam v v / 2 =
        Eφ + ∑ i, lam i * Eg i := by
    rw [lowerLagrangian_eq_sum x lam y₂, lowerLagrangian_eq_sum x lam y₁,
      lowerLagrangianDeriv_eq_sum, lowerHessian_eq_sum hφ hg]
    simp only [hEφ, hEg, add_apply, sum_apply, smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib, mul_div_assoc', ← Finset.sum_div]
    ring
  rw [e]
  calc _ ≤ |Eφ| + ∑ i, |lam i * Eg i| :=
        (abs_add_le _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
    _ ≤ ε * ‖v‖ ^ 2 + ∑ i, |lam i| * (ε * ‖v‖ ^ 2) := by
        gcongr with i
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hge i) (abs_nonneg _)
    _ = ε * (1 + ∑ i, |lam i|) * ‖v‖ ^ 2 := by
        rw [← Finset.sum_mul]
        ring

variable [FiniteDimensional ℝ F]

/-- Under (SSOC), KKT points of the follower's problem near `(x̄, ȳ)` with multipliers near `λ⁰`
are unique: this is the uniqueness part of the proof of Thm. 4.4 of [Dempe 2002, pp. 103–104]. -/
theorem exists_pos_eq_of_isLowerKKT (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ δ > 0, ∀ (x : E) (y₁ y₂ : F) (lam₁ lam₂ : ι → ℝ), dist x x₀ < δ → dist y₁ y₀ < δ →
      dist y₂ y₀ < δ → dist lam₁ lam₀ < δ → dist lam₂ lam₀ < δ →
      IsLowerKKT φ g x y₁ lam₁ → IsLowerKKT φ g x y₂ lam₂ → y₁ = y₂ := by
  obtain ⟨c, hc, η, hη, hH⟩ := exists_pos_lowerSSOC hkkt hssoc
  set Λ : ℝ := ∑ i, lam₀ i with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ ↦ hkkt.2.1 i
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hφd : ∀ p, DifferentiableAt ℝ φ p := fun p ↦ hφ.differentiable (by norm_num) p
  have hgd : ∀ i p, DifferentiableAt ℝ (g i) p := fun i p ↦ (hg i).differentiable (by norm_num) p
  obtain ⟨δ₁, hδ₁, hexp⟩ :=
    exists_pos_lowerLagrangian_expansion hφ hg x₀ y₀ lam₀ (ε := c / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, hstr⟩ :=
    exists_pos_abs_sub_le_of_contDiff hg1 (x₀, y₀) (ε := η / (2 * (Λ + 1))) (by positivity)
  have hpos : ∀ᶠ lam in 𝓝 lam₀, ∀ i, 0 < lam₀ i → 0 < lam i :=
    eventually_all.2 fun i ↦ by
      by_cases hi : 0 < lam₀ i
      · exact (((continuous_apply i).tendsto lam₀).eventually (lt_mem_nhds hi)).mono
          fun _ h _ ↦ h
      · exact Eventually.of_forall fun _ h ↦ absurd h hi
  obtain ⟨δ₃, hδ₃, hpos⟩ := Metric.eventually_nhds_iff.1 hpos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity,
    fun x y₁ y₂ lam₁ lam₂ hx hy₁ hy₂ hl₁ hl₂ hk₁ hk₂ ↦ ?_⟩
  simp only [lt_min_iff] at hx hy₁ hy₂ hl₁ hl₂
  by_contra hne
  have hn : 0 < ‖y₂ - y₁‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  -- the two second-order expansions
  have e₁ := hexp x y₁ y₂ lam₁ hx.1.1 hy₁.1.1 hy₂.1.1 hl₁.1.1
  have e₂ := hexp x y₂ y₁ lam₂ hx.1.1 hy₂.1.1 hy₁.1.1 hl₂.1.1
  rw [lowerLagrangianDeriv_eq_zero (hφd _) (fun i ↦ hgd i _) hk₁, zero_apply, sub_zero] at e₁
  rw [lowerLagrangianDeriv_eq_zero (hφd _) (fun i ↦ hgd i _) hk₂, zero_apply, sub_zero] at e₂
  have hvv : lowerHessian φ g x₀ y₀ lam₀ (y₁ - y₂) (y₁ - y₂) =
      lowerHessian φ g x₀ y₀ lam₀ (y₂ - y₁) (y₂ - y₁) := by
    rw [← neg_sub y₂ y₁]
    simp only [map_neg, neg_apply, neg_neg]
  rw [hvv, norm_sub_rev y₁ y₂] at e₂
  -- the multiplier terms have the right sign
  have c₁ : lowerLagrangian φ g x lam₁ y₂ - lowerLagrangian φ g x lam₂ y₂ ≤ 0 := by
    rw [lowerLagrangian_sub_lowerLagrangian, Finset.sum_eq_zero fun i _ ↦ hk₂.2.2.1 i, sub_zero]
    exact sum_mul_nonpos_of_mem_lowerFeasible hk₂.1 hk₁.2.1
  have c₂ : lowerLagrangian φ g x lam₂ y₁ - lowerLagrangian φ g x lam₁ y₁ ≤ 0 := by
    rw [lowerLagrangian_sub_lowerLagrangian, Finset.sum_eq_zero fun i _ ↦ hk₁.2.2.1 i, sub_zero]
    exact sum_mul_nonpos_of_mem_lowerFeasible hk₁.1 hk₂.2.1
  rw [abs_le] at e₁ e₂
  have hup : lowerHessian φ g x₀ y₀ lam₀ (y₂ - y₁) (y₂ - y₁) ≤ c / 2 * ‖y₂ - y₁‖ ^ 2 := by
    linarith [e₁.1, e₂.1]
  -- `y₂ - y₁` is almost critical
  have hcrit : ∀ i, 0 < lam₀ i → |fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ (y₂ - y₁)| ≤
      η / (2 * (Λ + 1)) * ‖y₂ - y₁‖ := by
    intro i hi
    have h0₁ : g i (x, y₁) = 0 :=
      (mul_eq_zero.1 (hk₁.2.2.1 i)).resolve_left (hpos hl₁.2 i hi).ne'
    have h0₂ : g i (x, y₂) = 0 :=
      (mul_eq_zero.1 (hk₂.2.2.1 i)).resolve_left (hpos hl₂.2 i hi).ne'
    have h := hstr i (x, y₂) (x, y₁) (by rw [Prod.dist_eq]; exact max_lt hx.1.2 hy₂.1.2)
      (by rw [Prod.dist_eq]; exact max_lt hx.1.2 hy₁.1.2)
    rwa [h0₁, h0₂, sub_self, zero_sub, abs_neg, fderiv_apply_sub_section (hgd i _),
      norm_prodMk_sub] at h
  have hk : Λ * (η / (2 * (Λ + 1))) < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hu : ∑ i, lam₀ i * |fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ (y₂ - y₁)| < η * ‖y₂ - y₁‖ := by
    calc _ ≤ ∑ i, lam₀ i * (η / (2 * (Λ + 1)) * ‖y₂ - y₁‖) := Finset.sum_le_sum fun i _ ↦ by
          rcases (hkkt.2.1 i).eq_or_lt with h | h
          · rw [← h, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hcrit i h) h.le
      _ = Λ * (η / (2 * (Λ + 1))) * ‖y₂ - y₁‖ := by
          rw [← Finset.sum_mul, ← hΛ]
          ring
      _ < η * ‖y₂ - y₁‖ := mul_lt_mul_of_pos_right hk hn
  have := hH _ hu
  nlinarith [mul_pos hc (pow_pos hn 2)]

/-- An elementary estimate used in `exists_pos_eq_of_isLowerKKT_of_lowerPLI`: if `d` is the
linearization of the increment `b - a` of a constraint up to `ε w`, `λ` is a multiplier
complementary to `a` and `μ` is close to `λ`, then `μ |d|` is controlled by `-λ b`. -/
theorem mul_abs_le_of_abs_sub_le {a b d lam μ δ ε R C w : ℝ} (hs : |b - a - d| ≤ ε * w)
    (hd : |d| ≤ C * w) (hlam : 0 ≤ lam) (hca : lam * a = 0) (hb : b ≤ 0) (hμ : |lam - μ| ≤ δ)
    (hμ0 : 0 ≤ μ) (hμR : μ ≤ R) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hw : 0 ≤ w) :
    μ * |d| ≤ -(lam * b) + (δ * C + δ * ε + R * ε) * w := by
  have ha : |b - a| ≤ (C + ε) * w := by
    have := abs_sub_abs_le_abs_sub (b - a) d
    linarith
  have hda : |d| ≤ |b - a| + ε * w := by
    have := abs_sub_abs_le_abs_sub d (b - a)
    rw [abs_sub_comm d (b - a)] at this
    linarith
  have hla : lam * |b - a| = -(lam * b) := by
    rw [← abs_of_nonneg hlam, ← abs_mul, abs_of_nonneg hlam, mul_sub, hca, sub_zero,
      abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hlam hb)]
  have hμa : μ * |b - a| ≤ lam * |b - a| + δ * ((C + ε) * w) := by
    have h1 : (μ - lam) * |b - a| ≤ |μ - lam| * |b - a| :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
    have h2 : |μ - lam| * |b - a| ≤ δ * ((C + ε) * w) := by
      rw [abs_sub_comm]
      exact mul_le_mul hμ ha (abs_nonneg _) hδ
    linarith
  calc μ * |d| ≤ μ * (|b - a| + ε * w) := mul_le_mul_of_nonneg_left hda hμ0
    _ = μ * |b - a| + μ * (ε * w) := by ring
    _ ≤ lam * |b - a| + δ * ((C + ε) * w) + R * (ε * w) :=
        add_le_add hμa (mul_le_mul_of_nonneg_right hμR (by positivity))
    _ = _ := by rw [hla]; ring

/-- Under (MFCQ) (in its dual form (PLI)) and (SSOC), KKT points of the follower's problem near
`(x̄, ȳ)` with multipliers near the multiplier set `Λ(x̄, ȳ)` are unique. The two multipliers may
be close to different points `μ¹, μ² ∈ Λ(x̄, ȳ)`; (SSOC) is applied at the midpoint
`(μ¹ + μ²) / 2 ∈ Λ(x̄, ȳ)`. -/
theorem exists_pos_eq_of_isLowerKKT_of_lowerPLI (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} (hpli : LowerPLI g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ δ > 0, ∀ (x : E) (y₁ y₂ : F) (lam₁ lam₂ : ι → ℝ), dist x x₀ < δ → dist y₁ y₀ < δ →
      dist y₂ y₀ < δ → lam₁ ∈ Metric.thickening δ (lowerMultipliers φ g x₀ y₀) →
      lam₂ ∈ Metric.thickening δ (lowerMultipliers φ g x₀ y₀) →
      IsLowerKKT φ g x y₁ lam₁ → IsLowerKKT φ g x y₂ lam₂ → y₁ = y₂ := by
  set Λ₀ := lowerMultipliers φ g x₀ y₀ with hΛ₀
  have hK : IsCompact Λ₀ := isCompact_lowerMultipliers hpli
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hφd : ∀ p, DifferentiableAt ℝ φ p := fun p ↦ hφ.differentiable (by norm_num) p
  have hgd : ∀ i p, DifferentiableAt ℝ (g i) p := fun i p ↦ (hg i).differentiable (by norm_num) p
  -- the Hessian is affine in the multiplier
  set Hφ := lowerHessian φ g x₀ y₀ 0
  set Hg : ι → F →L[ℝ] StrongDual ℝ F := fun i ↦ lowerHessian (g i) g x₀ y₀ 0
  have hHsum : ∀ lam v, lowerHessian φ g x₀ y₀ lam v v = Hφ v v + ∑ i, lam i * Hg i v v := by
    intro lam v
    rw [lowerHessian_eq_sum hφ hg]
    simp [Hφ, Hg]
  have hHc : Continuous fun p : (ι → ℝ) × F ↦ lowerHessian φ g x₀ y₀ p.1 p.2 p.2 := by
    simp only [hHsum]
    exact ((Hφ.continuous.comp continuous_snd).clm_apply continuous_snd).add
      (continuous_finsetSum _ fun i _ ↦ ((continuous_apply i).comp continuous_fst).mul
        (((Hg i).continuous.comp continuous_snd).clm_apply continuous_snd))
  obtain ⟨c, hc, η, hη, hH⟩ :=
    exists_pos_lowerSSOC_of_isCompact hK subset_rfl hHc.continuousOn hssoc
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.exists_pos_norm_le
  -- the constants
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set D : ι → StrongDual ℝ F := fun i ↦ fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ with hD
  set Mg : ℝ := ∑ i, ‖Hg i‖ with hMg
  have hMg0 : 0 ≤ Mg := Finset.sum_nonneg fun i _ ↦ ContinuousLinearMap.opNorm_nonneg _
  set M : ℝ := ‖Hφ‖ + (R + 1) * Mg with hM
  have hM0 : 0 ≤ M := by positivity
  set Dn : ℝ := ∑ i, ‖D i‖ with hDn
  have hDn0 : 0 ≤ Dn := Finset.sum_nonneg fun i _ ↦ ContinuousLinearMap.opNorm_nonneg _
  set ε₁ : ℝ := c / (8 * (1 + N * (R + 1))) with hε₁
  obtain ⟨δ₁, hδ₁, hexp⟩ :=
    exists_pos_lowerLagrangian_expansion_uniform hφ hg x₀ y₀ (ε := ε₁) (by positivity)
  set ε₂ : ℝ := η / (4 * (N * R + 1)) with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  obtain ⟨δ₂, hδ₂, hstr⟩ := exists_pos_abs_sub_le_of_contDiff hg1 (x₀, y₀) hε₂0
  set K : ℝ := M + c / 4 + Dn + N * ε₂ with hKdef
  have hK0 : 0 ≤ K := by positivity
  set δ : ℝ := min (min δ₁ δ₂) (min (min (c / (4 * (Mg + 1))) (η / (4 * (K + 1)))) 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδδ₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₃ : δ ≤ c / (4 * (Mg + 1)) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₄ : δ ≤ η / (4 * (K + 1)) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ0, fun x y₁ y₂ lam₁ lam₂ hx hy₁ hy₂ hl₁ hl₂ hk₁ hk₂ ↦ ?_⟩
  obtain ⟨μ₁, hμ₁, hd₁⟩ := Metric.mem_thickening_iff.1 hl₁
  obtain ⟨μ₂, hμ₂, hd₂⟩ := Metric.mem_thickening_iff.1 hl₂
  by_contra hne
  set v := y₂ - y₁ with hv
  have hn : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  have hn2 : ‖v‖ < 2 * δ := by
    calc ‖v‖ = ‖(y₂ - y₀) - (y₁ - y₀)‖ := by rw [hv, sub_sub_sub_cancel_right]
      _ ≤ ‖y₂ - y₀‖ + ‖y₁ - y₀‖ := norm_sub_le _ _
      _ < δ + δ := by rw [← dist_eq_norm, ← dist_eq_norm]; exact add_lt_add hy₂ hy₁
      _ = 2 * δ := by ring
  -- coordinatewise bounds on the multipliers
  have hcoord : ∀ lam μ, μ ∈ Λ₀ → dist lam μ < δ → ∀ i,
      |lam i - μ i| < δ ∧ |lam i| ≤ R + 1 ∧ 0 ≤ μ i ∧ μ i ≤ R := by
    intro lam μ hμ hd i
    have h1 : |lam i - μ i| < δ := by
      have := (dist_le_pi_dist lam μ i).trans_lt hd
      rwa [Real.dist_eq] at this
    have h2 : |μ i| ≤ R := by
      have := norm_le_pi_norm μ i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hR μ hμ)
    refine ⟨h1, ?_, hμ.2.1 i, (le_abs_self _).trans h2⟩
    have := abs_add_le (μ i) (lam i - μ i)
    rw [add_sub_cancel] at this
    linarith
  have hsumabs : ∀ lam μ, μ ∈ Λ₀ → dist lam μ < δ →
      ε₁ * (1 + ∑ i, |lam i|) * ‖v‖ ^ 2 ≤ c / 8 * ‖v‖ ^ 2 := by
    intro lam μ hμ hd
    have h1 : ∑ i, |lam i| ≤ N * (R + 1) := by
      calc ∑ i, |lam i| ≤ ∑ _i : ι, (R + 1) :=
            Finset.sum_le_sum fun i _ ↦ (hcoord lam μ hμ hd i).2.1
        _ = N * (R + 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
    have h2 : ε₁ * (1 + ∑ i, |lam i|) ≤ c / 8 := by
      calc ε₁ * (1 + ∑ i, |lam i|) ≤ ε₁ * (1 + N * (R + 1)) := by gcongr
        _ = c / 8 := by rw [hε₁]; field_simp
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  -- the Hessian estimates
  have hHg : ∀ i, |Hg i v v| ≤ ‖Hg i‖ * ‖v‖ ^ 2 := fun i ↦ by
    have := (Hg i).le_opNorm₂ v v
    rw [Real.norm_eq_abs] at this
    calc _ ≤ ‖Hg i‖ * ‖v‖ * ‖v‖ := this
      _ = _ := by ring
  have hHφ : |Hφ v v| ≤ ‖Hφ‖ * ‖v‖ ^ 2 := by
    have := Hφ.le_opNorm₂ v v
    rw [Real.norm_eq_abs] at this
    calc _ ≤ ‖Hφ‖ * ‖v‖ * ‖v‖ := this
      _ = _ := by ring
  have hHb : ∀ lam μ, μ ∈ Λ₀ → dist lam μ < δ →
      -(M * ‖v‖ ^ 2) ≤ lowerHessian φ g x₀ y₀ lam v v := by
    intro lam μ hμ hd
    rw [hHsum]
    have h1 : |∑ i, lam i * Hg i v v| ≤ (R + 1) * Mg * ‖v‖ ^ 2 := by
      calc _ ≤ ∑ i, |lam i * Hg i v v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (R + 1) * (‖Hg i‖ * ‖v‖ ^ 2) := Finset.sum_le_sum fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul (hcoord lam μ hμ hd i).2.1 (hHg i) (abs_nonneg _) (by positivity)
        _ = (R + 1) * Mg * ‖v‖ ^ 2 := by rw [hMg, ← Finset.mul_sum, ← Finset.sum_mul]; ring
    have := neg_abs_le (∑ i, lam i * Hg i v v)
    have := neg_abs_le (Hφ v v)
    rw [hM]
    linarith
  have hHd : ∀ lam μ, μ ∈ Λ₀ → dist lam μ < δ →
      lowerHessian φ g x₀ y₀ μ v v - δ * Mg * ‖v‖ ^ 2 ≤ lowerHessian φ g x₀ y₀ lam v v := by
    intro lam μ hμ hd
    rw [hHsum lam v, hHsum μ v]
    have h1 : |∑ i, (lam i - μ i) * Hg i v v| ≤ δ * Mg * ‖v‖ ^ 2 := by
      calc _ ≤ ∑ i, |(lam i - μ i) * Hg i v v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, δ * (‖Hg i‖ * ‖v‖ ^ 2) := Finset.sum_le_sum fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul (hcoord lam μ hμ hd i).1.le (hHg i) (abs_nonneg _) hδ0.le
        _ = δ * Mg * ‖v‖ ^ 2 := by rw [hMg, ← Finset.mul_sum, ← Finset.sum_mul]; ring
    have e : ∑ i, lam i * Hg i v v - ∑ i, μ i * Hg i v v = ∑ i, (lam i - μ i) * Hg i v v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have := neg_abs_le (∑ i, (lam i - μ i) * Hg i v v)
    linarith
  -- the second-order expansions at the two KKT points
  have e₁ := hexp x y₁ y₂ lam₁ (hx.trans_le hδδ₁) (hy₁.trans_le hδδ₁) (hy₂.trans_le hδδ₁)
  have e₂ := hexp x y₂ y₁ lam₂ (hx.trans_le hδδ₁) (hy₂.trans_le hδδ₁) (hy₁.trans_le hδδ₁)
  rw [lowerLagrangianDeriv_eq_zero (hφd _) (fun i ↦ hgd i _) hk₁, zero_apply, sub_zero] at e₁
  rw [lowerLagrangianDeriv_eq_zero (hφd _) (fun i ↦ hgd i _) hk₂, zero_apply, sub_zero] at e₂
  have hvv : ∀ lam, lowerHessian φ g x₀ y₀ lam (y₁ - y₂) (y₁ - y₂) =
      lowerHessian φ g x₀ y₀ lam v v := fun lam ↦ by
    rw [hv, ← neg_sub y₂ y₁]
    simp only [map_neg, neg_apply, neg_neg]
  rw [hvv, norm_sub_rev y₁ y₂] at e₂
  have hb₁ := (e₁.trans (hsumabs lam₁ μ₁ hμ₁ hd₁))
  have hb₂ := (e₂.trans (hsumabs lam₂ μ₂ hμ₂ hd₂))
  rw [abs_le] at hb₁ hb₂
  -- the multiplier terms
  set A₁ := ∑ i, lam₁ i * g i (x, y₂) with hA₁
  set A₂ := ∑ i, lam₂ i * g i (x, y₁) with hA₂
  have hL₁ : lowerLagrangian φ g x lam₁ y₂ - lowerLagrangian φ g x lam₁ y₁ =
      φ (x, y₂) - φ (x, y₁) + A₁ := by
    rw [lowerLagrangian_eq_of_isLowerKKT hk₁]
    simp only [lowerLagrangian, hA₁]
    ring
  have hL₂ : lowerLagrangian φ g x lam₂ y₁ - lowerLagrangian φ g x lam₂ y₂ =
      φ (x, y₁) - φ (x, y₂) + A₂ := by
    rw [lowerLagrangian_eq_of_isLowerKKT hk₂]
    simp only [lowerLagrangian, hA₂]
    ring
  have hA₁0 : A₁ ≤ 0 := sum_mul_nonpos_of_mem_lowerFeasible hk₂.1 hk₁.2.1
  have hA₂0 : A₂ ≤ 0 := sum_mul_nonpos_of_mem_lowerFeasible hk₁.1 hk₂.2.1
  have hlow : (lowerHessian φ g x₀ y₀ lam₁ v v + lowerHessian φ g x₀ y₀ lam₂ v v) / 2 -
      c / 4 * ‖v‖ ^ 2 ≤ A₁ + A₂ := by
    linarith [hb₁.1, hb₂.1]
  -- `v` is almost critical for the midpoint multiplier
  have hcritj : ∀ (lam μ : ι → ℝ) (ya yb : F), μ ∈ Λ₀ → dist lam μ < δ →
      dist ya y₀ < δ → dist yb y₀ < δ → IsLowerKKT φ g x ya lam → yb ∈ lowerFeasible g x →
      ∑ i, μ i * |D i (yb - ya)| ≤ -∑ i, lam i * g i (x, yb) +
        δ * (Dn + N * ε₂) * ‖yb - ya‖ + R * N * ε₂ * ‖yb - ya‖ := by
    intro lam μ ya yb hμ hd hya hyb hk hyb'
    have hi : ∀ i, μ i * |D i (yb - ya)| ≤ -(lam i * g i (x, yb)) +
        (δ * ‖D i‖ + δ * ε₂ + R * ε₂) * ‖yb - ya‖ := by
      intro i
      obtain ⟨hc1, -, hc3, hc4⟩ := hcoord lam μ hμ hd i
      have hs := hstr i (x, yb) (x, ya)
        (by rw [Prod.dist_eq]; exact max_lt (hx.trans_le hδδ₂) (hyb.trans_le hδδ₂))
        (by rw [Prod.dist_eq]; exact max_lt (hx.trans_le hδδ₂) (hya.trans_le hδδ₂))
      rw [fderiv_apply_sub_section (hgd i _), norm_prodMk_sub] at hs
      have hDw : |D i (yb - ya)| ≤ ‖D i‖ * ‖yb - ya‖ := by
        rw [← Real.norm_eq_abs]
        exact (D i).le_opNorm _
      exact mul_abs_le_of_abs_sub_le hs hDw (hk.2.1 i) (hk.2.2.1 i) (hyb' i) hc1.le hc3 hc4
        hδ0.le hε₂0.le (norm_nonneg _)
    calc ∑ i, μ i * |D i (yb - ya)| ≤ ∑ i, (-(lam i * g i (x, yb)) +
          (δ * ‖D i‖ + δ * ε₂ + R * ε₂) * ‖yb - ya‖) := Finset.sum_le_sum fun i _ ↦ hi i
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
          Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, ← hDn]
        ring
  have hc₁ := hcritj lam₁ μ₁ y₁ y₂ hμ₁ hd₁ hy₁ hy₂ hk₁ hk₂.1
  have hc₂ := hcritj lam₂ μ₂ y₂ y₁ hμ₂ hd₂ hy₂ hy₁ hk₂ hk₁.1
  have hDneg : ∀ i, |D i (y₁ - y₂)| = |D i v| := fun i ↦ by
    rw [hv, ← neg_sub y₂ y₁, map_neg, abs_neg]
  simp only [hDneg, norm_sub_rev y₁ y₂] at hc₂
  rw [← hA₁] at hc₁
  rw [← hA₂] at hc₂
  set μ := (1 / 2 : ℝ) • μ₁ + (1 / 2 : ℝ) • μ₂ with hμ
  have hμΛ : μ ∈ Λ₀ := convex_lowerMultipliers hμ₁ hμ₂ (by norm_num) (by norm_num) (by norm_num)
  have hμsum : ∑ i, μ i * |D i v| =
      (∑ i, μ₁ i * |D i v| + ∑ i, μ₂ i * |D i v|) / 2 := by
    simp only [hμ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    ring
  have hμH : lowerHessian φ g x₀ y₀ μ v v =
      (lowerHessian φ g x₀ y₀ μ₁ v v + lowerHessian φ g x₀ y₀ μ₂ v v) / 2 := by
    simp only [hHsum, hμ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hup : -(A₁ + A₂) ≤ (M + c / 4) * ‖v‖ ^ 2 := by
    have := hHb lam₁ μ₁ hμ₁ hd₁
    have := hHb lam₂ μ₂ hμ₂ hd₂
    linarith
  have hcrit : ∑ i, μ i * |D i v| < η * ‖v‖ := by
    have h1 : (M + c / 4) * ‖v‖ ^ 2 ≤ 2 * δ * (M + c / 4) * ‖v‖ := by
      have : ‖v‖ ^ 2 ≤ 2 * δ * ‖v‖ := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hn2.le hn.le
      calc _ ≤ (M + c / 4) * (2 * δ * ‖v‖) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : δ * K ≤ η / 4 := by
      calc δ * K ≤ η / (4 * (K + 1)) * K := mul_le_mul_of_nonneg_right hδ₄ hK0
        _ ≤ η / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
    have h3 : R * N * ε₂ ≤ η / 4 := by
      rw [hε₂, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h4 : δ * K * ‖v‖ ≤ η / 4 * ‖v‖ := mul_le_mul_of_nonneg_right h2 hn.le
    have h5 : R * N * ε₂ * ‖v‖ ≤ η / 4 * ‖v‖ := mul_le_mul_of_nonneg_right h3 hn.le
    rw [hμsum]
    rw [hKdef] at h4
    linarith [mul_pos hη hn]
  have hpos := hH μ hμΛ v hcrit
  have hd₁' := hHd lam₁ μ₁ hμ₁ hd₁
  have hd₂' := hHd lam₂ μ₂ hμ₂ hd₂
  have hδMg : δ * Mg ≤ c / 4 := by
    calc δ * Mg ≤ c / (4 * (Mg + 1)) * Mg := mul_le_mul_of_nonneg_right hδ₃ hMg0
      _ ≤ c / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
  have h6 : δ * Mg * ‖v‖ ^ 2 ≤ c / 4 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hδMg (by positivity)
  have := mul_pos hc (pow_pos hn 2)
  linarith

/-- Second-order sufficiency: under (SSOC), a KKT point `ȳ` is a strict local solution of the
follower's problem at `x̄` [Dempe 2002, p. 101]. -/
theorem exists_pos_lt_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ ρ > 0, ∀ z ∈ lowerFeasible g x₀, z ≠ y₀ → dist z y₀ < ρ → φ (x₀, y₀) < φ (x₀, z) := by
  obtain ⟨c, hc, η, hη, hH⟩ := exists_pos_lowerSSOC hkkt hssoc
  set Λ : ℝ := ∑ i, lam₀ i with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ ↦ hkkt.2.1 i
  set M : ℝ := ‖lowerHessian φ g x₀ y₀ lam₀‖ with hM
  have hM0 : 0 ≤ M := ContinuousLinearMap.opNorm_nonneg _
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hφd : ∀ p, DifferentiableAt ℝ φ p := fun p ↦ hφ.differentiable (by norm_num) p
  have hgd : ∀ i p, DifferentiableAt ℝ (g i) p := fun i p ↦ (hg i).differentiable (by norm_num) p
  obtain ⟨δ₁, hδ₁, hexp⟩ :=
    exists_pos_lowerLagrangian_expansion hφ hg x₀ y₀ lam₀ (ε := c / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, hstr⟩ :=
    exists_pos_abs_sub_le_of_contDiff hg1 (x₀, y₀) (ε := η / (4 * (Λ + 1))) (by positivity)
  set r : ℝ := η / (4 * (M / 2 + c / 4 + 1)) with hr
  have hr0 : 0 < r := by positivity
  refine ⟨min (min δ₁ δ₂) r, by positivity, fun z hz hne hdist ↦ ?_⟩
  simp only [lt_min_iff] at hdist
  have hn : 0 < ‖z - y₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hnr : ‖z - y₀‖ < r := by rw [← dist_eq_norm]; exact hdist.2
  have e := hexp x₀ y₀ z lam₀ (by rw [dist_self]; exact hδ₁) (by rw [dist_self]; exact hδ₁)
    hdist.1.1 (by rw [dist_self]; exact hδ₁)
  rw [lowerLagrangianDeriv_eq_zero (hφd _) (fun i ↦ hgd i _) hkkt, zero_apply, sub_zero,
    abs_le] at e
  have hL : φ (x₀, z) - φ (x₀, y₀) = (lowerLagrangian φ g x₀ lam₀ z -
      lowerLagrangian φ g x₀ lam₀ y₀) - ∑ i, lam₀ i * g i (x₀, z) := by
    rw [lowerLagrangian_eq_of_isLowerKKT hkkt]
    simp only [lowerLagrangian]
    ring
  have hG := sum_mul_nonpos_of_mem_lowerFeasible hz hkkt.2.1
  by_cases hcrit : ∑ i, lam₀ i * |fderiv ℝ (fun w ↦ g i (x₀, w)) y₀ (z - y₀)| < η * ‖z - y₀‖
  · have := hH _ hcrit
    have := mul_pos hc (pow_pos hn 2)
    linarith [e.1]
  push Not at hcrit
  -- first-order information on the strongly active constraints
  have hfo : ∀ i, lam₀ i * |fderiv ℝ (fun w ↦ g i (x₀, w)) y₀ (z - y₀)| ≤
      lam₀ i * (-g i (x₀, z)) + lam₀ i * (η / (4 * (Λ + 1)) * ‖z - y₀‖) := by
    intro i
    rcases mul_eq_zero.1 (hkkt.2.2.1 i) with h | h
    · rw [h]
      simp
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hkkt.2.1 i)
    have hs := hstr i (x₀, z) (x₀, y₀)
      (by rw [Prod.dist_eq, dist_self]; exact max_lt hδ₂ hdist.1.2)
      (by rw [dist_self]; exact hδ₂)
    rw [h, sub_zero, fderiv_apply_sub_section (hgd i _), norm_prodMk_sub, abs_le] at hs
    have hz' : g i (x₀, z) ≤ 0 := hz i
    exact abs_le.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hfo i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hΛ] at hsum
  simp only [mul_neg, Finset.sum_neg_distrib] at hsum
  have hk : Λ * (η / (4 * (Λ + 1))) ≤ η / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hk' : Λ * (η / (4 * (Λ + 1)) * ‖z - y₀‖) ≤ η / 4 * ‖z - y₀‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hk hn.le
  have hHv : -(M * ‖z - y₀‖ ^ 2) ≤ lowerHessian φ g x₀ y₀ lam₀ (z - y₀) (z - y₀) := by
    have := (lowerHessian φ g x₀ y₀ lam₀).le_opNorm₂ (z - y₀) (z - y₀)
    rw [Real.norm_eq_abs] at this
    nlinarith [neg_abs_le (lowerHessian φ g x₀ y₀ lam₀ (z - y₀) (z - y₀))]
  have hrr : (M / 2 + c / 4 + 1) * r = η / 4 := by
    rw [hr]
    field_simp
  have hq : (M / 2 + c / 4) * ‖z - y₀‖ ^ 2 ≤ η / 4 * ‖z - y₀‖ := by
    have : (M / 2 + c / 4) * ‖z - y₀‖ ≤ (M / 2 + c / 4 + 1) * r := by
      nlinarith
    rw [hrr] at this
    nlinarith
  have := mul_pos hη hn
  linarith [e.1]

variable [FiniteDimensional ℝ E]

/-- **Thm. 4.4 of [Dempe 2002]** (Kojima): if `ȳ` is a KKT point of the follower's problem at
`x̄` at which (MFCQ) (in its dual form (PLI)) and (SSOC) hold, then `ȳ` is strongly stable. The
data are `C²`. -/
theorem isLowerStronglyStable_of_lowerPLI (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hpli : LowerPLI g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    IsLowerStronglyStable φ g x₀ y₀ := by
  classical
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hy₀ : y₀ ∈ lowerFeasible g x₀ := hkkt.1
  set Λ₀ := lowerMultipliers φ g x₀ y₀ with hΛ₀
  have hΛ₀c : IsCompact Λ₀ := isCompact_lowerMultipliers hpli
  -- uniqueness of nearby KKT points
  obtain ⟨δ₁, hδ₁, huniq⟩ := exists_pos_eq_of_isLowerKKT_of_lowerPLI hφ hg hpli hssoc
  have hthick : Metric.cthickening (δ₁ / 2) Λ₀ ⊆ Metric.thickening δ₁ Λ₀ :=
    Metric.cthickening_subset_thickening' hδ₁ (by linarith) _
  -- near `(x̄, ȳ)`, (PLI) holds and all multipliers are close to `Λ(x̄, ȳ)`
  have hΛ : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), LowerPLI g p.1 p.2 ∧
      lowerMultipliers φ g p.1 p.2 ⊆ Metric.thickening (δ₁ / 2) Λ₀ :=
    (eventually_lowerPLI hg1 hpli).and (upperHemicontinuousAt_lowerMultipliers hφ1 hg1 hpli _
      Metric.isOpen_thickening (Metric.self_subset_thickening (by positivity) _))
  obtain ⟨δ₂, hδ₂, hΛ⟩ := Metric.eventually_nhds_iff.1 hΛ
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hkktloc : ∀ x z, dist x x₀ < δ → dist z y₀ < δ → z ∈ lowerFeasible g x →
      IsLocalMinOn (fun w ↦ φ (x, w)) (lowerFeasible g x) z →
      ∃ lam, lam ∈ Metric.thickening (δ₁ / 2) Λ₀ ∧ IsLowerKKT φ g x z lam := by
    intro x z hx hz hzG hmin
    have hp := hΛ (y := (x, z)) (by
      rw [Prod.dist_eq]
      exact max_lt (hx.trans_le (min_le_right _ _)) (hz.trans_le (min_le_right _ _)))
    obtain ⟨lam, hlam⟩ := exists_isLowerKKT_of_isLocalMinOn hzG hmin
      ((hφ1.comp (contDiff_prodMk_right x)).differentiable one_ne_zero z)
      (fun i ↦ ((hg1 i).comp (contDiff_prodMk_right x)).contDiffAt) hp.1
    exact ⟨lam, hp.2 hlam, hlam⟩
  -- `ȳ` is a strict local minimizer
  obtain ⟨ρ₀, hρ₀, hstrict⟩ := exists_pos_lt_of_lowerSSOC hφ hg hkkt hssoc
  set ρ := min ρ₀ δ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρρ₀ : ρ < ρ₀ := by
    have := min_le_left ρ₀ δ
    rw [hρ]
    linarith
  have hρδ : ρ < δ := by
    have := min_le_right ρ₀ δ
    rw [hρ]
    linarith
  -- the problem restricted to the closed ball `B̄(ȳ, ρ)`
  set K : E → Set F := fun x ↦ lowerFeasible g x ∩ Metric.closedBall y₀ ρ with hK
  have hKcl : IsClosed (graph K) :=
    (isClosed_graph_lowerFeasible fun i ↦ (hg i).continuous).inter
      (Metric.isClosed_closedBall.preimage continuous_snd)
  have hKb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C :=
    ⟨univ, univ_mem, _, isCompact_closedBall y₀ ρ, fun x _ ↦ inter_subset_right⟩
  have hy₀K : y₀ ∈ K x₀ := ⟨hy₀, Metric.mem_closedBall_self hρ0.le⟩
  have hsol₀ : y₀ ∈ solutionMap φ K x₀ := by
    refine ⟨hy₀K, fun z hz ↦ ?_⟩
    by_cases hzy : z = y₀
    · rw [hzy]
    exact (hstrict z hz.1 hzy ((Metric.mem_closedBall.1 hz.2).trans_lt hρρ₀)).le
  have hsol₀' : ∀ z ∈ solutionMap φ K x₀, z = y₀ := by
    intro z hz
    by_contra hzy
    have h1 := hstrict z hz.1.1 hzy ((Metric.mem_closedBall.1 hz.1.2).trans_lt hρρ₀)
    have h2 := hz.2 y₀ hy₀K
    linarith
  have hlip := lipschitzLikeAt_lowerFeasible (fun i ↦ (hg1 i).contDiffAt) hy₀
    ((lowerPLI_iff_lowerLevelRegular fun i ↦ (hg1 i).differentiable one_ne_zero _).1 hpli)
  have husc : UpperSemicontinuousAt (marginal (fun p ↦ (φ p : EReal)) K) x₀ := by
    intro t ht
    have h0 : (φ (x₀, y₀) : EReal) < t :=
      lt_of_le_of_lt (mem_solutionMap_iff_le_marginal.1 hsol₀).2 ht
    have hc : Continuous fun p : E × F ↦ (φ p : EReal) :=
      continuous_coe_real_ereal.comp hφ.continuous
    obtain ⟨U, hU, W, hW, hy₀W, hUW⟩ := exists_isOpen_of_eventually_nhds_prod
      (P := fun x y ↦ (φ (x, y) : EReal) < t)
      ((hc.tendsto (x₀, y₀)).eventually (eventually_lt_nhds h0))
    filter_upwards [hU, eventually_inter_nonempty_of_lipschitzLikeAt hlip hy₀
      (inter_mem (hW.mem_nhds hy₀W) (Metric.closedBall_mem_nhds y₀ hρ0))] with x hxU hx
    obtain ⟨w, hwG, hwW, hwB⟩ := hx
    exact lt_of_le_of_lt (VariationalAnalysis.marginal_le (show w ∈ K x from ⟨hwG, hwB⟩))
      (hUW x hxU w hwW)
  have hball : ∀ᶠ x in 𝓝 x₀, solutionMap φ K x ⊆ Metric.ball y₀ ρ :=
    upperHemicontinuousAt_solutionMap_of_upperSemicontinuousAt hKcl hKb husc hφ.continuous _
      Metric.isOpen_ball fun z hz ↦ by
        rw [hsol₀' z hz]
        exact Metric.mem_ball_self hρ0
  have hne : ∀ᶠ x in 𝓝 x₀, (solutionMap φ K x).Nonempty :=
    (eventually_inter_nonempty_of_lipschitzLikeAt hlip hy₀
      (Metric.closedBall_mem_nhds y₀ hρ0)).mono fun x hx ↦
        solutionMap_nonempty_of_isCompact ((isCompact_closedBall y₀ ρ).inter_left
          (isClosed_graph_lowerFeasible (fun i ↦ (hg i).continuous) |>.preimage
            (Continuous.prodMk_right x))) hx hφ.continuous
  -- the solution function and its multipliers
  set U : Set E := interior {x | dist x x₀ < δ ∧ solutionMap φ K x ⊆ Metric.ball y₀ ρ ∧
    (solutionMap φ K x).Nonempty} with hU
  have hUo : IsOpen U := isOpen_interior
  have hUx₀ : U ∈ 𝓝 x₀ := interior_mem_nhds.2
    ((show ∀ᶠ x in 𝓝 x₀, dist x x₀ < δ from Metric.ball_mem_nhds x₀ hδ0).and (hball.and hne))
  set s : E → F := fun x ↦
    if h : (solutionMap φ K x).Nonempty then h.some else y₀ with hs
  have hsK : ∀ x, s x ∈ Metric.closedBall y₀ ρ := fun x ↦ by
    by_cases h : (solutionMap φ K x).Nonempty
    · simp only [hs, dif_pos h]
      exact h.some_mem.1.2
    · simp only [hs, dif_neg h]
      exact Metric.mem_closedBall_self hρ0.le
  have hsU : ∀ x ∈ U, dist x x₀ < δ ∧ s x ∈ solutionMap φ K x ∧ s x ∈ Metric.ball y₀ ρ := by
    intro x hx
    obtain ⟨hxδ, hsub, hxne⟩ := interior_subset hx
    have : s x ∈ solutionMap φ K x := by
      simp only [hs, dif_pos hxne]
      exact hxne.some_mem
    exact ⟨hxδ, this, hsub this⟩
  have hsmin : ∀ x ∈ U, IsLocalMinOn (fun w ↦ φ (x, w)) (lowerFeasible g x) (s x) := by
    intro x hx
    obtain ⟨-, hsol, hsb⟩ := hsU x hx
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (lowerFeasible g x)
      (Metric.isOpen_ball.mem_nhds hsb)) fun w hw ↦
        hsol.2 w ⟨hw.1, Metric.ball_subset_closedBall hw.2⟩
  have hsδ : ∀ x ∈ U, dist (s x) y₀ < δ := fun x hx ↦
    (Metric.mem_ball.1 (hsU x hx).2.2).trans hρδ
  set μ : E → ι → ℝ := fun x ↦
    if h : ∃ lam, lam ∈ Metric.thickening (δ₁ / 2) Λ₀ ∧ IsLowerKKT φ g x (s x) lam then
      h.choose else lam₀ with hμ
  have hμb : ∀ x, μ x ∈ Metric.cthickening (δ₁ / 2) Λ₀ := fun x ↦ by
    by_cases h : ∃ lam, lam ∈ Metric.thickening (δ₁ / 2) Λ₀ ∧ IsLowerKKT φ g x (s x) lam
    · simp only [hμ, dif_pos h]
      exact Metric.thickening_subset_cthickening _ _ h.choose_spec.1
    · simp only [hμ, dif_neg h]
      exact Metric.self_subset_cthickening _ hkkt
  have hμU : ∀ x ∈ U, IsLowerKKT φ g x (s x) (μ x) := fun x hx ↦ by
    have h := hkktloc x (s x) (hsU x hx).1 (hsδ x hx) (hsU x hx).2.1.1.1 (hsmin x hx)
    simp only [hμ, dif_pos h]
    exact h.choose_spec.2
  -- uniqueness of local minimizers near `ȳ`
  have hsuniq : ∀ x ∈ U, ∀ z, dist z y₀ < δ₁ → ∀ lam ∈ Metric.thickening δ₁ Λ₀,
      IsLowerKKT φ g x z lam → z = s x := fun x hx z hz lam hlam hk ↦
    huniq x z (s x) lam (μ x) ((hsU x hx).1.trans_le hδδ₁) hz ((hsδ x hx).trans_le hδδ₁) hlam
      (hthick (hμb x)) hk (hμU x hx)
  refine ⟨δ, hδ0, U, hUx₀, s, ?_, ?_, fun x hx ↦ ⟨(hsδ x hx), (hsU x hx).2.1.1.1, hsmin x hx,
    fun z hz hzG hzmin ↦ ?_⟩⟩
  · exact hsol₀' _ (hsU x₀ (mem_of_mem_nhds hUx₀)).2.1
  · -- continuity: limits of KKT pairs are KKT pairs
    refine hUo.continuousOn_iff.2 fun x₁ hx₁ ↦ tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    have hev : ∀ᶠ n in atTop, ns n ∈ U := hns (hUo.mem_nhds hx₁)
    obtain ⟨⟨z, lam⟩, ⟨hz, hlam⟩, φ', hmono, hlim⟩ :=
      ((isCompact_closedBall y₀ ρ).prod hΛ₀c.cthickening).tendsto_subseq
        (x := fun n ↦ (s (ns n), μ (ns n))) fun n ↦ ⟨hsK _, hμb _⟩
    have hl1 : Tendsto (fun n ↦ s (ns (φ' n))) atTop (𝓝 z) :=
      (continuous_fst.tendsto _).comp hlim
    have hl2 : Tendsto (fun n ↦ μ (ns (φ' n))) atTop (𝓝 lam) :=
      (continuous_snd.tendsto _).comp hlim
    have ht : Tendsto (fun n ↦ ((ns (φ' n), s (ns (φ' n))), μ (ns (φ' n)))) atTop
        (𝓝 ((x₁, z), lam)) :=
      ((hns.comp hmono.tendsto_atTop).prodMk_nhds hl1).prodMk_nhds hl2
    have hk : IsLowerKKT φ g x₁ z lam :=
      (isClosed_graph_lowerMultipliers hφ1 hg1).mem_of_tendsto ht
        ((hmono.tendsto_atTop.eventually hev).mono fun n hn ↦ hμU _ hn)
    have hzs := hsuniq x₁ hx₁ z ((Metric.mem_closedBall.1 hz).trans_lt (hρδ.trans_le hδδ₁))
      lam (hthick hlam) hk
    exact ⟨φ', hzs ▸ hl1⟩
  · obtain ⟨lam, hlam, hk⟩ := hkktloc x z (hsU x hx).1 hz hzG hzmin
    exact hsuniq x hx z (hz.trans_le hδδ₁) lam
      (Metric.thickening_mono (by linarith) _ hlam) hk

/-- Thm. 4.4 of [Dempe 2002] in the version proved in the book (pp. 101–104): if `ȳ` is a KKT
point of the follower's problem at `x̄` at which (LICQ) and (SSOC) hold, then `ȳ` is strongly
stable. -/
theorem isLowerStronglyStable (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    IsLowerStronglyStable φ g x₀ y₀ :=
  isLowerStronglyStable_of_lowerPLI hφ hg hkkt (lowerPLI_of_lowerLICQ hkkt.1 hlicq) hssoc

/-- Thm. 4.4 of [Dempe 2002] as stated in the book: a local solution `ȳ` of the follower's
problem at `x̄` at which (MFCQ) (in its dual form (PLI)) and (SSOC) hold is strongly stable. -/
theorem isLowerStronglyStable_of_isLocalMinOn_of_lowerPLI (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} (hy₀ : y₀ ∈ lowerFeasible g x₀)
    (hmin : IsLocalMinOn (fun z ↦ φ (x₀, z)) (lowerFeasible g x₀) y₀)
    (hpli : LowerPLI g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    IsLowerStronglyStable φ g x₀ y₀ := by
  obtain ⟨lam₀, hkkt⟩ := exists_isLowerKKT_of_isLocalMinOn hy₀ hmin
    (((hφ.of_le (by norm_num)).comp (contDiff_prodMk_right x₀)).differentiable one_ne_zero y₀)
    (fun i ↦ (((hg i).of_le (by norm_num)).comp (contDiff_prodMk_right x₀)).contDiffAt) hpli
  exact isLowerStronglyStable_of_lowerPLI hφ hg hkkt hpli hssoc

/-- Thm. 4.4 of [Dempe 2002] for a local solution `ȳ` at which (LICQ) and (SSOC) hold. -/
theorem isLowerStronglyStable_of_isLocalMinOn (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} (hy₀ : y₀ ∈ lowerFeasible g x₀)
    (hmin : IsLocalMinOn (fun z ↦ φ (x₀, z)) (lowerFeasible g x₀) y₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    IsLowerStronglyStable φ g x₀ y₀ := by
  obtain ⟨lam₀, hkkt⟩ := exists_isLowerKKT_of_isLocalMinOn hy₀ hmin
    (((hφ.of_le (by norm_num)).comp (contDiff_prodMk_right x₀)).differentiable one_ne_zero y₀)
    (fun i ↦ (((hg i).of_le (by norm_num)).comp (contDiff_prodMk_right x₀)).contDiffAt)
    (lowerPLI_of_lowerLICQ hy₀ hlicq)
  exact isLowerStronglyStable hφ hg hkkt hlicq hssoc

end Bilevel
