/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.ValueFunctionDirectional

/-!
# Strong stability of local solutions

Thm. 4.4 of [Dempe 2002] (Kojima's theorem), in the version proved in the book: if `ȳ` is a
KKT point of the follower's problem `min_y {φ(x̄, y) | gᵢ(x̄, y) ≤ 0}` at which (LICQ) and the
strong second-order sufficient condition (SSOC) hold, then `ȳ` is *strongly stable*: for `x`
near `x̄` the problem has a unique local solution `y(x)` near `ȳ`, and `x ↦ y(x)` is continuous.

## Main results

* `LowerSSOC`: the strong second-order sufficient condition (SSOC) [Dempe 2002, p. 74], with the
  `y`-Hessian `lowerHessian` of the follower's Lagrangian `lowerLagrangian`.
* `IsLowerStronglyStable`: strong stability [Dempe 2002, Def. 4.4].
* `exists_pos_lowerLagrangian_expansion`: a second-order expansion of the Lagrangian, uniform in
  `x`, the base point and the multiplier.
* `exists_pos_lt_of_lowerSSOC`: (SSOC) makes a KKT point a strict local solution.
* `exists_pos_eq_of_isLowerKKT`: under (SSOC), KKT points near `(x̄, ȳ)` with multipliers near
  `λ⁰` are unique (no constraint qualification needed).
* `isLowerStronglyStable`, `isLowerStronglyStable_of_isLocalMinOn`: Thm. 4.4.

## Differences from the book

* Thm. 4.4 is stated in the book under (MFCQ), citing Kojima, but the book proves it (pp. 101–104)
  under (LICQ), which makes the multiplier unique; we follow the proof and assume (LICQ).
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

/-- A quantitative form of (SSOC): `∇²_yy L(x̄, ȳ, λ⁰)(v, v) ≥ c ‖v‖²` for all `v` that are
critical up to `η ‖v‖` in the weighted sense `∑ λ⁰ᵢ |∇_y gᵢ(x̄, ȳ) v| < η ‖v‖`. -/
theorem exists_pos_lowerSSOC [ProperSpace F] {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ c > 0, ∃ η > 0, ∀ v : F,
      ∑ i, lam₀ i * |fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ v| < η * ‖v‖ →
        c * ‖v‖ ^ 2 ≤ lowerHessian φ g x₀ y₀ lam₀ v v := by
  set H := lowerHessian φ g x₀ y₀ lam₀
  set D : ι → StrongDual ℝ F := fun i ↦ fderiv ℝ (fun z ↦ g i (x₀, z)) y₀
  set u : F → ℝ := fun v ↦ ∑ i, lam₀ i * |D i v| with hu_def
  set q : F → ℝ := fun v ↦ H v v with hq_def
  have hu : Continuous u := continuous_finsetSum _ fun i _ ↦
    continuous_const.mul ((D i).continuous.abs)
  have hq : Continuous q := H.continuous.clm_apply continuous_id
  have hu0 : ∀ v, 0 ≤ u v := fun v ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hkkt.2.1 i) (abs_nonneg _)
  have hS : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere 0 1
  -- positivity on the critical directions of the unit sphere
  obtain ⟨c, hc, hcC⟩ : ∃ c > 0, ∀ d ∈ Metric.sphere (0 : F) 1, u d = 0 → 2 * c ≤ q d := by
    set C := Metric.sphere (0 : F) 1 ∩ u ⁻¹' {0}
    have hC : IsCompact C := hS.inter_right (isClosed_singleton.preimage hu)
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨1, one_pos, fun d hd hd0 ↦ ?_⟩
      have : d ∈ C := ⟨hd, hd0⟩
      rw [hCe] at this
      simp at this
    obtain ⟨d, ⟨hdS, hd0⟩, hmin⟩ := hC.exists_isMinOn hCne hq.continuousOn
    have hd0' : u d = 0 := hd0
    have hpos : 0 < q d := by
      refine hssoc lam₀ hkkt d (fun h ↦ by rw [h] at hdS; simp at hdS) fun i hi ↦ ?_
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
        mul_nonneg (hkkt.2.1 i) (abs_nonneg (D i d))).1 hd0' i (Finset.mem_univ i)
      exact abs_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hi.ne')
    refine ⟨q d / 2, by positivity, fun d' hd' hd'0 ↦ ?_⟩
    have : q d ≤ q d' := hmin ⟨hd', hd'0⟩
    linarith
  -- a margin around the critical directions
  obtain ⟨η, hη, hηT⟩ : ∃ η > 0, ∀ d ∈ Metric.sphere (0 : F) 1, u d < η → c ≤ q d := by
    set T := Metric.sphere (0 : F) 1 ∩ {d | q d ≤ c}
    have hT : IsCompact T := hS.inter_right (isClosed_le hq continuous_const)
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · refine ⟨1, one_pos, fun d hd _ ↦ ?_⟩
      by_contra hlt
      have : d ∈ T := ⟨hd, (not_le.1 hlt).le⟩
      rw [hTe] at this
      simp at this
    obtain ⟨d, ⟨hdS, hdq⟩, hmin⟩ := hT.exists_isMinOn hTne hu.continuousOn
    have hdq' : q d ≤ c := hdq
    have hd0 : 0 < u d := by
      refine lt_of_le_of_ne (hu0 d) fun h ↦ ?_
      have := hcC d hdS h.symm
      linarith
    refine ⟨u d, hd0, fun d' hd' hlt ↦ ?_⟩
    by_contra hle
    have : u d ≤ u d' := hmin ⟨hd', (not_le.1 hle).le⟩
    linarith
  -- homogeneity
  refine ⟨c, hc, η, hη, fun v hv ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set d := ‖v‖⁻¹ • v with hd
  have hdS : d ∈ Metric.sphere (0 : F) 1 := by
    rw [mem_sphere_zero_iff_norm, hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hud : u d = ‖v‖⁻¹ * u v := by
    simp only [u, hd, map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hqd : q d = ‖v‖⁻¹ ^ 2 * q v := by
    simp only [q, hd, map_smul, smul_apply, smul_eq_mul]
    ring
  have h1 := hηT d hdS (by
    rw [hud]
    calc ‖v‖⁻¹ * u v < ‖v‖⁻¹ * (η * ‖v‖) := mul_lt_mul_of_pos_left hv (inv_pos.2 hn)
      _ = η := by field_simp)
  rw [hqd] at h1
  calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ ^ 2 * q v * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = q v := by field_simp


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

/-- **Thm. 4.4 of [Dempe 2002]** (Kojima), in the version proved in the book (pp. 101–104): if
`ȳ` is a KKT point of the follower's problem at `x̄` at which (LICQ) and (SSOC) hold, then `ȳ` is
strongly stable. The data are `C²`. -/
theorem isLowerStronglyStable (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    IsLowerStronglyStable φ g x₀ y₀ := by
  classical
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hy₀ : y₀ ∈ lowerFeasible g x₀ := hkkt.1
  have hpli : LowerPLI g x₀ y₀ := lowerPLI_of_lowerLICQ hkkt.1 hlicq
  -- uniqueness of nearby KKT points
  obtain ⟨δ₁, hδ₁, huniq⟩ := exists_pos_eq_of_isLowerKKT hφ hg hkkt hssoc
  -- near `(x̄, ȳ)`, (PLI) holds and all multipliers are close to `λ⁰`
  have hΛ : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), LowerPLI g p.1 p.2 ∧
      lowerMultipliers φ g p.1 p.2 ⊆ Metric.ball lam₀ (δ₁ / 2) :=
    (eventually_lowerPLI hg1 hpli).and (upperHemicontinuousAt_lowerMultipliers hφ1 hg1 hpli _
      Metric.isOpen_ball fun lam hlam ↦ by
        rw [lowerMultipliers_subsingleton_of_lowerLICQ hlicq hlam hkkt]
        exact Metric.mem_ball_self (by positivity))
  obtain ⟨δ₂, hδ₂, hΛ⟩ := Metric.eventually_nhds_iff.1 hΛ
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  have hkktloc : ∀ x z, dist x x₀ < δ → dist z y₀ < δ → z ∈ lowerFeasible g x →
      IsLocalMinOn (fun w ↦ φ (x, w)) (lowerFeasible g x) z →
      ∃ lam, dist lam lam₀ < δ₁ / 2 ∧ IsLowerKKT φ g x z lam := by
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
    if h : ∃ lam, dist lam lam₀ < δ₁ / 2 ∧ IsLowerKKT φ g x (s x) lam then h.choose else lam₀
    with hμ
  have hμb : ∀ x, dist (μ x) lam₀ ≤ δ₁ / 2 := fun x ↦ by
    by_cases h : ∃ lam, dist lam lam₀ < δ₁ / 2 ∧ IsLowerKKT φ g x (s x) lam
    · simp only [hμ, dif_pos h]
      exact h.choose_spec.1.le
    · simp only [hμ, dif_neg h]
      rw [dist_self]
      positivity
  have hμU : ∀ x ∈ U, IsLowerKKT φ g x (s x) (μ x) := fun x hx ↦ by
    have h := hkktloc x (s x) (hsU x hx).1 (hsδ x hx) (hsU x hx).2.1.1.1 (hsmin x hx)
    simp only [hμ, dif_pos h]
    exact h.choose_spec.2
  -- uniqueness of local minimizers near `ȳ`
  have hsuniq : ∀ x ∈ U, ∀ z, dist z y₀ < δ₁ → ∀ lam, dist lam lam₀ < δ₁ →
      IsLowerKKT φ g x z lam → z = s x := fun x hx z hz lam hlam hk ↦
    huniq x z (s x) lam (μ x) ((hsU x hx).1.trans_le hδδ₁) hz ((hsδ x hx).trans_le hδδ₁) hlam
      ((hμb x).trans_lt (by linarith)) hk (hμU x hx)
  refine ⟨δ, hδ0, U, hUx₀, s, ?_, ?_, fun x hx ↦ ⟨(hsδ x hx), (hsU x hx).2.1.1.1, hsmin x hx,
    fun z hz hzG hzmin ↦ ?_⟩⟩
  · exact hsol₀' _ (hsU x₀ (mem_of_mem_nhds hUx₀)).2.1
  · -- continuity: limits of KKT pairs are KKT pairs
    refine hUo.continuousOn_iff.2 fun x₁ hx₁ ↦ tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    have hev : ∀ᶠ n in atTop, ns n ∈ U := hns (hUo.mem_nhds hx₁)
    obtain ⟨⟨z, lam⟩, ⟨hz, hlam⟩, φ', hmono, hlim⟩ :=
      ((isCompact_closedBall y₀ ρ).prod (isCompact_closedBall lam₀ (δ₁ / 2))).tendsto_subseq
        (x := fun n ↦ (s (ns n), μ (ns n))) fun n ↦ ⟨hsK _, Metric.mem_closedBall.2 (hμb _)⟩
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
      lam ((Metric.mem_closedBall.1 hlam).trans_lt (by linarith)) hk
    exact ⟨φ', hzs ▸ hl1⟩
  · obtain ⟨lam, hlam, hk⟩ := hkktloc x z (hsU x hx).1 hz hzG hzmin
    exact hsuniq x hx z (hz.trans_le hδδ₁) lam (by linarith) hk

/-- Thm. 4.4 of [Dempe 2002] as stated in the book: a local solution `ȳ` of the follower's
problem at `x̄` at which (LICQ) and (SSOC) hold is strongly stable. -/
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
