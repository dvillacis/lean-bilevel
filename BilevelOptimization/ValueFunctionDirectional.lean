/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.ValueFunction
import BilevelOptimization.Farkas

/-!
# Directional derivatives of the optimal value function

Thm. 4.15, Cor. 4.4 and Thm. 4.16 of [Dempe 2002]: bounds for the Dini directional derivatives of
the follower's optimal value function `μ(x) = inf {φ(x, y) | gᵢ(x, y) ≤ 0}`, and its directional
differentiability under (LICQ) and for convex problems.

## Main definitions

* `lagrangianGradient φ g x y lam`: the partial gradient `∇ₓL(x, y, λ)` of the Lagrangian
  `L = φ + ∑ λᵢ gᵢ`.

## Main results

* `eventually_lowerValue_add_smul_le`: Thm. 4.15 of [Dempe 2002], upper bound: under (MFCQ) at
  `(x̄, ȳ)`, `D⁺μ(x̄; r) ≤ max {∇ₓL(x̄, ȳ, λ) r | λ ∈ Λ(x̄, ȳ)}`.
* `eventually_le_lowerValue_add_smul`: Thm. 4.15 of [Dempe 2002], lower bound:
  `D₊μ(x̄; r) ≥ min {∇ₓL(x̄, y, λ) r | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`.
* `exists_tendsto_slope_lowerValue_of_isConvexLower`: Thm. 4.16 of [Dempe 2002]: if the
  follower's problem is convex at `x̄` and satisfies Slater's condition there, `μ` is directionally
  differentiable at `x̄` and `μ'(x̄; r) = min_{y ∈ Ψ(x̄)} max_{λ ∈ Λ(x̄, y)} ∇ₓL(x̄, y, λ) r`.
* `exists_tendsto_slope_lowerValue_of_eventually_isConvexLower`: if the follower's problem is
  convex for all `x` near `x̄`, also
  `μ'(x̄; r) = max_{λ ∈ Λ} min_{y ∈ Ψ(x̄)} ∇ₓL(x̄, y, λ) r`, the formula of the book.
* `exists_tendsto_slope_lowerValue_of_lowerLICQ`: Cor. 4.4 of [Dempe 2002]: under (LICQ) at all
  `(x̄, y)`, `y ∈ Ψ(x̄)`, `μ'(x̄; r) = min {∇ₓL(x̄, y, λ(y)) r | y ∈ Ψ(x̄)}`, with the unique
  multiplier `λ(y)` (`lowerMultipliers_subsingleton_of_lowerLICQ`).
* `exists_lowerMultiplier_direction`: the duality of the linear programs (4.51) and (4.52).
* `lowerMultipliers_subset_of_isConvexLower`: for convex problems `Λ(x, y)` does not depend on
  `y ∈ Ψ(x)`.

## Remarks on the book

* The bounds of Thm. 4.15 are stated without the Dini derivatives (4.25), (4.26):
  `D⁺μ(x̄; r) < c` is replaced by `μ(x̄ + t r) ≤ μ(x̄) + t c` for small `t > 0`, for every `c`
  above the bound, and similarly for `D₊`.
* The upper bound of Thm. 4.15 holds at every feasible `ȳ` with `Λ(x̄, ȳ) ≠ ∅`, with `φ(x̄, ȳ)`
  in the place of `μ(x̄)`; only differentiability at `(x̄, ȳ)` is used. Without equality
  constraints no implicit function theorem is needed: the feasible curve is
  `t ↦ ȳ + t d` for a direction `d` given by linear programming duality, obtained here from
  Farkas' lemma.
* The lower bound of Thm. 4.15 is derived from the estimate (4.27) of the generalized gradient
  (Thm. 4.17, `exists_clarkeSubdiff_lowerValue_subset`) and
  `D₊μ(x̄; r) ≥ -μ°(x̄; -r)`, instead of the other way around.
* In Thm. 4.16 the existence of `μ'(x̄; r)` and the formula `min max` only need convexity at
  `x̄`. The proof in the book gives `max min ≤ D₊μ ≤ D⁺μ ≤ min max` and concludes by
  compactness; since `∇ₓL(x̄, y, λ) r` is not convex in `y`, no minimax theorem applies. Here
  the lower bound is sharpened to `min max ≤ D₊μ` and the upper bound to `D⁺μ ≤ max min`, by
  using in each a single limit point of the solutions `y(t)`, resp. of the multipliers `λ(t)`.
* In Cor. 4.4 the continuity of `y ↦ λ(y)` is not needed: the minimum is attained because the
  pairs `(y, λ)` with `y ∈ Ψ(x̄)`, `λ ∈ Λ(x̄, y)` form a compact set (closed graph and local
  boundedness of `Λ`, Thm. 4.2).
* (C) is replaced by local boundedness of the feasible-set map at `x̄`, and (MFCQ) at one feasible
  point by Slater's condition (for convex problems they are equivalent, as the book remarks).
-/

open Filter Topology Set
open scoped NNReal
open VariationalAnalysis (graph lowerFeasible lowerSolution lowerValue clarkeSubdiff clarkeDeriv
  LowerLevelRegular LocallyBoundedAt)
open ContinuousLinearMap (inl inr)

namespace Bilevel

/-! ### Auxiliary results -/

section Auxiliary

variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem tendsto_add_smul_nhdsGT (p w : X) :
    Tendsto (fun t : ℝ ↦ p + t • w) (𝓝[>] 0) (𝓝 p) := by
  have h : Continuous fun t : ℝ ↦ p + t • w := by fun_prop
  have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-- A first-order upper estimate along a ray. -/
theorem eventually_lt_add_mul_of_hasFDerivAt {u : X → ℝ} {u' : StrongDual ℝ X} {p w : X}
    (h : HasFDerivAt u u' p) {c : ℝ} (hc : u' w < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), u (p + t • w) < u p + t * c := by
  have hd : HasDerivAt (fun t : ℝ ↦ u (p + t • w)) (u' w) 0 := by
    have hl : HasDerivAt (fun t : ℝ ↦ p + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p
    have h' : HasFDerivAt u u' (p + (0 : ℝ) • w) := by simpa using h
    exact h'.comp_hasDerivAt (0 : ℝ) hl
  filter_upwards [hd.tendsto_slope_zero_right.eventually_lt_const hc, self_mem_nhdsWithin]
    with t ht ht0
  have ht0' : 0 < t := ht0
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht
  rw [inv_mul_lt_iff₀ ht0'] at ht
  linarith

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A first-order lower estimate in the first variable that is uniform in the second, for a
strictly differentiable function. -/
theorem eventually_mul_le_sub_of_hasStrictFDerivAt {ℓ : X × Z → ℝ} {ℓ' : StrongDual ℝ (X × Z)}
    {x₀ : X} {z₀ : Z} (h : HasStrictFDerivAt ℓ ℓ' (x₀, z₀)) {r : X} {c : ℝ}
    (hc : c < ℓ' (r, 0)) :
    ∀ᶠ q : ℝ × Z in 𝓝 (0, z₀), 0 < q.1 → q.1 * c ≤ ℓ (x₀ + q.1 • r, q.2) - ℓ (x₀, q.2) := by
  set η := (ℓ' (r, 0) - c) / (‖r‖ + 1) with hη
  have hη0 : 0 < η := div_pos (sub_pos.2 hc) (by positivity)
  have hη' : η * ‖r‖ ≤ ℓ' (r, 0) - c := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg r, sub_pos.2 hc]
  have hm : Tendsto (fun q : ℝ × Z ↦ ((x₀ + q.1 • r, q.2), (x₀, q.2))) (𝓝 (0, z₀))
      (𝓝 ((x₀, z₀), (x₀, z₀))) :=
    (by fun_prop : Continuous fun q : ℝ × Z ↦ ((x₀ + q.1 • r, q.2), (x₀, q.2))).tendsto' _ _
      (by simp)
  filter_upwards [hm.eventually ((hasStrictFDerivAt_iff_isLittleO.1 h).def hη0)] with q hq hq0
  have e : (x₀ + q.1 • r, q.2) - (x₀, q.2) = q.1 • ((r, 0) : X × Z) := by
    ext <;> simp
  have hn : ‖((r, 0) : X × Z)‖ = ‖r‖ := by simp
  rw [e, map_smul, norm_smul, hn, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0,
    smul_eq_mul, abs_le] at hq
  nlinarith [mul_le_mul_of_nonneg_left hη' hq0.le, hq.1]

/-- A first-order upper estimate in the first variable that is uniform in the second, for a
strictly differentiable function. -/
theorem eventually_sub_le_mul_of_hasStrictFDerivAt {ℓ : X × Z → ℝ} {ℓ' : StrongDual ℝ (X × Z)}
    {x₀ : X} {z₀ : Z} (h : HasStrictFDerivAt ℓ ℓ' (x₀, z₀)) {r : X} {c : ℝ}
    (hc : ℓ' (r, 0) < c) :
    ∀ᶠ q : ℝ × Z in 𝓝 (0, z₀), 0 < q.1 → ℓ (x₀ + q.1 • r, q.2) - ℓ (x₀, q.2) ≤ q.1 * c := by
  have := eventually_mul_le_sub_of_hasStrictFDerivAt h.neg (r := r) (c := -c)
    (by simpa using hc)
  filter_upwards [this] with q hq hq0
  have := hq hq0
  simp only [Pi.neg_apply] at this
  linarith

/-- A tube lemma: a property holding near `(0, z)` for all `z` in a compact set `K` holds on
`W` for all small `t`, for some open `W ⊇ K`. -/
theorem exists_isOpen_eventually_forall {Y : Type*} [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) {P : ℝ → Y → Prop} (hP : ∀ z ∈ K, ∀ᶠ q : ℝ × Y in 𝓝 (0, z), P q.1 q.2) :
    ∃ W : Set Y, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ W, P t z := by
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK (isOpen_interior (s := {q : ℝ × Y | P q.1 q.2}))
    (by
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      obtain rfl : t = 0 := ht
      exact mem_interior_iff_mem_nhds.2 (hP z hz))
  exact ⟨v, hv, hKv, Filter.mem_of_superset (hu.mem_nhds (h0u rfl)) fun t ht z hz ↦
    (interior_subset (huv (mk_mem_prod ht hz)) : (t, z) ∈ {q : ℝ × Y | P q.1 q.2})⟩

/-- Bounds for a difference quotient from bounds in `EReal`. -/
theorem slope_bounds_of_coe_le {a : EReal} {μ₀ t c₁ c₂ : ℝ} (ht : 0 < t)
    (h1 : ((μ₀ + t * c₁ : ℝ) : EReal) ≤ a) (h2 : a ≤ ((μ₀ + t * c₂ : ℝ) : EReal)) :
    c₁ ≤ (a.toReal - μ₀) / t ∧ (a.toReal - μ₀) / t ≤ c₂ := by
  have ha1 : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
  have ha2 : a ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  lift a to ℝ using ⟨ha1, ha2⟩
  rw [EReal.coe_le_coe_iff] at h1 h2
  rw [EReal.toReal_coe, le_div_iff₀ ht, div_le_iff₀ ht]
  constructor <;> linarith

end Auxiliary

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ} {x₀ : E} {y₀ : F}

/-- The partial gradient `∇ₓL(x, y, λ)` of the Lagrangian `L = φ + ∑ λᵢ gᵢ` of the follower's
problem with respect to the leader's variable. -/
noncomputable def lagrangianGradient (φ : E × F → ℝ) (g : ι → E × F → ℝ) (x : E) (y : F)
    (lam : ι → ℝ) : StrongDual ℝ E :=
  (fderiv ℝ φ (x, y)).comp (inl ℝ E F) + ∑ i, lam i • (fderiv ℝ (g i) (x, y)).comp (inl ℝ E F)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem lagrangianGradient_apply (x : E) (y : F) (lam : ι → ℝ) (r : E) :
    lagrangianGradient φ g x y lam r =
      fderiv ℝ φ (x, y) (r, 0) + ∑ i, lam i * fderiv ℝ (g i) (x, y) (r, 0) := by
  simp [lagrangianGradient]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem continuous_lagrangianGradient_apply (x : E) (y : F) (r : E) :
    Continuous fun lam : ι → ℝ ↦ lagrangianGradient φ g x y lam r := by
  simp only [lagrangianGradient_apply]
  exact continuous_const.add
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The Lagrangian `L(·, ·, λ)` is strictly differentiable where the data are `C¹`, and its
derivative in a direction `(r, 0)` is `∇ₓL r`. -/
theorem hasStrictFDerivAt_lagrangian {x : E} {y : F} (hφ : ContDiffAt ℝ 1 φ (x, y))
    (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x, y)) (lam : ι → ℝ) :
    ∃ D : StrongDual ℝ (E × F), HasStrictFDerivAt (fun p ↦ φ p + ∑ i, lam i * g i p) D (x, y) ∧
      ∀ r, D (r, 0) = lagrangianGradient φ g x y lam r :=
  ⟨fderiv ℝ φ (x, y) + ∑ i, lam i • fderiv ℝ (g i) (x, y),
    (hφ.hasStrictFDerivAt one_ne_zero).add (HasStrictFDerivAt.fun_sum fun i _ ↦
      ((hg i).hasStrictFDerivAt one_ne_zero).const_mul (lam i)),
    fun r ↦ by simp [lagrangianGradient]⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For `C¹` data, `∇ₓL(x, y, λ) r` is continuous in `(y, λ)`. -/
theorem continuous_lagrangianGradient_prod (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (x r : E) : Continuous fun p : F × (ι → ℝ) ↦ lagrangianGradient φ g x p.1 p.2 r := by
  have hDc : ∀ u : E × F → ℝ, ContDiff ℝ 1 u →
      Continuous fun p : F × (ι → ℝ) ↦ fderiv ℝ u (x, p.1) (r, 0) := fun u hu ↦
    ((hu.continuous_fderiv one_ne_zero).comp
      (by fun_prop : Continuous fun p : F × (ι → ℝ) ↦ (x, p.1))).clm_apply continuous_const
  simp only [lagrangianGradient_apply]
  exact (hDc φ hφ).add (continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp continuous_snd).mul (hDc (g i) (hg i)))

/-! ### Linear programming duality for the multiplier set -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Duality of the linear programs (4.51) and (4.52) of [Dempe 2002]: under (MFCQ), for every
`b` there are a multiplier `λ ∈ Λ(x̄, ȳ)` and a direction `d` with
`∇_y φ d ≤ ∑ λᵢ bᵢ` and `∇_y gᵢ d + bᵢ ≤ 0` for the active constraints. -/
theorem exists_lowerMultiplier_direction (hne : (lowerMultipliers φ g x₀ y₀).Nonempty)
    (hreg : LowerPLI g x₀ y₀) (b : ι → ℝ) :
    ∃ lam ∈ lowerMultipliers φ g x₀ y₀, ∃ d : F,
      fderiv ℝ (fun z ↦ φ (x₀, z)) y₀ d ≤ ∑ i, lam i * b i ∧
      ∀ i, g i (x₀, y₀) = 0 → fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ d + b i ≤ 0 := by
  classical
  obtain ⟨lam₁, hlam₁, hmax⟩ := (isCompact_lowerMultipliers hreg).exists_isMaxOn hne
    (f := fun lam : ι → ℝ ↦ ∑ i, lam i * b i)
    (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const).continuousOn
  by_contra hcon
  set A : StrongDual ℝ F := fderiv ℝ (fun z ↦ φ (x₀, z)) y₀ with hA
  set G : ι → StrongDual ℝ F := fun i ↦ fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ with hG
  set v : ℝ := ∑ i, lam₁ i * b i with hv
  set χ : ι → ℝ := fun i ↦ if g i (x₀, y₀) = 0 then 1 else 0 with hχ
  let a : Option ι → StrongDual ℝ (F × ℝ) := fun j ↦ j.elim
    (-(A.comp (ContinuousLinearMap.fst ℝ F ℝ)) + v • ContinuousLinearMap.snd ℝ F ℝ)
    (fun i ↦ χ i • (-((G i).comp (ContinuousLinearMap.fst ℝ F ℝ)) -
      b i • ContinuousLinearMap.snd ℝ F ℝ))
  have ha0 : ∀ d s, a none (d, s) = -(A d) + v * s := fun d s ↦ by simp [a]
  have ha1 : ∀ i d s, a (some i) (d, s) = χ i * (-(G i d) - b i * s) := fun i d s ↦ by
    simp [a]
  have hF : ∀ z : F × ℝ, (∀ j, 0 ≤ a j z) → 0 ≤ (-(ContinuousLinearMap.snd ℝ F ℝ)) z := by
    rintro ⟨d, s⟩ hz
    by_contra hs
    have hs0 : 0 < s := by simpa using hs
    refine hcon ⟨lam₁, hlam₁, s⁻¹ • d, ?_, fun i hi ↦ ?_⟩
    · have h := hz none
      rw [ha0] at h
      rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hs0]
      linarith
    · have h := hz (some i)
      rw [ha1, hχ] at h
      simp only [if_pos hi, one_mul] at h
      have h' : s⁻¹ * G i d ≤ -b i := by
        rw [inv_mul_le_iff₀ hs0]
        linarith
      rw [map_smul, smul_eq_mul]
      linarith
  obtain ⟨μ, hμ, hsum⟩ := exists_nonneg_eq_sum_of_forall_nonneg a _ hF
  set τ := μ none with hτ
  set ν : ι → ℝ := fun i ↦ μ (some i) * χ i with hν
  have hχ0 : ∀ i, 0 ≤ χ i := fun i ↦ by
    simp only [hχ]
    split_ifs <;> norm_num
  have hν0 : ∀ i, 0 ≤ ν i := fun i ↦ mul_nonneg (hμ _) (hχ0 i)
  have hνin : ∀ i, g i (x₀, y₀) ≠ 0 → ν i = 0 := fun i hi ↦ by simp [hν, hχ, hi]
  have key : ∀ d s, -s = τ * (-(A d) + v * s) - ∑ i, ν i * G i d - s * ∑ i, ν i * b i := by
    intro d s
    have h := congrArg (fun T : StrongDual ℝ (F × ℝ) ↦ T (d, s)) hsum
    simp only [Fintype.sum_option, add_apply, sum_apply, smul_apply, smul_eq_mul, ha0, ha1,
      neg_apply, ContinuousLinearMap.coe_snd'] at h
    rw [h, Finset.mul_sum, sub_sub, ← Finset.sum_add_distrib, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [hν]; ring
  have hd : ∀ d, τ * A d + ∑ i, ν i * G i d = 0 := fun d ↦ by
    have := key d 0
    simp only [mul_zero, add_zero, zero_mul, sub_zero, neg_zero] at this
    linarith
  have h1 : τ * v - ∑ i, ν i * b i = -1 := by
    have := key 0 1
    simp only [map_zero, neg_zero, zero_add, mul_one, mul_zero, Finset.sum_const_zero, sub_zero,
      one_mul] at this
    linarith
  rcases (hμ none).eq_or_lt with hτ0 | hτ0
  · -- `τ = 0`: (MFCQ) gives `ν = 0`
    have hτ0' : τ = 0 := hτ0.symm
    have hν' : ν = 0 := hreg ν hν0 (fun i hi ↦ hνin i hi.ne) (ContinuousLinearMap.ext fun d ↦ by
      have := hd d
      rw [hτ0', zero_mul, zero_add] at this
      simpa [sum_apply, smul_apply, hG] using this)
    rw [hτ0', hν'] at h1
    simp at h1
  · -- `τ > 0`: `ν / τ` is a multiplier with a larger value
    have hτpos : 0 < τ := hτ0
    have hlam' : (fun i ↦ ν i / τ) ∈ lowerMultipliers φ g x₀ y₀ := by
      refine ⟨hlam₁.1, fun i ↦ div_nonneg (hν0 i) hτpos.le, fun i ↦ ?_, ?_⟩
      · show ν i / τ * g i (x₀, y₀) = 0
        by_cases hi : g i (x₀, y₀) = 0
        · rw [hi, mul_zero]
        · rw [hνin i hi, zero_div, zero_mul]
      · refine ContinuousLinearMap.ext fun d ↦ ?_
        have e : ∑ i, ν i / τ * G i d = (∑ i, ν i * G i d) / τ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
        have h3 : ∑ i, ν i * G i d = -(τ * A d) := by linarith [hd d]
        simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply]
        change A d + ∑ i, ν i / τ * G i d = 0
        rw [e, h3, neg_div, mul_div_cancel_left₀ _ hτpos.ne', add_neg_cancel]
    have h2 : ∑ i, ν i / τ * b i ≤ v := hmax hlam'
    have e : ∑ i, ν i / τ * b i = (∑ i, ν i * b i) / τ := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [e, div_le_iff₀ hτpos] at h2
    linarith

/-! ### Thm. 4.15: bounds for the Dini directional derivatives -/

omit [FiniteDimensional ℝ E] in
/-- Thm. 4.15 of [Dempe 2002], upper bound: if `ȳ` is feasible at `x̄` with `Λ(x̄, ȳ) ≠ ∅` and
(MFCQ) holds at `(x̄, ȳ)`, then for every `c > max {∇ₓL(x̄, ȳ, λ) r | λ ∈ Λ(x̄, ȳ)}`,
`μ(x̄ + t r) ≤ φ(x̄, ȳ) + t c` for small `t > 0`. For `ȳ ∈ Ψ(x̄)` this is
`D⁺μ(x̄; r) ≤ max {∇ₓL(x̄, ȳ, λ) r | λ ∈ Λ(x̄, ȳ)}`. -/
theorem eventually_lowerValue_add_smul_le (hφ : DifferentiableAt ℝ φ (x₀, y₀))
    (hg : ∀ i, DifferentiableAt ℝ (g i) (x₀, y₀)) (hne : (lowerMultipliers φ g x₀ y₀).Nonempty)
    (hreg : LowerPLI g x₀ y₀) {r : E} {c : ℝ}
    (hc : ∀ lam ∈ lowerMultipliers φ g x₀ y₀, lagrangianGradient φ g x₀ y₀ lam r < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), lowerValue φ g (x₀ + t • r) ≤ ((φ (x₀, y₀) + t * c : ℝ) : EReal) := by
  have hK := isCompact_lowerMultipliers (φ := φ) hreg
  obtain ⟨lam₁, hlam₁, hmax₁⟩ := hK.exists_isMaxOn hne
    (continuous_lagrangianGradient_apply (φ := φ) (g := g) x₀ y₀ r).continuousOn
  obtain ⟨lam₂, hlam₂, hmax₂⟩ := hK.exists_isMaxOn hne (f := fun lam : ι → ℝ ↦ ∑ i, lam i)
    (continuous_finsetSum _ fun i _ ↦ continuous_apply i).continuousOn
  set m := lagrangianGradient φ g x₀ y₀ lam₁ r with hm
  set M := ∑ i, lam₂ i with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ hlam₂.2.1 i
  have hε : 0 < c - m := sub_pos.2 (hc lam₁ hlam₁)
  set δ := (c - m) / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδM : δ * M ≤ (c - m) / 2 := by
    have : δ * (M + 1) = (c - m) / 2 := by
      rw [hδ]
      field_simp
    nlinarith
  obtain ⟨lam, hlam, d, hd1, hd2⟩ := exists_lowerMultiplier_direction hne hreg
    (fun i ↦ fderiv ℝ (g i) (x₀, y₀) (r, 0) + δ)
  have hsplit : ∀ T : StrongDual ℝ (E × F), T (r, d) = T (r, 0) + T (0, d) := fun T ↦ by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hsec : ∀ u : E × F → ℝ, DifferentiableAt ℝ u (x₀, y₀) →
      fderiv ℝ (fun z ↦ u (x₀, z)) y₀ d = fderiv ℝ u (x₀, y₀) (0, d) := fun u hu ↦ by
    rw [fderiv_section hu]
    simp
  -- the objective decreases at rate less than `c` along `(r, d)`
  have hlt : fderiv ℝ φ (x₀, y₀) (r, d) < c := by
    have h1 : ∑ i, lam i * (fderiv ℝ (g i) (x₀, y₀) (r, 0) + δ) =
        ∑ i, lam i * fderiv ℝ (g i) (x₀, y₀) (r, 0) + δ * ∑ i, lam i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have h2 : ∑ i, lam i ≤ M := hmax₂ hlam
    have h3 : lagrangianGradient φ g x₀ y₀ lam r ≤ m := hmax₁ hlam
    rw [lagrangianGradient_apply] at h3
    rw [hsplit, ← hsec φ hφ]
    nlinarith [mul_le_mul_of_nonneg_left h2 hδ0.le]
  have h1 := eventually_lt_add_mul_of_hasFDerivAt hφ.hasFDerivAt (w := (r, d)) hlt
  have h2 : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), g i ((x₀, y₀) + t • (r, d)) ≤ 0 := fun i ↦ by
    by_cases hi : g i (x₀, y₀) = 0
    · have hneg : fderiv ℝ (g i) (x₀, y₀) (r, d) < 0 := by
        have := hd2 i hi
        rw [hsec (g i) (hg i)] at this
        rw [hsplit]
        linarith
      refine (eventually_lt_add_mul_of_hasFDerivAt (hg i).hasFDerivAt hneg).mono fun t ht ↦ ?_
      rw [hi, mul_zero, add_zero] at ht
      exact ht.le
    · exact (((hg i).continuousAt.tendsto.comp (tendsto_add_smul_nhdsGT _ _)).eventually_lt_const
        (lt_of_le_of_ne (hlam.1 i) hi)).mono fun t ht ↦ le_of_lt ht
  filter_upwards [h1, eventually_all.2 h2] with t ht hgt
  have e : (x₀, y₀) + t • (r, d) = (x₀ + t • r, y₀ + t • d) := by simp
  rw [e] at ht
  simp only [e] at hgt
  exact (VariationalAnalysis.lowerValue_le
    (show y₀ + t • d ∈ lowerFeasible g (x₀ + t • r) from hgt)).trans
    (EReal.coe_le_coe_iff.2 ht.le)

/-- Thm. 4.15 of [Dempe 2002], lower bound: under the assumptions of Thm. 4.14, for every
`c < min {∇ₓL(x̄, y, λ) r | y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`, `μ(x̄) + t c ≤ μ(x̄ + t r)` for small
`t > 0`, i.e. `D₊μ(x̄; r) ≥ min min ∇ₓL(x̄, y, λ) r`. -/
theorem eventually_le_lowerValue_add_smul (hgc : ∀ i, Continuous (g i)) (hφc : Continuous φ)
    (hb : LocallyBoundedAt (lowerFeasible g) x₀) (hne : (lowerFeasible g x₀).Nonempty)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y) {r : E} {c μ₀ : ℝ}
    (hμ₀ : lowerValue φ g x₀ = μ₀)
    (hc : ∀ y ∈ lowerSolution φ g x₀, ∀ u ∈ lagrangianGradients φ g x₀ y, c < u r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ((μ₀ + t * c : ℝ) : EReal) ≤ lowerValue φ g (x₀ + t • r) := by
  obtain ⟨U, hU, L, μ, hμ, hL, hsub⟩ :=
    exists_clarkeSubdiff_lowerValue_subset hgc hφc hb hne hφ hg hreg
  have hconv : Convex ℝ {ξ : StrongDual ℝ E | c < ξ r} :=
    convex_halfSpace_gt (f := fun ξ : StrongDual ℝ E ↦ ξ r) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ c
  have hall : ∀ ξ ∈ clarkeSubdiff μ x₀, c < ξ r := fun ξ hξ ↦
    convexHull_min (fun u hu ↦ by
      obtain ⟨y, hy, huy⟩ := mem_iUnion₂.1 hu
      exact hc y hy u huy) hconv (hsub hξ)
  obtain ⟨ξ, hξ, hξe⟩ := VariationalAnalysis.exists_mem_clarkeSubdiff_eq hU hL (-r)
  have hlt : clarkeDeriv μ x₀ (-r) < ((-c : ℝ) : EReal) := by
    rw [← hξe, EReal.coe_lt_coe_iff, map_neg]
    exact neg_lt_neg (hall ξ hξ)
  have hev := Filter.eventually_lt_of_limsup_lt hlt
  have htend : Tendsto (fun t : ℝ ↦ (x₀ + t • r, t)) (𝓝[>] 0) (𝓝 x₀ ×ˢ 𝓝[>] 0) :=
    (tendsto_add_smul_nhdsGT x₀ r).prodMk tendsto_id
  have hμ0 : μ x₀ = μ₀ := by
    have := hμ x₀ (mem_of_mem_nhds hU)
    rw [hμ₀] at this
    exact_mod_cast this.symm
  filter_upwards [htend.eventually hev, (tendsto_add_smul_nhdsGT x₀ r).eventually hU,
    self_mem_nhdsWithin] with t ht htU ht0
  have ht0' : 0 < t := ht0
  rw [hμ _ htU, EReal.coe_le_coe_iff]
  rw [EReal.coe_lt_coe_iff] at ht
  simp only [smul_neg, add_neg_cancel_right] at ht
  rw [div_lt_iff₀ ht0'] at ht
  linarith

/-! ### Convex problems: the saddle point inequality -/

section Convex

variable {x : E} {y y' : F} {lam : ι → ℝ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The saddle point inequality for a convex follower's problem: a KKT point `(y, λ)` satisfies
`φ(x, y) ≤ L(x, z, λ)` for all `z`. -/
theorem le_lagrangian_of_isLowerKKT (hconv : IsConvexLower φ g x)
    (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, DifferentiableAt ℝ (fun z ↦ g i (x, z)) y) (h : IsLowerKKT φ g x y lam) (z : F) :
    φ (x, y) ≤ φ (x, z) + ∑ i, lam i * g i (x, z) := by
  obtain ⟨-, hlam, hcs, hstat⟩ := h
  have h1 := Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (fun z ↦ φ (x, z)) y)
    hφ.hasFDerivAt hconv.1 (mem_univ y) z (mem_univ z)
  have h2 : ∀ i, g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (z - y) ≤ g i (x, z) := fun i ↦
    Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (fun z ↦ g i (x, z)) y)
      (hg i).hasFDerivAt (hconv.2 i) (mem_univ y) z (mem_univ z)
  have hs := congrArg (fun T : F →L[ℝ] ℝ ↦ T (z - y)) hstat
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at hs
  have h4 : ∑ i, lam i * (g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (z - y)) ≤
      ∑ i, lam i * g i (x, z) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h2 i) (hlam i)
  simp only [mul_add, hcs, zero_add] at h4
  beta_reduce at h1
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- For a convex follower's problem the multiplier set `Λ(x, y)` does not depend on the solution
`y ∈ Ψ(x)`. -/
theorem lowerMultipliers_subset_of_isConvexLower (hconv : IsConvexLower φ g x)
    (hdiff : IsDifferentiableLower φ g x) (hy : y ∈ lowerSolution φ g x)
    (hy' : y' ∈ lowerSolution φ g x) :
    lowerMultipliers φ g x y ⊆ lowerMultipliers φ g x y' := by
  intro lam hlam
  have hsad := le_lagrangian_of_isLowerKKT hconv (hdiff y).1 (hdiff y).2 hlam
  have heq : φ (x, y) = φ (x, y') := EReal.coe_eq_coe_iff.1 (hy.2.trans hy'.2.symm)
  have hfeas' : ∀ i, g i (x, y') ≤ 0 := hy'.1
  have hnp : ∀ i ∈ Finset.univ, lam i * g i (x, y') ≤ 0 := fun i _ ↦
    mul_nonpos_of_nonneg_of_nonpos (hlam.2.1 i) (hfeas' i)
  have hsum0 : ∑ i, lam i * g i (x, y') = 0 :=
    le_antisymm (Finset.sum_nonpos hnp) (by linarith [hsad y'])
  have hmin : IsLocalMin (fun z ↦ φ (x, z) + ∑ i, lam i * g i (x, z)) y' :=
    Filter.Eventually.of_forall fun z ↦ by
      show φ (x, y') + ∑ i, lam i * g i (x, y') ≤ φ (x, z) + ∑ i, lam i * g i (x, z)
      rw [hsum0]
      linarith [hsad z]
  have hℓ : HasFDerivAt (fun z ↦ φ (x, z) + ∑ i, lam i * g i (x, z))
      (fderiv ℝ (fun z ↦ φ (x, z)) y' + ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y') y' :=
    (hdiff y').1.hasFDerivAt.add (HasFDerivAt.fun_sum fun i _ ↦
      ((hdiff y').2 i).hasFDerivAt.const_mul (lam i))
  exact ⟨hfeas', hlam.2.1, fun i ↦ (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hsum0 i
    (Finset.mem_univ i), by rw [← hℓ.fderiv]; exact hmin.fderiv_eq_zero⟩

end Convex

/-! ### Thm. 4.16: directional differentiability for convex problems -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The lower bound in Thm. 4.16 of [Dempe 2002]: if the follower's problem is convex at `x̄` and
`Ψ` is upper semicontinuous at `x̄`, then for every
`c < min_{y ∈ Ψ(x̄)} max_{λ ∈ Λ(x̄, y)} ∇ₓL(x̄, y, λ) r`, `μ(x̄) + t c ≤ μ(x̄ + t r)` for small
`t > 0`. -/
theorem eventually_le_lowerValue_add_smul_of_isConvexLower (hconv : IsConvexLower φ g x₀)
    (hφ : ∀ y ∈ lowerSolution φ g x₀, ContDiffAt ℝ 1 φ (x₀, y))
    (hg : ∀ y ∈ lowerSolution φ g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hK : IsCompact (lowerSolution φ g x₀))
    (husc : UpperHemicontinuousAt (lowerSolution φ g) x₀)
    (hex : ∀ᶠ x in 𝓝 x₀, (lowerFeasible g x).Nonempty → (lowerSolution φ g x).Nonempty)
    {r : E} {c μ₀ : ℝ} (hμ₀ : lowerValue φ g x₀ = μ₀)
    (hc : ∀ y ∈ lowerSolution φ g x₀, ∃ lam ∈ lowerMultipliers φ g x₀ y,
      c < lagrangianGradient φ g x₀ y lam r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ((μ₀ + t * c : ℝ) : EReal) ≤ lowerValue φ g (x₀ + t • r) := by
  have hP : ∀ y ∈ lowerSolution φ g x₀, ∀ᶠ q : ℝ × F in 𝓝 (0, y), 0 < q.1 →
      ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ z, μ₀ ≤ φ (x₀, z) + ∑ i, lam i * g i (x₀, z)) ∧
        q.1 * c ≤ (φ (x₀ + q.1 • r, q.2) + ∑ i, lam i * g i (x₀ + q.1 • r, q.2)) -
          (φ (x₀, q.2) + ∑ i, lam i * g i (x₀, q.2)) := by
    intro y hy
    obtain ⟨lam, hlam, hlt⟩ := hc y hy
    obtain ⟨D, hD, hDr⟩ := hasStrictFDerivAt_lagrangian (hφ y hy) (hg y hy) lam
    have hμy : μ₀ = φ (x₀, y) := by
      have := (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy).symm.trans hμ₀
      exact_mod_cast this.symm
    have hsec : ∀ u : E × F → ℝ, ContDiffAt ℝ 1 u (x₀, y) →
        DifferentiableAt ℝ (fun z ↦ u (x₀, z)) y := fun u hu ↦
      (hu.differentiableAt one_ne_zero).comp y (hasFDerivAt_prodMk_right x₀ y).differentiableAt
    have hsad := le_lagrangian_of_isLowerKKT hconv (hsec φ (hφ y hy))
      (fun i ↦ hsec (g i) (hg y hy i)) hlam
    refine (eventually_mul_le_sub_of_hasStrictFDerivAt hD (r := r) (c := c)
      (by rw [hDr]; exact hlt)).mono fun q hq hq0 ↦ ⟨lam, hlam.2.1, fun z ↦ ?_, hq hq0⟩
    rw [hμy]
    exact hsad z
  obtain ⟨W, hWo, hKW, hT⟩ := exists_isOpen_eventually_forall hK
    (P := fun t y ↦ 0 < t → ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧
      (∀ z, μ₀ ≤ φ (x₀, z) + ∑ i, lam i * g i (x₀, z)) ∧
        t * c ≤ (φ (x₀ + t • r, y) + ∑ i, lam i * g i (x₀ + t • r, y)) -
          (φ (x₀, y) + ∑ i, lam i * g i (x₀, y))) hP
  have hline := tendsto_add_smul_nhdsGT x₀ r
  filter_upwards [hline.eventually (husc W hWo hKW), hline.eventually hex,
    nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with t h1 h2 h3 ht
  by_cases hG : (lowerFeasible g (x₀ + t • r)).Nonempty
  swap
  · rw [lowerValue_eq_top hG]
    exact le_top
  obtain ⟨y, hy⟩ := h2 hG
  obtain ⟨lam, hl0, hsad, hdiff⟩ := h3 y (h1 hy) ht
  rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy, EReal.coe_le_coe_iff]
  have hy' : ∀ i, g i (x₀ + t • r, y) ≤ 0 := hy.1
  have hneg : ∑ i, lam i * g i (x₀ + t • r, y) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hl0 i) (hy' i)
  linarith [hsad y]

/-- Thm. 4.16 of [Dempe 2002]: if the follower's problem has `C¹` data, a feasible-set map that
is locally bounded at `x̄`, is convex at `x̄` and satisfies Slater's condition there, then the
optimal value function is directionally differentiable at `x̄` with
`μ'(x̄; r) = min_{y ∈ Ψ(x̄)} max_{λ ∈ Λ(x̄, y)} ∇ₓL(x̄, y, λ) r`. -/
theorem exists_tendsto_slope_lowerValue_of_isConvexLower (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hconv : IsConvexLower φ g x₀) (hS : SlaterAt g x₀) (r : E) :
    ∃ v : ℝ, Tendsto (fun t : ℝ ↦ ((lowerValue φ g (x₀ + t • r)).toReal -
        (lowerValue φ g x₀).toReal) / t) (𝓝[>] 0) (𝓝 v) ∧
      (∃ y ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y,
        lagrangianGradient φ g x₀ y lam r ≤ v) ∧
      ∀ y ∈ lowerSolution φ g x₀, ∃ lam ∈ lowerMultipliers φ g x₀ y,
        v ≤ lagrangianGradient φ g x₀ y lam r := by
  have hφc := hφ.continuous
  have hgc := fun i ↦ (hg i).continuous
  have hφd := hφ.differentiable one_ne_zero
  have hgd := fun i ↦ (hg i).differentiable one_ne_zero
  have hdl : IsDifferentiableLower φ g x₀ := fun y ↦
    ⟨(hφd (x₀, y)).comp y (hasFDerivAt_prodMk_right x₀ y).differentiableAt,
      fun i ↦ (hgd i (x₀, y)).comp y (hasFDerivAt_prodMk_right x₀ y).differentiableAt⟩
  have hpli : ∀ y ∈ lowerFeasible g x₀, LowerPLI g x₀ y := fun y hy ↦
    lowerPLI_of_slaterAt hconv.2 (hdl y).2 hy hS
  have hregall : ∀ y ∈ lowerFeasible g x₀, LowerLevelRegular g x₀ y := fun y hy ↦
    (lowerPLI_iff_lowerLevelRegular fun i ↦ hgd i (x₀, y)).1 (hpli y hy)
  have husc : UpperHemicontinuousAt (lowerSolution φ g) x₀ :=
    upperHemicontinuousAt_lowerSolution_of_regular hgc (fun y _ i ↦ (hg i).contDiffAt) hregall
      (eventually_exists_isCompact_lowerFeasible hb).self_of_nhds hφc
  have hex := eventually_lowerSolution_nonempty hgc hφc hb
  have hKΨ : IsCompact (lowerSolution φ g x₀) := by
    rw [← solutionMap_lowerFeasible]
    exact isCompact_solutionMap (eventually_isCompact_lowerFeasible hgc hb).self_of_nhds hφc
  obtain ⟨z, hz⟩ := hS
  obtain ⟨y₀, hy₀⟩ := hex.self_of_nhds ⟨z, fun i ↦ (hz i).le⟩
  have hμ₀ : lowerValue φ g x₀ = (φ (x₀, y₀) : ℝ) :=
    VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy₀
  have hval : ∀ y ∈ lowerSolution φ g x₀, φ (x₀, y) = φ (x₀, y₀) := fun y hy ↦
    EReal.coe_eq_coe_iff.1 (hy.2.trans hy₀.2.symm)
  -- the multiplier set
  set Λ₀ := lowerMultipliers φ g x₀ y₀ with hΛ₀
  have hΛc : IsCompact Λ₀ := isCompact_lowerMultipliers (hpli y₀ hy₀.1)
  have hΛeq : ∀ y ∈ lowerSolution φ g x₀, lowerMultipliers φ g x₀ y = Λ₀ := fun y hy ↦
    Subset.antisymm (lowerMultipliers_subset_of_isConvexLower hconv hdl hy hy₀)
      (lowerMultipliers_subset_of_isConvexLower hconv hdl hy₀ hy)
  have hΛne : Λ₀.Nonempty := by
    have h : y₀ ∈ solutionMap φ (lowerFeasible g) x₀ := by rwa [solutionMap_lowerFeasible]
    exact exists_isLowerKKT_of_mem_solutionMap h (hdl y₀).1 (fun i ↦
      ((hg i).comp (by fun_prop : ContDiff ℝ 1 fun z : F ↦ (x₀, z))).contDiffAt) (hpli y₀ hy₀.1)
  -- `m(y) = max_λ ∇ₓL(x̄, y, λ) r`
  have hcont := continuous_lagrangianGradient_prod hφ hg x₀ r
  set m : F → ℝ := fun y ↦ sSup ((fun lam ↦ lagrangianGradient φ g x₀ y lam r) '' Λ₀) with hm
  have hmc : Continuous m :=
    hΛc.continuous_sSup (f := fun y lam ↦ lagrangianGradient φ g x₀ y lam r) hcont
  have himg : ∀ y, IsCompact ((fun lam ↦ lagrangianGradient φ g x₀ y lam r) '' Λ₀) := fun y ↦
    hΛc.image (continuous_lagrangianGradient_apply x₀ y r)
  have hle : ∀ y, ∀ lam ∈ Λ₀, lagrangianGradient φ g x₀ y lam r ≤ m y := fun y lam hlam ↦
    le_csSup (himg y).bddAbove (mem_image_of_mem _ hlam)
  have hatt : ∀ y, ∃ lam ∈ Λ₀, lagrangianGradient φ g x₀ y lam r = m y := fun y ↦
    (himg y).sSup_mem (hΛne.image _)
  obtain ⟨ys, hys, hmin⟩ := hKΨ.exists_isMinOn ⟨y₀, hy₀⟩ hmc.continuousOn
  have hupper : ∀ c, m ys < c → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      lowerValue φ g (x₀ + t • r) ≤ ((φ (x₀, y₀) + t * c : ℝ) : EReal) := fun c hc ↦ by
    rw [← hval ys hys]
    exact eventually_lowerValue_add_smul_le (hφd _) (fun i ↦ hgd i _)
      (by rw [hΛeq ys hys]; exact hΛne) (hpli ys hys.1)
      fun lam hlam ↦ (hle ys lam (by rwa [hΛeq ys hys] at hlam)).trans_lt hc
  have hlower : ∀ c, c < m ys → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((φ (x₀, y₀) + t * c : ℝ) : EReal) ≤ lowerValue φ g (x₀ + t • r) := fun c hc ↦
    eventually_le_lowerValue_add_smul_of_isConvexLower hconv (fun y _ ↦ hφ.contDiffAt)
      (fun y _ i ↦ (hg i).contDiffAt) hKΨ husc hex hμ₀ fun y hy ↦ by
        obtain ⟨lam, hlam, he⟩ := hatt y
        exact ⟨lam, by rwa [hΛeq y hy], by rw [he]; exact hc.trans_le (hmin hy)⟩
  refine ⟨m ys, ?_, ⟨ys, hys, fun lam hlam ↦ hle ys lam (by rwa [hΛeq ys hys] at hlam)⟩,
    fun y hy ↦ ?_⟩
  · simp only [hμ₀, EReal.toReal_coe]
    refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
    · filter_upwards [hlower ((c + m ys) / 2) (by linarith), hupper (m ys + 1) (by linarith),
        self_mem_nhdsWithin] with t h1 h2 ht
      exact lt_of_lt_of_le (by linarith) (slope_bounds_of_coe_le ht h1 h2).1
    · filter_upwards [hlower (m ys - 1) (by linarith), hupper ((c + m ys) / 2) (by linarith),
        self_mem_nhdsWithin] with t h1 h2 ht
      exact lt_of_le_of_lt (slope_bounds_of_coe_le ht h1 h2).2 (by linarith)
  · obtain ⟨lam, hlam, he⟩ := hatt y
    exact ⟨lam, by rwa [hΛeq y hy], by rw [he]; exact hmin hy⟩

/-- The upper bound in Thm. 4.16 of [Dempe 2002]: if the follower's problem is convex for all
parameters near `x̄` and satisfies Slater's condition at `x̄`, then for every
`c > max_{λ ∈ Λ} min_{y ∈ Ψ(x̄)} ∇ₓL(x̄, y, λ) r`, `μ(x̄ + t r) ≤ μ(x̄) + t c` for small
`t > 0`. -/
theorem eventually_lowerValue_add_smul_le_of_isConvexLower (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hconv : ∀ᶠ x in 𝓝 x₀, IsConvexLower φ g x) (hS : SlaterAt g x₀) {r : E} {c μ₀ : ℝ}
    (hμ₀ : lowerValue φ g x₀ = μ₀)
    (hc : ∀ y₀ ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y₀,
      ∃ y ∈ lowerSolution φ g x₀, lagrangianGradient φ g x₀ y lam r < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), lowerValue φ g (x₀ + t • r) ≤ ((μ₀ + t * c : ℝ) : EReal) := by
  have hφc := hφ.continuous
  have hgc := fun i ↦ (hg i).continuous
  have hφd := hφ.differentiable one_ne_zero
  have hgd := fun i ↦ (hg i).differentiable one_ne_zero
  have hdl : ∀ x, IsDifferentiableLower φ g x := fun x y ↦
    ⟨(hφd (x, y)).comp y (hasFDerivAt_prodMk_right x y).differentiableAt,
      fun i ↦ (hgd i (x, y)).comp y (hasFDerivAt_prodMk_right x y).differentiableAt⟩
  have hconv₀ := hconv.self_of_nhds
  have hex := eventually_lowerSolution_nonempty hgc hφc hb
  obtain ⟨z, hz⟩ := hS
  have hSl : ∀ᶠ x in 𝓝 x₀, ∀ i, g i (x, z) < 0 := eventually_all.2 fun i ↦
    (((hgc i).comp (continuous_id.prodMk continuous_const)).tendsto x₀).eventually_lt_const (hz i)
  have hpli : ∀ x, IsConvexLower φ g x → (∀ i, g i (x, z) < 0) → ∀ y ∈ lowerFeasible g x,
      LowerPLI g x y := fun x hcx hsx y hy ↦
    lowerPLI_of_slaterAt hcx.2 (hdl x y).2 hy ⟨z, hsx⟩
  have hkkt : ∀ x, IsConvexLower φ g x → (∀ i, g i (x, z) < 0) → ∀ y ∈ lowerSolution φ g x,
      (lowerMultipliers φ g x y).Nonempty := fun x hcx hsx y hy ↦
    exists_isLowerKKT_of_mem_solutionMap (by rwa [solutionMap_lowerFeasible]) (hdl x y).1
      (fun i ↦ ((hg i).comp (by fun_prop : ContDiff ℝ 1 fun w : F ↦ (x, w))).contDiffAt)
      (hpli x hcx hsx y hy.1)
  obtain ⟨y₀, hy₀⟩ := hex.self_of_nhds ⟨z, fun i ↦ (hz i).le⟩
  -- the multipliers at the solutions
  set Γ : E → Set (ι → ℝ) := fun x ↦
    {lam | ∃ y ∈ lowerSolution φ g x, lam ∈ lowerMultipliers φ g x y} with hΓ
  have hΓ₀ : Γ x₀ = lowerMultipliers φ g x₀ y₀ := by
    ext lam
    exact ⟨fun ⟨y, hy, h⟩ ↦ lowerMultipliers_subset_of_isConvexLower hconv₀ (hdl x₀) hy hy₀ h,
      fun h ↦ ⟨y₀, hy₀, h⟩⟩
  have hΓc : IsCompact (Γ x₀) := by
    rw [hΓ₀]
    exact isCompact_lowerMultipliers (hpli x₀ hconv₀ hz y₀ hy₀.1)
  -- first-order estimates, uniform in the multiplier
  have hP : ∀ lam ∈ Γ x₀, ∀ᶠ q : ℝ × (ι → ℝ) in 𝓝 (0, lam), 0 < q.1 →
      ∃ y ∈ lowerSolution φ g x₀,
        (φ (x₀ + q.1 • r, y) + ∑ i, q.2 i * g i (x₀ + q.1 • r, y)) -
          (φ (x₀, y) + ∑ i, q.2 i * g i (x₀, y)) ≤ q.1 * c := by
    rintro lam ⟨y₁, hy₁, hlam⟩
    obtain ⟨y, hy, hlt⟩ := hc y₁ hy₁ lam hlam
    have hℓ : ContDiff ℝ 1 (fun q : E × (ι → ℝ) ↦ φ (q.1, y) + ∑ i, q.2 i * g i (q.1, y)) := by
      fun_prop
    have hstrict := hℓ.contDiffAt.hasStrictFDerivAt one_ne_zero (x := (x₀, lam))
    have hpart : HasFDerivAt (fun x ↦ φ (x, y) + ∑ i, lam i * g i (x, y))
        (lagrangianGradient φ g x₀ y lam) x₀ := by
      unfold lagrangianGradient
      exact ((hφd (x₀, y)).hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_left x₀ y)).add
        (HasFDerivAt.fun_sum fun i _ ↦
          ((hgd i (x₀, y)).hasFDerivAt.comp x₀ (hasFDerivAt_prodMk_left x₀ y)).const_mul (lam i))
    have hchain := HasFDerivAt.comp (f := fun x : E ↦ (x, lam)) x₀ hstrict.hasFDerivAt
      (hasFDerivAt_prodMk_left x₀ lam)
    have heq := congrArg (fun T : StrongDual ℝ E ↦ T r) (hchain.unique hpart)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inl_apply] at heq
    exact (eventually_sub_le_mul_of_hasStrictFDerivAt hstrict (r := r) (c := c)
      (by rw [heq]; exact hlt)).mono fun q hq hq0 ↦ ⟨y, hy, hq hq0⟩
  obtain ⟨W, hWo, hΓW, hT⟩ := exists_isOpen_eventually_forall hΓc
    (P := fun t lam ↦ 0 < t → ∃ y ∈ lowerSolution φ g x₀,
      (φ (x₀ + t • r, y) + ∑ i, lam i * g i (x₀ + t • r, y)) -
        (φ (x₀, y) + ∑ i, lam i * g i (x₀, y)) ≤ t * c) hP
  -- `Γ` is upper semicontinuous at `x̄`
  have husc : UpperHemicontinuousAt Γ x₀ := by
    obtain ⟨U, hU, hB⟩ := hb
    refine upperHemicontinuousAt_of_mem_closure_graph (fun lam hmem ↦ ?_) ?_
    · obtain ⟨p, hpΓ, hp⟩ := mem_closure_iff_seq_limit.1 hmem
      have hpΓ' : ∀ n, ∃ y ∈ lowerSolution φ g (p n).1,
          (p n).2 ∈ lowerMultipliers φ g (p n).1 y := hpΓ
      choose yn hyn hln using hpΓ'
      have hfst : Tendsto (fun n ↦ (p n).1) atTop (𝓝 x₀) := (continuous_fst.tendsto _).comp hp
      have hsnd : Tendsto (fun n ↦ (p n).2) atTop (𝓝 lam) := (continuous_snd.tendsto _).comp hp
      have hfreq : ∃ᶠ n in atTop, yn n ∈ closure (⋃ x ∈ U, lowerFeasible g x) :=
        ((hfst.eventually hU).mono fun n hn ↦
          subset_closure (mem_biUnion hn (hyn n).1)).frequently
      obtain ⟨yb, -, σ, hσ, hyσ⟩ := hB.isCompact_closure.tendsto_subseq' hfreq
      have htend : Tendsto (fun n ↦ (((p (σ n)).1, yn (σ n)), (p (σ n)).2)) atTop
          (𝓝 ((x₀, yb), lam)) :=
        ((hfst.comp hσ.tendsto_atTop).prodMk_nhds hyσ).prodMk_nhds
          (hsnd.comp hσ.tendsto_atTop)
      have hmemΛ : lam ∈ lowerMultipliers φ g x₀ yb :=
        (isClosed_graph_lowerMultipliers hφ hg).mem_of_tendsto htend
          (Eventually.of_forall fun n ↦ hln (σ n))
      have hyb := mem_solutionMap_of_isLowerKKT hconv₀ (hdl x₀ yb).1 (hdl x₀ yb).2 hmemΛ
      rw [solutionMap_lowerFeasible] at hyb
      exact ⟨yb, hyb, hmemΛ⟩
    · -- a bound for the multipliers from Slater's condition
      obtain ⟨C₁, hC₁⟩ := ((isCompact_closedBall x₀ 1).prod
        hB.isCompact_closure).exists_bound_of_continuousOn hφc.continuousOn
      set σ : ι → ℝ := fun i ↦ -g i (x₀, z) / 2 with hσ
      have hσ0 : ∀ i, 0 < σ i := fun i ↦ by
        show 0 < -g i (x₀, z) / 2
        linarith [hz i]
      have hSl' : ∀ᶠ x in 𝓝 x₀, ∀ i, g i (x, z) < -σ i := eventually_all.2 fun i ↦
        (((hgc i).comp (continuous_id.prodMk continuous_const)).tendsto x₀).eventually_lt_const
          (by show g i (x₀, z) < -(-g i (x₀, z) / 2); linarith [hz i])
      have hzB : z ∈ closure (⋃ x ∈ U, lowerFeasible g x) :=
        subset_closure (mem_biUnion (mem_of_mem_nhds hU)
          (show z ∈ lowerFeasible g x₀ from fun i ↦ (hz i).le))
      refine ⟨{x | x ∈ U ∧ x ∈ Metric.closedBall x₀ 1 ∧ IsConvexLower φ g x ∧
        ∀ i, g i (x, z) < -σ i}, ?_, Icc 0 (fun i ↦ 2 * C₁ / σ i), isCompact_Icc, ?_⟩
      · filter_upwards [hU, Metric.closedBall_mem_nhds x₀ one_pos, hconv, hSl'] with x h1 h2 h3 h4
          using ⟨h1, h2, h3, h4⟩
      · rintro x ⟨hxU, hxB, hcx, hsx⟩ lam ⟨y, hy, hlam⟩
        have hsad := le_lagrangian_of_isLowerKKT hcx (hdl x y).1 (hdl x y).2 hlam z
        have b1 := hC₁ (x, y) (mk_mem_prod hxB (subset_closure (mem_biUnion hxU hy.1)))
        have b2 := hC₁ (x, z) (mk_mem_prod hxB hzB)
        rw [Real.norm_eq_abs, abs_le] at b1 b2
        refine ⟨fun i ↦ hlam.2.1 i, fun i ↦ ?_⟩
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ lam j * -g j (x, z) := fun j _ ↦
          mul_nonneg (hlam.2.1 j) (by linarith [hsx j, hσ0 j])
        have h1 := Finset.single_le_sum hnn (Finset.mem_univ i)
        have h2 : ∑ j, lam j * -g j (x, z) = -∑ j, lam j * g j (x, z) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
        have h3 : lam i * σ i ≤ lam i * -g i (x, z) :=
          mul_le_mul_of_nonneg_left (by linarith [hsx i]) (hlam.2.1 i)
        show lam i ≤ 2 * C₁ / σ i
        rw [le_div_iff₀ (hσ0 i)]
        linarith
  have hline := tendsto_add_smul_nhdsGT x₀ r
  filter_upwards [hline.eventually (husc W hWo hΓW), hline.eventually hex,
    hline.eventually hconv, hline.eventually hSl, nhdsWithin_le_nhds hT, self_mem_nhdsWithin]
    with t h1 h2 h3 h4 h5 ht
  obtain ⟨y, hy⟩ := h2 ⟨z, fun i ↦ (h4 i).le⟩
  obtain ⟨lam, hlam⟩ := hkkt _ h3 h4 y hy
  obtain ⟨y', hy', hdiff⟩ := h5 lam (h1 ⟨y, hy, hlam⟩) ht
  rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy, EReal.coe_le_coe_iff]
  have hsad := le_lagrangian_of_isLowerKKT h3 (hdl _ y).1 (hdl _ y).2 hlam y'
  have hμy : μ₀ = φ (x₀, y') := by
    have := (VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy').symm.trans hμ₀
    exact_mod_cast this.symm
  have hy'f : ∀ i, g i (x₀, y') ≤ 0 := hy'.1
  have hneg : ∑ i, lam i * g i (x₀, y') ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hlam.2.1 i) (hy'f i)
  linarith

/-- Thm. 4.16 of [Dempe 2002] with both formulas: if the follower's problem has `C¹` data, a
feasible-set map that is locally bounded at `x̄`, is convex for all parameters near `x̄` and
satisfies Slater's condition at `x̄`, then the optimal value function is directionally
differentiable at `x̄` and
`μ'(x̄; r) = min_{y ∈ Ψ(x̄)} max_{λ ∈ Λ} ∇ₓL(x̄, y, λ) r = max_{λ ∈ Λ} min_{y ∈ Ψ(x̄)} ∇ₓL(x̄, y, λ) r`,
where `Λ = Λ(x̄, y)` does not depend on `y ∈ Ψ(x̄)`. -/
theorem exists_tendsto_slope_lowerValue_of_eventually_isConvexLower (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hconv : ∀ᶠ x in 𝓝 x₀, IsConvexLower φ g x) (hS : SlaterAt g x₀) (r : E) :
    ∃ v : ℝ, Tendsto (fun t : ℝ ↦ ((lowerValue φ g (x₀ + t • r)).toReal -
        (lowerValue φ g x₀).toReal) / t) (𝓝[>] 0) (𝓝 v) ∧
      (∃ y ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y,
        lagrangianGradient φ g x₀ y lam r ≤ v) ∧
      (∀ y ∈ lowerSolution φ g x₀, ∃ lam ∈ lowerMultipliers φ g x₀ y,
        v ≤ lagrangianGradient φ g x₀ y lam r) ∧
      (∃ lam, (∀ y ∈ lowerSolution φ g x₀, lam ∈ lowerMultipliers φ g x₀ y) ∧
        ∀ y ∈ lowerSolution φ g x₀, v ≤ lagrangianGradient φ g x₀ y lam r) ∧
      ∀ y₀ ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y₀,
        ∃ y ∈ lowerSolution φ g x₀, lagrangianGradient φ g x₀ y lam r ≤ v := by
  have hconv₀ := hconv.self_of_nhds
  obtain ⟨v, htend, ⟨ys, hys, hmm⟩, hmM⟩ :=
    exists_tendsto_slope_lowerValue_of_isConvexLower hφ hg hb hconv₀ hS r
  have hφc := hφ.continuous
  have hgc := fun i ↦ (hg i).continuous
  have hdl : IsDifferentiableLower φ g x₀ := fun y ↦
    ⟨((hφ.differentiable one_ne_zero) (x₀, y)).comp y
        (hasFDerivAt_prodMk_right x₀ y).differentiableAt,
      fun i ↦ (((hg i).differentiable one_ne_zero) (x₀, y)).comp y
        (hasFDerivAt_prodMk_right x₀ y).differentiableAt⟩
  have hex := eventually_lowerSolution_nonempty hgc hφc hb
  have hKΨ : IsCompact (lowerSolution φ g x₀) := by
    rw [← solutionMap_lowerFeasible]
    exact isCompact_solutionMap (eventually_isCompact_lowerFeasible hgc hb).self_of_nhds hφc
  have hμ₀ : lowerValue φ g x₀ = (φ (x₀, ys) : ℝ) :=
    VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hys
  set Λs := lowerMultipliers φ g x₀ ys with hΛs
  have hΛeq : ∀ y ∈ lowerSolution φ g x₀, lowerMultipliers φ g x₀ y = Λs := fun y hy ↦
    Subset.antisymm (lowerMultipliers_subset_of_isConvexLower hconv₀ hdl hy hys)
      (lowerMultipliers_subset_of_isConvexLower hconv₀ hdl hys hy)
  have hΛne : Λs.Nonempty := let ⟨lam, hlam, _⟩ := hmM ys hys; ⟨lam, hlam⟩
  have hΛc : IsCompact Λs := by
    obtain ⟨z, hz⟩ := hS
    exact isCompact_lowerMultipliers
      (lowerPLI_of_slaterAt hconv₀.2 (hdl ys).2 hys.1 ⟨z, hz⟩)
  -- `n(λ) = min_y ∇ₓL(x̄, y, λ) r`
  have hcont : Continuous fun p : (ι → ℝ) × F ↦ lagrangianGradient φ g x₀ p.2 p.1 r :=
    (continuous_lagrangianGradient_prod hφ hg x₀ r).comp continuous_swap
  set n : (ι → ℝ) → ℝ := fun lam ↦
    sInf ((fun y ↦ lagrangianGradient φ g x₀ y lam r) '' lowerSolution φ g x₀) with hn
  have hnc : Continuous n :=
    hKΨ.continuous_sInf (f := fun lam y ↦ lagrangianGradient φ g x₀ y lam r) hcont
  have himg : ∀ lam, IsCompact
      ((fun y ↦ lagrangianGradient φ g x₀ y lam r) '' lowerSolution φ g x₀) := fun lam ↦
    hKΨ.image (hcont.comp (continuous_const.prodMk continuous_id))
  have hge : ∀ lam, ∀ y ∈ lowerSolution φ g x₀, n lam ≤ lagrangianGradient φ g x₀ y lam r :=
    fun lam y hy ↦ csInf_le (himg lam).bddBelow (mem_image_of_mem _ hy)
  have hatt : ∀ lam, ∃ y ∈ lowerSolution φ g x₀, lagrangianGradient φ g x₀ y lam r = n lam :=
    fun lam ↦ (himg lam).sInf_mem (Set.Nonempty.image _ ⟨ys, hys⟩)
  obtain ⟨ls, hls, hmax⟩ := hΛc.exists_isMaxOn hΛne hnc.continuousOn
  have hwv : n ls ≤ v := (hge ls ys hys).trans (hmm ls hls)
  have hvw : v ≤ n ls := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hev := eventually_lowerValue_add_smul_le_of_isConvexLower hφ hg hb hconv hS hμ₀
      (r := r) (c := n ls + ε) fun y₁ hy₁ lam hlam ↦ by
        obtain ⟨y, hy, he⟩ := hatt lam
        have : n lam ≤ n ls := hmax (by rwa [hΛeq y₁ hy₁] at hlam)
        exact ⟨y, hy, by rw [he]; linarith⟩
    obtain ⟨z, hz⟩ := hS
    have hSl : ∀ᶠ x in 𝓝 x₀, ∀ i, g i (x, z) < 0 := eventually_all.2 fun i ↦
      (((hgc i).comp (continuous_id.prodMk continuous_const)).tendsto x₀).eventually_lt_const
        (hz i)
    have hline := tendsto_add_smul_nhdsGT x₀ r
    refine le_of_tendsto htend ?_
    filter_upwards [hev, hline.eventually hex, hline.eventually hSl, self_mem_nhdsWithin]
      with t h1 h2 h3 ht
    have ht0 : 0 < t := ht
    obtain ⟨y, hy⟩ := h2 ⟨z, fun i ↦ (h3 i).le⟩
    rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy, EReal.coe_le_coe_iff] at h1
    rw [VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hy, hμ₀, EReal.toReal_coe,
      EReal.toReal_coe, div_le_iff₀ ht0]
    linarith
  refine ⟨v, htend, ⟨ys, hys, hmm⟩, hmM,
    ⟨ls, fun y hy ↦ by rw [hΛeq y hy]; exact hls, fun y hy ↦ hvw.trans (hge ls y hy)⟩,
    fun y₁ hy₁ lam hlam ↦ ?_⟩
  obtain ⟨y, hy, he⟩ := hatt lam
  have : n lam ≤ n ls := hmax (by rwa [hΛeq y₁ hy₁] at hlam)
  exact ⟨y, hy, by rw [he]; linarith⟩

/-! ### Cor. 4.4: directional differentiability under (LICQ) -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Under (LICQ) the multiplier of the follower's problem is unique. -/
theorem lowerMultipliers_subsingleton_of_lowerLICQ {x : E} {y : F} (h : LowerLICQ g x y) :
    (lowerMultipliers φ g x y).Subsingleton := by
  classical
  intro lam hlam lam' hlam'
  set ν : ι → ℝ := fun i ↦ lam i - lam' i with hν
  have hin : ∀ i, g i (x, y) ≠ 0 → ν i = 0 := fun i hi ↦ by
    simp only [hν]
    rw [(mul_eq_zero.1 (hlam.2.2.1 i)).resolve_right hi,
      (mul_eq_zero.1 (hlam'.2.2.1 i)).resolve_right hi, sub_zero]
  have hsum : ∑ i, ν i • fderiv ℝ (fun z ↦ g i (x, z)) y = 0 := by
    have e : ∀ i, ν i • fderiv ℝ (fun z ↦ g i (x, z)) y =
        lam i • fderiv ℝ (fun z ↦ g i (x, z)) y - lam' i • fderiv ℝ (fun z ↦ g i (x, z)) y :=
      fun i ↦ by simp only [hν]; module
    rw [Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_sub_distrib, sub_eq_zero]
    exact add_left_cancel (hlam.2.2.2.trans hlam'.2.2.2.symm)
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i ↦ g i (x, y) = 0)
    fun i ↦ ν i • fderiv ℝ (fun z ↦ g i (x, z)) y
  have hrest : ∑ i : {i // ¬ g i (x, y) = 0}, ν i.1 • fderiv ℝ (fun z ↦ g i.1 (x, z)) y = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hin i.1 i.2, zero_smul]
  rw [hrest, add_zero, hsum] at hsplit
  have hA := Fintype.linearIndependent_iff.1 h (fun i ↦ ν i.1) hsplit
  funext i
  by_cases hi : g i (x, y) = 0
  · exact sub_eq_zero.1 (hA ⟨i, hi⟩)
  · exact sub_eq_zero.1 (hin i hi)

/-- Cor. 4.4 of [Dempe 2002]: if the follower's problem has `C¹` data, a feasible-set map that is
locally bounded at `x̄`, and (LICQ) holds at all `(x̄, y)`, `y ∈ Ψ(x̄)`, then the optimal value
function is directionally differentiable at `x̄` with
`μ'(x̄; r) = min {∇ₓL(x̄, y, λ(y)) r | y ∈ Ψ(x̄)}`, where `λ(y)` is the multiplier at `y`. -/
theorem exists_tendsto_slope_lowerValue_of_lowerLICQ (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hb : LocallyBoundedAt (lowerFeasible g) x₀)
    (hne : (lowerFeasible g x₀).Nonempty)
    (hlicq : ∀ y ∈ lowerSolution φ g x₀, LowerLICQ g x₀ y) (r : E) :
    ∃ v : ℝ, Tendsto (fun t : ℝ ↦ ((lowerValue φ g (x₀ + t • r)).toReal -
        (lowerValue φ g x₀).toReal) / t) (𝓝[>] 0) (𝓝 v) ∧
      (∃ y ∈ lowerSolution φ g x₀, ∃ lam ∈ lowerMultipliers φ g x₀ y,
        lagrangianGradient φ g x₀ y lam r = v) ∧
      ∀ y ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y,
        v ≤ lagrangianGradient φ g x₀ y lam r := by
  have hφc := hφ.continuous
  have hgc := fun i ↦ (hg i).continuous
  have hφd := hφ.differentiable one_ne_zero
  have hgd := fun i ↦ (hg i).differentiable one_ne_zero
  have hpli : ∀ y ∈ lowerSolution φ g x₀, LowerPLI g x₀ y := fun y hy ↦
    lowerPLI_of_lowerLICQ hy.1 (hlicq y hy)
  have hreg : ∀ y ∈ lowerSolution φ g x₀, LowerLevelRegular g x₀ y := fun y hy ↦
    (lowerPLI_iff_lowerLevelRegular fun i ↦ hgd i (x₀, y)).1 (hpli y hy)
  have hKΨ : IsCompact (lowerSolution φ g x₀) := by
    rw [← solutionMap_lowerFeasible]
    exact isCompact_solutionMap (eventually_isCompact_lowerFeasible hgc hb).self_of_nhds hφc
  obtain ⟨y₀, hy₀⟩ := (eventually_lowerSolution_nonempty hgc hφc hb).self_of_nhds hne
  obtain ⟨lam₀, hlam₀⟩ : (lowerMultipliers φ g x₀ y₀).Nonempty :=
    exists_isLowerKKT_of_mem_solutionMap (by rwa [solutionMap_lowerFeasible])
      ((hφd (x₀, y₀)).comp y₀ (hasFDerivAt_prodMk_right x₀ y₀).differentiableAt)
      (fun i ↦ ((hg i).comp (by fun_prop : ContDiff ℝ 1 fun w : F ↦ (x₀, w))).contDiffAt)
      (hpli y₀ hy₀)
  -- the pairs `(y, λ)` with `y ∈ Ψ(x̄)`, `λ ∈ Λ(x̄, y)` form a compact set
  set T : Set (F × (ι → ℝ)) := (Prod.fst ⁻¹' lowerSolution φ g x₀) ∩
    ((fun q : F × (ι → ℝ) ↦ ((x₀, q.1), q.2)) ⁻¹'
      graph fun p : E × F ↦ lowerMultipliers φ g p.1 p.2) with hT
  have hTcl : IsClosed T := (hKΨ.isClosed.preimage continuous_fst).inter
    ((isClosed_graph_lowerMultipliers hφ hg).preimage (by fun_prop))
  have hloc : ∀ y ∈ lowerSolution φ g x₀, ∃ R : ℝ, ∃ V : Set F, V ∈ 𝓝 y ∧
      ∀ y' ∈ V, lowerMultipliers φ g x₀ y' ⊆ Metric.closedBall 0 R := fun y hy ↦ by
    obtain ⟨R, hR⟩ := exists_eventually_lowerMultipliers_subset hφ hg (hpli y hy)
    exact ⟨R, _, ((continuous_const.prodMk continuous_id).tendsto y).eventually hR,
      fun y' hy' ↦ hy'⟩
  choose! R V hV hRV using hloc
  obtain ⟨t, ht, hcover⟩ := hKΨ.elim_nhds_subcover V hV
  have hTsub : T ⊆ lowerSolution φ g x₀ ×ˢ Metric.closedBall (0 : ι → ℝ) (∑ y ∈ t, |R y|) := by
    rintro ⟨y, lam⟩ ⟨hy, hlam⟩
    obtain ⟨y', hy't, hyV⟩ := mem_iUnion₂.1 (hcover hy)
    exact ⟨hy, Metric.closedBall_subset_closedBall ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun y ↦ |R y|) (fun _ _ ↦ abs_nonneg _) hy't))
      (hRV y' (ht y' hy't) y hyV hlam)⟩
  have hTc : IsCompact T :=
    (hKΨ.prod (isCompact_closedBall 0 _)).of_isClosed_subset hTcl hTsub
  obtain ⟨⟨ys, ls⟩, ⟨hys, hls⟩, hmin⟩ := hTc.exists_isMinOn ⟨(y₀, lam₀), hy₀, hlam₀⟩
    (continuous_lagrangianGradient_prod hφ hg x₀ r).continuousOn
  have hys' : ys ∈ lowerSolution φ g x₀ := hys
  have hls' : ls ∈ lowerMultipliers φ g x₀ ys := hls
  have hminT : ∀ y ∈ lowerSolution φ g x₀, ∀ lam ∈ lowerMultipliers φ g x₀ y,
      lagrangianGradient φ g x₀ ys ls r ≤ lagrangianGradient φ g x₀ y lam r :=
    fun y hy lam hlam ↦ hmin (a := (y, lam)) ⟨hy, hlam⟩
  set v := lagrangianGradient φ g x₀ ys ls r with hv
  have hμ₀ : lowerValue φ g x₀ = (φ (x₀, ys) : ℝ) :=
    VariationalAnalysis.lowerValue_eq_of_mem_lowerSolution hys'
  have hupper : ∀ c, v < c → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      lowerValue φ g (x₀ + t • r) ≤ ((φ (x₀, ys) + t * c : ℝ) : EReal) := fun c hc ↦
    eventually_lowerValue_add_smul_le (hφd _) (fun i ↦ hgd i _) ⟨ls, hls'⟩ (hpli ys hys')
      fun lam hlam ↦ by
        rw [lowerMultipliers_subsingleton_of_lowerLICQ (hlicq ys hys') hlam hls']
        exact hc
  have hlower : ∀ c, c < v → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((φ (x₀, ys) + t * c : ℝ) : EReal) ≤ lowerValue φ g (x₀ + t • r) := fun c hc ↦
    eventually_le_lowerValue_add_smul hgc hφc hb hne (fun y _ ↦ hφ.contDiffAt)
      (fun y _ i ↦ (hg i).contDiffAt) hreg hμ₀ fun y hy u hu ↦ by
        obtain ⟨lam, hl0, hcs, hstat, rfl⟩ := hu
        have hmem : lam ∈ lowerMultipliers φ g x₀ y := by
          refine ⟨hy.1, hl0, hcs, ?_⟩
          have e : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y =
              (fderiv ℝ (g i) (x₀, y)).comp (inr ℝ E F) := fun i ↦ fderiv_section (hgd i _)
          rw [fderiv_section (hφd _)]
          simp only [e]
          exact hstat
        exact hc.trans_le (hminT y hy lam hmem)
  refine ⟨v, ?_, ⟨ys, hys', ls, hls', rfl⟩, hminT⟩
  simp only [hμ₀, EReal.toReal_coe]
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · filter_upwards [hlower ((c + v) / 2) (by linarith), hupper (v + 1) (by linarith),
      self_mem_nhdsWithin] with t h1 h2 ht
    exact lt_of_lt_of_le (by linarith) (slope_bounds_of_coe_le ht h1 h2).1
  · filter_upwards [hlower (v - 1) (by linarith), hupper ((c + v) / 2) (by linarith),
      self_mem_nhdsWithin] with t h1 h2 ht
    exact lt_of_le_of_lt (slope_bounds_of_coe_le ht h1 h2).2 (by linarith)

end Bilevel
