/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.KKT
import VariationalAnalysis.WellPosedness.Criterion

/-!
# Parametric optimization

Sect. 4.1–4.2 of [Dempe 2002] (Thm. 4.1–4.3) and the existence results Thm. 5.2–5.3 built on them: the
follower's problem `min_y {φ(x, y) | y ∈ K(x)}` as a parametric optimization problem in the
leader's variable `x`.

## Main definitions

* `UpperHemicontinuousAt Γ x`, `LowerHemicontinuousAt Γ x`: upper and lower semicontinuity of
  set-valued maps in the sense of [Dempe 2002, Def. 4.2] (upper/lower hemicontinuity).
* `localSolutionMap φ K`, `stationaryMap φ g`: the local solutions `Ψ_loc` and the stationary
  solutions `SP` of the follower's problem.

## Main results

* `isCompact_lowerMultipliers`, `lowerPLI_of_isBounded`, `lowerPLI_iff_isCompact`,
  `lowerPLI_iff_nonempty_isCompact`: Thm. 4.1 of [Dempe 2002]: at a local minimizer, positive
  linear independence of the active gradients (the dual form of (MFCQ)) holds iff the multiplier
  set `Λ(x, y)` is nonempty and compact; `convex_lowerMultipliers`.
* `solutionMap_subset_localSolutionMap`, `localSolutionMap_subset_stationaryMap`,
  `stationaryMap_subset_solutionMap`: the inclusions (4.7) and `SP = Ψ` for convex problems.
* `upperHemicontinuousAt_lowerMultipliers`, `upperHemicontinuousAt_stationaryMap`: Thm. 4.2 of
  [Dempe 2002]: for `C¹` data, (MFCQ) at `(x̄, ȳ)` makes `Λ` upper semicontinuous at `(x̄, ȳ)`
  (via local boundedness, `exists_eventually_lowerMultipliers_subset`, and the closed graph,
  `isClosed_graph_lowerMultipliers`); with local boundedness of the feasible-set map and (MFCQ) at
  all feasible points `(x̄, y)`, `SP` is upper semicontinuous at `x̄`.
* `eventually_lowerPLI`: for `C¹` constraints, dual (MFCQ) persists near `(x̄, ȳ)` (with a uniform
  constant, `exists_eventually_mul_norm_le_of_lowerPLI`).
* `continuousAt_marginal`, `upperHemicontinuousAt_solutionMap`: Thm. 4.3 of [Dempe 2002] (a
  Berge-type maximum theorem): if `gph K` is closed, `K` is uniformly bounded near `x̄` and lower
  semicontinuous at `x̄`, and `φ` is continuous, then the value function is continuous at `x̄` and
  `Ψ` is upper semicontinuous at `x̄`.
* `isClosed_bilevelFeasible`, `exists_isOptimisticSolution`: closedness of the feasible set of
  (5.5) and Thm. 5.2 of [Dempe 2002] (existence of optimistic solutions).
* `lowerSemicontinuousAt_pessimisticValue`, `exists_isPessimisticSolution`: Thm. 5.3 of
  [Dempe 2002] (existence of pessimistic solutions when `Ψ` is lower semicontinuous).
* `lipschitzLikeAt_lowerFeasible`, `lowerHemicontinuousAt_lowerFeasible`: (MFCQ) makes the
  feasible-set map `G(x) = {y | gᵢ(x, y) ≤ 0}` Lipschitz-like, hence lower semicontinuous (via
  the Mordukhovich criterion of lean-variational).
* `continuousAt_lowerValue_of_regular`, `upperHemicontinuousAt_lowerSolution_of_regular`,
  `exists_isOptimisticSolution_of_regular`: Thm. 4.3 and Thm. 5.2 of [Dempe 2002] for smooth
  inequality constraints under (MFCQ).

## Remarks on the book

* Assumption (C) of [Dempe 2002] (compactness of `{(x, y) | g(x, y) ≤ 0, h(x, y) = 0}`) is
  replaced by what the proofs use: a closed graph of `K` together with uniform boundedness of
  `K` near `x̄` (Thm. 4.3), or compactness of `{(x, y) | x ∈ Ω, y ∈ K(x)}` (Thm. 5.2, 5.3). The
  role of (MFCQ) in Thm. 4.3 and 5.2 is to make `K` lower semicontinuous; this is isolated in
  `lowerHemicontinuousAt_lowerFeasible`.
* (MFCQ) is used in its dual form (positive linear independence of the active gradients),
  which is equivalent to the primal form by Gordan's theorem (not formalized here).
* Lower-level equality constraints are omitted, as in `BilevelOptimization.KKT`.
* Thm. 4.2 assumes (MFCQ) only at the points of `SP(x̄)`. For the upper semicontinuity of `SP`
  this is not enough (`not_upperHemicontinuousAt_stationaryMap_example`: `min_y {y | y² ≤ x²}`
  has `SP(0) = ∅` but `SP(x) = {-|x|}` for `x ≠ 0`); the proof needs (MFCQ) at limits of
  stationary points, which are only known to be feasible. Here (MFCQ) is assumed at all
  feasible points `(x̄, y)`, as in Thm. 4.3. The data are assumed globally `C¹`, as in Ch. 4 of the
  book.
-/

open Filter Topology Set
open VariationalAnalysis (graph lowerFeasible lowerSolution lowerValue marginal)

namespace Bilevel

variable {E F : Type*}

/-! ### Semicontinuity of set-valued maps -/

section Hemicontinuity

variable [TopologicalSpace E] [TopologicalSpace F]

/-- Upper semicontinuity of a set-valued map in the sense of [Dempe 2002, Def. 4.2] (upper
hemicontinuity): for every open `V ⊇ Γ(x₀)`, `Γ(x) ⊆ V` for `x` near `x₀`. -/
def UpperHemicontinuousAt (Γ : E → Set F) (x₀ : E) : Prop :=
  ∀ V : Set F, IsOpen V → Γ x₀ ⊆ V → ∀ᶠ x in 𝓝 x₀, Γ x ⊆ V

/-- Lower semicontinuity of a set-valued map in the sense of [Dempe 2002, Def. 4.2] (lower
hemicontinuity): for every open `V` meeting `Γ(x₀)`, `Γ(x)` meets `V` for `x` near `x₀`. -/
def LowerHemicontinuousAt (Γ : E → Set F) (x₀ : E) : Prop :=
  ∀ V : Set F, IsOpen V → (Γ x₀ ∩ V).Nonempty → ∀ᶠ x in 𝓝 x₀, (Γ x ∩ V).Nonempty

variable {K : E → Set F} {x x₀ : E}

theorem exists_isOpen_of_eventually_nhds_prod {P : E → F → Prop} {z : F}
    (h : ∀ᶠ p : E × F in 𝓝 (x, z), P p.1 p.2) :
    ∃ U ∈ 𝓝 x, ∃ W, IsOpen W ∧ z ∈ W ∧ ∀ x' ∈ U, ∀ z' ∈ W, P x' z' := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h
  obtain ⟨W, hWV, hWo, hzW⟩ := mem_nhds_iff.1 hV
  exact ⟨U, hU, W, hWo, hzW, fun x' hx' z' hz' ↦ hUV (mk_mem_prod hx' (hWV hz'))⟩

/-- If `K` is lower semicontinuous at `x` and `z ∈ K(x)`, every property holding near `(x, z)`
holds at some `z' ∈ K(x')` for all `x'` near `x`. -/
theorem LowerHemicontinuousAt.eventually_exists (hK : LowerHemicontinuousAt K x) {z : F}
    (hz : z ∈ K x) {P : E → F → Prop} (h : ∀ᶠ p : E × F in 𝓝 (x, z), P p.1 p.2) :
    ∀ᶠ x' in 𝓝 x, ∃ z' ∈ K x', P x' z' := by
  obtain ⟨U, hU, W, hWo, hzW, hP⟩ := exists_isOpen_of_eventually_nhds_prod h
  filter_upwards [hU, hK W hWo ⟨z, hz, hzW⟩] with x' hx' hne
  obtain ⟨z', hz'K, hz'W⟩ := hne
  exact ⟨z', hz'K, hP x' hx' z' hz'W⟩

/-- A map that is uniformly bounded near `x₀` (its values near `x₀` lie in a common compact set)
and whose graph has no closure points over `x₀` outside it is upper semicontinuous at `x₀`. -/
theorem upperHemicontinuousAt_of_mem_closure_graph
    (hcl : ∀ y, (x₀, y) ∈ closure (graph K) → y ∈ K x₀)
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C) : UpperHemicontinuousAt K x₀ := by
  intro V hV hKV
  obtain ⟨U, hU, C, hC, hKC⟩ := hb
  have hP : ∀ y ∈ C, ∀ᶠ p : E × F in 𝓝 (x₀, y), p.2 ∈ K p.1 → p.2 ∈ V := by
    intro y _
    by_cases hy : y ∈ V
    · exact ((continuous_snd.tendsto (x₀, y)).eventually (hV.mem_nhds hy)).mono fun _ hp _ ↦ hp
    · exact Filter.Eventually.mono (isClosed_closure.isOpen_compl.mem_nhds
        (show (x₀, y) ∈ (closure (graph K))ᶜ from fun h ↦ hy (hKV (hcl y h))))
        fun p hp hpK ↦ absurd (subset_closure (s := graph K) hpK) hp
  filter_upwards [hU, hC.eventually_forall_of_forall_eventually
    (P := fun x y ↦ y ∈ K x → y ∈ V) hP] with x hxU hx y hy
  exact hx y (hKC x hxU hy) hy

/-- A map with closed graph that is uniformly bounded near `x₀` (its values near `x₀` lie in a
common compact set) is upper semicontinuous at `x₀`. -/
theorem upperHemicontinuousAt_of_isClosed_graph (hK : IsClosed (graph K))
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C) : UpperHemicontinuousAt K x₀ :=
  upperHemicontinuousAt_of_mem_closure_graph (fun _ h ↦ by rwa [hK.closure_eq] at h) hb

end Hemicontinuity

/-! ### Thm. 4.1: compactness of the multiplier set -/

section Multipliers

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
  {φ : E × F → ℝ} {g : ι → E × F → ℝ} {x : E} {y : F}

/-- Positive linear independence of the active gradients gives a uniform lower bound
`c ‖μ‖ ≤ ‖∑ μᵢ ∇_y gᵢ(x, y)‖` on the cone of admissible multipliers. -/
theorem exists_pos_mul_norm_le_of_lowerPLI (hreg : LowerPLI g x y) :
    ∃ c > 0, ∀ μ : ι → ℝ, (∀ i, 0 ≤ μ i) → (∀ i, g i (x, y) < 0 → μ i = 0) →
      c * ‖μ‖ ≤ ‖∑ i, μ i • fderiv ℝ (fun z ↦ g i (x, z)) y‖ := by
  set A : (ι → ℝ) → (F →L[ℝ] ℝ) := fun μ ↦ ∑ i, μ i • fderiv ℝ (fun z ↦ g i (x, z)) y
  set Cn : Set (ι → ℝ) := {μ | (∀ i, 0 ≤ μ i) ∧ ∀ i, g i (x, y) < 0 → μ i = 0}
  have hA : Continuous A :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have hCn : IsClosed Cn := by
    have e : Cn = (⋂ i, {μ : ι → ℝ | 0 ≤ μ i}) ∩ ⋂ i, {μ : ι → ℝ | g i (x, y) < 0 → μ i = 0} := by
      ext μ
      simp [Cn]
    rw [e]
    refine (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_iInter fun i ↦ ?_)
    by_cases h : g i (x, y) < 0
    · simpa [h] using isClosed_eq (continuous_apply i) continuous_const
    · simp [h]
  set S := Cn ∩ Metric.sphere (0 : ι → ℝ) 1
  have hS : IsCompact S := (isCompact_sphere 0 1).inter_left hCn
  have hmemS : ∀ μ ∈ Cn, μ ≠ 0 → ‖μ‖⁻¹ • μ ∈ S := by
    intro μ hμ hne
    refine ⟨⟨fun i ↦ ?_, fun i hi ↦ ?_⟩, ?_⟩
    · simpa only [Pi.smul_apply, smul_eq_mul] using
        mul_nonneg (inv_nonneg.2 (norm_nonneg μ)) (hμ.1 i)
    · simp [hμ.2 i hi]
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]
  have hlin : ∀ (t : ℝ) (μ : ι → ℝ), A (t • μ) = t • A μ := fun t μ ↦ by
    simp only [A, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun μ hμ0 hμin ↦ ?_⟩
    by_cases hμ : μ = 0
    · simp [hμ]
    · have := hmemS μ ⟨hμ0, hμin⟩ hμ
      rw [hSe] at this
      exact absurd this (notMem_empty _)
  · obtain ⟨μ₀, hμ₀S, hmin⟩ := hS.exists_isMinOn hSne (continuous_norm.comp hA).continuousOn
    have hpos : 0 < ‖A μ₀‖ := by
      refine norm_pos_iff.2 fun h0 ↦ ?_
      have h1 := hμ₀S.2
      rw [hreg μ₀ hμ₀S.1.1 hμ₀S.1.2 h0, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
    refine ⟨‖A μ₀‖, hpos, fun μ hμ0 hμin ↦ ?_⟩
    by_cases hμ : μ = 0
    · simp [hμ]
    · have h : ‖A μ₀‖ ≤ ‖A (‖μ‖⁻¹ • μ)‖ := hmin (hmemS μ ⟨hμ0, hμin⟩ hμ)
      rw [hlin, norm_smul, norm_inv, norm_norm] at h
      have hμpos : 0 < ‖μ‖ := norm_pos_iff.2 hμ
      calc ‖A μ₀‖ * ‖μ‖ ≤ ‖μ‖⁻¹ * ‖A μ‖ * ‖μ‖ := mul_le_mul_of_nonneg_right h hμpos.le
        _ = ‖A μ‖ := by field_simp

theorem isClosed_lowerMultipliers : IsClosed (lowerMultipliers φ g x y) := by
  have hA : Continuous fun lam : ι → ℝ ↦ ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).smul continuous_const
  have e : lowerMultipliers φ g x y = {_lam : ι → ℝ | ∀ i, g i (x, y) ≤ 0} ∩
      ((⋂ i, {lam : ι → ℝ | 0 ≤ lam i}) ∩ ((⋂ i, {lam : ι → ℝ | lam i * g i (x, y) = 0}) ∩
        {lam | fderiv ℝ (fun z ↦ φ (x, z)) y +
          ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y = 0})) := by
    ext lam
    simp [lowerMultipliers, IsLowerKKT]
  rw [e]
  refine IsClosed.inter ?_ ((isClosed_iInter fun i ↦ isClosed_le continuous_const
    (continuous_apply i)).inter ((isClosed_iInter fun i ↦ isClosed_eq
      ((continuous_apply i).mul continuous_const) continuous_const).inter
      (isClosed_eq (continuous_const.add hA) continuous_const)))
  by_cases h : ∀ i, g i (x, y) ≤ 0
  · simp [h]
  · simp [h]

theorem convex_lowerMultipliers : Convex ℝ (lowerMultipliers φ g x y) := by
  rintro l₁ ⟨hf, h1, c1, s1⟩ l₂ ⟨-, h2, c2, s2⟩ a b ha hb hab
  refine ⟨hf, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (h1 i)) (mul_nonneg hb (h2 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, mul_assoc, mul_assoc, c1 i, c2 i, mul_zero, mul_zero, add_zero]
  · have e : ∑ i, (a • l₁ + b • l₂) i • fderiv ℝ (fun z ↦ g i (x, z)) y =
        a • ∑ i, l₁ i • fderiv ℝ (fun z ↦ g i (x, z)) y +
          b • ∑ i, l₂ i • fderiv ℝ (fun z ↦ g i (x, z)) y := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, Finset.smul_sum]
    rw [e, eq_neg_of_add_eq_zero_right s1, eq_neg_of_add_eq_zero_right s2, smul_neg, smul_neg,
      ← neg_add, ← add_smul, hab, one_smul, add_neg_cancel]

/-- Thm. 4.1 of [Dempe 2002], `⇒`: positive linear independence of the active gradients (dual
(MFCQ)) makes the multiplier set compact. -/
theorem isCompact_lowerMultipliers (hreg : LowerPLI g x y) :
    IsCompact (lowerMultipliers φ g x y) := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_le_of_lowerPLI hreg
  refine Metric.isCompact_of_isClosed_isBounded isClosed_lowerMultipliers
    ((Metric.isBounded_closedBall (x := (0 : ι → ℝ))
      (r := ‖fderiv ℝ (fun z ↦ φ (x, z)) y‖ / c)).subset fun lam hlam ↦ ?_)
  obtain ⟨-, hl, hcs, hst⟩ := hlam
  have h := hbound lam hl fun i hi ↦ (mul_eq_zero.1 (hcs i)).resolve_right hi.ne
  rw [eq_neg_of_add_eq_zero_right hst, norm_neg] at h
  rw [mem_closedBall_zero_iff, le_div_iff₀ hc]
  linarith

/-- Thm. 4.1 of [Dempe 2002], `⇐`: if the multiplier set is nonempty and bounded, the active
gradients are positively linearly independent. -/
theorem lowerPLI_of_isBounded (hne : (lowerMultipliers φ g x y).Nonempty)
    (hb : Bornology.IsBounded (lowerMultipliers φ g x y)) : LowerPLI g x y := by
  obtain ⟨lam₀, hlam₀⟩ := hne
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  intro μ hμ0 hμin hμsum
  have hmem : ∀ t : ℝ, 0 ≤ t → lam₀ + t • μ ∈ lowerMultipliers φ g x y := fun t ht ↦ by
    obtain ⟨hf, hl, hcs, hst⟩ := hlam₀
    refine ⟨hf, fun i ↦ ?_, fun i ↦ ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hl i) (mul_nonneg ht (hμ0 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases (hf i).lt_or_eq with h | h
      · rw [hμin i h, mul_zero, add_zero]
        exact hcs i
      · rw [h, mul_zero]
    · have e : ∑ i, (lam₀ + t • μ) i • fderiv ℝ (fun z ↦ g i (x, z)) y =
          ∑ i, lam₀ i • fderiv ℝ (fun z ↦ g i (x, z)) y +
            t • ∑ i, μ i • fderiv ℝ (fun z ↦ g i (x, z)) y := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, Finset.smul_sum]
      rw [e, hμsum, smul_zero, add_zero]
      exact hst
  by_contra hne0
  have hpos : 0 < ‖μ‖ := norm_pos_iff.2 hne0
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ hlam₀)
  set t := (2 * R + 1) / ‖μ‖
  have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
  have h1 := hR _ (hmem t ht)
  have h2 := hR _ hlam₀
  have h3 : ‖t • μ‖ ≤ 2 * R := by
    calc ‖t • μ‖ = ‖(lam₀ + t • μ) - lam₀‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖lam₀ + t • μ‖ + ‖lam₀‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  rw [norm_smul, Real.norm_of_nonneg ht, div_mul_cancel₀ _ hpos.ne'] at h3
  linarith

/-- Thm. 4.1 of [Dempe 2002] for a nonempty multiplier set. -/
theorem lowerPLI_iff_isCompact (hne : (lowerMultipliers φ g x y).Nonempty) :
    LowerPLI g x y ↔ IsCompact (lowerMultipliers φ g x y) :=
  ⟨isCompact_lowerMultipliers, fun h ↦ lowerPLI_of_isBounded hne h.isBounded⟩

end Multipliers

/-! ### Local and stationary solutions -/

section Stationary

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]

/-- The local solutions `Ψ_loc(x)` of the follower's problem [Dempe 2002, Sect. 4.1]. -/
def localSolutionMap (φ : E × F → ℝ) (K : E → Set F) (x : E) : Set F :=
  {y | y ∈ K x ∧ IsLocalMinOn (fun z ↦ φ (x, z)) (K x) y}

/-- The stationary solutions `SP(x) = {y | Λ(x, y) ≠ ∅}` of the follower's problem
[Dempe 2002, Sect. 4.1]. -/
def stationaryMap (φ : E × F → ℝ) (g : ι → E × F → ℝ) (x : E) : Set F :=
  {y | (lowerMultipliers φ g x y).Nonempty}

variable {φ : E × F → ℝ} {g : ι → E × F → ℝ} {K : E → Set F} {x : E} {y : F}

omit [NormedSpace ℝ F] in
theorem solutionMap_subset_localSolutionMap : solutionMap φ K x ⊆ localSolutionMap φ K x :=
  fun _ hy ↦ ⟨hy.1, IsMinOn.localize (isMinOn_iff.2 fun z hz ↦ hy.2 z hz)⟩

/-- (4.7) of [Dempe 2002]: under (MFCQ), local solutions are stationary. -/
theorem localSolutionMap_subset_stationaryMap [FiniteDimensional ℝ F]
    (hy : y ∈ localSolutionMap φ (lowerFeasible g) x)
    (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) (hreg : LowerPLI g x y) :
    y ∈ stationaryMap φ g x :=
  exists_isLowerKKT_of_isLocalMinOn hy.1 hy.2 hφ hg hreg

/-- `SP = Ψ` for convex problems [Dempe 2002, after (4.7)]. -/
theorem stationaryMap_subset_solutionMap (hconv : IsConvexLower φ g x)
    (hdiff : IsDifferentiableLower φ g x) : stationaryMap φ g x ⊆ solutionMap φ (lowerFeasible g) x :=
  fun y ⟨_, hlam⟩ ↦ mem_solutionMap_of_isLowerKKT hconv (hdiff y).1 (hdiff y).2 hlam

/-- Thm. 4.1 of [Dempe 2002]: at a local solution of the follower's problem with `C¹` data,
positive linear independence of the active gradients (dual (MFCQ)) holds iff `Λ(x, y)` is
nonempty and compact (it is always convex, `convex_lowerMultipliers`). -/
theorem lowerPLI_iff_nonempty_isCompact [FiniteDimensional ℝ F]
    (hy : y ∈ localSolutionMap φ (lowerFeasible g) x)
    (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) :
    LowerPLI g x y ↔
      (lowerMultipliers φ g x y).Nonempty ∧ IsCompact (lowerMultipliers φ g x y) :=
  ⟨fun h ↦ ⟨localSolutionMap_subset_stationaryMap hy hφ hg h, isCompact_lowerMultipliers h⟩,
    fun ⟨hne, hc⟩ ↦ lowerPLI_of_isBounded hne hc.isBounded⟩

end Stationary

/-! ### Thm. 4.3: continuity of the value function and upper semicontinuity of `Ψ` -/

section Berge

variable [TopologicalSpace E] [TopologicalSpace F] {f φ : E × F → ℝ} {K : E → Set F}
  {Ω : Set E} {x x₀ : E}

/-- The value function is upper semicontinuous at `x₀` when `K` is lower semicontinuous at
`x₀` [Dempe 2002, Thm. 4.3]. -/
theorem upperSemicontinuousAt_marginal (hlsc : LowerHemicontinuousAt K x₀) (hφ : Continuous φ) :
    UpperSemicontinuousAt (marginal (fun p ↦ (φ p : EReal)) K) x₀ := by
  intro t ht
  unfold VariationalAnalysis.marginal at ht
  obtain ⟨z, hz⟩ := iInf_lt_iff.1 ht
  obtain ⟨hzK, hzt⟩ := iInf_lt_iff.1 hz
  have hc : Continuous fun p : E × F ↦ (φ p : EReal) := continuous_coe_real_ereal.comp hφ
  filter_upwards [hlsc.eventually_exists (P := fun x' z' ↦ (φ (x', z') : EReal) < t) hzK
    ((hc.tendsto (x₀, z)).eventually (eventually_lt_nhds hzt))] with x hx
  obtain ⟨z', hz'K, hz'⟩ := hx
  exact lt_of_le_of_lt (VariationalAnalysis.marginal_le hz'K) hz'

/-- The value function is lower semicontinuous at `x₀` when `gph K` is closed and `K` is
uniformly bounded near `x₀` [Dempe 2002, Thm. 4.3]. -/
theorem lowerSemicontinuousAt_marginal (hK : IsClosed (graph K))
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C) (hφ : Continuous φ) :
    LowerSemicontinuousAt (marginal (fun p ↦ (φ p : EReal)) K) x₀ := by
  intro t ht
  obtain ⟨U, hU, C, hC, hKC⟩ := hb
  obtain ⟨s, hts, hs⟩ := exists_between ht
  have hc : Continuous fun p : E × F ↦ (φ p : EReal) := continuous_coe_real_ereal.comp hφ
  have hP : ∀ y ∈ C, ∀ᶠ p : E × F in 𝓝 (x₀, y), p.2 ∈ K p.1 → s < (φ (p.1, p.2) : EReal) := by
    intro y _
    by_cases hy : y ∈ K x₀
    · exact ((hc.tendsto (x₀, y)).eventually (eventually_gt_nhds
        (hs.trans_le (VariationalAnalysis.marginal_le hy)))).mono fun _ hp _ ↦ hp
    · exact Filter.Eventually.mono (hK.isOpen_compl.mem_nhds
        (show (x₀, y) ∈ (graph K)ᶜ from hy)) fun p hp hpK ↦ absurd hpK hp
  filter_upwards [hU, hC.eventually_forall_of_forall_eventually
    (P := fun x y ↦ y ∈ K x → s < (φ (x, y) : EReal)) hP] with x hxU hx
  exact hts.trans_le (le_iInf₂ fun y hy ↦ (hx y (hKC x hxU hy) hy).le)

/-- Thm. 4.3 of [Dempe 2002], continuity of the value function: if `gph K` is closed, `K` is
uniformly bounded near `x₀` and lower semicontinuous at `x₀`, and `φ` is continuous, then
`μ(x) = inf {φ(x, y) | y ∈ K(x)}` is continuous at `x₀` (as an `EReal`-valued function). -/
theorem continuousAt_marginal (hK : IsClosed (graph K))
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C) (hlsc : LowerHemicontinuousAt K x₀)
    (hφ : Continuous φ) : ContinuousAt (marginal (fun p ↦ (φ p : EReal)) K) x₀ :=
  continuousAt_iff_lower_upperSemicontinuousAt.2
    ⟨lowerSemicontinuousAt_marginal hK hb hφ, upperSemicontinuousAt_marginal hlsc hφ⟩

/-- Thm. 4.3 of [Dempe 2002], upper semicontinuity of the solution map, under the assumptions
of `continuousAt_marginal`. -/
theorem upperHemicontinuousAt_solutionMap (hK : IsClosed (graph K))
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, K x ⊆ C) (hlsc : LowerHemicontinuousAt K x₀)
    (hφ : Continuous φ) : UpperHemicontinuousAt (solutionMap φ K) x₀ := by
  intro V hV hΨV
  obtain ⟨U, hU, C, hC, hKC⟩ := hb
  have hc : Continuous fun p : E × F ↦ (φ p : EReal) := continuous_coe_real_ereal.comp hφ
  have husc := upperSemicontinuousAt_marginal hlsc hφ
  have hP : ∀ y ∈ C, ∀ᶠ p : E × F in 𝓝 (x₀, y), p.2 ∈ solutionMap φ K p.1 → p.2 ∈ V := by
    intro y _
    by_cases hyV : y ∈ V
    · exact ((continuous_snd.tendsto (x₀, y)).eventually (hV.mem_nhds hyV)).mono fun _ hp _ ↦ hp
    by_cases hyK : y ∈ K x₀
    · have hlt : marginal (fun p ↦ (φ p : EReal)) K x₀ < φ (x₀, y) := by
        by_contra hle
        exact hyV (hΨV (mem_solutionMap_iff_le_marginal.2 ⟨hyK, not_lt.1 hle⟩))
      obtain ⟨s, hs1, hs2⟩ := exists_between hlt
      filter_upwards [(continuous_fst.tendsto (x₀, y)).eventually (husc s hs1),
        (hc.tendsto (x₀, y)).eventually (eventually_gt_nhds hs2)] with p hp1 hp2 hpΨ
      exact absurd (hp2.trans_le (mem_solutionMap_iff_le_marginal.1 hpΨ).2) (not_lt.2 hp1.le)
    · exact Filter.Eventually.mono (hK.isOpen_compl.mem_nhds
        (show (x₀, y) ∈ (graph K)ᶜ from hyK)) fun p hp hpΨ ↦ absurd hpΨ.1 hp
  filter_upwards [hU, hC.eventually_forall_of_forall_eventually
    (P := fun x y ↦ y ∈ solutionMap φ K x → y ∈ V) hP] with x hxU hx y hy
  exact hx y (hKC x hxU hy.1) hy

/-! ### Thm. 5.2 and 5.3: existence of optimistic and pessimistic solutions -/

/-- If `K` is lower semicontinuous at `x` and `gph K` is closed, the closure of `gph Ψ` above `x`
lies in `gph Ψ` (the closedness of `gph Ψ` used on p. 132 of [Dempe 2002]). -/
theorem mem_solutionMap_of_mem_closure (hK : IsClosed (graph K))
    (hlsc : LowerHemicontinuousAt K x) (hφ : Continuous φ) {y : F}
    (h : (x, y) ∈ closure (graph (solutionMap φ K))) : y ∈ solutionMap φ K x := by
  have hxy : y ∈ K x := (hK.closure_subset_iff.2 fun p hp ↦ hp.1) h
  refine ⟨hxy, fun z hz ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  set δ := (φ (x, y) - φ (x, z)) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : ∀ᶠ p : E × F in 𝓝 (x, z), φ p < φ (x, z) + δ :=
    (hφ.tendsto (x, z)).eventually (eventually_lt_nhds (by linarith))
  have h2 := hlsc.eventually_exists (P := fun x' z' ↦ φ (x', z') < φ (x, z) + δ) hz h1
  have h3 : ∀ᶠ p : E × F in 𝓝 (x, y), φ (x, y) - δ < φ p :=
    (hφ.tendsto (x, y)).eventually (eventually_gt_nhds (by linarith))
  obtain ⟨p, ⟨hp2, hp3⟩, hpΨ⟩ :=
    mem_closure_iff_nhds.1 h _ (((continuous_fst.tendsto (x, y)).eventually h2).and h3)
  obtain ⟨z', hz'K, hz'⟩ := hp2
  have h4 : φ (p.1, p.2) ≤ φ (p.1, z') := hpΨ.2 z' hz'K
  simp only [Prod.mk.eta] at h4
  linarith

/-- The feasible set of (5.5) is closed when `Ω` and `gph K` are closed, `K` is lower
semicontinuous on `Ω` and `φ` is continuous. -/
theorem isClosed_bilevelFeasible (hΩ : IsClosed Ω) (hK : IsClosed (graph K))
    (hlsc : ∀ x ∈ Ω, LowerHemicontinuousAt K x) (hφ : Continuous φ) :
    IsClosed (bilevelFeasible φ K Ω) := by
  refine isClosed_of_closure_subset fun p hp ↦ ?_
  have hx : p.1 ∈ Ω := ((hΩ.preimage continuous_fst).closure_subset_iff.2 fun q hq ↦ hq.1) hp
  exact ⟨hx, mem_solutionMap_of_mem_closure hK (hlsc _ hx) hφ
    (closure_mono (fun q hq ↦ hq.2) hp)⟩

theorem isCompact_apply (hC : IsCompact {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ K p.1})
    (hK : IsClosed (graph K)) (hx : x ∈ Ω) : IsCompact (K x) :=
  (hC.image continuous_snd).of_isClosed_subset
    (show IsClosed ((fun y : F ↦ (x, y)) ⁻¹' graph K) from hK.preimage (by fun_prop))
    fun y hy ↦ ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem solutionMap_nonempty_of_isCompact (hKx : IsCompact (K x)) (hne : (K x).Nonempty)
    (hφ : Continuous φ) : (solutionMap φ K x).Nonempty := by
  have hc : Continuous fun z ↦ φ (x, z) := by fun_prop
  obtain ⟨y, hy, hmin⟩ := hKx.exists_isMinOn hne hc.continuousOn
  exact ⟨y, hy, fun z hz ↦ hmin hz⟩

theorem isCompact_solutionMap (hKx : IsCompact (K x)) (hφ : Continuous φ) :
    IsCompact (solutionMap φ K x) := by
  have hc : Continuous fun z ↦ φ (x, z) := by fun_prop
  have e : solutionMap φ K x = K x ∩ ⋂ z ∈ K x, {y | φ (x, y) ≤ φ (x, z)} := by
    ext y
    simp [solutionMap]
  rw [e]
  exact hKx.inter_right (isClosed_biInter fun z _ ↦ isClosed_le hc continuous_const)

/-- Thm. 5.2 of [Dempe 2002] (existence of optimistic solutions): if
`{(x, y) | x ∈ Ω, y ∈ K(x)}` is compact, `Ω` and `gph K` are closed, `K` is lower
semicontinuous on `Ω`, `f`, `φ` are continuous and the follower's problem is feasible for some
`x ∈ Ω`, then a global optimistic solution exists. -/
theorem exists_isOptimisticSolution (hC : IsCompact {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ K p.1})
    (hΩ : IsClosed Ω) (hK : IsClosed (graph K)) (hlsc : ∀ x ∈ Ω, LowerHemicontinuousAt K x)
    (hφ : Continuous φ) (hf : Continuous f) (hne : ∃ x ∈ Ω, (K x).Nonempty) :
    ∃ x₀ y₀, IsOptimisticSolution f φ K Ω x₀ y₀ := by
  obtain ⟨x, hx, hKx⟩ := hne
  obtain ⟨y, hy⟩ := solutionMap_nonempty_of_isCompact (isCompact_apply hC hK hx) hKx hφ
  exact exists_isOptimisticSolution_of_isCompact
    (hC.of_isClosed_subset (isClosed_bilevelFeasible hΩ hK hlsc hφ) fun p hp ↦ ⟨hp.1, hp.2.1⟩)
    ⟨(x, y), hx, hy⟩ hf.continuousOn

/-- The pessimistic value function is lower semicontinuous at `x₀` when `Ψ` is lower
semicontinuous at `x₀` [Dempe 2002, proof of Thm. 5.3]. -/
theorem lowerSemicontinuousAt_pessimisticValue
    (hΨ : LowerHemicontinuousAt (solutionMap φ K) x₀) (hf : Continuous f) :
    LowerSemicontinuousAt (pessimisticValue f φ K) x₀ := by
  intro t ht
  unfold pessimisticValue at ht
  obtain ⟨y, hy⟩ := lt_iSup_iff.1 ht
  obtain ⟨hyΨ, hyt⟩ := lt_iSup_iff.1 hy
  have hc : Continuous fun p : E × F ↦ (f p : EReal) := continuous_coe_real_ereal.comp hf
  filter_upwards [hΨ.eventually_exists (P := fun x' y' ↦ t < (f (x', y') : EReal)) hyΨ
    ((hc.tendsto (x₀, y)).eventually (eventually_gt_nhds hyt))] with x hx
  obtain ⟨y', hy'Ψ, hy'⟩ := hx
  exact hy'.trans_le (le_pessimisticValue hy'Ψ)

/-- Thm. 5.3 of [Dempe 2002] (existence of pessimistic solutions): if
`{(x, y) | x ∈ Ω, y ∈ K(x)}` is compact, `gph K` is closed, `Ψ` is lower semicontinuous on `Ω`,
`f`, `φ` are continuous and the follower's problem is feasible for some `x ∈ Ω`, then a global
pessimistic solution exists. -/
theorem exists_isPessimisticSolution (hC : IsCompact {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ K p.1})
    (hK : IsClosed (graph K)) (hΨ : ∀ x ∈ Ω, LowerHemicontinuousAt (solutionMap φ K) x)
    (hφ : Continuous φ) (hf : Continuous f) (hne : ∃ x ∈ Ω, (K x).Nonempty) :
    ∃ x₀ y₀, IsPessimisticSolution f φ K Ω x₀ y₀ := by
  have hD : solvableSet φ K Ω = Prod.fst '' {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ K p.1} := by
    ext x
    constructor
    · rintro ⟨hx, y, hy⟩
      exact ⟨(x, y), ⟨hx, hy.1⟩, rfl⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨hp1, solutionMap_nonempty_of_isCompact (isCompact_apply hC hK hp1) ⟨p.2, hp2⟩ hφ⟩
  have hDc : IsCompact (solvableSet φ K Ω) := by
    rw [hD]
    exact hC.image continuous_fst
  obtain ⟨x, hx, hKx⟩ := hne
  have hDne : (solvableSet φ K Ω).Nonempty :=
    ⟨x, hx, solutionMap_nonempty_of_isCompact (isCompact_apply hC hK hx) hKx hφ⟩
  obtain ⟨x₀, hx₀, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hDne hDc fun x hx ↦
    (lowerSemicontinuousAt_pessimisticValue (hΨ x hx.1) hf).lowerSemicontinuousWithinAt _
  have hc : Continuous fun y ↦ f (x₀, y) := by fun_prop
  obtain ⟨y₀, hy₀, hmax⟩ := (isCompact_solutionMap (isCompact_apply hC hK hx₀.1) hφ).exists_isMaxOn
    hx₀.2 hc.continuousOn
  exact ⟨x₀, y₀, hx₀.1, hy₀, fun y hy ↦ hmax hy, hmin⟩

end Berge

/-! ### (MFCQ) and lower semicontinuity of the feasible-set map -/

section Regular

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {Ω : Set E} {x x₀ : E}
  {y y₀ : F}

omit [Fintype ι] in
/-- The partial derivative of a jointly differentiable function. -/
theorem fderiv_section {u : E × F → ℝ} (h : DifferentiableAt ℝ u (x, y)) :
    fderiv ℝ (fun z ↦ u (x, z)) y = (fderiv ℝ u (x, y)).comp (ContinuousLinearMap.inr ℝ E F) :=
  (h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)).fderiv

/-- For jointly differentiable constraints, `LowerPLI` is lower-level regularity (6.52) of
[Mordukhovich 2018] (`VariationalAnalysis.LowerLevelRegular`). -/
theorem lowerPLI_iff_lowerLevelRegular (hg : ∀ i, DifferentiableAt ℝ (g i) (x, y)) :
    LowerPLI g x y ↔ VariationalAnalysis.LowerLevelRegular g x y := by
  have h : ∀ i, fderiv ℝ (fun z ↦ g i (x, z)) y =
      (fderiv ℝ (g i) (x, y)).comp (ContinuousLinearMap.inr ℝ E F) := fun i ↦ fderiv_section (hg i)
  simp only [LowerPLI, VariationalAnalysis.LowerLevelRegular, h]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [Fintype ι] in
/-- A Lipschitz-like map `S` around `(x₀, y₀) ∈ gph S` meets every neighborhood of `y₀` at all
points near `x₀`. -/
theorem eventually_inter_nonempty_of_lipschitzLikeAt {S : E → Set F}
    (h : VariationalAnalysis.LipschitzLikeAt S x₀ y₀) (hy₀ : y₀ ∈ S x₀) {W : Set F}
    (hW : W ∈ 𝓝 y₀) : ∀ᶠ x in 𝓝 x₀, (S x ∩ W).Nonempty := by
  obtain ⟨ℓ, U, hU, V, hV, hlip⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  have hr : 0 < ε / (ℓ + 1) := div_pos hε (by positivity)
  filter_upwards [hU, Metric.ball_mem_nhds x₀ hr] with x hxU hxb
  obtain ⟨w, hwS, hw⟩ := hlip x₀ (mem_of_mem_nhds hU) x hxU y₀ ⟨hy₀, mem_of_mem_nhds hV⟩
  refine ⟨w, hwS, hball ?_⟩
  rw [Metric.mem_ball, dist_comm]
  rw [Metric.mem_ball, dist_comm, lt_div_iff₀ (by positivity)] at hxb
  have hd := dist_nonneg (x := x₀) (y := x)
  nlinarith [ℓ.coe_nonneg]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Under (MFCQ) (lower-level regularity) at `(x₀, y₀)`, the feasible-set map
`G(x) = {y | gᵢ(x, y) ≤ 0}` is Lipschitz-like around `(x₀, y₀)`, by the Mordukhovich criterion
[Mordukhovich 2018, Thm. 3.3] and the normals to `gph G` [Exercise 2.51(ii)]. -/
theorem lipschitzLikeAt_lowerFeasible (hg : ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y₀))
    (hy₀ : y₀ ∈ lowerFeasible g x₀) (hreg : VariationalAnalysis.LowerLevelRegular g x₀ y₀) :
    VariationalAnalysis.LipschitzLikeAt (lowerFeasible g) x₀ y₀ := by
  refine (VariationalAnalysis.lipschitzLikeAt_iff_forall_mem_coderiv_zero
    (VariationalAnalysis.locallyClosed_graph_lowerFeasible hg) hy₀).2 fun u hu ↦ ?_
  obtain ⟨lam, hlam, hcs, heq⟩ := VariationalAnalysis.normalCone_graph_lowerFeasible_subset hg hy₀ hreg hu
  have hl : lam = 0 := hreg lam hlam (fun i hi ↦ (mul_eq_zero.1 (hcs i)).resolve_right hi.ne) (by
    ext z
    have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (0, z)) heq
    simpa using this.symm)
  ext z
  have := congrArg (fun T : StrongDual ℝ (E × F) ↦ T (z, 0)) heq
  simpa [hl] using this

/-- Under (MFCQ) at every feasible point of the follower's problem at `x₀`, the feasible-set
map `G` is lower semicontinuous at `x₀` [Dempe 2002, role of (MFCQ) in Thm. 4.3]. -/
theorem lowerHemicontinuousAt_lowerFeasible
    (hg : ∀ y ∈ lowerFeasible g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerFeasible g x₀, VariationalAnalysis.LowerLevelRegular g x₀ y) :
    LowerHemicontinuousAt (lowerFeasible g) x₀ := by
  rintro V hV ⟨y, hyK, hyV⟩
  exact eventually_inter_nonempty_of_lipschitzLikeAt
    (lipschitzLikeAt_lowerFeasible (hg y hyK) hyK (hreg y hyK)) hyK (hV.mem_nhds hyV)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [Fintype ι] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
theorem isClosed_graph_lowerFeasible (hg : ∀ i, Continuous (g i)) :
    IsClosed (graph (lowerFeasible g)) := by
  rw [VariationalAnalysis.graph_lowerFeasible, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le (hg i) continuous_const

/-- Thm. 4.3 of [Dempe 2002] for smooth inequality constraints: under (MFCQ) at all feasible
points `(x₀, y)` and uniform boundedness of `G` near `x₀`, the lower-level value function is
continuous at `x₀`. -/
theorem continuousAt_lowerValue_of_regular (hgc : ∀ i, Continuous (g i))
    (hg : ∀ y ∈ lowerFeasible g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerFeasible g x₀, VariationalAnalysis.LowerLevelRegular g x₀ y)
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, lowerFeasible g x ⊆ C)
    (hφ : Continuous φ) : ContinuousAt (lowerValue φ g) x₀ :=
  continuousAt_marginal (isClosed_graph_lowerFeasible hgc) hb
    (lowerHemicontinuousAt_lowerFeasible hg hreg) hφ

/-- Thm. 4.3 of [Dempe 2002] for smooth inequality constraints: under the assumptions of
`continuousAt_lowerValue_of_regular`, the lower-level solution map is upper semicontinuous at
`x₀`. -/
theorem upperHemicontinuousAt_lowerSolution_of_regular (hgc : ∀ i, Continuous (g i))
    (hg : ∀ y ∈ lowerFeasible g x₀, ∀ i, ContDiffAt ℝ 1 (g i) (x₀, y))
    (hreg : ∀ y ∈ lowerFeasible g x₀, VariationalAnalysis.LowerLevelRegular g x₀ y)
    (hb : ∃ U ∈ 𝓝 x₀, ∃ C, IsCompact C ∧ ∀ x ∈ U, lowerFeasible g x ⊆ C)
    (hφ : Continuous φ) : UpperHemicontinuousAt (lowerSolution φ g) x₀ := by
  rw [← solutionMap_lowerFeasible]
  exact upperHemicontinuousAt_solutionMap (isClosed_graph_lowerFeasible hgc) hb
    (lowerHemicontinuousAt_lowerFeasible hg hreg) hφ

/-- Thm. 5.2 of [Dempe 2002] for smooth inequality constraints: if
`{(x, y) | x ∈ Ω, g(x, y) ≤ 0}` is compact, `Ω` is closed, (MFCQ) holds at all feasible points
with `x ∈ Ω`, `f`, `φ` are continuous and the follower's problem is feasible for some `x ∈ Ω`,
then a global optimistic solution exists. -/
theorem exists_isOptimisticSolution_of_regular (hgc : ∀ i, Continuous (g i))
    (hg : ∀ x ∈ Ω, ∀ y ∈ lowerFeasible g x, ∀ i, ContDiffAt ℝ 1 (g i) (x, y))
    (hreg : ∀ x ∈ Ω, ∀ y ∈ lowerFeasible g x, VariationalAnalysis.LowerLevelRegular g x y)
    (hC : IsCompact {p : E × F | p.1 ∈ Ω ∧ p.2 ∈ lowerFeasible g p.1}) (hΩ : IsClosed Ω)
    (hφ : Continuous φ) (hf : Continuous f) (hne : ∃ x ∈ Ω, (lowerFeasible g x).Nonempty) :
    ∃ x₀ y₀, IsOptimisticSolution f φ (lowerFeasible g) Ω x₀ y₀ :=
  exists_isOptimisticSolution hC hΩ (isClosed_graph_lowerFeasible hgc)
    (fun x hx ↦ lowerHemicontinuousAt_lowerFeasible (hg x hx) (hreg x hx)) hφ hf hne

end Regular

/-! ### Thm. 4.2: upper semicontinuity of `Λ` and `SP` -/

section Stability

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ} {x₀ : E} {y₀ : F}

omit [Fintype ι] in
/-- The partial derivative `(x, y) ↦ ∇_y u(x, y)` of a `C¹` function is continuous. -/
theorem continuous_fderiv_section {u : E × F → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous fun p : E × F ↦ fderiv ℝ (fun z ↦ u (p.1, z)) p.2 := by
  have : (fun p : E × F ↦ fderiv ℝ (fun z ↦ u (p.1, z)) p.2) =
      fun p ↦ (fderiv ℝ u p).comp (ContinuousLinearMap.inr ℝ E F) :=
    funext fun p ↦ fderiv_section ((hu.differentiable one_ne_zero) p)
  rw [this]
  exact (hu.continuous_fderiv one_ne_zero).clm_comp continuous_const

/-- For `C¹` data, the multiplier map `(x, y) ↦ Λ(x, y)` has a closed graph. -/
theorem isClosed_graph_lowerMultipliers (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    IsClosed (graph fun p : E × F ↦ lowerMultipliers φ g p.1 p.2) := by
  have hD : ∀ i, Continuous fun q : (E × F) × (ι → ℝ) ↦
      fderiv ℝ (fun z ↦ g i (q.1.1, z)) q.1.2 :=
    fun i ↦ (continuous_fderiv_section (hg i)).comp continuous_fst
  have e : graph (fun p : E × F ↦ lowerMultipliers φ g p.1 p.2) =
      (⋂ i, {q : (E × F) × (ι → ℝ) | g i q.1 ≤ 0}) ∩ ((⋂ i, {q | 0 ≤ q.2 i}) ∩
        ((⋂ i, {q | q.2 i * g i q.1 = 0}) ∩
          {q | fderiv ℝ (fun z ↦ φ (q.1.1, z)) q.1.2 +
            ∑ i, q.2 i • fderiv ℝ (fun z ↦ g i (q.1.1, z)) q.1.2 = 0})) := by
    ext q
    simp [VariationalAnalysis.graph, lowerMultipliers, IsLowerKKT]
  rw [e]
  refine (isClosed_iInter fun i ↦ isClosed_le ((hg i).continuous.comp continuous_fst)
    continuous_const).inter ((isClosed_iInter fun i ↦ isClosed_le continuous_const
      ((continuous_apply i).comp continuous_snd)).inter ((isClosed_iInter fun i ↦ isClosed_eq
        (((continuous_apply i).comp continuous_snd).mul ((hg i).continuous.comp continuous_fst))
        continuous_const).inter (isClosed_eq (((continuous_fderiv_section hφ).comp
          continuous_fst).add (continuous_finsetSum _ fun i _ ↦
            ((continuous_apply i).comp continuous_snd).smul (hD i))) continuous_const)))

/-- Positive linear independence of the active gradients (dual (MFCQ)) persists near `(x̄, ȳ)`
for `C¹` constraints, with a uniform constant: `c ‖μ‖ ≤ ‖∑ μᵢ ∇_y gᵢ(x, y)‖` for all admissible
multipliers `μ` at `(x, y)`. -/
theorem exists_eventually_mul_norm_le_of_lowerPLI (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hreg : LowerPLI g x₀ y₀) :
    ∃ c > 0, ∀ᶠ p : E × F in 𝓝 (x₀, y₀), ∀ μ : ι → ℝ, (∀ i, 0 ≤ μ i) →
      (∀ i, g i p < 0 → μ i = 0) →
        c * ‖μ‖ ≤ ‖∑ i, μ i • fderiv ℝ (fun z ↦ g i (p.1, z)) p.2‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_mul_norm_le_of_lowerPLI hreg
  set D : ι → E × F → StrongDual ℝ F := fun i p ↦ fderiv ℝ (fun z ↦ g i (p.1, z)) p.2 with hD
  have hDc : ∀ i, Continuous (D i) := fun i ↦ continuous_fderiv_section (hg i)
  have h1 : ∀ᶠ p in 𝓝 (x₀, y₀), ∀ i, g i (x₀, y₀) < 0 → g i p < 0 :=
    eventually_all.2 fun i ↦ by
      by_cases h : g i (x₀, y₀) < 0
      · exact ((hg i).continuous.continuousAt.eventually_lt continuousAt_const h).mono
          fun _ hp _ ↦ hp
      · exact Eventually.of_forall fun _ h' ↦ absurd h' h
  have h2 : ∀ᶠ p in 𝓝 (x₀, y₀), ∑ i, ‖D i p - D i (x₀, y₀)‖ < c / 2 :=
    (continuous_finsetSum _ fun i _ ↦ ((hDc i).sub continuous_const).norm).continuousAt.eventually_lt
      continuousAt_const (show ∑ i, ‖D i (x₀, y₀) - D i (x₀, y₀)‖ < c / 2 by simpa using half_pos hc)
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [h1, h2] with p hp1 hp2 μ hμ hsupp
  have hb : c * ‖μ‖ ≤ ‖∑ i, μ i • D i (x₀, y₀)‖ := hbound μ hμ fun i hi ↦ hsupp i (hp1 i hi)
  have hkey : ∑ i, μ i • D i (x₀, y₀) =
      ∑ i, μ i • D i p - ∑ i, μ i • (D i p - D i (x₀, y₀)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, sub_sub_cancel]
  have hnorm : ‖∑ i, μ i • (D i p - D i (x₀, y₀))‖ ≤ ‖μ‖ * (c / 2) :=
    calc ‖∑ i, μ i • (D i p - D i (x₀, y₀))‖
        ≤ ∑ i, ‖μ i • (D i p - D i (x₀, y₀))‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖μ‖ * ‖D i p - D i (x₀, y₀)‖ := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm μ i) (norm_nonneg _)
      _ = ‖μ‖ * ∑ i, ‖D i p - D i (x₀, y₀)‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ ‖μ‖ * (c / 2) := mul_le_mul_of_nonneg_left hp2.le (norm_nonneg _)
  have hle : c * ‖μ‖ ≤ ‖∑ i, μ i • D i p‖ + ‖μ‖ * (c / 2) :=
    calc c * ‖μ‖ ≤ ‖∑ i, μ i • D i (x₀, y₀)‖ := hb
      _ = ‖∑ i, μ i • D i p - ∑ i, μ i • (D i p - D i (x₀, y₀))‖ := by rw [hkey]
      _ ≤ ‖∑ i, μ i • D i p‖ + ‖∑ i, μ i • (D i p - D i (x₀, y₀))‖ := norm_sub_le _ _
      _ ≤ ‖∑ i, μ i • D i p‖ + ‖μ‖ * (c / 2) := by gcongr
  show c / 2 * ‖μ‖ ≤ ‖∑ i, μ i • D i p‖
  linarith

/-- Dual (MFCQ) for `C¹` constraints is stable: it persists near `(x̄, ȳ)`. -/
theorem eventually_lowerPLI (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀) :
    ∀ᶠ p : E × F in 𝓝 (x₀, y₀), LowerPLI g p.1 p.2 := by
  obtain ⟨c, hc, h⟩ := exists_eventually_mul_norm_le_of_lowerPLI hg hreg
  filter_upwards [h] with p hp μ hμ hsupp hsum
  have hle := hp μ hμ hsupp
  rw [hsum, norm_zero] at hle
  exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg μ]) (norm_nonneg _))

/-- First part of the proof of Thm. 4.2 of [Dempe 2002]: under (MFCQ) at `(x̄, ȳ)` (in its dual
form), the multiplier map `Λ` is locally bounded at `(x̄, ȳ)`. -/
theorem exists_eventually_lowerMultipliers_subset (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀) :
    ∃ R, ∀ᶠ p : E × F in 𝓝 (x₀, y₀), lowerMultipliers φ g p.1 p.2 ⊆ Metric.closedBall 0 R := by
  obtain ⟨c, hc, hb⟩ := exists_eventually_mul_norm_le_of_lowerPLI hg hreg
  have h3 : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), ‖fderiv ℝ (fun z ↦ φ (p.1, z)) p.2‖ <
      ‖fderiv ℝ (fun z ↦ φ (x₀, z)) y₀‖ + 1 :=
    (continuous_fderiv_section hφ).norm.continuousAt.eventually_lt continuousAt_const
      (lt_add_one _)
  refine ⟨(‖fderiv ℝ (fun z ↦ φ (x₀, z)) y₀‖ + 1) / c, ?_⟩
  filter_upwards [hb, h3] with p hp hp3 lam hlam
  obtain ⟨-, hl0, hcs, hKKT⟩ := hlam
  have h := hp lam hl0 fun i hi ↦ (mul_eq_zero.1 (hcs i)).resolve_right hi.ne
  rw [eq_neg_of_add_eq_zero_right hKKT, norm_neg] at h
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
  linarith

/-- Thm. 4.2 of [Dempe 2002], first part: for `C¹` data with (MFCQ) at `(x̄, ȳ)`, the multiplier
map `Λ` is upper semicontinuous at `(x̄, ȳ)`. -/
theorem upperHemicontinuousAt_lowerMultipliers (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀) :
    UpperHemicontinuousAt (fun p : E × F ↦ lowerMultipliers φ g p.1 p.2) (x₀, y₀) :=
  let ⟨R, hR⟩ := exists_eventually_lowerMultipliers_subset hφ hg hreg
  upperHemicontinuousAt_of_isClosed_graph (isClosed_graph_lowerMultipliers hφ hg)
    ⟨_, hR, _, isCompact_closedBall 0 R, fun _ hp ↦ hp⟩

/-- Thm. 4.2 of [Dempe 2002], second part: for `C¹` data, if the follower's feasible-set map is
locally bounded at `x̄` and (MFCQ) holds at every feasible point `(x̄, y)`, then the stationary
solution map `SP` is upper semicontinuous at `x̄`. (MFCQ) at the points of `SP(x̄)` alone, as in
the book, is not enough: `not_upperHemicontinuousAt_stationaryMap_example`. -/
theorem upperHemicontinuousAt_stationaryMap [FiniteDimensional ℝ F] (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hb : VariationalAnalysis.LocallyBoundedAt (lowerFeasible g) x₀)
    (hreg : ∀ y ∈ lowerFeasible g x₀, LowerPLI g x₀ y) :
    UpperHemicontinuousAt (stationaryMap φ g) x₀ := by
  have hSG : ∀ x, stationaryMap φ g x ⊆ lowerFeasible g x := fun _ _ ⟨_, hl⟩ ↦ hl.1
  refine upperHemicontinuousAt_of_mem_closure_graph (fun y hy ↦ ?_) ?_
  · -- closure points over `x̄` are stationary
    have hyG : y ∈ lowerFeasible g x₀ := by
      have h := closure_mono (show graph (stationaryMap φ g) ⊆ graph (lowerFeasible g) from
        fun p hp ↦ hSG p.1 hp) hy
      rwa [(isClosed_graph_lowerFeasible fun i ↦ (hg i).continuous).closure_eq] at h
    by_contra hne
    have hempty : lowerMultipliers φ g x₀ y = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hev := upperHemicontinuousAt_lowerMultipliers hφ hg (hreg y hyG) ∅ isOpen_empty
      (show lowerMultipliers φ g x₀ y ⊆ ∅ by rw [hempty])
    obtain ⟨p, hp, hpG⟩ := mem_closure_iff_nhds.1 hy _ hev
    obtain ⟨lam, hlam⟩ := hpG
    exact hp hlam
  · -- (C): uniform boundedness
    obtain ⟨U, hU, hB⟩ := hb
    exact ⟨U, hU, _, hB.isCompact_closure, fun x hx y hy ↦
      subset_closure (mem_biUnion hx (hSG x hy))⟩

end Stability

/-! ### Example: (MFCQ) on `SP(x̄)` alone does not give Thm. 4.2 -/

section Example

/-- The constraint `y² - x² ≤ 0`. -/
private def exg₂ : Unit → ℝ × ℝ → ℝ := fun _ p ↦ p.2 ^ 2 - p.1 ^ 2

private def exφ₂ : ℝ × ℝ → ℝ := fun p ↦ p.2

private theorem exφ₂_deriv (x y : ℝ) : fderiv ℝ (fun z ↦ exφ₂ (x, z)) y 1 = 1 :=
  fderiv_apply_one_of_hasDerivAt (hasDerivAt_id' y)

private theorem exg₂_deriv (x y : ℝ) : fderiv ℝ (fun z ↦ exg₂ () (x, z)) y 1 = 2 * y :=
  fderiv_apply_one_of_hasDerivAt (((hasDerivAt_pow 2 y).sub_const (x ^ 2)).congr_deriv
    (by ring))

private theorem exKKT_iff (x y : ℝ) (lam : Unit → ℝ) :
    fderiv ℝ (fun z ↦ exφ₂ (x, z)) y + ∑ i, lam i • fderiv ℝ (fun z ↦ exg₂ i (x, z)) y = 0 ↔
      1 + lam () * (2 * y) = 0 := by
  rw [← exφ₂_deriv x y, ← exg₂_deriv x y]
  constructor
  · intro h
    simpa using congrArg (fun T : StrongDual ℝ ℝ ↦ T 1) h
  · intro h
    refine ContinuousLinearMap.ext_ring ?_
    simpa using h

/-- Thm. 4.2 of [Dempe 2002] needs (MFCQ) beyond `SP(x̄)`: for `min_y {y | y² ≤ x²}` the
feasible-set map is locally bounded at `0` and `SP(0) = ∅` (so (MFCQ) holds at all points of
`SP(0)`), but `SP(x) = {-|x|}` for `x ≠ 0`, so `SP` is not upper semicontinuous at `0`. (MFCQ)
fails at the feasible point `(0, 0)`. -/
theorem not_upperHemicontinuousAt_stationaryMap_example :
    VariationalAnalysis.LocallyBoundedAt (lowerFeasible exg₂) 0 ∧
      stationaryMap exφ₂ exg₂ 0 = ∅ ∧ ¬ LowerPLI exg₂ 0 0 ∧
      ¬ UpperHemicontinuousAt (stationaryMap exφ₂ exg₂) 0 := by
  have hSP0 : stationaryMap exφ₂ exg₂ 0 = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy0 ↦ ?_
    obtain ⟨lam, hfeas, -, -, heq⟩ := hy0
    have hy : y = 0 := by
      have := hfeas ()
      simp only [exg₂] at this
      nlinarith [sq_nonneg y]
    rw [exKKT_iff, hy] at heq
    norm_num at heq
  have hSP : ∀ x : ℝ, x ≠ 0 → -|x| ∈ stationaryMap exφ₂ exg₂ x := fun x hx ↦ by
    have hax : |x| ≠ 0 := abs_ne_zero.2 hx
    refine ⟨fun _ ↦ 1 / (2 * |x|), fun _ ↦ ?_, fun _ ↦ by positivity, fun _ ↦ ?_, ?_⟩
    · simp [exg₂, sq_abs]
    · simp [exg₂, sq_abs]
    · rw [exKKT_iff]
      field_simp
      ring
  refine ⟨⟨Ioo (-1) 1, Ioo_mem_nhds (by norm_num) (by norm_num),
    (Metric.isBounded_Icc (-1 : ℝ) 1).subset ?_⟩, hSP0, ?_, ?_⟩
  · simp only [iUnion_subset_iff]
    intro x hx y hy
    have h := hy ()
    simp only [exg₂] at h
    obtain ⟨hx1, hx2⟩ := hx
    constructor <;> nlinarith [sq_nonneg (y + 1), sq_nonneg (y - 1)]
  · intro hreg
    have h := hreg (fun _ ↦ 1) (fun _ ↦ zero_le_one) (fun _ h ↦ by simp [exg₂] at h) (by
      refine ContinuousLinearMap.ext_ring ?_
      simpa using exg₂_deriv 0 0)
    simpa using congrFun h ()
  · intro husc
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (husc ∅ isOpen_empty (by rw [hSP0]))
    have hx : ε / 2 ≠ 0 := by positivity
    have := hball (show dist (ε / 2) 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith) (hSP (ε / 2) hx)
    exact this

end Example

end Bilevel
