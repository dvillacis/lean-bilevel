/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Basic
import VariationalAnalysis.Optimality.BilevelSmooth
import ConvexAnalysis.Convex.ConvexFunction

/-!
# The KKT reformulation of bilevel programs

Sect. 5.4–5.5 of [Dempe 2002] and the convex part of the single-level reformulations in
[Schmidt 2024], following [Dempe–Dutta 2012]: the follower's problem
`min_y {φ(x, y) | gᵢ(x, y) ≤ 0, i ∈ ι}` is replaced by its KKT conditions, giving the
reformulation (5.26)
`min_{x, y, λ} f(x, y)` s.t. `x ∈ Ω`, `∇_y φ(x, y) + ∑ λᵢ ∇_y gᵢ(x, y) = 0`, `g(x, y) ≤ 0`,
`λ ≥ 0`, `λᵢ gᵢ(x, y) = 0`.
Partial derivatives in `y` are derivatives of the sections `z ↦ φ(x, z)`, `z ↦ gᵢ(x, z)`.

## Main definitions

* `IsLowerKKT φ g x y λ`: `(y, λ)` satisfies the KKT conditions of the follower's problem at `x`.
* `lowerMultipliers φ g x y`: the multiplier set `Λ(x, y)`.
* `kktFeasible φ g Ω`: the feasible set of (5.26) in `(E × F) × ℝ^ι`.
* `IsConvexLower φ g x`, `SlaterAt g x`, `LowerPLI g x y`: convexity of the follower's problem,
  Slater's condition and positive linear independence of the active gradients (the dual form of
  (MFCQ)).

## Main results

* `isLowerKKT_iff_min`: (5.26) and the nonsmooth reformulation (5.27) with `min {-g, λ} = 0` have
  the same feasible set.
* `mem_solutionMap_of_isLowerKKT`: for a convex follower's problem the KKT conditions are
  sufficient (no constraint qualification).
* `exists_isLowerKKT_of_mem_solutionMap`, `lowerPLI_of_slaterAt`: they are necessary under
  positive linear independence (no convexity), which follows from Slater's condition for convex
  constraints.
* `isMinOn_kktFeasible_of_isMinOn`: global solutions of (5.5) give global solutions of (5.26)
  for every multiplier [Dempe–Dutta 2012; Schmidt 2024, p. 151].
* `isMinOn_bilevelFeasible_of_isMinOn_kktFeasible`: global solutions of (5.26) give global
  solutions of (5.5) under Slater's condition for all `x ∈ Ω` [Dempe–Dutta 2012;
  Schmidt 2024, p. 171].
* `isLocalMinOn_kktFeasible_of_isLocalMinOn`: Thm. 5.15 of [Dempe 2002]: local solutions of (5.5)
  (in particular local optimistic solutions) give local solutions of (5.26) for every multiplier.
* `not_isLocalMinOn_kktFeasible_nonconvex_example`: without convexity a global optimistic
  solution need not be a local solution of (5.26) [Dempe 2002, Example on p. 158].
* `isMinOn_kktFeasible_noSlater_example`, `not_isMinOn_bilevelFeasible_noSlater_example`:
  without Slater's condition global solutions of (5.26) need not solve (5.5)
  [Dempe–Dutta 2012; Schmidt 2024, pp. 180–187].

## Remarks on the sources

* Lower-level equality constraints are omitted (for a convex follower's problem they are affine
  in `y`); the leader's constraints are an arbitrary set `Ω` (Dempe: `G(y) ≤ 0`), without
  coupling.
* Thm. 5.15 of [Dempe 2002] assumes (MFCQ) for the follower's problem at all bilevel-feasible
  points; the proof only uses sufficiency of the KKT conditions (convexity), and (MFCQ) enters
  only to guarantee `Λ(x̄, ȳ) ≠ ∅` (`exists_isLowerKKT_of_mem_solutionMap`).
* The proofs on [Schmidt 2024, pp. 152, 173–179] use sufficiency of the KKT conditions at points
  other than the reference point without mentioning it; this is why convexity and
  differentiability are assumed for all `x ∈ Ω`.
* In the Example on p. 158 of [Dempe 2002] the nonzero stationary points of the follower's
  problem are `x = (3/8 ± 1/40) y`, not `(3/8 ± 1/1600) y`.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι : Type*}

section Definitions

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
variable (φ : E × F → ℝ) (g : ι → E × F → ℝ)

/-- The KKT conditions of the follower's problem `min_y {φ(x, y) | gᵢ(x, y) ≤ 0}` at `(y, λ)`. -/
def IsLowerKKT (x : E) (y : F) (lam : ι → ℝ) : Prop :=
  (∀ i, g i (x, y) ≤ 0) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i (x, y) = 0) ∧
    fderiv ℝ (fun z ↦ φ (x, z)) y + ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y = 0

/-- The set `Λ(x, y)` of KKT multipliers of the follower's problem. -/
def lowerMultipliers (x : E) (y : F) : Set (ι → ℝ) :=
  {lam | IsLowerKKT φ g x y lam}

/-- The feasible set of the KKT reformulation (5.26) of [Dempe 2002]. -/
def kktFeasible (Ω : Set E) : Set ((E × F) × (ι → ℝ)) :=
  {q | q.1.1 ∈ Ω ∧ IsLowerKKT φ g q.1.1 q.1.2 q.2}

/-- The follower's problem at `x` is convex. -/
def IsConvexLower (x : E) : Prop :=
  ConvexOn ℝ univ (fun z ↦ φ (x, z)) ∧ ∀ i, ConvexOn ℝ univ (fun z ↦ g i (x, z))

/-- The follower's problem at `x` has differentiable data. -/
def IsDifferentiableLower (x : E) : Prop :=
  ∀ y, DifferentiableAt ℝ (fun z ↦ φ (x, z)) y ∧ ∀ i, DifferentiableAt ℝ (fun z ↦ g i (x, z)) y

end Definitions

section Definitions'

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι] (g : ι → E × F → ℝ)

/-- Slater's condition for the follower's constraints at `x`. -/
def SlaterAt (x : E) : Prop :=
  ∃ z, ∀ i, g i (x, z) < 0

/-- Positive linear independence of the active gradients `∇_y gᵢ(x, y)`, the dual form of
(MFCQ) for the follower's problem. -/
def LowerPLI (x : E) (y : F) : Prop :=
  ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, g i (x, y) < 0 → lam i = 0) →
    ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y = 0 → lam = 0

end Definitions'

theorem min_eq_zero_iff {a b : ℝ} : min a b = 0 ↔ 0 ≤ a ∧ 0 ≤ b ∧ a * b = 0 := by
  constructor
  · intro h
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at h
      subst h
      exact ⟨le_rfl, hab, zero_mul _⟩
    · rw [min_eq_right hab] at h
      subst h
      exact ⟨hab, le_rfl, mul_zero _⟩
  · rintro ⟨ha, hb, hab⟩
    rcases mul_eq_zero.1 hab with h | h
    · subst h
      exact min_eq_left hb
    · subst h
      exact min_eq_right ha

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
variable {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {Ω : Set E} {x x₀ : E} {y y₀ : F}
  {lam lam₀ : ι → ℝ}

/-- The complementarity conditions of (5.26) are the equations `min {-gᵢ(x, y), λᵢ} = 0` of the
nonsmooth reformulation (5.27) of [Dempe 2002]. -/
theorem isLowerKKT_iff_min :
    IsLowerKKT φ g x y lam ↔ (∀ i, min (-g i (x, y)) (lam i) = 0) ∧
      fderiv ℝ (fun z ↦ φ (x, z)) y + ∑ i, lam i • fderiv ℝ (fun z ↦ g i (x, z)) y = 0 := by
  simp only [min_eq_zero_iff, IsLowerKKT, neg_nonneg, neg_mul, neg_eq_zero, mul_comm (g _ _)]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨fun i ↦ ⟨h1 i, h2 i, h3 i⟩, h4⟩,
    fun ⟨h, h4⟩ ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2.1, fun i ↦ (h i).2.2, h4⟩⟩

/-! ### KKT conditions of the follower's problem -/

/-- For a convex follower's problem the KKT conditions are sufficient for optimality. -/
theorem mem_solutionMap_of_isLowerKKT (hconv : IsConvexLower φ g x)
    (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, DifferentiableAt ℝ (fun z ↦ g i (x, z)) y) (h : IsLowerKKT φ g x y lam) :
    y ∈ solutionMap φ (lowerFeasible g) x := by
  obtain ⟨hfeas, hlam, hcs, hstat⟩ := h
  refine ⟨hfeas, fun z hz ↦ ?_⟩
  have hz' : ∀ i, g i (x, z) ≤ 0 := hz
  have h1 := Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (fun z ↦ φ (x, z)) y)
    hφ.hasFDerivAt hconv.1 (mem_univ y) z (mem_univ z)
  have h2 : ∀ i, g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (z - y) ≤ g i (x, z) := fun i ↦
    Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (fun z ↦ g i (x, z)) y)
      (hg i).hasFDerivAt (hconv.2 i) (mem_univ y) z (mem_univ z)
  have hs := congrArg (fun T : F →L[ℝ] ℝ ↦ T (z - y)) hstat
  simp only [add_apply, sum_apply,
    smul_apply, smul_eq_mul, zero_apply] at hs
  have h3 : ∑ i, lam i * g i (x, z) ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (hlam i) (hz' i)
  have h4 : ∑ i, lam i * (g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (z - y)) ≤
      ∑ i, lam i * g i (x, z) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h2 i) (hlam i)
  simp only [mul_add, hcs, zero_add] at h4
  beta_reduce at h1
  linarith

/-- Slater's condition for convex differentiable constraints implies positive linear
independence of the active gradients at every feasible point. -/
theorem lowerPLI_of_slaterAt (hconv : ∀ i, ConvexOn ℝ univ (fun z ↦ g i (x, z)))
    (hg : ∀ i, DifferentiableAt ℝ (fun z ↦ g i (x, z)) y) (hfeas : ∀ i, g i (x, y) ≤ 0)
    (hS : SlaterAt g x) : LowerPLI g x y := by
  obtain ⟨w, hw⟩ := hS
  intro lam hlam hin hsum
  have hcs : ∀ i, lam i * g i (x, y) = 0 := fun i ↦ by
    rcases (hfeas i).lt_or_eq with h | h
    · rw [hin i h, zero_mul]
    · rw [h, mul_zero]
  have h2 : ∀ i, g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (w - y) ≤ g i (x, w) := fun i ↦
    Convex_first_order_condition (f' := fun _ ↦ fderiv ℝ (fun z ↦ g i (x, z)) y)
      (hg i).hasFDerivAt (hconv i) (mem_univ y) w (mem_univ w)
  have hs := congrArg (fun T : F →L[ℝ] ℝ ↦ T (w - y)) hsum
  simp only [sum_apply, smul_apply, smul_eq_mul,
    zero_apply] at hs
  have h4 : ∑ i, lam i * (g i (x, y) + fderiv ℝ (fun z ↦ g i (x, z)) y (w - y)) ≤
      ∑ i, lam i * g i (x, w) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (h2 i) (hlam i)
  simp only [mul_add, hcs, zero_add, hs] at h4
  have hle : ∀ i ∈ Finset.univ, lam i * g i (x, w) ≤ 0 := fun i _ ↦
    mul_nonpos_of_nonneg_of_nonpos (hlam i) (hw i).le
  have hterm := (Finset.sum_eq_zero_iff_of_nonpos hle).1 (le_antisymm (Finset.sum_nonpos hle) h4)
  funext i
  exact (mul_eq_zero.1 (hterm i (Finset.mem_univ i))).resolve_right (hw i).ne

/-- The KKT conditions are necessary for optimality in the follower's problem under positive
linear independence of the active gradients (no convexity), via the normal cone to `C¹`
inequality systems [Mordukhovich 2018, Exercise 2.51(ii)]. -/
theorem exists_isLowerKKT_of_mem_solutionMap [FiniteDimensional ℝ F]
    (hy : y ∈ solutionMap φ (lowerFeasible g) x) (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) (hreg : LowerPLI g x y) :
    ∃ lam, IsLowerKKT φ g x y lam := by
  have hmin : IsLocalMinOn (fun z ↦ φ (x, z)) {z | ∀ i, g i (x, z) ≤ 0} y :=
    IsMinOn.localize (isMinOn_iff.2 fun z hz ↦ hy.2 z hz)
  have hN := VariationalAnalysis.regularNormalCone_subset_normalCone
    (VariationalAnalysis.neg_mem_regularNormalCone_of_hasFDerivAt hφ.hasFDerivAt hmin hy.1)
  obtain ⟨lam, hlam, hcs, heq⟩ :=
    VariationalAnalysis.normalCone_le_zero_subset (g := fun i z ↦ g i (x, z)) hg hy.1 hreg hN
  exact ⟨lam, hy.1, hlam, hcs, by rw [← heq, add_neg_cancel]⟩

/-- For a convex follower's problem with `C¹` constraints satisfying Slater's condition, the KKT
conditions characterize the solution map. -/
theorem mem_solutionMap_iff_exists_isLowerKKT [FiniteDimensional ℝ F]
    (hconv : IsConvexLower φ g x) (hS : SlaterAt g x)
    (hφ : DifferentiableAt ℝ (fun z ↦ φ (x, z)) y)
    (hg : ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) :
    y ∈ solutionMap φ (lowerFeasible g) x ↔ ∃ lam, IsLowerKKT φ g x y lam := by
  have hg' : ∀ i, DifferentiableAt ℝ (fun z ↦ g i (x, z)) y := fun i ↦
    (hg i).differentiableAt one_ne_zero
  exact ⟨fun hy ↦ exists_isLowerKKT_of_mem_solutionMap hy hφ hg
      (lowerPLI_of_slaterAt hconv.2 hg' hy.1 hS),
    fun ⟨_, h⟩ ↦ mem_solutionMap_of_isLowerKKT hconv hφ hg' h⟩

theorem mem_bilevelFeasible_of_mem_kktFeasible (hconv : ∀ x ∈ Ω, IsConvexLower φ g x)
    (hdiff : ∀ x ∈ Ω, IsDifferentiableLower φ g x) {q : (E × F) × (ι → ℝ)}
    (hq : q ∈ kktFeasible φ g Ω) : q.1 ∈ bilevelFeasible φ (lowerFeasible g) Ω :=
  ⟨hq.1, mem_solutionMap_of_isLowerKKT (hconv _ hq.1) (hdiff _ hq.1 _).1 (hdiff _ hq.1 _).2 hq.2⟩

/-! ### Global solutions -/

/-- Global solutions of (5.5) give global solutions of the KKT reformulation (5.26) for every
multiplier `λ̄ ∈ Λ(x̄, ȳ)` [Dempe–Dutta 2012; Schmidt 2024, p. 151]. Slater's condition at `x̄`
only serves to guarantee `Λ(x̄, ȳ) ≠ ∅` (`exists_isLowerKKT_of_mem_solutionMap`). -/
theorem isMinOn_kktFeasible_of_isMinOn
    (hmin : IsMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀)) (hx₀ : x₀ ∈ Ω)
    (hlam : lam₀ ∈ lowerMultipliers φ g x₀ y₀) (hconv : ∀ x ∈ Ω, IsConvexLower φ g x)
    (hdiff : ∀ x ∈ Ω, IsDifferentiableLower φ g x) :
    ((x₀, y₀), lam₀) ∈ kktFeasible φ g Ω ∧
      IsMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam₀) :=
  ⟨⟨hx₀, hlam⟩, isMinOn_iff.2 fun _ hq ↦
    isMinOn_iff.1 hmin _ (mem_bilevelFeasible_of_mem_kktFeasible hconv hdiff hq)⟩

/-- Global solutions of the KKT reformulation (5.26) give global solutions of (5.5) when
Slater's condition holds for all `x ∈ Ω` [Dempe–Dutta 2012; Schmidt 2024, p. 171]. -/
theorem isMinOn_bilevelFeasible_of_isMinOn_kktFeasible [FiniteDimensional ℝ F]
    (hmin : IsMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam₀))
    (hmem : ((x₀, y₀), lam₀) ∈ kktFeasible φ g Ω) (hconv : ∀ x ∈ Ω, IsConvexLower φ g x)
    (hS : ∀ x ∈ Ω, SlaterAt g x)
    (hsmooth : ∀ x ∈ Ω, ∀ y, DifferentiableAt ℝ (fun z ↦ φ (x, z)) y ∧
      ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) :
    (x₀, y₀) ∈ bilevelFeasible φ (lowerFeasible g) Ω ∧
      IsMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) := by
  have hdiff : ∀ x ∈ Ω, IsDifferentiableLower φ g x := fun x hx y ↦
    ⟨(hsmooth x hx y).1, fun i ↦ ((hsmooth x hx y).2 i).differentiableAt one_ne_zero⟩
  refine ⟨mem_bilevelFeasible_of_mem_kktFeasible hconv hdiff hmem, isMinOn_iff.2 fun p hp ↦ ?_⟩
  obtain ⟨lam, hlam⟩ := (mem_solutionMap_iff_exists_isLowerKKT (hconv _ hp.1) (hS _ hp.1)
    (hsmooth _ hp.1 p.2).1 (hsmooth _ hp.1 p.2).2).1 hp.2
  exact isMinOn_iff.1 hmin (p, lam) ⟨hp.1, hlam⟩

/-- Global solutions of (5.26) are global optimistic solutions under Slater's condition for all
`x ∈ Ω` (with `isOptimisticSolution_iff`). -/
theorem isOptimisticSolution_of_isMinOn_kktFeasible [FiniteDimensional ℝ F]
    (hmin : IsMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam₀))
    (hmem : ((x₀, y₀), lam₀) ∈ kktFeasible φ g Ω) (hconv : ∀ x ∈ Ω, IsConvexLower φ g x)
    (hS : ∀ x ∈ Ω, SlaterAt g x)
    (hsmooth : ∀ x ∈ Ω, ∀ y, DifferentiableAt ℝ (fun z ↦ φ (x, z)) y ∧
      ∀ i, ContDiffAt ℝ 1 (fun z ↦ g i (x, z)) y) :
    IsOptimisticSolution f φ (lowerFeasible g) Ω x₀ y₀ :=
  isOptimisticSolution_iff.2
    (isMinOn_bilevelFeasible_of_isMinOn_kktFeasible hmin hmem hconv hS hsmooth)

/-! ### Local solutions -/

section Local

variable [TopologicalSpace E]

/-- Thm. 5.15 of [Dempe 2002]: for a convex follower's problem, local solutions of (5.5) give
local solutions of the KKT reformulation (5.26) for every multiplier `λ̄ ∈ Λ(x̄, ȳ)`; the
neighborhood can be taken independent of `λ`. -/
theorem isLocalMinOn_kktFeasible_of_isLocalMinOn
    (hmin : IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀))
    (hconv : ∀ x ∈ Ω, IsConvexLower φ g x) (hdiff : ∀ x ∈ Ω, IsDifferentiableLower φ g x) :
    IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam₀) := by
  have h : ∀ᶠ q : (E × F) × (ι → ℝ) in 𝓝 ((x₀, y₀), lam₀),
      q.1 ∈ bilevelFeasible φ (lowerFeasible g) Ω → f (x₀, y₀) ≤ f q.1 :=
    (continuous_fst.tendsto ((x₀, y₀), lam₀)).eventually (eventually_nhdsWithin_iff.1 hmin)
  exact eventually_nhdsWithin_iff.2 (h.mono fun q hq hqK ↦
    hq (mem_bilevelFeasible_of_mem_kktFeasible hconv hdiff hqK))

/-- Thm. 5.15 of [Dempe 2002] for local optimistic solutions. -/
theorem IsLocalOptimisticSolution.isLocalMinOn_kktFeasible
    (h : IsLocalOptimisticSolution f φ (lowerFeasible g) Ω x₀ y₀)
    (hconv : ∀ x ∈ Ω, IsConvexLower φ g x) (hdiff : ∀ x ∈ Ω, IsDifferentiableLower φ g x) :
    IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam₀) :=
  isLocalMinOn_kktFeasible_of_isLocalMinOn h.isLocalMinOn hconv hdiff

end Local

/-! ### Examples -/

section Examples

theorem fderiv_apply_one_of_hasDerivAt {u : ℝ → ℝ} {u' t : ℝ} (h : HasDerivAt u u' t) :
    fderiv ℝ u t 1 = u' := by
  rw [fderiv_apply_one_eq_deriv, h.deriv]

/-- The follower's objective `y⁴ - x y³ + 0.28 x² y²` of the Example on p. 158 of
[Dempe 2002]. -/
private noncomputable def exφ : ℝ × ℝ → ℝ := fun p ↦ p.2 ^ 4 - p.1 * p.2 ^ 3 + 7 / 25 * p.1 ^ 2 * p.2 ^ 2

private def exg : Fin 0 → ℝ × ℝ → ℝ := fun i ↦ i.elim0

private theorem exφ_eq (x z : ℝ) :
    exφ (x, z) = z ^ 2 * ((z - x / 2) ^ 2 + 3 / 100 * x ^ 2) := by
  simp only [exφ]
  ring

private theorem exΨ (x y : ℝ) : y ∈ solutionMap exφ (lowerFeasible exg) x ↔ y = 0 := by
  constructor
  · rintro ⟨-, hmin⟩
    have h := hmin 0 fun i ↦ i.elim0
    rw [exφ_eq, exφ_eq] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h
    by_contra hy
    have h1 : 0 < y ^ 2 := by positivity
    have h2 : 0 ≤ (y - x / 2) ^ 2 + 3 / 100 * x ^ 2 := by positivity
    have h3 : (y - x / 2) ^ 2 + 3 / 100 * x ^ 2 = 0 := by nlinarith
    have hx : x = 0 := by nlinarith [sq_nonneg (y - x / 2), sq_nonneg x]
    subst hx
    exact hy (by nlinarith)
  · rintro rfl
    exact ⟨fun i ↦ i.elim0, fun z _ ↦ by rw [exφ_eq, exφ_eq]; simp only [ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity⟩

/-- Without convexity of the follower's problem, a global optimistic solution need not be a
local solution of the KKT reformulation (5.26) [Dempe 2002, Example on p. 158]: for
`min {-y | x ≥ 0, y ∈ Argmin_y {y⁴ - x y³ + 0.28 x² y²}}` the follower's unique solution is
`y = 0`, so `(0, 0)` is a global optimistic solution, but the stationary points `y = 2x/5`
give KKT-feasible points `(x, 2x/5)` with objective `-2x/5 < 0` arbitrarily close to `(0, 0)`. -/
theorem not_isLocalMinOn_kktFeasible_nonconvex_example (lam : Fin 0 → ℝ) :
    IsOptimisticSolution (fun p : ℝ × ℝ ↦ -p.2) exφ (lowerFeasible exg) (Ici 0) 0 0 ∧
      ¬ IsLocalMinOn (fun q : (ℝ × ℝ) × (Fin 0 → ℝ) ↦ -q.1.2) (kktFeasible exφ exg (Ici 0))
        ((0, 0), lam) := by
  constructor
  · refine isOptimisticSolution_iff.2 ⟨⟨mem_Ici.2 le_rfl, (exΨ 0 0).2 rfl⟩,
      isMinOn_iff.2 fun p hp ↦ ?_⟩
    rw [(exΨ p.1 p.2).1 hp.2]
  · intro hmin
    -- the KKT-feasible points `((t, 2t/5), λ)`, `t > 0`
    set q : ℝ → (ℝ × ℝ) × (Fin 0 → ℝ) := fun t ↦ ((t, 2 * t / 5), lam)
    have hq : ∀ t, 0 ≤ t → q t ∈ kktFeasible exφ exg (Ici 0) := fun t ht ↦ by
      refine ⟨ht, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hd : HasDerivAt (fun z : ℝ ↦ z ^ 4 - t * z ^ 3 + 7 / 25 * t ^ 2 * z ^ 2)
          (4 * (2 * t / 5) ^ 3 - t * (3 * (2 * t / 5) ^ 2) + 7 / 25 * t ^ 2 * (2 * (2 * t / 5)))
          (2 * t / 5) :=
        (((hasDerivAt_pow 4 (2 * t / 5)).sub ((hasDerivAt_pow 3 (2 * t / 5)).const_mul
          t)).add ((hasDerivAt_pow 2 (2 * t / 5)).const_mul (7 / 25 * t ^ 2))).congr_deriv
          (by norm_num)
      refine ContinuousLinearMap.ext_ring ?_
      rw [show (fun z ↦ exφ ((q t).1.1, z)) =
        fun z : ℝ ↦ z ^ 4 - t * z ^ 3 + 7 / 25 * t ^ 2 * z ^ 2 from rfl,
        fderiv_apply_one_of_hasDerivAt hd, zero_apply]
      ring
    have htend : Tendsto q (𝓝[>] 0) (𝓝[kktFeasible exφ exg (Ici 0)] ((0, 0), lam)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦
        hq t (le_of_lt ht)⟩
      have hc : Continuous q := by fun_prop
      have := hc.tendsto 0
      simp only [q, mul_zero, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := ((htend.eventually hmin).and self_mem_nhdsWithin).exists
    simp only [q, neg_zero] at ht
    exact absurd ht (not_le.2 (by linarith [show (0 : ℝ) < t from ht0]))

/-- The constraint `y² ≤ 0` of the Example in [Dempe–Dutta 2012] (see [Schmidt 2024,
pp. 180–187]); Slater's condition fails for every `x`. -/
private def exg' : Unit → ℝ × ℝ → ℝ := fun _ p ↦ p.2 ^ 2

private def exφ' : ℝ × ℝ → ℝ := fun p ↦ p.1 ^ 2 * p.2

theorem not_slaterAt_noSlater_example (x : ℝ) : ¬ SlaterAt exg' x := by
  rintro ⟨z, hz⟩
  have := hz ()
  simp only [exg'] at this
  nlinarith [sq_nonneg z]

private theorem mem_kktFeasible_noSlater {q : (ℝ × ℝ) × (Unit → ℝ)}
    (hq : q ∈ kktFeasible exφ' exg' univ) : q.1 = (0, 0) := by
  obtain ⟨-, hfeas, -, -, hstat⟩ := hq
  have hy : q.1.2 = 0 := by
    have := hfeas ()
    simp only [exg'] at this
    nlinarith [sq_nonneg q.1.2]
  have h1 := congrArg (fun T : ℝ →L[ℝ] ℝ ↦ T 1) hstat
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply,
    Finset.univ_unique, Finset.sum_singleton] at h1
  rw [show (fun z ↦ exφ' (q.1.1, z)) = fun z ↦ q.1.1 ^ 2 * z from rfl,
    fderiv_apply_one_of_hasDerivAt ((hasDerivAt_id' q.1.2).const_mul (q.1.1 ^ 2)),
    show (fun z ↦ exg' default (q.1.1, z)) = fun z : ℝ ↦ z ^ 2 from rfl,
    fderiv_apply_one_of_hasDerivAt (hasDerivAt_pow 2 q.1.2), hy] at h1
  norm_num at h1
  exact Prod.ext h1 hy

/-- Without Slater's condition, global solutions of the KKT reformulation need not solve the
bilevel problem [Dempe–Dutta 2012; Schmidt 2024, pp. 180–187]: for
`min {(x - 1)² + y² | y ∈ Argmin_y {x² y | y² ≤ 0}}` every `((0, 0), λ)` with `λ ≥ 0` is a global
solution of (5.26). -/
theorem isMinOn_kktFeasible_noSlater_example (lam : Unit → ℝ) (hlam : 0 ≤ lam ()) :
    ((0, 0), lam) ∈ kktFeasible exφ' exg' univ ∧
      IsMinOn (fun q : (ℝ × ℝ) × (Unit → ℝ) ↦ (q.1.1 - 1) ^ 2 + q.1.2 ^ 2)
        (kktFeasible exφ' exg' univ) ((0, 0), lam) := by
  refine ⟨⟨mem_univ _, fun _ ↦ by simp [exg'], fun _ ↦ hlam, fun _ ↦ by simp [exg'], ?_⟩,
    isMinOn_iff.2 fun q hq ↦ by rw [mem_kktFeasible_noSlater hq]⟩
  refine ContinuousLinearMap.ext_ring ?_
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, Finset.univ_unique,
    Finset.sum_singleton]
  rw [show (fun z ↦ exφ' ((0 : ℝ), z)) = fun z ↦ (0 : ℝ) ^ 2 * z from rfl,
    fderiv_apply_one_of_hasDerivAt ((hasDerivAt_id' (0 : ℝ)).const_mul ((0 : ℝ) ^ 2)),
    show (fun z ↦ exg' default ((0 : ℝ), z)) = fun z : ℝ ↦ z ^ 2 from rfl,
    fderiv_apply_one_of_hasDerivAt (hasDerivAt_pow 2 (0 : ℝ))]
  norm_num

/-- In the example of `isMinOn_kktFeasible_noSlater_example`, `(0, 0)` is not a global solution
of (5.5): the follower's unique solution is `y = 0` for every `x`, and `(1, 0)` has objective
value `0 < 1`. -/
theorem not_isMinOn_bilevelFeasible_noSlater_example :
    ¬ IsMinOn (fun p : ℝ × ℝ ↦ (p.1 - 1) ^ 2 + p.2 ^ 2)
      (bilevelFeasible exφ' (lowerFeasible exg') univ) (0, 0) := by
  intro h
  have hmem : ((1 : ℝ), (0 : ℝ)) ∈ bilevelFeasible exφ' (lowerFeasible exg') univ := by
    refine ⟨mem_univ _, fun _ ↦ by simp [exg'], fun z hz ↦ ?_⟩
    have := hz ()
    simp only [exg'] at this
    have hz0 : z = 0 := by nlinarith [sq_nonneg z]
    simp [exφ', hz0]
  have := isMinOn_iff.1 h _ hmem
  norm_num at this

end Examples

end Bilevel
