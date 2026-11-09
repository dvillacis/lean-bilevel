/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Parametric
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Local solutions of the KKT reformulation

The converse of Thm. 5.15 of [Dempe 2002] (`isLocalMinOn_kktFeasible_of_isLocalMinOn`), following
[Dempe–Dutta 2012, Thm. 3.1]: if `((x̄, ȳ), λ)` is a local solution of the KKT reformulation (5.26)
for *every* multiplier `λ ∈ Λ(x̄, ȳ)`, then `(x̄, ȳ)` is a local solution of (5.5). One multiplier
is not enough, so local solutions of (5.26) need not be local solutions of the bilevel problem
[Schmidt 2024, p. 188]. Under (CRCQ) it suffices to check the finitely many vertices of
`Λ(x̄, ȳ)` [Dempe–Dutta 2012, Cor. 3.3].

## Main results

* `isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible`: for `C¹` data with (MFCQ)
  at `(x̄, ȳ)`, local optimality in (5.26) for all `λ ∈ Λ(x̄, ȳ)` gives local optimality in (5.5).
  No convexity is needed.
* `isLocalMinOn_bilevelFeasible_iff_forall_isLocalMinOn_kktFeasible`: [Dempe–Dutta 2012,
  Thm. 3.1]: for a convex follower's problem with `C¹` data and Slater's condition at `x̄`,
  `(x̄, ȳ)` is a local solution of (5.5) iff `((x̄, ȳ), λ)` is a local solution of (5.26) for every
  `λ ∈ Λ(x̄, ȳ)`.
* `LowerCRCQ`: the constant rank constraint qualification for the follower's problem
  [Dempe 2002, p. 77].
* `mem_extremePoints_lowerMultipliers_iff`, `finite_extremePoints_lowerMultipliers`: the vertices
  of `Λ(x, y)` are the multipliers with linearly independent support gradients; there are finitely
  many.
* `upperHemicontinuousAt_extremePoints_lowerMultipliers`: under (MFCQ) and (CRCQ), limits of
  vertices of `Λ(x, y)` are vertices of `Λ(x̄, ȳ)`.
* `isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_isLocalMinOn_kktFeasible`,
  `isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_of_slaterAt`: [Dempe–Dutta 2012,
  Cor. 3.3]: under (CRCQ), local optimality in (5.26) at the vertices of `Λ(x̄, ȳ)` suffices.
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
* Both converses are instances of `isLocalMinOn_bilevelFeasible_of_selection` (tube lemma for a
  compact, upper semicontinuous selection of multipliers). For Cor. 3.3 the selection is the vertex
  map: its values are finite, every nonempty `Λ(x, y)` has a vertex (Krein–Milman,
  `IsCompact.extremePoints_nonempty`), and (CRCQ) makes it upper semicontinuous. Cor. 3.3 needs
  convexity only at `x̄` (to get (MFCQ) from Slater's condition).
* The statement of [Dempe–Dutta 2012, Thm. 3.1, Cor. 3.3] is taken from the Notability note
  *Solving Methods for Bilevel Optimization Problems* (pp. 26, 30); the paper itself is not in the
  library.
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

omit [NormedSpace ℝ E] in
/-- The common core of the local converses: if `M(x, y) ⊆ ℝ^ι` is upper semicontinuous at
`(x̄, ȳ)` with compact value `M(x̄, ȳ)`, every bilevel-feasible point near `(x̄, ȳ)` has a KKT
multiplier in `M`, and `((x̄, ȳ), λ)` is a local solution of (5.26) for every `λ ∈ M(x̄, ȳ)`, then
`(x̄, ȳ)` is a local solution of (5.5). The proof is the tube lemma for `M(x̄, ȳ)`. -/
theorem isLocalMinOn_bilevelFeasible_of_selection {M : E × F → Set (ι → ℝ)}
    (hMc : IsCompact (M (x₀, y₀))) (husc : UpperHemicontinuousAt M (x₀, y₀))
    (hsel : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), p ∈ bilevelFeasible φ (lowerFeasible g) Ω →
      ∃ lam ∈ M p, IsLowerKKT φ g p.1 p.2 lam)
    (hloc : ∀ lam ∈ M (x₀, y₀),
      IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam)) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) := by
  -- one neighborhood of `(x̄, ȳ)` works for a whole neighborhood of the compact `M(x̄, ȳ)`
  have hS : {q : (E × F) × (ι → ℝ) | q ∈ kktFeasible φ g Ω → f (x₀, y₀) ≤ f q.1} ∈
      𝓝 (x₀, y₀) ×ˢ 𝓝ˢ (M (x₀, y₀)) :=
    hMc.mem_prod_nhdsSet_of_forall fun lam hlam ↦ by
      rw [← nhds_prod_eq]
      exact eventually_nhdsWithin_iff.1 (hloc lam hlam)
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_prod_iff.1 hS
  obtain ⟨V, hV, hMV, hVt⟩ := mem_nhdsSet_iff_exists.1 ht₂
  refine eventually_nhdsWithin_iff.2 ?_
  filter_upwards [ht₁, husc V hV hMV, hsel] with p hp₁ hpV hp hpB
  obtain ⟨lam, hlamM, hlam⟩ := hp hpB
  exact hsub (mk_mem_prod hp₁ (hVt (hpV hlamM))) ⟨hpB.1, hlam⟩

/-- Near a point with (MFCQ) and `C¹` data, every bilevel-feasible point satisfies (MFCQ) and has
KKT multipliers. -/
theorem eventually_lowerPLI_and_nonempty_lowerMultipliers [FiniteDimensional ℝ F]
    (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀) :
    ∀ᶠ p : E × F in 𝓝 (x₀, y₀), p ∈ bilevelFeasible φ (lowerFeasible g) Ω →
      LowerPLI g p.1 p.2 ∧ (lowerMultipliers φ g p.1 p.2).Nonempty := by
  filter_upwards [eventually_lowerPLI hg hreg] with p hpreg hpB
  exact ⟨hpreg, exists_isLowerKKT_of_mem_solutionMap hpB.2
    ((hφ.comp (contDiff_prodMk_right p.1)).differentiable one_ne_zero p.2)
    (fun i ↦ ((hg i).comp (contDiff_prodMk_right p.1)).contDiffAt) hpreg⟩

/-- The converse of Thm. 5.15 of [Dempe 2002] [Dempe–Dutta 2012, Thm. 3.1]: for `C¹` data with
(MFCQ) at `(x̄, ȳ)` (in its dual form), if `((x̄, ȳ), λ)` is a local solution of the KKT
reformulation (5.26) for every `λ ∈ Λ(x̄, ȳ)`, then `(x̄, ȳ)` is a local solution of (5.5). -/
theorem isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible [FiniteDimensional ℝ F]
    (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀)
    (hloc : ∀ lam ∈ lowerMultipliers φ g x₀ y₀,
      IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam)) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) :=
  isLocalMinOn_bilevelFeasible_of_selection (M := fun p : E × F ↦ lowerMultipliers φ g p.1 p.2)
    (isCompact_lowerMultipliers hreg)
    (upperHemicontinuousAt_lowerMultipliers hφ hg hreg)
    ((eventually_lowerPLI_and_nonempty_lowerMultipliers (Ω := Ω) hφ hg hreg).mono fun _ hp hpB ↦
      let ⟨lam, hlam⟩ := (hp hpB).2
      ⟨lam, hlam, hlam⟩) hloc

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

/-! ### Vertices of the multiplier set: [Dempe–Dutta 2012, Cor. 3.3] -/

section Vertices

variable {x : E} {y : F} {lam mu : ι → ℝ}

/-- The constant rank constraint qualification (CRCQ) for the follower's problem at `(x, y)`
[Dempe 2002, p. 77]: for every set `J` of active constraints, the rank of the gradients
`∇_y gᵢ(x', y')`, `i ∈ J`, is constant for `(x', y')` near `(x, y)`. -/
def LowerCRCQ (g : ι → E × F → ℝ) (x : E) (y : F) : Prop :=
  ∀ J : Set ι, (∀ i ∈ J, g i (x, y) = 0) → ∀ᶠ p : E × F in 𝓝 (x, y),
    Module.finrank ℝ (Submodule.span ℝ
        (range fun i : J ↦ fderiv ℝ (fun z ↦ g i.1 (p.1, z)) p.2)) =
      Module.finrank ℝ (Submodule.span ℝ (range fun i : J ↦ fderiv ℝ (fun z ↦ g i.1 (x, z)) y))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A multiplier whose support gradients are linearly independent is determined by its support:
every multiplier supported in its support equals it. -/
theorem eq_of_mem_lowerMultipliers_of_linearIndependent (hlam : lam ∈ lowerMultipliers φ g x y)
    (hmu : mu ∈ lowerMultipliers φ g x y)
    (hind : LinearIndependent ℝ fun i : {i // 0 < lam i} ↦ fderiv ℝ (fun z ↦ g i.1 (x, z)) y)
    (hsupp : ∀ i, lam i = 0 → mu i = 0) : mu = lam := by
  classical
  have hsum : ∑ i, (mu i - lam i) • fderiv ℝ (fun z ↦ g i (x, z)) y = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [eq_neg_of_add_eq_zero_right hmu.2.2.2, eq_neg_of_add_eq_zero_right hlam.2.2.2, sub_self]
  have hzero : ∀ i, ¬ 0 < lam i → mu i - lam i = 0 := fun i hi ↦ by
    have h0 : lam i = 0 := le_antisymm (not_lt.1 hi) (hlam.2.1 i)
    rw [h0, hsupp i h0, sub_zero]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i ↦ 0 < lam i)
    fun i ↦ (mu i - lam i) • fderiv ℝ (fun z ↦ g i (x, z)) y
  have hrest : ∑ i : {i // ¬ 0 < lam i}, (mu i.1 - lam i.1) • fderiv ℝ (fun z ↦ g i.1 (x, z)) y
      = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hzero i.1 i.2, zero_smul]
  rw [hrest, add_zero, hsum] at hsplit
  have hc := Fintype.linearIndependent_iff.1 hind (fun i ↦ mu i.1 - lam i.1) hsplit
  funext i
  by_cases hi : 0 < lam i
  · exact (sub_eq_zero.1 (hc ⟨i, hi⟩))
  · exact (sub_eq_zero.1 (hzero i hi))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The vertices (extreme points) of the multiplier set `Λ(x, y)` are the multipliers whose
support gradients `∇_y gᵢ(x, y)`, `λᵢ > 0`, are linearly independent. -/
theorem mem_extremePoints_lowerMultipliers_iff :
    lam ∈ (lowerMultipliers φ g x y).extremePoints ℝ ↔ lam ∈ lowerMultipliers φ g x y ∧
      LinearIndependent ℝ fun i : {i // 0 < lam i} ↦ fderiv ℝ (fun z ↦ g i.1 (x, z)) y := by
  classical
  constructor
  · intro hext
    have hlam : lam ∈ lowerMultipliers φ g x y := hext.1
    refine ⟨hlam, Fintype.linearIndependent_iff.2 fun c hc i ↦ ?_⟩
    by_contra hci
    -- a nonzero dependence `c` on the support gives a segment through `λ` inside `Λ(x, y)`
    obtain ⟨d, hdp, hdn⟩ : ∃ d : ι → ℝ, (∀ j (h : 0 < lam j), d j = c ⟨j, h⟩) ∧
        ∀ j, ¬ 0 < lam j → d j = 0 :=
      ⟨fun j ↦ if h : 0 < lam j then c ⟨j, h⟩ else 0, fun _ h ↦ dif_pos h, fun _ h ↦ dif_neg h⟩
    have hdsum : ∑ j, d j • fderiv ℝ (fun z ↦ g j (x, z)) y = 0 := by
      have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j ↦ 0 < lam j)
        fun j ↦ d j • fderiv ℝ (fun z ↦ g j (x, z)) y
      have h1 : ∑ j : {j // 0 < lam j}, d j.1 • fderiv ℝ (fun z ↦ g j.1 (x, z)) y = 0 := by
        rw [← hc]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hdp j.1 j.2]
      have h2 : ∑ j : {j // ¬ 0 < lam j}, d j.1 • fderiv ℝ (fun z ↦ g j.1 (x, z)) y = 0 :=
        Finset.sum_eq_zero fun j _ ↦ by rw [hdn j.1 j.2, zero_smul]
      rw [← hsplit, h1, h2, add_zero]
    have hdg : ∀ j, d j * g j (x, y) = 0 := fun j ↦ by
      by_cases h : 0 < lam j
      · rw [(mul_eq_zero.1 (hlam.2.2.1 j)).resolve_left h.ne', mul_zero]
      · rw [hdn j h, zero_mul]
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, 0 ≤ lam j + t * d j ∧ 0 ≤ lam j - t * d j :=
      eventually_all.2 fun j ↦ by
        by_cases h : 0 < lam j
        · have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < lam j + t * d j :=
            continuousAt_const.eventually_lt
              (show Continuous fun t : ℝ ↦ lam j + t * d j by fun_prop).continuousAt
              (by simpa using h)
          have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < lam j - t * d j :=
            continuousAt_const.eventually_lt
              (show Continuous fun t : ℝ ↦ lam j - t * d j by fun_prop).continuousAt
              (by simpa using h)
          exact (h1.and h2).mono fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩
        · exact Eventually.of_forall fun t ↦ by
            rw [hdn j h, mul_zero, add_zero, sub_zero]
            exact ⟨hlam.2.1 j, hlam.2.1 j⟩
    obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have hmem : ∀ s : ℝ, (∀ j, 0 ≤ lam j + s * d j) →
        lam + s • d ∈ lowerMultipliers φ g x y := fun s hs ↦ by
      refine ⟨hlam.1, fun j ↦ hs j, fun j ↦ ?_, ?_⟩
      · show (lam j + s * d j) * g j (x, y) = 0
        rw [add_mul, hlam.2.2.1 j, mul_assoc, hdg j, mul_zero, zero_add]
      · show fderiv ℝ (fun z ↦ φ (x, z)) y +
          ∑ j, (lam j + s * d j) • fderiv ℝ (fun z ↦ g j (x, z)) y = 0
        simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hdsum,
          smul_zero, add_zero]
        exact hlam.2.2.2
    have h₁ := hmem t fun j ↦ (ht j).1
    have h₂ := hmem (-t) fun j ↦ by rw [neg_mul, ← sub_eq_add_neg]; exact (ht j).2
    have hseg : lam ∈ openSegment ℝ (lam + t • d) (lam + (-t) • d) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring⟩
    have heq := (mem_extremePoints_iff_left.1 hext).2 _ h₁ _ h₂ hseg
    have htd : t * d i.1 = 0 := by
      have := congrFun heq i.1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    rw [hdp i.1 i.2] at htd
    exact hci ((mul_eq_zero.1 htd).resolve_left (ne_of_gt ht0))
  · rintro ⟨hlam, hind⟩
    refine mem_extremePoints_iff_left.2 ⟨hlam, fun x₁ h₁ x₂ h₂ hseg ↦ ?_⟩
    obtain ⟨a, b, ha, hb, -, hx⟩ := hseg
    refine eq_of_mem_lowerMultipliers_of_linearIndependent hlam h₁ hind fun i hi ↦ ?_
    have h := congrFun hx i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hi] at h
    have h1 := mul_nonneg ha.le (h₁.2.1 i)
    have h2 := mul_nonneg hb.le (h₂.2.1 i)
    exact (mul_eq_zero.1 (by linarith : a * x₁ i = 0)).resolve_left ha.ne'

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The multiplier set has finitely many vertices: a vertex is determined by its support. -/
theorem finite_extremePoints_lowerMultipliers :
    ((lowerMultipliers φ g x y).extremePoints ℝ).Finite := by
  refine Set.Finite.of_finite_image (f := fun lam : ι → ℝ ↦ {i | 0 < lam i}) (Set.toFinite _) ?_
  intro lam hlam mu hmu h
  beta_reduce at h
  have hl := mem_extremePoints_lowerMultipliers_iff.1 hlam
  refine (eq_of_mem_lowerMultipliers_of_linearIndependent hl.1 hmu.1 hl.2 fun i hi ↦ ?_).symm
  have hnot : ¬ 0 < mu i := fun hm ↦ by
    have hl : 0 < lam i := (Set.ext_iff.1 h i).2 hm
    rw [hi] at hl
    exact lt_irrefl 0 hl
  exact le_antisymm (not_lt.1 hnot) (hmu.1.2.1 i)

/-- Under (CRCQ) and (MFCQ) at `(x̄, ȳ)`, for `C¹` data, the vertex map `(x, y) ↦ ext Λ(x, y)`
is upper semicontinuous at `(x̄, ȳ)`: limits of vertices of `Λ(x, y)` are vertices of
`Λ(x̄, ȳ)` [Dempe–Dutta 2012, proof of Cor. 3.3]. -/
theorem upperHemicontinuousAt_extremePoints_lowerMultipliers (hφ : ContDiff ℝ 1 φ)
    (hg : ∀ i, ContDiff ℝ 1 (g i)) (hreg : LowerPLI g x₀ y₀) (hcrcq : LowerCRCQ g x₀ y₀) :
    UpperHemicontinuousAt (fun p : E × F ↦ (lowerMultipliers φ g p.1 p.2).extremePoints ℝ)
      (x₀, y₀) := by
  classical
  refine upperHemicontinuousAt_of_mem_closure_graph (fun lam hcl ↦ ?_) ?_
  · have hΛ : lam ∈ lowerMultipliers φ g x₀ y₀ := by
      have h := closure_mono (show VariationalAnalysis.graph (fun p : E × F ↦
          (lowerMultipliers φ g p.1 p.2).extremePoints ℝ) ⊆
          VariationalAnalysis.graph (fun p : E × F ↦ lowerMultipliers φ g p.1 p.2) from
        fun q (hq : q.2 ∈ (lowerMultipliers φ g q.1.1 q.1.2).extremePoints ℝ) ↦
          (extremePoints_subset hq : q.2 ∈ lowerMultipliers φ g q.1.1 q.1.2)) hcl
      rwa [(isClosed_graph_lowerMultipliers hφ hg).closure_eq] at h
    refine mem_extremePoints_lowerMultipliers_iff.2 ⟨hΛ, ?_⟩
    have hact : ∀ i ∈ {i | 0 < lam i}, g i (x₀, y₀) = 0 := fun i hi ↦
      (mul_eq_zero.1 (hΛ.2.2.1 i)).resolve_left (ne_of_gt hi)
    have hpos : ∀ᶠ mu : ι → ℝ in 𝓝 lam, ∀ i ∈ {i | 0 < lam i}, 0 < mu i :=
      eventually_all.2 fun i ↦ by
        by_cases h : 0 < lam i
        · exact (continuousAt_const.eventually_lt (continuous_apply i).continuousAt h).mono
            fun _ h' _ ↦ h'
        · exact Eventually.of_forall fun _ hi ↦ absurd hi h
    -- a vertex `μ` of `Λ(x, y)` near `((x̄, ȳ), λ)` has support containing that of `λ`
    have hN := ((continuous_fst.tendsto ((x₀, y₀), lam)).eventually
      (hcrcq {i | 0 < lam i} hact)).and ((continuous_snd.tendsto ((x₀, y₀), lam)).eventually hpos)
    obtain ⟨q, ⟨hq1, hq2⟩, hqG⟩ := mem_closure_iff_nhds.1 hcl _ hN
    have hqG' : q.2 ∈ (lowerMultipliers φ g q.1.1 q.1.2).extremePoints ℝ := hqG
    have hqind := (mem_extremePoints_lowerMultipliers_iff.1 hqG').2
    have hindq : LinearIndependent ℝ
        fun i : {i | 0 < lam i} ↦ fderiv ℝ (fun z ↦ g i.1 (q.1.1, z)) q.1.2 :=
      hqind.comp (fun i : {i | 0 < lam i} ↦ (⟨i.1, hq2 i.1 i.2⟩ : {i // 0 < q.2 i}))
        fun a b h ↦ by
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext h
    -- (CRCQ) carries the independence to `(x̄, ȳ)`
    have hind : LinearIndependent ℝ
        fun i : {i | 0 < lam i} ↦ fderiv ℝ (fun z ↦ g i.1 (x₀, z)) y₀ :=
      linearIndependent_iff_card_eq_finrank_span.2 (by
        rw [Set.finrank, ← hq1, finrank_span_eq_card hindq])
    exact hind
  · obtain ⟨R, hR⟩ := exists_eventually_lowerMultipliers_subset hφ hg hreg
    exact ⟨_, hR, _, isCompact_closedBall 0 R, fun _ hp ↦ extremePoints_subset.trans hp⟩

/-- [Dempe–Dutta 2012, Cor. 3.3], general form: for `C¹` data with (MFCQ) and (CRCQ) at
`(x̄, ȳ)`, if `((x̄, ȳ), λ)` is a local solution of the KKT reformulation (5.26) for every vertex
`λ` of `Λ(x̄, ȳ)` (finitely many, `finite_extremePoints_lowerMultipliers`), then `(x̄, ȳ)` is a
local solution of (5.5). -/
theorem isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_isLocalMinOn_kktFeasible
    [FiniteDimensional ℝ F] (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hreg : LowerPLI g x₀ y₀) (hcrcq : LowerCRCQ g x₀ y₀)
    (hloc : ∀ lam ∈ (lowerMultipliers φ g x₀ y₀).extremePoints ℝ,
      IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam)) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) := by
  refine isLocalMinOn_bilevelFeasible_of_selection
    finite_extremePoints_lowerMultipliers.isCompact
    (upperHemicontinuousAt_extremePoints_lowerMultipliers hφ hg hreg hcrcq)
    ((eventually_lowerPLI_and_nonempty_lowerMultipliers (Ω := Ω) hφ hg hreg).mono
      fun p hp hpB ↦ ?_) hloc
  obtain ⟨hpreg, hne⟩ := hp hpB
  -- the compact convex set `Λ(x, y)` has a vertex (Krein–Milman)
  obtain ⟨lam, hlam⟩ := (isCompact_lowerMultipliers (φ := φ) hpreg).extremePoints_nonempty hne
  exact ⟨lam, hlam, hlam.1⟩

/-- [Dempe–Dutta 2012, Cor. 3.3]: for a follower's problem with `C¹` data, convex at `x̄`, with
Slater's condition and (CRCQ) at `x̄`, if `((x̄, ȳ), λ)` is a local solution of (5.26) for every
vertex `λ` of `Λ(x̄, ȳ)`, then `(x̄, ȳ)` is a local solution of (5.5). -/
theorem isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_of_slaterAt
    [FiniteDimensional ℝ F] (hφ : ContDiff ℝ 1 φ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hmem : (x₀, y₀) ∈ bilevelFeasible φ (lowerFeasible g) Ω) (hconv : IsConvexLower φ g x₀)
    (hS : SlaterAt g x₀) (hcrcq : LowerCRCQ g x₀ y₀)
    (hloc : ∀ lam ∈ (lowerMultipliers φ g x₀ y₀).extremePoints ℝ,
      IsLocalMinOn (fun q ↦ f q.1) (kktFeasible φ g Ω) ((x₀, y₀), lam)) :
    IsLocalMinOn f (bilevelFeasible φ (lowerFeasible g) Ω) (x₀, y₀) :=
  isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_isLocalMinOn_kktFeasible hφ hg
    (lowerPLI_of_slaterAt hconv.2
      (fun i ↦ ((hg i).comp (contDiff_prodMk_right x₀)).differentiable one_ne_zero y₀)
      hmem.2.1 hS) hcrcq hloc

end Vertices

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
