/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.GeneralizedJacobian

/-!
# Computing elements of the generalized Jacobian of the local solution function

Sect. 4.4.2 of [Dempe 2002] in the (LICQ) case, where `Λ(x̄, ȳ) = {λ⁰}`. For an admissible index
set `J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)`, let `R(I, λ⁰)` be the set of directions `r` for which the system
`KKT(r, I, λ⁰)` has a solution (p. 94). If `r` lies in the interior of `R(I, λ⁰)`, then the
Jacobian `∇y^I(x̄)` of the local solution function of (4.19) belongs to the generalized Jacobian
`∂y(x̄)` (Thm. 4.13); this applies under strict complementarity in `QP(λ⁰, r)` (Thm. 4.12, (SCR)),
and under the full rank condition (FRR) every admissible `I` qualifies, so that
`∂y(x̄) = conv {∇y^I(x̄) : I admissible}` (Thm. 4.12, (FRR)).

## Main results

* `fderiv_lowerKKTMap_eq_zero_iff`, `fderiv_lowerKKTMap_fderiv_lowerSelection`,
  `eq_fderiv_lowerSelection`: `(∇y^I(x̄) r, ∇λ^I(x̄) r)` is the unique solution of the equations
  of `KKT(r, I, λ⁰)`.
* `lowerQPRegion`: the sets `R(I, λ⁰)`.
* `hasDirDerivAt_eq_of_mem_interior_lowerQPRegion`: Cor. 4.2, `y'(x̄; r) = ∇y^I(x̄) r` on
  `int R(I, λ⁰)`.
* `exists_stronglyActive_fderiv_eq_of_mem_interior_lowerQPRegion`: Thm. 4.13.
* `LowerSCR`, `mem_interior_lowerQPRegion_of_lowerSCR`, `fderiv_mem_clarkeJacobian_of_lowerSCR`:
  Thm. 4.12, first assertion.
* `LowerFRR`, `exists_lowerSCR_of_lowerFRR`, `clarkeJacobian_eq_of_lowerFRR`: Thm. 4.12, second
  assertion.

## Differences from the book

* The book assumes (MFCQ), (SSOC), (CRCQ) and ranges over the vertices of `Λ(x̄, ȳ)`; we assume
  (LICQ), so that the only vertex is `λ⁰`, `S(r) = {λ⁰}`, (C2) is automatic, and Lemma 4.1 is not
  needed. The book gives no proofs (it cites [71, 73, 78]).
* (SCR) for `I` and `r` is formalized as: `KKT(r, I, λ⁰)` has a solution with `γᵢ > 0` for
  `i ∈ I \ J(λ⁰)` and `∇gᵢ(x̄, ȳ)(r, d) < 0` for active `i ∉ I`, i.e. `I` is the active set of
  `QP(λ⁰, r)` and strict complementarity holds there.
* (FRR) is formalized as surjectivity of the linear map
  `(d, γ_{J(λ⁰)}, r) ↦ (∇²_yy L d + ∇_y g_{J(λ⁰)}ᵀ γ + ∇²_yx L r, ∇g_{I(x̄,ȳ)}(x̄, ȳ)(r, d))`, i.e.
  full row rank of the matrix `M` on p. 91.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι] [DecidableEq ι] {φ : E × F → ℝ} {g : ι → E × F → ℝ}

/-- The linearized KKT map vanishes exactly on the solutions of the equations of
`KKT(r, I, λ⁰)`. -/
theorem fderiv_lowerKKTMap_eq_zero_iff (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (I : Finset ι) (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (r : E)
    (d : F) (γ : ι → ℝ) :
    fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀)) (r, (d, γ)) = 0 ↔
      lowerMixedHessian φ g x₀ y₀ lam₀ r + lowerHessian φ g x₀ y₀ lam₀ d +
          ∑ i, γ i • fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = 0 ∧
        (∀ i ∈ I, fderiv ℝ (g i) (x₀, y₀) (r, d) = 0) ∧ (∀ i ∉ I, γ i = 0) := by
  simp only [fderiv_lowerKKTMap_apply hφ hg, fderiv_lowerLagrangianDeriv_apply_eq,
    Prod.mk_eq_zero, funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi ↦ by simpa [hi] using h2 i, fun i hi ↦ by simpa [hi] using h2 i⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i ↦ by by_cases hi : i ∈ I <;> simp [hi, h2, h3]⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The derivative `(∇y^I(x̄) r, ∇λ^I(x̄) r)` of the selection of an admissible index set solves the
linearized KKT system of (4.19). -/
theorem fderiv_lowerKKTMap_fderiv_lowerSelection (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) (r : E) :
    fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀))
      (r, fderiv ℝ (lowerSelection φ g x₀ y₀ lam₀ I) x₀ r) = 0 := by
  have hinv := isInvertible_fderiv_lowerKKTMap hφ hg hkkt hlicq hssoc hI.1 hI.2
  have hcd := (contDiff_lowerKKTMap hφ hg I).contDiffAt (x := (x₀, (y₀, lam₀)))
  have hsel : lowerSelection φ g x₀ y₀ lam₀ I = hcd.implicitFunction one_ne_zero hinv := by
    unfold lowerSelection
    rw [dif_pos ⟨hcd, hinv⟩]
  have hev := hcd.eventually_apply_implicitFunction one_ne_zero hinv
  rw [← hsel] at hev
  have hdsel : HasFDerivAt (lowerSelection φ g x₀ y₀ lam₀ I)
      (fderiv ℝ (lowerSelection φ g x₀ y₀ lam₀ I) x₀) x₀ :=
    ((contDiffAt_lowerSelection x₀ y₀ lam₀ I).differentiableAt one_ne_zero).hasFDerivAt
  have hK : HasFDerivAt (lowerKKTMap φ g I) (fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀)))
      (x₀, lowerSelection φ g x₀ y₀ lam₀ I x₀) := by
    rw [lowerSelection_apply_self]
    exact (hcd.differentiableAt one_ne_zero).hasFDerivAt
  have hcomp := hK.comp x₀ ((hasFDerivAt_id x₀).prodMk hdsel)
  have hconst : HasFDerivAt (fun x ↦ lowerKKTMap φ g I (x, lowerSelection φ g x₀ y₀ lam₀ I x))
      (0 : E →L[ℝ] StrongDual ℝ F × (ι → ℝ)) x₀ :=
    (hasFDerivAt_const (lowerKKTMap φ g I (x₀, (y₀, lam₀))) x₀).congr_of_eventuallyEq hev
  have h := congrArg (fun T : E →L[ℝ] StrongDual ℝ F × (ι → ℝ) ↦ T r) (hcomp.unique hconst)
  simpa using h

/-- The equations of `KKT(r, I, λ⁰)` determine `(d, γ) = (∇y^I(x̄) r, ∇λ^I(x̄) r)`. -/
theorem eq_fderiv_lowerSelection (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E}
    {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r : E}
    {d : F} {γ : ι → ℝ} (h : fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀)) (r, (d, γ)) = 0) :
    (d, γ) = fderiv ℝ (lowerSelection φ g x₀ y₀ lam₀ I) x₀ r := by
  obtain ⟨e, he⟩ := isInvertible_fderiv_lowerKKTMap hφ hg hkkt hlicq hssoc hI.1 hI.2
  set T := fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀))
  have hinj : Function.Injective (T ∘L ContinuousLinearMap.inr ℝ E (F × (ι → ℝ))) := by
    rw [← he]
    exact e.injective
  have h0 := fderiv_lowerKKTMap_fderiv_lowerSelection hφ hg hkkt hlicq hssoc hI r
  have key : ∀ v : F × (ι → ℝ), T (0, v) = T (r, v) - T (r, 0) := fun v ↦ by
    rw [← map_sub]
    simp
  apply hinj
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
  rw [key, key, h, h0]

variable (φ g) in
/-- The set `R(I, λ⁰)` of [Dempe 2002, p. 94]: the directions `r` for which `KKT(r, I, λ⁰)` has a
solution. -/
def lowerQPRegion (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (I : Finset ι) : Set E :=
  {r | ∃ d γ, LowerQPSystem φ g x₀ y₀ lam₀ I r d γ}

/-- On `R(I, λ⁰)`, the solution `d` of `KKT(r, I, λ⁰)` is `∇y^I(x̄) r`. -/
theorem eq_fderiv_lowerSolutionSelection_of_lowerQPSystem (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r : E}
    {d : F} {γ : ι → ℝ} (hsys : LowerQPSystem φ g x₀ y₀ lam₀ I r d γ) :
    d = fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ r := by
  have hd := ((contDiffAt_lowerSelection (φ := φ) (g := g) x₀ y₀ lam₀ I).differentiableAt
    one_ne_zero).hasFDerivAt
  have hfst : fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ =
      (ContinuousLinearMap.fst ℝ F (ι → ℝ)).comp
        (fderiv ℝ (lowerSelection φ g x₀ y₀ lam₀ I) x₀) :=
    (hasFDerivAt_fst.comp x₀ hd).fderiv
  have h2 := eq_fderiv_lowerSelection hφ hg hkkt hlicq hssoc hI
    ((fderiv_lowerKKTMap_eq_zero_iff hφ hg I x₀ y₀ lam₀ r d γ).2
      ⟨hsys.1, hsys.2.1, hsys.2.2.2.2⟩)
  rw [hfst, ContinuousLinearMap.comp_apply, ← h2]
  rfl

section Solution

variable {s : E → F} {U : Set E}

/-- **Cor. 4.2 of [Dempe 2002]** under (LICQ): on the interior of `R(I, λ⁰)`, the directional
derivative of the local solution function is linear, `y'(x̄; r) = ∇y^I(x̄) r`. -/
theorem hasDirDerivAt_eq_of_mem_lowerQPRegion (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {s' : E → F} (hs' : HasDirDerivAt s s' x₀) {I : Finset ι}
    (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r : E} (hr : r ∈ lowerQPRegion φ g x₀ y₀ lam₀ I) :
    s' r = fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ r := by
  obtain ⟨s'', hs'', hqp⟩ := hasDirDerivAt_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  obtain ⟨d, γ, hsys⟩ := hr
  rw [tendsto_nhds_unique (hs' r) (hs'' r),
    ← eq_of_lowerQPSystem hφ hg hkkt hssoc hI.1 hI.2 hsys (hqp r)]
  exact eq_fderiv_lowerSolutionSelection_of_lowerQPSystem hφ hg hkkt hlicq hssoc hI hsys

/-- **Thm. 4.13 of [Dempe 2002]** under (LICQ): if `r ∈ int R(I, λ⁰)` for an admissible `I`, then
there is a strongly active selection function `y^Î(·)` with `∇y^I(x̄) = ∇y^Î(x̄) ∈ ∂y(x̄)`. -/
theorem exists_stronglyActive_fderiv_eq_of_mem_interior_lowerQPRegion (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r₀ : E}
    (hr₀ : r₀ ∈ interior (lowerQPRegion φ g x₀ y₀ lam₀ I)) :
    ∃ Î ∈ stronglyActive s (fun J : {J // LowerAdmissible g x₀ y₀ lam₀ J} ↦
        lowerSolutionSelection φ g x₀ y₀ lam₀ J) x₀,
      fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ =
          fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ Î) x₀ ∧
        fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ ∈ clarkeJacobian s x₀ := by
  obtain ⟨V, hx₀V, hV⟩ :=
    exists_isPC1Selection_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  obtain ⟨s', hs', -⟩ := hasDirDerivAt_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  obtain ⟨Î, hÎ, hAÎ⟩ := hV.exists_stronglyActive_eq_of_eqOn hx₀V hs' isOpen_interior ⟨r₀, hr₀⟩
    fun r hr ↦ hasDirDerivAt_eq_of_mem_lowerQPRegion hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin hs'
      hI (interior_subset hr)
  refine ⟨Î, hÎ, hAÎ, subset_convexHull ℝ _ ?_⟩
  rw [hV.bouligandJacobian_eq hx₀V]
  exact ⟨Î, hÎ, hAÎ.symm⟩

end Solution

variable (φ g) in
/-- The strict complementarity condition (SCR) of [Dempe 2002, p. 91] for the index set `I` and
the direction `r`: `KKT(r, I, λ⁰)` has a solution `(d, γ)` with `γᵢ > 0` for `i ∈ I \ J(λ⁰)` and
`∇gᵢ(x̄, ȳ)(r, d) < 0` for active `i ∉ I`. -/
def LowerSCR (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (I : Finset ι) (r : E) : Prop :=
  ∃ d γ, LowerQPSystem φ g x₀ y₀ lam₀ I r d γ ∧ (∀ i ∈ I, ¬ 0 < lam₀ i → 0 < γ i) ∧
    ∀ i ∉ I, g i (x₀, y₀) = 0 → fderiv ℝ (g i) (x₀, y₀) (r, d) < 0

/-- Under (SCR) for `I` and `r⁰`, the direction `r⁰` lies in the interior of `R(I, λ⁰)`: the
solution `(∇y^I(x̄) r, ∇λ^I(x̄) r)` of the equations depends continuously on `r`, and the strict
inequalities persist. -/
theorem mem_interior_lowerQPRegion_of_lowerSCR (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r₀ : E}
    (h : LowerSCR φ g x₀ y₀ lam₀ I r₀) : r₀ ∈ interior (lowerQPRegion φ g x₀ y₀ lam₀ I) := by
  obtain ⟨d₀, γ₀, hsys, hγ, hg0⟩ := h
  set D := fderiv ℝ (lowerSelection φ g x₀ y₀ lam₀ I) x₀
  have hD0 : (d₀, γ₀) = D r₀ := eq_fderiv_lowerSelection hφ hg hkkt hlicq hssoc hI
    ((fderiv_lowerKKTMap_eq_zero_iff hφ hg I x₀ y₀ lam₀ r₀ d₀ γ₀).2
      ⟨hsys.1, hsys.2.1, hsys.2.2.2.2⟩)
  have hEq : ∀ r, _ := fun r ↦ (fderiv_lowerKKTMap_eq_zero_iff hφ hg I x₀ y₀ lam₀ r (D r).1
    (D r).2).1 (fderiv_lowerKKTMap_fderiv_lowerSelection hφ hg hkkt hlicq hssoc hI r)
  have hγev : ∀ᶠ r in 𝓝 r₀, ∀ i ∈ I, ¬ 0 < lam₀ i → 0 < (D r).2 i :=
    eventually_all.2 fun i ↦ by
      by_cases hi : i ∈ I ∧ ¬ 0 < lam₀ i
      · have hc : Continuous fun r ↦ (D r).2 i :=
          (continuous_apply i).comp (continuous_snd.comp D.continuous)
        have h0 : 0 < (D r₀).2 i := by
          rw [← hD0]
          exact hγ i hi.1 hi.2
        exact (hc.continuousAt.eventually (lt_mem_nhds h0)).mono fun r hr _ _ ↦ hr
      · exact Eventually.of_forall fun r hi' hl ↦ absurd ⟨hi', hl⟩ hi
  have hgev : ∀ᶠ r in 𝓝 r₀, ∀ i ∉ I, g i (x₀, y₀) = 0 →
      fderiv ℝ (g i) (x₀, y₀) (r, (D r).1) < 0 :=
    eventually_all.2 fun i ↦ by
      by_cases hi : i ∉ I ∧ g i (x₀, y₀) = 0
      · have hc : Continuous fun r ↦ fderiv ℝ (g i) (x₀, y₀) (r, (D r).1) :=
          (fderiv ℝ (g i) (x₀, y₀)).continuous.comp
            (continuous_id.prodMk (continuous_fst.comp D.continuous))
        have h0 : fderiv ℝ (g i) (x₀, y₀) (r₀, (D r₀).1) < 0 := by
          rw [← hD0]
          exact hg0 i hi.1 hi.2
        exact (hc.continuousAt.eventually (gt_mem_nhds h0)).mono fun r hr _ _ ↦ hr
      · exact Eventually.of_forall fun r hi' ha ↦ absurd ⟨hi', ha⟩ hi
  refine mem_interior_iff_mem_nhds.2 ((hγev.and hgev).mono fun r ⟨h1, h2⟩ ↦
    ⟨(D r).1, (D r).2, (hEq r).1, (hEq r).2.1, fun i hi hia ↦ (h2 i hi hia).le,
      fun i hi hl ↦ (h1 i hi hl).le, (hEq r).2.2⟩)

/-- **Thm. 4.12 of [Dempe 2002]**, first assertion, under (LICQ): if (SCR) holds for an admissible
`I` and a direction `r⁰`, then `∇y^I(x̄) ∈ ∂y(x̄)`. -/
theorem fderiv_mem_clarkeJacobian_of_lowerSCR (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E} (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀)
    (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) {r₀ : E}
    (hscr : LowerSCR φ g x₀ y₀ lam₀ I r₀) :
    fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ ∈ clarkeJacobian s x₀ := by
  obtain ⟨-, -, -, h⟩ := exists_stronglyActive_fderiv_eq_of_mem_interior_lowerQPRegion hφ hg hkkt
    hlicq hssoc hU hs₀ hsc hsmin hI (mem_interior_lowerQPRegion_of_lowerSCR hφ hg hkkt hlicq hssoc
      hI hscr)
  exact h

variable (φ g) in
/-- The full row rank condition (FRR) of [Dempe 2002, p. 91] at `λ⁰`: the matrix `M` built from
`∇²_yy L`, `∇_y g_{J(λ⁰)}`, `∇²_yx L` and `∇g_{I(x̄, ȳ)}` has full row rank, i.e. every right-hand
side `(w, b)` is attained by some `(d, γ, r)` with `γ` supported on `J(λ⁰)`. -/
def LowerFRR (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) : Prop :=
  ∀ (w : StrongDual ℝ F) (b : ι → ℝ), ∃ (r : E) (d : F) (γ : ι → ℝ),
    (∀ i, ¬ 0 < lam₀ i → γ i = 0) ∧
    lowerMixedHessian φ g x₀ y₀ lam₀ r + lowerHessian φ g x₀ y₀ lam₀ d +
        ∑ i, γ i • fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ = w ∧
      ∀ i, g i (x₀, y₀) = 0 → fderiv ℝ (g i) (x₀, y₀) (r, d) = b i

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Under (FRR), (SCR) holds for every admissible index set `I` and a suitable direction. -/
theorem exists_lowerSCR_of_lowerFRR {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hfrr : LowerFRR φ g x₀ y₀ lam₀) {I : Finset ι} (hI : LowerAdmissible g x₀ y₀ lam₀ I) :
    ∃ r, LowerSCR φ g x₀ y₀ lam₀ I r := by
  classical
  set c : ι → ℝ := fun i ↦ if i ∈ I ∧ ¬ 0 < lam₀ i then 1 else 0 with hc
  obtain ⟨r, d, γ', hγ', hw, hb⟩ :=
    hfrr (-∑ i, c i • fderiv ℝ (fun z ↦ g i (x₀, z)) y₀) fun i ↦ if i ∈ I then 0 else -1
  refine ⟨r, d, γ' + c, ⟨?_, fun i hi ↦ ?_, fun i hi hia ↦ ?_, fun i hi hl ↦ ?_, fun i hi ↦ ?_⟩,
    fun i hi hl ↦ ?_, fun i hi hia ↦ ?_⟩
  · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← add_assoc, hw, neg_add_cancel]
  · rw [hb i (hI.2 i hi), if_pos hi]
  · rw [hb i hia, if_neg hi]
    norm_num
  · simp only [Pi.add_apply, hc, hγ' i hl, if_pos (And.intro hi hl)]
    norm_num
  · have hl : ¬ 0 < lam₀ i := fun h ↦ hi (hI.1 i h)
    simp [hc, hi, hγ' i hl]
  · simp only [Pi.add_apply, hc, hγ' i hl, if_pos (And.intro hi hl)]
    norm_num
  · rw [hb i hia, if_neg hi]
    norm_num

/-- **Thm. 4.12 of [Dempe 2002]**, second assertion, under (LICQ): under (FRR),
`∂y(x̄) = conv {∇y^I(x̄) : J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)}`. -/
theorem clarkeJacobian_eq_of_lowerFRR (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀)
    (hfrr : LowerFRR φ g x₀ y₀ lam₀) {s : E → F} {U : Set E} (hU : U ∈ 𝓝 x₀)
    (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    clarkeJacobian s x₀ = convexHull ℝ (range fun I : {I // LowerAdmissible g x₀ y₀ lam₀ I} ↦
      fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀) := by
  refine subset_antisymm ?_ (convexHull_min ?_ (convex_convexHull ℝ _))
  · rw [clarkeJacobian_eq_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin]
    exact convexHull_mono (image_subset_range _ _)
  · rintro _ ⟨I, rfl⟩
    obtain ⟨r, hr⟩ := exists_lowerSCR_of_lowerFRR hfrr I.2
    exact fderiv_mem_clarkeJacobian_of_lowerSCR hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin I.2 hr

end Bilevel
