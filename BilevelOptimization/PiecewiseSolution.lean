/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.StrongStability
import BilevelOptimization.PiecewiseSmooth

/-!
# Piecewise smoothness and directional derivatives of local solution functions

Thm. 4.10 and 4.11 of [Dempe 2002] (Ralph–Dempe) in the (LICQ) case: if `ȳ` is a KKT point of
the follower's problem at `x̄` with (LICQ) and (SSOC), the local solution function `y(·)` of
Thm. 4.4 is `PC¹` at `x̄`, and its directional derivative in direction `r` is the unique optimal
solution of the quadratic program `QP(λ⁰, r)` (4.20).

## Main results

* `lowerKKTMap`: the KKT system of the equality-constrained problems (4.19) with index set `I`.
* `isInvertible_fderiv_lowerKKTMap`: its Jacobian in `(y, λ)` is invertible whenever
  `J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)` (conditions (C1)–(C2) of p. 86).
* `lowerSelection`: the corresponding selection functions `(y^I(·), λ^I(·))`, by the implicit
  function theorem.
* `eventually_exists_lowerSelection`: near `x̄`, `y(x)` and its multiplier are the value of one of
  these selection functions.
* `isPC1At_of_lowerSSOC`, `exists_isPC1At_of_lowerSSOC`: Thm. 4.10.
* `lowerQPObjective`, `lowerQPFeasible`, `hasDirDerivAt_of_lowerSSOC`: Thm. 4.11.

## Differences from the book

* The book assumes (MFCQ) and (CRCQ) and refers to [235] for the proofs. We assume (LICQ), as in
  our version of Thm. 4.4 (`isLowerStronglyStable`). Under (LICQ), (CRCQ) holds automatically, the
  multiplier `λ⁰` is unique, and the auxiliary problem (4.21) is trivial.
* The selection functions are indexed by all index sets `I` (those that do not satisfy (C1)–(C2)
  get a constant function), and the multiplier is part of the selection.
* The data are `C²` on `E × F` and there are no equality constraints.
-/

open Filter Topology Set
open VariationalAnalysis (graph lowerFeasible)

namespace Bilevel

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [Fintype ι]

/-! ### The KKT system of the problems (4.19) -/

section KKTMap

variable (φ : E × F → ℝ) (g : ι → E × F → ℝ)

/-- The KKT system of the equality-constrained problem (4.19) of [Dempe 2002] with active index
set `I`, as a map of `(x, (y, λ))`: `∇_y L(x, y, λ) = 0`, `gᵢ(x, y) = 0` for `i ∈ I` and
`λᵢ = 0` for `i ∉ I`. -/
noncomputable def lowerKKTMap [DecidableEq ι] (I : Finset ι) (q : E × (F × (ι → ℝ))) :
    StrongDual ℝ F × (ι → ℝ) :=
  (lowerLagrangianDeriv φ g q.2.2 (q.1, q.2.1),
    fun i ↦ if i ∈ I then g i (q.1, q.2.1) else q.2.2 i)

/-- The mixed second derivative `∇²_yx L(x̄, ȳ, λ)` of the follower's Lagrangian. -/
noncomputable def lowerMixedHessian (x₀ : E) (y₀ : F) (lam : ι → ℝ) : E →L[ℝ] StrongDual ℝ F :=
  (fderiv ℝ (lowerLagrangianDeriv φ g lam) (x₀, y₀)).comp (ContinuousLinearMap.inl ℝ E F)

/-- The objective of the quadratic program `QP(λ⁰, r)` (4.20) of [Dempe 2002]:
`½ dᵀ ∇²_yy L d + dᵀ ∇²_yx L r`. -/
noncomputable def lowerQPObjective (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (r : E) (d : F) : ℝ :=
  lowerHessian φ g x₀ y₀ lam₀ d d / 2 + lowerMixedHessian φ g x₀ y₀ lam₀ r d

/-- The feasible set of `QP(λ⁰, r)` (4.20): `∇gᵢ(x̄, ȳ)(r, d) = 0` for `i ∈ J(λ⁰)` and `≤ 0` for
`i ∈ I(x̄, ȳ)`. -/
def lowerQPFeasible (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (r : E) : Set F :=
  {d | (∀ i, 0 < lam₀ i → fderiv ℝ (g i) (x₀, y₀) (r, d) = 0) ∧
    ∀ i, g i (x₀, y₀) = 0 → fderiv ℝ (g i) (x₀, y₀) (r, d) ≤ 0}

end KKTMap

variable {φ : E × F → ℝ} {g : ι → E × F → ℝ}

theorem fderiv_lowerLagrangianDeriv_apply (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (lam : ι → ℝ) (p v : E × F) :
    fderiv ℝ (lowerLagrangianDeriv φ g lam) p v =
      fderiv ℝ (fun p ↦ (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ E F)) p v +
        ∑ i, lam i • fderiv ℝ (fun p ↦ (fderiv ℝ (g i) p).comp (ContinuousLinearMap.inr ℝ E F))
          p v := by
  have hA := ((contDiff_fderiv_comp_inr hφ).differentiable one_ne_zero p).hasFDerivAt
  have hB := fun i ↦ ((contDiff_fderiv_comp_inr (hg i)).differentiable one_ne_zero p).hasFDerivAt
  have hd : HasFDerivAt (lowerLagrangianDeriv φ g lam)
      (fderiv ℝ (fun p ↦ (fderiv ℝ φ p).comp (ContinuousLinearMap.inr ℝ E F)) p +
        ∑ i, lam i • fderiv ℝ (fun p ↦ (fderiv ℝ (g i) p).comp
          (ContinuousLinearMap.inr ℝ E F)) p) p :=
    hA.add (HasFDerivAt.fun_sum fun i _ ↦ (hB i).const_smul (lam i))
  rw [hd.fderiv]
  simp only [add_apply, sum_apply, smul_apply]

/-- The derivative of the follower's `y`-gradient splits into the mixed and the `y`-Hessian. -/
theorem fderiv_lowerLagrangianDeriv_apply_eq (x₀ : E) (y₀ : F) (lam : ι → ℝ) (r : E) (d : F) :
    fderiv ℝ (lowerLagrangianDeriv φ g lam) (x₀, y₀) (r, d) =
      lowerMixedHessian φ g x₀ y₀ lam r + lowerHessian φ g x₀ y₀ lam d := by
  rw [show ((r, d) : E × F) = (r, 0) + (0, d) by simp, map_add]
  rfl

/-- The `y`-Hessian of the follower's Lagrangian is symmetric. -/
theorem lowerHessian_symm (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i)) (x₀ : E) (y₀ : F)
    (lam : ι → ℝ) (v w : F) : lowerHessian φ g x₀ y₀ lam v w = lowerHessian φ g x₀ y₀ lam w v := by
  have hL : ContDiff ℝ 2 (lowerLagrangian φ g x₀ lam) :=
    (hφ.comp (contDiff_prodMk_right x₀)).add
      (ContDiff.sum fun i _ ↦ contDiff_const.mul ((hg i).comp (contDiff_prodMk_right x₀)))
  rw [← fderiv_fderiv_lowerLagrangian hφ hg]
  exact hL.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w

/-- A limit along `𝓝[>] 0` of a function that is frequently nonpositive is nonpositive. -/
theorem nonpos_of_tendsto_of_frequently {f : ℝ → ℝ} {a : ℝ} (hf : Tendsto f (𝓝[>] 0) (𝓝 a))
    (h : ∃ᶠ t in 𝓝[>] 0, f t ≤ 0) : a ≤ 0 := by
  by_contra ha
  obtain ⟨t, ht, ht'⟩ := (h.and_eventually (hf.eventually (lt_mem_nhds (not_le.1 ha)))).exists
  linarith

variable [DecidableEq ι]

theorem contDiff_lowerKKTMap (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (I : Finset ι) : ContDiff ℝ 1 (lowerKKTMap φ g I) := by
  have hp : ContDiff ℝ 1 fun q : E × (F × (ι → ℝ)) ↦ (q.1, q.2.1) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hl : ∀ i, ContDiff ℝ 1 fun q : E × (F × (ι → ℝ)) ↦ q.2.2 i := fun i ↦
    (contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_snd)
  unfold lowerKKTMap lowerLagrangianDeriv
  refine ContDiff.prodMk (((contDiff_fderiv_comp_inr hφ).comp hp).add
    (ContDiff.sum fun i _ ↦ (hl i).smul ((contDiff_fderiv_comp_inr (hg i)).comp hp)))
    (contDiff_pi.2 fun i ↦ ?_)
  by_cases hi : i ∈ I
  · simp only [if_pos hi]
    exact ((hg i).of_le (by norm_num)).comp hp
  · simp only [if_neg hi]
    exact hl i

/-- The derivative of the KKT system of (4.19). -/
theorem fderiv_lowerKKTMap_apply (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    (I : Finset ι) (q : E × (F × (ι → ℝ))) (r : E) (d : F) (ν : ι → ℝ) :
    fderiv ℝ (lowerKKTMap φ g I) q (r, (d, ν)) =
      (fderiv ℝ (lowerLagrangianDeriv φ g q.2.2) (q.1, q.2.1) (r, d) +
        ∑ i, ν i • fderiv ℝ (fun z ↦ g i (q.1, z)) q.2.1,
        fun i ↦ if i ∈ I then fderiv ℝ (g i) (q.1, q.2.1) (r, d) else ν i) := by
  set p : E × F := (q.1, q.2.1)
  set π' : E × (F × (ι → ℝ)) →L[ℝ] E × F := (ContinuousLinearMap.fst ℝ E (F × (ι → ℝ))).prod
    ((ContinuousLinearMap.fst ℝ F (ι → ℝ)).comp (ContinuousLinearMap.snd ℝ E (F × (ι → ℝ))))
  have hπ : HasFDerivAt (fun q : E × (F × (ι → ℝ)) ↦ (q.1, q.2.1)) π' q :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp q hasFDerivAt_snd)
  have hl : ∀ i, HasFDerivAt (fun q : E × (F × (ι → ℝ)) ↦ q.2.2 i)
      ((ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.snd ℝ F (ι → ℝ)).comp
        (ContinuousLinearMap.snd ℝ E (F × (ι → ℝ))))) q := fun i ↦
    ((ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.snd ℝ F (ι → ℝ)).comp
        (ContinuousLinearMap.snd ℝ E (F × (ι → ℝ))))).hasFDerivAt
  have hA := (((contDiff_fderiv_comp_inr hφ).differentiable one_ne_zero p).hasFDerivAt).comp q hπ
  have hB := fun i ↦
    (((contDiff_fderiv_comp_inr (hg i)).differentiable one_ne_zero p).hasFDerivAt).comp q hπ
  have hG := fun i ↦ (((hg i).differentiable (by norm_num) p).hasFDerivAt).comp q hπ
  have h1 := hA.add (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hl i).smul (hB i))
  have h2 : HasFDerivAt (fun q : E × (F × (ι → ℝ)) ↦
      fun i ↦ if i ∈ I then g i (q.1, q.2.1) else q.2.2 i)
      (ContinuousLinearMap.pi fun i ↦ if i ∈ I then (fderiv ℝ (g i) p).comp π' else
        (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.snd ℝ F (ι → ℝ)).comp
          (ContinuousLinearMap.snd ℝ E (F × (ι → ℝ))))) q := by
    refine hasFDerivAt_pi.2 fun i ↦ ?_
    by_cases hi : i ∈ I
    · simp only [if_pos hi]
      exact hG i
    · simp only [if_neg hi]
      exact hl i
  have h : HasFDerivAt (lowerKKTMap φ g I) _ q := h1.prodMk h2
  rw [h.fderiv]
  ext1
  · simp only [ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', π',
      fderiv_lowerLagrangianDeriv_apply hφ hg, Finset.sum_add_distrib,
      fderiv_section ((hg _).differentiable (by norm_num) p)]
    abel
  · ext i
    by_cases hi : i ∈ I <;>
      simp [hi, π', p]

/-- `T` is invertible when it is injective between spaces of the same finite dimension. -/
theorem isInvertible_of_injective {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (T : X →L[ℝ] Y) (hdim : Module.finrank ℝ X = Module.finrank ℝ Y)
    (hT : Function.Injective T) : T.IsInvertible := by
  have hs : Function.Surjective (T : X →ₗ[ℝ] Y) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hT
  exact ⟨(LinearEquiv.ofBijective (T : X →ₗ[ℝ] Y) ⟨hT, hs⟩).toContinuousLinearEquiv,
    by ext; rfl⟩

theorem finrank_strongDual [FiniteDimensional ℝ F] :
    Module.finrank ℝ (StrongDual ℝ F) = Module.finrank ℝ F :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := F) (F' := ℝ)).finrank_eq.symm.trans
    Subspace.dual_finrank_eq

/-- Under (LICQ) and (SSOC), the Jacobian of the KKT system of (4.19) with respect to `(y, λ)` is
invertible for every index set `I` with `J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)`. -/
theorem isInvertible_fderiv_lowerKKTMap [FiniteDimensional ℝ F] (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {I : Finset ι} (hJI : ∀ i, 0 < lam₀ i → i ∈ I)
    (hIA : ∀ i ∈ I, g i (x₀, y₀) = 0) :
    (fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀)) ∘L
      ContinuousLinearMap.inr ℝ E (F × (ι → ℝ))).IsInvertible := by
  refine isInvertible_of_injective _ (by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_strongDual]) ?_
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨d, ν⟩ h0
  have h := h0
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inr_apply, fderiv_lowerKKTMap_apply hφ hg,
    fderiv_lowerLagrangianDeriv_apply_eq, map_zero, zero_add, Prod.mk_eq_zero] at h
  obtain ⟨h1, h2⟩ := h
  have hν : ∀ i, i ∉ I → ν i = 0 := fun i hi ↦ by
    have := congrFun h2 i
    simpa [hi] using this
  have hd : ∀ i ∈ I, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ d = 0 := fun i hi ↦ by
    have := congrFun h2 i
    simp only [if_pos hi, Pi.zero_apply] at this
    rw [fderiv_section_apply ((hg i).differentiable (by norm_num) _)]
    exact this
  -- `d = 0` by (SSOC)
  have hd0 : d = 0 := by
    by_contra hne
    have hpos := hssoc lam₀ hkkt d hne fun i hi ↦ hd i (hJI i hi)
    have happ := congrArg (fun T : StrongDual ℝ F ↦ T d) h1
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at happ
    have hsum : ∑ i, ν i * fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ d = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by
        by_cases hi : i ∈ I
        · rw [hd i hi, mul_zero]
        · rw [hν i hi, zero_mul]
    rw [hsum, add_zero] at happ
    linarith
  subst hd0
  -- `ν = 0` by (LICQ)
  rw [map_zero, zero_add] at h1
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i ↦ g i (x₀, y₀) = 0)
    fun i ↦ ν i • fderiv ℝ (fun z ↦ g i (x₀, z)) y₀
  have hrest : ∑ i : {i // ¬ g i (x₀, y₀) = 0}, ν i.1 • fderiv ℝ (fun z ↦ g i.1 (x₀, z)) y₀ = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hν i.1 fun hi ↦ i.2 (hIA i.1 hi), zero_smul]
  rw [hrest, add_zero, h1] at hsplit
  have hact := Fintype.linearIndependent_iff.1 hlicq (fun i ↦ ν i.1) hsplit
  refine Prod.ext rfl (funext fun i ↦ ?_)
  by_cases hi : g i (x₀, y₀) = 0
  · exact hact ⟨i, hi⟩
  · exact hν i fun hI ↦ hi (hIA i hI)

/-! ### Selection functions -/

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

open Classical in
/-- The solution–multiplier function `x ↦ (y^I(x), λ^I(x))` of the KKT system of (4.19) with index
set `I` near `(x̄, ȳ, λ⁰)`, given by the implicit function theorem (and the constant `(ȳ, λ⁰)`
when the theorem does not apply). -/
noncomputable def lowerSelection (φ : E × F → ℝ) (g : ι → E × F → ℝ) (x₀ : E) (y₀ : F)
    (lam₀ : ι → ℝ) (I : Finset ι) : E → F × (ι → ℝ) :=
  if h : ContDiffAt ℝ 1 (lowerKKTMap φ g I) (x₀, (y₀, lam₀)) ∧
      (fderiv ℝ (lowerKKTMap φ g I) (x₀, (y₀, lam₀)) ∘L
        ContinuousLinearMap.inr ℝ E (F × (ι → ℝ))).IsInvertible then
    h.1.implicitFunction one_ne_zero h.2
  else fun _ ↦ (y₀, lam₀)

/-- The local solution function `x ↦ y^I(x)` of the problem (4.19) with index set `I`: the first
component of `lowerSelection`. -/
noncomputable def lowerSolutionSelection (φ : E × F → ℝ) (g : ι → E × F → ℝ) (x₀ : E) (y₀ : F)
    (lam₀ : ι → ℝ) (I : Finset ι) (x : E) : F :=
  (lowerSelection φ g x₀ y₀ lam₀ I x).1

theorem contDiffAt_lowerSelection (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (I : Finset ι) :
    ContDiffAt ℝ 1 (lowerSelection φ g x₀ y₀ lam₀ I) x₀ := by
  unfold lowerSelection
  split_ifs with h
  · exact h.1.contDiffAt_implicitFunction one_ne_zero h.2
  · exact contDiffAt_const

theorem lowerSelection_apply_self (x₀ : E) (y₀ : F) (lam₀ : ι → ℝ) (I : Finset ι) :
    lowerSelection φ g x₀ y₀ lam₀ I x₀ = (y₀, lam₀) := by
  unfold lowerSelection
  split_ifs with h
  · exact h.1.implicitFunction_apply_self one_ne_zero h.2
  · rfl

/-- Every KKT point `(y, λ)` of the follower's problem at a parameter `x` near `x̄`, with `y`
near `ȳ`, is the value at `x` of one of the selection functions of (4.19) whose index set satisfies
`J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)`. -/
theorem exists_pos_lowerSelection_eq (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ δ > 0, ∀ (x : E) (y : F) (lam : ι → ℝ), dist x x₀ < δ → dist y y₀ < δ →
      IsLowerKKT φ g x y lam → ∃ I : Finset ι, (∀ i, 0 < lam₀ i → i ∈ I) ∧
        (∀ i ∈ I, g i (x₀, y₀) = 0) ∧ lowerSelection φ g x₀ y₀ lam₀ I x = (y, lam) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hpli : LowerPLI g x₀ y₀ := lowerPLI_of_lowerLICQ hkkt.1 hlicq
  set u : E × (F × (ι → ℝ)) := (x₀, (y₀, lam₀))
  -- the implicit function theorem for each admissible index set
  have hIFT : ∀ I : Finset ι, ∀ᶠ v in 𝓝 u, ((∀ i, 0 < lam₀ i → i ∈ I) ∧
      ∀ i ∈ I, g i (x₀, y₀) = 0) → lowerKKTMap φ g I v = lowerKKTMap φ g I u →
        lowerSelection φ g x₀ y₀ lam₀ I v.1 = v.2 := by
    intro I
    by_cases hadm : (∀ i, 0 < lam₀ i → i ∈ I) ∧ ∀ i ∈ I, g i (x₀, y₀) = 0
    · have hinv := isInvertible_fderiv_lowerKKTMap hφ hg hkkt hlicq hssoc hadm.1 hadm.2
      have hcd := (contDiff_lowerKKTMap hφ hg I).contDiffAt (x := u)
      filter_upwards [hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv]
        with v hv _ heq
      unfold lowerSelection
      rw [dif_pos ⟨hcd, hinv⟩]
      exact hv.1 heq
    · exact Eventually.of_forall fun v h ↦ absurd h hadm
  obtain ⟨r, hr, hIFT⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 hIFT)
  have hpos : ∀ᶠ lam in 𝓝 lam₀, ∀ i, 0 < lam₀ i → 0 < lam i :=
    eventually_all.2 fun i ↦ by
      by_cases hi : 0 < lam₀ i
      · exact (((continuous_apply i).tendsto lam₀).eventually (lt_mem_nhds hi)).mono
          fun _ h _ ↦ h
      · exact Eventually.of_forall fun _ h ↦ absurd h hi
  obtain ⟨r₂, hr₂, hpos⟩ := Metric.eventually_nhds_iff.1 hpos
  -- multipliers near `λ⁰` and inactive constraints staying inactive
  have hΛ : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), lowerMultipliers φ g p.1 p.2 ⊆
      Metric.ball lam₀ (min r r₂) :=
    upperHemicontinuousAt_lowerMultipliers hφ1 hg1 hpli _ Metric.isOpen_ball fun lam hlam ↦ by
      rw [lowerMultipliers_subsingleton_of_lowerLICQ hlicq hlam hkkt]
      exact Metric.mem_ball_self (lt_min hr hr₂)
  have hinact : ∀ᶠ p : E × F in 𝓝 (x₀, y₀), ∀ i, g i (x₀, y₀) < 0 → g i p < 0 :=
    eventually_all.2 fun i ↦ by
      by_cases hi : g i (x₀, y₀) < 0
      · exact (((hg i).continuous.tendsto _).eventually (eventually_lt_nhds hi)).mono
          fun _ h _ ↦ h
      · exact Eventually.of_forall fun _ h ↦ absurd h hi
  obtain ⟨δ₁, hδ₁, hnear⟩ := Metric.eventually_nhds_iff.1 (hΛ.and hinact)
  refine ⟨min r δ₁, lt_min hr hδ₁, fun x y lam hx hy hlam ↦ ?_⟩
  have hp : dist (x, y) (x₀, y₀) < δ₁ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_le (min_le_right _ _)) (hy.trans_le (min_le_right _ _))
  obtain ⟨hxΛ, hxin⟩ := hnear hp
  have hlε : dist lam lam₀ < min r r₂ := hxΛ hlam
  set I : Finset ι := Finset.univ.filter fun i ↦ g i (x, y) = 0 with hI
  have hmemI : ∀ i, i ∈ I ↔ g i (x, y) = 0 := fun i ↦ by simp [hI]
  have hJ : ∀ i, 0 < lam₀ i → i ∈ I := fun i hi ↦ (hmemI i).2
    ((mul_eq_zero.1 (hlam.2.2.1 i)).resolve_left (hpos (hlε.trans_le (min_le_right _ _)) i hi).ne')
  have hIA : ∀ i ∈ I, g i (x₀, y₀) = 0 := fun i hi ↦ by
    by_contra hne
    have := hxin i (lt_of_le_of_ne (hkkt.1 i) hne)
    rw [(hmemI i).1 hi] at this
    exact lt_irrefl _ this
  have hdφ : ∀ p, DifferentiableAt ℝ φ p := fun p ↦ hφ1.differentiable one_ne_zero p
  have hdg : ∀ i p, DifferentiableAt ℝ (g i) p := fun i p ↦ (hg1 i).differentiable one_ne_zero p
  have heq : lowerKKTMap φ g I (x, (y, lam)) = lowerKKTMap φ g I u := by
    simp only [lowerKKTMap, u]
    rw [lowerLagrangianDeriv_eq_zero (hdφ _) (fun i ↦ hdg i _) hlam,
      lowerLagrangianDeriv_eq_zero (hdφ _) (fun i ↦ hdg i _) hkkt]
    refine Prod.ext rfl (funext fun i ↦ ?_)
    by_cases hi : i ∈ I
    · simp only [if_pos hi, (hmemI i).1 hi, hIA i hi]
    · simp only [if_neg hi]
      rw [(mul_eq_zero.1 (hlam.2.2.1 i)).resolve_right fun h ↦ hi ((hmemI i).2 h)]
      by_contra h
      exact hi (hJ i (lt_of_le_of_ne (hkkt.2.1 i) h))
  refine ⟨I, hJ, hIA, hIFT (y := (x, (y, lam))) ?_ I ⟨hJ, hIA⟩ heq⟩
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_lt (hx.trans_le (min_le_left _ _))
    (max_lt (hy.trans_le (min_le_left _ _)) (hlε.trans_le (min_le_left _ _)))

/-- Near `x̄`, every local solution `y(x)` near `ȳ`, together with its multiplier, is the value of
one of the selection functions of (4.19) whose index set satisfies `J(λ⁰) ⊆ I ⊆ I(x̄, ȳ)`. -/
theorem eventually_exists_lowerSelection (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F}
    (hs : ContinuousAt s x₀) (hs₀ : s x₀ = y₀)
    (hsmin : ∀ᶠ x in 𝓝 x₀, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    ∀ᶠ x in 𝓝 x₀, ∃ I : Finset ι, (∀ i, 0 < lam₀ i → i ∈ I) ∧ (∀ i ∈ I, g i (x₀, y₀) = 0) ∧
      ∃ lam, IsLowerKKT φ g x (s x) lam ∧ lowerSelection φ g x₀ y₀ lam₀ I x = (s x, lam) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hg1 : ∀ i, ContDiff ℝ 1 (g i) := fun i ↦ (hg i).of_le (by norm_num)
  have hpli : LowerPLI g x₀ y₀ := lowerPLI_of_lowerLICQ hkkt.1 hlicq
  obtain ⟨δ, hδ, hsel⟩ := exists_pos_lowerSelection_eq hφ hg hkkt hlicq hssoc
  rw [ContinuousAt, hs₀] at hs
  have hpair : Tendsto (fun x ↦ (x, s x)) (𝓝 x₀) (𝓝 (x₀, y₀)) := tendsto_id.prodMk_nhds hs
  filter_upwards [hsmin, hpair.eventually (eventually_lowerPLI hg1 hpli),
    Metric.ball_mem_nhds x₀ hδ, hs.eventually (Metric.ball_mem_nhds y₀ hδ)]
    with x hx hxP hxδ hsδ
  obtain ⟨lam, hlam⟩ := exists_isLowerKKT_of_isLocalMinOn hx.1 hx.2
    ((hφ1.comp (contDiff_prodMk_right x)).differentiable one_ne_zero (s x))
    (fun i ↦ ((hg1 i).comp (contDiff_prodMk_right x)).contDiffAt) hxP
  obtain ⟨I, hJ, hIA, he⟩ := hsel x (s x) lam hxδ hsδ hlam
  exact ⟨I, hJ, hIA, lam, hlam, he⟩

/-- **Thm. 4.10 of [Dempe 2002]** (Ralph–Dempe) under (LICQ), with explicit selections: a
continuous local solution function `y(·)` through a KKT point `ȳ` with (LICQ) and (SSOC) is a
continuous selection of the local solution functions `y^I(·)` of the problems (4.19) on an open
neighborhood of `x̄`. -/
theorem exists_isPC1Selection_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    ∃ V, x₀ ∈ V ∧ IsPC1Selection s (lowerSolutionSelection φ g x₀ y₀ lam₀) V := by
  have hsel := eventually_exists_lowerSelection hφ hg hkkt hlicq hssoc (hsc.continuousAt hU) hs₀
    (Filter.mem_of_superset hU hsmin)
  set zs : Finset ι → E → F := lowerSolutionSelection φ g x₀ y₀ lam₀ with hzs
  have hcd : ∀ I, ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 1 (zs I) x := fun I ↦
    (contDiffAt_fst.comp x₀ (contDiffAt_lowerSelection x₀ y₀ lam₀ I)).eventually (by simp)
  set V : Set E := interior {x | x ∈ U ∧ (∀ I, ContDiffAt ℝ 1 (zs I) x) ∧ ∃ I, s x = zs I x}
  have hx₀V : x₀ ∈ V := mem_interior_iff_mem_nhds.2 (inter_mem hU ((eventually_all.2 hcd).and
    (hsel.mono fun x ⟨I, _, _, lam, _, he⟩ ↦
      ⟨I, by simp only [hzs, lowerSolutionSelection, he]⟩)))
  exact ⟨V, hx₀V, isOpen_interior, hsc.mono fun x hx ↦ (interior_subset hx).1,
    fun I x hx ↦ ((interior_subset hx).2.1 I).contDiffWithinAt, fun x hx ↦ (interior_subset hx).2.2⟩

/-- **Thm. 4.10 of [Dempe 2002]** (Ralph–Dempe) under (LICQ): a continuous local solution
function `y(·)` through a KKT point `ȳ` with (LICQ) and (SSOC) is `PC¹` at `x̄`, with the local
solution functions of the problems (4.19) as selection functions. -/
theorem isPC1At_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    IsPC1At s x₀ := by
  obtain ⟨V, hx₀V, hV⟩ :=
    exists_isPC1Selection_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  set e := Fintype.equivFin (Finset ι)
  refine ⟨_, fun k ↦ lowerSolutionSelection φ g x₀ y₀ lam₀ (e.symm k), V, hx₀V, hV.1, hV.2.1,
    fun k ↦ hV.2.2.1 _, fun x hx ↦ ?_⟩
  obtain ⟨I, hI⟩ := hV.2.2.2 x hx
  exact ⟨e I, by simp [hI]⟩

/-- Thm. 4.4 and 4.10 of [Dempe 2002] together: under (LICQ) and (SSOC) the strongly stable local
solution function is `PC¹`. -/
theorem exists_isPC1At_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) :
    ∃ δ > 0, ∃ U ∈ 𝓝 x₀, ∃ s : E → F, s x₀ = y₀ ∧ ContinuousOn s U ∧ (∀ x ∈ U,
      s x ∈ Metric.ball y₀ δ ∧ s x ∈ lowerFeasible g x ∧
        IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x) ∧
        ∀ z ∈ Metric.ball y₀ δ, z ∈ lowerFeasible g x →
          IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) z → z = s x) ∧
      IsPC1At s x₀ := by
  obtain ⟨δ, hδ, U, hU, s, hs₀, hsc, hs⟩ := isLowerStronglyStable hφ hg hkkt hlicq hssoc
  exact ⟨δ, hδ, U, hU, s, hs₀, hsc, hs, isPC1At_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc
    fun x hx ↦ ⟨(hs x hx).2.1, (hs x hx).2.2.1⟩⟩

/-- **Thm. 4.11 of [Dempe 2002]** (Ralph–Dempe) under (LICQ): the local solution function `y(·)`
of Thm. 4.10 is directionally differentiable at `x̄`, and its directional derivative in direction
`r` is the unique optimal solution of the quadratic program `QP(λ⁰, r)` (4.20). Under (LICQ) the
multiplier `λ⁰` is unique, so problem (4.21) is trivial. -/
theorem hasDirDerivAt_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    ∃ s' : E → F, HasDirDerivAt s s' x₀ ∧ ∀ r, s' r ∈ lowerQPFeasible g x₀ y₀ lam₀ r ∧
      ∀ d ∈ lowerQPFeasible g x₀ y₀ lam₀ r, d ≠ s' r →
        lowerQPObjective φ g x₀ y₀ lam₀ r (s' r) < lowerQPObjective φ g x₀ y₀ lam₀ r d := by
  have hpc := isPC1At_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  have hsel := eventually_exists_lowerSelection hφ hg hkkt hlicq hssoc (hsc.continuousAt hU) hs₀
    (Filter.mem_of_superset hU hsmin)
  have hdg : ∀ i p, DifferentiableAt ℝ (g i) p := fun i p ↦ (hg i).differentiable (by norm_num) p
  suffices key : ∀ r, ∃ d, Tendsto (fun t : ℝ ↦ t⁻¹ • (s (x₀ + t • r) - s x₀)) (𝓝[>] 0) (𝓝 d) ∧
      d ∈ lowerQPFeasible g x₀ y₀ lam₀ r ∧ ∀ d' ∈ lowerQPFeasible g x₀ y₀ lam₀ r, d' ≠ d →
        lowerQPObjective φ g x₀ y₀ lam₀ r d < lowerQPObjective φ g x₀ y₀ lam₀ r d' by
    choose s' hs' using key
    exact ⟨s', fun r ↦ (hs' r).1, fun r ↦ (hs' r).2⟩
  intro r
  obtain ⟨v, hv⟩ := hpc.exists_tendsto_slope r
  have hγ : Tendsto (fun t : ℝ ↦ x₀ + t • r) (𝓝[>] 0) (𝓝 x₀) := by
    have hc : Continuous fun t : ℝ ↦ x₀ + t • r := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  -- some selection is active for arbitrarily small `t > 0`
  obtain ⟨I, hfreq⟩ : ∃ I : Finset ι, ∃ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
      ((∀ i, 0 < lam₀ i → i ∈ I) ∧ (∀ i ∈ I, g i (x₀, y₀) = 0) ∧
        ∃ lam, IsLowerKKT φ g (x₀ + t • r) (s (x₀ + t • r)) lam ∧
          lowerSelection φ g x₀ y₀ lam₀ I (x₀ + t • r) = (s (x₀ + t • r), lam)) := by
    by_contra hcon
    simp only [not_exists, Filter.not_frequently] at hcon
    obtain ⟨t, ht, ht0, I, hI⟩ :=
      ((eventually_all.2 hcon).and ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
        (hγ.eventually hsel))).exists
    exact ht I ⟨ht0, hI⟩
  obtain ⟨-, -, hJI, hIA, -⟩ := hfreq.exists
  have hinv := isInvertible_fderiv_lowerKKTMap hφ hg hkkt hlicq hssoc hJI hIA
  set u : E × (F × (ι → ℝ)) := (x₀, (y₀, lam₀))
  have hcd := (contDiff_lowerKKTMap hφ hg I).contDiffAt (x := u)
  set ψ := lowerSelection φ g x₀ y₀ lam₀ I with hψdef
  have hψ : ψ = hcd.implicitFunction one_ne_zero hinv := by
    rw [hψdef]
    unfold lowerSelection
    rw [dif_pos ⟨hcd, hinv⟩]
  have hψ₀ : ψ x₀ = (y₀, lam₀) := lowerSelection_apply_self x₀ y₀ lam₀ I
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ x₀) x₀ :=
    ((contDiffAt_lowerSelection x₀ y₀ lam₀ I).differentiableAt one_ne_zero).hasFDerivAt
  set d := (fderiv ℝ ψ x₀ r).1 with hd
  set ν := (fderiv ℝ ψ x₀ r).2 with hν
  have hl : HasDerivAt (fun t : ℝ ↦ x₀ + t • r) r 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const r).const_add x₀
  have hline : HasDerivAt (fun t : ℝ ↦ ψ (x₀ + t • r)) (fderiv ℝ ψ x₀ r) 0 :=
    hψd.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ • (ψ (x₀ + t • r) - (y₀, lam₀))) (𝓝[>] 0)
      (𝓝 (fderiv ℝ ψ x₀ r)) :=
    hline.tendsto_slope_zero_right.congr fun t ↦ by simp [hψ₀]
  -- (a) the directional derivative of `s` is `d`
  have hdlim : Tendsto (fun t : ℝ ↦ t⁻¹ • ((ψ (x₀ + t • r)).1 - y₀)) (𝓝[>] 0) (𝓝 d) :=
    ((continuous_fst.tendsto _).comp hslope).congr fun t ↦ by simp
  have hvd : v = d := tendsto_nhds_unique_of_frequently_eq hv hdlim
    (hfreq.mono fun t ⟨_, _, _, lam, _, he⟩ ↦ by rw [he, hs₀])
  subst hvd
  -- (b) differentiating the KKT system of (4.19) along `ψ`
  have hF : ∀ᶠ x in 𝓝 x₀, lowerKKTMap φ g I (x, ψ x) = lowerKKTMap φ g I u := by
    rw [hψ]
    exact hcd.eventually_apply_implicitFunction one_ne_zero hinv
  have hcomp : HasFDerivAt (fun x ↦ lowerKKTMap φ g I (x, ψ x))
      ((fderiv ℝ (lowerKKTMap φ g I) u).comp
        ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ψ x₀))) x₀ := by
    have h2 : HasFDerivAt (lowerKKTMap φ g I) (fderiv ℝ (lowerKKTMap φ g I) u) (x₀, ψ x₀) := by
      rw [hψ₀]
      exact (hcd.differentiableAt one_ne_zero).hasFDerivAt
    exact h2.comp x₀ ((hasFDerivAt_id x₀).prodMk hψd)
  have hconst : HasFDerivAt (fun x ↦ lowerKKTMap φ g I (x, ψ x)) (0 : E →L[ℝ] _) x₀ :=
    (hasFDerivAt_const (lowerKKTMap φ g I u) x₀).congr_of_eventuallyEq hF
  have h0 : fderiv ℝ (lowerKKTMap φ g I) u (r, (d, ν)) = 0 := by
    have := congrArg (fun T : E →L[ℝ] StrongDual ℝ F × (ι → ℝ) ↦ T r) (hcomp.unique hconst)
    simpa using this
  rw [fderiv_lowerKKTMap_apply hφ hg, Prod.mk_eq_zero] at h0
  obtain ⟨hgrad, hcons⟩ := h0
  rw [fderiv_lowerLagrangianDeriv_apply_eq] at hgrad
  have hcI : ∀ i ∈ I, fderiv ℝ (g i) (x₀, y₀) (r, d) = 0 := fun i hi ↦ by
    simpa [hi] using congrFun hcons i
  have hνI : ∀ i ∉ I, ν i = 0 := fun i hi ↦ by
    simpa [hi] using congrFun hcons i
  -- (c) sign of the multiplier derivative on the weakly active constraints
  have hν0 : ∀ i, lam₀ i = 0 → 0 ≤ ν i := by
    intro i hi
    have hlim : Tendsto (fun t : ℝ ↦ -(t⁻¹ * ((ψ (x₀ + t • r)).2 i - lam₀ i))) (𝓝[>] 0)
        (𝓝 (-ν i)) :=
      ((((continuous_apply i).comp continuous_snd).tendsto _).comp hslope).neg.congr
        fun t ↦ by simp
    have := nonpos_of_tendsto_of_frequently hlim (hfreq.mono fun t ⟨ht, _, _, lam, hk, he⟩ ↦ by
      rw [he, hi, sub_zero, neg_nonpos]
      exact mul_nonneg (inv_nonneg.2 ht.le) (hk.2.1 i))
    linarith
  -- (d) `d` is feasible for `QP(λ⁰, r)`
  have hfeas : d ∈ lowerQPFeasible g x₀ y₀ lam₀ r := by
    refine ⟨fun i hi ↦ hcI i (hJI i hi), fun i hi ↦ ?_⟩
    by_cases hiI : i ∈ I
    · exact (hcI i hiI).le
    have hfst : HasDerivAt (fun t : ℝ ↦ (ψ (x₀ + t • r)).1) d 0 :=
      (ContinuousLinearMap.fst ℝ F (ι → ℝ)).hasFDerivAt.comp_hasDerivAt 0 hline
    have hpath : HasDerivAt (fun t : ℝ ↦ (x₀ + t • r, (ψ (x₀ + t • r)).1)) (r, d) 0 :=
      hl.prodMk hfst
    have hgi : HasDerivAt (fun t : ℝ ↦ g i (x₀ + t • r, (ψ (x₀ + t • r)).1))
        (fderiv ℝ (g i) (x₀, y₀) (r, d)) 0 :=
      (hdg i _).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp [hψ₀])
    refine nonpos_of_tendsto_of_frequently
      (f := fun t ↦ t⁻¹ * g i (x₀ + t • r, (ψ (x₀ + t • r)).1))
      (hgi.tendsto_slope_zero_right.congr fun t ↦ by simp [hψ₀, hi]) ?_
    exact hfreq.mono fun t ⟨ht, _, _, lam, hk, he⟩ ↦ by
      simp only [he]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht.le) (hk.1 i)
  -- (e) `d` is the unique optimal solution of `QP(λ⁰, r)`
  refine ⟨d, hv, hfeas, fun d' hd' hne ↦ ?_⟩
  set e := d' - d with he
  have he0 : e ≠ 0 := sub_ne_zero.2 hne
  have hDe : ∀ i, fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ e =
      fderiv ℝ (g i) (x₀, y₀) (r, d') - fderiv ℝ (g i) (x₀, y₀) (r, d) := fun i ↦ by
    rw [← map_sub, fderiv_apply_sub_section (hdg i _)]
  have hHe : 0 < lowerHessian φ g x₀ y₀ lam₀ e e := hssoc lam₀ hkkt e he0 fun i hi ↦ by
    rw [hDe, hd'.1 i hi, hcI i (hJI i hi), sub_self]
  have hsum : ∑ i, ν i * fderiv ℝ (fun z ↦ g i (x₀, z)) y₀ e ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ by
      by_cases hiI : i ∈ I
      · rw [hDe, hcI i hiI, sub_zero]
        rcases (hkkt.2.1 i).eq_or_lt with h | h
        · exact mul_nonpos_of_nonneg_of_nonpos (hν0 i h.symm) (hd'.2 i (hIA i hiI))
        · rw [hd'.1 i h, mul_zero]
      · rw [hνI i hiI, zero_mul]
  have hge := congrArg (fun T : StrongDual ℝ F ↦ T e) hgrad
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at hge
  have hd'e : d' = d + e := by rw [he, add_sub_cancel]
  have hsymm := lowerHessian_symm hφ hg x₀ y₀ lam₀ d e
  simp only [lowerQPObjective]
  rw [hd'e]
  simp only [map_add, add_apply]
  linarith

end Bilevel
