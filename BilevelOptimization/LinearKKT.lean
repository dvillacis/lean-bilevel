/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.LinearBilevel
import BilevelOptimization.MPCC

/-!
# F. John and KKT conditions for linear bilevel problems

Sect. 3.5.1 of [Dempe 2002]. Replacing the follower's LP by its KKT conditions, the optimistic LP–LP
bilevel problem becomes a program with the complementarity constraints
`min {C x + D y - b, λ} = 0` (3.16). Clarke's multiplier rule for this problem gives F. John
conditions in which the multipliers `ζᵢ`, `ξᵢ` of the two parts of the complementarity
constraints have the same sign (Thm. 3.6), and under a generalized Slater condition for the
tightened problem (3.17) the leading multiplier is `1` (Thm. 3.7).

## Main results

* `LinearBilevel.kktMPCC_mem_iff`: the KKT reformulation is a program with complementarity
  constraints and affine data.
* `LinearBilevel.isLocalMinOn_kktFeasible`: a local solution of the bilevel problem gives a local
  solution of the KKT reformulation for every multiplier.
* `LinearBilevel.exists_fritzJohn`: Thm. 3.6.
* `LinearBilevel.TightenedMFCQ`, `LinearBilevel.GeneralizedSlater`,
  `LinearBilevel.GeneralizedSlater.tightenedMFCQ`: Def. 3.2, and the constraint qualification it
  implies at `(x⁰, y⁰, λ⁰)`.
* `LinearBilevel.exists_kkt`: Thm. 3.7.

## Differences from the book

* The follower's problem is `min_y {d y : C x + D y ≥ b}` (the model `LinearBilevel`), with leader's
  constraints `A x + B y ≥ a` that may involve `y`; the book uses
  `min_x {⟨y¹, x⟩ : A¹ x + A² y² ≤ a, x ≥ 0}` with upper-level constraints `A³ y = b`, `y ≥ 0`. Sign
  constraints are rows of `C x + D y ≥ b` here, so the book's pairs `(η¹, γ¹)`, `(η², γ²)` become
  one pair `(ζ, ξ)` indexed by the rows, and the multiplier of `Dᵀ λ = d` is a vector `w ∈ F`
  with `ξᵢ = Dᵢ w`.
* The multipliers are given for every `λ⁰` with `(x⁰, y⁰, λ⁰)` feasible for (3.16), not only for
  some. The F. John multiplier `κ₀` is in `{0, 1}`, and `ζᵢ ξᵢ ≥ 0` holds for all `i`.
* Thm. 3.7 is proved under (MFCQ) for (3.17) in dual form (`TightenedMFCQ`), which the generalized
  Slater condition of Def. 3.2 implies (the constraints are affine).
-/

open Filter Topology Set ContinuousLinearMap

namespace Bilevel

namespace LinearBilevel

variable {E F κ ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (P : LinearBilevel E F κ ι)

/-! ### The KKT reformulation as a program with complementarity constraints -/

section MPCC

variable (E F ι) in
/-- The projection `(x, y, λ) ↦ x`. -/
def πx : ((E × F) × (ι → ℝ)) →L[ℝ] E := (fst ℝ E F).comp (fst ℝ (E × F) (ι → ℝ))

variable (E F ι) in
/-- The projection `(x, y, λ) ↦ y`. -/
def πy : ((E × F) × (ι → ℝ)) →L[ℝ] F := (snd ℝ E F).comp (fst ℝ (E × F) (ι → ℝ))

variable (E F) in
/-- The projection `(x, y, λ) ↦ λᵢ`. -/
def πl (i : ι) : ((E × F) × (ι → ℝ)) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp (snd ℝ (E × F) (ι → ℝ))

@[simp] theorem πx_apply (q : (E × F) × (ι → ℝ)) : πx E F ι q = q.1.1 := rfl
@[simp] theorem πy_apply (q : (E × F) × (ι → ℝ)) : πy E F ι q = q.1.2 := rfl
@[simp] theorem πl_apply (i : ι) (q : (E × F) × (ι → ℝ)) : πl E F i q = q.2 i := rfl

/-- The gradient of the leader's objective in `(x, y, λ)`. -/
def objectiveDeriv : StrongDual ℝ ((E × F) × (ι → ℝ)) :=
  P.cx.comp (πx E F ι) + P.cy.comp (πy E F ι)

/-- The gradient of the leader's constraint `aₖ - Aₖ x - Bₖ y ≤ 0`. -/
def upperDeriv (k : κ) : StrongDual ℝ ((E × F) × (ι → ℝ)) :=
  -(P.A k).comp (πx E F ι) - (P.B k).comp (πy E F ι)

/-- The gradient of the follower's constraint `bᵢ - Cᵢ x - Dᵢ y ≤ 0`. -/
def lowerDeriv (i : ι) : StrongDual ℝ ((E × F) × (ι → ℝ)) :=
  -(P.C i).comp (πx E F ι) - (P.D i).comp (πy E F ι)

variable [Fintype ι] [FiniteDimensional ℝ F]

/-- The gradient of the `k`-th coordinate `(∑ λᵢ Dᵢ - d)(eₖ)` of the dual constraint, for the basis
`e` of `F`. -/
noncomputable def dualDeriv (k : Fin (Module.finrank ℝ F)) : StrongDual ℝ ((E × F) × (ι → ℝ)) :=
  ∑ i, P.D i (Module.finBasis ℝ F k) • πl E F i

/-- The data `G ≤ 0` of the KKT reformulation as a program with complementarity constraints: the
leader's constraints. -/
def mpccG (k : κ) (q : (E × F) × (ι → ℝ)) : ℝ := P.a k + P.upperDeriv k q

/-- The data `H = 0`: the dual constraint `∑ λᵢ Dᵢ = d`, tested on the basis of `F`. -/
noncomputable def mpccH (k : Fin (Module.finrank ℝ F)) (q : (E × F) × (ι → ℝ)) : ℝ :=
  -P.d (Module.finBasis ℝ F k) + P.dualDeriv k q

/-- The data `g ≤ 0` of the complementarity constraints: the follower's constraints. -/
def mpccg (i : ι) (q : (E × F) × (ι → ℝ)) : ℝ := P.b i + P.lowerDeriv i q

/-- The data `v ≥ 0` of the complementarity constraints: the follower's multipliers. -/
def mpccv (i : ι) (q : (E × F) × (ι → ℝ)) : ℝ := q.2 i

omit [Fintype ι] [FiniteDimensional ℝ F] in
theorem mpccG_apply (k : κ) (q : (E × F) × (ι → ℝ)) :
    P.mpccG k q = P.a k - P.A k q.1.1 - P.B k q.1.2 := by
  simp [mpccG, upperDeriv]
  ring

omit [Fintype ι] [FiniteDimensional ℝ F] in
theorem mpccg_apply (i : ι) (q : (E × F) × (ι → ℝ)) : P.mpccg i q = -P.slack i q.1 := by
  simp [mpccg, lowerDeriv, slack]
  ring

theorem mpccH_apply (k : Fin (Module.finrank ℝ F)) (q : (E × F) × (ι → ℝ)) :
    P.mpccH k q = (∑ i, q.2 i • P.D i - P.d) (Module.finBasis ℝ F k) := by
  simp [mpccH, dualDeriv, mul_comm]
  ring

/-- The KKT reformulation of the LP–LP bilevel problem is the program with complementarity
constraints `G ≤ 0`, `H = 0`, `min {-g, v} = 0` (problem (3.16) of [Dempe 2002]). -/
theorem kktMPCC_mem_iff (q : (E × F) × (ι → ℝ)) :
    q ∈ P.kktFeasible ↔ q ∈ mpccFeasible P.mpccG P.mpccH P.mpccg mpccv := by
  have hdual : (∑ i, q.2 i • P.D i = P.d) ↔ ∀ k, P.mpccH k q = 0 := by
    simp only [mpccH_apply]
    constructor
    · intro h k
      rw [h, sub_self, zero_apply]
    · intro h
      have : ∑ i, q.2 i • P.D i - P.d = 0 :=
        ContinuousLinearMap.coe_injective ((Module.finBasis ℝ F).ext fun k ↦ by simpa using h k)
      exact sub_eq_zero.1 this
  simp only [kktFeasible, mpccFeasible, upperFeasible, IsDualFeasible, mem_lowerFeasible_iff,
    mem_ofPred_eq, mpccG_apply, mpccg_apply, neg_neg, mpccv, min_eq_zero_iff, hdual,
    sub_le_iff_le_add, Prod.mk.eta]
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5⟩
    refine ⟨fun k ↦ by linarith [h1 k], h4, fun i ↦ ⟨h2 i, h3 i, by rw [mul_comm]; exact h5 i⟩⟩
  · rintro ⟨h1, h4, h⟩
    exact ⟨fun k ↦ by linarith [h1 k], fun i ↦ (h i).1, ⟨fun i ↦ (h i).2.1, h4⟩,
      fun i ↦ by rw [mul_comm]; exact (h i).2.2⟩

omit [Fintype ι] [FiniteDimensional ℝ F] in
theorem objectiveDeriv_apply (q : (E × F) × (ι → ℝ)) : P.objectiveDeriv q = P.objective q.1 :=
  rfl

/-- A local solution of the LP–LP bilevel problem is a local solution of its KKT reformulation, for
every multiplier `λ`. -/
theorem isLocalMinOn_kktFeasible {p : E × F} (hmin : IsLocalMinOn P.objective P.feasible p)
    (lam : ι → ℝ) : IsLocalMinOn (fun q ↦ P.objective q.1) P.kktFeasible (p, lam) := by
  have h := (continuous_fst.continuousAt (x := (p, lam))).eventually
    (eventually_nhdsWithin_iff.1 hmin)
  refine eventually_nhdsWithin_iff.2 (h.mono fun q hq hqK ↦ hq ?_)
  rw [← P.image_fst_kktFeasible]
  exact ⟨q, hqK, rfl⟩

end MPCC

/-! ### F. John and KKT conditions -/

variable [Fintype κ] [Fintype ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Thm. 3.6 of [Dempe 2002]** (F. John conditions): if `(x⁰, y⁰)` is a local optimistic solution
of the LP–LP bilevel problem and `λ⁰` is a multiplier of the follower's LP at `(x⁰, y⁰)`, there are
`κ₀ ∈ {0, 1}`, `κ ≥ 0`, `w ∈ F`, `ζ`, `ξ`, not all zero, with
`κ₀ cₓ = ∑ κₖ Aₖ + ∑ ζᵢ Cᵢ`, `κ₀ c_y = ∑ κₖ Bₖ + ∑ ζᵢ Dᵢ`, `Dᵢ w = ξᵢ`, complementary slackness
`κₖ (Aₖ x⁰ + Bₖ y⁰ - aₖ) = 0`, `ζᵢ (Cᵢ x⁰ + Dᵢ y⁰ - bᵢ) = 0`, `ξᵢ λᵢ⁰ = 0`, and `ζᵢ ξᵢ ≥ 0`. -/
theorem exists_fritzJohn {p : E × F} {lam : ι → ℝ} (hlam : (p, lam) ∈ P.kktFeasible)
    (hmin : IsLocalMinOn P.objective P.feasible p) :
    ∃ κ₀ : ℝ, ∃ κ' : κ → ℝ, ∃ w : F, ∃ ζ ξ : ι → ℝ, (κ₀ = 0 ∨ κ₀ = 1) ∧ (∀ k, 0 ≤ κ' k) ∧
      (∀ k, κ' k * (P.A k p.1 + P.B k p.2 - P.a k) = 0) ∧ (∀ i, ζ i * P.slack i p = 0) ∧
      (∀ i, ξ i * lam i = 0) ∧ (∀ i, 0 ≤ ζ i * ξ i) ∧ (κ₀, κ', w, ζ, ξ) ≠ 0 ∧
      κ₀ • P.cx = ∑ k, κ' k • P.A k + ∑ i, ζ i • P.C i ∧
      κ₀ • P.cy = ∑ k, κ' k • P.B k + ∑ i, ζ i • P.D i ∧ ∀ i, P.D i w = ξ i := by
  classical
  have hz₀ := (P.kktMPCC_mem_iff _).1 hlam
  have hmin' : IsLocalMinOn (fun q ↦ P.objectiveDeriv q)
      (mpccFeasible P.mpccG P.mpccH P.mpccg mpccv) (p, lam) := by
    have h := P.isLocalMinOn_kktFeasible hmin lam
    have e : P.kktFeasible = mpccFeasible P.mpccG P.mpccH P.mpccg mpccv :=
      Set.ext P.kktMPCC_mem_iff
    rw [e] at h
    exact h
  obtain ⟨κ₀, κ', μ, ζ, ξ, hκ₀, hκ, hcs, hζ, hξ, hprod, hne, hsum⟩ :=
    exists_fritzJohn_mpcc hz₀ hmin' P.objectiveDeriv.hasStrictFDerivAt
      (fun k ↦ (P.upperDeriv k).hasStrictFDerivAt.const_add (P.a k))
      (fun k ↦ (P.dualDeriv k).hasStrictFDerivAt.const_add _)
      (fun i ↦ (P.lowerDeriv i).hasStrictFDerivAt.const_add (P.b i))
      (fun i ↦ (πl E F i).hasStrictFDerivAt)
  have happ := fun z : (E × F) × (ι → ℝ) ↦ congrArg (fun T ↦ T z) hsum
  set w : F := ∑ k, μ k • Module.finBasis ℝ F k
  refine ⟨κ₀, κ', w, ζ, ξ, hκ₀, hκ, fun k ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, hprod, ?_, ?_, ?_,
    fun i ↦ ?_⟩
  · have := hcs k
    rw [mpccG_apply] at this
    linear_combination -this
  · have := hζ i
    rw [mpccg_apply] at this
    linear_combination -this
  · simpa [mpccv] using hξ i
  · intro h0
    simp only [Prod.mk_eq_zero] at h0
    obtain ⟨h1, h2, h3, h4, h5⟩ := h0
    apply hne
    simp only [Prod.mk_eq_zero]
    exact ⟨h1, h2, funext fun k ↦
      Fintype.linearIndependent_iff.1 (Module.finBasis ℝ F).linearIndependent μ h3 k, h4, h5⟩
  · ext r
    have := happ ((r, 0), 0)
    simp [objectiveDeriv, upperDeriv, lowerDeriv, dualDeriv] at this
    simp only [smul_apply, add_apply, sum_apply, smul_eq_mul]
    linarith
  · ext s
    have := happ ((0, s), 0)
    simp [objectiveDeriv, upperDeriv, lowerDeriv, dualDeriv] at this
    simp only [smul_apply, add_apply, sum_apply, smul_eq_mul]
    linarith
  · have := happ ((0, 0), Pi.single i 1)
    simp [objectiveDeriv, upperDeriv, lowerDeriv, dualDeriv, Pi.single_apply] at this
    simp only [w, map_sum, map_smul, smul_eq_mul]
    linarith

/-- (MFCQ) for the tightened problem (3.17) of [Dempe 2002] at `(x⁰, y⁰, λ⁰)`, in dual form: the
gradients of its equality constraints `Cᵢ x + Dᵢ y = bᵢ` (`i` active), `∑ λᵢ Dᵢ = d` and `λᵢ = 0`
(`λᵢ⁰ = 0`) are linearly independent, and some direction `(r, s)` keeps the active follower's
constraints active and enters the interior of the active leader's constraints. -/
def TightenedMFCQ (p : E × F) (lam : ι → ℝ) : Prop :=
  (∀ α : ι → ℝ, (∀ i, α i * P.slack i p = 0) → ∑ i, α i • P.C i = 0 → ∑ i, α i • P.D i = 0 →
    α = 0) ∧
  (∀ w : F, (∀ i, P.D i w * lam i = 0) → w = 0) ∧
  ∃ (r : E) (s : F), (∀ i, P.slack i p = 0 → P.C i r + P.D i s = 0) ∧
    ∀ k, P.A k p.1 + P.B k p.2 = P.a k → 0 < P.A k r + P.B k s

/-- The generalized Slater condition of [Dempe 2002, Def. 3.2] for the tightened problem (3.17) at
`(x⁰, y⁰, λ⁰)`: the gradients of the equality constraints are linearly independent, and some
feasible point of (3.17) satisfies all inequality constraints strictly. -/
def GeneralizedSlater (p : E × F) (lam : ι → ℝ) : Prop :=
  (∀ α : ι → ℝ, (∀ i, α i * P.slack i p = 0) → ∑ i, α i • P.C i = 0 → ∑ i, α i • P.D i = 0 →
    α = 0) ∧
  (∀ w : F, (∀ i, P.D i w * lam i = 0) → w = 0) ∧
  ∃ (x : E) (y : F) (μ : ι → ℝ), (∀ k, P.a k < P.A k x + P.B k y) ∧
    (∀ i, P.slack i p = 0 → P.slack i (x, y) = 0) ∧ (∀ i, 0 < P.slack i p → 0 < P.slack i (x, y)) ∧
    (∀ i, lam i = 0 → μ i = 0) ∧ (∀ i, 0 < lam i → 0 < μ i) ∧ ∑ i, μ i • P.D i = P.d

omit [Fintype κ] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The generalized Slater condition implies (MFCQ) for (3.17): take the direction towards the
Slater point. -/
theorem GeneralizedSlater.tightenedMFCQ {p : E × F} {lam : ι → ℝ}
    (h : P.GeneralizedSlater p lam) : P.TightenedMFCQ p lam := by
  obtain ⟨h1, h2, x, y, -, hup, hact, -, -, -, -⟩ := h
  refine ⟨h1, h2, x - p.1, y - p.2, fun i hi ↦ ?_, fun k hk ↦ ?_⟩
  · have := hact i hi
    simp only [slack] at hi this
    rw [map_sub, map_sub]
    linarith
  · rw [map_sub, map_sub]
    linarith [hup k]

/-- **Thm. 3.7 of [Dempe 2002]** (KKT conditions): if in addition (MFCQ) holds for the tightened
problem (3.17), e.g. under the generalized Slater condition, the conditions of Thm. 3.6 hold with
`κ₀ = 1`. -/
theorem exists_kkt {p : E × F} {lam : ι → ℝ} (hlam : (p, lam) ∈ P.kktFeasible)
    (hmin : IsLocalMinOn P.objective P.feasible p) (hcq : P.TightenedMFCQ p lam) :
    ∃ κ' : κ → ℝ, ∃ w : F, ∃ ζ ξ : ι → ℝ, (∀ k, 0 ≤ κ' k) ∧
      (∀ k, κ' k * (P.A k p.1 + P.B k p.2 - P.a k) = 0) ∧ (∀ i, ζ i * P.slack i p = 0) ∧
      (∀ i, ξ i * lam i = 0) ∧ (∀ i, 0 ≤ ζ i * ξ i) ∧
      P.cx = ∑ k, κ' k • P.A k + ∑ i, ζ i • P.C i ∧
      P.cy = ∑ k, κ' k • P.B k + ∑ i, ζ i • P.D i ∧ ∀ i, P.D i w = ξ i := by
  obtain ⟨κ₀, κ', w, ζ, ξ, hκ₀ | hκ₀, hκ, hcs, hζ, hξ, hprod, hne, hx, hy, hw⟩ :=
    P.exists_fritzJohn hlam hmin
  · exfalso
    subst hκ₀
    obtain ⟨hα, hw0, r, s, hrs, hrsk⟩ := hcq
    rw [zero_smul] at hx hy
    -- test the stationarity conditions with the direction `(r, s)`
    have e := congrArg (fun T ↦ T r) hx.symm
    have e' := congrArg (fun T ↦ T s) hy.symm
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at e e'
    have hζterm : ∀ i, ζ i * (P.C i r + P.D i s) = 0 := fun i ↦ by
      rcases mul_eq_zero.1 (hζ i) with h0 | h0
      · rw [h0, zero_mul]
      · rw [hrs i h0, mul_zero]
    have e2 : ∑ k, κ' k * (P.A k r + P.B k s) = 0 := by
      have : ∑ k, κ' k * (P.A k r + P.B k s) + ∑ i, ζ i * (P.C i r + P.D i s) = 0 := by
        simp only [mul_add, Finset.sum_add_distrib]
        linarith
      rwa [Finset.sum_eq_zero fun i _ ↦ hζterm i, add_zero] at this
    have hterm : ∀ k ∈ Finset.univ, 0 ≤ κ' k * (P.A k r + P.B k s) := fun k _ ↦ by
      rcases mul_eq_zero.1 (hcs k) with h0 | h0
      · rw [h0, zero_mul]
      · exact mul_nonneg (hκ k) (hrsk k (by linarith)).le
    have hκ0 : κ' = 0 := funext fun k ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 e2 k (Finset.mem_univ k)
      rcases mul_eq_zero.1 (hcs k) with h0 | h0
      · exact h0
      · exact (mul_eq_zero.1 this).resolve_right (hrsk k (by linarith)).ne'
    subst hκ0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at hx hy
    have hζ0 := hα ζ hζ hx.symm hy.symm
    have hw' : w = 0 := hw0 w fun i ↦ by rw [hw i]; exact hξ i
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨trivial, trivial, hw', hζ0, funext fun i ↦ ?_⟩
    rw [← hw i, hw', map_zero]
    rfl
  · subst hκ₀
    simp only [one_smul] at hx hy
    exact ⟨κ', w, ζ, ξ, hκ, hcs, hζ, hξ, hprod, hx, hy, hw⟩

end LinearBilevel

end Bilevel
