/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.MPCC
import BilevelOptimization.Parametric

/-!
# Optimality conditions using the KKT reformulation

Sect. 5.5 of [Dempe 2002]: necessary optimality conditions for the nonsmooth KKT reformulation
(5.27)

`min f(x, y)` subject to `hⱼ(x) ≤ 0`, `∇_y L(x, y, λ) = 0`, `min {-gᵢ(x, y), λᵢ} = 0`

of the bilevel problem, where `L(x, y, λ) = φ(x, y) + ∑ λᵢ gᵢ(x, y)`. By `isLowerKKT_iff_min` its
feasible set is `kktFeasible φ g {x | ∀ j, h j x ≤ 0}`, the feasible set of (5.26).

## Main definitions

* `lowerStationarity φ g w`: the function `(x, y, λ) ↦ ∇_y L(x, y, λ) w`.
* `lagrangianSecondDeriv φ g q w`: the derivative of `(x, y) ↦ ∇_y L(x, y, λ) w` at `q = (x, y, λ)`,
  written `∇(∇ₓL(z⁰, ν⁰) ω)` in the book.
* `TightenedMFCQ φ g h q₀`: (MFCQ) for the tightened problem (5.30) at `q₀`.
* `TightenedSMFCQ φ g h q₀ κ`: (SMFCQ) for (5.30) at `q₀`, relative to the multiplier `κ` of the
  leader's constraints.

## Main results

* `exists_fritzJohn_kktReformulation`: Thm. 5.16 of [Dempe 2002] (Fritz John conditions (5.29)).
* `exists_kkt_kktReformulation`: Thm. 5.17, first part: under (MFCQ) for (5.30) the leading
  multiplier is `1` (conditions (5.34)).
* `nonneg_and_unique_kktReformulation`: Thm. 5.17, second part: under (SMFCQ) for (5.30) the
  multipliers are unique and `ζᵢ ≥ 0`, `ξᵢ ≥ 0` for the biactive indices (conditions (5.35)).

## Notation

Leader variable `x ∈ E`, follower variable `y ∈ F` (the book uses `y` for the leader); the book's
`F`, `f`, `g`, `G` are `f`, `φ`, `g`, `h` here, and the follower has no equality constraints, so
the multiplier `τ` does not appear. The multiplier `ω` of the stationarity condition is a vector
of `F`.

## Remarks on the book

* The conditions `ζᵢ ξᵢ ≥ 0` hold for all `i`, not only for the biactive indices `K`: outside `K`
  one of `ζᵢ`, `ξᵢ` vanishes by complementary slackness.
* The follower's data are assumed `C²` at `(x⁰, y⁰)`, so that the stationarity condition is
  strictly differentiable.
* (MFCQ) for (5.30) is stated without coordinates: linear independence of the gradients of the
  equality constraints is injectivity of the adjoint map `(ω, ζ, ξ) ↦ …`, where
  `ξᵢ = ∇_y gᵢ(x⁰, y⁰) ω` is determined by `ω`.
-/

open Filter Topology Set
open ContinuousLinearMap (fst snd inr)

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι J : Type*} [Fintype ι] [Fintype J] {f φ : E × F → ℝ} {g : ι → E × F → ℝ} {h : J → E → ℝ}
  {q q₀ : (E × F) × (ι → ℝ)}

section Definitions

/-- The derivative of `p ↦ ∇_y ψ(p) w` at `p`, i.e. `d ↦ ∇²ψ(p) d (0, w)`. -/
noncomputable def secondDerivApply (ψ : E × F → ℝ) (p : E × F) (w : F) : StrongDual ℝ (E × F) :=
  (ContinuousLinearMap.apply ℝ ℝ ((0 : E), w)).comp (fderiv ℝ (fderiv ℝ ψ) p)

variable (φ g)

/-- The function `(x, y, λ) ↦ ∇_y L(x, y, λ) w`, with the follower's Lagrangian
`L(x, y, λ) = φ(x, y) + ∑ λᵢ gᵢ(x, y)`. -/
noncomputable def lowerStationarity (w : F) (q : (E × F) × (ι → ℝ)) : ℝ :=
  fderiv ℝ φ q.1 (0, w) + ∑ i, q.2 i * fderiv ℝ (g i) q.1 (0, w)

/-- The derivative of `(x, y) ↦ ∇_y L(x, y, λ) w` at `q = (x, y, λ)`: the term
`∇(∇ₓL(z⁰, ν⁰) ω)` of (5.29) in [Dempe 2002]. -/
noncomputable def lagrangianSecondDeriv (q : (E × F) × (ι → ℝ)) (w : F) : StrongDual ℝ (E × F) :=
  secondDerivApply φ q.1 w + ∑ i, q.2 i • secondDerivApply (g i) q.1 w

/-- The derivative of `lowerStationarity φ g w` at `q`. -/
noncomputable def lowerStationarityDeriv (q : (E × F) × (ι → ℝ)) (w : F) :
    StrongDual ℝ ((E × F) × (ι → ℝ)) :=
  (secondDerivApply φ q.1 w).comp (fst ℝ (E × F) (ι → ℝ)) +
    ∑ i, (q.2 i • (secondDerivApply (g i) q.1 w).comp (fst ℝ (E × F) (ι → ℝ)) +
      fderiv ℝ (g i) q.1 (0, w) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (snd ℝ (E × F) (ι → ℝ)))

variable (h) in
/-- (MFCQ) at `q₀ = (x⁰, y⁰, λ⁰)` for the tightened problem (5.30) of [Dempe 2002], with equality
constraints `∇_y L = 0`, `gᵢ = 0` (`gᵢ(x⁰, y⁰) = 0`), `λᵢ = 0` (`λᵢ⁰ = 0`) and active inequality
constraints `hⱼ ≤ 0`: the gradients of the equality constraints are linearly independent, and
some direction `(d, γ)` in `(x, y, λ)` is tangent to them and has `∇hⱼ(x⁰) d < 0` for the active
`j` ((5.70)–(5.72)). -/
def TightenedMFCQ (q₀ : (E × F) × (ι → ℝ)) : Prop :=
  (∀ (ω : F) (ζ : ι → ℝ), (∀ i, ζ i * g i q₀.1 = 0) →
      (∀ i, fderiv ℝ (g i) q₀.1 (0, ω) * q₀.2 i = 0) →
      lagrangianSecondDeriv φ g q₀ ω + ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0 → ω = 0 ∧ ζ = 0) ∧
    ∃ (d : E × F) (γ : ι → ℝ),
      (∀ w : F, lagrangianSecondDeriv φ g q₀ w d + ∑ i, γ i * fderiv ℝ (g i) q₀.1 (0, w) = 0) ∧
      (∀ i, g i q₀.1 = 0 → fderiv ℝ (g i) q₀.1 d = 0) ∧ (∀ i, q₀.2 i = 0 → γ i = 0) ∧
      ∀ j, h j q₀.1.1 = 0 → fderiv ℝ (h j) q₀.1.1 d.1 < 0

variable (h) in
/-- (SMFCQ) at `q₀ = (x⁰, y⁰, λ⁰)` for the tightened problem (5.30) of [Dempe 2002], relative to
a multiplier `κ ≥ 0` of the constraints `hⱼ ≤ 0`: the gradients of the equality constraints and
of the `hⱼ` with `κⱼ > 0` are linearly independent, and some direction `(d, γ)` is tangent to
them and has `∇hⱼ(x⁰) d < 0` for the active `j` with `κⱼ = 0` ((5.33) for (5.30)). -/
def TightenedSMFCQ (q₀ : (E × F) × (ι → ℝ)) (κ : J → ℝ) : Prop :=
  (∀ (κ' : J → ℝ) (ω : F) (ζ : ι → ℝ), (∀ j, κ j = 0 → κ' j = 0) →
      (∀ i, ζ i * g i q₀.1 = 0) → (∀ i, fderiv ℝ (g i) q₀.1 (0, ω) * q₀.2 i = 0) →
      ∑ j, κ' j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) + lagrangianSecondDeriv φ g q₀ ω +
        ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0 → κ' = 0 ∧ ω = 0 ∧ ζ = 0) ∧
    ∃ (d : E × F) (γ : ι → ℝ),
      (∀ w : F, lagrangianSecondDeriv φ g q₀ w d + ∑ i, γ i * fderiv ℝ (g i) q₀.1 (0, w) = 0) ∧
      (∀ i, g i q₀.1 = 0 → fderiv ℝ (g i) q₀.1 d = 0) ∧ (∀ i, q₀.2 i = 0 → γ i = 0) ∧
      (∀ j, 0 < κ j → fderiv ℝ (h j) q₀.1.1 d.1 = 0) ∧
      ∀ j, h j q₀.1.1 = 0 → κ j = 0 → fderiv ℝ (h j) q₀.1.1 d.1 < 0

end Definitions

/-! ### The stationarity condition as a smooth constraint -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem secondDerivApply_apply (ψ : E × F → ℝ) (p : E × F) (w : F) (d : E × F) :
    secondDerivApply ψ p w d = fderiv ℝ (fderiv ℝ ψ) p d (0, w) :=
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasStrictFDerivAt_fderiv_apply {ψ : E × F → ℝ} {p : E × F} (hψ : ContDiffAt ℝ 2 ψ p)
    (w : F) : HasStrictFDerivAt (fun p' ↦ fderiv ℝ ψ p' (0, w)) (secondDerivApply ψ p w) p :=
  (ContinuousLinearMap.apply ℝ ℝ ((0 : E), w)).hasStrictFDerivAt.comp p
    ((hψ.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt one_ne_zero)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem hasStrictFDerivAt_lowerStationarity (hφ : ContDiffAt ℝ 2 φ q₀.1)
    (hg : ∀ i, ContDiffAt ℝ 2 (g i) q₀.1) (w : F) :
    HasStrictFDerivAt (lowerStationarity φ g w) (lowerStationarityDeriv φ g q₀ w) q₀ :=
  ((hasStrictFDerivAt_fderiv_apply hφ w).comp q₀ hasStrictFDerivAt_fst).add
    (HasStrictFDerivAt.fun_sum fun i _ ↦ (hasStrictFDerivAt_multiplier_kkt i).mul
      ((hasStrictFDerivAt_fderiv_apply (hg i) w).comp q₀ hasStrictFDerivAt_fst))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `lowerStationarity` in terms of the partial derivatives used in `IsLowerKKT`. -/
theorem lowerStationarity_eq (hφ : DifferentiableAt ℝ φ q.1)
    (hg : ∀ i, DifferentiableAt ℝ (g i) q.1) (w : F) :
    lowerStationarity φ g w q = (fderiv ℝ (fun z ↦ φ (q.1.1, z)) q.1.2 +
      ∑ i, q.2 i • fderiv ℝ (fun z ↦ g i (q.1.1, z)) q.1.2) w := by
  have hφ' : DifferentiableAt ℝ φ (q.1.1, q.1.2) := hφ
  have hg' : ∀ i, DifferentiableAt ℝ (g i) (q.1.1, q.1.2) := hg
  simp [lowerStationarity, fderiv_section hφ', fun i ↦ fderiv_section (hg' i)]

omit [FiniteDimensional ℝ E] [Fintype J] in
/-- Where the follower's data are differentiable, the feasible set of the KKT reformulation is
that of a program with complementarity constraints, the stationarity condition being tested on a
basis of `F`. -/
theorem mem_kktFeasible_iff_mem_mpccFeasible (hφ : DifferentiableAt ℝ φ q.1)
    (hg : ∀ i, DifferentiableAt ℝ (g i) q.1) :
    q ∈ kktFeasible φ g {x | ∀ j, h j x ≤ 0} ↔
      q ∈ mpccFeasible (fun j (r : (E × F) × (ι → ℝ)) ↦ h j r.1.1)
        (fun k ↦ lowerStationarity φ g (Module.finBasis ℝ F k)) (fun i r ↦ g i r.1)
        (fun i r ↦ r.2 i) := by
  have hst : (∀ k, lowerStationarity φ g (Module.finBasis ℝ F k) q = 0) ↔
      fderiv ℝ (fun z ↦ φ (q.1.1, z)) q.1.2 +
        ∑ i, q.2 i • fderiv ℝ (fun z ↦ g i (q.1.1, z)) q.1.2 = 0 := by
    simp only [lowerStationarity_eq hφ hg]
    constructor
    · intro hk
      exact ContinuousLinearMap.coe_injective
        ((Module.finBasis ℝ F).ext fun k ↦ by simpa using hk k)
    · intro h0 k
      rw [h0]
      rfl
  constructor
  · rintro ⟨hΩ, hK⟩
    obtain ⟨hm, hs⟩ := isLowerKKT_iff_min.1 hK
    exact ⟨hΩ, hst.2 hs, hm⟩
  · rintro ⟨hG, hH, hm⟩
    exact ⟨hG, isLowerKKT_iff_min.2 ⟨hm, hst.1 hH⟩⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype J] in
private theorem sum_mul_add_sum {κ : Type*} [Fintype κ] (μ A : κ → ℝ) (l γ : ι → ℝ)
    (B C : κ → ι → ℝ) :
    ∑ k, μ k * (A k + ∑ i, (l i * B k i + C k i * γ i)) =
      ∑ k, μ k * A k + ∑ i, ∑ k, l i * (μ k * B k i) + ∑ i, ∑ k, μ k * C k i * γ i := by
  have e : ∀ k, μ k * (A k + ∑ i, (l i * B k i + C k i * γ i)) =
      μ k * A k + ∑ i, l i * (μ k * B k i) + ∑ i, μ k * C k i * γ i := fun k ↦ by
    rw [mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [Finset.sum_congr rfl fun k _ ↦ e k]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k i ↦ l i * (μ k * B k i)),
    Finset.sum_comm (f := fun k i ↦ μ k * C k i * γ i)]

omit [FiniteDimensional ℝ E] in
/-- The multiplier combination of the gradients of the constraints of (5.27) in `(x, y, λ)`,
split into its `(x, y)` part and its `λ` part; `ω = ∑ μₖ bₖ` for the basis `b` of `F`. -/
theorem kkt_multiplier_sum_apply (κ₀ : ℝ) (κ : J → ℝ) (μ : Fin (Module.finrank ℝ F) → ℝ)
    (ζ ξ : ι → ℝ) (r : (E × F) × (ι → ℝ)) :
    (κ₀ • (fderiv ℝ f q₀.1).comp (fst ℝ (E × F) (ι → ℝ)) +
      ∑ j, κ j • ((fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F)).comp (fst ℝ (E × F) (ι → ℝ)) +
      ∑ k, μ k • lowerStationarityDeriv φ g q₀ (Module.finBasis ℝ F k) +
      ∑ i, ζ i • (fderiv ℝ (g i) q₀.1).comp (fst ℝ (E × F) (ι → ℝ)) -
      ∑ i, ξ i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (snd ℝ (E × F) (ι → ℝ))) r =
    (κ₀ • fderiv ℝ f q₀.1 + ∑ j, κ j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
      lagrangianSecondDeriv φ g q₀ (∑ k, μ k • Module.finBasis ℝ F k) +
      ∑ i, ζ i • fderiv ℝ (g i) q₀.1) r.1 +
    ∑ i, (fderiv ℝ (g i) q₀.1 (0, ∑ k, μ k • Module.finBasis ℝ F k) - ξ i) * r.2 i := by
  have hlin : ∀ T : StrongDual ℝ (E × F), T (0, ∑ k, μ k • Module.finBasis ℝ F k) =
      ∑ k, μ k * T (0, Module.finBasis ℝ F k) := fun T ↦ by
    show (T.comp (inr ℝ E F)) (∑ k, μ k • Module.finBasis ℝ F k) =
      ∑ k, μ k * (T.comp (inr ℝ E F)) (Module.finBasis ℝ F k)
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  simp only [lowerStationarityDeriv, lagrangianSecondDeriv, secondDerivApply_apply,
    add_apply, sub_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply, smul_eq_mul, hlin,
    sum_mul_add_sum, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- A multiplier combination of the constraint gradients of (5.27) vanishes iff its `(x, y)` part
vanishes and `ξᵢ = ∇_y gᵢ ω`. -/
theorem kkt_multiplier_sum_eq_zero_iff (κ₀ : ℝ) (κ : J → ℝ) (μ : Fin (Module.finrank ℝ F) → ℝ)
    (ζ ξ : ι → ℝ) :
    κ₀ • (fderiv ℝ f q₀.1).comp (fst ℝ (E × F) (ι → ℝ)) +
      ∑ j, κ j • ((fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F)).comp (fst ℝ (E × F) (ι → ℝ)) +
      ∑ k, μ k • lowerStationarityDeriv φ g q₀ (Module.finBasis ℝ F k) +
      ∑ i, ζ i • (fderiv ℝ (g i) q₀.1).comp (fst ℝ (E × F) (ι → ℝ)) -
      ∑ i, ξ i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (snd ℝ (E × F) (ι → ℝ)) = 0 ↔
    κ₀ • fderiv ℝ f q₀.1 + ∑ j, κ j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
      lagrangianSecondDeriv φ g q₀ (∑ k, μ k • Module.finBasis ℝ F k) +
      ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0 ∧
    ∀ i, fderiv ℝ (g i) q₀.1 (0, ∑ k, μ k • Module.finBasis ℝ F k) = ξ i := by
  classical
  constructor
  · intro hsum
    have happ := fun r ↦ (kkt_multiplier_sum_apply (f := f) (φ := φ) (g := g) (h := h) (q₀ := q₀)
      κ₀ κ μ ζ ξ r).symm.trans (by rw [hsum])
    refine ⟨ContinuousLinearMap.ext fun d ↦ ?_, fun i ↦ ?_⟩
    · have := happ (d, 0)
      simpa using this
    · have := happ (0, Pi.single i 1)
      simp only [map_zero, zero_add, zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun hi ↦ absurd (Finset.mem_univ i) hi), Pi.single_eq_same, mul_one] at this
      linarith
  · rintro ⟨h1, h2⟩
    refine ContinuousLinearMap.ext fun r ↦ ?_
    rw [kkt_multiplier_sum_apply, h1]
    simp [h2]

omit [FiniteDimensional ℝ E] [Fintype J] in
/-- A local solution of the KKT reformulation is a local solution of the corresponding program
with complementarity constraints. -/
theorem isLocalMinOn_mpccFeasible_of_kktFeasible
    (hq₀ : q₀ ∈ kktFeasible φ g {x | ∀ j, h j x ≤ 0})
    (hmin : IsLocalMinOn (fun q : (E × F) × (ι → ℝ) ↦ f q.1)
      (kktFeasible φ g {x | ∀ j, h j x ≤ 0}) q₀)
    (hφ : ContDiffAt ℝ 2 φ q₀.1) (hg : ∀ i, ContDiffAt ℝ 2 (g i) q₀.1) :
    q₀ ∈ mpccFeasible (fun j (r : (E × F) × (ι → ℝ)) ↦ h j r.1.1)
        (fun k ↦ lowerStationarity φ g (Module.finBasis ℝ F k)) (fun i r ↦ g i r.1)
        (fun i r ↦ r.2 i) ∧
      IsLocalMinOn (fun q : (E × F) × (ι → ℝ) ↦ f q.1)
        (mpccFeasible (fun j (r : (E × F) × (ι → ℝ)) ↦ h j r.1.1)
          (fun k ↦ lowerStationarity φ g (Module.finBasis ℝ F k)) (fun i r ↦ g i r.1)
          (fun i r ↦ r.2 i)) q₀ := by
  have hφd : DifferentiableAt ℝ φ q₀.1 := hφ.differentiableAt two_ne_zero
  have hgd : ∀ i, DifferentiableAt ℝ (g i) q₀.1 := fun i ↦ (hg i).differentiableAt two_ne_zero
  refine ⟨(mem_kktFeasible_iff_mem_mpccFeasible (h := h) hφd hgd).1 hq₀, ?_⟩
  -- near `q₀` the two feasible sets coincide
  have hev : ∀ᶠ q : (E × F) × (ι → ℝ) in 𝓝 q₀,
      DifferentiableAt ℝ φ q.1 ∧ ∀ i, DifferentiableAt ℝ (g i) q.1 := by
    have h1 : ∀ᶠ p in 𝓝 q₀.1, DifferentiableAt ℝ φ p ∧ ∀ i, DifferentiableAt ℝ (g i) p :=
      ((hφ.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt two_ne_zero).and
        (eventually_all.2 fun i ↦ ((hg i).eventually (by simp)).mono fun p hp ↦
          hp.differentiableAt two_ne_zero)
    exact continuous_fst.continuousAt.eventually h1
  refine eventually_nhdsWithin_iff.2 ?_
  filter_upwards [eventually_nhdsWithin_iff.1 hmin, hev] with q hq hd hqm
  exact hq ((mem_kktFeasible_iff_mem_mpccFeasible hd.1 hd.2).2 hqm)

/-! ### Fritz John and KKT conditions -/

/-- Thm. 5.16 of [Dempe 2002]: if `(x⁰, y⁰, λ⁰)` is a local solution of the nonsmooth KKT
reformulation (5.27), with `f`, `hⱼ` of class `C¹` and `φ`, `gᵢ` of class `C²` at the point, then
there are `κ₀ ∈ {0, 1}`, `κ ≥ 0`, `ω ∈ F`, `ζ`, `ξ`, not all zero, satisfying (5.29):
`κ₀ ∇f + ∑ κⱼ (∇hⱼ, 0) + ∇(∇_y L ω) + ∑ ζᵢ ∇gᵢ = 0`, `∇_y gᵢ ω = ξᵢ`, `κⱼ hⱼ = 0`, `ζᵢ gᵢ = 0`,
`ξᵢ λᵢ⁰ = 0` and `ζᵢ ξᵢ ≥ 0`. -/
theorem exists_fritzJohn_kktReformulation (hq₀ : q₀ ∈ kktFeasible φ g {x | ∀ j, h j x ≤ 0})
    (hmin : IsLocalMinOn (fun q : (E × F) × (ι → ℝ) ↦ f q.1)
      (kktFeasible φ g {x | ∀ j, h j x ≤ 0}) q₀)
    (hf : ContDiffAt ℝ 1 f q₀.1) (hh : ∀ j, ContDiffAt ℝ 1 (h j) q₀.1.1)
    (hφ : ContDiffAt ℝ 2 φ q₀.1) (hg : ∀ i, ContDiffAt ℝ 2 (g i) q₀.1) :
    ∃ κ₀ : ℝ, ∃ κ : J → ℝ, ∃ ω : F, ∃ ζ ξ : ι → ℝ, (κ₀ = 0 ∨ κ₀ = 1) ∧ (∀ j, 0 ≤ κ j) ∧
      (∀ j, κ j * h j q₀.1.1 = 0) ∧ (∀ i, ζ i * g i q₀.1 = 0) ∧ (∀ i, ξ i * q₀.2 i = 0) ∧
      (∀ i, 0 ≤ ζ i * ξ i) ∧ (κ₀, κ, ω, ζ, ξ) ≠ 0 ∧
      κ₀ • fderiv ℝ f q₀.1 + ∑ j, κ j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
        lagrangianSecondDeriv φ g q₀ ω + ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0 ∧
      ∀ i, fderiv ℝ (g i) q₀.1 (0, ω) = ξ i := by
  obtain ⟨hz₀, hmin'⟩ := isLocalMinOn_mpccFeasible_of_kktFeasible hq₀ hmin hφ hg
  obtain ⟨κ₀, κ, μ, ζ, ξ, hκ₀, hκ, hcs, hζ, hξ, hprod, hne, hsum⟩ :=
    exists_fritzJohn_mpcc hz₀ hmin'
      ((hf.hasStrictFDerivAt one_ne_zero).comp q₀ hasStrictFDerivAt_fst)
      (fun j ↦ (((hh j).hasStrictFDerivAt one_ne_zero).comp q₀.1 hasStrictFDerivAt_fst).comp q₀
        hasStrictFDerivAt_fst)
      (fun k ↦ hasStrictFDerivAt_lowerStationarity hφ hg (Module.finBasis ℝ F k))
      (hasStrictFDerivAt_comp_fst_kkt fun i ↦ (hg i).of_le one_le_two)
      hasStrictFDerivAt_multiplier_kkt
  obtain ⟨hsum', hξω⟩ := (kkt_multiplier_sum_eq_zero_iff κ₀ κ μ ζ ξ).1 hsum
  refine ⟨κ₀, κ, ∑ k, μ k • Module.finBasis ℝ F k, ζ, ξ, hκ₀, hκ, hcs, hζ, hξ, hprod, ?_, hsum',
    hξω⟩
  intro h0
  simp only [Prod.mk_eq_zero] at h0
  obtain ⟨h1, h2, h3, h4, h5⟩ := h0
  apply hne
  simp only [Prod.mk_eq_zero]
  exact ⟨h1, h2, funext fun k ↦
    Fintype.linearIndependent_iff.1 (Module.finBasis ℝ F).linearIndependent μ h3 k, h4, h5⟩

/-- Thm. 5.17 of [Dempe 2002], first part: if in addition (MFCQ) holds for the tightened problem
(5.30), then the conditions of Thm. 5.16 hold with leading multiplier `1` (conditions (5.34)). -/
theorem exists_kkt_kktReformulation (hq₀ : q₀ ∈ kktFeasible φ g {x | ∀ j, h j x ≤ 0})
    (hmin : IsLocalMinOn (fun q : (E × F) × (ι → ℝ) ↦ f q.1)
      (kktFeasible φ g {x | ∀ j, h j x ≤ 0}) q₀)
    (hf : ContDiffAt ℝ 1 f q₀.1) (hh : ∀ j, ContDiffAt ℝ 1 (h j) q₀.1.1)
    (hφ : ContDiffAt ℝ 2 φ q₀.1) (hg : ∀ i, ContDiffAt ℝ 2 (g i) q₀.1)
    (hcq : TightenedMFCQ φ g h q₀) :
    ∃ κ : J → ℝ, ∃ ω : F, ∃ ζ ξ : ι → ℝ, (∀ j, 0 ≤ κ j) ∧
      (∀ j, κ j * h j q₀.1.1 = 0) ∧ (∀ i, ζ i * g i q₀.1 = 0) ∧ (∀ i, ξ i * q₀.2 i = 0) ∧
      (∀ i, 0 ≤ ζ i * ξ i) ∧
      fderiv ℝ f q₀.1 + ∑ j, κ j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
        lagrangianSecondDeriv φ g q₀ ω + ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0 ∧
      ∀ i, fderiv ℝ (g i) q₀.1 (0, ω) = ξ i := by
  obtain ⟨κ₀, κ, ω, ζ, ξ, hκ₀ | hκ₀, hκ, hcs, hζ, hξ, hprod, hne, hsum, hξω⟩ :=
    exists_fritzJohn_kktReformulation hq₀ hmin hf hh hφ hg
  · exfalso
    subst hκ₀
    obtain ⟨hli, d, γ, hd, hdg, hγ, hdh⟩ := hcq
    rw [zero_smul, zero_add] at hsum
    -- test the stationarity condition with the direction `d`
    have e := congrArg (fun T : StrongDual ℝ (E × F) ↦ T d) hsum
    simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, zero_apply] at e
    have e1 : ∑ i, ζ i * fderiv ℝ (g i) q₀.1 d = 0 := Finset.sum_eq_zero fun i _ ↦ by
      rcases mul_eq_zero.1 (hζ i) with h0 | h0
      · rw [h0, zero_mul]
      · rw [hdg i h0, mul_zero]
    have e2 : lagrangianSecondDeriv φ g q₀ ω d = 0 := by
      have e3 : ∑ i, γ i * fderiv ℝ (g i) q₀.1 (0, ω) = 0 := Finset.sum_eq_zero fun i _ ↦ by
        rcases mul_eq_zero.1 (hξ i) with h0 | h0
        · rw [hξω i, h0, mul_zero]
        · rw [hγ i h0, zero_mul]
      have := hd ω
      linarith
    rw [e1, e2, add_zero, add_zero] at e
    have hterm : ∀ j ∈ Finset.univ, κ j * fderiv ℝ (h j) q₀.1.1 d.1 ≤ 0 := fun j _ ↦ by
      rcases mul_eq_zero.1 (hcs j) with h0 | h0
      · rw [h0, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos (hκ j) (hdh j h0).le
    have hκ0 : κ = 0 := funext fun j ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 e j (Finset.mem_univ j)
      rcases mul_eq_zero.1 (hcs j) with h0 | h0
      · exact h0
      · exact (mul_eq_zero.1 this).resolve_right (hdh j h0).ne
    subst hκ0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at hsum
    obtain ⟨hω, hζ0⟩ := hli ω ζ hζ (fun i ↦ by rw [hξω i]; exact hξ i) hsum
    apply hne
    simp only [Prod.mk_eq_zero]
    refine ⟨trivial, trivial, hω, hζ0, funext fun i ↦ ?_⟩
    rw [← hξω i, hω, Prod.mk_zero_zero, map_zero]
    rfl
  · subst hκ₀
    exact ⟨κ, ω, ζ, ξ, hκ, hcs, hζ, hξ, hprod, by simpa using hsum, hξω⟩

/-- Thm. 5.17 of [Dempe 2002], second part: let `(κ, ω, ζ, ξ)` be multipliers of the tightened
problem (5.30) at a local solution of (5.27) (the conditions (5.34) without `ζᵢ ξᵢ ≥ 0`), and let
(SMFCQ) hold for (5.30) relative to `κ`. Then `ζᵢ ≥ 0` and `ξᵢ ≥ 0` for the biactive indices
(conditions (5.35)), and the multipliers are unique. -/
theorem nonneg_and_unique_kktReformulation (hq₀ : q₀ ∈ kktFeasible φ g {x | ∀ j, h j x ≤ 0})
    (hmin : IsLocalMinOn (fun q : (E × F) × (ι → ℝ) ↦ f q.1)
      (kktFeasible φ g {x | ∀ j, h j x ≤ 0}) q₀)
    (hf : ContDiffAt ℝ 1 f q₀.1) (hh : ∀ j, ContDiffAt ℝ 1 (h j) q₀.1.1)
    (hφ : ContDiffAt ℝ 2 φ q₀.1) (hg : ∀ i, ContDiffAt ℝ 2 (g i) q₀.1)
    {κ : J → ℝ} {ω : F} {ζ ξ : ι → ℝ} (hκ : ∀ j, 0 ≤ κ j) (hcs : ∀ j, κ j * h j q₀.1.1 = 0)
    (hζ : ∀ i, ζ i * g i q₀.1 = 0) (hξ : ∀ i, ξ i * q₀.2 i = 0)
    (hsum : fderiv ℝ f q₀.1 + ∑ j, κ j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
      lagrangianSecondDeriv φ g q₀ ω + ∑ i, ζ i • fderiv ℝ (g i) q₀.1 = 0)
    (hξω : ∀ i, fderiv ℝ (g i) q₀.1 (0, ω) = ξ i) (hcq : TightenedSMFCQ φ g h q₀ κ) :
    (∀ i, g i q₀.1 = 0 → q₀.2 i = 0 → 0 ≤ ζ i ∧ 0 ≤ ξ i) ∧
      ∀ (κ' : J → ℝ) (ω' : F) (ζ' ξ' : ι → ℝ), (∀ j, 0 ≤ κ' j) →
        (∀ j, κ' j * h j q₀.1.1 = 0) → (∀ i, ζ' i * g i q₀.1 = 0) → (∀ i, ξ' i * q₀.2 i = 0) →
        fderiv ℝ f q₀.1 + ∑ j, κ' j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
          lagrangianSecondDeriv φ g q₀ ω' + ∑ i, ζ' i • fderiv ℝ (g i) q₀.1 = 0 →
        (∀ i, fderiv ℝ (g i) q₀.1 (0, ω') = ξ' i) → κ' = κ ∧ ω' = ω ∧ ζ' = ζ ∧ ξ' = ξ := by
  obtain ⟨hz₀, hmin'⟩ := isLocalMinOn_mpccFeasible_of_kktFeasible hq₀ hmin hφ hg
  have hrepr : ∀ w : F, ∑ k, (Module.finBasis ℝ F).repr w k • Module.finBasis ℝ F k = w :=
    fun w ↦ (Module.finBasis ℝ F).sum_repr w
  -- multipliers in coordinates with respect to the basis of `F`
  have hW : ∀ (κ' : J → ℝ) (ω' : F) (ζ' ξ' : ι → ℝ), (∀ j, κ' j * h j q₀.1.1 = 0) →
      (∀ i, ζ' i * g i q₀.1 = 0) → (∀ i, ξ' i * q₀.2 i = 0) →
      fderiv ℝ f q₀.1 + ∑ j, κ' j • (fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F) +
        lagrangianSecondDeriv φ g q₀ ω' + ∑ i, ζ' i • fderiv ℝ (g i) q₀.1 = 0 →
      (∀ i, fderiv ℝ (g i) q₀.1 (0, ω') = ξ' i) →
      IsWeakMultiplier (fun j (r : (E × F) × (ι → ℝ)) ↦ h j r.1.1) (fun i r ↦ g i r.1)
        (fun i r ↦ r.2 i) q₀ ((fderiv ℝ f q₀.1).comp (fst ℝ (E × F) (ι → ℝ)))
        (fun j ↦ ((fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F)).comp (fst ℝ (E × F) (ι → ℝ)))
        (fun k ↦ lowerStationarityDeriv φ g q₀ (Module.finBasis ℝ F k))
        (fun i ↦ (fderiv ℝ (g i) q₀.1).comp (fst ℝ (E × F) (ι → ℝ)))
        (fun i ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (snd ℝ (E × F) (ι → ℝ)))
        (κ', fun k ↦ (Module.finBasis ℝ F).repr ω' k, ζ', ξ') :=
    fun κ' ω' ζ' ξ' c1 c2 c3 e1 e2 ↦ by
      refine ⟨c1, c2, c3, ?_⟩
      have := (kkt_multiplier_sum_eq_zero_iff (f := f) (φ := φ) (g := g) (h := h) (q₀ := q₀) 1 κ'
        (fun k ↦ (Module.finBasis ℝ F).repr ω' k) ζ' ξ').2
        ⟨by rw [hrepr, one_smul]; exact e1, by rw [hrepr]; exact e2⟩
      rw [one_smul] at this
      exact this
  -- (SMFCQ) in dual form
  have hreg : ∀ m' : (J → ℝ) × (Fin (Module.finrank ℝ F) → ℝ) × (ι → ℝ) × (ι → ℝ),
      (∀ j, κ j = 0 → 0 ≤ m'.1 j) →
      IsWeakMultiplier (fun j (r : (E × F) × (ι → ℝ)) ↦ h j r.1.1) (fun i r ↦ g i r.1)
        (fun i r ↦ r.2 i) q₀ 0
        (fun j ↦ ((fderiv ℝ (h j) q₀.1.1).comp (fst ℝ E F)).comp (fst ℝ (E × F) (ι → ℝ)))
        (fun k ↦ lowerStationarityDeriv φ g q₀ (Module.finBasis ℝ F k))
        (fun i ↦ (fderiv ℝ (g i) q₀.1).comp (fst ℝ (E × F) (ι → ℝ)))
        (fun i ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (snd ℝ (E × F) (ι → ℝ))) m' → m' = 0 := by
    rintro ⟨κ', μ', ζ', ξ'⟩ hnn ⟨c1, c2, c3, e⟩
    simp only at hnn c1 c2 c3 e
    obtain ⟨e1, e2⟩ := (kkt_multiplier_sum_eq_zero_iff (f := f) (φ := φ) (g := g) (h := h)
      (q₀ := q₀) 0 κ' μ' ζ' ξ').1 (by rw [zero_smul]; exact e)
    rw [zero_smul, zero_add] at e1
    obtain ⟨hli, d, γ, hd, hdg, hγ, hdh0, hdh⟩ := hcq
    -- test the stationarity condition with the direction `d`
    have t := congrArg (fun T : StrongDual ℝ (E × F) ↦ T d) e1
    simp only [add_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, zero_apply] at t
    have t1 : ∑ i, ζ' i * fderiv ℝ (g i) q₀.1 d = 0 := Finset.sum_eq_zero fun i _ ↦ by
      rcases mul_eq_zero.1 (c2 i) with h0 | h0
      · rw [h0, zero_mul]
      · rw [hdg i h0, mul_zero]
    have t2 : lagrangianSecondDeriv φ g q₀ (∑ k, μ' k • Module.finBasis ℝ F k) d = 0 := by
      have t3 : ∑ i, γ i * fderiv ℝ (g i) q₀.1 (0, ∑ k, μ' k • Module.finBasis ℝ F k) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by
          rcases mul_eq_zero.1 (c3 i) with h0 | h0
          · rw [e2 i, h0, mul_zero]
          · rw [hγ i h0, zero_mul]
      have := hd (∑ k, μ' k • Module.finBasis ℝ F k)
      linarith
    rw [t1, t2, add_zero, add_zero] at t
    have hterm : ∀ j ∈ Finset.univ, κ' j * fderiv ℝ (h j) q₀.1.1 d.1 ≤ 0 := fun j _ ↦ by
      rcases (hκ j).lt_or_eq with hpos | hzero
      · rw [hdh0 j hpos, mul_zero]
      · rcases mul_eq_zero.1 (c1 j) with h0 | h0
        · rw [h0, zero_mul]
        · exact mul_nonpos_of_nonneg_of_nonpos (hnn j hzero.symm) (hdh j h0 hzero.symm).le
    have hκ'0 : ∀ j, κ j = 0 → κ' j = 0 := fun j hj ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 t j (Finset.mem_univ j)
      rcases mul_eq_zero.1 (c1 j) with h0 | h0
      · exact h0
      · exact (mul_eq_zero.1 this).resolve_right (hdh j h0 hj).ne
    obtain ⟨a1, a2, a3⟩ := hli κ' _ ζ' hκ'0 c2 (fun i ↦ by rw [e2 i]; exact c3 i) e1
    have hμ' : μ' = 0 := funext fun k ↦
      Fintype.linearIndependent_iff.1 (Module.finBasis ℝ F).linearIndependent μ' a2 k
    have hξ' : ξ' = 0 := funext fun i ↦ by
      rw [← e2 i, a2, Prod.mk_zero_zero, map_zero]
      rfl
    rw [a1, hμ', a3, hξ']
    rfl
  obtain ⟨hnn, huniq⟩ := nonneg_and_unique_of_isWeakMultiplier hz₀ hmin'
    ((hf.hasStrictFDerivAt one_ne_zero).comp q₀ hasStrictFDerivAt_fst)
    (fun j ↦ (((hh j).hasStrictFDerivAt one_ne_zero).comp q₀.1 hasStrictFDerivAt_fst).comp q₀
      hasStrictFDerivAt_fst)
    (fun k ↦ hasStrictFDerivAt_lowerStationarity hφ hg (Module.finBasis ℝ F k))
    (hasStrictFDerivAt_comp_fst_kkt fun i ↦ (hg i).of_le one_le_two)
    hasStrictFDerivAt_multiplier_kkt (hW κ ω ζ ξ hcs hζ hξ hsum hξω) hreg
  refine ⟨fun i hgi hvi ↦ hnn i hgi hvi, fun κ' ω' ζ' ξ' c0 c1 c2 c3 e1 e2 ↦ ?_⟩
  have := huniq _ (hW κ' ω' ζ' ξ' c1 c2 c3 e1 e2) c0
  simp only [Prod.mk.injEq] at this
  obtain ⟨u1, u2, u3, u4⟩ := this
  refine ⟨u1, ?_, u3, u4⟩
  rw [← hrepr ω', ← hrepr ω]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [congrFun u2 k]

end Bilevel
