/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.GeneralizedJacobian
import VariationalAnalysis.Subdifferential.NegConvexHull

/-!
# Pseudodifferentiable functions

Def. 4.11 and Thm. 4.9 of [Dempe 2002] (after Mikhalevich, Gupal, Norkin [206]). A function
`z : E → F` is *pseudodifferentiable* at `x̄` with *pseudodifferential* `Γ` if, near `x̄`, `Γ` is an
upper semicontinuous map with nonempty, convex and compact values in `E →L[ℝ] F` such that
`z(x) = z(x̄) + A (x − x̄) + o(‖x − x̄‖)` uniformly in `A ∈ Γ(x)` (4.16). A continuous selection of
finitely many pseudodifferentiable functions is pseudodifferentiable with
`Γ_z(x) = conv ⋃_{i ∈ I_z(x)} Γ_{zⁱ}(x)` (Thm. 4.9). In particular `C¹` functions
(`Γ(x) = {∇z(x)}`) and `PC¹` functions are pseudodifferentiable; for `PC¹` functions the generalized
Jacobian is a pseudodifferential, and so is it for the local solution function of the follower's
problem under (LICQ) and (SSOC) (the missing part of Cor. 4.1).

## Main results

* `IsPseudodifferential`, `IsPseudodiffAt`: Def. 4.11.
* `isPseudodifferential_iff_tendsto`: the sequential form (4.16) of the approximation property.
* `IsPseudodifferential.exists_norm_sub_le`, `IsPseudodifferential.continuousAt`: calmness and
  continuity at `x̄`.
* `isPseudodifferential_of_contDiffAt`: `C¹` functions, `Γ(x) = {∇z(x)}`.
* `isPseudodifferential_of_selection`: Thm. 4.9.
* `IsPC1Selection.isPseudodifferential`, `IsPC1Selection.isPseudodifferential_clarkeJacobian`:
  `PC¹` functions, with `Γ(x) = conv {∇zⁱ(x) : i ∈ I_z(x)}` or `Γ = ∂z`.
* `isPseudodifferential_of_lowerSSOC`: Cor. 4.1, pseudodifferentiability of the
  local solution function.

## Differences from the book

* Vector-valued functions `z : E → F`, with pseudodifferentials in `E →L[ℝ] F` (the book: scalar
  functions on `ℝᵖ`, row vectors).
* (4.16) is stated in `ε`-`δ` form (as (4.41) in the book's proof of Thm. 4.9);
  `isPseudodifferential_iff_tendsto` gives the sequential form.
* In Thm. 4.9 the functions `zⁱ` are assumed pseudodifferentiable at every point near `x̄` (the
  book leaves this implicit; it is needed for the upper semicontinuity of `Γ_z`); the proof
  handles all `k` at once instead of the book's induction from `k = 2`.
* The results of [206] that pseudodifferentiable functions are locally Lipschitz and that locally
  Lipschitz semismooth functions have the Clarke generalized Jacobian as pseudodifferential are not
  formalized; we prove calmness at `x̄`, and the second statement for `PC¹` functions.
-/

open Filter Topology Set Metric
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Def. 4.11 of [Dempe 2002]**: `Γ` is a pseudodifferential of `z` at `x̄`: near `x̄`, `Γ` has
nonempty, convex and compact values and is upper semicontinuous, and
`‖z(x) − z(x̄) − A (x − x̄)‖ ≤ ε ‖x − x̄‖` for all `A ∈ Γ(x)` and `x` close to `x̄` (4.16). -/
def IsPseudodifferential (z : E → F) (Γ : E → Set (E →L[ℝ] F)) (x₀ : E) : Prop :=
  (∀ᶠ x in 𝓝 x₀, (Γ x).Nonempty ∧ Convex ℝ (Γ x) ∧ IsCompact (Γ x) ∧
      UpperHemicontinuousAt Γ x) ∧
    ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ A ∈ Γ x, ‖z x - z x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖

/-- `z` is pseudodifferentiable at `x̄` [Dempe 2002, Def. 4.11]. -/
def IsPseudodiffAt (z : E → F) (x₀ : E) : Prop :=
  ∃ Γ, IsPseudodifferential z Γ x₀

/-- The approximation property of a pseudodifferential in the sequential form (4.16):
`‖z(xₖ) − z(x̄) − Aₖ (xₖ − x̄)‖ / ‖xₖ − x̄‖ → 0` whenever `xₖ → x̄` and `Aₖ ∈ Γ(xₖ)`. -/
theorem isPseudodifferential_iff_tendsto [FirstCountableTopology E] {z : E → F}
    {Γ : E → Set (E →L[ℝ] F)} {x₀ : E} :
    (∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ A ∈ Γ x, ‖z x - z x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖) ↔
      ∀ (x : ℕ → E) (A : ℕ → E →L[ℝ] F), Tendsto x atTop (𝓝 x₀) → (∀ k, A k ∈ Γ (x k)) →
        Tendsto (fun k ↦ ‖z (x k) - z x₀ - A k (x k - x₀)‖ / ‖x k - x₀‖) atTop (𝓝 0) := by
  constructor
  · intro h x A hx hA
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hx.eventually (h (ε / 2) (half_pos hε))] with k hk
    have hk' := hk (A k) (hA k)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    rcases eq_or_ne (‖x k - x₀‖) 0 with h0 | h0
    · rw [h0, div_zero]
      exact hε
    · rw [div_lt_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
      have := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  · intro h ε hε
    by_contra hne
    rw [not_eventually] at hne
    obtain ⟨x, hx, hbad⟩ := exists_seq_forall_of_frequently hne
    push Not at hbad
    choose A hA hlt using hbad
    have hlim := h x A hx hA
    have hev := (Metric.tendsto_nhds.1 hlim) ε hε
    obtain ⟨k, hk⟩ := hev.exists
    have hpos : 0 < ‖x k - x₀‖ := by
      by_contra h0
      have h0' : ‖x k - x₀‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
      have := hlt k
      rw [h0', mul_zero] at this
      exact absurd this (not_lt.2 (by
        rw [norm_eq_zero.1 h0', map_zero, sub_zero]
        have : x k = x₀ := sub_eq_zero.1 (norm_eq_zero.1 h0')
        rw [this, sub_self, norm_zero]))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hpos] at hk
    exact absurd (hlt k) (not_lt.2 hk.le)

namespace IsPseudodifferential

variable {z : E → F} {Γ : E → Set (E →L[ℝ] F)} {x₀ : E}

/-- A pseudodifferentiable function is calm at `x̄`: `‖z(x) − z(x̄)‖ ≤ C ‖x − x̄‖` near `x̄`. -/
theorem exists_norm_sub_le (h : IsPseudodifferential z Γ x₀) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ‖z x - z x₀‖ ≤ C * ‖x - x₀‖ := by
  obtain ⟨-, -, hc, husc⟩ := h.1.self_of_nhds
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball 0
  have hev := husc _ isOpen_ball hR
  refine ⟨R + 1, ?_⟩
  filter_upwards [hev, h.1, h.2 1 one_pos] with x hx hne hest
  obtain ⟨A, hA⟩ := hne.1
  have hAR : ‖A‖ < R := by simpa using hx hA
  have h1 := hest A hA
  calc ‖z x - z x₀‖ = ‖(z x - z x₀ - A (x - x₀)) + A (x - x₀)‖ := by rw [sub_add_cancel]
    _ ≤ ‖z x - z x₀ - A (x - x₀)‖ + ‖A (x - x₀)‖ := norm_add_le _ _
    _ ≤ 1 * ‖x - x₀‖ + ‖A‖ * ‖x - x₀‖ := add_le_add h1 (A.le_opNorm _)
    _ ≤ (R + 1) * ‖x - x₀‖ := by nlinarith [norm_nonneg (x - x₀)]

/-- A pseudodifferentiable function is continuous at `x̄`. -/
theorem continuousAt (h : IsPseudodifferential z Γ x₀) : ContinuousAt z x₀ := by
  obtain ⟨C, hC⟩ := h.exists_norm_sub_le
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun x ↦ |C| * ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
    simpa using (tendsto_norm_sub_self x₀).const_mul |C|
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hC] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))

/-- A smaller map with the same regularity is again a pseudodifferential. -/
theorem mono (h : IsPseudodifferential z Γ x₀) {Γ' : E → Set (E →L[ℝ] F)}
    (h' : ∀ᶠ x in 𝓝 x₀, (Γ' x).Nonempty ∧ Convex ℝ (Γ' x) ∧ IsCompact (Γ' x) ∧
      UpperHemicontinuousAt Γ' x)
    (hsub : ∀ᶠ x in 𝓝 x₀, Γ' x ⊆ Γ x) : IsPseudodifferential z Γ' x₀ := by
  refine ⟨h', fun ε hε ↦ ?_⟩
  filter_upwards [h.2 ε hε, hsub] with x hx hs A hA using hx A (hs hA)

end IsPseudodifferential

omit [NormedSpace ℝ E] in
/-- Upper semicontinuity of `x ↦ conv ⋃_{i ∈ J(x)} Γᵢ(x)` at `x̄`, if `J(x) ⊆ J(x̄)` near `x̄` and
the `Γᵢ`, `i ∈ J(x̄)`, are upper semicontinuous at `x̄` with compact values. -/
theorem upperHemicontinuousAt_convexHull_biUnion {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] {ι : Type*} [Finite ι] {Γs : ι → E → Set G}
    {J : E → Set ι} {x₀ : E} (hJ : ∀ᶠ x in 𝓝 x₀, J x ⊆ J x₀)
    (husc : ∀ i ∈ J x₀, UpperHemicontinuousAt (Γs i) x₀)
    (hc : ∀ i ∈ J x₀, IsCompact (Γs i x₀)) :
    UpperHemicontinuousAt (fun x ↦ convexHull ℝ (⋃ i ∈ J x, Γs i x)) x₀ := by
  intro W hW hsub
  have hcU : IsCompact (⋃ i ∈ J x₀, Γs i x₀) := (Set.toFinite (J x₀)).isCompact_biUnion hc
  have hK : IsCompact (convexHull ℝ (⋃ i ∈ J x₀, Γs i x₀)) :=
    VariationalAnalysis.isCompact_convexHull_of_isCompact hcU
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open hW hsub
  have hev : ∀ i, ∀ᶠ x in 𝓝 x₀, i ∈ J x₀ → Γs i x ⊆ thickening δ (Γs i x₀) := fun i ↦ by
    by_cases hi : i ∈ J x₀
    · exact (husc i hi _ isOpen_thickening (self_subset_thickening hδ _)).mono fun _ hx _ ↦ hx
    · exact Eventually.of_forall fun _ h ↦ absurd h hi
  have hconv : Convex ℝ (thickening δ (convexHull ℝ (⋃ i ∈ J x₀, Γs i x₀))) :=
    (convex_convexHull ℝ _).thickening δ
  filter_upwards [hJ, eventually_all.2 hev] with x hJx hx
  have hU : (⋃ i ∈ J x, Γs i x) ⊆ thickening δ (convexHull ℝ (⋃ i ∈ J x₀, Γs i x₀)) := by
    refine iUnion₂_subset fun i hi ↦ (hx i (hJx hi)).trans (thickening_subset_of_subset δ ?_)
    have h1 : Γs i x₀ ⊆ ⋃ j ∈ J x₀, Γs j x₀ :=
      subset_biUnion_of_mem (u := fun j ↦ Γs j x₀) (hJx hi)
    exact h1.trans (subset_convexHull ℝ _)
  exact (convexHull_min hU hconv).trans hδW

/-- `C¹` functions are pseudodifferentiable with `Γ(x) = {∇z(x)}` [Dempe 2002, p. 83]. -/
theorem isPseudodifferential_of_contDiffAt {z : E → F} {x₀ : E} (h : ContDiffAt ℝ 1 z x₀) :
    IsPseudodifferential z (fun x ↦ {fderiv ℝ z x}) x₀ := by
  refine ⟨(h.eventually (by simp)).mono fun x hx ↦ ⟨singleton_nonempty _, convex_singleton _,
    isCompact_singleton, fun W hW hsub ↦ ?_⟩, fun ε hε ↦ ?_⟩
  · have hc := hx.continuousAt_fderiv (by simp)
    exact (hc.eventually (hW.mem_nhds (hsub rfl))).mono fun _ hy ↦ singleton_subset_iff.2 hy
  · have hd := (h.differentiableAt (by simp)).hasFDerivAt
    have ho := hd.isLittleO.def (half_pos hε)
    have hc := (h.continuousAt_fderiv (by simp)).eventually
      (Metric.ball_mem_nhds (fderiv ℝ z x₀) (half_pos hε))
    filter_upwards [ho, hc] with x hox hcx A hA
    rw [mem_singleton_iff.1 hA]
    have hn : ‖fderiv ℝ z x - fderiv ℝ z x₀‖ ≤ ε / 2 := by
      rw [← dist_eq_norm]
      exact (mem_ball.1 hcx).le
    calc ‖z x - z x₀ - fderiv ℝ z x (x - x₀)‖ =
          ‖(z x - z x₀ - fderiv ℝ z x₀ (x - x₀)) - (fderiv ℝ z x - fderiv ℝ z x₀) (x - x₀)‖ := by
          congr 1
          simp only [sub_apply]
          abel
      _ ≤ ‖z x - z x₀ - fderiv ℝ z x₀ (x - x₀)‖ + ‖(fderiv ℝ z x - fderiv ℝ z x₀) (x - x₀)‖ :=
          norm_sub_le _ _
      _ ≤ ε / 2 * ‖x - x₀‖ + ε / 2 * ‖x - x₀‖ := by
          refine add_le_add hox ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
          exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ε * ‖x - x₀‖ := by ring

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Thm. 4.9 of [Dempe 2002]**: a continuous selection `z` of finitely many functions `zⁱ`, each
pseudodifferentiable near `x̄` with pseudodifferential `Γᵢ`, is pseudodifferentiable at `x̄` with
`Γ_z(x) = conv ⋃_{i ∈ I_z(x)} Γᵢ(x)`, `I_z(x) = {i : z(x) = zⁱ(x)}`. -/
theorem isPseudodifferential_of_selection {ι : Type*} [Finite ι] {z : E → F} {zs : ι → E → F}
    {Γs : ι → E → Set (E →L[ℝ] F)} {x₀ : E} (hz : ∀ᶠ x in 𝓝 x₀, ContinuousAt z x)
    (hzs : ∀ᶠ x in 𝓝 x₀, ∀ i, IsPseudodifferential (zs i) (Γs i) x)
    (hsel : ∀ᶠ x in 𝓝 x₀, ∃ i, z x = zs i x) :
    IsPseudodifferential z (fun x ↦ convexHull ℝ (⋃ i ∈ {i | z x = zs i x}, Γs i x)) x₀ := by
  -- the active index set can only shrink near a point where everything is continuous
  have hact : ∀ x, ContinuousAt z x → (∀ i, IsPseudodifferential (zs i) (Γs i) x) →
      ∀ᶠ y in 𝓝 x, {i | z y = zs i y} ⊆ {i | z x = zs i x} := fun x hzx hzsx ↦ by
    have hev : ∀ i, ∀ᶠ y in 𝓝 x, z x ≠ zs i x → z y ≠ zs i y := fun i ↦ by
      by_cases hi : z x = zs i x
      · exact Eventually.of_forall fun _ h ↦ absurd hi h
      · have hc : ContinuousAt (fun y ↦ z y - zs i y) x := hzx.sub (hzsx i).continuousAt
        exact (hc.eventually_ne (sub_ne_zero.2 hi)).mono fun _ hy _ h ↦ hy (sub_eq_zero.2 h)
    filter_upwards [eventually_all.2 hev] with y hy i hi
    by_contra h
    exact hy i h hi
  refine ⟨?_, fun ε hε ↦ ?_⟩
  · filter_upwards [hz, hzs, hsel] with x hzx hzsx hselx
    obtain ⟨i, hi⟩ := hselx
    obtain ⟨A, hA⟩ := ((hzsx i).1.self_of_nhds).1
    have hc : ∀ i ∈ {i | z x = zs i x}, IsCompact (Γs i x) := fun i _ ↦
      ((hzsx i).1.self_of_nhds).2.2.1
    refine ⟨⟨A, subset_convexHull ℝ _ (mem_biUnion (x := i) hi hA)⟩, convex_convexHull ℝ _,
      VariationalAnalysis.isCompact_convexHull_of_isCompact
        ((Set.toFinite _).isCompact_biUnion hc), ?_⟩
    exact upperHemicontinuousAt_convexHull_biUnion (hact x hzx hzsx)
      (fun i _ ↦ ((hzsx i).1.self_of_nhds).2.2.2) hc
  · have hzsx₀ := hzs.self_of_nhds
    filter_upwards [hact x₀ hz.self_of_nhds hzsx₀,
      eventually_all.2 fun i ↦ (hzsx₀ i).2 ε hε] with x hJ hest
    refine convexHull_min (iUnion₂_subset fun i hi A hA ↦ ?_) ?_
    · have hi₀ : z x₀ = zs i x₀ := hJ hi
      show ‖z x - z x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖
      rw [show z x = zs i x from hi, hi₀]
      exact hest i A hA
    · intro A hA B hB a b ha hb hab
      show ‖z x - z x₀ - (a • A + b • B) (x - x₀)‖ ≤ ε * ‖x - x₀‖
      have hA' : ‖z x - z x₀ - A (x - x₀)‖ ≤ ε * ‖x - x₀‖ := hA
      have hB' : ‖z x - z x₀ - B (x - x₀)‖ ≤ ε * ‖x - x₀‖ := hB
      calc ‖z x - z x₀ - (a • A + b • B) (x - x₀)‖ =
            ‖a • (z x - z x₀ - A (x - x₀)) + b • (z x - z x₀ - B (x - x₀))‖ := by
            congr 1
            simp only [add_apply, smul_apply]
            conv_lhs => rw [← one_smul ℝ (z x - z x₀), ← hab]
            module
        _ ≤ a * ‖z x - z x₀ - A (x - x₀)‖ + b * ‖z x - z x₀ - B (x - x₀)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * (ε * ‖x - x₀‖) + b * (ε * ‖x - x₀‖) := by gcongr
        _ = ε * ‖x - x₀‖ := by rw [← add_mul, hab, one_mul]

variable {ι : Type*} [Finite ι] {z : E → F} {zs : ι → E → F} {V : Set E}

/-- `PC¹` functions are pseudodifferentiable with `Γ_z(x) = conv {∇zⁱ(x) : i ∈ I_z(x)}`
(Thm. 4.9 with `Γᵢ(x) = {∇zⁱ(x)}`). -/
theorem IsPC1Selection.isPseudodifferential (h : IsPC1Selection z zs V) {x₀ : E} (hx₀ : x₀ ∈ V) :
    IsPseudodifferential z
      (fun x ↦ convexHull ℝ (⋃ i ∈ {i | z x = zs i x}, {fderiv ℝ (zs i) x})) x₀ := by
  have hV : ∀ᶠ x in 𝓝 x₀, x ∈ V := h.1.mem_nhds hx₀
  refine isPseudodifferential_of_selection (hV.mono fun x hx ↦ h.2.1.continuousAt
    (h.1.mem_nhds hx)) (hV.mono fun x hx i ↦ isPseudodifferential_of_contDiffAt
      ((h.2.2.1 i).contDiffAt (h.1.mem_nhds hx))) (hV.mono fun x hx ↦ h.2.2.2 x hx)

omit [FiniteDimensional ℝ F] in
/-- At points of `V`, some selection function of a `PC¹` function is strongly active. -/
theorem IsPC1Selection.stronglyActive_nonempty
    (h : IsPC1Selection z zs V) {x : E} (hx : x ∈ V) : (stronglyActive z zs x).Nonempty := by
  have hι : Fintype ι := Fintype.ofFinite ι
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hW : ∀ i, (closure (interior {y | z y = zs i y}))ᶜ ∈ 𝓝 x := fun i ↦
    (isOpen_compl_iff.2 isClosed_closure).mem_nhds fun hi ↦ (eq_empty_iff_forall_notMem.1 hne i) hi
  have hmem : (⋂ i, (closure (interior {y | z y = zs i y}))ᶜ) ∩ V ∈ 𝓝 x :=
    inter_mem (iInter_mem.2 hW) (h.1.mem_nhds hx)
  obtain ⟨i, w, hwW, hwi⟩ := h.exists_inter_interior isOpen_interior
    ((interior_subset).trans inter_subset_right) ⟨x, mem_interior_iff_mem_nhds.2 hmem⟩
  exact (mem_iInter.1 (inter_subset_left (interior_subset hwW)) i) (subset_closure hwi)

/-- `PC¹` functions are pseudodifferentiable with the generalized Jacobian `∂z` as
pseudodifferential (the `PC¹` case of [206], cf. [Dempe 2002, p. 83]). -/
theorem IsPC1Selection.isPseudodifferential_clarkeJacobian (h : IsPC1Selection z zs V) {x₀ : E}
    (hx₀ : x₀ ∈ V) : IsPseudodifferential z (clarkeJacobian z) x₀ := by
  have hV : ∀ᶠ x in 𝓝 x₀, x ∈ V := h.1.mem_nhds hx₀
  have heq : ∀ x ∈ V, clarkeJacobian z x =
      convexHull ℝ (⋃ i ∈ stronglyActive z zs x, {fderiv ℝ (zs i) x}) := fun x hx ↦ by
    rw [h.clarkeJacobian_eq hx]
    congr 1
    ext A
    simp [eq_comm]
  refine (h.isPseudodifferential hx₀).mono ?_ ?_
  · filter_upwards [hV.eventually_nhds] with x hx
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ V := hx
    obtain ⟨i, hi⟩ := h.stronglyActive_nonempty hx'.self_of_nhds
    rw [heq x hx'.self_of_nhds]
    refine ⟨⟨_, subset_convexHull ℝ _ (mem_biUnion hi (mem_singleton _))⟩, convex_convexHull ℝ _,
      VariationalAnalysis.isCompact_convexHull_of_isCompact
        ((Set.toFinite _).isCompact_biUnion fun _ _ ↦ isCompact_singleton), ?_⟩
    have hJ : ∀ᶠ y in 𝓝 x, stronglyActive z zs y ⊆ stronglyActive z zs x := by
      have hev : ∀ i, ∀ᶠ y in 𝓝 x, i ∉ stronglyActive z zs x → i ∉ stronglyActive z zs y :=
        fun i ↦ by
          by_cases hi : i ∈ stronglyActive z zs x
          · exact Eventually.of_forall fun _ h ↦ absurd hi h
          · exact Filter.mem_of_superset ((isOpen_compl_iff.2 isClosed_closure).mem_nhds hi)
              fun _ hy _ ↦ hy
      filter_upwards [eventually_all.2 hev] with y hy i hi
      by_contra h'
      exact hy i h' hi
    have husc := upperHemicontinuousAt_convexHull_biUnion (Γs := fun i y ↦ {fderiv ℝ (zs i) y}) hJ
      (fun i _ W hW hsub ↦ ?_) fun _ _ ↦ isCompact_singleton
    · intro W hW hsub
      have hsub' : convexHull ℝ (⋃ i ∈ stronglyActive z zs x, {fderiv ℝ (zs i) x}) ⊆ W := by
        rw [← heq x hx'.self_of_nhds]
        exact hsub
      filter_upwards [husc W hW hsub', hx'] with y hy hyV
      rw [heq y hyV]
      exact hy
    · have hc := ((h.2.2.1 i).contDiffAt (h.1.mem_nhds hx'.self_of_nhds)).continuousAt_fderiv
        (by simp)
      exact (hc.eventually (hW.mem_nhds (hsub rfl))).mono fun _ hy ↦ singleton_subset_iff.2 hy
  · filter_upwards [hV] with x hx
    rw [heq x hx]
    refine convexHull_mono (biUnion_mono (fun i hi ↦ ?_) fun _ _ ↦ subset_rfl)
    exact h.eq_of_mem_closure hx interior_subset hi

section LocalSolution

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {φ : E × F → ℝ} {g : κ → E × F → ℝ}

/-- **Cor. 4.1 of [Dempe 2002]**, pseudodifferentiability, under (LICQ): the local solution function
of the follower's problem is pseudodifferentiable at `x̄`, both with the generalized Jacobian `∂y`
and with `Γ_y(x) = conv {∇y^I(x) : I admissible, y(x) = y^I(x)}` as pseudodifferential. -/
theorem isPseudodifferential_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : κ → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    IsPseudodifferential s (clarkeJacobian s) x₀ ∧
      IsPseudodifferential s (fun x ↦ convexHull ℝ
        (⋃ I ∈ {I : {I // LowerAdmissible g x₀ y₀ lam₀ I} |
            s x = lowerSolutionSelection φ g x₀ y₀ lam₀ I x},
          {fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x})) x₀ := by
  obtain ⟨V, hx₀V, hV⟩ :=
    exists_isPC1Selection_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  exact ⟨hV.isPseudodifferential_clarkeJacobian hx₀V, hV.isPseudodifferential hx₀V⟩

end LocalSolution

end Bilevel
