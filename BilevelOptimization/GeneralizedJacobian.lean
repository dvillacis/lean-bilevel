/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.PiecewiseSolution
import VariationalAnalysis.SCD.SingleValued

/-!
# The generalized Jacobian of `PC¹` functions and of the local solution function

Clarke's generalized Jacobian in finite dimensions (Def. 4.7 of [Dempe 2002]),
`∂z(x̄) = conv {lim ∇z(xₖ) : xₖ → x̄, ∇z(xₖ) exists}`, and its computation for `PC¹` functions
(Thm. 4.7, for vector-valued functions as used in the book): `∂z(x̄)` is the convex hull of the
Jacobians at `x̄` of the strongly active selection functions, those with
`x̄ ∈ cl int Supp(z, zⁱ)` (4.14). As a consequence we get the first two assertions of Cor. 4.1 for
the local solution function `y(·)` of the follower's problem under (LICQ) and (SSOC).

## Main results

* `bouligandJacobian`, `clarkeJacobian`: the B-subdifferential (limiting Jacobians) and the
  generalized Jacobian (Def. 4.7); `bouligandJacobian_eq_bSubdiff` identifies the former with
  `VariationalAnalysis.bSubdiff` for maps `E → E`.
* `stronglyActive`: the strongly active selection functions `I⁰_z(x̄)` (4.14).
* `IsPC1Selection.exists_inter_interior`: the interiors of the sets `Supp(z, zⁱ)` are dense
  (Baire).
* `IsPC1Selection.exists_stronglyActive_apply_eq`: `z'(x̄; r) = ∇zⁱ(x̄) r` for a strongly active
  `i` (the sharpened form of (4.15) of [Dempe 2002]).
* `IsPC1Selection.exists_stronglyActive_fderiv_eq`: at a point of differentiability, `∇z(x)` is
  the Jacobian of a strongly active selection function.
* `IsPC1Selection.bouligandJacobian_eq`, `IsPC1Selection.clarkeJacobian_eq`: Thm. 4.7.
* `clarkeJacobian_eq_of_lowerSSOC`, `exists_stronglyActive_apply_eq_of_lowerSSOC`: Cor. 4.1 (first
  two assertions) for the local solution function under (LICQ) and (SSOC).

## Differences from the book

* Thm. 4.7 is proved for vector-valued functions (the book states it for scalar ones and says it
  applies analogously). The B-subdifferential is described exactly:
  `{lim ∇z(xₖ)} = {∇zⁱ(x̄) : i ∈ I⁰_z(x̄)}`.
* Cor. 4.1 is stated under (LICQ) instead of (MFCQ) and (CRCQ); its selection functions are all
  `y^I(·)`, `I ⊆ ι`, those not satisfying (C1), (C2) being constant. Pseudodifferentiability
  (Def. 4.11, Thm. 4.9) is not formalized. The Lipschitz and B-differentiability assertions are
  `IsPC1At.exists_lipschitzOnWith` and `IsPC1At.exists_isBouligandDiffAt`.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The B-subdifferential (Bouligand Jacobian) of `z` at `x̄`: the limits of `∇z(xₖ)` along points
of differentiability `xₖ → x̄`. -/
def bouligandJacobian (z : E → F) (x₀ : E) : Set (E →L[ℝ] F) :=
  {A | ∃ x : ℕ → E, (∀ k, DifferentiableAt ℝ z (x k)) ∧ Tendsto x atTop (𝓝 x₀) ∧
    Tendsto (fun k ↦ fderiv ℝ z (x k)) atTop (𝓝 A)}

/-- Clarke's generalized Jacobian of `z` at `x̄` [Dempe 2002, Def. 4.7]:
`∂z(x̄) = conv {lim ∇z(xₖ) : xₖ → x̄, ∇z(xₖ) exists}`. -/
def clarkeJacobian (z : E → F) (x₀ : E) : Set (E →L[ℝ] F) :=
  convexHull ℝ (bouligandJacobian z x₀)

/-- For maps `E → E`, the B-subdifferential is `VariationalAnalysis.bSubdiff`. -/
theorem bouligandJacobian_eq_bSubdiff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (f : H → H) (x : H) :
    bouligandJacobian f x = VariationalAnalysis.bSubdiff f x := by
  ext A
  exact ⟨fun ⟨y, hd, hy, hA⟩ ↦ ⟨y, hd, hy, hA⟩, fun ⟨y, hd, hy, hA⟩ ↦ ⟨y, hd, hy, hA⟩⟩

/-- The strongly active selection functions `I⁰_z(x̄) = {i : x̄ ∈ cl int Supp(z, zⁱ)}` (4.14) of
[Dempe 2002], where `Supp(z, zⁱ) = {x : z(x) = zⁱ(x)}` (4.13). -/
def stronglyActive {ι : Type*} (z : E → F) (zs : ι → E → F) (x₀ : E) : Set ι :=
  {i | x₀ ∈ closure (interior {x | z x = zs i x})}

variable {ι : Type*} {z : E → F} {zs : ι → E → F} {V : Set E}

/-- On `V`, `z = zⁱ` at the closure points of a subset of `Supp(z, zⁱ)`. -/
theorem IsPC1Selection.eq_of_mem_closure (h : IsPC1Selection z zs V) {x : E} (hx : x ∈ V)
    {i : ι} {S : Set E} (hS : S ⊆ {y | z y = zs i y}) (hxS : x ∈ closure S) : z x = zs i x := by
  have hc : ContinuousAt (fun y ↦ z y - zs i y) x :=
    (h.2.1.continuousAt (h.1.mem_nhds hx)).sub
      ((h.2.2.1 i).continuousOn.continuousAt (h.1.mem_nhds hx))
  have h1 := hc.continuousWithinAt.mem_closure_image hxS
  have h2 : (fun y ↦ z y - zs i y) '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_singleton_iff, sub_eq_zero]
    exact hS hy
  have h3 := closure_mono h2 h1
  rwa [closure_singleton, mem_singleton_iff, sub_eq_zero] at h3

/-- The interiors of the sets `Supp(z, zⁱ)` are dense in `V`: every nonempty open subset of `V`
meets one of them (Baire's theorem). -/
theorem IsPC1Selection.exists_inter_interior [Finite ι] [FiniteDimensional ℝ E]
    (h : IsPC1Selection z zs V) {W : Set E} (hW : IsOpen W) (hWV : W ⊆ V) (hne : W.Nonempty) :
    ∃ i, (W ∩ interior {x | z x = zs i x}).Nonempty := by
  have := FiniteDimensional.complete ℝ E
  let f : Option ι → Set E := fun j ↦ match j with
    | none => Vᶜ
    | some i => closure ({x | z x = zs i x} ∩ V)
  have hc : ∀ j, IsClosed (f j) := by
    rintro (_ | i)
    exacts [h.1.isClosed_compl, isClosed_closure]
  have hU : ⋃ j, f j = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : x ∈ V
    · obtain ⟨i, hi⟩ := h.2.2.2 x hx
      exact ⟨some i, subset_closure ⟨hi, hx⟩⟩
    · exact ⟨none, hx⟩
  obtain ⟨w, hwW, hw⟩ := (dense_iUnion_interior_of_closed hc hU).inter_open_nonempty W hW hne
  obtain ⟨j, hj⟩ := mem_iUnion.1 hw
  rcases j with _ | i
  · exact absurd (hWV hwW) (interior_subset hj)
  · refine ⟨i, w, hwW, interior_maximal (fun y hy ↦ ?_) (hW.inter isOpen_interior) ⟨hwW, hj⟩⟩
    exact h.eq_of_mem_closure (hWV hy.1) inter_subset_left (interior_subset hy.2)

/-- The sharpened form of (4.15) of [Dempe 2002]: the directional derivative of a `PC¹` function is
`z'(x; r) = ∇zⁱ(x) r` for a strongly active selection function `zⁱ`, `x ∈ cl int Supp(z, zⁱ)`. -/
theorem IsPC1Selection.exists_stronglyActive_apply_eq [Finite ι] [FiniteDimensional ℝ E]
    (h : IsPC1Selection z zs V) {x : E} (hx : x ∈ V) {z' : E → F} (hz' : HasDirDerivAt z z' x)
    (r : E) : ∃ i ∈ stronglyActive z zs x, z' r = fderiv ℝ (zs i) x r ∧ z x = zs i x := by
  have hι : Fintype ι := Fintype.ofFinite ι
  obtain ⟨K, U, hU, hL⟩ := h.exists_lipschitzOnWith hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (h.1.mem_nhds hx)
  -- for small `t > 0`, the ball `B(x + t r, t²)` lies in `V` and meets some `int Supp(z, zⁱ)`
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * ‖r‖ + t ^ 2 < ε := by
    have hc : Continuous fun t : ℝ ↦ t * ‖r‖ + t ^ 2 := by fun_prop
    exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually
      (eventually_lt_nhds (by simpa using hε))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i, ∃ y, dist y (x + t • r) < t ^ 2 ∧
      y ∈ interior {w | z w = zs i w} := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht (ht0 : 0 < t)
    have hsub : Metric.ball (x + t • r) (t ^ 2) ⊆ V := fun y hy ↦ hball (by
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y (x + t • r) + dist (x + t • r) x := dist_triangle _ _ _
        _ < ε := by
          rw [dist_eq_norm (x + t • r), add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg ht0.le]
          linarith)
    obtain ⟨i, y, hyB, hy⟩ := h.exists_inter_interior Metric.isOpen_ball hsub
      (Metric.nonempty_ball.2 (by positivity))
    exact ⟨i, y, hyB, hy⟩
  obtain ⟨i, hi⟩ := frequently_exists.1 hev.frequently
  classical
  set y : ℝ → E := fun t ↦ if hT : ∃ y, dist y (x + t • r) < t ^ 2 ∧
    y ∈ interior {w | z w = zs i w} then hT.choose else x + t • r with hy
  have hy_dist : ∀ t, dist (y t) (x + t • r) ≤ t ^ 2 := fun t ↦ by
    simp only [hy]
    split_ifs with hT
    · exact hT.choose_spec.1.le
    · rw [dist_self]
      positivity
  have hy_mem : ∃ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ interior {w | z w = zs i w} :=
    hi.mono fun t hT ↦ by
      simp only [hy, dif_pos hT]
      exact hT.choose_spec.2
  -- `t⁻¹ (y(t) - x) → r` and `y(t) → x`
  have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have herr : Tendsto (fun t : ℝ ↦ t⁻¹ • (y t - (x + t • r))) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_) ht0
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, ← dist_eq_norm]
    calc t⁻¹ * dist (y t) (x + t • r) ≤ t⁻¹ * t ^ 2 :=
          mul_le_mul_of_nonneg_left (hy_dist t) (inv_nonneg.2 ht.le)
      _ = t := by field_simp
  have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ • (y t - x)) (𝓝[>] 0) (𝓝 r) := by
    have := (tendsto_const_nhds (x := r)).add herr
    rw [add_zero] at this
    refine this.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    show r + t⁻¹ • (y t - (x + t • r)) = t⁻¹ • (y t - x)
    rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, smul_sub]
    abel
  have hyx : Tendsto y (𝓝[>] 0) (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).add (ht0.smul hslope)
    rw [zero_smul, add_zero] at this
    refine this.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
  have hact : i ∈ stronglyActive z zs x := mem_closure_of_frequently_of_tendsto hy_mem hyx
  have hzx : z x = zs i x := h.eq_of_mem_closure hx interior_subset hact
  -- the slopes of `zⁱ` and of `z` along `y(t)`
  have hzi : HasFDerivAt (zs i) (fderiv ℝ (zs i) x) x :=
    (((h.2.2.1 i).differentiableOn one_ne_zero x hx).differentiableAt
      (h.1.mem_nhds hx)).hasFDerivAt
  have h2 := tendsto_slope_comp_of_hasFDerivAt hzi hyx hslope
  have hline : Tendsto (fun t : ℝ ↦ x + t • r) (𝓝[>] 0) (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).add (ht0.smul (tendsto_const_nhds (x := r)))
    rwa [zero_smul, add_zero] at this
  have hz2 : Tendsto (fun t : ℝ ↦ t⁻¹ • (z (y t) - z (x + t • r))) (𝓝[>] 0) (𝓝 0) := by
    have hKt : Tendsto (fun t : ℝ ↦ (K : ℝ) * t) (𝓝[>] 0) (𝓝 0) := by
      simpa using ht0.const_mul (K : ℝ)
    refine squeeze_zero_norm' ?_ hKt
    filter_upwards [hyx.eventually hU, hline.eventually hU, self_mem_nhdsWithin]
      with t hyU hlU (ht : 0 < t)
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, ← dist_eq_norm]
    calc t⁻¹ * dist (z (y t)) (z (x + t • r)) ≤ t⁻¹ * (K * t ^ 2) :=
          mul_le_mul_of_nonneg_left ((hL.dist_le_mul _ hyU _ hlU).trans
            (mul_le_mul_of_nonneg_left (hy_dist t) K.coe_nonneg)) (inv_nonneg.2 ht.le)
      _ = K * t := by field_simp
  have h1 : Tendsto (fun t : ℝ ↦ t⁻¹ • (z (y t) - z x)) (𝓝[>] 0) (𝓝 (z' r)) := by
    have := (hz' r).add hz2
    rw [add_zero] at this
    refine this.congr fun t ↦ ?_
    rw [← smul_add]
    congr 1
    abel
  refine ⟨i, hact, tendsto_nhds_unique_of_frequently_eq h1 h2 (hy_mem.mono fun t ht ↦ ?_), hzx⟩
  have hyt : y t ∈ {w | z w = zs i w} := interior_subset ht
  rw [show z (y t) = zs i (y t) from hyt, hzx]

/-- At a point of differentiability of a `PC¹` function, its Jacobian is the Jacobian of a strongly
active selection function. -/
theorem IsPC1Selection.exists_stronglyActive_fderiv_eq [Finite ι] [FiniteDimensional ℝ E]
    (h : IsPC1Selection z zs V) {x : E} (hx : x ∈ V) (hd : DifferentiableAt ℝ z x) :
    ∃ i ∈ stronglyActive z zs x, fderiv ℝ z x = fderiv ℝ (zs i) x := by
  have := FiniteDimensional.complete ℝ E
  have hdir : HasDirDerivAt z (fderiv ℝ z x) x := HasFDerivAt.hasDirDerivAt hd.hasFDerivAt
  -- the kernels of `∇z(x) - ∇zⁱ(x)`, `i ∈ I⁰_z(x)`, cover `E`, so one of them is `E`
  let Ks : stronglyActive z zs x → Submodule ℝ E := fun i ↦
    (fderiv ℝ z x - fderiv ℝ (zs i.1) x).ker
  have hcover : ⋃ i, (Ks i : Set E) = univ := eq_univ_of_forall fun r ↦ by
    obtain ⟨i, hi, he, -⟩ := h.exists_stronglyActive_apply_eq hx hdir r
    refine mem_iUnion.2 ⟨⟨i, hi⟩, ?_⟩
    exact LinearMap.mem_ker.2 (by simp [he])
  have hclosed : ∀ i, IsClosed (Ks i : Set E) := fun i ↦
    ContinuousLinearMap.isClosed_ker (fderiv ℝ z x - fderiv ℝ (zs i.1) x)
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have htop := Submodule.eq_top_of_nonempty_interior' _ hi
  refine ⟨i.1, i.2, ContinuousLinearMap.ext fun r ↦ ?_⟩
  have hr : r ∈ Ks i := htop ▸ Submodule.mem_top
  have hr' := LinearMap.mem_ker.1 hr
  simpa [sub_eq_zero] using hr'

/-- **Thm. 4.7 of [Dempe 2002]**, B-subdifferential version: the limiting Jacobians of a `PC¹`
function at `x̄` are exactly the Jacobians `∇zⁱ(x̄)` of its strongly active selection functions. -/
theorem IsPC1Selection.bouligandJacobian_eq [Finite ι] [FiniteDimensional ℝ E]
    (h : IsPC1Selection z zs V) {x₀ : E} (hx₀ : x₀ ∈ V) :
    bouligandJacobian z x₀ = (fun i ↦ fderiv ℝ (zs i) x₀) '' stronglyActive z zs x₀ := by
  have hcf : ∀ i, ContinuousOn (fderiv ℝ (zs i)) V := fun i ↦
    (h.2.2.1 i).continuousOn_fderiv_of_isOpen h.1 le_rfl
  have hcf₀ : ∀ i, Tendsto (fderiv ℝ (zs i)) (𝓝 x₀) (𝓝 (fderiv ℝ (zs i) x₀)) := fun i ↦
    ((hcf i).continuousAt (h.1.mem_nhds hx₀)).tendsto
  ext A
  constructor
  · rintro ⟨x, hd, hx, hA⟩
    have hev : ∀ᶠ k in atTop, ∃ i, x k ∈ closure (interior {w | z w = zs i w}) ∧
        fderiv ℝ z (x k) = fderiv ℝ (zs i) (x k) :=
      (hx.eventually (h.1.mem_nhds hx₀)).mono fun k hk ↦
        let ⟨i, hi, he⟩ := h.exists_stronglyActive_fderiv_eq hk (hd k)
        ⟨i, hi, he⟩
    obtain ⟨i, hi⟩ := frequently_exists.1 hev.frequently
    have hcl := mem_closure_of_frequently_of_tendsto (hi.mono fun k hk ↦ hk.1) hx
    rw [closure_closure] at hcl
    exact ⟨i, hcl, tendsto_nhds_unique_of_frequently_eq ((hcf₀ i).comp hx) hA
      (hi.mono fun k hk ↦ hk.2.symm)⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨x, hxmem, hx⟩ := mem_closure_iff_seq_limit.1 (h.1.inter_closure ⟨hx₀, hi⟩)
    have hloc : ∀ k, z =ᶠ[𝓝 (x k)] zs i := fun k ↦ mem_interior_iff_mem_nhds.1 (hxmem k).2
    have hdi : ∀ k, DifferentiableAt ℝ (zs i) (x k) := fun k ↦
      ((h.2.2.1 i).differentiableOn one_ne_zero _ (hxmem k).1).differentiableAt
        (h.1.mem_nhds (hxmem k).1)
    refine ⟨x, fun k ↦ (hdi k).congr_of_eventuallyEq (hloc k), hx, ?_⟩
    exact ((hcf₀ i).comp hx).congr fun k ↦ (hloc k).fderiv_eq.symm

/-- **Thm. 4.7 of [Dempe 2002]**: the generalized Jacobian of a `PC¹` function is the convex hull
of the Jacobians of its strongly active selection functions,
`∂z(x̄) = conv {∇zⁱ(x̄) : x̄ ∈ cl int Supp(z, zⁱ)}`. -/
theorem IsPC1Selection.clarkeJacobian_eq [Finite ι] [FiniteDimensional ℝ E]
    (h : IsPC1Selection z zs V) {x₀ : E} (hx₀ : x₀ ∈ V) :
    clarkeJacobian z x₀ =
      convexHull ℝ ((fun i ↦ fderiv ℝ (zs i) x₀) '' stronglyActive z zs x₀) := by
  rw [clarkeJacobian, h.bouligandJacobian_eq hx₀]

/-! ### The local solution function -/

section Solution

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {φ : E × F → ℝ} {g : ι → E × F → ℝ}

/-- **Cor. 4.1 of [Dempe 2002]** (first assertion) under (LICQ) and (SSOC): the generalized
Jacobian of a continuous local solution function `y(·)` through `ȳ` is
`∂y(x̄) = conv {∇y^I(x̄) : I ∈ I⁰_y(x̄)}`, with the local solution functions `y^I(·)` of (4.19). -/
theorem clarkeJacobian_eq_of_lowerSSOC (hφ : ContDiff ℝ 2 φ) (hg : ∀ i, ContDiff ℝ 2 (g i))
    {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ} (hkkt : IsLowerKKT φ g x₀ y₀ lam₀)
    (hlicq : LowerLICQ g x₀ y₀) (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀) (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x)) :
    clarkeJacobian s x₀ = convexHull ℝ
      ((fun I ↦ fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀) ''
        stronglyActive s (lowerSolutionSelection φ g x₀ y₀ lam₀) x₀) := by
  obtain ⟨V, hx₀V, hV⟩ :=
    exists_isPC1Selection_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  exact hV.clarkeJacobian_eq hx₀V

/-- **Cor. 4.1 of [Dempe 2002]** (second assertion) under (LICQ) and (SSOC): the directional
derivative of a continuous local solution function `y(·)` through `ȳ` is
`y'(x̄; r) = ∇y^I(x̄) r` for some `I ∈ I⁰_y(x̄)`. -/
theorem exists_stronglyActive_apply_eq_of_lowerSSOC (hφ : ContDiff ℝ 2 φ)
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {x₀ : E} {y₀ : F} {lam₀ : ι → ℝ}
    (hkkt : IsLowerKKT φ g x₀ y₀ lam₀) (hlicq : LowerLICQ g x₀ y₀)
    (hssoc : LowerSSOC φ g x₀ y₀) {s : E → F} {U : Set E} (hU : U ∈ 𝓝 x₀) (hs₀ : s x₀ = y₀)
    (hsc : ContinuousOn s U)
    (hsmin : ∀ x ∈ U, s x ∈ lowerFeasible g x ∧
      IsLocalMinOn (fun z ↦ φ (x, z)) (lowerFeasible g x) (s x))
    {s' : E → F} (hs' : HasDirDerivAt s s' x₀) (r : E) :
    ∃ I ∈ stronglyActive s (lowerSolutionSelection φ g x₀ y₀ lam₀) x₀,
      s' r = fderiv ℝ (lowerSolutionSelection φ g x₀ y₀ lam₀ I) x₀ r := by
  obtain ⟨V, hx₀V, hV⟩ :=
    exists_isPC1Selection_of_lowerSSOC hφ hg hkkt hlicq hssoc hU hs₀ hsc hsmin
  obtain ⟨I, hI, he, -⟩ := hV.exists_stronglyActive_apply_eq hx₀V hs' r
  exact ⟨I, hI, he⟩

end Solution

end Bilevel
