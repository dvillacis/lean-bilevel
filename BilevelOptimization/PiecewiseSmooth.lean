/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.Parametric

/-!
# Piecewise continuously differentiable functions

Sect. 4.3 of [Dempe 2002]: a function `z` is *piecewise continuously differentiable* (`PC¹`) at
`x̄` if on an open neighborhood of `x̄` it is continuous and every value `z(x)` is the value
`zⁱ(x)` of one of finitely many `C¹` selection functions (Def. 4.5).

## Main results

* `IsPC1Selection`, `IsPC1At`: Def. 4.5 of [Dempe 2002].
* `norm_sub_le_of_forall_exists_eq`: a continuous selection of finitely many `C`-Lipschitz
  functions on an interval is `C`-Lipschitz (the one-dimensional core of Lemma 4.2 and
  Thm. 4.6 of [Dempe 2002]).
* `IsPC1Selection.exists_lipschitzOnWith`, `IsPC1At.exists_lipschitzOnWith`: Thm. 4.6 of
  [Dempe 2002]: `PC¹` functions are locally Lipschitz continuous.
* `exists_tendsto_slope_of_forall_exists_eq`: a continuous selection of finitely many functions
  of one variable that are differentiable at `0` has a right derivative at `0`, equal to the
  derivative of a selection function active at `0`.
* `IsPC1Selection.exists_tendsto_slope`, `IsPC1At.exists_tendsto_slope`: `PC¹` functions are
  directionally differentiable (Def. 4.9), and `z'(x̄; r) = ∇zⁱ(x̄) r` for a selection function
  active at `x̄` ((4.15) of [Dempe 2002], with active instead of strongly active selections).
* `HasDirDerivAt`, `IsBouligandDiffAt`: Def. 4.9 and 4.10 of [Dempe 2002].
* `HasDirDerivAt.norm_sub_le`, `HasDirDerivAt.map_smul`: the directional derivative of a locally
  Lipschitz function is Lipschitz with the same constant and positively homogeneous.
* `tendsto_slope_comp_of_hasFDerivAt`, `HasFDerivAt.hasDirDerivAt`: chain rule for one-sided
  directional derivatives along a curve; Fréchet differentiable functions are directionally
  differentiable.
* `HasDirDerivAt.isBouligandDiffAt`, `IsPC1At.exists_isBouligandDiffAt`: in finite dimensions, a
  locally Lipschitz, directionally differentiable function is Bouligand differentiable
  [Dempe 2002, p. 82]; in particular `PC¹` functions are.
* `isPC1At_max`: the pointwise maximum of two `C¹` functions is `PC¹`.

## Remarks on the sources

* Def. 4.5 asks for selection functions defined on the neighborhood only; here they are
  functions on the whole space that are `C¹` on the open neighborhood `V`.
* Thm. 4.6 is proved with a "real induction" along segments
  (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`) instead of the covering Lemma 4.2.
* The book obtains directional differentiability from the proof of Thm. 4.8 (semismoothness,
  via a connectedness argument on cones). Here the argument is done along the ray
  `t ↦ x̄ + t r`: the selection functions active at arbitrarily small `t > 0` all have the same
  derivative at `0`, since otherwise the interval `(0, δ)` would split into two disjoint
  nonempty closed sets. (4.15) is stated with the active index set `I_z(x̄)`; the sharper version
  with strongly active indices (`x̄ ∈ cl int Supp(z, zⁱ)`) is not formalized.
* The contingent cone of Def. 4.6 is `VariationalAnalysis.contingentCone`.
* The book cites [Scholtes 1994] for Bouligand differentiability; here it is proved by covering
  the unit sphere with finitely many balls.
* Not formalized: Thm. 4.7 (Clarke generalized Jacobian of a `PC¹` function), Thm. 4.8
  (semismoothness), Def. 4.11 and Thm. 4.9 (pseudodifferentiability).
-/

open Filter Topology Set

namespace Bilevel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### Selections of finitely many functions of one variable -/

omit [NormedSpace ℝ F] in
/-- A continuous selection of finitely many functions that are `C`-Lipschitz on `[a, b]` is
`C`-Lipschitz on `[a, b]` (the one-dimensional core of Thm. 4.6 of [Dempe 2002]). -/
theorem norm_sub_le_of_forall_exists_eq {ι : Type*} [Finite ι] {g : ℝ → F} {gs : ι → ℝ → F}
    {a b C : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hgs : ∀ i, ContinuousOn (gs i) (Icc a b))
    (hL : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖gs i t - gs i s‖ ≤ C * |t - s|)
    (hsel : ∀ t ∈ Icc a b, ∃ i, g t = gs i t) : ‖g b - g a‖ ≤ C * (b - a) := by
  set s : Set ℝ := {t | ‖g t - g a‖ ≤ C * (t - a)} with hs
  have hcl : IsClosed (s ∩ Icc a b) := by
    have hc : ContinuousOn (fun t ↦ ‖g t - g a‖ - C * (t - a)) (Icc a b) :=
      ((hg.sub continuousOn_const).norm).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    have h := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
    convert h using 1
    ext t
    simp only [hs, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
    tauto
  refine hcl.Icc_subset_of_forall_mem_nhdsWithin (by simp [hs]) (fun x hx ↦ ?_) ⟨hab, le_rfl⟩
  obtain ⟨hxs, hxa, hxb⟩ := hx
  have hIcc : ∀ᶠ t in 𝓝[>] x, t ∈ Icc a b :=
    mem_of_superset (Ioo_mem_nhdsGT hxb) fun t ht ↦ ⟨hxa.trans ht.1.le, ht.2.le⟩
  have hne : ∀ i, g x ≠ gs i x → ∀ᶠ t in 𝓝[>] x, g t ≠ gs i t := fun i hi ↦ by
    have hc : ContinuousWithinAt (fun t ↦ g t - gs i t) (Ioo x b) x :=
      ((hg.sub (hgs i)) x ⟨hxa, hxb.le⟩).mono fun t ht ↦ ⟨hxa.trans ht.1.le, ht.2.le⟩
    have ht := hc.tendsto
    rw [nhdsWithin_Ioo_eq_nhdsGT hxb] at ht
    exact (ht.eventually_ne (sub_ne_zero.2 hi)).mono fun t h ↦ sub_ne_zero.1 h
  have hall : ∀ᶠ t in 𝓝[>] x, ∀ i, g x ≠ gs i x → g t ≠ gs i t :=
    eventually_all.2 fun i ↦ by
      by_cases hi : g x = gs i x
      · exact Eventually.of_forall fun _ h ↦ absurd hi h
      · exact (hne i hi).mono fun _ h _ ↦ h
  filter_upwards [hIcc, hall, self_mem_nhdsWithin] with t ht hall hxt
  obtain ⟨i, hi⟩ := hsel t ht
  have hxi : g x = gs i x := by
    by_contra h
    exact hall i h hi
  have hxt' : x < t := hxt
  have h1 := hL i x ⟨hxa, hxb.le⟩ t ht
  rw [← hi, ← hxi, abs_of_pos (sub_pos.2 hxt')] at h1
  have h2 : ‖g x - g a‖ ≤ C * (x - a) := hxs
  show ‖g t - g a‖ ≤ C * (t - a)
  calc ‖g t - g a‖ ≤ ‖g t - g x‖ + ‖g x - g a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * (t - x) + C * (x - a) := add_le_add h1 h2
    _ = C * (t - a) := by ring

/-- A continuous selection of finitely many functions of one variable that are differentiable at
`0` has a right derivative at `0`, equal to the derivative of a selection function that is active
at `0`. -/
theorem exists_tendsto_slope_of_forall_exists_eq {ι : Type*} [Fintype ι] {g : ℝ → F}
    {gs : ι → ℝ → F} {c : ι → F} {δ : ℝ} (hδ : 0 < δ) (hg : ContinuousOn g (Ico 0 δ))
    (hgs : ∀ i, ContinuousOn (gs i) (Ico 0 δ)) (hd : ∀ i, HasDerivAt (gs i) (c i) 0)
    (hsel : ∀ t ∈ Ico 0 δ, ∃ i, g t = gs i t) :
    ∃ i, g 0 = gs i 0 ∧ Tendsto (fun t ↦ t⁻¹ • (g t - g 0)) (𝓝[>] 0) (𝓝 (c i)) := by
  classical
  have hIco : Ioo 0 δ ⊆ Ico 0 δ := Ioo_subset_Ico_self
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ico 0 δ := mem_of_superset (Ioo_mem_nhdsGT hδ) hIco
  have hlim : ∀ i, Tendsto (fun t ↦ g t - gs i t) (𝓝[>] 0) (𝓝 (g 0 - gs i 0)) := fun i ↦ by
    have hc : ContinuousWithinAt (fun t ↦ g t - gs i t) (Ioo 0 δ) 0 :=
      ((hg.sub (hgs i)) 0 ⟨le_rfl, hδ⟩).mono hIco
    have ht := hc.tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsGT hδ] at ht
  have hslope : ∀ i, Tendsto (fun t ↦ t⁻¹ • (gs i t - gs i 0)) (𝓝[>] 0) (𝓝 (c i)) := fun i ↦ by
    simpa only [zero_add] using (hd i).tendsto_slope_zero_right
  -- the selection functions active at arbitrarily small `t > 0`
  set J : Set ι := {i | ∃ᶠ t in 𝓝[>] (0 : ℝ), g t = gs i t} with hJ
  have hJ0 : ∀ i ∈ J, g 0 = gs i 0 := fun i hi ↦ by
    by_contra h
    obtain ⟨t, h1, h2⟩ := (Frequently.and_eventually hi
      ((hlim i).eventually_ne (sub_ne_zero.2 h))).exists
    exact h2 (sub_eq_zero.2 h1)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, i ∉ J → g t ≠ gs i t :=
    eventually_all.2 fun i ↦ by
      by_cases hi : i ∈ J
      · exact Eventually.of_forall fun _ h ↦ absurd hi h
      · exact (not_frequently.1 hi).mono fun _ h _ ↦ h
  have hsome : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ i ∈ J, g t = gs i t := by
    filter_upwards [hev, hall] with t ht hall
    obtain ⟨i, hi⟩ := hsel t ht
    exact ⟨i, by_contra fun h ↦ hall i h hi, hi⟩
  obtain ⟨-, i₀, hi₀, -⟩ := hsome.exists
  -- all of them have the same derivative at `0`
  have hkey : ∀ j ∈ J, c j = c i₀ := by
    intro j hj
    by_contra hne
    have hdist : ∀ k l, k ∈ J → l ∈ J → c k = c i₀ → c l ≠ c i₀ →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), gs k t ≠ gs l t := fun k l hk hl hck hcl ↦ by
      have h := (hslope k).sub (hslope l)
      have hne' : c k - c l ≠ 0 := sub_ne_zero.2 fun h ↦ hcl (h ▸ hck)
      refine (h.eventually_ne hne').mono fun t ht heq ↦ ht ?_
      rw [heq, ← hJ0 k hk, ← hJ0 l hl, sub_self]
    have hE : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ico 0 δ ∧ (∀ i, i ∉ J → g t ≠ gs i t) ∧
        ∀ k l, k ∈ J → l ∈ J → c k = c i₀ → c l ≠ c i₀ → gs k t ≠ gs l t := by
      refine hev.and (hall.and (eventually_all.2 fun k ↦ eventually_all.2 fun l ↦ ?_))
      by_cases h : k ∈ J ∧ l ∈ J ∧ c k = c i₀ ∧ c l ≠ c i₀
      · exact (hdist k l h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun _ ht _ _ _ _ ↦ ht
      · exact Eventually.of_forall fun _ hk hl hck hcl ↦ absurd ⟨hk, hl, hck, hcl⟩ h
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hE
    have hu : (0 : ℝ) < u := hu
    obtain ⟨t₁, ht₁, ht₁u⟩ := (Frequently.and_eventually hi₀ (Ioo_mem_nhdsGT hu)).exists
    obtain ⟨t₂, ht₂, ht₂u⟩ := (Frequently.and_eventually hj (Ioo_mem_nhdsGT hu)).exists
    have hS : uIcc t₁ t₂ ⊆ Ioo 0 u := ordConnected_Ioo.uIcc_subset ht₁u ht₂u
    have hSI : uIcc t₁ t₂ ⊆ Ico 0 δ := fun t ht ↦ (hsub (hS ht)).1
    have hclosed : ∀ (p : ι → Prop), IsClosed {t | t ∈ uIcc t₁ t₂ ∧ ∃ k, p k ∧ g t = gs k t} :=
      fun p ↦ by
        have e : {t | t ∈ uIcc t₁ t₂ ∧ ∃ k, p k ∧ g t = gs k t} =
            ⋃ k, {t | t ∈ uIcc t₁ t₂ ∧ p k ∧ g t = gs k t} := by
          ext t
          simp only [mem_ofPred_eq, mem_iUnion]
          constructor
          · rintro ⟨ht, k, hk, he⟩
            exact ⟨k, ht, hk, he⟩
          · rintro ⟨k, ht, hk, he⟩
            exact ⟨ht, k, hk, he⟩
        rw [e]
        refine isClosed_iUnion_of_finite fun k ↦ ?_
        by_cases hk : p k
        · have h := ((hg.sub (hgs k)).mono hSI).preimage_isClosed_of_isClosed isClosed_Icc
            (isClosed_singleton (x := (0 : F)))
          convert h using 1
          ext t
          simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, Pi.sub_apply,
            sub_eq_zero, hk, true_and]
        · convert isClosed_empty using 1
          ext t
          simp only [mem_ofPred_eq, hk, false_and, and_false, mem_empty_iff_false]
    obtain ⟨t, ht, ⟨-, k, ⟨hk, hck⟩, hgk⟩, ⟨-, l, ⟨hl, hcl⟩, hgl⟩⟩ :=
      isPreconnected_closed_iff.1 isPreconnected_uIcc _ _ (hclosed fun k ↦ k ∈ J ∧ c k = c i₀)
        (hclosed fun k ↦ k ∈ J ∧ c k ≠ c i₀)
        (fun t ht ↦ by
          obtain ⟨hI, hnJ, -⟩ := hsub (hS ht)
          obtain ⟨i, hi⟩ := hsel t hI
          have hiJ : i ∈ J := by_contra fun h ↦ hnJ i h hi
          by_cases hci : c i = c i₀
          · exact Or.inl ⟨ht, i, ⟨hiJ, hci⟩, hi⟩
          · exact Or.inr ⟨ht, i, ⟨hiJ, hci⟩, hi⟩)
        ⟨t₁, left_mem_uIcc, left_mem_uIcc, i₀, ⟨hi₀, rfl⟩, ht₁⟩
        ⟨t₂, right_mem_uIcc, right_mem_uIcc, j, ⟨hj, hne⟩, ht₂⟩
    exact (hsub (hS ht)).2.2 k l hk hl hck hcl (hgk.symm.trans hgl)
  -- the slope of `g` is eventually a slope of an active selection function
  refine ⟨i₀, hJ0 i₀ hi₀, Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  have hclose : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, k ∈ J → dist (t⁻¹ • (gs k t - gs k 0)) (c i₀) < ε :=
    eventually_all.2 fun k ↦ by
      by_cases hk : k ∈ J
      · exact (Metric.tendsto_nhds.1 (hslope k) ε hε).mono fun t ht _ ↦ hkey k hk ▸ ht
      · exact Eventually.of_forall fun _ h ↦ absurd h hk
  filter_upwards [hsome, hclose] with t ⟨k, hk, hgk⟩ hclose
  rw [hgk, hJ0 k hk]
  exact hclose k hk

/-! ### `PC¹` functions -/

/-- The functions `zs i` are `C¹` selection functions of `z` on the open set `V`
[Dempe 2002, Def. 4.5]: `z` is continuous on `V` and `z(x) ∈ {zⁱ(x)}` for `x ∈ V`. -/
def IsPC1Selection {ι : Type*} (z : E → F) (zs : ι → E → F) (V : Set E) : Prop :=
  IsOpen V ∧ ContinuousOn z V ∧ (∀ i, ContDiffOn ℝ 1 (zs i) V) ∧ ∀ x ∈ V, ∃ i, z x = zs i x

/-- A piecewise continuously differentiable (`PC¹`) function at `x₀` [Dempe 2002, Def. 4.5]: a
continuous selection of finitely many `C¹` functions on an open neighborhood of `x₀`. -/
def IsPC1At (z : E → F) (x₀ : E) : Prop :=
  ∃ (n : ℕ) (zs : Fin n → E → F) (V : Set E), x₀ ∈ V ∧ IsPC1Selection z zs V

/-- Thm. 4.6 of [Dempe 2002]: `PC¹` functions are locally Lipschitz continuous. -/
theorem IsPC1Selection.exists_lipschitzOnWith {ι : Type*} [Fintype ι] {z : E → F}
    {zs : ι → E → F} {V : Set E} (h : IsPC1Selection z zs V) {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ K, ∃ U ∈ 𝓝 x₀, LipschitzOnWith K z U := by
  obtain ⟨hV, hz, hzs, hsel⟩ := h
  have hloc : ∀ i, ∃ K, ∃ t ∈ 𝓝 x₀, LipschitzOnWith K (zs i) t := fun i ↦
    ((hzs i).contDiffAt (hV.mem_nhds hx₀)).exists_lipschitzOnWith
  choose K t ht hK using hloc
  have hT : V ∩ ⋂ i, t i ∈ 𝓝 x₀ := inter_mem (hV.mem_nhds hx₀) (iInter_mem.2 ht)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  set Ks : NNReal := ∑ i, K i with hKs
  have hKi : ∀ i, (K i : ℝ) ≤ Ks := fun i ↦
    NNReal.coe_le_coe.2 (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  refine ⟨Ks, Metric.ball x₀ ε, Metric.ball_mem_nhds x₀ hε,
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  set γ : ℝ → E := fun s ↦ y + s • (x - y) with hγdef
  have hγ : MapsTo γ (Icc 0 1) (Metric.ball x₀ ε) := fun s hs ↦ by
    have h := convex_ball x₀ ε hy hx (sub_nonneg.2 hs.2) hs.1 (by ring : 1 - s + s = 1)
    convert h using 1
    simp only [hγdef]
    module
  have hγV : MapsTo γ (Icc 0 1) V := fun s hs ↦ (hball (hγ hs)).1
  have hγt : ∀ i, MapsTo γ (Icc 0 1) (t i) := fun i s hs ↦ mem_iInter.1 (hball (hγ hs)).2 i
  have hγc : Continuous γ := by fun_prop
  have hmain := norm_sub_le_of_forall_exists_eq (g := z ∘ γ) (gs := fun i ↦ zs i ∘ γ)
    (C := Ks * ‖x - y‖) zero_le_one (hz.comp hγc.continuousOn hγV)
    (fun i ↦ ((hzs i).continuousOn.comp hγc.continuousOn hγV))
    (fun i s hs u hu ↦ by
      have h1 := (hK i).dist_le_mul (γ u) (hγt i hu) (γ s) (hγt i hs)
      rw [dist_eq_norm, dist_eq_norm] at h1
      have h2 : γ u - γ s = (u - s) • (x - y) := by simp only [hγdef]; module
      rw [h2, norm_smul, Real.norm_eq_abs] at h1
      calc ‖(zs i ∘ γ) u - (zs i ∘ γ) s‖ ≤ K i * (|u - s| * ‖x - y‖) := h1
        _ ≤ Ks * (|u - s| * ‖x - y‖) :=
          mul_le_mul_of_nonneg_right (hKi i) (by positivity)
        _ = Ks * ‖x - y‖ * |u - s| := by ring)
    (fun s hs ↦ hsel _ (hγV hs))
  simp only [Function.comp_apply, hγdef, one_smul, zero_smul, add_zero, add_sub_cancel,
    sub_zero, mul_one] at hmain
  rw [dist_eq_norm, dist_eq_norm]
  exact hmain

/-- Thm. 4.6 of [Dempe 2002]: `PC¹` functions are locally Lipschitz continuous. -/
theorem IsPC1At.exists_lipschitzOnWith {z : E → F} {x₀ : E} (h : IsPC1At z x₀) :
    ∃ K, ∃ U ∈ 𝓝 x₀, LipschitzOnWith K z U := by
  obtain ⟨n, zs, V, hx₀, h⟩ := h
  exact h.exists_lipschitzOnWith hx₀

/-- `PC¹` functions are directionally differentiable, and the directional derivative is
`z'(x₀; r) = ∇zⁱ(x₀) r` for a selection function `zⁱ` active at `x₀`
[Dempe 2002, Def. 4.9 and (4.15)]. -/
theorem IsPC1Selection.exists_tendsto_slope {ι : Type*} [Fintype ι] {z : E → F}
    {zs : ι → E → F} {V : Set E} (h : IsPC1Selection z zs V) {x₀ : E} (hx₀ : x₀ ∈ V) (r : E) :
    ∃ i, z x₀ = zs i x₀ ∧ Tendsto (fun t : ℝ ↦ t⁻¹ • (z (x₀ + t • r) - z x₀)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (zs i) x₀ r)) := by
  obtain ⟨hV, hz, hzs, hsel⟩ := h
  set γ : ℝ → E := fun t ↦ x₀ + t • r with hγdef
  have hγc : Continuous γ := by fun_prop
  have hpre : γ ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
    hγc.continuousAt.preimage_mem_nhds (by simpa [hγdef] using hV.mem_nhds hx₀)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre
  have hγV : MapsTo γ (Ico 0 δ) V := fun t ht ↦ hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2)
  have hd : ∀ i, HasDerivAt (zs i ∘ γ) (fderiv ℝ (zs i) x₀ r) 0 := fun i ↦ by
    have hγd : HasDerivAt γ r 0 := by
      simpa [hγdef] using ((hasDerivAt_id (0 : ℝ)).smul_const r).const_add x₀
    exact (((hzs i).contDiffAt (hV.mem_nhds hx₀)).differentiableAt one_ne_zero).hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hγd (by simp [hγdef])
  obtain ⟨i, hi, hlim⟩ := exists_tendsto_slope_of_forall_exists_eq (g := z ∘ γ)
    (gs := fun i ↦ zs i ∘ γ) hδ (hz.comp hγc.continuousOn hγV)
    (fun i ↦ (hzs i).continuousOn.comp hγc.continuousOn hγV) hd
    (fun t ht ↦ hsel _ (hγV ht))
  simp only [Function.comp_apply, hγdef, zero_smul, add_zero] at hi hlim
  exact ⟨i, hi, hlim⟩

/-- `PC¹` functions are directionally differentiable [Dempe 2002, Def. 4.9]. -/
theorem IsPC1At.exists_tendsto_slope {z : E → F} {x₀ : E} (h : IsPC1At z x₀) (r : E) :
    ∃ v, Tendsto (fun t : ℝ ↦ t⁻¹ • (z (x₀ + t • r) - z x₀)) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨n, zs, V, hx₀, h⟩ := h
  obtain ⟨i, -, hlim⟩ := h.exists_tendsto_slope hx₀ r
  exact ⟨_, hlim⟩

/-! ### Directional and Bouligand differentiability -/

/-- `z` is directionally differentiable at `x₀` with directional derivative `z'(x₀; r) = z' r`
[Dempe 2002, Def. 4.9]. -/
def HasDirDerivAt (z z' : E → F) (x₀ : E) : Prop :=
  ∀ r, Tendsto (fun t : ℝ ↦ t⁻¹ • (z (x₀ + t • r) - z x₀)) (𝓝[>] 0) (𝓝 (z' r))

/-- `z` is Bouligand differentiable at `x₀` [Dempe 2002, Def. 4.10]: it is directionally
differentiable and the directional derivative is a first-order approximation,
`z(x) = z(x₀) + z'(x₀; x - x₀) + o(‖x - x₀‖)`. -/
def IsBouligandDiffAt (z z' : E → F) (x₀ : E) : Prop :=
  HasDirDerivAt z z' x₀ ∧
    Tendsto (fun x ↦ ‖x - x₀‖⁻¹ * ‖z x - z x₀ - z' (x - x₀)‖) (𝓝[≠] x₀) (𝓝 0)

/-- Points `x₀ + t • r` with `t > 0` small lie in a given neighborhood of `x₀`. -/
theorem eventually_add_smul_mem {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀) (r : E) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • r ∈ U := by
  have h : Tendsto (fun t : ℝ ↦ x₀ + t • r) (𝓝 0) (𝓝 x₀) :=
    (continuous_const.add (continuous_id.smul continuous_const) :
      Continuous fun t : ℝ ↦ x₀ + t • r).tendsto' 0 x₀ (by simp)
  exact (h.eventually hU).filter_mono nhdsWithin_le_nhds

/-- The directional derivative of a function that is `K`-Lipschitz near `x₀` is `K`-Lipschitz
[Dempe 2002, p. 82]. -/
theorem HasDirDerivAt.norm_sub_le {z z' : E → F} {x₀ : E} {K : NNReal} {U : Set E}
    (h : HasDirDerivAt z z' x₀) (hU : U ∈ 𝓝 x₀) (hL : LipschitzOnWith K z U) (r s : E) :
    ‖z' r - z' s‖ ≤ K * ‖r - s‖ := by
  refine le_of_tendsto ((h r).sub (h s)).norm ?_
  filter_upwards [eventually_add_smul_mem hU r, eventually_add_smul_mem hU s,
    self_mem_nhdsWithin] with t hr hs ht
  have ht' : (0 : ℝ) < t := ht
  have h1 := hL.dist_le_mul _ hr _ hs
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht'] at h1
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos ht']
  calc t⁻¹ * ‖z (x₀ + t • r) - z (x₀ + t • s)‖ ≤ t⁻¹ * (K * (t * ‖r - s‖)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ht'.le)
    _ = K * ‖r - s‖ := by field_simp

/-- The directional derivative is positively homogeneous. -/
theorem HasDirDerivAt.map_smul {z z' : E → F} {x₀ : E} (h : HasDirDerivAt z z' x₀) {c : ℝ}
    (hc : 0 < c) (r : E) : z' (c • r) = c • z' r := by
  have hct : Tendsto (fun t : ℝ ↦ c * t) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const.mul continuous_id :
        Continuous fun t : ℝ ↦ c * t).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ mul_pos hc ht⟩
  have h2 : Tendsto (fun t : ℝ ↦ c • ((c * t)⁻¹ • (z (x₀ + (c * t) • r) - z x₀))) (𝓝[>] 0)
      (𝓝 (c • z' r)) := ((h r).comp hct).const_smul c
  refine tendsto_nhds_unique (h (c • r)) (h2.congr fun t ↦ ?_)
  rw [smul_smul, smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, mul_comm]

/-- A function that is Lipschitz near `x₀` and directionally differentiable at `x₀` is Bouligand
differentiable at `x₀` [Dempe 2002, p. 82]. -/
theorem HasDirDerivAt.isBouligandDiffAt [FiniteDimensional ℝ E] {z z' : E → F} {x₀ : E}
    {K : NNReal} {U : Set E} (h : HasDirDerivAt z z' x₀) (hU : U ∈ 𝓝 x₀)
    (hL : LipschitzOnWith K z U) : IsBouligandDiffAt z z' x₀ := by
  refine ⟨h, Metric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  set η : ℝ := ε / (2 * K + 2) with hη
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hη0 : 0 < η := by positivity
  have hηε : η * (2 * K + 1) < ε := by
    have : η * (2 * K + 2) = ε := by rw [hη]; field_simp
    nlinarith
  obtain ⟨T, hTS, hTfin, hcov⟩ := finite_cover_balls_of_compact (isCompact_sphere (0 : E) 1) hη0
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ d ∈ T, ‖t⁻¹ • (z (x₀ + t • d) - z x₀) - z' d‖ < η :=
    (eventually_all_finite hTfin).2 fun d _ ↦
      (Metric.tendsto_nhds.1 (h d) η hη0).mono fun t ht ↦ by rwa [← dist_eq_norm]
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu : (0 : ℝ) < u := hu
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x₀ (lt_min hu hρ)),
    self_mem_nhdsWithin] with x hx hne
  have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hne
  set τ := ‖x - x₀‖ with hτ
  have hτ0 : 0 < τ := norm_pos_iff.2 hne
  have hτlt : τ < min u ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  set d : E := τ⁻¹ • (x - x₀) with hd
  have hdS : d ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, hd, norm_smul, norm_inv, norm_norm, ← hτ,
      inv_mul_cancel₀ hτ0.ne']
  have hxd : x = x₀ + τ • d := by rw [hd, smul_inv_smul₀ hτ0.ne', add_sub_cancel]
  obtain ⟨e, heT, hde⟩ := mem_iUnion₂.1 (hcov hdS)
  have hde : ‖d - e‖ < η := by rwa [Metric.mem_ball, dist_eq_norm] at hde
  have he1 : ‖e‖ = 1 := mem_sphere_zero_iff_norm.1 (hTS heT)
  have hxU : x ∈ U := hball (Metric.ball_subset_ball (min_le_right _ _) hx)
  have heU : x₀ + τ • e ∈ U := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hτ0, he1, mul_one]
    exact hτlt.trans_le (min_le_right _ _))
  -- the three error terms
  have hA : ‖z x - z (x₀ + τ • e)‖ ≤ τ * (K * η) := by
    have h1 := hL.dist_le_mul _ hxU _ heU
    rw [dist_eq_norm, dist_eq_norm, hxd, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hτ0] at h1
    calc _ ≤ K * (τ * ‖d - e‖) := by rw [hxd]; exact h1
      _ ≤ K * (τ * η) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hde.le hτ0.le) hK0
      _ = τ * (K * η) := by ring
  have hB : ‖z (x₀ + τ • e) - z x₀ - τ • z' e‖ ≤ τ * η := by
    have h1 := hsub ⟨hτ0, hτlt.trans_le (min_le_left _ _)⟩ e heT
    have e1 : z (x₀ + τ • e) - z x₀ - τ • z' e =
        τ • (τ⁻¹ • (z (x₀ + τ • e) - z x₀) - z' e) := by
      rw [smul_sub, smul_inv_smul₀ hτ0.ne']
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
    exact mul_le_mul_of_nonneg_left h1.le hτ0.le
  have hC : ‖τ • z' e - z' (x - x₀)‖ ≤ τ * (K * η) := by
    have e1 : x - x₀ = τ • d := by rw [hxd, add_sub_cancel_left]
    rw [e1, h.map_smul hτ0, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
    refine mul_le_mul_of_nonneg_left ((h.norm_sub_le hU hL e d).trans ?_) hτ0.le
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_left hde.le hK0
  have htot : ‖z x - z x₀ - z' (x - x₀)‖ ≤ τ * (η * (2 * K + 1)) := by
    have e1 : z x - z x₀ - z' (x - x₀) = (z x - z (x₀ + τ • e)) +
        (z (x₀ + τ • e) - z x₀ - τ • z' e) + (τ • z' e - z' (x - x₀)) := by abel
    rw [e1]
    calc _ ≤ ‖z x - z (x₀ + τ • e)‖ + ‖z (x₀ + τ • e) - z x₀ - τ • z' e‖ +
          ‖τ • z' e - z' (x - x₀)‖ := norm_add₃_le
      _ ≤ τ * (K * η) + τ * η + τ * (K * η) := by gcongr
      _ = τ * (η * (2 * K + 1)) := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  calc τ⁻¹ * ‖z x - z x₀ - z' (x - x₀)‖ ≤ τ⁻¹ * (τ * (η * (2 * K + 1))) :=
        mul_le_mul_of_nonneg_left htot (inv_nonneg.2 hτ0.le)
    _ = η * (2 * K + 1) := by field_simp
    _ < ε := hηε

/-- `PC¹` functions on a finite-dimensional space are Bouligand differentiable
[Dempe 2002, p. 82]. -/
theorem IsPC1At.exists_isBouligandDiffAt [FiniteDimensional ℝ E] {z : E → F} {x₀ : E}
    (h : IsPC1At z x₀) : ∃ z', IsBouligandDiffAt z z' x₀ := by
  choose z' hz' using h.exists_tendsto_slope
  obtain ⟨K, U, hU, hL⟩ := h.exists_lipschitzOnWith
  exact ⟨z', HasDirDerivAt.isBouligandDiffAt hz' hU hL⟩

/-- Chain rule for one-sided directional derivatives along a curve: if `(p(t) - p₀) / t → v` as
`t → 0⁺` and `u` is differentiable at `p₀`, then `(u(p(t)) - u(p₀)) / t → u'(v)`. -/
theorem tendsto_slope_comp_of_hasFDerivAt {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {u : X → Y} {u' : X →L[ℝ] Y} {p₀ : X}
    (hu : HasFDerivAt u u' p₀) {p : ℝ → X} {v : X} (hp : Tendsto p (𝓝[>] 0) (𝓝 p₀))
    (hv : Tendsto (fun t ↦ t⁻¹ • (p t - p₀)) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (fun t ↦ t⁻¹ • (u (p t) - u p₀)) (𝓝[>] 0) (𝓝 (u' v)) := by
  have ho : (fun t ↦ u (p t) - u p₀ - u' (p t - p₀)) =o[𝓝[>] 0] fun t ↦ p t - p₀ :=
    hu.isLittleO.comp_tendsto hp
  have ho2 : (fun t : ℝ ↦ t⁻¹ • (u (p t) - u p₀ - u' (p t - p₀))) =o[𝓝[>] 0]
      fun t ↦ t⁻¹ • (p t - p₀) :=
    (Asymptotics.isBigO_refl (fun t : ℝ ↦ t⁻¹) _).smul_isLittleO ho
  have h0 := (Asymptotics.isLittleO_one_iff ℝ).1 (ho2.trans_isBigO (hv.isBigO_one ℝ))
  have h1 := h0.add ((u'.continuous.tendsto v).comp hv)
  rw [zero_add] at h1
  refine h1.congr fun t ↦ ?_
  simp only [Function.comp_apply]
  rw [map_smul]
  simp only [smul_sub]
  abel

/-- A Fréchet differentiable function is directionally differentiable, with `z'(x₀; r) = ∇z(x₀) r`. -/
theorem HasFDerivAt.hasDirDerivAt {z : E → F} {z' : E →L[ℝ] F} {x₀ : E}
    (h : HasFDerivAt z z' x₀) : HasDirDerivAt z z' x₀ := fun r ↦ by
  have hc : Continuous fun t : ℝ ↦ x₀ + t • r := by fun_prop
  have hp : Tendsto (fun t : ℝ ↦ x₀ + t • r) (𝓝[>] 0) (𝓝 x₀) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun t : ℝ ↦ t⁻¹ • ((x₀ + t • r) - x₀)) (𝓝[>] 0) (𝓝 r) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ by
      show r = t⁻¹ • (x₀ + t • r - x₀)
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul])
  exact tendsto_slope_comp_of_hasFDerivAt h hp hv

/-- The pointwise maximum of two `C¹` functions is a `PC¹` function [Dempe 2002, p. 78]. -/
theorem isPC1At_max {f₁ f₂ : E → ℝ} (h₁ : ContDiff ℝ 1 f₁) (h₂ : ContDiff ℝ 1 f₂) (x₀ : E) :
    IsPC1At (fun x ↦ max (f₁ x) (f₂ x)) x₀ := by
  refine ⟨2, ![f₁, f₂], univ, mem_univ _, isOpen_univ,
    (h₁.continuous.max h₂.continuous).continuousOn, fun i ↦ ?_, fun x _ ↦ ?_⟩
  · fin_cases i
    · exact h₁.contDiffOn
    · exact h₂.contDiffOn
  · rcases max_choice (f₁ x) (f₂ x) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

end Bilevel
