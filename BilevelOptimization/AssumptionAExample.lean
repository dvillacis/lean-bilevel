/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.KKTLocal
import BilevelOptimization.PiecewiseSmooth

/-!
# Assumption (A) without (CRCQ): the example on pp. 139–141 of [Dempe 2002]

Thm. 5.4 of [Dempe 2002] (`nonneg_fderiv_of_isLocalMinOn_bilevelFeasible`) needs (CRCQ), or in
this library (LICQ). The book remarks that the weaker assumption (A) of [67] gives directional
derivatives of the follower's solution, but the solution function need not be Lipschitz, its
directional derivative need not be continuous in the direction, and the condition (5.11) with
the lower Dini derivative fails at a global solution. This file verifies the example.

With the letters swapped to the library's convention (leader `x`, follower `y`):

* leader: `min y₂ + x₁² + x₂²` subject to `x₁² + (x₂ + 1)² ≤ 1`;
* follower: `min ½ (y₁ - 1)² + ½ y₂²` subject to `y₁ ≤ 0`, `y₁ + y₂ x₁ + x₂ ≤ 0`,

at `x̄ = ȳ = 0`. The follower's problem is the projection of `(1, 0)` onto a polyhedron, solved in
closed form by `exampleASol`.

## Main results

* `solutionMap_exampleA`: the follower's solution is unique, `Ψ(x) = {y(x)}`.
* `isOptimisticSolution_exampleA`: `(0, 0)` is a global optimistic solution (`y(x) = 0` on the
  leader's feasible set, where `x₂ ≤ 0`).
* `not_lowerLICQ_exampleA`, `not_lowerCRCQ_exampleA`: (LICQ) and (CRCQ) fail at `(0, 0)`.
* `not_lipschitzOnWith_exampleASol`: `y(·)` is not Lipschitz on any neighborhood of `0`.
* `hasDirDerivAt_exampleASol`: `y'(0; r) = (-r₂, -r₁)` if `r₂ > 0` and `0` if `r₂ ≤ 0`.
* `not_continuousAt_exampleADirDeriv`: `y'(0; ·)` is not continuous at `r = (1, 0)`; its limit
  `(0, -1)` from `r₂ > 0` and its value `0` are the two elements of the book's `Ω(r)`.
* `tendsto_slope_exampleAH`, `exampleAG_hasFDerivAt`: the direction `r = (1, 0)` satisfies the
  linearized leader's constraint `∇G(0) r = 0 ≤ 0`, while along `r' = (1, t) → r` the difference
  quotients of `H(x) = F(x, y(x))` tend to `-1`. So the lower Dini derivative `H₊(0; r) ≤ -1 < 0`
  at the global solution, and (5.11) with the lower Dini derivative is not a necessary condition.

## Differences from [Dempe 2002]

* Assumption (A) itself and the sets `Ω(r)` (optimal solutions of `QP(λ, r)` over the vertices of
  `Λ(x̄, ȳ)`) are not formalized; the file verifies the concrete facts behind the book's
  conclusions: failure of (LICQ)/(CRCQ), the solution function, the discontinuity of
  `y'(0; ·)`, and the negative lower Dini derivative at the global solution.
* The book computes `H₊(0; r) = -1` as a `liminf` over `t → 0+`, `r' → r`; we exhibit the curve
  `r' = (1, t)` along which the quotients tend to `-1`, which gives `H₊(0; r) ≤ -1`.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

/-- The leader's objective `F(x, y) = y₂ + x₁² + x₂²` of the example on p. 140. -/
def exampleAF (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := p.2.2 + p.1.1 ^ 2 + p.1.2 ^ 2

/-- The follower's objective `½ (y₁ - 1)² + ½ y₂²` of the example on p. 140. -/
noncomputable def exampleAφ (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ := (p.2.1 - 1) ^ 2 / 2 + p.2.2 ^ 2 / 2

/-- The follower's constraints `y₁ ≤ 0`, `y₁ + y₂ x₁ + x₂ ≤ 0` of the example on p. 140. -/
noncomputable def exampleAg : Fin 2 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
  ![fun p ↦ p.2.1, fun p ↦ p.2.1 + p.2.2 * p.1.1 + p.1.2]

/-- The leader's constraint function `G(x) = x₁² + (x₂ + 1)² - 1`. -/
def exampleAG (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + (x.2 + 1) ^ 2 - 1

/-- The leader's feasible set `{x | G(x) ≤ 0}`. -/
def exampleAΩ : Set (ℝ × ℝ) := {x | exampleAG x ≤ 0}

/-- The follower's solution function: the projection of `(1, 0)` onto the follower's
constraint set. -/
noncomputable def exampleASol (x : ℝ × ℝ) : ℝ × ℝ :=
  if x.2 ≤ 0 then 0
  else if x.1 ^ 2 ≤ x.2 then
    (1 - (1 + x.2) / (1 + x.1 ^ 2), -x.1 * ((1 + x.2) / (1 + x.1 ^ 2)))
  else (0, -x.2 / x.1)

/-- The composite leader's objective `H(x) = F(x, y(x))`. -/
noncomputable def exampleAH (x : ℝ × ℝ) : ℝ := exampleAF (x, exampleASol x)

theorem mem_lowerFeasible_exampleA {x y : ℝ × ℝ} :
    y ∈ lowerFeasible exampleAg x ↔ y.1 ≤ 0 ∧ y.1 + y.2 * x.1 + x.2 ≤ 0 := by
  simp [lowerFeasible, exampleAg, Fin.forall_fin_two]

theorem exampleASol_of_nonpos {x : ℝ × ℝ} (hx : x.2 ≤ 0) : exampleASol x = 0 := if_pos hx

theorem exampleASol_parabola {a : ℝ} (ha : a ≠ 0) : exampleASol (a, a ^ 2) = (0, -a) := by
  have h1 : ¬ (a, a ^ 2).2 ≤ 0 := by simp only [not_le]; positivity
  have h2 : (a, a ^ 2).1 ^ 2 ≤ (a, a ^ 2).2 := le_rfl
  rw [exampleASol, if_neg h1, if_pos h2]
  have h3 : (1 + a ^ 2) / (1 + a ^ 2) = 1 := div_self (by positivity)
  simp only [h3]
  ext <;> simp

theorem exampleASol_mem (x : ℝ × ℝ) : exampleASol x ∈ lowerFeasible exampleAg x := by
  rw [mem_lowerFeasible_exampleA]
  unfold exampleASol
  split_ifs with ha hb
  · simpa using ha
  · push Not at ha
    have hd : 0 < 1 + x.1 ^ 2 := by positivity
    have hc : (1 + x.2) / (1 + x.1 ^ 2) * (1 + x.1 ^ 2) = 1 + x.2 := by field_simp
    have hc1 : 1 ≤ (1 + x.2) / (1 + x.1 ^ 2) := by rw [le_div_iff₀ hd]; linarith
    refine ⟨by dsimp only; linarith, le_of_eq ?_⟩
    dsimp only
    linear_combination (-1 : ℝ) * hc
  · push Not at ha hb
    have hx1 : x.1 ≠ 0 := by rintro h; rw [h] at hb; nlinarith
    refine ⟨le_rfl, le_of_eq ?_⟩
    dsimp only
    field_simp
    ring

/-- The follower's objective grows quadratically away from `y(x)` on the follower's feasible
set (the objective is `½ ‖y - (1, 0)‖²` and `y(x)` is a KKT point). -/
theorem exampleAφ_add_le {x z : ℝ × ℝ} (hz : z ∈ lowerFeasible exampleAg x) :
    exampleAφ (x, exampleASol x) +
        ((z.1 - (exampleASol x).1) ^ 2 + (z.2 - (exampleASol x).2) ^ 2) / 2 ≤
      exampleAφ (x, z) := by
  rw [mem_lowerFeasible_exampleA] at hz
  obtain ⟨h1, h2⟩ := hz
  simp only [exampleAφ]
  unfold exampleASol
  split_ifs with ha hb
  · simp only [Prod.fst_zero, Prod.snd_zero]
    nlinarith
  · push Not at ha
    set c := (1 + x.2) / (1 + x.1 ^ 2) with hc
    have hc' : c * (1 + x.1 ^ 2) = 1 + x.2 := by rw [hc]; field_simp
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hc'' : c * (c * (1 + x.1 ^ 2)) = c * (1 + x.2) := by rw [hc']
    have hnn : 0 ≤ c * (-x.2 - (z.1 + z.2 * x.1)) := mul_nonneg hc0 (by linarith)
    nlinarith
  · push Not at ha hb
    have hx1 : x.1 ≠ 0 := by rintro h; rw [h] at hb; nlinarith
    have hx1' : 0 < x.1 ^ 2 := by positivity
    set l := x.2 / x.1 ^ 2 with hl
    have hl' : l * x.1 ^ 2 = x.2 := by rw [hl]; field_simp
    have hw : -x.2 / x.1 = -(l * x.1) := by rw [hl]; field_simp
    have hl0 : 0 ≤ l := by rw [hl]; positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hx1']; exact hb.le
    have hl'' : l * (l * x.1 ^ 2) = l * x.2 := by rw [hl']
    rw [hw]
    have hn1 : 0 ≤ (1 - l) * (-z.1) := mul_nonneg (by linarith) (by linarith)
    have hn2 : 0 ≤ l * (-(z.1 + z.2 * x.1 + x.2)) := mul_nonneg hl0 (by linarith)
    nlinarith

/-- The follower's solution is unique: `Ψ(x) = {y(x)}`. -/
theorem solutionMap_exampleA (x : ℝ × ℝ) :
    solutionMap exampleAφ (lowerFeasible exampleAg) x = {exampleASol x} := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · have h1 := exampleAφ_add_le hy.1
    have h2 := hy.2 _ (exampleASol_mem x)
    have h3 : (y.1 - (exampleASol x).1) ^ 2 + (y.2 - (exampleASol x).2) ^ 2 = 0 :=
      le_antisymm (by linarith) (by positivity)
    obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h3
    exact Prod.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e1))
      (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e2))
  · rw [mem_singleton_iff.1 hy]
    refine ⟨exampleASol_mem x, fun z hz ↦ ?_⟩
    have := exampleAφ_add_le hz
    have : 0 ≤ ((z.1 - (exampleASol x).1) ^ 2 + (z.2 - (exampleASol x).2) ^ 2) / 2 := by
      positivity
    linarith

theorem nonpos_of_mem_exampleAΩ {x : ℝ × ℝ} (hx : x ∈ exampleAΩ) : x.2 ≤ 0 := by
  have : x.1 ^ 2 + (x.2 + 1) ^ 2 - 1 ≤ 0 := hx
  nlinarith [sq_nonneg x.1]

/-- `(0, 0)` is a global optimistic solution: on the leader's feasible set `y(x) = 0` and
`H(x) = x₁² + x₂²`. -/
theorem isOptimisticSolution_exampleA :
    IsOptimisticSolution exampleAF exampleAφ (lowerFeasible exampleAg) exampleAΩ 0 0 := by
  have hΨ : ∀ x, exampleASol x ∈ solutionMap exampleAφ (lowerFeasible exampleAg) x := fun x ↦ by
    rw [solutionMap_exampleA]; exact mem_singleton _
  have hov : ∀ x, optimisticValue exampleAF exampleAφ (lowerFeasible exampleAg) x =
      exampleAF (x, exampleASol x) := fun x ↦
    optimisticValue_eq (hΨ x) fun z hz ↦ by
      rw [solutionMap_exampleA, mem_singleton_iff] at hz
      rw [hz]
  have h0 : exampleASol 0 = 0 := exampleASol_of_nonpos (by simp)
  refine ⟨by simp [exampleAΩ, exampleAG], by have := hΨ 0; rwa [h0] at this, fun y hy ↦ ?_, isMinOn_iff.2 fun x hx ↦ ?_⟩
  · rw [solutionMap_exampleA, h0, mem_singleton_iff] at hy
    rw [hy]
  · rw [hov, hov, h0, exampleASol_of_nonpos (nonpos_of_mem_exampleAΩ hx)]
    exact EReal.coe_le_coe_iff.2 (by simp [exampleAF]; positivity)

/-- (LICQ) fails at `(0, 0)`: both constraints are active with the same gradient `(1, 0)`. -/
theorem not_lowerLICQ_exampleA : ¬ LowerLICQ exampleAg 0 0 := by
  intro h
  have h0 : exampleAg 0 ((0 : ℝ × ℝ), (0 : ℝ × ℝ)) = 0 := by simp [exampleAg]
  have h1 : exampleAg 1 ((0 : ℝ × ℝ), (0 : ℝ × ℝ)) = 0 := by simp [exampleAg]
  have he : (fun z : ℝ × ℝ ↦ exampleAg 0 (0, z)) = fun z ↦ exampleAg 1 (0, z) := by
    funext z
    simp [exampleAg]
  have := h.injective (a₁ := ⟨0, h0⟩) (a₂ := ⟨1, h1⟩) (by simp only [he])
  simp at this

theorem fderiv_exampleAg_zero (x y : ℝ × ℝ) :
    fderiv ℝ (fun z ↦ exampleAg 0 (x, z)) y = ContinuousLinearMap.fst ℝ ℝ ℝ := by
  have : (fun z : ℝ × ℝ ↦ exampleAg 0 (x, z)) = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    funext z
    simp [exampleAg]
  rw [this]
  exact (ContinuousLinearMap.fst ℝ ℝ ℝ).fderiv

theorem fderiv_exampleAg_one (x y : ℝ × ℝ) :
    fderiv ℝ (fun z ↦ exampleAg 1 (x, z)) y =
      ContinuousLinearMap.fst ℝ ℝ ℝ + x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have : (fun z : ℝ × ℝ ↦ exampleAg 1 (x, z)) =
      fun z ↦ (ContinuousLinearMap.fst ℝ ℝ ℝ + x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ) z + x.2 := by
    funext z
    simp [exampleAg, mul_comm]
  rw [this]
  exact ((ContinuousLinearMap.fst ℝ ℝ ℝ + x.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.add_const
    x.2).fderiv

/-- (CRCQ) fails at `(0, 0)`: the gradients `(1, 0)`, `(1, x₁)` of the two active constraints
have rank `1` at `x₁ = 0` and rank `2` for `x₁ ≠ 0`. -/
theorem not_lowerCRCQ_exampleA : ¬ LowerCRCQ exampleAg 0 0 := by
  intro h
  have hact : ∀ i ∈ (univ : Set (Fin 2)), exampleAg i ((0 : ℝ × ℝ), (0 : ℝ × ℝ)) = 0 := by
    intro i _
    fin_cases i <;> simp [exampleAg]
  have hev := h univ hact
  have hc : Tendsto (fun s : ℝ ↦ (((s, 0) : ℝ × ℝ), (0 : ℝ × ℝ))) (𝓝[≠] 0)
      (𝓝 ((0 : ℝ × ℝ), (0 : ℝ × ℝ))) :=
    ((by fun_prop : Continuous fun s : ℝ ↦ (((s, 0) : ℝ × ℝ), (0 : ℝ × ℝ))).tendsto' 0 _
      (by simp)).mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hs0⟩ := ((hc.eventually hev).and self_mem_nhdsWithin).exists
  have hs0 : s ≠ 0 := hs0
  -- the gradients at the base point
  have hbase : (range fun i : (univ : Set (Fin 2)) ↦
      fderiv ℝ (fun z ↦ exampleAg i.1 ((0 : ℝ × ℝ), z)) (0 : ℝ × ℝ)) =
      {ContinuousLinearMap.fst ℝ ℝ ℝ} := by
    ext v
    simp only [mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, -⟩, rfl⟩
      fin_cases i
      · exact fderiv_exampleAg_zero _ _
      · simp [fderiv_exampleAg_one]
    · rintro rfl
      exact ⟨⟨0, mem_univ _⟩, fderiv_exampleAg_zero _ _⟩
  -- the gradients at the nearby point
  have hli : LinearIndependent ℝ fun i : (univ : Set (Fin 2)) ↦
      fderiv ℝ (fun z ↦ exampleAg i.1 (((s, 0) : ℝ × ℝ), z)) (0 : ℝ × ℝ) := by
    have hv : LinearIndependent ℝ ![ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.fst ℝ ℝ ℝ + s • ContinuousLinearMap.snd ℝ ℝ ℝ] := by
      refine LinearIndependent.pair_iff.2 fun a b hab ↦ ?_
      have e1 := congrArg (fun l : StrongDual ℝ (ℝ × ℝ) ↦ l (1, 0)) hab
      have e2 := congrArg (fun l : StrongDual ℝ (ℝ × ℝ) ↦ l (0, 1)) hab
      simp at e1 e2
      have hb : b = 0 := by
        rcases e2 with h | h
        · exact h
        · exact absurd h hs0
      exact ⟨by rw [hb] at e1; linarith, hb⟩
    have := hv.comp (fun i : (univ : Set (Fin 2)) ↦ i.1) Subtype.val_injective
    convert this using 1
    funext i
    obtain ⟨i, -⟩ := i
    fin_cases i
    · simp [fderiv_exampleAg_zero]
    · simp [fderiv_exampleAg_one]
  rw [hbase, finrank_span_singleton (by
    intro h
    have := congrArg (fun l : StrongDual ℝ (ℝ × ℝ) ↦ l (1, 0)) h
    simp at this), finrank_span_eq_card hli] at hs
  simp at hs

/-- `y(·)` is not Lipschitz on any neighborhood of `0`: `y(a, a²) = (0, -a)` while
`y(a, 0) = 0`. -/
theorem not_lipschitzOnWith_exampleASol (K : NNReal) {U : Set (ℝ × ℝ)} (hU : U ∈ 𝓝 0) :
    ¬ LipschitzOnWith K exampleASol U := by
  intro hL
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  set a : ℝ := min (ε / 2) (min (1 / 2) (1 / (2 * ((K : ℝ) + 1)))) with ha_def
  have hK : (0 : ℝ) ≤ K := K.2
  have ha : 0 < a := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have haε : a < ε := (min_le_left _ _).trans_lt (by linarith)
  have ha1 : a < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have haK : (K : ℝ) * a < 1 := by
    have h1 : a ≤ 1 / (2 * ((K : ℝ) + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hx : ((a, a ^ 2) : ℝ × ℝ) ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ha, abs_of_pos (by positivity)]
    constructor <;> nlinarith)
  have hx' : ((a, 0) : ℝ × ℝ) ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ha]
    simpa using ⟨haε, hε⟩)
  have h := hL.dist_le_mul _ hx _ hx'
  rw [exampleASol_parabola ha.ne', exampleASol_of_nonpos (by simp)] at h
  have h' : a ≤ K * a ^ 2 := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos ha, ha.le, (pow_pos ha 2).le] using h
  nlinarith

/-- The directional derivative `y'(0; r)` [Dempe 2002, p. 141]. -/
noncomputable def exampleADirDeriv (r : ℝ × ℝ) : ℝ × ℝ := if r.2 ≤ 0 then 0 else (-r.2, -r.1)

/-- `y(·)` is directionally differentiable at `0` with `y'(0; r) = (-r₂, -r₁)` if `r₂ > 0` and
`y'(0; r) = 0` if `r₂ ≤ 0`. -/
theorem hasDirDerivAt_exampleASol : HasDirDerivAt exampleASol exampleADirDeriv 0 := by
  intro r
  have h0 : exampleASol 0 = 0 := exampleASol_of_nonpos (by simp)
  simp only [zero_add, h0, sub_zero]
  by_cases hr : r.2 ≤ 0
  · rw [exampleADirDeriv, if_pos hr]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [exampleASol_of_nonpos (by simpa using mul_nonpos_of_nonneg_of_nonpos ht.le hr),
      smul_zero]
  · push Not at hr
    rw [exampleADirDeriv, if_neg (not_le.2 hr)]
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), t * r.1 ^ 2 < r.2 := by
      have hc : Tendsto (fun t : ℝ ↦ t * r.1 ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id.mul_const (r.1 ^ 2) :
          Tendsto (fun t : ℝ ↦ t * r.1 ^ 2) (𝓝 0) (𝓝 (0 * r.1 ^ 2)))
      exact hc.eventually (gt_mem_nhds hr)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • exampleASol (t • r) =
        ((t * r.1 ^ 2 - r.2) / (1 + t ^ 2 * r.1 ^ 2),
          -r.1 * ((1 + t * r.2) / (1 + t ^ 2 * r.1 ^ 2))) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsmall] with t (ht : 0 < t) h
      have h2 : ¬ (t • r).2 ≤ 0 := by
        simp only [Prod.smul_snd, smul_eq_mul, not_le]
        positivity
      have h3 : (t • r).1 ^ 2 ≤ (t • r).2 := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith
      rw [exampleASol, if_neg h2, if_pos h3]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
      have ht0 : t ≠ 0 := ht.ne'
      have hd1 : 1 + (t * r.1) ^ 2 ≠ 0 := by positivity
      have hd2 : 1 + t ^ 2 * r.1 ^ 2 ≠ 0 := by positivity
      ext
      · field_simp
        ring
      · field_simp
    refine Tendsto.congr' (EventuallyEq.symm hev) ?_
    have hcont : Continuous fun t : ℝ ↦ ((t * r.1 ^ 2 - r.2) / (1 + t ^ 2 * r.1 ^ 2),
        -r.1 * ((1 + t * r.2) / (1 + t ^ 2 * r.1 ^ 2))) := by
      fun_prop (disch := exact fun t ↦ by positivity)
    exact (hcont.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds

/-- `y'(0; ·)` is not continuous at `r = (1, 0)`: `y'(0; (1, s)) = (-s, -1) → (0, -1)` as
`s → 0+`, while `y'(0; (1, 0)) = 0`. -/
theorem not_continuousAt_exampleADirDeriv : ¬ ContinuousAt exampleADirDeriv (1, 0) := by
  intro h
  have hc : Tendsto (fun s : ℝ ↦ ((1, s) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 (1, 0)) :=
    ((by fun_prop : Continuous fun s : ℝ ↦ ((1, s) : ℝ × ℝ)).tendsto' 0 _ rfl).mono_left
      nhdsWithin_le_nhds
  have h1 := h.tendsto.comp hc
  have h2 : Tendsto (exampleADirDeriv ∘ fun s : ℝ ↦ ((1, s) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 (0, -1)) := by
    have hev : (fun s : ℝ ↦ ((-s, -1) : ℝ × ℝ)) =ᶠ[𝓝[>] 0]
        exampleADirDeriv ∘ fun s : ℝ ↦ ((1, s) : ℝ × ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      simp [exampleADirDeriv, not_le.2 hs]
    refine Tendsto.congr' hev ?_
    exact ((by fun_prop : Continuous fun s : ℝ ↦ ((-s, -1) : ℝ × ℝ)).tendsto' 0 _
      (by simp)).mono_left nhdsWithin_le_nhds
  have := congrArg Prod.snd (tendsto_nhds_unique h1 h2)
  simp [exampleADirDeriv] at this

/-- The leader's constraint has gradient `∇G(0) = (0, 2)`, so the direction `r = (1, 0)`
satisfies the linearized constraint `∇G(0) r = 0 ≤ 0` of (5.11). -/
theorem exampleAG_hasFDerivAt :
    HasFDerivAt exampleAG ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 ∧ exampleAG 0 = 0 ∧
      ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) = 0 := by
  refine ⟨?_, by simp [exampleAG], by simp⟩
  have h1 : HasFDerivAt (fun x : ℝ × ℝ ↦ x.1 ^ 2) (0 : StrongDual ℝ (ℝ × ℝ)) 0 := by
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ)) (E := ℝ) (F := ℝ)).pow 2
    simpa using this
  have h2 : HasFDerivAt (fun x : ℝ × ℝ ↦ (x.2 + 1) ^ 2)
      ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
    have := ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ)) (E := ℝ) (F := ℝ)).add_const
      (1 : ℝ)).pow 2
    simpa using this
  have := (h1.add h2).sub_const 1
  rw [zero_add] at this
  exact this

/-- Along `r' = (1, t) → r = (1, 0)` the difference quotients of `H(x) = F(x, y(x))` at the
global solution `0` tend to `-1`: the lower Dini derivative `H₊(0; r)` is at most `-1 < 0`, so
(5.11) with the lower Dini derivative is not a necessary optimality condition. -/
theorem tendsto_slope_exampleAH :
    Tendsto (fun t : ℝ ↦ t⁻¹ * (exampleAH (t • ((1, t) : ℝ × ℝ)) - exampleAH 0)) (𝓝[>] 0)
      (𝓝 (-1)) := by
  have h0 : exampleAH 0 = 0 := by
    simp [exampleAH, exampleASol_of_nonpos (x := 0) (by simp), exampleAF]
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (exampleAH (t • ((1, t) : ℝ × ℝ)) - exampleAH 0) = -1 + t + t ^ 3 := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hp : t • ((1, t) : ℝ × ℝ) = (t, t ^ 2) := by ext <;> simp [sq]
    rw [hp, h0, exampleAH, exampleASol_parabola ht.ne']
    simp only [exampleAF, sub_zero]
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  exact ((by fun_prop : Continuous fun t : ℝ ↦ -1 + t + t ^ 3).tendsto' 0 _ (by norm_num)).mono_left
    nhdsWithin_le_nhds

end Bilevel
