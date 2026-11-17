/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.ActiveConstraints
import BilevelOptimization.ValueFunctionDirectional

/-!
# Examples on the generalized Jacobian of the solution function

Two examples of Sect. 4.4.2 of [Dempe 2002] (roles of `x` and `y` swapped to the library's
convention: the parameter is `x`, the follower's variable `y`).

* pp. 89–90 [78]: `min {(y₁ − x)² + y₂² : −y₁ + y₂ ≤ 0, y₁ + y₂ ≤ 0}` at `x̄ = 0`. (LICQ),
  (SSOC) hold with the unique multiplier `λ = 0`, so every `I ⊆ {1, 2}` is admissible, but only
  `{1}` and `{2}` are strongly active: `∂y(0) = conv {(½, ½), (½, −½)}`, and the Jacobians of the
  selection functions of `I = {1, 2}` and `I = ∅`, `(0, 0)` and `(1, 0)`, are not in `∂y(0)`.
* p. 93 [71]: `min {(y − x)² : y − x ≤ 0}`. Here `y(x) = x`, (LICQ) and (SSOC) hold with
  `λ = 0`, `y'(x; r) = r` makes the constraint active in `QP(0, r)`, and the strict
  complementarity condition (SCR) fails for every index set and every direction, so the first
  assertion of Thm. 4.12 never applies; Thm. 4.13 applies to every direction since
  `R({1}, 0)` is the whole line.

## Main results

* `solutionMap_exampleJ`, `isMinOn_exampleJSel`, `stronglyActive_exampleJ`,
  `clarkeJacobian_exampleJ`, `fderiv_exampleJSel_both_not_mem`,
  `fderiv_exampleJSel_empty_not_mem`, `lowerLICQ_exampleJ`, `lowerMultipliers_exampleJ`,
  `lowerSSOC_exampleJ`.
* `solutionMap_exampleS`, `lowerLICQ_exampleS`, `lowerMultipliers_exampleS`, `lowerSSOC_exampleS`,
  `not_lowerSCR_exampleS`, `lowerQPRegion_exampleS`.

## Differences from the book

* In the first example the book's labels of the constraints are inconsistent (the problem lists
  `−y₁ + y₂ ≤ 0` first, the Lagrangian `y₁ + y₂` first, and `I = {1}` yields `(½, ½)` in both
  bullet points); we number the constraints as in the problem, so `y^{1}(x) = (x/2, x/2)` and
  `y^{2}(x) = (x/2, −x/2)`.
* The selection functions are given in closed form and shown to solve the problems (4.19) with the
  constraints in `I` as equations; they are not identified with the implicit-function selections
  `lowerSolutionSelection` of the general theory.
* (MFCQ) and (CRCQ) are replaced by the stronger (LICQ), which holds in both examples.
-/

open Filter Topology Set
open VariationalAnalysis (lowerFeasible)

namespace Bilevel

/-! ### The example on pp. 89–90 -/

/-- The follower's objective `(y₁ − x)² + y₂²` of the example on pp. 89–90 of [Dempe 2002]. -/
def exampleJφ (p : ℝ × (ℝ × ℝ)) : ℝ := (p.2.1 - p.1) ^ 2 + p.2.2 ^ 2

/-- The follower's constraints `−y₁ + y₂ ≤ 0`, `y₁ + y₂ ≤ 0`. -/
noncomputable def exampleJg : Fin 2 → ℝ × (ℝ × ℝ) → ℝ :=
  ![fun p ↦ -p.2.1 + p.2.2, fun p ↦ p.2.1 + p.2.2]

/-- The solution function: `(x/2, x/2)` for `x ≤ 0` and `(x/2, −x/2)` for `x > 0`. -/
noncomputable def exampleJSol (x : ℝ) : ℝ × ℝ :=
  if x ≤ 0 then (x / 2, x / 2) else (x / 2, -(x / 2))

theorem mem_lowerFeasible_exampleJ {x : ℝ} {y : ℝ × ℝ} :
    y ∈ lowerFeasible exampleJg x ↔ -y.1 + y.2 ≤ 0 ∧ y.1 + y.2 ≤ 0 := by
  simp [lowerFeasible, Fin.forall_fin_two, exampleJg]

theorem exampleJSol_mem (x : ℝ) : exampleJSol x ∈ lowerFeasible exampleJg x := by
  rw [mem_lowerFeasible_exampleJ]
  unfold exampleJSol
  split_ifs with h
  · constructor <;> (norm_num; try linarith)
  · constructor <;> (norm_num; try linarith)

/-- Quadratic growth: `φ(x, y) ≥ φ(x, y(x)) + ‖y − y(x)‖²` on the feasible set. -/
theorem exampleJφ_add_le {x : ℝ} {y : ℝ × ℝ} (hy : y ∈ lowerFeasible exampleJg x) :
    exampleJφ (x, exampleJSol x) +
        ((y.1 - (exampleJSol x).1) ^ 2 + (y.2 - (exampleJSol x).2) ^ 2) ≤ exampleJφ (x, y) := by
  obtain ⟨h0, h1⟩ := mem_lowerFeasible_exampleJ.1 hy
  unfold exampleJSol exampleJφ
  split_ifs with hx
  · simp only
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hx h0]
  · simp only
    nlinarith [mul_nonneg (not_le.1 hx).le (neg_nonneg.2 h1)]

/-- The solution set mapping of the example on pp. 89–90 is `Ψ(x) = {y(x)}`. -/
theorem solutionMap_exampleJ (x : ℝ) :
    solutionMap exampleJφ (lowerFeasible exampleJg) x = {exampleJSol x} := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · have h1 := exampleJφ_add_le hy.1
    have h2 := hy.2 _ (exampleJSol_mem x)
    have h3 : (y.1 - (exampleJSol x).1) ^ 2 + (y.2 - (exampleJSol x).2) ^ 2 = 0 :=
      le_antisymm (by linarith) (by positivity)
    obtain ⟨e1, e2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h3
    exact Prod.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e1))
      (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e2))
  · rw [mem_singleton_iff.1 hy]
    refine ⟨exampleJSol_mem x, fun z hz ↦ ?_⟩
    have := exampleJφ_add_le hz
    have : 0 ≤ (z.1 - (exampleJSol x).1) ^ 2 + (z.2 - (exampleJSol x).2) ^ 2 := by positivity
    linarith

/-- The selection functions `y^I(x)` of the example on pp. 89–90: `y^{1,2} = 0`,
`y^{1}(x) = (x/2, x/2)`, `y^{2}(x) = (x/2, −x/2)`, `y^∅(x) = (x, 0)` (constraints numbered from
`0` in Lean). -/
noncomputable def exampleJSel (I : Finset (Fin 2)) (x : ℝ) : ℝ × ℝ :=
  if 0 ∈ I then (if 1 ∈ I then 0 else (x / 2, x / 2))
  else if 1 ∈ I then (x / 2, -(x / 2)) else (x, 0)

theorem finset_fin_two_cases (I : Finset (Fin 2)) :
    I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I
  decide

theorem exampleJSel_both (x : ℝ) : exampleJSel {0, 1} x = 0 := by simp [exampleJSel]

theorem exampleJSel_zero (x : ℝ) : exampleJSel {0} x = (x / 2, x / 2) := by simp [exampleJSel]

theorem exampleJSel_one (x : ℝ) : exampleJSel {1} x = (x / 2, -(x / 2)) := by
  simp [exampleJSel]

theorem exampleJSel_empty (x : ℝ) : exampleJSel ∅ x = (x, 0) := by simp [exampleJSel]

/-- `y^I(x)` solves the problem (4.19): minimize `φ(x, ·)` subject to `gᵢ(x, ·) = 0`, `i ∈ I`. -/
theorem isMinOn_exampleJSel (I : Finset (Fin 2)) (x : ℝ) :
    (∀ i ∈ I, exampleJg i (x, exampleJSel I x) = 0) ∧
      IsMinOn (fun y ↦ exampleJφ (x, y)) {y | ∀ i ∈ I, exampleJg i (x, y) = 0}
        (exampleJSel I x) := by
  rcases finset_fin_two_cases I with rfl | rfl | rfl | rfl
  · refine ⟨by simp, fun y _ ↦ ?_⟩
    show exampleJφ (x, exampleJSel ∅ x) ≤ exampleJφ (x, y)
    rw [exampleJSel_empty]
    simp only [exampleJφ]
    nlinarith [sq_nonneg (y.1 - x), sq_nonneg y.2]
  · refine ⟨by simp [exampleJg, exampleJSel_zero], fun y hy ↦ ?_⟩
    have h : -y.1 + y.2 = 0 := by simpa [exampleJg] using hy
    have e : y.2 = y.1 := by linarith
    show exampleJφ (x, exampleJSel {0} x) ≤ exampleJφ (x, y)
    rw [exampleJSel_zero]
    simp only [exampleJφ]
    rw [e]
    nlinarith [sq_nonneg (y.1 - x / 2)]
  · refine ⟨by simp [exampleJg, exampleJSel_one], fun y hy ↦ ?_⟩
    have h : y.1 + y.2 = 0 := by simpa [exampleJg] using hy
    have e : y.2 = -y.1 := by linarith
    show exampleJφ (x, exampleJSel {1} x) ≤ exampleJφ (x, y)
    rw [exampleJSel_one]
    simp only [exampleJφ]
    rw [e]
    nlinarith [sq_nonneg (y.1 - x / 2)]
  · refine ⟨by simp [exampleJg, exampleJSel_both], fun y hy ↦ ?_⟩
    have h0 : -y.1 + y.2 = 0 := by simpa [exampleJg] using hy 0 (by simp)
    have h1 : y.1 + y.2 = 0 := by simpa [exampleJg] using hy 1 (by simp)
    have e : y = 0 := Prod.ext (by simp; linarith) (by simp; linarith)
    show exampleJφ (x, exampleJSel {0, 1} x) ≤ exampleJφ (x, y)
    rw [e, exampleJSel_both]

theorem supp_exampleJSel_both : {x | exampleJSol x = exampleJSel {0, 1} x} = {0} := by
  ext x
  show exampleJSol x = exampleJSel {0, 1} x ↔ x = 0
  rw [exampleJSel_both]
  unfold exampleJSol
  split_ifs with h <;> simp [Prod.ext_iff]

theorem supp_exampleJSel_zero : {x | exampleJSol x = exampleJSel {0} x} = Iic 0 := by
  ext x
  show exampleJSol x = exampleJSel {0} x ↔ x ≤ 0
  rw [exampleJSel_zero]
  unfold exampleJSol
  split_ifs with h
  · simp [h]
  · simp only [Prod.mk.injEq, true_and, h, iff_false]
    intro h'
    exact h (by linarith)

theorem supp_exampleJSel_one : {x | exampleJSol x = exampleJSel {1} x} = Ici 0 := by
  ext x
  show exampleJSol x = exampleJSel {1} x ↔ 0 ≤ x
  rw [exampleJSel_one]
  unfold exampleJSol
  split_ifs with h
  · simp only [Prod.mk.injEq, true_and]
    constructor <;> intro h' <;> linarith
  · simp only [true_iff]
    linarith

theorem supp_exampleJSel_empty : {x | exampleJSol x = exampleJSel ∅ x} = {0} := by
  ext x
  show exampleJSol x = exampleJSel ∅ x ↔ x = 0
  rw [exampleJSel_empty]
  unfold exampleJSol
  split_ifs with h <;> simp only [Prod.mk.injEq] <;> constructor <;>
    first | (rintro ⟨h1, h2⟩; linarith) | (rintro rfl; norm_num at h ⊢)

theorem exampleJSol_eq_abs : exampleJSol = fun x ↦ (x / 2, -(|x| / 2)) := by
  funext x
  unfold exampleJSol
  split_ifs with h
  · rw [abs_of_nonpos h]
    ring_nf
  · rw [abs_of_pos (not_le.1 h)]

theorem continuous_exampleJSol : Continuous exampleJSol := by
  rw [exampleJSol_eq_abs]
  fun_prop

/-- Each selection function is linear: `y^I(x) = x • y^I(1)`. -/
theorem exampleJSel_eq_toSpanSingleton (I : Finset (Fin 2)) :
    exampleJSel I = ContinuousLinearMap.toSpanSingleton ℝ (exampleJSel I 1) := by
  funext x
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  rcases finset_fin_two_cases I with rfl | rfl | rfl | rfl
  · simp [exampleJSel_empty]
  · simp only [exampleJSel_zero, Prod.smul_mk, smul_eq_mul]
    ext <;> ring
  · simp only [exampleJSel_one, Prod.smul_mk, smul_eq_mul]
    ext <;> ring
  · simp [exampleJSel_both]

theorem fderiv_exampleJSel (I : Finset (Fin 2)) (x : ℝ) :
    fderiv ℝ (exampleJSel I) x = ContinuousLinearMap.toSpanSingleton ℝ (exampleJSel I 1) := by
  conv_lhs => rw [exampleJSel_eq_toSpanSingleton I]
  exact (ContinuousLinearMap.toSpanSingleton ℝ (exampleJSel I 1)).fderiv

/-- The solution function is a continuous selection of the four functions `y^I`. -/
theorem isPC1Selection_exampleJ : IsPC1Selection exampleJSol exampleJSel univ := by
  refine ⟨isOpen_univ, continuous_exampleJSol.continuousOn, fun I ↦ ?_, fun x _ ↦ ?_⟩
  · rw [exampleJSel_eq_toSpanSingleton I]
    exact (ContinuousLinearMap.contDiff _).contDiffOn
  · by_cases hx : x ≤ 0
    · exact ⟨{0}, (Set.ext_iff.1 supp_exampleJSel_zero x).2 hx⟩
    · exact ⟨{1}, (Set.ext_iff.1 supp_exampleJSel_one x).2 (not_le.1 hx).le⟩

/-- Only `y^{1}` and `y^{2}` are strongly active at `x̄ = 0`; `Supp(y, y^{1,2}) = Supp(y, y^∅) = {0}`
have empty interior. -/
theorem stronglyActive_exampleJ : stronglyActive exampleJSol exampleJSel 0 = {{0}, {1}} := by
  ext I
  show (0 : ℝ) ∈ closure (interior {x | exampleJSol x = exampleJSel I x}) ↔ _
  rcases finset_fin_two_cases I with rfl | rfl | rfl | rfl
  · rw [supp_exampleJSel_empty, interior_singleton, closure_empty]
    simp
  · rw [supp_exampleJSel_zero, interior_Iic, closure_Iio]
    simp
  · rw [supp_exampleJSel_one, interior_Ici, closure_Ioi]
    simp
  · rw [supp_exampleJSel_both, interior_singleton, closure_empty]
    simp only [mem_empty_iff_false, mem_insert_iff, mem_singleton_iff, false_iff]
    decide

/-- `∂y(0) = conv {(½, ½), (½, −½)}` (Thm. 4.7). -/
theorem clarkeJacobian_exampleJ :
    clarkeJacobian exampleJSol 0 =
      segment ℝ (ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ), -(1 / 2 : ℝ))) := by
  rw [isPC1Selection_exampleJ.clarkeJacobian_eq (mem_univ 0), stronglyActive_exampleJ, image_pair,
    fderiv_exampleJSel, fderiv_exampleJSel, convexHull_pair, exampleJSel_zero, exampleJSel_one]

theorem fst_apply_one_of_mem_clarkeJacobian_exampleJ {T : ℝ →L[ℝ] ℝ × ℝ}
    (hT : T ∈ clarkeJacobian exampleJSol 0) : (T 1).1 = 1 / 2 := by
  rw [clarkeJacobian_exampleJ] at hT
  obtain ⟨a, b, -, -, hab, rfl⟩ := hT
  simp only [add_apply, smul_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Prod.fst_add, Prod.smul_fst,
    smul_eq_mul]
  linear_combination hab / 2

theorem fderiv_exampleJSel_zero_mem : fderiv ℝ (exampleJSel {0}) 0 ∈ clarkeJacobian exampleJSol 0 := by
  rw [clarkeJacobian_exampleJ, fderiv_exampleJSel, exampleJSel_zero]
  convert left_mem_segment ℝ _ _ using 3

theorem fderiv_exampleJSel_one_mem : fderiv ℝ (exampleJSel {1}) 0 ∈ clarkeJacobian exampleJSol 0 := by
  rw [clarkeJacobian_exampleJ, fderiv_exampleJSel, exampleJSel_one]
  convert right_mem_segment ℝ _ _ using 3

/-- For `I = {1, 2}`, `∇y^I(0) = (0, 0) ∉ ∂y(0)`. -/
theorem fderiv_exampleJSel_both_not_mem :
    fderiv ℝ (exampleJSel {0, 1}) 0 ∉ clarkeJacobian exampleJSol 0 := fun h ↦ by
  have := fst_apply_one_of_mem_clarkeJacobian_exampleJ h
  rw [fderiv_exampleJSel, exampleJSel_both] at this
  norm_num at this

/-- For `I = ∅`, `∇y^I(0) = (1, 0) ∉ ∂y(0)`. -/
theorem fderiv_exampleJSel_empty_not_mem :
    fderiv ℝ (exampleJSel ∅) 0 ∉ clarkeJacobian exampleJSol 0 := fun h ↦ by
  have := fst_apply_one_of_mem_clarkeJacobian_exampleJ h
  rw [fderiv_exampleJSel, exampleJSel_empty] at this
  norm_num at this

theorem fderiv_exampleJg_section (i : Fin 2) (x : ℝ) (y : ℝ × ℝ) :
    fderiv ℝ (fun z ↦ exampleJg i (x, z)) y =
      ![-ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ,
        ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ] i := by
  fin_cases i
  · have h : (fun z : ℝ × ℝ ↦ exampleJg 0 (x, z)) =
        ⇑(-ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) := by
      funext z
      simp [exampleJg]
    show fderiv ℝ (fun z ↦ exampleJg 0 (x, z)) y = _
    rw [h]
    exact ContinuousLinearMap.fderiv _
  · have h : (fun z : ℝ × ℝ ↦ exampleJg 1 (x, z)) =
        ⇑(ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) := by
      funext z
      simp [exampleJg]
    show fderiv ℝ (fun z ↦ exampleJg 1 (x, z)) y = _
    rw [h]
    exact ContinuousLinearMap.fderiv _

theorem fderiv_exampleJφ_section (x : ℝ) (y : ℝ × ℝ) :
    fderiv ℝ (fun z ↦ exampleJφ (x, z)) y =
      (2 * (y.1 - x)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  have h1 : HasFDerivAt (fun z : ℝ × ℝ ↦ z.1 - x) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    hasFDerivAt_fst.sub_const x
  have h2 : HasFDerivAt (fun z : ℝ × ℝ ↦ z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) y := hasFDerivAt_snd
  refine ((h1.pow 2).add (h2.pow 2)).fderiv.trans (ContinuousLinearMap.ext fun v ↦ ?_)
  simp

theorem differentiable_exampleJφ : Differentiable ℝ exampleJφ := by
  unfold exampleJφ
  fun_prop

/-- The `y`-gradient of the follower's Lagrangian at `λ = 0` is the linear map
`(x, y) ↦ 2(y₁ − x) e₁* + 2 y₂ e₂*`. -/
theorem lowerLagrangianDeriv_exampleJ :
    lowerLagrangianDeriv exampleJφ exampleJg 0 =
      ⇑((2 • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (2 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  funext p
  unfold lowerLagrangianDeriv
  rw [← fderiv_section (differentiable_exampleJφ p), fderiv_exampleJφ_section]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp

theorem lowerHessian_exampleJ (x₀ : ℝ) (y₀ d e : ℝ × ℝ) :
    lowerHessian exampleJφ exampleJg x₀ y₀ 0 d e = 2 * d.1 * e.1 + 2 * d.2 * e.2 := by
  unfold lowerHessian
  rw [lowerLagrangianDeriv_exampleJ, ContinuousLinearMap.fderiv]
  simp

/-- `(0, 0)` with `λ = 0` is a KKT point of the follower's problem at `x̄ = 0`. -/
theorem isLowerKKT_exampleJ : IsLowerKKT exampleJφ exampleJg 0 0 0 := by
  refine ⟨fun i ↦ ?_, fun i ↦ le_rfl, fun i ↦ zero_mul _, ?_⟩
  · fin_cases i <;> simp [exampleJg]
  · rw [fderiv_exampleJφ_section]
    simp

/-- (LICQ) holds at `(x̄, ȳ) = (0, (0, 0))`, where both constraints are active. -/
theorem lowerLICQ_exampleJ : LowerLICQ exampleJg 0 0 := by
  have hv : LinearIndependent ℝ ![-ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ,
      ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ] := by
    refine LinearIndependent.pair_iff.2 fun a b hab ↦ ?_
    have e1 := congrArg (fun l : StrongDual ℝ (ℝ × ℝ) ↦ l (1, 0)) hab
    have e2 := congrArg (fun l : StrongDual ℝ (ℝ × ℝ) ↦ l (0, 1)) hab
    simp at e1 e2
    constructor <;> linarith
  have := hv.comp (fun i : {i // exampleJg i (0, 0) = 0} ↦ i.1) Subtype.val_injective
  unfold LowerLICQ
  convert this using 1
  funext i
  simp [fderiv_exampleJg_section]

/-- `λ = 0` is the unique multiplier, as claimed on p. 90. -/
theorem lowerMultipliers_exampleJ : lowerMultipliers exampleJφ exampleJg 0 0 = {0} :=
  (eq_singleton_iff_unique_mem).2 ⟨isLowerKKT_exampleJ, fun _ hlam ↦
    lowerMultipliers_subsingleton_of_lowerLICQ lowerLICQ_exampleJ hlam isLowerKKT_exampleJ⟩

/-- (SSOC) holds at `(0, (0, 0))`: `∇²_yy L = 2 · id`. -/
theorem lowerSSOC_exampleJ : LowerSSOC exampleJφ exampleJg 0 0 := by
  intro lam hlam d hd _
  rw [lowerMultipliers_exampleJ, mem_singleton_iff] at hlam
  rw [hlam, lowerHessian_exampleJ]
  have : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Prod.ext h.1 h.2)
  rcases this with h | h
  · have := pow_pos (abs_pos.2 h) 2
    nlinarith [sq_abs d.1, sq_nonneg d.2]
  · have := pow_pos (abs_pos.2 h) 2
    nlinarith [sq_abs d.2, sq_nonneg d.1]

/-! ### The example on p. 93 -/

/-- The follower's objective `(y − x)²` of the example on p. 93 of [Dempe 2002]. -/
def exampleSφ (p : ℝ × ℝ) : ℝ := (p.2 - p.1) ^ 2

/-- The follower's constraint `y − x ≤ 0`. -/
def exampleSg : Fin 1 → ℝ × ℝ → ℝ := ![fun p ↦ p.2 - p.1]

theorem exampleSg_apply (i : Fin 1) (p : ℝ × ℝ) : exampleSg i p = p.2 - p.1 := by
  fin_cases i
  rfl

/-- The solution set mapping of the example on p. 93 is `Ψ(x) = {x}`. -/
theorem solutionMap_exampleS (x : ℝ) :
    solutionMap exampleSφ (lowerFeasible exampleSg) x = {x} := by
  have hx : x ∈ lowerFeasible exampleSg x := fun i ↦ by simp [exampleSg_apply]
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · have h := hy.2 x hx
    simp only [exampleSφ, sub_self] at h
    have : (y - x) ^ 2 = 0 := le_antisymm (by simpa using h) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · rw [mem_singleton_iff.1 hy]
    refine ⟨hx, fun z _ ↦ ?_⟩
    show (x - x) ^ 2 ≤ (z - x) ^ 2
    rw [sub_self]
    nlinarith [sq_nonneg (z - x)]

theorem fderiv_exampleSg_section (i : Fin 1) (x y : ℝ) :
    fderiv ℝ (fun z ↦ exampleSg i (x, z)) y = ContinuousLinearMap.id ℝ ℝ := by
  simp only [exampleSg_apply]
  exact ((hasFDerivAt_id y).sub_const x).fderiv

theorem fderiv_exampleSg_apply (i : Fin 1) (p : ℝ × ℝ) (r d : ℝ) :
    fderiv ℝ (exampleSg i) p (r, d) = d - r := by
  have h : exampleSg i = ⇑(ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    funext q
    simp [exampleSg_apply]
  rw [h, ContinuousLinearMap.fderiv]
  simp

theorem fderiv_exampleSφ_section (x y : ℝ) :
    fderiv ℝ (fun z ↦ exampleSφ (x, z)) y = (2 * (y - x)) • ContinuousLinearMap.id ℝ ℝ := by
  refine (((hasFDerivAt_id y).sub_const x).pow 2).fderiv.trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp

/-- The `y`-gradient of the follower's Lagrangian at `λ = 0`: `(x, y) ↦ 2(y − x)`. -/
theorem lowerLagrangianDeriv_exampleS :
    lowerLagrangianDeriv exampleSφ exampleSg 0 =
      ⇑((2 • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight
        (ContinuousLinearMap.id ℝ ℝ)) := by
  funext p
  unfold lowerLagrangianDeriv
  have hd : DifferentiableAt ℝ exampleSφ p := by
    unfold exampleSφ
    fun_prop
  rw [← fderiv_section hd, fderiv_exampleSφ_section]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp

theorem lowerHessian_exampleS (x₀ y₀ d e : ℝ) :
    lowerHessian exampleSφ exampleSg x₀ y₀ 0 d e = 2 * d * e := by
  unfold lowerHessian
  rw [lowerLagrangianDeriv_exampleS, ContinuousLinearMap.fderiv]
  simp

theorem lowerMixedHessian_exampleS (x₀ y₀ r e : ℝ) :
    lowerMixedHessian exampleSφ exampleSg x₀ y₀ 0 r e = -2 * r * e := by
  unfold lowerMixedHessian
  rw [lowerLagrangianDeriv_exampleS, ContinuousLinearMap.fderiv]
  simp

/-- `(x, x)` with `λ = 0` is a KKT point of the follower's problem. -/
theorem isLowerKKT_exampleS (x : ℝ) : IsLowerKKT exampleSφ exampleSg x x 0 := by
  refine ⟨fun i ↦ by simp [exampleSg_apply], fun i ↦ le_rfl, fun i ↦ zero_mul _, ?_⟩
  rw [fderiv_exampleSφ_section]
  simp

/-- (LICQ) holds at every `(x, x)`. -/
theorem lowerLICQ_exampleS (x : ℝ) : LowerLICQ exampleSg x x := by
  have hv : LinearIndependent ℝ fun _ : Fin 1 ↦ (ContinuousLinearMap.id ℝ ℝ : StrongDual ℝ ℝ) :=
    linearIndependent_unique_iff.2 fun h ↦ by
      have := congrArg (fun l : StrongDual ℝ ℝ ↦ l 1) h
      simp at this
  have := hv.comp (fun i : {i // exampleSg i (x, x) = 0} ↦ i.1) Subtype.val_injective
  unfold LowerLICQ
  convert this using 1
  funext i
  simp [fderiv_exampleSg_section]

theorem lowerMultipliers_exampleS (x : ℝ) : lowerMultipliers exampleSφ exampleSg x x = {0} :=
  (eq_singleton_iff_unique_mem).2 ⟨isLowerKKT_exampleS x, fun _ hlam ↦
    lowerMultipliers_subsingleton_of_lowerLICQ (lowerLICQ_exampleS x) hlam
      (isLowerKKT_exampleS x)⟩

/-- (SSOC) holds at every `(x, x)`. -/
theorem lowerSSOC_exampleS (x : ℝ) : LowerSSOC exampleSφ exampleSg x x := by
  intro lam hlam d hd _
  rw [lowerMultipliers_exampleS, mem_singleton_iff] at hlam
  rw [hlam, lowerHessian_exampleS]
  have := pow_pos (abs_pos.2 hd) 2
  nlinarith [sq_abs d]

/-- `y'(x; r) = r`, and the constraint is active in `QP(0, r)` at `y'(x; r)`. -/
theorem hasDirDerivAt_exampleS (x : ℝ) :
    HasDirDerivAt (fun x : ℝ ↦ x) (fun r ↦ r) x ∧
      ∀ r, fderiv ℝ (exampleSg 0) (x, x) (r, r) = 0 := by
  refine ⟨fun r ↦ ?_, fun r ↦ by rw [fderiv_exampleSg_apply, sub_self]⟩
  refine tendsto_nhdsWithin_congr (fun t ht ↦ ?_) tendsto_const_nhds
  have ht : t ≠ 0 := (mem_Ioi.1 ht).ne'
  simp [smul_eq_mul, ht]

/-- **The example on p. 93 of [Dempe 2002]**: the strict complementarity condition (SCR) of
Thm. 4.12 fails for every index set `I` and every direction `r`. -/
theorem not_lowerSCR_exampleS (x : ℝ) (I : Finset (Fin 1)) (r : ℝ) :
    ¬ LowerSCR exampleSφ exampleSg x x 0 I r := by
  rintro ⟨d, γ, ⟨h1, h2, -, -, h5⟩, hγ, hg⟩
  have e := congrArg (fun l : StrongDual ℝ ℝ ↦ l 1) h1
  simp only [add_apply, Fin.sum_univ_one, smul_apply, fderiv_exampleSg_section,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, zero_apply] at e
  rw [lowerMixedHessian_exampleS, lowerHessian_exampleS] at e
  by_cases h0 : (0 : Fin 1) ∈ I
  · have hd := h2 0 h0
    rw [fderiv_exampleSg_apply] at hd
    have := hγ 0 h0 (lt_irrefl 0)
    linarith
  · have hd := hg 0 h0 (by simp [exampleSg_apply])
    rw [fderiv_exampleSg_apply] at hd
    rw [h5 0 h0] at e
    linarith

/-- On the other hand, `R({1}, 0)` is the whole line, so Thm. 4.13 applies to every direction. -/
theorem lowerQPRegion_exampleS (x : ℝ) :
    LowerAdmissible exampleSg x x 0 {0} ∧ lowerQPRegion exampleSφ exampleSg x x 0 {0} = univ := by
  refine ⟨⟨fun i h ↦ absurd h (lt_irrefl 0), fun i _ ↦ by simp [exampleSg_apply]⟩,
    eq_univ_of_forall fun r ↦ ⟨r, 0, ?_, fun i _ ↦ ?_, fun i hi ↦ ?_, fun i _ _ ↦ le_rfl,
      fun i hi ↦ ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [add_apply, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, zero_apply]
    rw [lowerMixedHessian_exampleS, lowerHessian_exampleS]
    ring
  · rw [fderiv_exampleSg_apply, sub_self]
  · fin_cases i
    simp at hi
  · fin_cases i
    simp at hi

end Bilevel
