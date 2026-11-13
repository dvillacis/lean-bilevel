/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import BilevelOptimization.KKT
import VariationalAnalysis.Analysis.Farkas

/-!
# Single-level reformulations of linear bilevel problems

The LP–LP bilevel problem of [Schmidt 2024, pp. 118–144]
`min_{x, y} cₓ x + c_y y` s.t. `A x + B y ≥ a`, `y ∈ Argmin_y' {d y' | C x + D y' ≥ b}`,
with the rows of `A, B, C, D` and the vectors `cₓ, c_y, d` given as continuous linear functionals,
and its three single-level reformulations:

* the **KKT reformulation**: replace the follower's problem by primal feasibility
  `C x + D y ≥ b`, dual feasibility `Dᵀ λ = d`, `λ ≥ 0`, and complementarity
  `λᵢ (Cᵢ x + Dᵢ y - bᵢ) = 0`;
* the **strong-duality reformulation**: replace complementarity by `d y ≤ (b - C x)ᵀ λ`;
* the **big-M reformulation**: replace complementarity by `λᵢ ≤ M zᵢ`,
  `Cᵢ x + Dᵢ y - bᵢ ≤ M (1 - zᵢ)`, `zᵢ ∈ {0, 1}`.

## Main results

* `mem_lowerSolution_iff`: strong duality for the follower's LP: `y` solves the follower's
  problem iff it is feasible and has a dual feasible `λ` satisfying complementarity. No
  constraint qualification is needed (Farkas' lemma,
  `VariationalAnalysis.exists_nonneg_eq_sum_of_forall_nonneg`).
* `mem_lowerSolution_iff_exists_isLowerKKT`: the same in terms of the general KKT conditions
  `IsLowerKKT` of `BilevelOptimization.KKT`.
* `sum_mul_le_of_isDualFeasible`, `complementarity_iff_le`, `complementarity_iff_eq`: weak duality,
  and complementarity is equivalent to the strong-duality inequality and to equality of the
  primal and dual objectives [Schmidt 2024, pp. 141–144].
* `image_fst_kktFeasible`, `kktFeasible_eq_sdFeasible`: the KKT and the strong-duality
  reformulations project onto the bilevel feasible set.
* `isMinOn_kktFeasible_iff`, `isMinOn_sdFeasible_iff`: global solutions of the reformulations
  are exactly the global (optimistic) bilevel solutions, for every multiplier
  [Schmidt 2024, pp. 124, 143].
* `mem_kktFeasible_of_mem_bigMFeasible`, `exists_mem_bigMFeasible`,
  `isMinOn_bigMFeasible_of_isMinOn_kktFeasible`: the big-M reformulation is a restriction of the
  KKT reformulation for every `M`, and it is equivalent to it as soon as `M` bounds the
  multipliers and slacks of one global solution [Schmidt 2024, p. 133].

## Remarks on the sources

* Unlike the convex case (`isMinOn_bilevelFeasible_of_isMinOn_kktFeasible`), no Slater
  condition is needed: for linear constraints the KKT conditions are necessary without any
  constraint qualification.
* "`M` sufficiently large" on [Schmidt 2024, p. 133] is made precise as: `M` bounds the
  multipliers `λ` and the slacks `Cᵢ x + Dᵢ y - bᵢ` of some global solution of the KKT
  reformulation. Verifying such a bound is hard in general [Kleinert et al. 2020; Schmidt 2024,
  p. 134].
-/

open Filter Topology Set

namespace Bilevel

/-- The data of an LP–LP bilevel problem
`min cₓ x + c_y y` s.t. `A x + B y ≥ a`, `y ∈ Argmin_y' {d y' | C x + D y' ≥ b}`
[Schmidt 2024, p. 118]; the rows `Aₖ, Bₖ, Cᵢ, Dᵢ` are continuous linear functionals. -/
structure LinearBilevel (E F κ ι : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The leader's objective, `x`-part. -/
  cx : StrongDual ℝ E
  /-- The leader's objective, `y`-part. -/
  cy : StrongDual ℝ F
  /-- The leader's constraints `A x + B y ≥ a`. -/
  A : κ → StrongDual ℝ E
  /-- The leader's constraints `A x + B y ≥ a`. -/
  B : κ → StrongDual ℝ F
  /-- The leader's constraints `A x + B y ≥ a`. -/
  a : κ → ℝ
  /-- The follower's constraints `C x + D y ≥ b`. -/
  C : ι → StrongDual ℝ E
  /-- The follower's constraints `C x + D y ≥ b`. -/
  D : ι → StrongDual ℝ F
  /-- The follower's constraints `C x + D y ≥ b`. -/
  b : ι → ℝ
  /-- The follower's objective. -/
  d : StrongDual ℝ F

namespace LinearBilevel

variable {E F κ ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (P : LinearBilevel E F κ ι)

/-- The leader's objective `cₓ x + c_y y`. -/
def objective (p : E × F) : ℝ := P.cx p.1 + P.cy p.2

/-- The follower's objective `d y`. -/
def lowerObjective (p : E × F) : ℝ := P.d p.2

/-- The follower's constraints in the form `gᵢ(x, y) = bᵢ - Cᵢ x - Dᵢ y ≤ 0`. -/
def lowerConstraints (i : ι) (p : E × F) : ℝ := P.b i - P.C i p.1 - P.D i p.2

/-- The slack `Cᵢ x + Dᵢ y - bᵢ` of the `i`-th follower constraint. -/
def slack (i : ι) (p : E × F) : ℝ := P.C i p.1 + P.D i p.2 - P.b i

/-- The leader's feasible set `{(x, y) | A x + B y ≥ a}`. -/
def upperFeasible : Set (E × F) := {p | ∀ k, P.a k ≤ P.A k p.1 + P.B k p.2}

/-- The follower's feasible set `{y | C x + D y ≥ b}`. -/
def lowerFeasible (x : E) : Set F := VariationalAnalysis.lowerFeasible P.lowerConstraints x

/-- The follower's solution set `Argmin_y {d y | C x + D y ≥ b}`. -/
def lowerSolution (x : E) : Set F := solutionMap P.lowerObjective P.lowerFeasible x

/-- The bilevel feasible set. -/
def feasible : Set (E × F) := {p | p ∈ P.upperFeasible ∧ p.2 ∈ P.lowerSolution p.1}

variable [Fintype ι]

/-- Dual feasibility for the follower's LP: `Dᵀ λ = d`, `λ ≥ 0`. -/
def IsDualFeasible (lam : ι → ℝ) : Prop := (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • P.D i = P.d

/-- The feasible set of the KKT reformulation [Schmidt 2024, p. 123]. -/
def kktFeasible : Set ((E × F) × (ι → ℝ)) :=
  {q | q.1 ∈ P.upperFeasible ∧ q.1.2 ∈ P.lowerFeasible q.1.1 ∧ P.IsDualFeasible q.2 ∧
    ∀ i, q.2 i * P.slack i q.1 = 0}

/-- The feasible set of the strong-duality reformulation [Schmidt 2024, p. 143]. -/
def sdFeasible : Set ((E × F) × (ι → ℝ)) :=
  {q | q.1 ∈ P.upperFeasible ∧ q.1.2 ∈ P.lowerFeasible q.1.1 ∧ P.IsDualFeasible q.2 ∧
    P.d q.1.2 ≤ ∑ i, q.2 i * (P.b i - P.C i q.1.1)}

/-- The feasible set of the big-M reformulation [Schmidt 2024, p. 133], with binary variables
`z`. -/
def bigMFeasible (M : ℝ) : Set (((E × F) × (ι → ℝ)) × (ι → ℝ)) :=
  {r | r.1.1 ∈ P.upperFeasible ∧ r.1.1.2 ∈ P.lowerFeasible r.1.1.1 ∧ P.IsDualFeasible r.1.2 ∧
    (∀ i, r.2 i = 0 ∨ r.2 i = 1) ∧ (∀ i, r.1.2 i ≤ M * r.2 i) ∧
    ∀ i, P.slack i r.1.1 ≤ M * (1 - r.2 i)}

variable {P} {x : E} {y : F} {lam : ι → ℝ}

omit [Fintype ι] in
theorem mem_lowerFeasible_iff : y ∈ P.lowerFeasible x ↔ ∀ i, 0 ≤ P.slack i (x, y) :=
  forall_congr' fun i ↦ by
    show P.b i - P.C i x - P.D i y ≤ 0 ↔ 0 ≤ P.C i x + P.D i y - P.b i
    constructor <;> intro h <;> linarith

theorem apply_eq_sum_of_isDualFeasible (hlam : P.IsDualFeasible lam) (y : F) :
    P.d y = ∑ i, lam i * P.D i y := by
  rw [← hlam.2]
  simp only [sum_apply, smul_apply, smul_eq_mul]

/-- The duality gap is the complementarity sum: `d y - (b - C x)ᵀ λ = ∑ λᵢ (Cᵢ x + Dᵢ y - bᵢ)`
for dual feasible `λ`. -/
theorem sub_sum_eq_sum_mul_slack (hlam : P.IsDualFeasible lam) :
    P.d y - ∑ i, lam i * (P.b i - P.C i x) = ∑ i, lam i * P.slack i (x, y) := by
  rw [apply_eq_sum_of_isDualFeasible hlam, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [slack]; ring

/-- Weak duality for the follower's LP [Schmidt 2024, p. 141]. -/
theorem sum_mul_le_of_isDualFeasible (hy : y ∈ P.lowerFeasible x)
    (hlam : P.IsDualFeasible lam) : ∑ i, lam i * (P.b i - P.C i x) ≤ P.d y := by
  have h := sub_sum_eq_sum_mul_slack (x := x) (y := y) hlam
  have h0 : 0 ≤ ∑ i, lam i * P.slack i (x, y) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hlam.1 i) (mem_lowerFeasible_iff.1 hy i)
  linarith

/-- For primal and dual feasible `y`, `λ`, complementarity is equivalent to the strong-duality
inequality `d y ≤ (b - C x)ᵀ λ` [Schmidt 2024, p. 144]. -/
theorem complementarity_iff_le (hy : y ∈ P.lowerFeasible x) (hlam : P.IsDualFeasible lam) :
    (∀ i, lam i * P.slack i (x, y) = 0) ↔ P.d y ≤ ∑ i, lam i * (P.b i - P.C i x) := by
  have h := sub_sum_eq_sum_mul_slack (x := x) (y := y) hlam
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ lam i * P.slack i (x, y) := fun i _ ↦
    mul_nonneg (hlam.1 i) (mem_lowerFeasible_iff.1 hy i)
  constructor
  · intro hc
    rw [Finset.sum_eq_zero fun i _ ↦ hc i] at h
    linarith
  · intro hle i
    have hs : ∑ i, lam i * P.slack i (x, y) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs i (Finset.mem_univ i)

/-- For primal and dual feasible `y`, `λ`, complementarity is equivalent to equality of the
primal and dual objective values [Schmidt 2024, p. 144]. -/
theorem complementarity_iff_eq (hy : y ∈ P.lowerFeasible x) (hlam : P.IsDualFeasible lam) :
    (∀ i, lam i * P.slack i (x, y) = 0) ↔ P.d y = ∑ i, lam i * (P.b i - P.C i x) := by
  rw [complementarity_iff_le hy hlam]
  exact ⟨fun h ↦ le_antisymm h (sum_mul_le_of_isDualFeasible hy hlam), fun h ↦ h.le⟩

/-- Strong duality for the follower's LP, in KKT form: `y` solves the follower's problem iff it
is feasible and some dual feasible `λ` satisfies complementarity. No constraint qualification is
needed. -/
theorem mem_lowerSolution_iff [FiniteDimensional ℝ F] :
    y ∈ P.lowerSolution x ↔ y ∈ P.lowerFeasible x ∧
      ∃ lam, P.IsDualFeasible lam ∧ ∀ i, lam i * P.slack i (x, y) = 0 := by
  classical
  constructor
  · rintro ⟨hy, hmin⟩
    have hy' := mem_lowerFeasible_iff.1 hy
    refine ⟨hy, ?_⟩
    -- every direction `h` with `Dᵢ h ≥ 0` on the active constraints has `d h ≥ 0`
    have hdir : ∀ h : F, (∀ i : {i // P.slack i (x, y) = 0}, 0 ≤ P.D i.1 h) → 0 ≤ P.d h := by
      intro h hh
      have hslack : ∀ (i : ι) (t : ℝ), P.slack i (x, y + t • h) = P.slack i (x, y) + t * P.D i h :=
        fun i t ↦ by simp only [slack, map_add, map_smul, smul_eq_mul]; ring
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, 0 ≤ P.slack i (x, y + t • h) :=
        eventually_all.2 fun i ↦ by
          by_cases hi : P.slack i (x, y) = 0
          · exact eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ by
              rw [hslack, hi, zero_add]
              exact mul_nonneg ht.le (hh ⟨i, hi⟩)
          · have hpos : 0 < P.slack i (x, y) := lt_of_le_of_ne (hy' i) (Ne.symm hi)
            have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < P.slack i (x, y) + t * P.D i h :=
              continuousAt_const.eventually_lt
                (show Continuous fun t : ℝ ↦ P.slack i (x, y) + t * P.D i h by
                  fun_prop).continuousAt (by simpa using hpos)
            exact (h1.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦ by
              rw [hslack]
              exact ht.le
      obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
      have hle : P.d y ≤ P.d (y + t • h) := hmin _ (mem_lowerFeasible_iff.2 ht)
      rw [map_add, map_smul, smul_eq_mul] at hle
      have ht0' : (0 : ℝ) < t := ht0
      nlinarith
    -- Farkas' lemma on the active constraints
    obtain ⟨μ, hμ, hμd⟩ := VariationalAnalysis.exists_nonneg_eq_sum_of_forall_nonneg
      (fun i : {i // P.slack i (x, y) = 0} ↦ P.D i.1) P.d hdir
    obtain ⟨lam, hlp, hln⟩ : ∃ lam : ι → ℝ, (∀ i (hi : P.slack i (x, y) = 0), lam i = μ ⟨i, hi⟩) ∧
        ∀ i, ¬ P.slack i (x, y) = 0 → lam i = 0 :=
      ⟨fun i ↦ if hi : P.slack i (x, y) = 0 then μ ⟨i, hi⟩ else 0, fun _ hi ↦ dif_pos hi,
        fun _ hi ↦ dif_neg hi⟩
    refine ⟨lam, ⟨fun i ↦ ?_, ?_⟩, fun i ↦ ?_⟩
    · by_cases hi : P.slack i (x, y) = 0
      · rw [hlp i hi]
        exact hμ _
      · rw [hln i hi]
    · rw [hμd, ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ P.slack i (x, y) = 0)]
      have h0 : ∑ i : {i // ¬ P.slack i (x, y) = 0}, lam i.1 • P.D i.1 = 0 :=
        Finset.sum_eq_zero fun i _ ↦ by rw [hln i.1 i.2, zero_smul]
      rw [h0, add_zero]
      exact Fintype.sum_equiv (Equiv.refl _) _ _ fun i ↦ by rw [Equiv.refl_apply, hlp i.1 i.2]
    · by_cases hi : P.slack i (x, y) = 0
      · rw [hi, mul_zero]
      · rw [hln i hi, zero_mul]
  · rintro ⟨hy, lam, hlam, hc⟩
    refine ⟨hy, fun z hz ↦ ?_⟩
    show P.d y ≤ P.d z
    rw [(complementarity_iff_eq hy hlam).1 hc]
    exact sum_mul_le_of_isDualFeasible hz hlam

/-- The KKT conditions `IsLowerKKT` of the general reformulation (5.26), for the linear
follower's problem, are primal feasibility, dual feasibility and complementarity. -/
theorem isLowerKKT_iff :
    IsLowerKKT P.lowerObjective P.lowerConstraints x y lam ↔
      y ∈ P.lowerFeasible x ∧ P.IsDualFeasible lam ∧ ∀ i, lam i * P.slack i (x, y) = 0 := by
  have hφ : fderiv ℝ (fun z ↦ P.lowerObjective (x, z)) y = P.d := P.d.fderiv
  have hg : ∀ i, fderiv ℝ (fun z ↦ P.lowerConstraints i (x, z)) y = -P.D i := fun i ↦ by
    exact (((hasFDerivAt_const (P.b i - P.C i x) y).sub (P.D i).hasFDerivAt).fderiv).trans
      (zero_sub _)
  have hgs : ∀ i, P.lowerConstraints i (x, y) = -P.slack i (x, y) := fun i ↦ by
    simp only [lowerConstraints, slack]
    ring
  simp only [IsLowerKKT, hφ, hg, smul_neg, Finset.sum_neg_distrib, add_neg_eq_zero, hgs, mul_neg,
    neg_eq_zero, neg_nonpos, mem_lowerFeasible_iff, IsDualFeasible]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, ⟨h2, h4.symm⟩, h3⟩
  · rintro ⟨h1, ⟨h2, h4⟩, h3⟩
    exact ⟨h1, h2, h3, h4.symm⟩

/-- For a linear follower's problem, the KKT conditions characterize the solution set without
any constraint qualification (compare `mem_solutionMap_iff_exists_isLowerKKT`, which needs
Slater's condition). -/
theorem mem_lowerSolution_iff_exists_isLowerKKT [FiniteDimensional ℝ F] :
    y ∈ P.lowerSolution x ↔ ∃ lam, IsLowerKKT P.lowerObjective P.lowerConstraints x y lam := by
  simp only [isLowerKKT_iff, mem_lowerSolution_iff]
  exact ⟨fun ⟨hy, lam, h1, h2⟩ ↦ ⟨lam, hy, h1, h2⟩, fun ⟨lam, hy, h1, h2⟩ ↦ ⟨hy, lam, h1, h2⟩⟩

/-! ### The KKT and strong-duality reformulations -/

variable (P)

/-- The KKT reformulation projects onto the bilevel feasible set. -/
theorem image_fst_kktFeasible [FiniteDimensional ℝ F] :
    Prod.fst '' P.kktFeasible = P.feasible := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, mem_lowerSolution_iff.2 ⟨hq.2.1, q.2, hq.2.2.1, hq.2.2.2⟩⟩
  · rintro ⟨hp, hsol⟩
    obtain ⟨hy, lam, hlam, hc⟩ := mem_lowerSolution_iff.1 hsol
    exact ⟨(p, lam), ⟨hp, hy, hlam, hc⟩, rfl⟩

/-- The KKT and the strong-duality reformulations have the same feasible set
[Schmidt 2024, p. 144]. -/
theorem kktFeasible_eq_sdFeasible : P.kktFeasible = P.sdFeasible := by
  ext q
  exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3, (complementarity_iff_le h2 h3).1 h4⟩,
    fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3, (complementarity_iff_le h2 h3).2 h4⟩⟩

/-- The strong-duality reformulation projects onto the bilevel feasible set. -/
theorem image_fst_sdFeasible [FiniteDimensional ℝ F] :
    Prod.fst '' P.sdFeasible = P.feasible := by
  rw [← kktFeasible_eq_sdFeasible, image_fst_kktFeasible]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] in
/-- Minimizing `f ∘ Prod.fst` over a set `K` is minimizing `f` over its projection. -/
theorem isMinOn_comp_fst_iff {α β γ : Type*} [Preorder γ] {f : α → γ} {K : Set (α × β)}
    {S : Set α} (hKS : Prod.fst '' K = S) {q : α × β} :
    IsMinOn (fun q ↦ f q.1) K q ↔ IsMinOn f S q.1 := by
  rw [← hKS]
  constructor
  · intro h
    refine isMinOn_iff.2 ?_
    rintro _ ⟨q', hq', rfl⟩
    exact isMinOn_iff.1 h q' hq'
  · intro h
    exact isMinOn_iff.2 fun q' hq' ↦ isMinOn_iff.1 h _ ⟨q', hq', rfl⟩

/-- Global solutions of the KKT reformulation are exactly the global (optimistic) bilevel
solutions, with any multiplier [Schmidt 2024, p. 124]. -/
theorem isMinOn_kktFeasible_iff [FiniteDimensional ℝ F] {q : (E × F) × (ι → ℝ)} :
    IsMinOn (fun q ↦ P.objective q.1) P.kktFeasible q ↔ IsMinOn P.objective P.feasible q.1 :=
  isMinOn_comp_fst_iff P.image_fst_kktFeasible

/-- Global solutions of the strong-duality reformulation are exactly the global (optimistic)
bilevel solutions, with any multiplier [Schmidt 2024, p. 143]. -/
theorem isMinOn_sdFeasible_iff [FiniteDimensional ℝ F] {q : (E × F) × (ι → ℝ)} :
    IsMinOn (fun q ↦ P.objective q.1) P.sdFeasible q ↔ IsMinOn P.objective P.feasible q.1 :=
  isMinOn_comp_fst_iff P.image_fst_sdFeasible

/-- Every global bilevel solution comes with multipliers making it a global solution of the KKT
reformulation. -/
theorem exists_isMinOn_kktFeasible [FiniteDimensional ℝ F] {p : E × F} (hp : p ∈ P.feasible)
    (hmin : IsMinOn P.objective P.feasible p) :
    ∃ lam, (p, lam) ∈ P.kktFeasible ∧
      IsMinOn (fun q ↦ P.objective q.1) P.kktFeasible (p, lam) := by
  obtain ⟨q, hq, rfl⟩ := (P.image_fst_kktFeasible).symm ▸ hp
  exact ⟨q.2, hq, P.isMinOn_kktFeasible_iff.2 hmin⟩

/-! ### The big-M reformulation -/

variable {P} {M : ℝ}

/-- For every `M`, the big-M reformulation is a restriction of the KKT reformulation: the binary
variables select which side of each complementarity condition vanishes. -/
theorem mem_kktFeasible_of_mem_bigMFeasible {r : ((E × F) × (ι → ℝ)) × (ι → ℝ)}
    (hr : r ∈ P.bigMFeasible M) : r.1 ∈ P.kktFeasible := by
  obtain ⟨h1, h2, h3, hz, hlam, hs⟩ := hr
  refine ⟨h1, h2, h3, fun i ↦ ?_⟩
  rcases hz i with h | h
  · have : r.1.2 i = 0 := le_antisymm (by simpa [h] using hlam i) (h3.1 i)
    rw [this, zero_mul]
  · have : P.slack i r.1.1 = 0 :=
      le_antisymm (by simpa [h] using hs i) (mem_lowerFeasible_iff.1 h2 i)
    rw [this, mul_zero]

/-- A KKT-feasible point whose multipliers and slacks are bounded by `M` is feasible for the
big-M reformulation. -/
theorem exists_mem_bigMFeasible {q : (E × F) × (ι → ℝ)} (hq : q ∈ P.kktFeasible)
    (hlam : ∀ i, q.2 i ≤ M) (hs : ∀ i, P.slack i q.1 ≤ M) : ∃ z, (q, z) ∈ P.bigMFeasible M := by
  classical
  obtain ⟨h1, h2, h3, hc⟩ := hq
  refine ⟨fun i ↦ if P.slack i q.1 = 0 then 1 else 0, h1, h2, h3, fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ ?_⟩
  · by_cases h : P.slack i q.1 = 0
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  · by_cases h : P.slack i q.1 = 0
    · simpa [h] using hlam i
    · simp only [h, if_false, mul_zero]
      exact ((mul_eq_zero.1 (hc i)).resolve_right h).le
  · by_cases h : P.slack i q.1 = 0
    · simp [h]
    · simpa [h] using hs i

/-- The big-M reformulation [Schmidt 2024, p. 133]: if `M` bounds the multipliers and slacks of
a global solution `q` of the KKT reformulation, then `q` (with suitable binary variables) is a
global solution of the big-M reformulation, and every global solution of the big-M
reformulation gives a global solution of the KKT reformulation. -/
theorem isMinOn_bigMFeasible_of_isMinOn_kktFeasible {q : (E × F) × (ι → ℝ)}
    (hq : q ∈ P.kktFeasible) (hmin : IsMinOn (fun q ↦ P.objective q.1) P.kktFeasible q)
    (hlam : ∀ i, q.2 i ≤ M) (hs : ∀ i, P.slack i q.1 ≤ M) :
    ∃ z, (q, z) ∈ P.bigMFeasible M ∧
      IsMinOn (fun r ↦ P.objective r.1.1) (P.bigMFeasible M) (q, z) ∧
      ∀ r ∈ P.bigMFeasible M, IsMinOn (fun r ↦ P.objective r.1.1) (P.bigMFeasible M) r →
        IsMinOn (fun q ↦ P.objective q.1) P.kktFeasible r.1 := by
  obtain ⟨z, hz⟩ := exists_mem_bigMFeasible hq hlam hs
  refine ⟨z, hz, isMinOn_iff.2 fun r hr ↦
    isMinOn_iff.1 hmin _ (mem_kktFeasible_of_mem_bigMFeasible hr), fun r _ hr ↦ ?_⟩
  exact isMinOn_iff.2 fun q' hq' ↦ (isMinOn_iff.1 hr _ hz).trans (isMinOn_iff.1 hmin q' hq')

/-- Global solutions of the big-M reformulation are global (optimistic) bilevel solutions, as
soon as `M` bounds the multipliers and slacks of one global solution of the KKT reformulation. -/
theorem isMinOn_feasible_of_isMinOn_bigMFeasible [FiniteDimensional ℝ F]
    {q : (E × F) × (ι → ℝ)} (hq : q ∈ P.kktFeasible)
    (hmin : IsMinOn (fun q ↦ P.objective q.1) P.kktFeasible q)
    (hlam : ∀ i, q.2 i ≤ M) (hs : ∀ i, P.slack i q.1 ≤ M) {r : ((E × F) × (ι → ℝ)) × (ι → ℝ)}
    (hr : r ∈ P.bigMFeasible M)
    (hrmin : IsMinOn (fun r ↦ P.objective r.1.1) (P.bigMFeasible M) r) :
    r.1.1 ∈ P.feasible ∧ IsMinOn P.objective P.feasible r.1.1 := by
  obtain ⟨_, _, _, h⟩ := isMinOn_bigMFeasible_of_isMinOn_kktFeasible hq hmin hlam hs
  have hr' := mem_kktFeasible_of_mem_bigMFeasible hr
  refine ⟨P.image_fst_kktFeasible ▸ mem_image_of_mem Prod.fst hr', ?_⟩
  exact P.isMinOn_kktFeasible_iff.1 (h r hr hrmin)

end LinearBilevel

end Bilevel
