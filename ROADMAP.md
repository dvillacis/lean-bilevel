# Roadmap

Status: ✓ formalized, ◐ partially, ☐ not yet. D = [Dempe 2002], S = [Schmidt 2024] (physical
slide pages), DD = [Dempe–Dutta 2012].

## D Ch. 5.1 / S "Solution concepts": optimality concepts

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D (5.1)–(5.4), (5.7) | solution map, optimistic and pessimistic value functions | ✓ | `solutionMap`, `optimisticValue`, `pessimisticValue` | values in `EReal` |
| D Def 5.1 | local/global solutions under unique lower-level solutions | ✓ | `isLocalOptimisticSolution_iff`, `isOptimisticSolution_iff` | equivalent to Def 5.2 with or without uniqueness |
| D Def 5.2 | local and global optimistic solutions | ✓ | `IsLocalOptimisticSolution`, `IsOptimisticSolution` | |
| D Def 5.3 | local and global pessimistic solutions | ✓ | `IsLocalPessimisticSolution`, `IsPessimisticSolution` | |
| D (5.5), S p. 77, 87 | joint (optimistic) problem | ✓ | `bilevelFeasible` | |
| D (5.8) | lower optimal solutions | ✓ | `lowerOptimalSet` | |
| D p. 132 | global optimistic solutions = global solutions of (5.5) | ✓ | `isOptimisticSolution_iff` | no assumptions |
| D p. 163 | local optimistic ⇒ local for (5.5) / (5.36) | ✓ | `IsLocalOptimisticSolution.isLocalMinOn` | |
| D Ex. p. 157 | local for (5.5) ⇏ local optimistic | ✓ | `not_isLocalOptimisticSolution_example` | |
| D Thm 5.1, 5.2 | existence of optimistic solutions | ✓ | `exists_isOptimisticSolution_of_isCompact`, `exists_isOptimisticSolution`, `exists_isOptimisticSolution_of_regular` | (C) replaced by compactness of `{(x, y) \| x ∈ Ω, y ∈ K(x)}`; (MFCQ) enters through lower semicontinuity of `K` |
| D Thm 5.3 | existence of pessimistic solutions (`Ψ` l.s.c.) | ✓ | `exists_isPessimisticSolution`, `lowerSemicontinuousAt_pessimisticValue` | `φ_p` minimized over `solvableSet` (where `Ψ ≠ ∅`); over all of `Ω` the empty-`Ψ` points give `φ_p = -∞` |
| D Ex. pp. 129, 134; S pp. 74–84 | optimistic solution exists, pessimistic does not | ✓ | `isOptimisticSolution_example`, `not_isPessimisticSolution_example` | the book's formulas for `φ_o`, `φ_p` have the parameter's sign swapped |
| D Ex. pp. 135–136 | position of coupling constraints matters; inactive constraints matter | ✓ | `isMinOn_coupling_upper_example`, `isMinOn_coupling_lower_example`, `coupling_infeasible_example`; `isMinOn_inactive_example`, `isMinOn_inactive_constrained_example` | coupling constraints as an intersection with `bilevelFeasible`; in the second example the book swaps the components of the solution (follower `≈ 0.82`, leader `≈ 10.02`; exactly `2050/2501`, `25051/2501`) |
| S p. 85 | optimistic = pessimistic for unique lower-level solutions | ✓ | `isOptimisticSolution_iff_isPessimisticSolution`, `isLocalOptimisticSolution_iff_isLocalPessimisticSolution`, `optimisticValue_eq_pessimisticValue` | `Ψ(x)` has at most one point for `x ∈ Ω`; it may be empty |
| S p. 42 | high-point relaxation | ✓ | `highPointFeasible`, `bilevelFeasible_subset_highPointFeasible`, `iInf_highPointFeasible_le`, `isOptimisticSolution_of_isMinOn_highPointFeasible` | |

## D Ch. 3: linear bilevel problems

In `LinearGeometry.lean`, for the LP–LP model `LinearBilevel` (follower `min_y {d y | C x + D y ≥ b}`).

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D Ex. p. 30 | example of Fig. 3.1 | ✓ | `isMinOn_linear_example` | |
| D Def 3.1 | polyhedral point-to-set maps | ✓ | `IsConvexPolyhedral`, `IsPolyhedralMap` | |
| D Thm 3.1 | `Ψ_L` is polyhedral | ✓ | `LinearBilevel.graph_lowerSolution_eq`, `LinearBilevel.isPolyhedralMap_lowerSolution`, `LinearBilevel.feasible_eq`, `LinearBilevel.isClosed_feasible` | union of faces whose active set supports a dual feasible multiplier |
| D Cor 3.1 | a solution at a vertex | ✓ | `LinearBilevel.exists_isMinOn_feasible_mem_extremePoints` | uniqueness of the follower's solution not needed (optimistic case); constraint set assumed bounded; upper-level constraints may depend on `y` |
| D Thm 3.2 | existence under uniqueness, problem (3.4) | ✓ | `ParamLinearBilevel`, `ParamLinearBilevel.graph_lowerSolution_eq`, `ParamLinearBilevel.isClosed_feasible`, `ParamLinearBilevel.exists_isMinOn_feasible` | whole constraint set bounded instead of only `M̄` compact; uniqueness not needed (closed cones `isClosed_supportedCone` instead of continuity of the solution function) |
| D Thm 3.3 | existence of optimistic solutions | ✓ | `LinearBilevel.exists_isMinOn_feasible` | |
| D Ex. pp. 38–39 | pessimistic problem without solution | ✓ | `not_exists_isPessimisticSolution_linear_example` | |
| D Ex. p. 33 | disconnected feasible set | ✓ | `not_isPreconnected_linear_example` | points with `x = 1, 4` feasible, none with `x = 2` |
| D Thm 3.4–3.5 | relations to multicriteria optimization | ☐ | | |
| D Sect. 3.4.2 | 0-1 (big-M) reformulation | ✓ | see S p. 133 below | |
| D Thm 3.6–3.7 | F. John / KKT conditions | ☐ | | compare the general D Thm 5.16–5.17 |
| D Thm 3.8–3.10 | regions of stability, basic matrices | ☐ | | |
| D Thm 3.11 | global optimality via the duality gap | ✓ | `LinearBilevel.isMinOn_feasible_iff_forall_gap_pos` | pointwise form; avoids attainment in the quadratic problem (3.23) |

## D Ch. 4: parametric optimization

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D Def 4.2 | upper/lower semicontinuity of set-valued maps | ✓ | `UpperHemicontinuousAt`, `LowerHemicontinuousAt` | Hausdorff–Berge (hemicontinuity) sense |
| D Sect. 4.1 | `Ψ_loc`, `SP` | ✓ | `localSolutionMap`, `stationaryMap` | |
| D (4.7) | `Ψ ⊆ Ψ_loc ⊆ SP` under (MFCQ); `SP = Ψ` for convex problems | ✓ | `solutionMap_subset_localSolutionMap`, `localSolutionMap_subset_stationaryMap`, `stationaryMap_subset_solutionMap` | |
| D Thm 4.1 | (MFCQ) ⟺ `Λ(x, y)` nonempty, convex, compact | ✓ | `lowerPLI_iff_nonempty_isCompact`, `isCompact_lowerMultipliers`, `lowerPLI_of_isBounded`, `convex_lowerMultipliers` | dual (MFCQ) = positive linear independence; primal form via Gordan not formalized |
| D Thm 4.3 | value function continuous, `Ψ` u.s.c. | ✓ | `continuousAt_marginal`, `upperHemicontinuousAt_solutionMap`, `continuousAt_lowerValue_of_regular`, `upperHemicontinuousAt_lowerSolution_of_regular` | abstract version: closed `gph K`, `K` locally uniformly bounded and l.s.c. at `x̄` |
| — | (MFCQ) ⇒ `G(x) = {y \| g(x, y) ≤ 0}` Lipschitz-like, hence l.s.c. | ✓ | `lipschitzLikeAt_lowerFeasible`, `lowerHemicontinuousAt_lowerFeasible` | via the Mordukhovich criterion (lean-variational); `lowerPLI_iff_lowerLevelRegular` bridges the two regularity notions |
| — | `gph Ψ` closed above points where `K` is l.s.c. | ✓ | `mem_solutionMap_of_mem_closure`, `isClosed_bilevelFeasible` | |
| D Def 4.1 | semicontinuity of functions | ✓ | Mathlib `LowerSemicontinuousAt`, `UpperSemicontinuousAt` | |
| D Thm 4.2 | `Λ` and `SP` u.s.c. under (C), (MFCQ) | ✓ | `upperHemicontinuousAt_lowerMultipliers`, `upperHemicontinuousAt_stationaryMap`, `exists_eventually_lowerMultipliers_subset`, `isClosed_graph_lowerMultipliers` | for `SP`, (MFCQ) at all feasible `(x̄, y)`: the book's (MFCQ) on `SP(x̄)` is not enough (`not_upperHemicontinuousAt_stationaryMap_example`) |
| D Ex. p. 73 | `Ψ_loc` not u.s.c. (`x³/3 − yx`); D Ex. p. 74: no continuous selection of `Ψ` | ✓ | `not_upperHemicontinuousAt_localSolutionMap_example`, `not_exists_continuous_selection_example` | |
| D Def 4.3 | upper / local Lipschitz continuity of set-valued maps | ✓ | `UpperLipschitzAt`, `LocallyLipschitzAt`, `LocallyLipschitzAt.upperLipschitzAt`, `UpperLipschitzAt.upperHemicontinuousAt`, `LocallyLipschitzAt.lowerHemicontinuousAt`, `LocallyLipschitzAt.lipschitzLikeAt`, `upperLipschitzAt_singleton_iff`, `locallyLipschitzAt_singleton_iff`, `not_locallyLipschitzAt_example` | in `LipschitzMaps.lean`; nonempty compact images are not part of the definitions; single-valued case is D Def 4.4 |
| D Thm 4.4 | strong stability (Def 4.4) of local solutions under (SSOC) [Kojima] | ✓ | `LowerSSOC`, `IsLowerStronglyStable`, `isLowerStronglyStable_of_isLocalMinOn`, `isLowerStronglyStable`, `exists_pos_lt_of_lowerSSOC`, `exists_pos_eq_of_isLowerKKT` | in `StrongStability.lean`; under (LICQ), as in the book's proof (pp. 101–104), the (MFCQ) version is open; `C²` data, no equality constraints |
| D Thm 4.5 | upper Lipschitz continuity of local solutions and multipliers | ☐ | | |
| D Def 4.5 | `PC¹` functions | ✓ | `IsPC1Selection`, `IsPC1At`, `isPC1At_max` | in `PiecewiseSmooth.lean`; selections are global functions, `C¹` on the open neighborhood |
| D Def 4.6 | contingent cone | ✓ | `VariationalAnalysis.contingentCone` | lean-variational |
| D Thm 4.6 | `PC¹` functions are locally Lipschitz | ✓ | `IsPC1Selection.exists_lipschitzOnWith`, `IsPC1At.exists_lipschitzOnWith`, `norm_sub_le_of_forall_exists_eq` | real induction along segments instead of Lemma 4.2 |
| D Thm 4.7–4.8, Def 4.7–4.8 | Clarke Jacobian of `PC¹` functions, semismoothness | ☐ | | |
| D Def 4.9–4.10, (4.15) | directional and Bouligand differentiability of `PC¹` functions | ✓ | `HasDirDerivAt`, `IsBouligandDiffAt`, `IsPC1Selection.exists_tendsto_slope`, `IsPC1At.exists_tendsto_slope`, `HasDirDerivAt.norm_sub_le`, `HasDirDerivAt.map_smul`, `HasDirDerivAt.isBouligandDiffAt`, `IsPC1At.exists_isBouligandDiffAt` | (4.15) with active instead of strongly active selections; proved along rays by a connectedness argument |
| D Def 4.11, Thm 4.9 | pseudodifferentiability | ☐ | | |
| D Thm 4.10 | local solution function is `PC¹` under (SSOC) [Ralph–Dempe] | ✓ | `isPC1At_of_lowerSSOC`, `exists_isPC1At_of_lowerSSOC`, `lowerSelection`, `isInvertible_fderiv_lowerKKTMap`, `eventually_exists_lowerSelection` | in `PiecewiseSolution.lean`; under (LICQ) instead of (MFCQ) + (CRCQ) (the book refers to [235] for the proof); selection functions from the implicit function theorem for the problems (4.19) |
| D Thm 4.11 | directional derivative of the local solution function = unique solution of `QP(λ⁰, r)` (4.20) | ✓ | `hasDirDerivAt_of_lowerSSOC`, `lowerQPObjective`, `lowerQPFeasible` | under (LICQ), so `λ⁰` is unique and (4.21) is trivial |
| D Thm 4.12–4.13, Cor 4.1 | generalized Jacobian of the local solution function | ☐ | | the Lipschitz and B-differentiability parts of Cor 4.1 follow from `isPC1At_of_lowerSSOC` with `IsPC1At.exists_lipschitzOnWith` and `IsPC1At.exists_isBouligandDiffAt` |
| D Thm 4.14 | value function locally Lipschitz under (C), (MFCQ) | ✓ | `exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt` | (C) replaced by continuity of `g` and local boundedness of `G`; via [Mordukhovich 2018, Thm. 4.3] and `lipschitzLikeAt_lowerFeasible` |
| D Thm 4.15 | bounds for the Dini directional derivatives of the value function | ✓ | `eventually_lowerValue_add_smul_le`, `eventually_le_lowerValue_add_smul`, `exists_lowerMultiplier_direction`, `lagrangianGradient` | stated without Dini derivatives: `μ(x̄ + t r) ≤ μ(x̄) + t c` for small `t > 0` and every `c` above the bound; upper bound by LP duality (4.51)–(4.52) from Farkas' lemma, lower bound from (4.27) |
| D Thm 4.16 | directional differentiability of the value function for convex problems | ✓ | `exists_tendsto_slope_lowerValue_of_isConvexLower`, `exists_tendsto_slope_lowerValue_of_eventually_isConvexLower`, `eventually_le_lowerValue_add_smul_of_isConvexLower`, `eventually_lowerValue_add_smul_le_of_isConvexLower`, `lowerMultipliers_subset_of_isConvexLower`, `le_lagrangian_of_isLowerKKT` | `min max` formula with convexity at `x̄` only; the book's `max min` formula with convexity near `x̄`; the book's proof gives `max min ≤ D₊ ≤ D⁺ ≤ min max` and no minimax theorem applies, both bounds are sharpened here |
| D Cor 4.4 | directional derivative of the value function under (LICQ) | ✓ | `exists_tendsto_slope_lowerValue_of_lowerLICQ`, `lowerMultipliers_subsingleton_of_lowerLICQ` | the minimum is attained by compactness of `{(y, λ) \| y ∈ Ψ(x̄), λ ∈ Λ(x̄, y)}`; continuity of `y ↦ λ(y)` is not used |
| D Thm 4.17 | `∂̄φ(y⁰) ⊆ co ⋃ ∇L` (4.27) | ✓ | `clarkeSubdiff_lowerValue_subset`, `exists_clarkeSubdiff_lowerValue_subset`, `lagrangianGradients`; limiting version `subdiff_lowerValue_subset_iUnion` | via `∂̄μ = co ∂μ` (`VariationalAnalysis.clarkeSubdiff_eq_convexHull`) and [Mordukhovich 2018, Thm. 4.1(ii)] |
| D Cor 4.5 | equality in (4.27) under (LICQ) | ✓ | `clarkeSubdiff_lowerValue_eq_of_lowerLICQ`, `eventually_lowerValue_le_of_lowerLICQ`, `LowerLICQ`, `lowerPLI_of_lowerLICQ` | direct proof by feasible curves, not via Cor 4.4; Clarke regularity of `φ` not formalized |
| D Cor 4.6 | `∂̄φ(y⁰) = ∇L(x⁰, y⁰, Λ(x⁰, y⁰))` for convex problems with `Ψ(y⁰) = {x⁰}` | ✓ | `clarkeSubdiff_lowerValue_eq_of_isConvexLower`, `eventually_le_lowerValue_of_isConvexLower`, `upperHemicontinuousAt_lowerSolution` | direct proof by strict differentiability, not via Thm 4.16 |
| D Cor 4.7 | the same for jointly convex problems, `Ψ(y⁰)` arbitrary | ✓ | `clarkeSubdiff_lowerValue_eq_of_convexOn`, `le_lowerValue_of_convexOn`, `lagrangianGradients_subset_of_convexOn` | via KKT for the joint problem instead of Lemma 4.4 and the saddle-point argument; (MFCQ) at all `y ∈ Ψ(y⁰)` |

## D Ch. 5.4–5.5 / S "Single-level reformulations": the KKT reformulation

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D (5.26), (5.27) | KKT reformulation and its nonsmooth version | ✓ | `IsLowerKKT`, `lowerMultipliers`, `kktFeasible`, `isLowerKKT_iff_min` | no lower-level equality constraints |
| — | KKT conditions sufficient for a convex follower | ✓ | `mem_solutionMap_of_isLowerKKT` | via `Convex_first_order_condition` (lean-convex) |
| S pp. 115–117 | KKT conditions necessary under a CQ | ✓ | `exists_isLowerKKT_of_mem_solutionMap` | positive linear independence (dual MFCQ), via [Mordukhovich 2018, Ex. 2.51(ii)] |
| S p. 146 | Slater's condition | ✓ | `SlaterAt`, `lowerPLI_of_slaterAt`, `mem_solutionMap_iff_exists_isLowerKKT` | |
| DD, S p. 151 | bilevel global ⇒ KKT global for every multiplier | ✓ | `isMinOn_kktFeasible_of_isMinOn` | convexity for all `x ∈ Ω` (used silently on the slides) |
| DD, S p. 171 | KKT global ⇒ bilevel global under Slater for all `x ∈ Ω` | ✓ | `isMinOn_bilevelFeasible_of_isMinOn_kktFeasible`, `isOptimisticSolution_of_isMinOn_kktFeasible` | |
| D Thm 5.15 | local optimistic ⇒ local for (5.26) | ✓ | `isLocalMinOn_kktFeasible_of_isLocalMinOn`, `IsLocalOptimisticSolution.isLocalMinOn_kktFeasible` | (MFCQ) only needed for `Λ ≠ ∅` |
| D Ex. p. 158 | nonconvex follower: global solution not local for (5.26) | ✓ | `not_isLocalMinOn_kktFeasible_nonconvex_example` | stationary points are `(3/8 ± 1/40) y` |
| DD, S pp. 180–187 | no Slater anywhere: KKT global ⇏ bilevel global | ✓ | `isMinOn_kktFeasible_noSlater_example`, `not_isMinOn_bilevelFeasible_noSlater_example`, `not_slaterAt_noSlater_example` | |
| DD, S pp. 153–170 | Slater fails at the solution: bilevel global, KKT has no solution | ✓ | `isMinOn_bilevelFeasible_slaterFails_example`, `not_exists_isMinOn_kktFeasible_slaterFails_example`, `mem_kktFeasible_slaterFails_example`, `not_slaterAt_slaterFails_example`, `slaterAt_slaterFails_example` | feasible points `x = 2s²`, `y = (-s, -s²)`, `λ = 1/(4s)`; on the slides the stationarity condition has `2λ₂y₂` for `2λ₂y₁` |
| DD Thm 3.1 | KKT local for every multiplier ⇒ bilevel local; equivalence under convexity and Slater | ✓ | `isLocalMinOn_bilevelFeasible_of_forall_isLocalMinOn_kktFeasible`, `isLocalMinOn_bilevelFeasible_iff_forall_isLocalMinOn_kktFeasible` | converse needs only `C¹` and (MFCQ) at `(x̄, ȳ)`, no convexity; Slater only at `x̄`; via tube lemma and Thm 4.2 |
| DD, S p. 188 | local solutions of (5.26) need not be local bilevel solutions | ✓ | `isLocalMinOn_kktFeasible_not_isLocalMinOn_bilevelFeasible_example` | linear example from [Dempe et al. 2015] (in *Solving Methods*, p. 27), not Schmidt's Ex. 4.6 |
| D p. 77 | (CRCQ) | ✓ | `LowerCRCQ` | for the follower's inequality constraints |
| — | vertices of `Λ(x, y)`: independent support gradients, finitely many | ✓ | `mem_extremePoints_lowerMultipliers_iff`, `finite_extremePoints_lowerMultipliers` | vertices = `Set.extremePoints` |
| DD Cor 3.3 | under (CRCQ), vertices of `Λ(x̄, ȳ)` suffice | ✓ | `isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_isLocalMinOn_kktFeasible`, `isLocalMinOn_bilevelFeasible_of_forall_mem_extremePoints_of_slaterAt`, `upperHemicontinuousAt_extremePoints_lowerMultipliers` | no convexity in the general form; convexity only at `x̄` with Slater |
| D Thm 5.11 | (MFCQ) fails at every feasible point of (5.26) | ✓ | `not_nonsmoothMFCQ_complementarity`, `not_nonsmoothMFCQ_aggregatedComplementarity`, `not_nonsmoothMFCQ_kkt`, `not_nonsmoothMFCQ_kkt_aggregated`, `exists_abnormalMultiplier_complementarity` | for any program containing `g ≤ 0`, `v ≥ 0`, `vᵢ gᵢ = 0`; dual proof: `(λ, -g, -1)` is an abnormal multiplier (product rule), instead of the book's primal argument; (LICQ) fails too; stationarity plays no role |
| — | Clarke's generalized gradient of `min {a, b}` | ✓ | `exists_of_mem_clarkeSubdiff_min` | via `∂̄ = co ∂` and the minimum rule [Mordukhovich 2018, Prop. 4.9] |
| [Scheel–Scholtes 2000] | F. John / KKT conditions for programs with `min {-gᵢ, vᵢ} = 0` constraints; strong stationarity | ✓ | `exists_fritzJohn_mpcc`, `exists_kkt_mpcc`, `nonneg_and_unique_of_isWeakMultiplier`, `mpccFeasible`, `IsWeakMultiplier` | the abstract results behind D Thm 5.16, 5.17; (SMFCQ) in dual form |
| D Thm 5.16 | F. John conditions (5.29) for (5.27) | ✓ | `exists_fritzJohn_kktReformulation`, `lagrangianSecondDeriv` | `φ`, `gᵢ` of class `C²`; `ζᵢ ξᵢ ≥ 0` for all `i`; `κ₀ ∈ {0, 1}`; no lower-level equality constraints |
| D Thm 5.17 | KKT conditions (5.34) under (MFCQ) for (5.30); (5.35) and uniqueness under (SMFCQ) | ✓ | `exists_kkt_kktReformulation`, `nonneg_and_unique_kktReformulation`, `TightenedMFCQ`, `TightenedSMFCQ` | constraint qualifications stated without coordinates; second part by relaxing one biactive constraint and uniqueness of multipliers, instead of Bouligand stationarity |
| D Ex. p. 162 | (5.35) fails under (MFCQ) alone | ✓ | `isMinOn_mpccFeasible_example`, `nonsmoothMFCQ_example`, `not_nonneg_of_isWeakMultiplier_example` | the complementarity condition is `z₁ (z₁ + z₂) = 0`, misprinted as `z₁ (z₂ + z₃) = 0` |
| D Thm 5.12 | genericity of (PLICQ) | ☐ | | needs Whitney topology and Sard |
| — | Farkas' lemma, closedness of finitely generated cones, conic Carathéodory | ✓ | `exists_nonneg_eq_sum_of_forall_nonneg`, `isClosed_nonnegSpan`, `exists_nonneg_linearIndependent_sum_eq` | in `Farkas.lean`; candidate for lean-variational |
| S p. 118 | LP–LP bilevel problem | ✓ | `LinearBilevel` | rows as continuous linear functionals; leader constraints may couple `x` and `y` |
| S pp. 122, 139–142 | follower's LP: KKT conditions, dual, weak and strong duality | ✓ | `mem_lowerSolution_iff`, `sum_mul_le_of_isDualFeasible`, `mem_lowerSolution_iff_exists_isLowerKKT`, `isLowerKKT_iff` | no constraint qualification (Farkas) |
| S pp. 123–124 | KKT reformulation of LP–LP: global equivalence | ✓ | `image_fst_kktFeasible`, `isMinOn_kktFeasible_iff`, `exists_isMinOn_kktFeasible` | |
| S pp. 143–144 | strong-duality reformulation, equivalence with KKT | ✓ | `complementarity_iff_le`, `complementarity_iff_eq`, `kktFeasible_eq_sdFeasible`, `isMinOn_sdFeasible_iff` | |
| S p. 133 | big-M MILP reformulation | ✓ | `mem_kktFeasible_of_mem_bigMFeasible`, `exists_mem_bigMFeasible`, `isMinOn_bigMFeasible_of_isMinOn_kktFeasible`, `isMinOn_feasible_of_isMinOn_bigMFeasible` | "`M` sufficiently large" = `M` bounds multipliers and slacks of one global KKT solution |
| S p. 127 | (MFCQ)/(LICQ) fail at every feasible point of the KKT reformulation | ✓ | `LinearBilevel.not_nonsmoothMFCQ_kkt` | Ye–Zhu 1995; instance of D Thm 5.11 |
| S p. 134 | hardness of a bilevel-correct big-M | ☐ | | complexity result, out of scope |

## D Ch. 5.6: the value function approach

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D (5.36) | value function reformulation | ✓ | `bilevelFeasible_eq_valueFeasible`, `bilevelFeasible_lowerFeasible` | identifies (5.5) with `VariationalAnalysis.valueFeasible` |
| D Def 5.9 | partial calmness | ✓ | `VariationalAnalysis.PartiallyCalm` | [Mordukhovich 2018, Def. 6.14] |
| D p. 165 | uniform weak sharp minimum ⇒ partial calmness | ✓ | `VariationalAnalysis.partiallyCalm_of_uniform_weakSharp` | [Mordukhovich 2018, Prop. 6.17] |
| D p. 163 | (NMFCQ), (NLICQ), abnormal multipliers (5.39) | ✓ | `NonsmoothMFCQ`, `NonsmoothLICQ`, `abnormalMultipliers`, `NonsmoothLICQ.nonsmoothMFCQ` | via Clarke's generalized gradient |
| D Thm 5.18 | (NMFCQ) ⟺ `Λ⁰(z) = {0}` | ✓ | `nonsmoothMFCQ_iff_abnormalMultipliers_eq` | Motzkin's alternative `VariationalAnalysis.exists_multipliers_of_not_exists_direction`; needs nonempty generalized gradients (Lipschitz data), not feasibility |
| [Clarke 1983, Thm 6.1.1] | multiplier rule for Lipschitz programs (used in D Thm 5.20, 5.21) | ✓ | `exists_fritzJohn_clarke`, `exists_kkt_clarke_of_abnormalMultipliers_eq`, `exists_kkt_clarke_of_nonsmoothMFCQ` | from [Mordukhovich 2018, Thm. 6.5(ii)] with `∂f ⊆ ∂̄f` |
| D Thm 5.19 | (5.36) has a nontrivial abnormal multiplier; no (NMFCQ)/(NLICQ) | ✓ | `exists_abnormalMultiplier_valueConstraints`, `not_nonsmoothMFCQ_valueConstraints`, `valueConstraints` | "equality in (4.27)" as `co ⋃ ∇ₓL ⊆ ∂̄μ'(x̄)`; (C) not needed given it |
| D Thm 5.20 | F. John conditions via the value function | ✓ | `exists_fritzJohn_valueFunction` | nontriviality of the multipliers added (missing in the statement) |
| D Thm 5.21 | KKT conditions via the value function | ✓ | `exists_kkt_valueFunction` | equality in (4.27) not needed; limiting version with inner semicontinuity at one `ȳ`: `VariationalAnalysis.exists_multipliers_smooth_bilevel_upper` [Mordukhovich 2018, Thm. 6.21] |

## Not started

Ch. 5.2–5.3, 5.7, Ch. 7
(regularization), Ch. 8 (discrete bilevel problems).
