# Roadmap

Status: ✓ formalized, ◐ partially, ☐ not yet. D = [Dempe 2002], S = [Schmidt 2024] (physical
slide pages), DD = [Dempe–Dutta 2012].

## D Ch. 5.1 / S "Solution concepts": optimality concepts

| # | Statement | Status | Lean | Notes |
|---|---|---|---|---|
| D (5.1)–(5.4), (5.7) | solution map, optimistic and pessimistic value functions | ✓ | `solutionMap`, `optimisticValue`, `pessimisticValue` | values in `EReal` |
| D Def 5.1 | local/global solutions under unique lower-level solutions | ☐ | | subsumed by Def 5.2 when `Ψ` is single-valued |
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
| D Ex. pp. 135–136 | position of coupling constraints matters; inactive constraints matter | ☐ | | |
| S p. 85 | optimistic = pessimistic for unique lower-level solutions | ☐ | | |
| S p. 42 | high-point relaxation | ☐ | | |

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
| D Ex. p. 73 | `Ψ_loc` not u.s.c. (`x³/3 − yx`); D Ex. p. 74: no continuous selection of `Ψ` | ☐ | | |
| D Def 4.3 | upper / local Lipschitz continuity of set-valued maps | ☐ | | compare `VariationalAnalysis.LipschitzLikeAt` |
| D Thm 4.4 | strong stability under (MFCQ), (SSOC) [Kojima] | ☐ | | |
| D Sect. 4.3–4.4, Thm 4.5–4.13 | `PC¹` functions, directional differentiability of local solution functions (SSOC, CRCQ) | ☐ | | |
| D Thm 4.14 | value function locally Lipschitz under (C), (MFCQ) | ✓ | `exists_lipschitzOnWith_lowerValue_of_locallyBoundedAt` | (C) replaced by continuity of `g` and local boundedness of `G`; via [Mordukhovich 2018, Thm. 4.3] and `lipschitzLikeAt_lowerFeasible` |
| D Thm 4.15–4.16 | Dini directional derivatives and directional differentiability of the value function | ☐ | | |
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
| DD, S pp. 153–170 | Slater fails at the solution: bilevel global, KKT has no solution | ☐ | | |
| DD, S p. 188 | local solutions of (5.26) need not be local bilevel solutions | ☐ | | the DD converse (under Slater, for all multipliers) |
| D Thm 5.11 | (MFCQ) fails at every feasible point of (5.26) | ☐ | | |
| D Thm 5.16, 5.17 | F. John / KKT conditions for (5.27) | ☐ | | |
| D Thm 5.12 | genericity of (PLICQ) | ☐ | | needs Whitney topology and Sard |
| S pp. 118–144 | LP–LP: KKT, strong duality, big-M reformulations | ☐ | | |

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

D Ch. 3 (linear bilevel problems), Ch. 5.2–5.3, 5.7, Ch. 7
(regularization), Ch. 8 (discrete bilevel problems).
