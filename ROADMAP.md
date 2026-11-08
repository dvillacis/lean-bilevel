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
| D Thm 4.2 | `Λ` and `SP` u.s.c. under (C), (MFCQ) | ☐ | | |
| D Ex. p. 73 | `Ψ_loc` not u.s.c. (`x³/3 − yx`); D Ex. p. 74: no continuous selection of `Ψ` | ☐ | | |
| D Def 4.3 | upper / local Lipschitz continuity of set-valued maps | ☐ | | compare `VariationalAnalysis.LipschitzLikeAt` |
| D Thm 4.4 | strong stability under (MFCQ), (SSOC) [Kojima] | ☐ | | |
| D Sect. 4.3–4.4, Thm 4.5–4.13 | `PC¹` functions, directional differentiability of local solution functions (SSOC, CRCQ) | ☐ | | |
| D Thm 4.14 | value function locally Lipschitz under (C), (MFCQ) | ☐ | | |
| D Thm 4.15–4.17 | Dini directional derivatives, directional differentiability and Clarke generalized gradient of the value function | ☐ | | 4.17 needs Clarke calculus |

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
| D Thm 5.20, 5.21 | F. John / KKT conditions via the value function | ◐ | `VariationalAnalysis.exists_multipliers_smooth_bilevel_upper` | the limiting-subdifferential version [Mordukhovich 2018, Thm. 6.21]; Dempe's Clarke version is not formalized |
| D Thm 5.18, 5.19 | nonsmooth MFCQ fails for (5.36) | ☐ | | |

## Not started

D Ch. 3 (linear bilevel problems), Ch. 5.2–5.3, 5.7, Ch. 7
(regularization), Ch. 8 (discrete bilevel problems).
