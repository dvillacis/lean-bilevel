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
| D Thm 5.1, 5.2 | existence of optimistic solutions | ◐ | `exists_isOptimisticSolution_of_isCompact` | abstract core; compactness of `gph Ψ` from (C) and (MFCQ) needs D Thm 4.3 |
| D Thm 5.3 | existence of pessimistic solutions (`Ψ` l.s.c.) | ☐ | | |
| D Ex. pp. 129, 134; S pp. 74–84 | optimistic solution exists, pessimistic does not | ✓ | `isOptimisticSolution_example`, `not_isPessimisticSolution_example` | the book's formulas for `φ_o`, `φ_p` have the parameter's sign swapped |
| D Ex. pp. 135–136 | position of coupling constraints matters; inactive constraints matter | ☐ | | |
| S p. 85 | optimistic = pessimistic for unique lower-level solutions | ☐ | | |
| S p. 42 | high-point relaxation | ☐ | | |

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

D Ch. 3 (linear bilevel problems), Ch. 4 (parametric optimization), Ch. 5.2–5.3, 5.7, Ch. 7
(regularization), Ch. 8 (discrete bilevel problems).
