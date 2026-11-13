# lean-bilevel

A Lean 4 library of results on bilevel optimization in finite dimensions, built on
[lean-variational](https://github.com/dvillacis/lean-variational) (a formalization of [Mordukhovich 2018]) and Mathlib.

The optimality conditions of [Mordukhovich 2018, Ch. 6] (value function approach, partial calmness,
weak sharp minima, Thm. 6.21 and 6.23) live in lean-variational
(`VariationalAnalysis.Optimality.Bilevel`, `VariationalAnalysis.Optimality.BilevelSmooth`). This
library contains the material of [Dempe 2002] and [Schmidt 2024].

## Conventions

The leader's variable is `x ∈ E` and the follower's variable is `y ∈ F`; [Dempe 2002] uses the
opposite letters. The data are the leader's objective `f`, the follower's objective `φ`, the
follower's feasible-set map `K` (or constraints `gᵢ(x, y) ≤ 0`) and the leader's constraint set
`Ω`. The follower's solution map is `solutionMap φ K`.

## Contents

| Topic | Files | Content |
|---|---|---|
| Solution concepts | `BilevelOptimization/Basic` | optimistic and pessimistic solutions (D Def. 5.2, 5.3), the joint problem (5.5), lower optimal solutions (5.8), value function reformulation (5.36) and its link to lean-variational, unique lower-level solutions (D Def. 5.1, S p. 85), the high-point relaxation (S p. 42), examples |
| Parametric optimization | `BilevelOptimization/Parametric` | semicontinuity of set-valued maps (D Def. 4.2), compactness of the multiplier set (D Thm. 4.1), upper semicontinuity of the multiplier and stationary-point maps and persistence of (MFCQ) (D Thm. 4.2, with a counterexample to the book's hypotheses), continuity of the value function and upper semicontinuity of `Ψ` (D Thm. 4.3), (MFCQ) ⇒ lower semicontinuity of the feasible-set map, existence of optimistic and pessimistic solutions (D Thm. 5.2, 5.3) |
| Value function | `BilevelOptimization/ValueFunction` | local Lipschitz continuity of the follower's value function (D Thm. 4.14) and the estimate of its Clarke generalized gradient (D Thm. 4.17), with equality under (LICQ) or convexity (D Cor. 4.5–4.7) |
| Lipschitz programs | `BilevelOptimization/LipschitzProgram` | nonsmooth (MFCQ)/(LICQ) and abnormal multipliers (D Thm. 5.18), the Clarke multiplier rule in Fritz John and KKT form |
| Directional derivatives of the value function | `BilevelOptimization/ValueFunctionDirectional` | bounds for the Dini directional derivatives (D Thm. 4.15), directional differentiability under (LICQ) (D Cor. 4.4) and for convex problems with the min–max and max–min formulas (D Thm. 4.16) |
| Value function approach | `BilevelOptimization/ValueFunctionOptimality` | failure of nonsmooth constraint qualifications for (5.36) (D Thm. 5.19), Fritz John and KKT conditions via the Clarke gradient of the value function (D Thm. 5.20, 5.21) |
| KKT reformulation | `BilevelOptimization/KKT` | KKT conditions of a convex follower (sufficiency, necessity under Slater or positive linear independence), global equivalence with (5.26) [Dempe–Dutta 2012], local solutions (D Thm. 5.15), counterexamples without convexity or Slater, and with Slater failing only at the solution |
| Regularity of the KKT reformulation | `BilevelOptimization/KKTRegularity` | (MFCQ) and (LICQ) fail at every feasible point of a program containing complementarity conditions (D Thm. 5.11), in particular of the KKT reformulation (5.26) and of its LP–LP version [Schmidt 2024, p. 127] |
| Programs with complementarity constraints | `BilevelOptimization/MPCC` | Clarke's generalized gradient of a minimum of two smooth functions; Fritz John and KKT conditions and strong stationarity for programs with constraints `min {-gᵢ, vᵢ} = 0` [Scheel–Scholtes 2000]; an example where (MFCQ) does not give strong stationarity (D p. 162) |
| Optimality conditions via the KKT reformulation | `BilevelOptimization/KKTOptimality` | Fritz John conditions for the nonsmooth KKT reformulation (5.27) (D Thm. 5.16); KKT conditions under (MFCQ) for the tightened problem (5.30), and nonnegative, unique multipliers under (SMFCQ) (D Thm. 5.17) |
| Farkas' lemma | `BilevelOptimization/Farkas` | conic Carathéodory, closedness of finitely generated cones, Farkas' lemma in finite-dimensional normed spaces |
| Linear bilevel problems | `BilevelOptimization/LinearBilevel` | LP–LP bilevel problems [Schmidt 2024]: KKT conditions of the follower's LP without constraint qualification, weak and strong duality, global equivalence with the KKT, strong-duality and big-M reformulations |
| Geometry of linear bilevel problems | `BilevelOptimization/LinearGeometry` | D Ch. 3: polyhedral solution map (D Thm. 3.1), existence (D Thm. 3.3), vertex solutions (D Cor. 3.1), existence with leader-dependent follower objective (D Thm. 3.2), optimality via the duality gap (D Thm. 3.11), examples D pp. 30, 33, 38–39 |
| Lipschitz set-valued maps | `BilevelOptimization/LipschitzMaps` | upper and local Lipschitz continuity (D Def. 4.3) and their relation to semicontinuity and the Lipschitz-like property |
| Piecewise smooth functions | `BilevelOptimization/PiecewiseSmooth` | `PC¹` functions (D Def. 4.5): local Lipschitz continuity (D Thm. 4.6), directional and Bouligand differentiability (D Def. 4.9–4.10, (4.15)) |
| Strong stability | `BilevelOptimization/StrongStability` | (SSOC), second-order sufficiency, uniqueness of nearby KKT points and Kojima's strong stability under (LICQ) (D Thm. 4.4) |
| Piecewise smooth solutions | `BilevelOptimization/PiecewiseSolution` | selection functions of (4.19) by the implicit function theorem; the local solution function is `PC¹` (D Thm. 4.10) and its directional derivative solves `QP(λ⁰, r)` (D Thm. 4.11), under (LICQ) and (SSOC) |
| Optimality via strong stability | `BilevelOptimization/StrongStabilityOptimality` | unique lower-level solution function of a convex follower; necessary conditions (5.10), (5.11) with the directional derivative (D Thm. 5.4); non-sufficiency example (D p. 138) |
| Local KKT solutions | `BilevelOptimization/KKTLocal` | local solutions of (5.26) for every multiplier are local bilevel solutions, and the local equivalence under convexity and Slater [Dempe–Dutta 2012, Thm. 3.1]; under (CRCQ) the vertices of the multiplier set suffice (Cor. 3.3); a counterexample with a single multiplier |

D = [Dempe 2002]. `ROADMAP.md` lists the statements of the sources with their Lean names or status.

## Building

The package depends on [lean-variational](https://github.com/dvillacis/lean-variational) at a
pinned commit (see `lakefile.toml`), which in turn pins Mathlib.

```
lake build
lake env lean scripts/AuditAxioms.lean   # checks that no proof uses `sorry`
```

## References

* [Dempe 2002] S. Dempe, *Foundations of Bilevel Programming*, Kluwer, 2002.
* [Dempe–Dutta 2012] S. Dempe, J. Dutta, Is bilevel programming a special case of a mathematical
  program with complementarity constraints?, *Math. Program.* 131 (2012) 37–48.
* [Mordukhovich 2018] B. S. Mordukhovich, *Variational Analysis and Applications*, Springer, 2018.
* [Scheel–Scholtes 2000] H. Scheel, S. Scholtes, Mathematical programs with complementarity
  constraints: stationarity, optimality, and sensitivity, *Math. Oper. Res.* 25 (2000) 1–22.
* [Schmidt 2024] M. Schmidt, *A Primer on Bilevel and Robust Optimization*, lecture notes,
  IWOBIP 2024.
* [Ye–Zhu 1995] J. J. Ye, D. L. Zhu, Optimality conditions for bilevel programming problems,
  *Optimization* 33 (1995) 9–27.
