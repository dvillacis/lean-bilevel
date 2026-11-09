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
| Solution concepts | `BilevelOptimization/Basic` | optimistic and pessimistic solutions (D Def. 5.2, 5.3), the joint problem (5.5), lower optimal solutions (5.8), value function reformulation (5.36) and its link to lean-variational, examples |
| Parametric optimization | `BilevelOptimization/Parametric` | semicontinuity of set-valued maps (D Def. 4.2), compactness of the multiplier set (D Thm. 4.1), upper semicontinuity of the multiplier and stationary-point maps and persistence of (MFCQ) (D Thm. 4.2, with a counterexample to the book's hypotheses), continuity of the value function and upper semicontinuity of `Ψ` (D Thm. 4.3), (MFCQ) ⇒ lower semicontinuity of the feasible-set map, existence of optimistic and pessimistic solutions (D Thm. 5.2, 5.3) |
| Value function | `BilevelOptimization/ValueFunction` | local Lipschitz continuity of the follower's value function (D Thm. 4.14) and the estimate of its Clarke generalized gradient (D Thm. 4.17), with equality under (LICQ) or convexity (D Cor. 4.5–4.7) |
| Lipschitz programs | `BilevelOptimization/LipschitzProgram` | nonsmooth (MFCQ)/(LICQ) and abnormal multipliers (D Thm. 5.18), the Clarke multiplier rule in Fritz John and KKT form |
| Value function approach | `BilevelOptimization/ValueFunctionOptimality` | failure of nonsmooth constraint qualifications for (5.36) (D Thm. 5.19), Fritz John and KKT conditions via the Clarke gradient of the value function (D Thm. 5.20, 5.21) |
| KKT reformulation | `BilevelOptimization/KKT` | KKT conditions of a convex follower (sufficiency, necessity under Slater or positive linear independence), global equivalence with (5.26) [Dempe–Dutta 2012], local solutions (D Thm. 5.15), counterexamples without convexity or Slater |
| Farkas' lemma | `BilevelOptimization/Farkas` | conic Carathéodory, closedness of finitely generated cones, Farkas' lemma in finite-dimensional normed spaces |
| Linear bilevel problems | `BilevelOptimization/LinearBilevel` | LP–LP bilevel problems [Schmidt 2024]: KKT conditions of the follower's LP without constraint qualification, weak and strong duality, global equivalence with the KKT, strong-duality and big-M reformulations |
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
* [Schmidt 2024] M. Schmidt, *A Primer on Bilevel and Robust Optimization*, lecture notes,
  IWOBIP 2024.
