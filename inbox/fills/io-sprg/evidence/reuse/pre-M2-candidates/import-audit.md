# Exact import-closure audit before M0

The lead requested known missing roots before header freeze. The audit recursively
read only actual module imports from the current sources, stripping nested Lean
comments and strings first. No build, Lean invocation, package mutation, broad
filesystem inventory, or import edit was performed. The machine-readable result
is import-closure-audit.json; import-closures.json lists the followed modules.
The script audit_imports.py can be rerun from the intended worktree explicitly.

One selected public fact was absent before the audit:
`Nat.div_two_lt_floor` in Mathlib.Algebra.Order.Floor.Semifield. The lead added that
precise import to Stretch at commit bb3455c5015031a9b03a4013fbe8d372fc09791d, where
it is used. Claim42 does not import Stretch; its selected proof route does not need
this lower floor comparison because rounded quotient/noise-denominator cancellation
suffices. Thus no duplicate import in Params/Claim42 is proposed.

| Proof family | Required existing source modules / API | Audit conclusion |
| --- | --- | --- |
| Degree | Algebra.MonoidAlgebra.Degree; Data.Finsupp.Weight; Data.Sum.Basic | All in Degree's present precise closure. Six weighted wrappers use public generic support-degree facts; no new root. |
| Bucket / SparseFactor | Data.Finset.Card/Image; Data.List.FinRange; Logic.Equiv.Fin.Basic; finite-sum API; Data.Matrix.Mul | Existing owner imports reach the selected finite-cardinality, coordinate and matrix APIs. No sorting/interval root is needed for rank candidates. |
| Polynomial / correctness | MvPolynomial Eval/Rename/Variables; Finset sorting and Ring.Finset tensor expansion; List find? Core API | Existing explicit Polys/Correctness/constructor dependencies suffice for the selected route. No new root. |
| Params floor upper bounds | Algebra.Order.Floor.Semiring/Ring; Pow.Real | Already present. W<=ell+1 uses only upper floor/max bounds and real-power order, not the new factor-two lower lemma. |
| Tensor payload count | Algebra.Order.Ring.Basic (add_pow_le); Core Nat division/power inequalities | Already present. Do not add a generic binomial/Stirling root or Floor.Div merely for Nat.ceil-quotient arithmetic. |
| Stretch lower width | Floor.Semifield (Nat.div_two_lt_floor) | The single missing selected root, now added precisely at Stretch. |
| Power-gap transfer | Pow.Asymptotics; Pow.Real; SpecificLimits.Basic; Nat.Cast.Order.Field; imported PolyExpr | Already present. Positive powers absorb constants; Nat.cast_div_le handles integer quotients; eval_le normalizes polynomial bounds. |
| Claim42 log/rates | Pow.Asymptotics; Log.Basic/Base; Nat.Log | Already present through its actual dependencies. natLog_le_logb connects integer logs; existing log/rpow and exp/rpow asymptotics absorb terms. |
| Bucket tail factorial bound | Nat.Choose.Bounds; Complex.Exponential | Both are direct Load roots. choose_le_pow_div plus Real.pow_div_factorial_le_exp suffice; no Stirling import. |
| Shared subexponential security | TCSlib.Cryptography.Foundations.Subexponential | Already present where used through primitive definitions. Its public decay/closure API is for later advantage proofs, not a substitute for M2's ordinary stretch comparison. |

No other known missing root was found for the selected M1/M2/M3 proof paths.
SpecificAsymptotics, Floor.Div and Stirling remain absent where unnecessary and
are not recommended. This is a source-graph/API audit, not an elaboration proof.
Core/Lean provider roots not represented under the repository/package paths are
listed as unlocated; no claim is made to rebuild or inspect all of Lean itself.
