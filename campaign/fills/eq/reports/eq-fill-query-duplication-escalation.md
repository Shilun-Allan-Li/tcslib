# E-DUP — prohibited new cross-file pairs

The completed after-edit screen on frozen commit
`9d93626dadf1561c757494cfff992d1951a458e2` reports two new pair identities:

| Owned declaration | Other-file declaration | Reproduction |
|---|---|---|
| `NTimeDiagonalizer.lean::qy_guard_decider` | `Nondeterminism.lean::a3n_poly_fixed_eq` | 76/114 = 67% |
| `NTimeDiagonalizer.lean::qy_guard_decider` | `TMSAT.lean::tmsat_pt_eq` | 76/127 = 60% |

Neither reaches the screen's 90% copy threshold. Nevertheless, the brief independently says
**No new cross-file pair with an owned-file declaration on one side. Nothing is pre-disclosed.**
Therefore this delivery fails that requirement. The result is not waived as a generic idiom
or a pre-disclosed match. There are no new in-file pairs and no changed existing measurements.

Both neighboring private lemmas establish polynomial-time equality with a fixed word through
the public `computesFunInTime_ifEq` row. The new linear guard's local fixed-word decider also
uses that public row. The semantic searches had identified these neighboring constructions,
and the new proof uses the public increment laws rather than reproducing their unary-input
inductions, but that does not discharge the independent text-screen rule. The raw before,
after and comparison outputs are included. No other-file private lemma is cited.

This is a local escalation label for the duplication requirement, not a mathematical
unprovability claim. Following the earlier E-SERIAL finding, no additional proof construction
is attempted. The existing checkpoint is delivered with the prohibition failure explicitly
recorded. A continuation would need a permitted proof refactoring or a maintainer ruling;
the present delivery is not certified compliant.
