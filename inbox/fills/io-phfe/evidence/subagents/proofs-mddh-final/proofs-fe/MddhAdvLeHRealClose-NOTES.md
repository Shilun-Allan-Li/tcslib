# MddhAdvLe.hRealClose: one-block scalar-law ladder

Scratch-only candidate. No Lean, lake, build, Git, live source modification, or new public
helper was performed. This is NOT a completed proof or a native-checked candidate.

## Insertion and remaining obligations

Insert the proof-only fragment into the existing `hRealClose` body in
`TCSlib/Cryptography/Pairing/MatrixDH/SelfReduction.lean`, preserving its header.
The file has exactly one tactic block and two explicit local admitted equalities:

1. `hReductionTransport`: move the fixed-order advice sample through public-parameter
   generation, transport its coordinates by the public order equality, read the actual
   reduction with `hPreScalar`, and interchange the independent draws into the displayed
   `S,U,ab,rs,L` order. The original unused DLIN final scalar is integrated by `expect_const`;
   its draw is not removed from the definition of the actual experiment.
2. `hHybridResample`: transpose S to a tuple of whole columns, sample selected column j
   separately, and use the guard equivalence `b.val < j.val+1` iff
   `b.val = j.val or b.val < j.val`. The observer ignores S's j-column: selected output uses v,
   earlier outputs only use earlier S-columns, and later outputs use U. Thus the existing
   generic resampling/coordinate law applies. U and every other coordinate stay drawn.

The rest of the block instantiates `dlin_real_column_gap_le` with a genuine [0,1]-valued
acceptance probability and applies `ProbComp.abs_expect_sub_le` over U, S, and pp. It does
not add dlinMatrixSlack: its exact loss is `1/(p κ)^2` only. The complete direct reduction
combines this with the separately proved canonical random loss and existing hLossBudget.

## Exact reuse and searches (static, this invocation)

Read current live SelfReduction around lines330-560, including the unchanged hPreScalar
statement. Parent reports hPreScalar now native PASS: root corrected obsolete
`Matrix.dotProduct{_comm}` to global `dotProduct{_comm}`, and reduced the closed Fin indices
in hBase. The earlier scratch hPreScalar candidate is superseded by that checked root version.
No dot-product name is used in this new block.

Queries performed from the managed worktree:

- `rg -n 'abs_expect_sub_le_expect|expect_const|prob_nonneg|prob_le_one|expect_sample_coord|expect_sample_update|expect_expect_sample'` over Games/Probability,
  Games/Bridges/Experiments, OneWayFunctions/Basic.
- `sed -n '310,430p' TCSlib/Cryptography/Games/Probability.lean`.
- `sed -n '70,135p' TCSlib/Cryptography/Pairing/MatrixDH/ColumnLaws.lean`.
- `rg -n 'theorem (sample_bij|expect_sample_equiv|expect_sample_pair|expect_sample_comm|expect_sample_congr|prob_eq_expect)|ringEquivCongr|transpose.*Equiv|piCongrRight'`
  over Probability, Mathlib/Data/ZMod/Basic, Mathlib/Data/Matrix/Basic. One misspelled
  EnsemblesLemmas path failed; corrected inventory found Asymptotic/EnsemblesLemmas.
- `rg -n 'theorem card |lemma card |card \(.*ZMod|ZMod.card|order_eq_of_publicParams|orderSchedule_neZero'`
  over Mathlib/Data/ZMod, Pairing/Linear and ColumnLaws. An initially guessed Parameters path
  failed; actual public-parameter home is Pairing/MatrixDH/Parameters. ZMod.card is at
  Mathlib/Data/ZMod/Defs:164, and has the required `[Fintype (ZMod n)]`-polymorphic signature.
- Read Probability:294-313, OneWayFunctions/Basic:115-146, Pairing/Linear:215-248 and380-414,
  and MatrixDH/Parameters:1-90.

Relevant published APIs (all located in the preceding searches):

- `dlin_real_column_gap_le`, ColumnLaws:84: bounded observer of `(M,v)`; the real canonical
  transformed pair `(L*A, L*(A*rs))` is within `1/card(K)^2` of `(M,M*rs)`.
- `ProbComp.abs_expect_sub_le`, Probability:391: constant bounds average directly. This
  avoids repeating the lower-level abs-expect/expect-constant argument three times.
- `ProbComp.prob_nonneg` and `prob_le_one`, Probability:230 and236: observer bounds.
- `ProbComp.expect_sample_equiv`, Probability:304; `expect_sample_comm`:313;
  `expect_expect_sample`:326; `Games.Bridge.expect_sample_pair`, Bridges/Experiments:80:
  reindex/factor/commute the independent draws in the two remaining equalities.
- `ProbComp.expect_sample_coord`, Probability:383 (and its implementation through
  `expect_sample_update`:355): *generic* in the coordinate type β. Use
  β = `Fin 2 → ZMod pp.group.order` after transpose. It already proves the needed
  whole-column resampling; do not reprove the counting argument.
- Alternatively `OneWay.uprob_update`, Basic:131, is generic in α and can plant that same
  whole column, with all remaining matrices and D coins packed into ρ.
- `ZMod.ringEquivCongr`, Mathlib/Data/ZMod/Basic:419, with refl/symm/val readers:440/444/459;
  `ZMod.card`, Defs:164; public `order_eq_of_publicParams`: the scalar-field/card transport.
- `G.dlinSample_eq`, Pairing/Linear:231; `G.mddhPre_eq`, SelfReduction:278;
  `accept_eq`, `ProbComp.prob_bind`, `expect_bind`, `expect_pure`, `prob_eq_expect`:
  actual-game transport without reading the foreign `ProbComp.prob` body.

## Modularity and native-check cautions

No public helper is proposed. All new definitions are local mathematical observers/averages,
not samplers, machines or hosts. They use only known scalar draws, never discrete logarithms
or scalar witnesses for group data. No foreign public definition appears in a simp/rw/unfold
list. Explicit local definitions may reduce under `change`.

This fragment is 81 lines. Current SelfReduction is about700 lines; adding analogous random
comparison plus completing both transport equalities could approach1000. Prefer sharing the
observer/transport layout between the two local comparisons in the existing theorem if needed;
the generic Fubini/resampling laws already have public homes and must be reused rather than
copied. Root should check this surrounding ladder before filling either transport hole.
The local prime Fact and NeZero instances are explicit before the scalar theorem call,
preventing the previously diagnosed synthetic Field(ZMod _) problem.
