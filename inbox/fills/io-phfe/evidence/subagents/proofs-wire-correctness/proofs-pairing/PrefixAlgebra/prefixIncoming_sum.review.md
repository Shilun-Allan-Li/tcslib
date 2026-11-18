# prefixIncoming_sum proof candidate

Exactly one authorized helper proof is supplied in prefixIncoming_sum.proof.lean.inc.
Its searched header and opening statement prose are unchanged. The proof sketch is
refreshed: use the existing dependent-sigma-map injectivity theorem and a singleton
sum, rather than explicitly decomposing the sum by depth. The fragment has 45 lines,
maximum width 81, one tactic block and no admission or additional public declaration.
The agent ran no Lean, lake, Git, live edit or proof checker; root validation is pending.

## Native reuse probes already completed

The agent read the lead's raw logs:

- evidence/search/prefix-and-polynomial/run/mods/.lake_io-phfe-probes_PrefixAlgebraReuseExact.log;
- evidence/search/prefix-and-polynomial/run/mods/.lake_io-phfe-probes_PrefixAlgebraReuseApply.log.

Exact? reports exactly two unresolved goals, one for each proposed theorem, with no
typing errors. Apply? offers only partial conditional-equality proof steps and the two
expected sorry warnings. No complete existing theorem was found. Focused subsequent
searches are saved in prefixIncoming_sum.searches.txt.

## Reuse route and duplication boundary

The local child function is precisely `Sigma.map Fin.succ` with identity tuple maps.
Its injectivity is consumed from `Function.Injective.sigma_map`, Mathlib/Data/Sigma/
Basic:116, together with `Fin.succ_injective`, Data/Fin/SuccPred:39, and the identity-map
injectivity theorem. No generic sigma-map injection proof is reproduced inline.

The local hroot is only `Fin.succ_ne_zero` (core Init/Data/Fin/Lemmas:405) applied to
the first-coordinate equality from congrArg Sigma.fst. The show step reduces only the
Mathlib Sigma.map and the local empty-prefix tuple; no TCSlib definition is read.

`Fin.cases` (core Fin/Lemmas:893) splits the queried node depth. At depth zero,
`Subsingleton.elim` identifies the empty tuple with Fin.elim0. Its instance is the
existing `Pi.uniqueOfIsEmpty`, Mathlib/Logic/Unique:165, so no empty-function uniqueness
lemma is reproved. The root's supported sum is zero by hroot and the public
Finset.sum_const_zero. Core eq_self (:Init/SimpLemmas:36) and if_true/if_false evaluate
its explicit conditional.

At successor depth, the predecessor depth with the same tuple is a concrete edge e0.
The existing hchild.eq_iff turns equality of child images into edge equality, and
`Fintype.sum_ite_eq'`, generated at Algebra/BigOperators/Group/Finset/Piecewise:292-295,
evaluates the whole finite edge sum. No sum induction, new image-sum or fiberwise-sum
lemma is proved. The same hroot evaluates the final conditional.

The proof contains no foreign definition in simp/rw/unfold. The change/show steps reduce
only core/Mathlib operations and local proof abbreviations. The theorem is independent
of prefixFlow_balance and all M0 Layered admissions. It handles d=0, an empty I, and
arbitrary additive commutative monoids without extra inhabitedness or positivity.
No mathematical obstruction was found.

## Import availability checked statically

No extra import is needed beyond the proposed PrefixAlgebra imports. A read-only import
walk found these existing paths:

- Algebra.BigOperators.Fin → Logic.Equiv.Fin.Basic → Logic.Embedding.Set →
  Logic.Embedding.Basic → Logic.Equiv.Basic → Logic.Equiv.Sum → Data.Sigma.Basic;
- Algebra.BigOperators.Fin → Algebra.Group.Action.Pi → Algebra.Group.Pi.Basic →
  Logic.Unique.

This is only source-level import evidence; no native check was run by the agent.
