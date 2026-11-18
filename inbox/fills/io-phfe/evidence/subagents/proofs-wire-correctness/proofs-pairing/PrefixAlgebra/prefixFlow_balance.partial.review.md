# prefixFlow_balance: explicitly partial one-block draft

prefixFlow_balance.partial.lean.inc preserves the live theorem header and entire
docstring. It contains one tactic block and exactly ONE remaining admission, in the
nonterminal `cast k` branch. It is a proof-development fragment, not a completed theorem
or final proof claim. The agent ran no Lean/lake/Git/live edit or proof checker.

The draft supplies concrete proof code for the terminal-depth branch, and removes the
zero terminal-coefficient contribution in the nonterminal branch. Root must validate
the completed branch before relying on its exact elaboration.

## Work represented in the terminal branch

- Fin.lastCases separates terminal and nonterminal depths.
- Fin.castSucc_ne_last excludes every parent edge at terminal depth, via the first
  coordinate equality. No fresh finite-index theorem is proved.
- sigma_mk_injective identifies equality of leaves with equality of their tuples.
  Fintype.sum_ite_eq selects the terminal coefficient.
- The local value is expanded only within this same proof. Fin.val_last and Nat.sub_self
  make its suffix length zero. Fintype.sum_subsingleton, generated from
  Algebra/BigOperators/Group/Finset/Basic:1004, selects Fin.elim0 directly. This is more
  precise than redoing uniqueness or rewriting an arbitrary default empty function.
- Fin.append_elim0 (Tuple/Basic:315), Function.comp_apply, Fin.cast_cast / cast_refl
  (core Fin/Lemmas:498/:494), Fin.prod_univ_zero (BigOperators/Fin:57) and mul_one
  remove the empty completion and its weight.

The other branch uses only Fin.castSucc_ne_last and existing zero-sum laws to show
that no full tuple lies at its smaller depth. Its outstanding goal is outgoing
weighted child value = the current suffix value.

## New outgoing-fiber helper

prefixOutgoing_sum.proposed.lean.inc gives the exact new helper statement. It is generic
in an arbitrary edge flow and an additive commutative monoid. At u.depth<d it sums flow
on precisely the edges obtained by snoc u.2 a, otherwise it returns zero. The `if h`
keeps the required Fin d index proof explicit; no positivity restriction is imposed.
It supports empty label types and d=0. It adds no algorithm or data structure.

Name/conclusion searches found no matching public theorem; generic sum_sigma, fiberwise
sum, singleton-sum and Fin.snocEquiv laws are its nearest reusable ingredients.
Focused raw commands/results are in prefixFlow-and-outgoing.searches.txt.
The helper has NO proof in this invocation. A separate anonymous native target is in
prefixOutgoing_sum.probe.lean.inc, without importing the named placeholder declaration.

The root has since reported that native outgoing probes are COMPLETE at
`evidence/search/prefix-outgoing/run`: exact? has exactly one expected no-proof error,
apply? has only one partial-proof warning, with no typing error or full match.
The next invocation is authorized to draft that helper proof.

## Next nonterminal flow step after the outgoing helper

Specialize the helper's flow e to value(child e)*weight(lastLabel e). At castSucc k,
its dependent branch specializes to k.isLt. Fin.snoc_last then reduces the edge label,
leaving the sum of value(snoc tau a)*weight a over a.

Reindex the current nonempty suffix through Fin.consEquiv.sum_comp and
Fintype.sum_prod_type. Fin.prod_univ_succ with cons_zero/cons_succ splits its weight.
Fin.append_right_cons transports the prefix/suffix reassociation with its exact length
cast. Compose the casts through the existing Fin.cast_cast / cast_refl equations;
proof irrelevance handles different proofs of the same length equality. Distribute
child-value multiplication with Finset.sum_mul and use commutative-semiring associativity
and commutativity to align products. No separate generic weighted-cons-sum lemma is
needed, and no finite-sum or append/cast law should be reproved.

The remaining suffix-length arithmetic must reuse the published Nat subtraction/addition
lemmas and the certified k<d; a genuinely new arithmetic helper would require its own
search/probe before being proved. No mathematical obstruction is known. The unfinished
work is a dependent finite-sum and cast formalization problem, not a source statement
change or an added hypothesis.
