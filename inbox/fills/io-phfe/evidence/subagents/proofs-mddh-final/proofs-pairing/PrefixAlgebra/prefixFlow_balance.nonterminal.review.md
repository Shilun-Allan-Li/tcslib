# prefixFlow_balance: complete nonterminal branch candidate

prefixFlow_balance.nonterminal.lean.inc replaces only the existing `cast k` branch.
It assumes the original proof's local value definition, k : Fin d and tau : Fin k.val → I.
It has 64 lines, maximum width 81, no admission, no new public declaration, and no extra
`by` block. Its single tactic-goal placeholder `?_` is immediately discharged by the
following bullet, so it is not an unfinished hole. The frozen theorem header and prose
are not touched. The terminal branch and diagnostic partial file are not replaced.

The diagnostic partial was not written: the before/after hash during draft generation
was identical (96e7c8d9f19ddf2c3b102c124895258c353836f826f678542eefa281f1b5c24c).
The lead may of course continue changing that diagnostic file independently.
The agent ran no Lean/lake/Git/live edit or proof checker; native validation is pending.

## Dependencies and exact route

The only new theorem dependency is prefixOutgoing_sum, now reported native PASS by the
lead after its completed exact?/apply? searches. The fragment uses the lead's explicit
Sigma-node guard for dif_pos to prevent the inference problem observed in its proof.
It is independent of prefixIncoming_sum, backward_action and every security admission.
No additional helper statement or proof is introduced.

Let r = d-(k.val+1). The equality r+1 = d-k.val is composed from the exact existing
Nat.sub_succ (core Init/Data/Nat/Basic:281), congrArg Nat.succ, and
Nat.succ_pred_eq_of_pos (:900) applied to Nat.sub_pos_of_lt (:1087). The parent/child
full-tuple casts are Nat.add_sub_of_le at the certified k≤d and k+1≤d bounds. No new
natural-subtraction lemma or omega calculation is supplied.

The suffix equivalence is Fin.consEquiv (Data/Fin/Tuple/Basic:169), followed by
Equiv.arrowCongr (Logic/Equiv/Defs:450) for finCongr of the length equality
(Data/Fin/SuccPred:134). This keeps both dependent suffix index types fixed, avoiding
the ill-typed dependent motives caused by rewriting subtraction under a tuple cast.
Equiv.sum_comp (generated in Group/Finset/Defs:712) reindexes the parent suffix sum;
Fintype.sum_prod_type (Data/Fintype/BigOperators:253) separates first label and tail.
Finset.sum_mul (Algebra/BigOperators/Ring/Finset:49) expands the child value times its
last-label weight. The two remaining sums now have exactly the same index types.

For each first label and tail, Equiv.prod_comp (Group/Finset/Defs:712) for finCongr of
the reverse length equality transports the label product. Fin.prod_univ_succ
(BigOperators/Fin:72) and Fin.cons_zero/cons_succ (Tuple/Basic:118/:115) split it into
the first-label factor times the tail product. No product recurrence or reindexing law
is reproved.

The local coefficient-function equality uses precisely:

- Fin.append_cast_right, Tuple/Basic:368, to absorb the suffix's length cast;
- Fin.append_right_cons, Tuple/Basic:658, to reassociate prefix and first tail label;
- Function.comp_apply and Fin.cast_cast, core Fin/Lemmas:498, to compose the casts.

Both final casts prove the same equality d=(k.val+1)+r, so proof irrelevance makes them
definitionally identical. The local equality is only this composition of published
append/cast identities; no new generic append or cast theorem is added. A final
mul_right_comm followed by mul_assoc aligns the coefficient/weight products using the
existing commutative-semiring structure.

The nearest TCSlib use of consEquiv.trans(arrowCongr(finCongr ...)) is the public
tapeSplit in ZeroKnowledge/GraphIsomorphism/Proofs:764-765. It is specialized to Bool and
the length equality c+1=1+c, so it does not supply this arbitrary-label, subtraction-
length equivalence. The fragment uses the underlying public Mathlib constructors;
no proven material from that consumer is copied or imported.

## Rule 10, imports, and total dimensions

Every simp/rw argument is a theorem, reader or local proved equality. The change steps
reduce only the current proof's local value and suffixEquiv plus core/Mathlib tuple,
function and equivalence wrappers. No foreign TCSlib definition is read. No definition
is named in simp/rw/unfold; no new finite-sum, finite-product, or tuple host is recreated.
The existing PrefixAlgebra imports already expose every used public item; no new root
is needed. The fragment handles r=0 and empty I, adds no positivity/inhabitedness
hypothesis, and uses only the k<d certificate already present in this branch. The d=0
case remains the original terminal branch. No mathematical obstruction was found.
