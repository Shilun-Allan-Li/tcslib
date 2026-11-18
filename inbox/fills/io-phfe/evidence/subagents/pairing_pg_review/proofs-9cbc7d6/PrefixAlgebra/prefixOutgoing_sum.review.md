# prefixOutgoing_sum proof candidate

Exactly one authorized theorem proof is supplied. It preserves the current live header
byte for byte and the opening statement prose. Its sketch is refreshed to describe the
single global reindexing rather than a repeated depth-sum calculation. The fragment has
61 lines, maximum width 80, one tactic block and no admission or new public helper.
The agent ran no Lean, lake, Git, live edit or proof checker; native validation is pending.

## Required native reuse searches

The lead completed the exact?/apply? probes, and the agent read their raw logs:

- evidence/search/prefix-outgoing/run/mods/.lake_io-phfe-probes_PrefixOutgoingExact.log;
- evidence/search/prefix-outgoing/run/mods/.lake_io-phfe-probes_PrefixOutgoingApply.log.

Exact? has precisely one expected no-proof error; apply? has only a partial dependent-if
suggestion and its one admission warning. No typing error or complete public match was
found. Focused source searches are saved in prefixOutgoing_sum.searches.txt.

## Proof route and exact reuse

The local edgeEquiv is composed entirely from public Mathlib equivalences:

- Equiv.sigmaProdDistrib, Logic/Equiv/Prod:416, maps (predecessor prefix,last label)
  into a sigma of (initial tuple,last label) products;
- Equiv.prodComm, followed by Fin.snocEquiv (Data/Fin/Tuple/Basic:701), puts the pair in
  the (last label,initial tuple) order required by the snoc equivalence;
- Equiv.sigmaCongrRight, Logic/Equiv/Defs:627, applies these existing fiber equivalences.

No new bijection or inverse proofs are constructed. Equiv.sum_comp (generated at
Algebra/BigOperators/Group/Finset/Defs:712) reindexes the whole finite edge sum, and
Fintype.sum_prod_type_right (generated in Data/Fintype/BigOperators:265-268) makes the
last label the outer index. A change step computes only this local composition of
Mathlib equivalences. Fin.init_snoc (Tuple/Basic:500) identifies the resulting parent.
No Mathlib definition is passed to simp/rw/unfold.

The local prefixEmbed is Sigma.map Fin.castSucc with identity tuple maps.
Function.Injective.sigma_map (Data/Sigma/Basic:116), Fin.castSucc_injective
(Data/Fin/SuccPred:91) and identity injectivity supply its injection directly.
The proof does not reproduce generic sigma-map injectivity.

Fin.lastCases splits the queried node depth. At maximal depth,
Fin.castSucc_ne_last (SuccPred:196) excludes every embedded prefix via its first
coordinate. The dependent branch is false by Nat.lt_irrefl; existing zero-sum laws
finish. At a smaller depth k, k.isLt selects the positive dependent branch. The same
node tuple at depth k is the predecessor prefix q0. The existing injection's eq_iff
and Fintype.sum_ite_eq' (generated at Group/Finset/Piecewise:292-295) evaluate the inner
sum at q0, leaving precisely the displayed last-label sum.

All supplied facts are reused, including the finite sum reindexing and supported sum.
No TCSlib definition or other new helper admission is consumed. The proof is independent
of prefixIncoming_sum and prefixFlow_balance. It works for d=0, empty I and arbitrary
additive commutative monoids without new inhabitedness or positivity assumptions.

The nearest existing TCSlib consumers of prodComm.trans snocEquiv are local proof lets
in Composability/SequentialZK/Soundness:112 and Encryption/PublicKey/Regev/Experiments:262.
They expose no public equivalence theorem to import; the present proof uses the underlying
public Mathlib constructions directly. No proved material from those consumers is copied.

## Imports and size

No new import is necessary beyond the PrefixAlgebra skeleton. A read-only import walk
found Logic.Equiv.Prod through Algebra.BigOperators.Fin → Algebra.BigOperators.Ring.Finset
→ Algebra.BigOperators.Ring.Multiset → Algebra.BigOperators.Group.Multiset.Basic
→ Algebra.Group.Prod → Logic.Equiv.Prod. The sigma injection and finite-tuple imports
were verified in the previous incoming proof notes. This remains source import evidence,
not a substitute for a native proof check. The candidate adds about 44 proof lines to
the module, well inside the requested 1000-line bound. No mathematical obstruction found.
