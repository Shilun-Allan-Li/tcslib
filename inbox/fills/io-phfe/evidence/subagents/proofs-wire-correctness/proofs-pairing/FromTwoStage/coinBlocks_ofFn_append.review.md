# coinBlocks_ofFn_append proof candidate

The declaration header is byte-for-byte the native-searched header in
RunProbeHeaders.lean. The fragment supplies the new logical helper's factual
docstring and proof sketch; its body has one tactic block and no admissions or
new helper declaration. No Lean, lake, Git, live edit or checker was run. Native
validation of this body remains pending.

Root authorized this helper after isolated source-prefix probes excluding the
future endpoint and advantage theorems: all three proposed headers typed cleanly;
exact? had three expected no-proof errors, while apply? offered only partial
Prod.ext for this target and no relevant lemmas for the real/ideal targets.
Raw results are in evidence/search/committed-run-bridges/run. Thus this proof
cannot acquire an accidental dependency on the future endpoint theorem.

The proof follows the only applicable public reduction: Prod.ext reduces the
pair equality to two function equalities, and firstCoins_eq/secondCoins_eq expose
their coordinates. List.length_ofFn gives the two original machine coin lengths;
its local names h1/h2 are proof equalities, not new helper declarations. No
NUPPT.coinLen definition or Coins abbreviation is unfolded by a rewrite tactic.

For the first block, i.isLt transported by h1.symm proves that i lies inside
the first word. List.getD_append selects it, List.getD_eq_getElem reads its known
in-range coordinate and List.getElem_ofFn returns r1 i. For the second block,
le_trans (le_of_eq h1) (Nat.le_add_right _ _) proves the shifted position lies
after the first word. List.getD_append_right selects the second word; h1 and
Nat.add_sub_cancel_left remove its offset. The same in-range/ofFn laws return
r2 i. Proof irrelevance identifies the resulting Fin index with i.

No generic append, list-coordinate, finite-function or sampler result is
re-proved, and no local Fintype or coin generator is constructed. Empty tape
blocks are covered vacuously by function extensionality. No mathematical
obstruction was found. Root should natively check inference of the explicit
getD boundary arguments and the final List.getElem_ofFn rewrites.
