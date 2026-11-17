<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityFirstLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Parity Layer Evaluation

**Claim.** At each layer index, the AND gate applied to the corresponding parity-block minterm has the same value as the specified bottom-layer value.

**Proof.** Fix an index and use the layer equivalence to write it as a group together with a block assignment. By the first-layer construction, the indexed list entry is the minterm for that group and assignment. The minterm evaluation characterization says it evaluates to $-1$ exactly when the normalized assignment equals the block value (`FABL.parityBlockMinterm_eval_eq_neg_one_iff`). The level-$0$ parity-tree assignment is that same block value (`FABL.parityTreeAssignment_zero_eq_blockValue`), so the minterm evaluates to $-1$ exactly when the normalized assignment matches the level-$0$ assignment. The bottom-layer value is defined to be the exact AND-node value for this match: it is $-1$ in the matching case and $1$ otherwise. In the latter case, the minterm cannot equal $-1$ by the characterization; since its output is a sign and hence is either $1$ or $-1$, it must be $1$. Thus both outputs agree in either case. The equality identifying the list entry uses the first-layer length formula (`FABL.length_parityFirstLayer`) to reconcile the list index with the layer index.

**Key facts.** `FABL.length_parityFirstLayer`, `FABL.parityBlockMinterm_eval_eq_neg_one_iff`, `FABL.parityTreeAssignment_zero_eq_blockValue`.
