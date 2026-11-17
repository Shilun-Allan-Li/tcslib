<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityNextNodeInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Next parity node evaluation

**Claim.** Applying the gate dual to the level-$q+1$ node values on the specified input set gives the exact dual-gate node value, matching precisely when $a$ is the assignment of child-block products.

**Proof.** Split on the gate. For an AND gate, first show that the input set contains a node with value $-1$ exactly when $a$ differs from the assignment of child-block products. If such a node is present, membership identifies a child $j$, its group is the $j$th child group, and its block product differs from $a(j)$. Since an AND node has value $-1$ exactly when its block equals the actual block (`parityLayerValues_and_eq_neg_one_iff`), that product must equal the actual product at child $j$; this forces a mismatch with the proposed assignment. Conversely, if the assignments differ, choose a coordinate $j$ where they differ (`exists_apply_ne_of_ne`). Take the level node whose group is child $j$ and whose block is the actual block there. Its product differs from $a(j)$, so it belongs to the input set, and its AND value is $-1$. Thus the dual OR returns $-1$ precisely in the mismatch case, which is the exact dual-gate value.

For an OR gate, show instead that every node in the input set has value $-1$ exactly when the assignments match. If they match, membership supplies a child coordinate whose block product differs from $a(j)$; the node's block therefore cannot equal the actual block, so its OR value is $-1`parityLayerValues_or_eq_neg_one_iff`. Conversely, if the assignments do not match, choose a differing coordinate and construct the node with that child group and its actual block. It belongs to the input set, while its OR value is not $-1$, disproving the universal condition. The dual AND returns $-1$ exactly when all inputs have value $-1$. In both gate cases, evaluating this condition gives the stated exact node value.

**Key facts.** `FABL.mem_parityNextNodeInputs_iff`, `FABL.parityLayerValues_and_eq_neg_one_iff`, `FABL.exists_apply_ne_of_ne`, `FABL.parityLayerValues_or_eq_neg_one_iff`.
