<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.eval_parityOutputInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity output evaluation

**Claim.** Applying the gate dual to the level-zero node values on the specified output input set gives the product of the signs in the actual block at the unique index in $	ext{Fin}(r^0)$.

**Proof.** Split on the gate. For an AND gate, prove that the output input set contains a node valued $-1$ exactly when the actual block product is $-1$. Membership says the node's block product is $-1`, while an AND node is valued $-1$ exactly when its block is the actual block (`parityLayerValues_and_eq_neg_one_iff`). Since $	ext{Fin}(r^0)$ has just one element, the node's group index is the unique index, giving the claimed product. Conversely, choose the level-zero node corresponding under the layer equivalence to that unique index and the actual block; it belongs to the input set and has value $-1` when the actual block product is $-1` (`mem_parityOutputInputs_and_iff`). Therefore the dual OR evaluates to $-1$ exactly when the product is $-1$. For an OR gate, prove that all nodes in the input set have value $-1$ exactly when the actual block product is $-1`. If the product is $-1`, membership says each such node's block product is not $-1`; hence its block cannot be the actual block, and its OR value is $-1` (`parityLayerValues_or_eq_neg_one_iff`). If the actual product is $1`, the node corresponding to the unique index and actual block belongs to the input set but has value $1`, so the universal condition fails. The dual AND thus returns $-1$ precisely when the product is $-1`. Finally, signs have only the two values $1$ and $-1$, so in either case the gate result equals the actual block product.

**Key facts.** `FABL.mem_parityOutputInputs_and_iff`, `FABL.parityLayerValues_and_eq_neg_one_iff`, `FABL.mem_parityOutputInputs_or_iff`, `FABL.parityLayerValues_or_eq_neg_one_iff`.
