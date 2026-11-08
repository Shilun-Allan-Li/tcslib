<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.get_parityNextLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of the parity next layer

**Claim.** Under the canonical indexing of the layer by pairs $(g,a)$, the next-layer list entry at index $i$ is the set of child indices satisfying the stated child-group and sign-product condition.

**Proof.** The next-layer list is formed by applying the function that assigns to each index its next-node input set. Its length equals the layer size (`FABL.length_parityNextLayer`), so the cast index in the statement denotes the original index $i$. Evaluating the list at that index gives the input set for the pair corresponding to $i$, as claimed.

**Key facts.** `FABL.length_parityNextLayer`.
