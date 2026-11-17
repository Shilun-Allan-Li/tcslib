<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.get_parityBottomNextLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of the normalized parity next layer

**Claim.** Under the canonical indexing of the layer by pairs $(g,a)$, the normalized next-layer list entry at index $i$ is the set of child indices satisfying the stated child-group and normalized-sign-product condition.

**Proof.** The list is defined by applying the function that sends each layer index to its corresponding next-node input set. Its length is the layer size (`FABL.length_parityBottomNextLayer`), so the cast index used in the statement represents the same index $i$. Unfolding the list's function-based construction at that index yields exactly the next-node input set formed from the pair associated to $i$.

**Key facts.** `FABL.length_parityBottomNextLayer`.
