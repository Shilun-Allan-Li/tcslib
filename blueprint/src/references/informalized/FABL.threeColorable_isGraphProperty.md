<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.threeColorable_isGraphProperty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Colorability Is a Graph Property

**Claim.** The Boolean function indicating whether an encoded graph is 3-colorable is invariant under every permutation of the vertices, and hence is a graph property.

**Proof.** Fix a vertex permutation and an encoded graph. The colorability-preservation result ( `encodedGraphColorable_permute_iff`) states that the permuted graph is 3-colorable exactly when the original graph is 3-colorable. Therefore their Boolean indicators agree, which is precisely invariance under vertex permutations.

**Key facts.** `FABL.encodedGraphColorable_permute_iff`.
