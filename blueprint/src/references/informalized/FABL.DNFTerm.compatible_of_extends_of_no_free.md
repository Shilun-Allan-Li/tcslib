<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.compatible_of_extends_of_no_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility under extension with no free literals

**Claim.** If a term is compatible with a restriction, none of its literal coordinates are free under that restriction, and an extension agrees wherever the original restriction is fixed, then the term remains compatible with the extension.

**Proof.** Choose $x$ witnessing compatibility with the original restriction. For each literal, the satisfaction criterion says its coordinate in the completed vector has the required sign (`DNFTerm.eval_eq_neg_one_iff`). The no-free-literals hypothesis ensures that this literal's coordinate is not free: otherwise its position would belong to the free literal positions, by `DNFTerm.mem_freeLiteralPositions_iff`, contradicting that this set is empty. Since the extension agrees with the original restriction at every nonfree coordinate, the two completed vectors have the same sign at each literal coordinate, whether that coordinate was fixed at $+1$ or at $-1$. Thus the same assignment $x$ satisfies every literal after extension, proving compatibility.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`, `FABL.DNFTerm.mem_freeLiteralPositions_iff`.
