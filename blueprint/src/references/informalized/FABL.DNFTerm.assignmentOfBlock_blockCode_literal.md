<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.assignmentOfBlock_blockCode_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment Recovered at Selected Literals

**Claim.** For a term of width at most $w$, the assignment constructed from its block code agrees with the original assignment at the coordinate of every selected literal position.

**Proof.** At a literal’s coordinate, the assignment constructed from a block code is the block bit at that literal’s embedded position plus the inverse sign encoding of its required sign (`FABL.DNFTerm.assignmentOfBlock_literal`). For a selected position, the corresponding bit of the term’s block code is the original input bit plus that same inverse sign encoding (`FABL.DNFTerm.blockCode_bits`). Substitution leaves the original bit plus the sign adjustment twice. Since addition in $\mathbb{F}_2$ has characteristic two, the two copies cancel, leaving exactly the original input bit.

**Key facts.** `FABL.DNFTerm.assignmentOfBlock_literal`, `FABL.DNFTerm.blockCode_bits`.
