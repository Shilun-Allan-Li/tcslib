<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.relativeBit_satisfyingAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative bits of a satisfying assignment

**Claim.** For every literal position in a DNF term, the satisfying assignment’s coordinate plus the binary value corresponding to that literal’s required sign is zero in $\mathbb{F}_2$.

**Proof.** At position $j$, the literal’s coordinate belongs to the term’s support. By the fact that every listed literal’s index lies in the support (`FABL.DNFTerm.mem_support_of_mem_literals`), the satisfying assignment at that coordinate is the binary value corresponding to the required sign at that coordinate. The identification of the support literal with the literal at position $j$ (`FABL.DNFTerm.satisfyingAssignment_literal`) therefore rewrites the relative bit as a binary value added to itself. In characteristic two, every element added to itself is zero.

**Key facts.** `FABL.DNFTerm.satisfyingAssignment_literal`.
