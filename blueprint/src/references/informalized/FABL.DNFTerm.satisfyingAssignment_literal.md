<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.satisfyingAssignment_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The satisfying assignment meets every literal

**Claim.** At each literal position, the satisfying assignment evaluated at that literal’s coordinate equals the binary value corresponding to its required sign.

**Proof.** The literal at position $j$ occurs in the term’s list. Its index therefore belongs to the term’s support (`FABL.DNFTerm.mem_support_of_mem_literals`), so the satisfying assignment uses the support branch of its definition at that coordinate. The value there is the binary encoding inverse applied to the required sign of the support literal. The support-literal identification theorem says that the literal selected at this coordinate is exactly the literal at position $j$ (`FABL.DNFTerm.literalAt_eq`); substituting this identity gives the claimed value.

**Key facts.** `FABL.DNFTerm.mem_support_of_mem_literals`, `FABL.DNFTerm.literalAt_eq`.
