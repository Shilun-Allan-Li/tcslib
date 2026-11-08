<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.assignmentOfBlock_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment at a Literal Coordinate

**Claim.** At the coordinate of any literal in a term of width at most $w$, the assignment constructed from a block code equals the bit at that literal’s embedded position plus the inverse sign encoding of its required sign.

**Proof.** A literal in the term belongs to its support (`FABL.DNFTerm.mem_support_of_mem_literals`), so the assignment at its coordinate uses the support-based branch of its definition. The position associated to that support coordinate is precisely the literal’s position in the list (`FABL.DNFTerm.positionOfSupport_literal`). The literal selected from the support at this coordinate is the given literal (`FABL.DNFTerm.literalAt_eq`), so its required sign is the one used in the assignment formula. Substituting these identifications gives the stated block bit and sign adjustment.

**Key facts.** `FABL.DNFTerm.mem_support_of_mem_literals`, `FABL.DNFTerm.positionOfSupport_literal`, `FABL.DNFTerm.literalAt_eq`.
