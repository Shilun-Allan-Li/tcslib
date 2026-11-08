<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.termCoordinates_blockCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Term coordinates of its block code

**Claim.** For a term of width at most $w$, the list of coordinates selected by its block code from a set of literal positions is exactly the list of coordinates of the literals at those positions.

**Proof.** By definition, the block code’s term coordinates are obtained by taking the literal positions whose embeddings lie among the code’s selected positions, then mapping those positions to their literal coordinates. The code’s selected positions are precisely the embedded images of the given set (`FABL.DNFTerm.blockCode_positions`). Every literal position is less than $w$ because the term has width at most $w$. Since the position embedding preserves the position index, an embedded position belongs to that image exactly when the original position belongs to the given set. Thus the selected positions are exactly the original set, and mapping them to literal coordinates gives the stated list.

**Key facts.** `FABL.DNFTerm.blockCode_positions`.
