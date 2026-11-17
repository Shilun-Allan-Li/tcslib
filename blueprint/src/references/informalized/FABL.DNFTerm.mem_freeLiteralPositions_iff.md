<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.mem_freeLiteralPositions_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Literal Positions

**Claim.** A valid literal position belongs to the set of free literal positions exactly when the corresponding literal's coordinate is assigned the free restriction.

**Proof.** The set of free literal positions is the set of all valid positions filtered by the condition that the restriction at the position's literal coordinate is free. Thus a valid position belongs to that set precisely when it satisfies this filtering condition.
