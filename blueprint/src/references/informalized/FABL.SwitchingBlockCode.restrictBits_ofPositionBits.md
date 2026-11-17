<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.restrictBits_ofPositionBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction After Position-Bit Construction

**Claim.** For a finite position set $S$ and an assignment of bits on $S$, restricting the code constructed from them to its designated positions recovers the given assignment.

**Proof.** The constructed code has designated set $S$. At any position in $S$, its bit is defined to be the assigned bit at that position. Therefore the restricted function agrees with the original assignment at every input, and the functions are equal.
