<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.card_nonzero_positionBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of Nonzero Bit Assignments

**Claim.** For a finite set $S$ of positions, the number of nonzero functions from $S$ to the two-element field is $2^{|S|}-1$.

**Proof.** Among all functions from $S$ to the two-element field, exactly one is the zero function. The total number of functions is $2^{|S|}$, since each position admits two independent choices. Removing the unique zero function leaves $2^{|S|}-1$ nonzero functions.
