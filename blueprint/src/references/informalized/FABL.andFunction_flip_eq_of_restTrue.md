<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.andFunction_flip_eq_of_restTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipped AND on a nearly negative block

**Claim.** If every coordinate in the chosen block except the selected coordinate is $-1$, then flipping that coordinate makes the block AND equal to $-x_i$.

**Proof.** After flipping coordinate $i$, every other entry of the chosen block remains unchanged: this is the coordinate-preservation fact `FABL.inputBlock_flipCoordinate_of_ne_offset`. Thus the flipped input still satisfies the hypothesis that all entries except the selected one are $-1$. Apply the result that the block AND equals its selected entry (`FABL.andFunction_eq_of_restTrue`) to this flipped input. Its selected entry is $-x_i$ by the definition of the coordinate flip, giving the claim.

**Key facts.** `FABL.inputBlock_flipCoordinate_of_ne_offset`, `FABL.andFunction_eq_of_restTrue`.
