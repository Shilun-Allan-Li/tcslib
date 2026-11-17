<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.blockCode_termPositions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block code recovers term positions

**Claim.** The literal positions corresponding to the block code's positions are exactly the selected set of literal positions.

**Proof.** The block code is the position-and-bit construction on the image of the selected set under the position embedding. The result for recovering term positions from such an image states that taking the preimage through the embedding returns the original selected set (`FABL.SwitchingBlockCode.termPositions_of_mapped`). Applying it to the block code gives the claim.

**Key facts.** `FABL.SwitchingBlockCode.termPositions_of_mapped`.
