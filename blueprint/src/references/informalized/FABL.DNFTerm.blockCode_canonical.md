<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.blockCode_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical block code

**Claim.** The block code is canonical: every bit outside its selected positions is zero.

**Proof.** The block code is constructed by applying the position-and-bit construction to the image of the selected literal positions. The general fact that this construction is canonical says that all bits outside the supplied position set are zero (`FABL.SwitchingBlockCode.canonical_ofPositionBits`). Applying it to this image set and its assigned bits gives the result.

**Key facts.** `FABL.SwitchingBlockCode.canonical_ofPositionBits`.
