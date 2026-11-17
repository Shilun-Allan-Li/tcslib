<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.blockCode_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits of the block code

**Claim.** For each selected literal position, the block code bit at its embedded position equals the corresponding relative bit.

**Proof.** Fix a selected position $j$. Its image under the position embedding belongs to the image of the selected set, since $j$ itself witnesses membership in that image. Thus the block code uses the value assigned at this image position, rather than its default value zero. The chosen preimage of the embedded position must be $j$: the position embedding is injective, and the chosen preimage has the same image. Consequently the assigned value is exactly the relative bit at $j$.
