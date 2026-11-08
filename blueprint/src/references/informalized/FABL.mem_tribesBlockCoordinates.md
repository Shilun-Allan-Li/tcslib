<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mem_tribesBlockCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a Tribe Block

**Claim.** For a block index $i$ and within-block position $o$, the position corresponding to $(i,o)$ belongs to the coordinates of block $i$.

**Proof.** The coordinates of block $i$ are the image of all within-block positions under the embedding that sends $o$ to the position corresponding to $(i,o)$. In particular, the image of this specific $o$ belongs to that image set.
