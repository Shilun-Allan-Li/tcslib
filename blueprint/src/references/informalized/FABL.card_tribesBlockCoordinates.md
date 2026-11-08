<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.card_tribesBlockCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of a Block

**Claim.** The set of positions in any one block has cardinality $w$.

**Proof.** The block coordinates are the images of all $w$ positions in `Fin w` under the embedding that places them in the chosen block. Since the embedding is injective, the image has the same cardinality as its domain, which is $w$.
