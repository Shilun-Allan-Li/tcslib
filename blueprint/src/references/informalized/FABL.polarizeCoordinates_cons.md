<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.polarizeCoordinates_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization Along a List

**Claim.** For a Boolean function $f$, a coordinate $i$, and a list of coordinates $L$, polarizing along the list beginning with $i$ is the same as first polarizing at $i$ and then polarizing along $L$.

**Proof.** By the recursive definition of polarization along a list, processing a list with first entry $i$ applies coordinate polarization at $i$ and then processes the remaining list. Thus both sides are the same function.
