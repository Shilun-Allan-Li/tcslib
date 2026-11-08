<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.distanceToProperty_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimal Distance to a Property

**Claim.** For any function $g$ satisfying the nonempty property $P$, the distance from $f$ to $P$ is at most the normalized Hamming distance from $f$ to $g$.

**Proof.** By definition, the distance to $P$ is the normalized Hamming distance from $f$ to a closest function in $P$. The closest-function minimality result says this distance is no greater than the distance to any function satisfying $P$ (`closestInProperty_minimal`). Applying it to $g$ proves the claim.

**Key facts.** `FABL.closestInProperty_minimal`.
