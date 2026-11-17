<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.coordinateLocalCorrection_correctProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Correction Success from Closeness

**Claim.** If $f$ is within relative Hamming distance $\delta$ of the dictator at index $i$, then the local correction on the truth table for coordinate $j$ returns the corresponding dictator value with probability at least $1-2\delta$.

**Proof.** The dictator at $i$ is the parity function associated with the singleton set $\{i\}$. Thus the assumed closeness lets us apply the subset local-correction guarantee to the singleton, obtaining success probability at least $1-2\delta$ on the indicator-sign input for the true indices of coordinate $j$. The indicator-sign vector for that index set equals the coordinate truth table (`FABL.subsetIndicatorSign_coordinateTrueIndexSet`). The parity value on this vector is the sign encoding of the $j$th bit of index $i$, which is the target in the claim. Substituting these identifications gives the stated probability bound.

**Key facts.** `FABL.subsetLocalCorrection_correctProbability_ge`, `FABL.subsetIndicatorSign_coordinateTrueIndexSet`.
