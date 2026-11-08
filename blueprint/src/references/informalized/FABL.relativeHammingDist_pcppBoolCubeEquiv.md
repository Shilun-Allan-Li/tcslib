<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.relativeHammingDist_pcppBoolCubeEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Preserved by Binary Encoding

**Claim.** Coordinatewise encoding of Boolean strings as elements of the two-element field preserves relative Hamming distance.

**Proof.** Relative Hamming distance is the Hamming distance divided by the size of the domain, so it suffices to compare the Hamming distances. At each coordinate, the encoding is injective; consequently, two Boolean entries differ if and only if their encoded entries differ. The coordinatewise encoding therefore preserves the number of differing coordinates. Dividing these equal counts by the common domain size proves the result.
