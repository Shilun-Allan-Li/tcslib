<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.sum_signedSum_flipCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Flip Sum Identity

**Claim.** Summing the signed vector sums over all points obtained by flipping one coordinate gives $(n-2)$ times the signed vector sum at the original point.

**Proof.** Fix a coordinate $i$. The signed vector sum after flipping $i$ equals the original signed vector sum minus twice the contribution from coordinate $i$ (`signedSum_flipCoordinate`). Sum this identity over all $i$. The original sum occurs once for each of the $n$ coordinates, while the correction terms sum to twice the original signed vector sum, since they collect each coordinate's contribution once. Subtracting yields $(n-2)$ times the original sum.

**Key facts.** `FABL.signedSum_flipCoordinate`.
