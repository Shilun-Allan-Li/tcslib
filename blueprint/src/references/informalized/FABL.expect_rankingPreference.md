<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.expect_rankingPreference -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unbiased Pairwise Ranking

**Claim.** For any pairwise contest, the average sign value of that contest’s outcome over the six strict rankings of three candidates is zero.

**Proof.** Pair each ranking with its reversal, which exchanges every pairwise comparison. The reversal map is a bijection of the six rankings. For a fixed contest, the sign value under the reversed ranking is the negative of the original sign value; this is checked in each of the six ranking cases. Therefore the uniform expectation is equal to the expectation of the negative of the same function. Since expectation is linear, the latter is the negative of the former, so the expectation must be zero.
