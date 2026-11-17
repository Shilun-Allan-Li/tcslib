<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.mean_sq_binaryFunctionOnSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment Under Sign Encoding

**Claim.** The mean of the square of the function on the sign cube obtained by decoding each sign as a bit equals the mean of $f^2$ on the binary cube.

**Proof.** The binary-to-sign encoding is an equivalence of the two finite cubes, and its coordinatewise extension is therefore a bijection of the full cubes. Reindexing the uniform expectation along this equivalence leaves the mean unchanged. At each corresponding point, the definition of the encoded function turns its value back into the value of $f$ at the original binary point, so their squares agree. Hence the two means are equal.
