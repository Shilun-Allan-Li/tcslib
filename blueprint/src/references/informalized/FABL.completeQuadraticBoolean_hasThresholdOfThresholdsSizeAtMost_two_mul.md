<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBoolean_hasThresholdOfThresholdsSizeAtMost_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold-of-thresholds size bound

**Claim.** The complete quadratic Boolean function on $n$ sign coordinates can be expressed as a threshold of at most $2n$ linear threshold functions.

**Proof.** The complete quadratic Boolean function is symmetric under coordinate permutations ( `completeQuadraticBoolean_isSymmetric`). Apply the theorem that any symmetric Boolean function is a real sum of linear threshold functions of size at most $2n$ ( `symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul`) to obtain a representation of some size $t\le 2n$. A real sum of linear threshold functions of size $t$ yields a threshold of threshold functions of the same size ( `isThresholdOfThresholds_of_isRealSumOfLinearThresholds`). Together these give the required bound.

**Key facts.** `FABL.completeQuadraticBoolean_isSymmetric`, `FABL.symmetric_hasRealSumOfLinearThresholdsSizeAtMost_two_mul`, `FABL.isThresholdOfThresholds_of_isRealSumOfLinearThresholds`.
