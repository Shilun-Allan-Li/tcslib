<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.variance_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Under Sign Reversal

**Claim.** For a real-valued function on the sign cube, negating the function leaves its variance unchanged.

**Proof.** The mean of the negated function is the negative of the original mean, since expectation is linear. Consequently, at each point, the centered value of the negated function is the negative of the original centered value. Their squares agree pointwise, and taking expectations proves the equality.
