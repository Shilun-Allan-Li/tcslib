<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.variance_pos_of_not_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Variance of a Nonconstant Function

**Claim.** Every nonconstant real-valued function on the finite sign cube has strictly positive variance.

**Proof.** Variance is nonnegative because it is the expectation of squares. If it were zero, the nonnegative-expectation criterion on a finite space would force every squared centered value to vanish. Each value of the function would therefore equal its mean, making the function constant, contrary to the hypothesis. Hence its variance is strictly positive.
