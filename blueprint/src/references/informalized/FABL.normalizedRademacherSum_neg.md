<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.normalizedRademacherSum_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of the Normalized Sum

**Claim.** For every natural number $n$ and every sign vector $x$, negating all coordinates negates the normalized sum.

**Proof.** Expand the normalized sum as a linear form. At each coordinate, negation of the sign changes its real value to its negative, by the sign-value negation identity (`FABL.signValue_neg_hammingBall`). Each summand therefore changes to its negative, and the sum of these negated terms is the negative of the original sum.

**Key facts.** `FABL.signValue_neg_hammingBall`.
