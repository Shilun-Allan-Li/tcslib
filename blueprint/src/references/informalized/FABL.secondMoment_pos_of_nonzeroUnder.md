<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.secondMoment_pos_of_nonzeroUnder -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive second moment

**Claim.** If some point has nonzero probability mass and $X$ is nonzero there, then the second moment of $X$ is positive.

**Proof.** Apply the positivity principle for finite expectations (`FABL.pmfExpectation_pos_of_exists`) to the function $x\mapsto X(x)^2$. Its values are nonnegative because every real square is nonnegative. By hypothesis there is a point with nonzero mass where $X(x)\ne 0$; the square is then strictly positive there. These are precisely the conditions needed for that principle, so the second moment is positive.

**Key facts.** `FABL.pmfExpectation_pos_of_exists`.
