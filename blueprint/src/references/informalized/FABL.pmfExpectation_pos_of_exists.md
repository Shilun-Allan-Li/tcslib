<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfExpectation_pos_of_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of an Expectation

**Claim.** If $f$ is nonnegative everywhere and is strictly positive at some point having nonzero probability mass, then its expectation is strictly positive.

**Proof.** Choose a point $x$ with nonzero mass and $f(x)>0$. Every summand in the finite expectation is nonnegative, since probability masses and all values of $f$ are nonnegative. The summand at $x$ is strictly positive: nonzero mass has strictly positive real value, and it is multiplied by $f(x)>0$. Hence the whole sum is strictly positive.
