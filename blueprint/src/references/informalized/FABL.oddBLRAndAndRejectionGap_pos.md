<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLRAndAndRejectionGap_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Rejection Gap

**Claim.** For every natural number $n$, the minimum rejection probability of the uniform mixture of the odd BLR equation test and the sign-AND test, over all non-dictator sign-valued functions on the $n$-dimensional sign cube, is strictly positive.

**Proof.** The minimum is attained by some rejection value in the finite set defining the gap. Thus there is a non-dictator function $f$ whose rejection probability equals this minimum. Its acceptance probability is at most $1$ (`NonadaptiveFunctionTester.acceptanceProbability_le_one`). It cannot equal $1$, since perfect acceptance by the mixture characterizes dictators (`oddBLRAndAndFunctionTester_acceptanceProbability_eq_one_iff`), contrary to the choice of $f$. Hence its acceptance probability is strictly less than $1$, so its rejection probability, and therefore the minimum rejection gap, is strictly positive.

**Key facts.** `FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one`, `FABL.oddBLRAndAndFunctionTester_acceptanceProbability_eq_one_iff`.
