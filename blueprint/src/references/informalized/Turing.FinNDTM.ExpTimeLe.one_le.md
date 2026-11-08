<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.ExpTimeLe.one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on the Time Sum

**Claim.** If every partial sum of the probabilities of being unhalted is bounded above by $B$, then $1\le B$.

**Proof.** Use the assumed bound with $K=1$. The sum over times $t$ in the range from $0$ to $1$ consists only of the time-zero term. At time zero, the run has made no choices and is at its initial, nonhalting configuration, so the probability of being unhalted is $1$ (\texttt{notHaltedProb_haltRun_zero}). Thus the sum is $1$, and the assumed upper bound gives $1\le B$.

**Key facts.** `Turing.FinNDTM.notHaltedProb_haltRun_zero`.
