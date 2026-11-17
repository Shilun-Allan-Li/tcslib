<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InRPStrong.toInRP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strong Recognition Implies Recognition

**Claim.** A verifier whose acceptance probability on members is at least $1-(1/2)^{(|x|+1)^d+1}$ also gives the usual $2/3$ acceptance guarantee, while preserving perfect rejection of nonmembers.

**Proof.** Take the verifier and polynomial random-bit bound witnessing strong randomized recognition. For any input $x$, the exponent $(|x|+1)^d+1$ is at least $2$, since $|x|+1\ge 1$. Thus $(1/2)^{(|x|+1)^d+1}\le (1/2)^2=1/4$, so the assumed member acceptance probability is at least $1-1/4=3/4$, which is at least $2/3$. The nonmember rejection condition and efficiency are unchanged, so the same verifier witnesses randomized recognition.
