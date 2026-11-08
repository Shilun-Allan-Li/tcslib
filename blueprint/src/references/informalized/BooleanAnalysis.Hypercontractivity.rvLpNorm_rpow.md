<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power integral formula for the norm

**Claim.** If $q>0$ and $X$ belongs to $L^q(\mu)$, then $N_q(X)^q=\int |X|^q\,d\mu$.

**Proof.** The integral formula for the extended $L^q$ norm expresses its $q$th power as the integral of the $q$th power of the function's norm. The assumptions $q>0$ and $X\in L^q(\mu)$ ensure this formula applies with exponent $q$. For real-valued $X$, its norm is $|X|$, and the real-valued norm $N_q(X)$ is the real conversion of the extended norm. The integral is nonnegative, so this conversion and the real-power laws give the stated identity.
