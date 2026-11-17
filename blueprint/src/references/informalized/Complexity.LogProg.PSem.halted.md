<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Halted Configuration

**Claim.** A halted configuration whose answer is $b$ has probabilistic semantics with probability $1$ if $b$ is true and $0$ if $b$ is false, for any guard.

**Proof.** The halted configuration is terminating immediately, by the halted case of the termination definition. Running it for any sequence of choice bits leaves the configuration, and hence its answer, unchanged (Complexity.LogProg.narun_halted). Therefore every random choice sequence returns the same Boolean $b$. The probability of this constant outcome is $1$, and that of the other outcome is $0$ (Randomized.randProb_const). Considering the two possibilities for $b$ gives the claimed parameter and the corresponding false-output probability $1-p$.

**Key facts.** `Complexity.LogProg.narun_halted`, `Randomized.randProb_const`.
