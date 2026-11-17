<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.succ_of_nhalts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Length of a Halting Run

**Claim.** If every choice sequence of length $N$ from an active configuration leads to a halted state, then $N$ is positive.

**Proof.** If $N=0$, the empty choice sequence has length $N$, and running it leaves the initial configuration unchanged. Its state is active, so it is not halted, contradicting the assumed halting property for every sequence of length $N$. Therefore $N$ cannot be zero; hence it is positive.
