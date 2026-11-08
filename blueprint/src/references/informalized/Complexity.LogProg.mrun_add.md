<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.mrun_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Run Durations

**Claim.** For any initial configuration and natural numbers $s,t$, running the memory-augmented program for $s+t$ steps agrees with running it for $s$ steps and then for $t$ more steps.

**Proof.** A run of length $n$ is the $n$-fold iterate of the one-step transition function. The iterate law says that iterating a function $s+t$ times is the same as first iterating it $s$ times and then iterating it $t$ times. Since addition is commutative, the standard iterate law, which may place these two iteration counts in the opposite order, gives the stated identity after swapping $s$ and $t$.
