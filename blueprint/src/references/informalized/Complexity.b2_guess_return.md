<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_guess_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return from Guessing

**Claim.** If the scheduler configuration is halted, one host step from its guessing-phase configuration enters the assembly phase, with buffer $xu$ and assembly head at $|xu|-1$.

**Proof.** Because $c$ has no active state, the guessing-phase configuration places the host in the branch whose scheduler state is halted. The host transition for this branch moves the assembly head one cell to the left, enters the assembly state, and leaves the input head unchanged. The scheduler tapes and heads are retained; the host's assembly tape already stores $xu$ with its head at $|xu|$. The verifier tapes remain blank. These components are precisely those of the stated assembly configuration. The input-head equality uses the fact that a zero move leaves its position fixed (`moveInputPos_zero`).

**Key facts.** `Turing.moveInputPos_zero`.
