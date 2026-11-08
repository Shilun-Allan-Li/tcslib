<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_finished -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorption of the Finished State

**Claim.** For every bit string $x$ and all $k,j,p\in\mathbb{N}$, running $k$ rounds from the state with fresh cursor $j$, consumed length $p$, and finished phase returns that same state and emits the empty string.

**Proof.** Induct on the number of rounds. With zero rounds, the run returns its initial state and emits nothing. For the successor case, the finished-phase branch of a single round leaves the state unchanged and emits the empty string. The induction hypothesis then says the remaining rounds also leave this state unchanged and emit nothing; concatenating the two empty outputs proves the claim.
