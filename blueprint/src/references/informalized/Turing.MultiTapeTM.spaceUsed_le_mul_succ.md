<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.spaceUsed_le_mul_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Bound on Space Use

**Claim.** The total number of distinct work-tape cells visited from the initial configuration through step $t$ is at most $k(t+1)$.

**Proof.** There are $k$ work tapes. On any fixed tape, the head has one position at each of the $t+1$ times from $0$ through $t$, so the number of distinct positions it visits is at most $t+1$: repetitions can only reduce the number of distinct positions. Summing this bound over the $k$ tapes gives at most $k(t+1)$.
