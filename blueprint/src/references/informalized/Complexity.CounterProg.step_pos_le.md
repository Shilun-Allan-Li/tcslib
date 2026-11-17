<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.step_pos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read Position Preservation

**Claim.** If the read position of $s$ is at most $|x|$, then the state after one program step also has read position at most $|x|$.

**Proof.** All instructions except reading leave the read position unchanged, so the bound is preserved for them, including the halted state. A read instruction leaves the position unchanged at end of input. If it reads a bit, that bit exists at the current position, which implies the position is strictly less than $|x|$; increasing it by one therefore leaves it at most $|x|$.
