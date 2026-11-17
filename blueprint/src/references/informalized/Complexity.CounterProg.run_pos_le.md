<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.run_pos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Input-Position Growth

**Claim.** After $t$ steps from any state, the read position is at most its initial position plus $t$.

**Proof.** Induct on $t$, generalizing over the starting state. At zero steps the position is unchanged. For the successor case, first take one step and then apply the induction hypothesis to the resulting state, using the run decomposition law (`Complexity.CounterProg.run_succ`). A single step increases the read position by at most one: only a read instruction with an available input symbol advances it, and then it advances by exactly one; all other cases leave it unchanged. Adding these bounds gives an increase of at most $t+1$ over the original position.

**Key facts.** `Complexity.CounterProg.run_succ`.
