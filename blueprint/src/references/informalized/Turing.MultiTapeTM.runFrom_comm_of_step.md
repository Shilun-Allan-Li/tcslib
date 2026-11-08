<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_comm_of_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step-Commuting Maps Preserve Runs

**Claim.** If a map of configurations commutes with one-step transitions, then it carries every finite run to the corresponding run of the other machine.

**Proof.** The hypothesis says that applying one step in the target machine after mapping a configuration gives the same result as mapping its one-step successor. Iterating this relation shows that the target transition function iterated $n$ times after the map equals the map after the source transition function has been iterated $n$ times. Evaluating at the given configuration yields the claimed equality.
