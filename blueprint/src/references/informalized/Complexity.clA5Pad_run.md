<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pad_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded Runs Match Source Runs

**Claim.** For every time $t$, the padded machine run from a padded configuration equals the padding of the original machine run from that configuration.

**Proof.** It suffices to show that one step of the padded machine commutes with padding; the run-commutation principle then yields the equality for every number of steps (`Turing.MultiTapeTM.runFrom_comm_of_step`). For a configuration in the halting state, both machines leave their configuration unchanged, so the step relation holds. In a nonhalting state, the padded configuration presents the original machine with exactly the same symbols under its first $k$ work-tape heads. The transition therefore selects the same action as the original machine. Padding that action commutes with applying it to the padded configuration (`clA5Pad_apply`), which proves the one-step relation in this case as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Complexity.clA5Pad_apply`.
