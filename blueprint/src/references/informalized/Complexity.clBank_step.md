<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Componentwise Bank Step

**Claim.** One step of the bank from a product configuration equals the product configuration obtained by taking one counter step at every coordinate.

**Proof.** First identify the bank's component-action function with the function that, at each coordinate, uses the stationary halting action for a halted counter and otherwise uses that counter's transition (`Complexity.clBank_part`). Unfold the bank step: its control is assembled from the successor states of these component actions, and its work-tape actions are assembled from their work-tape actions. Compare the resulting configuration with the product of the individual counter steps. The input position agrees because the bank makes zero input-head movement (`Turing.moveInputPos_zero`). For each coordinate, split on whether its counter is halted: in the halted case its control action leaves its work tape and head position unchanged; in the active case these fields are exactly those produced by the counter transition. The output agrees because neither the bank nor the counter transitions append output. Thus all configuration fields agree.

**Key facts.** `Complexity.clBank_part`, `Turing.moveInputPos_zero`.
