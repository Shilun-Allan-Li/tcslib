<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_part -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bank Component Action

**Claim.** At each coordinate, the bank component action is the stationary halting action when that counter is halted, and otherwise is the counter transition on its state and scanned symbols.

**Proof.** Fix a coordinate. The product configuration stores the corresponding counter's work tape and head position at that coordinate, so its scanned work symbol is exactly the counter's scanned work symbol (there is only one work tape in each counter). Unfold the component action and split according to whether the counter state is halted. In the halted case, both sides are the stationary halting action. In the active case, the bank supplies the scanned work symbol just identified; its transition is evaluated with no input symbol, while the counter transition on the right uses the counter's scanned input symbol. These give the same action because the counter transition function ignores its input-symbol argument.
