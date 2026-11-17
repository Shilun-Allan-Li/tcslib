<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.storeToThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Store Followed by a Computation at a Specified Address

**Claim.** If $s$ executes within the remaining budget from the state whose memory is updated at $b$ to $z$, and the address and value expressions safely evaluate to $b$ and $z$ with $b$ below the space bound, then storing and executing $s$ from the original state ends in a state satisfying $Q$ within budget $T$.

**Proof.** First, the specified-address store result (Light.Ends.storeTo) turns the evaluation and validity hypotheses, together with the store-cost bound, into a bounded execution of the store from the original state. Its final state is exactly the state with memory updated at $b$ to $z$, so the assumed execution of $s$ supplies the postcondition for this first stage. Then the sequential composition result (Light.Ends.next) combines the store and the given execution of $s$, assigning the latter the remaining budget. The store-cost bound ensures the first-stage budget is within $T$.

**Key facts.** `Light.Ends.next`, `Light.Ends.storeTo`.
