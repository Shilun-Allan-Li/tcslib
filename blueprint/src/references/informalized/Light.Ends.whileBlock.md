<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.whileBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded execution of a while loop

**Claim.** Under the stated invariant, safety, progress, termination, and time-bound hypotheses, the loop ends in a state satisfying $Q$ within time $T$.

**Proof.** For each $j<n$, the round hypothesis gives a safe, true guard and a body execution that is block-safe and whose resulting state satisfies $I_{j+1}$. The block-execution result (`Ends.block`) turns this into an execution of the body within its block cost. Applying the fixed-cost loop theorem (`Ends.whileConst`) with that cost, the invariant sequence, and the given terminal condition yields the loop execution within the stated bound. The supplied bound is exactly the fixed-cost estimate for $n$ rounds plus the final guard check.

**Key facts.** `Light.Ends.block`, `Light.Ends.whileConst`.
