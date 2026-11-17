<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.storeThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Store Followed by a Computation

**Claim.** If $s$ executes within the remaining budget from the state produced by storing $e$ at address $a$, and the store's safety, address, and cost conditions hold, then the store followed by $s$ executes within budget $T$ and ends in a state satisfying $Q$.

**Proof.** First establish the bounded execution of the store itself, with budget $\operatorname{cost}(a)+\operatorname{cost}(e)+1$, using the store-with-final-state result (Light.Ends.storeLast); the assumed postcondition for this store is the assertion that $s$ can then execute within the remaining budget. Next apply the sequential composition result (Light.Ends.next), which combines this first execution with the given execution of $s$. The store-cost bound ensures the first-stage budget does not exceed $T$, and the second stage receives exactly the remainder $T-(\operatorname{cost}(a)+\operatorname{cost}(e)+1)$.

**Key facts.** `Light.Ends.next`, `Light.Ends.storeLast`.
