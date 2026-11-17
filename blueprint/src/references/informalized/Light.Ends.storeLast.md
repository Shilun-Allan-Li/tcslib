<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.storeLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Store with a Final State

**Claim.** Under the stated assumptions, the store statement executes from $(\mathrm{loc},\mu)$ within budget $T$ and ends in a state satisfying $Q$.

**Proof.** In the state with local function $\mathrm{loc}$ and memory $\mu$, the hypothesis $h$ says that $Q$ holds after updating memory at the natural-number conversion of the address expression's value to the value expression's value. The safety, valid-address, and cost assumptions are precisely the hypotheses needed for the store execution result (Light.Ends.store). Applying it yields the claimed bounded execution.

**Key facts.** `Light.Ends.store`.
