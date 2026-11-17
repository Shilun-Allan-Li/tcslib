<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.store -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Executing a Store

**Claim.** Under the stated safety, address, and cost hypotheses, if $Q$ holds in the state obtained by updating memory at the address to the value of $e$, then the store statement executes within budget $T$ and ends in a state satisfying $Q$.

**Proof.** Apply the store execution rule using the assumed safety of $a$ and $e$ and the validity of the address $a(\sigma)$. This gives an execution whose final state has the same local function as $\sigma$ and whose memory is updated at the natural-number conversion of $a(\sigma)$ to $e(\sigma)$. Its cost is exactly $\operatorname{cost}(a)+\operatorname{cost}(e)+1$, which is at most $T$ by hypothesis, and the assumed postcondition holds in that final state.
