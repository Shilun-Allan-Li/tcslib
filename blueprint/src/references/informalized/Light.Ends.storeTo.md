<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.storeTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Store to a Specified Address and Value

**Claim.** If the postcondition holds after updating memory at $b$ to $z$, and $a$ and $e$ are safe and evaluate to $b$ and $z$, with $b$ a valid address and the store cost at most $T$, then the store executes within budget $T$ and ends in a state satisfying $Q$.

**Proof.** The evaluation hypotheses identify the address value $a(\langle\operatorname{frame}(l),\mu\rangle)$ with the natural number $b$ and the stored value with $z$. Since $b$ is nonnegative and less than the space bound, its integer cast is a valid address. The natural-number conversion of that cast is $b$ itself, so updating memory at the evaluated address to the evaluated value produces exactly the state in which $Q$ is assumed. The store execution result (Light.Ends.store), applied with these facts and the cost bound, gives the conclusion.

**Key facts.** `Light.Ends.store`.
