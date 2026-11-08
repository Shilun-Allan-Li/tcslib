<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.setLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment from local and memory maps

**Claim.** If the postcondition holds after updating local $x$ to the value of $e$ in $(\mathrm{loc},\mu)$, and $e$ is safe there with cost plus one at most $T$, then assigning $e$ to $x$ from $(\mathrm{loc},\mu)$ ends within time $T$ and satisfies the postcondition.

**Proof.** Apply the bounded assignment result (`Light.Ends.set`) to the state with local map $\mathrm{loc}$ and memory map $\mu$. Its updated local map and unchanged memory are exactly the state in the postcondition, so the hypotheses provide the required safety, time bound, and final-state property.

**Key facts.** `Light.Ends.set`.
