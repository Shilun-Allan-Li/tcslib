<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.setThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment followed by execution

**Claim.** If $s$ ends from the state obtained by assigning $e$ to $x$ within the remaining budget $T-(\mathrm{cost}(e)+1)$ and satisfies $Q$, while $e$ is safe initially and its cost plus one is at most $T$, then the assignment followed by $s$ ends within $T$ and satisfies $Q$.

**Proof.** First apply the bounded assignment result (`Light.Ends.set`) with the postcondition that executing $s$ from the resulting state ends within the remaining budget and satisfies $Q$. The assignment's cost is exactly $\mathrm{cost}(e)+1$, so this postcondition holds by the hypothesis on $s$. Then compose the assignment with $s$ using the sequential composition result (`Light.Ends.next`), taking the assignment cost as the first budget. The assumed bound on that cost ensures it fits within $T$, and the remaining budget is precisely the one allowed for $s$.

**Key facts.** `Light.Ends.next`, `Light.Ends.set`.
