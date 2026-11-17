<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.setValThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment with prescribed result followed by execution

**Claim.** If $s$ ends from the state obtained by updating local $x$ to $z$ within the remaining budget and satisfies $Q$, and $e$ is safe initially, evaluates to $z$, and has cost plus one at most $T$, then assigning $e$ to $x$ and executing $s$ ends within $T$ and satisfies $Q$.

**Proof.** Apply the assignment-with-prescribed-result result (`Light.Ends.setVal`) with the postcondition that executing $s$ from the updated state ends within the remaining budget and satisfies $Q$. The hypothesis on $s$ supplies that postcondition. Compose the assignment and $s$ using the sequential composition result (`Light.Ends.next`), allocating the assignment its exact cost, $\mathrm{cost}(e)+1$. This cost fits within $T$, and the remaining budget is the one assumed for $s$.

**Key facts.** `Light.Ends.next`, `Light.Ends.setVal`.
