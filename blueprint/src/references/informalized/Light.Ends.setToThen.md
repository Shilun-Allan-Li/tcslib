<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.setToThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Set followed by a program

**Claim.** If $s$ ends from the state whose locals are the frame of $l$ after setting position $x$ to $z$, within the remaining budget, and satisfies $Q$, while $e$ is safe initially, evaluates to $z$, and its cost plus one is at most $T$, then assigning $e$ to $x$ and executing $s$ ends within $T$ and satisfies $Q$.

**Proof.** Use the assignment-to-a-prescribed-value result (`Light.Ends.setTo`) with postcondition that executing $s$ from the resulting state ends within the remaining budget and satisfies $Q$. The hypothesis on $s$ gives this postcondition because the assigned value is $z$. Then compose the assignment with $s$ using the sequential composition result (`Light.Ends.next`): the assignment takes its exact cost, $\mathrm{cost}(e)+1$, which is at most $T$, and leaves the stated remaining budget for $s$.

**Key facts.** `Light.Ends.next`, `Light.Ends.setTo`.
