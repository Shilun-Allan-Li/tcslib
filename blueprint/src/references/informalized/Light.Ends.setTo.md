<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.setTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment to a prescribed local value

**Claim.** If $Q$ holds in the state whose locals are the frame of $l$ after setting position $x$ to $z$, and $e$ is safe in the state with locals given by the frame of $l$ and evaluates to $z$, with cost plus one at most $T$, then assigning $e$ to $x$ ends within $T$ and satisfies $Q$.

**Proof.** The assertion that $e$ gives $z$ supplies both its safety and the equality between its value in the initial state and $z$. Apply the bounded assignment result (`Light.Ends.set`) with the postcondition asserting $Q$ of the state obtained by updating the initial local map at $x$ to that value. Since the value is $z$, the updated map is the update to the frame of $l$ by $z$. The frame update identity (`Light.update_frame_setLocal`) identifies this map with the frame of the list obtained by setting position $x$ to $z$; memory remains $\mu$. Thus the assumed postcondition applies.

**Key facts.** `Light.Ends.set`, `Light.update_frame_setLocal`.
