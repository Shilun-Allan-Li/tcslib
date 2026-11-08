<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.setVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment with a prescribed result

**Claim.** If $Q$ holds after updating local $x$ to $z$, and $e$ is safe in the initial state and evaluates there to $z$, with cost plus one at most $T$, then assigning $e$ to $x$ ends within $T$ and satisfies $Q$.

**Proof.** The equality between the value of $e$ and $z$ identifies the state produced by assignment with the state in the assumed postcondition: both have local map updated at $x$ to $z$ and unchanged memory. Apply the bounded assignment result (`Light.Ends.set`) using the safety of $e$, the given cost bound, and this postcondition.

**Key facts.** `Light.Ends.set`.
