<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.Decides.of_fails -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution When a Predicate Fails

**Claim.** If the predicate is false, the program has a run of at most $\mathrm{size}$ steps from the specified initial position and memory to position $l$, with the required agreement outside the scratch addresses.

**Proof.** Unpack the deciding data supplied by the hypothesis: a memory $m'$ and a step count $n\le\mathrm{size}$, together with agreement outside the scratch set and a run to position $l$ under the assumption that the predicate is false. Apply that conditional run statement to the given proof that the predicate is false. The same $m'$ and $n$ then satisfy all the requested conclusions.
