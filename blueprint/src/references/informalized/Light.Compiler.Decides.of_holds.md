<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Conditions.lean :: Light.Compiler.Decides.of_holds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution When a Predicate Holds

**Claim.** If the predicate holds, the program has a run of at most $\mathrm{size}$ steps from the specified initial position and memory to position $\mathrm{pos}+\mathrm{size}$, with the required agreement outside the scratch addresses.

**Proof.** Unpack the deciding data supplied by the hypothesis: a memory $m'$ and a step count $n\le\mathrm{size}$, together with agreement outside the scratch set and a run to position $\mathrm{pos}+\mathrm{size}$ whenever the predicate holds. Apply that conditional run statement to the given proof that the predicate holds. The same $m'$ and $n$ give the desired run and retain the bound and agreement properties.
