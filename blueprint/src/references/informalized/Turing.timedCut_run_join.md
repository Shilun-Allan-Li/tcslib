<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_run_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Two Run Segments

**Claim.** If running the machine for $s$ steps from $a$ yields $b$, and then for $t$ steps from $b$ yields $c$, its run for $s+t$ steps from $a$ yields $c$.

**Proof.** The run-concatenation identity (`Turing.MultiTapeTM.runFrom_add`) rewrites the run of length $s+t$ from $a$ as a run of length $t$ starting from the configuration reached after $s$ steps. Substitute the two assumed run equalities: the intermediate configuration is $b$, and the second segment ends at $c$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
