<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamRun_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialized Schedule Produces the Transform

**Claim.** For every CNF formula $\varphi$, running $|\mathrm{enc}(\varphi)|+1$ rounds on its encoding from cursor $\mathrm{numVars}(\varphi)$, consumed length zero, and formula phase emits the encoding of its clause-splitting transform.

**Proof.** The formula-schedule result applies with empty prefix and empty remainder, so the first $\mathrm{satStreamCount}(\varphi)$ rounds emit the encoding of the transform and end in finished phase. The length bound on the schedule count ensures this is no more than the stated number of rounds. Decompose the full run into those initial rounds and the remaining rounds; the run-addition identity gives the second segment starting from the finished state. Finished-state absorption shows that this segment preserves the state and emits nothing. The resulting output is therefore precisely the encoding of the transform, with the starting cursor equal to the formula's variable count.

**Key facts.** `Complexity.satStreamCount_le`, `Complexity.satStreamRun_add`, `Complexity.satStreamRun_formula`, `Complexity.satStreamRun_finished`.
