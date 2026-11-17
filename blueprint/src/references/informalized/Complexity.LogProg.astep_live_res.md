<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean :: Complexity.LogProg.astep_live_res -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live Result Remains Unset

**Claim.** If one abstract step from an active configuration with unset result produces another active configuration, then the resulting stored answer is still unset.

**Proof.** The possible-outcomes lemma (`astep_cases`) says that the step either produces an active configuration with its result unchanged, or halts with a stored Boolean answer. In the first case, equality with the given active result identifies the resulting answer as the original unset one. In the second case, equality with an active configuration is impossible because its state component is absent, whereas the specified result configuration has no active state. Thus only the first case can occur, and the result is unset.

**Key facts.** `Complexity.LogProg.astep_cases`.
