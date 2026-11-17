<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenMachine.lean :: Complexity.LogProg.ISGen.IG.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State equality and machine semantics

**Claim.** If two initial states are equal, any bounded termination and acceptance property holding from the second state also holds from the first.

**Proof.** Substitute the equal state into the semantic statement. The initial configurations then coincide, so the bounded termination condition and the equivalence between acceptance and the proposition are exactly those already given for the second state.
