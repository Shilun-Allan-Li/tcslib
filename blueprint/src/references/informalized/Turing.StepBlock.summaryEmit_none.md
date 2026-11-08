<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryEmit_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitting from an Empty Summary

**Claim.** Combining an empty summary with any optional Boolean value $b$ returns $b$.

**Proof.** There are three possibilities for $b$. If $b$ is absent, the definition returns the existing summary, which is absent. If $b$ is present and true, the definition returns true; if it is present and false, the definition returns false. In each case the result is $b$.
